#include<iostream>
#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/raw_ostream.h"
#include <unordered_map>
#include <unordered_set>
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/FileSystem.h"
#include <queue>

using namespace llvm;
using namespace std;

namespace 
{
    string getReg(Instruction *I)
    {
        string InstStr;
        raw_string_ostream OS(InstStr);
        I->print(OS);
        string Str = OS.str();
        // Find the position of '='
        size_t pos = Str.find('=');
        if (pos == std::string::npos)
            return ""; // If '=' is not found, return empty string
        // Extract the substring before '='
        string RegName = Str.substr(0, pos);
        // Trim whitespace from the extracted register name
        RegName.erase(std::remove_if(RegName.begin(), RegName.end(), ::isspace), RegName.end());
        return RegName;
    }

    vector<string> getOp(Instruction *I) 
    {
        string InstStr;
        raw_string_ostream OS(InstStr);

        I->print(OS);
        string Str = OS.str();

        size_t pos = Str.find('=');
        string newstr = Str.substr(pos + 1);

        // Create a vector to store all occurrences of '%'
        vector<string> opOcc;

        size_t new_pos = newstr.find('%');
        while (new_pos != string::npos) {
            // Extract the substring starting at the position of '%' with a length of 2 characters
            string op = newstr.substr(new_pos, 2);
            // Store the extracted substring in the vector
            opOcc.push_back(op);
            // Find the next occurrence of '%'
            new_pos = newstr.find('%', new_pos + 1);
        }
        return opOcc;
    }

    string getOperator(Instruction *I) 
    {
        string InstStr;
        raw_string_ostream OS(InstStr);

        I->print(OS);
        string Str = OS.str();

        size_t pos = Str.find('=');
        string newstr = Str.substr(pos + 1);

        string op = newstr.substr(1, 3); 
        return op;
    }

    struct constProp : public FunctionPass 
    {
        static char ID;
        constProp() : FunctionPass(ID) {}
        bool runOnFunction(Function &F) override
        {
            unordered_map<BasicBlock *, unordered_map<string, int64_t>> bbMap;
            unordered_map<Instruction *, unordered_map<string, int64_t>> instMap;
            unordered_map<BasicBlock *, unordered_map<string, Instruction *>> last_mod_out;
            unordered_map<string, int64_t> final_out;
            vector<string> alloca_var;
            

            // Initialize data flow values for each basic block and instruction
            for (BasicBlock &BB : F)
            {
                for (Instruction &I : BB)
                {
                    if (AllocaInst *AI = dyn_cast<AllocaInst>(&I))
                    {
                        string allocVar = AI->getName().str();
                        instMap[&I][allocVar] = INT64_MAX;  // Use INT64_MAX to represent an unknown value at the start
                        bbMap[&BB][allocVar] = INT64_MAX;
                        alloca_var.push_back(allocVar);
                        last_mod_out[&BB][allocVar] = &I;
                    }
                }
            }

            queue<BasicBlock *> workList;

            for (BasicBlock &BB : F)
                workList.push(&BB);

            while (!workList.empty())
            {
                BasicBlock *BB = workList.front();
                workList.pop();
                unordered_map<string, Instruction *> last_mod;
                BasicBlock *PredBB = BB->getUniquePredecessor();
                unordered_map<string, int64_t> curr_out;
                bool change = false;
            
                if (BB->getName() != "entry")
                {
                    if(PredBB)
                    {
                        for(auto i =  last_mod_out[PredBB].begin(); i!= last_mod_out[PredBB].end(); ++i)
                        last_mod[i->first] = i->second;
                    }
                    else
                    {
                        Instruction* I = BB->getFirstNonPHIOrDbg();
                        for(auto i = alloca_var.begin(); i!=alloca_var.end(); ++i)
                        {
                            string var = *i;
                            int flag = 0, count = 0, constant;
                            for (BasicBlock *Pred : predecessors(BB))
                            {
                                if(count == 0)
                                {
                                    constant = bbMap[Pred][var];
                                    count++;
                                }
                                else
                                {
                                    if(bbMap[Pred][var]!=constant)
                                    {
                                        flag = 1;
                                        break;
                                    }
                                }
                            }
                            if(flag == 1)
                            {
                                bbMap[BB][var] = INT64_MIN;
                                instMap[I][var] = INT64_MIN;
                                last_mod[var] = I;
                            }
                            else
                            {
                                bbMap[BB][var] = constant;
                                instMap[I][var] = constant;
                                last_mod[var] = I;
                            }
                            
                        }
                    }
                }
                else
                    {
                        for(auto i =  last_mod_out[BB].begin(); i!= last_mod_out[BB].end(); ++i)
                            last_mod[i->first] = i->second;
                    }

                // Transfer functions for each instruction in the basic block
                for (Instruction &I : *BB)
                {
                    // Process each instruction type and update the data flow values as necessary
                    // Your existing logic for handling AllocaInst, StoreInst, LoadInst, etc. goes here
                    // If the data flow value changes, set change to true
                    // Example handling for a Store Instruction
                    if (CallInst *CI = dyn_cast<CallInst>(&I))
                    {
                        Function *CalledFunc = CI->getCalledFunction();
                        if (CalledFunc && CalledFunc->getName().endswith("scanf"))
                        {
                            // Set the bottom value to INT_MIN for variables read by scanf
                            for (unsigned i = 1; i < CI->getNumOperands(); ++i)
                            {
                                Value *ArgValue = CI->getOperand(i);
                                if (PointerType *PT = dyn_cast<PointerType>(ArgValue->getType()))
                                {
                                    if (PT->getPointerElementType()->isIntegerTy())
                                    { 
                                        string VarName = cast<AllocaInst>(ArgValue)->getName().str();
                                        instMap[&I][VarName] = INT64_MIN;
                                        bbMap[BB][VarName] = INT64_MIN;
                                        last_mod[VarName] = &I;
                                    }
                                }
                            }
                        }
                    }
                    else if (StoreInst *SI = dyn_cast<StoreInst>(&I))
                    {
                        Value *StoredValue = SI->getValueOperand();
                        if (ConstantInt *CI = dyn_cast<ConstantInt>(StoredValue))
                        {
                            // If the stored value is a constant integer
                            string VarName = SI->getPointerOperand()->getName().str();
                            instMap[&I][VarName] = CI->getSExtValue();
                            last_mod[VarName] = &I;
                        }
                        else
                        {
                            string StoredVar = "%"+StoredValue->getName().str();
                            string VarName = SI->getPointerOperand()->getName().str();
                            if(instMap[last_mod[StoredVar]][StoredVar]==INT64_MIN)
                            {
                                instMap[&I][VarName] = instMap[last_mod[StoredVar]][StoredVar] ;
                                last_mod[VarName] = &I;
                            }    
                            else
                            {
                                instMap[&I][VarName] = instMap[last_mod[StoredVar]][StoredVar] ;
                                last_mod[VarName] = &I;
                            }
                        }
                    }
                    else if (LoadInst *LI = dyn_cast<LoadInst>(&I))
                    {
                        string tempReg = getReg(&*LI);
                        string varName = LI->getPointerOperand()->getName().str();
                        if (instMap[last_mod[varName]][varName] == INT64_MIN)
                        {
                            instMap[&I][tempReg] = instMap[last_mod[varName]][varName];
                            last_mod[tempReg] = &I;
                            instMap[&I][varName] = instMap[last_mod[varName]][varName];
                        }
                        else
                        {
                            instMap[&I][tempReg] = instMap[last_mod[varName]][varName];
                            instMap[&I][varName] = instMap[last_mod[varName]][varName];
                            last_mod[tempReg] = &I;
                        }
                    }
                    else if (BinaryOperator *BO = dyn_cast<BinaryOperator>(&I))
                    {
                        string OpName = getOperator(&*BO);
                        Value *Op1 = BO->getOperand(0);
                        Value *Op2 = BO->getOperand(1);
                        int64_t Result = 0;
                        string resultReg = getReg(&*BO);
                        
                        if(!(isa<Constant>(Op1)) && (isa<Constant>(Op2)))
                        {
                            string Op1Name = getOp(&*BO)[0];
                            if(instMap[last_mod[Op1Name]][Op1Name]==INT64_MIN)
                            {
                                instMap[&I][resultReg] = instMap[last_mod[Op1Name]][Op1Name];
                                last_mod[resultReg] = &I;
                            }
                            else
                            {
                                int64_t Op2Value = dyn_cast<ConstantInt>(Op2)->getSExtValue();
                                if (OpName == "add")
                                    Result = instMap[last_mod[Op1Name]][Op1Name] + Op2Value;
                                else if (OpName == "sub")
                                    Result = instMap[last_mod[Op1Name]][Op1Name] - Op2Value; 
                                else if(OpName == "mul")
                                    Result = instMap[last_mod[Op1Name]][Op1Name] * Op2Value; 
                                else if(OpName == "div")
                                    Result = instMap[last_mod[Op1Name]][Op1Name] / Op2Value; 

                                instMap[&I][resultReg] = Result;
                                instMap[&I][Op1Name] = instMap[last_mod[Op1Name]][Op1Name];
                                last_mod[resultReg] = &I;
                            }
                        }
                        else if(!(isa<Constant>(Op1)) && !(isa<Constant>(Op2)))
                        {
                            string Op1Name = getOp(&*BO)[0];
                            string Op2Name = getOp(&*BO)[1];
                            string resultReg = getReg(&*BO);

                            if((instMap[last_mod[Op1Name]][Op1Name]==INT64_MIN)||(instMap[last_mod[Op2Name]][Op2Name]==INT64_MIN))
                            {
                                instMap[&I][resultReg] = INT64_MIN;
                                instMap[&I][Op1Name] = instMap[last_mod[Op1Name]][Op1Name];
                                instMap[&I][Op2Name] = instMap[last_mod[Op2Name]][Op2Name];
                            }
                            else 
                            {
                                        
                                if (OpName == "add")
                                    Result = instMap[last_mod[Op1Name]][Op1Name] + instMap[last_mod[Op2Name]][Op2Name];
                                else if (OpName == "sub")
                                    Result = instMap[last_mod[Op1Name]][Op1Name] - instMap[last_mod[Op2Name]][Op2Name]; 
                                else if(OpName == "mul")
                                    Result = instMap[last_mod[Op1Name]][Op1Name] * instMap[last_mod[Op2Name]][Op2Name]; 
                                else if(OpName == "div")
                                    Result = instMap[last_mod[Op1Name]][Op1Name] / instMap[last_mod[Op2Name]][Op2Name]; 

                                instMap[&I][resultReg] = Result;
                                instMap[&I][Op1Name] = instMap[last_mod[Op1Name]][Op1Name];
                                instMap[&I][Op2Name] = instMap[last_mod[Op2Name]][Op2Name];
                                last_mod[resultReg] = &I;
                            }
                        }

                    }
                    
                }
                for(auto i = alloca_var.begin(); i!=alloca_var.end(); ++i)
                {
                    string var = *i;
                    int value = instMap[last_mod[var]][var];
                    bbMap[BB][var] = value;
                    curr_out[var] = value;
                }
                last_mod_out[BB] = last_mod;

                for(auto i = alloca_var.begin(); i!=alloca_var.end(); ++i)
                {
                    if(final_out[*i]!=curr_out[*i])
                    {
                        final_out[*i] = curr_out[*i];
                        change = true;
                    }
                }

                if (change)
                {
                    queue<BasicBlock*> tempQueue;
                    unordered_set<BasicBlock*> seenBlocks;

                    tempQueue.push(BB);
                    seenBlocks.insert(BB);

                    while (!tempQueue.empty())
                    {
                        BasicBlock* currentBB = tempQueue.front();
                        tempQueue.pop();

                        for (BasicBlock *Succ : successors(currentBB))
                        {
                            if (seenBlocks.find(Succ) == seenBlocks.end()) // Check if the block is already seen
                            {
                                workList.push(Succ);
                                tempQueue.push(Succ);
                                seenBlocks.insert(Succ);
                            }
                        }
                    }
                }
            }
            for (BasicBlock &BB : F) 
            {
                for (Instruction &I : BB) 
                {
                    errs() << I << " -> ";
                    if (instMap.find(&I) != instMap.end()) 
                    {
                        // Instruction found in instMap, write its associated values to file
                        
                        for (auto it = instMap[&I].begin(); it != instMap[&I].end(); ++it) 
                        {
                            errs() << it->first << " = ";
                            if (it->second == INT64_MAX)
                                errs()<< "TOP" << "  ";
                            else if (it->second == INT64_MIN)
                                errs()<< "BOTTOM" << "  ";
                            else
                                errs()<< it->second << "  ";
                        }
                        errs() << "\n\n";
                    }
                }
            }
        }     
    };
}

char constProp::ID = 0;
static RegisterPass<constProp> X("constProp", "Perform intrapocedural constant propagation", false, false);