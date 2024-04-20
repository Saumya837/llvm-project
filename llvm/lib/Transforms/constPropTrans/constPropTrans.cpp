#include<iostream>
#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/raw_ostream.h"
#include <unordered_map>
#include <unordered_set>
#include <map>
#include <regex>
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
        RegName.erase(remove_if(RegName.begin(), RegName.end(), ::isspace), RegName.end());
        return RegName;
    }

    vector<string> getOp(Instruction *I)
    {
        string InstStr;
        raw_string_ostream OS(InstStr);
        I->print(OS);
        string Str = OS.str();

        // Find the position of '=' to skip the instruction name and potential result storage
        size_t pos = Str.find('=');
        string newstr = Str.substr(pos + 1);

        vector<string> opOcc; // Vector to store operand names

        // Find all occurrences of '%', which indicate the start of an operand name
        size_t new_pos = newstr.find('%');
        while (new_pos != string::npos) {
            // Find the end of the operand name, which is delimited by a space, comma, or ')'
            size_t end_pos = newstr.find_first_of(" ,)", new_pos + 1);

            // Extract the operand from new_pos to end_pos
            string op = newstr.substr(new_pos, end_pos - new_pos);
            opOcc.push_back(op);

            // Search for the next '%'
            new_pos = newstr.find('%', end_pos);
        }
        return opOcc;
    }

    vector<int> getConst(Instruction *I) {
        string InstStr;
        raw_string_ostream OS(InstStr);
        I->print(OS);
        OS.flush();  // Ensure the string is updated with the content of the stream

        vector<int> constants;
        const string& Str = OS.str();
        
        for (size_t i = 0; i < Str.length(); ++i) {
            // Check if the current character is a digit and the previous character is either
            // a space or the start of the string (for numbers at the start).
            if (isdigit(Str[i]) && (i == 0 || isspace(Str[i - 1]))) {
                size_t start = i;
                // Move forward to capture the full integer
                while (i < Str.length() && isdigit(Str[i])) {
                    i++;
                }
                // Convert the substring that represents the integer to an int
                int value = stoi(Str.substr(start, i - start));
                constants.push_back(value);
            }
        }

        return constants;
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

    vector<string> getArgs(CallInst *CI)
     {
        string InstStr;
        raw_string_ostream OS(InstStr);
        CI->print(OS);
        OS.flush();  // Ensure the stream is flushed to the string

        vector<string> Args;
        size_t pos = 0;
        size_t end = 0;

        // Search for the 'noundef' keyword, then capture the argument that follows
        while ((pos = InstStr.find("noundef", pos)) != std::string::npos) {
            pos += 7;  // Move past "noundef"
            
            // Skip whitespace and find the start of the argument
            while (pos < InstStr.size() && isspace(InstStr[pos])) ++pos;

            // Check if the argument is a variable (starts with '%')
            if (pos < InstStr.size() && InstStr[pos] == '%')
            {
                end = pos;
                // Capture until a space, comma, or ')' is found
                while (end < InstStr.size() && InstStr[end] != ' ' && InstStr[end] != ',' && InstStr[end] != ')') ++end;
                Args.push_back(InstStr.substr(pos, end - pos));
            } 
            else
            {
                // It's a constant or other type of value; capture it similarly
                end = pos;
                while (end < InstStr.size() && InstStr[end] != ' ' && InstStr[end] != ',' && InstStr[end] != ')') ++end;
                Args.push_back(InstStr.substr(pos, end - pos));
            }
            pos = end;  // Update position to search for the next argument
        }
        return Args;
    }

    bool canRemoveStore(StoreInst *SI)
    {
        Value *StoredPtr = SI->getPointerOperand();
        Function *func = SI->getFunction();

        // Flag to start checking after the store instruction
        bool found = false;

        // Check if the stored pointer is used in subsequent instructions
        for (auto &I : instructions(func)) {
            if (&I == SI) {
                found = true;
                continue;
            }
            if (found)
            {
                // Check each operand in the instruction to see if it uses storedPtr
                for (unsigned int i = 0; i < I.getNumOperands(); i++) {
                    if (I.getOperand(i) == StoredPtr) 
                        return false;
                    }
            }
                            
        }
        return true;
    };

    bool isUsedAfterAlloca(Instruction *allocaInst) {
        Value *allocatedMemory = cast<AllocaInst>(allocaInst);
        bool pastAlloca = false; // Flag to track if we are past the AllocaInst in the block

        // Iterate over all instructions in the function to check for uses
        for (auto &BB : *allocaInst->getFunction()) {
            for (auto &I : BB) {
                if (&I == allocaInst) {
                    pastAlloca = true; // Set the flag once we encounter the AllocaInst
                    continue;
                }
                if (pastAlloca) { // Only check for uses after we've encountered AllocaInst
                    // Iterate over all operands in each instruction
                    for (unsigned int i = 0; i < I.getNumOperands(); i++) {
                        if (I.getOperand(i) == allocatedMemory) {
                            return true; // Memory is used after the AllocaInst
                        }
                    }
                }
            }
            pastAlloca = false; // Reset the flag as we move to the next basic block
        }
        return false; // No uses found after the AllocaInst in the function
    }


    struct constPropTrans : public ModulePass 
    {
        static char ID;
        constPropTrans() : ModulePass(ID) {}
        bool runOnModule(Module &M) override
        {
            unordered_map<BasicBlock *, unordered_map<string, int>> bbMap;
            unordered_map<Instruction *, unordered_map<string, int>> instMap;
            unordered_map<BasicBlock *, unordered_map<string, Instruction *>> last_mod_out;
            unordered_map<string, int> final_out;
            vector<string> alloca_var;
            map<string, map<string, int>>funcArg;
            set<Instruction *> InsToDel;

            for (auto &F: M)
            {
                string funcName = F.getName().str();
                if(funcName == "printf" || funcName == "scanf" || funcName == "main")
                    continue;
                else
                {
                    funcArg[funcName];
                    for(Argument &Arg : F.args())
                    {
                        string argName = '%'+Arg.getName().str(); // Get the name of the argument as string
                        funcArg[funcName][argName] =  INT_MAX;
                    }  
                }    
            }

            queue<Function *> workListFunc;
            unordered_map<Function *, queue<BasicBlock *>> workListBB;

            for (auto &F: M)
            {
                string funcName = F.getName().str();
                if((funcName != "printf") && (funcName != "__isoc99_scanf"))
                {
                    workListFunc.push(&F);
                    workListBB[&F];
                    for (BasicBlock &BB : F)
                        workListBB[&F].push(&BB);
                }
            }

            for (auto &F: M)
            {
                for (BasicBlock &BB : F)
                {
                    for (Instruction &I : BB)
                    {
                        if (AllocaInst *AI = dyn_cast<AllocaInst>(&I))
                        {
                            string allocVar = AI->getName().str();
                            // Initialize with INT64_MAX assuming no specific initial values are provided
                            instMap[&I][allocVar] = INT_MAX;
                            bbMap[&BB][allocVar] = INT_MAX;
                            alloca_var.push_back(allocVar);
                            last_mod_out[&BB][allocVar] = &I;
                        }
                    }
                }
            }
        
            while (!workListFunc.empty())
            {
                Function *F = workListFunc.front();
                workListFunc.pop();

                bool hasChanged = false; 

                string funcName = F->getName().str();
                //Printing the function passed
                auto itr = funcArg.find(funcName);
                if (itr != funcArg.end())
                {
                    //get the first Instruction inside the function
                    BasicBlock * BB = &(F->getEntryBlock());

                    Instruction *firstInst = &(F->getEntryBlock().front());

                    for (auto& arg : itr->second) {
                        instMap[firstInst][arg.first] = arg.second;
                        bbMap[BB][arg.first] = arg.second;
                        last_mod_out[BB][arg.first] = firstInst;
                    }
                }

                while (!workListBB[F].empty())
                {
                    BasicBlock *BB = workListBB[F].front();
                    workListBB[F].pop();
                    
                    unordered_map<string, Instruction *> last_mod;
                    BasicBlock *PredBB = BB->getUniquePredecessor();
                    unordered_map<string, int> curr_out;
                    bool change = false;
                    // Check if the function name exists in funcArg

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
                                    bbMap[BB][var] = INT_MIN;
                                    instMap[I][var] = INT_MIN;
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
                                            instMap[&I][VarName] = INT_MIN;
                                            bbMap[BB][VarName] = INT_MIN;
                                            last_mod[VarName] = &I;
                                        }
                                    }
                                }
                            }
                            else if (CalledFunc && CalledFunc->getName().endswith("printf"))
                                continue;
                            // Handling Call Instructions in a function
                            else
                            {
                                string callee = CalledFunc->getName().str();
                                vector<string> callArgs = getArgs(CI);
                                vector<int> argValues;

                                // Process each argument retrieved from the call
                                for (const auto& arg : callArgs) {
                                    if (arg[0] == '%')  // Check if the argument is a variable
                                        argValues.push_back(instMap[last_mod[arg]][arg]);
                                    else {  // Handle constant arguments
                                        int val = stoi(arg);  // Convert string to integer
                                        // errs()<< val <<" ";
                                        argValues.push_back(val);
                                    }
                                }
                                // errs()<<"\n";

                                int count = 0;
                                // Compare and potentially update function arguments
                                for (auto& var : funcArg[callee]) {
                                    if (var.second == INT_MAX)
                                    {
                                        var.second = argValues[count];
                                        hasChanged = true;
                                        count++;  
                                    }
                                    else if(var.second != argValues[count])
                                    {
                                        var.second = INT_MIN;
                                        hasChanged = true;
                                        count++;  
                                    }
                                }
                                if (hasChanged)
                                {
                                    workListFunc.push(CalledFunc);
                                    for(auto &BB : *CalledFunc)
                                        workListBB[CalledFunc].push(&BB);
                                }
                            }
                        }
                        else if (StoreInst *SI = dyn_cast<StoreInst>(&I))
                        {
                            Value *StoredValue = SI->getValueOperand();
                            string VarName = SI->getPointerOperand()->getName().str();
                            if (ConstantInt *CI = dyn_cast<ConstantInt>(StoredValue))
                            {
                                // If the stored value is a constant integer  
                                instMap[&I][VarName] = CI->getSExtValue();
                                last_mod[VarName] = &I;
                            }
                            else
                            {
                                string StoredVar = "%"+StoredValue->getName().str();
                                instMap[&I][VarName] = instMap[last_mod[StoredVar]][StoredVar] ;
                                last_mod[VarName] = &I;
                            }
                        }
                        else if (LoadInst *LI = dyn_cast<LoadInst>(&I))
                        {
                            string tempReg = getReg(&*LI);
                            string varName = LI->getPointerOperand()->getName().str();
                           
                            if (instMap[last_mod[varName]][varName] == INT_MIN)
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
                                if(instMap[last_mod[Op1Name]][Op1Name]==INT_MIN)
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

                                if((instMap[last_mod[Op1Name]][Op1Name]==INT_MIN)||(instMap[last_mod[Op2Name]][Op2Name]==INT_MIN))
                                {
                                    instMap[&I][resultReg] = INT_MIN;
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
                        else if (auto *ICmp = dyn_cast<ICmpInst>(&I))
                        {
                           vector<string> Opn;
                           Opn = getOp(ICmp);
                           string proVar = getReg(ICmp);
                           if (ICmp->getPredicate() == ICmpInst::ICMP_SGT)
                           {
                                if(Opn.size() == 1)
                                { 
                                    string varName = Opn[0];
                                    int64_t value = getConst(ICmp)[0];
                                    if(instMap[last_mod[varName]][varName] == INT_MIN)
                                    {
                                        last_mod[proVar] = &I;
                                        instMap[&I][proVar] = INT_MIN;
                                    }
                                    else
                                    {
                                        if(instMap[last_mod[varName]][varName] == value)
                                        {
                                            last_mod[proVar] = &I;
                                            instMap[&I][proVar] = 1;
                                        }
                                        else
                                        {
                                            last_mod[proVar] = &I;
                                            instMap[&I][proVar] = 0;
                                        }
                                    }
                                }
                            }
                            else if(ICmp->getPredicate() == ICmpInst::ICMP_NE)
                            {
                                if(Opn.size() == 1)
                                {
                                    string varName = Opn[0];
                                    int64_t value = getConst(ICmp)[0];

                                    if(instMap[last_mod[varName]][varName] == INT32_MIN)
                                    {
                                        last_mod[proVar] = &I;
                                        instMap[&I][proVar] = INT32_MIN;
                                    }
                                    else
                                    {
                                        if(instMap[last_mod[varName]][varName] == value)
                                        {
                                            last_mod[proVar] = &I;
                                            instMap[&I][proVar] = 0;
                                        }
                                        else
                                        {
                                            last_mod[proVar] = &I;
                                            instMap[&I][proVar] = 1;
                                        }
                                    }
                                }
                            }
                        }
                        else if (auto *Z = dyn_cast<ZExtInst>(&I))
                        {
                            string proVar = getReg(Z);
                            Value *srcValue = Z->getOperand(0);
                            string varName  = '%'+srcValue->getName().str();
                            last_mod[proVar] = &I;
                            instMap[&I][proVar] = instMap[last_mod[varName]][varName];
                        }
                        else if (SelectInst *SelInst = dyn_cast<SelectInst>(&I))
                        {
                            // Access the condition, true value, and false value of the select instruction
                            Value *Condition = SelInst->getCondition();
                            Value *TrueValue = SelInst->getTrueValue();
                            Value *FalseValue = SelInst->getFalseValue();

                            string procVar = getReg(SelInst);
                            string condVar = '%'+Condition->getName().str();

                            if(instMap[last_mod[condVar]][condVar]==INT_MIN)
                            {
                                instMap[&I][procVar] = INT_MIN;
                                last_mod[procVar] = &I;
                            }
                            else if(instMap[last_mod[condVar]][condVar]==0)
                            {
                                 if(FalseValue->hasName())
                                {
                                    string varName = FalseValue->getName().str();
                                    instMap[&I][procVar] = instMap[last_mod[varName]][varName];
                                    last_mod[procVar] = &I;
                                }
                                else if (ConstantInt *CI = dyn_cast<ConstantInt>(FalseValue))
                                {
                                    instMap[&I][procVar] = CI->getSExtValue();  // Directly use the constant integer value
                                    last_mod[procVar] = &I;
                                }
                            }
                            else if(instMap[last_mod[condVar]][condVar]==1)
                            {
                                 if(FalseValue->hasName())
                                {
                                    string varName = TrueValue->getName().str();
                                    instMap[&I][procVar] = instMap[last_mod[varName]][varName];
                                    last_mod[procVar] = &I;
                                }
                                else if (ConstantInt *CI = dyn_cast<ConstantInt>(TrueValue))
                                {
                                    instMap[&I][procVar] = CI->getSExtValue();  // Directly use the constant integer value
                                    last_mod[procVar] = &I;
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
                        unordered_set< BasicBlock* > seenBlocks;

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
                                    workListBB[F].push(Succ);
                                    tempQueue.push(Succ);
                                    seenBlocks.insert(Succ);
                                }
                            }
                        }
                    }
                }
            }

            for (auto &F : M)
            {
                for (BasicBlock &BB : F)
                {
                    for(Instruction &I : BB)
                    {
                         LLVMContext &context = M.getContext();
                        if(isa<LoadInst>(&I))
                        {
                            string valLoad  = getReg(&I);
                            int valRep = instMap[&I][valLoad];
                           
                            Value *Op1 = ConstantInt::get(Type::getInt32Ty(context), valRep);
                            if((instMap[&I][valLoad] != INT32_MIN) && (instMap[&I][valLoad] != INT32_MAX))
                            {
                                I.replaceAllUsesWith(Op1);
                                InsToDel.insert(&I);
                            }
                        }
                        else if(isa<BinaryOperator>(&I))
                        {
                            string valLoad  = getReg(&I);
                            int valRep = instMap[&I][valLoad];
                            Value *Op1 = ConstantInt::get(Type::getInt32Ty(context), valRep);
                            if((instMap[&I][valLoad] != INT32_MIN) && (instMap[&I][valLoad] != INT32_MAX))
                            {
                                I.replaceAllUsesWith(Op1);
                                InsToDel.insert(&I);
                            }
                        }
                    }
                }
            }

            for (const auto &I : InsToDel)
                I->eraseFromParent();
            
            InsToDel.clear();
            
            for (auto &F : M)
            {
                for (BasicBlock &BB : F)
                {
                    for(Instruction &I : BB)
                    {
                        if (StoreInst *SI = dyn_cast<StoreInst>(&I))//
                        {
                            if(canRemoveStore(SI))
                                InsToDel.insert(&I);
                        }
                    }
                }
            }

            for (const auto &I : InsToDel)
                I->eraseFromParent();

            InsToDel.clear();

            for (auto &F : M) {
                for (BasicBlock &BB : F) {
                    for (Instruction &I : BB) {
                        if (AllocaInst *AI = dyn_cast<AllocaInst>(&I))
                        {
                            if (!isUsedAfterAlloca(AI))
                                InsToDel.insert(&I);
                        }
                    }
                }
            }

            for (const auto &I : InsToDel)
                I->eraseFromParent();

        return true;
        }
    };
}

char constPropTrans::ID = 0;
static RegisterPass<constPropTrans> X("constPropTrans", "Perform interpocedural constant propagation");

