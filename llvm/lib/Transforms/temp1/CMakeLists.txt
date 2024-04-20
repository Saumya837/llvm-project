# If we don't need RTTI or EH, there's no reason to export anything
# from the hello plugin.

add_llvm_library(temp MODULE BUILDTREE_ONLY
  temp.cpp

  PLUGIN_TOOL
  opt
  )