//
// Created by karth on 1/11/2024.
//

#ifndef LLVM_UTILS_H
#define LLVM_UTILS_H

#include "pch.h"
#include <llvm/IR/Value.h>
#include <string>
#include <llvm/IR/DebugLoc.h>

namespace kutils {
    std::string value_as_string(const llvm::Value* value);

    std::string debug_loc_as_string(const llvm::DebugLoc* debug_loc);

    std::vector<std::vector<const llvm::BasicBlock *>> get_traversal_order(const llvm::Function* f);
}

#endif //LLVM_UTILS_H
