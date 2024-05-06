//
// Created by karth on 1/11/2024.
//

#include "llvm_utils.h"

#include <llvm/Support/raw_ostream.h>
#include "SVF-LLVM/LLVMUtil.h"
#include <llvm/ADT/SCCIterator.h>

namespace kutils {
    template<typename T>
    std::string to_string(T* obj) {
        std::string str;
        llvm::raw_string_ostream ost{str};
        obj->print(ost);
        return str;
    }

    std::string value_as_string(const llvm::Value* value) {
        return to_string(value);
    }

    std::string debug_loc_as_string(const llvm::DebugLoc* debug_loc) {
        return to_string(debug_loc);
    }

    std::vector<std::vector<const llvm::BasicBlock *>> get_traversal_order(const llvm::Function* f) {
        std::vector<std::vector<const llvm::BasicBlock *>> all_bbs;
        for (auto scc = llvm::scc_begin(f), end = llvm::scc_end(f); scc != end; ++scc) {
            std::vector<const llvm::BasicBlock *> bbs;
            for (auto bb: *scc) {
                bbs.push_back(bb);
            }
            all_bbs.insert(all_bbs.begin(), std::vector<const llvm::BasicBlock *>{bbs.rbegin(), bbs.rend()});
        }

        SPDLOG_INFO("Found {} SCC in {}", all_bbs.size(), f->getName());
        return all_bbs;
    }
}
