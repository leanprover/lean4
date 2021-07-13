/*
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Dany Fabian
*/

#pragma once
#include "lean/object.h"
#include "util/incbin.h"
#include "util/object_ref.h"
#include "util/string_ref.h"
#include "util/array_ref.h"
#include "kernel/environment.h"
#include "library/compiler/ir.h"
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/IRBuilder.h>

using namespace llvm;

namespace lean {
extern "C" obj_res lean_list_to_array(obj_arg type, obj_arg elems);
object_ref list_to_array(object_ref list);

namespace ir {
INCBIN(LeanRuntimeBitCode, "library/compiler/libleanruntime.bc");

extern "C" obj_res lean_ir_get_decls(b_obj_arg env);
extern "C" obj_res lean_ir_emit_llvm(b_obj_arg env, b_obj_arg mod_name, obj_arg world);
extern "C" obj_res lean_name_mangle(obj_arg name, obj_arg prefix);
extern "C" obj_res lean_mk_module_initialization_function_name(obj_arg name);
extern "C" obj_res lean_environment_import_names(obj_arg name);
string_ref name_mangle(name name);
string_ref mk_module_initialization_function_name(name name);
array_ref<name> environment_import_names(environment env);

class LeanIREmitter : public LLVMContext {
    const environment env;
    const name mod_name;
    std::unique_ptr<const Module> runtime;
    std::unique_ptr<Module> module;
    std::unique_ptr<IRBuilder<>> builder;
    public:
        LeanIREmitter(environment&& env, name&& mod_name);
        string_ref emit();
    private:
        void emitFunction(decl function);
        void emitModuleInitializer();
        std::tuple<CallInst *, BasicBlock *>emitImportInitializer(name importName, BasicBlock *error, BasicBlock *next);
        BasicBlock *createReturnIOSuccess();
        FunctionCallee getRuntimeFunction(std::string name);
};

}

}
