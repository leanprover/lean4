/*
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Dany Fabian
*/

#include "library/compiler/llvm.h"
#include "library/compiler/ir_decode_helpers.h"
#include "lean/io.h"
#include "llvm/Bitcode/BitcodeReader.h"
#include "llvm/IR/Verifier.h"

namespace lean {

object_ref list_to_array(object_ref list) {
  return object_ref(lean_list_to_array(box(0), list.to_obj_arg()));
}

namespace ir {

extern "C" obj_res lean_ir_emit_llvm(b_obj_arg env, b_obj_arg mod_name, obj_arg) {
    try {
        LeanIREmitter emitter(environment(env, true), name(mod_name, true));
        return io_result_mk_ok(emitter.emit().steal());
    }
    catch (char const* msg) {
        return io_result_mk_error(msg);
    }
}

LeanIREmitter::LeanIREmitter(environment&& env, name&& mod_name) : env{env}, mod_name{mod_name} {
    const MemoryBufferRef bufferRef(StringRef(reinterpret_cast<char const*>(&gLeanRuntimeBitCodeData), gLeanRuntimeBitCodeSize), "");
    Expected<std::unique_ptr<Module>> maybeRuntime = getLazyBitcodeModule(bufferRef, *this);
    if (Error err = maybeRuntime.takeError()) {
        throw "could not parse the lean runtime";
    }

    runtime = std::move(maybeRuntime.get());
    builder = std::make_unique<IRBuilder<>>(*this);
}

string_ref LeanIREmitter::emit() {
    module = std::make_unique<Module>(mod_name.to_string(), *this);
    module->setDataLayout(runtime->getDataLayout());
    module->setTargetTriple(runtime->getTargetTriple());

    std::string resStr{};
    {
        raw_string_ostream outstr(resStr);
        outstr << "\n";

        list_ref<decl> decls = list_ref<decl>(lean_ir_get_decls(env.raw()));
        for (decl decl : decls) {
            emitFunction(decl);
        }

        module->print(outstr, nullptr);
        verifyModule(*module, &outstr);
    }

    return string_ref(resStr);
}

string_ref name_mangle(name name) {
    return string_ref(lean_name_mangle(name.to_obj_arg(), string_ref("l_").to_obj_arg()));
}

void LeanIREmitter::emitFunction(decl function) {
    fun_id declName = decl_fun_id(function);

    FunctionCallee func = module->getOrInsertFunction(name_mangle(declName).to_std_string(), Type::getInt32Ty(*this));
    Function *callee = static_cast<Function *>(func.getCallee()); 
    BasicBlock *entry = BasicBlock::Create(*this, "entry", callee);
    builder->SetInsertPoint(entry);
    builder->CreateRet(ConstantInt::get(Type::getInt32Ty(*this), 42));
}

} // namespace ir

} // namespace lean
