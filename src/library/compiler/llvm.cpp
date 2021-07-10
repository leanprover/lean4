/*
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Dany Fabian
*/

#include "library/compiler/llvm.h"
#include "lean/io.h"
#include "library/compiler/ir.h"
#include "library/compiler/ir_decode_helpers.h"
#include "util/name.h"
#include "llvm/Bitcode/BitcodeReader.h"
#include "llvm/IR/Verifier.h"

namespace lean {

object_ref list_to_array(object_ref list) {
  return object_ref(lean_list_to_array(box(0), list.to_obj_arg()));
}

namespace ir {

extern "C" obj_res lean_ir_emit_llvm(b_obj_arg raw_env, b_obj_arg raw_mod_name, obj_arg) {
    environment constenv = environment(raw_env, true);
    name const mod_name  = name(raw_mod_name, true);
    const llvm::StringRef runtimeBitCode(reinterpret_cast<const char *>(&gLeanRuntimeBitCodeData), gLeanRuntimeBitCodeSize);
    const llvm::MemoryBufferRef bufferRef(runtimeBitCode, "");
    llvm::LLVMContext ctx{};

    auto maybeModule = llvm::getLazyBitcodeModule(bufferRef, ctx);
    if (auto err = maybeModule.takeError()) {
        return io_result_mk_error("nuu");
    }
    else {
        const auto module = std::move(maybeModule.get());
        llvm::Module newMod("myMod", ctx);
        newMod.setDataLayout(module->getDataLayout());
        newMod.setTargetTriple(module->getTargetTriple());
        auto types = newMod.getIdentifiedStructTypes();

        auto lean_obj = module->getTypeByName("struct.lean_object");
        llvm::PointerType *lean_obj_ptr = llvm::PointerType::get(lean_obj, 0);
        newMod.getOrInsertFunction("lean_dec", llvm::FunctionType::get(llvm::Type::getVoidTy(ctx), {lean_obj_ptr}, false));

        std::string resStr{};
        llvm::raw_string_ostream outstr(resStr);
        newMod.print(outstr, nullptr);
        outstr << "\n";
        outstr << mod_name.get_string().to_std_string() << "\n";

        object_ref decls = list_to_array(object_ref(lean_ir_get_decls(raw_env)));
        usize nDecls = array_size(decls.raw());
        outstr << nDecls << "\n";
        for (usize i = 0; i < nDecls; ++i) {
            decl decl = object_ref(array_get(decls.raw(), i), true);
            fun_id declName = decl_fun_id(decl);
            outstr << declName.to_string() << "\n";
        }

        llvm::verifyModule(newMod, &outstr);

        outstr.flush();
        return lean_io_result_mk_ok(mk_string(resStr));
    }
}

} // namespace ir

} // namespace lean
