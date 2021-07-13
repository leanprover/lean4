/*
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Dany Fabian
*/

#include "library/compiler/llvm.h"
#include "library/compiler/ir_decode_helpers.h"
#include "lean/io.h"
#include "util/object_ref.h"
#include "util/string_ref.h"
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
    catch (std::string msg) {
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

    emitModuleInitializer();

    list_ref<decl> decls = list_ref<decl>(lean_ir_get_decls(env.raw()));
    for (decl decl : decls) {
        emitFunction(decl);
    }

    std::string resStr{};
    {
        raw_string_ostream outstr(resStr);
        outstr << "\n";

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

string_ref mk_module_initialization_function_name(name name) {
    return string_ref(lean_mk_module_initialization_function_name(name.to_obj_arg()));
}

array_ref<name> environment_import_names(environment env) {
    return array_ref<name>(lean_environment_import_names(env.to_obj_arg()));
}

void LeanIREmitter::emitModuleInitializer() {
    IntegerType *boolTy = IntegerType::getInt1Ty(*this);
    GlobalVariable *initialized = new GlobalVariable(*module, boolTy, false, GlobalVariable::PrivateLinkage, ConstantInt::get(boolTy, 0), "_G_initialized");

    PointerType *lean_obj_ptr = PointerType::get(runtime->getTypeByName("struct.lean_object"), 0);
    std::string initializerFuncName = mk_module_initialization_function_name(mod_name).to_std_string();
    FunctionType *initializerFuncType = FunctionType::get(lean_obj_ptr, {lean_obj_ptr}, false);
    Function *initializerFunc = Function::Create(initializerFuncType, llvm::GlobalValue::ExternalLinkage, initializerFuncName, *module);
    initializerFunc->getArg(0)->setName("world");
    BasicBlock *entry = BasicBlock::Create(*this, "entry", initializerFunc);
    BasicBlock *ifNotInitialized = BasicBlock::Create(*this, "ifNotInitialized", initializerFunc);
    BasicBlock *returnSuccess = createReturnIOSuccess();
    initializerFunc->getBasicBlockList().push_back(returnSuccess);
    builder->SetInsertPoint(entry);
    LoadInst *initializedDeref = builder->CreateLoad(initialized->getType()->getElementType(), initialized, "isInitialized");
    builder->CreateCondBr(initializedDeref, returnSuccess, ifNotInitialized);
    array_ref<name> importNames = environment_import_names(env);
    BasicBlock *next = returnSuccess;
    BasicBlock *error = BasicBlock::Create(*this, "error", initializerFunc);
    std::vector<std::tuple<CallInst *, BasicBlock *>> errorCalls{};
    for (size_t i = importNames.size(); i > 0; --i)
    {   
        std::tuple<CallInst *, BasicBlock*>importRes = emitImportInitializer(importNames[i - 1], error, next);
        errorCalls.push_back(importRes);
        next = std::get<1>(importRes);
    }
    builder->SetInsertPoint(error);
    if (errorCalls.size() > 0)
    {
        PHINode *phi = builder->CreatePHI(lean_obj_ptr, 0);
        do {
            std::tuple<CallInst *, BasicBlock *>errorCall = errorCalls.back();
            errorCalls.pop_back();
            phi->addIncoming(std::get<0>(errorCall), std::get<1>(errorCall));
        } while (errorCalls.size() > 0);
        builder->CreateRet(phi);
    }
    else {
        builder->CreateUnreachable();
    }

    builder->SetInsertPoint(ifNotInitialized);
    builder->CreateStore(ConstantInt::get(boolTy, 1), initialized);
    builder->CreateBr(next);
}

std::tuple<CallInst*, BasicBlock *>LeanIREmitter::emitImportInitializer(name importName, BasicBlock *error, BasicBlock *next) {
    BasicBlock * res = BasicBlock::Create(*this, importName.to_string(), next->getParent(), next);
    builder->SetInsertPoint(res);

    PointerType *lean_obj_ptr = PointerType::get(runtime->getTypeByName("struct.lean_object"), 0);
    std::string initializerFuncName = mk_module_initialization_function_name(importName).to_std_string();
    FunctionType *initializerFuncType = FunctionType::get(lean_obj_ptr, {lean_obj_ptr}, false);
    Function *initializerFunc = Function::Create(initializerFuncType, llvm::GlobalValue::ExternalLinkage, initializerFuncName, *module);
    CallInst *initCall = builder->CreateCall(initializerFunc, builder->CreateCall(getRuntimeFunction("lean_io_mk_world")));
    Value *isNull = builder->CreateICmp(CmpInst::Predicate::ICMP_EQ, initCall, ConstantPointerNull::get(lean_obj_ptr), "isNull");

    BasicBlock *dec = BasicBlock::Create(*this, "dec", next->getParent(), next);
    builder->CreateCondBr(isNull, error, dec);
    
    builder->SetInsertPoint(dec);
    FunctionCallee lean_dec_ref = getRuntimeFunction("lean_dec_ref");
    builder->CreateCall(lean_dec_ref, initCall);
    builder->CreateBr(next);
    
    return std::make_tuple(initCall, res);
}

BasicBlock *LeanIREmitter::createReturnIOSuccess() {
    BasicBlock *returnSuccess = BasicBlock::Create(*this, "returnSuccess");
    builder->SetInsertPoint(returnSuccess);
    FunctionCallee lean_box = getRuntimeFunction("lean_box");
    FunctionCallee lean_io_result_mk_ok = getRuntimeFunction("lean_io_result_mk_ok");
    CallInst *box_0 = builder->CreateCall(lean_box.getFunctionType(), lean_box.getCallee(), ConstantInt::get(lean_box.getFunctionType()->getParamType(0), 0));
    CallInst *world = builder->CreateCall(lean_io_result_mk_ok, box_0);
    builder->CreateRet(world);
    return returnSuccess;
}

FunctionCallee LeanIREmitter::getRuntimeFunction(std::string name) {
    Function *runtimeFunction = runtime->getFunction(name);
    if (runtimeFunction == nullptr) throw std::string("could not find runtime function: ").append(name);
    FunctionCallee res = module->getOrInsertFunction(name, runtimeFunction->getFunctionType());
    return res;
}

} // namespace ir

} // namespace lean
