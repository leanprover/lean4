// Lean compiler output
// Module: Init.Lean.Compiler.IR.Basic
// Imports: Init.Data.Array Init.Lean.Data.KVMap Init.Lean.Data.Name Init.Lean.Data.Format Init.Lean.Compiler.ExternAttr
#include "runtime/lean.h"
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_Lean_IR_CtorInfo_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_MData_HasEmptyc;
lean_object* l_Lean_IR_LocalContext_getValue___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_body___boxed(lean_object*);
lean_object* l_RBNode_del___main___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(lean_object*, lean_object*);
uint8_t l_RBNode_isRed___rarg(lean_object*);
lean_object* l_Lean_IR_CtorInfo_HasBeq___closed__1;
uint8_t l_Lean_IR_FnBody_alphaEqv___main(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_erase___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_reshapeAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_addParamsRename(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_Expr_alphaEqv(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEqvAux___main___at_Lean_IR_IRType_beq___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_addVarRename(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_Arg_beq(lean_object*, lean_object*);
lean_object* l_Lean_IR_addParamsRename___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_ir_mk_uproj_expr(lean_object*, lean_object*);
lean_object* l_RBNode_find___main___at_Lean_IR_LocalContext_isJP___spec__1___boxed(lean_object*, lean_object*);
uint8_t l_Array_isEqvAux___main___at_Lean_IR_args_alphaEqv___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_IR_Index_lt(lean_object*, lean_object*);
lean_object* lean_ir_mk_vdecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_eraseJoinPointDecl(lean_object*, lean_object*);
lean_object* l_Lean_IR_LitVal_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_Arg_HasBeq;
lean_object* l_Lean_IR_AltCore_mmodifyBody___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_find___main___at_Lean_IR_VarId_alphaEqv___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_IR_LocalContext_isJP(lean_object*, lean_object*);
lean_object* l_Array_isEqvAux___main___at_Lean_IR_IRType_beq___main___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___rarg___closed__3;
lean_object* l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___at_Lean_IR_reshapeAux___main___spec__1(lean_object*);
lean_object* l_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l___private_Init_Util_1__mkPanicMessage(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_VarId_Lean_HasFormat(lean_object*);
uint8_t l_Lean_IR_IRType_isStruct(lean_object*);
lean_object* l_Lean_IR_mmodifyJPs(lean_object*);
lean_object* l_Lean_IR_mmodifyJPs___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isIrrelevant(lean_object*);
lean_object* l_Lean_IR_LocalContext_getJPParams(lean_object*, lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_IR_addParamsRename___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_CtorInfo_isScalar(lean_object*);
uint8_t l_Lean_IR_LocalContext_isParam(lean_object*, lean_object*);
uint8_t l_Lean_IR_FnBody_alphaEqv(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_IR_Inhabited;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_modifyJPs___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_VarId_HasBeq(lean_object*, lean_object*);
lean_object* lean_ir_mk_str_expr(lean_object*);
lean_object* l_Lean_IR_FnBody_alphaEqv___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Array_isEqvAux___main___at_Lean_IR_FnBody_alphaEqv___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEqvAux___main___at_Lean_IR_FnBody_alphaEqv___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_IRType_isIrrelevant___boxed(lean_object*);
lean_object* l_Lean_IR_LocalContext_addParams___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_IRType_isUnion___boxed(lean_object*);
lean_object* l_RBNode_balRight___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_ir_mk_param(lean_object*, uint8_t, lean_object*);
uint8_t l_Lean_IR_IRType_isObj(lean_object*);
lean_object* l_Lean_IR_Arg_alphaEqv___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_JoinPointId_Hashable___boxed(lean_object*);
lean_object* l_Lean_IR_Arg_HasBeq___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_IR_Alt_isDefault___boxed(lean_object*);
lean_object* l_Lean_IR_AltCore_body___boxed(lean_object*);
lean_object* l_Lean_IR_LocalContext_addParams(lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_resultType(lean_object*);
lean_object* l_Lean_IR_Decl_name(lean_object*);
lean_object* l_Lean_IR_Arg_Inhabited;
lean_object* l_Lean_IR_VarId_Hashable___boxed(lean_object*);
lean_object* l_Lean_IR_LocalContext_getType(lean_object*, lean_object*);
lean_object* l_Lean_IR_AltCore_body(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_ir_mk_papp_expr(lean_object*, lean_object*);
uint8_t l_Lean_IR_args_alphaEqv(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Arg_hasAeqv___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_RBNode_erase___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_IR_LitVal_HasBeq;
lean_object* l_Array_isEqvAux___main___at_Lean_IR_args_alphaEqv___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_VarId_alphaEqv(lean_object*, lean_object*, lean_object*);
lean_object* lean_ir_mk_fapp_expr(lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_isLocalVar___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_flattenAux___main(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_IR_CtorInfo_isRef(lean_object*);
lean_object* l_Lean_IR_CtorInfo_isRef___boxed(lean_object*);
lean_object* l_Lean_IR_VarId_alphaEqv___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_mmodifyJPs___spec__1___rarg___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_mmodifyJPs___spec__1___rarg___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_addParamRename(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_isTerminal___boxed(lean_object*);
lean_object* lean_ir_mk_jdecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_addJP(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_LocalContext_addParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_getJPParams___boxed(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_mmodifyJPs___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_getJPBody___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_alphaEqv___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_mkIf___closed__3;
lean_object* l_Lean_IR_AltCore_modifyBody(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_FnBody_isTerminal(lean_object*);
lean_object* l_Lean_IR_Decl_params___boxed(lean_object*);
uint8_t l_Lean_IR_FnBody_beq(lean_object*, lean_object*);
lean_object* l_Lean_IR_mkIf___closed__5;
lean_object* l_Lean_IR_args_hasAeqv___closed__1;
lean_object* l_Lean_IR_LocalContext_getValue(lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_addParam(lean_object*, lean_object*);
lean_object* l_Nat_repr(lean_object*);
lean_object* l_Lean_IR_Expr_hasAeqv___closed__1;
lean_object* l_Lean_IR_paramInh;
lean_object* l_Lean_IR_IRType_isObj___boxed(lean_object*);
lean_object* l_Lean_IR_IRType_HasBeq;
uint8_t l_Lean_IR_IRType_beq(lean_object*, lean_object*);
lean_object* l_Lean_IR_args_alphaEqv___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_IR_LitVal_HasBeq___closed__1;
lean_object* l_Lean_IR_push(lean_object*, lean_object*);
lean_object* l_Lean_IR_Expr_alphaEqv___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_ir_mk_alt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_IRType_beq___main___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_mkIf(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_split(lean_object*);
lean_object* l_Lean_IR_Decl_name___boxed(lean_object*);
lean_object* lean_ir_mk_num_expr(lean_object*);
uint8_t l_Lean_IR_IRType_beq___main(lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_nil;
lean_object* l_Lean_IR_CtorInfo_HasBeq;
lean_object* l_Lean_IR_IRType_HasBeq___closed__1;
lean_object* l_Lean_IR_Arg_hasAeqv;
lean_object* l_Lean_IR_flattenAux(lean_object*, lean_object*);
lean_object* l_Lean_IR_VarId_hasAeqv;
lean_object* lean_ir_mk_app_expr(lean_object*, lean_object*);
lean_object* l_Lean_IR_Expr_hasAeqv;
lean_object* l_Lean_IR_AltCore_mmodifyBody___rarg___closed__1;
lean_object* l_RBNode_insert___at_Lean_IR_LocalContext_addLocal___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_mkIf___closed__4;
lean_object* lean_ir_mk_proj_expr(lean_object*, lean_object*);
lean_object* l_Lean_IR_Alt_ctor(lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_HasBeq___closed__1;
lean_object* l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isUnion(lean_object*);
lean_object* lean_ir_mk_case(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_RBNode_ins___main___at_Lean_IR_mkIndexSet___spec__2(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_Decl_isExtern(lean_object*);
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_IR_addParamsRename___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_VarId_HasBeq___boxed(lean_object*, lean_object*);
uint8_t l_Array_isEqvAux___main___at_Lean_IR_IRType_beq___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_MData_empty;
lean_object* lean_ir_mk_extern_decl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_ir_mk_ctor_expr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_Inhabited;
uint8_t l_Lean_IR_LocalContext_contains(lean_object*, lean_object*);
uint8_t l_Lean_IR_JoinPointId_HasBeq(lean_object*, lean_object*);
lean_object* l_Lean_IR_AltCore_mmodifyBody(lean_object*);
lean_object* l_Lean_IR_JoinPointId_HasBeq___boxed(lean_object*, lean_object*);
extern lean_object* l_Bool_HasRepr___closed__1;
lean_object* l_RBNode_del___main___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2___boxed(lean_object*, lean_object*);
uint8_t l_Lean_IR_LitVal_beq(lean_object*, lean_object*);
lean_object* l_Lean_IR_AltCore_setBody(lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_contains___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_setBody(lean_object*, lean_object*);
lean_object* l_Lean_IR_Index_lt___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_args_hasAeqv;
lean_object* l_Lean_IR_CtorInfo_isScalar___boxed(lean_object*);
uint8_t l_Lean_IR_LocalContext_isLocalVar(lean_object*, lean_object*);
lean_object* l_RBNode_appendTrees___main___rarg(lean_object*, lean_object*);
extern lean_object* l_Bool_HasRepr___closed__2;
lean_object* l_Lean_IR_FnBody_flatten(lean_object*);
lean_object* lean_ir_mk_var_arg(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_RBNode_balLeft___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_altInh;
lean_object* lean_ir_mk_jmp(lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_isJP___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_mkIf___closed__2;
lean_object* l_Lean_IR_mkIf___closed__1;
lean_object* l_Lean_IR_mkIndexSet(lean_object*);
lean_object* l_Lean_IR_reshape(lean_object*, lean_object*);
lean_object* l_Lean_IR_JoinPointId_HasToString___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_IR_LocalContext_addParams___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_reshapeAux___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_resultType___boxed(lean_object*);
lean_object* l_Lean_IR_LocalContext_addLocal(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_CtorInfo_beq(lean_object*, lean_object*);
lean_object* l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_IRType_isStruct___boxed(lean_object*);
lean_object* l_RBNode_setBlack___rarg(lean_object*);
extern lean_object* l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___rarg___closed__2;
extern lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l_Lean_IR_FnBody_HasBeq;
lean_object* l_Array_isEqvAux___main___at_Lean_IR_IRType_beq___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_insert___at_Lean_IR_addVarRename___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* lean_ir_mk_uset(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_vsetInh;
lean_object* l_RBNode_find___main___at_Lean_IR_LocalContext_isJP___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_IR_modifyJPs(lean_object*, lean_object*);
lean_object* l_Lean_IR_VarIdSet_Inhabited;
lean_object* l_Lean_IR_LocalContext_isParam___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_VarId_HasToString___closed__1;
lean_object* lean_ir_mk_ret(lean_object*);
lean_object* lean_ir_mk_sproj_expr(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_getJPBody(lean_object*, lean_object*);
lean_object* lean_ir_mk_sset(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_VarId_HasToString(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_mmodifyJPs___spec__1(lean_object*);
lean_object* l_Lean_IR_FnBody_resetBody(lean_object*);
uint8_t l_Lean_IR_Arg_alphaEqv(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_altInh___closed__1;
lean_object* l_Lean_IR_mkIf___closed__6;
lean_object* l_Lean_IR_IRType_beq___boxed(lean_object*, lean_object*);
lean_object* lean_ir_mk_unreachable(lean_object*);
lean_object* l_Lean_IR_VarId_hasAeqv___closed__1;
lean_object* l_Lean_IR_paramInh___closed__1;
lean_object* l_Lean_IR_Arg_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_mkParam___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_JoinPointId_HasToString(lean_object*);
uint8_t l_Lean_KVMap_eqv(lean_object*, lean_object*);
size_t l_Lean_IR_VarId_Hashable(lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_Inhabited___closed__1;
uint8_t l_Lean_IR_Alt_isDefault(lean_object*);
lean_object* l_Lean_IR_LocalContext_getType___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_body(lean_object*);
lean_object* lean_ir_mk_decl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_find___main___at_Lean_IR_VarId_alphaEqv___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_params(lean_object*);
lean_object* l_Lean_IR_JoinPointId_Lean_HasFormat(lean_object*);
lean_object* l_Lean_IR_FnBody_beq___boxed(lean_object*, lean_object*);
size_t l_Lean_IR_JoinPointId_Hashable(lean_object*);
lean_object* l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___at_Lean_IR_reshapeAux___main___spec__1___closed__1;
lean_object* l_Array_umapMAux___main___at_Lean_IR_mmodifyJPs___spec__1___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Alt_default(lean_object*);
extern lean_object* l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___rarg___closed__1;
uint8_t l_RBNode_isBlack___rarg(lean_object*);
lean_object* l_Lean_IR_Decl_isExtern___boxed(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_eraseJoinPointDecl___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_IR_IRType_isScalar___boxed(lean_object*);
uint8_t l_Lean_IR_IRType_isScalar(lean_object*);
uint8_t l_Lean_IR_Index_lt(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_lt(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_IR_Index_lt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_Index_lt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_IR_VarId_HasBeq(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_IR_VarId_HasBeq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_VarId_HasBeq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* _init_l_Lean_IR_VarId_HasToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("x_");
return x_1;
}
}
lean_object* l_Lean_IR_VarId_HasToString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Nat_repr(x_1);
x_3 = l_Lean_IR_VarId_HasToString___closed__1;
x_4 = lean_string_append(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_IR_VarId_Lean_HasFormat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Nat_repr(x_1);
x_3 = l_Lean_IR_VarId_HasToString___closed__1;
x_4 = lean_string_append(x_3, x_2);
lean_dec(x_2);
x_5 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
size_t l_Lean_IR_VarId_Hashable(lean_object* x_1) {
_start:
{
size_t x_2; 
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
lean_object* l_Lean_IR_VarId_Hashable___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_VarId_Hashable(x_1);
lean_dec(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
uint8_t l_Lean_IR_JoinPointId_HasBeq(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_IR_JoinPointId_HasBeq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_JoinPointId_HasBeq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* _init_l_Lean_IR_JoinPointId_HasToString___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("block_");
return x_1;
}
}
lean_object* l_Lean_IR_JoinPointId_HasToString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Nat_repr(x_1);
x_3 = l_Lean_IR_JoinPointId_HasToString___closed__1;
x_4 = lean_string_append(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_IR_JoinPointId_Lean_HasFormat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Nat_repr(x_1);
x_3 = l_Lean_IR_JoinPointId_HasToString___closed__1;
x_4 = lean_string_append(x_3, x_2);
lean_dec(x_2);
x_5 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
size_t l_Lean_IR_JoinPointId_Hashable(lean_object* x_1) {
_start:
{
size_t x_2; 
x_2 = lean_usize_of_nat(x_1);
return x_2;
}
}
lean_object* l_Lean_IR_JoinPointId_Hashable___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_JoinPointId_Hashable(x_1);
lean_dec(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_MData_empty() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* _init_l_Lean_IR_MData_HasEmptyc() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
uint8_t l_Array_isEqvAux___main___at_Lean_IR_IRType_beq___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
x_9 = 1;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_fget(x_4, x_6);
x_11 = lean_array_fget(x_5, x_6);
x_12 = l_Lean_IR_IRType_beq___main(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_6);
x_13 = 0;
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_3 = lean_box(0);
x_6 = x_15;
goto _start;
}
}
}
}
uint8_t l_Array_isEqvAux___main___at_Lean_IR_IRType_beq___main___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
x_9 = 1;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_fget(x_4, x_6);
x_11 = lean_array_fget(x_5, x_6);
x_12 = l_Lean_IR_IRType_beq___main(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_6);
x_13 = 0;
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_3 = lean_box(0);
x_6 = x_15;
goto _start;
}
}
}
}
uint8_t l_Lean_IR_IRType_beq___main(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
case 2:
{
if (lean_obj_tag(x_2) == 2)
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
}
case 3:
{
if (lean_obj_tag(x_2) == 3)
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
case 4:
{
if (lean_obj_tag(x_2) == 4)
{
uint8_t x_11; 
x_11 = 1;
return x_11;
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
case 5:
{
if (lean_obj_tag(x_2) == 5)
{
uint8_t x_13; 
x_13 = 1;
return x_13;
}
else
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
}
case 6:
{
if (lean_obj_tag(x_2) == 6)
{
uint8_t x_15; 
x_15 = 1;
return x_15;
}
else
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
case 7:
{
if (lean_obj_tag(x_2) == 7)
{
uint8_t x_17; 
x_17 = 1;
return x_17;
}
else
{
uint8_t x_18; 
x_18 = 0;
return x_18;
}
}
case 8:
{
if (lean_obj_tag(x_2) == 8)
{
uint8_t x_19; 
x_19 = 1;
return x_19;
}
else
{
uint8_t x_20; 
x_20 = 0;
return x_20;
}
}
case 9:
{
if (lean_obj_tag(x_2) == 9)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_2, 1);
if (lean_obj_tag(x_21) == 0)
{
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_33; 
x_33 = lean_box(0);
x_25 = x_33;
goto block_32;
}
else
{
uint8_t x_34; 
x_34 = 0;
return x_34;
}
}
else
{
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_35; 
x_35 = 0;
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_21, 0);
x_37 = lean_ctor_get(x_23, 0);
x_38 = lean_name_eq(x_36, x_37);
if (x_38 == 0)
{
uint8_t x_39; 
x_39 = 0;
return x_39;
}
else
{
lean_object* x_40; 
x_40 = lean_box(0);
x_25 = x_40;
goto block_32;
}
}
}
block_32:
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_25);
x_26 = lean_array_get_size(x_22);
x_27 = lean_array_get_size(x_24);
x_28 = lean_nat_dec_eq(x_26, x_27);
lean_dec(x_27);
lean_dec(x_26);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = 0;
return x_29;
}
else
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_unsigned_to_nat(0u);
x_31 = l_Array_isEqvAux___main___at_Lean_IR_IRType_beq___main___spec__1(x_22, x_24, lean_box(0), x_22, x_24, x_30);
return x_31;
}
}
}
else
{
uint8_t x_41; 
x_41 = 0;
return x_41;
}
}
default: 
{
if (lean_obj_tag(x_2) == 10)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_42 = lean_ctor_get(x_1, 0);
x_43 = lean_ctor_get(x_1, 1);
x_44 = lean_ctor_get(x_2, 0);
x_45 = lean_ctor_get(x_2, 1);
x_46 = lean_name_eq(x_42, x_44);
if (x_46 == 0)
{
uint8_t x_47; 
x_47 = 0;
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_array_get_size(x_43);
x_49 = lean_array_get_size(x_45);
x_50 = lean_nat_dec_eq(x_48, x_49);
lean_dec(x_49);
lean_dec(x_48);
if (x_50 == 0)
{
uint8_t x_51; 
x_51 = 0;
return x_51;
}
else
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_unsigned_to_nat(0u);
x_53 = l_Array_isEqvAux___main___at_Lean_IR_IRType_beq___main___spec__2(x_43, x_45, lean_box(0), x_43, x_45, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
x_54 = 0;
return x_54;
}
}
}
}
}
lean_object* l_Array_isEqvAux___main___at_Lean_IR_IRType_beq___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_isEqvAux___main___at_Lean_IR_IRType_beq___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Array_isEqvAux___main___at_Lean_IR_IRType_beq___main___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_isEqvAux___main___at_Lean_IR_IRType_beq___main___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Lean_IR_IRType_beq___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_IRType_beq___main(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_IR_IRType_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_IR_IRType_beq___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_IR_IRType_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_IRType_beq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* _init_l_Lean_IR_IRType_HasBeq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_IRType_beq___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_IR_IRType_HasBeq() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_IRType_HasBeq___closed__1;
return x_1;
}
}
uint8_t l_Lean_IR_IRType_isScalar(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 6:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
case 7:
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
case 8:
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
case 9:
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
case 10:
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
default: 
{
uint8_t x_7; 
x_7 = 1;
return x_7;
}
}
}
}
lean_object* l_Lean_IR_IRType_isScalar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_IRType_isScalar(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Lean_IR_IRType_isObj(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 7:
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
case 8:
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
default: 
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
}
}
lean_object* l_Lean_IR_IRType_isObj___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_IRType_isObj(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Lean_IR_IRType_isIrrelevant(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
lean_object* l_Lean_IR_IRType_isIrrelevant___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_IRType_isIrrelevant(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Lean_IR_IRType_isStruct(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 9)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
lean_object* l_Lean_IR_IRType_isStruct___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_IRType_isStruct(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Lean_IR_IRType_isUnion(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 10)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
lean_object* l_Lean_IR_IRType_isUnion___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_IRType_isUnion(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Lean_IR_Arg_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_nat_dec_eq(x_3, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
else
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
}
}
}
lean_object* l_Lean_IR_Arg_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_Arg_beq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* _init_l_Lean_IR_Arg_HasBeq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_Arg_beq___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_IR_Arg_HasBeq() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_Arg_HasBeq___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_IR_Arg_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(1);
return x_1;
}
}
lean_object* lean_ir_mk_var_arg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
uint8_t l_Lean_IR_LitVal_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_nat_dec_eq(x_3, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_string_dec_eq(x_8, x_9);
return x_10;
}
}
}
}
lean_object* l_Lean_IR_LitVal_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_LitVal_beq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* _init_l_Lean_IR_LitVal_HasBeq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_LitVal_beq___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_IR_LitVal_HasBeq() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_LitVal_HasBeq___closed__1;
return x_1;
}
}
uint8_t l_Lean_IR_CtorInfo_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_1, 3);
x_7 = lean_ctor_get(x_1, 4);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_ctor_get(x_2, 2);
x_11 = lean_ctor_get(x_2, 3);
x_12 = lean_ctor_get(x_2, 4);
x_13 = lean_name_eq(x_3, x_8);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = 0;
return x_14;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_eq(x_4, x_9);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_eq(x_5, x_10);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = 0;
return x_18;
}
else
{
uint8_t x_19; 
x_19 = lean_nat_dec_eq(x_6, x_11);
if (x_19 == 0)
{
uint8_t x_20; 
x_20 = 0;
return x_20;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_eq(x_7, x_12);
return x_21;
}
}
}
}
}
}
lean_object* l_Lean_IR_CtorInfo_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_CtorInfo_beq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* _init_l_Lean_IR_CtorInfo_HasBeq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_CtorInfo_beq___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_IR_CtorInfo_HasBeq() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_CtorInfo_HasBeq___closed__1;
return x_1;
}
}
uint8_t l_Lean_IR_CtorInfo_isRef(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 2);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_lt(x_3, x_2);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_1, 3);
x_6 = lean_nat_dec_lt(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_1, 4);
x_8 = lean_nat_dec_lt(x_3, x_7);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = 1;
return x_10;
}
}
}
lean_object* l_Lean_IR_CtorInfo_isRef___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_CtorInfo_isRef(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
uint8_t l_Lean_IR_CtorInfo_isScalar(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_IR_CtorInfo_isRef(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
}
lean_object* l_Lean_IR_CtorInfo_isScalar___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_CtorInfo_isScalar(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* lean_ir_mk_ctor_expr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
lean_object* lean_ir_mk_proj_expr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* lean_ir_mk_uproj_expr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* lean_ir_mk_sproj_expr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* lean_ir_mk_fapp_expr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* lean_ir_mk_papp_expr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* lean_ir_mk_app_expr(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* lean_ir_mk_num_expr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
x_3 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
lean_object* lean_ir_mk_str_expr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
x_3 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_paramInh___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; uint32_t x_4; uint16_t x_5; uint8_t x_6; lean_object* x_7; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = 0;
x_3 = lean_box(7);
x_4 = 0;
x_5 = 0;
x_6 = 0;
x_7 = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 6, x_2);
lean_ctor_set_uint32(x_7, sizeof(void*)*2, x_4);
lean_ctor_set_uint16(x_7, sizeof(void*)*2 + 4, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 7, x_6);
return x_7;
}
}
lean_object* _init_l_Lean_IR_paramInh() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_paramInh___closed__1;
return x_1;
}
}
lean_object* lean_ir_mk_param(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; uint16_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = 0;
x_5 = 0;
x_6 = 0;
x_7 = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_3);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 6, x_2);
lean_ctor_set_uint32(x_7, sizeof(void*)*2, x_4);
lean_ctor_set_uint16(x_7, sizeof(void*)*2 + 4, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*2 + 7, x_6);
return x_7;
}
}
lean_object* l_Lean_IR_mkParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = lean_ir_mk_param(x_1, x_4, x_3);
return x_5;
}
}
lean_object* _init_l_Lean_IR_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(13);
return x_1;
}
}
lean_object* _init_l_Lean_IR_FnBody_nil() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(13);
return x_1;
}
}
lean_object* lean_ir_mk_vdecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
lean_object* lean_ir_mk_jdecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
lean_object* lean_ir_mk_uset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
lean_object* lean_ir_mk_sset(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
return x_7;
}
}
lean_object* lean_ir_mk_case(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(7);
x_5 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_3);
return x_5;
}
}
lean_object* lean_ir_mk_ret(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* lean_ir_mk_jmp(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* lean_ir_mk_unreachable(lean_object* x_1) {
_start:
{
lean_object* x_2; 
lean_dec(x_1);
x_2 = lean_box(13);
return x_2;
}
}
lean_object* l_Lean_IR_Alt_ctor(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Lean_IR_Alt_default(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_altInh___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(13);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_altInh() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_altInh___closed__1;
return x_1;
}
}
uint8_t l_Lean_IR_FnBody_isTerminal(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 10:
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
case 11:
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
case 12:
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
case 13:
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
default: 
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
}
}
}
lean_object* l_Lean_IR_FnBody_isTerminal___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_FnBody_isTerminal(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_IR_FnBody_body(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 3:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
return x_2;
}
case 5:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 5);
lean_inc(x_3);
return x_3;
}
case 6:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
return x_4;
}
case 7:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
return x_5;
}
case 8:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
return x_6;
}
case 9:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
return x_7;
}
case 10:
{
lean_inc(x_1);
return x_1;
}
case 11:
{
lean_inc(x_1);
return x_1;
}
case 12:
{
lean_inc(x_1);
return x_1;
}
case 13:
{
return x_1;
}
default: 
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
return x_8;
}
}
}
}
lean_object* l_Lean_IR_FnBody_body___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_FnBody_body(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_IR_FnBody_setBody(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 3);
lean_dec(x_4);
lean_ctor_set(x_1, 3, x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
lean_ctor_set(x_8, 3, x_2);
return x_8;
}
}
case 1:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_1, 3);
lean_dec(x_10);
lean_ctor_set(x_1, 3, x_2);
return x_1;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_1);
x_14 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set(x_14, 3, x_2);
return x_14;
}
}
case 2:
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_1);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_1, 3);
lean_dec(x_16);
lean_ctor_set(x_1, 3, x_2);
return x_1;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get(x_1, 1);
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_1);
x_20 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_19);
lean_ctor_set(x_20, 3, x_2);
return x_20;
}
}
case 3:
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_1, 2);
lean_dec(x_22);
lean_ctor_set(x_1, 2, x_2);
return x_1;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_1, 0);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_1);
x_25 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_2);
return x_25;
}
}
case 4:
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_1);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_1, 3);
lean_dec(x_27);
lean_ctor_set(x_1, 3, x_2);
return x_1;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_1, 0);
x_29 = lean_ctor_get(x_1, 1);
x_30 = lean_ctor_get(x_1, 2);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_1);
x_31 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_31, 2, x_30);
lean_ctor_set(x_31, 3, x_2);
return x_31;
}
}
case 5:
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_1);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_1, 5);
lean_dec(x_33);
lean_ctor_set(x_1, 5, x_2);
return x_1;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_1, 0);
x_35 = lean_ctor_get(x_1, 1);
x_36 = lean_ctor_get(x_1, 2);
x_37 = lean_ctor_get(x_1, 3);
x_38 = lean_ctor_get(x_1, 4);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_1);
x_39 = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_35);
lean_ctor_set(x_39, 2, x_36);
lean_ctor_set(x_39, 3, x_37);
lean_ctor_set(x_39, 4, x_38);
lean_ctor_set(x_39, 5, x_2);
return x_39;
}
}
case 6:
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_1);
if (x_40 == 0)
{
lean_object* x_41; uint32_t x_42; uint16_t x_43; 
x_41 = lean_ctor_get(x_1, 2);
lean_dec(x_41);
x_42 = 0;
x_43 = 0;
lean_ctor_set(x_1, 2, x_2);
lean_ctor_set_uint32(x_1, sizeof(void*)*3, x_42);
lean_ctor_set_uint16(x_1, sizeof(void*)*3 + 4, x_43);
return x_1;
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_47; uint32_t x_48; uint16_t x_49; lean_object* x_50; 
x_44 = lean_ctor_get(x_1, 0);
x_45 = lean_ctor_get(x_1, 1);
x_46 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 6);
x_47 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 7);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_1);
x_48 = 0;
x_49 = 0;
x_50 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_50, 0, x_44);
lean_ctor_set(x_50, 1, x_45);
lean_ctor_set(x_50, 2, x_2);
lean_ctor_set_uint8(x_50, sizeof(void*)*3 + 6, x_46);
lean_ctor_set_uint8(x_50, sizeof(void*)*3 + 7, x_47);
lean_ctor_set_uint32(x_50, sizeof(void*)*3, x_48);
lean_ctor_set_uint16(x_50, sizeof(void*)*3 + 4, x_49);
return x_50;
}
}
case 7:
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_1);
if (x_51 == 0)
{
lean_object* x_52; uint32_t x_53; uint16_t x_54; 
x_52 = lean_ctor_get(x_1, 2);
lean_dec(x_52);
x_53 = 0;
x_54 = 0;
lean_ctor_set(x_1, 2, x_2);
lean_ctor_set_uint32(x_1, sizeof(void*)*3, x_53);
lean_ctor_set_uint16(x_1, sizeof(void*)*3 + 4, x_54);
return x_1;
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_58; uint32_t x_59; uint16_t x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_1, 0);
x_56 = lean_ctor_get(x_1, 1);
x_57 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 6);
x_58 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 7);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_1);
x_59 = 0;
x_60 = 0;
x_61 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_61, 0, x_55);
lean_ctor_set(x_61, 1, x_56);
lean_ctor_set(x_61, 2, x_2);
lean_ctor_set_uint8(x_61, sizeof(void*)*3 + 6, x_57);
lean_ctor_set_uint8(x_61, sizeof(void*)*3 + 7, x_58);
lean_ctor_set_uint32(x_61, sizeof(void*)*3, x_59);
lean_ctor_set_uint16(x_61, sizeof(void*)*3 + 4, x_60);
return x_61;
}
}
case 8:
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_1);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_1, 1);
lean_dec(x_63);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_1, 0);
lean_inc(x_64);
lean_dec(x_1);
x_65 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_2);
return x_65;
}
}
case 9:
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_1);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_1, 1);
lean_dec(x_67);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_1, 0);
lean_inc(x_68);
lean_dec(x_1);
x_69 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_2);
return x_69;
}
}
default: 
{
lean_dec(x_2);
return x_1;
}
}
}
}
lean_object* l_Lean_IR_FnBody_resetBody(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(13);
x_3 = l_Lean_IR_FnBody_setBody(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_IR_FnBody_split(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_IR_FnBody_body(x_1);
x_3 = lean_box(13);
x_4 = l_Lean_IR_FnBody_setBody(x_1, x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_2);
return x_5;
}
}
lean_object* l_Lean_IR_AltCore_body(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
return x_3;
}
}
}
lean_object* l_Lean_IR_AltCore_body___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_AltCore_body(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_IR_AltCore_setBody(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_dec(x_4);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
}
else
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_1, 0);
lean_dec(x_8);
lean_ctor_set(x_1, 0, x_2);
return x_1;
}
else
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_2);
return x_9;
}
}
}
}
lean_object* l_Lean_IR_AltCore_modifyBody(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 1, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_2);
x_8 = lean_apply_1(x_1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_apply_1(x_1, x_11);
lean_ctor_set(x_2, 0, x_12);
return x_2;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_apply_1(x_1, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
lean_object* _init_l_Lean_IR_AltCore_mmodifyBody___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_Alt_default), 1, 0);
return x_1;
}
}
lean_object* l_Lean_IR_AltCore_mmodifyBody___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_IR_Alt_ctor), 2, 1);
lean_closure_set(x_9, 0, x_4);
x_10 = lean_apply_1(x_2, x_5);
x_11 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_9, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_apply_1(x_2, x_12);
x_17 = l_Lean_IR_AltCore_mmodifyBody___rarg___closed__1;
x_18 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_17, x_16);
return x_18;
}
}
}
lean_object* l_Lean_IR_AltCore_mmodifyBody(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_AltCore_mmodifyBody___rarg), 3, 0);
return x_2;
}
}
uint8_t l_Lean_IR_Alt_isDefault(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
}
}
lean_object* l_Lean_IR_Alt_isDefault___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_Alt_isDefault(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* l_Lean_IR_push(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(13);
x_4 = l_Lean_IR_FnBody_setBody(x_2, x_3);
x_5 = lean_array_push(x_1, x_4);
return x_5;
}
}
lean_object* l_Lean_IR_flattenAux___main(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_IR_FnBody_body(x_1);
x_5 = l_Lean_IR_push(x_2, x_1);
x_1 = x_4;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_1);
return x_7;
}
}
}
lean_object* l_Lean_IR_flattenAux(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_flattenAux___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_IR_FnBody_flatten(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Array_empty___closed__1;
x_3 = l_Lean_IR_flattenAux___main(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___at_Lean_IR_reshapeAux___main___spec__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(13);
x_2 = l_Array_empty___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___at_Lean_IR_reshapeAux___main___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Nat_repr(x_1);
x_3 = l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___rarg___closed__1;
x_4 = lean_string_append(x_3, x_2);
lean_dec(x_2);
x_5 = l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___rarg___closed__2;
x_6 = lean_string_append(x_4, x_5);
x_7 = l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___rarg___closed__3;
x_8 = lean_unsigned_to_nat(143u);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l___private_Init_Util_1__mkPanicMessage(x_7, x_8, x_9, x_6);
lean_dec(x_6);
x_11 = l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___at_Lean_IR_reshapeAux___main___spec__1___closed__1;
x_12 = lean_panic_fn(x_11, x_10);
return x_12;
}
}
lean_object* l_Lean_IR_reshapeAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_14; uint8_t x_15; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
lean_dec(x_2);
x_14 = lean_array_get_size(x_1);
x_15 = lean_nat_dec_lt(x_7, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_1);
lean_inc(x_7);
x_16 = l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___at_Lean_IR_reshapeAux___main___spec__1(x_7);
x_8 = x_16;
goto block_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_array_fget(x_1, x_7);
x_18 = lean_box(13);
x_19 = lean_array_fset(x_1, x_7, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_8 = x_20;
goto block_13;
}
block_13:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_IR_FnBody_setBody(x_9, x_3);
x_1 = x_10;
x_2 = x_7;
x_3 = x_11;
goto _start;
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
lean_object* l_Lean_IR_reshapeAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_reshapeAux___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_IR_reshape(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_array_get_size(x_1);
x_4 = l_Lean_IR_reshapeAux___main(x_1, x_3, x_2);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_modifyJPs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = l_Array_empty___closed__1;
x_7 = x_3;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_array_fget(x_3, x_2);
x_9 = lean_box(0);
x_10 = x_9;
x_11 = lean_array_fset(x_3, x_2, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_8, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_8, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_8, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_8, 3);
lean_inc(x_22);
lean_inc(x_1);
x_23 = lean_apply_1(x_1, x_21);
x_24 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_23);
lean_ctor_set(x_24, 3, x_22);
x_14 = x_24;
goto block_18;
}
else
{
lean_inc(x_8);
x_14 = x_8;
goto block_18;
}
block_18:
{
lean_object* x_15; lean_object* x_16; 
x_15 = x_14;
lean_dec(x_8);
x_16 = lean_array_fset(x_11, x_2, x_15);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_16;
goto _start;
}
}
}
}
lean_object* l_Lean_IR_modifyJPs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_umapMAux___main___at_Lean_IR_modifyJPs___spec__1(x_2, x_3, x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_mmodifyJPs___spec__1___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_add(x_1, x_7);
x_9 = x_6;
x_10 = lean_array_fset(x_3, x_1, x_9);
x_11 = l_Array_umapMAux___main___at_Lean_IR_mmodifyJPs___spec__1___rarg(x_4, x_5, x_8, x_10);
return x_11;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_mmodifyJPs___spec__1___rarg___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_3);
lean_ctor_set(x_8, 2, x_5);
lean_ctor_set(x_8, 3, x_4);
x_9 = lean_apply_2(x_7, lean_box(0), x_8);
return x_9;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_mmodifyJPs___spec__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_4);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Array_empty___closed__1;
x_10 = x_4;
x_11 = lean_apply_2(x_8, lean_box(0), x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_array_fget(x_4, x_3);
x_13 = lean_box(0);
x_14 = x_13;
x_15 = lean_array_fset(x_4, x_3, x_14);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_12);
x_17 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_IR_mmodifyJPs___spec__1___rarg___lambda__1___boxed), 6, 5);
lean_closure_set(x_17, 0, x_3);
lean_closure_set(x_17, 1, x_12);
lean_closure_set(x_17, 2, x_15);
lean_closure_set(x_17, 3, x_1);
lean_closure_set(x_17, 4, x_2);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_ctor_get(x_12, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_12, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_12, 2);
lean_inc(x_26);
x_27 = lean_ctor_get(x_12, 3);
lean_inc(x_27);
lean_dec(x_12);
x_28 = lean_apply_1(x_2, x_26);
x_29 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_IR_mmodifyJPs___spec__1___rarg___lambda__2), 5, 4);
lean_closure_set(x_29, 0, x_1);
lean_closure_set(x_29, 1, x_24);
lean_closure_set(x_29, 2, x_25);
lean_closure_set(x_29, 3, x_27);
lean_inc(x_16);
x_30 = lean_apply_4(x_16, lean_box(0), lean_box(0), x_28, x_29);
x_31 = lean_apply_4(x_16, lean_box(0), lean_box(0), x_30, x_17);
return x_31;
}
else
{
lean_dec(x_2);
x_18 = x_13;
goto block_23;
}
block_23:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_18);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_apply_2(x_20, lean_box(0), x_12);
x_22 = lean_apply_4(x_16, lean_box(0), lean_box(0), x_21, x_17);
return x_22;
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_mmodifyJPs___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_IR_mmodifyJPs___spec__1___rarg), 4, 0);
return x_2;
}
}
lean_object* l_Lean_IR_mmodifyJPs___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_umapMAux___main___at_Lean_IR_mmodifyJPs___spec__1___rarg(x_1, x_3, x_4, x_2);
return x_5;
}
}
lean_object* l_Lean_IR_mmodifyJPs(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_mmodifyJPs___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_mmodifyJPs___spec__1___rarg___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_umapMAux___main___at_Lean_IR_mmodifyJPs___spec__1___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* lean_ir_mk_alt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
lean_object* _init_l_Lean_IR_Decl_Inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_box(0);
x_2 = l_Array_empty___closed__1;
x_3 = lean_box(6);
x_4 = lean_box(13);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_IR_Decl_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_Decl_Inhabited___closed__1;
return x_1;
}
}
lean_object* l_Lean_IR_Decl_name(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
lean_object* l_Lean_IR_Decl_name___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_Decl_name(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_IR_Decl_params(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
lean_object* l_Lean_IR_Decl_params___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_Decl_params(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_IR_Decl_resultType(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 2);
lean_inc(x_2);
return x_2;
}
}
lean_object* l_Lean_IR_Decl_resultType___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_Decl_resultType(x_1);
lean_dec(x_1);
return x_2;
}
}
uint8_t l_Lean_IR_Decl_isExtern(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
}
}
lean_object* l_Lean_IR_Decl_isExtern___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_Decl_isExtern(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* lean_ir_mk_decl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
lean_object* lean_ir_mk_extern_decl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_4);
return x_5;
}
}
lean_object* _init_l_Lean_IR_vsetInh() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* l_RBNode_ins___main___at_Lean_IR_mkIndexSet___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; uint32_t x_5; uint16_t x_6; uint8_t x_7; lean_object* x_8; 
x_4 = 0;
x_5 = 0;
x_6 = 0;
x_7 = 0;
x_8 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 2, x_3);
lean_ctor_set(x_8, 3, x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*4 + 6, x_4);
lean_ctor_set_uint32(x_8, sizeof(void*)*4, x_5);
lean_ctor_set_uint16(x_8, sizeof(void*)*4 + 4, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*4 + 7, x_7);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 6);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_1, 2);
x_14 = lean_ctor_get(x_1, 3);
x_15 = lean_nat_dec_lt(x_2, x_12);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = lean_nat_dec_lt(x_12, x_2);
if (x_16 == 0)
{
uint32_t x_17; uint16_t x_18; uint8_t x_19; 
lean_dec(x_13);
lean_dec(x_12);
x_17 = 0;
x_18 = 0;
x_19 = 0;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_17);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_18);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_19);
return x_1;
}
else
{
lean_object* x_20; uint32_t x_21; uint16_t x_22; uint8_t x_23; 
x_20 = l_RBNode_ins___main___at_Lean_IR_mkIndexSet___spec__2(x_14, x_2, x_3);
x_21 = 0;
x_22 = 0;
x_23 = 0;
lean_ctor_set(x_1, 3, x_20);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_21);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_22);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_23);
return x_1;
}
}
else
{
lean_object* x_24; uint32_t x_25; uint16_t x_26; uint8_t x_27; 
x_24 = l_RBNode_ins___main___at_Lean_IR_mkIndexSet___spec__2(x_11, x_2, x_3);
x_25 = 0;
x_26 = 0;
x_27 = 0;
lean_ctor_set(x_1, 0, x_24);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_25);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_26);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_27);
return x_1;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_1, 0);
x_29 = lean_ctor_get(x_1, 1);
x_30 = lean_ctor_get(x_1, 2);
x_31 = lean_ctor_get(x_1, 3);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_1);
x_32 = lean_nat_dec_lt(x_2, x_29);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = lean_nat_dec_lt(x_29, x_2);
if (x_33 == 0)
{
uint32_t x_34; uint16_t x_35; uint8_t x_36; lean_object* x_37; 
lean_dec(x_30);
lean_dec(x_29);
x_34 = 0;
x_35 = 0;
x_36 = 0;
x_37 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_37, 0, x_28);
lean_ctor_set(x_37, 1, x_2);
lean_ctor_set(x_37, 2, x_3);
lean_ctor_set(x_37, 3, x_31);
lean_ctor_set_uint8(x_37, sizeof(void*)*4 + 6, x_9);
lean_ctor_set_uint32(x_37, sizeof(void*)*4, x_34);
lean_ctor_set_uint16(x_37, sizeof(void*)*4 + 4, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*4 + 7, x_36);
return x_37;
}
else
{
lean_object* x_38; uint32_t x_39; uint16_t x_40; uint8_t x_41; lean_object* x_42; 
x_38 = l_RBNode_ins___main___at_Lean_IR_mkIndexSet___spec__2(x_31, x_2, x_3);
x_39 = 0;
x_40 = 0;
x_41 = 0;
x_42 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_42, 0, x_28);
lean_ctor_set(x_42, 1, x_29);
lean_ctor_set(x_42, 2, x_30);
lean_ctor_set(x_42, 3, x_38);
lean_ctor_set_uint8(x_42, sizeof(void*)*4 + 6, x_9);
lean_ctor_set_uint32(x_42, sizeof(void*)*4, x_39);
lean_ctor_set_uint16(x_42, sizeof(void*)*4 + 4, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*4 + 7, x_41);
return x_42;
}
}
else
{
lean_object* x_43; uint32_t x_44; uint16_t x_45; uint8_t x_46; lean_object* x_47; 
x_43 = l_RBNode_ins___main___at_Lean_IR_mkIndexSet___spec__2(x_28, x_2, x_3);
x_44 = 0;
x_45 = 0;
x_46 = 0;
x_47 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set(x_47, 1, x_29);
lean_ctor_set(x_47, 2, x_30);
lean_ctor_set(x_47, 3, x_31);
lean_ctor_set_uint8(x_47, sizeof(void*)*4 + 6, x_9);
lean_ctor_set_uint32(x_47, sizeof(void*)*4, x_44);
lean_ctor_set_uint16(x_47, sizeof(void*)*4 + 4, x_45);
lean_ctor_set_uint8(x_47, sizeof(void*)*4 + 7, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_1);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_1, 0);
x_50 = lean_ctor_get(x_1, 1);
x_51 = lean_ctor_get(x_1, 2);
x_52 = lean_ctor_get(x_1, 3);
x_53 = lean_nat_dec_lt(x_2, x_50);
if (x_53 == 0)
{
uint8_t x_54; 
x_54 = lean_nat_dec_lt(x_50, x_2);
if (x_54 == 0)
{
uint32_t x_55; uint16_t x_56; uint8_t x_57; 
lean_dec(x_51);
lean_dec(x_50);
x_55 = 0;
x_56 = 0;
x_57 = 0;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_55);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_56);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_57);
return x_1;
}
else
{
uint8_t x_58; 
x_58 = l_RBNode_isRed___rarg(x_52);
if (x_58 == 0)
{
lean_object* x_59; uint32_t x_60; uint16_t x_61; uint8_t x_62; 
x_59 = l_RBNode_ins___main___at_Lean_IR_mkIndexSet___spec__2(x_52, x_2, x_3);
x_60 = 0;
x_61 = 0;
x_62 = 0;
lean_ctor_set(x_1, 3, x_59);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_60);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_61);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_62);
return x_1;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = l_RBNode_ins___main___at_Lean_IR_mkIndexSet___spec__2(x_52, x_2, x_3);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_63, 3);
lean_inc(x_65);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_63);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; uint32_t x_70; uint16_t x_71; uint8_t x_72; uint8_t x_73; uint32_t x_74; uint16_t x_75; uint8_t x_76; 
x_67 = lean_ctor_get(x_63, 3);
lean_dec(x_67);
x_68 = lean_ctor_get(x_63, 0);
lean_dec(x_68);
x_69 = 0;
x_70 = 0;
x_71 = 0;
x_72 = 0;
lean_ctor_set(x_63, 0, x_65);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 6, x_69);
lean_ctor_set_uint32(x_63, sizeof(void*)*4, x_70);
lean_ctor_set_uint16(x_63, sizeof(void*)*4 + 4, x_71);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 7, x_72);
x_73 = 1;
x_74 = 0;
x_75 = 0;
x_76 = 0;
lean_ctor_set(x_1, 3, x_63);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_73);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_74);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_75);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_76);
return x_1;
}
else
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; uint32_t x_80; uint16_t x_81; uint8_t x_82; lean_object* x_83; uint8_t x_84; uint32_t x_85; uint16_t x_86; uint8_t x_87; 
x_77 = lean_ctor_get(x_63, 1);
x_78 = lean_ctor_get(x_63, 2);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_63);
x_79 = 0;
x_80 = 0;
x_81 = 0;
x_82 = 0;
x_83 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_83, 0, x_65);
lean_ctor_set(x_83, 1, x_77);
lean_ctor_set(x_83, 2, x_78);
lean_ctor_set(x_83, 3, x_65);
lean_ctor_set_uint8(x_83, sizeof(void*)*4 + 6, x_79);
lean_ctor_set_uint32(x_83, sizeof(void*)*4, x_80);
lean_ctor_set_uint16(x_83, sizeof(void*)*4 + 4, x_81);
lean_ctor_set_uint8(x_83, sizeof(void*)*4 + 7, x_82);
x_84 = 1;
x_85 = 0;
x_86 = 0;
x_87 = 0;
lean_ctor_set(x_1, 3, x_83);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_84);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_85);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_86);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_87);
return x_1;
}
}
else
{
uint8_t x_88; 
x_88 = lean_ctor_get_uint8(x_65, sizeof(void*)*4 + 6);
if (x_88 == 0)
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_63);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_90 = lean_ctor_get(x_63, 1);
x_91 = lean_ctor_get(x_63, 2);
x_92 = lean_ctor_get(x_63, 3);
lean_dec(x_92);
x_93 = lean_ctor_get(x_63, 0);
lean_dec(x_93);
x_94 = !lean_is_exclusive(x_65);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; uint32_t x_100; uint16_t x_101; uint8_t x_102; uint32_t x_103; uint16_t x_104; uint8_t x_105; uint32_t x_106; uint16_t x_107; uint8_t x_108; 
x_95 = lean_ctor_get(x_65, 0);
x_96 = lean_ctor_get(x_65, 1);
x_97 = lean_ctor_get(x_65, 2);
x_98 = lean_ctor_get(x_65, 3);
x_99 = 1;
x_100 = 0;
x_101 = 0;
x_102 = 0;
lean_ctor_set(x_65, 3, x_64);
lean_ctor_set(x_65, 2, x_51);
lean_ctor_set(x_65, 1, x_50);
lean_ctor_set(x_65, 0, x_49);
lean_ctor_set_uint8(x_65, sizeof(void*)*4 + 6, x_99);
lean_ctor_set_uint32(x_65, sizeof(void*)*4, x_100);
lean_ctor_set_uint16(x_65, sizeof(void*)*4 + 4, x_101);
lean_ctor_set_uint8(x_65, sizeof(void*)*4 + 7, x_102);
x_103 = 0;
x_104 = 0;
x_105 = 0;
lean_ctor_set(x_63, 3, x_98);
lean_ctor_set(x_63, 2, x_97);
lean_ctor_set(x_63, 1, x_96);
lean_ctor_set(x_63, 0, x_95);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 6, x_99);
lean_ctor_set_uint32(x_63, sizeof(void*)*4, x_103);
lean_ctor_set_uint16(x_63, sizeof(void*)*4 + 4, x_104);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 7, x_105);
x_106 = 0;
x_107 = 0;
x_108 = 0;
lean_ctor_set(x_1, 3, x_63);
lean_ctor_set(x_1, 2, x_91);
lean_ctor_set(x_1, 1, x_90);
lean_ctor_set(x_1, 0, x_65);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_88);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_106);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_107);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_108);
return x_1;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; uint32_t x_114; uint16_t x_115; uint8_t x_116; lean_object* x_117; uint32_t x_118; uint16_t x_119; uint8_t x_120; uint32_t x_121; uint16_t x_122; uint8_t x_123; 
x_109 = lean_ctor_get(x_65, 0);
x_110 = lean_ctor_get(x_65, 1);
x_111 = lean_ctor_get(x_65, 2);
x_112 = lean_ctor_get(x_65, 3);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_65);
x_113 = 1;
x_114 = 0;
x_115 = 0;
x_116 = 0;
x_117 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_117, 0, x_49);
lean_ctor_set(x_117, 1, x_50);
lean_ctor_set(x_117, 2, x_51);
lean_ctor_set(x_117, 3, x_64);
lean_ctor_set_uint8(x_117, sizeof(void*)*4 + 6, x_113);
lean_ctor_set_uint32(x_117, sizeof(void*)*4, x_114);
lean_ctor_set_uint16(x_117, sizeof(void*)*4 + 4, x_115);
lean_ctor_set_uint8(x_117, sizeof(void*)*4 + 7, x_116);
x_118 = 0;
x_119 = 0;
x_120 = 0;
lean_ctor_set(x_63, 3, x_112);
lean_ctor_set(x_63, 2, x_111);
lean_ctor_set(x_63, 1, x_110);
lean_ctor_set(x_63, 0, x_109);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 6, x_113);
lean_ctor_set_uint32(x_63, sizeof(void*)*4, x_118);
lean_ctor_set_uint16(x_63, sizeof(void*)*4 + 4, x_119);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 7, x_120);
x_121 = 0;
x_122 = 0;
x_123 = 0;
lean_ctor_set(x_1, 3, x_63);
lean_ctor_set(x_1, 2, x_91);
lean_ctor_set(x_1, 1, x_90);
lean_ctor_set(x_1, 0, x_117);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_88);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_121);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_122);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_123);
return x_1;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; uint32_t x_132; uint16_t x_133; uint8_t x_134; lean_object* x_135; uint32_t x_136; uint16_t x_137; uint8_t x_138; lean_object* x_139; uint32_t x_140; uint16_t x_141; uint8_t x_142; 
x_124 = lean_ctor_get(x_63, 1);
x_125 = lean_ctor_get(x_63, 2);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_63);
x_126 = lean_ctor_get(x_65, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_65, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_65, 2);
lean_inc(x_128);
x_129 = lean_ctor_get(x_65, 3);
lean_inc(x_129);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 lean_ctor_release(x_65, 2);
 lean_ctor_release(x_65, 3);
 x_130 = x_65;
} else {
 lean_dec_ref(x_65);
 x_130 = lean_box(0);
}
x_131 = 1;
x_132 = 0;
x_133 = 0;
x_134 = 0;
if (lean_is_scalar(x_130)) {
 x_135 = lean_alloc_ctor(1, 4, 8);
} else {
 x_135 = x_130;
}
lean_ctor_set(x_135, 0, x_49);
lean_ctor_set(x_135, 1, x_50);
lean_ctor_set(x_135, 2, x_51);
lean_ctor_set(x_135, 3, x_64);
lean_ctor_set_uint8(x_135, sizeof(void*)*4 + 6, x_131);
lean_ctor_set_uint32(x_135, sizeof(void*)*4, x_132);
lean_ctor_set_uint16(x_135, sizeof(void*)*4 + 4, x_133);
lean_ctor_set_uint8(x_135, sizeof(void*)*4 + 7, x_134);
x_136 = 0;
x_137 = 0;
x_138 = 0;
x_139 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_139, 0, x_126);
lean_ctor_set(x_139, 1, x_127);
lean_ctor_set(x_139, 2, x_128);
lean_ctor_set(x_139, 3, x_129);
lean_ctor_set_uint8(x_139, sizeof(void*)*4 + 6, x_131);
lean_ctor_set_uint32(x_139, sizeof(void*)*4, x_136);
lean_ctor_set_uint16(x_139, sizeof(void*)*4 + 4, x_137);
lean_ctor_set_uint8(x_139, sizeof(void*)*4 + 7, x_138);
x_140 = 0;
x_141 = 0;
x_142 = 0;
lean_ctor_set(x_1, 3, x_139);
lean_ctor_set(x_1, 2, x_125);
lean_ctor_set(x_1, 1, x_124);
lean_ctor_set(x_1, 0, x_135);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_88);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_140);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_141);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_142);
return x_1;
}
}
else
{
uint8_t x_143; 
x_143 = !lean_is_exclusive(x_63);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; uint8_t x_146; uint32_t x_147; uint16_t x_148; uint8_t x_149; uint32_t x_150; uint16_t x_151; uint8_t x_152; 
x_144 = lean_ctor_get(x_63, 3);
lean_dec(x_144);
x_145 = lean_ctor_get(x_63, 0);
lean_dec(x_145);
x_146 = 0;
x_147 = 0;
x_148 = 0;
x_149 = 0;
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 6, x_146);
lean_ctor_set_uint32(x_63, sizeof(void*)*4, x_147);
lean_ctor_set_uint16(x_63, sizeof(void*)*4 + 4, x_148);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 7, x_149);
x_150 = 0;
x_151 = 0;
x_152 = 0;
lean_ctor_set(x_1, 3, x_63);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_88);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_150);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_151);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_152);
return x_1;
}
else
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; uint32_t x_156; uint16_t x_157; uint8_t x_158; lean_object* x_159; uint32_t x_160; uint16_t x_161; uint8_t x_162; 
x_153 = lean_ctor_get(x_63, 1);
x_154 = lean_ctor_get(x_63, 2);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_63);
x_155 = 0;
x_156 = 0;
x_157 = 0;
x_158 = 0;
x_159 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_159, 0, x_64);
lean_ctor_set(x_159, 1, x_153);
lean_ctor_set(x_159, 2, x_154);
lean_ctor_set(x_159, 3, x_65);
lean_ctor_set_uint8(x_159, sizeof(void*)*4 + 6, x_155);
lean_ctor_set_uint32(x_159, sizeof(void*)*4, x_156);
lean_ctor_set_uint16(x_159, sizeof(void*)*4 + 4, x_157);
lean_ctor_set_uint8(x_159, sizeof(void*)*4 + 7, x_158);
x_160 = 0;
x_161 = 0;
x_162 = 0;
lean_ctor_set(x_1, 3, x_159);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_88);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_160);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_161);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_162);
return x_1;
}
}
}
}
else
{
uint8_t x_163; 
x_163 = lean_ctor_get_uint8(x_64, sizeof(void*)*4 + 6);
if (x_163 == 0)
{
uint8_t x_164; 
x_164 = !lean_is_exclusive(x_63);
if (x_164 == 0)
{
lean_object* x_165; uint8_t x_166; 
x_165 = lean_ctor_get(x_63, 0);
lean_dec(x_165);
x_166 = !lean_is_exclusive(x_64);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; uint32_t x_172; uint16_t x_173; uint8_t x_174; uint32_t x_175; uint16_t x_176; uint8_t x_177; uint32_t x_178; uint16_t x_179; uint8_t x_180; 
x_167 = lean_ctor_get(x_64, 0);
x_168 = lean_ctor_get(x_64, 1);
x_169 = lean_ctor_get(x_64, 2);
x_170 = lean_ctor_get(x_64, 3);
x_171 = 1;
x_172 = 0;
x_173 = 0;
x_174 = 0;
lean_ctor_set(x_64, 3, x_167);
lean_ctor_set(x_64, 2, x_51);
lean_ctor_set(x_64, 1, x_50);
lean_ctor_set(x_64, 0, x_49);
lean_ctor_set_uint8(x_64, sizeof(void*)*4 + 6, x_171);
lean_ctor_set_uint32(x_64, sizeof(void*)*4, x_172);
lean_ctor_set_uint16(x_64, sizeof(void*)*4 + 4, x_173);
lean_ctor_set_uint8(x_64, sizeof(void*)*4 + 7, x_174);
x_175 = 0;
x_176 = 0;
x_177 = 0;
lean_ctor_set(x_63, 0, x_170);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 6, x_171);
lean_ctor_set_uint32(x_63, sizeof(void*)*4, x_175);
lean_ctor_set_uint16(x_63, sizeof(void*)*4 + 4, x_176);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 7, x_177);
x_178 = 0;
x_179 = 0;
x_180 = 0;
lean_ctor_set(x_1, 3, x_63);
lean_ctor_set(x_1, 2, x_169);
lean_ctor_set(x_1, 1, x_168);
lean_ctor_set(x_1, 0, x_64);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_163);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_178);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_179);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_180);
return x_1;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; uint32_t x_186; uint16_t x_187; uint8_t x_188; lean_object* x_189; uint32_t x_190; uint16_t x_191; uint8_t x_192; uint32_t x_193; uint16_t x_194; uint8_t x_195; 
x_181 = lean_ctor_get(x_64, 0);
x_182 = lean_ctor_get(x_64, 1);
x_183 = lean_ctor_get(x_64, 2);
x_184 = lean_ctor_get(x_64, 3);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_64);
x_185 = 1;
x_186 = 0;
x_187 = 0;
x_188 = 0;
x_189 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_189, 0, x_49);
lean_ctor_set(x_189, 1, x_50);
lean_ctor_set(x_189, 2, x_51);
lean_ctor_set(x_189, 3, x_181);
lean_ctor_set_uint8(x_189, sizeof(void*)*4 + 6, x_185);
lean_ctor_set_uint32(x_189, sizeof(void*)*4, x_186);
lean_ctor_set_uint16(x_189, sizeof(void*)*4 + 4, x_187);
lean_ctor_set_uint8(x_189, sizeof(void*)*4 + 7, x_188);
x_190 = 0;
x_191 = 0;
x_192 = 0;
lean_ctor_set(x_63, 0, x_184);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 6, x_185);
lean_ctor_set_uint32(x_63, sizeof(void*)*4, x_190);
lean_ctor_set_uint16(x_63, sizeof(void*)*4 + 4, x_191);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 7, x_192);
x_193 = 0;
x_194 = 0;
x_195 = 0;
lean_ctor_set(x_1, 3, x_63);
lean_ctor_set(x_1, 2, x_183);
lean_ctor_set(x_1, 1, x_182);
lean_ctor_set(x_1, 0, x_189);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_163);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_193);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_194);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_195);
return x_1;
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; uint32_t x_205; uint16_t x_206; uint8_t x_207; lean_object* x_208; uint32_t x_209; uint16_t x_210; uint8_t x_211; lean_object* x_212; uint32_t x_213; uint16_t x_214; uint8_t x_215; 
x_196 = lean_ctor_get(x_63, 1);
x_197 = lean_ctor_get(x_63, 2);
x_198 = lean_ctor_get(x_63, 3);
lean_inc(x_198);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_63);
x_199 = lean_ctor_get(x_64, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_64, 1);
lean_inc(x_200);
x_201 = lean_ctor_get(x_64, 2);
lean_inc(x_201);
x_202 = lean_ctor_get(x_64, 3);
lean_inc(x_202);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 lean_ctor_release(x_64, 2);
 lean_ctor_release(x_64, 3);
 x_203 = x_64;
} else {
 lean_dec_ref(x_64);
 x_203 = lean_box(0);
}
x_204 = 1;
x_205 = 0;
x_206 = 0;
x_207 = 0;
if (lean_is_scalar(x_203)) {
 x_208 = lean_alloc_ctor(1, 4, 8);
} else {
 x_208 = x_203;
}
lean_ctor_set(x_208, 0, x_49);
lean_ctor_set(x_208, 1, x_50);
lean_ctor_set(x_208, 2, x_51);
lean_ctor_set(x_208, 3, x_199);
lean_ctor_set_uint8(x_208, sizeof(void*)*4 + 6, x_204);
lean_ctor_set_uint32(x_208, sizeof(void*)*4, x_205);
lean_ctor_set_uint16(x_208, sizeof(void*)*4 + 4, x_206);
lean_ctor_set_uint8(x_208, sizeof(void*)*4 + 7, x_207);
x_209 = 0;
x_210 = 0;
x_211 = 0;
x_212 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_212, 0, x_202);
lean_ctor_set(x_212, 1, x_196);
lean_ctor_set(x_212, 2, x_197);
lean_ctor_set(x_212, 3, x_198);
lean_ctor_set_uint8(x_212, sizeof(void*)*4 + 6, x_204);
lean_ctor_set_uint32(x_212, sizeof(void*)*4, x_209);
lean_ctor_set_uint16(x_212, sizeof(void*)*4 + 4, x_210);
lean_ctor_set_uint8(x_212, sizeof(void*)*4 + 7, x_211);
x_213 = 0;
x_214 = 0;
x_215 = 0;
lean_ctor_set(x_1, 3, x_212);
lean_ctor_set(x_1, 2, x_201);
lean_ctor_set(x_1, 1, x_200);
lean_ctor_set(x_1, 0, x_208);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_163);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_213);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_214);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_215);
return x_1;
}
}
else
{
lean_object* x_216; 
x_216 = lean_ctor_get(x_63, 3);
lean_inc(x_216);
if (lean_obj_tag(x_216) == 0)
{
uint8_t x_217; 
x_217 = !lean_is_exclusive(x_63);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; uint8_t x_220; uint32_t x_221; uint16_t x_222; uint8_t x_223; uint32_t x_224; uint16_t x_225; uint8_t x_226; 
x_218 = lean_ctor_get(x_63, 3);
lean_dec(x_218);
x_219 = lean_ctor_get(x_63, 0);
lean_dec(x_219);
x_220 = 0;
x_221 = 0;
x_222 = 0;
x_223 = 0;
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 6, x_220);
lean_ctor_set_uint32(x_63, sizeof(void*)*4, x_221);
lean_ctor_set_uint16(x_63, sizeof(void*)*4 + 4, x_222);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 7, x_223);
x_224 = 0;
x_225 = 0;
x_226 = 0;
lean_ctor_set(x_1, 3, x_63);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_163);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_224);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_225);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_226);
return x_1;
}
else
{
lean_object* x_227; lean_object* x_228; uint8_t x_229; uint32_t x_230; uint16_t x_231; uint8_t x_232; lean_object* x_233; uint32_t x_234; uint16_t x_235; uint8_t x_236; 
x_227 = lean_ctor_get(x_63, 1);
x_228 = lean_ctor_get(x_63, 2);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_63);
x_229 = 0;
x_230 = 0;
x_231 = 0;
x_232 = 0;
x_233 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_233, 0, x_64);
lean_ctor_set(x_233, 1, x_227);
lean_ctor_set(x_233, 2, x_228);
lean_ctor_set(x_233, 3, x_216);
lean_ctor_set_uint8(x_233, sizeof(void*)*4 + 6, x_229);
lean_ctor_set_uint32(x_233, sizeof(void*)*4, x_230);
lean_ctor_set_uint16(x_233, sizeof(void*)*4 + 4, x_231);
lean_ctor_set_uint8(x_233, sizeof(void*)*4 + 7, x_232);
x_234 = 0;
x_235 = 0;
x_236 = 0;
lean_ctor_set(x_1, 3, x_233);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_163);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_234);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_235);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_236);
return x_1;
}
}
else
{
uint8_t x_237; 
x_237 = lean_ctor_get_uint8(x_216, sizeof(void*)*4 + 6);
if (x_237 == 0)
{
uint8_t x_238; 
lean_free_object(x_1);
x_238 = !lean_is_exclusive(x_63);
if (x_238 == 0)
{
lean_object* x_239; lean_object* x_240; uint8_t x_241; 
x_239 = lean_ctor_get(x_63, 3);
lean_dec(x_239);
x_240 = lean_ctor_get(x_63, 0);
lean_dec(x_240);
x_241 = !lean_is_exclusive(x_216);
if (x_241 == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint32_t x_246; uint16_t x_247; uint8_t x_248; uint8_t x_249; 
x_242 = lean_ctor_get(x_216, 0);
x_243 = lean_ctor_get(x_216, 1);
x_244 = lean_ctor_get(x_216, 2);
x_245 = lean_ctor_get(x_216, 3);
x_246 = 0;
x_247 = 0;
x_248 = 0;
lean_inc(x_64);
lean_ctor_set(x_216, 3, x_64);
lean_ctor_set(x_216, 2, x_51);
lean_ctor_set(x_216, 1, x_50);
lean_ctor_set(x_216, 0, x_49);
x_249 = !lean_is_exclusive(x_64);
if (x_249 == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; uint32_t x_254; uint16_t x_255; uint8_t x_256; uint32_t x_257; uint16_t x_258; uint8_t x_259; 
x_250 = lean_ctor_get(x_64, 3);
lean_dec(x_250);
x_251 = lean_ctor_get(x_64, 2);
lean_dec(x_251);
x_252 = lean_ctor_get(x_64, 1);
lean_dec(x_252);
x_253 = lean_ctor_get(x_64, 0);
lean_dec(x_253);
lean_ctor_set_uint8(x_216, sizeof(void*)*4 + 6, x_163);
lean_ctor_set_uint32(x_216, sizeof(void*)*4, x_246);
lean_ctor_set_uint16(x_216, sizeof(void*)*4 + 4, x_247);
lean_ctor_set_uint8(x_216, sizeof(void*)*4 + 7, x_248);
x_254 = 0;
x_255 = 0;
x_256 = 0;
lean_ctor_set(x_64, 3, x_245);
lean_ctor_set(x_64, 2, x_244);
lean_ctor_set(x_64, 1, x_243);
lean_ctor_set(x_64, 0, x_242);
lean_ctor_set_uint32(x_64, sizeof(void*)*4, x_254);
lean_ctor_set_uint16(x_64, sizeof(void*)*4 + 4, x_255);
lean_ctor_set_uint8(x_64, sizeof(void*)*4 + 7, x_256);
x_257 = 0;
x_258 = 0;
x_259 = 0;
lean_ctor_set(x_63, 3, x_64);
lean_ctor_set(x_63, 0, x_216);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 6, x_237);
lean_ctor_set_uint32(x_63, sizeof(void*)*4, x_257);
lean_ctor_set_uint16(x_63, sizeof(void*)*4 + 4, x_258);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 7, x_259);
return x_63;
}
else
{
uint32_t x_260; uint16_t x_261; uint8_t x_262; lean_object* x_263; uint32_t x_264; uint16_t x_265; uint8_t x_266; 
lean_dec(x_64);
lean_ctor_set_uint8(x_216, sizeof(void*)*4 + 6, x_163);
lean_ctor_set_uint32(x_216, sizeof(void*)*4, x_246);
lean_ctor_set_uint16(x_216, sizeof(void*)*4 + 4, x_247);
lean_ctor_set_uint8(x_216, sizeof(void*)*4 + 7, x_248);
x_260 = 0;
x_261 = 0;
x_262 = 0;
x_263 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_263, 0, x_242);
lean_ctor_set(x_263, 1, x_243);
lean_ctor_set(x_263, 2, x_244);
lean_ctor_set(x_263, 3, x_245);
lean_ctor_set_uint8(x_263, sizeof(void*)*4 + 6, x_163);
lean_ctor_set_uint32(x_263, sizeof(void*)*4, x_260);
lean_ctor_set_uint16(x_263, sizeof(void*)*4 + 4, x_261);
lean_ctor_set_uint8(x_263, sizeof(void*)*4 + 7, x_262);
x_264 = 0;
x_265 = 0;
x_266 = 0;
lean_ctor_set(x_63, 3, x_263);
lean_ctor_set(x_63, 0, x_216);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 6, x_237);
lean_ctor_set_uint32(x_63, sizeof(void*)*4, x_264);
lean_ctor_set_uint16(x_63, sizeof(void*)*4 + 4, x_265);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 7, x_266);
return x_63;
}
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; uint32_t x_271; uint16_t x_272; uint8_t x_273; lean_object* x_274; lean_object* x_275; uint32_t x_276; uint16_t x_277; uint8_t x_278; lean_object* x_279; uint32_t x_280; uint16_t x_281; uint8_t x_282; 
x_267 = lean_ctor_get(x_216, 0);
x_268 = lean_ctor_get(x_216, 1);
x_269 = lean_ctor_get(x_216, 2);
x_270 = lean_ctor_get(x_216, 3);
lean_inc(x_270);
lean_inc(x_269);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_216);
x_271 = 0;
x_272 = 0;
x_273 = 0;
lean_inc(x_64);
x_274 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_274, 0, x_49);
lean_ctor_set(x_274, 1, x_50);
lean_ctor_set(x_274, 2, x_51);
lean_ctor_set(x_274, 3, x_64);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 lean_ctor_release(x_64, 2);
 lean_ctor_release(x_64, 3);
 x_275 = x_64;
} else {
 lean_dec_ref(x_64);
 x_275 = lean_box(0);
}
lean_ctor_set_uint8(x_274, sizeof(void*)*4 + 6, x_163);
lean_ctor_set_uint32(x_274, sizeof(void*)*4, x_271);
lean_ctor_set_uint16(x_274, sizeof(void*)*4 + 4, x_272);
lean_ctor_set_uint8(x_274, sizeof(void*)*4 + 7, x_273);
x_276 = 0;
x_277 = 0;
x_278 = 0;
if (lean_is_scalar(x_275)) {
 x_279 = lean_alloc_ctor(1, 4, 8);
} else {
 x_279 = x_275;
}
lean_ctor_set(x_279, 0, x_267);
lean_ctor_set(x_279, 1, x_268);
lean_ctor_set(x_279, 2, x_269);
lean_ctor_set(x_279, 3, x_270);
lean_ctor_set_uint8(x_279, sizeof(void*)*4 + 6, x_163);
lean_ctor_set_uint32(x_279, sizeof(void*)*4, x_276);
lean_ctor_set_uint16(x_279, sizeof(void*)*4 + 4, x_277);
lean_ctor_set_uint8(x_279, sizeof(void*)*4 + 7, x_278);
x_280 = 0;
x_281 = 0;
x_282 = 0;
lean_ctor_set(x_63, 3, x_279);
lean_ctor_set(x_63, 0, x_274);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 6, x_237);
lean_ctor_set_uint32(x_63, sizeof(void*)*4, x_280);
lean_ctor_set_uint16(x_63, sizeof(void*)*4 + 4, x_281);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 7, x_282);
return x_63;
}
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; uint32_t x_290; uint16_t x_291; uint8_t x_292; lean_object* x_293; lean_object* x_294; uint32_t x_295; uint16_t x_296; uint8_t x_297; lean_object* x_298; uint32_t x_299; uint16_t x_300; uint8_t x_301; lean_object* x_302; 
x_283 = lean_ctor_get(x_63, 1);
x_284 = lean_ctor_get(x_63, 2);
lean_inc(x_284);
lean_inc(x_283);
lean_dec(x_63);
x_285 = lean_ctor_get(x_216, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_216, 1);
lean_inc(x_286);
x_287 = lean_ctor_get(x_216, 2);
lean_inc(x_287);
x_288 = lean_ctor_get(x_216, 3);
lean_inc(x_288);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 lean_ctor_release(x_216, 1);
 lean_ctor_release(x_216, 2);
 lean_ctor_release(x_216, 3);
 x_289 = x_216;
} else {
 lean_dec_ref(x_216);
 x_289 = lean_box(0);
}
x_290 = 0;
x_291 = 0;
x_292 = 0;
lean_inc(x_64);
if (lean_is_scalar(x_289)) {
 x_293 = lean_alloc_ctor(1, 4, 8);
} else {
 x_293 = x_289;
}
lean_ctor_set(x_293, 0, x_49);
lean_ctor_set(x_293, 1, x_50);
lean_ctor_set(x_293, 2, x_51);
lean_ctor_set(x_293, 3, x_64);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 lean_ctor_release(x_64, 2);
 lean_ctor_release(x_64, 3);
 x_294 = x_64;
} else {
 lean_dec_ref(x_64);
 x_294 = lean_box(0);
}
lean_ctor_set_uint8(x_293, sizeof(void*)*4 + 6, x_163);
lean_ctor_set_uint32(x_293, sizeof(void*)*4, x_290);
lean_ctor_set_uint16(x_293, sizeof(void*)*4 + 4, x_291);
lean_ctor_set_uint8(x_293, sizeof(void*)*4 + 7, x_292);
x_295 = 0;
x_296 = 0;
x_297 = 0;
if (lean_is_scalar(x_294)) {
 x_298 = lean_alloc_ctor(1, 4, 8);
} else {
 x_298 = x_294;
}
lean_ctor_set(x_298, 0, x_285);
lean_ctor_set(x_298, 1, x_286);
lean_ctor_set(x_298, 2, x_287);
lean_ctor_set(x_298, 3, x_288);
lean_ctor_set_uint8(x_298, sizeof(void*)*4 + 6, x_163);
lean_ctor_set_uint32(x_298, sizeof(void*)*4, x_295);
lean_ctor_set_uint16(x_298, sizeof(void*)*4 + 4, x_296);
lean_ctor_set_uint8(x_298, sizeof(void*)*4 + 7, x_297);
x_299 = 0;
x_300 = 0;
x_301 = 0;
x_302 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_302, 0, x_293);
lean_ctor_set(x_302, 1, x_283);
lean_ctor_set(x_302, 2, x_284);
lean_ctor_set(x_302, 3, x_298);
lean_ctor_set_uint8(x_302, sizeof(void*)*4 + 6, x_237);
lean_ctor_set_uint32(x_302, sizeof(void*)*4, x_299);
lean_ctor_set_uint16(x_302, sizeof(void*)*4 + 4, x_300);
lean_ctor_set_uint8(x_302, sizeof(void*)*4 + 7, x_301);
return x_302;
}
}
else
{
uint8_t x_303; 
x_303 = !lean_is_exclusive(x_63);
if (x_303 == 0)
{
lean_object* x_304; lean_object* x_305; uint8_t x_306; 
x_304 = lean_ctor_get(x_63, 3);
lean_dec(x_304);
x_305 = lean_ctor_get(x_63, 0);
lean_dec(x_305);
x_306 = !lean_is_exclusive(x_64);
if (x_306 == 0)
{
uint32_t x_307; uint16_t x_308; uint8_t x_309; uint8_t x_310; uint32_t x_311; uint16_t x_312; uint8_t x_313; uint32_t x_314; uint16_t x_315; uint8_t x_316; 
x_307 = 0;
x_308 = 0;
x_309 = 0;
lean_ctor_set_uint8(x_64, sizeof(void*)*4 + 6, x_237);
lean_ctor_set_uint32(x_64, sizeof(void*)*4, x_307);
lean_ctor_set_uint16(x_64, sizeof(void*)*4 + 4, x_308);
lean_ctor_set_uint8(x_64, sizeof(void*)*4 + 7, x_309);
x_310 = 0;
x_311 = 0;
x_312 = 0;
x_313 = 0;
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 6, x_310);
lean_ctor_set_uint32(x_63, sizeof(void*)*4, x_311);
lean_ctor_set_uint16(x_63, sizeof(void*)*4 + 4, x_312);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 7, x_313);
x_314 = 0;
x_315 = 0;
x_316 = 0;
lean_ctor_set(x_1, 3, x_63);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_237);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_314);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_315);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_316);
return x_1;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; uint32_t x_321; uint16_t x_322; uint8_t x_323; lean_object* x_324; uint8_t x_325; uint32_t x_326; uint16_t x_327; uint8_t x_328; uint32_t x_329; uint16_t x_330; uint8_t x_331; 
x_317 = lean_ctor_get(x_64, 0);
x_318 = lean_ctor_get(x_64, 1);
x_319 = lean_ctor_get(x_64, 2);
x_320 = lean_ctor_get(x_64, 3);
lean_inc(x_320);
lean_inc(x_319);
lean_inc(x_318);
lean_inc(x_317);
lean_dec(x_64);
x_321 = 0;
x_322 = 0;
x_323 = 0;
x_324 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_324, 0, x_317);
lean_ctor_set(x_324, 1, x_318);
lean_ctor_set(x_324, 2, x_319);
lean_ctor_set(x_324, 3, x_320);
lean_ctor_set_uint8(x_324, sizeof(void*)*4 + 6, x_237);
lean_ctor_set_uint32(x_324, sizeof(void*)*4, x_321);
lean_ctor_set_uint16(x_324, sizeof(void*)*4 + 4, x_322);
lean_ctor_set_uint8(x_324, sizeof(void*)*4 + 7, x_323);
x_325 = 0;
x_326 = 0;
x_327 = 0;
x_328 = 0;
lean_ctor_set(x_63, 0, x_324);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 6, x_325);
lean_ctor_set_uint32(x_63, sizeof(void*)*4, x_326);
lean_ctor_set_uint16(x_63, sizeof(void*)*4 + 4, x_327);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 7, x_328);
x_329 = 0;
x_330 = 0;
x_331 = 0;
lean_ctor_set(x_1, 3, x_63);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_237);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_329);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_330);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_331);
return x_1;
}
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; uint32_t x_339; uint16_t x_340; uint8_t x_341; lean_object* x_342; uint8_t x_343; uint32_t x_344; uint16_t x_345; uint8_t x_346; lean_object* x_347; uint32_t x_348; uint16_t x_349; uint8_t x_350; 
x_332 = lean_ctor_get(x_63, 1);
x_333 = lean_ctor_get(x_63, 2);
lean_inc(x_333);
lean_inc(x_332);
lean_dec(x_63);
x_334 = lean_ctor_get(x_64, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_64, 1);
lean_inc(x_335);
x_336 = lean_ctor_get(x_64, 2);
lean_inc(x_336);
x_337 = lean_ctor_get(x_64, 3);
lean_inc(x_337);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 lean_ctor_release(x_64, 2);
 lean_ctor_release(x_64, 3);
 x_338 = x_64;
} else {
 lean_dec_ref(x_64);
 x_338 = lean_box(0);
}
x_339 = 0;
x_340 = 0;
x_341 = 0;
if (lean_is_scalar(x_338)) {
 x_342 = lean_alloc_ctor(1, 4, 8);
} else {
 x_342 = x_338;
}
lean_ctor_set(x_342, 0, x_334);
lean_ctor_set(x_342, 1, x_335);
lean_ctor_set(x_342, 2, x_336);
lean_ctor_set(x_342, 3, x_337);
lean_ctor_set_uint8(x_342, sizeof(void*)*4 + 6, x_237);
lean_ctor_set_uint32(x_342, sizeof(void*)*4, x_339);
lean_ctor_set_uint16(x_342, sizeof(void*)*4 + 4, x_340);
lean_ctor_set_uint8(x_342, sizeof(void*)*4 + 7, x_341);
x_343 = 0;
x_344 = 0;
x_345 = 0;
x_346 = 0;
x_347 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_347, 0, x_342);
lean_ctor_set(x_347, 1, x_332);
lean_ctor_set(x_347, 2, x_333);
lean_ctor_set(x_347, 3, x_216);
lean_ctor_set_uint8(x_347, sizeof(void*)*4 + 6, x_343);
lean_ctor_set_uint32(x_347, sizeof(void*)*4, x_344);
lean_ctor_set_uint16(x_347, sizeof(void*)*4 + 4, x_345);
lean_ctor_set_uint8(x_347, sizeof(void*)*4 + 7, x_346);
x_348 = 0;
x_349 = 0;
x_350 = 0;
lean_ctor_set(x_1, 3, x_347);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_237);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_348);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_349);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_350);
return x_1;
}
}
}
}
}
}
}
}
else
{
uint8_t x_351; 
x_351 = l_RBNode_isRed___rarg(x_49);
if (x_351 == 0)
{
lean_object* x_352; uint32_t x_353; uint16_t x_354; uint8_t x_355; 
x_352 = l_RBNode_ins___main___at_Lean_IR_mkIndexSet___spec__2(x_49, x_2, x_3);
x_353 = 0;
x_354 = 0;
x_355 = 0;
lean_ctor_set(x_1, 0, x_352);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_353);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_354);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_355);
return x_1;
}
else
{
lean_object* x_356; lean_object* x_357; 
x_356 = l_RBNode_ins___main___at_Lean_IR_mkIndexSet___spec__2(x_49, x_2, x_3);
x_357 = lean_ctor_get(x_356, 0);
lean_inc(x_357);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; 
x_358 = lean_ctor_get(x_356, 3);
lean_inc(x_358);
if (lean_obj_tag(x_358) == 0)
{
uint8_t x_359; 
x_359 = !lean_is_exclusive(x_356);
if (x_359 == 0)
{
lean_object* x_360; lean_object* x_361; uint8_t x_362; uint32_t x_363; uint16_t x_364; uint8_t x_365; uint8_t x_366; uint32_t x_367; uint16_t x_368; uint8_t x_369; 
x_360 = lean_ctor_get(x_356, 3);
lean_dec(x_360);
x_361 = lean_ctor_get(x_356, 0);
lean_dec(x_361);
x_362 = 0;
x_363 = 0;
x_364 = 0;
x_365 = 0;
lean_ctor_set(x_356, 0, x_358);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 6, x_362);
lean_ctor_set_uint32(x_356, sizeof(void*)*4, x_363);
lean_ctor_set_uint16(x_356, sizeof(void*)*4 + 4, x_364);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 7, x_365);
x_366 = 1;
x_367 = 0;
x_368 = 0;
x_369 = 0;
lean_ctor_set(x_1, 0, x_356);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_366);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_367);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_368);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_369);
return x_1;
}
else
{
lean_object* x_370; lean_object* x_371; uint8_t x_372; uint32_t x_373; uint16_t x_374; uint8_t x_375; lean_object* x_376; uint8_t x_377; uint32_t x_378; uint16_t x_379; uint8_t x_380; 
x_370 = lean_ctor_get(x_356, 1);
x_371 = lean_ctor_get(x_356, 2);
lean_inc(x_371);
lean_inc(x_370);
lean_dec(x_356);
x_372 = 0;
x_373 = 0;
x_374 = 0;
x_375 = 0;
x_376 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_376, 0, x_358);
lean_ctor_set(x_376, 1, x_370);
lean_ctor_set(x_376, 2, x_371);
lean_ctor_set(x_376, 3, x_358);
lean_ctor_set_uint8(x_376, sizeof(void*)*4 + 6, x_372);
lean_ctor_set_uint32(x_376, sizeof(void*)*4, x_373);
lean_ctor_set_uint16(x_376, sizeof(void*)*4 + 4, x_374);
lean_ctor_set_uint8(x_376, sizeof(void*)*4 + 7, x_375);
x_377 = 1;
x_378 = 0;
x_379 = 0;
x_380 = 0;
lean_ctor_set(x_1, 0, x_376);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_377);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_378);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_379);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_380);
return x_1;
}
}
else
{
uint8_t x_381; 
x_381 = lean_ctor_get_uint8(x_358, sizeof(void*)*4 + 6);
if (x_381 == 0)
{
uint8_t x_382; 
x_382 = !lean_is_exclusive(x_356);
if (x_382 == 0)
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; uint8_t x_387; 
x_383 = lean_ctor_get(x_356, 1);
x_384 = lean_ctor_get(x_356, 2);
x_385 = lean_ctor_get(x_356, 3);
lean_dec(x_385);
x_386 = lean_ctor_get(x_356, 0);
lean_dec(x_386);
x_387 = !lean_is_exclusive(x_358);
if (x_387 == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; uint8_t x_392; uint32_t x_393; uint16_t x_394; uint8_t x_395; uint32_t x_396; uint16_t x_397; uint8_t x_398; uint32_t x_399; uint16_t x_400; uint8_t x_401; 
x_388 = lean_ctor_get(x_358, 0);
x_389 = lean_ctor_get(x_358, 1);
x_390 = lean_ctor_get(x_358, 2);
x_391 = lean_ctor_get(x_358, 3);
x_392 = 1;
x_393 = 0;
x_394 = 0;
x_395 = 0;
lean_ctor_set(x_358, 3, x_388);
lean_ctor_set(x_358, 2, x_384);
lean_ctor_set(x_358, 1, x_383);
lean_ctor_set(x_358, 0, x_357);
lean_ctor_set_uint8(x_358, sizeof(void*)*4 + 6, x_392);
lean_ctor_set_uint32(x_358, sizeof(void*)*4, x_393);
lean_ctor_set_uint16(x_358, sizeof(void*)*4 + 4, x_394);
lean_ctor_set_uint8(x_358, sizeof(void*)*4 + 7, x_395);
x_396 = 0;
x_397 = 0;
x_398 = 0;
lean_ctor_set(x_356, 3, x_52);
lean_ctor_set(x_356, 2, x_51);
lean_ctor_set(x_356, 1, x_50);
lean_ctor_set(x_356, 0, x_391);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 6, x_392);
lean_ctor_set_uint32(x_356, sizeof(void*)*4, x_396);
lean_ctor_set_uint16(x_356, sizeof(void*)*4 + 4, x_397);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 7, x_398);
x_399 = 0;
x_400 = 0;
x_401 = 0;
lean_ctor_set(x_1, 3, x_356);
lean_ctor_set(x_1, 2, x_390);
lean_ctor_set(x_1, 1, x_389);
lean_ctor_set(x_1, 0, x_358);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_381);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_399);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_400);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_401);
return x_1;
}
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; uint8_t x_406; uint32_t x_407; uint16_t x_408; uint8_t x_409; lean_object* x_410; uint32_t x_411; uint16_t x_412; uint8_t x_413; uint32_t x_414; uint16_t x_415; uint8_t x_416; 
x_402 = lean_ctor_get(x_358, 0);
x_403 = lean_ctor_get(x_358, 1);
x_404 = lean_ctor_get(x_358, 2);
x_405 = lean_ctor_get(x_358, 3);
lean_inc(x_405);
lean_inc(x_404);
lean_inc(x_403);
lean_inc(x_402);
lean_dec(x_358);
x_406 = 1;
x_407 = 0;
x_408 = 0;
x_409 = 0;
x_410 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_410, 0, x_357);
lean_ctor_set(x_410, 1, x_383);
lean_ctor_set(x_410, 2, x_384);
lean_ctor_set(x_410, 3, x_402);
lean_ctor_set_uint8(x_410, sizeof(void*)*4 + 6, x_406);
lean_ctor_set_uint32(x_410, sizeof(void*)*4, x_407);
lean_ctor_set_uint16(x_410, sizeof(void*)*4 + 4, x_408);
lean_ctor_set_uint8(x_410, sizeof(void*)*4 + 7, x_409);
x_411 = 0;
x_412 = 0;
x_413 = 0;
lean_ctor_set(x_356, 3, x_52);
lean_ctor_set(x_356, 2, x_51);
lean_ctor_set(x_356, 1, x_50);
lean_ctor_set(x_356, 0, x_405);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 6, x_406);
lean_ctor_set_uint32(x_356, sizeof(void*)*4, x_411);
lean_ctor_set_uint16(x_356, sizeof(void*)*4 + 4, x_412);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 7, x_413);
x_414 = 0;
x_415 = 0;
x_416 = 0;
lean_ctor_set(x_1, 3, x_356);
lean_ctor_set(x_1, 2, x_404);
lean_ctor_set(x_1, 1, x_403);
lean_ctor_set(x_1, 0, x_410);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_381);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_414);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_415);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_416);
return x_1;
}
}
else
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; uint8_t x_424; uint32_t x_425; uint16_t x_426; uint8_t x_427; lean_object* x_428; uint32_t x_429; uint16_t x_430; uint8_t x_431; lean_object* x_432; uint32_t x_433; uint16_t x_434; uint8_t x_435; 
x_417 = lean_ctor_get(x_356, 1);
x_418 = lean_ctor_get(x_356, 2);
lean_inc(x_418);
lean_inc(x_417);
lean_dec(x_356);
x_419 = lean_ctor_get(x_358, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_358, 1);
lean_inc(x_420);
x_421 = lean_ctor_get(x_358, 2);
lean_inc(x_421);
x_422 = lean_ctor_get(x_358, 3);
lean_inc(x_422);
if (lean_is_exclusive(x_358)) {
 lean_ctor_release(x_358, 0);
 lean_ctor_release(x_358, 1);
 lean_ctor_release(x_358, 2);
 lean_ctor_release(x_358, 3);
 x_423 = x_358;
} else {
 lean_dec_ref(x_358);
 x_423 = lean_box(0);
}
x_424 = 1;
x_425 = 0;
x_426 = 0;
x_427 = 0;
if (lean_is_scalar(x_423)) {
 x_428 = lean_alloc_ctor(1, 4, 8);
} else {
 x_428 = x_423;
}
lean_ctor_set(x_428, 0, x_357);
lean_ctor_set(x_428, 1, x_417);
lean_ctor_set(x_428, 2, x_418);
lean_ctor_set(x_428, 3, x_419);
lean_ctor_set_uint8(x_428, sizeof(void*)*4 + 6, x_424);
lean_ctor_set_uint32(x_428, sizeof(void*)*4, x_425);
lean_ctor_set_uint16(x_428, sizeof(void*)*4 + 4, x_426);
lean_ctor_set_uint8(x_428, sizeof(void*)*4 + 7, x_427);
x_429 = 0;
x_430 = 0;
x_431 = 0;
x_432 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_432, 0, x_422);
lean_ctor_set(x_432, 1, x_50);
lean_ctor_set(x_432, 2, x_51);
lean_ctor_set(x_432, 3, x_52);
lean_ctor_set_uint8(x_432, sizeof(void*)*4 + 6, x_424);
lean_ctor_set_uint32(x_432, sizeof(void*)*4, x_429);
lean_ctor_set_uint16(x_432, sizeof(void*)*4 + 4, x_430);
lean_ctor_set_uint8(x_432, sizeof(void*)*4 + 7, x_431);
x_433 = 0;
x_434 = 0;
x_435 = 0;
lean_ctor_set(x_1, 3, x_432);
lean_ctor_set(x_1, 2, x_421);
lean_ctor_set(x_1, 1, x_420);
lean_ctor_set(x_1, 0, x_428);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_381);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_433);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_434);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_435);
return x_1;
}
}
else
{
uint8_t x_436; 
x_436 = !lean_is_exclusive(x_356);
if (x_436 == 0)
{
lean_object* x_437; lean_object* x_438; uint8_t x_439; uint32_t x_440; uint16_t x_441; uint8_t x_442; uint32_t x_443; uint16_t x_444; uint8_t x_445; 
x_437 = lean_ctor_get(x_356, 3);
lean_dec(x_437);
x_438 = lean_ctor_get(x_356, 0);
lean_dec(x_438);
x_439 = 0;
x_440 = 0;
x_441 = 0;
x_442 = 0;
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 6, x_439);
lean_ctor_set_uint32(x_356, sizeof(void*)*4, x_440);
lean_ctor_set_uint16(x_356, sizeof(void*)*4 + 4, x_441);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 7, x_442);
x_443 = 0;
x_444 = 0;
x_445 = 0;
lean_ctor_set(x_1, 0, x_356);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_381);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_443);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_444);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_445);
return x_1;
}
else
{
lean_object* x_446; lean_object* x_447; uint8_t x_448; uint32_t x_449; uint16_t x_450; uint8_t x_451; lean_object* x_452; uint32_t x_453; uint16_t x_454; uint8_t x_455; 
x_446 = lean_ctor_get(x_356, 1);
x_447 = lean_ctor_get(x_356, 2);
lean_inc(x_447);
lean_inc(x_446);
lean_dec(x_356);
x_448 = 0;
x_449 = 0;
x_450 = 0;
x_451 = 0;
x_452 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_452, 0, x_357);
lean_ctor_set(x_452, 1, x_446);
lean_ctor_set(x_452, 2, x_447);
lean_ctor_set(x_452, 3, x_358);
lean_ctor_set_uint8(x_452, sizeof(void*)*4 + 6, x_448);
lean_ctor_set_uint32(x_452, sizeof(void*)*4, x_449);
lean_ctor_set_uint16(x_452, sizeof(void*)*4 + 4, x_450);
lean_ctor_set_uint8(x_452, sizeof(void*)*4 + 7, x_451);
x_453 = 0;
x_454 = 0;
x_455 = 0;
lean_ctor_set(x_1, 0, x_452);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_381);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_453);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_454);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_455);
return x_1;
}
}
}
}
else
{
uint8_t x_456; 
x_456 = lean_ctor_get_uint8(x_357, sizeof(void*)*4 + 6);
if (x_456 == 0)
{
uint8_t x_457; 
x_457 = !lean_is_exclusive(x_356);
if (x_457 == 0)
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; uint8_t x_462; 
x_458 = lean_ctor_get(x_356, 1);
x_459 = lean_ctor_get(x_356, 2);
x_460 = lean_ctor_get(x_356, 3);
x_461 = lean_ctor_get(x_356, 0);
lean_dec(x_461);
x_462 = !lean_is_exclusive(x_357);
if (x_462 == 0)
{
uint8_t x_463; uint32_t x_464; uint16_t x_465; uint8_t x_466; uint32_t x_467; uint16_t x_468; uint8_t x_469; uint32_t x_470; uint16_t x_471; uint8_t x_472; 
x_463 = 1;
x_464 = 0;
x_465 = 0;
x_466 = 0;
lean_ctor_set_uint8(x_357, sizeof(void*)*4 + 6, x_463);
lean_ctor_set_uint32(x_357, sizeof(void*)*4, x_464);
lean_ctor_set_uint16(x_357, sizeof(void*)*4 + 4, x_465);
lean_ctor_set_uint8(x_357, sizeof(void*)*4 + 7, x_466);
x_467 = 0;
x_468 = 0;
x_469 = 0;
lean_ctor_set(x_356, 3, x_52);
lean_ctor_set(x_356, 2, x_51);
lean_ctor_set(x_356, 1, x_50);
lean_ctor_set(x_356, 0, x_460);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 6, x_463);
lean_ctor_set_uint32(x_356, sizeof(void*)*4, x_467);
lean_ctor_set_uint16(x_356, sizeof(void*)*4 + 4, x_468);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 7, x_469);
x_470 = 0;
x_471 = 0;
x_472 = 0;
lean_ctor_set(x_1, 3, x_356);
lean_ctor_set(x_1, 2, x_459);
lean_ctor_set(x_1, 1, x_458);
lean_ctor_set(x_1, 0, x_357);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_456);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_470);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_471);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_472);
return x_1;
}
else
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; uint8_t x_477; uint32_t x_478; uint16_t x_479; uint8_t x_480; lean_object* x_481; uint32_t x_482; uint16_t x_483; uint8_t x_484; uint32_t x_485; uint16_t x_486; uint8_t x_487; 
x_473 = lean_ctor_get(x_357, 0);
x_474 = lean_ctor_get(x_357, 1);
x_475 = lean_ctor_get(x_357, 2);
x_476 = lean_ctor_get(x_357, 3);
lean_inc(x_476);
lean_inc(x_475);
lean_inc(x_474);
lean_inc(x_473);
lean_dec(x_357);
x_477 = 1;
x_478 = 0;
x_479 = 0;
x_480 = 0;
x_481 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_481, 0, x_473);
lean_ctor_set(x_481, 1, x_474);
lean_ctor_set(x_481, 2, x_475);
lean_ctor_set(x_481, 3, x_476);
lean_ctor_set_uint8(x_481, sizeof(void*)*4 + 6, x_477);
lean_ctor_set_uint32(x_481, sizeof(void*)*4, x_478);
lean_ctor_set_uint16(x_481, sizeof(void*)*4 + 4, x_479);
lean_ctor_set_uint8(x_481, sizeof(void*)*4 + 7, x_480);
x_482 = 0;
x_483 = 0;
x_484 = 0;
lean_ctor_set(x_356, 3, x_52);
lean_ctor_set(x_356, 2, x_51);
lean_ctor_set(x_356, 1, x_50);
lean_ctor_set(x_356, 0, x_460);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 6, x_477);
lean_ctor_set_uint32(x_356, sizeof(void*)*4, x_482);
lean_ctor_set_uint16(x_356, sizeof(void*)*4 + 4, x_483);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 7, x_484);
x_485 = 0;
x_486 = 0;
x_487 = 0;
lean_ctor_set(x_1, 3, x_356);
lean_ctor_set(x_1, 2, x_459);
lean_ctor_set(x_1, 1, x_458);
lean_ctor_set(x_1, 0, x_481);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_456);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_485);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_486);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_487);
return x_1;
}
}
else
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; uint8_t x_496; uint32_t x_497; uint16_t x_498; uint8_t x_499; lean_object* x_500; uint32_t x_501; uint16_t x_502; uint8_t x_503; lean_object* x_504; uint32_t x_505; uint16_t x_506; uint8_t x_507; 
x_488 = lean_ctor_get(x_356, 1);
x_489 = lean_ctor_get(x_356, 2);
x_490 = lean_ctor_get(x_356, 3);
lean_inc(x_490);
lean_inc(x_489);
lean_inc(x_488);
lean_dec(x_356);
x_491 = lean_ctor_get(x_357, 0);
lean_inc(x_491);
x_492 = lean_ctor_get(x_357, 1);
lean_inc(x_492);
x_493 = lean_ctor_get(x_357, 2);
lean_inc(x_493);
x_494 = lean_ctor_get(x_357, 3);
lean_inc(x_494);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 lean_ctor_release(x_357, 1);
 lean_ctor_release(x_357, 2);
 lean_ctor_release(x_357, 3);
 x_495 = x_357;
} else {
 lean_dec_ref(x_357);
 x_495 = lean_box(0);
}
x_496 = 1;
x_497 = 0;
x_498 = 0;
x_499 = 0;
if (lean_is_scalar(x_495)) {
 x_500 = lean_alloc_ctor(1, 4, 8);
} else {
 x_500 = x_495;
}
lean_ctor_set(x_500, 0, x_491);
lean_ctor_set(x_500, 1, x_492);
lean_ctor_set(x_500, 2, x_493);
lean_ctor_set(x_500, 3, x_494);
lean_ctor_set_uint8(x_500, sizeof(void*)*4 + 6, x_496);
lean_ctor_set_uint32(x_500, sizeof(void*)*4, x_497);
lean_ctor_set_uint16(x_500, sizeof(void*)*4 + 4, x_498);
lean_ctor_set_uint8(x_500, sizeof(void*)*4 + 7, x_499);
x_501 = 0;
x_502 = 0;
x_503 = 0;
x_504 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_504, 0, x_490);
lean_ctor_set(x_504, 1, x_50);
lean_ctor_set(x_504, 2, x_51);
lean_ctor_set(x_504, 3, x_52);
lean_ctor_set_uint8(x_504, sizeof(void*)*4 + 6, x_496);
lean_ctor_set_uint32(x_504, sizeof(void*)*4, x_501);
lean_ctor_set_uint16(x_504, sizeof(void*)*4 + 4, x_502);
lean_ctor_set_uint8(x_504, sizeof(void*)*4 + 7, x_503);
x_505 = 0;
x_506 = 0;
x_507 = 0;
lean_ctor_set(x_1, 3, x_504);
lean_ctor_set(x_1, 2, x_489);
lean_ctor_set(x_1, 1, x_488);
lean_ctor_set(x_1, 0, x_500);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_456);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_505);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_506);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_507);
return x_1;
}
}
else
{
lean_object* x_508; 
x_508 = lean_ctor_get(x_356, 3);
lean_inc(x_508);
if (lean_obj_tag(x_508) == 0)
{
uint8_t x_509; 
x_509 = !lean_is_exclusive(x_356);
if (x_509 == 0)
{
lean_object* x_510; lean_object* x_511; uint8_t x_512; uint32_t x_513; uint16_t x_514; uint8_t x_515; uint32_t x_516; uint16_t x_517; uint8_t x_518; 
x_510 = lean_ctor_get(x_356, 3);
lean_dec(x_510);
x_511 = lean_ctor_get(x_356, 0);
lean_dec(x_511);
x_512 = 0;
x_513 = 0;
x_514 = 0;
x_515 = 0;
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 6, x_512);
lean_ctor_set_uint32(x_356, sizeof(void*)*4, x_513);
lean_ctor_set_uint16(x_356, sizeof(void*)*4 + 4, x_514);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 7, x_515);
x_516 = 0;
x_517 = 0;
x_518 = 0;
lean_ctor_set(x_1, 0, x_356);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_456);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_516);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_517);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_518);
return x_1;
}
else
{
lean_object* x_519; lean_object* x_520; uint8_t x_521; uint32_t x_522; uint16_t x_523; uint8_t x_524; lean_object* x_525; uint32_t x_526; uint16_t x_527; uint8_t x_528; 
x_519 = lean_ctor_get(x_356, 1);
x_520 = lean_ctor_get(x_356, 2);
lean_inc(x_520);
lean_inc(x_519);
lean_dec(x_356);
x_521 = 0;
x_522 = 0;
x_523 = 0;
x_524 = 0;
x_525 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_525, 0, x_357);
lean_ctor_set(x_525, 1, x_519);
lean_ctor_set(x_525, 2, x_520);
lean_ctor_set(x_525, 3, x_508);
lean_ctor_set_uint8(x_525, sizeof(void*)*4 + 6, x_521);
lean_ctor_set_uint32(x_525, sizeof(void*)*4, x_522);
lean_ctor_set_uint16(x_525, sizeof(void*)*4 + 4, x_523);
lean_ctor_set_uint8(x_525, sizeof(void*)*4 + 7, x_524);
x_526 = 0;
x_527 = 0;
x_528 = 0;
lean_ctor_set(x_1, 0, x_525);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_456);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_526);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_527);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_528);
return x_1;
}
}
else
{
uint8_t x_529; 
x_529 = lean_ctor_get_uint8(x_508, sizeof(void*)*4 + 6);
if (x_529 == 0)
{
uint8_t x_530; 
lean_free_object(x_1);
x_530 = !lean_is_exclusive(x_356);
if (x_530 == 0)
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; uint8_t x_535; 
x_531 = lean_ctor_get(x_356, 1);
x_532 = lean_ctor_get(x_356, 2);
x_533 = lean_ctor_get(x_356, 3);
lean_dec(x_533);
x_534 = lean_ctor_get(x_356, 0);
lean_dec(x_534);
x_535 = !lean_is_exclusive(x_508);
if (x_535 == 0)
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; uint32_t x_540; uint16_t x_541; uint8_t x_542; uint8_t x_543; 
x_536 = lean_ctor_get(x_508, 0);
x_537 = lean_ctor_get(x_508, 1);
x_538 = lean_ctor_get(x_508, 2);
x_539 = lean_ctor_get(x_508, 3);
x_540 = 0;
x_541 = 0;
x_542 = 0;
lean_inc(x_357);
lean_ctor_set(x_508, 3, x_536);
lean_ctor_set(x_508, 2, x_532);
lean_ctor_set(x_508, 1, x_531);
lean_ctor_set(x_508, 0, x_357);
x_543 = !lean_is_exclusive(x_357);
if (x_543 == 0)
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; uint32_t x_548; uint16_t x_549; uint8_t x_550; uint32_t x_551; uint16_t x_552; uint8_t x_553; 
x_544 = lean_ctor_get(x_357, 3);
lean_dec(x_544);
x_545 = lean_ctor_get(x_357, 2);
lean_dec(x_545);
x_546 = lean_ctor_get(x_357, 1);
lean_dec(x_546);
x_547 = lean_ctor_get(x_357, 0);
lean_dec(x_547);
lean_ctor_set_uint8(x_508, sizeof(void*)*4 + 6, x_456);
lean_ctor_set_uint32(x_508, sizeof(void*)*4, x_540);
lean_ctor_set_uint16(x_508, sizeof(void*)*4 + 4, x_541);
lean_ctor_set_uint8(x_508, sizeof(void*)*4 + 7, x_542);
x_548 = 0;
x_549 = 0;
x_550 = 0;
lean_ctor_set(x_357, 3, x_52);
lean_ctor_set(x_357, 2, x_51);
lean_ctor_set(x_357, 1, x_50);
lean_ctor_set(x_357, 0, x_539);
lean_ctor_set_uint32(x_357, sizeof(void*)*4, x_548);
lean_ctor_set_uint16(x_357, sizeof(void*)*4 + 4, x_549);
lean_ctor_set_uint8(x_357, sizeof(void*)*4 + 7, x_550);
x_551 = 0;
x_552 = 0;
x_553 = 0;
lean_ctor_set(x_356, 3, x_357);
lean_ctor_set(x_356, 2, x_538);
lean_ctor_set(x_356, 1, x_537);
lean_ctor_set(x_356, 0, x_508);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 6, x_529);
lean_ctor_set_uint32(x_356, sizeof(void*)*4, x_551);
lean_ctor_set_uint16(x_356, sizeof(void*)*4 + 4, x_552);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 7, x_553);
return x_356;
}
else
{
uint32_t x_554; uint16_t x_555; uint8_t x_556; lean_object* x_557; uint32_t x_558; uint16_t x_559; uint8_t x_560; 
lean_dec(x_357);
lean_ctor_set_uint8(x_508, sizeof(void*)*4 + 6, x_456);
lean_ctor_set_uint32(x_508, sizeof(void*)*4, x_540);
lean_ctor_set_uint16(x_508, sizeof(void*)*4 + 4, x_541);
lean_ctor_set_uint8(x_508, sizeof(void*)*4 + 7, x_542);
x_554 = 0;
x_555 = 0;
x_556 = 0;
x_557 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_557, 0, x_539);
lean_ctor_set(x_557, 1, x_50);
lean_ctor_set(x_557, 2, x_51);
lean_ctor_set(x_557, 3, x_52);
lean_ctor_set_uint8(x_557, sizeof(void*)*4 + 6, x_456);
lean_ctor_set_uint32(x_557, sizeof(void*)*4, x_554);
lean_ctor_set_uint16(x_557, sizeof(void*)*4 + 4, x_555);
lean_ctor_set_uint8(x_557, sizeof(void*)*4 + 7, x_556);
x_558 = 0;
x_559 = 0;
x_560 = 0;
lean_ctor_set(x_356, 3, x_557);
lean_ctor_set(x_356, 2, x_538);
lean_ctor_set(x_356, 1, x_537);
lean_ctor_set(x_356, 0, x_508);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 6, x_529);
lean_ctor_set_uint32(x_356, sizeof(void*)*4, x_558);
lean_ctor_set_uint16(x_356, sizeof(void*)*4 + 4, x_559);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 7, x_560);
return x_356;
}
}
else
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; uint32_t x_565; uint16_t x_566; uint8_t x_567; lean_object* x_568; lean_object* x_569; uint32_t x_570; uint16_t x_571; uint8_t x_572; lean_object* x_573; uint32_t x_574; uint16_t x_575; uint8_t x_576; 
x_561 = lean_ctor_get(x_508, 0);
x_562 = lean_ctor_get(x_508, 1);
x_563 = lean_ctor_get(x_508, 2);
x_564 = lean_ctor_get(x_508, 3);
lean_inc(x_564);
lean_inc(x_563);
lean_inc(x_562);
lean_inc(x_561);
lean_dec(x_508);
x_565 = 0;
x_566 = 0;
x_567 = 0;
lean_inc(x_357);
x_568 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_568, 0, x_357);
lean_ctor_set(x_568, 1, x_531);
lean_ctor_set(x_568, 2, x_532);
lean_ctor_set(x_568, 3, x_561);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 lean_ctor_release(x_357, 1);
 lean_ctor_release(x_357, 2);
 lean_ctor_release(x_357, 3);
 x_569 = x_357;
} else {
 lean_dec_ref(x_357);
 x_569 = lean_box(0);
}
lean_ctor_set_uint8(x_568, sizeof(void*)*4 + 6, x_456);
lean_ctor_set_uint32(x_568, sizeof(void*)*4, x_565);
lean_ctor_set_uint16(x_568, sizeof(void*)*4 + 4, x_566);
lean_ctor_set_uint8(x_568, sizeof(void*)*4 + 7, x_567);
x_570 = 0;
x_571 = 0;
x_572 = 0;
if (lean_is_scalar(x_569)) {
 x_573 = lean_alloc_ctor(1, 4, 8);
} else {
 x_573 = x_569;
}
lean_ctor_set(x_573, 0, x_564);
lean_ctor_set(x_573, 1, x_50);
lean_ctor_set(x_573, 2, x_51);
lean_ctor_set(x_573, 3, x_52);
lean_ctor_set_uint8(x_573, sizeof(void*)*4 + 6, x_456);
lean_ctor_set_uint32(x_573, sizeof(void*)*4, x_570);
lean_ctor_set_uint16(x_573, sizeof(void*)*4 + 4, x_571);
lean_ctor_set_uint8(x_573, sizeof(void*)*4 + 7, x_572);
x_574 = 0;
x_575 = 0;
x_576 = 0;
lean_ctor_set(x_356, 3, x_573);
lean_ctor_set(x_356, 2, x_563);
lean_ctor_set(x_356, 1, x_562);
lean_ctor_set(x_356, 0, x_568);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 6, x_529);
lean_ctor_set_uint32(x_356, sizeof(void*)*4, x_574);
lean_ctor_set_uint16(x_356, sizeof(void*)*4 + 4, x_575);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 7, x_576);
return x_356;
}
}
else
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; uint32_t x_584; uint16_t x_585; uint8_t x_586; lean_object* x_587; lean_object* x_588; uint32_t x_589; uint16_t x_590; uint8_t x_591; lean_object* x_592; uint32_t x_593; uint16_t x_594; uint8_t x_595; lean_object* x_596; 
x_577 = lean_ctor_get(x_356, 1);
x_578 = lean_ctor_get(x_356, 2);
lean_inc(x_578);
lean_inc(x_577);
lean_dec(x_356);
x_579 = lean_ctor_get(x_508, 0);
lean_inc(x_579);
x_580 = lean_ctor_get(x_508, 1);
lean_inc(x_580);
x_581 = lean_ctor_get(x_508, 2);
lean_inc(x_581);
x_582 = lean_ctor_get(x_508, 3);
lean_inc(x_582);
if (lean_is_exclusive(x_508)) {
 lean_ctor_release(x_508, 0);
 lean_ctor_release(x_508, 1);
 lean_ctor_release(x_508, 2);
 lean_ctor_release(x_508, 3);
 x_583 = x_508;
} else {
 lean_dec_ref(x_508);
 x_583 = lean_box(0);
}
x_584 = 0;
x_585 = 0;
x_586 = 0;
lean_inc(x_357);
if (lean_is_scalar(x_583)) {
 x_587 = lean_alloc_ctor(1, 4, 8);
} else {
 x_587 = x_583;
}
lean_ctor_set(x_587, 0, x_357);
lean_ctor_set(x_587, 1, x_577);
lean_ctor_set(x_587, 2, x_578);
lean_ctor_set(x_587, 3, x_579);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 lean_ctor_release(x_357, 1);
 lean_ctor_release(x_357, 2);
 lean_ctor_release(x_357, 3);
 x_588 = x_357;
} else {
 lean_dec_ref(x_357);
 x_588 = lean_box(0);
}
lean_ctor_set_uint8(x_587, sizeof(void*)*4 + 6, x_456);
lean_ctor_set_uint32(x_587, sizeof(void*)*4, x_584);
lean_ctor_set_uint16(x_587, sizeof(void*)*4 + 4, x_585);
lean_ctor_set_uint8(x_587, sizeof(void*)*4 + 7, x_586);
x_589 = 0;
x_590 = 0;
x_591 = 0;
if (lean_is_scalar(x_588)) {
 x_592 = lean_alloc_ctor(1, 4, 8);
} else {
 x_592 = x_588;
}
lean_ctor_set(x_592, 0, x_582);
lean_ctor_set(x_592, 1, x_50);
lean_ctor_set(x_592, 2, x_51);
lean_ctor_set(x_592, 3, x_52);
lean_ctor_set_uint8(x_592, sizeof(void*)*4 + 6, x_456);
lean_ctor_set_uint32(x_592, sizeof(void*)*4, x_589);
lean_ctor_set_uint16(x_592, sizeof(void*)*4 + 4, x_590);
lean_ctor_set_uint8(x_592, sizeof(void*)*4 + 7, x_591);
x_593 = 0;
x_594 = 0;
x_595 = 0;
x_596 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_596, 0, x_587);
lean_ctor_set(x_596, 1, x_580);
lean_ctor_set(x_596, 2, x_581);
lean_ctor_set(x_596, 3, x_592);
lean_ctor_set_uint8(x_596, sizeof(void*)*4 + 6, x_529);
lean_ctor_set_uint32(x_596, sizeof(void*)*4, x_593);
lean_ctor_set_uint16(x_596, sizeof(void*)*4 + 4, x_594);
lean_ctor_set_uint8(x_596, sizeof(void*)*4 + 7, x_595);
return x_596;
}
}
else
{
uint8_t x_597; 
x_597 = !lean_is_exclusive(x_356);
if (x_597 == 0)
{
lean_object* x_598; lean_object* x_599; uint8_t x_600; 
x_598 = lean_ctor_get(x_356, 3);
lean_dec(x_598);
x_599 = lean_ctor_get(x_356, 0);
lean_dec(x_599);
x_600 = !lean_is_exclusive(x_357);
if (x_600 == 0)
{
uint32_t x_601; uint16_t x_602; uint8_t x_603; uint8_t x_604; uint32_t x_605; uint16_t x_606; uint8_t x_607; uint32_t x_608; uint16_t x_609; uint8_t x_610; 
x_601 = 0;
x_602 = 0;
x_603 = 0;
lean_ctor_set_uint8(x_357, sizeof(void*)*4 + 6, x_529);
lean_ctor_set_uint32(x_357, sizeof(void*)*4, x_601);
lean_ctor_set_uint16(x_357, sizeof(void*)*4 + 4, x_602);
lean_ctor_set_uint8(x_357, sizeof(void*)*4 + 7, x_603);
x_604 = 0;
x_605 = 0;
x_606 = 0;
x_607 = 0;
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 6, x_604);
lean_ctor_set_uint32(x_356, sizeof(void*)*4, x_605);
lean_ctor_set_uint16(x_356, sizeof(void*)*4 + 4, x_606);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 7, x_607);
x_608 = 0;
x_609 = 0;
x_610 = 0;
lean_ctor_set(x_1, 0, x_356);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_529);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_608);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_609);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_610);
return x_1;
}
else
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; uint32_t x_615; uint16_t x_616; uint8_t x_617; lean_object* x_618; uint8_t x_619; uint32_t x_620; uint16_t x_621; uint8_t x_622; uint32_t x_623; uint16_t x_624; uint8_t x_625; 
x_611 = lean_ctor_get(x_357, 0);
x_612 = lean_ctor_get(x_357, 1);
x_613 = lean_ctor_get(x_357, 2);
x_614 = lean_ctor_get(x_357, 3);
lean_inc(x_614);
lean_inc(x_613);
lean_inc(x_612);
lean_inc(x_611);
lean_dec(x_357);
x_615 = 0;
x_616 = 0;
x_617 = 0;
x_618 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_618, 0, x_611);
lean_ctor_set(x_618, 1, x_612);
lean_ctor_set(x_618, 2, x_613);
lean_ctor_set(x_618, 3, x_614);
lean_ctor_set_uint8(x_618, sizeof(void*)*4 + 6, x_529);
lean_ctor_set_uint32(x_618, sizeof(void*)*4, x_615);
lean_ctor_set_uint16(x_618, sizeof(void*)*4 + 4, x_616);
lean_ctor_set_uint8(x_618, sizeof(void*)*4 + 7, x_617);
x_619 = 0;
x_620 = 0;
x_621 = 0;
x_622 = 0;
lean_ctor_set(x_356, 0, x_618);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 6, x_619);
lean_ctor_set_uint32(x_356, sizeof(void*)*4, x_620);
lean_ctor_set_uint16(x_356, sizeof(void*)*4 + 4, x_621);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 7, x_622);
x_623 = 0;
x_624 = 0;
x_625 = 0;
lean_ctor_set(x_1, 0, x_356);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_529);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_623);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_624);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_625);
return x_1;
}
}
else
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; uint32_t x_633; uint16_t x_634; uint8_t x_635; lean_object* x_636; uint8_t x_637; uint32_t x_638; uint16_t x_639; uint8_t x_640; lean_object* x_641; uint32_t x_642; uint16_t x_643; uint8_t x_644; 
x_626 = lean_ctor_get(x_356, 1);
x_627 = lean_ctor_get(x_356, 2);
lean_inc(x_627);
lean_inc(x_626);
lean_dec(x_356);
x_628 = lean_ctor_get(x_357, 0);
lean_inc(x_628);
x_629 = lean_ctor_get(x_357, 1);
lean_inc(x_629);
x_630 = lean_ctor_get(x_357, 2);
lean_inc(x_630);
x_631 = lean_ctor_get(x_357, 3);
lean_inc(x_631);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 lean_ctor_release(x_357, 1);
 lean_ctor_release(x_357, 2);
 lean_ctor_release(x_357, 3);
 x_632 = x_357;
} else {
 lean_dec_ref(x_357);
 x_632 = lean_box(0);
}
x_633 = 0;
x_634 = 0;
x_635 = 0;
if (lean_is_scalar(x_632)) {
 x_636 = lean_alloc_ctor(1, 4, 8);
} else {
 x_636 = x_632;
}
lean_ctor_set(x_636, 0, x_628);
lean_ctor_set(x_636, 1, x_629);
lean_ctor_set(x_636, 2, x_630);
lean_ctor_set(x_636, 3, x_631);
lean_ctor_set_uint8(x_636, sizeof(void*)*4 + 6, x_529);
lean_ctor_set_uint32(x_636, sizeof(void*)*4, x_633);
lean_ctor_set_uint16(x_636, sizeof(void*)*4 + 4, x_634);
lean_ctor_set_uint8(x_636, sizeof(void*)*4 + 7, x_635);
x_637 = 0;
x_638 = 0;
x_639 = 0;
x_640 = 0;
x_641 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_641, 0, x_636);
lean_ctor_set(x_641, 1, x_626);
lean_ctor_set(x_641, 2, x_627);
lean_ctor_set(x_641, 3, x_508);
lean_ctor_set_uint8(x_641, sizeof(void*)*4 + 6, x_637);
lean_ctor_set_uint32(x_641, sizeof(void*)*4, x_638);
lean_ctor_set_uint16(x_641, sizeof(void*)*4 + 4, x_639);
lean_ctor_set_uint8(x_641, sizeof(void*)*4 + 7, x_640);
x_642 = 0;
x_643 = 0;
x_644 = 0;
lean_ctor_set(x_1, 0, x_641);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_529);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_642);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_643);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_644);
return x_1;
}
}
}
}
}
}
}
}
else
{
lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; uint8_t x_649; 
x_645 = lean_ctor_get(x_1, 0);
x_646 = lean_ctor_get(x_1, 1);
x_647 = lean_ctor_get(x_1, 2);
x_648 = lean_ctor_get(x_1, 3);
lean_inc(x_648);
lean_inc(x_647);
lean_inc(x_646);
lean_inc(x_645);
lean_dec(x_1);
x_649 = lean_nat_dec_lt(x_2, x_646);
if (x_649 == 0)
{
uint8_t x_650; 
x_650 = lean_nat_dec_lt(x_646, x_2);
if (x_650 == 0)
{
uint32_t x_651; uint16_t x_652; uint8_t x_653; lean_object* x_654; 
lean_dec(x_647);
lean_dec(x_646);
x_651 = 0;
x_652 = 0;
x_653 = 0;
x_654 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_654, 0, x_645);
lean_ctor_set(x_654, 1, x_2);
lean_ctor_set(x_654, 2, x_3);
lean_ctor_set(x_654, 3, x_648);
lean_ctor_set_uint8(x_654, sizeof(void*)*4 + 6, x_9);
lean_ctor_set_uint32(x_654, sizeof(void*)*4, x_651);
lean_ctor_set_uint16(x_654, sizeof(void*)*4 + 4, x_652);
lean_ctor_set_uint8(x_654, sizeof(void*)*4 + 7, x_653);
return x_654;
}
else
{
uint8_t x_655; 
x_655 = l_RBNode_isRed___rarg(x_648);
if (x_655 == 0)
{
lean_object* x_656; uint32_t x_657; uint16_t x_658; uint8_t x_659; lean_object* x_660; 
x_656 = l_RBNode_ins___main___at_Lean_IR_mkIndexSet___spec__2(x_648, x_2, x_3);
x_657 = 0;
x_658 = 0;
x_659 = 0;
x_660 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_660, 0, x_645);
lean_ctor_set(x_660, 1, x_646);
lean_ctor_set(x_660, 2, x_647);
lean_ctor_set(x_660, 3, x_656);
lean_ctor_set_uint8(x_660, sizeof(void*)*4 + 6, x_9);
lean_ctor_set_uint32(x_660, sizeof(void*)*4, x_657);
lean_ctor_set_uint16(x_660, sizeof(void*)*4 + 4, x_658);
lean_ctor_set_uint8(x_660, sizeof(void*)*4 + 7, x_659);
return x_660;
}
else
{
lean_object* x_661; lean_object* x_662; 
x_661 = l_RBNode_ins___main___at_Lean_IR_mkIndexSet___spec__2(x_648, x_2, x_3);
x_662 = lean_ctor_get(x_661, 0);
lean_inc(x_662);
if (lean_obj_tag(x_662) == 0)
{
lean_object* x_663; 
x_663 = lean_ctor_get(x_661, 3);
lean_inc(x_663);
if (lean_obj_tag(x_663) == 0)
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; uint8_t x_667; uint32_t x_668; uint16_t x_669; uint8_t x_670; lean_object* x_671; uint8_t x_672; uint32_t x_673; uint16_t x_674; uint8_t x_675; lean_object* x_676; 
x_664 = lean_ctor_get(x_661, 1);
lean_inc(x_664);
x_665 = lean_ctor_get(x_661, 2);
lean_inc(x_665);
if (lean_is_exclusive(x_661)) {
 lean_ctor_release(x_661, 0);
 lean_ctor_release(x_661, 1);
 lean_ctor_release(x_661, 2);
 lean_ctor_release(x_661, 3);
 x_666 = x_661;
} else {
 lean_dec_ref(x_661);
 x_666 = lean_box(0);
}
x_667 = 0;
x_668 = 0;
x_669 = 0;
x_670 = 0;
if (lean_is_scalar(x_666)) {
 x_671 = lean_alloc_ctor(1, 4, 8);
} else {
 x_671 = x_666;
}
lean_ctor_set(x_671, 0, x_663);
lean_ctor_set(x_671, 1, x_664);
lean_ctor_set(x_671, 2, x_665);
lean_ctor_set(x_671, 3, x_663);
lean_ctor_set_uint8(x_671, sizeof(void*)*4 + 6, x_667);
lean_ctor_set_uint32(x_671, sizeof(void*)*4, x_668);
lean_ctor_set_uint16(x_671, sizeof(void*)*4 + 4, x_669);
lean_ctor_set_uint8(x_671, sizeof(void*)*4 + 7, x_670);
x_672 = 1;
x_673 = 0;
x_674 = 0;
x_675 = 0;
x_676 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_676, 0, x_645);
lean_ctor_set(x_676, 1, x_646);
lean_ctor_set(x_676, 2, x_647);
lean_ctor_set(x_676, 3, x_671);
lean_ctor_set_uint8(x_676, sizeof(void*)*4 + 6, x_672);
lean_ctor_set_uint32(x_676, sizeof(void*)*4, x_673);
lean_ctor_set_uint16(x_676, sizeof(void*)*4 + 4, x_674);
lean_ctor_set_uint8(x_676, sizeof(void*)*4 + 7, x_675);
return x_676;
}
else
{
uint8_t x_677; 
x_677 = lean_ctor_get_uint8(x_663, sizeof(void*)*4 + 6);
if (x_677 == 0)
{
lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; uint8_t x_686; uint32_t x_687; uint16_t x_688; uint8_t x_689; lean_object* x_690; uint32_t x_691; uint16_t x_692; uint8_t x_693; lean_object* x_694; uint32_t x_695; uint16_t x_696; uint8_t x_697; lean_object* x_698; 
x_678 = lean_ctor_get(x_661, 1);
lean_inc(x_678);
x_679 = lean_ctor_get(x_661, 2);
lean_inc(x_679);
if (lean_is_exclusive(x_661)) {
 lean_ctor_release(x_661, 0);
 lean_ctor_release(x_661, 1);
 lean_ctor_release(x_661, 2);
 lean_ctor_release(x_661, 3);
 x_680 = x_661;
} else {
 lean_dec_ref(x_661);
 x_680 = lean_box(0);
}
x_681 = lean_ctor_get(x_663, 0);
lean_inc(x_681);
x_682 = lean_ctor_get(x_663, 1);
lean_inc(x_682);
x_683 = lean_ctor_get(x_663, 2);
lean_inc(x_683);
x_684 = lean_ctor_get(x_663, 3);
lean_inc(x_684);
if (lean_is_exclusive(x_663)) {
 lean_ctor_release(x_663, 0);
 lean_ctor_release(x_663, 1);
 lean_ctor_release(x_663, 2);
 lean_ctor_release(x_663, 3);
 x_685 = x_663;
} else {
 lean_dec_ref(x_663);
 x_685 = lean_box(0);
}
x_686 = 1;
x_687 = 0;
x_688 = 0;
x_689 = 0;
if (lean_is_scalar(x_685)) {
 x_690 = lean_alloc_ctor(1, 4, 8);
} else {
 x_690 = x_685;
}
lean_ctor_set(x_690, 0, x_645);
lean_ctor_set(x_690, 1, x_646);
lean_ctor_set(x_690, 2, x_647);
lean_ctor_set(x_690, 3, x_662);
lean_ctor_set_uint8(x_690, sizeof(void*)*4 + 6, x_686);
lean_ctor_set_uint32(x_690, sizeof(void*)*4, x_687);
lean_ctor_set_uint16(x_690, sizeof(void*)*4 + 4, x_688);
lean_ctor_set_uint8(x_690, sizeof(void*)*4 + 7, x_689);
x_691 = 0;
x_692 = 0;
x_693 = 0;
if (lean_is_scalar(x_680)) {
 x_694 = lean_alloc_ctor(1, 4, 8);
} else {
 x_694 = x_680;
}
lean_ctor_set(x_694, 0, x_681);
lean_ctor_set(x_694, 1, x_682);
lean_ctor_set(x_694, 2, x_683);
lean_ctor_set(x_694, 3, x_684);
lean_ctor_set_uint8(x_694, sizeof(void*)*4 + 6, x_686);
lean_ctor_set_uint32(x_694, sizeof(void*)*4, x_691);
lean_ctor_set_uint16(x_694, sizeof(void*)*4 + 4, x_692);
lean_ctor_set_uint8(x_694, sizeof(void*)*4 + 7, x_693);
x_695 = 0;
x_696 = 0;
x_697 = 0;
x_698 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_698, 0, x_690);
lean_ctor_set(x_698, 1, x_678);
lean_ctor_set(x_698, 2, x_679);
lean_ctor_set(x_698, 3, x_694);
lean_ctor_set_uint8(x_698, sizeof(void*)*4 + 6, x_677);
lean_ctor_set_uint32(x_698, sizeof(void*)*4, x_695);
lean_ctor_set_uint16(x_698, sizeof(void*)*4 + 4, x_696);
lean_ctor_set_uint8(x_698, sizeof(void*)*4 + 7, x_697);
return x_698;
}
else
{
lean_object* x_699; lean_object* x_700; lean_object* x_701; uint8_t x_702; uint32_t x_703; uint16_t x_704; uint8_t x_705; lean_object* x_706; uint32_t x_707; uint16_t x_708; uint8_t x_709; lean_object* x_710; 
x_699 = lean_ctor_get(x_661, 1);
lean_inc(x_699);
x_700 = lean_ctor_get(x_661, 2);
lean_inc(x_700);
if (lean_is_exclusive(x_661)) {
 lean_ctor_release(x_661, 0);
 lean_ctor_release(x_661, 1);
 lean_ctor_release(x_661, 2);
 lean_ctor_release(x_661, 3);
 x_701 = x_661;
} else {
 lean_dec_ref(x_661);
 x_701 = lean_box(0);
}
x_702 = 0;
x_703 = 0;
x_704 = 0;
x_705 = 0;
if (lean_is_scalar(x_701)) {
 x_706 = lean_alloc_ctor(1, 4, 8);
} else {
 x_706 = x_701;
}
lean_ctor_set(x_706, 0, x_662);
lean_ctor_set(x_706, 1, x_699);
lean_ctor_set(x_706, 2, x_700);
lean_ctor_set(x_706, 3, x_663);
lean_ctor_set_uint8(x_706, sizeof(void*)*4 + 6, x_702);
lean_ctor_set_uint32(x_706, sizeof(void*)*4, x_703);
lean_ctor_set_uint16(x_706, sizeof(void*)*4 + 4, x_704);
lean_ctor_set_uint8(x_706, sizeof(void*)*4 + 7, x_705);
x_707 = 0;
x_708 = 0;
x_709 = 0;
x_710 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_710, 0, x_645);
lean_ctor_set(x_710, 1, x_646);
lean_ctor_set(x_710, 2, x_647);
lean_ctor_set(x_710, 3, x_706);
lean_ctor_set_uint8(x_710, sizeof(void*)*4 + 6, x_677);
lean_ctor_set_uint32(x_710, sizeof(void*)*4, x_707);
lean_ctor_set_uint16(x_710, sizeof(void*)*4 + 4, x_708);
lean_ctor_set_uint8(x_710, sizeof(void*)*4 + 7, x_709);
return x_710;
}
}
}
else
{
uint8_t x_711; 
x_711 = lean_ctor_get_uint8(x_662, sizeof(void*)*4 + 6);
if (x_711 == 0)
{
lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; uint8_t x_721; uint32_t x_722; uint16_t x_723; uint8_t x_724; lean_object* x_725; uint32_t x_726; uint16_t x_727; uint8_t x_728; lean_object* x_729; uint32_t x_730; uint16_t x_731; uint8_t x_732; lean_object* x_733; 
x_712 = lean_ctor_get(x_661, 1);
lean_inc(x_712);
x_713 = lean_ctor_get(x_661, 2);
lean_inc(x_713);
x_714 = lean_ctor_get(x_661, 3);
lean_inc(x_714);
if (lean_is_exclusive(x_661)) {
 lean_ctor_release(x_661, 0);
 lean_ctor_release(x_661, 1);
 lean_ctor_release(x_661, 2);
 lean_ctor_release(x_661, 3);
 x_715 = x_661;
} else {
 lean_dec_ref(x_661);
 x_715 = lean_box(0);
}
x_716 = lean_ctor_get(x_662, 0);
lean_inc(x_716);
x_717 = lean_ctor_get(x_662, 1);
lean_inc(x_717);
x_718 = lean_ctor_get(x_662, 2);
lean_inc(x_718);
x_719 = lean_ctor_get(x_662, 3);
lean_inc(x_719);
if (lean_is_exclusive(x_662)) {
 lean_ctor_release(x_662, 0);
 lean_ctor_release(x_662, 1);
 lean_ctor_release(x_662, 2);
 lean_ctor_release(x_662, 3);
 x_720 = x_662;
} else {
 lean_dec_ref(x_662);
 x_720 = lean_box(0);
}
x_721 = 1;
x_722 = 0;
x_723 = 0;
x_724 = 0;
if (lean_is_scalar(x_720)) {
 x_725 = lean_alloc_ctor(1, 4, 8);
} else {
 x_725 = x_720;
}
lean_ctor_set(x_725, 0, x_645);
lean_ctor_set(x_725, 1, x_646);
lean_ctor_set(x_725, 2, x_647);
lean_ctor_set(x_725, 3, x_716);
lean_ctor_set_uint8(x_725, sizeof(void*)*4 + 6, x_721);
lean_ctor_set_uint32(x_725, sizeof(void*)*4, x_722);
lean_ctor_set_uint16(x_725, sizeof(void*)*4 + 4, x_723);
lean_ctor_set_uint8(x_725, sizeof(void*)*4 + 7, x_724);
x_726 = 0;
x_727 = 0;
x_728 = 0;
if (lean_is_scalar(x_715)) {
 x_729 = lean_alloc_ctor(1, 4, 8);
} else {
 x_729 = x_715;
}
lean_ctor_set(x_729, 0, x_719);
lean_ctor_set(x_729, 1, x_712);
lean_ctor_set(x_729, 2, x_713);
lean_ctor_set(x_729, 3, x_714);
lean_ctor_set_uint8(x_729, sizeof(void*)*4 + 6, x_721);
lean_ctor_set_uint32(x_729, sizeof(void*)*4, x_726);
lean_ctor_set_uint16(x_729, sizeof(void*)*4 + 4, x_727);
lean_ctor_set_uint8(x_729, sizeof(void*)*4 + 7, x_728);
x_730 = 0;
x_731 = 0;
x_732 = 0;
x_733 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_733, 0, x_725);
lean_ctor_set(x_733, 1, x_717);
lean_ctor_set(x_733, 2, x_718);
lean_ctor_set(x_733, 3, x_729);
lean_ctor_set_uint8(x_733, sizeof(void*)*4 + 6, x_711);
lean_ctor_set_uint32(x_733, sizeof(void*)*4, x_730);
lean_ctor_set_uint16(x_733, sizeof(void*)*4 + 4, x_731);
lean_ctor_set_uint8(x_733, sizeof(void*)*4 + 7, x_732);
return x_733;
}
else
{
lean_object* x_734; 
x_734 = lean_ctor_get(x_661, 3);
lean_inc(x_734);
if (lean_obj_tag(x_734) == 0)
{
lean_object* x_735; lean_object* x_736; lean_object* x_737; uint8_t x_738; uint32_t x_739; uint16_t x_740; uint8_t x_741; lean_object* x_742; uint32_t x_743; uint16_t x_744; uint8_t x_745; lean_object* x_746; 
x_735 = lean_ctor_get(x_661, 1);
lean_inc(x_735);
x_736 = lean_ctor_get(x_661, 2);
lean_inc(x_736);
if (lean_is_exclusive(x_661)) {
 lean_ctor_release(x_661, 0);
 lean_ctor_release(x_661, 1);
 lean_ctor_release(x_661, 2);
 lean_ctor_release(x_661, 3);
 x_737 = x_661;
} else {
 lean_dec_ref(x_661);
 x_737 = lean_box(0);
}
x_738 = 0;
x_739 = 0;
x_740 = 0;
x_741 = 0;
if (lean_is_scalar(x_737)) {
 x_742 = lean_alloc_ctor(1, 4, 8);
} else {
 x_742 = x_737;
}
lean_ctor_set(x_742, 0, x_662);
lean_ctor_set(x_742, 1, x_735);
lean_ctor_set(x_742, 2, x_736);
lean_ctor_set(x_742, 3, x_734);
lean_ctor_set_uint8(x_742, sizeof(void*)*4 + 6, x_738);
lean_ctor_set_uint32(x_742, sizeof(void*)*4, x_739);
lean_ctor_set_uint16(x_742, sizeof(void*)*4 + 4, x_740);
lean_ctor_set_uint8(x_742, sizeof(void*)*4 + 7, x_741);
x_743 = 0;
x_744 = 0;
x_745 = 0;
x_746 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_746, 0, x_645);
lean_ctor_set(x_746, 1, x_646);
lean_ctor_set(x_746, 2, x_647);
lean_ctor_set(x_746, 3, x_742);
lean_ctor_set_uint8(x_746, sizeof(void*)*4 + 6, x_711);
lean_ctor_set_uint32(x_746, sizeof(void*)*4, x_743);
lean_ctor_set_uint16(x_746, sizeof(void*)*4 + 4, x_744);
lean_ctor_set_uint8(x_746, sizeof(void*)*4 + 7, x_745);
return x_746;
}
else
{
uint8_t x_747; 
x_747 = lean_ctor_get_uint8(x_734, sizeof(void*)*4 + 6);
if (x_747 == 0)
{
lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; uint32_t x_756; uint16_t x_757; uint8_t x_758; lean_object* x_759; lean_object* x_760; uint32_t x_761; uint16_t x_762; uint8_t x_763; lean_object* x_764; uint32_t x_765; uint16_t x_766; uint8_t x_767; lean_object* x_768; 
x_748 = lean_ctor_get(x_661, 1);
lean_inc(x_748);
x_749 = lean_ctor_get(x_661, 2);
lean_inc(x_749);
if (lean_is_exclusive(x_661)) {
 lean_ctor_release(x_661, 0);
 lean_ctor_release(x_661, 1);
 lean_ctor_release(x_661, 2);
 lean_ctor_release(x_661, 3);
 x_750 = x_661;
} else {
 lean_dec_ref(x_661);
 x_750 = lean_box(0);
}
x_751 = lean_ctor_get(x_734, 0);
lean_inc(x_751);
x_752 = lean_ctor_get(x_734, 1);
lean_inc(x_752);
x_753 = lean_ctor_get(x_734, 2);
lean_inc(x_753);
x_754 = lean_ctor_get(x_734, 3);
lean_inc(x_754);
if (lean_is_exclusive(x_734)) {
 lean_ctor_release(x_734, 0);
 lean_ctor_release(x_734, 1);
 lean_ctor_release(x_734, 2);
 lean_ctor_release(x_734, 3);
 x_755 = x_734;
} else {
 lean_dec_ref(x_734);
 x_755 = lean_box(0);
}
x_756 = 0;
x_757 = 0;
x_758 = 0;
lean_inc(x_662);
if (lean_is_scalar(x_755)) {
 x_759 = lean_alloc_ctor(1, 4, 8);
} else {
 x_759 = x_755;
}
lean_ctor_set(x_759, 0, x_645);
lean_ctor_set(x_759, 1, x_646);
lean_ctor_set(x_759, 2, x_647);
lean_ctor_set(x_759, 3, x_662);
if (lean_is_exclusive(x_662)) {
 lean_ctor_release(x_662, 0);
 lean_ctor_release(x_662, 1);
 lean_ctor_release(x_662, 2);
 lean_ctor_release(x_662, 3);
 x_760 = x_662;
} else {
 lean_dec_ref(x_662);
 x_760 = lean_box(0);
}
lean_ctor_set_uint8(x_759, sizeof(void*)*4 + 6, x_711);
lean_ctor_set_uint32(x_759, sizeof(void*)*4, x_756);
lean_ctor_set_uint16(x_759, sizeof(void*)*4 + 4, x_757);
lean_ctor_set_uint8(x_759, sizeof(void*)*4 + 7, x_758);
x_761 = 0;
x_762 = 0;
x_763 = 0;
if (lean_is_scalar(x_760)) {
 x_764 = lean_alloc_ctor(1, 4, 8);
} else {
 x_764 = x_760;
}
lean_ctor_set(x_764, 0, x_751);
lean_ctor_set(x_764, 1, x_752);
lean_ctor_set(x_764, 2, x_753);
lean_ctor_set(x_764, 3, x_754);
lean_ctor_set_uint8(x_764, sizeof(void*)*4 + 6, x_711);
lean_ctor_set_uint32(x_764, sizeof(void*)*4, x_761);
lean_ctor_set_uint16(x_764, sizeof(void*)*4 + 4, x_762);
lean_ctor_set_uint8(x_764, sizeof(void*)*4 + 7, x_763);
x_765 = 0;
x_766 = 0;
x_767 = 0;
if (lean_is_scalar(x_750)) {
 x_768 = lean_alloc_ctor(1, 4, 8);
} else {
 x_768 = x_750;
}
lean_ctor_set(x_768, 0, x_759);
lean_ctor_set(x_768, 1, x_748);
lean_ctor_set(x_768, 2, x_749);
lean_ctor_set(x_768, 3, x_764);
lean_ctor_set_uint8(x_768, sizeof(void*)*4 + 6, x_747);
lean_ctor_set_uint32(x_768, sizeof(void*)*4, x_765);
lean_ctor_set_uint16(x_768, sizeof(void*)*4 + 4, x_766);
lean_ctor_set_uint8(x_768, sizeof(void*)*4 + 7, x_767);
return x_768;
}
else
{
lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; uint32_t x_777; uint16_t x_778; uint8_t x_779; lean_object* x_780; uint8_t x_781; uint32_t x_782; uint16_t x_783; uint8_t x_784; lean_object* x_785; uint32_t x_786; uint16_t x_787; uint8_t x_788; lean_object* x_789; 
x_769 = lean_ctor_get(x_661, 1);
lean_inc(x_769);
x_770 = lean_ctor_get(x_661, 2);
lean_inc(x_770);
if (lean_is_exclusive(x_661)) {
 lean_ctor_release(x_661, 0);
 lean_ctor_release(x_661, 1);
 lean_ctor_release(x_661, 2);
 lean_ctor_release(x_661, 3);
 x_771 = x_661;
} else {
 lean_dec_ref(x_661);
 x_771 = lean_box(0);
}
x_772 = lean_ctor_get(x_662, 0);
lean_inc(x_772);
x_773 = lean_ctor_get(x_662, 1);
lean_inc(x_773);
x_774 = lean_ctor_get(x_662, 2);
lean_inc(x_774);
x_775 = lean_ctor_get(x_662, 3);
lean_inc(x_775);
if (lean_is_exclusive(x_662)) {
 lean_ctor_release(x_662, 0);
 lean_ctor_release(x_662, 1);
 lean_ctor_release(x_662, 2);
 lean_ctor_release(x_662, 3);
 x_776 = x_662;
} else {
 lean_dec_ref(x_662);
 x_776 = lean_box(0);
}
x_777 = 0;
x_778 = 0;
x_779 = 0;
if (lean_is_scalar(x_776)) {
 x_780 = lean_alloc_ctor(1, 4, 8);
} else {
 x_780 = x_776;
}
lean_ctor_set(x_780, 0, x_772);
lean_ctor_set(x_780, 1, x_773);
lean_ctor_set(x_780, 2, x_774);
lean_ctor_set(x_780, 3, x_775);
lean_ctor_set_uint8(x_780, sizeof(void*)*4 + 6, x_747);
lean_ctor_set_uint32(x_780, sizeof(void*)*4, x_777);
lean_ctor_set_uint16(x_780, sizeof(void*)*4 + 4, x_778);
lean_ctor_set_uint8(x_780, sizeof(void*)*4 + 7, x_779);
x_781 = 0;
x_782 = 0;
x_783 = 0;
x_784 = 0;
if (lean_is_scalar(x_771)) {
 x_785 = lean_alloc_ctor(1, 4, 8);
} else {
 x_785 = x_771;
}
lean_ctor_set(x_785, 0, x_780);
lean_ctor_set(x_785, 1, x_769);
lean_ctor_set(x_785, 2, x_770);
lean_ctor_set(x_785, 3, x_734);
lean_ctor_set_uint8(x_785, sizeof(void*)*4 + 6, x_781);
lean_ctor_set_uint32(x_785, sizeof(void*)*4, x_782);
lean_ctor_set_uint16(x_785, sizeof(void*)*4 + 4, x_783);
lean_ctor_set_uint8(x_785, sizeof(void*)*4 + 7, x_784);
x_786 = 0;
x_787 = 0;
x_788 = 0;
x_789 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_789, 0, x_645);
lean_ctor_set(x_789, 1, x_646);
lean_ctor_set(x_789, 2, x_647);
lean_ctor_set(x_789, 3, x_785);
lean_ctor_set_uint8(x_789, sizeof(void*)*4 + 6, x_747);
lean_ctor_set_uint32(x_789, sizeof(void*)*4, x_786);
lean_ctor_set_uint16(x_789, sizeof(void*)*4 + 4, x_787);
lean_ctor_set_uint8(x_789, sizeof(void*)*4 + 7, x_788);
return x_789;
}
}
}
}
}
}
}
else
{
uint8_t x_790; 
x_790 = l_RBNode_isRed___rarg(x_645);
if (x_790 == 0)
{
lean_object* x_791; uint32_t x_792; uint16_t x_793; uint8_t x_794; lean_object* x_795; 
x_791 = l_RBNode_ins___main___at_Lean_IR_mkIndexSet___spec__2(x_645, x_2, x_3);
x_792 = 0;
x_793 = 0;
x_794 = 0;
x_795 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_795, 0, x_791);
lean_ctor_set(x_795, 1, x_646);
lean_ctor_set(x_795, 2, x_647);
lean_ctor_set(x_795, 3, x_648);
lean_ctor_set_uint8(x_795, sizeof(void*)*4 + 6, x_9);
lean_ctor_set_uint32(x_795, sizeof(void*)*4, x_792);
lean_ctor_set_uint16(x_795, sizeof(void*)*4 + 4, x_793);
lean_ctor_set_uint8(x_795, sizeof(void*)*4 + 7, x_794);
return x_795;
}
else
{
lean_object* x_796; lean_object* x_797; 
x_796 = l_RBNode_ins___main___at_Lean_IR_mkIndexSet___spec__2(x_645, x_2, x_3);
x_797 = lean_ctor_get(x_796, 0);
lean_inc(x_797);
if (lean_obj_tag(x_797) == 0)
{
lean_object* x_798; 
x_798 = lean_ctor_get(x_796, 3);
lean_inc(x_798);
if (lean_obj_tag(x_798) == 0)
{
lean_object* x_799; lean_object* x_800; lean_object* x_801; uint8_t x_802; uint32_t x_803; uint16_t x_804; uint8_t x_805; lean_object* x_806; uint8_t x_807; uint32_t x_808; uint16_t x_809; uint8_t x_810; lean_object* x_811; 
x_799 = lean_ctor_get(x_796, 1);
lean_inc(x_799);
x_800 = lean_ctor_get(x_796, 2);
lean_inc(x_800);
if (lean_is_exclusive(x_796)) {
 lean_ctor_release(x_796, 0);
 lean_ctor_release(x_796, 1);
 lean_ctor_release(x_796, 2);
 lean_ctor_release(x_796, 3);
 x_801 = x_796;
} else {
 lean_dec_ref(x_796);
 x_801 = lean_box(0);
}
x_802 = 0;
x_803 = 0;
x_804 = 0;
x_805 = 0;
if (lean_is_scalar(x_801)) {
 x_806 = lean_alloc_ctor(1, 4, 8);
} else {
 x_806 = x_801;
}
lean_ctor_set(x_806, 0, x_798);
lean_ctor_set(x_806, 1, x_799);
lean_ctor_set(x_806, 2, x_800);
lean_ctor_set(x_806, 3, x_798);
lean_ctor_set_uint8(x_806, sizeof(void*)*4 + 6, x_802);
lean_ctor_set_uint32(x_806, sizeof(void*)*4, x_803);
lean_ctor_set_uint16(x_806, sizeof(void*)*4 + 4, x_804);
lean_ctor_set_uint8(x_806, sizeof(void*)*4 + 7, x_805);
x_807 = 1;
x_808 = 0;
x_809 = 0;
x_810 = 0;
x_811 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_811, 0, x_806);
lean_ctor_set(x_811, 1, x_646);
lean_ctor_set(x_811, 2, x_647);
lean_ctor_set(x_811, 3, x_648);
lean_ctor_set_uint8(x_811, sizeof(void*)*4 + 6, x_807);
lean_ctor_set_uint32(x_811, sizeof(void*)*4, x_808);
lean_ctor_set_uint16(x_811, sizeof(void*)*4 + 4, x_809);
lean_ctor_set_uint8(x_811, sizeof(void*)*4 + 7, x_810);
return x_811;
}
else
{
uint8_t x_812; 
x_812 = lean_ctor_get_uint8(x_798, sizeof(void*)*4 + 6);
if (x_812 == 0)
{
lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; uint8_t x_821; uint32_t x_822; uint16_t x_823; uint8_t x_824; lean_object* x_825; uint32_t x_826; uint16_t x_827; uint8_t x_828; lean_object* x_829; uint32_t x_830; uint16_t x_831; uint8_t x_832; lean_object* x_833; 
x_813 = lean_ctor_get(x_796, 1);
lean_inc(x_813);
x_814 = lean_ctor_get(x_796, 2);
lean_inc(x_814);
if (lean_is_exclusive(x_796)) {
 lean_ctor_release(x_796, 0);
 lean_ctor_release(x_796, 1);
 lean_ctor_release(x_796, 2);
 lean_ctor_release(x_796, 3);
 x_815 = x_796;
} else {
 lean_dec_ref(x_796);
 x_815 = lean_box(0);
}
x_816 = lean_ctor_get(x_798, 0);
lean_inc(x_816);
x_817 = lean_ctor_get(x_798, 1);
lean_inc(x_817);
x_818 = lean_ctor_get(x_798, 2);
lean_inc(x_818);
x_819 = lean_ctor_get(x_798, 3);
lean_inc(x_819);
if (lean_is_exclusive(x_798)) {
 lean_ctor_release(x_798, 0);
 lean_ctor_release(x_798, 1);
 lean_ctor_release(x_798, 2);
 lean_ctor_release(x_798, 3);
 x_820 = x_798;
} else {
 lean_dec_ref(x_798);
 x_820 = lean_box(0);
}
x_821 = 1;
x_822 = 0;
x_823 = 0;
x_824 = 0;
if (lean_is_scalar(x_820)) {
 x_825 = lean_alloc_ctor(1, 4, 8);
} else {
 x_825 = x_820;
}
lean_ctor_set(x_825, 0, x_797);
lean_ctor_set(x_825, 1, x_813);
lean_ctor_set(x_825, 2, x_814);
lean_ctor_set(x_825, 3, x_816);
lean_ctor_set_uint8(x_825, sizeof(void*)*4 + 6, x_821);
lean_ctor_set_uint32(x_825, sizeof(void*)*4, x_822);
lean_ctor_set_uint16(x_825, sizeof(void*)*4 + 4, x_823);
lean_ctor_set_uint8(x_825, sizeof(void*)*4 + 7, x_824);
x_826 = 0;
x_827 = 0;
x_828 = 0;
if (lean_is_scalar(x_815)) {
 x_829 = lean_alloc_ctor(1, 4, 8);
} else {
 x_829 = x_815;
}
lean_ctor_set(x_829, 0, x_819);
lean_ctor_set(x_829, 1, x_646);
lean_ctor_set(x_829, 2, x_647);
lean_ctor_set(x_829, 3, x_648);
lean_ctor_set_uint8(x_829, sizeof(void*)*4 + 6, x_821);
lean_ctor_set_uint32(x_829, sizeof(void*)*4, x_826);
lean_ctor_set_uint16(x_829, sizeof(void*)*4 + 4, x_827);
lean_ctor_set_uint8(x_829, sizeof(void*)*4 + 7, x_828);
x_830 = 0;
x_831 = 0;
x_832 = 0;
x_833 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_833, 0, x_825);
lean_ctor_set(x_833, 1, x_817);
lean_ctor_set(x_833, 2, x_818);
lean_ctor_set(x_833, 3, x_829);
lean_ctor_set_uint8(x_833, sizeof(void*)*4 + 6, x_812);
lean_ctor_set_uint32(x_833, sizeof(void*)*4, x_830);
lean_ctor_set_uint16(x_833, sizeof(void*)*4 + 4, x_831);
lean_ctor_set_uint8(x_833, sizeof(void*)*4 + 7, x_832);
return x_833;
}
else
{
lean_object* x_834; lean_object* x_835; lean_object* x_836; uint8_t x_837; uint32_t x_838; uint16_t x_839; uint8_t x_840; lean_object* x_841; uint32_t x_842; uint16_t x_843; uint8_t x_844; lean_object* x_845; 
x_834 = lean_ctor_get(x_796, 1);
lean_inc(x_834);
x_835 = lean_ctor_get(x_796, 2);
lean_inc(x_835);
if (lean_is_exclusive(x_796)) {
 lean_ctor_release(x_796, 0);
 lean_ctor_release(x_796, 1);
 lean_ctor_release(x_796, 2);
 lean_ctor_release(x_796, 3);
 x_836 = x_796;
} else {
 lean_dec_ref(x_796);
 x_836 = lean_box(0);
}
x_837 = 0;
x_838 = 0;
x_839 = 0;
x_840 = 0;
if (lean_is_scalar(x_836)) {
 x_841 = lean_alloc_ctor(1, 4, 8);
} else {
 x_841 = x_836;
}
lean_ctor_set(x_841, 0, x_797);
lean_ctor_set(x_841, 1, x_834);
lean_ctor_set(x_841, 2, x_835);
lean_ctor_set(x_841, 3, x_798);
lean_ctor_set_uint8(x_841, sizeof(void*)*4 + 6, x_837);
lean_ctor_set_uint32(x_841, sizeof(void*)*4, x_838);
lean_ctor_set_uint16(x_841, sizeof(void*)*4 + 4, x_839);
lean_ctor_set_uint8(x_841, sizeof(void*)*4 + 7, x_840);
x_842 = 0;
x_843 = 0;
x_844 = 0;
x_845 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_845, 0, x_841);
lean_ctor_set(x_845, 1, x_646);
lean_ctor_set(x_845, 2, x_647);
lean_ctor_set(x_845, 3, x_648);
lean_ctor_set_uint8(x_845, sizeof(void*)*4 + 6, x_812);
lean_ctor_set_uint32(x_845, sizeof(void*)*4, x_842);
lean_ctor_set_uint16(x_845, sizeof(void*)*4 + 4, x_843);
lean_ctor_set_uint8(x_845, sizeof(void*)*4 + 7, x_844);
return x_845;
}
}
}
else
{
uint8_t x_846; 
x_846 = lean_ctor_get_uint8(x_797, sizeof(void*)*4 + 6);
if (x_846 == 0)
{
lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; uint8_t x_856; uint32_t x_857; uint16_t x_858; uint8_t x_859; lean_object* x_860; uint32_t x_861; uint16_t x_862; uint8_t x_863; lean_object* x_864; uint32_t x_865; uint16_t x_866; uint8_t x_867; lean_object* x_868; 
x_847 = lean_ctor_get(x_796, 1);
lean_inc(x_847);
x_848 = lean_ctor_get(x_796, 2);
lean_inc(x_848);
x_849 = lean_ctor_get(x_796, 3);
lean_inc(x_849);
if (lean_is_exclusive(x_796)) {
 lean_ctor_release(x_796, 0);
 lean_ctor_release(x_796, 1);
 lean_ctor_release(x_796, 2);
 lean_ctor_release(x_796, 3);
 x_850 = x_796;
} else {
 lean_dec_ref(x_796);
 x_850 = lean_box(0);
}
x_851 = lean_ctor_get(x_797, 0);
lean_inc(x_851);
x_852 = lean_ctor_get(x_797, 1);
lean_inc(x_852);
x_853 = lean_ctor_get(x_797, 2);
lean_inc(x_853);
x_854 = lean_ctor_get(x_797, 3);
lean_inc(x_854);
if (lean_is_exclusive(x_797)) {
 lean_ctor_release(x_797, 0);
 lean_ctor_release(x_797, 1);
 lean_ctor_release(x_797, 2);
 lean_ctor_release(x_797, 3);
 x_855 = x_797;
} else {
 lean_dec_ref(x_797);
 x_855 = lean_box(0);
}
x_856 = 1;
x_857 = 0;
x_858 = 0;
x_859 = 0;
if (lean_is_scalar(x_855)) {
 x_860 = lean_alloc_ctor(1, 4, 8);
} else {
 x_860 = x_855;
}
lean_ctor_set(x_860, 0, x_851);
lean_ctor_set(x_860, 1, x_852);
lean_ctor_set(x_860, 2, x_853);
lean_ctor_set(x_860, 3, x_854);
lean_ctor_set_uint8(x_860, sizeof(void*)*4 + 6, x_856);
lean_ctor_set_uint32(x_860, sizeof(void*)*4, x_857);
lean_ctor_set_uint16(x_860, sizeof(void*)*4 + 4, x_858);
lean_ctor_set_uint8(x_860, sizeof(void*)*4 + 7, x_859);
x_861 = 0;
x_862 = 0;
x_863 = 0;
if (lean_is_scalar(x_850)) {
 x_864 = lean_alloc_ctor(1, 4, 8);
} else {
 x_864 = x_850;
}
lean_ctor_set(x_864, 0, x_849);
lean_ctor_set(x_864, 1, x_646);
lean_ctor_set(x_864, 2, x_647);
lean_ctor_set(x_864, 3, x_648);
lean_ctor_set_uint8(x_864, sizeof(void*)*4 + 6, x_856);
lean_ctor_set_uint32(x_864, sizeof(void*)*4, x_861);
lean_ctor_set_uint16(x_864, sizeof(void*)*4 + 4, x_862);
lean_ctor_set_uint8(x_864, sizeof(void*)*4 + 7, x_863);
x_865 = 0;
x_866 = 0;
x_867 = 0;
x_868 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_868, 0, x_860);
lean_ctor_set(x_868, 1, x_847);
lean_ctor_set(x_868, 2, x_848);
lean_ctor_set(x_868, 3, x_864);
lean_ctor_set_uint8(x_868, sizeof(void*)*4 + 6, x_846);
lean_ctor_set_uint32(x_868, sizeof(void*)*4, x_865);
lean_ctor_set_uint16(x_868, sizeof(void*)*4 + 4, x_866);
lean_ctor_set_uint8(x_868, sizeof(void*)*4 + 7, x_867);
return x_868;
}
else
{
lean_object* x_869; 
x_869 = lean_ctor_get(x_796, 3);
lean_inc(x_869);
if (lean_obj_tag(x_869) == 0)
{
lean_object* x_870; lean_object* x_871; lean_object* x_872; uint8_t x_873; uint32_t x_874; uint16_t x_875; uint8_t x_876; lean_object* x_877; uint32_t x_878; uint16_t x_879; uint8_t x_880; lean_object* x_881; 
x_870 = lean_ctor_get(x_796, 1);
lean_inc(x_870);
x_871 = lean_ctor_get(x_796, 2);
lean_inc(x_871);
if (lean_is_exclusive(x_796)) {
 lean_ctor_release(x_796, 0);
 lean_ctor_release(x_796, 1);
 lean_ctor_release(x_796, 2);
 lean_ctor_release(x_796, 3);
 x_872 = x_796;
} else {
 lean_dec_ref(x_796);
 x_872 = lean_box(0);
}
x_873 = 0;
x_874 = 0;
x_875 = 0;
x_876 = 0;
if (lean_is_scalar(x_872)) {
 x_877 = lean_alloc_ctor(1, 4, 8);
} else {
 x_877 = x_872;
}
lean_ctor_set(x_877, 0, x_797);
lean_ctor_set(x_877, 1, x_870);
lean_ctor_set(x_877, 2, x_871);
lean_ctor_set(x_877, 3, x_869);
lean_ctor_set_uint8(x_877, sizeof(void*)*4 + 6, x_873);
lean_ctor_set_uint32(x_877, sizeof(void*)*4, x_874);
lean_ctor_set_uint16(x_877, sizeof(void*)*4 + 4, x_875);
lean_ctor_set_uint8(x_877, sizeof(void*)*4 + 7, x_876);
x_878 = 0;
x_879 = 0;
x_880 = 0;
x_881 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_881, 0, x_877);
lean_ctor_set(x_881, 1, x_646);
lean_ctor_set(x_881, 2, x_647);
lean_ctor_set(x_881, 3, x_648);
lean_ctor_set_uint8(x_881, sizeof(void*)*4 + 6, x_846);
lean_ctor_set_uint32(x_881, sizeof(void*)*4, x_878);
lean_ctor_set_uint16(x_881, sizeof(void*)*4 + 4, x_879);
lean_ctor_set_uint8(x_881, sizeof(void*)*4 + 7, x_880);
return x_881;
}
else
{
uint8_t x_882; 
x_882 = lean_ctor_get_uint8(x_869, sizeof(void*)*4 + 6);
if (x_882 == 0)
{
lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; uint32_t x_891; uint16_t x_892; uint8_t x_893; lean_object* x_894; lean_object* x_895; uint32_t x_896; uint16_t x_897; uint8_t x_898; lean_object* x_899; uint32_t x_900; uint16_t x_901; uint8_t x_902; lean_object* x_903; 
x_883 = lean_ctor_get(x_796, 1);
lean_inc(x_883);
x_884 = lean_ctor_get(x_796, 2);
lean_inc(x_884);
if (lean_is_exclusive(x_796)) {
 lean_ctor_release(x_796, 0);
 lean_ctor_release(x_796, 1);
 lean_ctor_release(x_796, 2);
 lean_ctor_release(x_796, 3);
 x_885 = x_796;
} else {
 lean_dec_ref(x_796);
 x_885 = lean_box(0);
}
x_886 = lean_ctor_get(x_869, 0);
lean_inc(x_886);
x_887 = lean_ctor_get(x_869, 1);
lean_inc(x_887);
x_888 = lean_ctor_get(x_869, 2);
lean_inc(x_888);
x_889 = lean_ctor_get(x_869, 3);
lean_inc(x_889);
if (lean_is_exclusive(x_869)) {
 lean_ctor_release(x_869, 0);
 lean_ctor_release(x_869, 1);
 lean_ctor_release(x_869, 2);
 lean_ctor_release(x_869, 3);
 x_890 = x_869;
} else {
 lean_dec_ref(x_869);
 x_890 = lean_box(0);
}
x_891 = 0;
x_892 = 0;
x_893 = 0;
lean_inc(x_797);
if (lean_is_scalar(x_890)) {
 x_894 = lean_alloc_ctor(1, 4, 8);
} else {
 x_894 = x_890;
}
lean_ctor_set(x_894, 0, x_797);
lean_ctor_set(x_894, 1, x_883);
lean_ctor_set(x_894, 2, x_884);
lean_ctor_set(x_894, 3, x_886);
if (lean_is_exclusive(x_797)) {
 lean_ctor_release(x_797, 0);
 lean_ctor_release(x_797, 1);
 lean_ctor_release(x_797, 2);
 lean_ctor_release(x_797, 3);
 x_895 = x_797;
} else {
 lean_dec_ref(x_797);
 x_895 = lean_box(0);
}
lean_ctor_set_uint8(x_894, sizeof(void*)*4 + 6, x_846);
lean_ctor_set_uint32(x_894, sizeof(void*)*4, x_891);
lean_ctor_set_uint16(x_894, sizeof(void*)*4 + 4, x_892);
lean_ctor_set_uint8(x_894, sizeof(void*)*4 + 7, x_893);
x_896 = 0;
x_897 = 0;
x_898 = 0;
if (lean_is_scalar(x_895)) {
 x_899 = lean_alloc_ctor(1, 4, 8);
} else {
 x_899 = x_895;
}
lean_ctor_set(x_899, 0, x_889);
lean_ctor_set(x_899, 1, x_646);
lean_ctor_set(x_899, 2, x_647);
lean_ctor_set(x_899, 3, x_648);
lean_ctor_set_uint8(x_899, sizeof(void*)*4 + 6, x_846);
lean_ctor_set_uint32(x_899, sizeof(void*)*4, x_896);
lean_ctor_set_uint16(x_899, sizeof(void*)*4 + 4, x_897);
lean_ctor_set_uint8(x_899, sizeof(void*)*4 + 7, x_898);
x_900 = 0;
x_901 = 0;
x_902 = 0;
if (lean_is_scalar(x_885)) {
 x_903 = lean_alloc_ctor(1, 4, 8);
} else {
 x_903 = x_885;
}
lean_ctor_set(x_903, 0, x_894);
lean_ctor_set(x_903, 1, x_887);
lean_ctor_set(x_903, 2, x_888);
lean_ctor_set(x_903, 3, x_899);
lean_ctor_set_uint8(x_903, sizeof(void*)*4 + 6, x_882);
lean_ctor_set_uint32(x_903, sizeof(void*)*4, x_900);
lean_ctor_set_uint16(x_903, sizeof(void*)*4 + 4, x_901);
lean_ctor_set_uint8(x_903, sizeof(void*)*4 + 7, x_902);
return x_903;
}
else
{
lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; uint32_t x_912; uint16_t x_913; uint8_t x_914; lean_object* x_915; uint8_t x_916; uint32_t x_917; uint16_t x_918; uint8_t x_919; lean_object* x_920; uint32_t x_921; uint16_t x_922; uint8_t x_923; lean_object* x_924; 
x_904 = lean_ctor_get(x_796, 1);
lean_inc(x_904);
x_905 = lean_ctor_get(x_796, 2);
lean_inc(x_905);
if (lean_is_exclusive(x_796)) {
 lean_ctor_release(x_796, 0);
 lean_ctor_release(x_796, 1);
 lean_ctor_release(x_796, 2);
 lean_ctor_release(x_796, 3);
 x_906 = x_796;
} else {
 lean_dec_ref(x_796);
 x_906 = lean_box(0);
}
x_907 = lean_ctor_get(x_797, 0);
lean_inc(x_907);
x_908 = lean_ctor_get(x_797, 1);
lean_inc(x_908);
x_909 = lean_ctor_get(x_797, 2);
lean_inc(x_909);
x_910 = lean_ctor_get(x_797, 3);
lean_inc(x_910);
if (lean_is_exclusive(x_797)) {
 lean_ctor_release(x_797, 0);
 lean_ctor_release(x_797, 1);
 lean_ctor_release(x_797, 2);
 lean_ctor_release(x_797, 3);
 x_911 = x_797;
} else {
 lean_dec_ref(x_797);
 x_911 = lean_box(0);
}
x_912 = 0;
x_913 = 0;
x_914 = 0;
if (lean_is_scalar(x_911)) {
 x_915 = lean_alloc_ctor(1, 4, 8);
} else {
 x_915 = x_911;
}
lean_ctor_set(x_915, 0, x_907);
lean_ctor_set(x_915, 1, x_908);
lean_ctor_set(x_915, 2, x_909);
lean_ctor_set(x_915, 3, x_910);
lean_ctor_set_uint8(x_915, sizeof(void*)*4 + 6, x_882);
lean_ctor_set_uint32(x_915, sizeof(void*)*4, x_912);
lean_ctor_set_uint16(x_915, sizeof(void*)*4 + 4, x_913);
lean_ctor_set_uint8(x_915, sizeof(void*)*4 + 7, x_914);
x_916 = 0;
x_917 = 0;
x_918 = 0;
x_919 = 0;
if (lean_is_scalar(x_906)) {
 x_920 = lean_alloc_ctor(1, 4, 8);
} else {
 x_920 = x_906;
}
lean_ctor_set(x_920, 0, x_915);
lean_ctor_set(x_920, 1, x_904);
lean_ctor_set(x_920, 2, x_905);
lean_ctor_set(x_920, 3, x_869);
lean_ctor_set_uint8(x_920, sizeof(void*)*4 + 6, x_916);
lean_ctor_set_uint32(x_920, sizeof(void*)*4, x_917);
lean_ctor_set_uint16(x_920, sizeof(void*)*4 + 4, x_918);
lean_ctor_set_uint8(x_920, sizeof(void*)*4 + 7, x_919);
x_921 = 0;
x_922 = 0;
x_923 = 0;
x_924 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_924, 0, x_920);
lean_ctor_set(x_924, 1, x_646);
lean_ctor_set(x_924, 2, x_647);
lean_ctor_set(x_924, 3, x_648);
lean_ctor_set_uint8(x_924, sizeof(void*)*4 + 6, x_882);
lean_ctor_set_uint32(x_924, sizeof(void*)*4, x_921);
lean_ctor_set_uint16(x_924, sizeof(void*)*4 + 4, x_922);
lean_ctor_set_uint8(x_924, sizeof(void*)*4 + 7, x_923);
return x_924;
}
}
}
}
}
}
}
}
}
}
}
lean_object* l_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_RBNode_isRed___rarg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_RBNode_ins___main___at_Lean_IR_mkIndexSet___spec__2(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_RBNode_ins___main___at_Lean_IR_mkIndexSet___spec__2(x_1, x_2, x_3);
x_7 = l_RBNode_setBlack___rarg(x_6);
return x_7;
}
}
}
lean_object* l_Lean_IR_mkIndexSet(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = lean_box(0);
x_4 = l_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_2, x_1, x_3);
return x_4;
}
}
lean_object* l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; uint32_t x_5; uint16_t x_6; uint8_t x_7; lean_object* x_8; 
x_4 = 0;
x_5 = 0;
x_6 = 0;
x_7 = 0;
x_8 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 2, x_3);
lean_ctor_set(x_8, 3, x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*4 + 6, x_4);
lean_ctor_set_uint32(x_8, sizeof(void*)*4, x_5);
lean_ctor_set_uint16(x_8, sizeof(void*)*4 + 4, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*4 + 7, x_7);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 6);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_1, 2);
x_14 = lean_ctor_get(x_1, 3);
x_15 = lean_nat_dec_lt(x_2, x_12);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = lean_nat_dec_lt(x_12, x_2);
if (x_16 == 0)
{
uint32_t x_17; uint16_t x_18; uint8_t x_19; 
lean_dec(x_13);
lean_dec(x_12);
x_17 = 0;
x_18 = 0;
x_19 = 0;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_17);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_18);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_19);
return x_1;
}
else
{
lean_object* x_20; uint32_t x_21; uint16_t x_22; uint8_t x_23; 
x_20 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_14, x_2, x_3);
x_21 = 0;
x_22 = 0;
x_23 = 0;
lean_ctor_set(x_1, 3, x_20);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_21);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_22);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_23);
return x_1;
}
}
else
{
lean_object* x_24; uint32_t x_25; uint16_t x_26; uint8_t x_27; 
x_24 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_11, x_2, x_3);
x_25 = 0;
x_26 = 0;
x_27 = 0;
lean_ctor_set(x_1, 0, x_24);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_25);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_26);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_27);
return x_1;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_1, 0);
x_29 = lean_ctor_get(x_1, 1);
x_30 = lean_ctor_get(x_1, 2);
x_31 = lean_ctor_get(x_1, 3);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_1);
x_32 = lean_nat_dec_lt(x_2, x_29);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = lean_nat_dec_lt(x_29, x_2);
if (x_33 == 0)
{
uint32_t x_34; uint16_t x_35; uint8_t x_36; lean_object* x_37; 
lean_dec(x_30);
lean_dec(x_29);
x_34 = 0;
x_35 = 0;
x_36 = 0;
x_37 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_37, 0, x_28);
lean_ctor_set(x_37, 1, x_2);
lean_ctor_set(x_37, 2, x_3);
lean_ctor_set(x_37, 3, x_31);
lean_ctor_set_uint8(x_37, sizeof(void*)*4 + 6, x_9);
lean_ctor_set_uint32(x_37, sizeof(void*)*4, x_34);
lean_ctor_set_uint16(x_37, sizeof(void*)*4 + 4, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*4 + 7, x_36);
return x_37;
}
else
{
lean_object* x_38; uint32_t x_39; uint16_t x_40; uint8_t x_41; lean_object* x_42; 
x_38 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_31, x_2, x_3);
x_39 = 0;
x_40 = 0;
x_41 = 0;
x_42 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_42, 0, x_28);
lean_ctor_set(x_42, 1, x_29);
lean_ctor_set(x_42, 2, x_30);
lean_ctor_set(x_42, 3, x_38);
lean_ctor_set_uint8(x_42, sizeof(void*)*4 + 6, x_9);
lean_ctor_set_uint32(x_42, sizeof(void*)*4, x_39);
lean_ctor_set_uint16(x_42, sizeof(void*)*4 + 4, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*4 + 7, x_41);
return x_42;
}
}
else
{
lean_object* x_43; uint32_t x_44; uint16_t x_45; uint8_t x_46; lean_object* x_47; 
x_43 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_28, x_2, x_3);
x_44 = 0;
x_45 = 0;
x_46 = 0;
x_47 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set(x_47, 1, x_29);
lean_ctor_set(x_47, 2, x_30);
lean_ctor_set(x_47, 3, x_31);
lean_ctor_set_uint8(x_47, sizeof(void*)*4 + 6, x_9);
lean_ctor_set_uint32(x_47, sizeof(void*)*4, x_44);
lean_ctor_set_uint16(x_47, sizeof(void*)*4 + 4, x_45);
lean_ctor_set_uint8(x_47, sizeof(void*)*4 + 7, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_1);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_1, 0);
x_50 = lean_ctor_get(x_1, 1);
x_51 = lean_ctor_get(x_1, 2);
x_52 = lean_ctor_get(x_1, 3);
x_53 = lean_nat_dec_lt(x_2, x_50);
if (x_53 == 0)
{
uint8_t x_54; 
x_54 = lean_nat_dec_lt(x_50, x_2);
if (x_54 == 0)
{
uint32_t x_55; uint16_t x_56; uint8_t x_57; 
lean_dec(x_51);
lean_dec(x_50);
x_55 = 0;
x_56 = 0;
x_57 = 0;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_55);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_56);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_57);
return x_1;
}
else
{
uint8_t x_58; 
x_58 = l_RBNode_isRed___rarg(x_52);
if (x_58 == 0)
{
lean_object* x_59; uint32_t x_60; uint16_t x_61; uint8_t x_62; 
x_59 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_52, x_2, x_3);
x_60 = 0;
x_61 = 0;
x_62 = 0;
lean_ctor_set(x_1, 3, x_59);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_60);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_61);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_62);
return x_1;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_52, x_2, x_3);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_63, 3);
lean_inc(x_65);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_63);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; uint32_t x_70; uint16_t x_71; uint8_t x_72; uint8_t x_73; uint32_t x_74; uint16_t x_75; uint8_t x_76; 
x_67 = lean_ctor_get(x_63, 3);
lean_dec(x_67);
x_68 = lean_ctor_get(x_63, 0);
lean_dec(x_68);
x_69 = 0;
x_70 = 0;
x_71 = 0;
x_72 = 0;
lean_ctor_set(x_63, 0, x_65);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 6, x_69);
lean_ctor_set_uint32(x_63, sizeof(void*)*4, x_70);
lean_ctor_set_uint16(x_63, sizeof(void*)*4 + 4, x_71);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 7, x_72);
x_73 = 1;
x_74 = 0;
x_75 = 0;
x_76 = 0;
lean_ctor_set(x_1, 3, x_63);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_73);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_74);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_75);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_76);
return x_1;
}
else
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; uint32_t x_80; uint16_t x_81; uint8_t x_82; lean_object* x_83; uint8_t x_84; uint32_t x_85; uint16_t x_86; uint8_t x_87; 
x_77 = lean_ctor_get(x_63, 1);
x_78 = lean_ctor_get(x_63, 2);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_63);
x_79 = 0;
x_80 = 0;
x_81 = 0;
x_82 = 0;
x_83 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_83, 0, x_65);
lean_ctor_set(x_83, 1, x_77);
lean_ctor_set(x_83, 2, x_78);
lean_ctor_set(x_83, 3, x_65);
lean_ctor_set_uint8(x_83, sizeof(void*)*4 + 6, x_79);
lean_ctor_set_uint32(x_83, sizeof(void*)*4, x_80);
lean_ctor_set_uint16(x_83, sizeof(void*)*4 + 4, x_81);
lean_ctor_set_uint8(x_83, sizeof(void*)*4 + 7, x_82);
x_84 = 1;
x_85 = 0;
x_86 = 0;
x_87 = 0;
lean_ctor_set(x_1, 3, x_83);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_84);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_85);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_86);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_87);
return x_1;
}
}
else
{
uint8_t x_88; 
x_88 = lean_ctor_get_uint8(x_65, sizeof(void*)*4 + 6);
if (x_88 == 0)
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_63);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_90 = lean_ctor_get(x_63, 1);
x_91 = lean_ctor_get(x_63, 2);
x_92 = lean_ctor_get(x_63, 3);
lean_dec(x_92);
x_93 = lean_ctor_get(x_63, 0);
lean_dec(x_93);
x_94 = !lean_is_exclusive(x_65);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; uint32_t x_100; uint16_t x_101; uint8_t x_102; uint32_t x_103; uint16_t x_104; uint8_t x_105; uint32_t x_106; uint16_t x_107; uint8_t x_108; 
x_95 = lean_ctor_get(x_65, 0);
x_96 = lean_ctor_get(x_65, 1);
x_97 = lean_ctor_get(x_65, 2);
x_98 = lean_ctor_get(x_65, 3);
x_99 = 1;
x_100 = 0;
x_101 = 0;
x_102 = 0;
lean_ctor_set(x_65, 3, x_64);
lean_ctor_set(x_65, 2, x_51);
lean_ctor_set(x_65, 1, x_50);
lean_ctor_set(x_65, 0, x_49);
lean_ctor_set_uint8(x_65, sizeof(void*)*4 + 6, x_99);
lean_ctor_set_uint32(x_65, sizeof(void*)*4, x_100);
lean_ctor_set_uint16(x_65, sizeof(void*)*4 + 4, x_101);
lean_ctor_set_uint8(x_65, sizeof(void*)*4 + 7, x_102);
x_103 = 0;
x_104 = 0;
x_105 = 0;
lean_ctor_set(x_63, 3, x_98);
lean_ctor_set(x_63, 2, x_97);
lean_ctor_set(x_63, 1, x_96);
lean_ctor_set(x_63, 0, x_95);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 6, x_99);
lean_ctor_set_uint32(x_63, sizeof(void*)*4, x_103);
lean_ctor_set_uint16(x_63, sizeof(void*)*4 + 4, x_104);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 7, x_105);
x_106 = 0;
x_107 = 0;
x_108 = 0;
lean_ctor_set(x_1, 3, x_63);
lean_ctor_set(x_1, 2, x_91);
lean_ctor_set(x_1, 1, x_90);
lean_ctor_set(x_1, 0, x_65);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_88);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_106);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_107);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_108);
return x_1;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; uint32_t x_114; uint16_t x_115; uint8_t x_116; lean_object* x_117; uint32_t x_118; uint16_t x_119; uint8_t x_120; uint32_t x_121; uint16_t x_122; uint8_t x_123; 
x_109 = lean_ctor_get(x_65, 0);
x_110 = lean_ctor_get(x_65, 1);
x_111 = lean_ctor_get(x_65, 2);
x_112 = lean_ctor_get(x_65, 3);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_65);
x_113 = 1;
x_114 = 0;
x_115 = 0;
x_116 = 0;
x_117 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_117, 0, x_49);
lean_ctor_set(x_117, 1, x_50);
lean_ctor_set(x_117, 2, x_51);
lean_ctor_set(x_117, 3, x_64);
lean_ctor_set_uint8(x_117, sizeof(void*)*4 + 6, x_113);
lean_ctor_set_uint32(x_117, sizeof(void*)*4, x_114);
lean_ctor_set_uint16(x_117, sizeof(void*)*4 + 4, x_115);
lean_ctor_set_uint8(x_117, sizeof(void*)*4 + 7, x_116);
x_118 = 0;
x_119 = 0;
x_120 = 0;
lean_ctor_set(x_63, 3, x_112);
lean_ctor_set(x_63, 2, x_111);
lean_ctor_set(x_63, 1, x_110);
lean_ctor_set(x_63, 0, x_109);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 6, x_113);
lean_ctor_set_uint32(x_63, sizeof(void*)*4, x_118);
lean_ctor_set_uint16(x_63, sizeof(void*)*4 + 4, x_119);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 7, x_120);
x_121 = 0;
x_122 = 0;
x_123 = 0;
lean_ctor_set(x_1, 3, x_63);
lean_ctor_set(x_1, 2, x_91);
lean_ctor_set(x_1, 1, x_90);
lean_ctor_set(x_1, 0, x_117);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_88);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_121);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_122);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_123);
return x_1;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; uint32_t x_132; uint16_t x_133; uint8_t x_134; lean_object* x_135; uint32_t x_136; uint16_t x_137; uint8_t x_138; lean_object* x_139; uint32_t x_140; uint16_t x_141; uint8_t x_142; 
x_124 = lean_ctor_get(x_63, 1);
x_125 = lean_ctor_get(x_63, 2);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_63);
x_126 = lean_ctor_get(x_65, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_65, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_65, 2);
lean_inc(x_128);
x_129 = lean_ctor_get(x_65, 3);
lean_inc(x_129);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 lean_ctor_release(x_65, 2);
 lean_ctor_release(x_65, 3);
 x_130 = x_65;
} else {
 lean_dec_ref(x_65);
 x_130 = lean_box(0);
}
x_131 = 1;
x_132 = 0;
x_133 = 0;
x_134 = 0;
if (lean_is_scalar(x_130)) {
 x_135 = lean_alloc_ctor(1, 4, 8);
} else {
 x_135 = x_130;
}
lean_ctor_set(x_135, 0, x_49);
lean_ctor_set(x_135, 1, x_50);
lean_ctor_set(x_135, 2, x_51);
lean_ctor_set(x_135, 3, x_64);
lean_ctor_set_uint8(x_135, sizeof(void*)*4 + 6, x_131);
lean_ctor_set_uint32(x_135, sizeof(void*)*4, x_132);
lean_ctor_set_uint16(x_135, sizeof(void*)*4 + 4, x_133);
lean_ctor_set_uint8(x_135, sizeof(void*)*4 + 7, x_134);
x_136 = 0;
x_137 = 0;
x_138 = 0;
x_139 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_139, 0, x_126);
lean_ctor_set(x_139, 1, x_127);
lean_ctor_set(x_139, 2, x_128);
lean_ctor_set(x_139, 3, x_129);
lean_ctor_set_uint8(x_139, sizeof(void*)*4 + 6, x_131);
lean_ctor_set_uint32(x_139, sizeof(void*)*4, x_136);
lean_ctor_set_uint16(x_139, sizeof(void*)*4 + 4, x_137);
lean_ctor_set_uint8(x_139, sizeof(void*)*4 + 7, x_138);
x_140 = 0;
x_141 = 0;
x_142 = 0;
lean_ctor_set(x_1, 3, x_139);
lean_ctor_set(x_1, 2, x_125);
lean_ctor_set(x_1, 1, x_124);
lean_ctor_set(x_1, 0, x_135);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_88);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_140);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_141);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_142);
return x_1;
}
}
else
{
uint8_t x_143; 
x_143 = !lean_is_exclusive(x_63);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; uint8_t x_146; uint32_t x_147; uint16_t x_148; uint8_t x_149; uint32_t x_150; uint16_t x_151; uint8_t x_152; 
x_144 = lean_ctor_get(x_63, 3);
lean_dec(x_144);
x_145 = lean_ctor_get(x_63, 0);
lean_dec(x_145);
x_146 = 0;
x_147 = 0;
x_148 = 0;
x_149 = 0;
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 6, x_146);
lean_ctor_set_uint32(x_63, sizeof(void*)*4, x_147);
lean_ctor_set_uint16(x_63, sizeof(void*)*4 + 4, x_148);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 7, x_149);
x_150 = 0;
x_151 = 0;
x_152 = 0;
lean_ctor_set(x_1, 3, x_63);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_88);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_150);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_151);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_152);
return x_1;
}
else
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; uint32_t x_156; uint16_t x_157; uint8_t x_158; lean_object* x_159; uint32_t x_160; uint16_t x_161; uint8_t x_162; 
x_153 = lean_ctor_get(x_63, 1);
x_154 = lean_ctor_get(x_63, 2);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_63);
x_155 = 0;
x_156 = 0;
x_157 = 0;
x_158 = 0;
x_159 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_159, 0, x_64);
lean_ctor_set(x_159, 1, x_153);
lean_ctor_set(x_159, 2, x_154);
lean_ctor_set(x_159, 3, x_65);
lean_ctor_set_uint8(x_159, sizeof(void*)*4 + 6, x_155);
lean_ctor_set_uint32(x_159, sizeof(void*)*4, x_156);
lean_ctor_set_uint16(x_159, sizeof(void*)*4 + 4, x_157);
lean_ctor_set_uint8(x_159, sizeof(void*)*4 + 7, x_158);
x_160 = 0;
x_161 = 0;
x_162 = 0;
lean_ctor_set(x_1, 3, x_159);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_88);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_160);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_161);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_162);
return x_1;
}
}
}
}
else
{
uint8_t x_163; 
x_163 = lean_ctor_get_uint8(x_64, sizeof(void*)*4 + 6);
if (x_163 == 0)
{
uint8_t x_164; 
x_164 = !lean_is_exclusive(x_63);
if (x_164 == 0)
{
lean_object* x_165; uint8_t x_166; 
x_165 = lean_ctor_get(x_63, 0);
lean_dec(x_165);
x_166 = !lean_is_exclusive(x_64);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; uint32_t x_172; uint16_t x_173; uint8_t x_174; uint32_t x_175; uint16_t x_176; uint8_t x_177; uint32_t x_178; uint16_t x_179; uint8_t x_180; 
x_167 = lean_ctor_get(x_64, 0);
x_168 = lean_ctor_get(x_64, 1);
x_169 = lean_ctor_get(x_64, 2);
x_170 = lean_ctor_get(x_64, 3);
x_171 = 1;
x_172 = 0;
x_173 = 0;
x_174 = 0;
lean_ctor_set(x_64, 3, x_167);
lean_ctor_set(x_64, 2, x_51);
lean_ctor_set(x_64, 1, x_50);
lean_ctor_set(x_64, 0, x_49);
lean_ctor_set_uint8(x_64, sizeof(void*)*4 + 6, x_171);
lean_ctor_set_uint32(x_64, sizeof(void*)*4, x_172);
lean_ctor_set_uint16(x_64, sizeof(void*)*4 + 4, x_173);
lean_ctor_set_uint8(x_64, sizeof(void*)*4 + 7, x_174);
x_175 = 0;
x_176 = 0;
x_177 = 0;
lean_ctor_set(x_63, 0, x_170);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 6, x_171);
lean_ctor_set_uint32(x_63, sizeof(void*)*4, x_175);
lean_ctor_set_uint16(x_63, sizeof(void*)*4 + 4, x_176);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 7, x_177);
x_178 = 0;
x_179 = 0;
x_180 = 0;
lean_ctor_set(x_1, 3, x_63);
lean_ctor_set(x_1, 2, x_169);
lean_ctor_set(x_1, 1, x_168);
lean_ctor_set(x_1, 0, x_64);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_163);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_178);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_179);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_180);
return x_1;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; uint32_t x_186; uint16_t x_187; uint8_t x_188; lean_object* x_189; uint32_t x_190; uint16_t x_191; uint8_t x_192; uint32_t x_193; uint16_t x_194; uint8_t x_195; 
x_181 = lean_ctor_get(x_64, 0);
x_182 = lean_ctor_get(x_64, 1);
x_183 = lean_ctor_get(x_64, 2);
x_184 = lean_ctor_get(x_64, 3);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_64);
x_185 = 1;
x_186 = 0;
x_187 = 0;
x_188 = 0;
x_189 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_189, 0, x_49);
lean_ctor_set(x_189, 1, x_50);
lean_ctor_set(x_189, 2, x_51);
lean_ctor_set(x_189, 3, x_181);
lean_ctor_set_uint8(x_189, sizeof(void*)*4 + 6, x_185);
lean_ctor_set_uint32(x_189, sizeof(void*)*4, x_186);
lean_ctor_set_uint16(x_189, sizeof(void*)*4 + 4, x_187);
lean_ctor_set_uint8(x_189, sizeof(void*)*4 + 7, x_188);
x_190 = 0;
x_191 = 0;
x_192 = 0;
lean_ctor_set(x_63, 0, x_184);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 6, x_185);
lean_ctor_set_uint32(x_63, sizeof(void*)*4, x_190);
lean_ctor_set_uint16(x_63, sizeof(void*)*4 + 4, x_191);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 7, x_192);
x_193 = 0;
x_194 = 0;
x_195 = 0;
lean_ctor_set(x_1, 3, x_63);
lean_ctor_set(x_1, 2, x_183);
lean_ctor_set(x_1, 1, x_182);
lean_ctor_set(x_1, 0, x_189);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_163);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_193);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_194);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_195);
return x_1;
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; uint32_t x_205; uint16_t x_206; uint8_t x_207; lean_object* x_208; uint32_t x_209; uint16_t x_210; uint8_t x_211; lean_object* x_212; uint32_t x_213; uint16_t x_214; uint8_t x_215; 
x_196 = lean_ctor_get(x_63, 1);
x_197 = lean_ctor_get(x_63, 2);
x_198 = lean_ctor_get(x_63, 3);
lean_inc(x_198);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_63);
x_199 = lean_ctor_get(x_64, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_64, 1);
lean_inc(x_200);
x_201 = lean_ctor_get(x_64, 2);
lean_inc(x_201);
x_202 = lean_ctor_get(x_64, 3);
lean_inc(x_202);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 lean_ctor_release(x_64, 2);
 lean_ctor_release(x_64, 3);
 x_203 = x_64;
} else {
 lean_dec_ref(x_64);
 x_203 = lean_box(0);
}
x_204 = 1;
x_205 = 0;
x_206 = 0;
x_207 = 0;
if (lean_is_scalar(x_203)) {
 x_208 = lean_alloc_ctor(1, 4, 8);
} else {
 x_208 = x_203;
}
lean_ctor_set(x_208, 0, x_49);
lean_ctor_set(x_208, 1, x_50);
lean_ctor_set(x_208, 2, x_51);
lean_ctor_set(x_208, 3, x_199);
lean_ctor_set_uint8(x_208, sizeof(void*)*4 + 6, x_204);
lean_ctor_set_uint32(x_208, sizeof(void*)*4, x_205);
lean_ctor_set_uint16(x_208, sizeof(void*)*4 + 4, x_206);
lean_ctor_set_uint8(x_208, sizeof(void*)*4 + 7, x_207);
x_209 = 0;
x_210 = 0;
x_211 = 0;
x_212 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_212, 0, x_202);
lean_ctor_set(x_212, 1, x_196);
lean_ctor_set(x_212, 2, x_197);
lean_ctor_set(x_212, 3, x_198);
lean_ctor_set_uint8(x_212, sizeof(void*)*4 + 6, x_204);
lean_ctor_set_uint32(x_212, sizeof(void*)*4, x_209);
lean_ctor_set_uint16(x_212, sizeof(void*)*4 + 4, x_210);
lean_ctor_set_uint8(x_212, sizeof(void*)*4 + 7, x_211);
x_213 = 0;
x_214 = 0;
x_215 = 0;
lean_ctor_set(x_1, 3, x_212);
lean_ctor_set(x_1, 2, x_201);
lean_ctor_set(x_1, 1, x_200);
lean_ctor_set(x_1, 0, x_208);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_163);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_213);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_214);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_215);
return x_1;
}
}
else
{
lean_object* x_216; 
x_216 = lean_ctor_get(x_63, 3);
lean_inc(x_216);
if (lean_obj_tag(x_216) == 0)
{
uint8_t x_217; 
x_217 = !lean_is_exclusive(x_63);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; uint8_t x_220; uint32_t x_221; uint16_t x_222; uint8_t x_223; uint32_t x_224; uint16_t x_225; uint8_t x_226; 
x_218 = lean_ctor_get(x_63, 3);
lean_dec(x_218);
x_219 = lean_ctor_get(x_63, 0);
lean_dec(x_219);
x_220 = 0;
x_221 = 0;
x_222 = 0;
x_223 = 0;
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 6, x_220);
lean_ctor_set_uint32(x_63, sizeof(void*)*4, x_221);
lean_ctor_set_uint16(x_63, sizeof(void*)*4 + 4, x_222);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 7, x_223);
x_224 = 0;
x_225 = 0;
x_226 = 0;
lean_ctor_set(x_1, 3, x_63);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_163);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_224);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_225);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_226);
return x_1;
}
else
{
lean_object* x_227; lean_object* x_228; uint8_t x_229; uint32_t x_230; uint16_t x_231; uint8_t x_232; lean_object* x_233; uint32_t x_234; uint16_t x_235; uint8_t x_236; 
x_227 = lean_ctor_get(x_63, 1);
x_228 = lean_ctor_get(x_63, 2);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_63);
x_229 = 0;
x_230 = 0;
x_231 = 0;
x_232 = 0;
x_233 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_233, 0, x_64);
lean_ctor_set(x_233, 1, x_227);
lean_ctor_set(x_233, 2, x_228);
lean_ctor_set(x_233, 3, x_216);
lean_ctor_set_uint8(x_233, sizeof(void*)*4 + 6, x_229);
lean_ctor_set_uint32(x_233, sizeof(void*)*4, x_230);
lean_ctor_set_uint16(x_233, sizeof(void*)*4 + 4, x_231);
lean_ctor_set_uint8(x_233, sizeof(void*)*4 + 7, x_232);
x_234 = 0;
x_235 = 0;
x_236 = 0;
lean_ctor_set(x_1, 3, x_233);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_163);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_234);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_235);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_236);
return x_1;
}
}
else
{
uint8_t x_237; 
x_237 = lean_ctor_get_uint8(x_216, sizeof(void*)*4 + 6);
if (x_237 == 0)
{
uint8_t x_238; 
lean_free_object(x_1);
x_238 = !lean_is_exclusive(x_63);
if (x_238 == 0)
{
lean_object* x_239; lean_object* x_240; uint8_t x_241; 
x_239 = lean_ctor_get(x_63, 3);
lean_dec(x_239);
x_240 = lean_ctor_get(x_63, 0);
lean_dec(x_240);
x_241 = !lean_is_exclusive(x_216);
if (x_241 == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint32_t x_246; uint16_t x_247; uint8_t x_248; uint8_t x_249; 
x_242 = lean_ctor_get(x_216, 0);
x_243 = lean_ctor_get(x_216, 1);
x_244 = lean_ctor_get(x_216, 2);
x_245 = lean_ctor_get(x_216, 3);
x_246 = 0;
x_247 = 0;
x_248 = 0;
lean_inc(x_64);
lean_ctor_set(x_216, 3, x_64);
lean_ctor_set(x_216, 2, x_51);
lean_ctor_set(x_216, 1, x_50);
lean_ctor_set(x_216, 0, x_49);
x_249 = !lean_is_exclusive(x_64);
if (x_249 == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; uint32_t x_254; uint16_t x_255; uint8_t x_256; uint32_t x_257; uint16_t x_258; uint8_t x_259; 
x_250 = lean_ctor_get(x_64, 3);
lean_dec(x_250);
x_251 = lean_ctor_get(x_64, 2);
lean_dec(x_251);
x_252 = lean_ctor_get(x_64, 1);
lean_dec(x_252);
x_253 = lean_ctor_get(x_64, 0);
lean_dec(x_253);
lean_ctor_set_uint8(x_216, sizeof(void*)*4 + 6, x_163);
lean_ctor_set_uint32(x_216, sizeof(void*)*4, x_246);
lean_ctor_set_uint16(x_216, sizeof(void*)*4 + 4, x_247);
lean_ctor_set_uint8(x_216, sizeof(void*)*4 + 7, x_248);
x_254 = 0;
x_255 = 0;
x_256 = 0;
lean_ctor_set(x_64, 3, x_245);
lean_ctor_set(x_64, 2, x_244);
lean_ctor_set(x_64, 1, x_243);
lean_ctor_set(x_64, 0, x_242);
lean_ctor_set_uint32(x_64, sizeof(void*)*4, x_254);
lean_ctor_set_uint16(x_64, sizeof(void*)*4 + 4, x_255);
lean_ctor_set_uint8(x_64, sizeof(void*)*4 + 7, x_256);
x_257 = 0;
x_258 = 0;
x_259 = 0;
lean_ctor_set(x_63, 3, x_64);
lean_ctor_set(x_63, 0, x_216);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 6, x_237);
lean_ctor_set_uint32(x_63, sizeof(void*)*4, x_257);
lean_ctor_set_uint16(x_63, sizeof(void*)*4 + 4, x_258);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 7, x_259);
return x_63;
}
else
{
uint32_t x_260; uint16_t x_261; uint8_t x_262; lean_object* x_263; uint32_t x_264; uint16_t x_265; uint8_t x_266; 
lean_dec(x_64);
lean_ctor_set_uint8(x_216, sizeof(void*)*4 + 6, x_163);
lean_ctor_set_uint32(x_216, sizeof(void*)*4, x_246);
lean_ctor_set_uint16(x_216, sizeof(void*)*4 + 4, x_247);
lean_ctor_set_uint8(x_216, sizeof(void*)*4 + 7, x_248);
x_260 = 0;
x_261 = 0;
x_262 = 0;
x_263 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_263, 0, x_242);
lean_ctor_set(x_263, 1, x_243);
lean_ctor_set(x_263, 2, x_244);
lean_ctor_set(x_263, 3, x_245);
lean_ctor_set_uint8(x_263, sizeof(void*)*4 + 6, x_163);
lean_ctor_set_uint32(x_263, sizeof(void*)*4, x_260);
lean_ctor_set_uint16(x_263, sizeof(void*)*4 + 4, x_261);
lean_ctor_set_uint8(x_263, sizeof(void*)*4 + 7, x_262);
x_264 = 0;
x_265 = 0;
x_266 = 0;
lean_ctor_set(x_63, 3, x_263);
lean_ctor_set(x_63, 0, x_216);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 6, x_237);
lean_ctor_set_uint32(x_63, sizeof(void*)*4, x_264);
lean_ctor_set_uint16(x_63, sizeof(void*)*4 + 4, x_265);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 7, x_266);
return x_63;
}
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; uint32_t x_271; uint16_t x_272; uint8_t x_273; lean_object* x_274; lean_object* x_275; uint32_t x_276; uint16_t x_277; uint8_t x_278; lean_object* x_279; uint32_t x_280; uint16_t x_281; uint8_t x_282; 
x_267 = lean_ctor_get(x_216, 0);
x_268 = lean_ctor_get(x_216, 1);
x_269 = lean_ctor_get(x_216, 2);
x_270 = lean_ctor_get(x_216, 3);
lean_inc(x_270);
lean_inc(x_269);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_216);
x_271 = 0;
x_272 = 0;
x_273 = 0;
lean_inc(x_64);
x_274 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_274, 0, x_49);
lean_ctor_set(x_274, 1, x_50);
lean_ctor_set(x_274, 2, x_51);
lean_ctor_set(x_274, 3, x_64);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 lean_ctor_release(x_64, 2);
 lean_ctor_release(x_64, 3);
 x_275 = x_64;
} else {
 lean_dec_ref(x_64);
 x_275 = lean_box(0);
}
lean_ctor_set_uint8(x_274, sizeof(void*)*4 + 6, x_163);
lean_ctor_set_uint32(x_274, sizeof(void*)*4, x_271);
lean_ctor_set_uint16(x_274, sizeof(void*)*4 + 4, x_272);
lean_ctor_set_uint8(x_274, sizeof(void*)*4 + 7, x_273);
x_276 = 0;
x_277 = 0;
x_278 = 0;
if (lean_is_scalar(x_275)) {
 x_279 = lean_alloc_ctor(1, 4, 8);
} else {
 x_279 = x_275;
}
lean_ctor_set(x_279, 0, x_267);
lean_ctor_set(x_279, 1, x_268);
lean_ctor_set(x_279, 2, x_269);
lean_ctor_set(x_279, 3, x_270);
lean_ctor_set_uint8(x_279, sizeof(void*)*4 + 6, x_163);
lean_ctor_set_uint32(x_279, sizeof(void*)*4, x_276);
lean_ctor_set_uint16(x_279, sizeof(void*)*4 + 4, x_277);
lean_ctor_set_uint8(x_279, sizeof(void*)*4 + 7, x_278);
x_280 = 0;
x_281 = 0;
x_282 = 0;
lean_ctor_set(x_63, 3, x_279);
lean_ctor_set(x_63, 0, x_274);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 6, x_237);
lean_ctor_set_uint32(x_63, sizeof(void*)*4, x_280);
lean_ctor_set_uint16(x_63, sizeof(void*)*4 + 4, x_281);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 7, x_282);
return x_63;
}
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; uint32_t x_290; uint16_t x_291; uint8_t x_292; lean_object* x_293; lean_object* x_294; uint32_t x_295; uint16_t x_296; uint8_t x_297; lean_object* x_298; uint32_t x_299; uint16_t x_300; uint8_t x_301; lean_object* x_302; 
x_283 = lean_ctor_get(x_63, 1);
x_284 = lean_ctor_get(x_63, 2);
lean_inc(x_284);
lean_inc(x_283);
lean_dec(x_63);
x_285 = lean_ctor_get(x_216, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_216, 1);
lean_inc(x_286);
x_287 = lean_ctor_get(x_216, 2);
lean_inc(x_287);
x_288 = lean_ctor_get(x_216, 3);
lean_inc(x_288);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 lean_ctor_release(x_216, 1);
 lean_ctor_release(x_216, 2);
 lean_ctor_release(x_216, 3);
 x_289 = x_216;
} else {
 lean_dec_ref(x_216);
 x_289 = lean_box(0);
}
x_290 = 0;
x_291 = 0;
x_292 = 0;
lean_inc(x_64);
if (lean_is_scalar(x_289)) {
 x_293 = lean_alloc_ctor(1, 4, 8);
} else {
 x_293 = x_289;
}
lean_ctor_set(x_293, 0, x_49);
lean_ctor_set(x_293, 1, x_50);
lean_ctor_set(x_293, 2, x_51);
lean_ctor_set(x_293, 3, x_64);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 lean_ctor_release(x_64, 2);
 lean_ctor_release(x_64, 3);
 x_294 = x_64;
} else {
 lean_dec_ref(x_64);
 x_294 = lean_box(0);
}
lean_ctor_set_uint8(x_293, sizeof(void*)*4 + 6, x_163);
lean_ctor_set_uint32(x_293, sizeof(void*)*4, x_290);
lean_ctor_set_uint16(x_293, sizeof(void*)*4 + 4, x_291);
lean_ctor_set_uint8(x_293, sizeof(void*)*4 + 7, x_292);
x_295 = 0;
x_296 = 0;
x_297 = 0;
if (lean_is_scalar(x_294)) {
 x_298 = lean_alloc_ctor(1, 4, 8);
} else {
 x_298 = x_294;
}
lean_ctor_set(x_298, 0, x_285);
lean_ctor_set(x_298, 1, x_286);
lean_ctor_set(x_298, 2, x_287);
lean_ctor_set(x_298, 3, x_288);
lean_ctor_set_uint8(x_298, sizeof(void*)*4 + 6, x_163);
lean_ctor_set_uint32(x_298, sizeof(void*)*4, x_295);
lean_ctor_set_uint16(x_298, sizeof(void*)*4 + 4, x_296);
lean_ctor_set_uint8(x_298, sizeof(void*)*4 + 7, x_297);
x_299 = 0;
x_300 = 0;
x_301 = 0;
x_302 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_302, 0, x_293);
lean_ctor_set(x_302, 1, x_283);
lean_ctor_set(x_302, 2, x_284);
lean_ctor_set(x_302, 3, x_298);
lean_ctor_set_uint8(x_302, sizeof(void*)*4 + 6, x_237);
lean_ctor_set_uint32(x_302, sizeof(void*)*4, x_299);
lean_ctor_set_uint16(x_302, sizeof(void*)*4 + 4, x_300);
lean_ctor_set_uint8(x_302, sizeof(void*)*4 + 7, x_301);
return x_302;
}
}
else
{
uint8_t x_303; 
x_303 = !lean_is_exclusive(x_63);
if (x_303 == 0)
{
lean_object* x_304; lean_object* x_305; uint8_t x_306; 
x_304 = lean_ctor_get(x_63, 3);
lean_dec(x_304);
x_305 = lean_ctor_get(x_63, 0);
lean_dec(x_305);
x_306 = !lean_is_exclusive(x_64);
if (x_306 == 0)
{
uint32_t x_307; uint16_t x_308; uint8_t x_309; uint8_t x_310; uint32_t x_311; uint16_t x_312; uint8_t x_313; uint32_t x_314; uint16_t x_315; uint8_t x_316; 
x_307 = 0;
x_308 = 0;
x_309 = 0;
lean_ctor_set_uint8(x_64, sizeof(void*)*4 + 6, x_237);
lean_ctor_set_uint32(x_64, sizeof(void*)*4, x_307);
lean_ctor_set_uint16(x_64, sizeof(void*)*4 + 4, x_308);
lean_ctor_set_uint8(x_64, sizeof(void*)*4 + 7, x_309);
x_310 = 0;
x_311 = 0;
x_312 = 0;
x_313 = 0;
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 6, x_310);
lean_ctor_set_uint32(x_63, sizeof(void*)*4, x_311);
lean_ctor_set_uint16(x_63, sizeof(void*)*4 + 4, x_312);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 7, x_313);
x_314 = 0;
x_315 = 0;
x_316 = 0;
lean_ctor_set(x_1, 3, x_63);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_237);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_314);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_315);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_316);
return x_1;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; uint32_t x_321; uint16_t x_322; uint8_t x_323; lean_object* x_324; uint8_t x_325; uint32_t x_326; uint16_t x_327; uint8_t x_328; uint32_t x_329; uint16_t x_330; uint8_t x_331; 
x_317 = lean_ctor_get(x_64, 0);
x_318 = lean_ctor_get(x_64, 1);
x_319 = lean_ctor_get(x_64, 2);
x_320 = lean_ctor_get(x_64, 3);
lean_inc(x_320);
lean_inc(x_319);
lean_inc(x_318);
lean_inc(x_317);
lean_dec(x_64);
x_321 = 0;
x_322 = 0;
x_323 = 0;
x_324 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_324, 0, x_317);
lean_ctor_set(x_324, 1, x_318);
lean_ctor_set(x_324, 2, x_319);
lean_ctor_set(x_324, 3, x_320);
lean_ctor_set_uint8(x_324, sizeof(void*)*4 + 6, x_237);
lean_ctor_set_uint32(x_324, sizeof(void*)*4, x_321);
lean_ctor_set_uint16(x_324, sizeof(void*)*4 + 4, x_322);
lean_ctor_set_uint8(x_324, sizeof(void*)*4 + 7, x_323);
x_325 = 0;
x_326 = 0;
x_327 = 0;
x_328 = 0;
lean_ctor_set(x_63, 0, x_324);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 6, x_325);
lean_ctor_set_uint32(x_63, sizeof(void*)*4, x_326);
lean_ctor_set_uint16(x_63, sizeof(void*)*4 + 4, x_327);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 7, x_328);
x_329 = 0;
x_330 = 0;
x_331 = 0;
lean_ctor_set(x_1, 3, x_63);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_237);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_329);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_330);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_331);
return x_1;
}
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; uint32_t x_339; uint16_t x_340; uint8_t x_341; lean_object* x_342; uint8_t x_343; uint32_t x_344; uint16_t x_345; uint8_t x_346; lean_object* x_347; uint32_t x_348; uint16_t x_349; uint8_t x_350; 
x_332 = lean_ctor_get(x_63, 1);
x_333 = lean_ctor_get(x_63, 2);
lean_inc(x_333);
lean_inc(x_332);
lean_dec(x_63);
x_334 = lean_ctor_get(x_64, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_64, 1);
lean_inc(x_335);
x_336 = lean_ctor_get(x_64, 2);
lean_inc(x_336);
x_337 = lean_ctor_get(x_64, 3);
lean_inc(x_337);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 lean_ctor_release(x_64, 2);
 lean_ctor_release(x_64, 3);
 x_338 = x_64;
} else {
 lean_dec_ref(x_64);
 x_338 = lean_box(0);
}
x_339 = 0;
x_340 = 0;
x_341 = 0;
if (lean_is_scalar(x_338)) {
 x_342 = lean_alloc_ctor(1, 4, 8);
} else {
 x_342 = x_338;
}
lean_ctor_set(x_342, 0, x_334);
lean_ctor_set(x_342, 1, x_335);
lean_ctor_set(x_342, 2, x_336);
lean_ctor_set(x_342, 3, x_337);
lean_ctor_set_uint8(x_342, sizeof(void*)*4 + 6, x_237);
lean_ctor_set_uint32(x_342, sizeof(void*)*4, x_339);
lean_ctor_set_uint16(x_342, sizeof(void*)*4 + 4, x_340);
lean_ctor_set_uint8(x_342, sizeof(void*)*4 + 7, x_341);
x_343 = 0;
x_344 = 0;
x_345 = 0;
x_346 = 0;
x_347 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_347, 0, x_342);
lean_ctor_set(x_347, 1, x_332);
lean_ctor_set(x_347, 2, x_333);
lean_ctor_set(x_347, 3, x_216);
lean_ctor_set_uint8(x_347, sizeof(void*)*4 + 6, x_343);
lean_ctor_set_uint32(x_347, sizeof(void*)*4, x_344);
lean_ctor_set_uint16(x_347, sizeof(void*)*4 + 4, x_345);
lean_ctor_set_uint8(x_347, sizeof(void*)*4 + 7, x_346);
x_348 = 0;
x_349 = 0;
x_350 = 0;
lean_ctor_set(x_1, 3, x_347);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_237);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_348);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_349);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_350);
return x_1;
}
}
}
}
}
}
}
}
else
{
uint8_t x_351; 
x_351 = l_RBNode_isRed___rarg(x_49);
if (x_351 == 0)
{
lean_object* x_352; uint32_t x_353; uint16_t x_354; uint8_t x_355; 
x_352 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_49, x_2, x_3);
x_353 = 0;
x_354 = 0;
x_355 = 0;
lean_ctor_set(x_1, 0, x_352);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_353);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_354);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_355);
return x_1;
}
else
{
lean_object* x_356; lean_object* x_357; 
x_356 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_49, x_2, x_3);
x_357 = lean_ctor_get(x_356, 0);
lean_inc(x_357);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; 
x_358 = lean_ctor_get(x_356, 3);
lean_inc(x_358);
if (lean_obj_tag(x_358) == 0)
{
uint8_t x_359; 
x_359 = !lean_is_exclusive(x_356);
if (x_359 == 0)
{
lean_object* x_360; lean_object* x_361; uint8_t x_362; uint32_t x_363; uint16_t x_364; uint8_t x_365; uint8_t x_366; uint32_t x_367; uint16_t x_368; uint8_t x_369; 
x_360 = lean_ctor_get(x_356, 3);
lean_dec(x_360);
x_361 = lean_ctor_get(x_356, 0);
lean_dec(x_361);
x_362 = 0;
x_363 = 0;
x_364 = 0;
x_365 = 0;
lean_ctor_set(x_356, 0, x_358);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 6, x_362);
lean_ctor_set_uint32(x_356, sizeof(void*)*4, x_363);
lean_ctor_set_uint16(x_356, sizeof(void*)*4 + 4, x_364);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 7, x_365);
x_366 = 1;
x_367 = 0;
x_368 = 0;
x_369 = 0;
lean_ctor_set(x_1, 0, x_356);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_366);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_367);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_368);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_369);
return x_1;
}
else
{
lean_object* x_370; lean_object* x_371; uint8_t x_372; uint32_t x_373; uint16_t x_374; uint8_t x_375; lean_object* x_376; uint8_t x_377; uint32_t x_378; uint16_t x_379; uint8_t x_380; 
x_370 = lean_ctor_get(x_356, 1);
x_371 = lean_ctor_get(x_356, 2);
lean_inc(x_371);
lean_inc(x_370);
lean_dec(x_356);
x_372 = 0;
x_373 = 0;
x_374 = 0;
x_375 = 0;
x_376 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_376, 0, x_358);
lean_ctor_set(x_376, 1, x_370);
lean_ctor_set(x_376, 2, x_371);
lean_ctor_set(x_376, 3, x_358);
lean_ctor_set_uint8(x_376, sizeof(void*)*4 + 6, x_372);
lean_ctor_set_uint32(x_376, sizeof(void*)*4, x_373);
lean_ctor_set_uint16(x_376, sizeof(void*)*4 + 4, x_374);
lean_ctor_set_uint8(x_376, sizeof(void*)*4 + 7, x_375);
x_377 = 1;
x_378 = 0;
x_379 = 0;
x_380 = 0;
lean_ctor_set(x_1, 0, x_376);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_377);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_378);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_379);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_380);
return x_1;
}
}
else
{
uint8_t x_381; 
x_381 = lean_ctor_get_uint8(x_358, sizeof(void*)*4 + 6);
if (x_381 == 0)
{
uint8_t x_382; 
x_382 = !lean_is_exclusive(x_356);
if (x_382 == 0)
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; uint8_t x_387; 
x_383 = lean_ctor_get(x_356, 1);
x_384 = lean_ctor_get(x_356, 2);
x_385 = lean_ctor_get(x_356, 3);
lean_dec(x_385);
x_386 = lean_ctor_get(x_356, 0);
lean_dec(x_386);
x_387 = !lean_is_exclusive(x_358);
if (x_387 == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; uint8_t x_392; uint32_t x_393; uint16_t x_394; uint8_t x_395; uint32_t x_396; uint16_t x_397; uint8_t x_398; uint32_t x_399; uint16_t x_400; uint8_t x_401; 
x_388 = lean_ctor_get(x_358, 0);
x_389 = lean_ctor_get(x_358, 1);
x_390 = lean_ctor_get(x_358, 2);
x_391 = lean_ctor_get(x_358, 3);
x_392 = 1;
x_393 = 0;
x_394 = 0;
x_395 = 0;
lean_ctor_set(x_358, 3, x_388);
lean_ctor_set(x_358, 2, x_384);
lean_ctor_set(x_358, 1, x_383);
lean_ctor_set(x_358, 0, x_357);
lean_ctor_set_uint8(x_358, sizeof(void*)*4 + 6, x_392);
lean_ctor_set_uint32(x_358, sizeof(void*)*4, x_393);
lean_ctor_set_uint16(x_358, sizeof(void*)*4 + 4, x_394);
lean_ctor_set_uint8(x_358, sizeof(void*)*4 + 7, x_395);
x_396 = 0;
x_397 = 0;
x_398 = 0;
lean_ctor_set(x_356, 3, x_52);
lean_ctor_set(x_356, 2, x_51);
lean_ctor_set(x_356, 1, x_50);
lean_ctor_set(x_356, 0, x_391);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 6, x_392);
lean_ctor_set_uint32(x_356, sizeof(void*)*4, x_396);
lean_ctor_set_uint16(x_356, sizeof(void*)*4 + 4, x_397);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 7, x_398);
x_399 = 0;
x_400 = 0;
x_401 = 0;
lean_ctor_set(x_1, 3, x_356);
lean_ctor_set(x_1, 2, x_390);
lean_ctor_set(x_1, 1, x_389);
lean_ctor_set(x_1, 0, x_358);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_381);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_399);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_400);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_401);
return x_1;
}
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; uint8_t x_406; uint32_t x_407; uint16_t x_408; uint8_t x_409; lean_object* x_410; uint32_t x_411; uint16_t x_412; uint8_t x_413; uint32_t x_414; uint16_t x_415; uint8_t x_416; 
x_402 = lean_ctor_get(x_358, 0);
x_403 = lean_ctor_get(x_358, 1);
x_404 = lean_ctor_get(x_358, 2);
x_405 = lean_ctor_get(x_358, 3);
lean_inc(x_405);
lean_inc(x_404);
lean_inc(x_403);
lean_inc(x_402);
lean_dec(x_358);
x_406 = 1;
x_407 = 0;
x_408 = 0;
x_409 = 0;
x_410 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_410, 0, x_357);
lean_ctor_set(x_410, 1, x_383);
lean_ctor_set(x_410, 2, x_384);
lean_ctor_set(x_410, 3, x_402);
lean_ctor_set_uint8(x_410, sizeof(void*)*4 + 6, x_406);
lean_ctor_set_uint32(x_410, sizeof(void*)*4, x_407);
lean_ctor_set_uint16(x_410, sizeof(void*)*4 + 4, x_408);
lean_ctor_set_uint8(x_410, sizeof(void*)*4 + 7, x_409);
x_411 = 0;
x_412 = 0;
x_413 = 0;
lean_ctor_set(x_356, 3, x_52);
lean_ctor_set(x_356, 2, x_51);
lean_ctor_set(x_356, 1, x_50);
lean_ctor_set(x_356, 0, x_405);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 6, x_406);
lean_ctor_set_uint32(x_356, sizeof(void*)*4, x_411);
lean_ctor_set_uint16(x_356, sizeof(void*)*4 + 4, x_412);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 7, x_413);
x_414 = 0;
x_415 = 0;
x_416 = 0;
lean_ctor_set(x_1, 3, x_356);
lean_ctor_set(x_1, 2, x_404);
lean_ctor_set(x_1, 1, x_403);
lean_ctor_set(x_1, 0, x_410);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_381);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_414);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_415);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_416);
return x_1;
}
}
else
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; uint8_t x_424; uint32_t x_425; uint16_t x_426; uint8_t x_427; lean_object* x_428; uint32_t x_429; uint16_t x_430; uint8_t x_431; lean_object* x_432; uint32_t x_433; uint16_t x_434; uint8_t x_435; 
x_417 = lean_ctor_get(x_356, 1);
x_418 = lean_ctor_get(x_356, 2);
lean_inc(x_418);
lean_inc(x_417);
lean_dec(x_356);
x_419 = lean_ctor_get(x_358, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_358, 1);
lean_inc(x_420);
x_421 = lean_ctor_get(x_358, 2);
lean_inc(x_421);
x_422 = lean_ctor_get(x_358, 3);
lean_inc(x_422);
if (lean_is_exclusive(x_358)) {
 lean_ctor_release(x_358, 0);
 lean_ctor_release(x_358, 1);
 lean_ctor_release(x_358, 2);
 lean_ctor_release(x_358, 3);
 x_423 = x_358;
} else {
 lean_dec_ref(x_358);
 x_423 = lean_box(0);
}
x_424 = 1;
x_425 = 0;
x_426 = 0;
x_427 = 0;
if (lean_is_scalar(x_423)) {
 x_428 = lean_alloc_ctor(1, 4, 8);
} else {
 x_428 = x_423;
}
lean_ctor_set(x_428, 0, x_357);
lean_ctor_set(x_428, 1, x_417);
lean_ctor_set(x_428, 2, x_418);
lean_ctor_set(x_428, 3, x_419);
lean_ctor_set_uint8(x_428, sizeof(void*)*4 + 6, x_424);
lean_ctor_set_uint32(x_428, sizeof(void*)*4, x_425);
lean_ctor_set_uint16(x_428, sizeof(void*)*4 + 4, x_426);
lean_ctor_set_uint8(x_428, sizeof(void*)*4 + 7, x_427);
x_429 = 0;
x_430 = 0;
x_431 = 0;
x_432 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_432, 0, x_422);
lean_ctor_set(x_432, 1, x_50);
lean_ctor_set(x_432, 2, x_51);
lean_ctor_set(x_432, 3, x_52);
lean_ctor_set_uint8(x_432, sizeof(void*)*4 + 6, x_424);
lean_ctor_set_uint32(x_432, sizeof(void*)*4, x_429);
lean_ctor_set_uint16(x_432, sizeof(void*)*4 + 4, x_430);
lean_ctor_set_uint8(x_432, sizeof(void*)*4 + 7, x_431);
x_433 = 0;
x_434 = 0;
x_435 = 0;
lean_ctor_set(x_1, 3, x_432);
lean_ctor_set(x_1, 2, x_421);
lean_ctor_set(x_1, 1, x_420);
lean_ctor_set(x_1, 0, x_428);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_381);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_433);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_434);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_435);
return x_1;
}
}
else
{
uint8_t x_436; 
x_436 = !lean_is_exclusive(x_356);
if (x_436 == 0)
{
lean_object* x_437; lean_object* x_438; uint8_t x_439; uint32_t x_440; uint16_t x_441; uint8_t x_442; uint32_t x_443; uint16_t x_444; uint8_t x_445; 
x_437 = lean_ctor_get(x_356, 3);
lean_dec(x_437);
x_438 = lean_ctor_get(x_356, 0);
lean_dec(x_438);
x_439 = 0;
x_440 = 0;
x_441 = 0;
x_442 = 0;
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 6, x_439);
lean_ctor_set_uint32(x_356, sizeof(void*)*4, x_440);
lean_ctor_set_uint16(x_356, sizeof(void*)*4 + 4, x_441);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 7, x_442);
x_443 = 0;
x_444 = 0;
x_445 = 0;
lean_ctor_set(x_1, 0, x_356);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_381);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_443);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_444);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_445);
return x_1;
}
else
{
lean_object* x_446; lean_object* x_447; uint8_t x_448; uint32_t x_449; uint16_t x_450; uint8_t x_451; lean_object* x_452; uint32_t x_453; uint16_t x_454; uint8_t x_455; 
x_446 = lean_ctor_get(x_356, 1);
x_447 = lean_ctor_get(x_356, 2);
lean_inc(x_447);
lean_inc(x_446);
lean_dec(x_356);
x_448 = 0;
x_449 = 0;
x_450 = 0;
x_451 = 0;
x_452 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_452, 0, x_357);
lean_ctor_set(x_452, 1, x_446);
lean_ctor_set(x_452, 2, x_447);
lean_ctor_set(x_452, 3, x_358);
lean_ctor_set_uint8(x_452, sizeof(void*)*4 + 6, x_448);
lean_ctor_set_uint32(x_452, sizeof(void*)*4, x_449);
lean_ctor_set_uint16(x_452, sizeof(void*)*4 + 4, x_450);
lean_ctor_set_uint8(x_452, sizeof(void*)*4 + 7, x_451);
x_453 = 0;
x_454 = 0;
x_455 = 0;
lean_ctor_set(x_1, 0, x_452);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_381);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_453);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_454);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_455);
return x_1;
}
}
}
}
else
{
uint8_t x_456; 
x_456 = lean_ctor_get_uint8(x_357, sizeof(void*)*4 + 6);
if (x_456 == 0)
{
uint8_t x_457; 
x_457 = !lean_is_exclusive(x_356);
if (x_457 == 0)
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; uint8_t x_462; 
x_458 = lean_ctor_get(x_356, 1);
x_459 = lean_ctor_get(x_356, 2);
x_460 = lean_ctor_get(x_356, 3);
x_461 = lean_ctor_get(x_356, 0);
lean_dec(x_461);
x_462 = !lean_is_exclusive(x_357);
if (x_462 == 0)
{
uint8_t x_463; uint32_t x_464; uint16_t x_465; uint8_t x_466; uint32_t x_467; uint16_t x_468; uint8_t x_469; uint32_t x_470; uint16_t x_471; uint8_t x_472; 
x_463 = 1;
x_464 = 0;
x_465 = 0;
x_466 = 0;
lean_ctor_set_uint8(x_357, sizeof(void*)*4 + 6, x_463);
lean_ctor_set_uint32(x_357, sizeof(void*)*4, x_464);
lean_ctor_set_uint16(x_357, sizeof(void*)*4 + 4, x_465);
lean_ctor_set_uint8(x_357, sizeof(void*)*4 + 7, x_466);
x_467 = 0;
x_468 = 0;
x_469 = 0;
lean_ctor_set(x_356, 3, x_52);
lean_ctor_set(x_356, 2, x_51);
lean_ctor_set(x_356, 1, x_50);
lean_ctor_set(x_356, 0, x_460);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 6, x_463);
lean_ctor_set_uint32(x_356, sizeof(void*)*4, x_467);
lean_ctor_set_uint16(x_356, sizeof(void*)*4 + 4, x_468);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 7, x_469);
x_470 = 0;
x_471 = 0;
x_472 = 0;
lean_ctor_set(x_1, 3, x_356);
lean_ctor_set(x_1, 2, x_459);
lean_ctor_set(x_1, 1, x_458);
lean_ctor_set(x_1, 0, x_357);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_456);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_470);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_471);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_472);
return x_1;
}
else
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; uint8_t x_477; uint32_t x_478; uint16_t x_479; uint8_t x_480; lean_object* x_481; uint32_t x_482; uint16_t x_483; uint8_t x_484; uint32_t x_485; uint16_t x_486; uint8_t x_487; 
x_473 = lean_ctor_get(x_357, 0);
x_474 = lean_ctor_get(x_357, 1);
x_475 = lean_ctor_get(x_357, 2);
x_476 = lean_ctor_get(x_357, 3);
lean_inc(x_476);
lean_inc(x_475);
lean_inc(x_474);
lean_inc(x_473);
lean_dec(x_357);
x_477 = 1;
x_478 = 0;
x_479 = 0;
x_480 = 0;
x_481 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_481, 0, x_473);
lean_ctor_set(x_481, 1, x_474);
lean_ctor_set(x_481, 2, x_475);
lean_ctor_set(x_481, 3, x_476);
lean_ctor_set_uint8(x_481, sizeof(void*)*4 + 6, x_477);
lean_ctor_set_uint32(x_481, sizeof(void*)*4, x_478);
lean_ctor_set_uint16(x_481, sizeof(void*)*4 + 4, x_479);
lean_ctor_set_uint8(x_481, sizeof(void*)*4 + 7, x_480);
x_482 = 0;
x_483 = 0;
x_484 = 0;
lean_ctor_set(x_356, 3, x_52);
lean_ctor_set(x_356, 2, x_51);
lean_ctor_set(x_356, 1, x_50);
lean_ctor_set(x_356, 0, x_460);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 6, x_477);
lean_ctor_set_uint32(x_356, sizeof(void*)*4, x_482);
lean_ctor_set_uint16(x_356, sizeof(void*)*4 + 4, x_483);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 7, x_484);
x_485 = 0;
x_486 = 0;
x_487 = 0;
lean_ctor_set(x_1, 3, x_356);
lean_ctor_set(x_1, 2, x_459);
lean_ctor_set(x_1, 1, x_458);
lean_ctor_set(x_1, 0, x_481);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_456);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_485);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_486);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_487);
return x_1;
}
}
else
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; uint8_t x_496; uint32_t x_497; uint16_t x_498; uint8_t x_499; lean_object* x_500; uint32_t x_501; uint16_t x_502; uint8_t x_503; lean_object* x_504; uint32_t x_505; uint16_t x_506; uint8_t x_507; 
x_488 = lean_ctor_get(x_356, 1);
x_489 = lean_ctor_get(x_356, 2);
x_490 = lean_ctor_get(x_356, 3);
lean_inc(x_490);
lean_inc(x_489);
lean_inc(x_488);
lean_dec(x_356);
x_491 = lean_ctor_get(x_357, 0);
lean_inc(x_491);
x_492 = lean_ctor_get(x_357, 1);
lean_inc(x_492);
x_493 = lean_ctor_get(x_357, 2);
lean_inc(x_493);
x_494 = lean_ctor_get(x_357, 3);
lean_inc(x_494);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 lean_ctor_release(x_357, 1);
 lean_ctor_release(x_357, 2);
 lean_ctor_release(x_357, 3);
 x_495 = x_357;
} else {
 lean_dec_ref(x_357);
 x_495 = lean_box(0);
}
x_496 = 1;
x_497 = 0;
x_498 = 0;
x_499 = 0;
if (lean_is_scalar(x_495)) {
 x_500 = lean_alloc_ctor(1, 4, 8);
} else {
 x_500 = x_495;
}
lean_ctor_set(x_500, 0, x_491);
lean_ctor_set(x_500, 1, x_492);
lean_ctor_set(x_500, 2, x_493);
lean_ctor_set(x_500, 3, x_494);
lean_ctor_set_uint8(x_500, sizeof(void*)*4 + 6, x_496);
lean_ctor_set_uint32(x_500, sizeof(void*)*4, x_497);
lean_ctor_set_uint16(x_500, sizeof(void*)*4 + 4, x_498);
lean_ctor_set_uint8(x_500, sizeof(void*)*4 + 7, x_499);
x_501 = 0;
x_502 = 0;
x_503 = 0;
x_504 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_504, 0, x_490);
lean_ctor_set(x_504, 1, x_50);
lean_ctor_set(x_504, 2, x_51);
lean_ctor_set(x_504, 3, x_52);
lean_ctor_set_uint8(x_504, sizeof(void*)*4 + 6, x_496);
lean_ctor_set_uint32(x_504, sizeof(void*)*4, x_501);
lean_ctor_set_uint16(x_504, sizeof(void*)*4 + 4, x_502);
lean_ctor_set_uint8(x_504, sizeof(void*)*4 + 7, x_503);
x_505 = 0;
x_506 = 0;
x_507 = 0;
lean_ctor_set(x_1, 3, x_504);
lean_ctor_set(x_1, 2, x_489);
lean_ctor_set(x_1, 1, x_488);
lean_ctor_set(x_1, 0, x_500);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_456);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_505);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_506);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_507);
return x_1;
}
}
else
{
lean_object* x_508; 
x_508 = lean_ctor_get(x_356, 3);
lean_inc(x_508);
if (lean_obj_tag(x_508) == 0)
{
uint8_t x_509; 
x_509 = !lean_is_exclusive(x_356);
if (x_509 == 0)
{
lean_object* x_510; lean_object* x_511; uint8_t x_512; uint32_t x_513; uint16_t x_514; uint8_t x_515; uint32_t x_516; uint16_t x_517; uint8_t x_518; 
x_510 = lean_ctor_get(x_356, 3);
lean_dec(x_510);
x_511 = lean_ctor_get(x_356, 0);
lean_dec(x_511);
x_512 = 0;
x_513 = 0;
x_514 = 0;
x_515 = 0;
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 6, x_512);
lean_ctor_set_uint32(x_356, sizeof(void*)*4, x_513);
lean_ctor_set_uint16(x_356, sizeof(void*)*4 + 4, x_514);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 7, x_515);
x_516 = 0;
x_517 = 0;
x_518 = 0;
lean_ctor_set(x_1, 0, x_356);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_456);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_516);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_517);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_518);
return x_1;
}
else
{
lean_object* x_519; lean_object* x_520; uint8_t x_521; uint32_t x_522; uint16_t x_523; uint8_t x_524; lean_object* x_525; uint32_t x_526; uint16_t x_527; uint8_t x_528; 
x_519 = lean_ctor_get(x_356, 1);
x_520 = lean_ctor_get(x_356, 2);
lean_inc(x_520);
lean_inc(x_519);
lean_dec(x_356);
x_521 = 0;
x_522 = 0;
x_523 = 0;
x_524 = 0;
x_525 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_525, 0, x_357);
lean_ctor_set(x_525, 1, x_519);
lean_ctor_set(x_525, 2, x_520);
lean_ctor_set(x_525, 3, x_508);
lean_ctor_set_uint8(x_525, sizeof(void*)*4 + 6, x_521);
lean_ctor_set_uint32(x_525, sizeof(void*)*4, x_522);
lean_ctor_set_uint16(x_525, sizeof(void*)*4 + 4, x_523);
lean_ctor_set_uint8(x_525, sizeof(void*)*4 + 7, x_524);
x_526 = 0;
x_527 = 0;
x_528 = 0;
lean_ctor_set(x_1, 0, x_525);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_456);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_526);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_527);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_528);
return x_1;
}
}
else
{
uint8_t x_529; 
x_529 = lean_ctor_get_uint8(x_508, sizeof(void*)*4 + 6);
if (x_529 == 0)
{
uint8_t x_530; 
lean_free_object(x_1);
x_530 = !lean_is_exclusive(x_356);
if (x_530 == 0)
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; uint8_t x_535; 
x_531 = lean_ctor_get(x_356, 1);
x_532 = lean_ctor_get(x_356, 2);
x_533 = lean_ctor_get(x_356, 3);
lean_dec(x_533);
x_534 = lean_ctor_get(x_356, 0);
lean_dec(x_534);
x_535 = !lean_is_exclusive(x_508);
if (x_535 == 0)
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; uint32_t x_540; uint16_t x_541; uint8_t x_542; uint8_t x_543; 
x_536 = lean_ctor_get(x_508, 0);
x_537 = lean_ctor_get(x_508, 1);
x_538 = lean_ctor_get(x_508, 2);
x_539 = lean_ctor_get(x_508, 3);
x_540 = 0;
x_541 = 0;
x_542 = 0;
lean_inc(x_357);
lean_ctor_set(x_508, 3, x_536);
lean_ctor_set(x_508, 2, x_532);
lean_ctor_set(x_508, 1, x_531);
lean_ctor_set(x_508, 0, x_357);
x_543 = !lean_is_exclusive(x_357);
if (x_543 == 0)
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; uint32_t x_548; uint16_t x_549; uint8_t x_550; uint32_t x_551; uint16_t x_552; uint8_t x_553; 
x_544 = lean_ctor_get(x_357, 3);
lean_dec(x_544);
x_545 = lean_ctor_get(x_357, 2);
lean_dec(x_545);
x_546 = lean_ctor_get(x_357, 1);
lean_dec(x_546);
x_547 = lean_ctor_get(x_357, 0);
lean_dec(x_547);
lean_ctor_set_uint8(x_508, sizeof(void*)*4 + 6, x_456);
lean_ctor_set_uint32(x_508, sizeof(void*)*4, x_540);
lean_ctor_set_uint16(x_508, sizeof(void*)*4 + 4, x_541);
lean_ctor_set_uint8(x_508, sizeof(void*)*4 + 7, x_542);
x_548 = 0;
x_549 = 0;
x_550 = 0;
lean_ctor_set(x_357, 3, x_52);
lean_ctor_set(x_357, 2, x_51);
lean_ctor_set(x_357, 1, x_50);
lean_ctor_set(x_357, 0, x_539);
lean_ctor_set_uint32(x_357, sizeof(void*)*4, x_548);
lean_ctor_set_uint16(x_357, sizeof(void*)*4 + 4, x_549);
lean_ctor_set_uint8(x_357, sizeof(void*)*4 + 7, x_550);
x_551 = 0;
x_552 = 0;
x_553 = 0;
lean_ctor_set(x_356, 3, x_357);
lean_ctor_set(x_356, 2, x_538);
lean_ctor_set(x_356, 1, x_537);
lean_ctor_set(x_356, 0, x_508);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 6, x_529);
lean_ctor_set_uint32(x_356, sizeof(void*)*4, x_551);
lean_ctor_set_uint16(x_356, sizeof(void*)*4 + 4, x_552);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 7, x_553);
return x_356;
}
else
{
uint32_t x_554; uint16_t x_555; uint8_t x_556; lean_object* x_557; uint32_t x_558; uint16_t x_559; uint8_t x_560; 
lean_dec(x_357);
lean_ctor_set_uint8(x_508, sizeof(void*)*4 + 6, x_456);
lean_ctor_set_uint32(x_508, sizeof(void*)*4, x_540);
lean_ctor_set_uint16(x_508, sizeof(void*)*4 + 4, x_541);
lean_ctor_set_uint8(x_508, sizeof(void*)*4 + 7, x_542);
x_554 = 0;
x_555 = 0;
x_556 = 0;
x_557 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_557, 0, x_539);
lean_ctor_set(x_557, 1, x_50);
lean_ctor_set(x_557, 2, x_51);
lean_ctor_set(x_557, 3, x_52);
lean_ctor_set_uint8(x_557, sizeof(void*)*4 + 6, x_456);
lean_ctor_set_uint32(x_557, sizeof(void*)*4, x_554);
lean_ctor_set_uint16(x_557, sizeof(void*)*4 + 4, x_555);
lean_ctor_set_uint8(x_557, sizeof(void*)*4 + 7, x_556);
x_558 = 0;
x_559 = 0;
x_560 = 0;
lean_ctor_set(x_356, 3, x_557);
lean_ctor_set(x_356, 2, x_538);
lean_ctor_set(x_356, 1, x_537);
lean_ctor_set(x_356, 0, x_508);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 6, x_529);
lean_ctor_set_uint32(x_356, sizeof(void*)*4, x_558);
lean_ctor_set_uint16(x_356, sizeof(void*)*4 + 4, x_559);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 7, x_560);
return x_356;
}
}
else
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; uint32_t x_565; uint16_t x_566; uint8_t x_567; lean_object* x_568; lean_object* x_569; uint32_t x_570; uint16_t x_571; uint8_t x_572; lean_object* x_573; uint32_t x_574; uint16_t x_575; uint8_t x_576; 
x_561 = lean_ctor_get(x_508, 0);
x_562 = lean_ctor_get(x_508, 1);
x_563 = lean_ctor_get(x_508, 2);
x_564 = lean_ctor_get(x_508, 3);
lean_inc(x_564);
lean_inc(x_563);
lean_inc(x_562);
lean_inc(x_561);
lean_dec(x_508);
x_565 = 0;
x_566 = 0;
x_567 = 0;
lean_inc(x_357);
x_568 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_568, 0, x_357);
lean_ctor_set(x_568, 1, x_531);
lean_ctor_set(x_568, 2, x_532);
lean_ctor_set(x_568, 3, x_561);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 lean_ctor_release(x_357, 1);
 lean_ctor_release(x_357, 2);
 lean_ctor_release(x_357, 3);
 x_569 = x_357;
} else {
 lean_dec_ref(x_357);
 x_569 = lean_box(0);
}
lean_ctor_set_uint8(x_568, sizeof(void*)*4 + 6, x_456);
lean_ctor_set_uint32(x_568, sizeof(void*)*4, x_565);
lean_ctor_set_uint16(x_568, sizeof(void*)*4 + 4, x_566);
lean_ctor_set_uint8(x_568, sizeof(void*)*4 + 7, x_567);
x_570 = 0;
x_571 = 0;
x_572 = 0;
if (lean_is_scalar(x_569)) {
 x_573 = lean_alloc_ctor(1, 4, 8);
} else {
 x_573 = x_569;
}
lean_ctor_set(x_573, 0, x_564);
lean_ctor_set(x_573, 1, x_50);
lean_ctor_set(x_573, 2, x_51);
lean_ctor_set(x_573, 3, x_52);
lean_ctor_set_uint8(x_573, sizeof(void*)*4 + 6, x_456);
lean_ctor_set_uint32(x_573, sizeof(void*)*4, x_570);
lean_ctor_set_uint16(x_573, sizeof(void*)*4 + 4, x_571);
lean_ctor_set_uint8(x_573, sizeof(void*)*4 + 7, x_572);
x_574 = 0;
x_575 = 0;
x_576 = 0;
lean_ctor_set(x_356, 3, x_573);
lean_ctor_set(x_356, 2, x_563);
lean_ctor_set(x_356, 1, x_562);
lean_ctor_set(x_356, 0, x_568);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 6, x_529);
lean_ctor_set_uint32(x_356, sizeof(void*)*4, x_574);
lean_ctor_set_uint16(x_356, sizeof(void*)*4 + 4, x_575);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 7, x_576);
return x_356;
}
}
else
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; uint32_t x_584; uint16_t x_585; uint8_t x_586; lean_object* x_587; lean_object* x_588; uint32_t x_589; uint16_t x_590; uint8_t x_591; lean_object* x_592; uint32_t x_593; uint16_t x_594; uint8_t x_595; lean_object* x_596; 
x_577 = lean_ctor_get(x_356, 1);
x_578 = lean_ctor_get(x_356, 2);
lean_inc(x_578);
lean_inc(x_577);
lean_dec(x_356);
x_579 = lean_ctor_get(x_508, 0);
lean_inc(x_579);
x_580 = lean_ctor_get(x_508, 1);
lean_inc(x_580);
x_581 = lean_ctor_get(x_508, 2);
lean_inc(x_581);
x_582 = lean_ctor_get(x_508, 3);
lean_inc(x_582);
if (lean_is_exclusive(x_508)) {
 lean_ctor_release(x_508, 0);
 lean_ctor_release(x_508, 1);
 lean_ctor_release(x_508, 2);
 lean_ctor_release(x_508, 3);
 x_583 = x_508;
} else {
 lean_dec_ref(x_508);
 x_583 = lean_box(0);
}
x_584 = 0;
x_585 = 0;
x_586 = 0;
lean_inc(x_357);
if (lean_is_scalar(x_583)) {
 x_587 = lean_alloc_ctor(1, 4, 8);
} else {
 x_587 = x_583;
}
lean_ctor_set(x_587, 0, x_357);
lean_ctor_set(x_587, 1, x_577);
lean_ctor_set(x_587, 2, x_578);
lean_ctor_set(x_587, 3, x_579);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 lean_ctor_release(x_357, 1);
 lean_ctor_release(x_357, 2);
 lean_ctor_release(x_357, 3);
 x_588 = x_357;
} else {
 lean_dec_ref(x_357);
 x_588 = lean_box(0);
}
lean_ctor_set_uint8(x_587, sizeof(void*)*4 + 6, x_456);
lean_ctor_set_uint32(x_587, sizeof(void*)*4, x_584);
lean_ctor_set_uint16(x_587, sizeof(void*)*4 + 4, x_585);
lean_ctor_set_uint8(x_587, sizeof(void*)*4 + 7, x_586);
x_589 = 0;
x_590 = 0;
x_591 = 0;
if (lean_is_scalar(x_588)) {
 x_592 = lean_alloc_ctor(1, 4, 8);
} else {
 x_592 = x_588;
}
lean_ctor_set(x_592, 0, x_582);
lean_ctor_set(x_592, 1, x_50);
lean_ctor_set(x_592, 2, x_51);
lean_ctor_set(x_592, 3, x_52);
lean_ctor_set_uint8(x_592, sizeof(void*)*4 + 6, x_456);
lean_ctor_set_uint32(x_592, sizeof(void*)*4, x_589);
lean_ctor_set_uint16(x_592, sizeof(void*)*4 + 4, x_590);
lean_ctor_set_uint8(x_592, sizeof(void*)*4 + 7, x_591);
x_593 = 0;
x_594 = 0;
x_595 = 0;
x_596 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_596, 0, x_587);
lean_ctor_set(x_596, 1, x_580);
lean_ctor_set(x_596, 2, x_581);
lean_ctor_set(x_596, 3, x_592);
lean_ctor_set_uint8(x_596, sizeof(void*)*4 + 6, x_529);
lean_ctor_set_uint32(x_596, sizeof(void*)*4, x_593);
lean_ctor_set_uint16(x_596, sizeof(void*)*4 + 4, x_594);
lean_ctor_set_uint8(x_596, sizeof(void*)*4 + 7, x_595);
return x_596;
}
}
else
{
uint8_t x_597; 
x_597 = !lean_is_exclusive(x_356);
if (x_597 == 0)
{
lean_object* x_598; lean_object* x_599; uint8_t x_600; 
x_598 = lean_ctor_get(x_356, 3);
lean_dec(x_598);
x_599 = lean_ctor_get(x_356, 0);
lean_dec(x_599);
x_600 = !lean_is_exclusive(x_357);
if (x_600 == 0)
{
uint32_t x_601; uint16_t x_602; uint8_t x_603; uint8_t x_604; uint32_t x_605; uint16_t x_606; uint8_t x_607; uint32_t x_608; uint16_t x_609; uint8_t x_610; 
x_601 = 0;
x_602 = 0;
x_603 = 0;
lean_ctor_set_uint8(x_357, sizeof(void*)*4 + 6, x_529);
lean_ctor_set_uint32(x_357, sizeof(void*)*4, x_601);
lean_ctor_set_uint16(x_357, sizeof(void*)*4 + 4, x_602);
lean_ctor_set_uint8(x_357, sizeof(void*)*4 + 7, x_603);
x_604 = 0;
x_605 = 0;
x_606 = 0;
x_607 = 0;
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 6, x_604);
lean_ctor_set_uint32(x_356, sizeof(void*)*4, x_605);
lean_ctor_set_uint16(x_356, sizeof(void*)*4 + 4, x_606);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 7, x_607);
x_608 = 0;
x_609 = 0;
x_610 = 0;
lean_ctor_set(x_1, 0, x_356);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_529);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_608);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_609);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_610);
return x_1;
}
else
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; uint32_t x_615; uint16_t x_616; uint8_t x_617; lean_object* x_618; uint8_t x_619; uint32_t x_620; uint16_t x_621; uint8_t x_622; uint32_t x_623; uint16_t x_624; uint8_t x_625; 
x_611 = lean_ctor_get(x_357, 0);
x_612 = lean_ctor_get(x_357, 1);
x_613 = lean_ctor_get(x_357, 2);
x_614 = lean_ctor_get(x_357, 3);
lean_inc(x_614);
lean_inc(x_613);
lean_inc(x_612);
lean_inc(x_611);
lean_dec(x_357);
x_615 = 0;
x_616 = 0;
x_617 = 0;
x_618 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_618, 0, x_611);
lean_ctor_set(x_618, 1, x_612);
lean_ctor_set(x_618, 2, x_613);
lean_ctor_set(x_618, 3, x_614);
lean_ctor_set_uint8(x_618, sizeof(void*)*4 + 6, x_529);
lean_ctor_set_uint32(x_618, sizeof(void*)*4, x_615);
lean_ctor_set_uint16(x_618, sizeof(void*)*4 + 4, x_616);
lean_ctor_set_uint8(x_618, sizeof(void*)*4 + 7, x_617);
x_619 = 0;
x_620 = 0;
x_621 = 0;
x_622 = 0;
lean_ctor_set(x_356, 0, x_618);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 6, x_619);
lean_ctor_set_uint32(x_356, sizeof(void*)*4, x_620);
lean_ctor_set_uint16(x_356, sizeof(void*)*4 + 4, x_621);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 7, x_622);
x_623 = 0;
x_624 = 0;
x_625 = 0;
lean_ctor_set(x_1, 0, x_356);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_529);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_623);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_624);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_625);
return x_1;
}
}
else
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; uint32_t x_633; uint16_t x_634; uint8_t x_635; lean_object* x_636; uint8_t x_637; uint32_t x_638; uint16_t x_639; uint8_t x_640; lean_object* x_641; uint32_t x_642; uint16_t x_643; uint8_t x_644; 
x_626 = lean_ctor_get(x_356, 1);
x_627 = lean_ctor_get(x_356, 2);
lean_inc(x_627);
lean_inc(x_626);
lean_dec(x_356);
x_628 = lean_ctor_get(x_357, 0);
lean_inc(x_628);
x_629 = lean_ctor_get(x_357, 1);
lean_inc(x_629);
x_630 = lean_ctor_get(x_357, 2);
lean_inc(x_630);
x_631 = lean_ctor_get(x_357, 3);
lean_inc(x_631);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 lean_ctor_release(x_357, 1);
 lean_ctor_release(x_357, 2);
 lean_ctor_release(x_357, 3);
 x_632 = x_357;
} else {
 lean_dec_ref(x_357);
 x_632 = lean_box(0);
}
x_633 = 0;
x_634 = 0;
x_635 = 0;
if (lean_is_scalar(x_632)) {
 x_636 = lean_alloc_ctor(1, 4, 8);
} else {
 x_636 = x_632;
}
lean_ctor_set(x_636, 0, x_628);
lean_ctor_set(x_636, 1, x_629);
lean_ctor_set(x_636, 2, x_630);
lean_ctor_set(x_636, 3, x_631);
lean_ctor_set_uint8(x_636, sizeof(void*)*4 + 6, x_529);
lean_ctor_set_uint32(x_636, sizeof(void*)*4, x_633);
lean_ctor_set_uint16(x_636, sizeof(void*)*4 + 4, x_634);
lean_ctor_set_uint8(x_636, sizeof(void*)*4 + 7, x_635);
x_637 = 0;
x_638 = 0;
x_639 = 0;
x_640 = 0;
x_641 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_641, 0, x_636);
lean_ctor_set(x_641, 1, x_626);
lean_ctor_set(x_641, 2, x_627);
lean_ctor_set(x_641, 3, x_508);
lean_ctor_set_uint8(x_641, sizeof(void*)*4 + 6, x_637);
lean_ctor_set_uint32(x_641, sizeof(void*)*4, x_638);
lean_ctor_set_uint16(x_641, sizeof(void*)*4 + 4, x_639);
lean_ctor_set_uint8(x_641, sizeof(void*)*4 + 7, x_640);
x_642 = 0;
x_643 = 0;
x_644 = 0;
lean_ctor_set(x_1, 0, x_641);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_529);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_642);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_643);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_644);
return x_1;
}
}
}
}
}
}
}
}
else
{
lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; uint8_t x_649; 
x_645 = lean_ctor_get(x_1, 0);
x_646 = lean_ctor_get(x_1, 1);
x_647 = lean_ctor_get(x_1, 2);
x_648 = lean_ctor_get(x_1, 3);
lean_inc(x_648);
lean_inc(x_647);
lean_inc(x_646);
lean_inc(x_645);
lean_dec(x_1);
x_649 = lean_nat_dec_lt(x_2, x_646);
if (x_649 == 0)
{
uint8_t x_650; 
x_650 = lean_nat_dec_lt(x_646, x_2);
if (x_650 == 0)
{
uint32_t x_651; uint16_t x_652; uint8_t x_653; lean_object* x_654; 
lean_dec(x_647);
lean_dec(x_646);
x_651 = 0;
x_652 = 0;
x_653 = 0;
x_654 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_654, 0, x_645);
lean_ctor_set(x_654, 1, x_2);
lean_ctor_set(x_654, 2, x_3);
lean_ctor_set(x_654, 3, x_648);
lean_ctor_set_uint8(x_654, sizeof(void*)*4 + 6, x_9);
lean_ctor_set_uint32(x_654, sizeof(void*)*4, x_651);
lean_ctor_set_uint16(x_654, sizeof(void*)*4 + 4, x_652);
lean_ctor_set_uint8(x_654, sizeof(void*)*4 + 7, x_653);
return x_654;
}
else
{
uint8_t x_655; 
x_655 = l_RBNode_isRed___rarg(x_648);
if (x_655 == 0)
{
lean_object* x_656; uint32_t x_657; uint16_t x_658; uint8_t x_659; lean_object* x_660; 
x_656 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_648, x_2, x_3);
x_657 = 0;
x_658 = 0;
x_659 = 0;
x_660 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_660, 0, x_645);
lean_ctor_set(x_660, 1, x_646);
lean_ctor_set(x_660, 2, x_647);
lean_ctor_set(x_660, 3, x_656);
lean_ctor_set_uint8(x_660, sizeof(void*)*4 + 6, x_9);
lean_ctor_set_uint32(x_660, sizeof(void*)*4, x_657);
lean_ctor_set_uint16(x_660, sizeof(void*)*4 + 4, x_658);
lean_ctor_set_uint8(x_660, sizeof(void*)*4 + 7, x_659);
return x_660;
}
else
{
lean_object* x_661; lean_object* x_662; 
x_661 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_648, x_2, x_3);
x_662 = lean_ctor_get(x_661, 0);
lean_inc(x_662);
if (lean_obj_tag(x_662) == 0)
{
lean_object* x_663; 
x_663 = lean_ctor_get(x_661, 3);
lean_inc(x_663);
if (lean_obj_tag(x_663) == 0)
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; uint8_t x_667; uint32_t x_668; uint16_t x_669; uint8_t x_670; lean_object* x_671; uint8_t x_672; uint32_t x_673; uint16_t x_674; uint8_t x_675; lean_object* x_676; 
x_664 = lean_ctor_get(x_661, 1);
lean_inc(x_664);
x_665 = lean_ctor_get(x_661, 2);
lean_inc(x_665);
if (lean_is_exclusive(x_661)) {
 lean_ctor_release(x_661, 0);
 lean_ctor_release(x_661, 1);
 lean_ctor_release(x_661, 2);
 lean_ctor_release(x_661, 3);
 x_666 = x_661;
} else {
 lean_dec_ref(x_661);
 x_666 = lean_box(0);
}
x_667 = 0;
x_668 = 0;
x_669 = 0;
x_670 = 0;
if (lean_is_scalar(x_666)) {
 x_671 = lean_alloc_ctor(1, 4, 8);
} else {
 x_671 = x_666;
}
lean_ctor_set(x_671, 0, x_663);
lean_ctor_set(x_671, 1, x_664);
lean_ctor_set(x_671, 2, x_665);
lean_ctor_set(x_671, 3, x_663);
lean_ctor_set_uint8(x_671, sizeof(void*)*4 + 6, x_667);
lean_ctor_set_uint32(x_671, sizeof(void*)*4, x_668);
lean_ctor_set_uint16(x_671, sizeof(void*)*4 + 4, x_669);
lean_ctor_set_uint8(x_671, sizeof(void*)*4 + 7, x_670);
x_672 = 1;
x_673 = 0;
x_674 = 0;
x_675 = 0;
x_676 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_676, 0, x_645);
lean_ctor_set(x_676, 1, x_646);
lean_ctor_set(x_676, 2, x_647);
lean_ctor_set(x_676, 3, x_671);
lean_ctor_set_uint8(x_676, sizeof(void*)*4 + 6, x_672);
lean_ctor_set_uint32(x_676, sizeof(void*)*4, x_673);
lean_ctor_set_uint16(x_676, sizeof(void*)*4 + 4, x_674);
lean_ctor_set_uint8(x_676, sizeof(void*)*4 + 7, x_675);
return x_676;
}
else
{
uint8_t x_677; 
x_677 = lean_ctor_get_uint8(x_663, sizeof(void*)*4 + 6);
if (x_677 == 0)
{
lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; uint8_t x_686; uint32_t x_687; uint16_t x_688; uint8_t x_689; lean_object* x_690; uint32_t x_691; uint16_t x_692; uint8_t x_693; lean_object* x_694; uint32_t x_695; uint16_t x_696; uint8_t x_697; lean_object* x_698; 
x_678 = lean_ctor_get(x_661, 1);
lean_inc(x_678);
x_679 = lean_ctor_get(x_661, 2);
lean_inc(x_679);
if (lean_is_exclusive(x_661)) {
 lean_ctor_release(x_661, 0);
 lean_ctor_release(x_661, 1);
 lean_ctor_release(x_661, 2);
 lean_ctor_release(x_661, 3);
 x_680 = x_661;
} else {
 lean_dec_ref(x_661);
 x_680 = lean_box(0);
}
x_681 = lean_ctor_get(x_663, 0);
lean_inc(x_681);
x_682 = lean_ctor_get(x_663, 1);
lean_inc(x_682);
x_683 = lean_ctor_get(x_663, 2);
lean_inc(x_683);
x_684 = lean_ctor_get(x_663, 3);
lean_inc(x_684);
if (lean_is_exclusive(x_663)) {
 lean_ctor_release(x_663, 0);
 lean_ctor_release(x_663, 1);
 lean_ctor_release(x_663, 2);
 lean_ctor_release(x_663, 3);
 x_685 = x_663;
} else {
 lean_dec_ref(x_663);
 x_685 = lean_box(0);
}
x_686 = 1;
x_687 = 0;
x_688 = 0;
x_689 = 0;
if (lean_is_scalar(x_685)) {
 x_690 = lean_alloc_ctor(1, 4, 8);
} else {
 x_690 = x_685;
}
lean_ctor_set(x_690, 0, x_645);
lean_ctor_set(x_690, 1, x_646);
lean_ctor_set(x_690, 2, x_647);
lean_ctor_set(x_690, 3, x_662);
lean_ctor_set_uint8(x_690, sizeof(void*)*4 + 6, x_686);
lean_ctor_set_uint32(x_690, sizeof(void*)*4, x_687);
lean_ctor_set_uint16(x_690, sizeof(void*)*4 + 4, x_688);
lean_ctor_set_uint8(x_690, sizeof(void*)*4 + 7, x_689);
x_691 = 0;
x_692 = 0;
x_693 = 0;
if (lean_is_scalar(x_680)) {
 x_694 = lean_alloc_ctor(1, 4, 8);
} else {
 x_694 = x_680;
}
lean_ctor_set(x_694, 0, x_681);
lean_ctor_set(x_694, 1, x_682);
lean_ctor_set(x_694, 2, x_683);
lean_ctor_set(x_694, 3, x_684);
lean_ctor_set_uint8(x_694, sizeof(void*)*4 + 6, x_686);
lean_ctor_set_uint32(x_694, sizeof(void*)*4, x_691);
lean_ctor_set_uint16(x_694, sizeof(void*)*4 + 4, x_692);
lean_ctor_set_uint8(x_694, sizeof(void*)*4 + 7, x_693);
x_695 = 0;
x_696 = 0;
x_697 = 0;
x_698 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_698, 0, x_690);
lean_ctor_set(x_698, 1, x_678);
lean_ctor_set(x_698, 2, x_679);
lean_ctor_set(x_698, 3, x_694);
lean_ctor_set_uint8(x_698, sizeof(void*)*4 + 6, x_677);
lean_ctor_set_uint32(x_698, sizeof(void*)*4, x_695);
lean_ctor_set_uint16(x_698, sizeof(void*)*4 + 4, x_696);
lean_ctor_set_uint8(x_698, sizeof(void*)*4 + 7, x_697);
return x_698;
}
else
{
lean_object* x_699; lean_object* x_700; lean_object* x_701; uint8_t x_702; uint32_t x_703; uint16_t x_704; uint8_t x_705; lean_object* x_706; uint32_t x_707; uint16_t x_708; uint8_t x_709; lean_object* x_710; 
x_699 = lean_ctor_get(x_661, 1);
lean_inc(x_699);
x_700 = lean_ctor_get(x_661, 2);
lean_inc(x_700);
if (lean_is_exclusive(x_661)) {
 lean_ctor_release(x_661, 0);
 lean_ctor_release(x_661, 1);
 lean_ctor_release(x_661, 2);
 lean_ctor_release(x_661, 3);
 x_701 = x_661;
} else {
 lean_dec_ref(x_661);
 x_701 = lean_box(0);
}
x_702 = 0;
x_703 = 0;
x_704 = 0;
x_705 = 0;
if (lean_is_scalar(x_701)) {
 x_706 = lean_alloc_ctor(1, 4, 8);
} else {
 x_706 = x_701;
}
lean_ctor_set(x_706, 0, x_662);
lean_ctor_set(x_706, 1, x_699);
lean_ctor_set(x_706, 2, x_700);
lean_ctor_set(x_706, 3, x_663);
lean_ctor_set_uint8(x_706, sizeof(void*)*4 + 6, x_702);
lean_ctor_set_uint32(x_706, sizeof(void*)*4, x_703);
lean_ctor_set_uint16(x_706, sizeof(void*)*4 + 4, x_704);
lean_ctor_set_uint8(x_706, sizeof(void*)*4 + 7, x_705);
x_707 = 0;
x_708 = 0;
x_709 = 0;
x_710 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_710, 0, x_645);
lean_ctor_set(x_710, 1, x_646);
lean_ctor_set(x_710, 2, x_647);
lean_ctor_set(x_710, 3, x_706);
lean_ctor_set_uint8(x_710, sizeof(void*)*4 + 6, x_677);
lean_ctor_set_uint32(x_710, sizeof(void*)*4, x_707);
lean_ctor_set_uint16(x_710, sizeof(void*)*4 + 4, x_708);
lean_ctor_set_uint8(x_710, sizeof(void*)*4 + 7, x_709);
return x_710;
}
}
}
else
{
uint8_t x_711; 
x_711 = lean_ctor_get_uint8(x_662, sizeof(void*)*4 + 6);
if (x_711 == 0)
{
lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; uint8_t x_721; uint32_t x_722; uint16_t x_723; uint8_t x_724; lean_object* x_725; uint32_t x_726; uint16_t x_727; uint8_t x_728; lean_object* x_729; uint32_t x_730; uint16_t x_731; uint8_t x_732; lean_object* x_733; 
x_712 = lean_ctor_get(x_661, 1);
lean_inc(x_712);
x_713 = lean_ctor_get(x_661, 2);
lean_inc(x_713);
x_714 = lean_ctor_get(x_661, 3);
lean_inc(x_714);
if (lean_is_exclusive(x_661)) {
 lean_ctor_release(x_661, 0);
 lean_ctor_release(x_661, 1);
 lean_ctor_release(x_661, 2);
 lean_ctor_release(x_661, 3);
 x_715 = x_661;
} else {
 lean_dec_ref(x_661);
 x_715 = lean_box(0);
}
x_716 = lean_ctor_get(x_662, 0);
lean_inc(x_716);
x_717 = lean_ctor_get(x_662, 1);
lean_inc(x_717);
x_718 = lean_ctor_get(x_662, 2);
lean_inc(x_718);
x_719 = lean_ctor_get(x_662, 3);
lean_inc(x_719);
if (lean_is_exclusive(x_662)) {
 lean_ctor_release(x_662, 0);
 lean_ctor_release(x_662, 1);
 lean_ctor_release(x_662, 2);
 lean_ctor_release(x_662, 3);
 x_720 = x_662;
} else {
 lean_dec_ref(x_662);
 x_720 = lean_box(0);
}
x_721 = 1;
x_722 = 0;
x_723 = 0;
x_724 = 0;
if (lean_is_scalar(x_720)) {
 x_725 = lean_alloc_ctor(1, 4, 8);
} else {
 x_725 = x_720;
}
lean_ctor_set(x_725, 0, x_645);
lean_ctor_set(x_725, 1, x_646);
lean_ctor_set(x_725, 2, x_647);
lean_ctor_set(x_725, 3, x_716);
lean_ctor_set_uint8(x_725, sizeof(void*)*4 + 6, x_721);
lean_ctor_set_uint32(x_725, sizeof(void*)*4, x_722);
lean_ctor_set_uint16(x_725, sizeof(void*)*4 + 4, x_723);
lean_ctor_set_uint8(x_725, sizeof(void*)*4 + 7, x_724);
x_726 = 0;
x_727 = 0;
x_728 = 0;
if (lean_is_scalar(x_715)) {
 x_729 = lean_alloc_ctor(1, 4, 8);
} else {
 x_729 = x_715;
}
lean_ctor_set(x_729, 0, x_719);
lean_ctor_set(x_729, 1, x_712);
lean_ctor_set(x_729, 2, x_713);
lean_ctor_set(x_729, 3, x_714);
lean_ctor_set_uint8(x_729, sizeof(void*)*4 + 6, x_721);
lean_ctor_set_uint32(x_729, sizeof(void*)*4, x_726);
lean_ctor_set_uint16(x_729, sizeof(void*)*4 + 4, x_727);
lean_ctor_set_uint8(x_729, sizeof(void*)*4 + 7, x_728);
x_730 = 0;
x_731 = 0;
x_732 = 0;
x_733 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_733, 0, x_725);
lean_ctor_set(x_733, 1, x_717);
lean_ctor_set(x_733, 2, x_718);
lean_ctor_set(x_733, 3, x_729);
lean_ctor_set_uint8(x_733, sizeof(void*)*4 + 6, x_711);
lean_ctor_set_uint32(x_733, sizeof(void*)*4, x_730);
lean_ctor_set_uint16(x_733, sizeof(void*)*4 + 4, x_731);
lean_ctor_set_uint8(x_733, sizeof(void*)*4 + 7, x_732);
return x_733;
}
else
{
lean_object* x_734; 
x_734 = lean_ctor_get(x_661, 3);
lean_inc(x_734);
if (lean_obj_tag(x_734) == 0)
{
lean_object* x_735; lean_object* x_736; lean_object* x_737; uint8_t x_738; uint32_t x_739; uint16_t x_740; uint8_t x_741; lean_object* x_742; uint32_t x_743; uint16_t x_744; uint8_t x_745; lean_object* x_746; 
x_735 = lean_ctor_get(x_661, 1);
lean_inc(x_735);
x_736 = lean_ctor_get(x_661, 2);
lean_inc(x_736);
if (lean_is_exclusive(x_661)) {
 lean_ctor_release(x_661, 0);
 lean_ctor_release(x_661, 1);
 lean_ctor_release(x_661, 2);
 lean_ctor_release(x_661, 3);
 x_737 = x_661;
} else {
 lean_dec_ref(x_661);
 x_737 = lean_box(0);
}
x_738 = 0;
x_739 = 0;
x_740 = 0;
x_741 = 0;
if (lean_is_scalar(x_737)) {
 x_742 = lean_alloc_ctor(1, 4, 8);
} else {
 x_742 = x_737;
}
lean_ctor_set(x_742, 0, x_662);
lean_ctor_set(x_742, 1, x_735);
lean_ctor_set(x_742, 2, x_736);
lean_ctor_set(x_742, 3, x_734);
lean_ctor_set_uint8(x_742, sizeof(void*)*4 + 6, x_738);
lean_ctor_set_uint32(x_742, sizeof(void*)*4, x_739);
lean_ctor_set_uint16(x_742, sizeof(void*)*4 + 4, x_740);
lean_ctor_set_uint8(x_742, sizeof(void*)*4 + 7, x_741);
x_743 = 0;
x_744 = 0;
x_745 = 0;
x_746 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_746, 0, x_645);
lean_ctor_set(x_746, 1, x_646);
lean_ctor_set(x_746, 2, x_647);
lean_ctor_set(x_746, 3, x_742);
lean_ctor_set_uint8(x_746, sizeof(void*)*4 + 6, x_711);
lean_ctor_set_uint32(x_746, sizeof(void*)*4, x_743);
lean_ctor_set_uint16(x_746, sizeof(void*)*4 + 4, x_744);
lean_ctor_set_uint8(x_746, sizeof(void*)*4 + 7, x_745);
return x_746;
}
else
{
uint8_t x_747; 
x_747 = lean_ctor_get_uint8(x_734, sizeof(void*)*4 + 6);
if (x_747 == 0)
{
lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; uint32_t x_756; uint16_t x_757; uint8_t x_758; lean_object* x_759; lean_object* x_760; uint32_t x_761; uint16_t x_762; uint8_t x_763; lean_object* x_764; uint32_t x_765; uint16_t x_766; uint8_t x_767; lean_object* x_768; 
x_748 = lean_ctor_get(x_661, 1);
lean_inc(x_748);
x_749 = lean_ctor_get(x_661, 2);
lean_inc(x_749);
if (lean_is_exclusive(x_661)) {
 lean_ctor_release(x_661, 0);
 lean_ctor_release(x_661, 1);
 lean_ctor_release(x_661, 2);
 lean_ctor_release(x_661, 3);
 x_750 = x_661;
} else {
 lean_dec_ref(x_661);
 x_750 = lean_box(0);
}
x_751 = lean_ctor_get(x_734, 0);
lean_inc(x_751);
x_752 = lean_ctor_get(x_734, 1);
lean_inc(x_752);
x_753 = lean_ctor_get(x_734, 2);
lean_inc(x_753);
x_754 = lean_ctor_get(x_734, 3);
lean_inc(x_754);
if (lean_is_exclusive(x_734)) {
 lean_ctor_release(x_734, 0);
 lean_ctor_release(x_734, 1);
 lean_ctor_release(x_734, 2);
 lean_ctor_release(x_734, 3);
 x_755 = x_734;
} else {
 lean_dec_ref(x_734);
 x_755 = lean_box(0);
}
x_756 = 0;
x_757 = 0;
x_758 = 0;
lean_inc(x_662);
if (lean_is_scalar(x_755)) {
 x_759 = lean_alloc_ctor(1, 4, 8);
} else {
 x_759 = x_755;
}
lean_ctor_set(x_759, 0, x_645);
lean_ctor_set(x_759, 1, x_646);
lean_ctor_set(x_759, 2, x_647);
lean_ctor_set(x_759, 3, x_662);
if (lean_is_exclusive(x_662)) {
 lean_ctor_release(x_662, 0);
 lean_ctor_release(x_662, 1);
 lean_ctor_release(x_662, 2);
 lean_ctor_release(x_662, 3);
 x_760 = x_662;
} else {
 lean_dec_ref(x_662);
 x_760 = lean_box(0);
}
lean_ctor_set_uint8(x_759, sizeof(void*)*4 + 6, x_711);
lean_ctor_set_uint32(x_759, sizeof(void*)*4, x_756);
lean_ctor_set_uint16(x_759, sizeof(void*)*4 + 4, x_757);
lean_ctor_set_uint8(x_759, sizeof(void*)*4 + 7, x_758);
x_761 = 0;
x_762 = 0;
x_763 = 0;
if (lean_is_scalar(x_760)) {
 x_764 = lean_alloc_ctor(1, 4, 8);
} else {
 x_764 = x_760;
}
lean_ctor_set(x_764, 0, x_751);
lean_ctor_set(x_764, 1, x_752);
lean_ctor_set(x_764, 2, x_753);
lean_ctor_set(x_764, 3, x_754);
lean_ctor_set_uint8(x_764, sizeof(void*)*4 + 6, x_711);
lean_ctor_set_uint32(x_764, sizeof(void*)*4, x_761);
lean_ctor_set_uint16(x_764, sizeof(void*)*4 + 4, x_762);
lean_ctor_set_uint8(x_764, sizeof(void*)*4 + 7, x_763);
x_765 = 0;
x_766 = 0;
x_767 = 0;
if (lean_is_scalar(x_750)) {
 x_768 = lean_alloc_ctor(1, 4, 8);
} else {
 x_768 = x_750;
}
lean_ctor_set(x_768, 0, x_759);
lean_ctor_set(x_768, 1, x_748);
lean_ctor_set(x_768, 2, x_749);
lean_ctor_set(x_768, 3, x_764);
lean_ctor_set_uint8(x_768, sizeof(void*)*4 + 6, x_747);
lean_ctor_set_uint32(x_768, sizeof(void*)*4, x_765);
lean_ctor_set_uint16(x_768, sizeof(void*)*4 + 4, x_766);
lean_ctor_set_uint8(x_768, sizeof(void*)*4 + 7, x_767);
return x_768;
}
else
{
lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; uint32_t x_777; uint16_t x_778; uint8_t x_779; lean_object* x_780; uint8_t x_781; uint32_t x_782; uint16_t x_783; uint8_t x_784; lean_object* x_785; uint32_t x_786; uint16_t x_787; uint8_t x_788; lean_object* x_789; 
x_769 = lean_ctor_get(x_661, 1);
lean_inc(x_769);
x_770 = lean_ctor_get(x_661, 2);
lean_inc(x_770);
if (lean_is_exclusive(x_661)) {
 lean_ctor_release(x_661, 0);
 lean_ctor_release(x_661, 1);
 lean_ctor_release(x_661, 2);
 lean_ctor_release(x_661, 3);
 x_771 = x_661;
} else {
 lean_dec_ref(x_661);
 x_771 = lean_box(0);
}
x_772 = lean_ctor_get(x_662, 0);
lean_inc(x_772);
x_773 = lean_ctor_get(x_662, 1);
lean_inc(x_773);
x_774 = lean_ctor_get(x_662, 2);
lean_inc(x_774);
x_775 = lean_ctor_get(x_662, 3);
lean_inc(x_775);
if (lean_is_exclusive(x_662)) {
 lean_ctor_release(x_662, 0);
 lean_ctor_release(x_662, 1);
 lean_ctor_release(x_662, 2);
 lean_ctor_release(x_662, 3);
 x_776 = x_662;
} else {
 lean_dec_ref(x_662);
 x_776 = lean_box(0);
}
x_777 = 0;
x_778 = 0;
x_779 = 0;
if (lean_is_scalar(x_776)) {
 x_780 = lean_alloc_ctor(1, 4, 8);
} else {
 x_780 = x_776;
}
lean_ctor_set(x_780, 0, x_772);
lean_ctor_set(x_780, 1, x_773);
lean_ctor_set(x_780, 2, x_774);
lean_ctor_set(x_780, 3, x_775);
lean_ctor_set_uint8(x_780, sizeof(void*)*4 + 6, x_747);
lean_ctor_set_uint32(x_780, sizeof(void*)*4, x_777);
lean_ctor_set_uint16(x_780, sizeof(void*)*4 + 4, x_778);
lean_ctor_set_uint8(x_780, sizeof(void*)*4 + 7, x_779);
x_781 = 0;
x_782 = 0;
x_783 = 0;
x_784 = 0;
if (lean_is_scalar(x_771)) {
 x_785 = lean_alloc_ctor(1, 4, 8);
} else {
 x_785 = x_771;
}
lean_ctor_set(x_785, 0, x_780);
lean_ctor_set(x_785, 1, x_769);
lean_ctor_set(x_785, 2, x_770);
lean_ctor_set(x_785, 3, x_734);
lean_ctor_set_uint8(x_785, sizeof(void*)*4 + 6, x_781);
lean_ctor_set_uint32(x_785, sizeof(void*)*4, x_782);
lean_ctor_set_uint16(x_785, sizeof(void*)*4 + 4, x_783);
lean_ctor_set_uint8(x_785, sizeof(void*)*4 + 7, x_784);
x_786 = 0;
x_787 = 0;
x_788 = 0;
x_789 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_789, 0, x_645);
lean_ctor_set(x_789, 1, x_646);
lean_ctor_set(x_789, 2, x_647);
lean_ctor_set(x_789, 3, x_785);
lean_ctor_set_uint8(x_789, sizeof(void*)*4 + 6, x_747);
lean_ctor_set_uint32(x_789, sizeof(void*)*4, x_786);
lean_ctor_set_uint16(x_789, sizeof(void*)*4 + 4, x_787);
lean_ctor_set_uint8(x_789, sizeof(void*)*4 + 7, x_788);
return x_789;
}
}
}
}
}
}
}
else
{
uint8_t x_790; 
x_790 = l_RBNode_isRed___rarg(x_645);
if (x_790 == 0)
{
lean_object* x_791; uint32_t x_792; uint16_t x_793; uint8_t x_794; lean_object* x_795; 
x_791 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_645, x_2, x_3);
x_792 = 0;
x_793 = 0;
x_794 = 0;
x_795 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_795, 0, x_791);
lean_ctor_set(x_795, 1, x_646);
lean_ctor_set(x_795, 2, x_647);
lean_ctor_set(x_795, 3, x_648);
lean_ctor_set_uint8(x_795, sizeof(void*)*4 + 6, x_9);
lean_ctor_set_uint32(x_795, sizeof(void*)*4, x_792);
lean_ctor_set_uint16(x_795, sizeof(void*)*4 + 4, x_793);
lean_ctor_set_uint8(x_795, sizeof(void*)*4 + 7, x_794);
return x_795;
}
else
{
lean_object* x_796; lean_object* x_797; 
x_796 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_645, x_2, x_3);
x_797 = lean_ctor_get(x_796, 0);
lean_inc(x_797);
if (lean_obj_tag(x_797) == 0)
{
lean_object* x_798; 
x_798 = lean_ctor_get(x_796, 3);
lean_inc(x_798);
if (lean_obj_tag(x_798) == 0)
{
lean_object* x_799; lean_object* x_800; lean_object* x_801; uint8_t x_802; uint32_t x_803; uint16_t x_804; uint8_t x_805; lean_object* x_806; uint8_t x_807; uint32_t x_808; uint16_t x_809; uint8_t x_810; lean_object* x_811; 
x_799 = lean_ctor_get(x_796, 1);
lean_inc(x_799);
x_800 = lean_ctor_get(x_796, 2);
lean_inc(x_800);
if (lean_is_exclusive(x_796)) {
 lean_ctor_release(x_796, 0);
 lean_ctor_release(x_796, 1);
 lean_ctor_release(x_796, 2);
 lean_ctor_release(x_796, 3);
 x_801 = x_796;
} else {
 lean_dec_ref(x_796);
 x_801 = lean_box(0);
}
x_802 = 0;
x_803 = 0;
x_804 = 0;
x_805 = 0;
if (lean_is_scalar(x_801)) {
 x_806 = lean_alloc_ctor(1, 4, 8);
} else {
 x_806 = x_801;
}
lean_ctor_set(x_806, 0, x_798);
lean_ctor_set(x_806, 1, x_799);
lean_ctor_set(x_806, 2, x_800);
lean_ctor_set(x_806, 3, x_798);
lean_ctor_set_uint8(x_806, sizeof(void*)*4 + 6, x_802);
lean_ctor_set_uint32(x_806, sizeof(void*)*4, x_803);
lean_ctor_set_uint16(x_806, sizeof(void*)*4 + 4, x_804);
lean_ctor_set_uint8(x_806, sizeof(void*)*4 + 7, x_805);
x_807 = 1;
x_808 = 0;
x_809 = 0;
x_810 = 0;
x_811 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_811, 0, x_806);
lean_ctor_set(x_811, 1, x_646);
lean_ctor_set(x_811, 2, x_647);
lean_ctor_set(x_811, 3, x_648);
lean_ctor_set_uint8(x_811, sizeof(void*)*4 + 6, x_807);
lean_ctor_set_uint32(x_811, sizeof(void*)*4, x_808);
lean_ctor_set_uint16(x_811, sizeof(void*)*4 + 4, x_809);
lean_ctor_set_uint8(x_811, sizeof(void*)*4 + 7, x_810);
return x_811;
}
else
{
uint8_t x_812; 
x_812 = lean_ctor_get_uint8(x_798, sizeof(void*)*4 + 6);
if (x_812 == 0)
{
lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; uint8_t x_821; uint32_t x_822; uint16_t x_823; uint8_t x_824; lean_object* x_825; uint32_t x_826; uint16_t x_827; uint8_t x_828; lean_object* x_829; uint32_t x_830; uint16_t x_831; uint8_t x_832; lean_object* x_833; 
x_813 = lean_ctor_get(x_796, 1);
lean_inc(x_813);
x_814 = lean_ctor_get(x_796, 2);
lean_inc(x_814);
if (lean_is_exclusive(x_796)) {
 lean_ctor_release(x_796, 0);
 lean_ctor_release(x_796, 1);
 lean_ctor_release(x_796, 2);
 lean_ctor_release(x_796, 3);
 x_815 = x_796;
} else {
 lean_dec_ref(x_796);
 x_815 = lean_box(0);
}
x_816 = lean_ctor_get(x_798, 0);
lean_inc(x_816);
x_817 = lean_ctor_get(x_798, 1);
lean_inc(x_817);
x_818 = lean_ctor_get(x_798, 2);
lean_inc(x_818);
x_819 = lean_ctor_get(x_798, 3);
lean_inc(x_819);
if (lean_is_exclusive(x_798)) {
 lean_ctor_release(x_798, 0);
 lean_ctor_release(x_798, 1);
 lean_ctor_release(x_798, 2);
 lean_ctor_release(x_798, 3);
 x_820 = x_798;
} else {
 lean_dec_ref(x_798);
 x_820 = lean_box(0);
}
x_821 = 1;
x_822 = 0;
x_823 = 0;
x_824 = 0;
if (lean_is_scalar(x_820)) {
 x_825 = lean_alloc_ctor(1, 4, 8);
} else {
 x_825 = x_820;
}
lean_ctor_set(x_825, 0, x_797);
lean_ctor_set(x_825, 1, x_813);
lean_ctor_set(x_825, 2, x_814);
lean_ctor_set(x_825, 3, x_816);
lean_ctor_set_uint8(x_825, sizeof(void*)*4 + 6, x_821);
lean_ctor_set_uint32(x_825, sizeof(void*)*4, x_822);
lean_ctor_set_uint16(x_825, sizeof(void*)*4 + 4, x_823);
lean_ctor_set_uint8(x_825, sizeof(void*)*4 + 7, x_824);
x_826 = 0;
x_827 = 0;
x_828 = 0;
if (lean_is_scalar(x_815)) {
 x_829 = lean_alloc_ctor(1, 4, 8);
} else {
 x_829 = x_815;
}
lean_ctor_set(x_829, 0, x_819);
lean_ctor_set(x_829, 1, x_646);
lean_ctor_set(x_829, 2, x_647);
lean_ctor_set(x_829, 3, x_648);
lean_ctor_set_uint8(x_829, sizeof(void*)*4 + 6, x_821);
lean_ctor_set_uint32(x_829, sizeof(void*)*4, x_826);
lean_ctor_set_uint16(x_829, sizeof(void*)*4 + 4, x_827);
lean_ctor_set_uint8(x_829, sizeof(void*)*4 + 7, x_828);
x_830 = 0;
x_831 = 0;
x_832 = 0;
x_833 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_833, 0, x_825);
lean_ctor_set(x_833, 1, x_817);
lean_ctor_set(x_833, 2, x_818);
lean_ctor_set(x_833, 3, x_829);
lean_ctor_set_uint8(x_833, sizeof(void*)*4 + 6, x_812);
lean_ctor_set_uint32(x_833, sizeof(void*)*4, x_830);
lean_ctor_set_uint16(x_833, sizeof(void*)*4 + 4, x_831);
lean_ctor_set_uint8(x_833, sizeof(void*)*4 + 7, x_832);
return x_833;
}
else
{
lean_object* x_834; lean_object* x_835; lean_object* x_836; uint8_t x_837; uint32_t x_838; uint16_t x_839; uint8_t x_840; lean_object* x_841; uint32_t x_842; uint16_t x_843; uint8_t x_844; lean_object* x_845; 
x_834 = lean_ctor_get(x_796, 1);
lean_inc(x_834);
x_835 = lean_ctor_get(x_796, 2);
lean_inc(x_835);
if (lean_is_exclusive(x_796)) {
 lean_ctor_release(x_796, 0);
 lean_ctor_release(x_796, 1);
 lean_ctor_release(x_796, 2);
 lean_ctor_release(x_796, 3);
 x_836 = x_796;
} else {
 lean_dec_ref(x_796);
 x_836 = lean_box(0);
}
x_837 = 0;
x_838 = 0;
x_839 = 0;
x_840 = 0;
if (lean_is_scalar(x_836)) {
 x_841 = lean_alloc_ctor(1, 4, 8);
} else {
 x_841 = x_836;
}
lean_ctor_set(x_841, 0, x_797);
lean_ctor_set(x_841, 1, x_834);
lean_ctor_set(x_841, 2, x_835);
lean_ctor_set(x_841, 3, x_798);
lean_ctor_set_uint8(x_841, sizeof(void*)*4 + 6, x_837);
lean_ctor_set_uint32(x_841, sizeof(void*)*4, x_838);
lean_ctor_set_uint16(x_841, sizeof(void*)*4 + 4, x_839);
lean_ctor_set_uint8(x_841, sizeof(void*)*4 + 7, x_840);
x_842 = 0;
x_843 = 0;
x_844 = 0;
x_845 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_845, 0, x_841);
lean_ctor_set(x_845, 1, x_646);
lean_ctor_set(x_845, 2, x_647);
lean_ctor_set(x_845, 3, x_648);
lean_ctor_set_uint8(x_845, sizeof(void*)*4 + 6, x_812);
lean_ctor_set_uint32(x_845, sizeof(void*)*4, x_842);
lean_ctor_set_uint16(x_845, sizeof(void*)*4 + 4, x_843);
lean_ctor_set_uint8(x_845, sizeof(void*)*4 + 7, x_844);
return x_845;
}
}
}
else
{
uint8_t x_846; 
x_846 = lean_ctor_get_uint8(x_797, sizeof(void*)*4 + 6);
if (x_846 == 0)
{
lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; uint8_t x_856; uint32_t x_857; uint16_t x_858; uint8_t x_859; lean_object* x_860; uint32_t x_861; uint16_t x_862; uint8_t x_863; lean_object* x_864; uint32_t x_865; uint16_t x_866; uint8_t x_867; lean_object* x_868; 
x_847 = lean_ctor_get(x_796, 1);
lean_inc(x_847);
x_848 = lean_ctor_get(x_796, 2);
lean_inc(x_848);
x_849 = lean_ctor_get(x_796, 3);
lean_inc(x_849);
if (lean_is_exclusive(x_796)) {
 lean_ctor_release(x_796, 0);
 lean_ctor_release(x_796, 1);
 lean_ctor_release(x_796, 2);
 lean_ctor_release(x_796, 3);
 x_850 = x_796;
} else {
 lean_dec_ref(x_796);
 x_850 = lean_box(0);
}
x_851 = lean_ctor_get(x_797, 0);
lean_inc(x_851);
x_852 = lean_ctor_get(x_797, 1);
lean_inc(x_852);
x_853 = lean_ctor_get(x_797, 2);
lean_inc(x_853);
x_854 = lean_ctor_get(x_797, 3);
lean_inc(x_854);
if (lean_is_exclusive(x_797)) {
 lean_ctor_release(x_797, 0);
 lean_ctor_release(x_797, 1);
 lean_ctor_release(x_797, 2);
 lean_ctor_release(x_797, 3);
 x_855 = x_797;
} else {
 lean_dec_ref(x_797);
 x_855 = lean_box(0);
}
x_856 = 1;
x_857 = 0;
x_858 = 0;
x_859 = 0;
if (lean_is_scalar(x_855)) {
 x_860 = lean_alloc_ctor(1, 4, 8);
} else {
 x_860 = x_855;
}
lean_ctor_set(x_860, 0, x_851);
lean_ctor_set(x_860, 1, x_852);
lean_ctor_set(x_860, 2, x_853);
lean_ctor_set(x_860, 3, x_854);
lean_ctor_set_uint8(x_860, sizeof(void*)*4 + 6, x_856);
lean_ctor_set_uint32(x_860, sizeof(void*)*4, x_857);
lean_ctor_set_uint16(x_860, sizeof(void*)*4 + 4, x_858);
lean_ctor_set_uint8(x_860, sizeof(void*)*4 + 7, x_859);
x_861 = 0;
x_862 = 0;
x_863 = 0;
if (lean_is_scalar(x_850)) {
 x_864 = lean_alloc_ctor(1, 4, 8);
} else {
 x_864 = x_850;
}
lean_ctor_set(x_864, 0, x_849);
lean_ctor_set(x_864, 1, x_646);
lean_ctor_set(x_864, 2, x_647);
lean_ctor_set(x_864, 3, x_648);
lean_ctor_set_uint8(x_864, sizeof(void*)*4 + 6, x_856);
lean_ctor_set_uint32(x_864, sizeof(void*)*4, x_861);
lean_ctor_set_uint16(x_864, sizeof(void*)*4 + 4, x_862);
lean_ctor_set_uint8(x_864, sizeof(void*)*4 + 7, x_863);
x_865 = 0;
x_866 = 0;
x_867 = 0;
x_868 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_868, 0, x_860);
lean_ctor_set(x_868, 1, x_847);
lean_ctor_set(x_868, 2, x_848);
lean_ctor_set(x_868, 3, x_864);
lean_ctor_set_uint8(x_868, sizeof(void*)*4 + 6, x_846);
lean_ctor_set_uint32(x_868, sizeof(void*)*4, x_865);
lean_ctor_set_uint16(x_868, sizeof(void*)*4 + 4, x_866);
lean_ctor_set_uint8(x_868, sizeof(void*)*4 + 7, x_867);
return x_868;
}
else
{
lean_object* x_869; 
x_869 = lean_ctor_get(x_796, 3);
lean_inc(x_869);
if (lean_obj_tag(x_869) == 0)
{
lean_object* x_870; lean_object* x_871; lean_object* x_872; uint8_t x_873; uint32_t x_874; uint16_t x_875; uint8_t x_876; lean_object* x_877; uint32_t x_878; uint16_t x_879; uint8_t x_880; lean_object* x_881; 
x_870 = lean_ctor_get(x_796, 1);
lean_inc(x_870);
x_871 = lean_ctor_get(x_796, 2);
lean_inc(x_871);
if (lean_is_exclusive(x_796)) {
 lean_ctor_release(x_796, 0);
 lean_ctor_release(x_796, 1);
 lean_ctor_release(x_796, 2);
 lean_ctor_release(x_796, 3);
 x_872 = x_796;
} else {
 lean_dec_ref(x_796);
 x_872 = lean_box(0);
}
x_873 = 0;
x_874 = 0;
x_875 = 0;
x_876 = 0;
if (lean_is_scalar(x_872)) {
 x_877 = lean_alloc_ctor(1, 4, 8);
} else {
 x_877 = x_872;
}
lean_ctor_set(x_877, 0, x_797);
lean_ctor_set(x_877, 1, x_870);
lean_ctor_set(x_877, 2, x_871);
lean_ctor_set(x_877, 3, x_869);
lean_ctor_set_uint8(x_877, sizeof(void*)*4 + 6, x_873);
lean_ctor_set_uint32(x_877, sizeof(void*)*4, x_874);
lean_ctor_set_uint16(x_877, sizeof(void*)*4 + 4, x_875);
lean_ctor_set_uint8(x_877, sizeof(void*)*4 + 7, x_876);
x_878 = 0;
x_879 = 0;
x_880 = 0;
x_881 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_881, 0, x_877);
lean_ctor_set(x_881, 1, x_646);
lean_ctor_set(x_881, 2, x_647);
lean_ctor_set(x_881, 3, x_648);
lean_ctor_set_uint8(x_881, sizeof(void*)*4 + 6, x_846);
lean_ctor_set_uint32(x_881, sizeof(void*)*4, x_878);
lean_ctor_set_uint16(x_881, sizeof(void*)*4 + 4, x_879);
lean_ctor_set_uint8(x_881, sizeof(void*)*4 + 7, x_880);
return x_881;
}
else
{
uint8_t x_882; 
x_882 = lean_ctor_get_uint8(x_869, sizeof(void*)*4 + 6);
if (x_882 == 0)
{
lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; uint32_t x_891; uint16_t x_892; uint8_t x_893; lean_object* x_894; lean_object* x_895; uint32_t x_896; uint16_t x_897; uint8_t x_898; lean_object* x_899; uint32_t x_900; uint16_t x_901; uint8_t x_902; lean_object* x_903; 
x_883 = lean_ctor_get(x_796, 1);
lean_inc(x_883);
x_884 = lean_ctor_get(x_796, 2);
lean_inc(x_884);
if (lean_is_exclusive(x_796)) {
 lean_ctor_release(x_796, 0);
 lean_ctor_release(x_796, 1);
 lean_ctor_release(x_796, 2);
 lean_ctor_release(x_796, 3);
 x_885 = x_796;
} else {
 lean_dec_ref(x_796);
 x_885 = lean_box(0);
}
x_886 = lean_ctor_get(x_869, 0);
lean_inc(x_886);
x_887 = lean_ctor_get(x_869, 1);
lean_inc(x_887);
x_888 = lean_ctor_get(x_869, 2);
lean_inc(x_888);
x_889 = lean_ctor_get(x_869, 3);
lean_inc(x_889);
if (lean_is_exclusive(x_869)) {
 lean_ctor_release(x_869, 0);
 lean_ctor_release(x_869, 1);
 lean_ctor_release(x_869, 2);
 lean_ctor_release(x_869, 3);
 x_890 = x_869;
} else {
 lean_dec_ref(x_869);
 x_890 = lean_box(0);
}
x_891 = 0;
x_892 = 0;
x_893 = 0;
lean_inc(x_797);
if (lean_is_scalar(x_890)) {
 x_894 = lean_alloc_ctor(1, 4, 8);
} else {
 x_894 = x_890;
}
lean_ctor_set(x_894, 0, x_797);
lean_ctor_set(x_894, 1, x_883);
lean_ctor_set(x_894, 2, x_884);
lean_ctor_set(x_894, 3, x_886);
if (lean_is_exclusive(x_797)) {
 lean_ctor_release(x_797, 0);
 lean_ctor_release(x_797, 1);
 lean_ctor_release(x_797, 2);
 lean_ctor_release(x_797, 3);
 x_895 = x_797;
} else {
 lean_dec_ref(x_797);
 x_895 = lean_box(0);
}
lean_ctor_set_uint8(x_894, sizeof(void*)*4 + 6, x_846);
lean_ctor_set_uint32(x_894, sizeof(void*)*4, x_891);
lean_ctor_set_uint16(x_894, sizeof(void*)*4 + 4, x_892);
lean_ctor_set_uint8(x_894, sizeof(void*)*4 + 7, x_893);
x_896 = 0;
x_897 = 0;
x_898 = 0;
if (lean_is_scalar(x_895)) {
 x_899 = lean_alloc_ctor(1, 4, 8);
} else {
 x_899 = x_895;
}
lean_ctor_set(x_899, 0, x_889);
lean_ctor_set(x_899, 1, x_646);
lean_ctor_set(x_899, 2, x_647);
lean_ctor_set(x_899, 3, x_648);
lean_ctor_set_uint8(x_899, sizeof(void*)*4 + 6, x_846);
lean_ctor_set_uint32(x_899, sizeof(void*)*4, x_896);
lean_ctor_set_uint16(x_899, sizeof(void*)*4 + 4, x_897);
lean_ctor_set_uint8(x_899, sizeof(void*)*4 + 7, x_898);
x_900 = 0;
x_901 = 0;
x_902 = 0;
if (lean_is_scalar(x_885)) {
 x_903 = lean_alloc_ctor(1, 4, 8);
} else {
 x_903 = x_885;
}
lean_ctor_set(x_903, 0, x_894);
lean_ctor_set(x_903, 1, x_887);
lean_ctor_set(x_903, 2, x_888);
lean_ctor_set(x_903, 3, x_899);
lean_ctor_set_uint8(x_903, sizeof(void*)*4 + 6, x_882);
lean_ctor_set_uint32(x_903, sizeof(void*)*4, x_900);
lean_ctor_set_uint16(x_903, sizeof(void*)*4 + 4, x_901);
lean_ctor_set_uint8(x_903, sizeof(void*)*4 + 7, x_902);
return x_903;
}
else
{
lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; uint32_t x_912; uint16_t x_913; uint8_t x_914; lean_object* x_915; uint8_t x_916; uint32_t x_917; uint16_t x_918; uint8_t x_919; lean_object* x_920; uint32_t x_921; uint16_t x_922; uint8_t x_923; lean_object* x_924; 
x_904 = lean_ctor_get(x_796, 1);
lean_inc(x_904);
x_905 = lean_ctor_get(x_796, 2);
lean_inc(x_905);
if (lean_is_exclusive(x_796)) {
 lean_ctor_release(x_796, 0);
 lean_ctor_release(x_796, 1);
 lean_ctor_release(x_796, 2);
 lean_ctor_release(x_796, 3);
 x_906 = x_796;
} else {
 lean_dec_ref(x_796);
 x_906 = lean_box(0);
}
x_907 = lean_ctor_get(x_797, 0);
lean_inc(x_907);
x_908 = lean_ctor_get(x_797, 1);
lean_inc(x_908);
x_909 = lean_ctor_get(x_797, 2);
lean_inc(x_909);
x_910 = lean_ctor_get(x_797, 3);
lean_inc(x_910);
if (lean_is_exclusive(x_797)) {
 lean_ctor_release(x_797, 0);
 lean_ctor_release(x_797, 1);
 lean_ctor_release(x_797, 2);
 lean_ctor_release(x_797, 3);
 x_911 = x_797;
} else {
 lean_dec_ref(x_797);
 x_911 = lean_box(0);
}
x_912 = 0;
x_913 = 0;
x_914 = 0;
if (lean_is_scalar(x_911)) {
 x_915 = lean_alloc_ctor(1, 4, 8);
} else {
 x_915 = x_911;
}
lean_ctor_set(x_915, 0, x_907);
lean_ctor_set(x_915, 1, x_908);
lean_ctor_set(x_915, 2, x_909);
lean_ctor_set(x_915, 3, x_910);
lean_ctor_set_uint8(x_915, sizeof(void*)*4 + 6, x_882);
lean_ctor_set_uint32(x_915, sizeof(void*)*4, x_912);
lean_ctor_set_uint16(x_915, sizeof(void*)*4 + 4, x_913);
lean_ctor_set_uint8(x_915, sizeof(void*)*4 + 7, x_914);
x_916 = 0;
x_917 = 0;
x_918 = 0;
x_919 = 0;
if (lean_is_scalar(x_906)) {
 x_920 = lean_alloc_ctor(1, 4, 8);
} else {
 x_920 = x_906;
}
lean_ctor_set(x_920, 0, x_915);
lean_ctor_set(x_920, 1, x_904);
lean_ctor_set(x_920, 2, x_905);
lean_ctor_set(x_920, 3, x_869);
lean_ctor_set_uint8(x_920, sizeof(void*)*4 + 6, x_916);
lean_ctor_set_uint32(x_920, sizeof(void*)*4, x_917);
lean_ctor_set_uint16(x_920, sizeof(void*)*4 + 4, x_918);
lean_ctor_set_uint8(x_920, sizeof(void*)*4 + 7, x_919);
x_921 = 0;
x_922 = 0;
x_923 = 0;
x_924 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_924, 0, x_920);
lean_ctor_set(x_924, 1, x_646);
lean_ctor_set(x_924, 2, x_647);
lean_ctor_set(x_924, 3, x_648);
lean_ctor_set_uint8(x_924, sizeof(void*)*4 + 6, x_882);
lean_ctor_set_uint32(x_924, sizeof(void*)*4, x_921);
lean_ctor_set_uint16(x_924, sizeof(void*)*4 + 4, x_922);
lean_ctor_set_uint8(x_924, sizeof(void*)*4 + 7, x_923);
return x_924;
}
}
}
}
}
}
}
}
}
}
}
lean_object* l_RBNode_insert___at_Lean_IR_LocalContext_addLocal___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_RBNode_isRed___rarg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_1, x_2, x_3);
x_7 = l_RBNode_setBlack___rarg(x_6);
return x_7;
}
}
}
lean_object* l_Lean_IR_LocalContext_addLocal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = l_RBNode_insert___at_Lean_IR_LocalContext_addLocal___spec__1(x_1, x_2, x_5);
return x_6;
}
}
lean_object* l_Lean_IR_LocalContext_addJP(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = l_RBNode_insert___at_Lean_IR_LocalContext_addLocal___spec__1(x_1, x_2, x_5);
return x_6;
}
}
lean_object* l_Lean_IR_LocalContext_addParam(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = l_RBNode_insert___at_Lean_IR_LocalContext_addLocal___spec__1(x_1, x_3, x_5);
return x_6;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_LocalContext_addParams___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = l_Lean_IR_LocalContext_addParam(x_4, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
x_4 = x_8;
goto _start;
}
}
}
lean_object* l_Lean_IR_LocalContext_addParams(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_iterateMAux___main___at_Lean_IR_LocalContext_addParams___spec__1(x_2, x_2, x_3, x_1);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_LocalContext_addParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_Lean_IR_LocalContext_addParams___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_LocalContext_addParams___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_LocalContext_addParams(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_RBNode_find___main___at_Lean_IR_LocalContext_isJP___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_nat_dec_lt(x_2, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_5, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
else
{
x_1 = x_7;
goto _start;
}
}
else
{
x_1 = x_4;
goto _start;
}
}
}
}
uint8_t l_Lean_IR_LocalContext_isJP(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_find___main___at_Lean_IR_LocalContext_isJP___spec__1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 2)
{
uint8_t x_6; 
lean_dec(x_5);
x_6 = 1;
return x_6;
}
else
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
}
}
}
lean_object* l_RBNode_find___main___at_Lean_IR_LocalContext_isJP___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_find___main___at_Lean_IR_LocalContext_isJP___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_IR_LocalContext_isJP___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_LocalContext_isJP(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_IR_LocalContext_getJPBody(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_find___main___at_Lean_IR_LocalContext_isJP___spec__1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_6) == 2)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; 
lean_free_object(x_3);
lean_dec(x_6);
x_8 = lean_box(0);
return x_8;
}
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
if (lean_obj_tag(x_9) == 2)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_9);
x_12 = lean_box(0);
return x_12;
}
}
}
}
}
lean_object* l_Lean_IR_LocalContext_getJPBody___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_LocalContext_getJPBody(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_IR_LocalContext_getJPParams(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_find___main___at_Lean_IR_LocalContext_isJP___spec__1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_6) == 2)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; 
lean_free_object(x_3);
lean_dec(x_6);
x_8 = lean_box(0);
return x_8;
}
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
if (lean_obj_tag(x_9) == 2)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_9);
x_12 = lean_box(0);
return x_12;
}
}
}
}
}
lean_object* l_Lean_IR_LocalContext_getJPParams___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_LocalContext_getJPParams(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
uint8_t l_Lean_IR_LocalContext_isParam(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_find___main___at_Lean_IR_LocalContext_isJP___spec__1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
lean_dec(x_5);
x_6 = 1;
return x_6;
}
else
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
}
}
}
lean_object* l_Lean_IR_LocalContext_isParam___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_LocalContext_isParam(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_IR_LocalContext_isLocalVar(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_find___main___at_Lean_IR_LocalContext_isJP___spec__1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 1)
{
uint8_t x_6; 
lean_dec(x_5);
x_6 = 1;
return x_6;
}
else
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
}
}
}
lean_object* l_Lean_IR_LocalContext_isLocalVar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_LocalContext_isLocalVar(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_IR_LocalContext_contains(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_find___main___at_Lean_IR_LocalContext_isJP___spec__1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_3);
x_5 = 1;
return x_5;
}
}
}
lean_object* l_Lean_IR_LocalContext_contains___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_LocalContext_contains(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_RBNode_del___main___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get(x_2, 3);
x_8 = lean_nat_dec_lt(x_1, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_5, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
lean_free_object(x_2);
lean_dec(x_6);
lean_dec(x_5);
x_10 = l_RBNode_appendTrees___main___rarg(x_4, x_7);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = l_RBNode_isBlack___rarg(x_7);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; uint32_t x_14; uint16_t x_15; uint8_t x_16; 
x_12 = l_RBNode_del___main___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(x_1, x_7);
x_13 = 0;
x_14 = 0;
x_15 = 0;
x_16 = 0;
lean_ctor_set(x_2, 3, x_12);
lean_ctor_set_uint8(x_2, sizeof(void*)*4 + 6, x_13);
lean_ctor_set_uint32(x_2, sizeof(void*)*4, x_14);
lean_ctor_set_uint16(x_2, sizeof(void*)*4 + 4, x_15);
lean_ctor_set_uint8(x_2, sizeof(void*)*4 + 7, x_16);
return x_2;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_free_object(x_2);
x_17 = l_RBNode_del___main___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(x_1, x_7);
x_18 = l_RBNode_balRight___rarg(x_4, x_5, x_6, x_17);
return x_18;
}
}
}
else
{
uint8_t x_19; 
x_19 = l_RBNode_isBlack___rarg(x_4);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; uint32_t x_22; uint16_t x_23; uint8_t x_24; 
x_20 = l_RBNode_del___main___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(x_1, x_4);
x_21 = 0;
x_22 = 0;
x_23 = 0;
x_24 = 0;
lean_ctor_set(x_2, 0, x_20);
lean_ctor_set_uint8(x_2, sizeof(void*)*4 + 6, x_21);
lean_ctor_set_uint32(x_2, sizeof(void*)*4, x_22);
lean_ctor_set_uint16(x_2, sizeof(void*)*4 + 4, x_23);
lean_ctor_set_uint8(x_2, sizeof(void*)*4 + 7, x_24);
return x_2;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_free_object(x_2);
x_25 = l_RBNode_del___main___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(x_1, x_4);
x_26 = l_RBNode_balLeft___rarg(x_25, x_5, x_6, x_7);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_2, 0);
x_28 = lean_ctor_get(x_2, 1);
x_29 = lean_ctor_get(x_2, 2);
x_30 = lean_ctor_get(x_2, 3);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_2);
x_31 = lean_nat_dec_lt(x_1, x_28);
if (x_31 == 0)
{
uint8_t x_32; 
x_32 = lean_nat_dec_lt(x_28, x_1);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_29);
lean_dec(x_28);
x_33 = l_RBNode_appendTrees___main___rarg(x_27, x_30);
return x_33;
}
else
{
uint8_t x_34; 
x_34 = l_RBNode_isBlack___rarg(x_30);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; uint32_t x_37; uint16_t x_38; uint8_t x_39; lean_object* x_40; 
x_35 = l_RBNode_del___main___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(x_1, x_30);
x_36 = 0;
x_37 = 0;
x_38 = 0;
x_39 = 0;
x_40 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_40, 0, x_27);
lean_ctor_set(x_40, 1, x_28);
lean_ctor_set(x_40, 2, x_29);
lean_ctor_set(x_40, 3, x_35);
lean_ctor_set_uint8(x_40, sizeof(void*)*4 + 6, x_36);
lean_ctor_set_uint32(x_40, sizeof(void*)*4, x_37);
lean_ctor_set_uint16(x_40, sizeof(void*)*4 + 4, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*4 + 7, x_39);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = l_RBNode_del___main___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(x_1, x_30);
x_42 = l_RBNode_balRight___rarg(x_27, x_28, x_29, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
x_43 = l_RBNode_isBlack___rarg(x_27);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; uint32_t x_46; uint16_t x_47; uint8_t x_48; lean_object* x_49; 
x_44 = l_RBNode_del___main___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(x_1, x_27);
x_45 = 0;
x_46 = 0;
x_47 = 0;
x_48 = 0;
x_49 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_28);
lean_ctor_set(x_49, 2, x_29);
lean_ctor_set(x_49, 3, x_30);
lean_ctor_set_uint8(x_49, sizeof(void*)*4 + 6, x_45);
lean_ctor_set_uint32(x_49, sizeof(void*)*4, x_46);
lean_ctor_set_uint16(x_49, sizeof(void*)*4 + 4, x_47);
lean_ctor_set_uint8(x_49, sizeof(void*)*4 + 7, x_48);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = l_RBNode_del___main___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(x_1, x_27);
x_51 = l_RBNode_balLeft___rarg(x_50, x_28, x_29, x_30);
return x_51;
}
}
}
}
}
}
lean_object* l_RBNode_erase___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_RBNode_del___main___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(x_1, x_2);
x_4 = l_RBNode_setBlack___rarg(x_3);
return x_4;
}
}
lean_object* l_Lean_IR_LocalContext_eraseJoinPointDecl(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_erase___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__1(x_2, x_1);
return x_3;
}
}
lean_object* l_RBNode_del___main___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_del___main___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_RBNode_erase___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_erase___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_IR_LocalContext_eraseJoinPointDecl___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_LocalContext_eraseJoinPointDecl(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_IR_LocalContext_getType(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_find___main___at_Lean_IR_LocalContext_isJP___spec__1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_6) == 2)
{
lean_object* x_7; 
lean_free_object(x_3);
lean_dec(x_6);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
if (lean_obj_tag(x_9) == 2)
{
lean_object* x_10; 
lean_dec(x_9);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
}
lean_object* l_Lean_IR_LocalContext_getType___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_LocalContext_getType(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_IR_LocalContext_getValue(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_find___main___at_Lean_IR_LocalContext_isJP___spec__1(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; 
lean_free_object(x_3);
lean_dec(x_6);
x_8 = lean_box(0);
return x_8;
}
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_9);
x_12 = lean_box(0);
return x_12;
}
}
}
}
}
lean_object* l_Lean_IR_LocalContext_getValue___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_LocalContext_getValue(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_RBNode_find___main___at_Lean_IR_VarId_alphaEqv___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_nat_dec_lt(x_2, x_5);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_nat_dec_lt(x_5, x_2);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc(x_6);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_6);
return x_10;
}
else
{
x_1 = x_7;
goto _start;
}
}
else
{
x_1 = x_4;
goto _start;
}
}
}
}
uint8_t l_Lean_IR_VarId_alphaEqv(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_RBNode_find___main___at_Lean_IR_VarId_alphaEqv___spec__1(x_1, x_2);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = lean_nat_dec_eq(x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_nat_dec_eq(x_6, x_3);
lean_dec(x_6);
return x_7;
}
}
}
lean_object* l_RBNode_find___main___at_Lean_IR_VarId_alphaEqv___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_RBNode_find___main___at_Lean_IR_VarId_alphaEqv___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_IR_VarId_alphaEqv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_IR_VarId_alphaEqv(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* _init_l_Lean_IR_VarId_hasAeqv___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_VarId_alphaEqv___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_IR_VarId_hasAeqv() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_VarId_hasAeqv___closed__1;
return x_1;
}
}
uint8_t l_Lean_IR_Arg_alphaEqv(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Lean_IR_VarId_alphaEqv(x_1, x_4, x_5);
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_8; 
x_8 = 0;
return x_8;
}
else
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
}
}
}
lean_object* l_Lean_IR_Arg_alphaEqv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_IR_Arg_alphaEqv(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* _init_l_Lean_IR_Arg_hasAeqv___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_Arg_alphaEqv___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_IR_Arg_hasAeqv() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_Arg_hasAeqv___closed__1;
return x_1;
}
}
uint8_t l_Array_isEqvAux___main___at_Lean_IR_args_alphaEqv___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_5);
x_9 = lean_nat_dec_lt(x_7, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_7);
x_10 = 1;
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_array_fget(x_5, x_7);
x_12 = lean_array_fget(x_6, x_7);
x_13 = l_Lean_IR_Arg_alphaEqv(x_1, x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
if (x_13 == 0)
{
uint8_t x_14; 
lean_dec(x_7);
x_14 = 0;
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_7, x_15);
lean_dec(x_7);
x_4 = lean_box(0);
x_7 = x_16;
goto _start;
}
}
}
}
uint8_t l_Lean_IR_args_alphaEqv(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_array_get_size(x_3);
x_6 = lean_nat_dec_eq(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_isEqvAux___main___at_Lean_IR_args_alphaEqv___spec__1(x_1, x_2, x_3, lean_box(0), x_2, x_3, x_8);
return x_9;
}
}
}
lean_object* l_Array_isEqvAux___main___at_Lean_IR_args_alphaEqv___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_isEqvAux___main___at_Lean_IR_args_alphaEqv___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
lean_object* l_Lean_IR_args_alphaEqv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_IR_args_alphaEqv(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* _init_l_Lean_IR_args_hasAeqv___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_args_alphaEqv___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_IR_args_hasAeqv() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_args_hasAeqv___closed__1;
return x_1;
}
}
uint8_t l_Lean_IR_Expr_alphaEqv(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = l_Lean_IR_CtorInfo_beq(x_4, x_6);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = 0;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = l_Lean_IR_args_alphaEqv(x_1, x_5, x_7);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = 0;
return x_11;
}
}
case 1:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_nat_dec_eq(x_12, x_14);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = 0;
return x_17;
}
else
{
uint8_t x_18; 
x_18 = l_Lean_IR_VarId_alphaEqv(x_1, x_13, x_15);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = 0;
return x_19;
}
}
case 2:
{
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 6);
x_23 = lean_ctor_get(x_2, 2);
x_24 = lean_ctor_get(x_3, 0);
x_25 = lean_ctor_get(x_3, 1);
x_26 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 6);
x_27 = lean_ctor_get(x_3, 2);
x_28 = l_Lean_IR_VarId_alphaEqv(x_1, x_20, x_24);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = 0;
return x_29;
}
else
{
uint8_t x_30; 
x_30 = l_Lean_IR_CtorInfo_beq(x_21, x_25);
if (x_30 == 0)
{
uint8_t x_31; 
x_31 = 0;
return x_31;
}
else
{
if (x_22 == 0)
{
if (x_26 == 0)
{
uint8_t x_32; 
x_32 = l_Lean_IR_args_alphaEqv(x_1, x_23, x_27);
return x_32;
}
else
{
uint8_t x_33; 
x_33 = 0;
return x_33;
}
}
else
{
if (x_26 == 0)
{
uint8_t x_34; 
x_34 = 0;
return x_34;
}
else
{
uint8_t x_35; 
x_35 = l_Lean_IR_args_alphaEqv(x_1, x_23, x_27);
return x_35;
}
}
}
}
}
else
{
uint8_t x_36; 
x_36 = 0;
return x_36;
}
}
case 3:
{
if (lean_obj_tag(x_3) == 3)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_2, 0);
x_38 = lean_ctor_get(x_2, 1);
x_39 = lean_ctor_get(x_3, 0);
x_40 = lean_ctor_get(x_3, 1);
x_41 = lean_nat_dec_eq(x_37, x_39);
if (x_41 == 0)
{
uint8_t x_42; 
x_42 = 0;
return x_42;
}
else
{
uint8_t x_43; 
x_43 = l_Lean_IR_VarId_alphaEqv(x_1, x_38, x_40);
return x_43;
}
}
else
{
uint8_t x_44; 
x_44 = 0;
return x_44;
}
}
case 4:
{
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_2, 0);
x_46 = lean_ctor_get(x_2, 1);
x_47 = lean_ctor_get(x_3, 0);
x_48 = lean_ctor_get(x_3, 1);
x_49 = lean_nat_dec_eq(x_45, x_47);
if (x_49 == 0)
{
uint8_t x_50; 
x_50 = 0;
return x_50;
}
else
{
uint8_t x_51; 
x_51 = l_Lean_IR_VarId_alphaEqv(x_1, x_46, x_48);
return x_51;
}
}
else
{
uint8_t x_52; 
x_52 = 0;
return x_52;
}
}
case 5:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_53 = lean_ctor_get(x_2, 0);
x_54 = lean_ctor_get(x_2, 1);
x_55 = lean_ctor_get(x_2, 2);
x_56 = lean_ctor_get(x_3, 0);
x_57 = lean_ctor_get(x_3, 1);
x_58 = lean_ctor_get(x_3, 2);
x_59 = lean_nat_dec_eq(x_53, x_56);
if (x_59 == 0)
{
uint8_t x_60; 
x_60 = 0;
return x_60;
}
else
{
uint8_t x_61; 
x_61 = lean_nat_dec_eq(x_54, x_57);
if (x_61 == 0)
{
uint8_t x_62; 
x_62 = 0;
return x_62;
}
else
{
uint8_t x_63; 
x_63 = l_Lean_IR_VarId_alphaEqv(x_1, x_55, x_58);
return x_63;
}
}
}
else
{
uint8_t x_64; 
x_64 = 0;
return x_64;
}
}
case 6:
{
if (lean_obj_tag(x_3) == 6)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_65 = lean_ctor_get(x_2, 0);
x_66 = lean_ctor_get(x_2, 1);
x_67 = lean_ctor_get(x_3, 0);
x_68 = lean_ctor_get(x_3, 1);
x_69 = lean_name_eq(x_65, x_67);
if (x_69 == 0)
{
uint8_t x_70; 
x_70 = 0;
return x_70;
}
else
{
uint8_t x_71; 
x_71 = l_Lean_IR_args_alphaEqv(x_1, x_66, x_68);
return x_71;
}
}
else
{
uint8_t x_72; 
x_72 = 0;
return x_72;
}
}
case 7:
{
if (lean_obj_tag(x_3) == 7)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_73 = lean_ctor_get(x_2, 0);
x_74 = lean_ctor_get(x_3, 0);
x_75 = lean_ctor_get(x_3, 1);
x_76 = lean_name_eq(x_73, x_74);
if (x_76 == 0)
{
uint8_t x_77; 
x_77 = 0;
return x_77;
}
else
{
uint8_t x_78; 
x_78 = l_Lean_IR_args_alphaEqv(x_1, x_75, x_75);
return x_78;
}
}
else
{
uint8_t x_79; 
x_79 = 0;
return x_79;
}
}
case 8:
{
if (lean_obj_tag(x_3) == 8)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_80 = lean_ctor_get(x_2, 0);
x_81 = lean_ctor_get(x_2, 1);
x_82 = lean_ctor_get(x_3, 0);
x_83 = lean_ctor_get(x_3, 1);
x_84 = l_Lean_IR_VarId_alphaEqv(x_1, x_80, x_82);
if (x_84 == 0)
{
uint8_t x_85; 
x_85 = 0;
return x_85;
}
else
{
uint8_t x_86; 
x_86 = l_Lean_IR_args_alphaEqv(x_1, x_81, x_83);
return x_86;
}
}
else
{
uint8_t x_87; 
x_87 = 0;
return x_87;
}
}
case 9:
{
if (lean_obj_tag(x_3) == 9)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_88 = lean_ctor_get(x_2, 0);
x_89 = lean_ctor_get(x_2, 1);
x_90 = lean_ctor_get(x_3, 0);
x_91 = lean_ctor_get(x_3, 1);
x_92 = l_Lean_IR_IRType_beq___main(x_88, x_90);
if (x_92 == 0)
{
uint8_t x_93; 
x_93 = 0;
return x_93;
}
else
{
uint8_t x_94; 
x_94 = l_Lean_IR_VarId_alphaEqv(x_1, x_89, x_91);
return x_94;
}
}
else
{
uint8_t x_95; 
x_95 = 0;
return x_95;
}
}
case 10:
{
if (lean_obj_tag(x_3) == 10)
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_96 = lean_ctor_get(x_2, 0);
x_97 = lean_ctor_get(x_3, 0);
x_98 = l_Lean_IR_VarId_alphaEqv(x_1, x_96, x_97);
return x_98;
}
else
{
uint8_t x_99; 
x_99 = 0;
return x_99;
}
}
case 11:
{
if (lean_obj_tag(x_3) == 11)
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_100 = lean_ctor_get(x_2, 0);
x_101 = lean_ctor_get(x_3, 0);
x_102 = l_Lean_IR_LitVal_beq(x_100, x_101);
return x_102;
}
else
{
uint8_t x_103; 
x_103 = 0;
return x_103;
}
}
case 12:
{
if (lean_obj_tag(x_3) == 12)
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_104 = lean_ctor_get(x_2, 0);
x_105 = lean_ctor_get(x_3, 0);
x_106 = l_Lean_IR_VarId_alphaEqv(x_1, x_104, x_105);
return x_106;
}
else
{
uint8_t x_107; 
x_107 = 0;
return x_107;
}
}
default: 
{
if (lean_obj_tag(x_3) == 13)
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_108 = lean_ctor_get(x_2, 0);
x_109 = lean_ctor_get(x_3, 0);
x_110 = l_Lean_IR_VarId_alphaEqv(x_1, x_108, x_109);
return x_110;
}
else
{
uint8_t x_111; 
x_111 = 0;
return x_111;
}
}
}
}
}
lean_object* l_Lean_IR_Expr_alphaEqv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_IR_Expr_alphaEqv(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* _init_l_Lean_IR_Expr_hasAeqv___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_Expr_alphaEqv___boxed), 3, 0);
return x_1;
}
}
lean_object* _init_l_Lean_IR_Expr_hasAeqv() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_Expr_hasAeqv___closed__1;
return x_1;
}
}
lean_object* l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_4; uint32_t x_5; uint16_t x_6; uint8_t x_7; lean_object* x_8; 
x_4 = 0;
x_5 = 0;
x_6 = 0;
x_7 = 0;
x_8 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_2);
lean_ctor_set(x_8, 2, x_3);
lean_ctor_set(x_8, 3, x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*4 + 6, x_4);
lean_ctor_set_uint32(x_8, sizeof(void*)*4, x_5);
lean_ctor_set_uint16(x_8, sizeof(void*)*4 + 4, x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*4 + 7, x_7);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 6);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_1, 2);
x_14 = lean_ctor_get(x_1, 3);
x_15 = lean_nat_dec_lt(x_2, x_12);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = lean_nat_dec_lt(x_12, x_2);
if (x_16 == 0)
{
uint32_t x_17; uint16_t x_18; uint8_t x_19; 
lean_dec(x_13);
lean_dec(x_12);
x_17 = 0;
x_18 = 0;
x_19 = 0;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_17);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_18);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_19);
return x_1;
}
else
{
lean_object* x_20; uint32_t x_21; uint16_t x_22; uint8_t x_23; 
x_20 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_14, x_2, x_3);
x_21 = 0;
x_22 = 0;
x_23 = 0;
lean_ctor_set(x_1, 3, x_20);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_21);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_22);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_23);
return x_1;
}
}
else
{
lean_object* x_24; uint32_t x_25; uint16_t x_26; uint8_t x_27; 
x_24 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_11, x_2, x_3);
x_25 = 0;
x_26 = 0;
x_27 = 0;
lean_ctor_set(x_1, 0, x_24);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_25);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_26);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_27);
return x_1;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_1, 0);
x_29 = lean_ctor_get(x_1, 1);
x_30 = lean_ctor_get(x_1, 2);
x_31 = lean_ctor_get(x_1, 3);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_1);
x_32 = lean_nat_dec_lt(x_2, x_29);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = lean_nat_dec_lt(x_29, x_2);
if (x_33 == 0)
{
uint32_t x_34; uint16_t x_35; uint8_t x_36; lean_object* x_37; 
lean_dec(x_30);
lean_dec(x_29);
x_34 = 0;
x_35 = 0;
x_36 = 0;
x_37 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_37, 0, x_28);
lean_ctor_set(x_37, 1, x_2);
lean_ctor_set(x_37, 2, x_3);
lean_ctor_set(x_37, 3, x_31);
lean_ctor_set_uint8(x_37, sizeof(void*)*4 + 6, x_9);
lean_ctor_set_uint32(x_37, sizeof(void*)*4, x_34);
lean_ctor_set_uint16(x_37, sizeof(void*)*4 + 4, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*4 + 7, x_36);
return x_37;
}
else
{
lean_object* x_38; uint32_t x_39; uint16_t x_40; uint8_t x_41; lean_object* x_42; 
x_38 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_31, x_2, x_3);
x_39 = 0;
x_40 = 0;
x_41 = 0;
x_42 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_42, 0, x_28);
lean_ctor_set(x_42, 1, x_29);
lean_ctor_set(x_42, 2, x_30);
lean_ctor_set(x_42, 3, x_38);
lean_ctor_set_uint8(x_42, sizeof(void*)*4 + 6, x_9);
lean_ctor_set_uint32(x_42, sizeof(void*)*4, x_39);
lean_ctor_set_uint16(x_42, sizeof(void*)*4 + 4, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*4 + 7, x_41);
return x_42;
}
}
else
{
lean_object* x_43; uint32_t x_44; uint16_t x_45; uint8_t x_46; lean_object* x_47; 
x_43 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_28, x_2, x_3);
x_44 = 0;
x_45 = 0;
x_46 = 0;
x_47 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set(x_47, 1, x_29);
lean_ctor_set(x_47, 2, x_30);
lean_ctor_set(x_47, 3, x_31);
lean_ctor_set_uint8(x_47, sizeof(void*)*4 + 6, x_9);
lean_ctor_set_uint32(x_47, sizeof(void*)*4, x_44);
lean_ctor_set_uint16(x_47, sizeof(void*)*4 + 4, x_45);
lean_ctor_set_uint8(x_47, sizeof(void*)*4 + 7, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_1);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_1, 0);
x_50 = lean_ctor_get(x_1, 1);
x_51 = lean_ctor_get(x_1, 2);
x_52 = lean_ctor_get(x_1, 3);
x_53 = lean_nat_dec_lt(x_2, x_50);
if (x_53 == 0)
{
uint8_t x_54; 
x_54 = lean_nat_dec_lt(x_50, x_2);
if (x_54 == 0)
{
uint32_t x_55; uint16_t x_56; uint8_t x_57; 
lean_dec(x_51);
lean_dec(x_50);
x_55 = 0;
x_56 = 0;
x_57 = 0;
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_55);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_56);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_57);
return x_1;
}
else
{
uint8_t x_58; 
x_58 = l_RBNode_isRed___rarg(x_52);
if (x_58 == 0)
{
lean_object* x_59; uint32_t x_60; uint16_t x_61; uint8_t x_62; 
x_59 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_52, x_2, x_3);
x_60 = 0;
x_61 = 0;
x_62 = 0;
lean_ctor_set(x_1, 3, x_59);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_60);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_61);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_62);
return x_1;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_52, x_2, x_3);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_63, 3);
lean_inc(x_65);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_63);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; uint32_t x_70; uint16_t x_71; uint8_t x_72; uint8_t x_73; uint32_t x_74; uint16_t x_75; uint8_t x_76; 
x_67 = lean_ctor_get(x_63, 3);
lean_dec(x_67);
x_68 = lean_ctor_get(x_63, 0);
lean_dec(x_68);
x_69 = 0;
x_70 = 0;
x_71 = 0;
x_72 = 0;
lean_ctor_set(x_63, 0, x_65);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 6, x_69);
lean_ctor_set_uint32(x_63, sizeof(void*)*4, x_70);
lean_ctor_set_uint16(x_63, sizeof(void*)*4 + 4, x_71);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 7, x_72);
x_73 = 1;
x_74 = 0;
x_75 = 0;
x_76 = 0;
lean_ctor_set(x_1, 3, x_63);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_73);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_74);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_75);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_76);
return x_1;
}
else
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; uint32_t x_80; uint16_t x_81; uint8_t x_82; lean_object* x_83; uint8_t x_84; uint32_t x_85; uint16_t x_86; uint8_t x_87; 
x_77 = lean_ctor_get(x_63, 1);
x_78 = lean_ctor_get(x_63, 2);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_63);
x_79 = 0;
x_80 = 0;
x_81 = 0;
x_82 = 0;
x_83 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_83, 0, x_65);
lean_ctor_set(x_83, 1, x_77);
lean_ctor_set(x_83, 2, x_78);
lean_ctor_set(x_83, 3, x_65);
lean_ctor_set_uint8(x_83, sizeof(void*)*4 + 6, x_79);
lean_ctor_set_uint32(x_83, sizeof(void*)*4, x_80);
lean_ctor_set_uint16(x_83, sizeof(void*)*4 + 4, x_81);
lean_ctor_set_uint8(x_83, sizeof(void*)*4 + 7, x_82);
x_84 = 1;
x_85 = 0;
x_86 = 0;
x_87 = 0;
lean_ctor_set(x_1, 3, x_83);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_84);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_85);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_86);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_87);
return x_1;
}
}
else
{
uint8_t x_88; 
x_88 = lean_ctor_get_uint8(x_65, sizeof(void*)*4 + 6);
if (x_88 == 0)
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_63);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_90 = lean_ctor_get(x_63, 1);
x_91 = lean_ctor_get(x_63, 2);
x_92 = lean_ctor_get(x_63, 3);
lean_dec(x_92);
x_93 = lean_ctor_get(x_63, 0);
lean_dec(x_93);
x_94 = !lean_is_exclusive(x_65);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; uint32_t x_100; uint16_t x_101; uint8_t x_102; uint32_t x_103; uint16_t x_104; uint8_t x_105; uint32_t x_106; uint16_t x_107; uint8_t x_108; 
x_95 = lean_ctor_get(x_65, 0);
x_96 = lean_ctor_get(x_65, 1);
x_97 = lean_ctor_get(x_65, 2);
x_98 = lean_ctor_get(x_65, 3);
x_99 = 1;
x_100 = 0;
x_101 = 0;
x_102 = 0;
lean_ctor_set(x_65, 3, x_64);
lean_ctor_set(x_65, 2, x_51);
lean_ctor_set(x_65, 1, x_50);
lean_ctor_set(x_65, 0, x_49);
lean_ctor_set_uint8(x_65, sizeof(void*)*4 + 6, x_99);
lean_ctor_set_uint32(x_65, sizeof(void*)*4, x_100);
lean_ctor_set_uint16(x_65, sizeof(void*)*4 + 4, x_101);
lean_ctor_set_uint8(x_65, sizeof(void*)*4 + 7, x_102);
x_103 = 0;
x_104 = 0;
x_105 = 0;
lean_ctor_set(x_63, 3, x_98);
lean_ctor_set(x_63, 2, x_97);
lean_ctor_set(x_63, 1, x_96);
lean_ctor_set(x_63, 0, x_95);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 6, x_99);
lean_ctor_set_uint32(x_63, sizeof(void*)*4, x_103);
lean_ctor_set_uint16(x_63, sizeof(void*)*4 + 4, x_104);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 7, x_105);
x_106 = 0;
x_107 = 0;
x_108 = 0;
lean_ctor_set(x_1, 3, x_63);
lean_ctor_set(x_1, 2, x_91);
lean_ctor_set(x_1, 1, x_90);
lean_ctor_set(x_1, 0, x_65);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_88);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_106);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_107);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_108);
return x_1;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; uint32_t x_114; uint16_t x_115; uint8_t x_116; lean_object* x_117; uint32_t x_118; uint16_t x_119; uint8_t x_120; uint32_t x_121; uint16_t x_122; uint8_t x_123; 
x_109 = lean_ctor_get(x_65, 0);
x_110 = lean_ctor_get(x_65, 1);
x_111 = lean_ctor_get(x_65, 2);
x_112 = lean_ctor_get(x_65, 3);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_65);
x_113 = 1;
x_114 = 0;
x_115 = 0;
x_116 = 0;
x_117 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_117, 0, x_49);
lean_ctor_set(x_117, 1, x_50);
lean_ctor_set(x_117, 2, x_51);
lean_ctor_set(x_117, 3, x_64);
lean_ctor_set_uint8(x_117, sizeof(void*)*4 + 6, x_113);
lean_ctor_set_uint32(x_117, sizeof(void*)*4, x_114);
lean_ctor_set_uint16(x_117, sizeof(void*)*4 + 4, x_115);
lean_ctor_set_uint8(x_117, sizeof(void*)*4 + 7, x_116);
x_118 = 0;
x_119 = 0;
x_120 = 0;
lean_ctor_set(x_63, 3, x_112);
lean_ctor_set(x_63, 2, x_111);
lean_ctor_set(x_63, 1, x_110);
lean_ctor_set(x_63, 0, x_109);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 6, x_113);
lean_ctor_set_uint32(x_63, sizeof(void*)*4, x_118);
lean_ctor_set_uint16(x_63, sizeof(void*)*4 + 4, x_119);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 7, x_120);
x_121 = 0;
x_122 = 0;
x_123 = 0;
lean_ctor_set(x_1, 3, x_63);
lean_ctor_set(x_1, 2, x_91);
lean_ctor_set(x_1, 1, x_90);
lean_ctor_set(x_1, 0, x_117);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_88);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_121);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_122);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_123);
return x_1;
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; uint32_t x_132; uint16_t x_133; uint8_t x_134; lean_object* x_135; uint32_t x_136; uint16_t x_137; uint8_t x_138; lean_object* x_139; uint32_t x_140; uint16_t x_141; uint8_t x_142; 
x_124 = lean_ctor_get(x_63, 1);
x_125 = lean_ctor_get(x_63, 2);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_63);
x_126 = lean_ctor_get(x_65, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_65, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_65, 2);
lean_inc(x_128);
x_129 = lean_ctor_get(x_65, 3);
lean_inc(x_129);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 lean_ctor_release(x_65, 2);
 lean_ctor_release(x_65, 3);
 x_130 = x_65;
} else {
 lean_dec_ref(x_65);
 x_130 = lean_box(0);
}
x_131 = 1;
x_132 = 0;
x_133 = 0;
x_134 = 0;
if (lean_is_scalar(x_130)) {
 x_135 = lean_alloc_ctor(1, 4, 8);
} else {
 x_135 = x_130;
}
lean_ctor_set(x_135, 0, x_49);
lean_ctor_set(x_135, 1, x_50);
lean_ctor_set(x_135, 2, x_51);
lean_ctor_set(x_135, 3, x_64);
lean_ctor_set_uint8(x_135, sizeof(void*)*4 + 6, x_131);
lean_ctor_set_uint32(x_135, sizeof(void*)*4, x_132);
lean_ctor_set_uint16(x_135, sizeof(void*)*4 + 4, x_133);
lean_ctor_set_uint8(x_135, sizeof(void*)*4 + 7, x_134);
x_136 = 0;
x_137 = 0;
x_138 = 0;
x_139 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_139, 0, x_126);
lean_ctor_set(x_139, 1, x_127);
lean_ctor_set(x_139, 2, x_128);
lean_ctor_set(x_139, 3, x_129);
lean_ctor_set_uint8(x_139, sizeof(void*)*4 + 6, x_131);
lean_ctor_set_uint32(x_139, sizeof(void*)*4, x_136);
lean_ctor_set_uint16(x_139, sizeof(void*)*4 + 4, x_137);
lean_ctor_set_uint8(x_139, sizeof(void*)*4 + 7, x_138);
x_140 = 0;
x_141 = 0;
x_142 = 0;
lean_ctor_set(x_1, 3, x_139);
lean_ctor_set(x_1, 2, x_125);
lean_ctor_set(x_1, 1, x_124);
lean_ctor_set(x_1, 0, x_135);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_88);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_140);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_141);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_142);
return x_1;
}
}
else
{
uint8_t x_143; 
x_143 = !lean_is_exclusive(x_63);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; uint8_t x_146; uint32_t x_147; uint16_t x_148; uint8_t x_149; uint32_t x_150; uint16_t x_151; uint8_t x_152; 
x_144 = lean_ctor_get(x_63, 3);
lean_dec(x_144);
x_145 = lean_ctor_get(x_63, 0);
lean_dec(x_145);
x_146 = 0;
x_147 = 0;
x_148 = 0;
x_149 = 0;
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 6, x_146);
lean_ctor_set_uint32(x_63, sizeof(void*)*4, x_147);
lean_ctor_set_uint16(x_63, sizeof(void*)*4 + 4, x_148);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 7, x_149);
x_150 = 0;
x_151 = 0;
x_152 = 0;
lean_ctor_set(x_1, 3, x_63);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_88);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_150);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_151);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_152);
return x_1;
}
else
{
lean_object* x_153; lean_object* x_154; uint8_t x_155; uint32_t x_156; uint16_t x_157; uint8_t x_158; lean_object* x_159; uint32_t x_160; uint16_t x_161; uint8_t x_162; 
x_153 = lean_ctor_get(x_63, 1);
x_154 = lean_ctor_get(x_63, 2);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_63);
x_155 = 0;
x_156 = 0;
x_157 = 0;
x_158 = 0;
x_159 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_159, 0, x_64);
lean_ctor_set(x_159, 1, x_153);
lean_ctor_set(x_159, 2, x_154);
lean_ctor_set(x_159, 3, x_65);
lean_ctor_set_uint8(x_159, sizeof(void*)*4 + 6, x_155);
lean_ctor_set_uint32(x_159, sizeof(void*)*4, x_156);
lean_ctor_set_uint16(x_159, sizeof(void*)*4 + 4, x_157);
lean_ctor_set_uint8(x_159, sizeof(void*)*4 + 7, x_158);
x_160 = 0;
x_161 = 0;
x_162 = 0;
lean_ctor_set(x_1, 3, x_159);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_88);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_160);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_161);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_162);
return x_1;
}
}
}
}
else
{
uint8_t x_163; 
x_163 = lean_ctor_get_uint8(x_64, sizeof(void*)*4 + 6);
if (x_163 == 0)
{
uint8_t x_164; 
x_164 = !lean_is_exclusive(x_63);
if (x_164 == 0)
{
lean_object* x_165; uint8_t x_166; 
x_165 = lean_ctor_get(x_63, 0);
lean_dec(x_165);
x_166 = !lean_is_exclusive(x_64);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; uint32_t x_172; uint16_t x_173; uint8_t x_174; uint32_t x_175; uint16_t x_176; uint8_t x_177; uint32_t x_178; uint16_t x_179; uint8_t x_180; 
x_167 = lean_ctor_get(x_64, 0);
x_168 = lean_ctor_get(x_64, 1);
x_169 = lean_ctor_get(x_64, 2);
x_170 = lean_ctor_get(x_64, 3);
x_171 = 1;
x_172 = 0;
x_173 = 0;
x_174 = 0;
lean_ctor_set(x_64, 3, x_167);
lean_ctor_set(x_64, 2, x_51);
lean_ctor_set(x_64, 1, x_50);
lean_ctor_set(x_64, 0, x_49);
lean_ctor_set_uint8(x_64, sizeof(void*)*4 + 6, x_171);
lean_ctor_set_uint32(x_64, sizeof(void*)*4, x_172);
lean_ctor_set_uint16(x_64, sizeof(void*)*4 + 4, x_173);
lean_ctor_set_uint8(x_64, sizeof(void*)*4 + 7, x_174);
x_175 = 0;
x_176 = 0;
x_177 = 0;
lean_ctor_set(x_63, 0, x_170);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 6, x_171);
lean_ctor_set_uint32(x_63, sizeof(void*)*4, x_175);
lean_ctor_set_uint16(x_63, sizeof(void*)*4 + 4, x_176);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 7, x_177);
x_178 = 0;
x_179 = 0;
x_180 = 0;
lean_ctor_set(x_1, 3, x_63);
lean_ctor_set(x_1, 2, x_169);
lean_ctor_set(x_1, 1, x_168);
lean_ctor_set(x_1, 0, x_64);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_163);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_178);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_179);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_180);
return x_1;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; uint32_t x_186; uint16_t x_187; uint8_t x_188; lean_object* x_189; uint32_t x_190; uint16_t x_191; uint8_t x_192; uint32_t x_193; uint16_t x_194; uint8_t x_195; 
x_181 = lean_ctor_get(x_64, 0);
x_182 = lean_ctor_get(x_64, 1);
x_183 = lean_ctor_get(x_64, 2);
x_184 = lean_ctor_get(x_64, 3);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_64);
x_185 = 1;
x_186 = 0;
x_187 = 0;
x_188 = 0;
x_189 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_189, 0, x_49);
lean_ctor_set(x_189, 1, x_50);
lean_ctor_set(x_189, 2, x_51);
lean_ctor_set(x_189, 3, x_181);
lean_ctor_set_uint8(x_189, sizeof(void*)*4 + 6, x_185);
lean_ctor_set_uint32(x_189, sizeof(void*)*4, x_186);
lean_ctor_set_uint16(x_189, sizeof(void*)*4 + 4, x_187);
lean_ctor_set_uint8(x_189, sizeof(void*)*4 + 7, x_188);
x_190 = 0;
x_191 = 0;
x_192 = 0;
lean_ctor_set(x_63, 0, x_184);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 6, x_185);
lean_ctor_set_uint32(x_63, sizeof(void*)*4, x_190);
lean_ctor_set_uint16(x_63, sizeof(void*)*4 + 4, x_191);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 7, x_192);
x_193 = 0;
x_194 = 0;
x_195 = 0;
lean_ctor_set(x_1, 3, x_63);
lean_ctor_set(x_1, 2, x_183);
lean_ctor_set(x_1, 1, x_182);
lean_ctor_set(x_1, 0, x_189);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_163);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_193);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_194);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_195);
return x_1;
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; uint32_t x_205; uint16_t x_206; uint8_t x_207; lean_object* x_208; uint32_t x_209; uint16_t x_210; uint8_t x_211; lean_object* x_212; uint32_t x_213; uint16_t x_214; uint8_t x_215; 
x_196 = lean_ctor_get(x_63, 1);
x_197 = lean_ctor_get(x_63, 2);
x_198 = lean_ctor_get(x_63, 3);
lean_inc(x_198);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_63);
x_199 = lean_ctor_get(x_64, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_64, 1);
lean_inc(x_200);
x_201 = lean_ctor_get(x_64, 2);
lean_inc(x_201);
x_202 = lean_ctor_get(x_64, 3);
lean_inc(x_202);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 lean_ctor_release(x_64, 2);
 lean_ctor_release(x_64, 3);
 x_203 = x_64;
} else {
 lean_dec_ref(x_64);
 x_203 = lean_box(0);
}
x_204 = 1;
x_205 = 0;
x_206 = 0;
x_207 = 0;
if (lean_is_scalar(x_203)) {
 x_208 = lean_alloc_ctor(1, 4, 8);
} else {
 x_208 = x_203;
}
lean_ctor_set(x_208, 0, x_49);
lean_ctor_set(x_208, 1, x_50);
lean_ctor_set(x_208, 2, x_51);
lean_ctor_set(x_208, 3, x_199);
lean_ctor_set_uint8(x_208, sizeof(void*)*4 + 6, x_204);
lean_ctor_set_uint32(x_208, sizeof(void*)*4, x_205);
lean_ctor_set_uint16(x_208, sizeof(void*)*4 + 4, x_206);
lean_ctor_set_uint8(x_208, sizeof(void*)*4 + 7, x_207);
x_209 = 0;
x_210 = 0;
x_211 = 0;
x_212 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_212, 0, x_202);
lean_ctor_set(x_212, 1, x_196);
lean_ctor_set(x_212, 2, x_197);
lean_ctor_set(x_212, 3, x_198);
lean_ctor_set_uint8(x_212, sizeof(void*)*4 + 6, x_204);
lean_ctor_set_uint32(x_212, sizeof(void*)*4, x_209);
lean_ctor_set_uint16(x_212, sizeof(void*)*4 + 4, x_210);
lean_ctor_set_uint8(x_212, sizeof(void*)*4 + 7, x_211);
x_213 = 0;
x_214 = 0;
x_215 = 0;
lean_ctor_set(x_1, 3, x_212);
lean_ctor_set(x_1, 2, x_201);
lean_ctor_set(x_1, 1, x_200);
lean_ctor_set(x_1, 0, x_208);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_163);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_213);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_214);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_215);
return x_1;
}
}
else
{
lean_object* x_216; 
x_216 = lean_ctor_get(x_63, 3);
lean_inc(x_216);
if (lean_obj_tag(x_216) == 0)
{
uint8_t x_217; 
x_217 = !lean_is_exclusive(x_63);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; uint8_t x_220; uint32_t x_221; uint16_t x_222; uint8_t x_223; uint32_t x_224; uint16_t x_225; uint8_t x_226; 
x_218 = lean_ctor_get(x_63, 3);
lean_dec(x_218);
x_219 = lean_ctor_get(x_63, 0);
lean_dec(x_219);
x_220 = 0;
x_221 = 0;
x_222 = 0;
x_223 = 0;
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 6, x_220);
lean_ctor_set_uint32(x_63, sizeof(void*)*4, x_221);
lean_ctor_set_uint16(x_63, sizeof(void*)*4 + 4, x_222);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 7, x_223);
x_224 = 0;
x_225 = 0;
x_226 = 0;
lean_ctor_set(x_1, 3, x_63);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_163);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_224);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_225);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_226);
return x_1;
}
else
{
lean_object* x_227; lean_object* x_228; uint8_t x_229; uint32_t x_230; uint16_t x_231; uint8_t x_232; lean_object* x_233; uint32_t x_234; uint16_t x_235; uint8_t x_236; 
x_227 = lean_ctor_get(x_63, 1);
x_228 = lean_ctor_get(x_63, 2);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_63);
x_229 = 0;
x_230 = 0;
x_231 = 0;
x_232 = 0;
x_233 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_233, 0, x_64);
lean_ctor_set(x_233, 1, x_227);
lean_ctor_set(x_233, 2, x_228);
lean_ctor_set(x_233, 3, x_216);
lean_ctor_set_uint8(x_233, sizeof(void*)*4 + 6, x_229);
lean_ctor_set_uint32(x_233, sizeof(void*)*4, x_230);
lean_ctor_set_uint16(x_233, sizeof(void*)*4 + 4, x_231);
lean_ctor_set_uint8(x_233, sizeof(void*)*4 + 7, x_232);
x_234 = 0;
x_235 = 0;
x_236 = 0;
lean_ctor_set(x_1, 3, x_233);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_163);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_234);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_235);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_236);
return x_1;
}
}
else
{
uint8_t x_237; 
x_237 = lean_ctor_get_uint8(x_216, sizeof(void*)*4 + 6);
if (x_237 == 0)
{
uint8_t x_238; 
lean_free_object(x_1);
x_238 = !lean_is_exclusive(x_63);
if (x_238 == 0)
{
lean_object* x_239; lean_object* x_240; uint8_t x_241; 
x_239 = lean_ctor_get(x_63, 3);
lean_dec(x_239);
x_240 = lean_ctor_get(x_63, 0);
lean_dec(x_240);
x_241 = !lean_is_exclusive(x_216);
if (x_241 == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint32_t x_246; uint16_t x_247; uint8_t x_248; uint8_t x_249; 
x_242 = lean_ctor_get(x_216, 0);
x_243 = lean_ctor_get(x_216, 1);
x_244 = lean_ctor_get(x_216, 2);
x_245 = lean_ctor_get(x_216, 3);
x_246 = 0;
x_247 = 0;
x_248 = 0;
lean_inc(x_64);
lean_ctor_set(x_216, 3, x_64);
lean_ctor_set(x_216, 2, x_51);
lean_ctor_set(x_216, 1, x_50);
lean_ctor_set(x_216, 0, x_49);
x_249 = !lean_is_exclusive(x_64);
if (x_249 == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; uint32_t x_254; uint16_t x_255; uint8_t x_256; uint32_t x_257; uint16_t x_258; uint8_t x_259; 
x_250 = lean_ctor_get(x_64, 3);
lean_dec(x_250);
x_251 = lean_ctor_get(x_64, 2);
lean_dec(x_251);
x_252 = lean_ctor_get(x_64, 1);
lean_dec(x_252);
x_253 = lean_ctor_get(x_64, 0);
lean_dec(x_253);
lean_ctor_set_uint8(x_216, sizeof(void*)*4 + 6, x_163);
lean_ctor_set_uint32(x_216, sizeof(void*)*4, x_246);
lean_ctor_set_uint16(x_216, sizeof(void*)*4 + 4, x_247);
lean_ctor_set_uint8(x_216, sizeof(void*)*4 + 7, x_248);
x_254 = 0;
x_255 = 0;
x_256 = 0;
lean_ctor_set(x_64, 3, x_245);
lean_ctor_set(x_64, 2, x_244);
lean_ctor_set(x_64, 1, x_243);
lean_ctor_set(x_64, 0, x_242);
lean_ctor_set_uint32(x_64, sizeof(void*)*4, x_254);
lean_ctor_set_uint16(x_64, sizeof(void*)*4 + 4, x_255);
lean_ctor_set_uint8(x_64, sizeof(void*)*4 + 7, x_256);
x_257 = 0;
x_258 = 0;
x_259 = 0;
lean_ctor_set(x_63, 3, x_64);
lean_ctor_set(x_63, 0, x_216);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 6, x_237);
lean_ctor_set_uint32(x_63, sizeof(void*)*4, x_257);
lean_ctor_set_uint16(x_63, sizeof(void*)*4 + 4, x_258);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 7, x_259);
return x_63;
}
else
{
uint32_t x_260; uint16_t x_261; uint8_t x_262; lean_object* x_263; uint32_t x_264; uint16_t x_265; uint8_t x_266; 
lean_dec(x_64);
lean_ctor_set_uint8(x_216, sizeof(void*)*4 + 6, x_163);
lean_ctor_set_uint32(x_216, sizeof(void*)*4, x_246);
lean_ctor_set_uint16(x_216, sizeof(void*)*4 + 4, x_247);
lean_ctor_set_uint8(x_216, sizeof(void*)*4 + 7, x_248);
x_260 = 0;
x_261 = 0;
x_262 = 0;
x_263 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_263, 0, x_242);
lean_ctor_set(x_263, 1, x_243);
lean_ctor_set(x_263, 2, x_244);
lean_ctor_set(x_263, 3, x_245);
lean_ctor_set_uint8(x_263, sizeof(void*)*4 + 6, x_163);
lean_ctor_set_uint32(x_263, sizeof(void*)*4, x_260);
lean_ctor_set_uint16(x_263, sizeof(void*)*4 + 4, x_261);
lean_ctor_set_uint8(x_263, sizeof(void*)*4 + 7, x_262);
x_264 = 0;
x_265 = 0;
x_266 = 0;
lean_ctor_set(x_63, 3, x_263);
lean_ctor_set(x_63, 0, x_216);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 6, x_237);
lean_ctor_set_uint32(x_63, sizeof(void*)*4, x_264);
lean_ctor_set_uint16(x_63, sizeof(void*)*4 + 4, x_265);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 7, x_266);
return x_63;
}
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; uint32_t x_271; uint16_t x_272; uint8_t x_273; lean_object* x_274; lean_object* x_275; uint32_t x_276; uint16_t x_277; uint8_t x_278; lean_object* x_279; uint32_t x_280; uint16_t x_281; uint8_t x_282; 
x_267 = lean_ctor_get(x_216, 0);
x_268 = lean_ctor_get(x_216, 1);
x_269 = lean_ctor_get(x_216, 2);
x_270 = lean_ctor_get(x_216, 3);
lean_inc(x_270);
lean_inc(x_269);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_216);
x_271 = 0;
x_272 = 0;
x_273 = 0;
lean_inc(x_64);
x_274 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_274, 0, x_49);
lean_ctor_set(x_274, 1, x_50);
lean_ctor_set(x_274, 2, x_51);
lean_ctor_set(x_274, 3, x_64);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 lean_ctor_release(x_64, 2);
 lean_ctor_release(x_64, 3);
 x_275 = x_64;
} else {
 lean_dec_ref(x_64);
 x_275 = lean_box(0);
}
lean_ctor_set_uint8(x_274, sizeof(void*)*4 + 6, x_163);
lean_ctor_set_uint32(x_274, sizeof(void*)*4, x_271);
lean_ctor_set_uint16(x_274, sizeof(void*)*4 + 4, x_272);
lean_ctor_set_uint8(x_274, sizeof(void*)*4 + 7, x_273);
x_276 = 0;
x_277 = 0;
x_278 = 0;
if (lean_is_scalar(x_275)) {
 x_279 = lean_alloc_ctor(1, 4, 8);
} else {
 x_279 = x_275;
}
lean_ctor_set(x_279, 0, x_267);
lean_ctor_set(x_279, 1, x_268);
lean_ctor_set(x_279, 2, x_269);
lean_ctor_set(x_279, 3, x_270);
lean_ctor_set_uint8(x_279, sizeof(void*)*4 + 6, x_163);
lean_ctor_set_uint32(x_279, sizeof(void*)*4, x_276);
lean_ctor_set_uint16(x_279, sizeof(void*)*4 + 4, x_277);
lean_ctor_set_uint8(x_279, sizeof(void*)*4 + 7, x_278);
x_280 = 0;
x_281 = 0;
x_282 = 0;
lean_ctor_set(x_63, 3, x_279);
lean_ctor_set(x_63, 0, x_274);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 6, x_237);
lean_ctor_set_uint32(x_63, sizeof(void*)*4, x_280);
lean_ctor_set_uint16(x_63, sizeof(void*)*4 + 4, x_281);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 7, x_282);
return x_63;
}
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; uint32_t x_290; uint16_t x_291; uint8_t x_292; lean_object* x_293; lean_object* x_294; uint32_t x_295; uint16_t x_296; uint8_t x_297; lean_object* x_298; uint32_t x_299; uint16_t x_300; uint8_t x_301; lean_object* x_302; 
x_283 = lean_ctor_get(x_63, 1);
x_284 = lean_ctor_get(x_63, 2);
lean_inc(x_284);
lean_inc(x_283);
lean_dec(x_63);
x_285 = lean_ctor_get(x_216, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_216, 1);
lean_inc(x_286);
x_287 = lean_ctor_get(x_216, 2);
lean_inc(x_287);
x_288 = lean_ctor_get(x_216, 3);
lean_inc(x_288);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 lean_ctor_release(x_216, 1);
 lean_ctor_release(x_216, 2);
 lean_ctor_release(x_216, 3);
 x_289 = x_216;
} else {
 lean_dec_ref(x_216);
 x_289 = lean_box(0);
}
x_290 = 0;
x_291 = 0;
x_292 = 0;
lean_inc(x_64);
if (lean_is_scalar(x_289)) {
 x_293 = lean_alloc_ctor(1, 4, 8);
} else {
 x_293 = x_289;
}
lean_ctor_set(x_293, 0, x_49);
lean_ctor_set(x_293, 1, x_50);
lean_ctor_set(x_293, 2, x_51);
lean_ctor_set(x_293, 3, x_64);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 lean_ctor_release(x_64, 2);
 lean_ctor_release(x_64, 3);
 x_294 = x_64;
} else {
 lean_dec_ref(x_64);
 x_294 = lean_box(0);
}
lean_ctor_set_uint8(x_293, sizeof(void*)*4 + 6, x_163);
lean_ctor_set_uint32(x_293, sizeof(void*)*4, x_290);
lean_ctor_set_uint16(x_293, sizeof(void*)*4 + 4, x_291);
lean_ctor_set_uint8(x_293, sizeof(void*)*4 + 7, x_292);
x_295 = 0;
x_296 = 0;
x_297 = 0;
if (lean_is_scalar(x_294)) {
 x_298 = lean_alloc_ctor(1, 4, 8);
} else {
 x_298 = x_294;
}
lean_ctor_set(x_298, 0, x_285);
lean_ctor_set(x_298, 1, x_286);
lean_ctor_set(x_298, 2, x_287);
lean_ctor_set(x_298, 3, x_288);
lean_ctor_set_uint8(x_298, sizeof(void*)*4 + 6, x_163);
lean_ctor_set_uint32(x_298, sizeof(void*)*4, x_295);
lean_ctor_set_uint16(x_298, sizeof(void*)*4 + 4, x_296);
lean_ctor_set_uint8(x_298, sizeof(void*)*4 + 7, x_297);
x_299 = 0;
x_300 = 0;
x_301 = 0;
x_302 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_302, 0, x_293);
lean_ctor_set(x_302, 1, x_283);
lean_ctor_set(x_302, 2, x_284);
lean_ctor_set(x_302, 3, x_298);
lean_ctor_set_uint8(x_302, sizeof(void*)*4 + 6, x_237);
lean_ctor_set_uint32(x_302, sizeof(void*)*4, x_299);
lean_ctor_set_uint16(x_302, sizeof(void*)*4 + 4, x_300);
lean_ctor_set_uint8(x_302, sizeof(void*)*4 + 7, x_301);
return x_302;
}
}
else
{
uint8_t x_303; 
x_303 = !lean_is_exclusive(x_63);
if (x_303 == 0)
{
lean_object* x_304; lean_object* x_305; uint8_t x_306; 
x_304 = lean_ctor_get(x_63, 3);
lean_dec(x_304);
x_305 = lean_ctor_get(x_63, 0);
lean_dec(x_305);
x_306 = !lean_is_exclusive(x_64);
if (x_306 == 0)
{
uint32_t x_307; uint16_t x_308; uint8_t x_309; uint8_t x_310; uint32_t x_311; uint16_t x_312; uint8_t x_313; uint32_t x_314; uint16_t x_315; uint8_t x_316; 
x_307 = 0;
x_308 = 0;
x_309 = 0;
lean_ctor_set_uint8(x_64, sizeof(void*)*4 + 6, x_237);
lean_ctor_set_uint32(x_64, sizeof(void*)*4, x_307);
lean_ctor_set_uint16(x_64, sizeof(void*)*4 + 4, x_308);
lean_ctor_set_uint8(x_64, sizeof(void*)*4 + 7, x_309);
x_310 = 0;
x_311 = 0;
x_312 = 0;
x_313 = 0;
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 6, x_310);
lean_ctor_set_uint32(x_63, sizeof(void*)*4, x_311);
lean_ctor_set_uint16(x_63, sizeof(void*)*4 + 4, x_312);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 7, x_313);
x_314 = 0;
x_315 = 0;
x_316 = 0;
lean_ctor_set(x_1, 3, x_63);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_237);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_314);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_315);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_316);
return x_1;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; uint32_t x_321; uint16_t x_322; uint8_t x_323; lean_object* x_324; uint8_t x_325; uint32_t x_326; uint16_t x_327; uint8_t x_328; uint32_t x_329; uint16_t x_330; uint8_t x_331; 
x_317 = lean_ctor_get(x_64, 0);
x_318 = lean_ctor_get(x_64, 1);
x_319 = lean_ctor_get(x_64, 2);
x_320 = lean_ctor_get(x_64, 3);
lean_inc(x_320);
lean_inc(x_319);
lean_inc(x_318);
lean_inc(x_317);
lean_dec(x_64);
x_321 = 0;
x_322 = 0;
x_323 = 0;
x_324 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_324, 0, x_317);
lean_ctor_set(x_324, 1, x_318);
lean_ctor_set(x_324, 2, x_319);
lean_ctor_set(x_324, 3, x_320);
lean_ctor_set_uint8(x_324, sizeof(void*)*4 + 6, x_237);
lean_ctor_set_uint32(x_324, sizeof(void*)*4, x_321);
lean_ctor_set_uint16(x_324, sizeof(void*)*4 + 4, x_322);
lean_ctor_set_uint8(x_324, sizeof(void*)*4 + 7, x_323);
x_325 = 0;
x_326 = 0;
x_327 = 0;
x_328 = 0;
lean_ctor_set(x_63, 0, x_324);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 6, x_325);
lean_ctor_set_uint32(x_63, sizeof(void*)*4, x_326);
lean_ctor_set_uint16(x_63, sizeof(void*)*4 + 4, x_327);
lean_ctor_set_uint8(x_63, sizeof(void*)*4 + 7, x_328);
x_329 = 0;
x_330 = 0;
x_331 = 0;
lean_ctor_set(x_1, 3, x_63);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_237);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_329);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_330);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_331);
return x_1;
}
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; uint32_t x_339; uint16_t x_340; uint8_t x_341; lean_object* x_342; uint8_t x_343; uint32_t x_344; uint16_t x_345; uint8_t x_346; lean_object* x_347; uint32_t x_348; uint16_t x_349; uint8_t x_350; 
x_332 = lean_ctor_get(x_63, 1);
x_333 = lean_ctor_get(x_63, 2);
lean_inc(x_333);
lean_inc(x_332);
lean_dec(x_63);
x_334 = lean_ctor_get(x_64, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_64, 1);
lean_inc(x_335);
x_336 = lean_ctor_get(x_64, 2);
lean_inc(x_336);
x_337 = lean_ctor_get(x_64, 3);
lean_inc(x_337);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 lean_ctor_release(x_64, 2);
 lean_ctor_release(x_64, 3);
 x_338 = x_64;
} else {
 lean_dec_ref(x_64);
 x_338 = lean_box(0);
}
x_339 = 0;
x_340 = 0;
x_341 = 0;
if (lean_is_scalar(x_338)) {
 x_342 = lean_alloc_ctor(1, 4, 8);
} else {
 x_342 = x_338;
}
lean_ctor_set(x_342, 0, x_334);
lean_ctor_set(x_342, 1, x_335);
lean_ctor_set(x_342, 2, x_336);
lean_ctor_set(x_342, 3, x_337);
lean_ctor_set_uint8(x_342, sizeof(void*)*4 + 6, x_237);
lean_ctor_set_uint32(x_342, sizeof(void*)*4, x_339);
lean_ctor_set_uint16(x_342, sizeof(void*)*4 + 4, x_340);
lean_ctor_set_uint8(x_342, sizeof(void*)*4 + 7, x_341);
x_343 = 0;
x_344 = 0;
x_345 = 0;
x_346 = 0;
x_347 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_347, 0, x_342);
lean_ctor_set(x_347, 1, x_332);
lean_ctor_set(x_347, 2, x_333);
lean_ctor_set(x_347, 3, x_216);
lean_ctor_set_uint8(x_347, sizeof(void*)*4 + 6, x_343);
lean_ctor_set_uint32(x_347, sizeof(void*)*4, x_344);
lean_ctor_set_uint16(x_347, sizeof(void*)*4 + 4, x_345);
lean_ctor_set_uint8(x_347, sizeof(void*)*4 + 7, x_346);
x_348 = 0;
x_349 = 0;
x_350 = 0;
lean_ctor_set(x_1, 3, x_347);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_237);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_348);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_349);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_350);
return x_1;
}
}
}
}
}
}
}
}
else
{
uint8_t x_351; 
x_351 = l_RBNode_isRed___rarg(x_49);
if (x_351 == 0)
{
lean_object* x_352; uint32_t x_353; uint16_t x_354; uint8_t x_355; 
x_352 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_49, x_2, x_3);
x_353 = 0;
x_354 = 0;
x_355 = 0;
lean_ctor_set(x_1, 0, x_352);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_353);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_354);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_355);
return x_1;
}
else
{
lean_object* x_356; lean_object* x_357; 
x_356 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_49, x_2, x_3);
x_357 = lean_ctor_get(x_356, 0);
lean_inc(x_357);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; 
x_358 = lean_ctor_get(x_356, 3);
lean_inc(x_358);
if (lean_obj_tag(x_358) == 0)
{
uint8_t x_359; 
x_359 = !lean_is_exclusive(x_356);
if (x_359 == 0)
{
lean_object* x_360; lean_object* x_361; uint8_t x_362; uint32_t x_363; uint16_t x_364; uint8_t x_365; uint8_t x_366; uint32_t x_367; uint16_t x_368; uint8_t x_369; 
x_360 = lean_ctor_get(x_356, 3);
lean_dec(x_360);
x_361 = lean_ctor_get(x_356, 0);
lean_dec(x_361);
x_362 = 0;
x_363 = 0;
x_364 = 0;
x_365 = 0;
lean_ctor_set(x_356, 0, x_358);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 6, x_362);
lean_ctor_set_uint32(x_356, sizeof(void*)*4, x_363);
lean_ctor_set_uint16(x_356, sizeof(void*)*4 + 4, x_364);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 7, x_365);
x_366 = 1;
x_367 = 0;
x_368 = 0;
x_369 = 0;
lean_ctor_set(x_1, 0, x_356);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_366);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_367);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_368);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_369);
return x_1;
}
else
{
lean_object* x_370; lean_object* x_371; uint8_t x_372; uint32_t x_373; uint16_t x_374; uint8_t x_375; lean_object* x_376; uint8_t x_377; uint32_t x_378; uint16_t x_379; uint8_t x_380; 
x_370 = lean_ctor_get(x_356, 1);
x_371 = lean_ctor_get(x_356, 2);
lean_inc(x_371);
lean_inc(x_370);
lean_dec(x_356);
x_372 = 0;
x_373 = 0;
x_374 = 0;
x_375 = 0;
x_376 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_376, 0, x_358);
lean_ctor_set(x_376, 1, x_370);
lean_ctor_set(x_376, 2, x_371);
lean_ctor_set(x_376, 3, x_358);
lean_ctor_set_uint8(x_376, sizeof(void*)*4 + 6, x_372);
lean_ctor_set_uint32(x_376, sizeof(void*)*4, x_373);
lean_ctor_set_uint16(x_376, sizeof(void*)*4 + 4, x_374);
lean_ctor_set_uint8(x_376, sizeof(void*)*4 + 7, x_375);
x_377 = 1;
x_378 = 0;
x_379 = 0;
x_380 = 0;
lean_ctor_set(x_1, 0, x_376);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_377);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_378);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_379);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_380);
return x_1;
}
}
else
{
uint8_t x_381; 
x_381 = lean_ctor_get_uint8(x_358, sizeof(void*)*4 + 6);
if (x_381 == 0)
{
uint8_t x_382; 
x_382 = !lean_is_exclusive(x_356);
if (x_382 == 0)
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; uint8_t x_387; 
x_383 = lean_ctor_get(x_356, 1);
x_384 = lean_ctor_get(x_356, 2);
x_385 = lean_ctor_get(x_356, 3);
lean_dec(x_385);
x_386 = lean_ctor_get(x_356, 0);
lean_dec(x_386);
x_387 = !lean_is_exclusive(x_358);
if (x_387 == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; uint8_t x_392; uint32_t x_393; uint16_t x_394; uint8_t x_395; uint32_t x_396; uint16_t x_397; uint8_t x_398; uint32_t x_399; uint16_t x_400; uint8_t x_401; 
x_388 = lean_ctor_get(x_358, 0);
x_389 = lean_ctor_get(x_358, 1);
x_390 = lean_ctor_get(x_358, 2);
x_391 = lean_ctor_get(x_358, 3);
x_392 = 1;
x_393 = 0;
x_394 = 0;
x_395 = 0;
lean_ctor_set(x_358, 3, x_388);
lean_ctor_set(x_358, 2, x_384);
lean_ctor_set(x_358, 1, x_383);
lean_ctor_set(x_358, 0, x_357);
lean_ctor_set_uint8(x_358, sizeof(void*)*4 + 6, x_392);
lean_ctor_set_uint32(x_358, sizeof(void*)*4, x_393);
lean_ctor_set_uint16(x_358, sizeof(void*)*4 + 4, x_394);
lean_ctor_set_uint8(x_358, sizeof(void*)*4 + 7, x_395);
x_396 = 0;
x_397 = 0;
x_398 = 0;
lean_ctor_set(x_356, 3, x_52);
lean_ctor_set(x_356, 2, x_51);
lean_ctor_set(x_356, 1, x_50);
lean_ctor_set(x_356, 0, x_391);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 6, x_392);
lean_ctor_set_uint32(x_356, sizeof(void*)*4, x_396);
lean_ctor_set_uint16(x_356, sizeof(void*)*4 + 4, x_397);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 7, x_398);
x_399 = 0;
x_400 = 0;
x_401 = 0;
lean_ctor_set(x_1, 3, x_356);
lean_ctor_set(x_1, 2, x_390);
lean_ctor_set(x_1, 1, x_389);
lean_ctor_set(x_1, 0, x_358);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_381);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_399);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_400);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_401);
return x_1;
}
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; uint8_t x_406; uint32_t x_407; uint16_t x_408; uint8_t x_409; lean_object* x_410; uint32_t x_411; uint16_t x_412; uint8_t x_413; uint32_t x_414; uint16_t x_415; uint8_t x_416; 
x_402 = lean_ctor_get(x_358, 0);
x_403 = lean_ctor_get(x_358, 1);
x_404 = lean_ctor_get(x_358, 2);
x_405 = lean_ctor_get(x_358, 3);
lean_inc(x_405);
lean_inc(x_404);
lean_inc(x_403);
lean_inc(x_402);
lean_dec(x_358);
x_406 = 1;
x_407 = 0;
x_408 = 0;
x_409 = 0;
x_410 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_410, 0, x_357);
lean_ctor_set(x_410, 1, x_383);
lean_ctor_set(x_410, 2, x_384);
lean_ctor_set(x_410, 3, x_402);
lean_ctor_set_uint8(x_410, sizeof(void*)*4 + 6, x_406);
lean_ctor_set_uint32(x_410, sizeof(void*)*4, x_407);
lean_ctor_set_uint16(x_410, sizeof(void*)*4 + 4, x_408);
lean_ctor_set_uint8(x_410, sizeof(void*)*4 + 7, x_409);
x_411 = 0;
x_412 = 0;
x_413 = 0;
lean_ctor_set(x_356, 3, x_52);
lean_ctor_set(x_356, 2, x_51);
lean_ctor_set(x_356, 1, x_50);
lean_ctor_set(x_356, 0, x_405);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 6, x_406);
lean_ctor_set_uint32(x_356, sizeof(void*)*4, x_411);
lean_ctor_set_uint16(x_356, sizeof(void*)*4 + 4, x_412);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 7, x_413);
x_414 = 0;
x_415 = 0;
x_416 = 0;
lean_ctor_set(x_1, 3, x_356);
lean_ctor_set(x_1, 2, x_404);
lean_ctor_set(x_1, 1, x_403);
lean_ctor_set(x_1, 0, x_410);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_381);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_414);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_415);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_416);
return x_1;
}
}
else
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; uint8_t x_424; uint32_t x_425; uint16_t x_426; uint8_t x_427; lean_object* x_428; uint32_t x_429; uint16_t x_430; uint8_t x_431; lean_object* x_432; uint32_t x_433; uint16_t x_434; uint8_t x_435; 
x_417 = lean_ctor_get(x_356, 1);
x_418 = lean_ctor_get(x_356, 2);
lean_inc(x_418);
lean_inc(x_417);
lean_dec(x_356);
x_419 = lean_ctor_get(x_358, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_358, 1);
lean_inc(x_420);
x_421 = lean_ctor_get(x_358, 2);
lean_inc(x_421);
x_422 = lean_ctor_get(x_358, 3);
lean_inc(x_422);
if (lean_is_exclusive(x_358)) {
 lean_ctor_release(x_358, 0);
 lean_ctor_release(x_358, 1);
 lean_ctor_release(x_358, 2);
 lean_ctor_release(x_358, 3);
 x_423 = x_358;
} else {
 lean_dec_ref(x_358);
 x_423 = lean_box(0);
}
x_424 = 1;
x_425 = 0;
x_426 = 0;
x_427 = 0;
if (lean_is_scalar(x_423)) {
 x_428 = lean_alloc_ctor(1, 4, 8);
} else {
 x_428 = x_423;
}
lean_ctor_set(x_428, 0, x_357);
lean_ctor_set(x_428, 1, x_417);
lean_ctor_set(x_428, 2, x_418);
lean_ctor_set(x_428, 3, x_419);
lean_ctor_set_uint8(x_428, sizeof(void*)*4 + 6, x_424);
lean_ctor_set_uint32(x_428, sizeof(void*)*4, x_425);
lean_ctor_set_uint16(x_428, sizeof(void*)*4 + 4, x_426);
lean_ctor_set_uint8(x_428, sizeof(void*)*4 + 7, x_427);
x_429 = 0;
x_430 = 0;
x_431 = 0;
x_432 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_432, 0, x_422);
lean_ctor_set(x_432, 1, x_50);
lean_ctor_set(x_432, 2, x_51);
lean_ctor_set(x_432, 3, x_52);
lean_ctor_set_uint8(x_432, sizeof(void*)*4 + 6, x_424);
lean_ctor_set_uint32(x_432, sizeof(void*)*4, x_429);
lean_ctor_set_uint16(x_432, sizeof(void*)*4 + 4, x_430);
lean_ctor_set_uint8(x_432, sizeof(void*)*4 + 7, x_431);
x_433 = 0;
x_434 = 0;
x_435 = 0;
lean_ctor_set(x_1, 3, x_432);
lean_ctor_set(x_1, 2, x_421);
lean_ctor_set(x_1, 1, x_420);
lean_ctor_set(x_1, 0, x_428);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_381);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_433);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_434);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_435);
return x_1;
}
}
else
{
uint8_t x_436; 
x_436 = !lean_is_exclusive(x_356);
if (x_436 == 0)
{
lean_object* x_437; lean_object* x_438; uint8_t x_439; uint32_t x_440; uint16_t x_441; uint8_t x_442; uint32_t x_443; uint16_t x_444; uint8_t x_445; 
x_437 = lean_ctor_get(x_356, 3);
lean_dec(x_437);
x_438 = lean_ctor_get(x_356, 0);
lean_dec(x_438);
x_439 = 0;
x_440 = 0;
x_441 = 0;
x_442 = 0;
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 6, x_439);
lean_ctor_set_uint32(x_356, sizeof(void*)*4, x_440);
lean_ctor_set_uint16(x_356, sizeof(void*)*4 + 4, x_441);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 7, x_442);
x_443 = 0;
x_444 = 0;
x_445 = 0;
lean_ctor_set(x_1, 0, x_356);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_381);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_443);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_444);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_445);
return x_1;
}
else
{
lean_object* x_446; lean_object* x_447; uint8_t x_448; uint32_t x_449; uint16_t x_450; uint8_t x_451; lean_object* x_452; uint32_t x_453; uint16_t x_454; uint8_t x_455; 
x_446 = lean_ctor_get(x_356, 1);
x_447 = lean_ctor_get(x_356, 2);
lean_inc(x_447);
lean_inc(x_446);
lean_dec(x_356);
x_448 = 0;
x_449 = 0;
x_450 = 0;
x_451 = 0;
x_452 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_452, 0, x_357);
lean_ctor_set(x_452, 1, x_446);
lean_ctor_set(x_452, 2, x_447);
lean_ctor_set(x_452, 3, x_358);
lean_ctor_set_uint8(x_452, sizeof(void*)*4 + 6, x_448);
lean_ctor_set_uint32(x_452, sizeof(void*)*4, x_449);
lean_ctor_set_uint16(x_452, sizeof(void*)*4 + 4, x_450);
lean_ctor_set_uint8(x_452, sizeof(void*)*4 + 7, x_451);
x_453 = 0;
x_454 = 0;
x_455 = 0;
lean_ctor_set(x_1, 0, x_452);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_381);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_453);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_454);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_455);
return x_1;
}
}
}
}
else
{
uint8_t x_456; 
x_456 = lean_ctor_get_uint8(x_357, sizeof(void*)*4 + 6);
if (x_456 == 0)
{
uint8_t x_457; 
x_457 = !lean_is_exclusive(x_356);
if (x_457 == 0)
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; uint8_t x_462; 
x_458 = lean_ctor_get(x_356, 1);
x_459 = lean_ctor_get(x_356, 2);
x_460 = lean_ctor_get(x_356, 3);
x_461 = lean_ctor_get(x_356, 0);
lean_dec(x_461);
x_462 = !lean_is_exclusive(x_357);
if (x_462 == 0)
{
uint8_t x_463; uint32_t x_464; uint16_t x_465; uint8_t x_466; uint32_t x_467; uint16_t x_468; uint8_t x_469; uint32_t x_470; uint16_t x_471; uint8_t x_472; 
x_463 = 1;
x_464 = 0;
x_465 = 0;
x_466 = 0;
lean_ctor_set_uint8(x_357, sizeof(void*)*4 + 6, x_463);
lean_ctor_set_uint32(x_357, sizeof(void*)*4, x_464);
lean_ctor_set_uint16(x_357, sizeof(void*)*4 + 4, x_465);
lean_ctor_set_uint8(x_357, sizeof(void*)*4 + 7, x_466);
x_467 = 0;
x_468 = 0;
x_469 = 0;
lean_ctor_set(x_356, 3, x_52);
lean_ctor_set(x_356, 2, x_51);
lean_ctor_set(x_356, 1, x_50);
lean_ctor_set(x_356, 0, x_460);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 6, x_463);
lean_ctor_set_uint32(x_356, sizeof(void*)*4, x_467);
lean_ctor_set_uint16(x_356, sizeof(void*)*4 + 4, x_468);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 7, x_469);
x_470 = 0;
x_471 = 0;
x_472 = 0;
lean_ctor_set(x_1, 3, x_356);
lean_ctor_set(x_1, 2, x_459);
lean_ctor_set(x_1, 1, x_458);
lean_ctor_set(x_1, 0, x_357);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_456);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_470);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_471);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_472);
return x_1;
}
else
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; uint8_t x_477; uint32_t x_478; uint16_t x_479; uint8_t x_480; lean_object* x_481; uint32_t x_482; uint16_t x_483; uint8_t x_484; uint32_t x_485; uint16_t x_486; uint8_t x_487; 
x_473 = lean_ctor_get(x_357, 0);
x_474 = lean_ctor_get(x_357, 1);
x_475 = lean_ctor_get(x_357, 2);
x_476 = lean_ctor_get(x_357, 3);
lean_inc(x_476);
lean_inc(x_475);
lean_inc(x_474);
lean_inc(x_473);
lean_dec(x_357);
x_477 = 1;
x_478 = 0;
x_479 = 0;
x_480 = 0;
x_481 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_481, 0, x_473);
lean_ctor_set(x_481, 1, x_474);
lean_ctor_set(x_481, 2, x_475);
lean_ctor_set(x_481, 3, x_476);
lean_ctor_set_uint8(x_481, sizeof(void*)*4 + 6, x_477);
lean_ctor_set_uint32(x_481, sizeof(void*)*4, x_478);
lean_ctor_set_uint16(x_481, sizeof(void*)*4 + 4, x_479);
lean_ctor_set_uint8(x_481, sizeof(void*)*4 + 7, x_480);
x_482 = 0;
x_483 = 0;
x_484 = 0;
lean_ctor_set(x_356, 3, x_52);
lean_ctor_set(x_356, 2, x_51);
lean_ctor_set(x_356, 1, x_50);
lean_ctor_set(x_356, 0, x_460);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 6, x_477);
lean_ctor_set_uint32(x_356, sizeof(void*)*4, x_482);
lean_ctor_set_uint16(x_356, sizeof(void*)*4 + 4, x_483);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 7, x_484);
x_485 = 0;
x_486 = 0;
x_487 = 0;
lean_ctor_set(x_1, 3, x_356);
lean_ctor_set(x_1, 2, x_459);
lean_ctor_set(x_1, 1, x_458);
lean_ctor_set(x_1, 0, x_481);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_456);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_485);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_486);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_487);
return x_1;
}
}
else
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; uint8_t x_496; uint32_t x_497; uint16_t x_498; uint8_t x_499; lean_object* x_500; uint32_t x_501; uint16_t x_502; uint8_t x_503; lean_object* x_504; uint32_t x_505; uint16_t x_506; uint8_t x_507; 
x_488 = lean_ctor_get(x_356, 1);
x_489 = lean_ctor_get(x_356, 2);
x_490 = lean_ctor_get(x_356, 3);
lean_inc(x_490);
lean_inc(x_489);
lean_inc(x_488);
lean_dec(x_356);
x_491 = lean_ctor_get(x_357, 0);
lean_inc(x_491);
x_492 = lean_ctor_get(x_357, 1);
lean_inc(x_492);
x_493 = lean_ctor_get(x_357, 2);
lean_inc(x_493);
x_494 = lean_ctor_get(x_357, 3);
lean_inc(x_494);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 lean_ctor_release(x_357, 1);
 lean_ctor_release(x_357, 2);
 lean_ctor_release(x_357, 3);
 x_495 = x_357;
} else {
 lean_dec_ref(x_357);
 x_495 = lean_box(0);
}
x_496 = 1;
x_497 = 0;
x_498 = 0;
x_499 = 0;
if (lean_is_scalar(x_495)) {
 x_500 = lean_alloc_ctor(1, 4, 8);
} else {
 x_500 = x_495;
}
lean_ctor_set(x_500, 0, x_491);
lean_ctor_set(x_500, 1, x_492);
lean_ctor_set(x_500, 2, x_493);
lean_ctor_set(x_500, 3, x_494);
lean_ctor_set_uint8(x_500, sizeof(void*)*4 + 6, x_496);
lean_ctor_set_uint32(x_500, sizeof(void*)*4, x_497);
lean_ctor_set_uint16(x_500, sizeof(void*)*4 + 4, x_498);
lean_ctor_set_uint8(x_500, sizeof(void*)*4 + 7, x_499);
x_501 = 0;
x_502 = 0;
x_503 = 0;
x_504 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_504, 0, x_490);
lean_ctor_set(x_504, 1, x_50);
lean_ctor_set(x_504, 2, x_51);
lean_ctor_set(x_504, 3, x_52);
lean_ctor_set_uint8(x_504, sizeof(void*)*4 + 6, x_496);
lean_ctor_set_uint32(x_504, sizeof(void*)*4, x_501);
lean_ctor_set_uint16(x_504, sizeof(void*)*4 + 4, x_502);
lean_ctor_set_uint8(x_504, sizeof(void*)*4 + 7, x_503);
x_505 = 0;
x_506 = 0;
x_507 = 0;
lean_ctor_set(x_1, 3, x_504);
lean_ctor_set(x_1, 2, x_489);
lean_ctor_set(x_1, 1, x_488);
lean_ctor_set(x_1, 0, x_500);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_456);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_505);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_506);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_507);
return x_1;
}
}
else
{
lean_object* x_508; 
x_508 = lean_ctor_get(x_356, 3);
lean_inc(x_508);
if (lean_obj_tag(x_508) == 0)
{
uint8_t x_509; 
x_509 = !lean_is_exclusive(x_356);
if (x_509 == 0)
{
lean_object* x_510; lean_object* x_511; uint8_t x_512; uint32_t x_513; uint16_t x_514; uint8_t x_515; uint32_t x_516; uint16_t x_517; uint8_t x_518; 
x_510 = lean_ctor_get(x_356, 3);
lean_dec(x_510);
x_511 = lean_ctor_get(x_356, 0);
lean_dec(x_511);
x_512 = 0;
x_513 = 0;
x_514 = 0;
x_515 = 0;
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 6, x_512);
lean_ctor_set_uint32(x_356, sizeof(void*)*4, x_513);
lean_ctor_set_uint16(x_356, sizeof(void*)*4 + 4, x_514);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 7, x_515);
x_516 = 0;
x_517 = 0;
x_518 = 0;
lean_ctor_set(x_1, 0, x_356);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_456);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_516);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_517);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_518);
return x_1;
}
else
{
lean_object* x_519; lean_object* x_520; uint8_t x_521; uint32_t x_522; uint16_t x_523; uint8_t x_524; lean_object* x_525; uint32_t x_526; uint16_t x_527; uint8_t x_528; 
x_519 = lean_ctor_get(x_356, 1);
x_520 = lean_ctor_get(x_356, 2);
lean_inc(x_520);
lean_inc(x_519);
lean_dec(x_356);
x_521 = 0;
x_522 = 0;
x_523 = 0;
x_524 = 0;
x_525 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_525, 0, x_357);
lean_ctor_set(x_525, 1, x_519);
lean_ctor_set(x_525, 2, x_520);
lean_ctor_set(x_525, 3, x_508);
lean_ctor_set_uint8(x_525, sizeof(void*)*4 + 6, x_521);
lean_ctor_set_uint32(x_525, sizeof(void*)*4, x_522);
lean_ctor_set_uint16(x_525, sizeof(void*)*4 + 4, x_523);
lean_ctor_set_uint8(x_525, sizeof(void*)*4 + 7, x_524);
x_526 = 0;
x_527 = 0;
x_528 = 0;
lean_ctor_set(x_1, 0, x_525);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_456);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_526);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_527);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_528);
return x_1;
}
}
else
{
uint8_t x_529; 
x_529 = lean_ctor_get_uint8(x_508, sizeof(void*)*4 + 6);
if (x_529 == 0)
{
uint8_t x_530; 
lean_free_object(x_1);
x_530 = !lean_is_exclusive(x_356);
if (x_530 == 0)
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; uint8_t x_535; 
x_531 = lean_ctor_get(x_356, 1);
x_532 = lean_ctor_get(x_356, 2);
x_533 = lean_ctor_get(x_356, 3);
lean_dec(x_533);
x_534 = lean_ctor_get(x_356, 0);
lean_dec(x_534);
x_535 = !lean_is_exclusive(x_508);
if (x_535 == 0)
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; uint32_t x_540; uint16_t x_541; uint8_t x_542; uint8_t x_543; 
x_536 = lean_ctor_get(x_508, 0);
x_537 = lean_ctor_get(x_508, 1);
x_538 = lean_ctor_get(x_508, 2);
x_539 = lean_ctor_get(x_508, 3);
x_540 = 0;
x_541 = 0;
x_542 = 0;
lean_inc(x_357);
lean_ctor_set(x_508, 3, x_536);
lean_ctor_set(x_508, 2, x_532);
lean_ctor_set(x_508, 1, x_531);
lean_ctor_set(x_508, 0, x_357);
x_543 = !lean_is_exclusive(x_357);
if (x_543 == 0)
{
lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; uint32_t x_548; uint16_t x_549; uint8_t x_550; uint32_t x_551; uint16_t x_552; uint8_t x_553; 
x_544 = lean_ctor_get(x_357, 3);
lean_dec(x_544);
x_545 = lean_ctor_get(x_357, 2);
lean_dec(x_545);
x_546 = lean_ctor_get(x_357, 1);
lean_dec(x_546);
x_547 = lean_ctor_get(x_357, 0);
lean_dec(x_547);
lean_ctor_set_uint8(x_508, sizeof(void*)*4 + 6, x_456);
lean_ctor_set_uint32(x_508, sizeof(void*)*4, x_540);
lean_ctor_set_uint16(x_508, sizeof(void*)*4 + 4, x_541);
lean_ctor_set_uint8(x_508, sizeof(void*)*4 + 7, x_542);
x_548 = 0;
x_549 = 0;
x_550 = 0;
lean_ctor_set(x_357, 3, x_52);
lean_ctor_set(x_357, 2, x_51);
lean_ctor_set(x_357, 1, x_50);
lean_ctor_set(x_357, 0, x_539);
lean_ctor_set_uint32(x_357, sizeof(void*)*4, x_548);
lean_ctor_set_uint16(x_357, sizeof(void*)*4 + 4, x_549);
lean_ctor_set_uint8(x_357, sizeof(void*)*4 + 7, x_550);
x_551 = 0;
x_552 = 0;
x_553 = 0;
lean_ctor_set(x_356, 3, x_357);
lean_ctor_set(x_356, 2, x_538);
lean_ctor_set(x_356, 1, x_537);
lean_ctor_set(x_356, 0, x_508);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 6, x_529);
lean_ctor_set_uint32(x_356, sizeof(void*)*4, x_551);
lean_ctor_set_uint16(x_356, sizeof(void*)*4 + 4, x_552);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 7, x_553);
return x_356;
}
else
{
uint32_t x_554; uint16_t x_555; uint8_t x_556; lean_object* x_557; uint32_t x_558; uint16_t x_559; uint8_t x_560; 
lean_dec(x_357);
lean_ctor_set_uint8(x_508, sizeof(void*)*4 + 6, x_456);
lean_ctor_set_uint32(x_508, sizeof(void*)*4, x_540);
lean_ctor_set_uint16(x_508, sizeof(void*)*4 + 4, x_541);
lean_ctor_set_uint8(x_508, sizeof(void*)*4 + 7, x_542);
x_554 = 0;
x_555 = 0;
x_556 = 0;
x_557 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_557, 0, x_539);
lean_ctor_set(x_557, 1, x_50);
lean_ctor_set(x_557, 2, x_51);
lean_ctor_set(x_557, 3, x_52);
lean_ctor_set_uint8(x_557, sizeof(void*)*4 + 6, x_456);
lean_ctor_set_uint32(x_557, sizeof(void*)*4, x_554);
lean_ctor_set_uint16(x_557, sizeof(void*)*4 + 4, x_555);
lean_ctor_set_uint8(x_557, sizeof(void*)*4 + 7, x_556);
x_558 = 0;
x_559 = 0;
x_560 = 0;
lean_ctor_set(x_356, 3, x_557);
lean_ctor_set(x_356, 2, x_538);
lean_ctor_set(x_356, 1, x_537);
lean_ctor_set(x_356, 0, x_508);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 6, x_529);
lean_ctor_set_uint32(x_356, sizeof(void*)*4, x_558);
lean_ctor_set_uint16(x_356, sizeof(void*)*4 + 4, x_559);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 7, x_560);
return x_356;
}
}
else
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; uint32_t x_565; uint16_t x_566; uint8_t x_567; lean_object* x_568; lean_object* x_569; uint32_t x_570; uint16_t x_571; uint8_t x_572; lean_object* x_573; uint32_t x_574; uint16_t x_575; uint8_t x_576; 
x_561 = lean_ctor_get(x_508, 0);
x_562 = lean_ctor_get(x_508, 1);
x_563 = lean_ctor_get(x_508, 2);
x_564 = lean_ctor_get(x_508, 3);
lean_inc(x_564);
lean_inc(x_563);
lean_inc(x_562);
lean_inc(x_561);
lean_dec(x_508);
x_565 = 0;
x_566 = 0;
x_567 = 0;
lean_inc(x_357);
x_568 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_568, 0, x_357);
lean_ctor_set(x_568, 1, x_531);
lean_ctor_set(x_568, 2, x_532);
lean_ctor_set(x_568, 3, x_561);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 lean_ctor_release(x_357, 1);
 lean_ctor_release(x_357, 2);
 lean_ctor_release(x_357, 3);
 x_569 = x_357;
} else {
 lean_dec_ref(x_357);
 x_569 = lean_box(0);
}
lean_ctor_set_uint8(x_568, sizeof(void*)*4 + 6, x_456);
lean_ctor_set_uint32(x_568, sizeof(void*)*4, x_565);
lean_ctor_set_uint16(x_568, sizeof(void*)*4 + 4, x_566);
lean_ctor_set_uint8(x_568, sizeof(void*)*4 + 7, x_567);
x_570 = 0;
x_571 = 0;
x_572 = 0;
if (lean_is_scalar(x_569)) {
 x_573 = lean_alloc_ctor(1, 4, 8);
} else {
 x_573 = x_569;
}
lean_ctor_set(x_573, 0, x_564);
lean_ctor_set(x_573, 1, x_50);
lean_ctor_set(x_573, 2, x_51);
lean_ctor_set(x_573, 3, x_52);
lean_ctor_set_uint8(x_573, sizeof(void*)*4 + 6, x_456);
lean_ctor_set_uint32(x_573, sizeof(void*)*4, x_570);
lean_ctor_set_uint16(x_573, sizeof(void*)*4 + 4, x_571);
lean_ctor_set_uint8(x_573, sizeof(void*)*4 + 7, x_572);
x_574 = 0;
x_575 = 0;
x_576 = 0;
lean_ctor_set(x_356, 3, x_573);
lean_ctor_set(x_356, 2, x_563);
lean_ctor_set(x_356, 1, x_562);
lean_ctor_set(x_356, 0, x_568);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 6, x_529);
lean_ctor_set_uint32(x_356, sizeof(void*)*4, x_574);
lean_ctor_set_uint16(x_356, sizeof(void*)*4 + 4, x_575);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 7, x_576);
return x_356;
}
}
else
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; uint32_t x_584; uint16_t x_585; uint8_t x_586; lean_object* x_587; lean_object* x_588; uint32_t x_589; uint16_t x_590; uint8_t x_591; lean_object* x_592; uint32_t x_593; uint16_t x_594; uint8_t x_595; lean_object* x_596; 
x_577 = lean_ctor_get(x_356, 1);
x_578 = lean_ctor_get(x_356, 2);
lean_inc(x_578);
lean_inc(x_577);
lean_dec(x_356);
x_579 = lean_ctor_get(x_508, 0);
lean_inc(x_579);
x_580 = lean_ctor_get(x_508, 1);
lean_inc(x_580);
x_581 = lean_ctor_get(x_508, 2);
lean_inc(x_581);
x_582 = lean_ctor_get(x_508, 3);
lean_inc(x_582);
if (lean_is_exclusive(x_508)) {
 lean_ctor_release(x_508, 0);
 lean_ctor_release(x_508, 1);
 lean_ctor_release(x_508, 2);
 lean_ctor_release(x_508, 3);
 x_583 = x_508;
} else {
 lean_dec_ref(x_508);
 x_583 = lean_box(0);
}
x_584 = 0;
x_585 = 0;
x_586 = 0;
lean_inc(x_357);
if (lean_is_scalar(x_583)) {
 x_587 = lean_alloc_ctor(1, 4, 8);
} else {
 x_587 = x_583;
}
lean_ctor_set(x_587, 0, x_357);
lean_ctor_set(x_587, 1, x_577);
lean_ctor_set(x_587, 2, x_578);
lean_ctor_set(x_587, 3, x_579);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 lean_ctor_release(x_357, 1);
 lean_ctor_release(x_357, 2);
 lean_ctor_release(x_357, 3);
 x_588 = x_357;
} else {
 lean_dec_ref(x_357);
 x_588 = lean_box(0);
}
lean_ctor_set_uint8(x_587, sizeof(void*)*4 + 6, x_456);
lean_ctor_set_uint32(x_587, sizeof(void*)*4, x_584);
lean_ctor_set_uint16(x_587, sizeof(void*)*4 + 4, x_585);
lean_ctor_set_uint8(x_587, sizeof(void*)*4 + 7, x_586);
x_589 = 0;
x_590 = 0;
x_591 = 0;
if (lean_is_scalar(x_588)) {
 x_592 = lean_alloc_ctor(1, 4, 8);
} else {
 x_592 = x_588;
}
lean_ctor_set(x_592, 0, x_582);
lean_ctor_set(x_592, 1, x_50);
lean_ctor_set(x_592, 2, x_51);
lean_ctor_set(x_592, 3, x_52);
lean_ctor_set_uint8(x_592, sizeof(void*)*4 + 6, x_456);
lean_ctor_set_uint32(x_592, sizeof(void*)*4, x_589);
lean_ctor_set_uint16(x_592, sizeof(void*)*4 + 4, x_590);
lean_ctor_set_uint8(x_592, sizeof(void*)*4 + 7, x_591);
x_593 = 0;
x_594 = 0;
x_595 = 0;
x_596 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_596, 0, x_587);
lean_ctor_set(x_596, 1, x_580);
lean_ctor_set(x_596, 2, x_581);
lean_ctor_set(x_596, 3, x_592);
lean_ctor_set_uint8(x_596, sizeof(void*)*4 + 6, x_529);
lean_ctor_set_uint32(x_596, sizeof(void*)*4, x_593);
lean_ctor_set_uint16(x_596, sizeof(void*)*4 + 4, x_594);
lean_ctor_set_uint8(x_596, sizeof(void*)*4 + 7, x_595);
return x_596;
}
}
else
{
uint8_t x_597; 
x_597 = !lean_is_exclusive(x_356);
if (x_597 == 0)
{
lean_object* x_598; lean_object* x_599; uint8_t x_600; 
x_598 = lean_ctor_get(x_356, 3);
lean_dec(x_598);
x_599 = lean_ctor_get(x_356, 0);
lean_dec(x_599);
x_600 = !lean_is_exclusive(x_357);
if (x_600 == 0)
{
uint32_t x_601; uint16_t x_602; uint8_t x_603; uint8_t x_604; uint32_t x_605; uint16_t x_606; uint8_t x_607; uint32_t x_608; uint16_t x_609; uint8_t x_610; 
x_601 = 0;
x_602 = 0;
x_603 = 0;
lean_ctor_set_uint8(x_357, sizeof(void*)*4 + 6, x_529);
lean_ctor_set_uint32(x_357, sizeof(void*)*4, x_601);
lean_ctor_set_uint16(x_357, sizeof(void*)*4 + 4, x_602);
lean_ctor_set_uint8(x_357, sizeof(void*)*4 + 7, x_603);
x_604 = 0;
x_605 = 0;
x_606 = 0;
x_607 = 0;
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 6, x_604);
lean_ctor_set_uint32(x_356, sizeof(void*)*4, x_605);
lean_ctor_set_uint16(x_356, sizeof(void*)*4 + 4, x_606);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 7, x_607);
x_608 = 0;
x_609 = 0;
x_610 = 0;
lean_ctor_set(x_1, 0, x_356);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_529);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_608);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_609);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_610);
return x_1;
}
else
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; uint32_t x_615; uint16_t x_616; uint8_t x_617; lean_object* x_618; uint8_t x_619; uint32_t x_620; uint16_t x_621; uint8_t x_622; uint32_t x_623; uint16_t x_624; uint8_t x_625; 
x_611 = lean_ctor_get(x_357, 0);
x_612 = lean_ctor_get(x_357, 1);
x_613 = lean_ctor_get(x_357, 2);
x_614 = lean_ctor_get(x_357, 3);
lean_inc(x_614);
lean_inc(x_613);
lean_inc(x_612);
lean_inc(x_611);
lean_dec(x_357);
x_615 = 0;
x_616 = 0;
x_617 = 0;
x_618 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_618, 0, x_611);
lean_ctor_set(x_618, 1, x_612);
lean_ctor_set(x_618, 2, x_613);
lean_ctor_set(x_618, 3, x_614);
lean_ctor_set_uint8(x_618, sizeof(void*)*4 + 6, x_529);
lean_ctor_set_uint32(x_618, sizeof(void*)*4, x_615);
lean_ctor_set_uint16(x_618, sizeof(void*)*4 + 4, x_616);
lean_ctor_set_uint8(x_618, sizeof(void*)*4 + 7, x_617);
x_619 = 0;
x_620 = 0;
x_621 = 0;
x_622 = 0;
lean_ctor_set(x_356, 0, x_618);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 6, x_619);
lean_ctor_set_uint32(x_356, sizeof(void*)*4, x_620);
lean_ctor_set_uint16(x_356, sizeof(void*)*4 + 4, x_621);
lean_ctor_set_uint8(x_356, sizeof(void*)*4 + 7, x_622);
x_623 = 0;
x_624 = 0;
x_625 = 0;
lean_ctor_set(x_1, 0, x_356);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_529);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_623);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_624);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_625);
return x_1;
}
}
else
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; uint32_t x_633; uint16_t x_634; uint8_t x_635; lean_object* x_636; uint8_t x_637; uint32_t x_638; uint16_t x_639; uint8_t x_640; lean_object* x_641; uint32_t x_642; uint16_t x_643; uint8_t x_644; 
x_626 = lean_ctor_get(x_356, 1);
x_627 = lean_ctor_get(x_356, 2);
lean_inc(x_627);
lean_inc(x_626);
lean_dec(x_356);
x_628 = lean_ctor_get(x_357, 0);
lean_inc(x_628);
x_629 = lean_ctor_get(x_357, 1);
lean_inc(x_629);
x_630 = lean_ctor_get(x_357, 2);
lean_inc(x_630);
x_631 = lean_ctor_get(x_357, 3);
lean_inc(x_631);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 lean_ctor_release(x_357, 1);
 lean_ctor_release(x_357, 2);
 lean_ctor_release(x_357, 3);
 x_632 = x_357;
} else {
 lean_dec_ref(x_357);
 x_632 = lean_box(0);
}
x_633 = 0;
x_634 = 0;
x_635 = 0;
if (lean_is_scalar(x_632)) {
 x_636 = lean_alloc_ctor(1, 4, 8);
} else {
 x_636 = x_632;
}
lean_ctor_set(x_636, 0, x_628);
lean_ctor_set(x_636, 1, x_629);
lean_ctor_set(x_636, 2, x_630);
lean_ctor_set(x_636, 3, x_631);
lean_ctor_set_uint8(x_636, sizeof(void*)*4 + 6, x_529);
lean_ctor_set_uint32(x_636, sizeof(void*)*4, x_633);
lean_ctor_set_uint16(x_636, sizeof(void*)*4 + 4, x_634);
lean_ctor_set_uint8(x_636, sizeof(void*)*4 + 7, x_635);
x_637 = 0;
x_638 = 0;
x_639 = 0;
x_640 = 0;
x_641 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_641, 0, x_636);
lean_ctor_set(x_641, 1, x_626);
lean_ctor_set(x_641, 2, x_627);
lean_ctor_set(x_641, 3, x_508);
lean_ctor_set_uint8(x_641, sizeof(void*)*4 + 6, x_637);
lean_ctor_set_uint32(x_641, sizeof(void*)*4, x_638);
lean_ctor_set_uint16(x_641, sizeof(void*)*4 + 4, x_639);
lean_ctor_set_uint8(x_641, sizeof(void*)*4 + 7, x_640);
x_642 = 0;
x_643 = 0;
x_644 = 0;
lean_ctor_set(x_1, 0, x_641);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 6, x_529);
lean_ctor_set_uint32(x_1, sizeof(void*)*4, x_642);
lean_ctor_set_uint16(x_1, sizeof(void*)*4 + 4, x_643);
lean_ctor_set_uint8(x_1, sizeof(void*)*4 + 7, x_644);
return x_1;
}
}
}
}
}
}
}
}
else
{
lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; uint8_t x_649; 
x_645 = lean_ctor_get(x_1, 0);
x_646 = lean_ctor_get(x_1, 1);
x_647 = lean_ctor_get(x_1, 2);
x_648 = lean_ctor_get(x_1, 3);
lean_inc(x_648);
lean_inc(x_647);
lean_inc(x_646);
lean_inc(x_645);
lean_dec(x_1);
x_649 = lean_nat_dec_lt(x_2, x_646);
if (x_649 == 0)
{
uint8_t x_650; 
x_650 = lean_nat_dec_lt(x_646, x_2);
if (x_650 == 0)
{
uint32_t x_651; uint16_t x_652; uint8_t x_653; lean_object* x_654; 
lean_dec(x_647);
lean_dec(x_646);
x_651 = 0;
x_652 = 0;
x_653 = 0;
x_654 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_654, 0, x_645);
lean_ctor_set(x_654, 1, x_2);
lean_ctor_set(x_654, 2, x_3);
lean_ctor_set(x_654, 3, x_648);
lean_ctor_set_uint8(x_654, sizeof(void*)*4 + 6, x_9);
lean_ctor_set_uint32(x_654, sizeof(void*)*4, x_651);
lean_ctor_set_uint16(x_654, sizeof(void*)*4 + 4, x_652);
lean_ctor_set_uint8(x_654, sizeof(void*)*4 + 7, x_653);
return x_654;
}
else
{
uint8_t x_655; 
x_655 = l_RBNode_isRed___rarg(x_648);
if (x_655 == 0)
{
lean_object* x_656; uint32_t x_657; uint16_t x_658; uint8_t x_659; lean_object* x_660; 
x_656 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_648, x_2, x_3);
x_657 = 0;
x_658 = 0;
x_659 = 0;
x_660 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_660, 0, x_645);
lean_ctor_set(x_660, 1, x_646);
lean_ctor_set(x_660, 2, x_647);
lean_ctor_set(x_660, 3, x_656);
lean_ctor_set_uint8(x_660, sizeof(void*)*4 + 6, x_9);
lean_ctor_set_uint32(x_660, sizeof(void*)*4, x_657);
lean_ctor_set_uint16(x_660, sizeof(void*)*4 + 4, x_658);
lean_ctor_set_uint8(x_660, sizeof(void*)*4 + 7, x_659);
return x_660;
}
else
{
lean_object* x_661; lean_object* x_662; 
x_661 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_648, x_2, x_3);
x_662 = lean_ctor_get(x_661, 0);
lean_inc(x_662);
if (lean_obj_tag(x_662) == 0)
{
lean_object* x_663; 
x_663 = lean_ctor_get(x_661, 3);
lean_inc(x_663);
if (lean_obj_tag(x_663) == 0)
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; uint8_t x_667; uint32_t x_668; uint16_t x_669; uint8_t x_670; lean_object* x_671; uint8_t x_672; uint32_t x_673; uint16_t x_674; uint8_t x_675; lean_object* x_676; 
x_664 = lean_ctor_get(x_661, 1);
lean_inc(x_664);
x_665 = lean_ctor_get(x_661, 2);
lean_inc(x_665);
if (lean_is_exclusive(x_661)) {
 lean_ctor_release(x_661, 0);
 lean_ctor_release(x_661, 1);
 lean_ctor_release(x_661, 2);
 lean_ctor_release(x_661, 3);
 x_666 = x_661;
} else {
 lean_dec_ref(x_661);
 x_666 = lean_box(0);
}
x_667 = 0;
x_668 = 0;
x_669 = 0;
x_670 = 0;
if (lean_is_scalar(x_666)) {
 x_671 = lean_alloc_ctor(1, 4, 8);
} else {
 x_671 = x_666;
}
lean_ctor_set(x_671, 0, x_663);
lean_ctor_set(x_671, 1, x_664);
lean_ctor_set(x_671, 2, x_665);
lean_ctor_set(x_671, 3, x_663);
lean_ctor_set_uint8(x_671, sizeof(void*)*4 + 6, x_667);
lean_ctor_set_uint32(x_671, sizeof(void*)*4, x_668);
lean_ctor_set_uint16(x_671, sizeof(void*)*4 + 4, x_669);
lean_ctor_set_uint8(x_671, sizeof(void*)*4 + 7, x_670);
x_672 = 1;
x_673 = 0;
x_674 = 0;
x_675 = 0;
x_676 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_676, 0, x_645);
lean_ctor_set(x_676, 1, x_646);
lean_ctor_set(x_676, 2, x_647);
lean_ctor_set(x_676, 3, x_671);
lean_ctor_set_uint8(x_676, sizeof(void*)*4 + 6, x_672);
lean_ctor_set_uint32(x_676, sizeof(void*)*4, x_673);
lean_ctor_set_uint16(x_676, sizeof(void*)*4 + 4, x_674);
lean_ctor_set_uint8(x_676, sizeof(void*)*4 + 7, x_675);
return x_676;
}
else
{
uint8_t x_677; 
x_677 = lean_ctor_get_uint8(x_663, sizeof(void*)*4 + 6);
if (x_677 == 0)
{
lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; uint8_t x_686; uint32_t x_687; uint16_t x_688; uint8_t x_689; lean_object* x_690; uint32_t x_691; uint16_t x_692; uint8_t x_693; lean_object* x_694; uint32_t x_695; uint16_t x_696; uint8_t x_697; lean_object* x_698; 
x_678 = lean_ctor_get(x_661, 1);
lean_inc(x_678);
x_679 = lean_ctor_get(x_661, 2);
lean_inc(x_679);
if (lean_is_exclusive(x_661)) {
 lean_ctor_release(x_661, 0);
 lean_ctor_release(x_661, 1);
 lean_ctor_release(x_661, 2);
 lean_ctor_release(x_661, 3);
 x_680 = x_661;
} else {
 lean_dec_ref(x_661);
 x_680 = lean_box(0);
}
x_681 = lean_ctor_get(x_663, 0);
lean_inc(x_681);
x_682 = lean_ctor_get(x_663, 1);
lean_inc(x_682);
x_683 = lean_ctor_get(x_663, 2);
lean_inc(x_683);
x_684 = lean_ctor_get(x_663, 3);
lean_inc(x_684);
if (lean_is_exclusive(x_663)) {
 lean_ctor_release(x_663, 0);
 lean_ctor_release(x_663, 1);
 lean_ctor_release(x_663, 2);
 lean_ctor_release(x_663, 3);
 x_685 = x_663;
} else {
 lean_dec_ref(x_663);
 x_685 = lean_box(0);
}
x_686 = 1;
x_687 = 0;
x_688 = 0;
x_689 = 0;
if (lean_is_scalar(x_685)) {
 x_690 = lean_alloc_ctor(1, 4, 8);
} else {
 x_690 = x_685;
}
lean_ctor_set(x_690, 0, x_645);
lean_ctor_set(x_690, 1, x_646);
lean_ctor_set(x_690, 2, x_647);
lean_ctor_set(x_690, 3, x_662);
lean_ctor_set_uint8(x_690, sizeof(void*)*4 + 6, x_686);
lean_ctor_set_uint32(x_690, sizeof(void*)*4, x_687);
lean_ctor_set_uint16(x_690, sizeof(void*)*4 + 4, x_688);
lean_ctor_set_uint8(x_690, sizeof(void*)*4 + 7, x_689);
x_691 = 0;
x_692 = 0;
x_693 = 0;
if (lean_is_scalar(x_680)) {
 x_694 = lean_alloc_ctor(1, 4, 8);
} else {
 x_694 = x_680;
}
lean_ctor_set(x_694, 0, x_681);
lean_ctor_set(x_694, 1, x_682);
lean_ctor_set(x_694, 2, x_683);
lean_ctor_set(x_694, 3, x_684);
lean_ctor_set_uint8(x_694, sizeof(void*)*4 + 6, x_686);
lean_ctor_set_uint32(x_694, sizeof(void*)*4, x_691);
lean_ctor_set_uint16(x_694, sizeof(void*)*4 + 4, x_692);
lean_ctor_set_uint8(x_694, sizeof(void*)*4 + 7, x_693);
x_695 = 0;
x_696 = 0;
x_697 = 0;
x_698 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_698, 0, x_690);
lean_ctor_set(x_698, 1, x_678);
lean_ctor_set(x_698, 2, x_679);
lean_ctor_set(x_698, 3, x_694);
lean_ctor_set_uint8(x_698, sizeof(void*)*4 + 6, x_677);
lean_ctor_set_uint32(x_698, sizeof(void*)*4, x_695);
lean_ctor_set_uint16(x_698, sizeof(void*)*4 + 4, x_696);
lean_ctor_set_uint8(x_698, sizeof(void*)*4 + 7, x_697);
return x_698;
}
else
{
lean_object* x_699; lean_object* x_700; lean_object* x_701; uint8_t x_702; uint32_t x_703; uint16_t x_704; uint8_t x_705; lean_object* x_706; uint32_t x_707; uint16_t x_708; uint8_t x_709; lean_object* x_710; 
x_699 = lean_ctor_get(x_661, 1);
lean_inc(x_699);
x_700 = lean_ctor_get(x_661, 2);
lean_inc(x_700);
if (lean_is_exclusive(x_661)) {
 lean_ctor_release(x_661, 0);
 lean_ctor_release(x_661, 1);
 lean_ctor_release(x_661, 2);
 lean_ctor_release(x_661, 3);
 x_701 = x_661;
} else {
 lean_dec_ref(x_661);
 x_701 = lean_box(0);
}
x_702 = 0;
x_703 = 0;
x_704 = 0;
x_705 = 0;
if (lean_is_scalar(x_701)) {
 x_706 = lean_alloc_ctor(1, 4, 8);
} else {
 x_706 = x_701;
}
lean_ctor_set(x_706, 0, x_662);
lean_ctor_set(x_706, 1, x_699);
lean_ctor_set(x_706, 2, x_700);
lean_ctor_set(x_706, 3, x_663);
lean_ctor_set_uint8(x_706, sizeof(void*)*4 + 6, x_702);
lean_ctor_set_uint32(x_706, sizeof(void*)*4, x_703);
lean_ctor_set_uint16(x_706, sizeof(void*)*4 + 4, x_704);
lean_ctor_set_uint8(x_706, sizeof(void*)*4 + 7, x_705);
x_707 = 0;
x_708 = 0;
x_709 = 0;
x_710 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_710, 0, x_645);
lean_ctor_set(x_710, 1, x_646);
lean_ctor_set(x_710, 2, x_647);
lean_ctor_set(x_710, 3, x_706);
lean_ctor_set_uint8(x_710, sizeof(void*)*4 + 6, x_677);
lean_ctor_set_uint32(x_710, sizeof(void*)*4, x_707);
lean_ctor_set_uint16(x_710, sizeof(void*)*4 + 4, x_708);
lean_ctor_set_uint8(x_710, sizeof(void*)*4 + 7, x_709);
return x_710;
}
}
}
else
{
uint8_t x_711; 
x_711 = lean_ctor_get_uint8(x_662, sizeof(void*)*4 + 6);
if (x_711 == 0)
{
lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; uint8_t x_721; uint32_t x_722; uint16_t x_723; uint8_t x_724; lean_object* x_725; uint32_t x_726; uint16_t x_727; uint8_t x_728; lean_object* x_729; uint32_t x_730; uint16_t x_731; uint8_t x_732; lean_object* x_733; 
x_712 = lean_ctor_get(x_661, 1);
lean_inc(x_712);
x_713 = lean_ctor_get(x_661, 2);
lean_inc(x_713);
x_714 = lean_ctor_get(x_661, 3);
lean_inc(x_714);
if (lean_is_exclusive(x_661)) {
 lean_ctor_release(x_661, 0);
 lean_ctor_release(x_661, 1);
 lean_ctor_release(x_661, 2);
 lean_ctor_release(x_661, 3);
 x_715 = x_661;
} else {
 lean_dec_ref(x_661);
 x_715 = lean_box(0);
}
x_716 = lean_ctor_get(x_662, 0);
lean_inc(x_716);
x_717 = lean_ctor_get(x_662, 1);
lean_inc(x_717);
x_718 = lean_ctor_get(x_662, 2);
lean_inc(x_718);
x_719 = lean_ctor_get(x_662, 3);
lean_inc(x_719);
if (lean_is_exclusive(x_662)) {
 lean_ctor_release(x_662, 0);
 lean_ctor_release(x_662, 1);
 lean_ctor_release(x_662, 2);
 lean_ctor_release(x_662, 3);
 x_720 = x_662;
} else {
 lean_dec_ref(x_662);
 x_720 = lean_box(0);
}
x_721 = 1;
x_722 = 0;
x_723 = 0;
x_724 = 0;
if (lean_is_scalar(x_720)) {
 x_725 = lean_alloc_ctor(1, 4, 8);
} else {
 x_725 = x_720;
}
lean_ctor_set(x_725, 0, x_645);
lean_ctor_set(x_725, 1, x_646);
lean_ctor_set(x_725, 2, x_647);
lean_ctor_set(x_725, 3, x_716);
lean_ctor_set_uint8(x_725, sizeof(void*)*4 + 6, x_721);
lean_ctor_set_uint32(x_725, sizeof(void*)*4, x_722);
lean_ctor_set_uint16(x_725, sizeof(void*)*4 + 4, x_723);
lean_ctor_set_uint8(x_725, sizeof(void*)*4 + 7, x_724);
x_726 = 0;
x_727 = 0;
x_728 = 0;
if (lean_is_scalar(x_715)) {
 x_729 = lean_alloc_ctor(1, 4, 8);
} else {
 x_729 = x_715;
}
lean_ctor_set(x_729, 0, x_719);
lean_ctor_set(x_729, 1, x_712);
lean_ctor_set(x_729, 2, x_713);
lean_ctor_set(x_729, 3, x_714);
lean_ctor_set_uint8(x_729, sizeof(void*)*4 + 6, x_721);
lean_ctor_set_uint32(x_729, sizeof(void*)*4, x_726);
lean_ctor_set_uint16(x_729, sizeof(void*)*4 + 4, x_727);
lean_ctor_set_uint8(x_729, sizeof(void*)*4 + 7, x_728);
x_730 = 0;
x_731 = 0;
x_732 = 0;
x_733 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_733, 0, x_725);
lean_ctor_set(x_733, 1, x_717);
lean_ctor_set(x_733, 2, x_718);
lean_ctor_set(x_733, 3, x_729);
lean_ctor_set_uint8(x_733, sizeof(void*)*4 + 6, x_711);
lean_ctor_set_uint32(x_733, sizeof(void*)*4, x_730);
lean_ctor_set_uint16(x_733, sizeof(void*)*4 + 4, x_731);
lean_ctor_set_uint8(x_733, sizeof(void*)*4 + 7, x_732);
return x_733;
}
else
{
lean_object* x_734; 
x_734 = lean_ctor_get(x_661, 3);
lean_inc(x_734);
if (lean_obj_tag(x_734) == 0)
{
lean_object* x_735; lean_object* x_736; lean_object* x_737; uint8_t x_738; uint32_t x_739; uint16_t x_740; uint8_t x_741; lean_object* x_742; uint32_t x_743; uint16_t x_744; uint8_t x_745; lean_object* x_746; 
x_735 = lean_ctor_get(x_661, 1);
lean_inc(x_735);
x_736 = lean_ctor_get(x_661, 2);
lean_inc(x_736);
if (lean_is_exclusive(x_661)) {
 lean_ctor_release(x_661, 0);
 lean_ctor_release(x_661, 1);
 lean_ctor_release(x_661, 2);
 lean_ctor_release(x_661, 3);
 x_737 = x_661;
} else {
 lean_dec_ref(x_661);
 x_737 = lean_box(0);
}
x_738 = 0;
x_739 = 0;
x_740 = 0;
x_741 = 0;
if (lean_is_scalar(x_737)) {
 x_742 = lean_alloc_ctor(1, 4, 8);
} else {
 x_742 = x_737;
}
lean_ctor_set(x_742, 0, x_662);
lean_ctor_set(x_742, 1, x_735);
lean_ctor_set(x_742, 2, x_736);
lean_ctor_set(x_742, 3, x_734);
lean_ctor_set_uint8(x_742, sizeof(void*)*4 + 6, x_738);
lean_ctor_set_uint32(x_742, sizeof(void*)*4, x_739);
lean_ctor_set_uint16(x_742, sizeof(void*)*4 + 4, x_740);
lean_ctor_set_uint8(x_742, sizeof(void*)*4 + 7, x_741);
x_743 = 0;
x_744 = 0;
x_745 = 0;
x_746 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_746, 0, x_645);
lean_ctor_set(x_746, 1, x_646);
lean_ctor_set(x_746, 2, x_647);
lean_ctor_set(x_746, 3, x_742);
lean_ctor_set_uint8(x_746, sizeof(void*)*4 + 6, x_711);
lean_ctor_set_uint32(x_746, sizeof(void*)*4, x_743);
lean_ctor_set_uint16(x_746, sizeof(void*)*4 + 4, x_744);
lean_ctor_set_uint8(x_746, sizeof(void*)*4 + 7, x_745);
return x_746;
}
else
{
uint8_t x_747; 
x_747 = lean_ctor_get_uint8(x_734, sizeof(void*)*4 + 6);
if (x_747 == 0)
{
lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; uint32_t x_756; uint16_t x_757; uint8_t x_758; lean_object* x_759; lean_object* x_760; uint32_t x_761; uint16_t x_762; uint8_t x_763; lean_object* x_764; uint32_t x_765; uint16_t x_766; uint8_t x_767; lean_object* x_768; 
x_748 = lean_ctor_get(x_661, 1);
lean_inc(x_748);
x_749 = lean_ctor_get(x_661, 2);
lean_inc(x_749);
if (lean_is_exclusive(x_661)) {
 lean_ctor_release(x_661, 0);
 lean_ctor_release(x_661, 1);
 lean_ctor_release(x_661, 2);
 lean_ctor_release(x_661, 3);
 x_750 = x_661;
} else {
 lean_dec_ref(x_661);
 x_750 = lean_box(0);
}
x_751 = lean_ctor_get(x_734, 0);
lean_inc(x_751);
x_752 = lean_ctor_get(x_734, 1);
lean_inc(x_752);
x_753 = lean_ctor_get(x_734, 2);
lean_inc(x_753);
x_754 = lean_ctor_get(x_734, 3);
lean_inc(x_754);
if (lean_is_exclusive(x_734)) {
 lean_ctor_release(x_734, 0);
 lean_ctor_release(x_734, 1);
 lean_ctor_release(x_734, 2);
 lean_ctor_release(x_734, 3);
 x_755 = x_734;
} else {
 lean_dec_ref(x_734);
 x_755 = lean_box(0);
}
x_756 = 0;
x_757 = 0;
x_758 = 0;
lean_inc(x_662);
if (lean_is_scalar(x_755)) {
 x_759 = lean_alloc_ctor(1, 4, 8);
} else {
 x_759 = x_755;
}
lean_ctor_set(x_759, 0, x_645);
lean_ctor_set(x_759, 1, x_646);
lean_ctor_set(x_759, 2, x_647);
lean_ctor_set(x_759, 3, x_662);
if (lean_is_exclusive(x_662)) {
 lean_ctor_release(x_662, 0);
 lean_ctor_release(x_662, 1);
 lean_ctor_release(x_662, 2);
 lean_ctor_release(x_662, 3);
 x_760 = x_662;
} else {
 lean_dec_ref(x_662);
 x_760 = lean_box(0);
}
lean_ctor_set_uint8(x_759, sizeof(void*)*4 + 6, x_711);
lean_ctor_set_uint32(x_759, sizeof(void*)*4, x_756);
lean_ctor_set_uint16(x_759, sizeof(void*)*4 + 4, x_757);
lean_ctor_set_uint8(x_759, sizeof(void*)*4 + 7, x_758);
x_761 = 0;
x_762 = 0;
x_763 = 0;
if (lean_is_scalar(x_760)) {
 x_764 = lean_alloc_ctor(1, 4, 8);
} else {
 x_764 = x_760;
}
lean_ctor_set(x_764, 0, x_751);
lean_ctor_set(x_764, 1, x_752);
lean_ctor_set(x_764, 2, x_753);
lean_ctor_set(x_764, 3, x_754);
lean_ctor_set_uint8(x_764, sizeof(void*)*4 + 6, x_711);
lean_ctor_set_uint32(x_764, sizeof(void*)*4, x_761);
lean_ctor_set_uint16(x_764, sizeof(void*)*4 + 4, x_762);
lean_ctor_set_uint8(x_764, sizeof(void*)*4 + 7, x_763);
x_765 = 0;
x_766 = 0;
x_767 = 0;
if (lean_is_scalar(x_750)) {
 x_768 = lean_alloc_ctor(1, 4, 8);
} else {
 x_768 = x_750;
}
lean_ctor_set(x_768, 0, x_759);
lean_ctor_set(x_768, 1, x_748);
lean_ctor_set(x_768, 2, x_749);
lean_ctor_set(x_768, 3, x_764);
lean_ctor_set_uint8(x_768, sizeof(void*)*4 + 6, x_747);
lean_ctor_set_uint32(x_768, sizeof(void*)*4, x_765);
lean_ctor_set_uint16(x_768, sizeof(void*)*4 + 4, x_766);
lean_ctor_set_uint8(x_768, sizeof(void*)*4 + 7, x_767);
return x_768;
}
else
{
lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; uint32_t x_777; uint16_t x_778; uint8_t x_779; lean_object* x_780; uint8_t x_781; uint32_t x_782; uint16_t x_783; uint8_t x_784; lean_object* x_785; uint32_t x_786; uint16_t x_787; uint8_t x_788; lean_object* x_789; 
x_769 = lean_ctor_get(x_661, 1);
lean_inc(x_769);
x_770 = lean_ctor_get(x_661, 2);
lean_inc(x_770);
if (lean_is_exclusive(x_661)) {
 lean_ctor_release(x_661, 0);
 lean_ctor_release(x_661, 1);
 lean_ctor_release(x_661, 2);
 lean_ctor_release(x_661, 3);
 x_771 = x_661;
} else {
 lean_dec_ref(x_661);
 x_771 = lean_box(0);
}
x_772 = lean_ctor_get(x_662, 0);
lean_inc(x_772);
x_773 = lean_ctor_get(x_662, 1);
lean_inc(x_773);
x_774 = lean_ctor_get(x_662, 2);
lean_inc(x_774);
x_775 = lean_ctor_get(x_662, 3);
lean_inc(x_775);
if (lean_is_exclusive(x_662)) {
 lean_ctor_release(x_662, 0);
 lean_ctor_release(x_662, 1);
 lean_ctor_release(x_662, 2);
 lean_ctor_release(x_662, 3);
 x_776 = x_662;
} else {
 lean_dec_ref(x_662);
 x_776 = lean_box(0);
}
x_777 = 0;
x_778 = 0;
x_779 = 0;
if (lean_is_scalar(x_776)) {
 x_780 = lean_alloc_ctor(1, 4, 8);
} else {
 x_780 = x_776;
}
lean_ctor_set(x_780, 0, x_772);
lean_ctor_set(x_780, 1, x_773);
lean_ctor_set(x_780, 2, x_774);
lean_ctor_set(x_780, 3, x_775);
lean_ctor_set_uint8(x_780, sizeof(void*)*4 + 6, x_747);
lean_ctor_set_uint32(x_780, sizeof(void*)*4, x_777);
lean_ctor_set_uint16(x_780, sizeof(void*)*4 + 4, x_778);
lean_ctor_set_uint8(x_780, sizeof(void*)*4 + 7, x_779);
x_781 = 0;
x_782 = 0;
x_783 = 0;
x_784 = 0;
if (lean_is_scalar(x_771)) {
 x_785 = lean_alloc_ctor(1, 4, 8);
} else {
 x_785 = x_771;
}
lean_ctor_set(x_785, 0, x_780);
lean_ctor_set(x_785, 1, x_769);
lean_ctor_set(x_785, 2, x_770);
lean_ctor_set(x_785, 3, x_734);
lean_ctor_set_uint8(x_785, sizeof(void*)*4 + 6, x_781);
lean_ctor_set_uint32(x_785, sizeof(void*)*4, x_782);
lean_ctor_set_uint16(x_785, sizeof(void*)*4 + 4, x_783);
lean_ctor_set_uint8(x_785, sizeof(void*)*4 + 7, x_784);
x_786 = 0;
x_787 = 0;
x_788 = 0;
x_789 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_789, 0, x_645);
lean_ctor_set(x_789, 1, x_646);
lean_ctor_set(x_789, 2, x_647);
lean_ctor_set(x_789, 3, x_785);
lean_ctor_set_uint8(x_789, sizeof(void*)*4 + 6, x_747);
lean_ctor_set_uint32(x_789, sizeof(void*)*4, x_786);
lean_ctor_set_uint16(x_789, sizeof(void*)*4 + 4, x_787);
lean_ctor_set_uint8(x_789, sizeof(void*)*4 + 7, x_788);
return x_789;
}
}
}
}
}
}
}
else
{
uint8_t x_790; 
x_790 = l_RBNode_isRed___rarg(x_645);
if (x_790 == 0)
{
lean_object* x_791; uint32_t x_792; uint16_t x_793; uint8_t x_794; lean_object* x_795; 
x_791 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_645, x_2, x_3);
x_792 = 0;
x_793 = 0;
x_794 = 0;
x_795 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_795, 0, x_791);
lean_ctor_set(x_795, 1, x_646);
lean_ctor_set(x_795, 2, x_647);
lean_ctor_set(x_795, 3, x_648);
lean_ctor_set_uint8(x_795, sizeof(void*)*4 + 6, x_9);
lean_ctor_set_uint32(x_795, sizeof(void*)*4, x_792);
lean_ctor_set_uint16(x_795, sizeof(void*)*4 + 4, x_793);
lean_ctor_set_uint8(x_795, sizeof(void*)*4 + 7, x_794);
return x_795;
}
else
{
lean_object* x_796; lean_object* x_797; 
x_796 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_645, x_2, x_3);
x_797 = lean_ctor_get(x_796, 0);
lean_inc(x_797);
if (lean_obj_tag(x_797) == 0)
{
lean_object* x_798; 
x_798 = lean_ctor_get(x_796, 3);
lean_inc(x_798);
if (lean_obj_tag(x_798) == 0)
{
lean_object* x_799; lean_object* x_800; lean_object* x_801; uint8_t x_802; uint32_t x_803; uint16_t x_804; uint8_t x_805; lean_object* x_806; uint8_t x_807; uint32_t x_808; uint16_t x_809; uint8_t x_810; lean_object* x_811; 
x_799 = lean_ctor_get(x_796, 1);
lean_inc(x_799);
x_800 = lean_ctor_get(x_796, 2);
lean_inc(x_800);
if (lean_is_exclusive(x_796)) {
 lean_ctor_release(x_796, 0);
 lean_ctor_release(x_796, 1);
 lean_ctor_release(x_796, 2);
 lean_ctor_release(x_796, 3);
 x_801 = x_796;
} else {
 lean_dec_ref(x_796);
 x_801 = lean_box(0);
}
x_802 = 0;
x_803 = 0;
x_804 = 0;
x_805 = 0;
if (lean_is_scalar(x_801)) {
 x_806 = lean_alloc_ctor(1, 4, 8);
} else {
 x_806 = x_801;
}
lean_ctor_set(x_806, 0, x_798);
lean_ctor_set(x_806, 1, x_799);
lean_ctor_set(x_806, 2, x_800);
lean_ctor_set(x_806, 3, x_798);
lean_ctor_set_uint8(x_806, sizeof(void*)*4 + 6, x_802);
lean_ctor_set_uint32(x_806, sizeof(void*)*4, x_803);
lean_ctor_set_uint16(x_806, sizeof(void*)*4 + 4, x_804);
lean_ctor_set_uint8(x_806, sizeof(void*)*4 + 7, x_805);
x_807 = 1;
x_808 = 0;
x_809 = 0;
x_810 = 0;
x_811 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_811, 0, x_806);
lean_ctor_set(x_811, 1, x_646);
lean_ctor_set(x_811, 2, x_647);
lean_ctor_set(x_811, 3, x_648);
lean_ctor_set_uint8(x_811, sizeof(void*)*4 + 6, x_807);
lean_ctor_set_uint32(x_811, sizeof(void*)*4, x_808);
lean_ctor_set_uint16(x_811, sizeof(void*)*4 + 4, x_809);
lean_ctor_set_uint8(x_811, sizeof(void*)*4 + 7, x_810);
return x_811;
}
else
{
uint8_t x_812; 
x_812 = lean_ctor_get_uint8(x_798, sizeof(void*)*4 + 6);
if (x_812 == 0)
{
lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; uint8_t x_821; uint32_t x_822; uint16_t x_823; uint8_t x_824; lean_object* x_825; uint32_t x_826; uint16_t x_827; uint8_t x_828; lean_object* x_829; uint32_t x_830; uint16_t x_831; uint8_t x_832; lean_object* x_833; 
x_813 = lean_ctor_get(x_796, 1);
lean_inc(x_813);
x_814 = lean_ctor_get(x_796, 2);
lean_inc(x_814);
if (lean_is_exclusive(x_796)) {
 lean_ctor_release(x_796, 0);
 lean_ctor_release(x_796, 1);
 lean_ctor_release(x_796, 2);
 lean_ctor_release(x_796, 3);
 x_815 = x_796;
} else {
 lean_dec_ref(x_796);
 x_815 = lean_box(0);
}
x_816 = lean_ctor_get(x_798, 0);
lean_inc(x_816);
x_817 = lean_ctor_get(x_798, 1);
lean_inc(x_817);
x_818 = lean_ctor_get(x_798, 2);
lean_inc(x_818);
x_819 = lean_ctor_get(x_798, 3);
lean_inc(x_819);
if (lean_is_exclusive(x_798)) {
 lean_ctor_release(x_798, 0);
 lean_ctor_release(x_798, 1);
 lean_ctor_release(x_798, 2);
 lean_ctor_release(x_798, 3);
 x_820 = x_798;
} else {
 lean_dec_ref(x_798);
 x_820 = lean_box(0);
}
x_821 = 1;
x_822 = 0;
x_823 = 0;
x_824 = 0;
if (lean_is_scalar(x_820)) {
 x_825 = lean_alloc_ctor(1, 4, 8);
} else {
 x_825 = x_820;
}
lean_ctor_set(x_825, 0, x_797);
lean_ctor_set(x_825, 1, x_813);
lean_ctor_set(x_825, 2, x_814);
lean_ctor_set(x_825, 3, x_816);
lean_ctor_set_uint8(x_825, sizeof(void*)*4 + 6, x_821);
lean_ctor_set_uint32(x_825, sizeof(void*)*4, x_822);
lean_ctor_set_uint16(x_825, sizeof(void*)*4 + 4, x_823);
lean_ctor_set_uint8(x_825, sizeof(void*)*4 + 7, x_824);
x_826 = 0;
x_827 = 0;
x_828 = 0;
if (lean_is_scalar(x_815)) {
 x_829 = lean_alloc_ctor(1, 4, 8);
} else {
 x_829 = x_815;
}
lean_ctor_set(x_829, 0, x_819);
lean_ctor_set(x_829, 1, x_646);
lean_ctor_set(x_829, 2, x_647);
lean_ctor_set(x_829, 3, x_648);
lean_ctor_set_uint8(x_829, sizeof(void*)*4 + 6, x_821);
lean_ctor_set_uint32(x_829, sizeof(void*)*4, x_826);
lean_ctor_set_uint16(x_829, sizeof(void*)*4 + 4, x_827);
lean_ctor_set_uint8(x_829, sizeof(void*)*4 + 7, x_828);
x_830 = 0;
x_831 = 0;
x_832 = 0;
x_833 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_833, 0, x_825);
lean_ctor_set(x_833, 1, x_817);
lean_ctor_set(x_833, 2, x_818);
lean_ctor_set(x_833, 3, x_829);
lean_ctor_set_uint8(x_833, sizeof(void*)*4 + 6, x_812);
lean_ctor_set_uint32(x_833, sizeof(void*)*4, x_830);
lean_ctor_set_uint16(x_833, sizeof(void*)*4 + 4, x_831);
lean_ctor_set_uint8(x_833, sizeof(void*)*4 + 7, x_832);
return x_833;
}
else
{
lean_object* x_834; lean_object* x_835; lean_object* x_836; uint8_t x_837; uint32_t x_838; uint16_t x_839; uint8_t x_840; lean_object* x_841; uint32_t x_842; uint16_t x_843; uint8_t x_844; lean_object* x_845; 
x_834 = lean_ctor_get(x_796, 1);
lean_inc(x_834);
x_835 = lean_ctor_get(x_796, 2);
lean_inc(x_835);
if (lean_is_exclusive(x_796)) {
 lean_ctor_release(x_796, 0);
 lean_ctor_release(x_796, 1);
 lean_ctor_release(x_796, 2);
 lean_ctor_release(x_796, 3);
 x_836 = x_796;
} else {
 lean_dec_ref(x_796);
 x_836 = lean_box(0);
}
x_837 = 0;
x_838 = 0;
x_839 = 0;
x_840 = 0;
if (lean_is_scalar(x_836)) {
 x_841 = lean_alloc_ctor(1, 4, 8);
} else {
 x_841 = x_836;
}
lean_ctor_set(x_841, 0, x_797);
lean_ctor_set(x_841, 1, x_834);
lean_ctor_set(x_841, 2, x_835);
lean_ctor_set(x_841, 3, x_798);
lean_ctor_set_uint8(x_841, sizeof(void*)*4 + 6, x_837);
lean_ctor_set_uint32(x_841, sizeof(void*)*4, x_838);
lean_ctor_set_uint16(x_841, sizeof(void*)*4 + 4, x_839);
lean_ctor_set_uint8(x_841, sizeof(void*)*4 + 7, x_840);
x_842 = 0;
x_843 = 0;
x_844 = 0;
x_845 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_845, 0, x_841);
lean_ctor_set(x_845, 1, x_646);
lean_ctor_set(x_845, 2, x_647);
lean_ctor_set(x_845, 3, x_648);
lean_ctor_set_uint8(x_845, sizeof(void*)*4 + 6, x_812);
lean_ctor_set_uint32(x_845, sizeof(void*)*4, x_842);
lean_ctor_set_uint16(x_845, sizeof(void*)*4 + 4, x_843);
lean_ctor_set_uint8(x_845, sizeof(void*)*4 + 7, x_844);
return x_845;
}
}
}
else
{
uint8_t x_846; 
x_846 = lean_ctor_get_uint8(x_797, sizeof(void*)*4 + 6);
if (x_846 == 0)
{
lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; uint8_t x_856; uint32_t x_857; uint16_t x_858; uint8_t x_859; lean_object* x_860; uint32_t x_861; uint16_t x_862; uint8_t x_863; lean_object* x_864; uint32_t x_865; uint16_t x_866; uint8_t x_867; lean_object* x_868; 
x_847 = lean_ctor_get(x_796, 1);
lean_inc(x_847);
x_848 = lean_ctor_get(x_796, 2);
lean_inc(x_848);
x_849 = lean_ctor_get(x_796, 3);
lean_inc(x_849);
if (lean_is_exclusive(x_796)) {
 lean_ctor_release(x_796, 0);
 lean_ctor_release(x_796, 1);
 lean_ctor_release(x_796, 2);
 lean_ctor_release(x_796, 3);
 x_850 = x_796;
} else {
 lean_dec_ref(x_796);
 x_850 = lean_box(0);
}
x_851 = lean_ctor_get(x_797, 0);
lean_inc(x_851);
x_852 = lean_ctor_get(x_797, 1);
lean_inc(x_852);
x_853 = lean_ctor_get(x_797, 2);
lean_inc(x_853);
x_854 = lean_ctor_get(x_797, 3);
lean_inc(x_854);
if (lean_is_exclusive(x_797)) {
 lean_ctor_release(x_797, 0);
 lean_ctor_release(x_797, 1);
 lean_ctor_release(x_797, 2);
 lean_ctor_release(x_797, 3);
 x_855 = x_797;
} else {
 lean_dec_ref(x_797);
 x_855 = lean_box(0);
}
x_856 = 1;
x_857 = 0;
x_858 = 0;
x_859 = 0;
if (lean_is_scalar(x_855)) {
 x_860 = lean_alloc_ctor(1, 4, 8);
} else {
 x_860 = x_855;
}
lean_ctor_set(x_860, 0, x_851);
lean_ctor_set(x_860, 1, x_852);
lean_ctor_set(x_860, 2, x_853);
lean_ctor_set(x_860, 3, x_854);
lean_ctor_set_uint8(x_860, sizeof(void*)*4 + 6, x_856);
lean_ctor_set_uint32(x_860, sizeof(void*)*4, x_857);
lean_ctor_set_uint16(x_860, sizeof(void*)*4 + 4, x_858);
lean_ctor_set_uint8(x_860, sizeof(void*)*4 + 7, x_859);
x_861 = 0;
x_862 = 0;
x_863 = 0;
if (lean_is_scalar(x_850)) {
 x_864 = lean_alloc_ctor(1, 4, 8);
} else {
 x_864 = x_850;
}
lean_ctor_set(x_864, 0, x_849);
lean_ctor_set(x_864, 1, x_646);
lean_ctor_set(x_864, 2, x_647);
lean_ctor_set(x_864, 3, x_648);
lean_ctor_set_uint8(x_864, sizeof(void*)*4 + 6, x_856);
lean_ctor_set_uint32(x_864, sizeof(void*)*4, x_861);
lean_ctor_set_uint16(x_864, sizeof(void*)*4 + 4, x_862);
lean_ctor_set_uint8(x_864, sizeof(void*)*4 + 7, x_863);
x_865 = 0;
x_866 = 0;
x_867 = 0;
x_868 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_868, 0, x_860);
lean_ctor_set(x_868, 1, x_847);
lean_ctor_set(x_868, 2, x_848);
lean_ctor_set(x_868, 3, x_864);
lean_ctor_set_uint8(x_868, sizeof(void*)*4 + 6, x_846);
lean_ctor_set_uint32(x_868, sizeof(void*)*4, x_865);
lean_ctor_set_uint16(x_868, sizeof(void*)*4 + 4, x_866);
lean_ctor_set_uint8(x_868, sizeof(void*)*4 + 7, x_867);
return x_868;
}
else
{
lean_object* x_869; 
x_869 = lean_ctor_get(x_796, 3);
lean_inc(x_869);
if (lean_obj_tag(x_869) == 0)
{
lean_object* x_870; lean_object* x_871; lean_object* x_872; uint8_t x_873; uint32_t x_874; uint16_t x_875; uint8_t x_876; lean_object* x_877; uint32_t x_878; uint16_t x_879; uint8_t x_880; lean_object* x_881; 
x_870 = lean_ctor_get(x_796, 1);
lean_inc(x_870);
x_871 = lean_ctor_get(x_796, 2);
lean_inc(x_871);
if (lean_is_exclusive(x_796)) {
 lean_ctor_release(x_796, 0);
 lean_ctor_release(x_796, 1);
 lean_ctor_release(x_796, 2);
 lean_ctor_release(x_796, 3);
 x_872 = x_796;
} else {
 lean_dec_ref(x_796);
 x_872 = lean_box(0);
}
x_873 = 0;
x_874 = 0;
x_875 = 0;
x_876 = 0;
if (lean_is_scalar(x_872)) {
 x_877 = lean_alloc_ctor(1, 4, 8);
} else {
 x_877 = x_872;
}
lean_ctor_set(x_877, 0, x_797);
lean_ctor_set(x_877, 1, x_870);
lean_ctor_set(x_877, 2, x_871);
lean_ctor_set(x_877, 3, x_869);
lean_ctor_set_uint8(x_877, sizeof(void*)*4 + 6, x_873);
lean_ctor_set_uint32(x_877, sizeof(void*)*4, x_874);
lean_ctor_set_uint16(x_877, sizeof(void*)*4 + 4, x_875);
lean_ctor_set_uint8(x_877, sizeof(void*)*4 + 7, x_876);
x_878 = 0;
x_879 = 0;
x_880 = 0;
x_881 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_881, 0, x_877);
lean_ctor_set(x_881, 1, x_646);
lean_ctor_set(x_881, 2, x_647);
lean_ctor_set(x_881, 3, x_648);
lean_ctor_set_uint8(x_881, sizeof(void*)*4 + 6, x_846);
lean_ctor_set_uint32(x_881, sizeof(void*)*4, x_878);
lean_ctor_set_uint16(x_881, sizeof(void*)*4 + 4, x_879);
lean_ctor_set_uint8(x_881, sizeof(void*)*4 + 7, x_880);
return x_881;
}
else
{
uint8_t x_882; 
x_882 = lean_ctor_get_uint8(x_869, sizeof(void*)*4 + 6);
if (x_882 == 0)
{
lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; uint32_t x_891; uint16_t x_892; uint8_t x_893; lean_object* x_894; lean_object* x_895; uint32_t x_896; uint16_t x_897; uint8_t x_898; lean_object* x_899; uint32_t x_900; uint16_t x_901; uint8_t x_902; lean_object* x_903; 
x_883 = lean_ctor_get(x_796, 1);
lean_inc(x_883);
x_884 = lean_ctor_get(x_796, 2);
lean_inc(x_884);
if (lean_is_exclusive(x_796)) {
 lean_ctor_release(x_796, 0);
 lean_ctor_release(x_796, 1);
 lean_ctor_release(x_796, 2);
 lean_ctor_release(x_796, 3);
 x_885 = x_796;
} else {
 lean_dec_ref(x_796);
 x_885 = lean_box(0);
}
x_886 = lean_ctor_get(x_869, 0);
lean_inc(x_886);
x_887 = lean_ctor_get(x_869, 1);
lean_inc(x_887);
x_888 = lean_ctor_get(x_869, 2);
lean_inc(x_888);
x_889 = lean_ctor_get(x_869, 3);
lean_inc(x_889);
if (lean_is_exclusive(x_869)) {
 lean_ctor_release(x_869, 0);
 lean_ctor_release(x_869, 1);
 lean_ctor_release(x_869, 2);
 lean_ctor_release(x_869, 3);
 x_890 = x_869;
} else {
 lean_dec_ref(x_869);
 x_890 = lean_box(0);
}
x_891 = 0;
x_892 = 0;
x_893 = 0;
lean_inc(x_797);
if (lean_is_scalar(x_890)) {
 x_894 = lean_alloc_ctor(1, 4, 8);
} else {
 x_894 = x_890;
}
lean_ctor_set(x_894, 0, x_797);
lean_ctor_set(x_894, 1, x_883);
lean_ctor_set(x_894, 2, x_884);
lean_ctor_set(x_894, 3, x_886);
if (lean_is_exclusive(x_797)) {
 lean_ctor_release(x_797, 0);
 lean_ctor_release(x_797, 1);
 lean_ctor_release(x_797, 2);
 lean_ctor_release(x_797, 3);
 x_895 = x_797;
} else {
 lean_dec_ref(x_797);
 x_895 = lean_box(0);
}
lean_ctor_set_uint8(x_894, sizeof(void*)*4 + 6, x_846);
lean_ctor_set_uint32(x_894, sizeof(void*)*4, x_891);
lean_ctor_set_uint16(x_894, sizeof(void*)*4 + 4, x_892);
lean_ctor_set_uint8(x_894, sizeof(void*)*4 + 7, x_893);
x_896 = 0;
x_897 = 0;
x_898 = 0;
if (lean_is_scalar(x_895)) {
 x_899 = lean_alloc_ctor(1, 4, 8);
} else {
 x_899 = x_895;
}
lean_ctor_set(x_899, 0, x_889);
lean_ctor_set(x_899, 1, x_646);
lean_ctor_set(x_899, 2, x_647);
lean_ctor_set(x_899, 3, x_648);
lean_ctor_set_uint8(x_899, sizeof(void*)*4 + 6, x_846);
lean_ctor_set_uint32(x_899, sizeof(void*)*4, x_896);
lean_ctor_set_uint16(x_899, sizeof(void*)*4 + 4, x_897);
lean_ctor_set_uint8(x_899, sizeof(void*)*4 + 7, x_898);
x_900 = 0;
x_901 = 0;
x_902 = 0;
if (lean_is_scalar(x_885)) {
 x_903 = lean_alloc_ctor(1, 4, 8);
} else {
 x_903 = x_885;
}
lean_ctor_set(x_903, 0, x_894);
lean_ctor_set(x_903, 1, x_887);
lean_ctor_set(x_903, 2, x_888);
lean_ctor_set(x_903, 3, x_899);
lean_ctor_set_uint8(x_903, sizeof(void*)*4 + 6, x_882);
lean_ctor_set_uint32(x_903, sizeof(void*)*4, x_900);
lean_ctor_set_uint16(x_903, sizeof(void*)*4 + 4, x_901);
lean_ctor_set_uint8(x_903, sizeof(void*)*4 + 7, x_902);
return x_903;
}
else
{
lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; uint32_t x_912; uint16_t x_913; uint8_t x_914; lean_object* x_915; uint8_t x_916; uint32_t x_917; uint16_t x_918; uint8_t x_919; lean_object* x_920; uint32_t x_921; uint16_t x_922; uint8_t x_923; lean_object* x_924; 
x_904 = lean_ctor_get(x_796, 1);
lean_inc(x_904);
x_905 = lean_ctor_get(x_796, 2);
lean_inc(x_905);
if (lean_is_exclusive(x_796)) {
 lean_ctor_release(x_796, 0);
 lean_ctor_release(x_796, 1);
 lean_ctor_release(x_796, 2);
 lean_ctor_release(x_796, 3);
 x_906 = x_796;
} else {
 lean_dec_ref(x_796);
 x_906 = lean_box(0);
}
x_907 = lean_ctor_get(x_797, 0);
lean_inc(x_907);
x_908 = lean_ctor_get(x_797, 1);
lean_inc(x_908);
x_909 = lean_ctor_get(x_797, 2);
lean_inc(x_909);
x_910 = lean_ctor_get(x_797, 3);
lean_inc(x_910);
if (lean_is_exclusive(x_797)) {
 lean_ctor_release(x_797, 0);
 lean_ctor_release(x_797, 1);
 lean_ctor_release(x_797, 2);
 lean_ctor_release(x_797, 3);
 x_911 = x_797;
} else {
 lean_dec_ref(x_797);
 x_911 = lean_box(0);
}
x_912 = 0;
x_913 = 0;
x_914 = 0;
if (lean_is_scalar(x_911)) {
 x_915 = lean_alloc_ctor(1, 4, 8);
} else {
 x_915 = x_911;
}
lean_ctor_set(x_915, 0, x_907);
lean_ctor_set(x_915, 1, x_908);
lean_ctor_set(x_915, 2, x_909);
lean_ctor_set(x_915, 3, x_910);
lean_ctor_set_uint8(x_915, sizeof(void*)*4 + 6, x_882);
lean_ctor_set_uint32(x_915, sizeof(void*)*4, x_912);
lean_ctor_set_uint16(x_915, sizeof(void*)*4 + 4, x_913);
lean_ctor_set_uint8(x_915, sizeof(void*)*4 + 7, x_914);
x_916 = 0;
x_917 = 0;
x_918 = 0;
x_919 = 0;
if (lean_is_scalar(x_906)) {
 x_920 = lean_alloc_ctor(1, 4, 8);
} else {
 x_920 = x_906;
}
lean_ctor_set(x_920, 0, x_915);
lean_ctor_set(x_920, 1, x_904);
lean_ctor_set(x_920, 2, x_905);
lean_ctor_set(x_920, 3, x_869);
lean_ctor_set_uint8(x_920, sizeof(void*)*4 + 6, x_916);
lean_ctor_set_uint32(x_920, sizeof(void*)*4, x_917);
lean_ctor_set_uint16(x_920, sizeof(void*)*4 + 4, x_918);
lean_ctor_set_uint8(x_920, sizeof(void*)*4 + 7, x_919);
x_921 = 0;
x_922 = 0;
x_923 = 0;
x_924 = lean_alloc_ctor(1, 4, 8);
lean_ctor_set(x_924, 0, x_920);
lean_ctor_set(x_924, 1, x_646);
lean_ctor_set(x_924, 2, x_647);
lean_ctor_set(x_924, 3, x_648);
lean_ctor_set_uint8(x_924, sizeof(void*)*4 + 6, x_882);
lean_ctor_set_uint32(x_924, sizeof(void*)*4, x_921);
lean_ctor_set_uint16(x_924, sizeof(void*)*4 + 4, x_922);
lean_ctor_set_uint8(x_924, sizeof(void*)*4 + 7, x_923);
return x_924;
}
}
}
}
}
}
}
}
}
}
}
lean_object* l_RBNode_insert___at_Lean_IR_addVarRename___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_RBNode_isRed___rarg(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_1, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_1, x_2, x_3);
x_7 = l_RBNode_setBlack___rarg(x_6);
return x_7;
}
}
}
lean_object* l_Lean_IR_addVarRename(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_RBNode_insert___at_Lean_IR_addVarRename___spec__1(x_1, x_2, x_3);
return x_5;
}
else
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
}
}
lean_object* l_Lean_IR_addParamRename(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = l_Lean_IR_IRType_beq___main(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(0);
return x_7;
}
else
{
uint8_t x_8; uint8_t x_9; uint8_t x_10; 
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 6);
x_9 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 6);
if (x_8 == 0)
{
if (x_9 == 0)
{
uint8_t x_17; 
x_17 = 1;
x_10 = x_17;
goto block_16;
}
else
{
uint8_t x_18; 
x_18 = 0;
x_10 = x_18;
goto block_16;
}
}
else
{
if (x_9 == 0)
{
uint8_t x_19; 
x_19 = 0;
x_10 = x_19;
goto block_16;
}
else
{
uint8_t x_20; 
x_20 = 1;
x_10 = x_20;
goto block_16;
}
}
block_16:
{
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
lean_dec(x_3);
x_14 = l_Lean_IR_addVarRename(x_1, x_12, x_13);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_IR_addParamsRename___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_3);
x_9 = lean_nat_dec_lt(x_4, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_array_fget(x_2, x_4);
x_11 = lean_array_fget(x_3, x_4);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
x_14 = lean_box(0);
x_4 = x_13;
x_5 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
x_17 = l_Lean_IR_addParamRename(x_16, x_10, x_11);
x_4 = x_13;
x_5 = x_17;
goto _start;
}
}
}
}
}
lean_object* l_Lean_IR_addParamsRename(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_array_get_size(x_3);
x_6 = lean_nat_dec_eq(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_1);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_IR_addParamsRename___spec__1(x_2, x_2, x_3, x_9, x_8);
return x_10;
}
}
}
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_IR_addParamsRename___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateM_u2082Aux___main___at_Lean_IR_addParamsRename___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_IR_addParamsRename___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_addParamsRename(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
uint8_t l_Array_isEqvAux___main___at_Lean_IR_FnBody_alphaEqv___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_5);
x_9 = lean_nat_dec_lt(x_7, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_7);
lean_dec(x_1);
x_10 = 1;
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_fget(x_5, x_7);
x_12 = lean_array_fget(x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_dec(x_12);
x_17 = l_Lean_IR_CtorInfo_beq(x_13, x_15);
lean_dec(x_15);
lean_dec(x_13);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_1);
x_18 = 0;
return x_18;
}
else
{
uint8_t x_19; 
lean_inc(x_1);
x_19 = l_Lean_IR_FnBody_alphaEqv___main(x_1, x_14, x_16);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_7);
lean_dec(x_1);
x_20 = 0;
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_7, x_21);
lean_dec(x_7);
x_4 = lean_box(0);
x_7 = x_22;
goto _start;
}
}
}
else
{
uint8_t x_24; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_1);
x_24 = 0;
return x_24;
}
}
else
{
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_25; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_1);
x_25 = 0;
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_11, 0);
lean_inc(x_26);
lean_dec(x_11);
x_27 = lean_ctor_get(x_12, 0);
lean_inc(x_27);
lean_dec(x_12);
lean_inc(x_1);
x_28 = l_Lean_IR_FnBody_alphaEqv___main(x_1, x_26, x_27);
if (x_28 == 0)
{
uint8_t x_29; 
lean_dec(x_7);
lean_dec(x_1);
x_29 = 0;
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_7, x_30);
lean_dec(x_7);
x_4 = lean_box(0);
x_7 = x_31;
goto _start;
}
}
}
}
}
}
uint8_t l_Lean_IR_FnBody_alphaEqv___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 3);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 3);
lean_inc(x_11);
lean_dec(x_3);
x_12 = l_Lean_IR_IRType_beq___main(x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_13 = 0;
return x_13;
}
else
{
uint8_t x_14; 
x_14 = l_Lean_IR_Expr_alphaEqv(x_1, x_6, x_10);
lean_dec(x_10);
lean_dec(x_6);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_15 = 0;
return x_15;
}
else
{
lean_object* x_16; 
x_16 = l_Lean_IR_addVarRename(x_1, x_4, x_8);
x_1 = x_16;
x_2 = x_7;
x_3 = x_11;
goto _start;
}
}
}
else
{
uint8_t x_18; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = 0;
return x_18;
}
}
case 1:
{
if (lean_obj_tag(x_3) == 1)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 3);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_ctor_get(x_3, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_3, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_3, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_3, 3);
lean_inc(x_26);
lean_dec(x_3);
lean_inc(x_1);
x_27 = l_Lean_IR_addParamsRename(x_1, x_20, x_24);
lean_dec(x_24);
lean_dec(x_20);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_1);
x_28 = 0;
return x_28;
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_IR_FnBody_alphaEqv___main(x_29, x_21, x_25);
if (x_30 == 0)
{
uint8_t x_31; 
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_1);
x_31 = 0;
return x_31;
}
else
{
lean_object* x_32; 
x_32 = l_Lean_IR_addVarRename(x_1, x_19, x_23);
x_1 = x_32;
x_2 = x_22;
x_3 = x_26;
goto _start;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_34 = 0;
return x_34;
}
}
case 2:
{
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_35 = lean_ctor_get(x_2, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_2, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_2, 2);
lean_inc(x_37);
x_38 = lean_ctor_get(x_2, 3);
lean_inc(x_38);
lean_dec(x_2);
x_39 = lean_ctor_get(x_3, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_3, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_3, 2);
lean_inc(x_41);
x_42 = lean_ctor_get(x_3, 3);
lean_inc(x_42);
lean_dec(x_3);
x_43 = l_Lean_IR_VarId_alphaEqv(x_1, x_35, x_39);
lean_dec(x_39);
lean_dec(x_35);
if (x_43 == 0)
{
uint8_t x_44; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_1);
x_44 = 0;
return x_44;
}
else
{
uint8_t x_45; 
x_45 = lean_nat_dec_eq(x_36, x_40);
lean_dec(x_40);
lean_dec(x_36);
if (x_45 == 0)
{
uint8_t x_46; 
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_1);
x_46 = 0;
return x_46;
}
else
{
uint8_t x_47; 
x_47 = l_Lean_IR_Arg_alphaEqv(x_1, x_37, x_41);
lean_dec(x_41);
lean_dec(x_37);
if (x_47 == 0)
{
uint8_t x_48; 
lean_dec(x_42);
lean_dec(x_38);
lean_dec(x_1);
x_48 = 0;
return x_48;
}
else
{
x_2 = x_38;
x_3 = x_42;
goto _start;
}
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = 0;
return x_50;
}
}
case 3:
{
if (lean_obj_tag(x_3) == 3)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_51 = lean_ctor_get(x_2, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_2, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_2, 2);
lean_inc(x_53);
lean_dec(x_2);
x_54 = lean_ctor_get(x_3, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_3, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_3, 2);
lean_inc(x_56);
lean_dec(x_3);
x_57 = l_Lean_IR_VarId_alphaEqv(x_1, x_51, x_54);
lean_dec(x_54);
lean_dec(x_51);
if (x_57 == 0)
{
uint8_t x_58; 
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_1);
x_58 = 0;
return x_58;
}
else
{
uint8_t x_59; 
x_59 = lean_nat_dec_eq(x_52, x_55);
lean_dec(x_55);
lean_dec(x_52);
if (x_59 == 0)
{
uint8_t x_60; 
lean_dec(x_56);
lean_dec(x_53);
lean_dec(x_1);
x_60 = 0;
return x_60;
}
else
{
x_2 = x_53;
x_3 = x_56;
goto _start;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_62 = 0;
return x_62;
}
}
case 4:
{
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_63 = lean_ctor_get(x_2, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_2, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_2, 2);
lean_inc(x_65);
x_66 = lean_ctor_get(x_2, 3);
lean_inc(x_66);
lean_dec(x_2);
x_67 = lean_ctor_get(x_3, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_3, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_3, 2);
lean_inc(x_69);
x_70 = lean_ctor_get(x_3, 3);
lean_inc(x_70);
lean_dec(x_3);
x_71 = l_Lean_IR_VarId_alphaEqv(x_1, x_63, x_67);
lean_dec(x_67);
lean_dec(x_63);
if (x_71 == 0)
{
uint8_t x_72; 
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_1);
x_72 = 0;
return x_72;
}
else
{
uint8_t x_73; 
x_73 = lean_nat_dec_eq(x_64, x_68);
lean_dec(x_68);
lean_dec(x_64);
if (x_73 == 0)
{
uint8_t x_74; 
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_1);
x_74 = 0;
return x_74;
}
else
{
uint8_t x_75; 
x_75 = l_Lean_IR_VarId_alphaEqv(x_1, x_65, x_69);
lean_dec(x_69);
lean_dec(x_65);
if (x_75 == 0)
{
uint8_t x_76; 
lean_dec(x_70);
lean_dec(x_66);
lean_dec(x_1);
x_76 = 0;
return x_76;
}
else
{
x_2 = x_66;
x_3 = x_70;
goto _start;
}
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_78 = 0;
return x_78;
}
}
case 5:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_79 = lean_ctor_get(x_2, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_2, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_2, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_2, 3);
lean_inc(x_82);
x_83 = lean_ctor_get(x_2, 4);
lean_inc(x_83);
x_84 = lean_ctor_get(x_2, 5);
lean_inc(x_84);
lean_dec(x_2);
x_85 = lean_ctor_get(x_3, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_3, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_3, 2);
lean_inc(x_87);
x_88 = lean_ctor_get(x_3, 3);
lean_inc(x_88);
x_89 = lean_ctor_get(x_3, 4);
lean_inc(x_89);
x_90 = lean_ctor_get(x_3, 5);
lean_inc(x_90);
lean_dec(x_3);
x_91 = l_Lean_IR_VarId_alphaEqv(x_1, x_79, x_85);
lean_dec(x_85);
lean_dec(x_79);
if (x_91 == 0)
{
uint8_t x_92; 
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_1);
x_92 = 0;
return x_92;
}
else
{
uint8_t x_93; 
x_93 = lean_nat_dec_eq(x_80, x_86);
lean_dec(x_86);
lean_dec(x_80);
if (x_93 == 0)
{
uint8_t x_94; 
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_1);
x_94 = 0;
return x_94;
}
else
{
uint8_t x_95; 
x_95 = lean_nat_dec_eq(x_81, x_87);
lean_dec(x_87);
lean_dec(x_81);
if (x_95 == 0)
{
uint8_t x_96; 
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_1);
x_96 = 0;
return x_96;
}
else
{
uint8_t x_97; 
x_97 = l_Lean_IR_VarId_alphaEqv(x_1, x_82, x_88);
lean_dec(x_88);
lean_dec(x_82);
if (x_97 == 0)
{
uint8_t x_98; 
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_1);
x_98 = 0;
return x_98;
}
else
{
uint8_t x_99; 
x_99 = l_Lean_IR_IRType_beq___main(x_83, x_89);
lean_dec(x_89);
lean_dec(x_83);
if (x_99 == 0)
{
uint8_t x_100; 
lean_dec(x_90);
lean_dec(x_84);
lean_dec(x_1);
x_100 = 0;
return x_100;
}
else
{
x_2 = x_84;
x_3 = x_90;
goto _start;
}
}
}
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_102 = 0;
return x_102;
}
}
case 6:
{
if (lean_obj_tag(x_3) == 6)
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; uint8_t x_111; lean_object* x_112; uint8_t x_113; uint8_t x_120; 
x_103 = lean_ctor_get(x_2, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_2, 1);
lean_inc(x_104);
x_105 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 6);
x_106 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 7);
x_107 = lean_ctor_get(x_2, 2);
lean_inc(x_107);
lean_dec(x_2);
x_108 = lean_ctor_get(x_3, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_3, 1);
lean_inc(x_109);
x_110 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 6);
x_111 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 7);
x_112 = lean_ctor_get(x_3, 2);
lean_inc(x_112);
lean_dec(x_3);
x_120 = l_Lean_IR_VarId_alphaEqv(x_1, x_103, x_108);
lean_dec(x_108);
lean_dec(x_103);
if (x_120 == 0)
{
uint8_t x_121; 
lean_dec(x_112);
lean_dec(x_109);
lean_dec(x_107);
lean_dec(x_104);
lean_dec(x_1);
x_121 = 0;
return x_121;
}
else
{
uint8_t x_122; 
x_122 = lean_nat_dec_eq(x_104, x_109);
lean_dec(x_109);
lean_dec(x_104);
if (x_122 == 0)
{
uint8_t x_123; 
lean_dec(x_112);
lean_dec(x_107);
lean_dec(x_1);
x_123 = 0;
return x_123;
}
else
{
if (x_105 == 0)
{
if (x_110 == 0)
{
uint8_t x_124; 
x_124 = 1;
x_113 = x_124;
goto block_119;
}
else
{
uint8_t x_125; 
x_125 = 0;
x_113 = x_125;
goto block_119;
}
}
else
{
if (x_110 == 0)
{
uint8_t x_126; 
x_126 = 0;
x_113 = x_126;
goto block_119;
}
else
{
uint8_t x_127; 
x_127 = 1;
x_113 = x_127;
goto block_119;
}
}
}
}
block_119:
{
if (x_113 == 0)
{
uint8_t x_114; 
lean_dec(x_112);
lean_dec(x_107);
lean_dec(x_1);
x_114 = 0;
return x_114;
}
else
{
if (x_106 == 0)
{
if (x_111 == 0)
{
x_2 = x_107;
x_3 = x_112;
goto _start;
}
else
{
uint8_t x_116; 
lean_dec(x_112);
lean_dec(x_107);
lean_dec(x_1);
x_116 = 0;
return x_116;
}
}
else
{
if (x_111 == 0)
{
uint8_t x_117; 
lean_dec(x_112);
lean_dec(x_107);
lean_dec(x_1);
x_117 = 0;
return x_117;
}
else
{
x_2 = x_107;
x_3 = x_112;
goto _start;
}
}
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_128 = 0;
return x_128;
}
}
case 7:
{
if (lean_obj_tag(x_3) == 7)
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; uint8_t x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; uint8_t x_137; lean_object* x_138; uint8_t x_139; uint8_t x_146; 
x_129 = lean_ctor_get(x_2, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_2, 1);
lean_inc(x_130);
x_131 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 6);
x_132 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 7);
x_133 = lean_ctor_get(x_2, 2);
lean_inc(x_133);
lean_dec(x_2);
x_134 = lean_ctor_get(x_3, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_3, 1);
lean_inc(x_135);
x_136 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 6);
x_137 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 7);
x_138 = lean_ctor_get(x_3, 2);
lean_inc(x_138);
lean_dec(x_3);
x_146 = l_Lean_IR_VarId_alphaEqv(x_1, x_129, x_134);
lean_dec(x_134);
lean_dec(x_129);
if (x_146 == 0)
{
uint8_t x_147; 
lean_dec(x_138);
lean_dec(x_135);
lean_dec(x_133);
lean_dec(x_130);
lean_dec(x_1);
x_147 = 0;
return x_147;
}
else
{
uint8_t x_148; 
x_148 = lean_nat_dec_eq(x_130, x_135);
lean_dec(x_135);
lean_dec(x_130);
if (x_148 == 0)
{
uint8_t x_149; 
lean_dec(x_138);
lean_dec(x_133);
lean_dec(x_1);
x_149 = 0;
return x_149;
}
else
{
if (x_131 == 0)
{
if (x_136 == 0)
{
uint8_t x_150; 
x_150 = 1;
x_139 = x_150;
goto block_145;
}
else
{
uint8_t x_151; 
x_151 = 0;
x_139 = x_151;
goto block_145;
}
}
else
{
if (x_136 == 0)
{
uint8_t x_152; 
x_152 = 0;
x_139 = x_152;
goto block_145;
}
else
{
uint8_t x_153; 
x_153 = 1;
x_139 = x_153;
goto block_145;
}
}
}
}
block_145:
{
if (x_139 == 0)
{
uint8_t x_140; 
lean_dec(x_138);
lean_dec(x_133);
lean_dec(x_1);
x_140 = 0;
return x_140;
}
else
{
if (x_132 == 0)
{
if (x_137 == 0)
{
x_2 = x_133;
x_3 = x_138;
goto _start;
}
else
{
uint8_t x_142; 
lean_dec(x_138);
lean_dec(x_133);
lean_dec(x_1);
x_142 = 0;
return x_142;
}
}
else
{
if (x_137 == 0)
{
uint8_t x_143; 
lean_dec(x_138);
lean_dec(x_133);
lean_dec(x_1);
x_143 = 0;
return x_143;
}
else
{
x_2 = x_133;
x_3 = x_138;
goto _start;
}
}
}
}
}
else
{
uint8_t x_154; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_154 = 0;
return x_154;
}
}
case 8:
{
if (lean_obj_tag(x_3) == 8)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_155 = lean_ctor_get(x_2, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_2, 1);
lean_inc(x_156);
lean_dec(x_2);
x_157 = lean_ctor_get(x_3, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_3, 1);
lean_inc(x_158);
lean_dec(x_3);
x_159 = l_Lean_IR_VarId_alphaEqv(x_1, x_155, x_157);
lean_dec(x_157);
lean_dec(x_155);
if (x_159 == 0)
{
uint8_t x_160; 
lean_dec(x_158);
lean_dec(x_156);
lean_dec(x_1);
x_160 = 0;
return x_160;
}
else
{
x_2 = x_156;
x_3 = x_158;
goto _start;
}
}
else
{
uint8_t x_162; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_162 = 0;
return x_162;
}
}
case 9:
{
if (lean_obj_tag(x_3) == 9)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; 
x_163 = lean_ctor_get(x_2, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_2, 1);
lean_inc(x_164);
lean_dec(x_2);
x_165 = lean_ctor_get(x_3, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_3, 1);
lean_inc(x_166);
lean_dec(x_3);
x_167 = l_Lean_KVMap_eqv(x_163, x_165);
lean_dec(x_165);
lean_dec(x_163);
if (x_167 == 0)
{
uint8_t x_168; 
lean_dec(x_166);
lean_dec(x_164);
lean_dec(x_1);
x_168 = 0;
return x_168;
}
else
{
x_2 = x_164;
x_3 = x_166;
goto _start;
}
}
else
{
uint8_t x_170; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_170 = 0;
return x_170;
}
}
case 10:
{
if (lean_obj_tag(x_3) == 10)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_171 = lean_ctor_get(x_2, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_2, 1);
lean_inc(x_172);
x_173 = lean_ctor_get(x_2, 3);
lean_inc(x_173);
lean_dec(x_2);
x_174 = lean_ctor_get(x_3, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_3, 1);
lean_inc(x_175);
x_176 = lean_ctor_get(x_3, 3);
lean_inc(x_176);
lean_dec(x_3);
x_177 = lean_name_eq(x_171, x_174);
lean_dec(x_174);
lean_dec(x_171);
if (x_177 == 0)
{
uint8_t x_178; 
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_1);
x_178 = 0;
return x_178;
}
else
{
uint8_t x_179; 
x_179 = l_Lean_IR_VarId_alphaEqv(x_1, x_172, x_175);
lean_dec(x_175);
lean_dec(x_172);
if (x_179 == 0)
{
uint8_t x_180; 
lean_dec(x_176);
lean_dec(x_173);
lean_dec(x_1);
x_180 = 0;
return x_180;
}
else
{
lean_object* x_181; lean_object* x_182; uint8_t x_183; 
x_181 = lean_array_get_size(x_173);
x_182 = lean_array_get_size(x_176);
x_183 = lean_nat_dec_eq(x_181, x_182);
lean_dec(x_182);
lean_dec(x_181);
if (x_183 == 0)
{
uint8_t x_184; 
lean_dec(x_176);
lean_dec(x_173);
lean_dec(x_1);
x_184 = 0;
return x_184;
}
else
{
lean_object* x_185; uint8_t x_186; 
x_185 = lean_unsigned_to_nat(0u);
x_186 = l_Array_isEqvAux___main___at_Lean_IR_FnBody_alphaEqv___main___spec__1(x_1, x_173, x_176, lean_box(0), x_173, x_176, x_185);
lean_dec(x_176);
lean_dec(x_173);
return x_186;
}
}
}
}
else
{
uint8_t x_187; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_187 = 0;
return x_187;
}
}
case 11:
{
if (lean_obj_tag(x_3) == 11)
{
lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_188 = lean_ctor_get(x_2, 0);
lean_inc(x_188);
lean_dec(x_2);
x_189 = lean_ctor_get(x_3, 0);
lean_inc(x_189);
lean_dec(x_3);
x_190 = l_Lean_IR_Arg_alphaEqv(x_1, x_188, x_189);
lean_dec(x_189);
lean_dec(x_188);
lean_dec(x_1);
return x_190;
}
else
{
uint8_t x_191; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_191 = 0;
return x_191;
}
}
case 12:
{
if (lean_obj_tag(x_3) == 12)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_192 = lean_ctor_get(x_2, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_2, 1);
lean_inc(x_193);
lean_dec(x_2);
x_194 = lean_ctor_get(x_3, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_3, 1);
lean_inc(x_195);
lean_dec(x_3);
x_196 = lean_nat_dec_eq(x_192, x_194);
lean_dec(x_194);
lean_dec(x_192);
if (x_196 == 0)
{
uint8_t x_197; 
lean_dec(x_195);
lean_dec(x_193);
lean_dec(x_1);
x_197 = 0;
return x_197;
}
else
{
uint8_t x_198; 
x_198 = l_Lean_IR_args_alphaEqv(x_1, x_193, x_195);
lean_dec(x_195);
lean_dec(x_193);
lean_dec(x_1);
return x_198;
}
}
else
{
uint8_t x_199; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_199 = 0;
return x_199;
}
}
default: 
{
lean_dec(x_1);
if (lean_obj_tag(x_3) == 13)
{
uint8_t x_200; 
x_200 = 1;
return x_200;
}
else
{
uint8_t x_201; 
lean_dec(x_3);
x_201 = 0;
return x_201;
}
}
}
}
}
lean_object* l_Array_isEqvAux___main___at_Lean_IR_FnBody_alphaEqv___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_isEqvAux___main___at_Lean_IR_FnBody_alphaEqv___main___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_box(x_8);
return x_9;
}
}
lean_object* l_Lean_IR_FnBody_alphaEqv___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_IR_FnBody_alphaEqv___main(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
uint8_t l_Lean_IR_FnBody_alphaEqv(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_IR_FnBody_alphaEqv___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_IR_FnBody_alphaEqv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_IR_FnBody_alphaEqv(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
uint8_t l_Lean_IR_FnBody_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(0);
x_4 = l_Lean_IR_FnBody_alphaEqv___main(x_3, x_1, x_2);
return x_4;
}
}
lean_object* l_Lean_IR_FnBody_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_FnBody_beq(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* _init_l_Lean_IR_FnBody_HasBeq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_FnBody_beq___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_IR_FnBody_HasBeq() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_FnBody_HasBeq___closed__1;
return x_1;
}
}
lean_object* _init_l_Lean_IR_VarIdSet_Inhabited() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
lean_object* _init_l_Lean_IR_mkIf___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Bool");
return x_1;
}
}
lean_object* _init_l_Lean_IR_mkIf___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_mkIf___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_mkIf___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_mkIf___closed__2;
x_2 = l_Bool_HasRepr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_mkIf___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_mkIf___closed__3;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_2);
lean_ctor_set(x_3, 4, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_mkIf___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_IR_mkIf___closed__2;
x_2 = l_Bool_HasRepr___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_mkIf___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_IR_mkIf___closed__5;
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 3, x_3);
lean_ctor_set(x_4, 4, x_3);
return x_4;
}
}
lean_object* l_Lean_IR_mkIf(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = l_Lean_IR_mkIf___closed__4;
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
x_6 = l_Lean_IR_mkIf___closed__6;
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
x_8 = l_Lean_mkAppStx___closed__9;
x_9 = lean_array_push(x_8, x_5);
x_10 = lean_array_push(x_9, x_7);
x_11 = l_Lean_IR_mkIf___closed__2;
x_12 = lean_box(1);
x_13 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_1);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_10);
return x_13;
}
}
lean_object* initialize_Init_Data_Array(lean_object*);
lean_object* initialize_Init_Lean_Data_KVMap(lean_object*);
lean_object* initialize_Init_Lean_Data_Name(lean_object*);
lean_object* initialize_Init_Lean_Data_Format(lean_object*);
lean_object* initialize_Init_Lean_Compiler_ExternAttr(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Compiler_IR_Basic(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Data_KVMap(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Data_Name(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Data_Format(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_ExternAttr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_VarId_HasToString___closed__1 = _init_l_Lean_IR_VarId_HasToString___closed__1();
lean_mark_persistent(l_Lean_IR_VarId_HasToString___closed__1);
l_Lean_IR_JoinPointId_HasToString___closed__1 = _init_l_Lean_IR_JoinPointId_HasToString___closed__1();
lean_mark_persistent(l_Lean_IR_JoinPointId_HasToString___closed__1);
l_Lean_IR_MData_empty = _init_l_Lean_IR_MData_empty();
lean_mark_persistent(l_Lean_IR_MData_empty);
l_Lean_IR_MData_HasEmptyc = _init_l_Lean_IR_MData_HasEmptyc();
lean_mark_persistent(l_Lean_IR_MData_HasEmptyc);
l_Lean_IR_IRType_HasBeq___closed__1 = _init_l_Lean_IR_IRType_HasBeq___closed__1();
lean_mark_persistent(l_Lean_IR_IRType_HasBeq___closed__1);
l_Lean_IR_IRType_HasBeq = _init_l_Lean_IR_IRType_HasBeq();
lean_mark_persistent(l_Lean_IR_IRType_HasBeq);
l_Lean_IR_Arg_HasBeq___closed__1 = _init_l_Lean_IR_Arg_HasBeq___closed__1();
lean_mark_persistent(l_Lean_IR_Arg_HasBeq___closed__1);
l_Lean_IR_Arg_HasBeq = _init_l_Lean_IR_Arg_HasBeq();
lean_mark_persistent(l_Lean_IR_Arg_HasBeq);
l_Lean_IR_Arg_Inhabited = _init_l_Lean_IR_Arg_Inhabited();
lean_mark_persistent(l_Lean_IR_Arg_Inhabited);
l_Lean_IR_LitVal_HasBeq___closed__1 = _init_l_Lean_IR_LitVal_HasBeq___closed__1();
lean_mark_persistent(l_Lean_IR_LitVal_HasBeq___closed__1);
l_Lean_IR_LitVal_HasBeq = _init_l_Lean_IR_LitVal_HasBeq();
lean_mark_persistent(l_Lean_IR_LitVal_HasBeq);
l_Lean_IR_CtorInfo_HasBeq___closed__1 = _init_l_Lean_IR_CtorInfo_HasBeq___closed__1();
lean_mark_persistent(l_Lean_IR_CtorInfo_HasBeq___closed__1);
l_Lean_IR_CtorInfo_HasBeq = _init_l_Lean_IR_CtorInfo_HasBeq();
lean_mark_persistent(l_Lean_IR_CtorInfo_HasBeq);
l_Lean_IR_paramInh___closed__1 = _init_l_Lean_IR_paramInh___closed__1();
lean_mark_persistent(l_Lean_IR_paramInh___closed__1);
l_Lean_IR_paramInh = _init_l_Lean_IR_paramInh();
lean_mark_persistent(l_Lean_IR_paramInh);
l_Lean_IR_Inhabited = _init_l_Lean_IR_Inhabited();
lean_mark_persistent(l_Lean_IR_Inhabited);
l_Lean_IR_FnBody_nil = _init_l_Lean_IR_FnBody_nil();
lean_mark_persistent(l_Lean_IR_FnBody_nil);
l_Lean_IR_altInh___closed__1 = _init_l_Lean_IR_altInh___closed__1();
lean_mark_persistent(l_Lean_IR_altInh___closed__1);
l_Lean_IR_altInh = _init_l_Lean_IR_altInh();
lean_mark_persistent(l_Lean_IR_altInh);
l_Lean_IR_AltCore_mmodifyBody___rarg___closed__1 = _init_l_Lean_IR_AltCore_mmodifyBody___rarg___closed__1();
lean_mark_persistent(l_Lean_IR_AltCore_mmodifyBody___rarg___closed__1);
l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___at_Lean_IR_reshapeAux___main___spec__1___closed__1 = _init_l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___at_Lean_IR_reshapeAux___main___spec__1___closed__1();
lean_mark_persistent(l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___at_Lean_IR_reshapeAux___main___spec__1___closed__1);
l_Lean_IR_Decl_Inhabited___closed__1 = _init_l_Lean_IR_Decl_Inhabited___closed__1();
lean_mark_persistent(l_Lean_IR_Decl_Inhabited___closed__1);
l_Lean_IR_Decl_Inhabited = _init_l_Lean_IR_Decl_Inhabited();
lean_mark_persistent(l_Lean_IR_Decl_Inhabited);
l_Lean_IR_vsetInh = _init_l_Lean_IR_vsetInh();
lean_mark_persistent(l_Lean_IR_vsetInh);
l_Lean_IR_VarId_hasAeqv___closed__1 = _init_l_Lean_IR_VarId_hasAeqv___closed__1();
lean_mark_persistent(l_Lean_IR_VarId_hasAeqv___closed__1);
l_Lean_IR_VarId_hasAeqv = _init_l_Lean_IR_VarId_hasAeqv();
lean_mark_persistent(l_Lean_IR_VarId_hasAeqv);
l_Lean_IR_Arg_hasAeqv___closed__1 = _init_l_Lean_IR_Arg_hasAeqv___closed__1();
lean_mark_persistent(l_Lean_IR_Arg_hasAeqv___closed__1);
l_Lean_IR_Arg_hasAeqv = _init_l_Lean_IR_Arg_hasAeqv();
lean_mark_persistent(l_Lean_IR_Arg_hasAeqv);
l_Lean_IR_args_hasAeqv___closed__1 = _init_l_Lean_IR_args_hasAeqv___closed__1();
lean_mark_persistent(l_Lean_IR_args_hasAeqv___closed__1);
l_Lean_IR_args_hasAeqv = _init_l_Lean_IR_args_hasAeqv();
lean_mark_persistent(l_Lean_IR_args_hasAeqv);
l_Lean_IR_Expr_hasAeqv___closed__1 = _init_l_Lean_IR_Expr_hasAeqv___closed__1();
lean_mark_persistent(l_Lean_IR_Expr_hasAeqv___closed__1);
l_Lean_IR_Expr_hasAeqv = _init_l_Lean_IR_Expr_hasAeqv();
lean_mark_persistent(l_Lean_IR_Expr_hasAeqv);
l_Lean_IR_FnBody_HasBeq___closed__1 = _init_l_Lean_IR_FnBody_HasBeq___closed__1();
lean_mark_persistent(l_Lean_IR_FnBody_HasBeq___closed__1);
l_Lean_IR_FnBody_HasBeq = _init_l_Lean_IR_FnBody_HasBeq();
lean_mark_persistent(l_Lean_IR_FnBody_HasBeq);
l_Lean_IR_VarIdSet_Inhabited = _init_l_Lean_IR_VarIdSet_Inhabited();
lean_mark_persistent(l_Lean_IR_VarIdSet_Inhabited);
l_Lean_IR_mkIf___closed__1 = _init_l_Lean_IR_mkIf___closed__1();
lean_mark_persistent(l_Lean_IR_mkIf___closed__1);
l_Lean_IR_mkIf___closed__2 = _init_l_Lean_IR_mkIf___closed__2();
lean_mark_persistent(l_Lean_IR_mkIf___closed__2);
l_Lean_IR_mkIf___closed__3 = _init_l_Lean_IR_mkIf___closed__3();
lean_mark_persistent(l_Lean_IR_mkIf___closed__3);
l_Lean_IR_mkIf___closed__4 = _init_l_Lean_IR_mkIf___closed__4();
lean_mark_persistent(l_Lean_IR_mkIf___closed__4);
l_Lean_IR_mkIf___closed__5 = _init_l_Lean_IR_mkIf___closed__5();
lean_mark_persistent(l_Lean_IR_mkIf___closed__5);
l_Lean_IR_mkIf___closed__6 = _init_l_Lean_IR_mkIf___closed__6();
lean_mark_persistent(l_Lean_IR_mkIf___closed__6);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
