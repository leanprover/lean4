// Lean compiler output
// Module: Init.Lean.Compiler.IR.Basic
// Imports: Init.Data.Array Init.Lean.Name Init.Lean.KVMap Init.Lean.Format Init.Lean.Compiler.ExternAttr
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
extern uint8_t l_String_anyAux___main___at_String_all___spec__1___closed__1;
lean_object* l_RBNode_del___main___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(lean_object*, lean_object*);
uint8_t l_RBNode_isRed___rarg(lean_object*);
lean_object* l_Lean_IR_CtorInfo_HasBeq___closed__1;
uint8_t l_Lean_IR_FnBody_alphaEqv___main(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_erase___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__1___boxed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_IR_reshapeAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_addParamsRename(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_Expr_alphaEqv(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_addVarRename(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_Arg_beq(lean_object*, lean_object*);
lean_object* l_Lean_IR_addParamsRename___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_ir_mk_uproj_expr(lean_object*, lean_object*);
lean_object* l_RBNode_find___main___at_Lean_IR_LocalContext_isJP___spec__1___boxed(lean_object*, lean_object*);
extern uint8_t l_String_Iterator_extract___closed__1;
uint8_t l_Lean_IR_Index_lt(lean_object*, lean_object*);
lean_object* lean_ir_mk_vdecl(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_LocalContext_eraseJoinPointDecl(lean_object*, lean_object*);
lean_object* l_Lean_IR_LitVal_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_Arg_HasBeq;
uint8_t l_Array_isEqv___at_Lean_IR_IRType_beq___main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_IR_AltCore_mmodifyBody___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_RBNode_find___main___at_Lean_IR_VarId_alphaEqv___spec__1(lean_object*, lean_object*);
uint8_t l_Lean_IR_LocalContext_isJP(lean_object*, lean_object*);
extern lean_object* l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___rarg___closed__3;
lean_object* l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___at_Lean_IR_reshapeAux___main___spec__1(lean_object*);
lean_object* l_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
uint8_t l_Array_isEqv___at_Lean_IR_FnBody_alphaEqv___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_1__mkPanicMessage(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_VarId_Lean_HasFormat(lean_object*);
uint8_t l_Lean_IR_IRType_isStruct(lean_object*);
lean_object* l_Lean_IR_mmodifyJPs(lean_object*);
lean_object* l_Lean_IR_mmodifyJPs___rarg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isIrrelevant(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
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
lean_object* l_Lean_IR_IRType_isIrrelevant___boxed(lean_object*);
lean_object* l_Lean_IR_LocalContext_addParams___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_IRType_isUnion___boxed(lean_object*);
lean_object* l_RBNode_balRight___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_ir_mk_param(lean_object*, uint8_t, lean_object*);
uint8_t l_Lean_IR_IRType_isObj(lean_object*);
lean_object* l_Lean_IR_Arg_alphaEqv___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEqvAux___main___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_JoinPointId_Hashable___boxed(lean_object*);
lean_object* l_Lean_IR_Arg_HasBeq___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_IR_Alt_isDefault___boxed(lean_object*);
lean_object* l_Lean_IR_AltCore_body___boxed(lean_object*);
lean_object* l_Lean_IR_LocalContext_addParams(lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_resultType(lean_object*);
lean_object* l_Lean_IR_Decl_name(lean_object*);
uint8_t l_Array_isEqv___at_Lean_IR_FnBody_alphaEqv___main___spec__1___lambda__1(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Array_umapMAux___main___at_Lean_IR_mmodifyJPs___spec__1___boxed(lean_object*);
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
lean_object* l_Lean_IR_mkIf___closed__7;
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_IR_addParamsRename___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_VarId_HasBeq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_MData_empty;
lean_object* l_Array_isEqv___at_Lean_IR_FnBody_alphaEqv___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_IR_addParamsRename___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_ir_mk_var_arg(lean_object*);
lean_object* l_panic(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEqv___at_Lean_IR_args_alphaEqv___spec__1(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Array_isEqv___at_Lean_IR_args_alphaEqv___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_resultType___boxed(lean_object*);
lean_object* l_Lean_IR_LocalContext_addLocal(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_CtorInfo_beq(lean_object*, lean_object*);
lean_object* l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_IRType_isStruct___boxed(lean_object*);
lean_object* l_RBNode_setBlack___rarg(lean_object*);
extern lean_object* l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___rarg___closed__2;
lean_object* l_Lean_IR_FnBody_HasBeq;
lean_object* l_Array_isEqv___at_Lean_IR_FnBody_alphaEqv___main___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Array_isEqv___at_Lean_IR_IRType_beq___main___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_mmodifyJPs___boxed(lean_object*);
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
uint8_t l_Bool_DecidableEq(uint8_t, uint8_t);
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
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_IR_addParamsRename___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___rarg___closed__1;
uint8_t l_RBNode_isBlack___rarg(lean_object*);
lean_object* l_Lean_IR_Decl_isExtern___boxed(lean_object*);
lean_object* l_Lean_IR_AltCore_mmodifyBody___boxed(lean_object*);
lean_object* l_Array_isEqv___at_Lean_IR_IRType_beq___main___spec__1___closed__1;
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
lean_object* _init_l_Array_isEqv___at_Lean_IR_IRType_beq___main___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_IRType_beq___main___boxed), 2, 0);
return x_1;
}
}
uint8_t l_Array_isEqv___at_Lean_IR_IRType_beq___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_array_get_size(x_1);
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_Array_isEqv___at_Lean_IR_IRType_beq___main___spec__1___closed__1;
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_isEqvAux___main___rarg(x_1, x_2, lean_box(0), x_7, x_8);
return x_9;
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
lean_object* x_21; 
x_21 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_1, 1);
x_24 = lean_ctor_get(x_2, 1);
x_25 = l_Array_isEqv___at_Lean_IR_IRType_beq___main___spec__1(x_23, x_24);
return x_25;
}
else
{
uint8_t x_26; 
x_26 = 0;
return x_26;
}
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = 0;
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_1, 1);
x_30 = lean_ctor_get(x_2, 1);
x_31 = lean_ctor_get(x_21, 0);
x_32 = lean_ctor_get(x_27, 0);
x_33 = lean_name_eq(x_31, x_32);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = 0;
return x_34;
}
else
{
uint8_t x_35; 
x_35 = l_Array_isEqv___at_Lean_IR_IRType_beq___main___spec__1(x_29, x_30);
return x_35;
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
default: 
{
if (lean_obj_tag(x_2) == 10)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_1, 0);
x_38 = lean_ctor_get(x_1, 1);
x_39 = lean_ctor_get(x_2, 0);
x_40 = lean_ctor_get(x_2, 1);
x_41 = lean_name_eq(x_37, x_39);
if (x_41 == 0)
{
uint8_t x_42; 
x_42 = 0;
return x_42;
}
else
{
uint8_t x_43; 
x_43 = l_Array_isEqv___at_Lean_IR_IRType_beq___main___spec__1(x_38, x_40);
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
}
}
}
lean_object* l_Array_isEqv___at_Lean_IR_IRType_beq___main___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_isEqv___at_Lean_IR_IRType_beq___main___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
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
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = 0;
x_3 = lean_box(7);
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
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
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_2);
return x_4;
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
lean_object* x_41; 
x_41 = lean_ctor_get(x_1, 2);
lean_dec(x_41);
lean_ctor_set(x_1, 2, x_2);
return x_1;
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_1, 0);
x_43 = lean_ctor_get(x_1, 1);
x_44 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_45 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_1);
x_46 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_43);
lean_ctor_set(x_46, 2, x_2);
lean_ctor_set_uint8(x_46, sizeof(void*)*3, x_44);
lean_ctor_set_uint8(x_46, sizeof(void*)*3 + 1, x_45);
return x_46;
}
}
case 7:
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_1);
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_1, 2);
lean_dec(x_48);
lean_ctor_set(x_1, 2, x_2);
return x_1;
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_1, 0);
x_50 = lean_ctor_get(x_1, 1);
x_51 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_52 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_1);
x_53 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_53, 0, x_49);
lean_ctor_set(x_53, 1, x_50);
lean_ctor_set(x_53, 2, x_2);
lean_ctor_set_uint8(x_53, sizeof(void*)*3, x_51);
lean_ctor_set_uint8(x_53, sizeof(void*)*3 + 1, x_52);
return x_53;
}
}
case 8:
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_1);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_1, 1);
lean_dec(x_55);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_1, 0);
lean_inc(x_56);
lean_dec(x_1);
x_57 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_2);
return x_57;
}
}
case 9:
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_1);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_1, 1);
lean_dec(x_59);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_1, 0);
lean_inc(x_60);
lean_dec(x_1);
x_61 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_2);
return x_61;
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
lean_object* l_Lean_IR_AltCore_mmodifyBody___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_AltCore_mmodifyBody(x_1);
lean_dec(x_1);
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
uint8_t x_3; uint8_t x_4; uint8_t x_5; 
x_3 = l_Lean_IR_FnBody_isTerminal(x_1);
x_4 = 1;
x_5 = l_Bool_DecidableEq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_IR_FnBody_body(x_1);
x_7 = l_Lean_IR_push(x_2, x_1);
x_1 = x_6;
x_2 = x_7;
goto _start;
}
else
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_1);
return x_9;
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
x_8 = lean_unsigned_to_nat(140u);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l___private_Init_Util_1__mkPanicMessage(x_7, x_8, x_9, x_6);
lean_dec(x_6);
x_11 = l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___at_Lean_IR_reshapeAux___main___spec__1___closed__1;
x_12 = lean_panic_fn(x_10);
return x_12;
}
}
lean_object* l_Lean_IR_reshapeAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
x_6 = 1;
x_7 = l_Bool_DecidableEq(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_16; uint8_t x_17; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_2, x_8);
lean_dec(x_2);
x_16 = lean_array_get_size(x_1);
x_17 = lean_nat_dec_lt(x_9, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_1);
lean_inc(x_9);
x_18 = l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___at_Lean_IR_reshapeAux___main___spec__1(x_9);
x_10 = x_18;
goto block_15;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_array_fget(x_1, x_9);
x_20 = lean_box(13);
x_21 = lean_array_fset(x_1, x_9, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_10 = x_22;
goto block_15;
}
block_15:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_IR_FnBody_setBody(x_11, x_3);
x_1 = x_12;
x_2 = x_9;
x_3 = x_13;
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
lean_inc(x_8);
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
lean_inc(x_12);
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
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_mmodifyJPs___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_umapMAux___main___at_Lean_IR_mmodifyJPs___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_IR_mmodifyJPs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_mmodifyJPs(x_1);
lean_dec(x_1);
return x_2;
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
uint8_t x_4; lean_object* x_5; 
x_4 = 0;
x_5 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*4, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 3);
x_12 = lean_nat_dec_lt(x_2, x_9);
x_13 = 1;
x_14 = l_Bool_DecidableEq(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; uint8_t x_16; 
x_15 = lean_nat_dec_lt(x_9, x_2);
x_16 = l_Bool_DecidableEq(x_15, x_13);
if (x_16 == 0)
{
lean_dec(x_10);
lean_dec(x_9);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
lean_object* x_17; 
x_17 = l_RBNode_ins___main___at_Lean_IR_mkIndexSet___spec__2(x_11, x_2, x_3);
lean_ctor_set(x_1, 3, x_17);
return x_1;
}
}
else
{
lean_object* x_18; 
x_18 = l_RBNode_ins___main___at_Lean_IR_mkIndexSet___spec__2(x_8, x_2, x_3);
lean_ctor_set(x_1, 0, x_18);
return x_1;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_ctor_get(x_1, 2);
x_22 = lean_ctor_get(x_1, 3);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_23 = lean_nat_dec_lt(x_2, x_20);
x_24 = 1;
x_25 = l_Bool_DecidableEq(x_23, x_24);
if (x_25 == 0)
{
uint8_t x_26; uint8_t x_27; 
x_26 = lean_nat_dec_lt(x_20, x_2);
x_27 = l_Bool_DecidableEq(x_26, x_24);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_21);
lean_dec(x_20);
x_28 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_2);
lean_ctor_set(x_28, 2, x_3);
lean_ctor_set(x_28, 3, x_22);
lean_ctor_set_uint8(x_28, sizeof(void*)*4, x_6);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_RBNode_ins___main___at_Lean_IR_mkIndexSet___spec__2(x_22, x_2, x_3);
x_30 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_30, 0, x_19);
lean_ctor_set(x_30, 1, x_20);
lean_ctor_set(x_30, 2, x_21);
lean_ctor_set(x_30, 3, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_6);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_RBNode_ins___main___at_Lean_IR_mkIndexSet___spec__2(x_19, x_2, x_3);
x_32 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_20);
lean_ctor_set(x_32, 2, x_21);
lean_ctor_set(x_32, 3, x_22);
lean_ctor_set_uint8(x_32, sizeof(void*)*4, x_6);
return x_32;
}
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_1);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; 
x_34 = lean_ctor_get(x_1, 0);
x_35 = lean_ctor_get(x_1, 1);
x_36 = lean_ctor_get(x_1, 2);
x_37 = lean_ctor_get(x_1, 3);
x_38 = lean_nat_dec_lt(x_2, x_35);
x_39 = 1;
x_40 = l_Bool_DecidableEq(x_38, x_39);
if (x_40 == 0)
{
uint8_t x_41; uint8_t x_42; 
x_41 = lean_nat_dec_lt(x_35, x_2);
x_42 = l_Bool_DecidableEq(x_41, x_39);
if (x_42 == 0)
{
lean_dec(x_36);
lean_dec(x_35);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
uint8_t x_43; uint8_t x_44; 
x_43 = l_RBNode_isRed___rarg(x_37);
x_44 = l_Bool_DecidableEq(x_43, x_39);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = l_RBNode_ins___main___at_Lean_IR_mkIndexSet___spec__2(x_37, x_2, x_3);
lean_ctor_set(x_1, 3, x_45);
return x_1;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = l_RBNode_ins___main___at_Lean_IR_mkIndexSet___spec__2(x_37, x_2, x_3);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_46, 3);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_46);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_46, 3);
lean_dec(x_50);
x_51 = lean_ctor_get(x_46, 0);
lean_dec(x_51);
x_52 = 0;
lean_ctor_set(x_46, 0, x_48);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_52);
x_53 = 1;
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_53);
return x_1;
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_ctor_get(x_46, 1);
x_55 = lean_ctor_get(x_46, 2);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_46);
x_56 = 0;
x_57 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_57, 0, x_48);
lean_ctor_set(x_57, 1, x_54);
lean_ctor_set(x_57, 2, x_55);
lean_ctor_set(x_57, 3, x_48);
lean_ctor_set_uint8(x_57, sizeof(void*)*4, x_56);
x_58 = 1;
lean_ctor_set(x_1, 3, x_57);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_58);
return x_1;
}
}
else
{
uint8_t x_59; 
x_59 = lean_ctor_get_uint8(x_48, sizeof(void*)*4);
if (x_59 == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_46);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_61 = lean_ctor_get(x_46, 1);
x_62 = lean_ctor_get(x_46, 2);
x_63 = lean_ctor_get(x_46, 3);
lean_dec(x_63);
x_64 = lean_ctor_get(x_46, 0);
lean_dec(x_64);
x_65 = !lean_is_exclusive(x_48);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_66 = lean_ctor_get(x_48, 0);
x_67 = lean_ctor_get(x_48, 1);
x_68 = lean_ctor_get(x_48, 2);
x_69 = lean_ctor_get(x_48, 3);
x_70 = 1;
lean_ctor_set(x_48, 3, x_47);
lean_ctor_set(x_48, 2, x_36);
lean_ctor_set(x_48, 1, x_35);
lean_ctor_set(x_48, 0, x_34);
lean_ctor_set_uint8(x_48, sizeof(void*)*4, x_70);
lean_ctor_set(x_46, 3, x_69);
lean_ctor_set(x_46, 2, x_68);
lean_ctor_set(x_46, 1, x_67);
lean_ctor_set(x_46, 0, x_66);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_70);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set(x_1, 2, x_62);
lean_ctor_set(x_1, 1, x_61);
lean_ctor_set(x_1, 0, x_48);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_59);
return x_1;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; 
x_71 = lean_ctor_get(x_48, 0);
x_72 = lean_ctor_get(x_48, 1);
x_73 = lean_ctor_get(x_48, 2);
x_74 = lean_ctor_get(x_48, 3);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_48);
x_75 = 1;
x_76 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_76, 0, x_34);
lean_ctor_set(x_76, 1, x_35);
lean_ctor_set(x_76, 2, x_36);
lean_ctor_set(x_76, 3, x_47);
lean_ctor_set_uint8(x_76, sizeof(void*)*4, x_75);
lean_ctor_set(x_46, 3, x_74);
lean_ctor_set(x_46, 2, x_73);
lean_ctor_set(x_46, 1, x_72);
lean_ctor_set(x_46, 0, x_71);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_75);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set(x_1, 2, x_62);
lean_ctor_set(x_1, 1, x_61);
lean_ctor_set(x_1, 0, x_76);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_59);
return x_1;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; 
x_77 = lean_ctor_get(x_46, 1);
x_78 = lean_ctor_get(x_46, 2);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_46);
x_79 = lean_ctor_get(x_48, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_48, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_48, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_48, 3);
lean_inc(x_82);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 lean_ctor_release(x_48, 2);
 lean_ctor_release(x_48, 3);
 x_83 = x_48;
} else {
 lean_dec_ref(x_48);
 x_83 = lean_box(0);
}
x_84 = 1;
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(1, 4, 1);
} else {
 x_85 = x_83;
}
lean_ctor_set(x_85, 0, x_34);
lean_ctor_set(x_85, 1, x_35);
lean_ctor_set(x_85, 2, x_36);
lean_ctor_set(x_85, 3, x_47);
lean_ctor_set_uint8(x_85, sizeof(void*)*4, x_84);
x_86 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_86, 0, x_79);
lean_ctor_set(x_86, 1, x_80);
lean_ctor_set(x_86, 2, x_81);
lean_ctor_set(x_86, 3, x_82);
lean_ctor_set_uint8(x_86, sizeof(void*)*4, x_84);
lean_ctor_set(x_1, 3, x_86);
lean_ctor_set(x_1, 2, x_78);
lean_ctor_set(x_1, 1, x_77);
lean_ctor_set(x_1, 0, x_85);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_59);
return x_1;
}
}
else
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_46);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_88 = lean_ctor_get(x_46, 3);
lean_dec(x_88);
x_89 = lean_ctor_get(x_46, 0);
lean_dec(x_89);
x_90 = 0;
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_90);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_59);
return x_1;
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_46, 1);
x_92 = lean_ctor_get(x_46, 2);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_46);
x_93 = 0;
x_94 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_94, 0, x_47);
lean_ctor_set(x_94, 1, x_91);
lean_ctor_set(x_94, 2, x_92);
lean_ctor_set(x_94, 3, x_48);
lean_ctor_set_uint8(x_94, sizeof(void*)*4, x_93);
lean_ctor_set(x_1, 3, x_94);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_59);
return x_1;
}
}
}
}
else
{
uint8_t x_95; 
x_95 = lean_ctor_get_uint8(x_47, sizeof(void*)*4);
if (x_95 == 0)
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_46);
if (x_96 == 0)
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_ctor_get(x_46, 0);
lean_dec(x_97);
x_98 = !lean_is_exclusive(x_47);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_99 = lean_ctor_get(x_47, 0);
x_100 = lean_ctor_get(x_47, 1);
x_101 = lean_ctor_get(x_47, 2);
x_102 = lean_ctor_get(x_47, 3);
x_103 = 1;
lean_ctor_set(x_47, 3, x_99);
lean_ctor_set(x_47, 2, x_36);
lean_ctor_set(x_47, 1, x_35);
lean_ctor_set(x_47, 0, x_34);
lean_ctor_set_uint8(x_47, sizeof(void*)*4, x_103);
lean_ctor_set(x_46, 0, x_102);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_103);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set(x_1, 2, x_101);
lean_ctor_set(x_1, 1, x_100);
lean_ctor_set(x_1, 0, x_47);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_95);
return x_1;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; 
x_104 = lean_ctor_get(x_47, 0);
x_105 = lean_ctor_get(x_47, 1);
x_106 = lean_ctor_get(x_47, 2);
x_107 = lean_ctor_get(x_47, 3);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_47);
x_108 = 1;
x_109 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_109, 0, x_34);
lean_ctor_set(x_109, 1, x_35);
lean_ctor_set(x_109, 2, x_36);
lean_ctor_set(x_109, 3, x_104);
lean_ctor_set_uint8(x_109, sizeof(void*)*4, x_108);
lean_ctor_set(x_46, 0, x_107);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_108);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set(x_1, 2, x_106);
lean_ctor_set(x_1, 1, x_105);
lean_ctor_set(x_1, 0, x_109);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_95);
return x_1;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; 
x_110 = lean_ctor_get(x_46, 1);
x_111 = lean_ctor_get(x_46, 2);
x_112 = lean_ctor_get(x_46, 3);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_46);
x_113 = lean_ctor_get(x_47, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_47, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_47, 2);
lean_inc(x_115);
x_116 = lean_ctor_get(x_47, 3);
lean_inc(x_116);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_117 = x_47;
} else {
 lean_dec_ref(x_47);
 x_117 = lean_box(0);
}
x_118 = 1;
if (lean_is_scalar(x_117)) {
 x_119 = lean_alloc_ctor(1, 4, 1);
} else {
 x_119 = x_117;
}
lean_ctor_set(x_119, 0, x_34);
lean_ctor_set(x_119, 1, x_35);
lean_ctor_set(x_119, 2, x_36);
lean_ctor_set(x_119, 3, x_113);
lean_ctor_set_uint8(x_119, sizeof(void*)*4, x_118);
x_120 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_120, 0, x_116);
lean_ctor_set(x_120, 1, x_110);
lean_ctor_set(x_120, 2, x_111);
lean_ctor_set(x_120, 3, x_112);
lean_ctor_set_uint8(x_120, sizeof(void*)*4, x_118);
lean_ctor_set(x_1, 3, x_120);
lean_ctor_set(x_1, 2, x_115);
lean_ctor_set(x_1, 1, x_114);
lean_ctor_set(x_1, 0, x_119);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_95);
return x_1;
}
}
else
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_46, 3);
lean_inc(x_121);
if (lean_obj_tag(x_121) == 0)
{
uint8_t x_122; 
x_122 = !lean_is_exclusive(x_46);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_123 = lean_ctor_get(x_46, 3);
lean_dec(x_123);
x_124 = lean_ctor_get(x_46, 0);
lean_dec(x_124);
x_125 = 0;
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_125);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_95);
return x_1;
}
else
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; 
x_126 = lean_ctor_get(x_46, 1);
x_127 = lean_ctor_get(x_46, 2);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_46);
x_128 = 0;
x_129 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_129, 0, x_47);
lean_ctor_set(x_129, 1, x_126);
lean_ctor_set(x_129, 2, x_127);
lean_ctor_set(x_129, 3, x_121);
lean_ctor_set_uint8(x_129, sizeof(void*)*4, x_128);
lean_ctor_set(x_1, 3, x_129);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_95);
return x_1;
}
}
else
{
uint8_t x_130; 
x_130 = lean_ctor_get_uint8(x_121, sizeof(void*)*4);
if (x_130 == 0)
{
uint8_t x_131; 
lean_free_object(x_1);
x_131 = !lean_is_exclusive(x_46);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_132 = lean_ctor_get(x_46, 3);
lean_dec(x_132);
x_133 = lean_ctor_get(x_46, 0);
lean_dec(x_133);
x_134 = !lean_is_exclusive(x_121);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_135 = lean_ctor_get(x_121, 0);
x_136 = lean_ctor_get(x_121, 1);
x_137 = lean_ctor_get(x_121, 2);
x_138 = lean_ctor_get(x_121, 3);
lean_inc(x_47);
lean_ctor_set(x_121, 3, x_47);
lean_ctor_set(x_121, 2, x_36);
lean_ctor_set(x_121, 1, x_35);
lean_ctor_set(x_121, 0, x_34);
x_139 = !lean_is_exclusive(x_47);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_140 = lean_ctor_get(x_47, 3);
lean_dec(x_140);
x_141 = lean_ctor_get(x_47, 2);
lean_dec(x_141);
x_142 = lean_ctor_get(x_47, 1);
lean_dec(x_142);
x_143 = lean_ctor_get(x_47, 0);
lean_dec(x_143);
lean_ctor_set_uint8(x_121, sizeof(void*)*4, x_95);
lean_ctor_set(x_47, 3, x_138);
lean_ctor_set(x_47, 2, x_137);
lean_ctor_set(x_47, 1, x_136);
lean_ctor_set(x_47, 0, x_135);
lean_ctor_set(x_46, 3, x_47);
lean_ctor_set(x_46, 0, x_121);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_130);
return x_46;
}
else
{
lean_object* x_144; 
lean_dec(x_47);
lean_ctor_set_uint8(x_121, sizeof(void*)*4, x_95);
x_144 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_144, 0, x_135);
lean_ctor_set(x_144, 1, x_136);
lean_ctor_set(x_144, 2, x_137);
lean_ctor_set(x_144, 3, x_138);
lean_ctor_set_uint8(x_144, sizeof(void*)*4, x_95);
lean_ctor_set(x_46, 3, x_144);
lean_ctor_set(x_46, 0, x_121);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_130);
return x_46;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_145 = lean_ctor_get(x_121, 0);
x_146 = lean_ctor_get(x_121, 1);
x_147 = lean_ctor_get(x_121, 2);
x_148 = lean_ctor_get(x_121, 3);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_121);
lean_inc(x_47);
x_149 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_149, 0, x_34);
lean_ctor_set(x_149, 1, x_35);
lean_ctor_set(x_149, 2, x_36);
lean_ctor_set(x_149, 3, x_47);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_150 = x_47;
} else {
 lean_dec_ref(x_47);
 x_150 = lean_box(0);
}
lean_ctor_set_uint8(x_149, sizeof(void*)*4, x_95);
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 4, 1);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_145);
lean_ctor_set(x_151, 1, x_146);
lean_ctor_set(x_151, 2, x_147);
lean_ctor_set(x_151, 3, x_148);
lean_ctor_set_uint8(x_151, sizeof(void*)*4, x_95);
lean_ctor_set(x_46, 3, x_151);
lean_ctor_set(x_46, 0, x_149);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_130);
return x_46;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_152 = lean_ctor_get(x_46, 1);
x_153 = lean_ctor_get(x_46, 2);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_46);
x_154 = lean_ctor_get(x_121, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_121, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_121, 2);
lean_inc(x_156);
x_157 = lean_ctor_get(x_121, 3);
lean_inc(x_157);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 lean_ctor_release(x_121, 2);
 lean_ctor_release(x_121, 3);
 x_158 = x_121;
} else {
 lean_dec_ref(x_121);
 x_158 = lean_box(0);
}
lean_inc(x_47);
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 4, 1);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_34);
lean_ctor_set(x_159, 1, x_35);
lean_ctor_set(x_159, 2, x_36);
lean_ctor_set(x_159, 3, x_47);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_160 = x_47;
} else {
 lean_dec_ref(x_47);
 x_160 = lean_box(0);
}
lean_ctor_set_uint8(x_159, sizeof(void*)*4, x_95);
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 4, 1);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_154);
lean_ctor_set(x_161, 1, x_155);
lean_ctor_set(x_161, 2, x_156);
lean_ctor_set(x_161, 3, x_157);
lean_ctor_set_uint8(x_161, sizeof(void*)*4, x_95);
x_162 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_152);
lean_ctor_set(x_162, 2, x_153);
lean_ctor_set(x_162, 3, x_161);
lean_ctor_set_uint8(x_162, sizeof(void*)*4, x_130);
return x_162;
}
}
else
{
uint8_t x_163; 
x_163 = !lean_is_exclusive(x_46);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_164 = lean_ctor_get(x_46, 3);
lean_dec(x_164);
x_165 = lean_ctor_get(x_46, 0);
lean_dec(x_165);
x_166 = !lean_is_exclusive(x_47);
if (x_166 == 0)
{
uint8_t x_167; 
lean_ctor_set_uint8(x_47, sizeof(void*)*4, x_130);
x_167 = 0;
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_167);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_130);
return x_1;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_168 = lean_ctor_get(x_47, 0);
x_169 = lean_ctor_get(x_47, 1);
x_170 = lean_ctor_get(x_47, 2);
x_171 = lean_ctor_get(x_47, 3);
lean_inc(x_171);
lean_inc(x_170);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_47);
x_172 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_172, 0, x_168);
lean_ctor_set(x_172, 1, x_169);
lean_ctor_set(x_172, 2, x_170);
lean_ctor_set(x_172, 3, x_171);
lean_ctor_set_uint8(x_172, sizeof(void*)*4, x_130);
x_173 = 0;
lean_ctor_set(x_46, 0, x_172);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_173);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_130);
return x_1;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; lean_object* x_183; 
x_174 = lean_ctor_get(x_46, 1);
x_175 = lean_ctor_get(x_46, 2);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_46);
x_176 = lean_ctor_get(x_47, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_47, 1);
lean_inc(x_177);
x_178 = lean_ctor_get(x_47, 2);
lean_inc(x_178);
x_179 = lean_ctor_get(x_47, 3);
lean_inc(x_179);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_180 = x_47;
} else {
 lean_dec_ref(x_47);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(1, 4, 1);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_176);
lean_ctor_set(x_181, 1, x_177);
lean_ctor_set(x_181, 2, x_178);
lean_ctor_set(x_181, 3, x_179);
lean_ctor_set_uint8(x_181, sizeof(void*)*4, x_130);
x_182 = 0;
x_183 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_174);
lean_ctor_set(x_183, 2, x_175);
lean_ctor_set(x_183, 3, x_121);
lean_ctor_set_uint8(x_183, sizeof(void*)*4, x_182);
lean_ctor_set(x_1, 3, x_183);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_130);
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
uint8_t x_184; uint8_t x_185; 
x_184 = l_RBNode_isRed___rarg(x_34);
x_185 = l_Bool_DecidableEq(x_184, x_39);
if (x_185 == 0)
{
lean_object* x_186; 
x_186 = l_RBNode_ins___main___at_Lean_IR_mkIndexSet___spec__2(x_34, x_2, x_3);
lean_ctor_set(x_1, 0, x_186);
return x_1;
}
else
{
lean_object* x_187; lean_object* x_188; 
x_187 = l_RBNode_ins___main___at_Lean_IR_mkIndexSet___spec__2(x_34, x_2, x_3);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; 
x_189 = lean_ctor_get(x_187, 3);
lean_inc(x_189);
if (lean_obj_tag(x_189) == 0)
{
uint8_t x_190; 
x_190 = !lean_is_exclusive(x_187);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; uint8_t x_193; uint8_t x_194; 
x_191 = lean_ctor_get(x_187, 3);
lean_dec(x_191);
x_192 = lean_ctor_get(x_187, 0);
lean_dec(x_192);
x_193 = 0;
lean_ctor_set(x_187, 0, x_189);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_193);
x_194 = 1;
lean_ctor_set(x_1, 0, x_187);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_194);
return x_1;
}
else
{
lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; uint8_t x_199; 
x_195 = lean_ctor_get(x_187, 1);
x_196 = lean_ctor_get(x_187, 2);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_187);
x_197 = 0;
x_198 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_198, 0, x_189);
lean_ctor_set(x_198, 1, x_195);
lean_ctor_set(x_198, 2, x_196);
lean_ctor_set(x_198, 3, x_189);
lean_ctor_set_uint8(x_198, sizeof(void*)*4, x_197);
x_199 = 1;
lean_ctor_set(x_1, 0, x_198);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_199);
return x_1;
}
}
else
{
uint8_t x_200; 
x_200 = lean_ctor_get_uint8(x_189, sizeof(void*)*4);
if (x_200 == 0)
{
uint8_t x_201; 
x_201 = !lean_is_exclusive(x_187);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; 
x_202 = lean_ctor_get(x_187, 1);
x_203 = lean_ctor_get(x_187, 2);
x_204 = lean_ctor_get(x_187, 3);
lean_dec(x_204);
x_205 = lean_ctor_get(x_187, 0);
lean_dec(x_205);
x_206 = !lean_is_exclusive(x_189);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; 
x_207 = lean_ctor_get(x_189, 0);
x_208 = lean_ctor_get(x_189, 1);
x_209 = lean_ctor_get(x_189, 2);
x_210 = lean_ctor_get(x_189, 3);
x_211 = 1;
lean_ctor_set(x_189, 3, x_207);
lean_ctor_set(x_189, 2, x_203);
lean_ctor_set(x_189, 1, x_202);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set_uint8(x_189, sizeof(void*)*4, x_211);
lean_ctor_set(x_187, 3, x_37);
lean_ctor_set(x_187, 2, x_36);
lean_ctor_set(x_187, 1, x_35);
lean_ctor_set(x_187, 0, x_210);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_211);
lean_ctor_set(x_1, 3, x_187);
lean_ctor_set(x_1, 2, x_209);
lean_ctor_set(x_1, 1, x_208);
lean_ctor_set(x_1, 0, x_189);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_200);
return x_1;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; 
x_212 = lean_ctor_get(x_189, 0);
x_213 = lean_ctor_get(x_189, 1);
x_214 = lean_ctor_get(x_189, 2);
x_215 = lean_ctor_get(x_189, 3);
lean_inc(x_215);
lean_inc(x_214);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_189);
x_216 = 1;
x_217 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_217, 0, x_188);
lean_ctor_set(x_217, 1, x_202);
lean_ctor_set(x_217, 2, x_203);
lean_ctor_set(x_217, 3, x_212);
lean_ctor_set_uint8(x_217, sizeof(void*)*4, x_216);
lean_ctor_set(x_187, 3, x_37);
lean_ctor_set(x_187, 2, x_36);
lean_ctor_set(x_187, 1, x_35);
lean_ctor_set(x_187, 0, x_215);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_216);
lean_ctor_set(x_1, 3, x_187);
lean_ctor_set(x_1, 2, x_214);
lean_ctor_set(x_1, 1, x_213);
lean_ctor_set(x_1, 0, x_217);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_200);
return x_1;
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; lean_object* x_226; lean_object* x_227; 
x_218 = lean_ctor_get(x_187, 1);
x_219 = lean_ctor_get(x_187, 2);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_187);
x_220 = lean_ctor_get(x_189, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_189, 1);
lean_inc(x_221);
x_222 = lean_ctor_get(x_189, 2);
lean_inc(x_222);
x_223 = lean_ctor_get(x_189, 3);
lean_inc(x_223);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 lean_ctor_release(x_189, 2);
 lean_ctor_release(x_189, 3);
 x_224 = x_189;
} else {
 lean_dec_ref(x_189);
 x_224 = lean_box(0);
}
x_225 = 1;
if (lean_is_scalar(x_224)) {
 x_226 = lean_alloc_ctor(1, 4, 1);
} else {
 x_226 = x_224;
}
lean_ctor_set(x_226, 0, x_188);
lean_ctor_set(x_226, 1, x_218);
lean_ctor_set(x_226, 2, x_219);
lean_ctor_set(x_226, 3, x_220);
lean_ctor_set_uint8(x_226, sizeof(void*)*4, x_225);
x_227 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_227, 0, x_223);
lean_ctor_set(x_227, 1, x_35);
lean_ctor_set(x_227, 2, x_36);
lean_ctor_set(x_227, 3, x_37);
lean_ctor_set_uint8(x_227, sizeof(void*)*4, x_225);
lean_ctor_set(x_1, 3, x_227);
lean_ctor_set(x_1, 2, x_222);
lean_ctor_set(x_1, 1, x_221);
lean_ctor_set(x_1, 0, x_226);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_200);
return x_1;
}
}
else
{
uint8_t x_228; 
x_228 = !lean_is_exclusive(x_187);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; uint8_t x_231; 
x_229 = lean_ctor_get(x_187, 3);
lean_dec(x_229);
x_230 = lean_ctor_get(x_187, 0);
lean_dec(x_230);
x_231 = 0;
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_231);
lean_ctor_set(x_1, 0, x_187);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_200);
return x_1;
}
else
{
lean_object* x_232; lean_object* x_233; uint8_t x_234; lean_object* x_235; 
x_232 = lean_ctor_get(x_187, 1);
x_233 = lean_ctor_get(x_187, 2);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_187);
x_234 = 0;
x_235 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_235, 0, x_188);
lean_ctor_set(x_235, 1, x_232);
lean_ctor_set(x_235, 2, x_233);
lean_ctor_set(x_235, 3, x_189);
lean_ctor_set_uint8(x_235, sizeof(void*)*4, x_234);
lean_ctor_set(x_1, 0, x_235);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_200);
return x_1;
}
}
}
}
else
{
uint8_t x_236; 
x_236 = lean_ctor_get_uint8(x_188, sizeof(void*)*4);
if (x_236 == 0)
{
uint8_t x_237; 
x_237 = !lean_is_exclusive(x_187);
if (x_237 == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; 
x_238 = lean_ctor_get(x_187, 1);
x_239 = lean_ctor_get(x_187, 2);
x_240 = lean_ctor_get(x_187, 3);
x_241 = lean_ctor_get(x_187, 0);
lean_dec(x_241);
x_242 = !lean_is_exclusive(x_188);
if (x_242 == 0)
{
uint8_t x_243; 
x_243 = 1;
lean_ctor_set_uint8(x_188, sizeof(void*)*4, x_243);
lean_ctor_set(x_187, 3, x_37);
lean_ctor_set(x_187, 2, x_36);
lean_ctor_set(x_187, 1, x_35);
lean_ctor_set(x_187, 0, x_240);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_243);
lean_ctor_set(x_1, 3, x_187);
lean_ctor_set(x_1, 2, x_239);
lean_ctor_set(x_1, 1, x_238);
lean_ctor_set(x_1, 0, x_188);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_236);
return x_1;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; uint8_t x_248; lean_object* x_249; 
x_244 = lean_ctor_get(x_188, 0);
x_245 = lean_ctor_get(x_188, 1);
x_246 = lean_ctor_get(x_188, 2);
x_247 = lean_ctor_get(x_188, 3);
lean_inc(x_247);
lean_inc(x_246);
lean_inc(x_245);
lean_inc(x_244);
lean_dec(x_188);
x_248 = 1;
x_249 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_249, 0, x_244);
lean_ctor_set(x_249, 1, x_245);
lean_ctor_set(x_249, 2, x_246);
lean_ctor_set(x_249, 3, x_247);
lean_ctor_set_uint8(x_249, sizeof(void*)*4, x_248);
lean_ctor_set(x_187, 3, x_37);
lean_ctor_set(x_187, 2, x_36);
lean_ctor_set(x_187, 1, x_35);
lean_ctor_set(x_187, 0, x_240);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_248);
lean_ctor_set(x_1, 3, x_187);
lean_ctor_set(x_1, 2, x_239);
lean_ctor_set(x_1, 1, x_238);
lean_ctor_set(x_1, 0, x_249);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_236);
return x_1;
}
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; lean_object* x_259; lean_object* x_260; 
x_250 = lean_ctor_get(x_187, 1);
x_251 = lean_ctor_get(x_187, 2);
x_252 = lean_ctor_get(x_187, 3);
lean_inc(x_252);
lean_inc(x_251);
lean_inc(x_250);
lean_dec(x_187);
x_253 = lean_ctor_get(x_188, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_188, 1);
lean_inc(x_254);
x_255 = lean_ctor_get(x_188, 2);
lean_inc(x_255);
x_256 = lean_ctor_get(x_188, 3);
lean_inc(x_256);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 lean_ctor_release(x_188, 2);
 lean_ctor_release(x_188, 3);
 x_257 = x_188;
} else {
 lean_dec_ref(x_188);
 x_257 = lean_box(0);
}
x_258 = 1;
if (lean_is_scalar(x_257)) {
 x_259 = lean_alloc_ctor(1, 4, 1);
} else {
 x_259 = x_257;
}
lean_ctor_set(x_259, 0, x_253);
lean_ctor_set(x_259, 1, x_254);
lean_ctor_set(x_259, 2, x_255);
lean_ctor_set(x_259, 3, x_256);
lean_ctor_set_uint8(x_259, sizeof(void*)*4, x_258);
x_260 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_260, 0, x_252);
lean_ctor_set(x_260, 1, x_35);
lean_ctor_set(x_260, 2, x_36);
lean_ctor_set(x_260, 3, x_37);
lean_ctor_set_uint8(x_260, sizeof(void*)*4, x_258);
lean_ctor_set(x_1, 3, x_260);
lean_ctor_set(x_1, 2, x_251);
lean_ctor_set(x_1, 1, x_250);
lean_ctor_set(x_1, 0, x_259);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_236);
return x_1;
}
}
else
{
lean_object* x_261; 
x_261 = lean_ctor_get(x_187, 3);
lean_inc(x_261);
if (lean_obj_tag(x_261) == 0)
{
uint8_t x_262; 
x_262 = !lean_is_exclusive(x_187);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; uint8_t x_265; 
x_263 = lean_ctor_get(x_187, 3);
lean_dec(x_263);
x_264 = lean_ctor_get(x_187, 0);
lean_dec(x_264);
x_265 = 0;
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_265);
lean_ctor_set(x_1, 0, x_187);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_236);
return x_1;
}
else
{
lean_object* x_266; lean_object* x_267; uint8_t x_268; lean_object* x_269; 
x_266 = lean_ctor_get(x_187, 1);
x_267 = lean_ctor_get(x_187, 2);
lean_inc(x_267);
lean_inc(x_266);
lean_dec(x_187);
x_268 = 0;
x_269 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_269, 0, x_188);
lean_ctor_set(x_269, 1, x_266);
lean_ctor_set(x_269, 2, x_267);
lean_ctor_set(x_269, 3, x_261);
lean_ctor_set_uint8(x_269, sizeof(void*)*4, x_268);
lean_ctor_set(x_1, 0, x_269);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_236);
return x_1;
}
}
else
{
uint8_t x_270; 
x_270 = lean_ctor_get_uint8(x_261, sizeof(void*)*4);
if (x_270 == 0)
{
uint8_t x_271; 
lean_free_object(x_1);
x_271 = !lean_is_exclusive(x_187);
if (x_271 == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; uint8_t x_276; 
x_272 = lean_ctor_get(x_187, 1);
x_273 = lean_ctor_get(x_187, 2);
x_274 = lean_ctor_get(x_187, 3);
lean_dec(x_274);
x_275 = lean_ctor_get(x_187, 0);
lean_dec(x_275);
x_276 = !lean_is_exclusive(x_261);
if (x_276 == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; uint8_t x_281; 
x_277 = lean_ctor_get(x_261, 0);
x_278 = lean_ctor_get(x_261, 1);
x_279 = lean_ctor_get(x_261, 2);
x_280 = lean_ctor_get(x_261, 3);
lean_inc(x_188);
lean_ctor_set(x_261, 3, x_277);
lean_ctor_set(x_261, 2, x_273);
lean_ctor_set(x_261, 1, x_272);
lean_ctor_set(x_261, 0, x_188);
x_281 = !lean_is_exclusive(x_188);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_282 = lean_ctor_get(x_188, 3);
lean_dec(x_282);
x_283 = lean_ctor_get(x_188, 2);
lean_dec(x_283);
x_284 = lean_ctor_get(x_188, 1);
lean_dec(x_284);
x_285 = lean_ctor_get(x_188, 0);
lean_dec(x_285);
lean_ctor_set_uint8(x_261, sizeof(void*)*4, x_236);
lean_ctor_set(x_188, 3, x_37);
lean_ctor_set(x_188, 2, x_36);
lean_ctor_set(x_188, 1, x_35);
lean_ctor_set(x_188, 0, x_280);
lean_ctor_set(x_187, 3, x_188);
lean_ctor_set(x_187, 2, x_279);
lean_ctor_set(x_187, 1, x_278);
lean_ctor_set(x_187, 0, x_261);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_270);
return x_187;
}
else
{
lean_object* x_286; 
lean_dec(x_188);
lean_ctor_set_uint8(x_261, sizeof(void*)*4, x_236);
x_286 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_286, 0, x_280);
lean_ctor_set(x_286, 1, x_35);
lean_ctor_set(x_286, 2, x_36);
lean_ctor_set(x_286, 3, x_37);
lean_ctor_set_uint8(x_286, sizeof(void*)*4, x_236);
lean_ctor_set(x_187, 3, x_286);
lean_ctor_set(x_187, 2, x_279);
lean_ctor_set(x_187, 1, x_278);
lean_ctor_set(x_187, 0, x_261);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_270);
return x_187;
}
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_287 = lean_ctor_get(x_261, 0);
x_288 = lean_ctor_get(x_261, 1);
x_289 = lean_ctor_get(x_261, 2);
x_290 = lean_ctor_get(x_261, 3);
lean_inc(x_290);
lean_inc(x_289);
lean_inc(x_288);
lean_inc(x_287);
lean_dec(x_261);
lean_inc(x_188);
x_291 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_291, 0, x_188);
lean_ctor_set(x_291, 1, x_272);
lean_ctor_set(x_291, 2, x_273);
lean_ctor_set(x_291, 3, x_287);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 lean_ctor_release(x_188, 2);
 lean_ctor_release(x_188, 3);
 x_292 = x_188;
} else {
 lean_dec_ref(x_188);
 x_292 = lean_box(0);
}
lean_ctor_set_uint8(x_291, sizeof(void*)*4, x_236);
if (lean_is_scalar(x_292)) {
 x_293 = lean_alloc_ctor(1, 4, 1);
} else {
 x_293 = x_292;
}
lean_ctor_set(x_293, 0, x_290);
lean_ctor_set(x_293, 1, x_35);
lean_ctor_set(x_293, 2, x_36);
lean_ctor_set(x_293, 3, x_37);
lean_ctor_set_uint8(x_293, sizeof(void*)*4, x_236);
lean_ctor_set(x_187, 3, x_293);
lean_ctor_set(x_187, 2, x_289);
lean_ctor_set(x_187, 1, x_288);
lean_ctor_set(x_187, 0, x_291);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_270);
return x_187;
}
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_294 = lean_ctor_get(x_187, 1);
x_295 = lean_ctor_get(x_187, 2);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_187);
x_296 = lean_ctor_get(x_261, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_261, 1);
lean_inc(x_297);
x_298 = lean_ctor_get(x_261, 2);
lean_inc(x_298);
x_299 = lean_ctor_get(x_261, 3);
lean_inc(x_299);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 lean_ctor_release(x_261, 2);
 lean_ctor_release(x_261, 3);
 x_300 = x_261;
} else {
 lean_dec_ref(x_261);
 x_300 = lean_box(0);
}
lean_inc(x_188);
if (lean_is_scalar(x_300)) {
 x_301 = lean_alloc_ctor(1, 4, 1);
} else {
 x_301 = x_300;
}
lean_ctor_set(x_301, 0, x_188);
lean_ctor_set(x_301, 1, x_294);
lean_ctor_set(x_301, 2, x_295);
lean_ctor_set(x_301, 3, x_296);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 lean_ctor_release(x_188, 2);
 lean_ctor_release(x_188, 3);
 x_302 = x_188;
} else {
 lean_dec_ref(x_188);
 x_302 = lean_box(0);
}
lean_ctor_set_uint8(x_301, sizeof(void*)*4, x_236);
if (lean_is_scalar(x_302)) {
 x_303 = lean_alloc_ctor(1, 4, 1);
} else {
 x_303 = x_302;
}
lean_ctor_set(x_303, 0, x_299);
lean_ctor_set(x_303, 1, x_35);
lean_ctor_set(x_303, 2, x_36);
lean_ctor_set(x_303, 3, x_37);
lean_ctor_set_uint8(x_303, sizeof(void*)*4, x_236);
x_304 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_304, 0, x_301);
lean_ctor_set(x_304, 1, x_297);
lean_ctor_set(x_304, 2, x_298);
lean_ctor_set(x_304, 3, x_303);
lean_ctor_set_uint8(x_304, sizeof(void*)*4, x_270);
return x_304;
}
}
else
{
uint8_t x_305; 
x_305 = !lean_is_exclusive(x_187);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; uint8_t x_308; 
x_306 = lean_ctor_get(x_187, 3);
lean_dec(x_306);
x_307 = lean_ctor_get(x_187, 0);
lean_dec(x_307);
x_308 = !lean_is_exclusive(x_188);
if (x_308 == 0)
{
uint8_t x_309; 
lean_ctor_set_uint8(x_188, sizeof(void*)*4, x_270);
x_309 = 0;
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_309);
lean_ctor_set(x_1, 0, x_187);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_270);
return x_1;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; 
x_310 = lean_ctor_get(x_188, 0);
x_311 = lean_ctor_get(x_188, 1);
x_312 = lean_ctor_get(x_188, 2);
x_313 = lean_ctor_get(x_188, 3);
lean_inc(x_313);
lean_inc(x_312);
lean_inc(x_311);
lean_inc(x_310);
lean_dec(x_188);
x_314 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_314, 0, x_310);
lean_ctor_set(x_314, 1, x_311);
lean_ctor_set(x_314, 2, x_312);
lean_ctor_set(x_314, 3, x_313);
lean_ctor_set_uint8(x_314, sizeof(void*)*4, x_270);
x_315 = 0;
lean_ctor_set(x_187, 0, x_314);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_315);
lean_ctor_set(x_1, 0, x_187);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_270);
return x_1;
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; lean_object* x_325; 
x_316 = lean_ctor_get(x_187, 1);
x_317 = lean_ctor_get(x_187, 2);
lean_inc(x_317);
lean_inc(x_316);
lean_dec(x_187);
x_318 = lean_ctor_get(x_188, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_188, 1);
lean_inc(x_319);
x_320 = lean_ctor_get(x_188, 2);
lean_inc(x_320);
x_321 = lean_ctor_get(x_188, 3);
lean_inc(x_321);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 lean_ctor_release(x_188, 2);
 lean_ctor_release(x_188, 3);
 x_322 = x_188;
} else {
 lean_dec_ref(x_188);
 x_322 = lean_box(0);
}
if (lean_is_scalar(x_322)) {
 x_323 = lean_alloc_ctor(1, 4, 1);
} else {
 x_323 = x_322;
}
lean_ctor_set(x_323, 0, x_318);
lean_ctor_set(x_323, 1, x_319);
lean_ctor_set(x_323, 2, x_320);
lean_ctor_set(x_323, 3, x_321);
lean_ctor_set_uint8(x_323, sizeof(void*)*4, x_270);
x_324 = 0;
x_325 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_325, 0, x_323);
lean_ctor_set(x_325, 1, x_316);
lean_ctor_set(x_325, 2, x_317);
lean_ctor_set(x_325, 3, x_261);
lean_ctor_set_uint8(x_325, sizeof(void*)*4, x_324);
lean_ctor_set(x_1, 0, x_325);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_270);
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
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_330; uint8_t x_331; uint8_t x_332; 
x_326 = lean_ctor_get(x_1, 0);
x_327 = lean_ctor_get(x_1, 1);
x_328 = lean_ctor_get(x_1, 2);
x_329 = lean_ctor_get(x_1, 3);
lean_inc(x_329);
lean_inc(x_328);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_1);
x_330 = lean_nat_dec_lt(x_2, x_327);
x_331 = 1;
x_332 = l_Bool_DecidableEq(x_330, x_331);
if (x_332 == 0)
{
uint8_t x_333; uint8_t x_334; 
x_333 = lean_nat_dec_lt(x_327, x_2);
x_334 = l_Bool_DecidableEq(x_333, x_331);
if (x_334 == 0)
{
lean_object* x_335; 
lean_dec(x_328);
lean_dec(x_327);
x_335 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_335, 0, x_326);
lean_ctor_set(x_335, 1, x_2);
lean_ctor_set(x_335, 2, x_3);
lean_ctor_set(x_335, 3, x_329);
lean_ctor_set_uint8(x_335, sizeof(void*)*4, x_6);
return x_335;
}
else
{
uint8_t x_336; uint8_t x_337; 
x_336 = l_RBNode_isRed___rarg(x_329);
x_337 = l_Bool_DecidableEq(x_336, x_331);
if (x_337 == 0)
{
lean_object* x_338; lean_object* x_339; 
x_338 = l_RBNode_ins___main___at_Lean_IR_mkIndexSet___spec__2(x_329, x_2, x_3);
x_339 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_339, 0, x_326);
lean_ctor_set(x_339, 1, x_327);
lean_ctor_set(x_339, 2, x_328);
lean_ctor_set(x_339, 3, x_338);
lean_ctor_set_uint8(x_339, sizeof(void*)*4, x_6);
return x_339;
}
else
{
lean_object* x_340; lean_object* x_341; 
x_340 = l_RBNode_ins___main___at_Lean_IR_mkIndexSet___spec__2(x_329, x_2, x_3);
x_341 = lean_ctor_get(x_340, 0);
lean_inc(x_341);
if (lean_obj_tag(x_341) == 0)
{
lean_object* x_342; 
x_342 = lean_ctor_get(x_340, 3);
lean_inc(x_342);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; uint8_t x_346; lean_object* x_347; uint8_t x_348; lean_object* x_349; 
x_343 = lean_ctor_get(x_340, 1);
lean_inc(x_343);
x_344 = lean_ctor_get(x_340, 2);
lean_inc(x_344);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 lean_ctor_release(x_340, 2);
 lean_ctor_release(x_340, 3);
 x_345 = x_340;
} else {
 lean_dec_ref(x_340);
 x_345 = lean_box(0);
}
x_346 = 0;
if (lean_is_scalar(x_345)) {
 x_347 = lean_alloc_ctor(1, 4, 1);
} else {
 x_347 = x_345;
}
lean_ctor_set(x_347, 0, x_342);
lean_ctor_set(x_347, 1, x_343);
lean_ctor_set(x_347, 2, x_344);
lean_ctor_set(x_347, 3, x_342);
lean_ctor_set_uint8(x_347, sizeof(void*)*4, x_346);
x_348 = 1;
x_349 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_349, 0, x_326);
lean_ctor_set(x_349, 1, x_327);
lean_ctor_set(x_349, 2, x_328);
lean_ctor_set(x_349, 3, x_347);
lean_ctor_set_uint8(x_349, sizeof(void*)*4, x_348);
return x_349;
}
else
{
uint8_t x_350; 
x_350 = lean_ctor_get_uint8(x_342, sizeof(void*)*4);
if (x_350 == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_351 = lean_ctor_get(x_340, 1);
lean_inc(x_351);
x_352 = lean_ctor_get(x_340, 2);
lean_inc(x_352);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 lean_ctor_release(x_340, 2);
 lean_ctor_release(x_340, 3);
 x_353 = x_340;
} else {
 lean_dec_ref(x_340);
 x_353 = lean_box(0);
}
x_354 = lean_ctor_get(x_342, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_342, 1);
lean_inc(x_355);
x_356 = lean_ctor_get(x_342, 2);
lean_inc(x_356);
x_357 = lean_ctor_get(x_342, 3);
lean_inc(x_357);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 lean_ctor_release(x_342, 2);
 lean_ctor_release(x_342, 3);
 x_358 = x_342;
} else {
 lean_dec_ref(x_342);
 x_358 = lean_box(0);
}
x_359 = 1;
if (lean_is_scalar(x_358)) {
 x_360 = lean_alloc_ctor(1, 4, 1);
} else {
 x_360 = x_358;
}
lean_ctor_set(x_360, 0, x_326);
lean_ctor_set(x_360, 1, x_327);
lean_ctor_set(x_360, 2, x_328);
lean_ctor_set(x_360, 3, x_341);
lean_ctor_set_uint8(x_360, sizeof(void*)*4, x_359);
if (lean_is_scalar(x_353)) {
 x_361 = lean_alloc_ctor(1, 4, 1);
} else {
 x_361 = x_353;
}
lean_ctor_set(x_361, 0, x_354);
lean_ctor_set(x_361, 1, x_355);
lean_ctor_set(x_361, 2, x_356);
lean_ctor_set(x_361, 3, x_357);
lean_ctor_set_uint8(x_361, sizeof(void*)*4, x_359);
x_362 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_362, 0, x_360);
lean_ctor_set(x_362, 1, x_351);
lean_ctor_set(x_362, 2, x_352);
lean_ctor_set(x_362, 3, x_361);
lean_ctor_set_uint8(x_362, sizeof(void*)*4, x_350);
return x_362;
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; uint8_t x_366; lean_object* x_367; lean_object* x_368; 
x_363 = lean_ctor_get(x_340, 1);
lean_inc(x_363);
x_364 = lean_ctor_get(x_340, 2);
lean_inc(x_364);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 lean_ctor_release(x_340, 2);
 lean_ctor_release(x_340, 3);
 x_365 = x_340;
} else {
 lean_dec_ref(x_340);
 x_365 = lean_box(0);
}
x_366 = 0;
if (lean_is_scalar(x_365)) {
 x_367 = lean_alloc_ctor(1, 4, 1);
} else {
 x_367 = x_365;
}
lean_ctor_set(x_367, 0, x_341);
lean_ctor_set(x_367, 1, x_363);
lean_ctor_set(x_367, 2, x_364);
lean_ctor_set(x_367, 3, x_342);
lean_ctor_set_uint8(x_367, sizeof(void*)*4, x_366);
x_368 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_368, 0, x_326);
lean_ctor_set(x_368, 1, x_327);
lean_ctor_set(x_368, 2, x_328);
lean_ctor_set(x_368, 3, x_367);
lean_ctor_set_uint8(x_368, sizeof(void*)*4, x_350);
return x_368;
}
}
}
else
{
uint8_t x_369; 
x_369 = lean_ctor_get_uint8(x_341, sizeof(void*)*4);
if (x_369 == 0)
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; uint8_t x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_370 = lean_ctor_get(x_340, 1);
lean_inc(x_370);
x_371 = lean_ctor_get(x_340, 2);
lean_inc(x_371);
x_372 = lean_ctor_get(x_340, 3);
lean_inc(x_372);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 lean_ctor_release(x_340, 2);
 lean_ctor_release(x_340, 3);
 x_373 = x_340;
} else {
 lean_dec_ref(x_340);
 x_373 = lean_box(0);
}
x_374 = lean_ctor_get(x_341, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_341, 1);
lean_inc(x_375);
x_376 = lean_ctor_get(x_341, 2);
lean_inc(x_376);
x_377 = lean_ctor_get(x_341, 3);
lean_inc(x_377);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 lean_ctor_release(x_341, 2);
 lean_ctor_release(x_341, 3);
 x_378 = x_341;
} else {
 lean_dec_ref(x_341);
 x_378 = lean_box(0);
}
x_379 = 1;
if (lean_is_scalar(x_378)) {
 x_380 = lean_alloc_ctor(1, 4, 1);
} else {
 x_380 = x_378;
}
lean_ctor_set(x_380, 0, x_326);
lean_ctor_set(x_380, 1, x_327);
lean_ctor_set(x_380, 2, x_328);
lean_ctor_set(x_380, 3, x_374);
lean_ctor_set_uint8(x_380, sizeof(void*)*4, x_379);
if (lean_is_scalar(x_373)) {
 x_381 = lean_alloc_ctor(1, 4, 1);
} else {
 x_381 = x_373;
}
lean_ctor_set(x_381, 0, x_377);
lean_ctor_set(x_381, 1, x_370);
lean_ctor_set(x_381, 2, x_371);
lean_ctor_set(x_381, 3, x_372);
lean_ctor_set_uint8(x_381, sizeof(void*)*4, x_379);
x_382 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_382, 0, x_380);
lean_ctor_set(x_382, 1, x_375);
lean_ctor_set(x_382, 2, x_376);
lean_ctor_set(x_382, 3, x_381);
lean_ctor_set_uint8(x_382, sizeof(void*)*4, x_369);
return x_382;
}
else
{
lean_object* x_383; 
x_383 = lean_ctor_get(x_340, 3);
lean_inc(x_383);
if (lean_obj_tag(x_383) == 0)
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; uint8_t x_387; lean_object* x_388; lean_object* x_389; 
x_384 = lean_ctor_get(x_340, 1);
lean_inc(x_384);
x_385 = lean_ctor_get(x_340, 2);
lean_inc(x_385);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 lean_ctor_release(x_340, 2);
 lean_ctor_release(x_340, 3);
 x_386 = x_340;
} else {
 lean_dec_ref(x_340);
 x_386 = lean_box(0);
}
x_387 = 0;
if (lean_is_scalar(x_386)) {
 x_388 = lean_alloc_ctor(1, 4, 1);
} else {
 x_388 = x_386;
}
lean_ctor_set(x_388, 0, x_341);
lean_ctor_set(x_388, 1, x_384);
lean_ctor_set(x_388, 2, x_385);
lean_ctor_set(x_388, 3, x_383);
lean_ctor_set_uint8(x_388, sizeof(void*)*4, x_387);
x_389 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_389, 0, x_326);
lean_ctor_set(x_389, 1, x_327);
lean_ctor_set(x_389, 2, x_328);
lean_ctor_set(x_389, 3, x_388);
lean_ctor_set_uint8(x_389, sizeof(void*)*4, x_369);
return x_389;
}
else
{
uint8_t x_390; 
x_390 = lean_ctor_get_uint8(x_383, sizeof(void*)*4);
if (x_390 == 0)
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_391 = lean_ctor_get(x_340, 1);
lean_inc(x_391);
x_392 = lean_ctor_get(x_340, 2);
lean_inc(x_392);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 lean_ctor_release(x_340, 2);
 lean_ctor_release(x_340, 3);
 x_393 = x_340;
} else {
 lean_dec_ref(x_340);
 x_393 = lean_box(0);
}
x_394 = lean_ctor_get(x_383, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_383, 1);
lean_inc(x_395);
x_396 = lean_ctor_get(x_383, 2);
lean_inc(x_396);
x_397 = lean_ctor_get(x_383, 3);
lean_inc(x_397);
if (lean_is_exclusive(x_383)) {
 lean_ctor_release(x_383, 0);
 lean_ctor_release(x_383, 1);
 lean_ctor_release(x_383, 2);
 lean_ctor_release(x_383, 3);
 x_398 = x_383;
} else {
 lean_dec_ref(x_383);
 x_398 = lean_box(0);
}
lean_inc(x_341);
if (lean_is_scalar(x_398)) {
 x_399 = lean_alloc_ctor(1, 4, 1);
} else {
 x_399 = x_398;
}
lean_ctor_set(x_399, 0, x_326);
lean_ctor_set(x_399, 1, x_327);
lean_ctor_set(x_399, 2, x_328);
lean_ctor_set(x_399, 3, x_341);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 lean_ctor_release(x_341, 2);
 lean_ctor_release(x_341, 3);
 x_400 = x_341;
} else {
 lean_dec_ref(x_341);
 x_400 = lean_box(0);
}
lean_ctor_set_uint8(x_399, sizeof(void*)*4, x_369);
if (lean_is_scalar(x_400)) {
 x_401 = lean_alloc_ctor(1, 4, 1);
} else {
 x_401 = x_400;
}
lean_ctor_set(x_401, 0, x_394);
lean_ctor_set(x_401, 1, x_395);
lean_ctor_set(x_401, 2, x_396);
lean_ctor_set(x_401, 3, x_397);
lean_ctor_set_uint8(x_401, sizeof(void*)*4, x_369);
if (lean_is_scalar(x_393)) {
 x_402 = lean_alloc_ctor(1, 4, 1);
} else {
 x_402 = x_393;
}
lean_ctor_set(x_402, 0, x_399);
lean_ctor_set(x_402, 1, x_391);
lean_ctor_set(x_402, 2, x_392);
lean_ctor_set(x_402, 3, x_401);
lean_ctor_set_uint8(x_402, sizeof(void*)*4, x_390);
return x_402;
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; uint8_t x_412; lean_object* x_413; lean_object* x_414; 
x_403 = lean_ctor_get(x_340, 1);
lean_inc(x_403);
x_404 = lean_ctor_get(x_340, 2);
lean_inc(x_404);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 lean_ctor_release(x_340, 2);
 lean_ctor_release(x_340, 3);
 x_405 = x_340;
} else {
 lean_dec_ref(x_340);
 x_405 = lean_box(0);
}
x_406 = lean_ctor_get(x_341, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_341, 1);
lean_inc(x_407);
x_408 = lean_ctor_get(x_341, 2);
lean_inc(x_408);
x_409 = lean_ctor_get(x_341, 3);
lean_inc(x_409);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 lean_ctor_release(x_341, 2);
 lean_ctor_release(x_341, 3);
 x_410 = x_341;
} else {
 lean_dec_ref(x_341);
 x_410 = lean_box(0);
}
if (lean_is_scalar(x_410)) {
 x_411 = lean_alloc_ctor(1, 4, 1);
} else {
 x_411 = x_410;
}
lean_ctor_set(x_411, 0, x_406);
lean_ctor_set(x_411, 1, x_407);
lean_ctor_set(x_411, 2, x_408);
lean_ctor_set(x_411, 3, x_409);
lean_ctor_set_uint8(x_411, sizeof(void*)*4, x_390);
x_412 = 0;
if (lean_is_scalar(x_405)) {
 x_413 = lean_alloc_ctor(1, 4, 1);
} else {
 x_413 = x_405;
}
lean_ctor_set(x_413, 0, x_411);
lean_ctor_set(x_413, 1, x_403);
lean_ctor_set(x_413, 2, x_404);
lean_ctor_set(x_413, 3, x_383);
lean_ctor_set_uint8(x_413, sizeof(void*)*4, x_412);
x_414 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_414, 0, x_326);
lean_ctor_set(x_414, 1, x_327);
lean_ctor_set(x_414, 2, x_328);
lean_ctor_set(x_414, 3, x_413);
lean_ctor_set_uint8(x_414, sizeof(void*)*4, x_390);
return x_414;
}
}
}
}
}
}
}
else
{
uint8_t x_415; uint8_t x_416; 
x_415 = l_RBNode_isRed___rarg(x_326);
x_416 = l_Bool_DecidableEq(x_415, x_331);
if (x_416 == 0)
{
lean_object* x_417; lean_object* x_418; 
x_417 = l_RBNode_ins___main___at_Lean_IR_mkIndexSet___spec__2(x_326, x_2, x_3);
x_418 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_418, 0, x_417);
lean_ctor_set(x_418, 1, x_327);
lean_ctor_set(x_418, 2, x_328);
lean_ctor_set(x_418, 3, x_329);
lean_ctor_set_uint8(x_418, sizeof(void*)*4, x_6);
return x_418;
}
else
{
lean_object* x_419; lean_object* x_420; 
x_419 = l_RBNode_ins___main___at_Lean_IR_mkIndexSet___spec__2(x_326, x_2, x_3);
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_421; 
x_421 = lean_ctor_get(x_419, 3);
lean_inc(x_421);
if (lean_obj_tag(x_421) == 0)
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; uint8_t x_425; lean_object* x_426; uint8_t x_427; lean_object* x_428; 
x_422 = lean_ctor_get(x_419, 1);
lean_inc(x_422);
x_423 = lean_ctor_get(x_419, 2);
lean_inc(x_423);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 lean_ctor_release(x_419, 2);
 lean_ctor_release(x_419, 3);
 x_424 = x_419;
} else {
 lean_dec_ref(x_419);
 x_424 = lean_box(0);
}
x_425 = 0;
if (lean_is_scalar(x_424)) {
 x_426 = lean_alloc_ctor(1, 4, 1);
} else {
 x_426 = x_424;
}
lean_ctor_set(x_426, 0, x_421);
lean_ctor_set(x_426, 1, x_422);
lean_ctor_set(x_426, 2, x_423);
lean_ctor_set(x_426, 3, x_421);
lean_ctor_set_uint8(x_426, sizeof(void*)*4, x_425);
x_427 = 1;
x_428 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_428, 0, x_426);
lean_ctor_set(x_428, 1, x_327);
lean_ctor_set(x_428, 2, x_328);
lean_ctor_set(x_428, 3, x_329);
lean_ctor_set_uint8(x_428, sizeof(void*)*4, x_427);
return x_428;
}
else
{
uint8_t x_429; 
x_429 = lean_ctor_get_uint8(x_421, sizeof(void*)*4);
if (x_429 == 0)
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; uint8_t x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_430 = lean_ctor_get(x_419, 1);
lean_inc(x_430);
x_431 = lean_ctor_get(x_419, 2);
lean_inc(x_431);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 lean_ctor_release(x_419, 2);
 lean_ctor_release(x_419, 3);
 x_432 = x_419;
} else {
 lean_dec_ref(x_419);
 x_432 = lean_box(0);
}
x_433 = lean_ctor_get(x_421, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_421, 1);
lean_inc(x_434);
x_435 = lean_ctor_get(x_421, 2);
lean_inc(x_435);
x_436 = lean_ctor_get(x_421, 3);
lean_inc(x_436);
if (lean_is_exclusive(x_421)) {
 lean_ctor_release(x_421, 0);
 lean_ctor_release(x_421, 1);
 lean_ctor_release(x_421, 2);
 lean_ctor_release(x_421, 3);
 x_437 = x_421;
} else {
 lean_dec_ref(x_421);
 x_437 = lean_box(0);
}
x_438 = 1;
if (lean_is_scalar(x_437)) {
 x_439 = lean_alloc_ctor(1, 4, 1);
} else {
 x_439 = x_437;
}
lean_ctor_set(x_439, 0, x_420);
lean_ctor_set(x_439, 1, x_430);
lean_ctor_set(x_439, 2, x_431);
lean_ctor_set(x_439, 3, x_433);
lean_ctor_set_uint8(x_439, sizeof(void*)*4, x_438);
if (lean_is_scalar(x_432)) {
 x_440 = lean_alloc_ctor(1, 4, 1);
} else {
 x_440 = x_432;
}
lean_ctor_set(x_440, 0, x_436);
lean_ctor_set(x_440, 1, x_327);
lean_ctor_set(x_440, 2, x_328);
lean_ctor_set(x_440, 3, x_329);
lean_ctor_set_uint8(x_440, sizeof(void*)*4, x_438);
x_441 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_441, 0, x_439);
lean_ctor_set(x_441, 1, x_434);
lean_ctor_set(x_441, 2, x_435);
lean_ctor_set(x_441, 3, x_440);
lean_ctor_set_uint8(x_441, sizeof(void*)*4, x_429);
return x_441;
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; uint8_t x_445; lean_object* x_446; lean_object* x_447; 
x_442 = lean_ctor_get(x_419, 1);
lean_inc(x_442);
x_443 = lean_ctor_get(x_419, 2);
lean_inc(x_443);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 lean_ctor_release(x_419, 2);
 lean_ctor_release(x_419, 3);
 x_444 = x_419;
} else {
 lean_dec_ref(x_419);
 x_444 = lean_box(0);
}
x_445 = 0;
if (lean_is_scalar(x_444)) {
 x_446 = lean_alloc_ctor(1, 4, 1);
} else {
 x_446 = x_444;
}
lean_ctor_set(x_446, 0, x_420);
lean_ctor_set(x_446, 1, x_442);
lean_ctor_set(x_446, 2, x_443);
lean_ctor_set(x_446, 3, x_421);
lean_ctor_set_uint8(x_446, sizeof(void*)*4, x_445);
x_447 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_447, 0, x_446);
lean_ctor_set(x_447, 1, x_327);
lean_ctor_set(x_447, 2, x_328);
lean_ctor_set(x_447, 3, x_329);
lean_ctor_set_uint8(x_447, sizeof(void*)*4, x_429);
return x_447;
}
}
}
else
{
uint8_t x_448; 
x_448 = lean_ctor_get_uint8(x_420, sizeof(void*)*4);
if (x_448 == 0)
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; uint8_t x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; 
x_449 = lean_ctor_get(x_419, 1);
lean_inc(x_449);
x_450 = lean_ctor_get(x_419, 2);
lean_inc(x_450);
x_451 = lean_ctor_get(x_419, 3);
lean_inc(x_451);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 lean_ctor_release(x_419, 2);
 lean_ctor_release(x_419, 3);
 x_452 = x_419;
} else {
 lean_dec_ref(x_419);
 x_452 = lean_box(0);
}
x_453 = lean_ctor_get(x_420, 0);
lean_inc(x_453);
x_454 = lean_ctor_get(x_420, 1);
lean_inc(x_454);
x_455 = lean_ctor_get(x_420, 2);
lean_inc(x_455);
x_456 = lean_ctor_get(x_420, 3);
lean_inc(x_456);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 lean_ctor_release(x_420, 2);
 lean_ctor_release(x_420, 3);
 x_457 = x_420;
} else {
 lean_dec_ref(x_420);
 x_457 = lean_box(0);
}
x_458 = 1;
if (lean_is_scalar(x_457)) {
 x_459 = lean_alloc_ctor(1, 4, 1);
} else {
 x_459 = x_457;
}
lean_ctor_set(x_459, 0, x_453);
lean_ctor_set(x_459, 1, x_454);
lean_ctor_set(x_459, 2, x_455);
lean_ctor_set(x_459, 3, x_456);
lean_ctor_set_uint8(x_459, sizeof(void*)*4, x_458);
if (lean_is_scalar(x_452)) {
 x_460 = lean_alloc_ctor(1, 4, 1);
} else {
 x_460 = x_452;
}
lean_ctor_set(x_460, 0, x_451);
lean_ctor_set(x_460, 1, x_327);
lean_ctor_set(x_460, 2, x_328);
lean_ctor_set(x_460, 3, x_329);
lean_ctor_set_uint8(x_460, sizeof(void*)*4, x_458);
x_461 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_461, 0, x_459);
lean_ctor_set(x_461, 1, x_449);
lean_ctor_set(x_461, 2, x_450);
lean_ctor_set(x_461, 3, x_460);
lean_ctor_set_uint8(x_461, sizeof(void*)*4, x_448);
return x_461;
}
else
{
lean_object* x_462; 
x_462 = lean_ctor_get(x_419, 3);
lean_inc(x_462);
if (lean_obj_tag(x_462) == 0)
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; uint8_t x_466; lean_object* x_467; lean_object* x_468; 
x_463 = lean_ctor_get(x_419, 1);
lean_inc(x_463);
x_464 = lean_ctor_get(x_419, 2);
lean_inc(x_464);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 lean_ctor_release(x_419, 2);
 lean_ctor_release(x_419, 3);
 x_465 = x_419;
} else {
 lean_dec_ref(x_419);
 x_465 = lean_box(0);
}
x_466 = 0;
if (lean_is_scalar(x_465)) {
 x_467 = lean_alloc_ctor(1, 4, 1);
} else {
 x_467 = x_465;
}
lean_ctor_set(x_467, 0, x_420);
lean_ctor_set(x_467, 1, x_463);
lean_ctor_set(x_467, 2, x_464);
lean_ctor_set(x_467, 3, x_462);
lean_ctor_set_uint8(x_467, sizeof(void*)*4, x_466);
x_468 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_468, 0, x_467);
lean_ctor_set(x_468, 1, x_327);
lean_ctor_set(x_468, 2, x_328);
lean_ctor_set(x_468, 3, x_329);
lean_ctor_set_uint8(x_468, sizeof(void*)*4, x_448);
return x_468;
}
else
{
uint8_t x_469; 
x_469 = lean_ctor_get_uint8(x_462, sizeof(void*)*4);
if (x_469 == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_470 = lean_ctor_get(x_419, 1);
lean_inc(x_470);
x_471 = lean_ctor_get(x_419, 2);
lean_inc(x_471);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 lean_ctor_release(x_419, 2);
 lean_ctor_release(x_419, 3);
 x_472 = x_419;
} else {
 lean_dec_ref(x_419);
 x_472 = lean_box(0);
}
x_473 = lean_ctor_get(x_462, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_462, 1);
lean_inc(x_474);
x_475 = lean_ctor_get(x_462, 2);
lean_inc(x_475);
x_476 = lean_ctor_get(x_462, 3);
lean_inc(x_476);
if (lean_is_exclusive(x_462)) {
 lean_ctor_release(x_462, 0);
 lean_ctor_release(x_462, 1);
 lean_ctor_release(x_462, 2);
 lean_ctor_release(x_462, 3);
 x_477 = x_462;
} else {
 lean_dec_ref(x_462);
 x_477 = lean_box(0);
}
lean_inc(x_420);
if (lean_is_scalar(x_477)) {
 x_478 = lean_alloc_ctor(1, 4, 1);
} else {
 x_478 = x_477;
}
lean_ctor_set(x_478, 0, x_420);
lean_ctor_set(x_478, 1, x_470);
lean_ctor_set(x_478, 2, x_471);
lean_ctor_set(x_478, 3, x_473);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 lean_ctor_release(x_420, 2);
 lean_ctor_release(x_420, 3);
 x_479 = x_420;
} else {
 lean_dec_ref(x_420);
 x_479 = lean_box(0);
}
lean_ctor_set_uint8(x_478, sizeof(void*)*4, x_448);
if (lean_is_scalar(x_479)) {
 x_480 = lean_alloc_ctor(1, 4, 1);
} else {
 x_480 = x_479;
}
lean_ctor_set(x_480, 0, x_476);
lean_ctor_set(x_480, 1, x_327);
lean_ctor_set(x_480, 2, x_328);
lean_ctor_set(x_480, 3, x_329);
lean_ctor_set_uint8(x_480, sizeof(void*)*4, x_448);
if (lean_is_scalar(x_472)) {
 x_481 = lean_alloc_ctor(1, 4, 1);
} else {
 x_481 = x_472;
}
lean_ctor_set(x_481, 0, x_478);
lean_ctor_set(x_481, 1, x_474);
lean_ctor_set(x_481, 2, x_475);
lean_ctor_set(x_481, 3, x_480);
lean_ctor_set_uint8(x_481, sizeof(void*)*4, x_469);
return x_481;
}
else
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; uint8_t x_491; lean_object* x_492; lean_object* x_493; 
x_482 = lean_ctor_get(x_419, 1);
lean_inc(x_482);
x_483 = lean_ctor_get(x_419, 2);
lean_inc(x_483);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 lean_ctor_release(x_419, 2);
 lean_ctor_release(x_419, 3);
 x_484 = x_419;
} else {
 lean_dec_ref(x_419);
 x_484 = lean_box(0);
}
x_485 = lean_ctor_get(x_420, 0);
lean_inc(x_485);
x_486 = lean_ctor_get(x_420, 1);
lean_inc(x_486);
x_487 = lean_ctor_get(x_420, 2);
lean_inc(x_487);
x_488 = lean_ctor_get(x_420, 3);
lean_inc(x_488);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 lean_ctor_release(x_420, 2);
 lean_ctor_release(x_420, 3);
 x_489 = x_420;
} else {
 lean_dec_ref(x_420);
 x_489 = lean_box(0);
}
if (lean_is_scalar(x_489)) {
 x_490 = lean_alloc_ctor(1, 4, 1);
} else {
 x_490 = x_489;
}
lean_ctor_set(x_490, 0, x_485);
lean_ctor_set(x_490, 1, x_486);
lean_ctor_set(x_490, 2, x_487);
lean_ctor_set(x_490, 3, x_488);
lean_ctor_set_uint8(x_490, sizeof(void*)*4, x_469);
x_491 = 0;
if (lean_is_scalar(x_484)) {
 x_492 = lean_alloc_ctor(1, 4, 1);
} else {
 x_492 = x_484;
}
lean_ctor_set(x_492, 0, x_490);
lean_ctor_set(x_492, 1, x_482);
lean_ctor_set(x_492, 2, x_483);
lean_ctor_set(x_492, 3, x_462);
lean_ctor_set_uint8(x_492, sizeof(void*)*4, x_491);
x_493 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_493, 0, x_492);
lean_ctor_set(x_493, 1, x_327);
lean_ctor_set(x_493, 2, x_328);
lean_ctor_set(x_493, 3, x_329);
lean_ctor_set_uint8(x_493, sizeof(void*)*4, x_469);
return x_493;
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
uint8_t x_4; uint8_t x_5; uint8_t x_6; 
x_4 = l_RBNode_isRed___rarg(x_1);
x_5 = 1;
x_6 = l_Bool_DecidableEq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = l_RBNode_ins___main___at_Lean_IR_mkIndexSet___spec__2(x_1, x_2, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_RBNode_ins___main___at_Lean_IR_mkIndexSet___spec__2(x_1, x_2, x_3);
x_9 = l_RBNode_setBlack___rarg(x_8);
return x_9;
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
uint8_t x_4; lean_object* x_5; 
x_4 = 0;
x_5 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*4, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 3);
x_12 = lean_nat_dec_lt(x_2, x_9);
x_13 = 1;
x_14 = l_Bool_DecidableEq(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; uint8_t x_16; 
x_15 = lean_nat_dec_lt(x_9, x_2);
x_16 = l_Bool_DecidableEq(x_15, x_13);
if (x_16 == 0)
{
lean_dec(x_10);
lean_dec(x_9);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
lean_object* x_17; 
x_17 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_11, x_2, x_3);
lean_ctor_set(x_1, 3, x_17);
return x_1;
}
}
else
{
lean_object* x_18; 
x_18 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_8, x_2, x_3);
lean_ctor_set(x_1, 0, x_18);
return x_1;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_ctor_get(x_1, 2);
x_22 = lean_ctor_get(x_1, 3);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_23 = lean_nat_dec_lt(x_2, x_20);
x_24 = 1;
x_25 = l_Bool_DecidableEq(x_23, x_24);
if (x_25 == 0)
{
uint8_t x_26; uint8_t x_27; 
x_26 = lean_nat_dec_lt(x_20, x_2);
x_27 = l_Bool_DecidableEq(x_26, x_24);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_21);
lean_dec(x_20);
x_28 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_2);
lean_ctor_set(x_28, 2, x_3);
lean_ctor_set(x_28, 3, x_22);
lean_ctor_set_uint8(x_28, sizeof(void*)*4, x_6);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_22, x_2, x_3);
x_30 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_30, 0, x_19);
lean_ctor_set(x_30, 1, x_20);
lean_ctor_set(x_30, 2, x_21);
lean_ctor_set(x_30, 3, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_6);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_19, x_2, x_3);
x_32 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_20);
lean_ctor_set(x_32, 2, x_21);
lean_ctor_set(x_32, 3, x_22);
lean_ctor_set_uint8(x_32, sizeof(void*)*4, x_6);
return x_32;
}
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_1);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; 
x_34 = lean_ctor_get(x_1, 0);
x_35 = lean_ctor_get(x_1, 1);
x_36 = lean_ctor_get(x_1, 2);
x_37 = lean_ctor_get(x_1, 3);
x_38 = lean_nat_dec_lt(x_2, x_35);
x_39 = 1;
x_40 = l_Bool_DecidableEq(x_38, x_39);
if (x_40 == 0)
{
uint8_t x_41; uint8_t x_42; 
x_41 = lean_nat_dec_lt(x_35, x_2);
x_42 = l_Bool_DecidableEq(x_41, x_39);
if (x_42 == 0)
{
lean_dec(x_36);
lean_dec(x_35);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
uint8_t x_43; uint8_t x_44; 
x_43 = l_RBNode_isRed___rarg(x_37);
x_44 = l_Bool_DecidableEq(x_43, x_39);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_37, x_2, x_3);
lean_ctor_set(x_1, 3, x_45);
return x_1;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_37, x_2, x_3);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_46, 3);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_46);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_46, 3);
lean_dec(x_50);
x_51 = lean_ctor_get(x_46, 0);
lean_dec(x_51);
x_52 = 0;
lean_ctor_set(x_46, 0, x_48);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_52);
x_53 = 1;
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_53);
return x_1;
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_ctor_get(x_46, 1);
x_55 = lean_ctor_get(x_46, 2);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_46);
x_56 = 0;
x_57 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_57, 0, x_48);
lean_ctor_set(x_57, 1, x_54);
lean_ctor_set(x_57, 2, x_55);
lean_ctor_set(x_57, 3, x_48);
lean_ctor_set_uint8(x_57, sizeof(void*)*4, x_56);
x_58 = 1;
lean_ctor_set(x_1, 3, x_57);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_58);
return x_1;
}
}
else
{
uint8_t x_59; 
x_59 = lean_ctor_get_uint8(x_48, sizeof(void*)*4);
if (x_59 == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_46);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_61 = lean_ctor_get(x_46, 1);
x_62 = lean_ctor_get(x_46, 2);
x_63 = lean_ctor_get(x_46, 3);
lean_dec(x_63);
x_64 = lean_ctor_get(x_46, 0);
lean_dec(x_64);
x_65 = !lean_is_exclusive(x_48);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_66 = lean_ctor_get(x_48, 0);
x_67 = lean_ctor_get(x_48, 1);
x_68 = lean_ctor_get(x_48, 2);
x_69 = lean_ctor_get(x_48, 3);
x_70 = 1;
lean_ctor_set(x_48, 3, x_47);
lean_ctor_set(x_48, 2, x_36);
lean_ctor_set(x_48, 1, x_35);
lean_ctor_set(x_48, 0, x_34);
lean_ctor_set_uint8(x_48, sizeof(void*)*4, x_70);
lean_ctor_set(x_46, 3, x_69);
lean_ctor_set(x_46, 2, x_68);
lean_ctor_set(x_46, 1, x_67);
lean_ctor_set(x_46, 0, x_66);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_70);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set(x_1, 2, x_62);
lean_ctor_set(x_1, 1, x_61);
lean_ctor_set(x_1, 0, x_48);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_59);
return x_1;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; 
x_71 = lean_ctor_get(x_48, 0);
x_72 = lean_ctor_get(x_48, 1);
x_73 = lean_ctor_get(x_48, 2);
x_74 = lean_ctor_get(x_48, 3);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_48);
x_75 = 1;
x_76 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_76, 0, x_34);
lean_ctor_set(x_76, 1, x_35);
lean_ctor_set(x_76, 2, x_36);
lean_ctor_set(x_76, 3, x_47);
lean_ctor_set_uint8(x_76, sizeof(void*)*4, x_75);
lean_ctor_set(x_46, 3, x_74);
lean_ctor_set(x_46, 2, x_73);
lean_ctor_set(x_46, 1, x_72);
lean_ctor_set(x_46, 0, x_71);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_75);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set(x_1, 2, x_62);
lean_ctor_set(x_1, 1, x_61);
lean_ctor_set(x_1, 0, x_76);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_59);
return x_1;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; 
x_77 = lean_ctor_get(x_46, 1);
x_78 = lean_ctor_get(x_46, 2);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_46);
x_79 = lean_ctor_get(x_48, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_48, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_48, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_48, 3);
lean_inc(x_82);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 lean_ctor_release(x_48, 2);
 lean_ctor_release(x_48, 3);
 x_83 = x_48;
} else {
 lean_dec_ref(x_48);
 x_83 = lean_box(0);
}
x_84 = 1;
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(1, 4, 1);
} else {
 x_85 = x_83;
}
lean_ctor_set(x_85, 0, x_34);
lean_ctor_set(x_85, 1, x_35);
lean_ctor_set(x_85, 2, x_36);
lean_ctor_set(x_85, 3, x_47);
lean_ctor_set_uint8(x_85, sizeof(void*)*4, x_84);
x_86 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_86, 0, x_79);
lean_ctor_set(x_86, 1, x_80);
lean_ctor_set(x_86, 2, x_81);
lean_ctor_set(x_86, 3, x_82);
lean_ctor_set_uint8(x_86, sizeof(void*)*4, x_84);
lean_ctor_set(x_1, 3, x_86);
lean_ctor_set(x_1, 2, x_78);
lean_ctor_set(x_1, 1, x_77);
lean_ctor_set(x_1, 0, x_85);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_59);
return x_1;
}
}
else
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_46);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_88 = lean_ctor_get(x_46, 3);
lean_dec(x_88);
x_89 = lean_ctor_get(x_46, 0);
lean_dec(x_89);
x_90 = 0;
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_90);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_59);
return x_1;
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_46, 1);
x_92 = lean_ctor_get(x_46, 2);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_46);
x_93 = 0;
x_94 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_94, 0, x_47);
lean_ctor_set(x_94, 1, x_91);
lean_ctor_set(x_94, 2, x_92);
lean_ctor_set(x_94, 3, x_48);
lean_ctor_set_uint8(x_94, sizeof(void*)*4, x_93);
lean_ctor_set(x_1, 3, x_94);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_59);
return x_1;
}
}
}
}
else
{
uint8_t x_95; 
x_95 = lean_ctor_get_uint8(x_47, sizeof(void*)*4);
if (x_95 == 0)
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_46);
if (x_96 == 0)
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_ctor_get(x_46, 0);
lean_dec(x_97);
x_98 = !lean_is_exclusive(x_47);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_99 = lean_ctor_get(x_47, 0);
x_100 = lean_ctor_get(x_47, 1);
x_101 = lean_ctor_get(x_47, 2);
x_102 = lean_ctor_get(x_47, 3);
x_103 = 1;
lean_ctor_set(x_47, 3, x_99);
lean_ctor_set(x_47, 2, x_36);
lean_ctor_set(x_47, 1, x_35);
lean_ctor_set(x_47, 0, x_34);
lean_ctor_set_uint8(x_47, sizeof(void*)*4, x_103);
lean_ctor_set(x_46, 0, x_102);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_103);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set(x_1, 2, x_101);
lean_ctor_set(x_1, 1, x_100);
lean_ctor_set(x_1, 0, x_47);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_95);
return x_1;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; 
x_104 = lean_ctor_get(x_47, 0);
x_105 = lean_ctor_get(x_47, 1);
x_106 = lean_ctor_get(x_47, 2);
x_107 = lean_ctor_get(x_47, 3);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_47);
x_108 = 1;
x_109 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_109, 0, x_34);
lean_ctor_set(x_109, 1, x_35);
lean_ctor_set(x_109, 2, x_36);
lean_ctor_set(x_109, 3, x_104);
lean_ctor_set_uint8(x_109, sizeof(void*)*4, x_108);
lean_ctor_set(x_46, 0, x_107);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_108);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set(x_1, 2, x_106);
lean_ctor_set(x_1, 1, x_105);
lean_ctor_set(x_1, 0, x_109);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_95);
return x_1;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; 
x_110 = lean_ctor_get(x_46, 1);
x_111 = lean_ctor_get(x_46, 2);
x_112 = lean_ctor_get(x_46, 3);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_46);
x_113 = lean_ctor_get(x_47, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_47, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_47, 2);
lean_inc(x_115);
x_116 = lean_ctor_get(x_47, 3);
lean_inc(x_116);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_117 = x_47;
} else {
 lean_dec_ref(x_47);
 x_117 = lean_box(0);
}
x_118 = 1;
if (lean_is_scalar(x_117)) {
 x_119 = lean_alloc_ctor(1, 4, 1);
} else {
 x_119 = x_117;
}
lean_ctor_set(x_119, 0, x_34);
lean_ctor_set(x_119, 1, x_35);
lean_ctor_set(x_119, 2, x_36);
lean_ctor_set(x_119, 3, x_113);
lean_ctor_set_uint8(x_119, sizeof(void*)*4, x_118);
x_120 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_120, 0, x_116);
lean_ctor_set(x_120, 1, x_110);
lean_ctor_set(x_120, 2, x_111);
lean_ctor_set(x_120, 3, x_112);
lean_ctor_set_uint8(x_120, sizeof(void*)*4, x_118);
lean_ctor_set(x_1, 3, x_120);
lean_ctor_set(x_1, 2, x_115);
lean_ctor_set(x_1, 1, x_114);
lean_ctor_set(x_1, 0, x_119);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_95);
return x_1;
}
}
else
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_46, 3);
lean_inc(x_121);
if (lean_obj_tag(x_121) == 0)
{
uint8_t x_122; 
x_122 = !lean_is_exclusive(x_46);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_123 = lean_ctor_get(x_46, 3);
lean_dec(x_123);
x_124 = lean_ctor_get(x_46, 0);
lean_dec(x_124);
x_125 = 0;
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_125);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_95);
return x_1;
}
else
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; 
x_126 = lean_ctor_get(x_46, 1);
x_127 = lean_ctor_get(x_46, 2);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_46);
x_128 = 0;
x_129 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_129, 0, x_47);
lean_ctor_set(x_129, 1, x_126);
lean_ctor_set(x_129, 2, x_127);
lean_ctor_set(x_129, 3, x_121);
lean_ctor_set_uint8(x_129, sizeof(void*)*4, x_128);
lean_ctor_set(x_1, 3, x_129);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_95);
return x_1;
}
}
else
{
uint8_t x_130; 
x_130 = lean_ctor_get_uint8(x_121, sizeof(void*)*4);
if (x_130 == 0)
{
uint8_t x_131; 
lean_free_object(x_1);
x_131 = !lean_is_exclusive(x_46);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_132 = lean_ctor_get(x_46, 3);
lean_dec(x_132);
x_133 = lean_ctor_get(x_46, 0);
lean_dec(x_133);
x_134 = !lean_is_exclusive(x_121);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_135 = lean_ctor_get(x_121, 0);
x_136 = lean_ctor_get(x_121, 1);
x_137 = lean_ctor_get(x_121, 2);
x_138 = lean_ctor_get(x_121, 3);
lean_inc(x_47);
lean_ctor_set(x_121, 3, x_47);
lean_ctor_set(x_121, 2, x_36);
lean_ctor_set(x_121, 1, x_35);
lean_ctor_set(x_121, 0, x_34);
x_139 = !lean_is_exclusive(x_47);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_140 = lean_ctor_get(x_47, 3);
lean_dec(x_140);
x_141 = lean_ctor_get(x_47, 2);
lean_dec(x_141);
x_142 = lean_ctor_get(x_47, 1);
lean_dec(x_142);
x_143 = lean_ctor_get(x_47, 0);
lean_dec(x_143);
lean_ctor_set_uint8(x_121, sizeof(void*)*4, x_95);
lean_ctor_set(x_47, 3, x_138);
lean_ctor_set(x_47, 2, x_137);
lean_ctor_set(x_47, 1, x_136);
lean_ctor_set(x_47, 0, x_135);
lean_ctor_set(x_46, 3, x_47);
lean_ctor_set(x_46, 0, x_121);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_130);
return x_46;
}
else
{
lean_object* x_144; 
lean_dec(x_47);
lean_ctor_set_uint8(x_121, sizeof(void*)*4, x_95);
x_144 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_144, 0, x_135);
lean_ctor_set(x_144, 1, x_136);
lean_ctor_set(x_144, 2, x_137);
lean_ctor_set(x_144, 3, x_138);
lean_ctor_set_uint8(x_144, sizeof(void*)*4, x_95);
lean_ctor_set(x_46, 3, x_144);
lean_ctor_set(x_46, 0, x_121);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_130);
return x_46;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_145 = lean_ctor_get(x_121, 0);
x_146 = lean_ctor_get(x_121, 1);
x_147 = lean_ctor_get(x_121, 2);
x_148 = lean_ctor_get(x_121, 3);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_121);
lean_inc(x_47);
x_149 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_149, 0, x_34);
lean_ctor_set(x_149, 1, x_35);
lean_ctor_set(x_149, 2, x_36);
lean_ctor_set(x_149, 3, x_47);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_150 = x_47;
} else {
 lean_dec_ref(x_47);
 x_150 = lean_box(0);
}
lean_ctor_set_uint8(x_149, sizeof(void*)*4, x_95);
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 4, 1);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_145);
lean_ctor_set(x_151, 1, x_146);
lean_ctor_set(x_151, 2, x_147);
lean_ctor_set(x_151, 3, x_148);
lean_ctor_set_uint8(x_151, sizeof(void*)*4, x_95);
lean_ctor_set(x_46, 3, x_151);
lean_ctor_set(x_46, 0, x_149);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_130);
return x_46;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_152 = lean_ctor_get(x_46, 1);
x_153 = lean_ctor_get(x_46, 2);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_46);
x_154 = lean_ctor_get(x_121, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_121, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_121, 2);
lean_inc(x_156);
x_157 = lean_ctor_get(x_121, 3);
lean_inc(x_157);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 lean_ctor_release(x_121, 2);
 lean_ctor_release(x_121, 3);
 x_158 = x_121;
} else {
 lean_dec_ref(x_121);
 x_158 = lean_box(0);
}
lean_inc(x_47);
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 4, 1);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_34);
lean_ctor_set(x_159, 1, x_35);
lean_ctor_set(x_159, 2, x_36);
lean_ctor_set(x_159, 3, x_47);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_160 = x_47;
} else {
 lean_dec_ref(x_47);
 x_160 = lean_box(0);
}
lean_ctor_set_uint8(x_159, sizeof(void*)*4, x_95);
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 4, 1);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_154);
lean_ctor_set(x_161, 1, x_155);
lean_ctor_set(x_161, 2, x_156);
lean_ctor_set(x_161, 3, x_157);
lean_ctor_set_uint8(x_161, sizeof(void*)*4, x_95);
x_162 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_152);
lean_ctor_set(x_162, 2, x_153);
lean_ctor_set(x_162, 3, x_161);
lean_ctor_set_uint8(x_162, sizeof(void*)*4, x_130);
return x_162;
}
}
else
{
uint8_t x_163; 
x_163 = !lean_is_exclusive(x_46);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_164 = lean_ctor_get(x_46, 3);
lean_dec(x_164);
x_165 = lean_ctor_get(x_46, 0);
lean_dec(x_165);
x_166 = !lean_is_exclusive(x_47);
if (x_166 == 0)
{
uint8_t x_167; 
lean_ctor_set_uint8(x_47, sizeof(void*)*4, x_130);
x_167 = 0;
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_167);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_130);
return x_1;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_168 = lean_ctor_get(x_47, 0);
x_169 = lean_ctor_get(x_47, 1);
x_170 = lean_ctor_get(x_47, 2);
x_171 = lean_ctor_get(x_47, 3);
lean_inc(x_171);
lean_inc(x_170);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_47);
x_172 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_172, 0, x_168);
lean_ctor_set(x_172, 1, x_169);
lean_ctor_set(x_172, 2, x_170);
lean_ctor_set(x_172, 3, x_171);
lean_ctor_set_uint8(x_172, sizeof(void*)*4, x_130);
x_173 = 0;
lean_ctor_set(x_46, 0, x_172);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_173);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_130);
return x_1;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; lean_object* x_183; 
x_174 = lean_ctor_get(x_46, 1);
x_175 = lean_ctor_get(x_46, 2);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_46);
x_176 = lean_ctor_get(x_47, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_47, 1);
lean_inc(x_177);
x_178 = lean_ctor_get(x_47, 2);
lean_inc(x_178);
x_179 = lean_ctor_get(x_47, 3);
lean_inc(x_179);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_180 = x_47;
} else {
 lean_dec_ref(x_47);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(1, 4, 1);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_176);
lean_ctor_set(x_181, 1, x_177);
lean_ctor_set(x_181, 2, x_178);
lean_ctor_set(x_181, 3, x_179);
lean_ctor_set_uint8(x_181, sizeof(void*)*4, x_130);
x_182 = 0;
x_183 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_174);
lean_ctor_set(x_183, 2, x_175);
lean_ctor_set(x_183, 3, x_121);
lean_ctor_set_uint8(x_183, sizeof(void*)*4, x_182);
lean_ctor_set(x_1, 3, x_183);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_130);
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
uint8_t x_184; uint8_t x_185; 
x_184 = l_RBNode_isRed___rarg(x_34);
x_185 = l_Bool_DecidableEq(x_184, x_39);
if (x_185 == 0)
{
lean_object* x_186; 
x_186 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_34, x_2, x_3);
lean_ctor_set(x_1, 0, x_186);
return x_1;
}
else
{
lean_object* x_187; lean_object* x_188; 
x_187 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_34, x_2, x_3);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; 
x_189 = lean_ctor_get(x_187, 3);
lean_inc(x_189);
if (lean_obj_tag(x_189) == 0)
{
uint8_t x_190; 
x_190 = !lean_is_exclusive(x_187);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; uint8_t x_193; uint8_t x_194; 
x_191 = lean_ctor_get(x_187, 3);
lean_dec(x_191);
x_192 = lean_ctor_get(x_187, 0);
lean_dec(x_192);
x_193 = 0;
lean_ctor_set(x_187, 0, x_189);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_193);
x_194 = 1;
lean_ctor_set(x_1, 0, x_187);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_194);
return x_1;
}
else
{
lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; uint8_t x_199; 
x_195 = lean_ctor_get(x_187, 1);
x_196 = lean_ctor_get(x_187, 2);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_187);
x_197 = 0;
x_198 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_198, 0, x_189);
lean_ctor_set(x_198, 1, x_195);
lean_ctor_set(x_198, 2, x_196);
lean_ctor_set(x_198, 3, x_189);
lean_ctor_set_uint8(x_198, sizeof(void*)*4, x_197);
x_199 = 1;
lean_ctor_set(x_1, 0, x_198);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_199);
return x_1;
}
}
else
{
uint8_t x_200; 
x_200 = lean_ctor_get_uint8(x_189, sizeof(void*)*4);
if (x_200 == 0)
{
uint8_t x_201; 
x_201 = !lean_is_exclusive(x_187);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; 
x_202 = lean_ctor_get(x_187, 1);
x_203 = lean_ctor_get(x_187, 2);
x_204 = lean_ctor_get(x_187, 3);
lean_dec(x_204);
x_205 = lean_ctor_get(x_187, 0);
lean_dec(x_205);
x_206 = !lean_is_exclusive(x_189);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; 
x_207 = lean_ctor_get(x_189, 0);
x_208 = lean_ctor_get(x_189, 1);
x_209 = lean_ctor_get(x_189, 2);
x_210 = lean_ctor_get(x_189, 3);
x_211 = 1;
lean_ctor_set(x_189, 3, x_207);
lean_ctor_set(x_189, 2, x_203);
lean_ctor_set(x_189, 1, x_202);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set_uint8(x_189, sizeof(void*)*4, x_211);
lean_ctor_set(x_187, 3, x_37);
lean_ctor_set(x_187, 2, x_36);
lean_ctor_set(x_187, 1, x_35);
lean_ctor_set(x_187, 0, x_210);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_211);
lean_ctor_set(x_1, 3, x_187);
lean_ctor_set(x_1, 2, x_209);
lean_ctor_set(x_1, 1, x_208);
lean_ctor_set(x_1, 0, x_189);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_200);
return x_1;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; 
x_212 = lean_ctor_get(x_189, 0);
x_213 = lean_ctor_get(x_189, 1);
x_214 = lean_ctor_get(x_189, 2);
x_215 = lean_ctor_get(x_189, 3);
lean_inc(x_215);
lean_inc(x_214);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_189);
x_216 = 1;
x_217 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_217, 0, x_188);
lean_ctor_set(x_217, 1, x_202);
lean_ctor_set(x_217, 2, x_203);
lean_ctor_set(x_217, 3, x_212);
lean_ctor_set_uint8(x_217, sizeof(void*)*4, x_216);
lean_ctor_set(x_187, 3, x_37);
lean_ctor_set(x_187, 2, x_36);
lean_ctor_set(x_187, 1, x_35);
lean_ctor_set(x_187, 0, x_215);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_216);
lean_ctor_set(x_1, 3, x_187);
lean_ctor_set(x_1, 2, x_214);
lean_ctor_set(x_1, 1, x_213);
lean_ctor_set(x_1, 0, x_217);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_200);
return x_1;
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; lean_object* x_226; lean_object* x_227; 
x_218 = lean_ctor_get(x_187, 1);
x_219 = lean_ctor_get(x_187, 2);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_187);
x_220 = lean_ctor_get(x_189, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_189, 1);
lean_inc(x_221);
x_222 = lean_ctor_get(x_189, 2);
lean_inc(x_222);
x_223 = lean_ctor_get(x_189, 3);
lean_inc(x_223);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 lean_ctor_release(x_189, 2);
 lean_ctor_release(x_189, 3);
 x_224 = x_189;
} else {
 lean_dec_ref(x_189);
 x_224 = lean_box(0);
}
x_225 = 1;
if (lean_is_scalar(x_224)) {
 x_226 = lean_alloc_ctor(1, 4, 1);
} else {
 x_226 = x_224;
}
lean_ctor_set(x_226, 0, x_188);
lean_ctor_set(x_226, 1, x_218);
lean_ctor_set(x_226, 2, x_219);
lean_ctor_set(x_226, 3, x_220);
lean_ctor_set_uint8(x_226, sizeof(void*)*4, x_225);
x_227 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_227, 0, x_223);
lean_ctor_set(x_227, 1, x_35);
lean_ctor_set(x_227, 2, x_36);
lean_ctor_set(x_227, 3, x_37);
lean_ctor_set_uint8(x_227, sizeof(void*)*4, x_225);
lean_ctor_set(x_1, 3, x_227);
lean_ctor_set(x_1, 2, x_222);
lean_ctor_set(x_1, 1, x_221);
lean_ctor_set(x_1, 0, x_226);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_200);
return x_1;
}
}
else
{
uint8_t x_228; 
x_228 = !lean_is_exclusive(x_187);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; uint8_t x_231; 
x_229 = lean_ctor_get(x_187, 3);
lean_dec(x_229);
x_230 = lean_ctor_get(x_187, 0);
lean_dec(x_230);
x_231 = 0;
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_231);
lean_ctor_set(x_1, 0, x_187);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_200);
return x_1;
}
else
{
lean_object* x_232; lean_object* x_233; uint8_t x_234; lean_object* x_235; 
x_232 = lean_ctor_get(x_187, 1);
x_233 = lean_ctor_get(x_187, 2);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_187);
x_234 = 0;
x_235 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_235, 0, x_188);
lean_ctor_set(x_235, 1, x_232);
lean_ctor_set(x_235, 2, x_233);
lean_ctor_set(x_235, 3, x_189);
lean_ctor_set_uint8(x_235, sizeof(void*)*4, x_234);
lean_ctor_set(x_1, 0, x_235);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_200);
return x_1;
}
}
}
}
else
{
uint8_t x_236; 
x_236 = lean_ctor_get_uint8(x_188, sizeof(void*)*4);
if (x_236 == 0)
{
uint8_t x_237; 
x_237 = !lean_is_exclusive(x_187);
if (x_237 == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; 
x_238 = lean_ctor_get(x_187, 1);
x_239 = lean_ctor_get(x_187, 2);
x_240 = lean_ctor_get(x_187, 3);
x_241 = lean_ctor_get(x_187, 0);
lean_dec(x_241);
x_242 = !lean_is_exclusive(x_188);
if (x_242 == 0)
{
uint8_t x_243; 
x_243 = 1;
lean_ctor_set_uint8(x_188, sizeof(void*)*4, x_243);
lean_ctor_set(x_187, 3, x_37);
lean_ctor_set(x_187, 2, x_36);
lean_ctor_set(x_187, 1, x_35);
lean_ctor_set(x_187, 0, x_240);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_243);
lean_ctor_set(x_1, 3, x_187);
lean_ctor_set(x_1, 2, x_239);
lean_ctor_set(x_1, 1, x_238);
lean_ctor_set(x_1, 0, x_188);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_236);
return x_1;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; uint8_t x_248; lean_object* x_249; 
x_244 = lean_ctor_get(x_188, 0);
x_245 = lean_ctor_get(x_188, 1);
x_246 = lean_ctor_get(x_188, 2);
x_247 = lean_ctor_get(x_188, 3);
lean_inc(x_247);
lean_inc(x_246);
lean_inc(x_245);
lean_inc(x_244);
lean_dec(x_188);
x_248 = 1;
x_249 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_249, 0, x_244);
lean_ctor_set(x_249, 1, x_245);
lean_ctor_set(x_249, 2, x_246);
lean_ctor_set(x_249, 3, x_247);
lean_ctor_set_uint8(x_249, sizeof(void*)*4, x_248);
lean_ctor_set(x_187, 3, x_37);
lean_ctor_set(x_187, 2, x_36);
lean_ctor_set(x_187, 1, x_35);
lean_ctor_set(x_187, 0, x_240);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_248);
lean_ctor_set(x_1, 3, x_187);
lean_ctor_set(x_1, 2, x_239);
lean_ctor_set(x_1, 1, x_238);
lean_ctor_set(x_1, 0, x_249);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_236);
return x_1;
}
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; lean_object* x_259; lean_object* x_260; 
x_250 = lean_ctor_get(x_187, 1);
x_251 = lean_ctor_get(x_187, 2);
x_252 = lean_ctor_get(x_187, 3);
lean_inc(x_252);
lean_inc(x_251);
lean_inc(x_250);
lean_dec(x_187);
x_253 = lean_ctor_get(x_188, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_188, 1);
lean_inc(x_254);
x_255 = lean_ctor_get(x_188, 2);
lean_inc(x_255);
x_256 = lean_ctor_get(x_188, 3);
lean_inc(x_256);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 lean_ctor_release(x_188, 2);
 lean_ctor_release(x_188, 3);
 x_257 = x_188;
} else {
 lean_dec_ref(x_188);
 x_257 = lean_box(0);
}
x_258 = 1;
if (lean_is_scalar(x_257)) {
 x_259 = lean_alloc_ctor(1, 4, 1);
} else {
 x_259 = x_257;
}
lean_ctor_set(x_259, 0, x_253);
lean_ctor_set(x_259, 1, x_254);
lean_ctor_set(x_259, 2, x_255);
lean_ctor_set(x_259, 3, x_256);
lean_ctor_set_uint8(x_259, sizeof(void*)*4, x_258);
x_260 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_260, 0, x_252);
lean_ctor_set(x_260, 1, x_35);
lean_ctor_set(x_260, 2, x_36);
lean_ctor_set(x_260, 3, x_37);
lean_ctor_set_uint8(x_260, sizeof(void*)*4, x_258);
lean_ctor_set(x_1, 3, x_260);
lean_ctor_set(x_1, 2, x_251);
lean_ctor_set(x_1, 1, x_250);
lean_ctor_set(x_1, 0, x_259);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_236);
return x_1;
}
}
else
{
lean_object* x_261; 
x_261 = lean_ctor_get(x_187, 3);
lean_inc(x_261);
if (lean_obj_tag(x_261) == 0)
{
uint8_t x_262; 
x_262 = !lean_is_exclusive(x_187);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; uint8_t x_265; 
x_263 = lean_ctor_get(x_187, 3);
lean_dec(x_263);
x_264 = lean_ctor_get(x_187, 0);
lean_dec(x_264);
x_265 = 0;
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_265);
lean_ctor_set(x_1, 0, x_187);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_236);
return x_1;
}
else
{
lean_object* x_266; lean_object* x_267; uint8_t x_268; lean_object* x_269; 
x_266 = lean_ctor_get(x_187, 1);
x_267 = lean_ctor_get(x_187, 2);
lean_inc(x_267);
lean_inc(x_266);
lean_dec(x_187);
x_268 = 0;
x_269 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_269, 0, x_188);
lean_ctor_set(x_269, 1, x_266);
lean_ctor_set(x_269, 2, x_267);
lean_ctor_set(x_269, 3, x_261);
lean_ctor_set_uint8(x_269, sizeof(void*)*4, x_268);
lean_ctor_set(x_1, 0, x_269);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_236);
return x_1;
}
}
else
{
uint8_t x_270; 
x_270 = lean_ctor_get_uint8(x_261, sizeof(void*)*4);
if (x_270 == 0)
{
uint8_t x_271; 
lean_free_object(x_1);
x_271 = !lean_is_exclusive(x_187);
if (x_271 == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; uint8_t x_276; 
x_272 = lean_ctor_get(x_187, 1);
x_273 = lean_ctor_get(x_187, 2);
x_274 = lean_ctor_get(x_187, 3);
lean_dec(x_274);
x_275 = lean_ctor_get(x_187, 0);
lean_dec(x_275);
x_276 = !lean_is_exclusive(x_261);
if (x_276 == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; uint8_t x_281; 
x_277 = lean_ctor_get(x_261, 0);
x_278 = lean_ctor_get(x_261, 1);
x_279 = lean_ctor_get(x_261, 2);
x_280 = lean_ctor_get(x_261, 3);
lean_inc(x_188);
lean_ctor_set(x_261, 3, x_277);
lean_ctor_set(x_261, 2, x_273);
lean_ctor_set(x_261, 1, x_272);
lean_ctor_set(x_261, 0, x_188);
x_281 = !lean_is_exclusive(x_188);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_282 = lean_ctor_get(x_188, 3);
lean_dec(x_282);
x_283 = lean_ctor_get(x_188, 2);
lean_dec(x_283);
x_284 = lean_ctor_get(x_188, 1);
lean_dec(x_284);
x_285 = lean_ctor_get(x_188, 0);
lean_dec(x_285);
lean_ctor_set_uint8(x_261, sizeof(void*)*4, x_236);
lean_ctor_set(x_188, 3, x_37);
lean_ctor_set(x_188, 2, x_36);
lean_ctor_set(x_188, 1, x_35);
lean_ctor_set(x_188, 0, x_280);
lean_ctor_set(x_187, 3, x_188);
lean_ctor_set(x_187, 2, x_279);
lean_ctor_set(x_187, 1, x_278);
lean_ctor_set(x_187, 0, x_261);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_270);
return x_187;
}
else
{
lean_object* x_286; 
lean_dec(x_188);
lean_ctor_set_uint8(x_261, sizeof(void*)*4, x_236);
x_286 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_286, 0, x_280);
lean_ctor_set(x_286, 1, x_35);
lean_ctor_set(x_286, 2, x_36);
lean_ctor_set(x_286, 3, x_37);
lean_ctor_set_uint8(x_286, sizeof(void*)*4, x_236);
lean_ctor_set(x_187, 3, x_286);
lean_ctor_set(x_187, 2, x_279);
lean_ctor_set(x_187, 1, x_278);
lean_ctor_set(x_187, 0, x_261);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_270);
return x_187;
}
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_287 = lean_ctor_get(x_261, 0);
x_288 = lean_ctor_get(x_261, 1);
x_289 = lean_ctor_get(x_261, 2);
x_290 = lean_ctor_get(x_261, 3);
lean_inc(x_290);
lean_inc(x_289);
lean_inc(x_288);
lean_inc(x_287);
lean_dec(x_261);
lean_inc(x_188);
x_291 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_291, 0, x_188);
lean_ctor_set(x_291, 1, x_272);
lean_ctor_set(x_291, 2, x_273);
lean_ctor_set(x_291, 3, x_287);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 lean_ctor_release(x_188, 2);
 lean_ctor_release(x_188, 3);
 x_292 = x_188;
} else {
 lean_dec_ref(x_188);
 x_292 = lean_box(0);
}
lean_ctor_set_uint8(x_291, sizeof(void*)*4, x_236);
if (lean_is_scalar(x_292)) {
 x_293 = lean_alloc_ctor(1, 4, 1);
} else {
 x_293 = x_292;
}
lean_ctor_set(x_293, 0, x_290);
lean_ctor_set(x_293, 1, x_35);
lean_ctor_set(x_293, 2, x_36);
lean_ctor_set(x_293, 3, x_37);
lean_ctor_set_uint8(x_293, sizeof(void*)*4, x_236);
lean_ctor_set(x_187, 3, x_293);
lean_ctor_set(x_187, 2, x_289);
lean_ctor_set(x_187, 1, x_288);
lean_ctor_set(x_187, 0, x_291);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_270);
return x_187;
}
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_294 = lean_ctor_get(x_187, 1);
x_295 = lean_ctor_get(x_187, 2);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_187);
x_296 = lean_ctor_get(x_261, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_261, 1);
lean_inc(x_297);
x_298 = lean_ctor_get(x_261, 2);
lean_inc(x_298);
x_299 = lean_ctor_get(x_261, 3);
lean_inc(x_299);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 lean_ctor_release(x_261, 2);
 lean_ctor_release(x_261, 3);
 x_300 = x_261;
} else {
 lean_dec_ref(x_261);
 x_300 = lean_box(0);
}
lean_inc(x_188);
if (lean_is_scalar(x_300)) {
 x_301 = lean_alloc_ctor(1, 4, 1);
} else {
 x_301 = x_300;
}
lean_ctor_set(x_301, 0, x_188);
lean_ctor_set(x_301, 1, x_294);
lean_ctor_set(x_301, 2, x_295);
lean_ctor_set(x_301, 3, x_296);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 lean_ctor_release(x_188, 2);
 lean_ctor_release(x_188, 3);
 x_302 = x_188;
} else {
 lean_dec_ref(x_188);
 x_302 = lean_box(0);
}
lean_ctor_set_uint8(x_301, sizeof(void*)*4, x_236);
if (lean_is_scalar(x_302)) {
 x_303 = lean_alloc_ctor(1, 4, 1);
} else {
 x_303 = x_302;
}
lean_ctor_set(x_303, 0, x_299);
lean_ctor_set(x_303, 1, x_35);
lean_ctor_set(x_303, 2, x_36);
lean_ctor_set(x_303, 3, x_37);
lean_ctor_set_uint8(x_303, sizeof(void*)*4, x_236);
x_304 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_304, 0, x_301);
lean_ctor_set(x_304, 1, x_297);
lean_ctor_set(x_304, 2, x_298);
lean_ctor_set(x_304, 3, x_303);
lean_ctor_set_uint8(x_304, sizeof(void*)*4, x_270);
return x_304;
}
}
else
{
uint8_t x_305; 
x_305 = !lean_is_exclusive(x_187);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; uint8_t x_308; 
x_306 = lean_ctor_get(x_187, 3);
lean_dec(x_306);
x_307 = lean_ctor_get(x_187, 0);
lean_dec(x_307);
x_308 = !lean_is_exclusive(x_188);
if (x_308 == 0)
{
uint8_t x_309; 
lean_ctor_set_uint8(x_188, sizeof(void*)*4, x_270);
x_309 = 0;
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_309);
lean_ctor_set(x_1, 0, x_187);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_270);
return x_1;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; 
x_310 = lean_ctor_get(x_188, 0);
x_311 = lean_ctor_get(x_188, 1);
x_312 = lean_ctor_get(x_188, 2);
x_313 = lean_ctor_get(x_188, 3);
lean_inc(x_313);
lean_inc(x_312);
lean_inc(x_311);
lean_inc(x_310);
lean_dec(x_188);
x_314 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_314, 0, x_310);
lean_ctor_set(x_314, 1, x_311);
lean_ctor_set(x_314, 2, x_312);
lean_ctor_set(x_314, 3, x_313);
lean_ctor_set_uint8(x_314, sizeof(void*)*4, x_270);
x_315 = 0;
lean_ctor_set(x_187, 0, x_314);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_315);
lean_ctor_set(x_1, 0, x_187);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_270);
return x_1;
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; lean_object* x_325; 
x_316 = lean_ctor_get(x_187, 1);
x_317 = lean_ctor_get(x_187, 2);
lean_inc(x_317);
lean_inc(x_316);
lean_dec(x_187);
x_318 = lean_ctor_get(x_188, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_188, 1);
lean_inc(x_319);
x_320 = lean_ctor_get(x_188, 2);
lean_inc(x_320);
x_321 = lean_ctor_get(x_188, 3);
lean_inc(x_321);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 lean_ctor_release(x_188, 2);
 lean_ctor_release(x_188, 3);
 x_322 = x_188;
} else {
 lean_dec_ref(x_188);
 x_322 = lean_box(0);
}
if (lean_is_scalar(x_322)) {
 x_323 = lean_alloc_ctor(1, 4, 1);
} else {
 x_323 = x_322;
}
lean_ctor_set(x_323, 0, x_318);
lean_ctor_set(x_323, 1, x_319);
lean_ctor_set(x_323, 2, x_320);
lean_ctor_set(x_323, 3, x_321);
lean_ctor_set_uint8(x_323, sizeof(void*)*4, x_270);
x_324 = 0;
x_325 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_325, 0, x_323);
lean_ctor_set(x_325, 1, x_316);
lean_ctor_set(x_325, 2, x_317);
lean_ctor_set(x_325, 3, x_261);
lean_ctor_set_uint8(x_325, sizeof(void*)*4, x_324);
lean_ctor_set(x_1, 0, x_325);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_270);
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
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_330; uint8_t x_331; uint8_t x_332; 
x_326 = lean_ctor_get(x_1, 0);
x_327 = lean_ctor_get(x_1, 1);
x_328 = lean_ctor_get(x_1, 2);
x_329 = lean_ctor_get(x_1, 3);
lean_inc(x_329);
lean_inc(x_328);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_1);
x_330 = lean_nat_dec_lt(x_2, x_327);
x_331 = 1;
x_332 = l_Bool_DecidableEq(x_330, x_331);
if (x_332 == 0)
{
uint8_t x_333; uint8_t x_334; 
x_333 = lean_nat_dec_lt(x_327, x_2);
x_334 = l_Bool_DecidableEq(x_333, x_331);
if (x_334 == 0)
{
lean_object* x_335; 
lean_dec(x_328);
lean_dec(x_327);
x_335 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_335, 0, x_326);
lean_ctor_set(x_335, 1, x_2);
lean_ctor_set(x_335, 2, x_3);
lean_ctor_set(x_335, 3, x_329);
lean_ctor_set_uint8(x_335, sizeof(void*)*4, x_6);
return x_335;
}
else
{
uint8_t x_336; uint8_t x_337; 
x_336 = l_RBNode_isRed___rarg(x_329);
x_337 = l_Bool_DecidableEq(x_336, x_331);
if (x_337 == 0)
{
lean_object* x_338; lean_object* x_339; 
x_338 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_329, x_2, x_3);
x_339 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_339, 0, x_326);
lean_ctor_set(x_339, 1, x_327);
lean_ctor_set(x_339, 2, x_328);
lean_ctor_set(x_339, 3, x_338);
lean_ctor_set_uint8(x_339, sizeof(void*)*4, x_6);
return x_339;
}
else
{
lean_object* x_340; lean_object* x_341; 
x_340 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_329, x_2, x_3);
x_341 = lean_ctor_get(x_340, 0);
lean_inc(x_341);
if (lean_obj_tag(x_341) == 0)
{
lean_object* x_342; 
x_342 = lean_ctor_get(x_340, 3);
lean_inc(x_342);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; uint8_t x_346; lean_object* x_347; uint8_t x_348; lean_object* x_349; 
x_343 = lean_ctor_get(x_340, 1);
lean_inc(x_343);
x_344 = lean_ctor_get(x_340, 2);
lean_inc(x_344);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 lean_ctor_release(x_340, 2);
 lean_ctor_release(x_340, 3);
 x_345 = x_340;
} else {
 lean_dec_ref(x_340);
 x_345 = lean_box(0);
}
x_346 = 0;
if (lean_is_scalar(x_345)) {
 x_347 = lean_alloc_ctor(1, 4, 1);
} else {
 x_347 = x_345;
}
lean_ctor_set(x_347, 0, x_342);
lean_ctor_set(x_347, 1, x_343);
lean_ctor_set(x_347, 2, x_344);
lean_ctor_set(x_347, 3, x_342);
lean_ctor_set_uint8(x_347, sizeof(void*)*4, x_346);
x_348 = 1;
x_349 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_349, 0, x_326);
lean_ctor_set(x_349, 1, x_327);
lean_ctor_set(x_349, 2, x_328);
lean_ctor_set(x_349, 3, x_347);
lean_ctor_set_uint8(x_349, sizeof(void*)*4, x_348);
return x_349;
}
else
{
uint8_t x_350; 
x_350 = lean_ctor_get_uint8(x_342, sizeof(void*)*4);
if (x_350 == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_351 = lean_ctor_get(x_340, 1);
lean_inc(x_351);
x_352 = lean_ctor_get(x_340, 2);
lean_inc(x_352);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 lean_ctor_release(x_340, 2);
 lean_ctor_release(x_340, 3);
 x_353 = x_340;
} else {
 lean_dec_ref(x_340);
 x_353 = lean_box(0);
}
x_354 = lean_ctor_get(x_342, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_342, 1);
lean_inc(x_355);
x_356 = lean_ctor_get(x_342, 2);
lean_inc(x_356);
x_357 = lean_ctor_get(x_342, 3);
lean_inc(x_357);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 lean_ctor_release(x_342, 2);
 lean_ctor_release(x_342, 3);
 x_358 = x_342;
} else {
 lean_dec_ref(x_342);
 x_358 = lean_box(0);
}
x_359 = 1;
if (lean_is_scalar(x_358)) {
 x_360 = lean_alloc_ctor(1, 4, 1);
} else {
 x_360 = x_358;
}
lean_ctor_set(x_360, 0, x_326);
lean_ctor_set(x_360, 1, x_327);
lean_ctor_set(x_360, 2, x_328);
lean_ctor_set(x_360, 3, x_341);
lean_ctor_set_uint8(x_360, sizeof(void*)*4, x_359);
if (lean_is_scalar(x_353)) {
 x_361 = lean_alloc_ctor(1, 4, 1);
} else {
 x_361 = x_353;
}
lean_ctor_set(x_361, 0, x_354);
lean_ctor_set(x_361, 1, x_355);
lean_ctor_set(x_361, 2, x_356);
lean_ctor_set(x_361, 3, x_357);
lean_ctor_set_uint8(x_361, sizeof(void*)*4, x_359);
x_362 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_362, 0, x_360);
lean_ctor_set(x_362, 1, x_351);
lean_ctor_set(x_362, 2, x_352);
lean_ctor_set(x_362, 3, x_361);
lean_ctor_set_uint8(x_362, sizeof(void*)*4, x_350);
return x_362;
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; uint8_t x_366; lean_object* x_367; lean_object* x_368; 
x_363 = lean_ctor_get(x_340, 1);
lean_inc(x_363);
x_364 = lean_ctor_get(x_340, 2);
lean_inc(x_364);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 lean_ctor_release(x_340, 2);
 lean_ctor_release(x_340, 3);
 x_365 = x_340;
} else {
 lean_dec_ref(x_340);
 x_365 = lean_box(0);
}
x_366 = 0;
if (lean_is_scalar(x_365)) {
 x_367 = lean_alloc_ctor(1, 4, 1);
} else {
 x_367 = x_365;
}
lean_ctor_set(x_367, 0, x_341);
lean_ctor_set(x_367, 1, x_363);
lean_ctor_set(x_367, 2, x_364);
lean_ctor_set(x_367, 3, x_342);
lean_ctor_set_uint8(x_367, sizeof(void*)*4, x_366);
x_368 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_368, 0, x_326);
lean_ctor_set(x_368, 1, x_327);
lean_ctor_set(x_368, 2, x_328);
lean_ctor_set(x_368, 3, x_367);
lean_ctor_set_uint8(x_368, sizeof(void*)*4, x_350);
return x_368;
}
}
}
else
{
uint8_t x_369; 
x_369 = lean_ctor_get_uint8(x_341, sizeof(void*)*4);
if (x_369 == 0)
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; uint8_t x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_370 = lean_ctor_get(x_340, 1);
lean_inc(x_370);
x_371 = lean_ctor_get(x_340, 2);
lean_inc(x_371);
x_372 = lean_ctor_get(x_340, 3);
lean_inc(x_372);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 lean_ctor_release(x_340, 2);
 lean_ctor_release(x_340, 3);
 x_373 = x_340;
} else {
 lean_dec_ref(x_340);
 x_373 = lean_box(0);
}
x_374 = lean_ctor_get(x_341, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_341, 1);
lean_inc(x_375);
x_376 = lean_ctor_get(x_341, 2);
lean_inc(x_376);
x_377 = lean_ctor_get(x_341, 3);
lean_inc(x_377);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 lean_ctor_release(x_341, 2);
 lean_ctor_release(x_341, 3);
 x_378 = x_341;
} else {
 lean_dec_ref(x_341);
 x_378 = lean_box(0);
}
x_379 = 1;
if (lean_is_scalar(x_378)) {
 x_380 = lean_alloc_ctor(1, 4, 1);
} else {
 x_380 = x_378;
}
lean_ctor_set(x_380, 0, x_326);
lean_ctor_set(x_380, 1, x_327);
lean_ctor_set(x_380, 2, x_328);
lean_ctor_set(x_380, 3, x_374);
lean_ctor_set_uint8(x_380, sizeof(void*)*4, x_379);
if (lean_is_scalar(x_373)) {
 x_381 = lean_alloc_ctor(1, 4, 1);
} else {
 x_381 = x_373;
}
lean_ctor_set(x_381, 0, x_377);
lean_ctor_set(x_381, 1, x_370);
lean_ctor_set(x_381, 2, x_371);
lean_ctor_set(x_381, 3, x_372);
lean_ctor_set_uint8(x_381, sizeof(void*)*4, x_379);
x_382 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_382, 0, x_380);
lean_ctor_set(x_382, 1, x_375);
lean_ctor_set(x_382, 2, x_376);
lean_ctor_set(x_382, 3, x_381);
lean_ctor_set_uint8(x_382, sizeof(void*)*4, x_369);
return x_382;
}
else
{
lean_object* x_383; 
x_383 = lean_ctor_get(x_340, 3);
lean_inc(x_383);
if (lean_obj_tag(x_383) == 0)
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; uint8_t x_387; lean_object* x_388; lean_object* x_389; 
x_384 = lean_ctor_get(x_340, 1);
lean_inc(x_384);
x_385 = lean_ctor_get(x_340, 2);
lean_inc(x_385);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 lean_ctor_release(x_340, 2);
 lean_ctor_release(x_340, 3);
 x_386 = x_340;
} else {
 lean_dec_ref(x_340);
 x_386 = lean_box(0);
}
x_387 = 0;
if (lean_is_scalar(x_386)) {
 x_388 = lean_alloc_ctor(1, 4, 1);
} else {
 x_388 = x_386;
}
lean_ctor_set(x_388, 0, x_341);
lean_ctor_set(x_388, 1, x_384);
lean_ctor_set(x_388, 2, x_385);
lean_ctor_set(x_388, 3, x_383);
lean_ctor_set_uint8(x_388, sizeof(void*)*4, x_387);
x_389 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_389, 0, x_326);
lean_ctor_set(x_389, 1, x_327);
lean_ctor_set(x_389, 2, x_328);
lean_ctor_set(x_389, 3, x_388);
lean_ctor_set_uint8(x_389, sizeof(void*)*4, x_369);
return x_389;
}
else
{
uint8_t x_390; 
x_390 = lean_ctor_get_uint8(x_383, sizeof(void*)*4);
if (x_390 == 0)
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_391 = lean_ctor_get(x_340, 1);
lean_inc(x_391);
x_392 = lean_ctor_get(x_340, 2);
lean_inc(x_392);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 lean_ctor_release(x_340, 2);
 lean_ctor_release(x_340, 3);
 x_393 = x_340;
} else {
 lean_dec_ref(x_340);
 x_393 = lean_box(0);
}
x_394 = lean_ctor_get(x_383, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_383, 1);
lean_inc(x_395);
x_396 = lean_ctor_get(x_383, 2);
lean_inc(x_396);
x_397 = lean_ctor_get(x_383, 3);
lean_inc(x_397);
if (lean_is_exclusive(x_383)) {
 lean_ctor_release(x_383, 0);
 lean_ctor_release(x_383, 1);
 lean_ctor_release(x_383, 2);
 lean_ctor_release(x_383, 3);
 x_398 = x_383;
} else {
 lean_dec_ref(x_383);
 x_398 = lean_box(0);
}
lean_inc(x_341);
if (lean_is_scalar(x_398)) {
 x_399 = lean_alloc_ctor(1, 4, 1);
} else {
 x_399 = x_398;
}
lean_ctor_set(x_399, 0, x_326);
lean_ctor_set(x_399, 1, x_327);
lean_ctor_set(x_399, 2, x_328);
lean_ctor_set(x_399, 3, x_341);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 lean_ctor_release(x_341, 2);
 lean_ctor_release(x_341, 3);
 x_400 = x_341;
} else {
 lean_dec_ref(x_341);
 x_400 = lean_box(0);
}
lean_ctor_set_uint8(x_399, sizeof(void*)*4, x_369);
if (lean_is_scalar(x_400)) {
 x_401 = lean_alloc_ctor(1, 4, 1);
} else {
 x_401 = x_400;
}
lean_ctor_set(x_401, 0, x_394);
lean_ctor_set(x_401, 1, x_395);
lean_ctor_set(x_401, 2, x_396);
lean_ctor_set(x_401, 3, x_397);
lean_ctor_set_uint8(x_401, sizeof(void*)*4, x_369);
if (lean_is_scalar(x_393)) {
 x_402 = lean_alloc_ctor(1, 4, 1);
} else {
 x_402 = x_393;
}
lean_ctor_set(x_402, 0, x_399);
lean_ctor_set(x_402, 1, x_391);
lean_ctor_set(x_402, 2, x_392);
lean_ctor_set(x_402, 3, x_401);
lean_ctor_set_uint8(x_402, sizeof(void*)*4, x_390);
return x_402;
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; uint8_t x_412; lean_object* x_413; lean_object* x_414; 
x_403 = lean_ctor_get(x_340, 1);
lean_inc(x_403);
x_404 = lean_ctor_get(x_340, 2);
lean_inc(x_404);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 lean_ctor_release(x_340, 2);
 lean_ctor_release(x_340, 3);
 x_405 = x_340;
} else {
 lean_dec_ref(x_340);
 x_405 = lean_box(0);
}
x_406 = lean_ctor_get(x_341, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_341, 1);
lean_inc(x_407);
x_408 = lean_ctor_get(x_341, 2);
lean_inc(x_408);
x_409 = lean_ctor_get(x_341, 3);
lean_inc(x_409);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 lean_ctor_release(x_341, 2);
 lean_ctor_release(x_341, 3);
 x_410 = x_341;
} else {
 lean_dec_ref(x_341);
 x_410 = lean_box(0);
}
if (lean_is_scalar(x_410)) {
 x_411 = lean_alloc_ctor(1, 4, 1);
} else {
 x_411 = x_410;
}
lean_ctor_set(x_411, 0, x_406);
lean_ctor_set(x_411, 1, x_407);
lean_ctor_set(x_411, 2, x_408);
lean_ctor_set(x_411, 3, x_409);
lean_ctor_set_uint8(x_411, sizeof(void*)*4, x_390);
x_412 = 0;
if (lean_is_scalar(x_405)) {
 x_413 = lean_alloc_ctor(1, 4, 1);
} else {
 x_413 = x_405;
}
lean_ctor_set(x_413, 0, x_411);
lean_ctor_set(x_413, 1, x_403);
lean_ctor_set(x_413, 2, x_404);
lean_ctor_set(x_413, 3, x_383);
lean_ctor_set_uint8(x_413, sizeof(void*)*4, x_412);
x_414 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_414, 0, x_326);
lean_ctor_set(x_414, 1, x_327);
lean_ctor_set(x_414, 2, x_328);
lean_ctor_set(x_414, 3, x_413);
lean_ctor_set_uint8(x_414, sizeof(void*)*4, x_390);
return x_414;
}
}
}
}
}
}
}
else
{
uint8_t x_415; uint8_t x_416; 
x_415 = l_RBNode_isRed___rarg(x_326);
x_416 = l_Bool_DecidableEq(x_415, x_331);
if (x_416 == 0)
{
lean_object* x_417; lean_object* x_418; 
x_417 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_326, x_2, x_3);
x_418 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_418, 0, x_417);
lean_ctor_set(x_418, 1, x_327);
lean_ctor_set(x_418, 2, x_328);
lean_ctor_set(x_418, 3, x_329);
lean_ctor_set_uint8(x_418, sizeof(void*)*4, x_6);
return x_418;
}
else
{
lean_object* x_419; lean_object* x_420; 
x_419 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_326, x_2, x_3);
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_421; 
x_421 = lean_ctor_get(x_419, 3);
lean_inc(x_421);
if (lean_obj_tag(x_421) == 0)
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; uint8_t x_425; lean_object* x_426; uint8_t x_427; lean_object* x_428; 
x_422 = lean_ctor_get(x_419, 1);
lean_inc(x_422);
x_423 = lean_ctor_get(x_419, 2);
lean_inc(x_423);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 lean_ctor_release(x_419, 2);
 lean_ctor_release(x_419, 3);
 x_424 = x_419;
} else {
 lean_dec_ref(x_419);
 x_424 = lean_box(0);
}
x_425 = 0;
if (lean_is_scalar(x_424)) {
 x_426 = lean_alloc_ctor(1, 4, 1);
} else {
 x_426 = x_424;
}
lean_ctor_set(x_426, 0, x_421);
lean_ctor_set(x_426, 1, x_422);
lean_ctor_set(x_426, 2, x_423);
lean_ctor_set(x_426, 3, x_421);
lean_ctor_set_uint8(x_426, sizeof(void*)*4, x_425);
x_427 = 1;
x_428 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_428, 0, x_426);
lean_ctor_set(x_428, 1, x_327);
lean_ctor_set(x_428, 2, x_328);
lean_ctor_set(x_428, 3, x_329);
lean_ctor_set_uint8(x_428, sizeof(void*)*4, x_427);
return x_428;
}
else
{
uint8_t x_429; 
x_429 = lean_ctor_get_uint8(x_421, sizeof(void*)*4);
if (x_429 == 0)
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; uint8_t x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_430 = lean_ctor_get(x_419, 1);
lean_inc(x_430);
x_431 = lean_ctor_get(x_419, 2);
lean_inc(x_431);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 lean_ctor_release(x_419, 2);
 lean_ctor_release(x_419, 3);
 x_432 = x_419;
} else {
 lean_dec_ref(x_419);
 x_432 = lean_box(0);
}
x_433 = lean_ctor_get(x_421, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_421, 1);
lean_inc(x_434);
x_435 = lean_ctor_get(x_421, 2);
lean_inc(x_435);
x_436 = lean_ctor_get(x_421, 3);
lean_inc(x_436);
if (lean_is_exclusive(x_421)) {
 lean_ctor_release(x_421, 0);
 lean_ctor_release(x_421, 1);
 lean_ctor_release(x_421, 2);
 lean_ctor_release(x_421, 3);
 x_437 = x_421;
} else {
 lean_dec_ref(x_421);
 x_437 = lean_box(0);
}
x_438 = 1;
if (lean_is_scalar(x_437)) {
 x_439 = lean_alloc_ctor(1, 4, 1);
} else {
 x_439 = x_437;
}
lean_ctor_set(x_439, 0, x_420);
lean_ctor_set(x_439, 1, x_430);
lean_ctor_set(x_439, 2, x_431);
lean_ctor_set(x_439, 3, x_433);
lean_ctor_set_uint8(x_439, sizeof(void*)*4, x_438);
if (lean_is_scalar(x_432)) {
 x_440 = lean_alloc_ctor(1, 4, 1);
} else {
 x_440 = x_432;
}
lean_ctor_set(x_440, 0, x_436);
lean_ctor_set(x_440, 1, x_327);
lean_ctor_set(x_440, 2, x_328);
lean_ctor_set(x_440, 3, x_329);
lean_ctor_set_uint8(x_440, sizeof(void*)*4, x_438);
x_441 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_441, 0, x_439);
lean_ctor_set(x_441, 1, x_434);
lean_ctor_set(x_441, 2, x_435);
lean_ctor_set(x_441, 3, x_440);
lean_ctor_set_uint8(x_441, sizeof(void*)*4, x_429);
return x_441;
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; uint8_t x_445; lean_object* x_446; lean_object* x_447; 
x_442 = lean_ctor_get(x_419, 1);
lean_inc(x_442);
x_443 = lean_ctor_get(x_419, 2);
lean_inc(x_443);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 lean_ctor_release(x_419, 2);
 lean_ctor_release(x_419, 3);
 x_444 = x_419;
} else {
 lean_dec_ref(x_419);
 x_444 = lean_box(0);
}
x_445 = 0;
if (lean_is_scalar(x_444)) {
 x_446 = lean_alloc_ctor(1, 4, 1);
} else {
 x_446 = x_444;
}
lean_ctor_set(x_446, 0, x_420);
lean_ctor_set(x_446, 1, x_442);
lean_ctor_set(x_446, 2, x_443);
lean_ctor_set(x_446, 3, x_421);
lean_ctor_set_uint8(x_446, sizeof(void*)*4, x_445);
x_447 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_447, 0, x_446);
lean_ctor_set(x_447, 1, x_327);
lean_ctor_set(x_447, 2, x_328);
lean_ctor_set(x_447, 3, x_329);
lean_ctor_set_uint8(x_447, sizeof(void*)*4, x_429);
return x_447;
}
}
}
else
{
uint8_t x_448; 
x_448 = lean_ctor_get_uint8(x_420, sizeof(void*)*4);
if (x_448 == 0)
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; uint8_t x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; 
x_449 = lean_ctor_get(x_419, 1);
lean_inc(x_449);
x_450 = lean_ctor_get(x_419, 2);
lean_inc(x_450);
x_451 = lean_ctor_get(x_419, 3);
lean_inc(x_451);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 lean_ctor_release(x_419, 2);
 lean_ctor_release(x_419, 3);
 x_452 = x_419;
} else {
 lean_dec_ref(x_419);
 x_452 = lean_box(0);
}
x_453 = lean_ctor_get(x_420, 0);
lean_inc(x_453);
x_454 = lean_ctor_get(x_420, 1);
lean_inc(x_454);
x_455 = lean_ctor_get(x_420, 2);
lean_inc(x_455);
x_456 = lean_ctor_get(x_420, 3);
lean_inc(x_456);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 lean_ctor_release(x_420, 2);
 lean_ctor_release(x_420, 3);
 x_457 = x_420;
} else {
 lean_dec_ref(x_420);
 x_457 = lean_box(0);
}
x_458 = 1;
if (lean_is_scalar(x_457)) {
 x_459 = lean_alloc_ctor(1, 4, 1);
} else {
 x_459 = x_457;
}
lean_ctor_set(x_459, 0, x_453);
lean_ctor_set(x_459, 1, x_454);
lean_ctor_set(x_459, 2, x_455);
lean_ctor_set(x_459, 3, x_456);
lean_ctor_set_uint8(x_459, sizeof(void*)*4, x_458);
if (lean_is_scalar(x_452)) {
 x_460 = lean_alloc_ctor(1, 4, 1);
} else {
 x_460 = x_452;
}
lean_ctor_set(x_460, 0, x_451);
lean_ctor_set(x_460, 1, x_327);
lean_ctor_set(x_460, 2, x_328);
lean_ctor_set(x_460, 3, x_329);
lean_ctor_set_uint8(x_460, sizeof(void*)*4, x_458);
x_461 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_461, 0, x_459);
lean_ctor_set(x_461, 1, x_449);
lean_ctor_set(x_461, 2, x_450);
lean_ctor_set(x_461, 3, x_460);
lean_ctor_set_uint8(x_461, sizeof(void*)*4, x_448);
return x_461;
}
else
{
lean_object* x_462; 
x_462 = lean_ctor_get(x_419, 3);
lean_inc(x_462);
if (lean_obj_tag(x_462) == 0)
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; uint8_t x_466; lean_object* x_467; lean_object* x_468; 
x_463 = lean_ctor_get(x_419, 1);
lean_inc(x_463);
x_464 = lean_ctor_get(x_419, 2);
lean_inc(x_464);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 lean_ctor_release(x_419, 2);
 lean_ctor_release(x_419, 3);
 x_465 = x_419;
} else {
 lean_dec_ref(x_419);
 x_465 = lean_box(0);
}
x_466 = 0;
if (lean_is_scalar(x_465)) {
 x_467 = lean_alloc_ctor(1, 4, 1);
} else {
 x_467 = x_465;
}
lean_ctor_set(x_467, 0, x_420);
lean_ctor_set(x_467, 1, x_463);
lean_ctor_set(x_467, 2, x_464);
lean_ctor_set(x_467, 3, x_462);
lean_ctor_set_uint8(x_467, sizeof(void*)*4, x_466);
x_468 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_468, 0, x_467);
lean_ctor_set(x_468, 1, x_327);
lean_ctor_set(x_468, 2, x_328);
lean_ctor_set(x_468, 3, x_329);
lean_ctor_set_uint8(x_468, sizeof(void*)*4, x_448);
return x_468;
}
else
{
uint8_t x_469; 
x_469 = lean_ctor_get_uint8(x_462, sizeof(void*)*4);
if (x_469 == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_470 = lean_ctor_get(x_419, 1);
lean_inc(x_470);
x_471 = lean_ctor_get(x_419, 2);
lean_inc(x_471);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 lean_ctor_release(x_419, 2);
 lean_ctor_release(x_419, 3);
 x_472 = x_419;
} else {
 lean_dec_ref(x_419);
 x_472 = lean_box(0);
}
x_473 = lean_ctor_get(x_462, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_462, 1);
lean_inc(x_474);
x_475 = lean_ctor_get(x_462, 2);
lean_inc(x_475);
x_476 = lean_ctor_get(x_462, 3);
lean_inc(x_476);
if (lean_is_exclusive(x_462)) {
 lean_ctor_release(x_462, 0);
 lean_ctor_release(x_462, 1);
 lean_ctor_release(x_462, 2);
 lean_ctor_release(x_462, 3);
 x_477 = x_462;
} else {
 lean_dec_ref(x_462);
 x_477 = lean_box(0);
}
lean_inc(x_420);
if (lean_is_scalar(x_477)) {
 x_478 = lean_alloc_ctor(1, 4, 1);
} else {
 x_478 = x_477;
}
lean_ctor_set(x_478, 0, x_420);
lean_ctor_set(x_478, 1, x_470);
lean_ctor_set(x_478, 2, x_471);
lean_ctor_set(x_478, 3, x_473);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 lean_ctor_release(x_420, 2);
 lean_ctor_release(x_420, 3);
 x_479 = x_420;
} else {
 lean_dec_ref(x_420);
 x_479 = lean_box(0);
}
lean_ctor_set_uint8(x_478, sizeof(void*)*4, x_448);
if (lean_is_scalar(x_479)) {
 x_480 = lean_alloc_ctor(1, 4, 1);
} else {
 x_480 = x_479;
}
lean_ctor_set(x_480, 0, x_476);
lean_ctor_set(x_480, 1, x_327);
lean_ctor_set(x_480, 2, x_328);
lean_ctor_set(x_480, 3, x_329);
lean_ctor_set_uint8(x_480, sizeof(void*)*4, x_448);
if (lean_is_scalar(x_472)) {
 x_481 = lean_alloc_ctor(1, 4, 1);
} else {
 x_481 = x_472;
}
lean_ctor_set(x_481, 0, x_478);
lean_ctor_set(x_481, 1, x_474);
lean_ctor_set(x_481, 2, x_475);
lean_ctor_set(x_481, 3, x_480);
lean_ctor_set_uint8(x_481, sizeof(void*)*4, x_469);
return x_481;
}
else
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; uint8_t x_491; lean_object* x_492; lean_object* x_493; 
x_482 = lean_ctor_get(x_419, 1);
lean_inc(x_482);
x_483 = lean_ctor_get(x_419, 2);
lean_inc(x_483);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 lean_ctor_release(x_419, 2);
 lean_ctor_release(x_419, 3);
 x_484 = x_419;
} else {
 lean_dec_ref(x_419);
 x_484 = lean_box(0);
}
x_485 = lean_ctor_get(x_420, 0);
lean_inc(x_485);
x_486 = lean_ctor_get(x_420, 1);
lean_inc(x_486);
x_487 = lean_ctor_get(x_420, 2);
lean_inc(x_487);
x_488 = lean_ctor_get(x_420, 3);
lean_inc(x_488);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 lean_ctor_release(x_420, 2);
 lean_ctor_release(x_420, 3);
 x_489 = x_420;
} else {
 lean_dec_ref(x_420);
 x_489 = lean_box(0);
}
if (lean_is_scalar(x_489)) {
 x_490 = lean_alloc_ctor(1, 4, 1);
} else {
 x_490 = x_489;
}
lean_ctor_set(x_490, 0, x_485);
lean_ctor_set(x_490, 1, x_486);
lean_ctor_set(x_490, 2, x_487);
lean_ctor_set(x_490, 3, x_488);
lean_ctor_set_uint8(x_490, sizeof(void*)*4, x_469);
x_491 = 0;
if (lean_is_scalar(x_484)) {
 x_492 = lean_alloc_ctor(1, 4, 1);
} else {
 x_492 = x_484;
}
lean_ctor_set(x_492, 0, x_490);
lean_ctor_set(x_492, 1, x_482);
lean_ctor_set(x_492, 2, x_483);
lean_ctor_set(x_492, 3, x_462);
lean_ctor_set_uint8(x_492, sizeof(void*)*4, x_491);
x_493 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_493, 0, x_492);
lean_ctor_set(x_493, 1, x_327);
lean_ctor_set(x_493, 2, x_328);
lean_ctor_set(x_493, 3, x_329);
lean_ctor_set_uint8(x_493, sizeof(void*)*4, x_469);
return x_493;
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
uint8_t x_4; uint8_t x_5; uint8_t x_6; 
x_4 = l_RBNode_isRed___rarg(x_1);
x_5 = 1;
x_6 = l_Bool_DecidableEq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_1, x_2, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_1, x_2, x_3);
x_9 = l_RBNode_setBlack___rarg(x_8);
return x_9;
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_nat_dec_lt(x_2, x_5);
x_9 = 1;
x_10 = l_Bool_DecidableEq(x_8, x_9);
if (x_10 == 0)
{
uint8_t x_11; uint8_t x_12; 
x_11 = lean_nat_dec_lt(x_5, x_2);
x_12 = l_Bool_DecidableEq(x_11, x_9);
if (x_12 == 0)
{
lean_object* x_13; 
lean_inc(x_6);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_6);
return x_13;
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get(x_2, 3);
x_8 = lean_nat_dec_lt(x_1, x_5);
x_9 = 1;
x_10 = l_Bool_DecidableEq(x_8, x_9);
if (x_10 == 0)
{
uint8_t x_11; uint8_t x_12; 
x_11 = lean_nat_dec_lt(x_5, x_1);
x_12 = l_Bool_DecidableEq(x_11, x_9);
if (x_12 == 0)
{
lean_object* x_13; 
lean_free_object(x_2);
lean_dec(x_6);
lean_dec(x_5);
x_13 = l_RBNode_appendTrees___main___rarg(x_4, x_7);
return x_13;
}
else
{
uint8_t x_14; uint8_t x_15; 
x_14 = l_RBNode_isBlack___rarg(x_7);
x_15 = l_Bool_DecidableEq(x_14, x_9);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_RBNode_del___main___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(x_1, x_7);
x_17 = 0;
lean_ctor_set(x_2, 3, x_16);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_17);
return x_2;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_free_object(x_2);
x_18 = l_RBNode_del___main___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(x_1, x_7);
x_19 = l_RBNode_balRight___rarg(x_4, x_5, x_6, x_18);
return x_19;
}
}
}
else
{
uint8_t x_20; uint8_t x_21; 
x_20 = l_RBNode_isBlack___rarg(x_4);
x_21 = l_Bool_DecidableEq(x_20, x_9);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = l_RBNode_del___main___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(x_1, x_4);
x_23 = 0;
lean_ctor_set(x_2, 0, x_22);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_23);
return x_2;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_free_object(x_2);
x_24 = l_RBNode_del___main___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(x_1, x_4);
x_25 = l_RBNode_balLeft___rarg(x_24, x_5, x_6, x_7);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_ctor_get(x_2, 1);
x_28 = lean_ctor_get(x_2, 2);
x_29 = lean_ctor_get(x_2, 3);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_2);
x_30 = lean_nat_dec_lt(x_1, x_27);
x_31 = 1;
x_32 = l_Bool_DecidableEq(x_30, x_31);
if (x_32 == 0)
{
uint8_t x_33; uint8_t x_34; 
x_33 = lean_nat_dec_lt(x_27, x_1);
x_34 = l_Bool_DecidableEq(x_33, x_31);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_28);
lean_dec(x_27);
x_35 = l_RBNode_appendTrees___main___rarg(x_26, x_29);
return x_35;
}
else
{
uint8_t x_36; uint8_t x_37; 
x_36 = l_RBNode_isBlack___rarg(x_29);
x_37 = l_Bool_DecidableEq(x_36, x_31);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_38 = l_RBNode_del___main___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(x_1, x_29);
x_39 = 0;
x_40 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_40, 0, x_26);
lean_ctor_set(x_40, 1, x_27);
lean_ctor_set(x_40, 2, x_28);
lean_ctor_set(x_40, 3, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*4, x_39);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = l_RBNode_del___main___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(x_1, x_29);
x_42 = l_RBNode_balRight___rarg(x_26, x_27, x_28, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; uint8_t x_44; 
x_43 = l_RBNode_isBlack___rarg(x_26);
x_44 = l_Bool_DecidableEq(x_43, x_31);
if (x_44 == 0)
{
lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_45 = l_RBNode_del___main___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(x_1, x_26);
x_46 = 0;
x_47 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_27);
lean_ctor_set(x_47, 2, x_28);
lean_ctor_set(x_47, 3, x_29);
lean_ctor_set_uint8(x_47, sizeof(void*)*4, x_46);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = l_RBNode_del___main___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(x_1, x_26);
x_49 = l_RBNode_balLeft___rarg(x_48, x_27, x_28, x_29);
return x_49;
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_nat_dec_lt(x_2, x_5);
x_9 = 1;
x_10 = l_Bool_DecidableEq(x_8, x_9);
if (x_10 == 0)
{
uint8_t x_11; uint8_t x_12; 
x_11 = lean_nat_dec_lt(x_5, x_2);
x_12 = l_Bool_DecidableEq(x_11, x_9);
if (x_12 == 0)
{
lean_object* x_13; 
lean_inc(x_6);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_6);
return x_13;
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
uint8_t l_Array_isEqv___at_Lean_IR_args_alphaEqv___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_alloc_closure((void*)(l_Lean_IR_Arg_alphaEqv___boxed), 3, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_array_get_size(x_2);
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_eq(x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_isEqvAux___main___rarg(x_2, x_3, lean_box(0), x_4, x_9);
return x_10;
}
}
}
uint8_t l_Lean_IR_args_alphaEqv(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Array_isEqv___at_Lean_IR_args_alphaEqv___spec__1(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Array_isEqv___at_Lean_IR_args_alphaEqv___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_isEqv___at_Lean_IR_args_alphaEqv___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_Lean_IR_args_alphaEqv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_IR_args_alphaEqv(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_1);
x_9 = 0;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = l_Array_isEqv___at_Lean_IR_args_alphaEqv___spec__1(x_1, x_5, x_7);
return x_10;
}
}
else
{
uint8_t x_11; 
lean_dec(x_1);
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
lean_dec(x_1);
x_17 = 0;
return x_17;
}
else
{
uint8_t x_18; 
x_18 = l_Lean_IR_VarId_alphaEqv(x_1, x_13, x_15);
lean_dec(x_1);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_1);
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
x_22 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_23 = lean_ctor_get(x_2, 2);
x_24 = lean_ctor_get(x_3, 0);
x_25 = lean_ctor_get(x_3, 1);
x_26 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_27 = lean_ctor_get(x_3, 2);
x_28 = l_Lean_IR_VarId_alphaEqv(x_1, x_20, x_24);
if (x_28 == 0)
{
uint8_t x_29; 
lean_dec(x_1);
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
lean_dec(x_1);
x_31 = 0;
return x_31;
}
else
{
uint8_t x_32; 
x_32 = l_Bool_DecidableEq(x_22, x_26);
if (x_32 == 0)
{
uint8_t x_33; 
lean_dec(x_1);
x_33 = 0;
return x_33;
}
else
{
uint8_t x_34; 
x_34 = l_Array_isEqv___at_Lean_IR_args_alphaEqv___spec__1(x_1, x_23, x_27);
return x_34;
}
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_1);
x_35 = 0;
return x_35;
}
}
case 3:
{
if (lean_obj_tag(x_3) == 3)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_36 = lean_ctor_get(x_2, 0);
x_37 = lean_ctor_get(x_2, 1);
x_38 = lean_ctor_get(x_3, 0);
x_39 = lean_ctor_get(x_3, 1);
x_40 = lean_nat_dec_eq(x_36, x_38);
if (x_40 == 0)
{
uint8_t x_41; 
lean_dec(x_1);
x_41 = 0;
return x_41;
}
else
{
uint8_t x_42; 
x_42 = l_Lean_IR_VarId_alphaEqv(x_1, x_37, x_39);
lean_dec(x_1);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_1);
x_43 = 0;
return x_43;
}
}
case 4:
{
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_44 = lean_ctor_get(x_2, 0);
x_45 = lean_ctor_get(x_2, 1);
x_46 = lean_ctor_get(x_3, 0);
x_47 = lean_ctor_get(x_3, 1);
x_48 = lean_nat_dec_eq(x_44, x_46);
if (x_48 == 0)
{
uint8_t x_49; 
lean_dec(x_1);
x_49 = 0;
return x_49;
}
else
{
uint8_t x_50; 
x_50 = l_Lean_IR_VarId_alphaEqv(x_1, x_45, x_47);
lean_dec(x_1);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_1);
x_51 = 0;
return x_51;
}
}
case 5:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_52 = lean_ctor_get(x_2, 0);
x_53 = lean_ctor_get(x_2, 1);
x_54 = lean_ctor_get(x_2, 2);
x_55 = lean_ctor_get(x_3, 0);
x_56 = lean_ctor_get(x_3, 1);
x_57 = lean_ctor_get(x_3, 2);
x_58 = lean_nat_dec_eq(x_52, x_55);
if (x_58 == 0)
{
uint8_t x_59; 
lean_dec(x_1);
x_59 = 0;
return x_59;
}
else
{
uint8_t x_60; 
x_60 = lean_nat_dec_eq(x_53, x_56);
if (x_60 == 0)
{
uint8_t x_61; 
lean_dec(x_1);
x_61 = 0;
return x_61;
}
else
{
uint8_t x_62; 
x_62 = l_Lean_IR_VarId_alphaEqv(x_1, x_54, x_57);
lean_dec(x_1);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_1);
x_63 = 0;
return x_63;
}
}
case 6:
{
if (lean_obj_tag(x_3) == 6)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_64 = lean_ctor_get(x_2, 0);
x_65 = lean_ctor_get(x_2, 1);
x_66 = lean_ctor_get(x_3, 0);
x_67 = lean_ctor_get(x_3, 1);
x_68 = lean_name_eq(x_64, x_66);
if (x_68 == 0)
{
uint8_t x_69; 
lean_dec(x_1);
x_69 = 0;
return x_69;
}
else
{
uint8_t x_70; 
x_70 = l_Array_isEqv___at_Lean_IR_args_alphaEqv___spec__1(x_1, x_65, x_67);
return x_70;
}
}
else
{
uint8_t x_71; 
lean_dec(x_1);
x_71 = 0;
return x_71;
}
}
case 7:
{
if (lean_obj_tag(x_3) == 7)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_72 = lean_ctor_get(x_2, 0);
x_73 = lean_ctor_get(x_3, 0);
x_74 = lean_ctor_get(x_3, 1);
x_75 = lean_name_eq(x_72, x_73);
if (x_75 == 0)
{
uint8_t x_76; 
lean_dec(x_1);
x_76 = 0;
return x_76;
}
else
{
uint8_t x_77; 
x_77 = l_Array_isEqv___at_Lean_IR_args_alphaEqv___spec__1(x_1, x_74, x_74);
return x_77;
}
}
else
{
uint8_t x_78; 
lean_dec(x_1);
x_78 = 0;
return x_78;
}
}
case 8:
{
if (lean_obj_tag(x_3) == 8)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_79 = lean_ctor_get(x_2, 0);
x_80 = lean_ctor_get(x_2, 1);
x_81 = lean_ctor_get(x_3, 0);
x_82 = lean_ctor_get(x_3, 1);
x_83 = l_Lean_IR_VarId_alphaEqv(x_1, x_79, x_81);
if (x_83 == 0)
{
uint8_t x_84; 
lean_dec(x_1);
x_84 = 0;
return x_84;
}
else
{
uint8_t x_85; 
x_85 = l_Array_isEqv___at_Lean_IR_args_alphaEqv___spec__1(x_1, x_80, x_82);
return x_85;
}
}
else
{
uint8_t x_86; 
lean_dec(x_1);
x_86 = 0;
return x_86;
}
}
case 9:
{
if (lean_obj_tag(x_3) == 9)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_87 = lean_ctor_get(x_2, 0);
x_88 = lean_ctor_get(x_2, 1);
x_89 = lean_ctor_get(x_3, 0);
x_90 = lean_ctor_get(x_3, 1);
x_91 = l_Lean_IR_IRType_beq___main(x_87, x_89);
if (x_91 == 0)
{
uint8_t x_92; 
lean_dec(x_1);
x_92 = 0;
return x_92;
}
else
{
uint8_t x_93; 
x_93 = l_Lean_IR_VarId_alphaEqv(x_1, x_88, x_90);
lean_dec(x_1);
return x_93;
}
}
else
{
uint8_t x_94; 
lean_dec(x_1);
x_94 = 0;
return x_94;
}
}
case 10:
{
if (lean_obj_tag(x_3) == 10)
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_95 = lean_ctor_get(x_2, 0);
x_96 = lean_ctor_get(x_3, 0);
x_97 = l_Lean_IR_VarId_alphaEqv(x_1, x_95, x_96);
lean_dec(x_1);
return x_97;
}
else
{
uint8_t x_98; 
lean_dec(x_1);
x_98 = 0;
return x_98;
}
}
case 11:
{
lean_dec(x_1);
if (lean_obj_tag(x_3) == 11)
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_99 = lean_ctor_get(x_2, 0);
x_100 = lean_ctor_get(x_3, 0);
x_101 = l_Lean_IR_LitVal_beq(x_99, x_100);
return x_101;
}
else
{
uint8_t x_102; 
x_102 = 0;
return x_102;
}
}
case 12:
{
if (lean_obj_tag(x_3) == 12)
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_103 = lean_ctor_get(x_2, 0);
x_104 = lean_ctor_get(x_3, 0);
x_105 = l_Lean_IR_VarId_alphaEqv(x_1, x_103, x_104);
lean_dec(x_1);
return x_105;
}
else
{
uint8_t x_106; 
lean_dec(x_1);
x_106 = 0;
return x_106;
}
}
default: 
{
if (lean_obj_tag(x_3) == 13)
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_107 = lean_ctor_get(x_2, 0);
x_108 = lean_ctor_get(x_3, 0);
x_109 = l_Lean_IR_VarId_alphaEqv(x_1, x_107, x_108);
lean_dec(x_1);
return x_109;
}
else
{
uint8_t x_110; 
lean_dec(x_1);
x_110 = 0;
return x_110;
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
uint8_t x_4; lean_object* x_5; 
x_4 = 0;
x_5 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
lean_ctor_set(x_5, 3, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*4, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*4);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 3);
x_12 = lean_nat_dec_lt(x_2, x_9);
x_13 = 1;
x_14 = l_Bool_DecidableEq(x_12, x_13);
if (x_14 == 0)
{
uint8_t x_15; uint8_t x_16; 
x_15 = lean_nat_dec_lt(x_9, x_2);
x_16 = l_Bool_DecidableEq(x_15, x_13);
if (x_16 == 0)
{
lean_dec(x_10);
lean_dec(x_9);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
lean_object* x_17; 
x_17 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_11, x_2, x_3);
lean_ctor_set(x_1, 3, x_17);
return x_1;
}
}
else
{
lean_object* x_18; 
x_18 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_8, x_2, x_3);
lean_ctor_set(x_1, 0, x_18);
return x_1;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_1, 1);
x_21 = lean_ctor_get(x_1, 2);
x_22 = lean_ctor_get(x_1, 3);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_1);
x_23 = lean_nat_dec_lt(x_2, x_20);
x_24 = 1;
x_25 = l_Bool_DecidableEq(x_23, x_24);
if (x_25 == 0)
{
uint8_t x_26; uint8_t x_27; 
x_26 = lean_nat_dec_lt(x_20, x_2);
x_27 = l_Bool_DecidableEq(x_26, x_24);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_21);
lean_dec(x_20);
x_28 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_2);
lean_ctor_set(x_28, 2, x_3);
lean_ctor_set(x_28, 3, x_22);
lean_ctor_set_uint8(x_28, sizeof(void*)*4, x_6);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_22, x_2, x_3);
x_30 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_30, 0, x_19);
lean_ctor_set(x_30, 1, x_20);
lean_ctor_set(x_30, 2, x_21);
lean_ctor_set(x_30, 3, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_6);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_19, x_2, x_3);
x_32 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_20);
lean_ctor_set(x_32, 2, x_21);
lean_ctor_set(x_32, 3, x_22);
lean_ctor_set_uint8(x_32, sizeof(void*)*4, x_6);
return x_32;
}
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_1);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; 
x_34 = lean_ctor_get(x_1, 0);
x_35 = lean_ctor_get(x_1, 1);
x_36 = lean_ctor_get(x_1, 2);
x_37 = lean_ctor_get(x_1, 3);
x_38 = lean_nat_dec_lt(x_2, x_35);
x_39 = 1;
x_40 = l_Bool_DecidableEq(x_38, x_39);
if (x_40 == 0)
{
uint8_t x_41; uint8_t x_42; 
x_41 = lean_nat_dec_lt(x_35, x_2);
x_42 = l_Bool_DecidableEq(x_41, x_39);
if (x_42 == 0)
{
lean_dec(x_36);
lean_dec(x_35);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
uint8_t x_43; uint8_t x_44; 
x_43 = l_RBNode_isRed___rarg(x_37);
x_44 = l_Bool_DecidableEq(x_43, x_39);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_37, x_2, x_3);
lean_ctor_set(x_1, 3, x_45);
return x_1;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_37, x_2, x_3);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_46, 3);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_46);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_46, 3);
lean_dec(x_50);
x_51 = lean_ctor_get(x_46, 0);
lean_dec(x_51);
x_52 = 0;
lean_ctor_set(x_46, 0, x_48);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_52);
x_53 = 1;
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_53);
return x_1;
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_ctor_get(x_46, 1);
x_55 = lean_ctor_get(x_46, 2);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_46);
x_56 = 0;
x_57 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_57, 0, x_48);
lean_ctor_set(x_57, 1, x_54);
lean_ctor_set(x_57, 2, x_55);
lean_ctor_set(x_57, 3, x_48);
lean_ctor_set_uint8(x_57, sizeof(void*)*4, x_56);
x_58 = 1;
lean_ctor_set(x_1, 3, x_57);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_58);
return x_1;
}
}
else
{
uint8_t x_59; 
x_59 = lean_ctor_get_uint8(x_48, sizeof(void*)*4);
if (x_59 == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_46);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_61 = lean_ctor_get(x_46, 1);
x_62 = lean_ctor_get(x_46, 2);
x_63 = lean_ctor_get(x_46, 3);
lean_dec(x_63);
x_64 = lean_ctor_get(x_46, 0);
lean_dec(x_64);
x_65 = !lean_is_exclusive(x_48);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_66 = lean_ctor_get(x_48, 0);
x_67 = lean_ctor_get(x_48, 1);
x_68 = lean_ctor_get(x_48, 2);
x_69 = lean_ctor_get(x_48, 3);
x_70 = 1;
lean_ctor_set(x_48, 3, x_47);
lean_ctor_set(x_48, 2, x_36);
lean_ctor_set(x_48, 1, x_35);
lean_ctor_set(x_48, 0, x_34);
lean_ctor_set_uint8(x_48, sizeof(void*)*4, x_70);
lean_ctor_set(x_46, 3, x_69);
lean_ctor_set(x_46, 2, x_68);
lean_ctor_set(x_46, 1, x_67);
lean_ctor_set(x_46, 0, x_66);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_70);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set(x_1, 2, x_62);
lean_ctor_set(x_1, 1, x_61);
lean_ctor_set(x_1, 0, x_48);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_59);
return x_1;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; 
x_71 = lean_ctor_get(x_48, 0);
x_72 = lean_ctor_get(x_48, 1);
x_73 = lean_ctor_get(x_48, 2);
x_74 = lean_ctor_get(x_48, 3);
lean_inc(x_74);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_48);
x_75 = 1;
x_76 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_76, 0, x_34);
lean_ctor_set(x_76, 1, x_35);
lean_ctor_set(x_76, 2, x_36);
lean_ctor_set(x_76, 3, x_47);
lean_ctor_set_uint8(x_76, sizeof(void*)*4, x_75);
lean_ctor_set(x_46, 3, x_74);
lean_ctor_set(x_46, 2, x_73);
lean_ctor_set(x_46, 1, x_72);
lean_ctor_set(x_46, 0, x_71);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_75);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set(x_1, 2, x_62);
lean_ctor_set(x_1, 1, x_61);
lean_ctor_set(x_1, 0, x_76);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_59);
return x_1;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; 
x_77 = lean_ctor_get(x_46, 1);
x_78 = lean_ctor_get(x_46, 2);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_46);
x_79 = lean_ctor_get(x_48, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_48, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_48, 2);
lean_inc(x_81);
x_82 = lean_ctor_get(x_48, 3);
lean_inc(x_82);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 lean_ctor_release(x_48, 2);
 lean_ctor_release(x_48, 3);
 x_83 = x_48;
} else {
 lean_dec_ref(x_48);
 x_83 = lean_box(0);
}
x_84 = 1;
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(1, 4, 1);
} else {
 x_85 = x_83;
}
lean_ctor_set(x_85, 0, x_34);
lean_ctor_set(x_85, 1, x_35);
lean_ctor_set(x_85, 2, x_36);
lean_ctor_set(x_85, 3, x_47);
lean_ctor_set_uint8(x_85, sizeof(void*)*4, x_84);
x_86 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_86, 0, x_79);
lean_ctor_set(x_86, 1, x_80);
lean_ctor_set(x_86, 2, x_81);
lean_ctor_set(x_86, 3, x_82);
lean_ctor_set_uint8(x_86, sizeof(void*)*4, x_84);
lean_ctor_set(x_1, 3, x_86);
lean_ctor_set(x_1, 2, x_78);
lean_ctor_set(x_1, 1, x_77);
lean_ctor_set(x_1, 0, x_85);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_59);
return x_1;
}
}
else
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_46);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_88 = lean_ctor_get(x_46, 3);
lean_dec(x_88);
x_89 = lean_ctor_get(x_46, 0);
lean_dec(x_89);
x_90 = 0;
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_90);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_59);
return x_1;
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_46, 1);
x_92 = lean_ctor_get(x_46, 2);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_46);
x_93 = 0;
x_94 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_94, 0, x_47);
lean_ctor_set(x_94, 1, x_91);
lean_ctor_set(x_94, 2, x_92);
lean_ctor_set(x_94, 3, x_48);
lean_ctor_set_uint8(x_94, sizeof(void*)*4, x_93);
lean_ctor_set(x_1, 3, x_94);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_59);
return x_1;
}
}
}
}
else
{
uint8_t x_95; 
x_95 = lean_ctor_get_uint8(x_47, sizeof(void*)*4);
if (x_95 == 0)
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_46);
if (x_96 == 0)
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_ctor_get(x_46, 0);
lean_dec(x_97);
x_98 = !lean_is_exclusive(x_47);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_99 = lean_ctor_get(x_47, 0);
x_100 = lean_ctor_get(x_47, 1);
x_101 = lean_ctor_get(x_47, 2);
x_102 = lean_ctor_get(x_47, 3);
x_103 = 1;
lean_ctor_set(x_47, 3, x_99);
lean_ctor_set(x_47, 2, x_36);
lean_ctor_set(x_47, 1, x_35);
lean_ctor_set(x_47, 0, x_34);
lean_ctor_set_uint8(x_47, sizeof(void*)*4, x_103);
lean_ctor_set(x_46, 0, x_102);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_103);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set(x_1, 2, x_101);
lean_ctor_set(x_1, 1, x_100);
lean_ctor_set(x_1, 0, x_47);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_95);
return x_1;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; 
x_104 = lean_ctor_get(x_47, 0);
x_105 = lean_ctor_get(x_47, 1);
x_106 = lean_ctor_get(x_47, 2);
x_107 = lean_ctor_get(x_47, 3);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_47);
x_108 = 1;
x_109 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_109, 0, x_34);
lean_ctor_set(x_109, 1, x_35);
lean_ctor_set(x_109, 2, x_36);
lean_ctor_set(x_109, 3, x_104);
lean_ctor_set_uint8(x_109, sizeof(void*)*4, x_108);
lean_ctor_set(x_46, 0, x_107);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_108);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set(x_1, 2, x_106);
lean_ctor_set(x_1, 1, x_105);
lean_ctor_set(x_1, 0, x_109);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_95);
return x_1;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; 
x_110 = lean_ctor_get(x_46, 1);
x_111 = lean_ctor_get(x_46, 2);
x_112 = lean_ctor_get(x_46, 3);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_46);
x_113 = lean_ctor_get(x_47, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_47, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_47, 2);
lean_inc(x_115);
x_116 = lean_ctor_get(x_47, 3);
lean_inc(x_116);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_117 = x_47;
} else {
 lean_dec_ref(x_47);
 x_117 = lean_box(0);
}
x_118 = 1;
if (lean_is_scalar(x_117)) {
 x_119 = lean_alloc_ctor(1, 4, 1);
} else {
 x_119 = x_117;
}
lean_ctor_set(x_119, 0, x_34);
lean_ctor_set(x_119, 1, x_35);
lean_ctor_set(x_119, 2, x_36);
lean_ctor_set(x_119, 3, x_113);
lean_ctor_set_uint8(x_119, sizeof(void*)*4, x_118);
x_120 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_120, 0, x_116);
lean_ctor_set(x_120, 1, x_110);
lean_ctor_set(x_120, 2, x_111);
lean_ctor_set(x_120, 3, x_112);
lean_ctor_set_uint8(x_120, sizeof(void*)*4, x_118);
lean_ctor_set(x_1, 3, x_120);
lean_ctor_set(x_1, 2, x_115);
lean_ctor_set(x_1, 1, x_114);
lean_ctor_set(x_1, 0, x_119);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_95);
return x_1;
}
}
else
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_46, 3);
lean_inc(x_121);
if (lean_obj_tag(x_121) == 0)
{
uint8_t x_122; 
x_122 = !lean_is_exclusive(x_46);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_123 = lean_ctor_get(x_46, 3);
lean_dec(x_123);
x_124 = lean_ctor_get(x_46, 0);
lean_dec(x_124);
x_125 = 0;
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_125);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_95);
return x_1;
}
else
{
lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; 
x_126 = lean_ctor_get(x_46, 1);
x_127 = lean_ctor_get(x_46, 2);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_46);
x_128 = 0;
x_129 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_129, 0, x_47);
lean_ctor_set(x_129, 1, x_126);
lean_ctor_set(x_129, 2, x_127);
lean_ctor_set(x_129, 3, x_121);
lean_ctor_set_uint8(x_129, sizeof(void*)*4, x_128);
lean_ctor_set(x_1, 3, x_129);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_95);
return x_1;
}
}
else
{
uint8_t x_130; 
x_130 = lean_ctor_get_uint8(x_121, sizeof(void*)*4);
if (x_130 == 0)
{
uint8_t x_131; 
lean_free_object(x_1);
x_131 = !lean_is_exclusive(x_46);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_132 = lean_ctor_get(x_46, 3);
lean_dec(x_132);
x_133 = lean_ctor_get(x_46, 0);
lean_dec(x_133);
x_134 = !lean_is_exclusive(x_121);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_135 = lean_ctor_get(x_121, 0);
x_136 = lean_ctor_get(x_121, 1);
x_137 = lean_ctor_get(x_121, 2);
x_138 = lean_ctor_get(x_121, 3);
lean_inc(x_47);
lean_ctor_set(x_121, 3, x_47);
lean_ctor_set(x_121, 2, x_36);
lean_ctor_set(x_121, 1, x_35);
lean_ctor_set(x_121, 0, x_34);
x_139 = !lean_is_exclusive(x_47);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_140 = lean_ctor_get(x_47, 3);
lean_dec(x_140);
x_141 = lean_ctor_get(x_47, 2);
lean_dec(x_141);
x_142 = lean_ctor_get(x_47, 1);
lean_dec(x_142);
x_143 = lean_ctor_get(x_47, 0);
lean_dec(x_143);
lean_ctor_set_uint8(x_121, sizeof(void*)*4, x_95);
lean_ctor_set(x_47, 3, x_138);
lean_ctor_set(x_47, 2, x_137);
lean_ctor_set(x_47, 1, x_136);
lean_ctor_set(x_47, 0, x_135);
lean_ctor_set(x_46, 3, x_47);
lean_ctor_set(x_46, 0, x_121);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_130);
return x_46;
}
else
{
lean_object* x_144; 
lean_dec(x_47);
lean_ctor_set_uint8(x_121, sizeof(void*)*4, x_95);
x_144 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_144, 0, x_135);
lean_ctor_set(x_144, 1, x_136);
lean_ctor_set(x_144, 2, x_137);
lean_ctor_set(x_144, 3, x_138);
lean_ctor_set_uint8(x_144, sizeof(void*)*4, x_95);
lean_ctor_set(x_46, 3, x_144);
lean_ctor_set(x_46, 0, x_121);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_130);
return x_46;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_145 = lean_ctor_get(x_121, 0);
x_146 = lean_ctor_get(x_121, 1);
x_147 = lean_ctor_get(x_121, 2);
x_148 = lean_ctor_get(x_121, 3);
lean_inc(x_148);
lean_inc(x_147);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_121);
lean_inc(x_47);
x_149 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_149, 0, x_34);
lean_ctor_set(x_149, 1, x_35);
lean_ctor_set(x_149, 2, x_36);
lean_ctor_set(x_149, 3, x_47);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_150 = x_47;
} else {
 lean_dec_ref(x_47);
 x_150 = lean_box(0);
}
lean_ctor_set_uint8(x_149, sizeof(void*)*4, x_95);
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 4, 1);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_145);
lean_ctor_set(x_151, 1, x_146);
lean_ctor_set(x_151, 2, x_147);
lean_ctor_set(x_151, 3, x_148);
lean_ctor_set_uint8(x_151, sizeof(void*)*4, x_95);
lean_ctor_set(x_46, 3, x_151);
lean_ctor_set(x_46, 0, x_149);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_130);
return x_46;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_152 = lean_ctor_get(x_46, 1);
x_153 = lean_ctor_get(x_46, 2);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_46);
x_154 = lean_ctor_get(x_121, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_121, 1);
lean_inc(x_155);
x_156 = lean_ctor_get(x_121, 2);
lean_inc(x_156);
x_157 = lean_ctor_get(x_121, 3);
lean_inc(x_157);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 lean_ctor_release(x_121, 2);
 lean_ctor_release(x_121, 3);
 x_158 = x_121;
} else {
 lean_dec_ref(x_121);
 x_158 = lean_box(0);
}
lean_inc(x_47);
if (lean_is_scalar(x_158)) {
 x_159 = lean_alloc_ctor(1, 4, 1);
} else {
 x_159 = x_158;
}
lean_ctor_set(x_159, 0, x_34);
lean_ctor_set(x_159, 1, x_35);
lean_ctor_set(x_159, 2, x_36);
lean_ctor_set(x_159, 3, x_47);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_160 = x_47;
} else {
 lean_dec_ref(x_47);
 x_160 = lean_box(0);
}
lean_ctor_set_uint8(x_159, sizeof(void*)*4, x_95);
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 4, 1);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_154);
lean_ctor_set(x_161, 1, x_155);
lean_ctor_set(x_161, 2, x_156);
lean_ctor_set(x_161, 3, x_157);
lean_ctor_set_uint8(x_161, sizeof(void*)*4, x_95);
x_162 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_152);
lean_ctor_set(x_162, 2, x_153);
lean_ctor_set(x_162, 3, x_161);
lean_ctor_set_uint8(x_162, sizeof(void*)*4, x_130);
return x_162;
}
}
else
{
uint8_t x_163; 
x_163 = !lean_is_exclusive(x_46);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_164 = lean_ctor_get(x_46, 3);
lean_dec(x_164);
x_165 = lean_ctor_get(x_46, 0);
lean_dec(x_165);
x_166 = !lean_is_exclusive(x_47);
if (x_166 == 0)
{
uint8_t x_167; 
lean_ctor_set_uint8(x_47, sizeof(void*)*4, x_130);
x_167 = 0;
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_167);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_130);
return x_1;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_168 = lean_ctor_get(x_47, 0);
x_169 = lean_ctor_get(x_47, 1);
x_170 = lean_ctor_get(x_47, 2);
x_171 = lean_ctor_get(x_47, 3);
lean_inc(x_171);
lean_inc(x_170);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_47);
x_172 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_172, 0, x_168);
lean_ctor_set(x_172, 1, x_169);
lean_ctor_set(x_172, 2, x_170);
lean_ctor_set(x_172, 3, x_171);
lean_ctor_set_uint8(x_172, sizeof(void*)*4, x_130);
x_173 = 0;
lean_ctor_set(x_46, 0, x_172);
lean_ctor_set_uint8(x_46, sizeof(void*)*4, x_173);
lean_ctor_set(x_1, 3, x_46);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_130);
return x_1;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; lean_object* x_183; 
x_174 = lean_ctor_get(x_46, 1);
x_175 = lean_ctor_get(x_46, 2);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_46);
x_176 = lean_ctor_get(x_47, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_47, 1);
lean_inc(x_177);
x_178 = lean_ctor_get(x_47, 2);
lean_inc(x_178);
x_179 = lean_ctor_get(x_47, 3);
lean_inc(x_179);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 lean_ctor_release(x_47, 2);
 lean_ctor_release(x_47, 3);
 x_180 = x_47;
} else {
 lean_dec_ref(x_47);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(1, 4, 1);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_176);
lean_ctor_set(x_181, 1, x_177);
lean_ctor_set(x_181, 2, x_178);
lean_ctor_set(x_181, 3, x_179);
lean_ctor_set_uint8(x_181, sizeof(void*)*4, x_130);
x_182 = 0;
x_183 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_174);
lean_ctor_set(x_183, 2, x_175);
lean_ctor_set(x_183, 3, x_121);
lean_ctor_set_uint8(x_183, sizeof(void*)*4, x_182);
lean_ctor_set(x_1, 3, x_183);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_130);
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
uint8_t x_184; uint8_t x_185; 
x_184 = l_RBNode_isRed___rarg(x_34);
x_185 = l_Bool_DecidableEq(x_184, x_39);
if (x_185 == 0)
{
lean_object* x_186; 
x_186 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_34, x_2, x_3);
lean_ctor_set(x_1, 0, x_186);
return x_1;
}
else
{
lean_object* x_187; lean_object* x_188; 
x_187 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_34, x_2, x_3);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; 
x_189 = lean_ctor_get(x_187, 3);
lean_inc(x_189);
if (lean_obj_tag(x_189) == 0)
{
uint8_t x_190; 
x_190 = !lean_is_exclusive(x_187);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; uint8_t x_193; uint8_t x_194; 
x_191 = lean_ctor_get(x_187, 3);
lean_dec(x_191);
x_192 = lean_ctor_get(x_187, 0);
lean_dec(x_192);
x_193 = 0;
lean_ctor_set(x_187, 0, x_189);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_193);
x_194 = 1;
lean_ctor_set(x_1, 0, x_187);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_194);
return x_1;
}
else
{
lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; uint8_t x_199; 
x_195 = lean_ctor_get(x_187, 1);
x_196 = lean_ctor_get(x_187, 2);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_187);
x_197 = 0;
x_198 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_198, 0, x_189);
lean_ctor_set(x_198, 1, x_195);
lean_ctor_set(x_198, 2, x_196);
lean_ctor_set(x_198, 3, x_189);
lean_ctor_set_uint8(x_198, sizeof(void*)*4, x_197);
x_199 = 1;
lean_ctor_set(x_1, 0, x_198);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_199);
return x_1;
}
}
else
{
uint8_t x_200; 
x_200 = lean_ctor_get_uint8(x_189, sizeof(void*)*4);
if (x_200 == 0)
{
uint8_t x_201; 
x_201 = !lean_is_exclusive(x_187);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; 
x_202 = lean_ctor_get(x_187, 1);
x_203 = lean_ctor_get(x_187, 2);
x_204 = lean_ctor_get(x_187, 3);
lean_dec(x_204);
x_205 = lean_ctor_get(x_187, 0);
lean_dec(x_205);
x_206 = !lean_is_exclusive(x_189);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; 
x_207 = lean_ctor_get(x_189, 0);
x_208 = lean_ctor_get(x_189, 1);
x_209 = lean_ctor_get(x_189, 2);
x_210 = lean_ctor_get(x_189, 3);
x_211 = 1;
lean_ctor_set(x_189, 3, x_207);
lean_ctor_set(x_189, 2, x_203);
lean_ctor_set(x_189, 1, x_202);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set_uint8(x_189, sizeof(void*)*4, x_211);
lean_ctor_set(x_187, 3, x_37);
lean_ctor_set(x_187, 2, x_36);
lean_ctor_set(x_187, 1, x_35);
lean_ctor_set(x_187, 0, x_210);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_211);
lean_ctor_set(x_1, 3, x_187);
lean_ctor_set(x_1, 2, x_209);
lean_ctor_set(x_1, 1, x_208);
lean_ctor_set(x_1, 0, x_189);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_200);
return x_1;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; 
x_212 = lean_ctor_get(x_189, 0);
x_213 = lean_ctor_get(x_189, 1);
x_214 = lean_ctor_get(x_189, 2);
x_215 = lean_ctor_get(x_189, 3);
lean_inc(x_215);
lean_inc(x_214);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_189);
x_216 = 1;
x_217 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_217, 0, x_188);
lean_ctor_set(x_217, 1, x_202);
lean_ctor_set(x_217, 2, x_203);
lean_ctor_set(x_217, 3, x_212);
lean_ctor_set_uint8(x_217, sizeof(void*)*4, x_216);
lean_ctor_set(x_187, 3, x_37);
lean_ctor_set(x_187, 2, x_36);
lean_ctor_set(x_187, 1, x_35);
lean_ctor_set(x_187, 0, x_215);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_216);
lean_ctor_set(x_1, 3, x_187);
lean_ctor_set(x_1, 2, x_214);
lean_ctor_set(x_1, 1, x_213);
lean_ctor_set(x_1, 0, x_217);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_200);
return x_1;
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; lean_object* x_226; lean_object* x_227; 
x_218 = lean_ctor_get(x_187, 1);
x_219 = lean_ctor_get(x_187, 2);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_187);
x_220 = lean_ctor_get(x_189, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_189, 1);
lean_inc(x_221);
x_222 = lean_ctor_get(x_189, 2);
lean_inc(x_222);
x_223 = lean_ctor_get(x_189, 3);
lean_inc(x_223);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 lean_ctor_release(x_189, 2);
 lean_ctor_release(x_189, 3);
 x_224 = x_189;
} else {
 lean_dec_ref(x_189);
 x_224 = lean_box(0);
}
x_225 = 1;
if (lean_is_scalar(x_224)) {
 x_226 = lean_alloc_ctor(1, 4, 1);
} else {
 x_226 = x_224;
}
lean_ctor_set(x_226, 0, x_188);
lean_ctor_set(x_226, 1, x_218);
lean_ctor_set(x_226, 2, x_219);
lean_ctor_set(x_226, 3, x_220);
lean_ctor_set_uint8(x_226, sizeof(void*)*4, x_225);
x_227 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_227, 0, x_223);
lean_ctor_set(x_227, 1, x_35);
lean_ctor_set(x_227, 2, x_36);
lean_ctor_set(x_227, 3, x_37);
lean_ctor_set_uint8(x_227, sizeof(void*)*4, x_225);
lean_ctor_set(x_1, 3, x_227);
lean_ctor_set(x_1, 2, x_222);
lean_ctor_set(x_1, 1, x_221);
lean_ctor_set(x_1, 0, x_226);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_200);
return x_1;
}
}
else
{
uint8_t x_228; 
x_228 = !lean_is_exclusive(x_187);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; uint8_t x_231; 
x_229 = lean_ctor_get(x_187, 3);
lean_dec(x_229);
x_230 = lean_ctor_get(x_187, 0);
lean_dec(x_230);
x_231 = 0;
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_231);
lean_ctor_set(x_1, 0, x_187);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_200);
return x_1;
}
else
{
lean_object* x_232; lean_object* x_233; uint8_t x_234; lean_object* x_235; 
x_232 = lean_ctor_get(x_187, 1);
x_233 = lean_ctor_get(x_187, 2);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_187);
x_234 = 0;
x_235 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_235, 0, x_188);
lean_ctor_set(x_235, 1, x_232);
lean_ctor_set(x_235, 2, x_233);
lean_ctor_set(x_235, 3, x_189);
lean_ctor_set_uint8(x_235, sizeof(void*)*4, x_234);
lean_ctor_set(x_1, 0, x_235);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_200);
return x_1;
}
}
}
}
else
{
uint8_t x_236; 
x_236 = lean_ctor_get_uint8(x_188, sizeof(void*)*4);
if (x_236 == 0)
{
uint8_t x_237; 
x_237 = !lean_is_exclusive(x_187);
if (x_237 == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; 
x_238 = lean_ctor_get(x_187, 1);
x_239 = lean_ctor_get(x_187, 2);
x_240 = lean_ctor_get(x_187, 3);
x_241 = lean_ctor_get(x_187, 0);
lean_dec(x_241);
x_242 = !lean_is_exclusive(x_188);
if (x_242 == 0)
{
uint8_t x_243; 
x_243 = 1;
lean_ctor_set_uint8(x_188, sizeof(void*)*4, x_243);
lean_ctor_set(x_187, 3, x_37);
lean_ctor_set(x_187, 2, x_36);
lean_ctor_set(x_187, 1, x_35);
lean_ctor_set(x_187, 0, x_240);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_243);
lean_ctor_set(x_1, 3, x_187);
lean_ctor_set(x_1, 2, x_239);
lean_ctor_set(x_1, 1, x_238);
lean_ctor_set(x_1, 0, x_188);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_236);
return x_1;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; uint8_t x_248; lean_object* x_249; 
x_244 = lean_ctor_get(x_188, 0);
x_245 = lean_ctor_get(x_188, 1);
x_246 = lean_ctor_get(x_188, 2);
x_247 = lean_ctor_get(x_188, 3);
lean_inc(x_247);
lean_inc(x_246);
lean_inc(x_245);
lean_inc(x_244);
lean_dec(x_188);
x_248 = 1;
x_249 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_249, 0, x_244);
lean_ctor_set(x_249, 1, x_245);
lean_ctor_set(x_249, 2, x_246);
lean_ctor_set(x_249, 3, x_247);
lean_ctor_set_uint8(x_249, sizeof(void*)*4, x_248);
lean_ctor_set(x_187, 3, x_37);
lean_ctor_set(x_187, 2, x_36);
lean_ctor_set(x_187, 1, x_35);
lean_ctor_set(x_187, 0, x_240);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_248);
lean_ctor_set(x_1, 3, x_187);
lean_ctor_set(x_1, 2, x_239);
lean_ctor_set(x_1, 1, x_238);
lean_ctor_set(x_1, 0, x_249);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_236);
return x_1;
}
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; lean_object* x_259; lean_object* x_260; 
x_250 = lean_ctor_get(x_187, 1);
x_251 = lean_ctor_get(x_187, 2);
x_252 = lean_ctor_get(x_187, 3);
lean_inc(x_252);
lean_inc(x_251);
lean_inc(x_250);
lean_dec(x_187);
x_253 = lean_ctor_get(x_188, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_188, 1);
lean_inc(x_254);
x_255 = lean_ctor_get(x_188, 2);
lean_inc(x_255);
x_256 = lean_ctor_get(x_188, 3);
lean_inc(x_256);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 lean_ctor_release(x_188, 2);
 lean_ctor_release(x_188, 3);
 x_257 = x_188;
} else {
 lean_dec_ref(x_188);
 x_257 = lean_box(0);
}
x_258 = 1;
if (lean_is_scalar(x_257)) {
 x_259 = lean_alloc_ctor(1, 4, 1);
} else {
 x_259 = x_257;
}
lean_ctor_set(x_259, 0, x_253);
lean_ctor_set(x_259, 1, x_254);
lean_ctor_set(x_259, 2, x_255);
lean_ctor_set(x_259, 3, x_256);
lean_ctor_set_uint8(x_259, sizeof(void*)*4, x_258);
x_260 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_260, 0, x_252);
lean_ctor_set(x_260, 1, x_35);
lean_ctor_set(x_260, 2, x_36);
lean_ctor_set(x_260, 3, x_37);
lean_ctor_set_uint8(x_260, sizeof(void*)*4, x_258);
lean_ctor_set(x_1, 3, x_260);
lean_ctor_set(x_1, 2, x_251);
lean_ctor_set(x_1, 1, x_250);
lean_ctor_set(x_1, 0, x_259);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_236);
return x_1;
}
}
else
{
lean_object* x_261; 
x_261 = lean_ctor_get(x_187, 3);
lean_inc(x_261);
if (lean_obj_tag(x_261) == 0)
{
uint8_t x_262; 
x_262 = !lean_is_exclusive(x_187);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; uint8_t x_265; 
x_263 = lean_ctor_get(x_187, 3);
lean_dec(x_263);
x_264 = lean_ctor_get(x_187, 0);
lean_dec(x_264);
x_265 = 0;
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_265);
lean_ctor_set(x_1, 0, x_187);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_236);
return x_1;
}
else
{
lean_object* x_266; lean_object* x_267; uint8_t x_268; lean_object* x_269; 
x_266 = lean_ctor_get(x_187, 1);
x_267 = lean_ctor_get(x_187, 2);
lean_inc(x_267);
lean_inc(x_266);
lean_dec(x_187);
x_268 = 0;
x_269 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_269, 0, x_188);
lean_ctor_set(x_269, 1, x_266);
lean_ctor_set(x_269, 2, x_267);
lean_ctor_set(x_269, 3, x_261);
lean_ctor_set_uint8(x_269, sizeof(void*)*4, x_268);
lean_ctor_set(x_1, 0, x_269);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_236);
return x_1;
}
}
else
{
uint8_t x_270; 
x_270 = lean_ctor_get_uint8(x_261, sizeof(void*)*4);
if (x_270 == 0)
{
uint8_t x_271; 
lean_free_object(x_1);
x_271 = !lean_is_exclusive(x_187);
if (x_271 == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; uint8_t x_276; 
x_272 = lean_ctor_get(x_187, 1);
x_273 = lean_ctor_get(x_187, 2);
x_274 = lean_ctor_get(x_187, 3);
lean_dec(x_274);
x_275 = lean_ctor_get(x_187, 0);
lean_dec(x_275);
x_276 = !lean_is_exclusive(x_261);
if (x_276 == 0)
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; uint8_t x_281; 
x_277 = lean_ctor_get(x_261, 0);
x_278 = lean_ctor_get(x_261, 1);
x_279 = lean_ctor_get(x_261, 2);
x_280 = lean_ctor_get(x_261, 3);
lean_inc(x_188);
lean_ctor_set(x_261, 3, x_277);
lean_ctor_set(x_261, 2, x_273);
lean_ctor_set(x_261, 1, x_272);
lean_ctor_set(x_261, 0, x_188);
x_281 = !lean_is_exclusive(x_188);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_282 = lean_ctor_get(x_188, 3);
lean_dec(x_282);
x_283 = lean_ctor_get(x_188, 2);
lean_dec(x_283);
x_284 = lean_ctor_get(x_188, 1);
lean_dec(x_284);
x_285 = lean_ctor_get(x_188, 0);
lean_dec(x_285);
lean_ctor_set_uint8(x_261, sizeof(void*)*4, x_236);
lean_ctor_set(x_188, 3, x_37);
lean_ctor_set(x_188, 2, x_36);
lean_ctor_set(x_188, 1, x_35);
lean_ctor_set(x_188, 0, x_280);
lean_ctor_set(x_187, 3, x_188);
lean_ctor_set(x_187, 2, x_279);
lean_ctor_set(x_187, 1, x_278);
lean_ctor_set(x_187, 0, x_261);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_270);
return x_187;
}
else
{
lean_object* x_286; 
lean_dec(x_188);
lean_ctor_set_uint8(x_261, sizeof(void*)*4, x_236);
x_286 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_286, 0, x_280);
lean_ctor_set(x_286, 1, x_35);
lean_ctor_set(x_286, 2, x_36);
lean_ctor_set(x_286, 3, x_37);
lean_ctor_set_uint8(x_286, sizeof(void*)*4, x_236);
lean_ctor_set(x_187, 3, x_286);
lean_ctor_set(x_187, 2, x_279);
lean_ctor_set(x_187, 1, x_278);
lean_ctor_set(x_187, 0, x_261);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_270);
return x_187;
}
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_287 = lean_ctor_get(x_261, 0);
x_288 = lean_ctor_get(x_261, 1);
x_289 = lean_ctor_get(x_261, 2);
x_290 = lean_ctor_get(x_261, 3);
lean_inc(x_290);
lean_inc(x_289);
lean_inc(x_288);
lean_inc(x_287);
lean_dec(x_261);
lean_inc(x_188);
x_291 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_291, 0, x_188);
lean_ctor_set(x_291, 1, x_272);
lean_ctor_set(x_291, 2, x_273);
lean_ctor_set(x_291, 3, x_287);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 lean_ctor_release(x_188, 2);
 lean_ctor_release(x_188, 3);
 x_292 = x_188;
} else {
 lean_dec_ref(x_188);
 x_292 = lean_box(0);
}
lean_ctor_set_uint8(x_291, sizeof(void*)*4, x_236);
if (lean_is_scalar(x_292)) {
 x_293 = lean_alloc_ctor(1, 4, 1);
} else {
 x_293 = x_292;
}
lean_ctor_set(x_293, 0, x_290);
lean_ctor_set(x_293, 1, x_35);
lean_ctor_set(x_293, 2, x_36);
lean_ctor_set(x_293, 3, x_37);
lean_ctor_set_uint8(x_293, sizeof(void*)*4, x_236);
lean_ctor_set(x_187, 3, x_293);
lean_ctor_set(x_187, 2, x_289);
lean_ctor_set(x_187, 1, x_288);
lean_ctor_set(x_187, 0, x_291);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_270);
return x_187;
}
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_294 = lean_ctor_get(x_187, 1);
x_295 = lean_ctor_get(x_187, 2);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_187);
x_296 = lean_ctor_get(x_261, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_261, 1);
lean_inc(x_297);
x_298 = lean_ctor_get(x_261, 2);
lean_inc(x_298);
x_299 = lean_ctor_get(x_261, 3);
lean_inc(x_299);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 lean_ctor_release(x_261, 2);
 lean_ctor_release(x_261, 3);
 x_300 = x_261;
} else {
 lean_dec_ref(x_261);
 x_300 = lean_box(0);
}
lean_inc(x_188);
if (lean_is_scalar(x_300)) {
 x_301 = lean_alloc_ctor(1, 4, 1);
} else {
 x_301 = x_300;
}
lean_ctor_set(x_301, 0, x_188);
lean_ctor_set(x_301, 1, x_294);
lean_ctor_set(x_301, 2, x_295);
lean_ctor_set(x_301, 3, x_296);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 lean_ctor_release(x_188, 2);
 lean_ctor_release(x_188, 3);
 x_302 = x_188;
} else {
 lean_dec_ref(x_188);
 x_302 = lean_box(0);
}
lean_ctor_set_uint8(x_301, sizeof(void*)*4, x_236);
if (lean_is_scalar(x_302)) {
 x_303 = lean_alloc_ctor(1, 4, 1);
} else {
 x_303 = x_302;
}
lean_ctor_set(x_303, 0, x_299);
lean_ctor_set(x_303, 1, x_35);
lean_ctor_set(x_303, 2, x_36);
lean_ctor_set(x_303, 3, x_37);
lean_ctor_set_uint8(x_303, sizeof(void*)*4, x_236);
x_304 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_304, 0, x_301);
lean_ctor_set(x_304, 1, x_297);
lean_ctor_set(x_304, 2, x_298);
lean_ctor_set(x_304, 3, x_303);
lean_ctor_set_uint8(x_304, sizeof(void*)*4, x_270);
return x_304;
}
}
else
{
uint8_t x_305; 
x_305 = !lean_is_exclusive(x_187);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; uint8_t x_308; 
x_306 = lean_ctor_get(x_187, 3);
lean_dec(x_306);
x_307 = lean_ctor_get(x_187, 0);
lean_dec(x_307);
x_308 = !lean_is_exclusive(x_188);
if (x_308 == 0)
{
uint8_t x_309; 
lean_ctor_set_uint8(x_188, sizeof(void*)*4, x_270);
x_309 = 0;
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_309);
lean_ctor_set(x_1, 0, x_187);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_270);
return x_1;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; uint8_t x_315; 
x_310 = lean_ctor_get(x_188, 0);
x_311 = lean_ctor_get(x_188, 1);
x_312 = lean_ctor_get(x_188, 2);
x_313 = lean_ctor_get(x_188, 3);
lean_inc(x_313);
lean_inc(x_312);
lean_inc(x_311);
lean_inc(x_310);
lean_dec(x_188);
x_314 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_314, 0, x_310);
lean_ctor_set(x_314, 1, x_311);
lean_ctor_set(x_314, 2, x_312);
lean_ctor_set(x_314, 3, x_313);
lean_ctor_set_uint8(x_314, sizeof(void*)*4, x_270);
x_315 = 0;
lean_ctor_set(x_187, 0, x_314);
lean_ctor_set_uint8(x_187, sizeof(void*)*4, x_315);
lean_ctor_set(x_1, 0, x_187);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_270);
return x_1;
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; lean_object* x_325; 
x_316 = lean_ctor_get(x_187, 1);
x_317 = lean_ctor_get(x_187, 2);
lean_inc(x_317);
lean_inc(x_316);
lean_dec(x_187);
x_318 = lean_ctor_get(x_188, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_188, 1);
lean_inc(x_319);
x_320 = lean_ctor_get(x_188, 2);
lean_inc(x_320);
x_321 = lean_ctor_get(x_188, 3);
lean_inc(x_321);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 lean_ctor_release(x_188, 2);
 lean_ctor_release(x_188, 3);
 x_322 = x_188;
} else {
 lean_dec_ref(x_188);
 x_322 = lean_box(0);
}
if (lean_is_scalar(x_322)) {
 x_323 = lean_alloc_ctor(1, 4, 1);
} else {
 x_323 = x_322;
}
lean_ctor_set(x_323, 0, x_318);
lean_ctor_set(x_323, 1, x_319);
lean_ctor_set(x_323, 2, x_320);
lean_ctor_set(x_323, 3, x_321);
lean_ctor_set_uint8(x_323, sizeof(void*)*4, x_270);
x_324 = 0;
x_325 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_325, 0, x_323);
lean_ctor_set(x_325, 1, x_316);
lean_ctor_set(x_325, 2, x_317);
lean_ctor_set(x_325, 3, x_261);
lean_ctor_set_uint8(x_325, sizeof(void*)*4, x_324);
lean_ctor_set(x_1, 0, x_325);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_270);
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
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; uint8_t x_330; uint8_t x_331; uint8_t x_332; 
x_326 = lean_ctor_get(x_1, 0);
x_327 = lean_ctor_get(x_1, 1);
x_328 = lean_ctor_get(x_1, 2);
x_329 = lean_ctor_get(x_1, 3);
lean_inc(x_329);
lean_inc(x_328);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_1);
x_330 = lean_nat_dec_lt(x_2, x_327);
x_331 = 1;
x_332 = l_Bool_DecidableEq(x_330, x_331);
if (x_332 == 0)
{
uint8_t x_333; uint8_t x_334; 
x_333 = lean_nat_dec_lt(x_327, x_2);
x_334 = l_Bool_DecidableEq(x_333, x_331);
if (x_334 == 0)
{
lean_object* x_335; 
lean_dec(x_328);
lean_dec(x_327);
x_335 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_335, 0, x_326);
lean_ctor_set(x_335, 1, x_2);
lean_ctor_set(x_335, 2, x_3);
lean_ctor_set(x_335, 3, x_329);
lean_ctor_set_uint8(x_335, sizeof(void*)*4, x_6);
return x_335;
}
else
{
uint8_t x_336; uint8_t x_337; 
x_336 = l_RBNode_isRed___rarg(x_329);
x_337 = l_Bool_DecidableEq(x_336, x_331);
if (x_337 == 0)
{
lean_object* x_338; lean_object* x_339; 
x_338 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_329, x_2, x_3);
x_339 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_339, 0, x_326);
lean_ctor_set(x_339, 1, x_327);
lean_ctor_set(x_339, 2, x_328);
lean_ctor_set(x_339, 3, x_338);
lean_ctor_set_uint8(x_339, sizeof(void*)*4, x_6);
return x_339;
}
else
{
lean_object* x_340; lean_object* x_341; 
x_340 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_329, x_2, x_3);
x_341 = lean_ctor_get(x_340, 0);
lean_inc(x_341);
if (lean_obj_tag(x_341) == 0)
{
lean_object* x_342; 
x_342 = lean_ctor_get(x_340, 3);
lean_inc(x_342);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; uint8_t x_346; lean_object* x_347; uint8_t x_348; lean_object* x_349; 
x_343 = lean_ctor_get(x_340, 1);
lean_inc(x_343);
x_344 = lean_ctor_get(x_340, 2);
lean_inc(x_344);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 lean_ctor_release(x_340, 2);
 lean_ctor_release(x_340, 3);
 x_345 = x_340;
} else {
 lean_dec_ref(x_340);
 x_345 = lean_box(0);
}
x_346 = 0;
if (lean_is_scalar(x_345)) {
 x_347 = lean_alloc_ctor(1, 4, 1);
} else {
 x_347 = x_345;
}
lean_ctor_set(x_347, 0, x_342);
lean_ctor_set(x_347, 1, x_343);
lean_ctor_set(x_347, 2, x_344);
lean_ctor_set(x_347, 3, x_342);
lean_ctor_set_uint8(x_347, sizeof(void*)*4, x_346);
x_348 = 1;
x_349 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_349, 0, x_326);
lean_ctor_set(x_349, 1, x_327);
lean_ctor_set(x_349, 2, x_328);
lean_ctor_set(x_349, 3, x_347);
lean_ctor_set_uint8(x_349, sizeof(void*)*4, x_348);
return x_349;
}
else
{
uint8_t x_350; 
x_350 = lean_ctor_get_uint8(x_342, sizeof(void*)*4);
if (x_350 == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; uint8_t x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_351 = lean_ctor_get(x_340, 1);
lean_inc(x_351);
x_352 = lean_ctor_get(x_340, 2);
lean_inc(x_352);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 lean_ctor_release(x_340, 2);
 lean_ctor_release(x_340, 3);
 x_353 = x_340;
} else {
 lean_dec_ref(x_340);
 x_353 = lean_box(0);
}
x_354 = lean_ctor_get(x_342, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_342, 1);
lean_inc(x_355);
x_356 = lean_ctor_get(x_342, 2);
lean_inc(x_356);
x_357 = lean_ctor_get(x_342, 3);
lean_inc(x_357);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 lean_ctor_release(x_342, 2);
 lean_ctor_release(x_342, 3);
 x_358 = x_342;
} else {
 lean_dec_ref(x_342);
 x_358 = lean_box(0);
}
x_359 = 1;
if (lean_is_scalar(x_358)) {
 x_360 = lean_alloc_ctor(1, 4, 1);
} else {
 x_360 = x_358;
}
lean_ctor_set(x_360, 0, x_326);
lean_ctor_set(x_360, 1, x_327);
lean_ctor_set(x_360, 2, x_328);
lean_ctor_set(x_360, 3, x_341);
lean_ctor_set_uint8(x_360, sizeof(void*)*4, x_359);
if (lean_is_scalar(x_353)) {
 x_361 = lean_alloc_ctor(1, 4, 1);
} else {
 x_361 = x_353;
}
lean_ctor_set(x_361, 0, x_354);
lean_ctor_set(x_361, 1, x_355);
lean_ctor_set(x_361, 2, x_356);
lean_ctor_set(x_361, 3, x_357);
lean_ctor_set_uint8(x_361, sizeof(void*)*4, x_359);
x_362 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_362, 0, x_360);
lean_ctor_set(x_362, 1, x_351);
lean_ctor_set(x_362, 2, x_352);
lean_ctor_set(x_362, 3, x_361);
lean_ctor_set_uint8(x_362, sizeof(void*)*4, x_350);
return x_362;
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; uint8_t x_366; lean_object* x_367; lean_object* x_368; 
x_363 = lean_ctor_get(x_340, 1);
lean_inc(x_363);
x_364 = lean_ctor_get(x_340, 2);
lean_inc(x_364);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 lean_ctor_release(x_340, 2);
 lean_ctor_release(x_340, 3);
 x_365 = x_340;
} else {
 lean_dec_ref(x_340);
 x_365 = lean_box(0);
}
x_366 = 0;
if (lean_is_scalar(x_365)) {
 x_367 = lean_alloc_ctor(1, 4, 1);
} else {
 x_367 = x_365;
}
lean_ctor_set(x_367, 0, x_341);
lean_ctor_set(x_367, 1, x_363);
lean_ctor_set(x_367, 2, x_364);
lean_ctor_set(x_367, 3, x_342);
lean_ctor_set_uint8(x_367, sizeof(void*)*4, x_366);
x_368 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_368, 0, x_326);
lean_ctor_set(x_368, 1, x_327);
lean_ctor_set(x_368, 2, x_328);
lean_ctor_set(x_368, 3, x_367);
lean_ctor_set_uint8(x_368, sizeof(void*)*4, x_350);
return x_368;
}
}
}
else
{
uint8_t x_369; 
x_369 = lean_ctor_get_uint8(x_341, sizeof(void*)*4);
if (x_369 == 0)
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; uint8_t x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_370 = lean_ctor_get(x_340, 1);
lean_inc(x_370);
x_371 = lean_ctor_get(x_340, 2);
lean_inc(x_371);
x_372 = lean_ctor_get(x_340, 3);
lean_inc(x_372);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 lean_ctor_release(x_340, 2);
 lean_ctor_release(x_340, 3);
 x_373 = x_340;
} else {
 lean_dec_ref(x_340);
 x_373 = lean_box(0);
}
x_374 = lean_ctor_get(x_341, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_341, 1);
lean_inc(x_375);
x_376 = lean_ctor_get(x_341, 2);
lean_inc(x_376);
x_377 = lean_ctor_get(x_341, 3);
lean_inc(x_377);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 lean_ctor_release(x_341, 2);
 lean_ctor_release(x_341, 3);
 x_378 = x_341;
} else {
 lean_dec_ref(x_341);
 x_378 = lean_box(0);
}
x_379 = 1;
if (lean_is_scalar(x_378)) {
 x_380 = lean_alloc_ctor(1, 4, 1);
} else {
 x_380 = x_378;
}
lean_ctor_set(x_380, 0, x_326);
lean_ctor_set(x_380, 1, x_327);
lean_ctor_set(x_380, 2, x_328);
lean_ctor_set(x_380, 3, x_374);
lean_ctor_set_uint8(x_380, sizeof(void*)*4, x_379);
if (lean_is_scalar(x_373)) {
 x_381 = lean_alloc_ctor(1, 4, 1);
} else {
 x_381 = x_373;
}
lean_ctor_set(x_381, 0, x_377);
lean_ctor_set(x_381, 1, x_370);
lean_ctor_set(x_381, 2, x_371);
lean_ctor_set(x_381, 3, x_372);
lean_ctor_set_uint8(x_381, sizeof(void*)*4, x_379);
x_382 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_382, 0, x_380);
lean_ctor_set(x_382, 1, x_375);
lean_ctor_set(x_382, 2, x_376);
lean_ctor_set(x_382, 3, x_381);
lean_ctor_set_uint8(x_382, sizeof(void*)*4, x_369);
return x_382;
}
else
{
lean_object* x_383; 
x_383 = lean_ctor_get(x_340, 3);
lean_inc(x_383);
if (lean_obj_tag(x_383) == 0)
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; uint8_t x_387; lean_object* x_388; lean_object* x_389; 
x_384 = lean_ctor_get(x_340, 1);
lean_inc(x_384);
x_385 = lean_ctor_get(x_340, 2);
lean_inc(x_385);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 lean_ctor_release(x_340, 2);
 lean_ctor_release(x_340, 3);
 x_386 = x_340;
} else {
 lean_dec_ref(x_340);
 x_386 = lean_box(0);
}
x_387 = 0;
if (lean_is_scalar(x_386)) {
 x_388 = lean_alloc_ctor(1, 4, 1);
} else {
 x_388 = x_386;
}
lean_ctor_set(x_388, 0, x_341);
lean_ctor_set(x_388, 1, x_384);
lean_ctor_set(x_388, 2, x_385);
lean_ctor_set(x_388, 3, x_383);
lean_ctor_set_uint8(x_388, sizeof(void*)*4, x_387);
x_389 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_389, 0, x_326);
lean_ctor_set(x_389, 1, x_327);
lean_ctor_set(x_389, 2, x_328);
lean_ctor_set(x_389, 3, x_388);
lean_ctor_set_uint8(x_389, sizeof(void*)*4, x_369);
return x_389;
}
else
{
uint8_t x_390; 
x_390 = lean_ctor_get_uint8(x_383, sizeof(void*)*4);
if (x_390 == 0)
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_391 = lean_ctor_get(x_340, 1);
lean_inc(x_391);
x_392 = lean_ctor_get(x_340, 2);
lean_inc(x_392);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 lean_ctor_release(x_340, 2);
 lean_ctor_release(x_340, 3);
 x_393 = x_340;
} else {
 lean_dec_ref(x_340);
 x_393 = lean_box(0);
}
x_394 = lean_ctor_get(x_383, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_383, 1);
lean_inc(x_395);
x_396 = lean_ctor_get(x_383, 2);
lean_inc(x_396);
x_397 = lean_ctor_get(x_383, 3);
lean_inc(x_397);
if (lean_is_exclusive(x_383)) {
 lean_ctor_release(x_383, 0);
 lean_ctor_release(x_383, 1);
 lean_ctor_release(x_383, 2);
 lean_ctor_release(x_383, 3);
 x_398 = x_383;
} else {
 lean_dec_ref(x_383);
 x_398 = lean_box(0);
}
lean_inc(x_341);
if (lean_is_scalar(x_398)) {
 x_399 = lean_alloc_ctor(1, 4, 1);
} else {
 x_399 = x_398;
}
lean_ctor_set(x_399, 0, x_326);
lean_ctor_set(x_399, 1, x_327);
lean_ctor_set(x_399, 2, x_328);
lean_ctor_set(x_399, 3, x_341);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 lean_ctor_release(x_341, 2);
 lean_ctor_release(x_341, 3);
 x_400 = x_341;
} else {
 lean_dec_ref(x_341);
 x_400 = lean_box(0);
}
lean_ctor_set_uint8(x_399, sizeof(void*)*4, x_369);
if (lean_is_scalar(x_400)) {
 x_401 = lean_alloc_ctor(1, 4, 1);
} else {
 x_401 = x_400;
}
lean_ctor_set(x_401, 0, x_394);
lean_ctor_set(x_401, 1, x_395);
lean_ctor_set(x_401, 2, x_396);
lean_ctor_set(x_401, 3, x_397);
lean_ctor_set_uint8(x_401, sizeof(void*)*4, x_369);
if (lean_is_scalar(x_393)) {
 x_402 = lean_alloc_ctor(1, 4, 1);
} else {
 x_402 = x_393;
}
lean_ctor_set(x_402, 0, x_399);
lean_ctor_set(x_402, 1, x_391);
lean_ctor_set(x_402, 2, x_392);
lean_ctor_set(x_402, 3, x_401);
lean_ctor_set_uint8(x_402, sizeof(void*)*4, x_390);
return x_402;
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; uint8_t x_412; lean_object* x_413; lean_object* x_414; 
x_403 = lean_ctor_get(x_340, 1);
lean_inc(x_403);
x_404 = lean_ctor_get(x_340, 2);
lean_inc(x_404);
if (lean_is_exclusive(x_340)) {
 lean_ctor_release(x_340, 0);
 lean_ctor_release(x_340, 1);
 lean_ctor_release(x_340, 2);
 lean_ctor_release(x_340, 3);
 x_405 = x_340;
} else {
 lean_dec_ref(x_340);
 x_405 = lean_box(0);
}
x_406 = lean_ctor_get(x_341, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_341, 1);
lean_inc(x_407);
x_408 = lean_ctor_get(x_341, 2);
lean_inc(x_408);
x_409 = lean_ctor_get(x_341, 3);
lean_inc(x_409);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 lean_ctor_release(x_341, 2);
 lean_ctor_release(x_341, 3);
 x_410 = x_341;
} else {
 lean_dec_ref(x_341);
 x_410 = lean_box(0);
}
if (lean_is_scalar(x_410)) {
 x_411 = lean_alloc_ctor(1, 4, 1);
} else {
 x_411 = x_410;
}
lean_ctor_set(x_411, 0, x_406);
lean_ctor_set(x_411, 1, x_407);
lean_ctor_set(x_411, 2, x_408);
lean_ctor_set(x_411, 3, x_409);
lean_ctor_set_uint8(x_411, sizeof(void*)*4, x_390);
x_412 = 0;
if (lean_is_scalar(x_405)) {
 x_413 = lean_alloc_ctor(1, 4, 1);
} else {
 x_413 = x_405;
}
lean_ctor_set(x_413, 0, x_411);
lean_ctor_set(x_413, 1, x_403);
lean_ctor_set(x_413, 2, x_404);
lean_ctor_set(x_413, 3, x_383);
lean_ctor_set_uint8(x_413, sizeof(void*)*4, x_412);
x_414 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_414, 0, x_326);
lean_ctor_set(x_414, 1, x_327);
lean_ctor_set(x_414, 2, x_328);
lean_ctor_set(x_414, 3, x_413);
lean_ctor_set_uint8(x_414, sizeof(void*)*4, x_390);
return x_414;
}
}
}
}
}
}
}
else
{
uint8_t x_415; uint8_t x_416; 
x_415 = l_RBNode_isRed___rarg(x_326);
x_416 = l_Bool_DecidableEq(x_415, x_331);
if (x_416 == 0)
{
lean_object* x_417; lean_object* x_418; 
x_417 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_326, x_2, x_3);
x_418 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_418, 0, x_417);
lean_ctor_set(x_418, 1, x_327);
lean_ctor_set(x_418, 2, x_328);
lean_ctor_set(x_418, 3, x_329);
lean_ctor_set_uint8(x_418, sizeof(void*)*4, x_6);
return x_418;
}
else
{
lean_object* x_419; lean_object* x_420; 
x_419 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_326, x_2, x_3);
x_420 = lean_ctor_get(x_419, 0);
lean_inc(x_420);
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_421; 
x_421 = lean_ctor_get(x_419, 3);
lean_inc(x_421);
if (lean_obj_tag(x_421) == 0)
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; uint8_t x_425; lean_object* x_426; uint8_t x_427; lean_object* x_428; 
x_422 = lean_ctor_get(x_419, 1);
lean_inc(x_422);
x_423 = lean_ctor_get(x_419, 2);
lean_inc(x_423);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 lean_ctor_release(x_419, 2);
 lean_ctor_release(x_419, 3);
 x_424 = x_419;
} else {
 lean_dec_ref(x_419);
 x_424 = lean_box(0);
}
x_425 = 0;
if (lean_is_scalar(x_424)) {
 x_426 = lean_alloc_ctor(1, 4, 1);
} else {
 x_426 = x_424;
}
lean_ctor_set(x_426, 0, x_421);
lean_ctor_set(x_426, 1, x_422);
lean_ctor_set(x_426, 2, x_423);
lean_ctor_set(x_426, 3, x_421);
lean_ctor_set_uint8(x_426, sizeof(void*)*4, x_425);
x_427 = 1;
x_428 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_428, 0, x_426);
lean_ctor_set(x_428, 1, x_327);
lean_ctor_set(x_428, 2, x_328);
lean_ctor_set(x_428, 3, x_329);
lean_ctor_set_uint8(x_428, sizeof(void*)*4, x_427);
return x_428;
}
else
{
uint8_t x_429; 
x_429 = lean_ctor_get_uint8(x_421, sizeof(void*)*4);
if (x_429 == 0)
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; uint8_t x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
x_430 = lean_ctor_get(x_419, 1);
lean_inc(x_430);
x_431 = lean_ctor_get(x_419, 2);
lean_inc(x_431);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 lean_ctor_release(x_419, 2);
 lean_ctor_release(x_419, 3);
 x_432 = x_419;
} else {
 lean_dec_ref(x_419);
 x_432 = lean_box(0);
}
x_433 = lean_ctor_get(x_421, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_421, 1);
lean_inc(x_434);
x_435 = lean_ctor_get(x_421, 2);
lean_inc(x_435);
x_436 = lean_ctor_get(x_421, 3);
lean_inc(x_436);
if (lean_is_exclusive(x_421)) {
 lean_ctor_release(x_421, 0);
 lean_ctor_release(x_421, 1);
 lean_ctor_release(x_421, 2);
 lean_ctor_release(x_421, 3);
 x_437 = x_421;
} else {
 lean_dec_ref(x_421);
 x_437 = lean_box(0);
}
x_438 = 1;
if (lean_is_scalar(x_437)) {
 x_439 = lean_alloc_ctor(1, 4, 1);
} else {
 x_439 = x_437;
}
lean_ctor_set(x_439, 0, x_420);
lean_ctor_set(x_439, 1, x_430);
lean_ctor_set(x_439, 2, x_431);
lean_ctor_set(x_439, 3, x_433);
lean_ctor_set_uint8(x_439, sizeof(void*)*4, x_438);
if (lean_is_scalar(x_432)) {
 x_440 = lean_alloc_ctor(1, 4, 1);
} else {
 x_440 = x_432;
}
lean_ctor_set(x_440, 0, x_436);
lean_ctor_set(x_440, 1, x_327);
lean_ctor_set(x_440, 2, x_328);
lean_ctor_set(x_440, 3, x_329);
lean_ctor_set_uint8(x_440, sizeof(void*)*4, x_438);
x_441 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_441, 0, x_439);
lean_ctor_set(x_441, 1, x_434);
lean_ctor_set(x_441, 2, x_435);
lean_ctor_set(x_441, 3, x_440);
lean_ctor_set_uint8(x_441, sizeof(void*)*4, x_429);
return x_441;
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; uint8_t x_445; lean_object* x_446; lean_object* x_447; 
x_442 = lean_ctor_get(x_419, 1);
lean_inc(x_442);
x_443 = lean_ctor_get(x_419, 2);
lean_inc(x_443);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 lean_ctor_release(x_419, 2);
 lean_ctor_release(x_419, 3);
 x_444 = x_419;
} else {
 lean_dec_ref(x_419);
 x_444 = lean_box(0);
}
x_445 = 0;
if (lean_is_scalar(x_444)) {
 x_446 = lean_alloc_ctor(1, 4, 1);
} else {
 x_446 = x_444;
}
lean_ctor_set(x_446, 0, x_420);
lean_ctor_set(x_446, 1, x_442);
lean_ctor_set(x_446, 2, x_443);
lean_ctor_set(x_446, 3, x_421);
lean_ctor_set_uint8(x_446, sizeof(void*)*4, x_445);
x_447 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_447, 0, x_446);
lean_ctor_set(x_447, 1, x_327);
lean_ctor_set(x_447, 2, x_328);
lean_ctor_set(x_447, 3, x_329);
lean_ctor_set_uint8(x_447, sizeof(void*)*4, x_429);
return x_447;
}
}
}
else
{
uint8_t x_448; 
x_448 = lean_ctor_get_uint8(x_420, sizeof(void*)*4);
if (x_448 == 0)
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; uint8_t x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; 
x_449 = lean_ctor_get(x_419, 1);
lean_inc(x_449);
x_450 = lean_ctor_get(x_419, 2);
lean_inc(x_450);
x_451 = lean_ctor_get(x_419, 3);
lean_inc(x_451);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 lean_ctor_release(x_419, 2);
 lean_ctor_release(x_419, 3);
 x_452 = x_419;
} else {
 lean_dec_ref(x_419);
 x_452 = lean_box(0);
}
x_453 = lean_ctor_get(x_420, 0);
lean_inc(x_453);
x_454 = lean_ctor_get(x_420, 1);
lean_inc(x_454);
x_455 = lean_ctor_get(x_420, 2);
lean_inc(x_455);
x_456 = lean_ctor_get(x_420, 3);
lean_inc(x_456);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 lean_ctor_release(x_420, 2);
 lean_ctor_release(x_420, 3);
 x_457 = x_420;
} else {
 lean_dec_ref(x_420);
 x_457 = lean_box(0);
}
x_458 = 1;
if (lean_is_scalar(x_457)) {
 x_459 = lean_alloc_ctor(1, 4, 1);
} else {
 x_459 = x_457;
}
lean_ctor_set(x_459, 0, x_453);
lean_ctor_set(x_459, 1, x_454);
lean_ctor_set(x_459, 2, x_455);
lean_ctor_set(x_459, 3, x_456);
lean_ctor_set_uint8(x_459, sizeof(void*)*4, x_458);
if (lean_is_scalar(x_452)) {
 x_460 = lean_alloc_ctor(1, 4, 1);
} else {
 x_460 = x_452;
}
lean_ctor_set(x_460, 0, x_451);
lean_ctor_set(x_460, 1, x_327);
lean_ctor_set(x_460, 2, x_328);
lean_ctor_set(x_460, 3, x_329);
lean_ctor_set_uint8(x_460, sizeof(void*)*4, x_458);
x_461 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_461, 0, x_459);
lean_ctor_set(x_461, 1, x_449);
lean_ctor_set(x_461, 2, x_450);
lean_ctor_set(x_461, 3, x_460);
lean_ctor_set_uint8(x_461, sizeof(void*)*4, x_448);
return x_461;
}
else
{
lean_object* x_462; 
x_462 = lean_ctor_get(x_419, 3);
lean_inc(x_462);
if (lean_obj_tag(x_462) == 0)
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; uint8_t x_466; lean_object* x_467; lean_object* x_468; 
x_463 = lean_ctor_get(x_419, 1);
lean_inc(x_463);
x_464 = lean_ctor_get(x_419, 2);
lean_inc(x_464);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 lean_ctor_release(x_419, 2);
 lean_ctor_release(x_419, 3);
 x_465 = x_419;
} else {
 lean_dec_ref(x_419);
 x_465 = lean_box(0);
}
x_466 = 0;
if (lean_is_scalar(x_465)) {
 x_467 = lean_alloc_ctor(1, 4, 1);
} else {
 x_467 = x_465;
}
lean_ctor_set(x_467, 0, x_420);
lean_ctor_set(x_467, 1, x_463);
lean_ctor_set(x_467, 2, x_464);
lean_ctor_set(x_467, 3, x_462);
lean_ctor_set_uint8(x_467, sizeof(void*)*4, x_466);
x_468 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_468, 0, x_467);
lean_ctor_set(x_468, 1, x_327);
lean_ctor_set(x_468, 2, x_328);
lean_ctor_set(x_468, 3, x_329);
lean_ctor_set_uint8(x_468, sizeof(void*)*4, x_448);
return x_468;
}
else
{
uint8_t x_469; 
x_469 = lean_ctor_get_uint8(x_462, sizeof(void*)*4);
if (x_469 == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_470 = lean_ctor_get(x_419, 1);
lean_inc(x_470);
x_471 = lean_ctor_get(x_419, 2);
lean_inc(x_471);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 lean_ctor_release(x_419, 2);
 lean_ctor_release(x_419, 3);
 x_472 = x_419;
} else {
 lean_dec_ref(x_419);
 x_472 = lean_box(0);
}
x_473 = lean_ctor_get(x_462, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_462, 1);
lean_inc(x_474);
x_475 = lean_ctor_get(x_462, 2);
lean_inc(x_475);
x_476 = lean_ctor_get(x_462, 3);
lean_inc(x_476);
if (lean_is_exclusive(x_462)) {
 lean_ctor_release(x_462, 0);
 lean_ctor_release(x_462, 1);
 lean_ctor_release(x_462, 2);
 lean_ctor_release(x_462, 3);
 x_477 = x_462;
} else {
 lean_dec_ref(x_462);
 x_477 = lean_box(0);
}
lean_inc(x_420);
if (lean_is_scalar(x_477)) {
 x_478 = lean_alloc_ctor(1, 4, 1);
} else {
 x_478 = x_477;
}
lean_ctor_set(x_478, 0, x_420);
lean_ctor_set(x_478, 1, x_470);
lean_ctor_set(x_478, 2, x_471);
lean_ctor_set(x_478, 3, x_473);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 lean_ctor_release(x_420, 2);
 lean_ctor_release(x_420, 3);
 x_479 = x_420;
} else {
 lean_dec_ref(x_420);
 x_479 = lean_box(0);
}
lean_ctor_set_uint8(x_478, sizeof(void*)*4, x_448);
if (lean_is_scalar(x_479)) {
 x_480 = lean_alloc_ctor(1, 4, 1);
} else {
 x_480 = x_479;
}
lean_ctor_set(x_480, 0, x_476);
lean_ctor_set(x_480, 1, x_327);
lean_ctor_set(x_480, 2, x_328);
lean_ctor_set(x_480, 3, x_329);
lean_ctor_set_uint8(x_480, sizeof(void*)*4, x_448);
if (lean_is_scalar(x_472)) {
 x_481 = lean_alloc_ctor(1, 4, 1);
} else {
 x_481 = x_472;
}
lean_ctor_set(x_481, 0, x_478);
lean_ctor_set(x_481, 1, x_474);
lean_ctor_set(x_481, 2, x_475);
lean_ctor_set(x_481, 3, x_480);
lean_ctor_set_uint8(x_481, sizeof(void*)*4, x_469);
return x_481;
}
else
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; uint8_t x_491; lean_object* x_492; lean_object* x_493; 
x_482 = lean_ctor_get(x_419, 1);
lean_inc(x_482);
x_483 = lean_ctor_get(x_419, 2);
lean_inc(x_483);
if (lean_is_exclusive(x_419)) {
 lean_ctor_release(x_419, 0);
 lean_ctor_release(x_419, 1);
 lean_ctor_release(x_419, 2);
 lean_ctor_release(x_419, 3);
 x_484 = x_419;
} else {
 lean_dec_ref(x_419);
 x_484 = lean_box(0);
}
x_485 = lean_ctor_get(x_420, 0);
lean_inc(x_485);
x_486 = lean_ctor_get(x_420, 1);
lean_inc(x_486);
x_487 = lean_ctor_get(x_420, 2);
lean_inc(x_487);
x_488 = lean_ctor_get(x_420, 3);
lean_inc(x_488);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 lean_ctor_release(x_420, 2);
 lean_ctor_release(x_420, 3);
 x_489 = x_420;
} else {
 lean_dec_ref(x_420);
 x_489 = lean_box(0);
}
if (lean_is_scalar(x_489)) {
 x_490 = lean_alloc_ctor(1, 4, 1);
} else {
 x_490 = x_489;
}
lean_ctor_set(x_490, 0, x_485);
lean_ctor_set(x_490, 1, x_486);
lean_ctor_set(x_490, 2, x_487);
lean_ctor_set(x_490, 3, x_488);
lean_ctor_set_uint8(x_490, sizeof(void*)*4, x_469);
x_491 = 0;
if (lean_is_scalar(x_484)) {
 x_492 = lean_alloc_ctor(1, 4, 1);
} else {
 x_492 = x_484;
}
lean_ctor_set(x_492, 0, x_490);
lean_ctor_set(x_492, 1, x_482);
lean_ctor_set(x_492, 2, x_483);
lean_ctor_set(x_492, 3, x_462);
lean_ctor_set_uint8(x_492, sizeof(void*)*4, x_491);
x_493 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_493, 0, x_492);
lean_ctor_set(x_493, 1, x_327);
lean_ctor_set(x_493, 2, x_328);
lean_ctor_set(x_493, 3, x_329);
lean_ctor_set_uint8(x_493, sizeof(void*)*4, x_469);
return x_493;
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
uint8_t x_4; uint8_t x_5; uint8_t x_6; 
x_4 = l_RBNode_isRed___rarg(x_1);
x_5 = 1;
x_6 = l_Bool_DecidableEq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_1, x_2, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_1, x_2, x_3);
x_9 = l_RBNode_setBlack___rarg(x_8);
return x_9;
}
}
}
lean_object* l_Lean_IR_addVarRename(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; 
x_4 = lean_nat_dec_eq(x_2, x_3);
x_5 = 1;
x_6 = l_Bool_DecidableEq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = l_RBNode_insert___at_Lean_IR_addVarRename___spec__1(x_1, x_2, x_3);
return x_7;
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
uint8_t x_7; 
x_7 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
lean_dec(x_3);
x_11 = l_Lean_IR_addVarRename(x_1, x_9, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
else
{
uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; 
x_13 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_14 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
x_15 = l_Bool_DecidableEq(x_13, x_14);
x_16 = 1;
x_17 = l_Bool_DecidableEq(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = lean_box(0);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_ctor_get(x_3, 0);
lean_inc(x_20);
lean_dec(x_3);
x_21 = l_Lean_IR_addVarRename(x_1, x_19, x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
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
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_IR_addParamsRename___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
uint8_t x_7; 
x_7 = l_String_Iterator_extract___closed__1;
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_1);
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_iterateM_u2082Aux___main___at_Lean_IR_addParamsRename___spec__1(x_2, x_2, x_3, x_9, x_8);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = lean_box(0);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_1);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Array_iterateM_u2082Aux___main___at_Lean_IR_addParamsRename___spec__2(x_2, x_2, x_3, x_14, x_13);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_1);
x_16 = lean_box(0);
return x_16;
}
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
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_IR_addParamsRename___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_iterateM_u2082Aux___main___at_Lean_IR_addParamsRename___spec__2(x_1, x_2, x_3, x_4, x_5);
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
uint8_t l_Array_isEqv___at_Lean_IR_FnBody_alphaEqv___main___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 1);
lean_inc(x_7);
lean_dec(x_3);
x_8 = l_Lean_IR_CtorInfo_beq(x_4, x_6);
lean_dec(x_6);
lean_dec(x_4);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_9 = 0;
return x_9;
}
else
{
uint8_t x_10; 
x_10 = l_Lean_IR_FnBody_alphaEqv___main(x_1, x_5, x_7);
return x_10;
}
}
else
{
uint8_t x_11; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = 0;
return x_11;
}
}
else
{
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_12; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = 0;
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
lean_dec(x_3);
x_15 = l_Lean_IR_FnBody_alphaEqv___main(x_1, x_13, x_14);
return x_15;
}
}
}
}
uint8_t l_Array_isEqv___at_Lean_IR_FnBody_alphaEqv___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_alloc_closure((void*)(l_Array_isEqv___at_Lean_IR_FnBody_alphaEqv___main___spec__1___lambda__1___boxed), 3, 1);
lean_closure_set(x_4, 0, x_1);
x_5 = lean_array_get_size(x_2);
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_eq(x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = 0;
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l_Array_isEqvAux___main___rarg(x_2, x_3, lean_box(0), x_4, x_9);
return x_10;
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
lean_inc(x_1);
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
lean_object* x_103; lean_object* x_104; uint8_t x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; uint8_t x_111; lean_object* x_112; uint8_t x_113; 
x_103 = lean_ctor_get(x_2, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_2, 1);
lean_inc(x_104);
x_105 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_106 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_107 = lean_ctor_get(x_2, 2);
lean_inc(x_107);
lean_dec(x_2);
x_108 = lean_ctor_get(x_3, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_3, 1);
lean_inc(x_109);
x_110 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_111 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_112 = lean_ctor_get(x_3, 2);
lean_inc(x_112);
lean_dec(x_3);
x_113 = l_Lean_IR_VarId_alphaEqv(x_1, x_103, x_108);
lean_dec(x_108);
lean_dec(x_103);
if (x_113 == 0)
{
uint8_t x_114; 
lean_dec(x_112);
lean_dec(x_109);
lean_dec(x_107);
lean_dec(x_104);
lean_dec(x_1);
x_114 = 0;
return x_114;
}
else
{
uint8_t x_115; 
x_115 = lean_nat_dec_eq(x_104, x_109);
lean_dec(x_109);
lean_dec(x_104);
if (x_115 == 0)
{
uint8_t x_116; 
lean_dec(x_112);
lean_dec(x_107);
lean_dec(x_1);
x_116 = 0;
return x_116;
}
else
{
uint8_t x_117; 
x_117 = l_Bool_DecidableEq(x_105, x_110);
if (x_117 == 0)
{
uint8_t x_118; 
lean_dec(x_112);
lean_dec(x_107);
lean_dec(x_1);
x_118 = 0;
return x_118;
}
else
{
uint8_t x_119; 
x_119 = l_Bool_DecidableEq(x_106, x_111);
if (x_119 == 0)
{
uint8_t x_120; 
lean_dec(x_112);
lean_dec(x_107);
lean_dec(x_1);
x_120 = 0;
return x_120;
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
uint8_t x_122; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_122 = 0;
return x_122;
}
}
case 7:
{
if (lean_obj_tag(x_3) == 7)
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; uint8_t x_131; lean_object* x_132; uint8_t x_133; 
x_123 = lean_ctor_get(x_2, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_2, 1);
lean_inc(x_124);
x_125 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_126 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_127 = lean_ctor_get(x_2, 2);
lean_inc(x_127);
lean_dec(x_2);
x_128 = lean_ctor_get(x_3, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_3, 1);
lean_inc(x_129);
x_130 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_131 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
x_132 = lean_ctor_get(x_3, 2);
lean_inc(x_132);
lean_dec(x_3);
x_133 = l_Lean_IR_VarId_alphaEqv(x_1, x_123, x_128);
lean_dec(x_128);
lean_dec(x_123);
if (x_133 == 0)
{
uint8_t x_134; 
lean_dec(x_132);
lean_dec(x_129);
lean_dec(x_127);
lean_dec(x_124);
lean_dec(x_1);
x_134 = 0;
return x_134;
}
else
{
uint8_t x_135; 
x_135 = lean_nat_dec_eq(x_124, x_129);
lean_dec(x_129);
lean_dec(x_124);
if (x_135 == 0)
{
uint8_t x_136; 
lean_dec(x_132);
lean_dec(x_127);
lean_dec(x_1);
x_136 = 0;
return x_136;
}
else
{
uint8_t x_137; 
x_137 = l_Bool_DecidableEq(x_125, x_130);
if (x_137 == 0)
{
uint8_t x_138; 
lean_dec(x_132);
lean_dec(x_127);
lean_dec(x_1);
x_138 = 0;
return x_138;
}
else
{
uint8_t x_139; 
x_139 = l_Bool_DecidableEq(x_126, x_131);
if (x_139 == 0)
{
uint8_t x_140; 
lean_dec(x_132);
lean_dec(x_127);
lean_dec(x_1);
x_140 = 0;
return x_140;
}
else
{
x_2 = x_127;
x_3 = x_132;
goto _start;
}
}
}
}
}
else
{
uint8_t x_142; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_142 = 0;
return x_142;
}
}
case 8:
{
if (lean_obj_tag(x_3) == 8)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_143 = lean_ctor_get(x_2, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_2, 1);
lean_inc(x_144);
lean_dec(x_2);
x_145 = lean_ctor_get(x_3, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_3, 1);
lean_inc(x_146);
lean_dec(x_3);
x_147 = l_Lean_IR_VarId_alphaEqv(x_1, x_143, x_145);
lean_dec(x_145);
lean_dec(x_143);
if (x_147 == 0)
{
uint8_t x_148; 
lean_dec(x_146);
lean_dec(x_144);
lean_dec(x_1);
x_148 = 0;
return x_148;
}
else
{
x_2 = x_144;
x_3 = x_146;
goto _start;
}
}
else
{
uint8_t x_150; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_150 = 0;
return x_150;
}
}
case 9:
{
if (lean_obj_tag(x_3) == 9)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_151 = lean_ctor_get(x_2, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_2, 1);
lean_inc(x_152);
lean_dec(x_2);
x_153 = lean_ctor_get(x_3, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_3, 1);
lean_inc(x_154);
lean_dec(x_3);
x_155 = l_Lean_KVMap_eqv(x_151, x_153);
lean_dec(x_153);
lean_dec(x_151);
if (x_155 == 0)
{
uint8_t x_156; 
lean_dec(x_154);
lean_dec(x_152);
lean_dec(x_1);
x_156 = 0;
return x_156;
}
else
{
x_2 = x_152;
x_3 = x_154;
goto _start;
}
}
else
{
uint8_t x_158; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_158 = 0;
return x_158;
}
}
case 10:
{
if (lean_obj_tag(x_3) == 10)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_159 = lean_ctor_get(x_2, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_2, 1);
lean_inc(x_160);
x_161 = lean_ctor_get(x_2, 3);
lean_inc(x_161);
lean_dec(x_2);
x_162 = lean_ctor_get(x_3, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_3, 1);
lean_inc(x_163);
x_164 = lean_ctor_get(x_3, 3);
lean_inc(x_164);
lean_dec(x_3);
x_165 = lean_name_eq(x_159, x_162);
lean_dec(x_162);
lean_dec(x_159);
if (x_165 == 0)
{
uint8_t x_166; 
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_1);
x_166 = 0;
return x_166;
}
else
{
uint8_t x_167; 
x_167 = l_Lean_IR_VarId_alphaEqv(x_1, x_160, x_163);
lean_dec(x_163);
lean_dec(x_160);
if (x_167 == 0)
{
uint8_t x_168; 
lean_dec(x_164);
lean_dec(x_161);
lean_dec(x_1);
x_168 = 0;
return x_168;
}
else
{
uint8_t x_169; 
x_169 = l_Array_isEqv___at_Lean_IR_FnBody_alphaEqv___main___spec__1(x_1, x_161, x_164);
lean_dec(x_164);
lean_dec(x_161);
return x_169;
}
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
case 11:
{
if (lean_obj_tag(x_3) == 11)
{
lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_171 = lean_ctor_get(x_2, 0);
lean_inc(x_171);
lean_dec(x_2);
x_172 = lean_ctor_get(x_3, 0);
lean_inc(x_172);
lean_dec(x_3);
x_173 = l_Lean_IR_Arg_alphaEqv(x_1, x_171, x_172);
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_1);
return x_173;
}
else
{
uint8_t x_174; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_174 = 0;
return x_174;
}
}
case 12:
{
if (lean_obj_tag(x_3) == 12)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_175 = lean_ctor_get(x_2, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_2, 1);
lean_inc(x_176);
lean_dec(x_2);
x_177 = lean_ctor_get(x_3, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_3, 1);
lean_inc(x_178);
lean_dec(x_3);
x_179 = lean_nat_dec_eq(x_175, x_177);
lean_dec(x_177);
lean_dec(x_175);
if (x_179 == 0)
{
uint8_t x_180; 
lean_dec(x_178);
lean_dec(x_176);
lean_dec(x_1);
x_180 = 0;
return x_180;
}
else
{
uint8_t x_181; 
x_181 = l_Array_isEqv___at_Lean_IR_args_alphaEqv___spec__1(x_1, x_176, x_178);
lean_dec(x_178);
lean_dec(x_176);
return x_181;
}
}
else
{
uint8_t x_182; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_182 = 0;
return x_182;
}
}
default: 
{
lean_dec(x_1);
if (lean_obj_tag(x_3) == 13)
{
uint8_t x_183; 
x_183 = 1;
return x_183;
}
else
{
uint8_t x_184; 
lean_dec(x_3);
x_184 = 0;
return x_184;
}
}
}
}
}
lean_object* l_Array_isEqv___at_Lean_IR_FnBody_alphaEqv___main___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_isEqv___at_Lean_IR_FnBody_alphaEqv___main___spec__1___lambda__1(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
lean_object* l_Array_isEqv___at_Lean_IR_FnBody_alphaEqv___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_isEqv___at_Lean_IR_FnBody_alphaEqv___main___spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
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
lean_object* _init_l_Lean_IR_mkIf___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
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
x_8 = l_Lean_IR_mkIf___closed__7;
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
lean_object* initialize_Init_Lean_Name(lean_object*);
lean_object* initialize_Init_Lean_KVMap(lean_object*);
lean_object* initialize_Init_Lean_Format(lean_object*);
lean_object* initialize_Init_Lean_Compiler_ExternAttr(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Compiler_IR_Basic(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Name(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_KVMap(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Format(lean_io_mk_world());
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
l_Array_isEqv___at_Lean_IR_IRType_beq___main___spec__1___closed__1 = _init_l_Array_isEqv___at_Lean_IR_IRType_beq___main___spec__1___closed__1();
lean_mark_persistent(l_Array_isEqv___at_Lean_IR_IRType_beq___main___spec__1___closed__1);
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
l_Lean_IR_mkIf___closed__7 = _init_l_Lean_IR_mkIf___closed__7();
lean_mark_persistent(l_Lean_IR_mkIf___closed__7);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
