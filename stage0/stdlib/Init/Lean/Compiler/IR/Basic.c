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
uint8_t l_coeDecidableEq(uint8_t);
lean_object* l_Lean_IR_VarId_hasAeqv;
lean_object* lean_ir_mk_app_expr(lean_object*, lean_object*);
lean_object* l_Lean_IR_Expr_hasAeqv;
lean_object* l_Lean_IR_AltCore_mmodifyBody___rarg___closed__1;
lean_object* l_RBNode_insert___at_Lean_IR_LocalContext_addLocal___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_mmodifyJPs___spec__1___boxed(lean_object*);
lean_object* l_Lean_IR_mkIf___closed__4;
lean_object* lean_ir_mk_proj_expr(lean_object*, lean_object*);
lean_object* l_Lean_IR_Alt_ctor(lean_object*, lean_object*);
extern uint8_t l_String_posOfAux___main___closed__2;
lean_object* l_Lean_IR_FnBody_HasBeq___closed__1;
lean_object* l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(lean_object*, lean_object*, lean_object*);
extern uint8_t l_String_posOfAux___main___closed__1;
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
lean_object* l_Array_iterateM_u2082Aux___main___at_Lean_IR_addParamsRename___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t x_3; uint8_t x_4; 
x_3 = l_Lean_IR_FnBody_isTerminal(x_1);
x_4 = l_coeDecidableEq(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_IR_FnBody_body(x_1);
x_6 = l_Lean_IR_push(x_2, x_1);
x_1 = x_5;
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_1);
return x_8;
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
lean_object* x_4; uint8_t x_5; uint8_t x_6; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
x_6 = l_coeDecidableEq(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_15; uint8_t x_16; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_2, x_7);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = lean_nat_dec_lt(x_8, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_1);
lean_inc(x_8);
x_17 = l___private_Init_Data_Array_Basic_1__swapAtPanic_x21___at_Lean_IR_reshapeAux___main___spec__1(x_8);
x_9 = x_17;
goto block_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_array_fget(x_1, x_8);
x_19 = lean_box(13);
x_20 = lean_array_fset(x_1, x_8, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_9 = x_21;
goto block_14;
}
block_14:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_IR_FnBody_setBody(x_10, x_3);
x_1 = x_11;
x_2 = x_8;
x_3 = x_12;
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 3);
x_12 = lean_nat_dec_lt(x_2, x_9);
x_13 = l_coeDecidableEq(x_12);
if (x_13 == 0)
{
uint8_t x_14; uint8_t x_15; 
x_14 = lean_nat_dec_lt(x_9, x_2);
x_15 = l_coeDecidableEq(x_14);
if (x_15 == 0)
{
lean_dec(x_10);
lean_dec(x_9);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
lean_object* x_16; 
x_16 = l_RBNode_ins___main___at_Lean_IR_mkIndexSet___spec__2(x_11, x_2, x_3);
lean_ctor_set(x_1, 3, x_16);
return x_1;
}
}
else
{
lean_object* x_17; 
x_17 = l_RBNode_ins___main___at_Lean_IR_mkIndexSet___spec__2(x_8, x_2, x_3);
lean_ctor_set(x_1, 0, x_17);
return x_1;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_ctor_get(x_1, 2);
x_21 = lean_ctor_get(x_1, 3);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_1);
x_22 = lean_nat_dec_lt(x_2, x_19);
x_23 = l_coeDecidableEq(x_22);
if (x_23 == 0)
{
uint8_t x_24; uint8_t x_25; 
x_24 = lean_nat_dec_lt(x_19, x_2);
x_25 = l_coeDecidableEq(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_20);
lean_dec(x_19);
x_26 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_2);
lean_ctor_set(x_26, 2, x_3);
lean_ctor_set(x_26, 3, x_21);
lean_ctor_set_uint8(x_26, sizeof(void*)*4, x_6);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_RBNode_ins___main___at_Lean_IR_mkIndexSet___spec__2(x_21, x_2, x_3);
x_28 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_28, 0, x_18);
lean_ctor_set(x_28, 1, x_19);
lean_ctor_set(x_28, 2, x_20);
lean_ctor_set(x_28, 3, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*4, x_6);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_RBNode_ins___main___at_Lean_IR_mkIndexSet___spec__2(x_18, x_2, x_3);
x_30 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_19);
lean_ctor_set(x_30, 2, x_20);
lean_ctor_set(x_30, 3, x_21);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_6);
return x_30;
}
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_1);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; 
x_32 = lean_ctor_get(x_1, 0);
x_33 = lean_ctor_get(x_1, 1);
x_34 = lean_ctor_get(x_1, 2);
x_35 = lean_ctor_get(x_1, 3);
x_36 = lean_nat_dec_lt(x_2, x_33);
x_37 = l_coeDecidableEq(x_36);
if (x_37 == 0)
{
uint8_t x_38; uint8_t x_39; 
x_38 = lean_nat_dec_lt(x_33, x_2);
x_39 = l_coeDecidableEq(x_38);
if (x_39 == 0)
{
lean_dec(x_34);
lean_dec(x_33);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
uint8_t x_40; uint8_t x_41; 
x_40 = l_RBNode_isRed___rarg(x_35);
x_41 = l_coeDecidableEq(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = l_RBNode_ins___main___at_Lean_IR_mkIndexSet___spec__2(x_35, x_2, x_3);
lean_ctor_set(x_1, 3, x_42);
return x_1;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = l_RBNode_ins___main___at_Lean_IR_mkIndexSet___spec__2(x_35, x_2, x_3);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_43, 3);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_43);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_43, 3);
lean_dec(x_47);
x_48 = lean_ctor_get(x_43, 0);
lean_dec(x_48);
x_49 = 0;
lean_ctor_set(x_43, 0, x_45);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_49);
x_50 = 1;
lean_ctor_set(x_1, 3, x_43);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_50);
return x_1;
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; uint8_t x_55; 
x_51 = lean_ctor_get(x_43, 1);
x_52 = lean_ctor_get(x_43, 2);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_43);
x_53 = 0;
x_54 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_54, 0, x_45);
lean_ctor_set(x_54, 1, x_51);
lean_ctor_set(x_54, 2, x_52);
lean_ctor_set(x_54, 3, x_45);
lean_ctor_set_uint8(x_54, sizeof(void*)*4, x_53);
x_55 = 1;
lean_ctor_set(x_1, 3, x_54);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_55);
return x_1;
}
}
else
{
uint8_t x_56; 
x_56 = lean_ctor_get_uint8(x_45, sizeof(void*)*4);
if (x_56 == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_43);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_58 = lean_ctor_get(x_43, 1);
x_59 = lean_ctor_get(x_43, 2);
x_60 = lean_ctor_get(x_43, 3);
lean_dec(x_60);
x_61 = lean_ctor_get(x_43, 0);
lean_dec(x_61);
x_62 = !lean_is_exclusive(x_45);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_63 = lean_ctor_get(x_45, 0);
x_64 = lean_ctor_get(x_45, 1);
x_65 = lean_ctor_get(x_45, 2);
x_66 = lean_ctor_get(x_45, 3);
x_67 = 1;
lean_ctor_set(x_45, 3, x_44);
lean_ctor_set(x_45, 2, x_34);
lean_ctor_set(x_45, 1, x_33);
lean_ctor_set(x_45, 0, x_32);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_67);
lean_ctor_set(x_43, 3, x_66);
lean_ctor_set(x_43, 2, x_65);
lean_ctor_set(x_43, 1, x_64);
lean_ctor_set(x_43, 0, x_63);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_67);
lean_ctor_set(x_1, 3, x_43);
lean_ctor_set(x_1, 2, x_59);
lean_ctor_set(x_1, 1, x_58);
lean_ctor_set(x_1, 0, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_56);
return x_1;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_45, 0);
x_69 = lean_ctor_get(x_45, 1);
x_70 = lean_ctor_get(x_45, 2);
x_71 = lean_ctor_get(x_45, 3);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_45);
x_72 = 1;
x_73 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_73, 0, x_32);
lean_ctor_set(x_73, 1, x_33);
lean_ctor_set(x_73, 2, x_34);
lean_ctor_set(x_73, 3, x_44);
lean_ctor_set_uint8(x_73, sizeof(void*)*4, x_72);
lean_ctor_set(x_43, 3, x_71);
lean_ctor_set(x_43, 2, x_70);
lean_ctor_set(x_43, 1, x_69);
lean_ctor_set(x_43, 0, x_68);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_72);
lean_ctor_set(x_1, 3, x_43);
lean_ctor_set(x_1, 2, x_59);
lean_ctor_set(x_1, 1, x_58);
lean_ctor_set(x_1, 0, x_73);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_56);
return x_1;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; 
x_74 = lean_ctor_get(x_43, 1);
x_75 = lean_ctor_get(x_43, 2);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_43);
x_76 = lean_ctor_get(x_45, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_45, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_45, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_45, 3);
lean_inc(x_79);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 lean_ctor_release(x_45, 2);
 lean_ctor_release(x_45, 3);
 x_80 = x_45;
} else {
 lean_dec_ref(x_45);
 x_80 = lean_box(0);
}
x_81 = 1;
if (lean_is_scalar(x_80)) {
 x_82 = lean_alloc_ctor(1, 4, 1);
} else {
 x_82 = x_80;
}
lean_ctor_set(x_82, 0, x_32);
lean_ctor_set(x_82, 1, x_33);
lean_ctor_set(x_82, 2, x_34);
lean_ctor_set(x_82, 3, x_44);
lean_ctor_set_uint8(x_82, sizeof(void*)*4, x_81);
x_83 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_83, 0, x_76);
lean_ctor_set(x_83, 1, x_77);
lean_ctor_set(x_83, 2, x_78);
lean_ctor_set(x_83, 3, x_79);
lean_ctor_set_uint8(x_83, sizeof(void*)*4, x_81);
lean_ctor_set(x_1, 3, x_83);
lean_ctor_set(x_1, 2, x_75);
lean_ctor_set(x_1, 1, x_74);
lean_ctor_set(x_1, 0, x_82);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_56);
return x_1;
}
}
else
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_43);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_43, 3);
lean_dec(x_85);
x_86 = lean_ctor_get(x_43, 0);
lean_dec(x_86);
x_87 = 0;
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_87);
lean_ctor_set(x_1, 3, x_43);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_56);
return x_1;
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_43, 1);
x_89 = lean_ctor_get(x_43, 2);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_43);
x_90 = 0;
x_91 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_91, 0, x_44);
lean_ctor_set(x_91, 1, x_88);
lean_ctor_set(x_91, 2, x_89);
lean_ctor_set(x_91, 3, x_45);
lean_ctor_set_uint8(x_91, sizeof(void*)*4, x_90);
lean_ctor_set(x_1, 3, x_91);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_56);
return x_1;
}
}
}
}
else
{
uint8_t x_92; 
x_92 = lean_ctor_get_uint8(x_44, sizeof(void*)*4);
if (x_92 == 0)
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_43);
if (x_93 == 0)
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_ctor_get(x_43, 0);
lean_dec(x_94);
x_95 = !lean_is_exclusive(x_44);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_96 = lean_ctor_get(x_44, 0);
x_97 = lean_ctor_get(x_44, 1);
x_98 = lean_ctor_get(x_44, 2);
x_99 = lean_ctor_get(x_44, 3);
x_100 = 1;
lean_ctor_set(x_44, 3, x_96);
lean_ctor_set(x_44, 2, x_34);
lean_ctor_set(x_44, 1, x_33);
lean_ctor_set(x_44, 0, x_32);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_100);
lean_ctor_set(x_43, 0, x_99);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_100);
lean_ctor_set(x_1, 3, x_43);
lean_ctor_set(x_1, 2, x_98);
lean_ctor_set(x_1, 1, x_97);
lean_ctor_set(x_1, 0, x_44);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_92);
return x_1;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; 
x_101 = lean_ctor_get(x_44, 0);
x_102 = lean_ctor_get(x_44, 1);
x_103 = lean_ctor_get(x_44, 2);
x_104 = lean_ctor_get(x_44, 3);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_44);
x_105 = 1;
x_106 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_106, 0, x_32);
lean_ctor_set(x_106, 1, x_33);
lean_ctor_set(x_106, 2, x_34);
lean_ctor_set(x_106, 3, x_101);
lean_ctor_set_uint8(x_106, sizeof(void*)*4, x_105);
lean_ctor_set(x_43, 0, x_104);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_105);
lean_ctor_set(x_1, 3, x_43);
lean_ctor_set(x_1, 2, x_103);
lean_ctor_set(x_1, 1, x_102);
lean_ctor_set(x_1, 0, x_106);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_92);
return x_1;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; 
x_107 = lean_ctor_get(x_43, 1);
x_108 = lean_ctor_get(x_43, 2);
x_109 = lean_ctor_get(x_43, 3);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_43);
x_110 = lean_ctor_get(x_44, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_44, 1);
lean_inc(x_111);
x_112 = lean_ctor_get(x_44, 2);
lean_inc(x_112);
x_113 = lean_ctor_get(x_44, 3);
lean_inc(x_113);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 lean_ctor_release(x_44, 3);
 x_114 = x_44;
} else {
 lean_dec_ref(x_44);
 x_114 = lean_box(0);
}
x_115 = 1;
if (lean_is_scalar(x_114)) {
 x_116 = lean_alloc_ctor(1, 4, 1);
} else {
 x_116 = x_114;
}
lean_ctor_set(x_116, 0, x_32);
lean_ctor_set(x_116, 1, x_33);
lean_ctor_set(x_116, 2, x_34);
lean_ctor_set(x_116, 3, x_110);
lean_ctor_set_uint8(x_116, sizeof(void*)*4, x_115);
x_117 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_117, 0, x_113);
lean_ctor_set(x_117, 1, x_107);
lean_ctor_set(x_117, 2, x_108);
lean_ctor_set(x_117, 3, x_109);
lean_ctor_set_uint8(x_117, sizeof(void*)*4, x_115);
lean_ctor_set(x_1, 3, x_117);
lean_ctor_set(x_1, 2, x_112);
lean_ctor_set(x_1, 1, x_111);
lean_ctor_set(x_1, 0, x_116);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_92);
return x_1;
}
}
else
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_43, 3);
lean_inc(x_118);
if (lean_obj_tag(x_118) == 0)
{
uint8_t x_119; 
x_119 = !lean_is_exclusive(x_43);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_120 = lean_ctor_get(x_43, 3);
lean_dec(x_120);
x_121 = lean_ctor_get(x_43, 0);
lean_dec(x_121);
x_122 = 0;
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_122);
lean_ctor_set(x_1, 3, x_43);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_92);
return x_1;
}
else
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_43, 1);
x_124 = lean_ctor_get(x_43, 2);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_43);
x_125 = 0;
x_126 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_126, 0, x_44);
lean_ctor_set(x_126, 1, x_123);
lean_ctor_set(x_126, 2, x_124);
lean_ctor_set(x_126, 3, x_118);
lean_ctor_set_uint8(x_126, sizeof(void*)*4, x_125);
lean_ctor_set(x_1, 3, x_126);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_92);
return x_1;
}
}
else
{
uint8_t x_127; 
x_127 = lean_ctor_get_uint8(x_118, sizeof(void*)*4);
if (x_127 == 0)
{
uint8_t x_128; 
lean_free_object(x_1);
x_128 = !lean_is_exclusive(x_43);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_129 = lean_ctor_get(x_43, 3);
lean_dec(x_129);
x_130 = lean_ctor_get(x_43, 0);
lean_dec(x_130);
x_131 = !lean_is_exclusive(x_118);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_132 = lean_ctor_get(x_118, 0);
x_133 = lean_ctor_get(x_118, 1);
x_134 = lean_ctor_get(x_118, 2);
x_135 = lean_ctor_get(x_118, 3);
lean_inc(x_44);
lean_ctor_set(x_118, 3, x_44);
lean_ctor_set(x_118, 2, x_34);
lean_ctor_set(x_118, 1, x_33);
lean_ctor_set(x_118, 0, x_32);
x_136 = !lean_is_exclusive(x_44);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_137 = lean_ctor_get(x_44, 3);
lean_dec(x_137);
x_138 = lean_ctor_get(x_44, 2);
lean_dec(x_138);
x_139 = lean_ctor_get(x_44, 1);
lean_dec(x_139);
x_140 = lean_ctor_get(x_44, 0);
lean_dec(x_140);
lean_ctor_set_uint8(x_118, sizeof(void*)*4, x_92);
lean_ctor_set(x_44, 3, x_135);
lean_ctor_set(x_44, 2, x_134);
lean_ctor_set(x_44, 1, x_133);
lean_ctor_set(x_44, 0, x_132);
lean_ctor_set(x_43, 3, x_44);
lean_ctor_set(x_43, 0, x_118);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_127);
return x_43;
}
else
{
lean_object* x_141; 
lean_dec(x_44);
lean_ctor_set_uint8(x_118, sizeof(void*)*4, x_92);
x_141 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_141, 0, x_132);
lean_ctor_set(x_141, 1, x_133);
lean_ctor_set(x_141, 2, x_134);
lean_ctor_set(x_141, 3, x_135);
lean_ctor_set_uint8(x_141, sizeof(void*)*4, x_92);
lean_ctor_set(x_43, 3, x_141);
lean_ctor_set(x_43, 0, x_118);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_127);
return x_43;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_142 = lean_ctor_get(x_118, 0);
x_143 = lean_ctor_get(x_118, 1);
x_144 = lean_ctor_get(x_118, 2);
x_145 = lean_ctor_get(x_118, 3);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_118);
lean_inc(x_44);
x_146 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_146, 0, x_32);
lean_ctor_set(x_146, 1, x_33);
lean_ctor_set(x_146, 2, x_34);
lean_ctor_set(x_146, 3, x_44);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 lean_ctor_release(x_44, 3);
 x_147 = x_44;
} else {
 lean_dec_ref(x_44);
 x_147 = lean_box(0);
}
lean_ctor_set_uint8(x_146, sizeof(void*)*4, x_92);
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 4, 1);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_142);
lean_ctor_set(x_148, 1, x_143);
lean_ctor_set(x_148, 2, x_144);
lean_ctor_set(x_148, 3, x_145);
lean_ctor_set_uint8(x_148, sizeof(void*)*4, x_92);
lean_ctor_set(x_43, 3, x_148);
lean_ctor_set(x_43, 0, x_146);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_127);
return x_43;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_149 = lean_ctor_get(x_43, 1);
x_150 = lean_ctor_get(x_43, 2);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_43);
x_151 = lean_ctor_get(x_118, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_118, 1);
lean_inc(x_152);
x_153 = lean_ctor_get(x_118, 2);
lean_inc(x_153);
x_154 = lean_ctor_get(x_118, 3);
lean_inc(x_154);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 lean_ctor_release(x_118, 2);
 lean_ctor_release(x_118, 3);
 x_155 = x_118;
} else {
 lean_dec_ref(x_118);
 x_155 = lean_box(0);
}
lean_inc(x_44);
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(1, 4, 1);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_32);
lean_ctor_set(x_156, 1, x_33);
lean_ctor_set(x_156, 2, x_34);
lean_ctor_set(x_156, 3, x_44);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 lean_ctor_release(x_44, 3);
 x_157 = x_44;
} else {
 lean_dec_ref(x_44);
 x_157 = lean_box(0);
}
lean_ctor_set_uint8(x_156, sizeof(void*)*4, x_92);
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 4, 1);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_151);
lean_ctor_set(x_158, 1, x_152);
lean_ctor_set(x_158, 2, x_153);
lean_ctor_set(x_158, 3, x_154);
lean_ctor_set_uint8(x_158, sizeof(void*)*4, x_92);
x_159 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_149);
lean_ctor_set(x_159, 2, x_150);
lean_ctor_set(x_159, 3, x_158);
lean_ctor_set_uint8(x_159, sizeof(void*)*4, x_127);
return x_159;
}
}
else
{
uint8_t x_160; 
x_160 = !lean_is_exclusive(x_43);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_161 = lean_ctor_get(x_43, 3);
lean_dec(x_161);
x_162 = lean_ctor_get(x_43, 0);
lean_dec(x_162);
x_163 = !lean_is_exclusive(x_44);
if (x_163 == 0)
{
uint8_t x_164; 
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_127);
x_164 = 0;
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_164);
lean_ctor_set(x_1, 3, x_43);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_127);
return x_1;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_165 = lean_ctor_get(x_44, 0);
x_166 = lean_ctor_get(x_44, 1);
x_167 = lean_ctor_get(x_44, 2);
x_168 = lean_ctor_get(x_44, 3);
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_44);
x_169 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_169, 0, x_165);
lean_ctor_set(x_169, 1, x_166);
lean_ctor_set(x_169, 2, x_167);
lean_ctor_set(x_169, 3, x_168);
lean_ctor_set_uint8(x_169, sizeof(void*)*4, x_127);
x_170 = 0;
lean_ctor_set(x_43, 0, x_169);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_170);
lean_ctor_set(x_1, 3, x_43);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_127);
return x_1;
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; lean_object* x_180; 
x_171 = lean_ctor_get(x_43, 1);
x_172 = lean_ctor_get(x_43, 2);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_43);
x_173 = lean_ctor_get(x_44, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_44, 1);
lean_inc(x_174);
x_175 = lean_ctor_get(x_44, 2);
lean_inc(x_175);
x_176 = lean_ctor_get(x_44, 3);
lean_inc(x_176);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 lean_ctor_release(x_44, 3);
 x_177 = x_44;
} else {
 lean_dec_ref(x_44);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(1, 4, 1);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_173);
lean_ctor_set(x_178, 1, x_174);
lean_ctor_set(x_178, 2, x_175);
lean_ctor_set(x_178, 3, x_176);
lean_ctor_set_uint8(x_178, sizeof(void*)*4, x_127);
x_179 = 0;
x_180 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_171);
lean_ctor_set(x_180, 2, x_172);
lean_ctor_set(x_180, 3, x_118);
lean_ctor_set_uint8(x_180, sizeof(void*)*4, x_179);
lean_ctor_set(x_1, 3, x_180);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_127);
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
uint8_t x_181; uint8_t x_182; 
x_181 = l_RBNode_isRed___rarg(x_32);
x_182 = l_coeDecidableEq(x_181);
if (x_182 == 0)
{
lean_object* x_183; 
x_183 = l_RBNode_ins___main___at_Lean_IR_mkIndexSet___spec__2(x_32, x_2, x_3);
lean_ctor_set(x_1, 0, x_183);
return x_1;
}
else
{
lean_object* x_184; lean_object* x_185; 
x_184 = l_RBNode_ins___main___at_Lean_IR_mkIndexSet___spec__2(x_32, x_2, x_3);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; 
x_186 = lean_ctor_get(x_184, 3);
lean_inc(x_186);
if (lean_obj_tag(x_186) == 0)
{
uint8_t x_187; 
x_187 = !lean_is_exclusive(x_184);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; uint8_t x_190; uint8_t x_191; 
x_188 = lean_ctor_get(x_184, 3);
lean_dec(x_188);
x_189 = lean_ctor_get(x_184, 0);
lean_dec(x_189);
x_190 = 0;
lean_ctor_set(x_184, 0, x_186);
lean_ctor_set_uint8(x_184, sizeof(void*)*4, x_190);
x_191 = 1;
lean_ctor_set(x_1, 0, x_184);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_191);
return x_1;
}
else
{
lean_object* x_192; lean_object* x_193; uint8_t x_194; lean_object* x_195; uint8_t x_196; 
x_192 = lean_ctor_get(x_184, 1);
x_193 = lean_ctor_get(x_184, 2);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_184);
x_194 = 0;
x_195 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_195, 0, x_186);
lean_ctor_set(x_195, 1, x_192);
lean_ctor_set(x_195, 2, x_193);
lean_ctor_set(x_195, 3, x_186);
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_194);
x_196 = 1;
lean_ctor_set(x_1, 0, x_195);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_196);
return x_1;
}
}
else
{
uint8_t x_197; 
x_197 = lean_ctor_get_uint8(x_186, sizeof(void*)*4);
if (x_197 == 0)
{
uint8_t x_198; 
x_198 = !lean_is_exclusive(x_184);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; 
x_199 = lean_ctor_get(x_184, 1);
x_200 = lean_ctor_get(x_184, 2);
x_201 = lean_ctor_get(x_184, 3);
lean_dec(x_201);
x_202 = lean_ctor_get(x_184, 0);
lean_dec(x_202);
x_203 = !lean_is_exclusive(x_186);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; 
x_204 = lean_ctor_get(x_186, 0);
x_205 = lean_ctor_get(x_186, 1);
x_206 = lean_ctor_get(x_186, 2);
x_207 = lean_ctor_get(x_186, 3);
x_208 = 1;
lean_ctor_set(x_186, 3, x_204);
lean_ctor_set(x_186, 2, x_200);
lean_ctor_set(x_186, 1, x_199);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_208);
lean_ctor_set(x_184, 3, x_35);
lean_ctor_set(x_184, 2, x_34);
lean_ctor_set(x_184, 1, x_33);
lean_ctor_set(x_184, 0, x_207);
lean_ctor_set_uint8(x_184, sizeof(void*)*4, x_208);
lean_ctor_set(x_1, 3, x_184);
lean_ctor_set(x_1, 2, x_206);
lean_ctor_set(x_1, 1, x_205);
lean_ctor_set(x_1, 0, x_186);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_197);
return x_1;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; lean_object* x_214; 
x_209 = lean_ctor_get(x_186, 0);
x_210 = lean_ctor_get(x_186, 1);
x_211 = lean_ctor_get(x_186, 2);
x_212 = lean_ctor_get(x_186, 3);
lean_inc(x_212);
lean_inc(x_211);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_186);
x_213 = 1;
x_214 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_214, 0, x_185);
lean_ctor_set(x_214, 1, x_199);
lean_ctor_set(x_214, 2, x_200);
lean_ctor_set(x_214, 3, x_209);
lean_ctor_set_uint8(x_214, sizeof(void*)*4, x_213);
lean_ctor_set(x_184, 3, x_35);
lean_ctor_set(x_184, 2, x_34);
lean_ctor_set(x_184, 1, x_33);
lean_ctor_set(x_184, 0, x_212);
lean_ctor_set_uint8(x_184, sizeof(void*)*4, x_213);
lean_ctor_set(x_1, 3, x_184);
lean_ctor_set(x_1, 2, x_211);
lean_ctor_set(x_1, 1, x_210);
lean_ctor_set(x_1, 0, x_214);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_197);
return x_1;
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; lean_object* x_223; lean_object* x_224; 
x_215 = lean_ctor_get(x_184, 1);
x_216 = lean_ctor_get(x_184, 2);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_184);
x_217 = lean_ctor_get(x_186, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_186, 1);
lean_inc(x_218);
x_219 = lean_ctor_get(x_186, 2);
lean_inc(x_219);
x_220 = lean_ctor_get(x_186, 3);
lean_inc(x_220);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 lean_ctor_release(x_186, 2);
 lean_ctor_release(x_186, 3);
 x_221 = x_186;
} else {
 lean_dec_ref(x_186);
 x_221 = lean_box(0);
}
x_222 = 1;
if (lean_is_scalar(x_221)) {
 x_223 = lean_alloc_ctor(1, 4, 1);
} else {
 x_223 = x_221;
}
lean_ctor_set(x_223, 0, x_185);
lean_ctor_set(x_223, 1, x_215);
lean_ctor_set(x_223, 2, x_216);
lean_ctor_set(x_223, 3, x_217);
lean_ctor_set_uint8(x_223, sizeof(void*)*4, x_222);
x_224 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_224, 0, x_220);
lean_ctor_set(x_224, 1, x_33);
lean_ctor_set(x_224, 2, x_34);
lean_ctor_set(x_224, 3, x_35);
lean_ctor_set_uint8(x_224, sizeof(void*)*4, x_222);
lean_ctor_set(x_1, 3, x_224);
lean_ctor_set(x_1, 2, x_219);
lean_ctor_set(x_1, 1, x_218);
lean_ctor_set(x_1, 0, x_223);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_197);
return x_1;
}
}
else
{
uint8_t x_225; 
x_225 = !lean_is_exclusive(x_184);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; uint8_t x_228; 
x_226 = lean_ctor_get(x_184, 3);
lean_dec(x_226);
x_227 = lean_ctor_get(x_184, 0);
lean_dec(x_227);
x_228 = 0;
lean_ctor_set_uint8(x_184, sizeof(void*)*4, x_228);
lean_ctor_set(x_1, 0, x_184);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_197);
return x_1;
}
else
{
lean_object* x_229; lean_object* x_230; uint8_t x_231; lean_object* x_232; 
x_229 = lean_ctor_get(x_184, 1);
x_230 = lean_ctor_get(x_184, 2);
lean_inc(x_230);
lean_inc(x_229);
lean_dec(x_184);
x_231 = 0;
x_232 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_232, 0, x_185);
lean_ctor_set(x_232, 1, x_229);
lean_ctor_set(x_232, 2, x_230);
lean_ctor_set(x_232, 3, x_186);
lean_ctor_set_uint8(x_232, sizeof(void*)*4, x_231);
lean_ctor_set(x_1, 0, x_232);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_197);
return x_1;
}
}
}
}
else
{
uint8_t x_233; 
x_233 = lean_ctor_get_uint8(x_185, sizeof(void*)*4);
if (x_233 == 0)
{
uint8_t x_234; 
x_234 = !lean_is_exclusive(x_184);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; 
x_235 = lean_ctor_get(x_184, 1);
x_236 = lean_ctor_get(x_184, 2);
x_237 = lean_ctor_get(x_184, 3);
x_238 = lean_ctor_get(x_184, 0);
lean_dec(x_238);
x_239 = !lean_is_exclusive(x_185);
if (x_239 == 0)
{
uint8_t x_240; 
x_240 = 1;
lean_ctor_set_uint8(x_185, sizeof(void*)*4, x_240);
lean_ctor_set(x_184, 3, x_35);
lean_ctor_set(x_184, 2, x_34);
lean_ctor_set(x_184, 1, x_33);
lean_ctor_set(x_184, 0, x_237);
lean_ctor_set_uint8(x_184, sizeof(void*)*4, x_240);
lean_ctor_set(x_1, 3, x_184);
lean_ctor_set(x_1, 2, x_236);
lean_ctor_set(x_1, 1, x_235);
lean_ctor_set(x_1, 0, x_185);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_233);
return x_1;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; lean_object* x_246; 
x_241 = lean_ctor_get(x_185, 0);
x_242 = lean_ctor_get(x_185, 1);
x_243 = lean_ctor_get(x_185, 2);
x_244 = lean_ctor_get(x_185, 3);
lean_inc(x_244);
lean_inc(x_243);
lean_inc(x_242);
lean_inc(x_241);
lean_dec(x_185);
x_245 = 1;
x_246 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_246, 0, x_241);
lean_ctor_set(x_246, 1, x_242);
lean_ctor_set(x_246, 2, x_243);
lean_ctor_set(x_246, 3, x_244);
lean_ctor_set_uint8(x_246, sizeof(void*)*4, x_245);
lean_ctor_set(x_184, 3, x_35);
lean_ctor_set(x_184, 2, x_34);
lean_ctor_set(x_184, 1, x_33);
lean_ctor_set(x_184, 0, x_237);
lean_ctor_set_uint8(x_184, sizeof(void*)*4, x_245);
lean_ctor_set(x_1, 3, x_184);
lean_ctor_set(x_1, 2, x_236);
lean_ctor_set(x_1, 1, x_235);
lean_ctor_set(x_1, 0, x_246);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_233);
return x_1;
}
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; uint8_t x_255; lean_object* x_256; lean_object* x_257; 
x_247 = lean_ctor_get(x_184, 1);
x_248 = lean_ctor_get(x_184, 2);
x_249 = lean_ctor_get(x_184, 3);
lean_inc(x_249);
lean_inc(x_248);
lean_inc(x_247);
lean_dec(x_184);
x_250 = lean_ctor_get(x_185, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_185, 1);
lean_inc(x_251);
x_252 = lean_ctor_get(x_185, 2);
lean_inc(x_252);
x_253 = lean_ctor_get(x_185, 3);
lean_inc(x_253);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 lean_ctor_release(x_185, 2);
 lean_ctor_release(x_185, 3);
 x_254 = x_185;
} else {
 lean_dec_ref(x_185);
 x_254 = lean_box(0);
}
x_255 = 1;
if (lean_is_scalar(x_254)) {
 x_256 = lean_alloc_ctor(1, 4, 1);
} else {
 x_256 = x_254;
}
lean_ctor_set(x_256, 0, x_250);
lean_ctor_set(x_256, 1, x_251);
lean_ctor_set(x_256, 2, x_252);
lean_ctor_set(x_256, 3, x_253);
lean_ctor_set_uint8(x_256, sizeof(void*)*4, x_255);
x_257 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_257, 0, x_249);
lean_ctor_set(x_257, 1, x_33);
lean_ctor_set(x_257, 2, x_34);
lean_ctor_set(x_257, 3, x_35);
lean_ctor_set_uint8(x_257, sizeof(void*)*4, x_255);
lean_ctor_set(x_1, 3, x_257);
lean_ctor_set(x_1, 2, x_248);
lean_ctor_set(x_1, 1, x_247);
lean_ctor_set(x_1, 0, x_256);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_233);
return x_1;
}
}
else
{
lean_object* x_258; 
x_258 = lean_ctor_get(x_184, 3);
lean_inc(x_258);
if (lean_obj_tag(x_258) == 0)
{
uint8_t x_259; 
x_259 = !lean_is_exclusive(x_184);
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; uint8_t x_262; 
x_260 = lean_ctor_get(x_184, 3);
lean_dec(x_260);
x_261 = lean_ctor_get(x_184, 0);
lean_dec(x_261);
x_262 = 0;
lean_ctor_set_uint8(x_184, sizeof(void*)*4, x_262);
lean_ctor_set(x_1, 0, x_184);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_233);
return x_1;
}
else
{
lean_object* x_263; lean_object* x_264; uint8_t x_265; lean_object* x_266; 
x_263 = lean_ctor_get(x_184, 1);
x_264 = lean_ctor_get(x_184, 2);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_184);
x_265 = 0;
x_266 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_266, 0, x_185);
lean_ctor_set(x_266, 1, x_263);
lean_ctor_set(x_266, 2, x_264);
lean_ctor_set(x_266, 3, x_258);
lean_ctor_set_uint8(x_266, sizeof(void*)*4, x_265);
lean_ctor_set(x_1, 0, x_266);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_233);
return x_1;
}
}
else
{
uint8_t x_267; 
x_267 = lean_ctor_get_uint8(x_258, sizeof(void*)*4);
if (x_267 == 0)
{
uint8_t x_268; 
lean_free_object(x_1);
x_268 = !lean_is_exclusive(x_184);
if (x_268 == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; uint8_t x_273; 
x_269 = lean_ctor_get(x_184, 1);
x_270 = lean_ctor_get(x_184, 2);
x_271 = lean_ctor_get(x_184, 3);
lean_dec(x_271);
x_272 = lean_ctor_get(x_184, 0);
lean_dec(x_272);
x_273 = !lean_is_exclusive(x_258);
if (x_273 == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; uint8_t x_278; 
x_274 = lean_ctor_get(x_258, 0);
x_275 = lean_ctor_get(x_258, 1);
x_276 = lean_ctor_get(x_258, 2);
x_277 = lean_ctor_get(x_258, 3);
lean_inc(x_185);
lean_ctor_set(x_258, 3, x_274);
lean_ctor_set(x_258, 2, x_270);
lean_ctor_set(x_258, 1, x_269);
lean_ctor_set(x_258, 0, x_185);
x_278 = !lean_is_exclusive(x_185);
if (x_278 == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_279 = lean_ctor_get(x_185, 3);
lean_dec(x_279);
x_280 = lean_ctor_get(x_185, 2);
lean_dec(x_280);
x_281 = lean_ctor_get(x_185, 1);
lean_dec(x_281);
x_282 = lean_ctor_get(x_185, 0);
lean_dec(x_282);
lean_ctor_set_uint8(x_258, sizeof(void*)*4, x_233);
lean_ctor_set(x_185, 3, x_35);
lean_ctor_set(x_185, 2, x_34);
lean_ctor_set(x_185, 1, x_33);
lean_ctor_set(x_185, 0, x_277);
lean_ctor_set(x_184, 3, x_185);
lean_ctor_set(x_184, 2, x_276);
lean_ctor_set(x_184, 1, x_275);
lean_ctor_set(x_184, 0, x_258);
lean_ctor_set_uint8(x_184, sizeof(void*)*4, x_267);
return x_184;
}
else
{
lean_object* x_283; 
lean_dec(x_185);
lean_ctor_set_uint8(x_258, sizeof(void*)*4, x_233);
x_283 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_283, 0, x_277);
lean_ctor_set(x_283, 1, x_33);
lean_ctor_set(x_283, 2, x_34);
lean_ctor_set(x_283, 3, x_35);
lean_ctor_set_uint8(x_283, sizeof(void*)*4, x_233);
lean_ctor_set(x_184, 3, x_283);
lean_ctor_set(x_184, 2, x_276);
lean_ctor_set(x_184, 1, x_275);
lean_ctor_set(x_184, 0, x_258);
lean_ctor_set_uint8(x_184, sizeof(void*)*4, x_267);
return x_184;
}
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_284 = lean_ctor_get(x_258, 0);
x_285 = lean_ctor_get(x_258, 1);
x_286 = lean_ctor_get(x_258, 2);
x_287 = lean_ctor_get(x_258, 3);
lean_inc(x_287);
lean_inc(x_286);
lean_inc(x_285);
lean_inc(x_284);
lean_dec(x_258);
lean_inc(x_185);
x_288 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_288, 0, x_185);
lean_ctor_set(x_288, 1, x_269);
lean_ctor_set(x_288, 2, x_270);
lean_ctor_set(x_288, 3, x_284);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 lean_ctor_release(x_185, 2);
 lean_ctor_release(x_185, 3);
 x_289 = x_185;
} else {
 lean_dec_ref(x_185);
 x_289 = lean_box(0);
}
lean_ctor_set_uint8(x_288, sizeof(void*)*4, x_233);
if (lean_is_scalar(x_289)) {
 x_290 = lean_alloc_ctor(1, 4, 1);
} else {
 x_290 = x_289;
}
lean_ctor_set(x_290, 0, x_287);
lean_ctor_set(x_290, 1, x_33);
lean_ctor_set(x_290, 2, x_34);
lean_ctor_set(x_290, 3, x_35);
lean_ctor_set_uint8(x_290, sizeof(void*)*4, x_233);
lean_ctor_set(x_184, 3, x_290);
lean_ctor_set(x_184, 2, x_286);
lean_ctor_set(x_184, 1, x_285);
lean_ctor_set(x_184, 0, x_288);
lean_ctor_set_uint8(x_184, sizeof(void*)*4, x_267);
return x_184;
}
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_291 = lean_ctor_get(x_184, 1);
x_292 = lean_ctor_get(x_184, 2);
lean_inc(x_292);
lean_inc(x_291);
lean_dec(x_184);
x_293 = lean_ctor_get(x_258, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_258, 1);
lean_inc(x_294);
x_295 = lean_ctor_get(x_258, 2);
lean_inc(x_295);
x_296 = lean_ctor_get(x_258, 3);
lean_inc(x_296);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 lean_ctor_release(x_258, 2);
 lean_ctor_release(x_258, 3);
 x_297 = x_258;
} else {
 lean_dec_ref(x_258);
 x_297 = lean_box(0);
}
lean_inc(x_185);
if (lean_is_scalar(x_297)) {
 x_298 = lean_alloc_ctor(1, 4, 1);
} else {
 x_298 = x_297;
}
lean_ctor_set(x_298, 0, x_185);
lean_ctor_set(x_298, 1, x_291);
lean_ctor_set(x_298, 2, x_292);
lean_ctor_set(x_298, 3, x_293);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 lean_ctor_release(x_185, 2);
 lean_ctor_release(x_185, 3);
 x_299 = x_185;
} else {
 lean_dec_ref(x_185);
 x_299 = lean_box(0);
}
lean_ctor_set_uint8(x_298, sizeof(void*)*4, x_233);
if (lean_is_scalar(x_299)) {
 x_300 = lean_alloc_ctor(1, 4, 1);
} else {
 x_300 = x_299;
}
lean_ctor_set(x_300, 0, x_296);
lean_ctor_set(x_300, 1, x_33);
lean_ctor_set(x_300, 2, x_34);
lean_ctor_set(x_300, 3, x_35);
lean_ctor_set_uint8(x_300, sizeof(void*)*4, x_233);
x_301 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_301, 0, x_298);
lean_ctor_set(x_301, 1, x_294);
lean_ctor_set(x_301, 2, x_295);
lean_ctor_set(x_301, 3, x_300);
lean_ctor_set_uint8(x_301, sizeof(void*)*4, x_267);
return x_301;
}
}
else
{
uint8_t x_302; 
x_302 = !lean_is_exclusive(x_184);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; uint8_t x_305; 
x_303 = lean_ctor_get(x_184, 3);
lean_dec(x_303);
x_304 = lean_ctor_get(x_184, 0);
lean_dec(x_304);
x_305 = !lean_is_exclusive(x_185);
if (x_305 == 0)
{
uint8_t x_306; 
lean_ctor_set_uint8(x_185, sizeof(void*)*4, x_267);
x_306 = 0;
lean_ctor_set_uint8(x_184, sizeof(void*)*4, x_306);
lean_ctor_set(x_1, 0, x_184);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_267);
return x_1;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; 
x_307 = lean_ctor_get(x_185, 0);
x_308 = lean_ctor_get(x_185, 1);
x_309 = lean_ctor_get(x_185, 2);
x_310 = lean_ctor_get(x_185, 3);
lean_inc(x_310);
lean_inc(x_309);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_185);
x_311 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_311, 0, x_307);
lean_ctor_set(x_311, 1, x_308);
lean_ctor_set(x_311, 2, x_309);
lean_ctor_set(x_311, 3, x_310);
lean_ctor_set_uint8(x_311, sizeof(void*)*4, x_267);
x_312 = 0;
lean_ctor_set(x_184, 0, x_311);
lean_ctor_set_uint8(x_184, sizeof(void*)*4, x_312);
lean_ctor_set(x_1, 0, x_184);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_267);
return x_1;
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; uint8_t x_321; lean_object* x_322; 
x_313 = lean_ctor_get(x_184, 1);
x_314 = lean_ctor_get(x_184, 2);
lean_inc(x_314);
lean_inc(x_313);
lean_dec(x_184);
x_315 = lean_ctor_get(x_185, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_185, 1);
lean_inc(x_316);
x_317 = lean_ctor_get(x_185, 2);
lean_inc(x_317);
x_318 = lean_ctor_get(x_185, 3);
lean_inc(x_318);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 lean_ctor_release(x_185, 2);
 lean_ctor_release(x_185, 3);
 x_319 = x_185;
} else {
 lean_dec_ref(x_185);
 x_319 = lean_box(0);
}
if (lean_is_scalar(x_319)) {
 x_320 = lean_alloc_ctor(1, 4, 1);
} else {
 x_320 = x_319;
}
lean_ctor_set(x_320, 0, x_315);
lean_ctor_set(x_320, 1, x_316);
lean_ctor_set(x_320, 2, x_317);
lean_ctor_set(x_320, 3, x_318);
lean_ctor_set_uint8(x_320, sizeof(void*)*4, x_267);
x_321 = 0;
x_322 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_322, 0, x_320);
lean_ctor_set(x_322, 1, x_313);
lean_ctor_set(x_322, 2, x_314);
lean_ctor_set(x_322, 3, x_258);
lean_ctor_set_uint8(x_322, sizeof(void*)*4, x_321);
lean_ctor_set(x_1, 0, x_322);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_267);
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
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; uint8_t x_328; 
x_323 = lean_ctor_get(x_1, 0);
x_324 = lean_ctor_get(x_1, 1);
x_325 = lean_ctor_get(x_1, 2);
x_326 = lean_ctor_get(x_1, 3);
lean_inc(x_326);
lean_inc(x_325);
lean_inc(x_324);
lean_inc(x_323);
lean_dec(x_1);
x_327 = lean_nat_dec_lt(x_2, x_324);
x_328 = l_coeDecidableEq(x_327);
if (x_328 == 0)
{
uint8_t x_329; uint8_t x_330; 
x_329 = lean_nat_dec_lt(x_324, x_2);
x_330 = l_coeDecidableEq(x_329);
if (x_330 == 0)
{
lean_object* x_331; 
lean_dec(x_325);
lean_dec(x_324);
x_331 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_331, 0, x_323);
lean_ctor_set(x_331, 1, x_2);
lean_ctor_set(x_331, 2, x_3);
lean_ctor_set(x_331, 3, x_326);
lean_ctor_set_uint8(x_331, sizeof(void*)*4, x_6);
return x_331;
}
else
{
uint8_t x_332; uint8_t x_333; 
x_332 = l_RBNode_isRed___rarg(x_326);
x_333 = l_coeDecidableEq(x_332);
if (x_333 == 0)
{
lean_object* x_334; lean_object* x_335; 
x_334 = l_RBNode_ins___main___at_Lean_IR_mkIndexSet___spec__2(x_326, x_2, x_3);
x_335 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_335, 0, x_323);
lean_ctor_set(x_335, 1, x_324);
lean_ctor_set(x_335, 2, x_325);
lean_ctor_set(x_335, 3, x_334);
lean_ctor_set_uint8(x_335, sizeof(void*)*4, x_6);
return x_335;
}
else
{
lean_object* x_336; lean_object* x_337; 
x_336 = l_RBNode_ins___main___at_Lean_IR_mkIndexSet___spec__2(x_326, x_2, x_3);
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; 
x_338 = lean_ctor_get(x_336, 3);
lean_inc(x_338);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; uint8_t x_342; lean_object* x_343; uint8_t x_344; lean_object* x_345; 
x_339 = lean_ctor_get(x_336, 1);
lean_inc(x_339);
x_340 = lean_ctor_get(x_336, 2);
lean_inc(x_340);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 lean_ctor_release(x_336, 2);
 lean_ctor_release(x_336, 3);
 x_341 = x_336;
} else {
 lean_dec_ref(x_336);
 x_341 = lean_box(0);
}
x_342 = 0;
if (lean_is_scalar(x_341)) {
 x_343 = lean_alloc_ctor(1, 4, 1);
} else {
 x_343 = x_341;
}
lean_ctor_set(x_343, 0, x_338);
lean_ctor_set(x_343, 1, x_339);
lean_ctor_set(x_343, 2, x_340);
lean_ctor_set(x_343, 3, x_338);
lean_ctor_set_uint8(x_343, sizeof(void*)*4, x_342);
x_344 = 1;
x_345 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_345, 0, x_323);
lean_ctor_set(x_345, 1, x_324);
lean_ctor_set(x_345, 2, x_325);
lean_ctor_set(x_345, 3, x_343);
lean_ctor_set_uint8(x_345, sizeof(void*)*4, x_344);
return x_345;
}
else
{
uint8_t x_346; 
x_346 = lean_ctor_get_uint8(x_338, sizeof(void*)*4);
if (x_346 == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; uint8_t x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_347 = lean_ctor_get(x_336, 1);
lean_inc(x_347);
x_348 = lean_ctor_get(x_336, 2);
lean_inc(x_348);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 lean_ctor_release(x_336, 2);
 lean_ctor_release(x_336, 3);
 x_349 = x_336;
} else {
 lean_dec_ref(x_336);
 x_349 = lean_box(0);
}
x_350 = lean_ctor_get(x_338, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_338, 1);
lean_inc(x_351);
x_352 = lean_ctor_get(x_338, 2);
lean_inc(x_352);
x_353 = lean_ctor_get(x_338, 3);
lean_inc(x_353);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 lean_ctor_release(x_338, 2);
 lean_ctor_release(x_338, 3);
 x_354 = x_338;
} else {
 lean_dec_ref(x_338);
 x_354 = lean_box(0);
}
x_355 = 1;
if (lean_is_scalar(x_354)) {
 x_356 = lean_alloc_ctor(1, 4, 1);
} else {
 x_356 = x_354;
}
lean_ctor_set(x_356, 0, x_323);
lean_ctor_set(x_356, 1, x_324);
lean_ctor_set(x_356, 2, x_325);
lean_ctor_set(x_356, 3, x_337);
lean_ctor_set_uint8(x_356, sizeof(void*)*4, x_355);
if (lean_is_scalar(x_349)) {
 x_357 = lean_alloc_ctor(1, 4, 1);
} else {
 x_357 = x_349;
}
lean_ctor_set(x_357, 0, x_350);
lean_ctor_set(x_357, 1, x_351);
lean_ctor_set(x_357, 2, x_352);
lean_ctor_set(x_357, 3, x_353);
lean_ctor_set_uint8(x_357, sizeof(void*)*4, x_355);
x_358 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_358, 0, x_356);
lean_ctor_set(x_358, 1, x_347);
lean_ctor_set(x_358, 2, x_348);
lean_ctor_set(x_358, 3, x_357);
lean_ctor_set_uint8(x_358, sizeof(void*)*4, x_346);
return x_358;
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; uint8_t x_362; lean_object* x_363; lean_object* x_364; 
x_359 = lean_ctor_get(x_336, 1);
lean_inc(x_359);
x_360 = lean_ctor_get(x_336, 2);
lean_inc(x_360);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 lean_ctor_release(x_336, 2);
 lean_ctor_release(x_336, 3);
 x_361 = x_336;
} else {
 lean_dec_ref(x_336);
 x_361 = lean_box(0);
}
x_362 = 0;
if (lean_is_scalar(x_361)) {
 x_363 = lean_alloc_ctor(1, 4, 1);
} else {
 x_363 = x_361;
}
lean_ctor_set(x_363, 0, x_337);
lean_ctor_set(x_363, 1, x_359);
lean_ctor_set(x_363, 2, x_360);
lean_ctor_set(x_363, 3, x_338);
lean_ctor_set_uint8(x_363, sizeof(void*)*4, x_362);
x_364 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_364, 0, x_323);
lean_ctor_set(x_364, 1, x_324);
lean_ctor_set(x_364, 2, x_325);
lean_ctor_set(x_364, 3, x_363);
lean_ctor_set_uint8(x_364, sizeof(void*)*4, x_346);
return x_364;
}
}
}
else
{
uint8_t x_365; 
x_365 = lean_ctor_get_uint8(x_337, sizeof(void*)*4);
if (x_365 == 0)
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; uint8_t x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_366 = lean_ctor_get(x_336, 1);
lean_inc(x_366);
x_367 = lean_ctor_get(x_336, 2);
lean_inc(x_367);
x_368 = lean_ctor_get(x_336, 3);
lean_inc(x_368);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 lean_ctor_release(x_336, 2);
 lean_ctor_release(x_336, 3);
 x_369 = x_336;
} else {
 lean_dec_ref(x_336);
 x_369 = lean_box(0);
}
x_370 = lean_ctor_get(x_337, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_337, 1);
lean_inc(x_371);
x_372 = lean_ctor_get(x_337, 2);
lean_inc(x_372);
x_373 = lean_ctor_get(x_337, 3);
lean_inc(x_373);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 lean_ctor_release(x_337, 2);
 lean_ctor_release(x_337, 3);
 x_374 = x_337;
} else {
 lean_dec_ref(x_337);
 x_374 = lean_box(0);
}
x_375 = 1;
if (lean_is_scalar(x_374)) {
 x_376 = lean_alloc_ctor(1, 4, 1);
} else {
 x_376 = x_374;
}
lean_ctor_set(x_376, 0, x_323);
lean_ctor_set(x_376, 1, x_324);
lean_ctor_set(x_376, 2, x_325);
lean_ctor_set(x_376, 3, x_370);
lean_ctor_set_uint8(x_376, sizeof(void*)*4, x_375);
if (lean_is_scalar(x_369)) {
 x_377 = lean_alloc_ctor(1, 4, 1);
} else {
 x_377 = x_369;
}
lean_ctor_set(x_377, 0, x_373);
lean_ctor_set(x_377, 1, x_366);
lean_ctor_set(x_377, 2, x_367);
lean_ctor_set(x_377, 3, x_368);
lean_ctor_set_uint8(x_377, sizeof(void*)*4, x_375);
x_378 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_378, 0, x_376);
lean_ctor_set(x_378, 1, x_371);
lean_ctor_set(x_378, 2, x_372);
lean_ctor_set(x_378, 3, x_377);
lean_ctor_set_uint8(x_378, sizeof(void*)*4, x_365);
return x_378;
}
else
{
lean_object* x_379; 
x_379 = lean_ctor_get(x_336, 3);
lean_inc(x_379);
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; uint8_t x_383; lean_object* x_384; lean_object* x_385; 
x_380 = lean_ctor_get(x_336, 1);
lean_inc(x_380);
x_381 = lean_ctor_get(x_336, 2);
lean_inc(x_381);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 lean_ctor_release(x_336, 2);
 lean_ctor_release(x_336, 3);
 x_382 = x_336;
} else {
 lean_dec_ref(x_336);
 x_382 = lean_box(0);
}
x_383 = 0;
if (lean_is_scalar(x_382)) {
 x_384 = lean_alloc_ctor(1, 4, 1);
} else {
 x_384 = x_382;
}
lean_ctor_set(x_384, 0, x_337);
lean_ctor_set(x_384, 1, x_380);
lean_ctor_set(x_384, 2, x_381);
lean_ctor_set(x_384, 3, x_379);
lean_ctor_set_uint8(x_384, sizeof(void*)*4, x_383);
x_385 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_385, 0, x_323);
lean_ctor_set(x_385, 1, x_324);
lean_ctor_set(x_385, 2, x_325);
lean_ctor_set(x_385, 3, x_384);
lean_ctor_set_uint8(x_385, sizeof(void*)*4, x_365);
return x_385;
}
else
{
uint8_t x_386; 
x_386 = lean_ctor_get_uint8(x_379, sizeof(void*)*4);
if (x_386 == 0)
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_387 = lean_ctor_get(x_336, 1);
lean_inc(x_387);
x_388 = lean_ctor_get(x_336, 2);
lean_inc(x_388);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 lean_ctor_release(x_336, 2);
 lean_ctor_release(x_336, 3);
 x_389 = x_336;
} else {
 lean_dec_ref(x_336);
 x_389 = lean_box(0);
}
x_390 = lean_ctor_get(x_379, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_379, 1);
lean_inc(x_391);
x_392 = lean_ctor_get(x_379, 2);
lean_inc(x_392);
x_393 = lean_ctor_get(x_379, 3);
lean_inc(x_393);
if (lean_is_exclusive(x_379)) {
 lean_ctor_release(x_379, 0);
 lean_ctor_release(x_379, 1);
 lean_ctor_release(x_379, 2);
 lean_ctor_release(x_379, 3);
 x_394 = x_379;
} else {
 lean_dec_ref(x_379);
 x_394 = lean_box(0);
}
lean_inc(x_337);
if (lean_is_scalar(x_394)) {
 x_395 = lean_alloc_ctor(1, 4, 1);
} else {
 x_395 = x_394;
}
lean_ctor_set(x_395, 0, x_323);
lean_ctor_set(x_395, 1, x_324);
lean_ctor_set(x_395, 2, x_325);
lean_ctor_set(x_395, 3, x_337);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 lean_ctor_release(x_337, 2);
 lean_ctor_release(x_337, 3);
 x_396 = x_337;
} else {
 lean_dec_ref(x_337);
 x_396 = lean_box(0);
}
lean_ctor_set_uint8(x_395, sizeof(void*)*4, x_365);
if (lean_is_scalar(x_396)) {
 x_397 = lean_alloc_ctor(1, 4, 1);
} else {
 x_397 = x_396;
}
lean_ctor_set(x_397, 0, x_390);
lean_ctor_set(x_397, 1, x_391);
lean_ctor_set(x_397, 2, x_392);
lean_ctor_set(x_397, 3, x_393);
lean_ctor_set_uint8(x_397, sizeof(void*)*4, x_365);
if (lean_is_scalar(x_389)) {
 x_398 = lean_alloc_ctor(1, 4, 1);
} else {
 x_398 = x_389;
}
lean_ctor_set(x_398, 0, x_395);
lean_ctor_set(x_398, 1, x_387);
lean_ctor_set(x_398, 2, x_388);
lean_ctor_set(x_398, 3, x_397);
lean_ctor_set_uint8(x_398, sizeof(void*)*4, x_386);
return x_398;
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; uint8_t x_408; lean_object* x_409; lean_object* x_410; 
x_399 = lean_ctor_get(x_336, 1);
lean_inc(x_399);
x_400 = lean_ctor_get(x_336, 2);
lean_inc(x_400);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 lean_ctor_release(x_336, 2);
 lean_ctor_release(x_336, 3);
 x_401 = x_336;
} else {
 lean_dec_ref(x_336);
 x_401 = lean_box(0);
}
x_402 = lean_ctor_get(x_337, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_337, 1);
lean_inc(x_403);
x_404 = lean_ctor_get(x_337, 2);
lean_inc(x_404);
x_405 = lean_ctor_get(x_337, 3);
lean_inc(x_405);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 lean_ctor_release(x_337, 2);
 lean_ctor_release(x_337, 3);
 x_406 = x_337;
} else {
 lean_dec_ref(x_337);
 x_406 = lean_box(0);
}
if (lean_is_scalar(x_406)) {
 x_407 = lean_alloc_ctor(1, 4, 1);
} else {
 x_407 = x_406;
}
lean_ctor_set(x_407, 0, x_402);
lean_ctor_set(x_407, 1, x_403);
lean_ctor_set(x_407, 2, x_404);
lean_ctor_set(x_407, 3, x_405);
lean_ctor_set_uint8(x_407, sizeof(void*)*4, x_386);
x_408 = 0;
if (lean_is_scalar(x_401)) {
 x_409 = lean_alloc_ctor(1, 4, 1);
} else {
 x_409 = x_401;
}
lean_ctor_set(x_409, 0, x_407);
lean_ctor_set(x_409, 1, x_399);
lean_ctor_set(x_409, 2, x_400);
lean_ctor_set(x_409, 3, x_379);
lean_ctor_set_uint8(x_409, sizeof(void*)*4, x_408);
x_410 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_410, 0, x_323);
lean_ctor_set(x_410, 1, x_324);
lean_ctor_set(x_410, 2, x_325);
lean_ctor_set(x_410, 3, x_409);
lean_ctor_set_uint8(x_410, sizeof(void*)*4, x_386);
return x_410;
}
}
}
}
}
}
}
else
{
uint8_t x_411; uint8_t x_412; 
x_411 = l_RBNode_isRed___rarg(x_323);
x_412 = l_coeDecidableEq(x_411);
if (x_412 == 0)
{
lean_object* x_413; lean_object* x_414; 
x_413 = l_RBNode_ins___main___at_Lean_IR_mkIndexSet___spec__2(x_323, x_2, x_3);
x_414 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_414, 0, x_413);
lean_ctor_set(x_414, 1, x_324);
lean_ctor_set(x_414, 2, x_325);
lean_ctor_set(x_414, 3, x_326);
lean_ctor_set_uint8(x_414, sizeof(void*)*4, x_6);
return x_414;
}
else
{
lean_object* x_415; lean_object* x_416; 
x_415 = l_RBNode_ins___main___at_Lean_IR_mkIndexSet___spec__2(x_323, x_2, x_3);
x_416 = lean_ctor_get(x_415, 0);
lean_inc(x_416);
if (lean_obj_tag(x_416) == 0)
{
lean_object* x_417; 
x_417 = lean_ctor_get(x_415, 3);
lean_inc(x_417);
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; uint8_t x_421; lean_object* x_422; uint8_t x_423; lean_object* x_424; 
x_418 = lean_ctor_get(x_415, 1);
lean_inc(x_418);
x_419 = lean_ctor_get(x_415, 2);
lean_inc(x_419);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 lean_ctor_release(x_415, 2);
 lean_ctor_release(x_415, 3);
 x_420 = x_415;
} else {
 lean_dec_ref(x_415);
 x_420 = lean_box(0);
}
x_421 = 0;
if (lean_is_scalar(x_420)) {
 x_422 = lean_alloc_ctor(1, 4, 1);
} else {
 x_422 = x_420;
}
lean_ctor_set(x_422, 0, x_417);
lean_ctor_set(x_422, 1, x_418);
lean_ctor_set(x_422, 2, x_419);
lean_ctor_set(x_422, 3, x_417);
lean_ctor_set_uint8(x_422, sizeof(void*)*4, x_421);
x_423 = 1;
x_424 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_424, 0, x_422);
lean_ctor_set(x_424, 1, x_324);
lean_ctor_set(x_424, 2, x_325);
lean_ctor_set(x_424, 3, x_326);
lean_ctor_set_uint8(x_424, sizeof(void*)*4, x_423);
return x_424;
}
else
{
uint8_t x_425; 
x_425 = lean_ctor_get_uint8(x_417, sizeof(void*)*4);
if (x_425 == 0)
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; uint8_t x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_426 = lean_ctor_get(x_415, 1);
lean_inc(x_426);
x_427 = lean_ctor_get(x_415, 2);
lean_inc(x_427);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 lean_ctor_release(x_415, 2);
 lean_ctor_release(x_415, 3);
 x_428 = x_415;
} else {
 lean_dec_ref(x_415);
 x_428 = lean_box(0);
}
x_429 = lean_ctor_get(x_417, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_417, 1);
lean_inc(x_430);
x_431 = lean_ctor_get(x_417, 2);
lean_inc(x_431);
x_432 = lean_ctor_get(x_417, 3);
lean_inc(x_432);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 lean_ctor_release(x_417, 2);
 lean_ctor_release(x_417, 3);
 x_433 = x_417;
} else {
 lean_dec_ref(x_417);
 x_433 = lean_box(0);
}
x_434 = 1;
if (lean_is_scalar(x_433)) {
 x_435 = lean_alloc_ctor(1, 4, 1);
} else {
 x_435 = x_433;
}
lean_ctor_set(x_435, 0, x_416);
lean_ctor_set(x_435, 1, x_426);
lean_ctor_set(x_435, 2, x_427);
lean_ctor_set(x_435, 3, x_429);
lean_ctor_set_uint8(x_435, sizeof(void*)*4, x_434);
if (lean_is_scalar(x_428)) {
 x_436 = lean_alloc_ctor(1, 4, 1);
} else {
 x_436 = x_428;
}
lean_ctor_set(x_436, 0, x_432);
lean_ctor_set(x_436, 1, x_324);
lean_ctor_set(x_436, 2, x_325);
lean_ctor_set(x_436, 3, x_326);
lean_ctor_set_uint8(x_436, sizeof(void*)*4, x_434);
x_437 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_437, 0, x_435);
lean_ctor_set(x_437, 1, x_430);
lean_ctor_set(x_437, 2, x_431);
lean_ctor_set(x_437, 3, x_436);
lean_ctor_set_uint8(x_437, sizeof(void*)*4, x_425);
return x_437;
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; uint8_t x_441; lean_object* x_442; lean_object* x_443; 
x_438 = lean_ctor_get(x_415, 1);
lean_inc(x_438);
x_439 = lean_ctor_get(x_415, 2);
lean_inc(x_439);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 lean_ctor_release(x_415, 2);
 lean_ctor_release(x_415, 3);
 x_440 = x_415;
} else {
 lean_dec_ref(x_415);
 x_440 = lean_box(0);
}
x_441 = 0;
if (lean_is_scalar(x_440)) {
 x_442 = lean_alloc_ctor(1, 4, 1);
} else {
 x_442 = x_440;
}
lean_ctor_set(x_442, 0, x_416);
lean_ctor_set(x_442, 1, x_438);
lean_ctor_set(x_442, 2, x_439);
lean_ctor_set(x_442, 3, x_417);
lean_ctor_set_uint8(x_442, sizeof(void*)*4, x_441);
x_443 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_443, 0, x_442);
lean_ctor_set(x_443, 1, x_324);
lean_ctor_set(x_443, 2, x_325);
lean_ctor_set(x_443, 3, x_326);
lean_ctor_set_uint8(x_443, sizeof(void*)*4, x_425);
return x_443;
}
}
}
else
{
uint8_t x_444; 
x_444 = lean_ctor_get_uint8(x_416, sizeof(void*)*4);
if (x_444 == 0)
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; uint8_t x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; 
x_445 = lean_ctor_get(x_415, 1);
lean_inc(x_445);
x_446 = lean_ctor_get(x_415, 2);
lean_inc(x_446);
x_447 = lean_ctor_get(x_415, 3);
lean_inc(x_447);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 lean_ctor_release(x_415, 2);
 lean_ctor_release(x_415, 3);
 x_448 = x_415;
} else {
 lean_dec_ref(x_415);
 x_448 = lean_box(0);
}
x_449 = lean_ctor_get(x_416, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_416, 1);
lean_inc(x_450);
x_451 = lean_ctor_get(x_416, 2);
lean_inc(x_451);
x_452 = lean_ctor_get(x_416, 3);
lean_inc(x_452);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 lean_ctor_release(x_416, 3);
 x_453 = x_416;
} else {
 lean_dec_ref(x_416);
 x_453 = lean_box(0);
}
x_454 = 1;
if (lean_is_scalar(x_453)) {
 x_455 = lean_alloc_ctor(1, 4, 1);
} else {
 x_455 = x_453;
}
lean_ctor_set(x_455, 0, x_449);
lean_ctor_set(x_455, 1, x_450);
lean_ctor_set(x_455, 2, x_451);
lean_ctor_set(x_455, 3, x_452);
lean_ctor_set_uint8(x_455, sizeof(void*)*4, x_454);
if (lean_is_scalar(x_448)) {
 x_456 = lean_alloc_ctor(1, 4, 1);
} else {
 x_456 = x_448;
}
lean_ctor_set(x_456, 0, x_447);
lean_ctor_set(x_456, 1, x_324);
lean_ctor_set(x_456, 2, x_325);
lean_ctor_set(x_456, 3, x_326);
lean_ctor_set_uint8(x_456, sizeof(void*)*4, x_454);
x_457 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_457, 0, x_455);
lean_ctor_set(x_457, 1, x_445);
lean_ctor_set(x_457, 2, x_446);
lean_ctor_set(x_457, 3, x_456);
lean_ctor_set_uint8(x_457, sizeof(void*)*4, x_444);
return x_457;
}
else
{
lean_object* x_458; 
x_458 = lean_ctor_get(x_415, 3);
lean_inc(x_458);
if (lean_obj_tag(x_458) == 0)
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; uint8_t x_462; lean_object* x_463; lean_object* x_464; 
x_459 = lean_ctor_get(x_415, 1);
lean_inc(x_459);
x_460 = lean_ctor_get(x_415, 2);
lean_inc(x_460);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 lean_ctor_release(x_415, 2);
 lean_ctor_release(x_415, 3);
 x_461 = x_415;
} else {
 lean_dec_ref(x_415);
 x_461 = lean_box(0);
}
x_462 = 0;
if (lean_is_scalar(x_461)) {
 x_463 = lean_alloc_ctor(1, 4, 1);
} else {
 x_463 = x_461;
}
lean_ctor_set(x_463, 0, x_416);
lean_ctor_set(x_463, 1, x_459);
lean_ctor_set(x_463, 2, x_460);
lean_ctor_set(x_463, 3, x_458);
lean_ctor_set_uint8(x_463, sizeof(void*)*4, x_462);
x_464 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_464, 0, x_463);
lean_ctor_set(x_464, 1, x_324);
lean_ctor_set(x_464, 2, x_325);
lean_ctor_set(x_464, 3, x_326);
lean_ctor_set_uint8(x_464, sizeof(void*)*4, x_444);
return x_464;
}
else
{
uint8_t x_465; 
x_465 = lean_ctor_get_uint8(x_458, sizeof(void*)*4);
if (x_465 == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; 
x_466 = lean_ctor_get(x_415, 1);
lean_inc(x_466);
x_467 = lean_ctor_get(x_415, 2);
lean_inc(x_467);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 lean_ctor_release(x_415, 2);
 lean_ctor_release(x_415, 3);
 x_468 = x_415;
} else {
 lean_dec_ref(x_415);
 x_468 = lean_box(0);
}
x_469 = lean_ctor_get(x_458, 0);
lean_inc(x_469);
x_470 = lean_ctor_get(x_458, 1);
lean_inc(x_470);
x_471 = lean_ctor_get(x_458, 2);
lean_inc(x_471);
x_472 = lean_ctor_get(x_458, 3);
lean_inc(x_472);
if (lean_is_exclusive(x_458)) {
 lean_ctor_release(x_458, 0);
 lean_ctor_release(x_458, 1);
 lean_ctor_release(x_458, 2);
 lean_ctor_release(x_458, 3);
 x_473 = x_458;
} else {
 lean_dec_ref(x_458);
 x_473 = lean_box(0);
}
lean_inc(x_416);
if (lean_is_scalar(x_473)) {
 x_474 = lean_alloc_ctor(1, 4, 1);
} else {
 x_474 = x_473;
}
lean_ctor_set(x_474, 0, x_416);
lean_ctor_set(x_474, 1, x_466);
lean_ctor_set(x_474, 2, x_467);
lean_ctor_set(x_474, 3, x_469);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 lean_ctor_release(x_416, 3);
 x_475 = x_416;
} else {
 lean_dec_ref(x_416);
 x_475 = lean_box(0);
}
lean_ctor_set_uint8(x_474, sizeof(void*)*4, x_444);
if (lean_is_scalar(x_475)) {
 x_476 = lean_alloc_ctor(1, 4, 1);
} else {
 x_476 = x_475;
}
lean_ctor_set(x_476, 0, x_472);
lean_ctor_set(x_476, 1, x_324);
lean_ctor_set(x_476, 2, x_325);
lean_ctor_set(x_476, 3, x_326);
lean_ctor_set_uint8(x_476, sizeof(void*)*4, x_444);
if (lean_is_scalar(x_468)) {
 x_477 = lean_alloc_ctor(1, 4, 1);
} else {
 x_477 = x_468;
}
lean_ctor_set(x_477, 0, x_474);
lean_ctor_set(x_477, 1, x_470);
lean_ctor_set(x_477, 2, x_471);
lean_ctor_set(x_477, 3, x_476);
lean_ctor_set_uint8(x_477, sizeof(void*)*4, x_465);
return x_477;
}
else
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; uint8_t x_487; lean_object* x_488; lean_object* x_489; 
x_478 = lean_ctor_get(x_415, 1);
lean_inc(x_478);
x_479 = lean_ctor_get(x_415, 2);
lean_inc(x_479);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 lean_ctor_release(x_415, 2);
 lean_ctor_release(x_415, 3);
 x_480 = x_415;
} else {
 lean_dec_ref(x_415);
 x_480 = lean_box(0);
}
x_481 = lean_ctor_get(x_416, 0);
lean_inc(x_481);
x_482 = lean_ctor_get(x_416, 1);
lean_inc(x_482);
x_483 = lean_ctor_get(x_416, 2);
lean_inc(x_483);
x_484 = lean_ctor_get(x_416, 3);
lean_inc(x_484);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 lean_ctor_release(x_416, 3);
 x_485 = x_416;
} else {
 lean_dec_ref(x_416);
 x_485 = lean_box(0);
}
if (lean_is_scalar(x_485)) {
 x_486 = lean_alloc_ctor(1, 4, 1);
} else {
 x_486 = x_485;
}
lean_ctor_set(x_486, 0, x_481);
lean_ctor_set(x_486, 1, x_482);
lean_ctor_set(x_486, 2, x_483);
lean_ctor_set(x_486, 3, x_484);
lean_ctor_set_uint8(x_486, sizeof(void*)*4, x_465);
x_487 = 0;
if (lean_is_scalar(x_480)) {
 x_488 = lean_alloc_ctor(1, 4, 1);
} else {
 x_488 = x_480;
}
lean_ctor_set(x_488, 0, x_486);
lean_ctor_set(x_488, 1, x_478);
lean_ctor_set(x_488, 2, x_479);
lean_ctor_set(x_488, 3, x_458);
lean_ctor_set_uint8(x_488, sizeof(void*)*4, x_487);
x_489 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_489, 0, x_488);
lean_ctor_set(x_489, 1, x_324);
lean_ctor_set(x_489, 2, x_325);
lean_ctor_set(x_489, 3, x_326);
lean_ctor_set_uint8(x_489, sizeof(void*)*4, x_465);
return x_489;
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
uint8_t x_4; uint8_t x_5; 
x_4 = l_RBNode_isRed___rarg(x_1);
x_5 = l_coeDecidableEq(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_RBNode_ins___main___at_Lean_IR_mkIndexSet___spec__2(x_1, x_2, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_RBNode_ins___main___at_Lean_IR_mkIndexSet___spec__2(x_1, x_2, x_3);
x_8 = l_RBNode_setBlack___rarg(x_7);
return x_8;
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 3);
x_12 = lean_nat_dec_lt(x_2, x_9);
x_13 = l_coeDecidableEq(x_12);
if (x_13 == 0)
{
uint8_t x_14; uint8_t x_15; 
x_14 = lean_nat_dec_lt(x_9, x_2);
x_15 = l_coeDecidableEq(x_14);
if (x_15 == 0)
{
lean_dec(x_10);
lean_dec(x_9);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
lean_object* x_16; 
x_16 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_11, x_2, x_3);
lean_ctor_set(x_1, 3, x_16);
return x_1;
}
}
else
{
lean_object* x_17; 
x_17 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_8, x_2, x_3);
lean_ctor_set(x_1, 0, x_17);
return x_1;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_ctor_get(x_1, 2);
x_21 = lean_ctor_get(x_1, 3);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_1);
x_22 = lean_nat_dec_lt(x_2, x_19);
x_23 = l_coeDecidableEq(x_22);
if (x_23 == 0)
{
uint8_t x_24; uint8_t x_25; 
x_24 = lean_nat_dec_lt(x_19, x_2);
x_25 = l_coeDecidableEq(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_20);
lean_dec(x_19);
x_26 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_2);
lean_ctor_set(x_26, 2, x_3);
lean_ctor_set(x_26, 3, x_21);
lean_ctor_set_uint8(x_26, sizeof(void*)*4, x_6);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_21, x_2, x_3);
x_28 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_28, 0, x_18);
lean_ctor_set(x_28, 1, x_19);
lean_ctor_set(x_28, 2, x_20);
lean_ctor_set(x_28, 3, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*4, x_6);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_18, x_2, x_3);
x_30 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_19);
lean_ctor_set(x_30, 2, x_20);
lean_ctor_set(x_30, 3, x_21);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_6);
return x_30;
}
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_1);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; 
x_32 = lean_ctor_get(x_1, 0);
x_33 = lean_ctor_get(x_1, 1);
x_34 = lean_ctor_get(x_1, 2);
x_35 = lean_ctor_get(x_1, 3);
x_36 = lean_nat_dec_lt(x_2, x_33);
x_37 = l_coeDecidableEq(x_36);
if (x_37 == 0)
{
uint8_t x_38; uint8_t x_39; 
x_38 = lean_nat_dec_lt(x_33, x_2);
x_39 = l_coeDecidableEq(x_38);
if (x_39 == 0)
{
lean_dec(x_34);
lean_dec(x_33);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
uint8_t x_40; uint8_t x_41; 
x_40 = l_RBNode_isRed___rarg(x_35);
x_41 = l_coeDecidableEq(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_35, x_2, x_3);
lean_ctor_set(x_1, 3, x_42);
return x_1;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_35, x_2, x_3);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_43, 3);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_43);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_43, 3);
lean_dec(x_47);
x_48 = lean_ctor_get(x_43, 0);
lean_dec(x_48);
x_49 = 0;
lean_ctor_set(x_43, 0, x_45);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_49);
x_50 = 1;
lean_ctor_set(x_1, 3, x_43);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_50);
return x_1;
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; uint8_t x_55; 
x_51 = lean_ctor_get(x_43, 1);
x_52 = lean_ctor_get(x_43, 2);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_43);
x_53 = 0;
x_54 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_54, 0, x_45);
lean_ctor_set(x_54, 1, x_51);
lean_ctor_set(x_54, 2, x_52);
lean_ctor_set(x_54, 3, x_45);
lean_ctor_set_uint8(x_54, sizeof(void*)*4, x_53);
x_55 = 1;
lean_ctor_set(x_1, 3, x_54);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_55);
return x_1;
}
}
else
{
uint8_t x_56; 
x_56 = lean_ctor_get_uint8(x_45, sizeof(void*)*4);
if (x_56 == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_43);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_58 = lean_ctor_get(x_43, 1);
x_59 = lean_ctor_get(x_43, 2);
x_60 = lean_ctor_get(x_43, 3);
lean_dec(x_60);
x_61 = lean_ctor_get(x_43, 0);
lean_dec(x_61);
x_62 = !lean_is_exclusive(x_45);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_63 = lean_ctor_get(x_45, 0);
x_64 = lean_ctor_get(x_45, 1);
x_65 = lean_ctor_get(x_45, 2);
x_66 = lean_ctor_get(x_45, 3);
x_67 = 1;
lean_ctor_set(x_45, 3, x_44);
lean_ctor_set(x_45, 2, x_34);
lean_ctor_set(x_45, 1, x_33);
lean_ctor_set(x_45, 0, x_32);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_67);
lean_ctor_set(x_43, 3, x_66);
lean_ctor_set(x_43, 2, x_65);
lean_ctor_set(x_43, 1, x_64);
lean_ctor_set(x_43, 0, x_63);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_67);
lean_ctor_set(x_1, 3, x_43);
lean_ctor_set(x_1, 2, x_59);
lean_ctor_set(x_1, 1, x_58);
lean_ctor_set(x_1, 0, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_56);
return x_1;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_45, 0);
x_69 = lean_ctor_get(x_45, 1);
x_70 = lean_ctor_get(x_45, 2);
x_71 = lean_ctor_get(x_45, 3);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_45);
x_72 = 1;
x_73 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_73, 0, x_32);
lean_ctor_set(x_73, 1, x_33);
lean_ctor_set(x_73, 2, x_34);
lean_ctor_set(x_73, 3, x_44);
lean_ctor_set_uint8(x_73, sizeof(void*)*4, x_72);
lean_ctor_set(x_43, 3, x_71);
lean_ctor_set(x_43, 2, x_70);
lean_ctor_set(x_43, 1, x_69);
lean_ctor_set(x_43, 0, x_68);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_72);
lean_ctor_set(x_1, 3, x_43);
lean_ctor_set(x_1, 2, x_59);
lean_ctor_set(x_1, 1, x_58);
lean_ctor_set(x_1, 0, x_73);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_56);
return x_1;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; 
x_74 = lean_ctor_get(x_43, 1);
x_75 = lean_ctor_get(x_43, 2);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_43);
x_76 = lean_ctor_get(x_45, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_45, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_45, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_45, 3);
lean_inc(x_79);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 lean_ctor_release(x_45, 2);
 lean_ctor_release(x_45, 3);
 x_80 = x_45;
} else {
 lean_dec_ref(x_45);
 x_80 = lean_box(0);
}
x_81 = 1;
if (lean_is_scalar(x_80)) {
 x_82 = lean_alloc_ctor(1, 4, 1);
} else {
 x_82 = x_80;
}
lean_ctor_set(x_82, 0, x_32);
lean_ctor_set(x_82, 1, x_33);
lean_ctor_set(x_82, 2, x_34);
lean_ctor_set(x_82, 3, x_44);
lean_ctor_set_uint8(x_82, sizeof(void*)*4, x_81);
x_83 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_83, 0, x_76);
lean_ctor_set(x_83, 1, x_77);
lean_ctor_set(x_83, 2, x_78);
lean_ctor_set(x_83, 3, x_79);
lean_ctor_set_uint8(x_83, sizeof(void*)*4, x_81);
lean_ctor_set(x_1, 3, x_83);
lean_ctor_set(x_1, 2, x_75);
lean_ctor_set(x_1, 1, x_74);
lean_ctor_set(x_1, 0, x_82);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_56);
return x_1;
}
}
else
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_43);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_43, 3);
lean_dec(x_85);
x_86 = lean_ctor_get(x_43, 0);
lean_dec(x_86);
x_87 = 0;
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_87);
lean_ctor_set(x_1, 3, x_43);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_56);
return x_1;
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_43, 1);
x_89 = lean_ctor_get(x_43, 2);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_43);
x_90 = 0;
x_91 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_91, 0, x_44);
lean_ctor_set(x_91, 1, x_88);
lean_ctor_set(x_91, 2, x_89);
lean_ctor_set(x_91, 3, x_45);
lean_ctor_set_uint8(x_91, sizeof(void*)*4, x_90);
lean_ctor_set(x_1, 3, x_91);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_56);
return x_1;
}
}
}
}
else
{
uint8_t x_92; 
x_92 = lean_ctor_get_uint8(x_44, sizeof(void*)*4);
if (x_92 == 0)
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_43);
if (x_93 == 0)
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_ctor_get(x_43, 0);
lean_dec(x_94);
x_95 = !lean_is_exclusive(x_44);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_96 = lean_ctor_get(x_44, 0);
x_97 = lean_ctor_get(x_44, 1);
x_98 = lean_ctor_get(x_44, 2);
x_99 = lean_ctor_get(x_44, 3);
x_100 = 1;
lean_ctor_set(x_44, 3, x_96);
lean_ctor_set(x_44, 2, x_34);
lean_ctor_set(x_44, 1, x_33);
lean_ctor_set(x_44, 0, x_32);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_100);
lean_ctor_set(x_43, 0, x_99);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_100);
lean_ctor_set(x_1, 3, x_43);
lean_ctor_set(x_1, 2, x_98);
lean_ctor_set(x_1, 1, x_97);
lean_ctor_set(x_1, 0, x_44);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_92);
return x_1;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; 
x_101 = lean_ctor_get(x_44, 0);
x_102 = lean_ctor_get(x_44, 1);
x_103 = lean_ctor_get(x_44, 2);
x_104 = lean_ctor_get(x_44, 3);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_44);
x_105 = 1;
x_106 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_106, 0, x_32);
lean_ctor_set(x_106, 1, x_33);
lean_ctor_set(x_106, 2, x_34);
lean_ctor_set(x_106, 3, x_101);
lean_ctor_set_uint8(x_106, sizeof(void*)*4, x_105);
lean_ctor_set(x_43, 0, x_104);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_105);
lean_ctor_set(x_1, 3, x_43);
lean_ctor_set(x_1, 2, x_103);
lean_ctor_set(x_1, 1, x_102);
lean_ctor_set(x_1, 0, x_106);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_92);
return x_1;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; 
x_107 = lean_ctor_get(x_43, 1);
x_108 = lean_ctor_get(x_43, 2);
x_109 = lean_ctor_get(x_43, 3);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_43);
x_110 = lean_ctor_get(x_44, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_44, 1);
lean_inc(x_111);
x_112 = lean_ctor_get(x_44, 2);
lean_inc(x_112);
x_113 = lean_ctor_get(x_44, 3);
lean_inc(x_113);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 lean_ctor_release(x_44, 3);
 x_114 = x_44;
} else {
 lean_dec_ref(x_44);
 x_114 = lean_box(0);
}
x_115 = 1;
if (lean_is_scalar(x_114)) {
 x_116 = lean_alloc_ctor(1, 4, 1);
} else {
 x_116 = x_114;
}
lean_ctor_set(x_116, 0, x_32);
lean_ctor_set(x_116, 1, x_33);
lean_ctor_set(x_116, 2, x_34);
lean_ctor_set(x_116, 3, x_110);
lean_ctor_set_uint8(x_116, sizeof(void*)*4, x_115);
x_117 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_117, 0, x_113);
lean_ctor_set(x_117, 1, x_107);
lean_ctor_set(x_117, 2, x_108);
lean_ctor_set(x_117, 3, x_109);
lean_ctor_set_uint8(x_117, sizeof(void*)*4, x_115);
lean_ctor_set(x_1, 3, x_117);
lean_ctor_set(x_1, 2, x_112);
lean_ctor_set(x_1, 1, x_111);
lean_ctor_set(x_1, 0, x_116);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_92);
return x_1;
}
}
else
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_43, 3);
lean_inc(x_118);
if (lean_obj_tag(x_118) == 0)
{
uint8_t x_119; 
x_119 = !lean_is_exclusive(x_43);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_120 = lean_ctor_get(x_43, 3);
lean_dec(x_120);
x_121 = lean_ctor_get(x_43, 0);
lean_dec(x_121);
x_122 = 0;
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_122);
lean_ctor_set(x_1, 3, x_43);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_92);
return x_1;
}
else
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_43, 1);
x_124 = lean_ctor_get(x_43, 2);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_43);
x_125 = 0;
x_126 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_126, 0, x_44);
lean_ctor_set(x_126, 1, x_123);
lean_ctor_set(x_126, 2, x_124);
lean_ctor_set(x_126, 3, x_118);
lean_ctor_set_uint8(x_126, sizeof(void*)*4, x_125);
lean_ctor_set(x_1, 3, x_126);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_92);
return x_1;
}
}
else
{
uint8_t x_127; 
x_127 = lean_ctor_get_uint8(x_118, sizeof(void*)*4);
if (x_127 == 0)
{
uint8_t x_128; 
lean_free_object(x_1);
x_128 = !lean_is_exclusive(x_43);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_129 = lean_ctor_get(x_43, 3);
lean_dec(x_129);
x_130 = lean_ctor_get(x_43, 0);
lean_dec(x_130);
x_131 = !lean_is_exclusive(x_118);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_132 = lean_ctor_get(x_118, 0);
x_133 = lean_ctor_get(x_118, 1);
x_134 = lean_ctor_get(x_118, 2);
x_135 = lean_ctor_get(x_118, 3);
lean_inc(x_44);
lean_ctor_set(x_118, 3, x_44);
lean_ctor_set(x_118, 2, x_34);
lean_ctor_set(x_118, 1, x_33);
lean_ctor_set(x_118, 0, x_32);
x_136 = !lean_is_exclusive(x_44);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_137 = lean_ctor_get(x_44, 3);
lean_dec(x_137);
x_138 = lean_ctor_get(x_44, 2);
lean_dec(x_138);
x_139 = lean_ctor_get(x_44, 1);
lean_dec(x_139);
x_140 = lean_ctor_get(x_44, 0);
lean_dec(x_140);
lean_ctor_set_uint8(x_118, sizeof(void*)*4, x_92);
lean_ctor_set(x_44, 3, x_135);
lean_ctor_set(x_44, 2, x_134);
lean_ctor_set(x_44, 1, x_133);
lean_ctor_set(x_44, 0, x_132);
lean_ctor_set(x_43, 3, x_44);
lean_ctor_set(x_43, 0, x_118);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_127);
return x_43;
}
else
{
lean_object* x_141; 
lean_dec(x_44);
lean_ctor_set_uint8(x_118, sizeof(void*)*4, x_92);
x_141 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_141, 0, x_132);
lean_ctor_set(x_141, 1, x_133);
lean_ctor_set(x_141, 2, x_134);
lean_ctor_set(x_141, 3, x_135);
lean_ctor_set_uint8(x_141, sizeof(void*)*4, x_92);
lean_ctor_set(x_43, 3, x_141);
lean_ctor_set(x_43, 0, x_118);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_127);
return x_43;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_142 = lean_ctor_get(x_118, 0);
x_143 = lean_ctor_get(x_118, 1);
x_144 = lean_ctor_get(x_118, 2);
x_145 = lean_ctor_get(x_118, 3);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_118);
lean_inc(x_44);
x_146 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_146, 0, x_32);
lean_ctor_set(x_146, 1, x_33);
lean_ctor_set(x_146, 2, x_34);
lean_ctor_set(x_146, 3, x_44);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 lean_ctor_release(x_44, 3);
 x_147 = x_44;
} else {
 lean_dec_ref(x_44);
 x_147 = lean_box(0);
}
lean_ctor_set_uint8(x_146, sizeof(void*)*4, x_92);
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 4, 1);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_142);
lean_ctor_set(x_148, 1, x_143);
lean_ctor_set(x_148, 2, x_144);
lean_ctor_set(x_148, 3, x_145);
lean_ctor_set_uint8(x_148, sizeof(void*)*4, x_92);
lean_ctor_set(x_43, 3, x_148);
lean_ctor_set(x_43, 0, x_146);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_127);
return x_43;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_149 = lean_ctor_get(x_43, 1);
x_150 = lean_ctor_get(x_43, 2);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_43);
x_151 = lean_ctor_get(x_118, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_118, 1);
lean_inc(x_152);
x_153 = lean_ctor_get(x_118, 2);
lean_inc(x_153);
x_154 = lean_ctor_get(x_118, 3);
lean_inc(x_154);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 lean_ctor_release(x_118, 2);
 lean_ctor_release(x_118, 3);
 x_155 = x_118;
} else {
 lean_dec_ref(x_118);
 x_155 = lean_box(0);
}
lean_inc(x_44);
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(1, 4, 1);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_32);
lean_ctor_set(x_156, 1, x_33);
lean_ctor_set(x_156, 2, x_34);
lean_ctor_set(x_156, 3, x_44);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 lean_ctor_release(x_44, 3);
 x_157 = x_44;
} else {
 lean_dec_ref(x_44);
 x_157 = lean_box(0);
}
lean_ctor_set_uint8(x_156, sizeof(void*)*4, x_92);
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 4, 1);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_151);
lean_ctor_set(x_158, 1, x_152);
lean_ctor_set(x_158, 2, x_153);
lean_ctor_set(x_158, 3, x_154);
lean_ctor_set_uint8(x_158, sizeof(void*)*4, x_92);
x_159 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_149);
lean_ctor_set(x_159, 2, x_150);
lean_ctor_set(x_159, 3, x_158);
lean_ctor_set_uint8(x_159, sizeof(void*)*4, x_127);
return x_159;
}
}
else
{
uint8_t x_160; 
x_160 = !lean_is_exclusive(x_43);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_161 = lean_ctor_get(x_43, 3);
lean_dec(x_161);
x_162 = lean_ctor_get(x_43, 0);
lean_dec(x_162);
x_163 = !lean_is_exclusive(x_44);
if (x_163 == 0)
{
uint8_t x_164; 
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_127);
x_164 = 0;
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_164);
lean_ctor_set(x_1, 3, x_43);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_127);
return x_1;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_165 = lean_ctor_get(x_44, 0);
x_166 = lean_ctor_get(x_44, 1);
x_167 = lean_ctor_get(x_44, 2);
x_168 = lean_ctor_get(x_44, 3);
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_44);
x_169 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_169, 0, x_165);
lean_ctor_set(x_169, 1, x_166);
lean_ctor_set(x_169, 2, x_167);
lean_ctor_set(x_169, 3, x_168);
lean_ctor_set_uint8(x_169, sizeof(void*)*4, x_127);
x_170 = 0;
lean_ctor_set(x_43, 0, x_169);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_170);
lean_ctor_set(x_1, 3, x_43);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_127);
return x_1;
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; lean_object* x_180; 
x_171 = lean_ctor_get(x_43, 1);
x_172 = lean_ctor_get(x_43, 2);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_43);
x_173 = lean_ctor_get(x_44, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_44, 1);
lean_inc(x_174);
x_175 = lean_ctor_get(x_44, 2);
lean_inc(x_175);
x_176 = lean_ctor_get(x_44, 3);
lean_inc(x_176);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 lean_ctor_release(x_44, 3);
 x_177 = x_44;
} else {
 lean_dec_ref(x_44);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(1, 4, 1);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_173);
lean_ctor_set(x_178, 1, x_174);
lean_ctor_set(x_178, 2, x_175);
lean_ctor_set(x_178, 3, x_176);
lean_ctor_set_uint8(x_178, sizeof(void*)*4, x_127);
x_179 = 0;
x_180 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_171);
lean_ctor_set(x_180, 2, x_172);
lean_ctor_set(x_180, 3, x_118);
lean_ctor_set_uint8(x_180, sizeof(void*)*4, x_179);
lean_ctor_set(x_1, 3, x_180);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_127);
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
uint8_t x_181; uint8_t x_182; 
x_181 = l_RBNode_isRed___rarg(x_32);
x_182 = l_coeDecidableEq(x_181);
if (x_182 == 0)
{
lean_object* x_183; 
x_183 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_32, x_2, x_3);
lean_ctor_set(x_1, 0, x_183);
return x_1;
}
else
{
lean_object* x_184; lean_object* x_185; 
x_184 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_32, x_2, x_3);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; 
x_186 = lean_ctor_get(x_184, 3);
lean_inc(x_186);
if (lean_obj_tag(x_186) == 0)
{
uint8_t x_187; 
x_187 = !lean_is_exclusive(x_184);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; uint8_t x_190; uint8_t x_191; 
x_188 = lean_ctor_get(x_184, 3);
lean_dec(x_188);
x_189 = lean_ctor_get(x_184, 0);
lean_dec(x_189);
x_190 = 0;
lean_ctor_set(x_184, 0, x_186);
lean_ctor_set_uint8(x_184, sizeof(void*)*4, x_190);
x_191 = 1;
lean_ctor_set(x_1, 0, x_184);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_191);
return x_1;
}
else
{
lean_object* x_192; lean_object* x_193; uint8_t x_194; lean_object* x_195; uint8_t x_196; 
x_192 = lean_ctor_get(x_184, 1);
x_193 = lean_ctor_get(x_184, 2);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_184);
x_194 = 0;
x_195 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_195, 0, x_186);
lean_ctor_set(x_195, 1, x_192);
lean_ctor_set(x_195, 2, x_193);
lean_ctor_set(x_195, 3, x_186);
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_194);
x_196 = 1;
lean_ctor_set(x_1, 0, x_195);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_196);
return x_1;
}
}
else
{
uint8_t x_197; 
x_197 = lean_ctor_get_uint8(x_186, sizeof(void*)*4);
if (x_197 == 0)
{
uint8_t x_198; 
x_198 = !lean_is_exclusive(x_184);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; 
x_199 = lean_ctor_get(x_184, 1);
x_200 = lean_ctor_get(x_184, 2);
x_201 = lean_ctor_get(x_184, 3);
lean_dec(x_201);
x_202 = lean_ctor_get(x_184, 0);
lean_dec(x_202);
x_203 = !lean_is_exclusive(x_186);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; 
x_204 = lean_ctor_get(x_186, 0);
x_205 = lean_ctor_get(x_186, 1);
x_206 = lean_ctor_get(x_186, 2);
x_207 = lean_ctor_get(x_186, 3);
x_208 = 1;
lean_ctor_set(x_186, 3, x_204);
lean_ctor_set(x_186, 2, x_200);
lean_ctor_set(x_186, 1, x_199);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_208);
lean_ctor_set(x_184, 3, x_35);
lean_ctor_set(x_184, 2, x_34);
lean_ctor_set(x_184, 1, x_33);
lean_ctor_set(x_184, 0, x_207);
lean_ctor_set_uint8(x_184, sizeof(void*)*4, x_208);
lean_ctor_set(x_1, 3, x_184);
lean_ctor_set(x_1, 2, x_206);
lean_ctor_set(x_1, 1, x_205);
lean_ctor_set(x_1, 0, x_186);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_197);
return x_1;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; lean_object* x_214; 
x_209 = lean_ctor_get(x_186, 0);
x_210 = lean_ctor_get(x_186, 1);
x_211 = lean_ctor_get(x_186, 2);
x_212 = lean_ctor_get(x_186, 3);
lean_inc(x_212);
lean_inc(x_211);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_186);
x_213 = 1;
x_214 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_214, 0, x_185);
lean_ctor_set(x_214, 1, x_199);
lean_ctor_set(x_214, 2, x_200);
lean_ctor_set(x_214, 3, x_209);
lean_ctor_set_uint8(x_214, sizeof(void*)*4, x_213);
lean_ctor_set(x_184, 3, x_35);
lean_ctor_set(x_184, 2, x_34);
lean_ctor_set(x_184, 1, x_33);
lean_ctor_set(x_184, 0, x_212);
lean_ctor_set_uint8(x_184, sizeof(void*)*4, x_213);
lean_ctor_set(x_1, 3, x_184);
lean_ctor_set(x_1, 2, x_211);
lean_ctor_set(x_1, 1, x_210);
lean_ctor_set(x_1, 0, x_214);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_197);
return x_1;
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; lean_object* x_223; lean_object* x_224; 
x_215 = lean_ctor_get(x_184, 1);
x_216 = lean_ctor_get(x_184, 2);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_184);
x_217 = lean_ctor_get(x_186, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_186, 1);
lean_inc(x_218);
x_219 = lean_ctor_get(x_186, 2);
lean_inc(x_219);
x_220 = lean_ctor_get(x_186, 3);
lean_inc(x_220);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 lean_ctor_release(x_186, 2);
 lean_ctor_release(x_186, 3);
 x_221 = x_186;
} else {
 lean_dec_ref(x_186);
 x_221 = lean_box(0);
}
x_222 = 1;
if (lean_is_scalar(x_221)) {
 x_223 = lean_alloc_ctor(1, 4, 1);
} else {
 x_223 = x_221;
}
lean_ctor_set(x_223, 0, x_185);
lean_ctor_set(x_223, 1, x_215);
lean_ctor_set(x_223, 2, x_216);
lean_ctor_set(x_223, 3, x_217);
lean_ctor_set_uint8(x_223, sizeof(void*)*4, x_222);
x_224 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_224, 0, x_220);
lean_ctor_set(x_224, 1, x_33);
lean_ctor_set(x_224, 2, x_34);
lean_ctor_set(x_224, 3, x_35);
lean_ctor_set_uint8(x_224, sizeof(void*)*4, x_222);
lean_ctor_set(x_1, 3, x_224);
lean_ctor_set(x_1, 2, x_219);
lean_ctor_set(x_1, 1, x_218);
lean_ctor_set(x_1, 0, x_223);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_197);
return x_1;
}
}
else
{
uint8_t x_225; 
x_225 = !lean_is_exclusive(x_184);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; uint8_t x_228; 
x_226 = lean_ctor_get(x_184, 3);
lean_dec(x_226);
x_227 = lean_ctor_get(x_184, 0);
lean_dec(x_227);
x_228 = 0;
lean_ctor_set_uint8(x_184, sizeof(void*)*4, x_228);
lean_ctor_set(x_1, 0, x_184);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_197);
return x_1;
}
else
{
lean_object* x_229; lean_object* x_230; uint8_t x_231; lean_object* x_232; 
x_229 = lean_ctor_get(x_184, 1);
x_230 = lean_ctor_get(x_184, 2);
lean_inc(x_230);
lean_inc(x_229);
lean_dec(x_184);
x_231 = 0;
x_232 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_232, 0, x_185);
lean_ctor_set(x_232, 1, x_229);
lean_ctor_set(x_232, 2, x_230);
lean_ctor_set(x_232, 3, x_186);
lean_ctor_set_uint8(x_232, sizeof(void*)*4, x_231);
lean_ctor_set(x_1, 0, x_232);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_197);
return x_1;
}
}
}
}
else
{
uint8_t x_233; 
x_233 = lean_ctor_get_uint8(x_185, sizeof(void*)*4);
if (x_233 == 0)
{
uint8_t x_234; 
x_234 = !lean_is_exclusive(x_184);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; 
x_235 = lean_ctor_get(x_184, 1);
x_236 = lean_ctor_get(x_184, 2);
x_237 = lean_ctor_get(x_184, 3);
x_238 = lean_ctor_get(x_184, 0);
lean_dec(x_238);
x_239 = !lean_is_exclusive(x_185);
if (x_239 == 0)
{
uint8_t x_240; 
x_240 = 1;
lean_ctor_set_uint8(x_185, sizeof(void*)*4, x_240);
lean_ctor_set(x_184, 3, x_35);
lean_ctor_set(x_184, 2, x_34);
lean_ctor_set(x_184, 1, x_33);
lean_ctor_set(x_184, 0, x_237);
lean_ctor_set_uint8(x_184, sizeof(void*)*4, x_240);
lean_ctor_set(x_1, 3, x_184);
lean_ctor_set(x_1, 2, x_236);
lean_ctor_set(x_1, 1, x_235);
lean_ctor_set(x_1, 0, x_185);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_233);
return x_1;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; lean_object* x_246; 
x_241 = lean_ctor_get(x_185, 0);
x_242 = lean_ctor_get(x_185, 1);
x_243 = lean_ctor_get(x_185, 2);
x_244 = lean_ctor_get(x_185, 3);
lean_inc(x_244);
lean_inc(x_243);
lean_inc(x_242);
lean_inc(x_241);
lean_dec(x_185);
x_245 = 1;
x_246 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_246, 0, x_241);
lean_ctor_set(x_246, 1, x_242);
lean_ctor_set(x_246, 2, x_243);
lean_ctor_set(x_246, 3, x_244);
lean_ctor_set_uint8(x_246, sizeof(void*)*4, x_245);
lean_ctor_set(x_184, 3, x_35);
lean_ctor_set(x_184, 2, x_34);
lean_ctor_set(x_184, 1, x_33);
lean_ctor_set(x_184, 0, x_237);
lean_ctor_set_uint8(x_184, sizeof(void*)*4, x_245);
lean_ctor_set(x_1, 3, x_184);
lean_ctor_set(x_1, 2, x_236);
lean_ctor_set(x_1, 1, x_235);
lean_ctor_set(x_1, 0, x_246);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_233);
return x_1;
}
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; uint8_t x_255; lean_object* x_256; lean_object* x_257; 
x_247 = lean_ctor_get(x_184, 1);
x_248 = lean_ctor_get(x_184, 2);
x_249 = lean_ctor_get(x_184, 3);
lean_inc(x_249);
lean_inc(x_248);
lean_inc(x_247);
lean_dec(x_184);
x_250 = lean_ctor_get(x_185, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_185, 1);
lean_inc(x_251);
x_252 = lean_ctor_get(x_185, 2);
lean_inc(x_252);
x_253 = lean_ctor_get(x_185, 3);
lean_inc(x_253);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 lean_ctor_release(x_185, 2);
 lean_ctor_release(x_185, 3);
 x_254 = x_185;
} else {
 lean_dec_ref(x_185);
 x_254 = lean_box(0);
}
x_255 = 1;
if (lean_is_scalar(x_254)) {
 x_256 = lean_alloc_ctor(1, 4, 1);
} else {
 x_256 = x_254;
}
lean_ctor_set(x_256, 0, x_250);
lean_ctor_set(x_256, 1, x_251);
lean_ctor_set(x_256, 2, x_252);
lean_ctor_set(x_256, 3, x_253);
lean_ctor_set_uint8(x_256, sizeof(void*)*4, x_255);
x_257 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_257, 0, x_249);
lean_ctor_set(x_257, 1, x_33);
lean_ctor_set(x_257, 2, x_34);
lean_ctor_set(x_257, 3, x_35);
lean_ctor_set_uint8(x_257, sizeof(void*)*4, x_255);
lean_ctor_set(x_1, 3, x_257);
lean_ctor_set(x_1, 2, x_248);
lean_ctor_set(x_1, 1, x_247);
lean_ctor_set(x_1, 0, x_256);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_233);
return x_1;
}
}
else
{
lean_object* x_258; 
x_258 = lean_ctor_get(x_184, 3);
lean_inc(x_258);
if (lean_obj_tag(x_258) == 0)
{
uint8_t x_259; 
x_259 = !lean_is_exclusive(x_184);
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; uint8_t x_262; 
x_260 = lean_ctor_get(x_184, 3);
lean_dec(x_260);
x_261 = lean_ctor_get(x_184, 0);
lean_dec(x_261);
x_262 = 0;
lean_ctor_set_uint8(x_184, sizeof(void*)*4, x_262);
lean_ctor_set(x_1, 0, x_184);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_233);
return x_1;
}
else
{
lean_object* x_263; lean_object* x_264; uint8_t x_265; lean_object* x_266; 
x_263 = lean_ctor_get(x_184, 1);
x_264 = lean_ctor_get(x_184, 2);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_184);
x_265 = 0;
x_266 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_266, 0, x_185);
lean_ctor_set(x_266, 1, x_263);
lean_ctor_set(x_266, 2, x_264);
lean_ctor_set(x_266, 3, x_258);
lean_ctor_set_uint8(x_266, sizeof(void*)*4, x_265);
lean_ctor_set(x_1, 0, x_266);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_233);
return x_1;
}
}
else
{
uint8_t x_267; 
x_267 = lean_ctor_get_uint8(x_258, sizeof(void*)*4);
if (x_267 == 0)
{
uint8_t x_268; 
lean_free_object(x_1);
x_268 = !lean_is_exclusive(x_184);
if (x_268 == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; uint8_t x_273; 
x_269 = lean_ctor_get(x_184, 1);
x_270 = lean_ctor_get(x_184, 2);
x_271 = lean_ctor_get(x_184, 3);
lean_dec(x_271);
x_272 = lean_ctor_get(x_184, 0);
lean_dec(x_272);
x_273 = !lean_is_exclusive(x_258);
if (x_273 == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; uint8_t x_278; 
x_274 = lean_ctor_get(x_258, 0);
x_275 = lean_ctor_get(x_258, 1);
x_276 = lean_ctor_get(x_258, 2);
x_277 = lean_ctor_get(x_258, 3);
lean_inc(x_185);
lean_ctor_set(x_258, 3, x_274);
lean_ctor_set(x_258, 2, x_270);
lean_ctor_set(x_258, 1, x_269);
lean_ctor_set(x_258, 0, x_185);
x_278 = !lean_is_exclusive(x_185);
if (x_278 == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_279 = lean_ctor_get(x_185, 3);
lean_dec(x_279);
x_280 = lean_ctor_get(x_185, 2);
lean_dec(x_280);
x_281 = lean_ctor_get(x_185, 1);
lean_dec(x_281);
x_282 = lean_ctor_get(x_185, 0);
lean_dec(x_282);
lean_ctor_set_uint8(x_258, sizeof(void*)*4, x_233);
lean_ctor_set(x_185, 3, x_35);
lean_ctor_set(x_185, 2, x_34);
lean_ctor_set(x_185, 1, x_33);
lean_ctor_set(x_185, 0, x_277);
lean_ctor_set(x_184, 3, x_185);
lean_ctor_set(x_184, 2, x_276);
lean_ctor_set(x_184, 1, x_275);
lean_ctor_set(x_184, 0, x_258);
lean_ctor_set_uint8(x_184, sizeof(void*)*4, x_267);
return x_184;
}
else
{
lean_object* x_283; 
lean_dec(x_185);
lean_ctor_set_uint8(x_258, sizeof(void*)*4, x_233);
x_283 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_283, 0, x_277);
lean_ctor_set(x_283, 1, x_33);
lean_ctor_set(x_283, 2, x_34);
lean_ctor_set(x_283, 3, x_35);
lean_ctor_set_uint8(x_283, sizeof(void*)*4, x_233);
lean_ctor_set(x_184, 3, x_283);
lean_ctor_set(x_184, 2, x_276);
lean_ctor_set(x_184, 1, x_275);
lean_ctor_set(x_184, 0, x_258);
lean_ctor_set_uint8(x_184, sizeof(void*)*4, x_267);
return x_184;
}
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_284 = lean_ctor_get(x_258, 0);
x_285 = lean_ctor_get(x_258, 1);
x_286 = lean_ctor_get(x_258, 2);
x_287 = lean_ctor_get(x_258, 3);
lean_inc(x_287);
lean_inc(x_286);
lean_inc(x_285);
lean_inc(x_284);
lean_dec(x_258);
lean_inc(x_185);
x_288 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_288, 0, x_185);
lean_ctor_set(x_288, 1, x_269);
lean_ctor_set(x_288, 2, x_270);
lean_ctor_set(x_288, 3, x_284);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 lean_ctor_release(x_185, 2);
 lean_ctor_release(x_185, 3);
 x_289 = x_185;
} else {
 lean_dec_ref(x_185);
 x_289 = lean_box(0);
}
lean_ctor_set_uint8(x_288, sizeof(void*)*4, x_233);
if (lean_is_scalar(x_289)) {
 x_290 = lean_alloc_ctor(1, 4, 1);
} else {
 x_290 = x_289;
}
lean_ctor_set(x_290, 0, x_287);
lean_ctor_set(x_290, 1, x_33);
lean_ctor_set(x_290, 2, x_34);
lean_ctor_set(x_290, 3, x_35);
lean_ctor_set_uint8(x_290, sizeof(void*)*4, x_233);
lean_ctor_set(x_184, 3, x_290);
lean_ctor_set(x_184, 2, x_286);
lean_ctor_set(x_184, 1, x_285);
lean_ctor_set(x_184, 0, x_288);
lean_ctor_set_uint8(x_184, sizeof(void*)*4, x_267);
return x_184;
}
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_291 = lean_ctor_get(x_184, 1);
x_292 = lean_ctor_get(x_184, 2);
lean_inc(x_292);
lean_inc(x_291);
lean_dec(x_184);
x_293 = lean_ctor_get(x_258, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_258, 1);
lean_inc(x_294);
x_295 = lean_ctor_get(x_258, 2);
lean_inc(x_295);
x_296 = lean_ctor_get(x_258, 3);
lean_inc(x_296);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 lean_ctor_release(x_258, 2);
 lean_ctor_release(x_258, 3);
 x_297 = x_258;
} else {
 lean_dec_ref(x_258);
 x_297 = lean_box(0);
}
lean_inc(x_185);
if (lean_is_scalar(x_297)) {
 x_298 = lean_alloc_ctor(1, 4, 1);
} else {
 x_298 = x_297;
}
lean_ctor_set(x_298, 0, x_185);
lean_ctor_set(x_298, 1, x_291);
lean_ctor_set(x_298, 2, x_292);
lean_ctor_set(x_298, 3, x_293);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 lean_ctor_release(x_185, 2);
 lean_ctor_release(x_185, 3);
 x_299 = x_185;
} else {
 lean_dec_ref(x_185);
 x_299 = lean_box(0);
}
lean_ctor_set_uint8(x_298, sizeof(void*)*4, x_233);
if (lean_is_scalar(x_299)) {
 x_300 = lean_alloc_ctor(1, 4, 1);
} else {
 x_300 = x_299;
}
lean_ctor_set(x_300, 0, x_296);
lean_ctor_set(x_300, 1, x_33);
lean_ctor_set(x_300, 2, x_34);
lean_ctor_set(x_300, 3, x_35);
lean_ctor_set_uint8(x_300, sizeof(void*)*4, x_233);
x_301 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_301, 0, x_298);
lean_ctor_set(x_301, 1, x_294);
lean_ctor_set(x_301, 2, x_295);
lean_ctor_set(x_301, 3, x_300);
lean_ctor_set_uint8(x_301, sizeof(void*)*4, x_267);
return x_301;
}
}
else
{
uint8_t x_302; 
x_302 = !lean_is_exclusive(x_184);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; uint8_t x_305; 
x_303 = lean_ctor_get(x_184, 3);
lean_dec(x_303);
x_304 = lean_ctor_get(x_184, 0);
lean_dec(x_304);
x_305 = !lean_is_exclusive(x_185);
if (x_305 == 0)
{
uint8_t x_306; 
lean_ctor_set_uint8(x_185, sizeof(void*)*4, x_267);
x_306 = 0;
lean_ctor_set_uint8(x_184, sizeof(void*)*4, x_306);
lean_ctor_set(x_1, 0, x_184);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_267);
return x_1;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; 
x_307 = lean_ctor_get(x_185, 0);
x_308 = lean_ctor_get(x_185, 1);
x_309 = lean_ctor_get(x_185, 2);
x_310 = lean_ctor_get(x_185, 3);
lean_inc(x_310);
lean_inc(x_309);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_185);
x_311 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_311, 0, x_307);
lean_ctor_set(x_311, 1, x_308);
lean_ctor_set(x_311, 2, x_309);
lean_ctor_set(x_311, 3, x_310);
lean_ctor_set_uint8(x_311, sizeof(void*)*4, x_267);
x_312 = 0;
lean_ctor_set(x_184, 0, x_311);
lean_ctor_set_uint8(x_184, sizeof(void*)*4, x_312);
lean_ctor_set(x_1, 0, x_184);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_267);
return x_1;
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; uint8_t x_321; lean_object* x_322; 
x_313 = lean_ctor_get(x_184, 1);
x_314 = lean_ctor_get(x_184, 2);
lean_inc(x_314);
lean_inc(x_313);
lean_dec(x_184);
x_315 = lean_ctor_get(x_185, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_185, 1);
lean_inc(x_316);
x_317 = lean_ctor_get(x_185, 2);
lean_inc(x_317);
x_318 = lean_ctor_get(x_185, 3);
lean_inc(x_318);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 lean_ctor_release(x_185, 2);
 lean_ctor_release(x_185, 3);
 x_319 = x_185;
} else {
 lean_dec_ref(x_185);
 x_319 = lean_box(0);
}
if (lean_is_scalar(x_319)) {
 x_320 = lean_alloc_ctor(1, 4, 1);
} else {
 x_320 = x_319;
}
lean_ctor_set(x_320, 0, x_315);
lean_ctor_set(x_320, 1, x_316);
lean_ctor_set(x_320, 2, x_317);
lean_ctor_set(x_320, 3, x_318);
lean_ctor_set_uint8(x_320, sizeof(void*)*4, x_267);
x_321 = 0;
x_322 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_322, 0, x_320);
lean_ctor_set(x_322, 1, x_313);
lean_ctor_set(x_322, 2, x_314);
lean_ctor_set(x_322, 3, x_258);
lean_ctor_set_uint8(x_322, sizeof(void*)*4, x_321);
lean_ctor_set(x_1, 0, x_322);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_267);
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
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; uint8_t x_328; 
x_323 = lean_ctor_get(x_1, 0);
x_324 = lean_ctor_get(x_1, 1);
x_325 = lean_ctor_get(x_1, 2);
x_326 = lean_ctor_get(x_1, 3);
lean_inc(x_326);
lean_inc(x_325);
lean_inc(x_324);
lean_inc(x_323);
lean_dec(x_1);
x_327 = lean_nat_dec_lt(x_2, x_324);
x_328 = l_coeDecidableEq(x_327);
if (x_328 == 0)
{
uint8_t x_329; uint8_t x_330; 
x_329 = lean_nat_dec_lt(x_324, x_2);
x_330 = l_coeDecidableEq(x_329);
if (x_330 == 0)
{
lean_object* x_331; 
lean_dec(x_325);
lean_dec(x_324);
x_331 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_331, 0, x_323);
lean_ctor_set(x_331, 1, x_2);
lean_ctor_set(x_331, 2, x_3);
lean_ctor_set(x_331, 3, x_326);
lean_ctor_set_uint8(x_331, sizeof(void*)*4, x_6);
return x_331;
}
else
{
uint8_t x_332; uint8_t x_333; 
x_332 = l_RBNode_isRed___rarg(x_326);
x_333 = l_coeDecidableEq(x_332);
if (x_333 == 0)
{
lean_object* x_334; lean_object* x_335; 
x_334 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_326, x_2, x_3);
x_335 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_335, 0, x_323);
lean_ctor_set(x_335, 1, x_324);
lean_ctor_set(x_335, 2, x_325);
lean_ctor_set(x_335, 3, x_334);
lean_ctor_set_uint8(x_335, sizeof(void*)*4, x_6);
return x_335;
}
else
{
lean_object* x_336; lean_object* x_337; 
x_336 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_326, x_2, x_3);
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; 
x_338 = lean_ctor_get(x_336, 3);
lean_inc(x_338);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; uint8_t x_342; lean_object* x_343; uint8_t x_344; lean_object* x_345; 
x_339 = lean_ctor_get(x_336, 1);
lean_inc(x_339);
x_340 = lean_ctor_get(x_336, 2);
lean_inc(x_340);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 lean_ctor_release(x_336, 2);
 lean_ctor_release(x_336, 3);
 x_341 = x_336;
} else {
 lean_dec_ref(x_336);
 x_341 = lean_box(0);
}
x_342 = 0;
if (lean_is_scalar(x_341)) {
 x_343 = lean_alloc_ctor(1, 4, 1);
} else {
 x_343 = x_341;
}
lean_ctor_set(x_343, 0, x_338);
lean_ctor_set(x_343, 1, x_339);
lean_ctor_set(x_343, 2, x_340);
lean_ctor_set(x_343, 3, x_338);
lean_ctor_set_uint8(x_343, sizeof(void*)*4, x_342);
x_344 = 1;
x_345 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_345, 0, x_323);
lean_ctor_set(x_345, 1, x_324);
lean_ctor_set(x_345, 2, x_325);
lean_ctor_set(x_345, 3, x_343);
lean_ctor_set_uint8(x_345, sizeof(void*)*4, x_344);
return x_345;
}
else
{
uint8_t x_346; 
x_346 = lean_ctor_get_uint8(x_338, sizeof(void*)*4);
if (x_346 == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; uint8_t x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_347 = lean_ctor_get(x_336, 1);
lean_inc(x_347);
x_348 = lean_ctor_get(x_336, 2);
lean_inc(x_348);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 lean_ctor_release(x_336, 2);
 lean_ctor_release(x_336, 3);
 x_349 = x_336;
} else {
 lean_dec_ref(x_336);
 x_349 = lean_box(0);
}
x_350 = lean_ctor_get(x_338, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_338, 1);
lean_inc(x_351);
x_352 = lean_ctor_get(x_338, 2);
lean_inc(x_352);
x_353 = lean_ctor_get(x_338, 3);
lean_inc(x_353);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 lean_ctor_release(x_338, 2);
 lean_ctor_release(x_338, 3);
 x_354 = x_338;
} else {
 lean_dec_ref(x_338);
 x_354 = lean_box(0);
}
x_355 = 1;
if (lean_is_scalar(x_354)) {
 x_356 = lean_alloc_ctor(1, 4, 1);
} else {
 x_356 = x_354;
}
lean_ctor_set(x_356, 0, x_323);
lean_ctor_set(x_356, 1, x_324);
lean_ctor_set(x_356, 2, x_325);
lean_ctor_set(x_356, 3, x_337);
lean_ctor_set_uint8(x_356, sizeof(void*)*4, x_355);
if (lean_is_scalar(x_349)) {
 x_357 = lean_alloc_ctor(1, 4, 1);
} else {
 x_357 = x_349;
}
lean_ctor_set(x_357, 0, x_350);
lean_ctor_set(x_357, 1, x_351);
lean_ctor_set(x_357, 2, x_352);
lean_ctor_set(x_357, 3, x_353);
lean_ctor_set_uint8(x_357, sizeof(void*)*4, x_355);
x_358 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_358, 0, x_356);
lean_ctor_set(x_358, 1, x_347);
lean_ctor_set(x_358, 2, x_348);
lean_ctor_set(x_358, 3, x_357);
lean_ctor_set_uint8(x_358, sizeof(void*)*4, x_346);
return x_358;
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; uint8_t x_362; lean_object* x_363; lean_object* x_364; 
x_359 = lean_ctor_get(x_336, 1);
lean_inc(x_359);
x_360 = lean_ctor_get(x_336, 2);
lean_inc(x_360);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 lean_ctor_release(x_336, 2);
 lean_ctor_release(x_336, 3);
 x_361 = x_336;
} else {
 lean_dec_ref(x_336);
 x_361 = lean_box(0);
}
x_362 = 0;
if (lean_is_scalar(x_361)) {
 x_363 = lean_alloc_ctor(1, 4, 1);
} else {
 x_363 = x_361;
}
lean_ctor_set(x_363, 0, x_337);
lean_ctor_set(x_363, 1, x_359);
lean_ctor_set(x_363, 2, x_360);
lean_ctor_set(x_363, 3, x_338);
lean_ctor_set_uint8(x_363, sizeof(void*)*4, x_362);
x_364 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_364, 0, x_323);
lean_ctor_set(x_364, 1, x_324);
lean_ctor_set(x_364, 2, x_325);
lean_ctor_set(x_364, 3, x_363);
lean_ctor_set_uint8(x_364, sizeof(void*)*4, x_346);
return x_364;
}
}
}
else
{
uint8_t x_365; 
x_365 = lean_ctor_get_uint8(x_337, sizeof(void*)*4);
if (x_365 == 0)
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; uint8_t x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_366 = lean_ctor_get(x_336, 1);
lean_inc(x_366);
x_367 = lean_ctor_get(x_336, 2);
lean_inc(x_367);
x_368 = lean_ctor_get(x_336, 3);
lean_inc(x_368);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 lean_ctor_release(x_336, 2);
 lean_ctor_release(x_336, 3);
 x_369 = x_336;
} else {
 lean_dec_ref(x_336);
 x_369 = lean_box(0);
}
x_370 = lean_ctor_get(x_337, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_337, 1);
lean_inc(x_371);
x_372 = lean_ctor_get(x_337, 2);
lean_inc(x_372);
x_373 = lean_ctor_get(x_337, 3);
lean_inc(x_373);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 lean_ctor_release(x_337, 2);
 lean_ctor_release(x_337, 3);
 x_374 = x_337;
} else {
 lean_dec_ref(x_337);
 x_374 = lean_box(0);
}
x_375 = 1;
if (lean_is_scalar(x_374)) {
 x_376 = lean_alloc_ctor(1, 4, 1);
} else {
 x_376 = x_374;
}
lean_ctor_set(x_376, 0, x_323);
lean_ctor_set(x_376, 1, x_324);
lean_ctor_set(x_376, 2, x_325);
lean_ctor_set(x_376, 3, x_370);
lean_ctor_set_uint8(x_376, sizeof(void*)*4, x_375);
if (lean_is_scalar(x_369)) {
 x_377 = lean_alloc_ctor(1, 4, 1);
} else {
 x_377 = x_369;
}
lean_ctor_set(x_377, 0, x_373);
lean_ctor_set(x_377, 1, x_366);
lean_ctor_set(x_377, 2, x_367);
lean_ctor_set(x_377, 3, x_368);
lean_ctor_set_uint8(x_377, sizeof(void*)*4, x_375);
x_378 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_378, 0, x_376);
lean_ctor_set(x_378, 1, x_371);
lean_ctor_set(x_378, 2, x_372);
lean_ctor_set(x_378, 3, x_377);
lean_ctor_set_uint8(x_378, sizeof(void*)*4, x_365);
return x_378;
}
else
{
lean_object* x_379; 
x_379 = lean_ctor_get(x_336, 3);
lean_inc(x_379);
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; uint8_t x_383; lean_object* x_384; lean_object* x_385; 
x_380 = lean_ctor_get(x_336, 1);
lean_inc(x_380);
x_381 = lean_ctor_get(x_336, 2);
lean_inc(x_381);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 lean_ctor_release(x_336, 2);
 lean_ctor_release(x_336, 3);
 x_382 = x_336;
} else {
 lean_dec_ref(x_336);
 x_382 = lean_box(0);
}
x_383 = 0;
if (lean_is_scalar(x_382)) {
 x_384 = lean_alloc_ctor(1, 4, 1);
} else {
 x_384 = x_382;
}
lean_ctor_set(x_384, 0, x_337);
lean_ctor_set(x_384, 1, x_380);
lean_ctor_set(x_384, 2, x_381);
lean_ctor_set(x_384, 3, x_379);
lean_ctor_set_uint8(x_384, sizeof(void*)*4, x_383);
x_385 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_385, 0, x_323);
lean_ctor_set(x_385, 1, x_324);
lean_ctor_set(x_385, 2, x_325);
lean_ctor_set(x_385, 3, x_384);
lean_ctor_set_uint8(x_385, sizeof(void*)*4, x_365);
return x_385;
}
else
{
uint8_t x_386; 
x_386 = lean_ctor_get_uint8(x_379, sizeof(void*)*4);
if (x_386 == 0)
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_387 = lean_ctor_get(x_336, 1);
lean_inc(x_387);
x_388 = lean_ctor_get(x_336, 2);
lean_inc(x_388);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 lean_ctor_release(x_336, 2);
 lean_ctor_release(x_336, 3);
 x_389 = x_336;
} else {
 lean_dec_ref(x_336);
 x_389 = lean_box(0);
}
x_390 = lean_ctor_get(x_379, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_379, 1);
lean_inc(x_391);
x_392 = lean_ctor_get(x_379, 2);
lean_inc(x_392);
x_393 = lean_ctor_get(x_379, 3);
lean_inc(x_393);
if (lean_is_exclusive(x_379)) {
 lean_ctor_release(x_379, 0);
 lean_ctor_release(x_379, 1);
 lean_ctor_release(x_379, 2);
 lean_ctor_release(x_379, 3);
 x_394 = x_379;
} else {
 lean_dec_ref(x_379);
 x_394 = lean_box(0);
}
lean_inc(x_337);
if (lean_is_scalar(x_394)) {
 x_395 = lean_alloc_ctor(1, 4, 1);
} else {
 x_395 = x_394;
}
lean_ctor_set(x_395, 0, x_323);
lean_ctor_set(x_395, 1, x_324);
lean_ctor_set(x_395, 2, x_325);
lean_ctor_set(x_395, 3, x_337);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 lean_ctor_release(x_337, 2);
 lean_ctor_release(x_337, 3);
 x_396 = x_337;
} else {
 lean_dec_ref(x_337);
 x_396 = lean_box(0);
}
lean_ctor_set_uint8(x_395, sizeof(void*)*4, x_365);
if (lean_is_scalar(x_396)) {
 x_397 = lean_alloc_ctor(1, 4, 1);
} else {
 x_397 = x_396;
}
lean_ctor_set(x_397, 0, x_390);
lean_ctor_set(x_397, 1, x_391);
lean_ctor_set(x_397, 2, x_392);
lean_ctor_set(x_397, 3, x_393);
lean_ctor_set_uint8(x_397, sizeof(void*)*4, x_365);
if (lean_is_scalar(x_389)) {
 x_398 = lean_alloc_ctor(1, 4, 1);
} else {
 x_398 = x_389;
}
lean_ctor_set(x_398, 0, x_395);
lean_ctor_set(x_398, 1, x_387);
lean_ctor_set(x_398, 2, x_388);
lean_ctor_set(x_398, 3, x_397);
lean_ctor_set_uint8(x_398, sizeof(void*)*4, x_386);
return x_398;
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; uint8_t x_408; lean_object* x_409; lean_object* x_410; 
x_399 = lean_ctor_get(x_336, 1);
lean_inc(x_399);
x_400 = lean_ctor_get(x_336, 2);
lean_inc(x_400);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 lean_ctor_release(x_336, 2);
 lean_ctor_release(x_336, 3);
 x_401 = x_336;
} else {
 lean_dec_ref(x_336);
 x_401 = lean_box(0);
}
x_402 = lean_ctor_get(x_337, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_337, 1);
lean_inc(x_403);
x_404 = lean_ctor_get(x_337, 2);
lean_inc(x_404);
x_405 = lean_ctor_get(x_337, 3);
lean_inc(x_405);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 lean_ctor_release(x_337, 2);
 lean_ctor_release(x_337, 3);
 x_406 = x_337;
} else {
 lean_dec_ref(x_337);
 x_406 = lean_box(0);
}
if (lean_is_scalar(x_406)) {
 x_407 = lean_alloc_ctor(1, 4, 1);
} else {
 x_407 = x_406;
}
lean_ctor_set(x_407, 0, x_402);
lean_ctor_set(x_407, 1, x_403);
lean_ctor_set(x_407, 2, x_404);
lean_ctor_set(x_407, 3, x_405);
lean_ctor_set_uint8(x_407, sizeof(void*)*4, x_386);
x_408 = 0;
if (lean_is_scalar(x_401)) {
 x_409 = lean_alloc_ctor(1, 4, 1);
} else {
 x_409 = x_401;
}
lean_ctor_set(x_409, 0, x_407);
lean_ctor_set(x_409, 1, x_399);
lean_ctor_set(x_409, 2, x_400);
lean_ctor_set(x_409, 3, x_379);
lean_ctor_set_uint8(x_409, sizeof(void*)*4, x_408);
x_410 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_410, 0, x_323);
lean_ctor_set(x_410, 1, x_324);
lean_ctor_set(x_410, 2, x_325);
lean_ctor_set(x_410, 3, x_409);
lean_ctor_set_uint8(x_410, sizeof(void*)*4, x_386);
return x_410;
}
}
}
}
}
}
}
else
{
uint8_t x_411; uint8_t x_412; 
x_411 = l_RBNode_isRed___rarg(x_323);
x_412 = l_coeDecidableEq(x_411);
if (x_412 == 0)
{
lean_object* x_413; lean_object* x_414; 
x_413 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_323, x_2, x_3);
x_414 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_414, 0, x_413);
lean_ctor_set(x_414, 1, x_324);
lean_ctor_set(x_414, 2, x_325);
lean_ctor_set(x_414, 3, x_326);
lean_ctor_set_uint8(x_414, sizeof(void*)*4, x_6);
return x_414;
}
else
{
lean_object* x_415; lean_object* x_416; 
x_415 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_323, x_2, x_3);
x_416 = lean_ctor_get(x_415, 0);
lean_inc(x_416);
if (lean_obj_tag(x_416) == 0)
{
lean_object* x_417; 
x_417 = lean_ctor_get(x_415, 3);
lean_inc(x_417);
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; uint8_t x_421; lean_object* x_422; uint8_t x_423; lean_object* x_424; 
x_418 = lean_ctor_get(x_415, 1);
lean_inc(x_418);
x_419 = lean_ctor_get(x_415, 2);
lean_inc(x_419);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 lean_ctor_release(x_415, 2);
 lean_ctor_release(x_415, 3);
 x_420 = x_415;
} else {
 lean_dec_ref(x_415);
 x_420 = lean_box(0);
}
x_421 = 0;
if (lean_is_scalar(x_420)) {
 x_422 = lean_alloc_ctor(1, 4, 1);
} else {
 x_422 = x_420;
}
lean_ctor_set(x_422, 0, x_417);
lean_ctor_set(x_422, 1, x_418);
lean_ctor_set(x_422, 2, x_419);
lean_ctor_set(x_422, 3, x_417);
lean_ctor_set_uint8(x_422, sizeof(void*)*4, x_421);
x_423 = 1;
x_424 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_424, 0, x_422);
lean_ctor_set(x_424, 1, x_324);
lean_ctor_set(x_424, 2, x_325);
lean_ctor_set(x_424, 3, x_326);
lean_ctor_set_uint8(x_424, sizeof(void*)*4, x_423);
return x_424;
}
else
{
uint8_t x_425; 
x_425 = lean_ctor_get_uint8(x_417, sizeof(void*)*4);
if (x_425 == 0)
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; uint8_t x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_426 = lean_ctor_get(x_415, 1);
lean_inc(x_426);
x_427 = lean_ctor_get(x_415, 2);
lean_inc(x_427);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 lean_ctor_release(x_415, 2);
 lean_ctor_release(x_415, 3);
 x_428 = x_415;
} else {
 lean_dec_ref(x_415);
 x_428 = lean_box(0);
}
x_429 = lean_ctor_get(x_417, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_417, 1);
lean_inc(x_430);
x_431 = lean_ctor_get(x_417, 2);
lean_inc(x_431);
x_432 = lean_ctor_get(x_417, 3);
lean_inc(x_432);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 lean_ctor_release(x_417, 2);
 lean_ctor_release(x_417, 3);
 x_433 = x_417;
} else {
 lean_dec_ref(x_417);
 x_433 = lean_box(0);
}
x_434 = 1;
if (lean_is_scalar(x_433)) {
 x_435 = lean_alloc_ctor(1, 4, 1);
} else {
 x_435 = x_433;
}
lean_ctor_set(x_435, 0, x_416);
lean_ctor_set(x_435, 1, x_426);
lean_ctor_set(x_435, 2, x_427);
lean_ctor_set(x_435, 3, x_429);
lean_ctor_set_uint8(x_435, sizeof(void*)*4, x_434);
if (lean_is_scalar(x_428)) {
 x_436 = lean_alloc_ctor(1, 4, 1);
} else {
 x_436 = x_428;
}
lean_ctor_set(x_436, 0, x_432);
lean_ctor_set(x_436, 1, x_324);
lean_ctor_set(x_436, 2, x_325);
lean_ctor_set(x_436, 3, x_326);
lean_ctor_set_uint8(x_436, sizeof(void*)*4, x_434);
x_437 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_437, 0, x_435);
lean_ctor_set(x_437, 1, x_430);
lean_ctor_set(x_437, 2, x_431);
lean_ctor_set(x_437, 3, x_436);
lean_ctor_set_uint8(x_437, sizeof(void*)*4, x_425);
return x_437;
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; uint8_t x_441; lean_object* x_442; lean_object* x_443; 
x_438 = lean_ctor_get(x_415, 1);
lean_inc(x_438);
x_439 = lean_ctor_get(x_415, 2);
lean_inc(x_439);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 lean_ctor_release(x_415, 2);
 lean_ctor_release(x_415, 3);
 x_440 = x_415;
} else {
 lean_dec_ref(x_415);
 x_440 = lean_box(0);
}
x_441 = 0;
if (lean_is_scalar(x_440)) {
 x_442 = lean_alloc_ctor(1, 4, 1);
} else {
 x_442 = x_440;
}
lean_ctor_set(x_442, 0, x_416);
lean_ctor_set(x_442, 1, x_438);
lean_ctor_set(x_442, 2, x_439);
lean_ctor_set(x_442, 3, x_417);
lean_ctor_set_uint8(x_442, sizeof(void*)*4, x_441);
x_443 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_443, 0, x_442);
lean_ctor_set(x_443, 1, x_324);
lean_ctor_set(x_443, 2, x_325);
lean_ctor_set(x_443, 3, x_326);
lean_ctor_set_uint8(x_443, sizeof(void*)*4, x_425);
return x_443;
}
}
}
else
{
uint8_t x_444; 
x_444 = lean_ctor_get_uint8(x_416, sizeof(void*)*4);
if (x_444 == 0)
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; uint8_t x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; 
x_445 = lean_ctor_get(x_415, 1);
lean_inc(x_445);
x_446 = lean_ctor_get(x_415, 2);
lean_inc(x_446);
x_447 = lean_ctor_get(x_415, 3);
lean_inc(x_447);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 lean_ctor_release(x_415, 2);
 lean_ctor_release(x_415, 3);
 x_448 = x_415;
} else {
 lean_dec_ref(x_415);
 x_448 = lean_box(0);
}
x_449 = lean_ctor_get(x_416, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_416, 1);
lean_inc(x_450);
x_451 = lean_ctor_get(x_416, 2);
lean_inc(x_451);
x_452 = lean_ctor_get(x_416, 3);
lean_inc(x_452);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 lean_ctor_release(x_416, 3);
 x_453 = x_416;
} else {
 lean_dec_ref(x_416);
 x_453 = lean_box(0);
}
x_454 = 1;
if (lean_is_scalar(x_453)) {
 x_455 = lean_alloc_ctor(1, 4, 1);
} else {
 x_455 = x_453;
}
lean_ctor_set(x_455, 0, x_449);
lean_ctor_set(x_455, 1, x_450);
lean_ctor_set(x_455, 2, x_451);
lean_ctor_set(x_455, 3, x_452);
lean_ctor_set_uint8(x_455, sizeof(void*)*4, x_454);
if (lean_is_scalar(x_448)) {
 x_456 = lean_alloc_ctor(1, 4, 1);
} else {
 x_456 = x_448;
}
lean_ctor_set(x_456, 0, x_447);
lean_ctor_set(x_456, 1, x_324);
lean_ctor_set(x_456, 2, x_325);
lean_ctor_set(x_456, 3, x_326);
lean_ctor_set_uint8(x_456, sizeof(void*)*4, x_454);
x_457 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_457, 0, x_455);
lean_ctor_set(x_457, 1, x_445);
lean_ctor_set(x_457, 2, x_446);
lean_ctor_set(x_457, 3, x_456);
lean_ctor_set_uint8(x_457, sizeof(void*)*4, x_444);
return x_457;
}
else
{
lean_object* x_458; 
x_458 = lean_ctor_get(x_415, 3);
lean_inc(x_458);
if (lean_obj_tag(x_458) == 0)
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; uint8_t x_462; lean_object* x_463; lean_object* x_464; 
x_459 = lean_ctor_get(x_415, 1);
lean_inc(x_459);
x_460 = lean_ctor_get(x_415, 2);
lean_inc(x_460);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 lean_ctor_release(x_415, 2);
 lean_ctor_release(x_415, 3);
 x_461 = x_415;
} else {
 lean_dec_ref(x_415);
 x_461 = lean_box(0);
}
x_462 = 0;
if (lean_is_scalar(x_461)) {
 x_463 = lean_alloc_ctor(1, 4, 1);
} else {
 x_463 = x_461;
}
lean_ctor_set(x_463, 0, x_416);
lean_ctor_set(x_463, 1, x_459);
lean_ctor_set(x_463, 2, x_460);
lean_ctor_set(x_463, 3, x_458);
lean_ctor_set_uint8(x_463, sizeof(void*)*4, x_462);
x_464 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_464, 0, x_463);
lean_ctor_set(x_464, 1, x_324);
lean_ctor_set(x_464, 2, x_325);
lean_ctor_set(x_464, 3, x_326);
lean_ctor_set_uint8(x_464, sizeof(void*)*4, x_444);
return x_464;
}
else
{
uint8_t x_465; 
x_465 = lean_ctor_get_uint8(x_458, sizeof(void*)*4);
if (x_465 == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; 
x_466 = lean_ctor_get(x_415, 1);
lean_inc(x_466);
x_467 = lean_ctor_get(x_415, 2);
lean_inc(x_467);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 lean_ctor_release(x_415, 2);
 lean_ctor_release(x_415, 3);
 x_468 = x_415;
} else {
 lean_dec_ref(x_415);
 x_468 = lean_box(0);
}
x_469 = lean_ctor_get(x_458, 0);
lean_inc(x_469);
x_470 = lean_ctor_get(x_458, 1);
lean_inc(x_470);
x_471 = lean_ctor_get(x_458, 2);
lean_inc(x_471);
x_472 = lean_ctor_get(x_458, 3);
lean_inc(x_472);
if (lean_is_exclusive(x_458)) {
 lean_ctor_release(x_458, 0);
 lean_ctor_release(x_458, 1);
 lean_ctor_release(x_458, 2);
 lean_ctor_release(x_458, 3);
 x_473 = x_458;
} else {
 lean_dec_ref(x_458);
 x_473 = lean_box(0);
}
lean_inc(x_416);
if (lean_is_scalar(x_473)) {
 x_474 = lean_alloc_ctor(1, 4, 1);
} else {
 x_474 = x_473;
}
lean_ctor_set(x_474, 0, x_416);
lean_ctor_set(x_474, 1, x_466);
lean_ctor_set(x_474, 2, x_467);
lean_ctor_set(x_474, 3, x_469);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 lean_ctor_release(x_416, 3);
 x_475 = x_416;
} else {
 lean_dec_ref(x_416);
 x_475 = lean_box(0);
}
lean_ctor_set_uint8(x_474, sizeof(void*)*4, x_444);
if (lean_is_scalar(x_475)) {
 x_476 = lean_alloc_ctor(1, 4, 1);
} else {
 x_476 = x_475;
}
lean_ctor_set(x_476, 0, x_472);
lean_ctor_set(x_476, 1, x_324);
lean_ctor_set(x_476, 2, x_325);
lean_ctor_set(x_476, 3, x_326);
lean_ctor_set_uint8(x_476, sizeof(void*)*4, x_444);
if (lean_is_scalar(x_468)) {
 x_477 = lean_alloc_ctor(1, 4, 1);
} else {
 x_477 = x_468;
}
lean_ctor_set(x_477, 0, x_474);
lean_ctor_set(x_477, 1, x_470);
lean_ctor_set(x_477, 2, x_471);
lean_ctor_set(x_477, 3, x_476);
lean_ctor_set_uint8(x_477, sizeof(void*)*4, x_465);
return x_477;
}
else
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; uint8_t x_487; lean_object* x_488; lean_object* x_489; 
x_478 = lean_ctor_get(x_415, 1);
lean_inc(x_478);
x_479 = lean_ctor_get(x_415, 2);
lean_inc(x_479);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 lean_ctor_release(x_415, 2);
 lean_ctor_release(x_415, 3);
 x_480 = x_415;
} else {
 lean_dec_ref(x_415);
 x_480 = lean_box(0);
}
x_481 = lean_ctor_get(x_416, 0);
lean_inc(x_481);
x_482 = lean_ctor_get(x_416, 1);
lean_inc(x_482);
x_483 = lean_ctor_get(x_416, 2);
lean_inc(x_483);
x_484 = lean_ctor_get(x_416, 3);
lean_inc(x_484);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 lean_ctor_release(x_416, 3);
 x_485 = x_416;
} else {
 lean_dec_ref(x_416);
 x_485 = lean_box(0);
}
if (lean_is_scalar(x_485)) {
 x_486 = lean_alloc_ctor(1, 4, 1);
} else {
 x_486 = x_485;
}
lean_ctor_set(x_486, 0, x_481);
lean_ctor_set(x_486, 1, x_482);
lean_ctor_set(x_486, 2, x_483);
lean_ctor_set(x_486, 3, x_484);
lean_ctor_set_uint8(x_486, sizeof(void*)*4, x_465);
x_487 = 0;
if (lean_is_scalar(x_480)) {
 x_488 = lean_alloc_ctor(1, 4, 1);
} else {
 x_488 = x_480;
}
lean_ctor_set(x_488, 0, x_486);
lean_ctor_set(x_488, 1, x_478);
lean_ctor_set(x_488, 2, x_479);
lean_ctor_set(x_488, 3, x_458);
lean_ctor_set_uint8(x_488, sizeof(void*)*4, x_487);
x_489 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_489, 0, x_488);
lean_ctor_set(x_489, 1, x_324);
lean_ctor_set(x_489, 2, x_325);
lean_ctor_set(x_489, 3, x_326);
lean_ctor_set_uint8(x_489, sizeof(void*)*4, x_465);
return x_489;
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
uint8_t x_4; uint8_t x_5; 
x_4 = l_RBNode_isRed___rarg(x_1);
x_5 = l_coeDecidableEq(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_1, x_2, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_RBNode_ins___main___at_Lean_IR_LocalContext_addLocal___spec__2(x_1, x_2, x_3);
x_8 = l_RBNode_setBlack___rarg(x_7);
return x_8;
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_nat_dec_lt(x_2, x_5);
x_9 = l_coeDecidableEq(x_8);
if (x_9 == 0)
{
uint8_t x_10; uint8_t x_11; 
x_10 = lean_nat_dec_lt(x_5, x_2);
x_11 = l_coeDecidableEq(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_inc(x_6);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_6);
return x_12;
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get(x_2, 3);
x_8 = lean_nat_dec_lt(x_1, x_5);
x_9 = l_coeDecidableEq(x_8);
if (x_9 == 0)
{
uint8_t x_10; uint8_t x_11; 
x_10 = lean_nat_dec_lt(x_5, x_1);
x_11 = l_coeDecidableEq(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_free_object(x_2);
lean_dec(x_6);
lean_dec(x_5);
x_12 = l_RBNode_appendTrees___main___rarg(x_4, x_7);
return x_12;
}
else
{
uint8_t x_13; uint8_t x_14; 
x_13 = l_RBNode_isBlack___rarg(x_7);
x_14 = l_coeDecidableEq(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = l_RBNode_del___main___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(x_1, x_7);
x_16 = 0;
lean_ctor_set(x_2, 3, x_15);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_16);
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
uint8_t x_19; uint8_t x_20; 
x_19 = l_RBNode_isBlack___rarg(x_4);
x_20 = l_coeDecidableEq(x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = l_RBNode_del___main___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(x_1, x_4);
x_22 = 0;
lean_ctor_set(x_2, 0, x_21);
lean_ctor_set_uint8(x_2, sizeof(void*)*4, x_22);
return x_2;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_free_object(x_2);
x_23 = l_RBNode_del___main___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(x_1, x_4);
x_24 = l_RBNode_balLeft___rarg(x_23, x_5, x_6, x_7);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_ctor_get(x_2, 2);
x_28 = lean_ctor_get(x_2, 3);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_2);
x_29 = lean_nat_dec_lt(x_1, x_26);
x_30 = l_coeDecidableEq(x_29);
if (x_30 == 0)
{
uint8_t x_31; uint8_t x_32; 
x_31 = lean_nat_dec_lt(x_26, x_1);
x_32 = l_coeDecidableEq(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_27);
lean_dec(x_26);
x_33 = l_RBNode_appendTrees___main___rarg(x_25, x_28);
return x_33;
}
else
{
uint8_t x_34; uint8_t x_35; 
x_34 = l_RBNode_isBlack___rarg(x_28);
x_35 = l_coeDecidableEq(x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_36 = l_RBNode_del___main___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(x_1, x_28);
x_37 = 0;
x_38 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_38, 0, x_25);
lean_ctor_set(x_38, 1, x_26);
lean_ctor_set(x_38, 2, x_27);
lean_ctor_set(x_38, 3, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*4, x_37);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = l_RBNode_del___main___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(x_1, x_28);
x_40 = l_RBNode_balRight___rarg(x_25, x_26, x_27, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; uint8_t x_42; 
x_41 = l_RBNode_isBlack___rarg(x_25);
x_42 = l_coeDecidableEq(x_41);
if (x_42 == 0)
{
lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_43 = l_RBNode_del___main___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(x_1, x_25);
x_44 = 0;
x_45 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_26);
lean_ctor_set(x_45, 2, x_27);
lean_ctor_set(x_45, 3, x_28);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_44);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = l_RBNode_del___main___at_Lean_IR_LocalContext_eraseJoinPointDecl___spec__2(x_1, x_25);
x_47 = l_RBNode_balLeft___rarg(x_46, x_26, x_27, x_28);
return x_47;
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_1, 3);
x_8 = lean_nat_dec_lt(x_2, x_5);
x_9 = l_coeDecidableEq(x_8);
if (x_9 == 0)
{
uint8_t x_10; uint8_t x_11; 
x_10 = lean_nat_dec_lt(x_5, x_2);
x_11 = l_coeDecidableEq(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_inc(x_6);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_6);
return x_12;
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 3);
x_12 = lean_nat_dec_lt(x_2, x_9);
x_13 = l_coeDecidableEq(x_12);
if (x_13 == 0)
{
uint8_t x_14; uint8_t x_15; 
x_14 = lean_nat_dec_lt(x_9, x_2);
x_15 = l_coeDecidableEq(x_14);
if (x_15 == 0)
{
lean_dec(x_10);
lean_dec(x_9);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
lean_object* x_16; 
x_16 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_11, x_2, x_3);
lean_ctor_set(x_1, 3, x_16);
return x_1;
}
}
else
{
lean_object* x_17; 
x_17 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_8, x_2, x_3);
lean_ctor_set(x_1, 0, x_17);
return x_1;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_ctor_get(x_1, 2);
x_21 = lean_ctor_get(x_1, 3);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_1);
x_22 = lean_nat_dec_lt(x_2, x_19);
x_23 = l_coeDecidableEq(x_22);
if (x_23 == 0)
{
uint8_t x_24; uint8_t x_25; 
x_24 = lean_nat_dec_lt(x_19, x_2);
x_25 = l_coeDecidableEq(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_20);
lean_dec(x_19);
x_26 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_2);
lean_ctor_set(x_26, 2, x_3);
lean_ctor_set(x_26, 3, x_21);
lean_ctor_set_uint8(x_26, sizeof(void*)*4, x_6);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_21, x_2, x_3);
x_28 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_28, 0, x_18);
lean_ctor_set(x_28, 1, x_19);
lean_ctor_set(x_28, 2, x_20);
lean_ctor_set(x_28, 3, x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*4, x_6);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_18, x_2, x_3);
x_30 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_19);
lean_ctor_set(x_30, 2, x_20);
lean_ctor_set(x_30, 3, x_21);
lean_ctor_set_uint8(x_30, sizeof(void*)*4, x_6);
return x_30;
}
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_1);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; 
x_32 = lean_ctor_get(x_1, 0);
x_33 = lean_ctor_get(x_1, 1);
x_34 = lean_ctor_get(x_1, 2);
x_35 = lean_ctor_get(x_1, 3);
x_36 = lean_nat_dec_lt(x_2, x_33);
x_37 = l_coeDecidableEq(x_36);
if (x_37 == 0)
{
uint8_t x_38; uint8_t x_39; 
x_38 = lean_nat_dec_lt(x_33, x_2);
x_39 = l_coeDecidableEq(x_38);
if (x_39 == 0)
{
lean_dec(x_34);
lean_dec(x_33);
lean_ctor_set(x_1, 2, x_3);
lean_ctor_set(x_1, 1, x_2);
return x_1;
}
else
{
uint8_t x_40; uint8_t x_41; 
x_40 = l_RBNode_isRed___rarg(x_35);
x_41 = l_coeDecidableEq(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_35, x_2, x_3);
lean_ctor_set(x_1, 3, x_42);
return x_1;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_35, x_2, x_3);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_43, 3);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_43);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; 
x_47 = lean_ctor_get(x_43, 3);
lean_dec(x_47);
x_48 = lean_ctor_get(x_43, 0);
lean_dec(x_48);
x_49 = 0;
lean_ctor_set(x_43, 0, x_45);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_49);
x_50 = 1;
lean_ctor_set(x_1, 3, x_43);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_50);
return x_1;
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; uint8_t x_55; 
x_51 = lean_ctor_get(x_43, 1);
x_52 = lean_ctor_get(x_43, 2);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_43);
x_53 = 0;
x_54 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_54, 0, x_45);
lean_ctor_set(x_54, 1, x_51);
lean_ctor_set(x_54, 2, x_52);
lean_ctor_set(x_54, 3, x_45);
lean_ctor_set_uint8(x_54, sizeof(void*)*4, x_53);
x_55 = 1;
lean_ctor_set(x_1, 3, x_54);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_55);
return x_1;
}
}
else
{
uint8_t x_56; 
x_56 = lean_ctor_get_uint8(x_45, sizeof(void*)*4);
if (x_56 == 0)
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_43);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_58 = lean_ctor_get(x_43, 1);
x_59 = lean_ctor_get(x_43, 2);
x_60 = lean_ctor_get(x_43, 3);
lean_dec(x_60);
x_61 = lean_ctor_get(x_43, 0);
lean_dec(x_61);
x_62 = !lean_is_exclusive(x_45);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_63 = lean_ctor_get(x_45, 0);
x_64 = lean_ctor_get(x_45, 1);
x_65 = lean_ctor_get(x_45, 2);
x_66 = lean_ctor_get(x_45, 3);
x_67 = 1;
lean_ctor_set(x_45, 3, x_44);
lean_ctor_set(x_45, 2, x_34);
lean_ctor_set(x_45, 1, x_33);
lean_ctor_set(x_45, 0, x_32);
lean_ctor_set_uint8(x_45, sizeof(void*)*4, x_67);
lean_ctor_set(x_43, 3, x_66);
lean_ctor_set(x_43, 2, x_65);
lean_ctor_set(x_43, 1, x_64);
lean_ctor_set(x_43, 0, x_63);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_67);
lean_ctor_set(x_1, 3, x_43);
lean_ctor_set(x_1, 2, x_59);
lean_ctor_set(x_1, 1, x_58);
lean_ctor_set(x_1, 0, x_45);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_56);
return x_1;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_45, 0);
x_69 = lean_ctor_get(x_45, 1);
x_70 = lean_ctor_get(x_45, 2);
x_71 = lean_ctor_get(x_45, 3);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_45);
x_72 = 1;
x_73 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_73, 0, x_32);
lean_ctor_set(x_73, 1, x_33);
lean_ctor_set(x_73, 2, x_34);
lean_ctor_set(x_73, 3, x_44);
lean_ctor_set_uint8(x_73, sizeof(void*)*4, x_72);
lean_ctor_set(x_43, 3, x_71);
lean_ctor_set(x_43, 2, x_70);
lean_ctor_set(x_43, 1, x_69);
lean_ctor_set(x_43, 0, x_68);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_72);
lean_ctor_set(x_1, 3, x_43);
lean_ctor_set(x_1, 2, x_59);
lean_ctor_set(x_1, 1, x_58);
lean_ctor_set(x_1, 0, x_73);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_56);
return x_1;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; 
x_74 = lean_ctor_get(x_43, 1);
x_75 = lean_ctor_get(x_43, 2);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_43);
x_76 = lean_ctor_get(x_45, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_45, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_45, 2);
lean_inc(x_78);
x_79 = lean_ctor_get(x_45, 3);
lean_inc(x_79);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 lean_ctor_release(x_45, 2);
 lean_ctor_release(x_45, 3);
 x_80 = x_45;
} else {
 lean_dec_ref(x_45);
 x_80 = lean_box(0);
}
x_81 = 1;
if (lean_is_scalar(x_80)) {
 x_82 = lean_alloc_ctor(1, 4, 1);
} else {
 x_82 = x_80;
}
lean_ctor_set(x_82, 0, x_32);
lean_ctor_set(x_82, 1, x_33);
lean_ctor_set(x_82, 2, x_34);
lean_ctor_set(x_82, 3, x_44);
lean_ctor_set_uint8(x_82, sizeof(void*)*4, x_81);
x_83 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_83, 0, x_76);
lean_ctor_set(x_83, 1, x_77);
lean_ctor_set(x_83, 2, x_78);
lean_ctor_set(x_83, 3, x_79);
lean_ctor_set_uint8(x_83, sizeof(void*)*4, x_81);
lean_ctor_set(x_1, 3, x_83);
lean_ctor_set(x_1, 2, x_75);
lean_ctor_set(x_1, 1, x_74);
lean_ctor_set(x_1, 0, x_82);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_56);
return x_1;
}
}
else
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_43);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_ctor_get(x_43, 3);
lean_dec(x_85);
x_86 = lean_ctor_get(x_43, 0);
lean_dec(x_86);
x_87 = 0;
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_87);
lean_ctor_set(x_1, 3, x_43);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_56);
return x_1;
}
else
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_43, 1);
x_89 = lean_ctor_get(x_43, 2);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_43);
x_90 = 0;
x_91 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_91, 0, x_44);
lean_ctor_set(x_91, 1, x_88);
lean_ctor_set(x_91, 2, x_89);
lean_ctor_set(x_91, 3, x_45);
lean_ctor_set_uint8(x_91, sizeof(void*)*4, x_90);
lean_ctor_set(x_1, 3, x_91);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_56);
return x_1;
}
}
}
}
else
{
uint8_t x_92; 
x_92 = lean_ctor_get_uint8(x_44, sizeof(void*)*4);
if (x_92 == 0)
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_43);
if (x_93 == 0)
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_ctor_get(x_43, 0);
lean_dec(x_94);
x_95 = !lean_is_exclusive(x_44);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_96 = lean_ctor_get(x_44, 0);
x_97 = lean_ctor_get(x_44, 1);
x_98 = lean_ctor_get(x_44, 2);
x_99 = lean_ctor_get(x_44, 3);
x_100 = 1;
lean_ctor_set(x_44, 3, x_96);
lean_ctor_set(x_44, 2, x_34);
lean_ctor_set(x_44, 1, x_33);
lean_ctor_set(x_44, 0, x_32);
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_100);
lean_ctor_set(x_43, 0, x_99);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_100);
lean_ctor_set(x_1, 3, x_43);
lean_ctor_set(x_1, 2, x_98);
lean_ctor_set(x_1, 1, x_97);
lean_ctor_set(x_1, 0, x_44);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_92);
return x_1;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; 
x_101 = lean_ctor_get(x_44, 0);
x_102 = lean_ctor_get(x_44, 1);
x_103 = lean_ctor_get(x_44, 2);
x_104 = lean_ctor_get(x_44, 3);
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_44);
x_105 = 1;
x_106 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_106, 0, x_32);
lean_ctor_set(x_106, 1, x_33);
lean_ctor_set(x_106, 2, x_34);
lean_ctor_set(x_106, 3, x_101);
lean_ctor_set_uint8(x_106, sizeof(void*)*4, x_105);
lean_ctor_set(x_43, 0, x_104);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_105);
lean_ctor_set(x_1, 3, x_43);
lean_ctor_set(x_1, 2, x_103);
lean_ctor_set(x_1, 1, x_102);
lean_ctor_set(x_1, 0, x_106);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_92);
return x_1;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; 
x_107 = lean_ctor_get(x_43, 1);
x_108 = lean_ctor_get(x_43, 2);
x_109 = lean_ctor_get(x_43, 3);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_43);
x_110 = lean_ctor_get(x_44, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_44, 1);
lean_inc(x_111);
x_112 = lean_ctor_get(x_44, 2);
lean_inc(x_112);
x_113 = lean_ctor_get(x_44, 3);
lean_inc(x_113);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 lean_ctor_release(x_44, 3);
 x_114 = x_44;
} else {
 lean_dec_ref(x_44);
 x_114 = lean_box(0);
}
x_115 = 1;
if (lean_is_scalar(x_114)) {
 x_116 = lean_alloc_ctor(1, 4, 1);
} else {
 x_116 = x_114;
}
lean_ctor_set(x_116, 0, x_32);
lean_ctor_set(x_116, 1, x_33);
lean_ctor_set(x_116, 2, x_34);
lean_ctor_set(x_116, 3, x_110);
lean_ctor_set_uint8(x_116, sizeof(void*)*4, x_115);
x_117 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_117, 0, x_113);
lean_ctor_set(x_117, 1, x_107);
lean_ctor_set(x_117, 2, x_108);
lean_ctor_set(x_117, 3, x_109);
lean_ctor_set_uint8(x_117, sizeof(void*)*4, x_115);
lean_ctor_set(x_1, 3, x_117);
lean_ctor_set(x_1, 2, x_112);
lean_ctor_set(x_1, 1, x_111);
lean_ctor_set(x_1, 0, x_116);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_92);
return x_1;
}
}
else
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_43, 3);
lean_inc(x_118);
if (lean_obj_tag(x_118) == 0)
{
uint8_t x_119; 
x_119 = !lean_is_exclusive(x_43);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_120 = lean_ctor_get(x_43, 3);
lean_dec(x_120);
x_121 = lean_ctor_get(x_43, 0);
lean_dec(x_121);
x_122 = 0;
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_122);
lean_ctor_set(x_1, 3, x_43);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_92);
return x_1;
}
else
{
lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_43, 1);
x_124 = lean_ctor_get(x_43, 2);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_43);
x_125 = 0;
x_126 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_126, 0, x_44);
lean_ctor_set(x_126, 1, x_123);
lean_ctor_set(x_126, 2, x_124);
lean_ctor_set(x_126, 3, x_118);
lean_ctor_set_uint8(x_126, sizeof(void*)*4, x_125);
lean_ctor_set(x_1, 3, x_126);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_92);
return x_1;
}
}
else
{
uint8_t x_127; 
x_127 = lean_ctor_get_uint8(x_118, sizeof(void*)*4);
if (x_127 == 0)
{
uint8_t x_128; 
lean_free_object(x_1);
x_128 = !lean_is_exclusive(x_43);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_129 = lean_ctor_get(x_43, 3);
lean_dec(x_129);
x_130 = lean_ctor_get(x_43, 0);
lean_dec(x_130);
x_131 = !lean_is_exclusive(x_118);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_132 = lean_ctor_get(x_118, 0);
x_133 = lean_ctor_get(x_118, 1);
x_134 = lean_ctor_get(x_118, 2);
x_135 = lean_ctor_get(x_118, 3);
lean_inc(x_44);
lean_ctor_set(x_118, 3, x_44);
lean_ctor_set(x_118, 2, x_34);
lean_ctor_set(x_118, 1, x_33);
lean_ctor_set(x_118, 0, x_32);
x_136 = !lean_is_exclusive(x_44);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_137 = lean_ctor_get(x_44, 3);
lean_dec(x_137);
x_138 = lean_ctor_get(x_44, 2);
lean_dec(x_138);
x_139 = lean_ctor_get(x_44, 1);
lean_dec(x_139);
x_140 = lean_ctor_get(x_44, 0);
lean_dec(x_140);
lean_ctor_set_uint8(x_118, sizeof(void*)*4, x_92);
lean_ctor_set(x_44, 3, x_135);
lean_ctor_set(x_44, 2, x_134);
lean_ctor_set(x_44, 1, x_133);
lean_ctor_set(x_44, 0, x_132);
lean_ctor_set(x_43, 3, x_44);
lean_ctor_set(x_43, 0, x_118);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_127);
return x_43;
}
else
{
lean_object* x_141; 
lean_dec(x_44);
lean_ctor_set_uint8(x_118, sizeof(void*)*4, x_92);
x_141 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_141, 0, x_132);
lean_ctor_set(x_141, 1, x_133);
lean_ctor_set(x_141, 2, x_134);
lean_ctor_set(x_141, 3, x_135);
lean_ctor_set_uint8(x_141, sizeof(void*)*4, x_92);
lean_ctor_set(x_43, 3, x_141);
lean_ctor_set(x_43, 0, x_118);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_127);
return x_43;
}
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_142 = lean_ctor_get(x_118, 0);
x_143 = lean_ctor_get(x_118, 1);
x_144 = lean_ctor_get(x_118, 2);
x_145 = lean_ctor_get(x_118, 3);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_118);
lean_inc(x_44);
x_146 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_146, 0, x_32);
lean_ctor_set(x_146, 1, x_33);
lean_ctor_set(x_146, 2, x_34);
lean_ctor_set(x_146, 3, x_44);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 lean_ctor_release(x_44, 3);
 x_147 = x_44;
} else {
 lean_dec_ref(x_44);
 x_147 = lean_box(0);
}
lean_ctor_set_uint8(x_146, sizeof(void*)*4, x_92);
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 4, 1);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_142);
lean_ctor_set(x_148, 1, x_143);
lean_ctor_set(x_148, 2, x_144);
lean_ctor_set(x_148, 3, x_145);
lean_ctor_set_uint8(x_148, sizeof(void*)*4, x_92);
lean_ctor_set(x_43, 3, x_148);
lean_ctor_set(x_43, 0, x_146);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_127);
return x_43;
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_149 = lean_ctor_get(x_43, 1);
x_150 = lean_ctor_get(x_43, 2);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_43);
x_151 = lean_ctor_get(x_118, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_118, 1);
lean_inc(x_152);
x_153 = lean_ctor_get(x_118, 2);
lean_inc(x_153);
x_154 = lean_ctor_get(x_118, 3);
lean_inc(x_154);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 lean_ctor_release(x_118, 2);
 lean_ctor_release(x_118, 3);
 x_155 = x_118;
} else {
 lean_dec_ref(x_118);
 x_155 = lean_box(0);
}
lean_inc(x_44);
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(1, 4, 1);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_32);
lean_ctor_set(x_156, 1, x_33);
lean_ctor_set(x_156, 2, x_34);
lean_ctor_set(x_156, 3, x_44);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 lean_ctor_release(x_44, 3);
 x_157 = x_44;
} else {
 lean_dec_ref(x_44);
 x_157 = lean_box(0);
}
lean_ctor_set_uint8(x_156, sizeof(void*)*4, x_92);
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 4, 1);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_151);
lean_ctor_set(x_158, 1, x_152);
lean_ctor_set(x_158, 2, x_153);
lean_ctor_set(x_158, 3, x_154);
lean_ctor_set_uint8(x_158, sizeof(void*)*4, x_92);
x_159 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_149);
lean_ctor_set(x_159, 2, x_150);
lean_ctor_set(x_159, 3, x_158);
lean_ctor_set_uint8(x_159, sizeof(void*)*4, x_127);
return x_159;
}
}
else
{
uint8_t x_160; 
x_160 = !lean_is_exclusive(x_43);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_161 = lean_ctor_get(x_43, 3);
lean_dec(x_161);
x_162 = lean_ctor_get(x_43, 0);
lean_dec(x_162);
x_163 = !lean_is_exclusive(x_44);
if (x_163 == 0)
{
uint8_t x_164; 
lean_ctor_set_uint8(x_44, sizeof(void*)*4, x_127);
x_164 = 0;
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_164);
lean_ctor_set(x_1, 3, x_43);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_127);
return x_1;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_165 = lean_ctor_get(x_44, 0);
x_166 = lean_ctor_get(x_44, 1);
x_167 = lean_ctor_get(x_44, 2);
x_168 = lean_ctor_get(x_44, 3);
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_44);
x_169 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_169, 0, x_165);
lean_ctor_set(x_169, 1, x_166);
lean_ctor_set(x_169, 2, x_167);
lean_ctor_set(x_169, 3, x_168);
lean_ctor_set_uint8(x_169, sizeof(void*)*4, x_127);
x_170 = 0;
lean_ctor_set(x_43, 0, x_169);
lean_ctor_set_uint8(x_43, sizeof(void*)*4, x_170);
lean_ctor_set(x_1, 3, x_43);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_127);
return x_1;
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; lean_object* x_180; 
x_171 = lean_ctor_get(x_43, 1);
x_172 = lean_ctor_get(x_43, 2);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_43);
x_173 = lean_ctor_get(x_44, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_44, 1);
lean_inc(x_174);
x_175 = lean_ctor_get(x_44, 2);
lean_inc(x_175);
x_176 = lean_ctor_get(x_44, 3);
lean_inc(x_176);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 lean_ctor_release(x_44, 2);
 lean_ctor_release(x_44, 3);
 x_177 = x_44;
} else {
 lean_dec_ref(x_44);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(1, 4, 1);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_173);
lean_ctor_set(x_178, 1, x_174);
lean_ctor_set(x_178, 2, x_175);
lean_ctor_set(x_178, 3, x_176);
lean_ctor_set_uint8(x_178, sizeof(void*)*4, x_127);
x_179 = 0;
x_180 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_171);
lean_ctor_set(x_180, 2, x_172);
lean_ctor_set(x_180, 3, x_118);
lean_ctor_set_uint8(x_180, sizeof(void*)*4, x_179);
lean_ctor_set(x_1, 3, x_180);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_127);
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
uint8_t x_181; uint8_t x_182; 
x_181 = l_RBNode_isRed___rarg(x_32);
x_182 = l_coeDecidableEq(x_181);
if (x_182 == 0)
{
lean_object* x_183; 
x_183 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_32, x_2, x_3);
lean_ctor_set(x_1, 0, x_183);
return x_1;
}
else
{
lean_object* x_184; lean_object* x_185; 
x_184 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_32, x_2, x_3);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; 
x_186 = lean_ctor_get(x_184, 3);
lean_inc(x_186);
if (lean_obj_tag(x_186) == 0)
{
uint8_t x_187; 
x_187 = !lean_is_exclusive(x_184);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; uint8_t x_190; uint8_t x_191; 
x_188 = lean_ctor_get(x_184, 3);
lean_dec(x_188);
x_189 = lean_ctor_get(x_184, 0);
lean_dec(x_189);
x_190 = 0;
lean_ctor_set(x_184, 0, x_186);
lean_ctor_set_uint8(x_184, sizeof(void*)*4, x_190);
x_191 = 1;
lean_ctor_set(x_1, 0, x_184);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_191);
return x_1;
}
else
{
lean_object* x_192; lean_object* x_193; uint8_t x_194; lean_object* x_195; uint8_t x_196; 
x_192 = lean_ctor_get(x_184, 1);
x_193 = lean_ctor_get(x_184, 2);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_184);
x_194 = 0;
x_195 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_195, 0, x_186);
lean_ctor_set(x_195, 1, x_192);
lean_ctor_set(x_195, 2, x_193);
lean_ctor_set(x_195, 3, x_186);
lean_ctor_set_uint8(x_195, sizeof(void*)*4, x_194);
x_196 = 1;
lean_ctor_set(x_1, 0, x_195);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_196);
return x_1;
}
}
else
{
uint8_t x_197; 
x_197 = lean_ctor_get_uint8(x_186, sizeof(void*)*4);
if (x_197 == 0)
{
uint8_t x_198; 
x_198 = !lean_is_exclusive(x_184);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; 
x_199 = lean_ctor_get(x_184, 1);
x_200 = lean_ctor_get(x_184, 2);
x_201 = lean_ctor_get(x_184, 3);
lean_dec(x_201);
x_202 = lean_ctor_get(x_184, 0);
lean_dec(x_202);
x_203 = !lean_is_exclusive(x_186);
if (x_203 == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; 
x_204 = lean_ctor_get(x_186, 0);
x_205 = lean_ctor_get(x_186, 1);
x_206 = lean_ctor_get(x_186, 2);
x_207 = lean_ctor_get(x_186, 3);
x_208 = 1;
lean_ctor_set(x_186, 3, x_204);
lean_ctor_set(x_186, 2, x_200);
lean_ctor_set(x_186, 1, x_199);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set_uint8(x_186, sizeof(void*)*4, x_208);
lean_ctor_set(x_184, 3, x_35);
lean_ctor_set(x_184, 2, x_34);
lean_ctor_set(x_184, 1, x_33);
lean_ctor_set(x_184, 0, x_207);
lean_ctor_set_uint8(x_184, sizeof(void*)*4, x_208);
lean_ctor_set(x_1, 3, x_184);
lean_ctor_set(x_1, 2, x_206);
lean_ctor_set(x_1, 1, x_205);
lean_ctor_set(x_1, 0, x_186);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_197);
return x_1;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; lean_object* x_214; 
x_209 = lean_ctor_get(x_186, 0);
x_210 = lean_ctor_get(x_186, 1);
x_211 = lean_ctor_get(x_186, 2);
x_212 = lean_ctor_get(x_186, 3);
lean_inc(x_212);
lean_inc(x_211);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_186);
x_213 = 1;
x_214 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_214, 0, x_185);
lean_ctor_set(x_214, 1, x_199);
lean_ctor_set(x_214, 2, x_200);
lean_ctor_set(x_214, 3, x_209);
lean_ctor_set_uint8(x_214, sizeof(void*)*4, x_213);
lean_ctor_set(x_184, 3, x_35);
lean_ctor_set(x_184, 2, x_34);
lean_ctor_set(x_184, 1, x_33);
lean_ctor_set(x_184, 0, x_212);
lean_ctor_set_uint8(x_184, sizeof(void*)*4, x_213);
lean_ctor_set(x_1, 3, x_184);
lean_ctor_set(x_1, 2, x_211);
lean_ctor_set(x_1, 1, x_210);
lean_ctor_set(x_1, 0, x_214);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_197);
return x_1;
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; lean_object* x_223; lean_object* x_224; 
x_215 = lean_ctor_get(x_184, 1);
x_216 = lean_ctor_get(x_184, 2);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_184);
x_217 = lean_ctor_get(x_186, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_186, 1);
lean_inc(x_218);
x_219 = lean_ctor_get(x_186, 2);
lean_inc(x_219);
x_220 = lean_ctor_get(x_186, 3);
lean_inc(x_220);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 lean_ctor_release(x_186, 2);
 lean_ctor_release(x_186, 3);
 x_221 = x_186;
} else {
 lean_dec_ref(x_186);
 x_221 = lean_box(0);
}
x_222 = 1;
if (lean_is_scalar(x_221)) {
 x_223 = lean_alloc_ctor(1, 4, 1);
} else {
 x_223 = x_221;
}
lean_ctor_set(x_223, 0, x_185);
lean_ctor_set(x_223, 1, x_215);
lean_ctor_set(x_223, 2, x_216);
lean_ctor_set(x_223, 3, x_217);
lean_ctor_set_uint8(x_223, sizeof(void*)*4, x_222);
x_224 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_224, 0, x_220);
lean_ctor_set(x_224, 1, x_33);
lean_ctor_set(x_224, 2, x_34);
lean_ctor_set(x_224, 3, x_35);
lean_ctor_set_uint8(x_224, sizeof(void*)*4, x_222);
lean_ctor_set(x_1, 3, x_224);
lean_ctor_set(x_1, 2, x_219);
lean_ctor_set(x_1, 1, x_218);
lean_ctor_set(x_1, 0, x_223);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_197);
return x_1;
}
}
else
{
uint8_t x_225; 
x_225 = !lean_is_exclusive(x_184);
if (x_225 == 0)
{
lean_object* x_226; lean_object* x_227; uint8_t x_228; 
x_226 = lean_ctor_get(x_184, 3);
lean_dec(x_226);
x_227 = lean_ctor_get(x_184, 0);
lean_dec(x_227);
x_228 = 0;
lean_ctor_set_uint8(x_184, sizeof(void*)*4, x_228);
lean_ctor_set(x_1, 0, x_184);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_197);
return x_1;
}
else
{
lean_object* x_229; lean_object* x_230; uint8_t x_231; lean_object* x_232; 
x_229 = lean_ctor_get(x_184, 1);
x_230 = lean_ctor_get(x_184, 2);
lean_inc(x_230);
lean_inc(x_229);
lean_dec(x_184);
x_231 = 0;
x_232 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_232, 0, x_185);
lean_ctor_set(x_232, 1, x_229);
lean_ctor_set(x_232, 2, x_230);
lean_ctor_set(x_232, 3, x_186);
lean_ctor_set_uint8(x_232, sizeof(void*)*4, x_231);
lean_ctor_set(x_1, 0, x_232);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_197);
return x_1;
}
}
}
}
else
{
uint8_t x_233; 
x_233 = lean_ctor_get_uint8(x_185, sizeof(void*)*4);
if (x_233 == 0)
{
uint8_t x_234; 
x_234 = !lean_is_exclusive(x_184);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; 
x_235 = lean_ctor_get(x_184, 1);
x_236 = lean_ctor_get(x_184, 2);
x_237 = lean_ctor_get(x_184, 3);
x_238 = lean_ctor_get(x_184, 0);
lean_dec(x_238);
x_239 = !lean_is_exclusive(x_185);
if (x_239 == 0)
{
uint8_t x_240; 
x_240 = 1;
lean_ctor_set_uint8(x_185, sizeof(void*)*4, x_240);
lean_ctor_set(x_184, 3, x_35);
lean_ctor_set(x_184, 2, x_34);
lean_ctor_set(x_184, 1, x_33);
lean_ctor_set(x_184, 0, x_237);
lean_ctor_set_uint8(x_184, sizeof(void*)*4, x_240);
lean_ctor_set(x_1, 3, x_184);
lean_ctor_set(x_1, 2, x_236);
lean_ctor_set(x_1, 1, x_235);
lean_ctor_set(x_1, 0, x_185);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_233);
return x_1;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; lean_object* x_246; 
x_241 = lean_ctor_get(x_185, 0);
x_242 = lean_ctor_get(x_185, 1);
x_243 = lean_ctor_get(x_185, 2);
x_244 = lean_ctor_get(x_185, 3);
lean_inc(x_244);
lean_inc(x_243);
lean_inc(x_242);
lean_inc(x_241);
lean_dec(x_185);
x_245 = 1;
x_246 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_246, 0, x_241);
lean_ctor_set(x_246, 1, x_242);
lean_ctor_set(x_246, 2, x_243);
lean_ctor_set(x_246, 3, x_244);
lean_ctor_set_uint8(x_246, sizeof(void*)*4, x_245);
lean_ctor_set(x_184, 3, x_35);
lean_ctor_set(x_184, 2, x_34);
lean_ctor_set(x_184, 1, x_33);
lean_ctor_set(x_184, 0, x_237);
lean_ctor_set_uint8(x_184, sizeof(void*)*4, x_245);
lean_ctor_set(x_1, 3, x_184);
lean_ctor_set(x_1, 2, x_236);
lean_ctor_set(x_1, 1, x_235);
lean_ctor_set(x_1, 0, x_246);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_233);
return x_1;
}
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; uint8_t x_255; lean_object* x_256; lean_object* x_257; 
x_247 = lean_ctor_get(x_184, 1);
x_248 = lean_ctor_get(x_184, 2);
x_249 = lean_ctor_get(x_184, 3);
lean_inc(x_249);
lean_inc(x_248);
lean_inc(x_247);
lean_dec(x_184);
x_250 = lean_ctor_get(x_185, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_185, 1);
lean_inc(x_251);
x_252 = lean_ctor_get(x_185, 2);
lean_inc(x_252);
x_253 = lean_ctor_get(x_185, 3);
lean_inc(x_253);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 lean_ctor_release(x_185, 2);
 lean_ctor_release(x_185, 3);
 x_254 = x_185;
} else {
 lean_dec_ref(x_185);
 x_254 = lean_box(0);
}
x_255 = 1;
if (lean_is_scalar(x_254)) {
 x_256 = lean_alloc_ctor(1, 4, 1);
} else {
 x_256 = x_254;
}
lean_ctor_set(x_256, 0, x_250);
lean_ctor_set(x_256, 1, x_251);
lean_ctor_set(x_256, 2, x_252);
lean_ctor_set(x_256, 3, x_253);
lean_ctor_set_uint8(x_256, sizeof(void*)*4, x_255);
x_257 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_257, 0, x_249);
lean_ctor_set(x_257, 1, x_33);
lean_ctor_set(x_257, 2, x_34);
lean_ctor_set(x_257, 3, x_35);
lean_ctor_set_uint8(x_257, sizeof(void*)*4, x_255);
lean_ctor_set(x_1, 3, x_257);
lean_ctor_set(x_1, 2, x_248);
lean_ctor_set(x_1, 1, x_247);
lean_ctor_set(x_1, 0, x_256);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_233);
return x_1;
}
}
else
{
lean_object* x_258; 
x_258 = lean_ctor_get(x_184, 3);
lean_inc(x_258);
if (lean_obj_tag(x_258) == 0)
{
uint8_t x_259; 
x_259 = !lean_is_exclusive(x_184);
if (x_259 == 0)
{
lean_object* x_260; lean_object* x_261; uint8_t x_262; 
x_260 = lean_ctor_get(x_184, 3);
lean_dec(x_260);
x_261 = lean_ctor_get(x_184, 0);
lean_dec(x_261);
x_262 = 0;
lean_ctor_set_uint8(x_184, sizeof(void*)*4, x_262);
lean_ctor_set(x_1, 0, x_184);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_233);
return x_1;
}
else
{
lean_object* x_263; lean_object* x_264; uint8_t x_265; lean_object* x_266; 
x_263 = lean_ctor_get(x_184, 1);
x_264 = lean_ctor_get(x_184, 2);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_184);
x_265 = 0;
x_266 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_266, 0, x_185);
lean_ctor_set(x_266, 1, x_263);
lean_ctor_set(x_266, 2, x_264);
lean_ctor_set(x_266, 3, x_258);
lean_ctor_set_uint8(x_266, sizeof(void*)*4, x_265);
lean_ctor_set(x_1, 0, x_266);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_233);
return x_1;
}
}
else
{
uint8_t x_267; 
x_267 = lean_ctor_get_uint8(x_258, sizeof(void*)*4);
if (x_267 == 0)
{
uint8_t x_268; 
lean_free_object(x_1);
x_268 = !lean_is_exclusive(x_184);
if (x_268 == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; uint8_t x_273; 
x_269 = lean_ctor_get(x_184, 1);
x_270 = lean_ctor_get(x_184, 2);
x_271 = lean_ctor_get(x_184, 3);
lean_dec(x_271);
x_272 = lean_ctor_get(x_184, 0);
lean_dec(x_272);
x_273 = !lean_is_exclusive(x_258);
if (x_273 == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; uint8_t x_278; 
x_274 = lean_ctor_get(x_258, 0);
x_275 = lean_ctor_get(x_258, 1);
x_276 = lean_ctor_get(x_258, 2);
x_277 = lean_ctor_get(x_258, 3);
lean_inc(x_185);
lean_ctor_set(x_258, 3, x_274);
lean_ctor_set(x_258, 2, x_270);
lean_ctor_set(x_258, 1, x_269);
lean_ctor_set(x_258, 0, x_185);
x_278 = !lean_is_exclusive(x_185);
if (x_278 == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_279 = lean_ctor_get(x_185, 3);
lean_dec(x_279);
x_280 = lean_ctor_get(x_185, 2);
lean_dec(x_280);
x_281 = lean_ctor_get(x_185, 1);
lean_dec(x_281);
x_282 = lean_ctor_get(x_185, 0);
lean_dec(x_282);
lean_ctor_set_uint8(x_258, sizeof(void*)*4, x_233);
lean_ctor_set(x_185, 3, x_35);
lean_ctor_set(x_185, 2, x_34);
lean_ctor_set(x_185, 1, x_33);
lean_ctor_set(x_185, 0, x_277);
lean_ctor_set(x_184, 3, x_185);
lean_ctor_set(x_184, 2, x_276);
lean_ctor_set(x_184, 1, x_275);
lean_ctor_set(x_184, 0, x_258);
lean_ctor_set_uint8(x_184, sizeof(void*)*4, x_267);
return x_184;
}
else
{
lean_object* x_283; 
lean_dec(x_185);
lean_ctor_set_uint8(x_258, sizeof(void*)*4, x_233);
x_283 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_283, 0, x_277);
lean_ctor_set(x_283, 1, x_33);
lean_ctor_set(x_283, 2, x_34);
lean_ctor_set(x_283, 3, x_35);
lean_ctor_set_uint8(x_283, sizeof(void*)*4, x_233);
lean_ctor_set(x_184, 3, x_283);
lean_ctor_set(x_184, 2, x_276);
lean_ctor_set(x_184, 1, x_275);
lean_ctor_set(x_184, 0, x_258);
lean_ctor_set_uint8(x_184, sizeof(void*)*4, x_267);
return x_184;
}
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_284 = lean_ctor_get(x_258, 0);
x_285 = lean_ctor_get(x_258, 1);
x_286 = lean_ctor_get(x_258, 2);
x_287 = lean_ctor_get(x_258, 3);
lean_inc(x_287);
lean_inc(x_286);
lean_inc(x_285);
lean_inc(x_284);
lean_dec(x_258);
lean_inc(x_185);
x_288 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_288, 0, x_185);
lean_ctor_set(x_288, 1, x_269);
lean_ctor_set(x_288, 2, x_270);
lean_ctor_set(x_288, 3, x_284);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 lean_ctor_release(x_185, 2);
 lean_ctor_release(x_185, 3);
 x_289 = x_185;
} else {
 lean_dec_ref(x_185);
 x_289 = lean_box(0);
}
lean_ctor_set_uint8(x_288, sizeof(void*)*4, x_233);
if (lean_is_scalar(x_289)) {
 x_290 = lean_alloc_ctor(1, 4, 1);
} else {
 x_290 = x_289;
}
lean_ctor_set(x_290, 0, x_287);
lean_ctor_set(x_290, 1, x_33);
lean_ctor_set(x_290, 2, x_34);
lean_ctor_set(x_290, 3, x_35);
lean_ctor_set_uint8(x_290, sizeof(void*)*4, x_233);
lean_ctor_set(x_184, 3, x_290);
lean_ctor_set(x_184, 2, x_286);
lean_ctor_set(x_184, 1, x_285);
lean_ctor_set(x_184, 0, x_288);
lean_ctor_set_uint8(x_184, sizeof(void*)*4, x_267);
return x_184;
}
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_291 = lean_ctor_get(x_184, 1);
x_292 = lean_ctor_get(x_184, 2);
lean_inc(x_292);
lean_inc(x_291);
lean_dec(x_184);
x_293 = lean_ctor_get(x_258, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_258, 1);
lean_inc(x_294);
x_295 = lean_ctor_get(x_258, 2);
lean_inc(x_295);
x_296 = lean_ctor_get(x_258, 3);
lean_inc(x_296);
if (lean_is_exclusive(x_258)) {
 lean_ctor_release(x_258, 0);
 lean_ctor_release(x_258, 1);
 lean_ctor_release(x_258, 2);
 lean_ctor_release(x_258, 3);
 x_297 = x_258;
} else {
 lean_dec_ref(x_258);
 x_297 = lean_box(0);
}
lean_inc(x_185);
if (lean_is_scalar(x_297)) {
 x_298 = lean_alloc_ctor(1, 4, 1);
} else {
 x_298 = x_297;
}
lean_ctor_set(x_298, 0, x_185);
lean_ctor_set(x_298, 1, x_291);
lean_ctor_set(x_298, 2, x_292);
lean_ctor_set(x_298, 3, x_293);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 lean_ctor_release(x_185, 2);
 lean_ctor_release(x_185, 3);
 x_299 = x_185;
} else {
 lean_dec_ref(x_185);
 x_299 = lean_box(0);
}
lean_ctor_set_uint8(x_298, sizeof(void*)*4, x_233);
if (lean_is_scalar(x_299)) {
 x_300 = lean_alloc_ctor(1, 4, 1);
} else {
 x_300 = x_299;
}
lean_ctor_set(x_300, 0, x_296);
lean_ctor_set(x_300, 1, x_33);
lean_ctor_set(x_300, 2, x_34);
lean_ctor_set(x_300, 3, x_35);
lean_ctor_set_uint8(x_300, sizeof(void*)*4, x_233);
x_301 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_301, 0, x_298);
lean_ctor_set(x_301, 1, x_294);
lean_ctor_set(x_301, 2, x_295);
lean_ctor_set(x_301, 3, x_300);
lean_ctor_set_uint8(x_301, sizeof(void*)*4, x_267);
return x_301;
}
}
else
{
uint8_t x_302; 
x_302 = !lean_is_exclusive(x_184);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; uint8_t x_305; 
x_303 = lean_ctor_get(x_184, 3);
lean_dec(x_303);
x_304 = lean_ctor_get(x_184, 0);
lean_dec(x_304);
x_305 = !lean_is_exclusive(x_185);
if (x_305 == 0)
{
uint8_t x_306; 
lean_ctor_set_uint8(x_185, sizeof(void*)*4, x_267);
x_306 = 0;
lean_ctor_set_uint8(x_184, sizeof(void*)*4, x_306);
lean_ctor_set(x_1, 0, x_184);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_267);
return x_1;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; 
x_307 = lean_ctor_get(x_185, 0);
x_308 = lean_ctor_get(x_185, 1);
x_309 = lean_ctor_get(x_185, 2);
x_310 = lean_ctor_get(x_185, 3);
lean_inc(x_310);
lean_inc(x_309);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_185);
x_311 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_311, 0, x_307);
lean_ctor_set(x_311, 1, x_308);
lean_ctor_set(x_311, 2, x_309);
lean_ctor_set(x_311, 3, x_310);
lean_ctor_set_uint8(x_311, sizeof(void*)*4, x_267);
x_312 = 0;
lean_ctor_set(x_184, 0, x_311);
lean_ctor_set_uint8(x_184, sizeof(void*)*4, x_312);
lean_ctor_set(x_1, 0, x_184);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_267);
return x_1;
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; uint8_t x_321; lean_object* x_322; 
x_313 = lean_ctor_get(x_184, 1);
x_314 = lean_ctor_get(x_184, 2);
lean_inc(x_314);
lean_inc(x_313);
lean_dec(x_184);
x_315 = lean_ctor_get(x_185, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_185, 1);
lean_inc(x_316);
x_317 = lean_ctor_get(x_185, 2);
lean_inc(x_317);
x_318 = lean_ctor_get(x_185, 3);
lean_inc(x_318);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 lean_ctor_release(x_185, 2);
 lean_ctor_release(x_185, 3);
 x_319 = x_185;
} else {
 lean_dec_ref(x_185);
 x_319 = lean_box(0);
}
if (lean_is_scalar(x_319)) {
 x_320 = lean_alloc_ctor(1, 4, 1);
} else {
 x_320 = x_319;
}
lean_ctor_set(x_320, 0, x_315);
lean_ctor_set(x_320, 1, x_316);
lean_ctor_set(x_320, 2, x_317);
lean_ctor_set(x_320, 3, x_318);
lean_ctor_set_uint8(x_320, sizeof(void*)*4, x_267);
x_321 = 0;
x_322 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_322, 0, x_320);
lean_ctor_set(x_322, 1, x_313);
lean_ctor_set(x_322, 2, x_314);
lean_ctor_set(x_322, 3, x_258);
lean_ctor_set_uint8(x_322, sizeof(void*)*4, x_321);
lean_ctor_set(x_1, 0, x_322);
lean_ctor_set_uint8(x_1, sizeof(void*)*4, x_267);
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
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; uint8_t x_328; 
x_323 = lean_ctor_get(x_1, 0);
x_324 = lean_ctor_get(x_1, 1);
x_325 = lean_ctor_get(x_1, 2);
x_326 = lean_ctor_get(x_1, 3);
lean_inc(x_326);
lean_inc(x_325);
lean_inc(x_324);
lean_inc(x_323);
lean_dec(x_1);
x_327 = lean_nat_dec_lt(x_2, x_324);
x_328 = l_coeDecidableEq(x_327);
if (x_328 == 0)
{
uint8_t x_329; uint8_t x_330; 
x_329 = lean_nat_dec_lt(x_324, x_2);
x_330 = l_coeDecidableEq(x_329);
if (x_330 == 0)
{
lean_object* x_331; 
lean_dec(x_325);
lean_dec(x_324);
x_331 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_331, 0, x_323);
lean_ctor_set(x_331, 1, x_2);
lean_ctor_set(x_331, 2, x_3);
lean_ctor_set(x_331, 3, x_326);
lean_ctor_set_uint8(x_331, sizeof(void*)*4, x_6);
return x_331;
}
else
{
uint8_t x_332; uint8_t x_333; 
x_332 = l_RBNode_isRed___rarg(x_326);
x_333 = l_coeDecidableEq(x_332);
if (x_333 == 0)
{
lean_object* x_334; lean_object* x_335; 
x_334 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_326, x_2, x_3);
x_335 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_335, 0, x_323);
lean_ctor_set(x_335, 1, x_324);
lean_ctor_set(x_335, 2, x_325);
lean_ctor_set(x_335, 3, x_334);
lean_ctor_set_uint8(x_335, sizeof(void*)*4, x_6);
return x_335;
}
else
{
lean_object* x_336; lean_object* x_337; 
x_336 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_326, x_2, x_3);
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; 
x_338 = lean_ctor_get(x_336, 3);
lean_inc(x_338);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; uint8_t x_342; lean_object* x_343; uint8_t x_344; lean_object* x_345; 
x_339 = lean_ctor_get(x_336, 1);
lean_inc(x_339);
x_340 = lean_ctor_get(x_336, 2);
lean_inc(x_340);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 lean_ctor_release(x_336, 2);
 lean_ctor_release(x_336, 3);
 x_341 = x_336;
} else {
 lean_dec_ref(x_336);
 x_341 = lean_box(0);
}
x_342 = 0;
if (lean_is_scalar(x_341)) {
 x_343 = lean_alloc_ctor(1, 4, 1);
} else {
 x_343 = x_341;
}
lean_ctor_set(x_343, 0, x_338);
lean_ctor_set(x_343, 1, x_339);
lean_ctor_set(x_343, 2, x_340);
lean_ctor_set(x_343, 3, x_338);
lean_ctor_set_uint8(x_343, sizeof(void*)*4, x_342);
x_344 = 1;
x_345 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_345, 0, x_323);
lean_ctor_set(x_345, 1, x_324);
lean_ctor_set(x_345, 2, x_325);
lean_ctor_set(x_345, 3, x_343);
lean_ctor_set_uint8(x_345, sizeof(void*)*4, x_344);
return x_345;
}
else
{
uint8_t x_346; 
x_346 = lean_ctor_get_uint8(x_338, sizeof(void*)*4);
if (x_346 == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; uint8_t x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_347 = lean_ctor_get(x_336, 1);
lean_inc(x_347);
x_348 = lean_ctor_get(x_336, 2);
lean_inc(x_348);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 lean_ctor_release(x_336, 2);
 lean_ctor_release(x_336, 3);
 x_349 = x_336;
} else {
 lean_dec_ref(x_336);
 x_349 = lean_box(0);
}
x_350 = lean_ctor_get(x_338, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_338, 1);
lean_inc(x_351);
x_352 = lean_ctor_get(x_338, 2);
lean_inc(x_352);
x_353 = lean_ctor_get(x_338, 3);
lean_inc(x_353);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 lean_ctor_release(x_338, 2);
 lean_ctor_release(x_338, 3);
 x_354 = x_338;
} else {
 lean_dec_ref(x_338);
 x_354 = lean_box(0);
}
x_355 = 1;
if (lean_is_scalar(x_354)) {
 x_356 = lean_alloc_ctor(1, 4, 1);
} else {
 x_356 = x_354;
}
lean_ctor_set(x_356, 0, x_323);
lean_ctor_set(x_356, 1, x_324);
lean_ctor_set(x_356, 2, x_325);
lean_ctor_set(x_356, 3, x_337);
lean_ctor_set_uint8(x_356, sizeof(void*)*4, x_355);
if (lean_is_scalar(x_349)) {
 x_357 = lean_alloc_ctor(1, 4, 1);
} else {
 x_357 = x_349;
}
lean_ctor_set(x_357, 0, x_350);
lean_ctor_set(x_357, 1, x_351);
lean_ctor_set(x_357, 2, x_352);
lean_ctor_set(x_357, 3, x_353);
lean_ctor_set_uint8(x_357, sizeof(void*)*4, x_355);
x_358 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_358, 0, x_356);
lean_ctor_set(x_358, 1, x_347);
lean_ctor_set(x_358, 2, x_348);
lean_ctor_set(x_358, 3, x_357);
lean_ctor_set_uint8(x_358, sizeof(void*)*4, x_346);
return x_358;
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; uint8_t x_362; lean_object* x_363; lean_object* x_364; 
x_359 = lean_ctor_get(x_336, 1);
lean_inc(x_359);
x_360 = lean_ctor_get(x_336, 2);
lean_inc(x_360);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 lean_ctor_release(x_336, 2);
 lean_ctor_release(x_336, 3);
 x_361 = x_336;
} else {
 lean_dec_ref(x_336);
 x_361 = lean_box(0);
}
x_362 = 0;
if (lean_is_scalar(x_361)) {
 x_363 = lean_alloc_ctor(1, 4, 1);
} else {
 x_363 = x_361;
}
lean_ctor_set(x_363, 0, x_337);
lean_ctor_set(x_363, 1, x_359);
lean_ctor_set(x_363, 2, x_360);
lean_ctor_set(x_363, 3, x_338);
lean_ctor_set_uint8(x_363, sizeof(void*)*4, x_362);
x_364 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_364, 0, x_323);
lean_ctor_set(x_364, 1, x_324);
lean_ctor_set(x_364, 2, x_325);
lean_ctor_set(x_364, 3, x_363);
lean_ctor_set_uint8(x_364, sizeof(void*)*4, x_346);
return x_364;
}
}
}
else
{
uint8_t x_365; 
x_365 = lean_ctor_get_uint8(x_337, sizeof(void*)*4);
if (x_365 == 0)
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; uint8_t x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_366 = lean_ctor_get(x_336, 1);
lean_inc(x_366);
x_367 = lean_ctor_get(x_336, 2);
lean_inc(x_367);
x_368 = lean_ctor_get(x_336, 3);
lean_inc(x_368);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 lean_ctor_release(x_336, 2);
 lean_ctor_release(x_336, 3);
 x_369 = x_336;
} else {
 lean_dec_ref(x_336);
 x_369 = lean_box(0);
}
x_370 = lean_ctor_get(x_337, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_337, 1);
lean_inc(x_371);
x_372 = lean_ctor_get(x_337, 2);
lean_inc(x_372);
x_373 = lean_ctor_get(x_337, 3);
lean_inc(x_373);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 lean_ctor_release(x_337, 2);
 lean_ctor_release(x_337, 3);
 x_374 = x_337;
} else {
 lean_dec_ref(x_337);
 x_374 = lean_box(0);
}
x_375 = 1;
if (lean_is_scalar(x_374)) {
 x_376 = lean_alloc_ctor(1, 4, 1);
} else {
 x_376 = x_374;
}
lean_ctor_set(x_376, 0, x_323);
lean_ctor_set(x_376, 1, x_324);
lean_ctor_set(x_376, 2, x_325);
lean_ctor_set(x_376, 3, x_370);
lean_ctor_set_uint8(x_376, sizeof(void*)*4, x_375);
if (lean_is_scalar(x_369)) {
 x_377 = lean_alloc_ctor(1, 4, 1);
} else {
 x_377 = x_369;
}
lean_ctor_set(x_377, 0, x_373);
lean_ctor_set(x_377, 1, x_366);
lean_ctor_set(x_377, 2, x_367);
lean_ctor_set(x_377, 3, x_368);
lean_ctor_set_uint8(x_377, sizeof(void*)*4, x_375);
x_378 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_378, 0, x_376);
lean_ctor_set(x_378, 1, x_371);
lean_ctor_set(x_378, 2, x_372);
lean_ctor_set(x_378, 3, x_377);
lean_ctor_set_uint8(x_378, sizeof(void*)*4, x_365);
return x_378;
}
else
{
lean_object* x_379; 
x_379 = lean_ctor_get(x_336, 3);
lean_inc(x_379);
if (lean_obj_tag(x_379) == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; uint8_t x_383; lean_object* x_384; lean_object* x_385; 
x_380 = lean_ctor_get(x_336, 1);
lean_inc(x_380);
x_381 = lean_ctor_get(x_336, 2);
lean_inc(x_381);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 lean_ctor_release(x_336, 2);
 lean_ctor_release(x_336, 3);
 x_382 = x_336;
} else {
 lean_dec_ref(x_336);
 x_382 = lean_box(0);
}
x_383 = 0;
if (lean_is_scalar(x_382)) {
 x_384 = lean_alloc_ctor(1, 4, 1);
} else {
 x_384 = x_382;
}
lean_ctor_set(x_384, 0, x_337);
lean_ctor_set(x_384, 1, x_380);
lean_ctor_set(x_384, 2, x_381);
lean_ctor_set(x_384, 3, x_379);
lean_ctor_set_uint8(x_384, sizeof(void*)*4, x_383);
x_385 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_385, 0, x_323);
lean_ctor_set(x_385, 1, x_324);
lean_ctor_set(x_385, 2, x_325);
lean_ctor_set(x_385, 3, x_384);
lean_ctor_set_uint8(x_385, sizeof(void*)*4, x_365);
return x_385;
}
else
{
uint8_t x_386; 
x_386 = lean_ctor_get_uint8(x_379, sizeof(void*)*4);
if (x_386 == 0)
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_387 = lean_ctor_get(x_336, 1);
lean_inc(x_387);
x_388 = lean_ctor_get(x_336, 2);
lean_inc(x_388);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 lean_ctor_release(x_336, 2);
 lean_ctor_release(x_336, 3);
 x_389 = x_336;
} else {
 lean_dec_ref(x_336);
 x_389 = lean_box(0);
}
x_390 = lean_ctor_get(x_379, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_379, 1);
lean_inc(x_391);
x_392 = lean_ctor_get(x_379, 2);
lean_inc(x_392);
x_393 = lean_ctor_get(x_379, 3);
lean_inc(x_393);
if (lean_is_exclusive(x_379)) {
 lean_ctor_release(x_379, 0);
 lean_ctor_release(x_379, 1);
 lean_ctor_release(x_379, 2);
 lean_ctor_release(x_379, 3);
 x_394 = x_379;
} else {
 lean_dec_ref(x_379);
 x_394 = lean_box(0);
}
lean_inc(x_337);
if (lean_is_scalar(x_394)) {
 x_395 = lean_alloc_ctor(1, 4, 1);
} else {
 x_395 = x_394;
}
lean_ctor_set(x_395, 0, x_323);
lean_ctor_set(x_395, 1, x_324);
lean_ctor_set(x_395, 2, x_325);
lean_ctor_set(x_395, 3, x_337);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 lean_ctor_release(x_337, 2);
 lean_ctor_release(x_337, 3);
 x_396 = x_337;
} else {
 lean_dec_ref(x_337);
 x_396 = lean_box(0);
}
lean_ctor_set_uint8(x_395, sizeof(void*)*4, x_365);
if (lean_is_scalar(x_396)) {
 x_397 = lean_alloc_ctor(1, 4, 1);
} else {
 x_397 = x_396;
}
lean_ctor_set(x_397, 0, x_390);
lean_ctor_set(x_397, 1, x_391);
lean_ctor_set(x_397, 2, x_392);
lean_ctor_set(x_397, 3, x_393);
lean_ctor_set_uint8(x_397, sizeof(void*)*4, x_365);
if (lean_is_scalar(x_389)) {
 x_398 = lean_alloc_ctor(1, 4, 1);
} else {
 x_398 = x_389;
}
lean_ctor_set(x_398, 0, x_395);
lean_ctor_set(x_398, 1, x_387);
lean_ctor_set(x_398, 2, x_388);
lean_ctor_set(x_398, 3, x_397);
lean_ctor_set_uint8(x_398, sizeof(void*)*4, x_386);
return x_398;
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; uint8_t x_408; lean_object* x_409; lean_object* x_410; 
x_399 = lean_ctor_get(x_336, 1);
lean_inc(x_399);
x_400 = lean_ctor_get(x_336, 2);
lean_inc(x_400);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 lean_ctor_release(x_336, 2);
 lean_ctor_release(x_336, 3);
 x_401 = x_336;
} else {
 lean_dec_ref(x_336);
 x_401 = lean_box(0);
}
x_402 = lean_ctor_get(x_337, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_337, 1);
lean_inc(x_403);
x_404 = lean_ctor_get(x_337, 2);
lean_inc(x_404);
x_405 = lean_ctor_get(x_337, 3);
lean_inc(x_405);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 lean_ctor_release(x_337, 2);
 lean_ctor_release(x_337, 3);
 x_406 = x_337;
} else {
 lean_dec_ref(x_337);
 x_406 = lean_box(0);
}
if (lean_is_scalar(x_406)) {
 x_407 = lean_alloc_ctor(1, 4, 1);
} else {
 x_407 = x_406;
}
lean_ctor_set(x_407, 0, x_402);
lean_ctor_set(x_407, 1, x_403);
lean_ctor_set(x_407, 2, x_404);
lean_ctor_set(x_407, 3, x_405);
lean_ctor_set_uint8(x_407, sizeof(void*)*4, x_386);
x_408 = 0;
if (lean_is_scalar(x_401)) {
 x_409 = lean_alloc_ctor(1, 4, 1);
} else {
 x_409 = x_401;
}
lean_ctor_set(x_409, 0, x_407);
lean_ctor_set(x_409, 1, x_399);
lean_ctor_set(x_409, 2, x_400);
lean_ctor_set(x_409, 3, x_379);
lean_ctor_set_uint8(x_409, sizeof(void*)*4, x_408);
x_410 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_410, 0, x_323);
lean_ctor_set(x_410, 1, x_324);
lean_ctor_set(x_410, 2, x_325);
lean_ctor_set(x_410, 3, x_409);
lean_ctor_set_uint8(x_410, sizeof(void*)*4, x_386);
return x_410;
}
}
}
}
}
}
}
else
{
uint8_t x_411; uint8_t x_412; 
x_411 = l_RBNode_isRed___rarg(x_323);
x_412 = l_coeDecidableEq(x_411);
if (x_412 == 0)
{
lean_object* x_413; lean_object* x_414; 
x_413 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_323, x_2, x_3);
x_414 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_414, 0, x_413);
lean_ctor_set(x_414, 1, x_324);
lean_ctor_set(x_414, 2, x_325);
lean_ctor_set(x_414, 3, x_326);
lean_ctor_set_uint8(x_414, sizeof(void*)*4, x_6);
return x_414;
}
else
{
lean_object* x_415; lean_object* x_416; 
x_415 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_323, x_2, x_3);
x_416 = lean_ctor_get(x_415, 0);
lean_inc(x_416);
if (lean_obj_tag(x_416) == 0)
{
lean_object* x_417; 
x_417 = lean_ctor_get(x_415, 3);
lean_inc(x_417);
if (lean_obj_tag(x_417) == 0)
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; uint8_t x_421; lean_object* x_422; uint8_t x_423; lean_object* x_424; 
x_418 = lean_ctor_get(x_415, 1);
lean_inc(x_418);
x_419 = lean_ctor_get(x_415, 2);
lean_inc(x_419);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 lean_ctor_release(x_415, 2);
 lean_ctor_release(x_415, 3);
 x_420 = x_415;
} else {
 lean_dec_ref(x_415);
 x_420 = lean_box(0);
}
x_421 = 0;
if (lean_is_scalar(x_420)) {
 x_422 = lean_alloc_ctor(1, 4, 1);
} else {
 x_422 = x_420;
}
lean_ctor_set(x_422, 0, x_417);
lean_ctor_set(x_422, 1, x_418);
lean_ctor_set(x_422, 2, x_419);
lean_ctor_set(x_422, 3, x_417);
lean_ctor_set_uint8(x_422, sizeof(void*)*4, x_421);
x_423 = 1;
x_424 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_424, 0, x_422);
lean_ctor_set(x_424, 1, x_324);
lean_ctor_set(x_424, 2, x_325);
lean_ctor_set(x_424, 3, x_326);
lean_ctor_set_uint8(x_424, sizeof(void*)*4, x_423);
return x_424;
}
else
{
uint8_t x_425; 
x_425 = lean_ctor_get_uint8(x_417, sizeof(void*)*4);
if (x_425 == 0)
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; uint8_t x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_426 = lean_ctor_get(x_415, 1);
lean_inc(x_426);
x_427 = lean_ctor_get(x_415, 2);
lean_inc(x_427);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 lean_ctor_release(x_415, 2);
 lean_ctor_release(x_415, 3);
 x_428 = x_415;
} else {
 lean_dec_ref(x_415);
 x_428 = lean_box(0);
}
x_429 = lean_ctor_get(x_417, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_417, 1);
lean_inc(x_430);
x_431 = lean_ctor_get(x_417, 2);
lean_inc(x_431);
x_432 = lean_ctor_get(x_417, 3);
lean_inc(x_432);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 lean_ctor_release(x_417, 2);
 lean_ctor_release(x_417, 3);
 x_433 = x_417;
} else {
 lean_dec_ref(x_417);
 x_433 = lean_box(0);
}
x_434 = 1;
if (lean_is_scalar(x_433)) {
 x_435 = lean_alloc_ctor(1, 4, 1);
} else {
 x_435 = x_433;
}
lean_ctor_set(x_435, 0, x_416);
lean_ctor_set(x_435, 1, x_426);
lean_ctor_set(x_435, 2, x_427);
lean_ctor_set(x_435, 3, x_429);
lean_ctor_set_uint8(x_435, sizeof(void*)*4, x_434);
if (lean_is_scalar(x_428)) {
 x_436 = lean_alloc_ctor(1, 4, 1);
} else {
 x_436 = x_428;
}
lean_ctor_set(x_436, 0, x_432);
lean_ctor_set(x_436, 1, x_324);
lean_ctor_set(x_436, 2, x_325);
lean_ctor_set(x_436, 3, x_326);
lean_ctor_set_uint8(x_436, sizeof(void*)*4, x_434);
x_437 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_437, 0, x_435);
lean_ctor_set(x_437, 1, x_430);
lean_ctor_set(x_437, 2, x_431);
lean_ctor_set(x_437, 3, x_436);
lean_ctor_set_uint8(x_437, sizeof(void*)*4, x_425);
return x_437;
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; uint8_t x_441; lean_object* x_442; lean_object* x_443; 
x_438 = lean_ctor_get(x_415, 1);
lean_inc(x_438);
x_439 = lean_ctor_get(x_415, 2);
lean_inc(x_439);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 lean_ctor_release(x_415, 2);
 lean_ctor_release(x_415, 3);
 x_440 = x_415;
} else {
 lean_dec_ref(x_415);
 x_440 = lean_box(0);
}
x_441 = 0;
if (lean_is_scalar(x_440)) {
 x_442 = lean_alloc_ctor(1, 4, 1);
} else {
 x_442 = x_440;
}
lean_ctor_set(x_442, 0, x_416);
lean_ctor_set(x_442, 1, x_438);
lean_ctor_set(x_442, 2, x_439);
lean_ctor_set(x_442, 3, x_417);
lean_ctor_set_uint8(x_442, sizeof(void*)*4, x_441);
x_443 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_443, 0, x_442);
lean_ctor_set(x_443, 1, x_324);
lean_ctor_set(x_443, 2, x_325);
lean_ctor_set(x_443, 3, x_326);
lean_ctor_set_uint8(x_443, sizeof(void*)*4, x_425);
return x_443;
}
}
}
else
{
uint8_t x_444; 
x_444 = lean_ctor_get_uint8(x_416, sizeof(void*)*4);
if (x_444 == 0)
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; uint8_t x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; 
x_445 = lean_ctor_get(x_415, 1);
lean_inc(x_445);
x_446 = lean_ctor_get(x_415, 2);
lean_inc(x_446);
x_447 = lean_ctor_get(x_415, 3);
lean_inc(x_447);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 lean_ctor_release(x_415, 2);
 lean_ctor_release(x_415, 3);
 x_448 = x_415;
} else {
 lean_dec_ref(x_415);
 x_448 = lean_box(0);
}
x_449 = lean_ctor_get(x_416, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_416, 1);
lean_inc(x_450);
x_451 = lean_ctor_get(x_416, 2);
lean_inc(x_451);
x_452 = lean_ctor_get(x_416, 3);
lean_inc(x_452);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 lean_ctor_release(x_416, 3);
 x_453 = x_416;
} else {
 lean_dec_ref(x_416);
 x_453 = lean_box(0);
}
x_454 = 1;
if (lean_is_scalar(x_453)) {
 x_455 = lean_alloc_ctor(1, 4, 1);
} else {
 x_455 = x_453;
}
lean_ctor_set(x_455, 0, x_449);
lean_ctor_set(x_455, 1, x_450);
lean_ctor_set(x_455, 2, x_451);
lean_ctor_set(x_455, 3, x_452);
lean_ctor_set_uint8(x_455, sizeof(void*)*4, x_454);
if (lean_is_scalar(x_448)) {
 x_456 = lean_alloc_ctor(1, 4, 1);
} else {
 x_456 = x_448;
}
lean_ctor_set(x_456, 0, x_447);
lean_ctor_set(x_456, 1, x_324);
lean_ctor_set(x_456, 2, x_325);
lean_ctor_set(x_456, 3, x_326);
lean_ctor_set_uint8(x_456, sizeof(void*)*4, x_454);
x_457 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_457, 0, x_455);
lean_ctor_set(x_457, 1, x_445);
lean_ctor_set(x_457, 2, x_446);
lean_ctor_set(x_457, 3, x_456);
lean_ctor_set_uint8(x_457, sizeof(void*)*4, x_444);
return x_457;
}
else
{
lean_object* x_458; 
x_458 = lean_ctor_get(x_415, 3);
lean_inc(x_458);
if (lean_obj_tag(x_458) == 0)
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; uint8_t x_462; lean_object* x_463; lean_object* x_464; 
x_459 = lean_ctor_get(x_415, 1);
lean_inc(x_459);
x_460 = lean_ctor_get(x_415, 2);
lean_inc(x_460);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 lean_ctor_release(x_415, 2);
 lean_ctor_release(x_415, 3);
 x_461 = x_415;
} else {
 lean_dec_ref(x_415);
 x_461 = lean_box(0);
}
x_462 = 0;
if (lean_is_scalar(x_461)) {
 x_463 = lean_alloc_ctor(1, 4, 1);
} else {
 x_463 = x_461;
}
lean_ctor_set(x_463, 0, x_416);
lean_ctor_set(x_463, 1, x_459);
lean_ctor_set(x_463, 2, x_460);
lean_ctor_set(x_463, 3, x_458);
lean_ctor_set_uint8(x_463, sizeof(void*)*4, x_462);
x_464 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_464, 0, x_463);
lean_ctor_set(x_464, 1, x_324);
lean_ctor_set(x_464, 2, x_325);
lean_ctor_set(x_464, 3, x_326);
lean_ctor_set_uint8(x_464, sizeof(void*)*4, x_444);
return x_464;
}
else
{
uint8_t x_465; 
x_465 = lean_ctor_get_uint8(x_458, sizeof(void*)*4);
if (x_465 == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; 
x_466 = lean_ctor_get(x_415, 1);
lean_inc(x_466);
x_467 = lean_ctor_get(x_415, 2);
lean_inc(x_467);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 lean_ctor_release(x_415, 2);
 lean_ctor_release(x_415, 3);
 x_468 = x_415;
} else {
 lean_dec_ref(x_415);
 x_468 = lean_box(0);
}
x_469 = lean_ctor_get(x_458, 0);
lean_inc(x_469);
x_470 = lean_ctor_get(x_458, 1);
lean_inc(x_470);
x_471 = lean_ctor_get(x_458, 2);
lean_inc(x_471);
x_472 = lean_ctor_get(x_458, 3);
lean_inc(x_472);
if (lean_is_exclusive(x_458)) {
 lean_ctor_release(x_458, 0);
 lean_ctor_release(x_458, 1);
 lean_ctor_release(x_458, 2);
 lean_ctor_release(x_458, 3);
 x_473 = x_458;
} else {
 lean_dec_ref(x_458);
 x_473 = lean_box(0);
}
lean_inc(x_416);
if (lean_is_scalar(x_473)) {
 x_474 = lean_alloc_ctor(1, 4, 1);
} else {
 x_474 = x_473;
}
lean_ctor_set(x_474, 0, x_416);
lean_ctor_set(x_474, 1, x_466);
lean_ctor_set(x_474, 2, x_467);
lean_ctor_set(x_474, 3, x_469);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 lean_ctor_release(x_416, 3);
 x_475 = x_416;
} else {
 lean_dec_ref(x_416);
 x_475 = lean_box(0);
}
lean_ctor_set_uint8(x_474, sizeof(void*)*4, x_444);
if (lean_is_scalar(x_475)) {
 x_476 = lean_alloc_ctor(1, 4, 1);
} else {
 x_476 = x_475;
}
lean_ctor_set(x_476, 0, x_472);
lean_ctor_set(x_476, 1, x_324);
lean_ctor_set(x_476, 2, x_325);
lean_ctor_set(x_476, 3, x_326);
lean_ctor_set_uint8(x_476, sizeof(void*)*4, x_444);
if (lean_is_scalar(x_468)) {
 x_477 = lean_alloc_ctor(1, 4, 1);
} else {
 x_477 = x_468;
}
lean_ctor_set(x_477, 0, x_474);
lean_ctor_set(x_477, 1, x_470);
lean_ctor_set(x_477, 2, x_471);
lean_ctor_set(x_477, 3, x_476);
lean_ctor_set_uint8(x_477, sizeof(void*)*4, x_465);
return x_477;
}
else
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; uint8_t x_487; lean_object* x_488; lean_object* x_489; 
x_478 = lean_ctor_get(x_415, 1);
lean_inc(x_478);
x_479 = lean_ctor_get(x_415, 2);
lean_inc(x_479);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 lean_ctor_release(x_415, 1);
 lean_ctor_release(x_415, 2);
 lean_ctor_release(x_415, 3);
 x_480 = x_415;
} else {
 lean_dec_ref(x_415);
 x_480 = lean_box(0);
}
x_481 = lean_ctor_get(x_416, 0);
lean_inc(x_481);
x_482 = lean_ctor_get(x_416, 1);
lean_inc(x_482);
x_483 = lean_ctor_get(x_416, 2);
lean_inc(x_483);
x_484 = lean_ctor_get(x_416, 3);
lean_inc(x_484);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 lean_ctor_release(x_416, 2);
 lean_ctor_release(x_416, 3);
 x_485 = x_416;
} else {
 lean_dec_ref(x_416);
 x_485 = lean_box(0);
}
if (lean_is_scalar(x_485)) {
 x_486 = lean_alloc_ctor(1, 4, 1);
} else {
 x_486 = x_485;
}
lean_ctor_set(x_486, 0, x_481);
lean_ctor_set(x_486, 1, x_482);
lean_ctor_set(x_486, 2, x_483);
lean_ctor_set(x_486, 3, x_484);
lean_ctor_set_uint8(x_486, sizeof(void*)*4, x_465);
x_487 = 0;
if (lean_is_scalar(x_480)) {
 x_488 = lean_alloc_ctor(1, 4, 1);
} else {
 x_488 = x_480;
}
lean_ctor_set(x_488, 0, x_486);
lean_ctor_set(x_488, 1, x_478);
lean_ctor_set(x_488, 2, x_479);
lean_ctor_set(x_488, 3, x_458);
lean_ctor_set_uint8(x_488, sizeof(void*)*4, x_487);
x_489 = lean_alloc_ctor(1, 4, 1);
lean_ctor_set(x_489, 0, x_488);
lean_ctor_set(x_489, 1, x_324);
lean_ctor_set(x_489, 2, x_325);
lean_ctor_set(x_489, 3, x_326);
lean_ctor_set_uint8(x_489, sizeof(void*)*4, x_465);
return x_489;
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
uint8_t x_4; uint8_t x_5; 
x_4 = l_RBNode_isRed___rarg(x_1);
x_5 = l_coeDecidableEq(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_1, x_2, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_RBNode_ins___main___at_Lean_IR_addVarRename___spec__2(x_1, x_2, x_3);
x_8 = l_RBNode_setBlack___rarg(x_7);
return x_8;
}
}
}
lean_object* l_Lean_IR_addVarRename(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; 
x_4 = lean_nat_dec_eq(x_2, x_3);
x_5 = l_coeDecidableEq(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_RBNode_insert___at_Lean_IR_addVarRename___spec__1(x_1, x_2, x_3);
return x_6;
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
x_7 = l_String_posOfAux___main___closed__1;
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
uint8_t x_13; uint8_t x_14; uint8_t x_15; 
x_13 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_14 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
if (x_13 == 0)
{
if (x_14 == 0)
{
uint8_t x_23; 
x_23 = 1;
x_15 = x_23;
goto block_22;
}
else
{
uint8_t x_24; 
x_24 = 0;
x_15 = x_24;
goto block_22;
}
}
else
{
if (x_14 == 0)
{
uint8_t x_25; 
x_25 = 0;
x_15 = x_25;
goto block_22;
}
else
{
uint8_t x_26; 
x_26 = 1;
x_15 = x_26;
goto block_22;
}
}
block_22:
{
uint8_t x_16; 
x_16 = l_coeDecidableEq(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_box(0);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_ctor_get(x_3, 0);
lean_inc(x_19);
lean_dec(x_3);
x_20 = l_Lean_IR_addVarRename(x_1, x_18, x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
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
x_7 = l_String_posOfAux___main___closed__2;
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
x_12 = l_String_posOfAux___main___closed__1;
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
x_131 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_132 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_133 = lean_ctor_get(x_2, 2);
lean_inc(x_133);
lean_dec(x_2);
x_134 = lean_ctor_get(x_3, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_3, 1);
lean_inc(x_135);
x_136 = lean_ctor_get_uint8(x_3, sizeof(void*)*3);
x_137 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 1);
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
