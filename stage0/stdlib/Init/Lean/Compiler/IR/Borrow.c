// Lean compiler output
// Module: Init.Lean.Compiler.IR.Borrow
// Imports: Init.Data.Nat Init.Lean.Compiler.ExportAttr Init.Lean.Compiler.IR.CompilerM Init.Lean.Compiler.IR.NormIds
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
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Lean_IR_Borrow_Key_Hashable;
lean_object* l_Lean_IR_Borrow_whileModifingParamMapAux___main___at_Lean_IR_Borrow_collectDecls___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_Borrow_updateParamSet___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_updateParamMap___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_mkInitParamMap___closed__1;
lean_object* l_Lean_IR_inferBorrow___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_HasToString___boxed(lean_object*);
extern lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__20;
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_IR_Borrow_isOwned(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_mkInitParamMap(lean_object*, lean_object*);
lean_object* l_Lean_Format_pretty(lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_markModifiedParamMap(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_formatParams___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_IR_Borrow_collectDecls___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_AssocList_contains___main___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_whileModifingOwnedAux___main___at_Lean_IR_Borrow_collectDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_Borrow_ApplyParamMap_visitDecls___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_foldlM___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_updateParamSet___boxed(lean_object*, lean_object*);
lean_object* l_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_InitParamMap_visitDecls(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_Borrow_Key_beq(lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_Key_Hashable___closed__1;
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_ownArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_InitParamMap_initBorrowIfNotExported(uint8_t, lean_object*);
lean_object* l_Lean_IR_Borrow_collectFnBody(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_ownArgsUsingParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_getEnv___rarg(lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_whileModifingOwnedAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_Borrow_updateParamMap___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_mkInitParamMap___boxed(lean_object*, lean_object*);
uint8_t l_Lean_IR_IRType_isObj(lean_object*);
lean_object* l_mkHashMap___at_Lean_IR_Borrow_mkInitParamMap___spec__1(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
extern lean_object* l_Lean_IR_Arg_Inhabited;
lean_object* l_HashMapImp_insert___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_Key_beq___boxed(lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_IR_Borrow_ownParamsUsingArgs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_AltCore_body(lean_object*);
lean_object* l_Lean_IR_Borrow_Lean_HasFormat;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_Borrow_ApplyParamMap_visitDecls___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_foldlM___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_moveEntries___main___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_collectExpr(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_find___main___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_AssocList_find___main___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_markModifiedParamMap___boxed(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_Lean_HasFormat___closed__1;
lean_object* l_Lean_IR_Borrow_collectFnBody___main(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_foldlM___main___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__5(lean_object*, lean_object*);
lean_object* l_HashMapImp_expand___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__3(lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_InitParamMap_visitFnBody___main(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_FnBody_isTerminal(lean_object*);
lean_object* l_Lean_IR_Borrow_ApplyParamMap_visitDecls___boxed(lean_object*, lean_object*);
size_t l_Lean_Name_hash(lean_object*);
lean_object* l_Nat_repr(lean_object*);
extern lean_object* l_Lean_IR_paramInh;
lean_object* l_Lean_IR_Borrow_ParamMap_fmt(lean_object*);
lean_object* l_Lean_IR_Borrow_collectDecls___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_collectDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_find_x3f___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_ownArgs(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_InitParamMap_initBorrow(lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_IR_Borrow_ownArgsUsingParams___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_IR_Borrow_InitParamMap_visitDecls___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_AssocList_foldlM___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__2;
lean_object* l_Lean_IR_Borrow_infer(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_IR_Borrow_collectDecls___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_InitParamMap_visitDecls___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_IR_Borrow_ownArgsUsingParams___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_IR_Borrow_ownArgsIfParam___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_updateParamMap(lean_object*, lean_object*, lean_object*);
lean_object* l_mkHashMapImp___rarg(lean_object*);
lean_object* l_Lean_IR_Borrow_HasToString(lean_object*);
lean_object* l_Lean_IR_Borrow_whileModifingParamMapAux(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Nat_forMAux___main___at_Lean_IR_Borrow_ownParamsUsingArgs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_ownParamsUsingArgs(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_IR_Borrow_collectFnBody___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_IR_Borrow_ownArgsIfParam___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isExport(lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__21;
lean_object* l_Array_forMAux___main___at_Lean_IR_Borrow_InitParamMap_visitDecls___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_applyParamMap(lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_markModifiedParamMap___rarg(lean_object*);
lean_object* l_Lean_IR_Borrow_ownParamsUsingArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_whileModifingParamMapAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_setBody(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_whileModifingOwnedAux(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Util_1__mkPanicMessage___closed__2;
extern lean_object* l_Lean_IR_JoinPointId_HasToString___closed__1;
lean_object* l_Array_forMAux___main___at_Lean_IR_Borrow_ownArgs___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_inferBorrow(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_isOwned___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_ApplyParamMap_visitDecls(lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_ownArgsIfParam(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_ownArgsUsingParams(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_ownArgsIfParam___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_Borrow_updateParamMap___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_Key_HasBeq;
lean_object* l_RBNode_findCore___main___at_Lean_IR_UniqueIds_checkId___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_InitParamMap_visitFnBody(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_InitParamMap_initBorrowIfNotExported___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_whileModifingParamMap(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_Borrow_updateParamSet___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_mix_hash(size_t, size_t);
lean_object* lean_ir_find_env_decl(lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_ownArgs___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_Key_getHash___boxed(lean_object*);
size_t l_Lean_IR_Borrow_Key_getHash(lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_IR_Borrow_ownArgs___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at_Lean_IR_Borrow_collectFnBody___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_preserveTailCall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_ownVar___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_find_x3f___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_preserveTailCall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_AssocList_replace___main___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_Key_HasBeq___closed__1;
lean_object* l_Lean_IR_FnBody_body(lean_object*);
lean_object* l_Lean_IR_Borrow_whileModifingOwned(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_updateParamSet(lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_ownArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_contains___main___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_params(lean_object*);
lean_object* l_Lean_IR_Borrow_applyParamMap___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_collectDecls(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_getParamInfo(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_ownVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_ParamMap_fmt___boxed(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_Borrow_InitParamMap_initBorrow___spec__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_infer___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_Borrow_whileModifingParamMapAux___main___at_Lean_IR_Borrow_collectDecls___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_foldlM___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__3;
uint8_t l_Lean_IR_Borrow_Key_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_name_eq(x_3, x_4);
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_name_eq(x_8, x_10);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_eq(x_9, x_11);
return x_14;
}
}
}
}
}
lean_object* l_Lean_IR_Borrow_Key_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_Borrow_Key_beq(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* _init_l_Lean_IR_Borrow_Key_HasBeq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_Borrow_Key_beq___boxed), 2, 0);
return x_1;
}
}
lean_object* _init_l_Lean_IR_Borrow_Key_HasBeq() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_Borrow_Key_HasBeq___closed__1;
return x_1;
}
}
size_t l_Lean_IR_Borrow_Key_getHash(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; size_t x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Lean_Name_hash(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = l_Lean_Name_hash(x_4);
x_7 = lean_usize_of_nat(x_5);
x_8 = lean_usize_mix_hash(x_6, x_7);
return x_8;
}
}
}
lean_object* l_Lean_IR_Borrow_Key_getHash___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_Borrow_Key_getHash(x_1);
lean_dec(x_1);
x_3 = lean_box_usize(x_2);
return x_3;
}
}
lean_object* _init_l_Lean_IR_Borrow_Key_Hashable___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_Borrow_Key_getHash___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_IR_Borrow_Key_Hashable() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_Borrow_Key_Hashable___closed__1;
return x_1;
}
}
lean_object* _init_l_AssocList_foldlM___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" -> ");
return x_1;
}
}
lean_object* _init_l_AssocList_foldlM___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_AssocList_foldlM___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_AssocList_foldlM___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Util_1__mkPanicMessage___closed__2;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_AssocList_foldlM___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_dec(x_2);
x_6 = 0;
x_7 = lean_box(1);
x_8 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*2, x_6);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_box(0);
x_11 = l_Array_iterateMAux___main___at_Lean_IR_formatParams___spec__2(x_4, x_4, x_9, x_10);
lean_dec(x_4);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = l_Lean_Name_toString___closed__1;
x_14 = l_Lean_Name_toStringWithSep___main(x_13, x_12);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*2, x_6);
x_17 = l_AssocList_foldlM___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__2;
x_18 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_6);
x_19 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_11);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_6);
x_1 = x_19;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_21 = lean_ctor_get(x_3, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_dec(x_3);
x_23 = l_Lean_Name_toString___closed__1;
x_24 = l_Lean_Name_toStringWithSep___main(x_23, x_21);
x_25 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_AssocList_foldlM___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__3;
x_27 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*2, x_6);
x_28 = l_Nat_repr(x_22);
x_29 = l_Lean_IR_JoinPointId_HasToString___closed__1;
x_30 = lean_string_append(x_29, x_28);
lean_dec(x_28);
x_31 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*2, x_6);
x_33 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_33, 0, x_8);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*2, x_6);
x_34 = l_AssocList_foldlM___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__2;
x_35 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*2, x_6);
x_36 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_11);
lean_ctor_set_uint8(x_36, sizeof(void*)*2, x_6);
x_1 = x_36;
x_2 = x_5;
goto _start;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_8 = l_AssocList_foldlM___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__1(x_4, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_3 = x_10;
x_4 = x_8;
goto _start;
}
}
}
lean_object* l_Lean_IR_Borrow_ParamMap_fmt(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_box(0);
x_5 = l_Array_iterateMAux___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__2(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = 0;
x_9 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__20;
x_10 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*2, x_8);
x_11 = l___private_Init_Lean_Compiler_IR_Format_5__formatIRType___main___closed__21;
x_12 = lean_alloc_ctor(4, 2, 1);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*2, x_8);
return x_12;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_Borrow_ParamMap_fmt___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_Borrow_ParamMap_fmt(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_Borrow_Lean_HasFormat___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_Borrow_ParamMap_fmt___boxed), 1, 0);
return x_1;
}
}
lean_object* _init_l_Lean_IR_Borrow_Lean_HasFormat() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_IR_Borrow_Lean_HasFormat___closed__1;
return x_1;
}
}
lean_object* l_Lean_IR_Borrow_HasToString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_IR_Borrow_ParamMap_fmt(x_1);
x_3 = l_Lean_Options_empty;
x_4 = l_Lean_Format_pretty(x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_IR_Borrow_HasToString___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_Borrow_HasToString(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_Borrow_InitParamMap_initBorrow___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_5 = l_Array_empty___closed__1;
x_6 = x_2;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_7 = lean_array_fget(x_2, x_1);
x_8 = lean_box(0);
lean_inc(x_7);
x_9 = x_8;
x_10 = lean_array_fset(x_2, x_1, x_9);
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
x_13 = l_Lean_IR_IRType_isObj(x_12);
x_14 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*2, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_1, x_15);
x_17 = x_14;
x_18 = lean_array_fset(x_10, x_1, x_17);
lean_dec(x_1);
x_1 = x_16;
x_2 = x_18;
goto _start;
}
}
}
lean_object* l_Lean_IR_Borrow_InitParamMap_initBorrow(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Array_umapMAux___main___at_Lean_IR_Borrow_InitParamMap_initBorrow___spec__1(x_2, x_1);
return x_3;
}
}
lean_object* l_Lean_IR_Borrow_InitParamMap_initBorrowIfNotExported(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_umapMAux___main___at_Lean_IR_Borrow_InitParamMap_initBorrow___spec__1(x_3, x_2);
return x_4;
}
else
{
return x_2;
}
}
}
lean_object* l_Lean_IR_Borrow_InitParamMap_initBorrowIfNotExported___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_IR_Borrow_InitParamMap_initBorrowIfNotExported(x_3, x_2);
return x_4;
}
}
uint8_t l_AssocList_contains___main___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = l_Lean_IR_Borrow_Key_beq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
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
lean_object* l_AssocList_foldlM___main___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__5(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_IR_Borrow_Key_getHash(x_4);
x_8 = lean_usize_modn(x_7, x_6);
lean_dec(x_6);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 2, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = l_Lean_IR_Borrow_Key_getHash(x_12);
x_17 = lean_usize_modn(x_16, x_15);
lean_dec(x_15);
x_18 = lean_array_uget(x_1, x_17);
x_19 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_array_uset(x_1, x_17, x_19);
x_1 = x_20;
x_2 = x_14;
goto _start;
}
}
}
}
lean_object* l_HashMapImp_moveEntries___main___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_AssocList_foldlM___main___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__5(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
lean_object* l_HashMapImp_expand___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_mul(x_3, x_4);
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_5, x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_HashMapImp_moveEntries___main___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__4(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_AssocList_replace___main___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = l_Lean_IR_Borrow_Key_beq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_AssocList_replace___main___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__6(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = l_Lean_IR_Borrow_Key_beq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_AssocList_replace___main___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__6(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
lean_object* l_HashMapImp_insert___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = l_Lean_IR_Borrow_Key_getHash(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_AssocList_contains___main___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__2(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_10);
x_15 = lean_array_uset(x_6, x_9, x_14);
x_16 = lean_nat_dec_le(x_13, x_7);
lean_dec(x_7);
if (x_16 == 0)
{
lean_object* x_17; 
lean_free_object(x_1);
x_17 = l_HashMapImp_expand___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__3(x_13, x_15);
return x_17;
}
else
{
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_18 = l_AssocList_replace___main___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__6(x_2, x_3, x_10);
x_19 = lean_array_uset(x_6, x_9, x_18);
lean_ctor_set(x_1, 1, x_19);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; uint8_t x_26; 
x_20 = lean_ctor_get(x_1, 0);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_1);
x_22 = lean_array_get_size(x_21);
x_23 = l_Lean_IR_Borrow_Key_getHash(x_2);
x_24 = lean_usize_modn(x_23, x_22);
x_25 = lean_array_uget(x_21, x_24);
x_26 = l_AssocList_contains___main___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__2(x_2, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_20, x_27);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 2, x_25);
x_30 = lean_array_uset(x_21, x_24, x_29);
x_31 = lean_nat_dec_le(x_28, x_22);
lean_dec(x_22);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_HashMapImp_expand___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__3(x_28, x_30);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_30);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_22);
x_34 = l_AssocList_replace___main___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__6(x_2, x_3, x_25);
x_35 = lean_array_uset(x_21, x_24, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_20);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l_Lean_IR_Borrow_InitParamMap_visitFnBody___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 3);
lean_inc(x_14);
lean_dec(x_2);
lean_inc(x_1);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_11);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Array_umapMAux___main___at_Lean_IR_Borrow_InitParamMap_initBorrow___spec__1(x_16, x_12);
x_18 = l_HashMapImp_insert___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__1(x_3, x_15, x_17);
lean_inc(x_1);
x_19 = l_Lean_IR_Borrow_InitParamMap_visitFnBody___main(x_1, x_13, x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_2 = x_14;
x_3 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
x_22 = lean_box(0);
x_4 = x_22;
goto block_10;
}
block_10:
{
uint8_t x_5; 
lean_dec(x_4);
x_5 = l_Lean_IR_FnBody_isTerminal(x_2);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_Lean_IR_FnBody_body(x_2);
lean_dec(x_2);
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
}
}
}
lean_object* l_AssocList_contains___main___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Lean_IR_Borrow_InitParamMap_visitFnBody(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Borrow_InitParamMap_visitFnBody___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Array_forMAux___main___at_Lean_IR_Borrow_InitParamMap_visitDecls___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_3, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_array_fget(x_2, x_3);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_9, 3);
lean_inc(x_14);
lean_dec(x_9);
lean_inc(x_12);
x_15 = l_Lean_isExport(x_1, x_12);
lean_inc(x_12);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_12);
x_17 = l_Lean_IR_Borrow_InitParamMap_initBorrowIfNotExported(x_15, x_13);
x_18 = l_HashMapImp_insert___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__1(x_4, x_16, x_17);
x_19 = l_Lean_IR_Borrow_InitParamMap_visitFnBody___main(x_12, x_14, x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_3 = x_11;
x_4 = x_20;
goto _start;
}
else
{
lean_dec(x_9);
x_3 = x_11;
goto _start;
}
}
}
}
lean_object* l_Lean_IR_Borrow_InitParamMap_visitDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_forMAux___main___at_Lean_IR_Borrow_InitParamMap_visitDecls___spec__1(x_1, x_2, x_4, x_3);
return x_5;
}
}
lean_object* l_Array_forMAux___main___at_Lean_IR_Borrow_InitParamMap_visitDecls___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_forMAux___main___at_Lean_IR_Borrow_InitParamMap_visitDecls___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_Borrow_InitParamMap_visitDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Borrow_InitParamMap_visitDecls(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_mkHashMap___at_Lean_IR_Borrow_mkInitParamMap___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_Borrow_mkInitParamMap___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_Lean_IR_Borrow_mkInitParamMap(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_IR_Borrow_mkInitParamMap___closed__1;
x_5 = l_Array_forMAux___main___at_Lean_IR_Borrow_InitParamMap_visitDecls___spec__1(x_1, x_2, x_3, x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_Lean_IR_Borrow_mkInitParamMap___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_Borrow_mkInitParamMap(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_AssocList_find___main___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = l_Lean_IR_Borrow_Key_beq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
lean_object* l_HashMapImp_find_x3f___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_IR_Borrow_Key_getHash(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_find___main___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
lean_object* l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
if (lean_obj_tag(x_1) == 1)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = lean_ctor_get(x_1, 2);
x_16 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
x_17 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main(x_15, x_2, x_3);
lean_inc(x_2);
x_18 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main(x_16, x_2, x_3);
lean_inc(x_13);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_13);
x_20 = l_HashMapImp_find_x3f___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main___spec__1(x_3, x_19);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_ctor_set(x_1, 3, x_18);
lean_ctor_set(x_1, 2, x_17);
return x_1;
}
else
{
lean_object* x_21; 
lean_dec(x_14);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
lean_ctor_set(x_1, 3, x_18);
lean_ctor_set(x_1, 2, x_17);
lean_ctor_set(x_1, 1, x_21);
return x_1;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
x_24 = lean_ctor_get(x_1, 2);
x_25 = lean_ctor_get(x_1, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
lean_inc(x_2);
x_26 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main(x_24, x_2, x_3);
lean_inc(x_2);
x_27 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main(x_25, x_2, x_3);
lean_inc(x_22);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_22);
x_29 = l_HashMapImp_find_x3f___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main___spec__1(x_3, x_28);
lean_dec(x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_30, 0, x_22);
lean_ctor_set(x_30, 1, x_23);
lean_ctor_set(x_30, 2, x_26);
lean_ctor_set(x_30, 3, x_27);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_23);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_32, 0, x_22);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_26);
lean_ctor_set(x_32, 3, x_27);
return x_32;
}
}
}
else
{
lean_object* x_33; 
x_33 = lean_box(0);
x_4 = x_33;
goto block_11;
}
block_11:
{
uint8_t x_5; 
lean_dec(x_4);
x_5 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = l_Lean_IR_FnBody_body(x_1);
x_7 = lean_box(13);
x_8 = l_Lean_IR_FnBody_setBody(x_1, x_7);
x_9 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main(x_6, x_2, x_3);
x_10 = l_Lean_IR_FnBody_setBody(x_8, x_9);
return x_10;
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
}
lean_object* l_AssocList_find___main___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_AssocList_find___main___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_HashMapImp_find_x3f___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HashMapImp_find_x3f___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_Borrow_ApplyParamMap_visitDecls___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_6 = l_Array_empty___closed__1;
x_7 = x_3;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_array_fget(x_3, x_2);
x_9 = lean_box(0);
lean_inc(x_8);
x_10 = x_9;
x_11 = lean_array_fset(x_3, x_2, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_2, x_12);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_8, 2);
lean_inc(x_16);
x_17 = lean_ctor_get(x_8, 3);
lean_inc(x_17);
lean_inc(x_14);
x_18 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main(x_17, x_14, x_1);
lean_inc(x_14);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_14);
x_20 = l_HashMapImp_find_x3f___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main___spec__1(x_1, x_19);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_15);
lean_ctor_set(x_21, 2, x_16);
lean_ctor_set(x_21, 3, x_18);
x_22 = x_21;
x_23 = lean_array_fset(x_11, x_2, x_22);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_23;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_15);
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_14);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_16);
lean_ctor_set(x_26, 3, x_18);
x_27 = x_26;
x_28 = lean_array_fset(x_11, x_2, x_27);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_28;
goto _start;
}
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_inc(x_8);
x_30 = x_8;
x_31 = lean_array_fset(x_11, x_2, x_30);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_31;
goto _start;
}
}
}
}
lean_object* l_Lean_IR_Borrow_ApplyParamMap_visitDecls(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_umapMAux___main___at_Lean_IR_Borrow_ApplyParamMap_visitDecls___spec__1(x_2, x_3, x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_Borrow_ApplyParamMap_visitDecls___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at_Lean_IR_Borrow_ApplyParamMap_visitDecls___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_IR_Borrow_ApplyParamMap_visitDecls___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_Borrow_ApplyParamMap_visitDecls(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_IR_Borrow_applyParamMap(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Array_umapMAux___main___at_Lean_IR_Borrow_ApplyParamMap_visitDecls___spec__1(x_2, x_3, x_1);
return x_4;
}
}
lean_object* l_Lean_IR_Borrow_applyParamMap___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_Borrow_applyParamMap(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_IR_Borrow_markModifiedParamMap___rarg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; 
x_3 = 1;
lean_ctor_set_uint8(x_1, sizeof(void*)*2 + 1, x_3);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_9 = 1;
x_10 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set_uint8(x_10, sizeof(void*)*2, x_8);
lean_ctor_set_uint8(x_10, sizeof(void*)*2 + 1, x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
lean_object* l_Lean_IR_Borrow_markModifiedParamMap(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_Borrow_markModifiedParamMap___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_IR_Borrow_markModifiedParamMap___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_Borrow_markModifiedParamMap(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_IR_Borrow_ownVar(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 1);
x_7 = l_RBNode_findCore___main___at_Lean_IR_UniqueIds_checkId___spec__1(x_5, x_1);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_3, 1);
lean_dec(x_9);
x_10 = lean_ctor_get(x_3, 0);
lean_dec(x_10);
x_11 = lean_box(0);
x_12 = l_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_5, x_1, x_11);
x_13 = 1;
lean_ctor_set(x_3, 1, x_12);
lean_ctor_set_uint8(x_3, sizeof(void*)*2, x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
x_15 = lean_box(0);
x_16 = l_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_5, x_1, x_15);
x_17 = 1;
x_18 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 1, x_6);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_3);
return x_21;
}
}
}
lean_object* l_Lean_IR_Borrow_ownVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Borrow_ownVar(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_IR_Borrow_ownArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_IR_Borrow_ownVar(x_4, x_2, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
}
lean_object* l_Lean_IR_Borrow_ownArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Borrow_ownArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_forMAux___main___at_Lean_IR_Borrow_ownArgs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_2, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_fget(x_1, x_2);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_2, x_10);
lean_dec(x_2);
x_12 = l_Lean_IR_Borrow_ownArg(x_9, x_3, x_4);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_2 = x_11;
x_4 = x_13;
goto _start;
}
}
}
lean_object* l_Lean_IR_Borrow_ownArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_forMAux___main___at_Lean_IR_Borrow_ownArgs___spec__1(x_1, x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Array_forMAux___main___at_Lean_IR_Borrow_ownArgs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_forMAux___main___at_Lean_IR_Borrow_ownArgs___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_Borrow_ownArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Borrow_ownArgs(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_IR_Borrow_isOwned(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = l_RBNode_findCore___main___at_Lean_IR_UniqueIds_checkId___spec__1(x_4, x_1);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_6 = 0;
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
x_9 = 1;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
}
}
lean_object* l_Lean_IR_Borrow_isOwned___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Borrow_isOwned(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_Borrow_updateParamMap___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_8 = l_Array_empty___closed__1;
x_9 = x_3;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_array_fget(x_3, x_2);
x_12 = lean_box(0);
lean_inc(x_11);
x_13 = x_12;
x_14 = lean_array_fset(x_3, x_2, x_13);
x_15 = lean_ctor_get_uint8(x_11, sizeof(void*)*2);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_2, x_16);
lean_inc(x_11);
x_18 = x_11;
x_19 = lean_array_fset(x_14, x_2, x_18);
lean_dec(x_2);
x_2 = x_17;
x_3 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_11, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 1);
x_24 = l_RBNode_findCore___main___at_Lean_IR_UniqueIds_checkId___spec__1(x_23, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_22);
lean_dec(x_21);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_2, x_25);
lean_inc(x_11);
x_27 = x_11;
x_28 = lean_array_fset(x_14, x_2, x_27);
lean_dec(x_2);
x_2 = x_26;
x_3 = x_28;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_24);
x_30 = l_Lean_IR_Borrow_markModifiedParamMap___rarg(x_5);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = 0;
x_33 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_33, 0, x_21);
lean_ctor_set(x_33, 1, x_22);
lean_ctor_set_uint8(x_33, sizeof(void*)*2, x_32);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_2, x_34);
x_36 = x_33;
x_37 = lean_array_fset(x_14, x_2, x_36);
lean_dec(x_2);
x_2 = x_35;
x_3 = x_37;
x_5 = x_31;
goto _start;
}
}
}
}
}
lean_object* l_Lean_IR_Borrow_updateParamMap(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = l_HashMapImp_find_x3f___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main___spec__1(x_4, x_1);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_10 = l_Array_umapMAux___main___at_Lean_IR_Borrow_updateParamMap___spec__1(x_3, x_9, x_8, x_2, x_3);
lean_dec(x_3);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_12, 0);
x_16 = l_HashMapImp_insert___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__1(x_15, x_1, x_14);
lean_ctor_set(x_12, 0, x_16);
x_17 = lean_box(0);
lean_ctor_set(x_10, 0, x_17);
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
x_21 = lean_ctor_get_uint8(x_12, sizeof(void*)*2);
x_22 = lean_ctor_get_uint8(x_12, sizeof(void*)*2 + 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_23 = l_HashMapImp_insert___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__1(x_19, x_1, x_18);
x_24 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set_uint8(x_24, sizeof(void*)*2, x_21);
lean_ctor_set_uint8(x_24, sizeof(void*)*2 + 1, x_22);
x_25 = lean_box(0);
lean_ctor_set(x_10, 1, x_24);
lean_ctor_set(x_10, 0, x_25);
return x_10;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_26 = lean_ctor_get(x_10, 1);
x_27 = lean_ctor_get(x_10, 0);
lean_inc(x_26);
lean_inc(x_27);
lean_dec(x_10);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
x_30 = lean_ctor_get_uint8(x_26, sizeof(void*)*2);
x_31 = lean_ctor_get_uint8(x_26, sizeof(void*)*2 + 1);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_32 = x_26;
} else {
 lean_dec_ref(x_26);
 x_32 = lean_box(0);
}
x_33 = l_HashMapImp_insert___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__1(x_28, x_1, x_27);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 2);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_29);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_30);
lean_ctor_set_uint8(x_34, sizeof(void*)*2 + 1, x_31);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_Borrow_updateParamMap___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_umapMAux___main___at_Lean_IR_Borrow_updateParamMap___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_IR_Borrow_updateParamMap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Borrow_updateParamMap(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_IR_Borrow_getParamInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = l_HashMapImp_find_x3f___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main___spec__1(x_4, x_1);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ir_find_env_decl(x_7, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Array_empty___closed__1;
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = l_Lean_IR_Decl_params(x_11);
lean_dec(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
lean_dec(x_1);
x_14 = l_Array_empty___closed__1;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_ctor_get(x_5, 0);
lean_inc(x_16);
lean_dec(x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
}
}
lean_object* l_Nat_forMAux___main___at_Lean_IR_Borrow_ownArgsUsingParams___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_4, x_9);
lean_dec(x_4);
x_11 = lean_nat_sub(x_3, x_10);
x_12 = lean_nat_sub(x_11, x_9);
lean_dec(x_11);
x_13 = l_Lean_IR_Arg_Inhabited;
x_14 = lean_array_get(x_13, x_1, x_12);
x_15 = l_Lean_IR_paramInh;
x_16 = lean_array_get(x_15, x_2, x_12);
lean_dec(x_12);
x_17 = lean_ctor_get_uint8(x_16, sizeof(void*)*2);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Lean_IR_Borrow_ownArg(x_14, x_5, x_6);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_4 = x_10;
x_6 = x_19;
goto _start;
}
else
{
lean_dec(x_14);
x_4 = x_10;
goto _start;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_4);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
}
}
lean_object* l_Lean_IR_Borrow_ownArgsUsingParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_array_get_size(x_1);
lean_inc(x_5);
x_6 = l_Nat_forMAux___main___at_Lean_IR_Borrow_ownArgsUsingParams___spec__1(x_1, x_2, x_5, x_5, x_3, x_4);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_Nat_forMAux___main___at_Lean_IR_Borrow_ownArgsUsingParams___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_forMAux___main___at_Lean_IR_Borrow_ownArgsUsingParams___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_IR_Borrow_ownArgsUsingParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Borrow_ownArgsUsingParams(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Nat_forMAux___main___at_Lean_IR_Borrow_ownParamsUsingArgs___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_4, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_4, x_9);
lean_dec(x_4);
x_11 = lean_nat_sub(x_3, x_10);
x_12 = lean_nat_sub(x_11, x_9);
lean_dec(x_11);
x_13 = l_Lean_IR_Arg_Inhabited;
x_14 = lean_array_get(x_13, x_1, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_IR_paramInh;
x_17 = lean_array_get(x_16, x_2, x_12);
lean_dec(x_12);
x_18 = l_Lean_IR_Borrow_isOwned(x_15, x_5, x_6);
lean_dec(x_15);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_17);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_4 = x_10;
x_6 = x_21;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_dec(x_17);
x_25 = l_Lean_IR_Borrow_ownVar(x_24, x_5, x_23);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_4 = x_10;
x_6 = x_26;
goto _start;
}
}
else
{
lean_dec(x_12);
x_4 = x_10;
goto _start;
}
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_4);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_6);
return x_30;
}
}
}
lean_object* l_Lean_IR_Borrow_ownParamsUsingArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_array_get_size(x_1);
lean_inc(x_5);
x_6 = l_Nat_forMAux___main___at_Lean_IR_Borrow_ownParamsUsingArgs___spec__1(x_1, x_2, x_5, x_5, x_3, x_4);
lean_dec(x_5);
return x_6;
}
}
lean_object* l_Nat_forMAux___main___at_Lean_IR_Borrow_ownParamsUsingArgs___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_forMAux___main___at_Lean_IR_Borrow_ownParamsUsingArgs___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_IR_Borrow_ownParamsUsingArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Borrow_ownParamsUsingArgs(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_forMAux___main___at_Lean_IR_Borrow_ownArgsIfParam___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_3, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get(x_1, 2);
x_15 = l_RBNode_findCore___main___at_Lean_IR_UniqueIds_checkId___spec__1(x_14, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_dec(x_13);
x_3 = x_12;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_15);
x_17 = l_Lean_IR_Borrow_ownVar(x_13, x_4, x_5);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_3 = x_12;
x_5 = x_18;
goto _start;
}
}
else
{
x_3 = x_12;
goto _start;
}
}
}
}
lean_object* l_Lean_IR_Borrow_ownArgsIfParam(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Array_forMAux___main___at_Lean_IR_Borrow_ownArgsIfParam___spec__1(x_2, x_1, x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Array_forMAux___main___at_Lean_IR_Borrow_ownArgsIfParam___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forMAux___main___at_Lean_IR_Borrow_ownArgsIfParam___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_IR_Borrow_ownArgsIfParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Borrow_ownArgsIfParam(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_IR_Borrow_collectExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_IR_Borrow_ownVar(x_1, x_3, x_4);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_forMAux___main___at_Lean_IR_Borrow_ownArgsIfParam___spec__1(x_3, x_5, x_8, x_3, x_7);
lean_dec(x_5);
lean_dec(x_3);
return x_9;
}
case 1:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec(x_2);
x_11 = l_Lean_IR_Borrow_ownVar(x_1, x_3, x_4);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_IR_Borrow_ownVar(x_10, x_3, x_12);
lean_dec(x_3);
return x_13;
}
case 2:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 2);
lean_inc(x_15);
lean_dec(x_2);
x_16 = l_Lean_IR_Borrow_ownVar(x_1, x_3, x_4);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_IR_Borrow_ownVar(x_14, x_3, x_17);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Array_forMAux___main___at_Lean_IR_Borrow_ownArgsIfParam___spec__1(x_3, x_15, x_20, x_3, x_19);
lean_dec(x_15);
lean_dec(x_3);
return x_21;
}
case 3:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_dec(x_2);
x_23 = l_Lean_IR_Borrow_isOwned(x_1, x_3, x_4);
lean_dec(x_1);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
uint8_t x_26; 
lean_dec(x_22);
lean_dec(x_3);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_23, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_23, 0, x_28);
return x_23;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_dec(x_23);
x_33 = l_Lean_IR_Borrow_ownVar(x_22, x_3, x_32);
lean_dec(x_3);
return x_33;
}
}
case 6:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_34 = lean_ctor_get(x_2, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_2, 1);
lean_inc(x_35);
lean_dec(x_2);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_34);
lean_inc(x_3);
x_37 = l_Lean_IR_Borrow_getParamInfo(x_36, x_3, x_4);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_IR_Borrow_ownVar(x_1, x_3, x_39);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l_Lean_IR_Borrow_ownArgsUsingParams(x_35, x_38, x_3, x_41);
lean_dec(x_3);
lean_dec(x_38);
lean_dec(x_35);
return x_42;
}
case 7:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_2, 1);
lean_inc(x_43);
lean_dec(x_2);
x_44 = l_Lean_IR_Borrow_ownVar(x_1, x_3, x_4);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_unsigned_to_nat(0u);
x_47 = l_Array_forMAux___main___at_Lean_IR_Borrow_ownArgs___spec__1(x_43, x_46, x_3, x_45);
lean_dec(x_3);
lean_dec(x_43);
return x_47;
}
case 8:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_48 = lean_ctor_get(x_2, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_2, 1);
lean_inc(x_49);
lean_dec(x_2);
x_50 = l_Lean_IR_Borrow_ownVar(x_1, x_3, x_4);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = l_Lean_IR_Borrow_ownVar(x_48, x_3, x_51);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_unsigned_to_nat(0u);
x_55 = l_Array_forMAux___main___at_Lean_IR_Borrow_ownArgs___spec__1(x_49, x_54, x_3, x_53);
lean_dec(x_3);
lean_dec(x_49);
return x_55;
}
default: 
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_4);
return x_57;
}
}
}
}
lean_object* l_Lean_IR_Borrow_preserveTailCall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_2) == 6)
{
if (lean_obj_tag(x_3) == 11)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_3, 0);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
x_11 = lean_name_eq(x_10, x_7);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_5);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_eq(x_1, x_9);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_5);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_inc(x_7);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_7);
lean_inc(x_4);
x_18 = l_Lean_IR_Borrow_getParamInfo(x_17, x_4, x_5);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_IR_Borrow_ownParamsUsingArgs(x_8, x_19, x_4, x_20);
lean_dec(x_4);
lean_dec(x_19);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_4);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_5);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_4);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_5);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_4);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_5);
return x_27;
}
}
}
lean_object* l_Lean_IR_Borrow_preserveTailCall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_Borrow_preserveTailCall(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_Borrow_updateParamSet___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_3, x_9);
lean_dec(x_3);
x_11 = lean_box(0);
x_12 = l_RBNode_insert___at_Lean_IR_mkIndexSet___spec__1(x_4, x_8, x_11);
x_3 = x_10;
x_4 = x_12;
goto _start;
}
}
}
lean_object* l_Lean_IR_Borrow_updateParamSet(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Array_iterateMAux___main___at_Lean_IR_Borrow_updateParamSet___spec__1(x_2, x_2, x_5, x_4);
lean_ctor_set(x_1, 2, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_iterateMAux___main___at_Lean_IR_Borrow_updateParamSet___spec__1(x_2, x_2, x_10, x_9);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_11);
return x_12;
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_Borrow_updateParamSet___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_Lean_IR_Borrow_updateParamSet___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_Borrow_updateParamSet___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_Borrow_updateParamSet(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Array_forMAux___main___at_Lean_IR_Borrow_collectFnBody___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_2, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_array_fget(x_1, x_2);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_2, x_10);
lean_dec(x_2);
x_12 = l_Lean_IR_AltCore_body(x_9);
lean_dec(x_9);
lean_inc(x_3);
x_13 = l_Lean_IR_Borrow_collectFnBody___main(x_12, x_3, x_4);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_2 = x_11;
x_4 = x_14;
goto _start;
}
}
}
lean_object* l_Lean_IR_Borrow_collectFnBody___main(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 3);
lean_inc(x_13);
lean_dec(x_1);
lean_inc(x_2);
lean_inc(x_13);
x_14 = l_Lean_IR_Borrow_collectFnBody___main(x_13, x_2, x_3);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
lean_inc(x_2);
lean_inc(x_12);
lean_inc(x_11);
x_16 = l_Lean_IR_Borrow_collectExpr(x_11, x_12, x_2, x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_IR_Borrow_preserveTailCall(x_11, x_12, x_13, x_2, x_17);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
return x_18;
}
case 1:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 3);
lean_inc(x_22);
lean_dec(x_1);
lean_inc(x_2);
x_23 = l_Lean_IR_Borrow_updateParamSet(x_2, x_20);
lean_dec(x_20);
x_24 = l_Lean_IR_Borrow_collectFnBody___main(x_21, x_23, x_3);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_ctor_get(x_2, 1);
lean_inc(x_26);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_19);
x_28 = l_Lean_IR_Borrow_updateParamMap(x_27, x_2, x_25);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_1 = x_22;
x_3 = x_29;
goto _start;
}
case 10:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_1, 3);
lean_inc(x_31);
lean_dec(x_1);
x_32 = lean_unsigned_to_nat(0u);
x_33 = l_Array_forMAux___main___at_Lean_IR_Borrow_collectFnBody___main___spec__1(x_31, x_32, x_2, x_3);
lean_dec(x_31);
return x_33;
}
case 12:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 1);
lean_inc(x_35);
lean_dec(x_1);
x_36 = lean_ctor_get(x_2, 1);
lean_inc(x_36);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
lean_inc(x_2);
x_38 = l_Lean_IR_Borrow_getParamInfo(x_37, x_2, x_3);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_IR_Borrow_ownArgsUsingParams(x_35, x_39, x_2, x_40);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_Lean_IR_Borrow_ownParamsUsingArgs(x_35, x_39, x_2, x_42);
lean_dec(x_2);
lean_dec(x_39);
lean_dec(x_35);
return x_43;
}
default: 
{
lean_object* x_44; 
x_44 = lean_box(0);
x_4 = x_44;
goto block_10;
}
}
block_10:
{
uint8_t x_5; 
lean_dec(x_4);
x_5 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = l_Lean_IR_FnBody_body(x_1);
lean_dec(x_1);
x_1 = x_6;
goto _start;
}
else
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
}
}
}
lean_object* l_Array_forMAux___main___at_Lean_IR_Borrow_collectFnBody___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_forMAux___main___at_Lean_IR_Borrow_collectFnBody___main___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_Borrow_collectFnBody(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Borrow_collectFnBody___main(x_1, x_2, x_3);
return x_4;
}
}
lean_object* l_Lean_IR_Borrow_whileModifingOwnedAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
lean_dec(x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
uint8_t x_6; lean_object* x_7; uint8_t x_8; 
x_6 = 0;
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_6);
lean_inc(x_1);
lean_inc(x_3);
x_7 = lean_apply_2(x_1, x_3, x_4);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_ctor_get_uint8(x_9, sizeof(void*)*2);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_1);
x_12 = lean_box(0);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; 
lean_free_object(x_7);
x_13 = lean_box(0);
x_2 = x_13;
x_4 = x_9;
goto _start;
}
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_3);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = lean_box(0);
x_2 = x_19;
x_4 = x_15;
goto _start;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_ctor_get(x_4, 1);
x_23 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_4);
x_24 = 0;
x_25 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 1, x_23);
lean_inc(x_1);
lean_inc(x_3);
x_26 = lean_apply_2(x_1, x_3, x_25);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
x_29 = lean_ctor_get_uint8(x_27, sizeof(void*)*2);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_3);
lean_dec(x_1);
x_30 = lean_box(0);
if (lean_is_scalar(x_28)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_28;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
return x_31;
}
else
{
lean_object* x_32; 
lean_dec(x_28);
x_32 = lean_box(0);
x_2 = x_32;
x_4 = x_27;
goto _start;
}
}
}
}
lean_object* l_Lean_IR_Borrow_whileModifingOwnedAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Borrow_whileModifingOwnedAux___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_IR_Borrow_whileModifingOwned(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_Lean_IR_Borrow_whileModifingOwnedAux___main(x_1, x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Lean_IR_Borrow_whileModifingOwnedAux___main___at_Lean_IR_Borrow_collectDecl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
lean_dec(x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
uint8_t x_6; lean_object* x_7; uint8_t x_8; 
x_6 = 0;
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_6);
lean_inc(x_3);
lean_inc(x_1);
x_7 = l_Lean_IR_Borrow_collectFnBody___main(x_1, x_3, x_4);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_ctor_get_uint8(x_9, sizeof(void*)*2);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_1);
x_12 = lean_box(0);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; 
lean_free_object(x_7);
x_13 = lean_box(0);
x_2 = x_13;
x_4 = x_9;
goto _start;
}
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_3);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = lean_box(0);
x_2 = x_19;
x_4 = x_15;
goto _start;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_ctor_get(x_4, 1);
x_23 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_4);
x_24 = 0;
x_25 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_24);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 1, x_23);
lean_inc(x_3);
lean_inc(x_1);
x_26 = l_Lean_IR_Borrow_collectFnBody___main(x_1, x_3, x_25);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
x_29 = lean_ctor_get_uint8(x_27, sizeof(void*)*2);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_3);
lean_dec(x_1);
x_30 = lean_box(0);
if (lean_is_scalar(x_28)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_28;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
return x_31;
}
else
{
lean_object* x_32; 
lean_dec(x_28);
x_32 = lean_box(0);
x_2 = x_32;
x_4 = x_27;
goto _start;
}
}
}
}
lean_object* l_Lean_IR_Borrow_collectDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_dec(x_1);
lean_inc(x_2);
x_7 = l_Lean_IR_Borrow_updateParamSet(x_2, x_5);
lean_dec(x_5);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 1);
lean_dec(x_10);
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
lean_inc(x_4);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 0, x_8);
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_3, 1);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_3, 1, x_14);
x_15 = lean_box(0);
lean_inc(x_7);
x_16 = l_Lean_IR_Borrow_whileModifingOwnedAux___main___at_Lean_IR_Borrow_collectDecl___spec__1(x_6, x_15, x_7, x_3);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_4);
x_19 = l_Lean_IR_Borrow_updateParamMap(x_18, x_7, x_17);
lean_dec(x_7);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_ctor_get(x_3, 0);
x_21 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
x_22 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 1);
lean_inc(x_20);
lean_dec(x_3);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*2, x_21);
lean_ctor_set_uint8(x_24, sizeof(void*)*2 + 1, x_22);
x_25 = lean_box(0);
lean_inc(x_7);
x_26 = l_Lean_IR_Borrow_whileModifingOwnedAux___main___at_Lean_IR_Borrow_collectDecl___spec__1(x_6, x_25, x_7, x_24);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_4);
x_29 = l_Lean_IR_Borrow_updateParamMap(x_28, x_7, x_27);
lean_dec(x_7);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_30 = lean_ctor_get(x_7, 2);
lean_inc(x_30);
lean_dec(x_7);
lean_inc(x_4);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_8);
lean_ctor_set(x_31, 1, x_4);
lean_ctor_set(x_31, 2, x_30);
x_32 = lean_ctor_get(x_3, 0);
lean_inc(x_32);
x_33 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
x_34 = lean_ctor_get_uint8(x_3, sizeof(void*)*2 + 1);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 x_35 = x_3;
} else {
 lean_dec_ref(x_3);
 x_35 = lean_box(0);
}
x_36 = lean_box(0);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 2);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*2, x_33);
lean_ctor_set_uint8(x_37, sizeof(void*)*2 + 1, x_34);
x_38 = lean_box(0);
lean_inc(x_31);
x_39 = l_Lean_IR_Borrow_whileModifingOwnedAux___main___at_Lean_IR_Borrow_collectDecl___spec__1(x_6, x_38, x_31, x_37);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_4);
x_42 = l_Lean_IR_Borrow_updateParamMap(x_41, x_31, x_40);
lean_dec(x_31);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_2);
lean_dec(x_1);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_3);
return x_44;
}
}
}
lean_object* l_Lean_IR_Borrow_whileModifingParamMapAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
lean_dec(x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
uint8_t x_6; lean_object* x_7; uint8_t x_8; 
x_6 = 0;
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 1, x_6);
lean_inc(x_1);
lean_inc(x_3);
x_7 = lean_apply_2(x_1, x_3, x_4);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_ctor_get_uint8(x_9, sizeof(void*)*2 + 1);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_3);
lean_dec(x_1);
x_12 = lean_box(0);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; 
lean_free_object(x_7);
x_13 = lean_box(0);
x_2 = x_13;
x_4 = x_9;
goto _start;
}
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*2 + 1);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_3);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
else
{
lean_object* x_19; 
x_19 = lean_box(0);
x_2 = x_19;
x_4 = x_15;
goto _start;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_21 = lean_ctor_get(x_4, 0);
x_22 = lean_ctor_get(x_4, 1);
x_23 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_4);
x_24 = 0;
x_25 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*2, x_23);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 1, x_24);
lean_inc(x_1);
lean_inc(x_3);
x_26 = lean_apply_2(x_1, x_3, x_25);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_28 = x_26;
} else {
 lean_dec_ref(x_26);
 x_28 = lean_box(0);
}
x_29 = lean_ctor_get_uint8(x_27, sizeof(void*)*2 + 1);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_3);
lean_dec(x_1);
x_30 = lean_box(0);
if (lean_is_scalar(x_28)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_28;
}
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
return x_31;
}
else
{
lean_object* x_32; 
lean_dec(x_28);
x_32 = lean_box(0);
x_2 = x_32;
x_4 = x_27;
goto _start;
}
}
}
}
lean_object* l_Lean_IR_Borrow_whileModifingParamMapAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Borrow_whileModifingParamMapAux___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_IR_Borrow_whileModifingParamMap(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = l_Lean_IR_Borrow_whileModifingParamMapAux___main(x_1, x_4, x_2, x_3);
return x_5;
}
}
lean_object* l_Array_forMAux___main___at_Lean_IR_Borrow_collectDecls___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_2, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_array_fget(x_1, x_2);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_2, x_10);
lean_dec(x_2);
lean_inc(x_3);
x_12 = l_Lean_IR_Borrow_collectDecl(x_9, x_3, x_4);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_2 = x_11;
x_4 = x_13;
goto _start;
}
}
}
lean_object* l_Lean_IR_Borrow_whileModifingParamMapAux___main___at_Lean_IR_Borrow_collectDecls___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
lean_dec(x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = 0;
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 1, x_6);
x_7 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_8 = l_Array_forMAux___main___at_Lean_IR_Borrow_collectDecls___spec__1(x_1, x_7, x_3, x_4);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 1);
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = lean_ctor_get_uint8(x_10, sizeof(void*)*2 + 1);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_3);
x_13 = lean_box(0);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; 
lean_free_object(x_8);
x_14 = lean_box(0);
x_2 = x_14;
x_4 = x_10;
goto _start;
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_dec(x_8);
x_17 = lean_ctor_get_uint8(x_16, sizeof(void*)*2 + 1);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
else
{
lean_object* x_20; 
x_20 = lean_box(0);
x_2 = x_20;
x_4 = x_16;
goto _start;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_22 = lean_ctor_get(x_4, 0);
x_23 = lean_ctor_get(x_4, 1);
x_24 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_4);
x_25 = 0;
x_26 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_23);
lean_ctor_set_uint8(x_26, sizeof(void*)*2, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 1, x_25);
x_27 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
x_28 = l_Array_forMAux___main___at_Lean_IR_Borrow_collectDecls___spec__1(x_1, x_27, x_3, x_26);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_30 = x_28;
} else {
 lean_dec_ref(x_28);
 x_30 = lean_box(0);
}
x_31 = lean_ctor_get_uint8(x_29, sizeof(void*)*2 + 1);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_3);
x_32 = lean_box(0);
if (lean_is_scalar(x_30)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_30;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_29);
return x_33;
}
else
{
lean_object* x_34; 
lean_dec(x_30);
x_34 = lean_box(0);
x_2 = x_34;
x_4 = x_29;
goto _start;
}
}
}
}
lean_object* l_Lean_IR_Borrow_collectDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_box(0);
x_5 = l_Lean_IR_Borrow_whileModifingParamMapAux___main___at_Lean_IR_Borrow_collectDecls___spec__2(x_1, x_4, x_2, x_3);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
lean_object* l_Array_forMAux___main___at_Lean_IR_Borrow_collectDecls___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_forMAux___main___at_Lean_IR_Borrow_collectDecls___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_Borrow_whileModifingParamMapAux___main___at_Lean_IR_Borrow_collectDecls___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_Borrow_whileModifingParamMapAux___main___at_Lean_IR_Borrow_collectDecls___spec__2(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_Borrow_collectDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_Borrow_collectDecls(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_IR_Borrow_infer(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_box(0);
x_4 = lean_box(0);
lean_inc(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 2, x_3);
x_6 = l_Lean_IR_Borrow_mkInitParamMap(x_1, x_2);
lean_dec(x_1);
x_7 = 0;
x_8 = lean_alloc_ctor(0, 2, 2);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_3);
lean_ctor_set_uint8(x_8, sizeof(void*)*2, x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*2 + 1, x_7);
x_9 = l_Lean_IR_Borrow_collectDecls(x_2, x_5, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
return x_10;
}
}
lean_object* l_Lean_IR_Borrow_infer___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_Borrow_infer(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
lean_object* l_Lean_IR_inferBorrow(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_IR_getEnv___rarg(x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Lean_IR_Borrow_infer(x_6, x_1);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_umapMAux___main___at_Lean_IR_Borrow_ApplyParamMap_visitDecls___spec__1(x_7, x_8, x_1);
lean_dec(x_7);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = l_Lean_IR_Borrow_infer(x_10, x_1);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_umapMAux___main___at_Lean_IR_Borrow_ApplyParamMap_visitDecls___spec__1(x_12, x_13, x_1);
lean_dec(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
}
lean_object* l_Lean_IR_inferBorrow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_inferBorrow(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Init_Data_Nat(lean_object*);
lean_object* initialize_Init_Lean_Compiler_ExportAttr(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_CompilerM(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_NormIds(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Compiler_IR_Borrow(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_ExportAttr(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_CompilerM(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_NormIds(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_Borrow_Key_HasBeq___closed__1 = _init_l_Lean_IR_Borrow_Key_HasBeq___closed__1();
lean_mark_persistent(l_Lean_IR_Borrow_Key_HasBeq___closed__1);
l_Lean_IR_Borrow_Key_HasBeq = _init_l_Lean_IR_Borrow_Key_HasBeq();
lean_mark_persistent(l_Lean_IR_Borrow_Key_HasBeq);
l_Lean_IR_Borrow_Key_Hashable___closed__1 = _init_l_Lean_IR_Borrow_Key_Hashable___closed__1();
lean_mark_persistent(l_Lean_IR_Borrow_Key_Hashable___closed__1);
l_Lean_IR_Borrow_Key_Hashable = _init_l_Lean_IR_Borrow_Key_Hashable();
lean_mark_persistent(l_Lean_IR_Borrow_Key_Hashable);
l_AssocList_foldlM___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__1 = _init_l_AssocList_foldlM___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__1();
lean_mark_persistent(l_AssocList_foldlM___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__1);
l_AssocList_foldlM___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__2 = _init_l_AssocList_foldlM___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__2();
lean_mark_persistent(l_AssocList_foldlM___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__2);
l_AssocList_foldlM___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__3 = _init_l_AssocList_foldlM___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__3();
lean_mark_persistent(l_AssocList_foldlM___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__3);
l_Lean_IR_Borrow_Lean_HasFormat___closed__1 = _init_l_Lean_IR_Borrow_Lean_HasFormat___closed__1();
lean_mark_persistent(l_Lean_IR_Borrow_Lean_HasFormat___closed__1);
l_Lean_IR_Borrow_Lean_HasFormat = _init_l_Lean_IR_Borrow_Lean_HasFormat();
lean_mark_persistent(l_Lean_IR_Borrow_Lean_HasFormat);
l_Lean_IR_Borrow_mkInitParamMap___closed__1 = _init_l_Lean_IR_Borrow_mkInitParamMap___closed__1();
lean_mark_persistent(l_Lean_IR_Borrow_mkInitParamMap___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
