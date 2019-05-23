// Lean compiler output
// Module: init.lean.compiler.ir.borrow
// Imports: init.lean.compiler.export init.lean.compiler.ir.compilerm init.lean.compiler.ir.normids
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_AssocList_find___main___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main___spec__2___boxed(obj*, obj*);
extern obj* l_Array_empty___closed__1;
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_HashMapImp_find___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main___spec__1(obj*, obj*);
obj* l_Lean_Format_pretty(obj*, obj*);
extern obj* l_Lean_IR_JoinPointId_HasToString___closed__1;
obj* l_Lean_IR_Borrow_ownArgs(obj*, obj*, obj*);
obj* l_Lean_IR_Borrow_ownArgsUsingParams(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Borrow_InitParamMap_initBorrowIfNotExported(uint8, obj*);
obj* l_Lean_IR_Borrow_isOwned(obj*, obj*, obj*);
obj* l_Lean_IR_Borrow_whileModifingOwnedAux___main___at_Lean_IR_Borrow_collectDecl___main___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_mforAux___main___at_Lean_IR_Borrow_ownArgs___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Borrow_Key_beq___boxed(obj*, obj*);
obj* l_Lean_IR_Borrow_applyParamMap(obj*, obj*);
uint8 l_Lean_isExport(obj*, obj*);
obj* l_Lean_IR_Borrow_HasToString___boxed(obj*);
obj* l_Lean_IR_Borrow_collectDecls(obj*, obj*, obj*);
obj* l_Lean_IR_Borrow_Key_getHash___boxed(obj*);
obj* l_Lean_IR_Decl_normalizeIds(obj*);
obj* l_Lean_IR_Borrow_Key_getHash___main___boxed(obj*);
obj* l_Lean_IR_Borrow_ownArg___boxed(obj*, obj*, obj*);
obj* l_AssocList_foldl___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__2;
obj* l_Lean_IR_Borrow_preserveTailCall(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Borrow_InitParamMap_visitDecls(obj*, obj*, obj*);
obj* l_Lean_IR_Borrow_Lean_HasFormat;
obj* l_Array_miterateAux___main___at_Lean_IR_Borrow_updateParamSet___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Borrow_ParamMap_fmt___closed__1;
obj* l_Lean_IR_Borrow_updateParamMap___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_Borrow_whileModifingOwnedAux___main___at_Lean_IR_Borrow_collectDecl___main___spec__1(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main___boxed(obj*, obj*, obj*);
obj* l_Nat_mforAux___main___at_Lean_IR_Borrow_ownArgsUsingParams___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Name_toStringWithSep___main(obj*, obj*);
obj* l_Lean_IR_Borrow_infer___boxed(obj*, obj*);
obj* l_Nat_mforAux___main___at_Lean_IR_Borrow_ownParamsUsingArgs___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Borrow_ParamMap_fmt___closed__2;
obj* l_RBNode_findCore___main___at_Lean_IR_UniqueIds_checkId___spec__1(obj*, obj*);
obj* l_Lean_IR_Borrow_ownArg(obj*, obj*, obj*);
obj* l_AssocList_contains___main___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__2___boxed(obj*, obj*);
obj* l_Array_mforAux___main___at_Lean_IR_Borrow_ownArgsIfParam___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Borrow_InitParamMap_visitDecls___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_Borrow_ParamMap_fmt___boxed(obj*);
obj* l_Lean_IR_Borrow_ownParamsUsingArgs(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Options_empty;
obj* l_Lean_IR_Borrow_whileModifingParamMapAux(obj*, obj*, obj*, obj*);
uint8 l_Lean_IR_IRType_isObj___main(uint8);
obj* l_Lean_IR_Borrow_ownArgsIfParam___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_Borrow_preserveTailCall___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Borrow_whileModifingOwnedAux___main(obj*, obj*, obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_Borrow_updateParamMap___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_Borrow_ApplyParamMap_visitDecls___spec__1(obj*, obj*, obj*);
obj* l_Lean_IR_Borrow_collectDecl___main(obj*, obj*, obj*);
obj* l_AssocList_foldl___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__1;
obj* l_Lean_IR_Borrow_getParamInfo(obj*, obj*, obj*);
obj* l_Lean_IR_Borrow_whileModifingParamMapAux___main___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_mforAux___main___at_Lean_IR_Borrow_InitParamMap_visitDecls___spec__1(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Borrow_applyParamMap___boxed(obj*, obj*);
obj* l_Lean_IR_Borrow_isOwned___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_Borrow_whileModifingOwnedAux___main___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Borrow_collectDecl(obj*, obj*, obj*);
obj* l_Nat_repr(obj*);
obj* l_Lean_IR_Borrow_Key_HasBeq;
obj* l_Lean_IR_Borrow_whileModifingOwnedAux(obj*, obj*, obj*, obj*);
extern "C" usize lean_name_hash_usize(obj*);
uint8 l_AssocList_contains___main___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__2(obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_Nat_mforAux___main___at_Lean_IR_Borrow_ownParamsUsingArgs___spec__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Array_mforAux___main___at_Lean_IR_Borrow_ownArgsIfParam___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_inferBorrow___boxed(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Lean_IR_inferBorrow(obj*, obj*, obj*);
obj* l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main(obj*, obj*, obj*);
uint8 l_Lean_IR_FnBody_isTerminal___main(obj*);
obj* l_Lean_IR_Borrow_InitParamMap_visitFnBody___main(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_formatParams___spec__2(obj*, obj*, obj*, obj*);
obj* l_HashMapImp_insert___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__1(obj*, obj*, obj*);
obj* l_RBNode_insert___at_Lean_IR_UniqueIds_checkId___spec__2(obj*, obj*, obj*);
obj* l_Lean_IR_Borrow_ownParamsUsingArgs___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Borrow_ApplyParamMap_visitDecls___boxed(obj*, obj*);
obj* l_Lean_IR_Borrow_collectFnBody(obj*, obj*, obj*);
obj* l_Lean_IR_Borrow_whileModifingOwned(obj*, obj*, obj*);
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_AssocList_foldl___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__1(obj*, obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_mkHashMap___at_Lean_IR_Borrow_mkInitParamMap___spec__1(obj*);
obj* l_Lean_IR_Borrow_mkInitParamMap___boxed(obj*, obj*);
obj* l_Array_mforAux___main___at_Lean_IR_Borrow_collectFnBody___main___spec__1___boxed(obj*, obj*, obj*, obj*);
extern obj* l_Lean_IR_paramInh;
obj* l_Lean_IR_Borrow_ApplyParamMap_visitDecls(obj*, obj*);
uint8 l_Lean_IR_Borrow_Key_beq(obj*, obj*);
obj* l_Lean_IR_Borrow_whileModifingOwnedAux___boxed(obj*, obj*, obj*, obj*);
usize l_Lean_IR_Borrow_Key_getHash(obj*);
obj* l_HashMapImp_find___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main___spec__1___boxed(obj*, obj*);
obj* l_Lean_IR_Borrow_whileModifingParamMapAux___main(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Borrow_whileModifingParamMapAux___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Borrow_InitParamMap_initBorrow(obj*);
obj* l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_Borrow_ParamMap_fmt(obj*);
obj* l_AssocList_foldl___main___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__5(obj*, obj*);
obj* l_Lean_IR_Borrow_ownVar___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_Borrow_infer(obj*, obj*);
obj* l_Lean_IR_Borrow_getParamInfo___boxed(obj*, obj*, obj*);
obj* l_Array_mforAux___main___at_Lean_IR_Borrow_InitParamMap_visitDecls___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Borrow_updateParamMap(obj*, obj*, obj*);
obj* l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(obj*, obj*, obj*);
obj* l_Lean_IR_Borrow_collectExpr(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Borrow_ownArgs___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_Borrow_markModifiedParamMap___rarg(obj*);
obj* l_Lean_IR_Borrow_whileModifingParamMapAux___main___at_Lean_IR_Borrow_collectDecls___spec__2(obj*, obj*, obj*, obj*);
obj* l_Array_mforAux___main___at_Lean_IR_Borrow_collectDecls___spec__1(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Borrow_ownVar(obj*, obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_Borrow_InitParamMap_initBorrow___spec__1(obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_Borrow_ApplyParamMap_visitDecls___spec__1___closed__1;
obj* l_Lean_IR_Borrow_markModifiedParamMap___boxed(obj*);
obj* l_Lean_IR_AltCore_body___main(obj*);
obj* l_Lean_IR_Borrow_ownArgsUsingParams___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Array_hmmapAux___main___at_Lean_IR_inferBorrow___spec__1(obj*, obj*);
obj* l_Lean_IR_Borrow_InitParamMap_initBorrowIfNotExported___boxed(obj*, obj*);
obj* l_Lean_IR_findEnvDecl(obj*, obj*);
namespace lean {
usize usize_modn(usize, obj*);
}
namespace lean {
usize usize_mix_hash(usize, usize);
}
obj* l_Array_hmmapAux___main___at_Lean_IR_Borrow_ApplyParamMap_visitDecls___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_IR_getEnv___rarg(obj*);
obj* l_Lean_IR_Decl_params___main(obj*);
obj* l_Lean_IR_Borrow_Key_Hashable;
obj* l_Array_mforAux___main___at_Lean_IR_Borrow_ownArgs___spec__1(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Borrow_whileModifingParamMap(obj*, obj*, obj*);
obj* l_mkHashMapImp___rarg(obj*);
obj* l_Lean_IR_Borrow_updateParamSet(obj*, obj*);
obj* l_Lean_IR_Borrow_whileModifingParamMapAux___main___at_Lean_IR_Borrow_collectDecls___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_FnBody_setBody___main(obj*, obj*);
obj* l_Nat_mforAux___main___at_Lean_IR_Borrow_ownArgsUsingParams___spec__1(obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_withParams___spec__2___closed__1;
obj* l_Array_mforAux___main___at_Lean_IR_Borrow_collectFnBody___main___spec__1(obj*, obj*, obj*, obj*);
obj* l_Array_mforAux___main___at_Lean_IR_Borrow_collectDecls___spec__1___boxed(obj*, obj*, obj*, obj*);
usize l_Lean_IR_Borrow_Key_getHash___main(obj*);
obj* l_Lean_IR_Borrow_markModifiedParamMap(obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__2(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Borrow_updateParamSet___boxed(obj*, obj*);
obj* l_Lean_IR_FnBody_body___main(obj*);
extern obj* l_Lean_Name_toString___closed__1;
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
namespace lean {
usize usize_of_nat(obj*);
}
obj* l_Lean_IR_Borrow_mkInitParamMap___closed__1;
obj* l_Lean_IR_Borrow_Key_beq___main___boxed(obj*, obj*);
obj* l_Lean_IR_Borrow_collectDecls___boxed(obj*, obj*, obj*);
uint8 l_Lean_IR_Borrow_Key_beq___main(obj*, obj*);
obj* l_Lean_IR_Borrow_collectExpr___main(obj*, obj*, obj*, obj*);
obj* l_AssocList_replace___main___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__6(obj*, obj*, obj*);
obj* l_Array_miterateAux___main___at_Lean_IR_Borrow_updateParamSet___spec__1(obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Borrow_ownArgsIfParam(obj*, obj*, obj*);
namespace lean {
obj* nat_mul(obj*, obj*);
}
obj* l_Array_hmmapAux___main___at_Lean_IR_Borrow_updateParamMap___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_IR_Borrow_HasToString(obj*);
obj* l_Lean_IR_Borrow_collectFnBody___main(obj*, obj*, obj*);
obj* l_Lean_IR_Borrow_InitParamMap_visitFnBody(obj*, obj*, obj*);
obj* l_HashMapImp_expand___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__3(obj*, obj*);
obj* l_Lean_IR_Borrow_mkInitParamMap(obj*, obj*);
obj* l_AssocList_find___main___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main___spec__2(obj*, obj*);
extern obj* l_Lean_IR_Arg_Inhabited;
obj* l_HashMapImp_moveEntries___main___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__4(obj*, obj*, obj*);
uint8 l_Lean_IR_Borrow_Key_beq___main(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_3; uint8 x_4; 
x_2 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean_name_dec_eq(x_2, x_3);
return x_4;
}
else
{
uint8 x_5; 
x_5 = 0;
return x_5;
}
}
else
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_6; 
x_6 = 0;
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; uint8 x_11; 
x_7 = lean::cnstr_get(x_0, 0);
x_8 = lean::cnstr_get(x_0, 1);
x_9 = lean::cnstr_get(x_1, 0);
x_10 = lean::cnstr_get(x_1, 1);
x_11 = lean_name_dec_eq(x_7, x_9);
if (x_11 == 0)
{
uint8 x_12; 
x_12 = 0;
return x_12;
}
else
{
uint8 x_13; 
x_13 = lean::nat_dec_eq(x_8, x_10);
return x_13;
}
}
}
}
}
obj* l_Lean_IR_Borrow_Key_beq___main___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_IR_Borrow_Key_beq___main(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
uint8 l_Lean_IR_Borrow_Key_beq(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_Lean_IR_Borrow_Key_beq___main(x_0, x_1);
return x_2;
}
}
obj* l_Lean_IR_Borrow_Key_beq___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_Lean_IR_Borrow_Key_beq(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l_Lean_IR_Borrow_Key_HasBeq() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_Borrow_Key_beq___boxed), 2, 0);
return x_0;
}
}
usize l_Lean_IR_Borrow_Key_getHash___main(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; usize x_2; 
x_1 = lean::cnstr_get(x_0, 0);
x_2 = lean_name_hash_usize(x_1);
return x_2;
}
else
{
obj* x_3; obj* x_4; usize x_5; usize x_6; usize x_7; 
x_3 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
x_5 = lean_name_hash_usize(x_3);
x_6 = lean::usize_of_nat(x_4);
x_7 = lean::usize_mix_hash(x_5, x_6);
return x_7;
}
}
}
obj* l_Lean_IR_Borrow_Key_getHash___main___boxed(obj* x_0) {
_start:
{
usize x_1; obj* x_2; 
x_1 = l_Lean_IR_Borrow_Key_getHash___main(x_0);
x_2 = lean::box_size_t(x_1);
lean::dec(x_0);
return x_2;
}
}
usize l_Lean_IR_Borrow_Key_getHash(obj* x_0) {
_start:
{
usize x_1; 
x_1 = l_Lean_IR_Borrow_Key_getHash___main(x_0);
return x_1;
}
}
obj* l_Lean_IR_Borrow_Key_getHash___boxed(obj* x_0) {
_start:
{
usize x_1; obj* x_2; 
x_1 = l_Lean_IR_Borrow_Key_getHash(x_0);
x_2 = lean::box_size_t(x_1);
lean::dec(x_0);
return x_2;
}
}
obj* _init_l_Lean_IR_Borrow_Key_Hashable() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_Borrow_Key_getHash___boxed), 1, 0);
return x_0;
}
}
obj* _init_l_AssocList_foldl___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string(" -> ");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_AssocList_foldl___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string(":");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_AssocList_foldl___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__1(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_4; obj* x_6; uint8 x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 2);
lean::inc(x_6);
lean::dec(x_1);
x_9 = 0;
x_10 = lean::box(1);
x_11 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_11, 0, x_0);
lean::cnstr_set(x_11, 1, x_10);
lean::cnstr_set_scalar(x_11, sizeof(void*)*2, x_9);
x_12 = x_11;
x_13 = lean::mk_nat_obj(0ul);
x_14 = lean::box(0);
x_15 = l_Array_miterateAux___main___at_Lean_IR_formatParams___spec__2(x_4, x_4, x_13, x_14);
lean::dec(x_4);
if (lean::obj_tag(x_2) == 0)
{
obj* x_17; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_17 = lean::cnstr_get(x_2, 0);
lean::inc(x_17);
lean::dec(x_2);
x_20 = l_Lean_Name_toString___closed__1;
x_21 = l_Lean_Name_toStringWithSep___main(x_20, x_17);
x_22 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_22, 0, x_21);
x_23 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_23, 0, x_12);
lean::cnstr_set(x_23, 1, x_22);
lean::cnstr_set_scalar(x_23, sizeof(void*)*2, x_9);
x_24 = x_23;
x_25 = l_AssocList_foldl___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__1;
x_26 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_25);
lean::cnstr_set_scalar(x_26, sizeof(void*)*2, x_9);
x_27 = x_26;
x_28 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_15);
lean::cnstr_set_scalar(x_28, sizeof(void*)*2, x_9);
x_29 = x_28;
x_0 = x_29;
x_1 = x_6;
goto _start;
}
else
{
obj* x_31; obj* x_33; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_31 = lean::cnstr_get(x_2, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_2, 1);
lean::inc(x_33);
lean::dec(x_2);
x_36 = l_Lean_Name_toString___closed__1;
x_37 = l_Lean_Name_toStringWithSep___main(x_36, x_31);
x_38 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_38, 0, x_37);
x_39 = l_AssocList_foldl___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__2;
x_40 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_40, 0, x_38);
lean::cnstr_set(x_40, 1, x_39);
lean::cnstr_set_scalar(x_40, sizeof(void*)*2, x_9);
x_41 = x_40;
x_42 = l_Nat_repr(x_33);
x_43 = l_Lean_IR_JoinPointId_HasToString___closed__1;
x_44 = lean::string_append(x_43, x_42);
lean::dec(x_42);
x_46 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_46, 0, x_44);
x_47 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_47, 0, x_41);
lean::cnstr_set(x_47, 1, x_46);
lean::cnstr_set_scalar(x_47, sizeof(void*)*2, x_9);
x_48 = x_47;
x_49 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_49, 0, x_12);
lean::cnstr_set(x_49, 1, x_48);
lean::cnstr_set_scalar(x_49, sizeof(void*)*2, x_9);
x_50 = x_49;
x_51 = l_AssocList_foldl___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__1;
x_52 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_52, 0, x_50);
lean::cnstr_set(x_52, 1, x_51);
lean::cnstr_set_scalar(x_52, sizeof(void*)*2, x_9);
x_53 = x_52;
x_54 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_15);
lean::cnstr_set_scalar(x_54, sizeof(void*)*2, x_9);
x_55 = x_54;
x_0 = x_55;
x_1 = x_6;
goto _start;
}
}
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_1);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
lean::dec(x_2);
return x_3;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::array_fget(x_1, x_2);
x_9 = l_AssocList_foldl___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__1(x_3, x_8);
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_add(x_2, x_10);
lean::dec(x_2);
x_2 = x_11;
x_3 = x_9;
goto _start;
}
}
}
obj* _init_l_Lean_IR_Borrow_ParamMap_fmt___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("{");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_Borrow_ParamMap_fmt___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("}");
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Lean_IR_Borrow_ParamMap_fmt(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; uint8 x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_1 = lean::cnstr_get(x_0, 1);
x_2 = lean::mk_nat_obj(0ul);
x_3 = lean::box(0);
x_4 = l_Array_miterateAux___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__2(x_0, x_1, x_2, x_3);
x_5 = lean::mk_nat_obj(1ul);
x_6 = lean::alloc_cnstr(3, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_4);
x_7 = 0;
x_8 = l_Lean_IR_Borrow_ParamMap_fmt___closed__1;
x_9 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_6);
lean::cnstr_set_scalar(x_9, sizeof(void*)*2, x_7);
x_10 = x_9;
x_11 = l_Lean_IR_Borrow_ParamMap_fmt___closed__2;
x_12 = lean::alloc_cnstr(4, 2, 1);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
lean::cnstr_set_scalar(x_12, sizeof(void*)*2, x_7);
x_13 = x_12;
return x_13;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_miterateAux___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__2(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_Borrow_ParamMap_fmt___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_Borrow_ParamMap_fmt(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_Borrow_Lean_HasFormat() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_Borrow_ParamMap_fmt___boxed), 1, 0);
return x_0;
}
}
obj* l_Lean_IR_Borrow_HasToString(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_IR_Borrow_ParamMap_fmt(x_0);
x_2 = l_Lean_Options_empty;
x_3 = l_Lean_Format_pretty(x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_Borrow_HasToString___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_Borrow_HasToString(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_Borrow_InitParamMap_initBorrow___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::array_get_size(x_1);
x_3 = lean::nat_dec_lt(x_0, x_2);
lean::dec(x_2);
if (x_3 == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; uint8 x_11; obj* x_12; uint8 x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_6 = lean::array_fget(x_1, x_0);
x_7 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_withParams___spec__2___closed__1;
x_8 = lean::array_fset(x_1, x_0, x_7);
x_9 = lean::cnstr_get(x_6, 0);
x_11 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1 + 1);
if (lean::is_exclusive(x_6)) {
 x_12 = x_6;
} else {
 lean::inc(x_9);
 lean::dec(x_6);
 x_12 = lean::box(0);
}
x_13 = l_Lean_IR_IRType_isObj___main(x_11);
if (lean::is_scalar(x_12)) {
 x_14 = lean::alloc_cnstr(0, 1, 2);
} else {
 x_14 = x_12;
}
lean::cnstr_set(x_14, 0, x_9);
lean::cnstr_set_scalar(x_14, sizeof(void*)*1, x_13);
x_15 = x_14;
lean::cnstr_set_scalar(x_15, sizeof(void*)*1 + 1, x_11);
x_16 = x_15;
x_17 = lean::mk_nat_obj(1ul);
x_18 = lean::nat_add(x_0, x_17);
x_19 = lean::array_fset(x_8, x_0, x_16);
lean::dec(x_0);
x_0 = x_18;
x_1 = x_19;
goto _start;
}
}
}
obj* l_Lean_IR_Borrow_InitParamMap_initBorrow(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_nat_obj(0ul);
x_2 = l_Array_hmmapAux___main___at_Lean_IR_Borrow_InitParamMap_initBorrow___spec__1(x_1, x_0);
return x_2;
}
}
obj* l_Lean_IR_Borrow_InitParamMap_initBorrowIfNotExported(uint8 x_0, obj* x_1) {
_start:
{
if (x_0 == 0)
{
obj* x_2; obj* x_3; 
x_2 = lean::mk_nat_obj(0ul);
x_3 = l_Array_hmmapAux___main___at_Lean_IR_Borrow_InitParamMap_initBorrow___spec__1(x_2, x_1);
return x_3;
}
else
{
return x_1;
}
}
}
obj* l_Lean_IR_Borrow_InitParamMap_initBorrowIfNotExported___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = lean::unbox(x_0);
x_3 = l_Lean_IR_Borrow_InitParamMap_initBorrowIfNotExported(x_2, x_1);
return x_3;
}
}
uint8 l_AssocList_contains___main___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__2(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
uint8 x_2; 
x_2 = 0;
return x_2;
}
else
{
obj* x_3; obj* x_4; uint8 x_5; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 2);
x_5 = l_Lean_IR_Borrow_Key_beq___main(x_3, x_0);
if (x_5 == 0)
{
x_1 = x_4;
goto _start;
}
else
{
uint8 x_7; 
x_7 = 1;
return x_7;
}
}
}
}
obj* l_AssocList_foldl___main___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__5(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
return x_0;
}
else
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_9; usize x_10; usize x_11; obj* x_13; obj* x_14; obj* x_15; 
x_2 = lean::cnstr_get(x_1, 0);
x_4 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
if (lean::is_exclusive(x_1)) {
 x_8 = x_1;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_1);
 x_8 = lean::box(0);
}
x_9 = lean::array_get_size(x_0);
x_10 = l_Lean_IR_Borrow_Key_getHash___main(x_2);
x_11 = lean::usize_modn(x_10, x_9);
lean::dec(x_9);
x_13 = lean::array_uget(x_0, x_11);
if (lean::is_scalar(x_8)) {
 x_14 = lean::alloc_cnstr(1, 3, 0);
} else {
 x_14 = x_8;
}
lean::cnstr_set(x_14, 0, x_2);
lean::cnstr_set(x_14, 1, x_4);
lean::cnstr_set(x_14, 2, x_13);
x_15 = lean::array_uset(x_0, x_11, x_14);
x_0 = x_15;
x_1 = x_6;
goto _start;
}
}
}
obj* l_HashMapImp_moveEntries___main___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_1);
x_4 = lean::nat_dec_lt(x_0, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_8 = lean::array_fget(x_1, x_0);
x_9 = lean::box(0);
x_10 = lean::array_fset(x_1, x_0, x_9);
x_11 = l_AssocList_foldl___main___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__5(x_2, x_8);
x_12 = lean::mk_nat_obj(1ul);
x_13 = lean::nat_add(x_0, x_12);
lean::dec(x_0);
x_0 = x_13;
x_1 = x_10;
x_2 = x_11;
goto _start;
}
}
}
obj* l_HashMapImp_expand___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__3(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_2 = lean::array_get_size(x_1);
x_3 = lean::mk_nat_obj(2ul);
x_4 = lean::nat_mul(x_2, x_3);
lean::dec(x_2);
x_6 = lean::box(0);
x_7 = lean::mk_array(x_4, x_6);
x_8 = lean::mk_nat_obj(0ul);
x_9 = l_HashMapImp_moveEntries___main___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__4(x_8, x_1, x_7);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_0);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
}
obj* l_AssocList_replace___main___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__6(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_1);
lean::dec(x_0);
return x_2;
}
else
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; uint8 x_12; 
x_5 = lean::cnstr_get(x_2, 0);
x_7 = lean::cnstr_get(x_2, 1);
x_9 = lean::cnstr_get(x_2, 2);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 lean::cnstr_set(x_2, 2, lean::box(0));
 x_11 = x_2;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::inc(x_9);
 lean::dec(x_2);
 x_11 = lean::box(0);
}
x_12 = l_Lean_IR_Borrow_Key_beq___main(x_5, x_0);
if (x_12 == 0)
{
obj* x_13; obj* x_14; 
x_13 = l_AssocList_replace___main___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__6(x_0, x_1, x_9);
if (lean::is_scalar(x_11)) {
 x_14 = lean::alloc_cnstr(1, 3, 0);
} else {
 x_14 = x_11;
}
lean::cnstr_set(x_14, 0, x_5);
lean::cnstr_set(x_14, 1, x_7);
lean::cnstr_set(x_14, 2, x_13);
return x_14;
}
else
{
obj* x_17; 
lean::dec(x_7);
lean::dec(x_5);
if (lean::is_scalar(x_11)) {
 x_17 = lean::alloc_cnstr(1, 3, 0);
} else {
 x_17 = x_11;
}
lean::cnstr_set(x_17, 0, x_0);
lean::cnstr_set(x_17, 1, x_1);
lean::cnstr_set(x_17, 2, x_9);
return x_17;
}
}
}
}
obj* l_HashMapImp_insert___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_7; obj* x_8; usize x_9; usize x_10; obj* x_11; uint8 x_12; 
x_3 = lean::cnstr_get(x_0, 0);
x_5 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_7 = x_0;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::dec(x_0);
 x_7 = lean::box(0);
}
x_8 = lean::array_get_size(x_5);
x_9 = l_Lean_IR_Borrow_Key_getHash___main(x_1);
x_10 = lean::usize_modn(x_9, x_8);
x_11 = lean::array_uget(x_5, x_10);
x_12 = l_AssocList_contains___main___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__2(x_1, x_11);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_16; obj* x_17; uint8 x_18; 
x_13 = lean::mk_nat_obj(1ul);
x_14 = lean::nat_add(x_3, x_13);
lean::dec(x_3);
x_16 = lean::alloc_cnstr(1, 3, 0);
lean::cnstr_set(x_16, 0, x_1);
lean::cnstr_set(x_16, 1, x_2);
lean::cnstr_set(x_16, 2, x_11);
x_17 = lean::array_uset(x_5, x_10, x_16);
x_18 = lean::nat_dec_le(x_14, x_8);
lean::dec(x_8);
if (x_18 == 0)
{
obj* x_21; 
lean::dec(x_7);
x_21 = l_HashMapImp_expand___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__3(x_14, x_17);
return x_21;
}
else
{
obj* x_22; 
if (lean::is_scalar(x_7)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_7;
}
lean::cnstr_set(x_22, 0, x_14);
lean::cnstr_set(x_22, 1, x_17);
return x_22;
}
}
else
{
obj* x_24; obj* x_25; obj* x_26; 
lean::dec(x_8);
x_24 = l_AssocList_replace___main___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__6(x_1, x_2, x_11);
x_25 = lean::array_uset(x_5, x_10, x_24);
if (lean::is_scalar(x_7)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_7;
}
lean::cnstr_set(x_26, 0, x_3);
lean::cnstr_set(x_26, 1, x_25);
return x_26;
}
}
}
obj* l_Lean_IR_Borrow_InitParamMap_visitFnBody___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
switch (lean::obj_tag(x_1)) {
case 1:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_20; obj* x_21; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_1, 2);
lean::inc(x_9);
x_11 = lean::cnstr_get(x_1, 3);
lean::inc(x_11);
lean::dec(x_1);
lean::inc(x_0);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_0);
lean::cnstr_set(x_15, 1, x_5);
x_16 = lean::mk_nat_obj(0ul);
x_17 = l_Array_hmmapAux___main___at_Lean_IR_Borrow_InitParamMap_initBorrow___spec__1(x_16, x_7);
x_18 = l_HashMapImp_insert___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__1(x_2, x_15, x_17);
lean::inc(x_0);
x_20 = l_Lean_IR_Borrow_InitParamMap_visitFnBody___main(x_0, x_9, x_18);
x_21 = lean::cnstr_get(x_20, 1);
lean::inc(x_21);
lean::dec(x_20);
x_1 = x_11;
x_2 = x_21;
goto _start;
}
default:
{
obj* x_25; 
x_25 = lean::box(0);
x_3 = x_25;
goto lbl_4;
}
}
lbl_4:
{
uint8 x_27; 
lean::dec(x_3);
x_27 = l_Lean_IR_FnBody_isTerminal___main(x_1);
if (x_27 == 0)
{
obj* x_28; 
x_28 = l_Lean_IR_FnBody_body___main(x_1);
lean::dec(x_1);
x_1 = x_28;
goto _start;
}
else
{
obj* x_33; obj* x_34; 
lean::dec(x_1);
lean::dec(x_0);
x_33 = lean::box(0);
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_2);
return x_34;
}
}
}
}
obj* l_AssocList_contains___main___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; obj* x_3; 
x_2 = l_AssocList_contains___main___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__2(x_0, x_1);
x_3 = lean::box(x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_IR_Borrow_InitParamMap_visitFnBody(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_Borrow_InitParamMap_visitFnBody___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Array_mforAux___main___at_Lean_IR_Borrow_InitParamMap_visitDecls___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_1);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_8; obj* x_9; 
lean::dec(x_2);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_3);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; 
x_10 = lean::array_fget(x_1, x_2);
x_11 = lean::mk_nat_obj(1ul);
x_12 = lean::nat_add(x_2, x_11);
lean::dec(x_2);
if (lean::obj_tag(x_10) == 0)
{
obj* x_14; obj* x_16; obj* x_18; uint8 x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_14 = lean::cnstr_get(x_10, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_10, 1);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_10, 2);
lean::inc(x_18);
lean::dec(x_10);
x_21 = l_Lean_isExport(x_0, x_14);
lean::inc(x_14);
x_23 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_23, 0, x_14);
x_24 = l_Lean_IR_Borrow_InitParamMap_initBorrowIfNotExported(x_21, x_16);
x_25 = l_HashMapImp_insert___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__1(x_3, x_23, x_24);
x_26 = l_Lean_IR_Borrow_InitParamMap_visitFnBody___main(x_14, x_18, x_25);
x_27 = lean::cnstr_get(x_26, 1);
lean::inc(x_27);
lean::dec(x_26);
x_2 = x_12;
x_3 = x_27;
goto _start;
}
else
{
lean::dec(x_10);
x_2 = x_12;
goto _start;
}
}
}
}
obj* l_Lean_IR_Borrow_InitParamMap_visitDecls(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0ul);
x_4 = l_Array_mforAux___main___at_Lean_IR_Borrow_InitParamMap_visitDecls___spec__1(x_0, x_1, x_3, x_2);
return x_4;
}
}
obj* l_Array_mforAux___main___at_Lean_IR_Borrow_InitParamMap_visitDecls___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_mforAux___main___at_Lean_IR_Borrow_InitParamMap_visitDecls___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_Borrow_InitParamMap_visitDecls___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_Borrow_InitParamMap_visitDecls(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_mkHashMap___at_Lean_IR_Borrow_mkInitParamMap___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_mkHashMapImp___rarg(x_0);
return x_1;
}
}
obj* _init_l_Lean_IR_Borrow_mkInitParamMap___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_nat_obj(8ul);
x_1 = l_mkHashMapImp___rarg(x_0);
return x_1;
}
}
obj* l_Lean_IR_Borrow_mkInitParamMap(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::mk_nat_obj(0ul);
x_3 = l_Lean_IR_Borrow_mkInitParamMap___closed__1;
x_4 = l_Array_mforAux___main___at_Lean_IR_Borrow_InitParamMap_visitDecls___spec__1(x_0, x_1, x_2, x_3);
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
lean::dec(x_4);
return x_5;
}
}
obj* l_Lean_IR_Borrow_mkInitParamMap___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_Borrow_mkInitParamMap(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_AssocList_find___main___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main___spec__2(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_7; uint8 x_10; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_1, 2);
lean::inc(x_7);
lean::dec(x_1);
x_10 = l_Lean_IR_Borrow_Key_beq___main(x_3, x_0);
lean::dec(x_3);
if (x_10 == 0)
{
lean::dec(x_5);
x_1 = x_7;
goto _start;
}
else
{
obj* x_15; 
lean::dec(x_7);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_5);
return x_15;
}
}
}
}
obj* l_HashMapImp_find___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; usize x_4; usize x_5; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_0, 1);
x_3 = lean::array_get_size(x_2);
x_4 = l_Lean_IR_Borrow_Key_getHash___main(x_1);
x_5 = lean::usize_modn(x_4, x_3);
lean::dec(x_3);
x_7 = lean::array_uget(x_2, x_5);
x_8 = l_AssocList_find___main___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main___spec__2(x_1, x_7);
return x_8;
}
}
obj* l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
switch (lean::obj_tag(x_0)) {
case 1:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_20; 
x_5 = lean::cnstr_get(x_0, 0);
x_7 = lean::cnstr_get(x_0, 1);
x_9 = lean::cnstr_get(x_0, 2);
x_11 = lean::cnstr_get(x_0, 3);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 lean::cnstr_set(x_0, 2, lean::box(0));
 lean::cnstr_set(x_0, 3, lean::box(0));
 x_13 = x_0;
} else {
 lean::inc(x_5);
 lean::inc(x_7);
 lean::inc(x_9);
 lean::inc(x_11);
 lean::dec(x_0);
 x_13 = lean::box(0);
}
lean::inc(x_1);
x_15 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main(x_9, x_1, x_2);
lean::inc(x_1);
x_17 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main(x_11, x_1, x_2);
lean::inc(x_5);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_1);
lean::cnstr_set(x_19, 1, x_5);
x_20 = l_HashMapImp_find___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main___spec__1(x_2, x_19);
lean::dec(x_19);
if (lean::obj_tag(x_20) == 0)
{
obj* x_22; 
if (lean::is_scalar(x_13)) {
 x_22 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_22 = x_13;
}
lean::cnstr_set(x_22, 0, x_5);
lean::cnstr_set(x_22, 1, x_7);
lean::cnstr_set(x_22, 2, x_15);
lean::cnstr_set(x_22, 3, x_17);
return x_22;
}
else
{
obj* x_24; obj* x_27; 
lean::dec(x_7);
x_24 = lean::cnstr_get(x_20, 0);
lean::inc(x_24);
lean::dec(x_20);
if (lean::is_scalar(x_13)) {
 x_27 = lean::alloc_cnstr(1, 4, 0);
} else {
 x_27 = x_13;
}
lean::cnstr_set(x_27, 0, x_5);
lean::cnstr_set(x_27, 1, x_24);
lean::cnstr_set(x_27, 2, x_15);
lean::cnstr_set(x_27, 3, x_17);
return x_27;
}
}
default:
{
obj* x_28; 
x_28 = lean::box(0);
x_3 = x_28;
goto lbl_4;
}
}
lbl_4:
{
uint8 x_30; 
lean::dec(x_3);
x_30 = l_Lean_IR_FnBody_isTerminal___main(x_0);
if (x_30 == 0)
{
obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_31 = l_Lean_IR_FnBody_body___main(x_0);
x_32 = lean::box(13);
x_33 = l_Lean_IR_FnBody_setBody___main(x_0, x_32);
x_34 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main(x_31, x_1, x_2);
x_35 = l_Lean_IR_FnBody_setBody___main(x_33, x_34);
return x_35;
}
else
{
lean::dec(x_1);
return x_0;
}
}
}
}
obj* l_AssocList_find___main___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_AssocList_find___main___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main___spec__2(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_HashMapImp_find___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_HashMapImp_find___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main___spec__1(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* _init_l_Array_hmmapAux___main___at_Lean_IR_Borrow_ApplyParamMap_visitDecls___spec__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; uint8 x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::mk_nat_obj(0ul);
x_1 = lean::mk_empty_array(x_0);
x_2 = lean::box(0);
x_3 = 6;
x_4 = lean::box(13);
x_5 = lean::alloc_cnstr(0, 3, 1);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_1);
lean::cnstr_set(x_5, 2, x_4);
lean::cnstr_set_scalar(x_5, sizeof(void*)*3, x_3);
x_6 = x_5;
return x_6;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_Borrow_ApplyParamMap_visitDecls___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::array_get_size(x_2);
x_4 = lean::nat_dec_lt(x_1, x_3);
lean::dec(x_3);
if (x_4 == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::array_fget(x_2, x_1);
x_8 = l_Array_hmmapAux___main___at_Lean_IR_Borrow_ApplyParamMap_visitDecls___spec__1___closed__1;
x_9 = lean::array_fset(x_2, x_1, x_8);
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_add(x_1, x_10);
if (lean::obj_tag(x_7) == 0)
{
obj* x_12; obj* x_14; uint8 x_16; obj* x_17; obj* x_19; obj* x_21; obj* x_23; obj* x_24; 
x_12 = lean::cnstr_get(x_7, 0);
x_14 = lean::cnstr_get(x_7, 1);
x_16 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*3);
x_17 = lean::cnstr_get(x_7, 2);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_set(x_7, 0, lean::box(0));
 lean::cnstr_set(x_7, 1, lean::box(0));
 lean::cnstr_set(x_7, 2, lean::box(0));
 x_19 = x_7;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::inc(x_17);
 lean::dec(x_7);
 x_19 = lean::box(0);
}
lean::inc(x_12);
x_21 = l_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main(x_17, x_12, x_0);
lean::inc(x_12);
x_23 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_23, 0, x_12);
x_24 = l_HashMapImp_find___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main___spec__1(x_0, x_23);
lean::dec(x_23);
if (lean::obj_tag(x_24) == 0)
{
obj* x_26; obj* x_27; obj* x_28; 
if (lean::is_scalar(x_19)) {
 x_26 = lean::alloc_cnstr(0, 3, 1);
} else {
 x_26 = x_19;
}
lean::cnstr_set(x_26, 0, x_12);
lean::cnstr_set(x_26, 1, x_14);
lean::cnstr_set(x_26, 2, x_21);
lean::cnstr_set_scalar(x_26, sizeof(void*)*3, x_16);
x_27 = x_26;
x_28 = lean::array_fset(x_9, x_1, x_27);
lean::dec(x_1);
x_1 = x_11;
x_2 = x_28;
goto _start;
}
else
{
obj* x_32; obj* x_35; obj* x_36; obj* x_37; 
lean::dec(x_14);
x_32 = lean::cnstr_get(x_24, 0);
lean::inc(x_32);
lean::dec(x_24);
if (lean::is_scalar(x_19)) {
 x_35 = lean::alloc_cnstr(0, 3, 1);
} else {
 x_35 = x_19;
}
lean::cnstr_set(x_35, 0, x_12);
lean::cnstr_set(x_35, 1, x_32);
lean::cnstr_set(x_35, 2, x_21);
lean::cnstr_set_scalar(x_35, sizeof(void*)*3, x_16);
x_36 = x_35;
x_37 = lean::array_fset(x_9, x_1, x_36);
lean::dec(x_1);
x_1 = x_11;
x_2 = x_37;
goto _start;
}
}
else
{
obj* x_40; 
x_40 = lean::array_fset(x_9, x_1, x_7);
lean::dec(x_1);
x_1 = x_11;
x_2 = x_40;
goto _start;
}
}
}
}
obj* l_Lean_IR_Borrow_ApplyParamMap_visitDecls(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::mk_nat_obj(0ul);
x_3 = l_Array_hmmapAux___main___at_Lean_IR_Borrow_ApplyParamMap_visitDecls___spec__1(x_1, x_2, x_0);
return x_3;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_Borrow_ApplyParamMap_visitDecls___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Array_hmmapAux___main___at_Lean_IR_Borrow_ApplyParamMap_visitDecls___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Lean_IR_Borrow_ApplyParamMap_visitDecls___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_Borrow_ApplyParamMap_visitDecls(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_IR_Borrow_applyParamMap(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::mk_nat_obj(0ul);
x_3 = l_Array_hmmapAux___main___at_Lean_IR_Borrow_ApplyParamMap_visitDecls___spec__1(x_1, x_2, x_0);
return x_3;
}
}
obj* l_Lean_IR_Borrow_applyParamMap___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_Borrow_applyParamMap(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_IR_Borrow_markModifiedParamMap___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; uint8 x_5; obj* x_6; uint8 x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_1 = lean::cnstr_get(x_0, 0);
x_3 = lean::cnstr_get(x_0, 1);
x_5 = lean::cnstr_get_scalar<uint8>(x_0, sizeof(void*)*2);
if (lean::is_exclusive(x_0)) {
 x_6 = x_0;
} else {
 lean::inc(x_1);
 lean::inc(x_3);
 lean::dec(x_0);
 x_6 = lean::box(0);
}
x_7 = 1;
if (lean::is_scalar(x_6)) {
 x_8 = lean::alloc_cnstr(0, 2, 2);
} else {
 x_8 = x_6;
}
lean::cnstr_set(x_8, 0, x_1);
lean::cnstr_set(x_8, 1, x_3);
lean::cnstr_set_scalar(x_8, sizeof(void*)*2, x_5);
x_9 = x_8;
lean::cnstr_set_scalar(x_9, sizeof(void*)*2 + 1, x_7);
x_10 = x_9;
x_11 = lean::box(0);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_10);
return x_12;
}
}
obj* l_Lean_IR_Borrow_markModifiedParamMap(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_IR_Borrow_markModifiedParamMap___rarg), 1, 0);
return x_1;
}
}
obj* l_Lean_IR_Borrow_markModifiedParamMap___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_IR_Borrow_markModifiedParamMap(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_IR_Borrow_ownVar(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; uint8 x_7; obj* x_9; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*2 + 1);
lean::inc(x_5);
x_9 = l_RBNode_findCore___main___at_Lean_IR_UniqueIds_checkId___spec__1(x_5, x_0);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; obj* x_11; obj* x_12; uint8 x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 x_10 = x_2;
} else {
 lean::dec(x_2);
 x_10 = lean::box(0);
}
x_11 = lean::box(0);
x_12 = l_RBNode_insert___at_Lean_IR_UniqueIds_checkId___spec__2(x_5, x_0, x_11);
x_13 = 1;
if (lean::is_scalar(x_10)) {
 x_14 = lean::alloc_cnstr(0, 2, 2);
} else {
 x_14 = x_10;
}
lean::cnstr_set(x_14, 0, x_3);
lean::cnstr_set(x_14, 1, x_12);
lean::cnstr_set_scalar(x_14, sizeof(void*)*2, x_13);
x_15 = x_14;
lean::cnstr_set_scalar(x_15, sizeof(void*)*2 + 1, x_7);
x_16 = x_15;
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_11);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
else
{
obj* x_22; obj* x_23; 
lean::dec(x_5);
lean::dec(x_9);
lean::dec(x_3);
lean::dec(x_0);
x_22 = lean::box(0);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_2);
return x_23;
}
}
}
obj* l_Lean_IR_Borrow_ownVar___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_Borrow_ownVar(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_IR_Borrow_ownArg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; obj* x_6; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_Lean_IR_Borrow_ownVar(x_3, x_1, x_2);
return x_6;
}
else
{
obj* x_7; obj* x_8; 
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_2);
return x_8;
}
}
}
obj* l_Lean_IR_Borrow_ownArg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_Borrow_ownArg(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Array_mforAux___main___at_Lean_IR_Borrow_ownArgs___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_0);
x_5 = lean::nat_dec_lt(x_1, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_8; obj* x_9; 
lean::dec(x_1);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_3);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_15; 
x_10 = lean::array_fget(x_0, x_1);
x_11 = lean::mk_nat_obj(1ul);
x_12 = lean::nat_add(x_1, x_11);
lean::dec(x_1);
x_14 = l_Lean_IR_Borrow_ownArg(x_10, x_2, x_3);
x_15 = lean::cnstr_get(x_14, 1);
lean::inc(x_15);
lean::dec(x_14);
x_1 = x_12;
x_3 = x_15;
goto _start;
}
}
}
obj* l_Lean_IR_Borrow_ownArgs(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::mk_nat_obj(0ul);
x_4 = l_Array_mforAux___main___at_Lean_IR_Borrow_ownArgs___spec__1(x_0, x_3, x_1, x_2);
return x_4;
}
}
obj* l_Array_mforAux___main___at_Lean_IR_Borrow_ownArgs___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_mforAux___main___at_Lean_IR_Borrow_ownArgs___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_IR_Borrow_ownArgs___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_Borrow_ownArgs(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_IR_Borrow_isOwned(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; 
x_3 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
x_5 = l_RBNode_findCore___main___at_Lean_IR_UniqueIds_checkId___spec__1(x_3, x_0);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; obj* x_7; obj* x_8; 
x_6 = 0;
x_7 = lean::box(x_6);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_2);
return x_8;
}
else
{
uint8 x_10; obj* x_11; obj* x_12; 
lean::dec(x_5);
x_10 = 1;
x_11 = lean::box(x_10);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_2);
return x_12;
}
}
}
obj* l_Lean_IR_Borrow_isOwned___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_Borrow_isOwned(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_Borrow_updateParamMap___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_2);
x_6 = lean::nat_dec_lt(x_1, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_10; 
lean::dec(x_1);
lean::dec(x_0);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_2);
lean::cnstr_set(x_10, 1, x_4);
return x_10;
}
else
{
obj* x_11; obj* x_12; obj* x_13; uint8 x_14; uint8 x_15; 
x_11 = lean::array_fget(x_2, x_1);
x_12 = l_Array_hmmapAux___main___at_Lean_IR_NormalizeIds_withParams___spec__2___closed__1;
x_13 = lean::array_fset(x_2, x_1, x_12);
x_14 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
x_15 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1 + 1);
if (x_14 == 0)
{
obj* x_16; obj* x_17; obj* x_18; 
x_16 = lean::mk_nat_obj(1ul);
x_17 = lean::nat_add(x_1, x_16);
x_18 = lean::array_fset(x_13, x_1, x_11);
lean::dec(x_1);
x_1 = x_17;
x_2 = x_18;
goto _start;
}
else
{
obj* x_21; obj* x_23; obj* x_25; 
x_21 = lean::cnstr_get(x_11, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_0, 1);
lean::inc(x_23);
x_25 = l_RBNode_findCore___main___at_Lean_IR_UniqueIds_checkId___spec__1(x_23, x_21);
if (lean::obj_tag(x_25) == 0)
{
obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_21);
x_27 = lean::mk_nat_obj(1ul);
x_28 = lean::nat_add(x_1, x_27);
x_29 = lean::array_fset(x_13, x_1, x_11);
lean::dec(x_1);
x_1 = x_28;
x_2 = x_29;
goto _start;
}
else
{
obj* x_33; obj* x_34; obj* x_35; uint8 x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_25);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_33 = x_11;
} else {
 lean::dec(x_11);
 x_33 = lean::box(0);
}
x_34 = l_Lean_IR_Borrow_markModifiedParamMap___rarg(x_4);
x_35 = lean::cnstr_get(x_34, 1);
lean::inc(x_35);
lean::dec(x_34);
x_38 = 0;
if (lean::is_scalar(x_33)) {
 x_39 = lean::alloc_cnstr(0, 1, 2);
} else {
 x_39 = x_33;
}
lean::cnstr_set(x_39, 0, x_21);
lean::cnstr_set_scalar(x_39, sizeof(void*)*1, x_38);
x_40 = x_39;
lean::cnstr_set_scalar(x_40, sizeof(void*)*1 + 1, x_15);
x_41 = x_40;
x_42 = lean::mk_nat_obj(1ul);
x_43 = lean::nat_add(x_1, x_42);
x_44 = lean::array_fset(x_13, x_1, x_41);
lean::dec(x_1);
x_1 = x_43;
x_2 = x_44;
x_4 = x_35;
goto _start;
}
}
}
}
}
obj* l_Lean_IR_Borrow_updateParamMap(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = l_HashMapImp_find___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main___spec__1(x_3, x_0);
lean::dec(x_3);
if (lean::obj_tag(x_5) == 0)
{
obj* x_8; obj* x_9; 
lean::dec(x_0);
x_8 = lean::box(0);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_2);
return x_9;
}
else
{
obj* x_10; obj* x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_23; uint8 x_25; uint8 x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
lean::dec(x_5);
x_13 = lean::mk_nat_obj(0ul);
lean::inc(x_2);
x_15 = l_Array_hmmapAux___main___at_Lean_IR_Borrow_updateParamMap___spec__1(x_2, x_13, x_10, x_1, x_2);
x_16 = lean::cnstr_get(x_15, 1);
x_18 = lean::cnstr_get(x_15, 0);
if (lean::is_exclusive(x_15)) {
 x_20 = x_15;
} else {
 lean::inc(x_18);
 lean::inc(x_16);
 lean::dec(x_15);
 x_20 = lean::box(0);
}
x_21 = lean::cnstr_get(x_16, 0);
x_23 = lean::cnstr_get(x_16, 1);
x_25 = lean::cnstr_get_scalar<uint8>(x_16, sizeof(void*)*2);
x_26 = lean::cnstr_get_scalar<uint8>(x_16, sizeof(void*)*2 + 1);
if (lean::is_exclusive(x_16)) {
 x_27 = x_16;
} else {
 lean::inc(x_21);
 lean::inc(x_23);
 lean::dec(x_16);
 x_27 = lean::box(0);
}
x_28 = l_HashMapImp_insert___at_Lean_IR_Borrow_InitParamMap_visitFnBody___main___spec__1(x_21, x_0, x_18);
if (lean::is_scalar(x_27)) {
 x_29 = lean::alloc_cnstr(0, 2, 2);
} else {
 x_29 = x_27;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_23);
lean::cnstr_set_scalar(x_29, sizeof(void*)*2, x_25);
x_30 = x_29;
lean::cnstr_set_scalar(x_30, sizeof(void*)*2 + 1, x_26);
x_31 = x_30;
x_32 = lean::box(0);
if (lean::is_scalar(x_20)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_20;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_31);
return x_33;
}
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_Borrow_updateParamMap___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_hmmapAux___main___at_Lean_IR_Borrow_updateParamMap___spec__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_Lean_IR_Borrow_updateParamMap___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_Borrow_updateParamMap(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_IR_Borrow_getParamInfo(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_5 = l_HashMapImp_find___at_Lean_IR_Borrow_ApplyParamMap_visitFnBody___main___spec__1(x_3, x_0);
lean::dec(x_3);
if (lean::obj_tag(x_5) == 0)
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::cnstr_get(x_0, 0);
x_8 = lean::cnstr_get(x_1, 0);
x_9 = l_Lean_IR_findEnvDecl(x_8, x_7);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; obj* x_11; 
x_10 = l_Array_empty___closed__1;
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_15; obj* x_17; 
x_12 = lean::cnstr_get(x_9, 0);
lean::inc(x_12);
lean::dec(x_9);
x_15 = l_Lean_IR_Decl_params___main(x_12);
lean::dec(x_12);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_2);
return x_17;
}
}
else
{
obj* x_18; obj* x_19; 
x_18 = l_Array_empty___closed__1;
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_2);
return x_19;
}
}
else
{
obj* x_20; obj* x_23; 
x_20 = lean::cnstr_get(x_5, 0);
lean::inc(x_20);
lean::dec(x_5);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_20);
lean::cnstr_set(x_23, 1, x_2);
return x_23;
}
}
}
obj* l_Lean_IR_Borrow_getParamInfo___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_Borrow_getParamInfo(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_Nat_mforAux___main___at_Lean_IR_Borrow_ownArgsUsingParams___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::mk_nat_obj(0ul);
x_7 = lean::nat_dec_eq(x_3, x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; uint8 x_19; 
x_8 = lean::mk_nat_obj(1ul);
x_9 = lean::nat_sub(x_3, x_8);
lean::dec(x_3);
x_11 = lean::nat_sub(x_2, x_9);
x_12 = lean::nat_sub(x_11, x_8);
lean::dec(x_11);
x_14 = l_Lean_IR_Arg_Inhabited;
x_15 = lean::array_get(x_14, x_0, x_12);
x_16 = l_Lean_IR_paramInh;
x_17 = lean::array_get(x_16, x_1, x_12);
lean::dec(x_12);
x_19 = lean::cnstr_get_scalar<uint8>(x_17, sizeof(void*)*1);
lean::dec(x_17);
if (x_19 == 0)
{
obj* x_21; obj* x_22; 
x_21 = l_Lean_IR_Borrow_ownArg(x_15, x_4, x_5);
x_22 = lean::cnstr_get(x_21, 1);
lean::inc(x_22);
lean::dec(x_21);
x_3 = x_9;
x_5 = x_22;
goto _start;
}
else
{
lean::dec(x_15);
x_3 = x_9;
goto _start;
}
}
else
{
obj* x_29; obj* x_30; 
lean::dec(x_3);
x_29 = lean::box(0);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_5);
return x_30;
}
}
}
obj* l_Lean_IR_Borrow_ownArgsUsingParams(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; 
x_4 = lean::array_get_size(x_0);
lean::inc(x_4);
x_6 = l_Nat_mforAux___main___at_Lean_IR_Borrow_ownArgsUsingParams___spec__1(x_0, x_1, x_4, x_4, x_2, x_3);
lean::dec(x_4);
return x_6;
}
}
obj* l_Nat_mforAux___main___at_Lean_IR_Borrow_ownArgsUsingParams___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Nat_mforAux___main___at_Lean_IR_Borrow_ownArgsUsingParams___spec__1(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_4);
return x_6;
}
}
obj* l_Lean_IR_Borrow_ownArgsUsingParams___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_Borrow_ownArgsUsingParams(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
obj* l_Nat_mforAux___main___at_Lean_IR_Borrow_ownParamsUsingArgs___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::mk_nat_obj(0ul);
x_7 = lean::nat_dec_eq(x_3, x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_15; 
x_8 = lean::mk_nat_obj(1ul);
x_9 = lean::nat_sub(x_3, x_8);
lean::dec(x_3);
x_11 = lean::nat_sub(x_2, x_9);
x_12 = lean::nat_sub(x_11, x_8);
lean::dec(x_11);
x_14 = l_Lean_IR_Arg_Inhabited;
x_15 = lean::array_get(x_14, x_0, x_12);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; obj* x_19; obj* x_20; obj* x_22; obj* x_24; uint8 x_26; 
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
lean::dec(x_15);
x_19 = l_Lean_IR_paramInh;
x_20 = lean::array_get(x_19, x_1, x_12);
lean::dec(x_12);
x_22 = l_Lean_IR_Borrow_isOwned(x_16, x_4, x_5);
lean::dec(x_16);
x_24 = lean::cnstr_get(x_22, 0);
lean::inc(x_24);
x_26 = lean::unbox(x_24);
if (x_26 == 0)
{
obj* x_28; 
lean::dec(x_20);
x_28 = lean::cnstr_get(x_22, 1);
lean::inc(x_28);
lean::dec(x_22);
x_3 = x_9;
x_5 = x_28;
goto _start;
}
else
{
obj* x_32; obj* x_35; obj* x_38; obj* x_39; 
x_32 = lean::cnstr_get(x_22, 1);
lean::inc(x_32);
lean::dec(x_22);
x_35 = lean::cnstr_get(x_20, 0);
lean::inc(x_35);
lean::dec(x_20);
x_38 = l_Lean_IR_Borrow_ownVar(x_35, x_4, x_32);
x_39 = lean::cnstr_get(x_38, 1);
lean::inc(x_39);
lean::dec(x_38);
x_3 = x_9;
x_5 = x_39;
goto _start;
}
}
else
{
lean::dec(x_12);
x_3 = x_9;
goto _start;
}
}
else
{
obj* x_46; obj* x_47; 
lean::dec(x_3);
x_46 = lean::box(0);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_5);
return x_47;
}
}
}
obj* l_Lean_IR_Borrow_ownParamsUsingArgs(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; 
x_4 = lean::array_get_size(x_0);
lean::inc(x_4);
x_6 = l_Nat_mforAux___main___at_Lean_IR_Borrow_ownParamsUsingArgs___spec__1(x_0, x_1, x_4, x_4, x_2, x_3);
lean::dec(x_4);
return x_6;
}
}
obj* l_Nat_mforAux___main___at_Lean_IR_Borrow_ownParamsUsingArgs___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Nat_mforAux___main___at_Lean_IR_Borrow_ownParamsUsingArgs___spec__1(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_4);
return x_6;
}
}
obj* l_Lean_IR_Borrow_ownParamsUsingArgs___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_Borrow_ownParamsUsingArgs(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
obj* l_Array_mforAux___main___at_Lean_IR_Borrow_ownArgsIfParam___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::array_get_size(x_1);
x_6 = lean::nat_dec_lt(x_2, x_5);
lean::dec(x_5);
if (x_6 == 0)
{
obj* x_10; obj* x_11; 
lean::dec(x_0);
lean::dec(x_2);
x_10 = lean::box(0);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_4);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_14; 
x_12 = lean::array_fget(x_1, x_2);
x_13 = lean::mk_nat_obj(1ul);
x_14 = lean::nat_add(x_2, x_13);
lean::dec(x_2);
if (lean::obj_tag(x_12) == 0)
{
obj* x_16; obj* x_19; obj* x_21; 
x_16 = lean::cnstr_get(x_12, 0);
lean::inc(x_16);
lean::dec(x_12);
x_19 = lean::cnstr_get(x_0, 2);
lean::inc(x_19);
x_21 = l_RBNode_findCore___main___at_Lean_IR_UniqueIds_checkId___spec__1(x_19, x_16);
if (lean::obj_tag(x_21) == 0)
{
lean::dec(x_16);
x_2 = x_14;
goto _start;
}
else
{
obj* x_25; obj* x_26; 
lean::dec(x_21);
x_25 = l_Lean_IR_Borrow_ownVar(x_16, x_3, x_4);
x_26 = lean::cnstr_get(x_25, 1);
lean::inc(x_26);
lean::dec(x_25);
x_2 = x_14;
x_4 = x_26;
goto _start;
}
}
else
{
x_2 = x_14;
goto _start;
}
}
}
}
obj* l_Lean_IR_Borrow_ownArgsIfParam(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; 
x_3 = lean::mk_nat_obj(0ul);
lean::inc(x_1);
x_5 = l_Array_mforAux___main___at_Lean_IR_Borrow_ownArgsIfParam___spec__1(x_1, x_0, x_3, x_1, x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_Array_mforAux___main___at_Lean_IR_Borrow_ownArgsIfParam___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Array_mforAux___main___at_Lean_IR_Borrow_ownArgsIfParam___spec__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_3);
return x_5;
}
}
obj* l_Lean_IR_Borrow_ownArgsIfParam___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_Borrow_ownArgsIfParam(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Lean_IR_Borrow_collectExpr___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_4; obj* x_7; obj* x_8; obj* x_11; obj* x_13; 
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
x_7 = l_Lean_IR_Borrow_ownVar(x_0, x_2, x_3);
x_8 = lean::cnstr_get(x_7, 1);
lean::inc(x_8);
lean::dec(x_7);
x_11 = lean::mk_nat_obj(0ul);
lean::inc(x_2);
x_13 = l_Array_mforAux___main___at_Lean_IR_Borrow_ownArgsIfParam___spec__1(x_2, x_4, x_11, x_2, x_8);
lean::dec(x_4);
lean::dec(x_2);
return x_13;
}
case 1:
{
obj* x_16; obj* x_19; obj* x_20; obj* x_23; 
x_16 = lean::cnstr_get(x_1, 1);
lean::inc(x_16);
lean::dec(x_1);
x_19 = l_Lean_IR_Borrow_ownVar(x_0, x_2, x_3);
x_20 = lean::cnstr_get(x_19, 1);
lean::inc(x_20);
lean::dec(x_19);
x_23 = l_Lean_IR_Borrow_ownVar(x_16, x_2, x_20);
lean::dec(x_2);
return x_23;
}
case 2:
{
obj* x_25; obj* x_27; obj* x_30; obj* x_31; obj* x_34; obj* x_35; obj* x_38; obj* x_40; 
x_25 = lean::cnstr_get(x_1, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_1, 2);
lean::inc(x_27);
lean::dec(x_1);
x_30 = l_Lean_IR_Borrow_ownVar(x_0, x_2, x_3);
x_31 = lean::cnstr_get(x_30, 1);
lean::inc(x_31);
lean::dec(x_30);
x_34 = l_Lean_IR_Borrow_ownVar(x_25, x_2, x_31);
x_35 = lean::cnstr_get(x_34, 1);
lean::inc(x_35);
lean::dec(x_34);
x_38 = lean::mk_nat_obj(0ul);
lean::inc(x_2);
x_40 = l_Array_mforAux___main___at_Lean_IR_Borrow_ownArgsIfParam___spec__1(x_2, x_27, x_38, x_2, x_35);
lean::dec(x_27);
lean::dec(x_2);
return x_40;
}
case 3:
{
obj* x_43; obj* x_46; obj* x_48; uint8 x_50; 
x_43 = lean::cnstr_get(x_1, 1);
lean::inc(x_43);
lean::dec(x_1);
x_46 = l_Lean_IR_Borrow_isOwned(x_0, x_2, x_3);
lean::dec(x_0);
x_48 = lean::cnstr_get(x_46, 0);
lean::inc(x_48);
x_50 = lean::unbox(x_48);
if (x_50 == 0)
{
obj* x_53; obj* x_55; obj* x_56; obj* x_57; 
lean::dec(x_2);
lean::dec(x_43);
x_53 = lean::cnstr_get(x_46, 1);
if (lean::is_exclusive(x_46)) {
 lean::cnstr_release(x_46, 0);
 x_55 = x_46;
} else {
 lean::inc(x_53);
 lean::dec(x_46);
 x_55 = lean::box(0);
}
x_56 = lean::box(0);
if (lean::is_scalar(x_55)) {
 x_57 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_57 = x_55;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_53);
return x_57;
}
else
{
obj* x_58; obj* x_61; 
x_58 = lean::cnstr_get(x_46, 1);
lean::inc(x_58);
lean::dec(x_46);
x_61 = l_Lean_IR_Borrow_ownVar(x_43, x_2, x_58);
lean::dec(x_2);
return x_61;
}
}
case 6:
{
obj* x_63; obj* x_65; obj* x_68; obj* x_69; obj* x_71; obj* x_73; obj* x_76; obj* x_77; obj* x_80; 
x_63 = lean::cnstr_get(x_1, 0);
lean::inc(x_63);
x_65 = lean::cnstr_get(x_1, 1);
lean::inc(x_65);
lean::dec(x_1);
x_68 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_68, 0, x_63);
x_69 = l_Lean_IR_Borrow_getParamInfo(x_68, x_2, x_3);
lean::dec(x_68);
x_71 = lean::cnstr_get(x_69, 0);
lean::inc(x_71);
x_73 = lean::cnstr_get(x_69, 1);
lean::inc(x_73);
lean::dec(x_69);
x_76 = l_Lean_IR_Borrow_ownVar(x_0, x_2, x_73);
x_77 = lean::cnstr_get(x_76, 1);
lean::inc(x_77);
lean::dec(x_76);
x_80 = l_Lean_IR_Borrow_ownArgsUsingParams(x_65, x_71, x_2, x_77);
lean::dec(x_2);
lean::dec(x_71);
lean::dec(x_65);
return x_80;
}
case 7:
{
obj* x_84; obj* x_87; obj* x_88; obj* x_91; obj* x_92; 
x_84 = lean::cnstr_get(x_1, 1);
lean::inc(x_84);
lean::dec(x_1);
x_87 = l_Lean_IR_Borrow_ownVar(x_0, x_2, x_3);
x_88 = lean::cnstr_get(x_87, 1);
lean::inc(x_88);
lean::dec(x_87);
x_91 = lean::mk_nat_obj(0ul);
x_92 = l_Array_mforAux___main___at_Lean_IR_Borrow_ownArgs___spec__1(x_84, x_91, x_2, x_88);
lean::dec(x_2);
lean::dec(x_84);
return x_92;
}
case 8:
{
obj* x_95; obj* x_97; obj* x_100; obj* x_101; obj* x_104; obj* x_105; obj* x_108; obj* x_109; 
x_95 = lean::cnstr_get(x_1, 0);
lean::inc(x_95);
x_97 = lean::cnstr_get(x_1, 1);
lean::inc(x_97);
lean::dec(x_1);
x_100 = l_Lean_IR_Borrow_ownVar(x_0, x_2, x_3);
x_101 = lean::cnstr_get(x_100, 1);
lean::inc(x_101);
lean::dec(x_100);
x_104 = l_Lean_IR_Borrow_ownVar(x_95, x_2, x_101);
x_105 = lean::cnstr_get(x_104, 1);
lean::inc(x_105);
lean::dec(x_104);
x_108 = lean::mk_nat_obj(0ul);
x_109 = l_Array_mforAux___main___at_Lean_IR_Borrow_ownArgs___spec__1(x_97, x_108, x_2, x_105);
lean::dec(x_2);
lean::dec(x_97);
return x_109;
}
default:
{
obj* x_115; obj* x_116; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_115 = lean::box(0);
x_116 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_116, 0, x_115);
lean::cnstr_set(x_116, 1, x_3);
return x_116;
}
}
}
}
obj* l_Lean_IR_Borrow_collectExpr(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_Borrow_collectExpr___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_IR_Borrow_preserveTailCall(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 6:
{
switch (lean::obj_tag(x_2)) {
case 11:
{
obj* x_5; 
x_5 = lean::cnstr_get(x_2, 0);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_8; obj* x_11; obj* x_12; uint8 x_13; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::dec(x_1);
x_11 = lean::cnstr_get(x_5, 0);
x_12 = lean::cnstr_get(x_3, 1);
x_13 = lean_name_dec_eq(x_12, x_6);
if (x_13 == 0)
{
obj* x_16; obj* x_17; 
lean::dec(x_6);
lean::dec(x_8);
x_16 = lean::box(0);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_4);
return x_17;
}
else
{
uint8 x_18; 
x_18 = lean::nat_dec_eq(x_0, x_11);
if (x_18 == 0)
{
obj* x_21; obj* x_22; 
lean::dec(x_6);
lean::dec(x_8);
x_21 = lean::box(0);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_4);
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_26; obj* x_28; obj* x_31; 
x_23 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_23, 0, x_6);
x_24 = l_Lean_IR_Borrow_getParamInfo(x_23, x_3, x_4);
lean::dec(x_23);
x_26 = lean::cnstr_get(x_24, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_24, 1);
lean::inc(x_28);
lean::dec(x_24);
x_31 = l_Lean_IR_Borrow_ownParamsUsingArgs(x_8, x_26, x_3, x_28);
lean::dec(x_26);
lean::dec(x_8);
return x_31;
}
}
}
else
{
obj* x_35; obj* x_36; 
lean::dec(x_1);
x_35 = lean::box(0);
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_4);
return x_36;
}
}
default:
{
obj* x_38; obj* x_39; 
lean::dec(x_1);
x_38 = lean::box(0);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_4);
return x_39;
}
}
}
default:
{
obj* x_41; obj* x_42; 
lean::dec(x_1);
x_41 = lean::box(0);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_4);
return x_42;
}
}
}
}
obj* l_Lean_IR_Borrow_preserveTailCall___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_IR_Borrow_preserveTailCall(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_3);
return x_5;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_Borrow_updateParamSet___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_1);
x_5 = lean::nat_dec_lt(x_2, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
lean::dec(x_2);
return x_3;
}
else
{
obj* x_8; obj* x_9; obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_8 = lean::array_fget(x_1, x_2);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
lean::dec(x_8);
x_12 = lean::mk_nat_obj(1ul);
x_13 = lean::nat_add(x_2, x_12);
lean::dec(x_2);
x_15 = lean::box(0);
x_16 = l_RBNode_insert___at_Lean_IR_UniqueIds_checkId___spec__2(x_3, x_9, x_15);
x_2 = x_13;
x_3 = x_16;
goto _start;
}
}
}
obj* l_Lean_IR_Borrow_updateParamSet(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_2 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
x_6 = lean::cnstr_get(x_0, 2);
if (lean::is_exclusive(x_0)) {
 x_8 = x_0;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_0);
 x_8 = lean::box(0);
}
x_9 = lean::mk_nat_obj(0ul);
x_10 = l_Array_miterateAux___main___at_Lean_IR_Borrow_updateParamSet___spec__1(x_1, x_1, x_9, x_6);
if (lean::is_scalar(x_8)) {
 x_11 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_11 = x_8;
}
lean::cnstr_set(x_11, 0, x_2);
lean::cnstr_set(x_11, 1, x_4);
lean::cnstr_set(x_11, 2, x_10);
return x_11;
}
}
obj* l_Array_miterateAux___main___at_Lean_IR_Borrow_updateParamSet___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_miterateAux___main___at_Lean_IR_Borrow_updateParamSet___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_Borrow_updateParamSet___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_Borrow_updateParamSet(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_mforAux___main___at_Lean_IR_Borrow_collectFnBody___main___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_0);
x_5 = lean::nat_dec_lt(x_1, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_9; obj* x_10; 
lean::dec(x_1);
lean::dec(x_2);
x_9 = lean::box(0);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_18; obj* x_19; 
x_11 = lean::array_fget(x_0, x_1);
x_12 = lean::mk_nat_obj(1ul);
x_13 = lean::nat_add(x_1, x_12);
lean::dec(x_1);
x_15 = l_Lean_IR_AltCore_body___main(x_11);
lean::dec(x_11);
lean::inc(x_2);
x_18 = l_Lean_IR_Borrow_collectFnBody___main(x_15, x_2, x_3);
x_19 = lean::cnstr_get(x_18, 1);
lean::inc(x_19);
lean::dec(x_18);
x_1 = x_13;
x_3 = x_19;
goto _start;
}
}
}
obj* l_Lean_IR_Borrow_collectFnBody___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_5; obj* x_7; obj* x_9; obj* x_14; obj* x_15; obj* x_21; obj* x_22; obj* x_25; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 1);
lean::inc(x_7);
x_9 = lean::cnstr_get(x_0, 2);
lean::inc(x_9);
lean::dec(x_0);
lean::inc(x_1);
lean::inc(x_9);
x_14 = l_Lean_IR_Borrow_collectFnBody___main(x_9, x_1, x_2);
x_15 = lean::cnstr_get(x_14, 1);
lean::inc(x_15);
lean::dec(x_14);
lean::inc(x_1);
lean::inc(x_7);
lean::inc(x_5);
x_21 = l_Lean_IR_Borrow_collectExpr___main(x_5, x_7, x_1, x_15);
x_22 = lean::cnstr_get(x_21, 1);
lean::inc(x_22);
lean::dec(x_21);
x_25 = l_Lean_IR_Borrow_preserveTailCall(x_5, x_7, x_9, x_1, x_22);
lean::dec(x_1);
lean::dec(x_9);
lean::dec(x_5);
return x_25;
}
case 1:
{
obj* x_29; obj* x_31; obj* x_33; obj* x_35; obj* x_39; obj* x_41; obj* x_42; obj* x_45; obj* x_47; obj* x_48; obj* x_49; 
x_29 = lean::cnstr_get(x_0, 0);
lean::inc(x_29);
x_31 = lean::cnstr_get(x_0, 1);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_0, 2);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_0, 3);
lean::inc(x_35);
lean::dec(x_0);
lean::inc(x_1);
x_39 = l_Lean_IR_Borrow_updateParamSet(x_1, x_31);
lean::dec(x_31);
x_41 = l_Lean_IR_Borrow_collectFnBody___main(x_33, x_39, x_2);
x_42 = lean::cnstr_get(x_41, 1);
lean::inc(x_42);
lean::dec(x_41);
x_45 = lean::cnstr_get(x_1, 1);
lean::inc(x_45);
x_47 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_47, 0, x_45);
lean::cnstr_set(x_47, 1, x_29);
x_48 = l_Lean_IR_Borrow_updateParamMap(x_47, x_1, x_42);
x_49 = lean::cnstr_get(x_48, 1);
lean::inc(x_49);
lean::dec(x_48);
x_0 = x_35;
x_2 = x_49;
goto _start;
}
case 10:
{
obj* x_53; obj* x_56; obj* x_57; 
x_53 = lean::cnstr_get(x_0, 2);
lean::inc(x_53);
lean::dec(x_0);
x_56 = lean::mk_nat_obj(0ul);
x_57 = l_Array_mforAux___main___at_Lean_IR_Borrow_collectFnBody___main___spec__1(x_53, x_56, x_1, x_2);
lean::dec(x_53);
return x_57;
}
case 12:
{
obj* x_59; obj* x_61; obj* x_64; obj* x_66; obj* x_67; obj* x_69; obj* x_71; obj* x_74; obj* x_75; obj* x_78; 
x_59 = lean::cnstr_get(x_0, 0);
lean::inc(x_59);
x_61 = lean::cnstr_get(x_0, 1);
lean::inc(x_61);
lean::dec(x_0);
x_64 = lean::cnstr_get(x_1, 1);
lean::inc(x_64);
x_66 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_66, 0, x_64);
lean::cnstr_set(x_66, 1, x_59);
x_67 = l_Lean_IR_Borrow_getParamInfo(x_66, x_1, x_2);
lean::dec(x_66);
x_69 = lean::cnstr_get(x_67, 0);
lean::inc(x_69);
x_71 = lean::cnstr_get(x_67, 1);
lean::inc(x_71);
lean::dec(x_67);
x_74 = l_Lean_IR_Borrow_ownArgsUsingParams(x_61, x_69, x_1, x_71);
x_75 = lean::cnstr_get(x_74, 1);
lean::inc(x_75);
lean::dec(x_74);
x_78 = l_Lean_IR_Borrow_ownParamsUsingArgs(x_61, x_69, x_1, x_75);
lean::dec(x_1);
lean::dec(x_69);
lean::dec(x_61);
return x_78;
}
default:
{
obj* x_82; 
x_82 = lean::box(0);
x_3 = x_82;
goto lbl_4;
}
}
lbl_4:
{
uint8 x_84; 
lean::dec(x_3);
x_84 = l_Lean_IR_FnBody_isTerminal___main(x_0);
if (x_84 == 0)
{
obj* x_85; 
x_85 = l_Lean_IR_FnBody_body___main(x_0);
lean::dec(x_0);
x_0 = x_85;
goto _start;
}
else
{
obj* x_90; obj* x_91; 
lean::dec(x_1);
lean::dec(x_0);
x_90 = lean::box(0);
x_91 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_2);
return x_91;
}
}
}
}
obj* l_Array_mforAux___main___at_Lean_IR_Borrow_collectFnBody___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_mforAux___main___at_Lean_IR_Borrow_collectFnBody___main___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_Lean_IR_Borrow_collectFnBody(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_Borrow_collectFnBody___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_Borrow_whileModifingOwnedAux___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; uint8 x_8; obj* x_9; uint8 x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_16; obj* x_17; obj* x_19; uint8 x_20; 
x_4 = lean::cnstr_get(x_3, 0);
x_6 = lean::cnstr_get(x_3, 1);
x_8 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*2 + 1);
if (lean::is_exclusive(x_3)) {
 x_9 = x_3;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_3);
 x_9 = lean::box(0);
}
x_10 = 0;
if (lean::is_scalar(x_9)) {
 x_11 = lean::alloc_cnstr(0, 2, 2);
} else {
 x_11 = x_9;
}
lean::cnstr_set(x_11, 0, x_4);
lean::cnstr_set(x_11, 1, x_6);
lean::cnstr_set_scalar(x_11, sizeof(void*)*2, x_10);
x_12 = x_11;
lean::cnstr_set_scalar(x_12, sizeof(void*)*2 + 1, x_8);
x_13 = x_12;
lean::inc(x_2);
lean::inc(x_0);
x_16 = lean::apply_2(x_0, x_2, x_13);
x_17 = lean::cnstr_get(x_16, 1);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_release(x_16, 0);
 lean::cnstr_set(x_16, 1, lean::box(0));
 x_19 = x_16;
} else {
 lean::inc(x_17);
 lean::dec(x_16);
 x_19 = lean::box(0);
}
x_20 = lean::cnstr_get_scalar<uint8>(x_17, sizeof(void*)*2);
if (x_20 == 0)
{
obj* x_23; obj* x_24; 
lean::dec(x_0);
lean::dec(x_2);
x_23 = lean::box(0);
if (lean::is_scalar(x_19)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_19;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_17);
return x_24;
}
else
{
obj* x_26; 
lean::dec(x_19);
x_26 = lean::box(0);
x_1 = x_26;
x_3 = x_17;
goto _start;
}
}
}
obj* l_Lean_IR_Borrow_whileModifingOwnedAux___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_Borrow_whileModifingOwnedAux___main(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_Borrow_whileModifingOwnedAux(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_Borrow_whileModifingOwnedAux___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_IR_Borrow_whileModifingOwnedAux___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_Borrow_whileModifingOwnedAux(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_Borrow_whileModifingOwned(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = l_Lean_IR_Borrow_whileModifingOwnedAux___main(x_0, x_3, x_1, x_2);
return x_4;
}
}
obj* l_Lean_IR_Borrow_whileModifingOwnedAux___main___at_Lean_IR_Borrow_collectDecl___main___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; uint8 x_8; obj* x_9; uint8 x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_16; obj* x_17; obj* x_19; uint8 x_20; 
x_4 = lean::cnstr_get(x_3, 0);
x_6 = lean::cnstr_get(x_3, 1);
x_8 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*2 + 1);
if (lean::is_exclusive(x_3)) {
 x_9 = x_3;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_3);
 x_9 = lean::box(0);
}
x_10 = 0;
if (lean::is_scalar(x_9)) {
 x_11 = lean::alloc_cnstr(0, 2, 2);
} else {
 x_11 = x_9;
}
lean::cnstr_set(x_11, 0, x_4);
lean::cnstr_set(x_11, 1, x_6);
lean::cnstr_set_scalar(x_11, sizeof(void*)*2, x_10);
x_12 = x_11;
lean::cnstr_set_scalar(x_12, sizeof(void*)*2 + 1, x_8);
x_13 = x_12;
lean::inc(x_2);
lean::inc(x_0);
x_16 = l_Lean_IR_Borrow_collectFnBody___main(x_0, x_2, x_13);
x_17 = lean::cnstr_get(x_16, 1);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_release(x_16, 0);
 lean::cnstr_set(x_16, 1, lean::box(0));
 x_19 = x_16;
} else {
 lean::inc(x_17);
 lean::dec(x_16);
 x_19 = lean::box(0);
}
x_20 = lean::cnstr_get_scalar<uint8>(x_17, sizeof(void*)*2);
if (x_20 == 0)
{
obj* x_23; obj* x_24; 
lean::dec(x_0);
lean::dec(x_2);
x_23 = lean::box(0);
if (lean::is_scalar(x_19)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_19;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_17);
return x_24;
}
else
{
obj* x_26; 
lean::dec(x_19);
x_26 = lean::box(0);
x_1 = x_26;
x_3 = x_17;
goto _start;
}
}
}
obj* l_Lean_IR_Borrow_collectDecl___main(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_3; obj* x_5; obj* x_7; obj* x_11; obj* x_13; obj* x_16; obj* x_18; obj* x_20; obj* x_21; uint8 x_23; uint8 x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_32; obj* x_33; obj* x_36; obj* x_37; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 1);
lean::inc(x_5);
x_7 = lean::cnstr_get(x_0, 2);
lean::inc(x_7);
lean::dec(x_0);
lean::inc(x_1);
x_11 = l_Lean_IR_Borrow_updateParamSet(x_1, x_5);
lean::dec(x_5);
x_13 = lean::cnstr_get(x_1, 0);
lean::inc(x_13);
lean::dec(x_1);
x_16 = lean::cnstr_get(x_11, 2);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 lean::cnstr_release(x_11, 1);
 x_18 = x_11;
} else {
 lean::inc(x_16);
 lean::dec(x_11);
 x_18 = lean::box(0);
}
lean::inc(x_3);
if (lean::is_scalar(x_18)) {
 x_20 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_20 = x_18;
}
lean::cnstr_set(x_20, 0, x_13);
lean::cnstr_set(x_20, 1, x_3);
lean::cnstr_set(x_20, 2, x_16);
x_21 = lean::cnstr_get(x_2, 0);
x_23 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*2);
x_24 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*2 + 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 1);
 x_25 = x_2;
} else {
 lean::inc(x_21);
 lean::dec(x_2);
 x_25 = lean::box(0);
}
x_26 = lean::box(0);
if (lean::is_scalar(x_25)) {
 x_27 = lean::alloc_cnstr(0, 2, 2);
} else {
 x_27 = x_25;
}
lean::cnstr_set(x_27, 0, x_21);
lean::cnstr_set(x_27, 1, x_26);
lean::cnstr_set_scalar(x_27, sizeof(void*)*2, x_23);
x_28 = x_27;
lean::cnstr_set_scalar(x_28, sizeof(void*)*2 + 1, x_24);
x_29 = x_28;
x_30 = lean::box(0);
lean::inc(x_20);
x_32 = l_Lean_IR_Borrow_whileModifingOwnedAux___main___at_Lean_IR_Borrow_collectDecl___main___spec__1(x_7, x_30, x_20, x_29);
x_33 = lean::cnstr_get(x_32, 1);
lean::inc(x_33);
lean::dec(x_32);
x_36 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_36, 0, x_3);
x_37 = l_Lean_IR_Borrow_updateParamMap(x_36, x_20, x_33);
lean::dec(x_20);
return x_37;
}
else
{
obj* x_41; obj* x_42; 
lean::dec(x_1);
lean::dec(x_0);
x_41 = lean::box(0);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_2);
return x_42;
}
}
}
obj* l_Lean_IR_Borrow_whileModifingOwnedAux___main___at_Lean_IR_Borrow_collectDecl___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_Borrow_whileModifingOwnedAux___main___at_Lean_IR_Borrow_collectDecl___main___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_Borrow_collectDecl(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_Borrow_collectDecl___main(x_0, x_1, x_2);
return x_3;
}
}
obj* l_Lean_IR_Borrow_whileModifingParamMapAux___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; uint8 x_8; obj* x_9; uint8 x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_16; obj* x_17; obj* x_19; uint8 x_20; 
x_4 = lean::cnstr_get(x_3, 0);
x_6 = lean::cnstr_get(x_3, 1);
x_8 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*2);
if (lean::is_exclusive(x_3)) {
 x_9 = x_3;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_3);
 x_9 = lean::box(0);
}
x_10 = 0;
if (lean::is_scalar(x_9)) {
 x_11 = lean::alloc_cnstr(0, 2, 2);
} else {
 x_11 = x_9;
}
lean::cnstr_set(x_11, 0, x_4);
lean::cnstr_set(x_11, 1, x_6);
lean::cnstr_set_scalar(x_11, sizeof(void*)*2, x_8);
x_12 = x_11;
lean::cnstr_set_scalar(x_12, sizeof(void*)*2 + 1, x_10);
x_13 = x_12;
lean::inc(x_2);
lean::inc(x_0);
x_16 = lean::apply_2(x_0, x_2, x_13);
x_17 = lean::cnstr_get(x_16, 1);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_release(x_16, 0);
 lean::cnstr_set(x_16, 1, lean::box(0));
 x_19 = x_16;
} else {
 lean::inc(x_17);
 lean::dec(x_16);
 x_19 = lean::box(0);
}
x_20 = lean::cnstr_get_scalar<uint8>(x_17, sizeof(void*)*2 + 1);
if (x_20 == 0)
{
obj* x_23; obj* x_24; 
lean::dec(x_0);
lean::dec(x_2);
x_23 = lean::box(0);
if (lean::is_scalar(x_19)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_19;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_17);
return x_24;
}
else
{
obj* x_26; 
lean::dec(x_19);
x_26 = lean::box(0);
x_1 = x_26;
x_3 = x_17;
goto _start;
}
}
}
obj* l_Lean_IR_Borrow_whileModifingParamMapAux___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_Borrow_whileModifingParamMapAux___main(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_Borrow_whileModifingParamMapAux(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_Borrow_whileModifingParamMapAux___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l_Lean_IR_Borrow_whileModifingParamMapAux___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_Borrow_whileModifingParamMapAux(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_Borrow_whileModifingParamMap(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::box(0);
x_4 = l_Lean_IR_Borrow_whileModifingParamMapAux___main(x_0, x_3, x_1, x_2);
return x_4;
}
}
obj* l_Array_mforAux___main___at_Lean_IR_Borrow_collectDecls___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::array_get_size(x_0);
x_5 = lean::nat_dec_lt(x_1, x_4);
lean::dec(x_4);
if (x_5 == 0)
{
obj* x_9; obj* x_10; 
lean::dec(x_1);
lean::dec(x_2);
x_9 = lean::box(0);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_16; obj* x_17; 
x_11 = lean::array_fget(x_0, x_1);
x_12 = lean::mk_nat_obj(1ul);
x_13 = lean::nat_add(x_1, x_12);
lean::dec(x_1);
lean::inc(x_2);
x_16 = l_Lean_IR_Borrow_collectDecl___main(x_11, x_2, x_3);
x_17 = lean::cnstr_get(x_16, 1);
lean::inc(x_17);
lean::dec(x_16);
x_1 = x_13;
x_3 = x_17;
goto _start;
}
}
}
obj* l_Lean_IR_Borrow_whileModifingParamMapAux___main___at_Lean_IR_Borrow_collectDecls___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; uint8 x_8; obj* x_9; uint8 x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_19; uint8 x_20; 
x_4 = lean::cnstr_get(x_3, 0);
x_6 = lean::cnstr_get(x_3, 1);
x_8 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*2);
if (lean::is_exclusive(x_3)) {
 x_9 = x_3;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_3);
 x_9 = lean::box(0);
}
x_10 = 0;
if (lean::is_scalar(x_9)) {
 x_11 = lean::alloc_cnstr(0, 2, 2);
} else {
 x_11 = x_9;
}
lean::cnstr_set(x_11, 0, x_4);
lean::cnstr_set(x_11, 1, x_6);
lean::cnstr_set_scalar(x_11, sizeof(void*)*2, x_8);
x_12 = x_11;
lean::cnstr_set_scalar(x_12, sizeof(void*)*2 + 1, x_10);
x_13 = x_12;
x_14 = lean::mk_nat_obj(0ul);
lean::inc(x_2);
x_16 = l_Array_mforAux___main___at_Lean_IR_Borrow_collectDecls___spec__1(x_0, x_14, x_2, x_13);
x_17 = lean::cnstr_get(x_16, 1);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_release(x_16, 0);
 lean::cnstr_set(x_16, 1, lean::box(0));
 x_19 = x_16;
} else {
 lean::inc(x_17);
 lean::dec(x_16);
 x_19 = lean::box(0);
}
x_20 = lean::cnstr_get_scalar<uint8>(x_17, sizeof(void*)*2 + 1);
if (x_20 == 0)
{
obj* x_22; obj* x_23; 
lean::dec(x_2);
x_22 = lean::box(0);
if (lean::is_scalar(x_19)) {
 x_23 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_23 = x_19;
}
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_17);
return x_23;
}
else
{
obj* x_25; 
lean::dec(x_19);
x_25 = lean::box(0);
x_1 = x_25;
x_3 = x_17;
goto _start;
}
}
}
obj* l_Lean_IR_Borrow_collectDecls(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_10; 
x_3 = lean::box(0);
x_4 = l_Lean_IR_Borrow_whileModifingParamMapAux___main___at_Lean_IR_Borrow_collectDecls___spec__2(x_0, x_3, x_1, x_2);
x_5 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_7 = x_4;
} else {
 lean::inc(x_5);
 lean::dec(x_4);
 x_7 = lean::box(0);
}
x_8 = lean::cnstr_get(x_5, 0);
lean::inc(x_8);
if (lean::is_scalar(x_7)) {
 x_10 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_10 = x_7;
}
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_5);
return x_10;
}
}
obj* l_Array_mforAux___main___at_Lean_IR_Borrow_collectDecls___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Array_mforAux___main___at_Lean_IR_Borrow_collectDecls___spec__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l_Lean_IR_Borrow_whileModifingParamMapAux___main___at_Lean_IR_Borrow_collectDecls___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_IR_Borrow_whileModifingParamMapAux___main___at_Lean_IR_Borrow_collectDecls___spec__2(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_IR_Borrow_collectDecls___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_Borrow_collectDecls(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Lean_IR_Borrow_infer(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_5; obj* x_6; uint8 x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_2 = lean::box(0);
x_3 = lean::box(0);
lean::inc(x_0);
x_5 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_5, 0, x_0);
lean::cnstr_set(x_5, 1, x_3);
lean::cnstr_set(x_5, 2, x_2);
x_6 = l_Lean_IR_Borrow_mkInitParamMap(x_0, x_1);
lean::dec(x_0);
x_8 = 0;
x_9 = lean::alloc_cnstr(0, 2, 2);
lean::cnstr_set(x_9, 0, x_6);
lean::cnstr_set(x_9, 1, x_2);
lean::cnstr_set_scalar(x_9, sizeof(void*)*2, x_8);
x_10 = x_9;
lean::cnstr_set_scalar(x_10, sizeof(void*)*2 + 1, x_8);
x_11 = x_10;
x_12 = l_Lean_IR_Borrow_collectDecls(x_1, x_5, x_11);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
lean::dec(x_12);
return x_13;
}
}
obj* l_Lean_IR_Borrow_infer___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_IR_Borrow_infer(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Array_hmmapAux___main___at_Lean_IR_inferBorrow___spec__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; 
x_2 = lean::array_get_size(x_1);
x_3 = lean::nat_dec_lt(x_0, x_2);
lean::dec(x_2);
if (x_3 == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_6 = lean::array_fget(x_1, x_0);
x_7 = l_Array_hmmapAux___main___at_Lean_IR_Borrow_ApplyParamMap_visitDecls___spec__1___closed__1;
x_8 = lean::array_fset(x_1, x_0, x_7);
x_9 = l_Lean_IR_Decl_normalizeIds(x_6);
x_10 = lean::mk_nat_obj(1ul);
x_11 = lean::nat_add(x_0, x_10);
x_12 = lean::array_fset(x_8, x_0, x_9);
lean::dec(x_0);
x_0 = x_11;
x_1 = x_12;
goto _start;
}
}
}
obj* l_Lean_IR_inferBorrow(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_getEnv___rarg(x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_14; 
x_4 = lean::cnstr_get(x_3, 0);
x_6 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_8 = x_3;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_3);
 x_8 = lean::box(0);
}
x_9 = lean::mk_nat_obj(0ul);
x_10 = l_Array_hmmapAux___main___at_Lean_IR_inferBorrow___spec__1(x_9, x_0);
x_11 = l_Lean_IR_Borrow_infer(x_4, x_10);
x_12 = l_Array_hmmapAux___main___at_Lean_IR_Borrow_ApplyParamMap_visitDecls___spec__1(x_11, x_9, x_10);
lean::dec(x_11);
if (lean::is_scalar(x_8)) {
 x_14 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_14 = x_8;
}
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_6);
return x_14;
}
else
{
obj* x_16; obj* x_18; obj* x_20; obj* x_21; 
lean::dec(x_0);
x_16 = lean::cnstr_get(x_3, 0);
x_18 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_20 = x_3;
} else {
 lean::inc(x_16);
 lean::inc(x_18);
 lean::dec(x_3);
 x_20 = lean::box(0);
}
if (lean::is_scalar(x_20)) {
 x_21 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_21 = x_20;
}
lean::cnstr_set(x_21, 0, x_16);
lean::cnstr_set(x_21, 1, x_18);
return x_21;
}
}
}
obj* l_Lean_IR_inferBorrow___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_IR_inferBorrow(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* initialize_init_lean_compiler_export(obj*);
obj* initialize_init_lean_compiler_ir_compilerm(obj*);
obj* initialize_init_lean_compiler_ir_normids(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_compiler_ir_borrow(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_export(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_compilerm(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_compiler_ir_normids(w);
if (io_result_is_error(w)) return w;
 l_Lean_IR_Borrow_Key_HasBeq = _init_l_Lean_IR_Borrow_Key_HasBeq();
lean::mark_persistent(l_Lean_IR_Borrow_Key_HasBeq);
 l_Lean_IR_Borrow_Key_Hashable = _init_l_Lean_IR_Borrow_Key_Hashable();
lean::mark_persistent(l_Lean_IR_Borrow_Key_Hashable);
 l_AssocList_foldl___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__1 = _init_l_AssocList_foldl___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__1();
lean::mark_persistent(l_AssocList_foldl___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__1);
 l_AssocList_foldl___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__2 = _init_l_AssocList_foldl___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__2();
lean::mark_persistent(l_AssocList_foldl___main___at_Lean_IR_Borrow_ParamMap_fmt___spec__1___closed__2);
 l_Lean_IR_Borrow_ParamMap_fmt___closed__1 = _init_l_Lean_IR_Borrow_ParamMap_fmt___closed__1();
lean::mark_persistent(l_Lean_IR_Borrow_ParamMap_fmt___closed__1);
 l_Lean_IR_Borrow_ParamMap_fmt___closed__2 = _init_l_Lean_IR_Borrow_ParamMap_fmt___closed__2();
lean::mark_persistent(l_Lean_IR_Borrow_ParamMap_fmt___closed__2);
 l_Lean_IR_Borrow_Lean_HasFormat = _init_l_Lean_IR_Borrow_Lean_HasFormat();
lean::mark_persistent(l_Lean_IR_Borrow_Lean_HasFormat);
 l_Lean_IR_Borrow_mkInitParamMap___closed__1 = _init_l_Lean_IR_Borrow_mkInitParamMap___closed__1();
lean::mark_persistent(l_Lean_IR_Borrow_mkInitParamMap___closed__1);
 l_Array_hmmapAux___main___at_Lean_IR_Borrow_ApplyParamMap_visitDecls___spec__1___closed__1 = _init_l_Array_hmmapAux___main___at_Lean_IR_Borrow_ApplyParamMap_visitDecls___spec__1___closed__1();
lean::mark_persistent(l_Array_hmmapAux___main___at_Lean_IR_Borrow_ApplyParamMap_visitDecls___spec__1___closed__1);
return w;
}
