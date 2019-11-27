// Lean compiler output
// Module: Init.Lean.Compiler.IR.ExpandResetReuse
// Imports: Init.Control.State Init.Control.Reader Init.Data.Nat Init.Lean.Compiler.IR.CompilerM Init.Lean.Compiler.IR.NormIds Init.Lean.Compiler.IR.FreeVars
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
lean_object* l_Lean_IR_ExpandResetReuse_mkProjMap___closed__1;
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExpandResetReuse_removeSelfSet___main___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern uint8_t l_String_anyAux___main___at_String_all___spec__1___closed__1;
lean_object* l_Lean_IR_ExpandResetReuse_main(lean_object*);
lean_object* l_Nat_foldAux___main___at_Lean_IR_ExpandResetReuse_setFields___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_IR_ExpandResetReuse_removeSelfSet___main(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExpandResetReuse_reuseToSet(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExpandResetReuse_releaseUnreadFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_moveEntries___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_IR_ExpandResetReuse_releaseUnreadFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_contains___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncFor___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExpandResetReuse_isSelfSSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
uint8_t l_AssocList_contains___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at_Lean_IR_ExpandResetReuse_releaseUnreadFields___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverseAux___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExpandResetReuse_removeSelfSet___boxed(lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_IR_ExpandResetReuse_eraseProjIncForAux___main___spec__1___boxed(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lean_IR_Inhabited;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_ExpandResetReuse_reuseToSet___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_ExpandResetReuse_reuseToSet___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExpandResetReuse_reuseToCtor___main(lean_object*, lean_object*);
lean_object* l_mkHashMap___at_Lean_IR_ExpandResetReuse_mkProjMap___spec__1(lean_object*);
lean_object* l_Lean_IR_ExpandResetReuse_removeSelfSet(lean_object*, lean_object*);
lean_object* l_AssocList_replace___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__6(lean_object*, lean_object*, lean_object*);
lean_object* l_AssocList_foldlM___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__5(lean_object*, lean_object*);
lean_object* l_HashMapImp_find___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExpandResetReuse_consumed___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___main(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExpandResetReuse_mkSlowPath___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_ExpandResetReuse_removeSelfSet___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExpandResetReuse_setFields(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_Arg_Inhabited;
uint8_t l_Lean_IR_ExpandResetReuse_isSelfSSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_AltCore_body(lean_object*);
lean_object* l_Lean_IR_ExpandResetReuse_mkFastPath(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExpandResetReuse_mkProjMap(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_ExpandResetReuse_removeSelfSet___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_ExpandResetReuse_reuseToCtor___main___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExpandResetReuse_isSelfSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_expand___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__3(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_FnBody_isTerminal(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_ExpandResetReuse_searchAndExpand___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_back___at_Lean_IR_ExpandResetReuse_eraseProjIncForAux___main___spec__1(lean_object*);
lean_object* l_Lean_IR_push(lean_object*, lean_object*);
lean_object* l_Lean_IR_mkIf(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExpandResetReuse_mkFresh(lean_object*);
lean_object* l_Nat_foldMAux___main___at_Lean_IR_ExpandResetReuse_releaseUnreadFields___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_modn(size_t, lean_object*);
lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncFor(lean_object*, lean_object*, lean_object*);
lean_object* l_mkHashMapImp___rarg(lean_object*);
lean_object* l_Lean_IR_ExpandResetReuse_reuseToSet___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExpandResetReuse_searchAndExpand___main___closed__1;
size_t lean_usize_of_nat(lean_object*);
uint8_t l_Lean_IR_ExpandResetReuse_consumed(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExpandResetReuse_consumed___main___boxed(lean_object*, lean_object*);
lean_object* l_Nat_foldAux___main___at_Lean_IR_ExpandResetReuse_setFields___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExpandResetReuse_mkFresh___boxed(lean_object*);
lean_object* l_Lean_IR_ExpandResetReuse_isSelfUSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_expandResetReuse(lean_object*);
lean_object* l_AssocList_find___main___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_setBody(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExpandResetReuse_reuseToCtor(lean_object*, lean_object*);
lean_object* l_AssocList_find___main___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__2___boxed(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_anyRangeMAux___main___at_Lean_IR_ExpandResetReuse_consumed___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncForAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExpandResetReuse_searchAndExpand___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_ExpandResetReuse_mkSlowPath___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_reshape(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExpandResetReuse_mkFastPath___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExpandResetReuse_mkSlowPath(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_ExpandResetReuse_isSelfSet(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExpandResetReuse_searchAndExpand(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExpandResetReuse_reuseToSet___main(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExpandResetReuse_reuseToCtor___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExpandResetReuse_mkFresh___rarg(lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExpandResetReuse_setFields___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_ExpandResetReuse_expand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_normalizeIds(lean_object*);
uint8_t l_Lean_IR_ExpandResetReuse_consumed___main(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExpandResetReuse_reuseToCtor___main___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExpandResetReuse_reuseToSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Bool_DecidableEq(uint8_t, uint8_t);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_body(lean_object*);
lean_object* l_HashMapImp_insert___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_IR_ExpandResetReuse_reuseToCtor___main___spec__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_ExpandResetReuse_isSelfUSet(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_HashMapImp_find___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_IR_ExpandResetReuse_expand___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_anyRangeMAux___main___at_Lean_IR_ExpandResetReuse_consumed___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_MaxIndex_collectDecl(lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___main___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_IR_ExpandResetReuse_mkSlowPath___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_AssocList_contains___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_6 = lean_nat_dec_eq(x_4, x_1);
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
lean_object* l_AssocList_foldlM___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__5(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_usize_of_nat(x_4);
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
x_16 = lean_usize_of_nat(x_12);
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
lean_object* l_HashMapImp_moveEntries___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_AssocList_foldlM___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__5(x_3, x_6);
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
lean_object* l_HashMapImp_expand___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__3(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_HashMapImp_moveEntries___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__4(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
lean_object* l_AssocList_replace___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = lean_nat_dec_eq(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_AssocList_replace___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__6(x_1, x_2, x_7);
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
x_13 = lean_nat_dec_eq(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_AssocList_replace___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__6(x_1, x_2, x_12);
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
lean_object* l_HashMapImp_insert___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_usize_of_nat(x_2);
x_9 = lean_usize_modn(x_8, x_7);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_AssocList_contains___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__2(x_2, x_10);
x_12 = 1;
x_13 = l_Bool_DecidableEq(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_5, x_14);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_3);
lean_ctor_set(x_16, 2, x_10);
x_17 = lean_array_uset(x_6, x_9, x_16);
x_18 = lean_nat_dec_le(x_15, x_7);
lean_dec(x_7);
if (x_18 == 0)
{
lean_object* x_19; 
lean_free_object(x_1);
x_19 = l_HashMapImp_expand___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__3(x_15, x_17);
return x_19;
}
else
{
lean_ctor_set(x_1, 1, x_17);
lean_ctor_set(x_1, 0, x_15);
return x_1;
}
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
x_20 = l_AssocList_replace___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__6(x_2, x_3, x_10);
x_21 = lean_array_uset(x_6, x_9, x_20);
lean_ctor_set(x_1, 1, x_21);
return x_1;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; 
x_22 = lean_ctor_get(x_1, 0);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_1);
x_24 = lean_array_get_size(x_23);
x_25 = lean_usize_of_nat(x_2);
x_26 = lean_usize_modn(x_25, x_24);
x_27 = lean_array_uget(x_23, x_26);
x_28 = l_AssocList_contains___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__2(x_2, x_27);
x_29 = 1;
x_30 = l_Bool_DecidableEq(x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_22, x_31);
lean_dec(x_22);
x_33 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_3);
lean_ctor_set(x_33, 2, x_27);
x_34 = lean_array_uset(x_23, x_26, x_33);
x_35 = lean_nat_dec_le(x_32, x_24);
lean_dec(x_24);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_HashMapImp_expand___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__3(x_32, x_34);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_24);
x_38 = l_AssocList_replace___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__6(x_2, x_3, x_27);
x_39 = lean_array_uset(x_23, x_26, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_22);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
lean_object* l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 3:
{
lean_object* x_4; 
x_4 = l_HashMapImp_insert___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(x_3, x_1, x_2);
return x_4;
}
case 4:
{
lean_object* x_5; 
x_5 = l_HashMapImp_insert___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(x_3, x_1, x_2);
return x_5;
}
case 5:
{
lean_object* x_6; 
x_6 = l_HashMapImp_insert___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(x_3, x_1, x_2);
return x_6;
}
default: 
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
}
lean_object* l_AssocList_contains___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_AssocList_contains___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = l_Lean_IR_AltCore_body(x_7);
lean_dec(x_7);
x_9 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___main(x_8, x_4);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
x_4 = x_9;
goto _start;
}
}
}
lean_object* l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___main(x_12, x_2);
switch (lean_obj_tag(x_11)) {
case 3:
{
lean_object* x_14; 
x_14 = l_HashMapImp_insert___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(x_13, x_10, x_11);
return x_14;
}
case 4:
{
lean_object* x_15; 
x_15 = l_HashMapImp_insert___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(x_13, x_10, x_11);
return x_15;
}
case 5:
{
lean_object* x_16; 
x_16 = l_HashMapImp_insert___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(x_13, x_10, x_11);
return x_16;
}
default: 
{
lean_dec(x_11);
lean_dec(x_10);
return x_13;
}
}
}
case 1:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_1, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 3);
lean_inc(x_18);
lean_dec(x_1);
x_19 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___main(x_18, x_2);
x_1 = x_17;
x_2 = x_19;
goto _start;
}
case 10:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_1, 3);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Array_iterateMAux___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___main___spec__1(x_21, x_21, x_22, x_2);
lean_dec(x_21);
return x_23;
}
default: 
{
lean_object* x_24; 
x_24 = lean_box(0);
x_3 = x_24;
goto block_9;
}
}
block_9:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; 
lean_dec(x_3);
x_4 = l_Lean_IR_FnBody_isTerminal(x_1);
x_5 = 1;
x_6 = l_Bool_DecidableEq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = l_Lean_IR_FnBody_body(x_1);
lean_dec(x_1);
x_1 = x_7;
goto _start;
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___main___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___main(x_1, x_2);
return x_3;
}
}
lean_object* l_mkHashMap___at_Lean_IR_ExpandResetReuse_mkProjMap___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_IR_ExpandResetReuse_mkProjMap___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_mkHashMapImp___rarg(x_1);
return x_2;
}
}
lean_object* l_Lean_IR_ExpandResetReuse_mkProjMap(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Lean_IR_ExpandResetReuse_mkProjMap___closed__1;
x_4 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___main(x_2, x_3);
return x_4;
}
else
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = l_Lean_IR_ExpandResetReuse_mkProjMap___closed__1;
return x_5;
}
}
}
uint8_t l_Array_anyRangeMAux___main___at_Lean_IR_ExpandResetReuse_consumed___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
uint8_t x_7; 
lean_dec(x_5);
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_array_fget(x_3, x_5);
x_9 = l_Lean_IR_AltCore_body(x_8);
lean_dec(x_8);
x_10 = l_Lean_IR_ExpandResetReuse_consumed___main(x_1, x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_5);
x_11 = 1;
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_5 = x_13;
goto _start;
}
}
}
}
uint8_t l_Lean_IR_ExpandResetReuse_consumed___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 2)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_2, 3);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_nat_dec_eq(x_1, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
x_2 = x_10;
goto _start;
}
else
{
uint8_t x_14; 
lean_dec(x_10);
x_14 = 1;
return x_14;
}
}
else
{
lean_object* x_15; 
lean_dec(x_9);
x_15 = lean_ctor_get(x_2, 3);
lean_inc(x_15);
lean_dec(x_2);
x_2 = x_15;
goto _start;
}
}
case 7:
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 2);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_nat_dec_eq(x_1, x_17);
lean_dec(x_17);
if (x_19 == 0)
{
x_2 = x_18;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_18);
x_21 = 1;
return x_21;
}
}
case 10:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_2, 3);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_array_get_size(x_22);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Array_anyRangeMAux___main___at_Lean_IR_ExpandResetReuse_consumed___main___spec__1(x_1, x_22, x_22, x_23, x_24);
lean_dec(x_23);
lean_dec(x_22);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = 1;
return x_26;
}
else
{
uint8_t x_27; 
x_27 = 0;
return x_27;
}
}
default: 
{
lean_object* x_28; 
x_28 = lean_box(0);
x_3 = x_28;
goto block_8;
}
}
block_8:
{
uint8_t x_4; 
lean_dec(x_3);
x_4 = l_Lean_IR_FnBody_isTerminal(x_2);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lean_IR_FnBody_body(x_2);
lean_dec(x_2);
x_2 = x_5;
goto _start;
}
else
{
uint8_t x_7; 
lean_dec(x_2);
x_7 = 0;
return x_7;
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at_Lean_IR_ExpandResetReuse_consumed___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_anyRangeMAux___main___at_Lean_IR_ExpandResetReuse_consumed___main___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Lean_IR_ExpandResetReuse_consumed___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_ExpandResetReuse_consumed___main(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
uint8_t l_Lean_IR_ExpandResetReuse_consumed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_IR_ExpandResetReuse_consumed___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_IR_ExpandResetReuse_consumed___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_ExpandResetReuse_consumed(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* l_Array_back___at_Lean_IR_ExpandResetReuse_eraseProjIncForAux___main___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_sub(x_2, x_3);
lean_dec(x_2);
x_5 = l_Lean_IR_Inhabited;
x_6 = lean_array_get(x_5, x_1, x_4);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_11; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_array_get_size(x_2);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_nat_dec_lt(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = l_Array_back___at_Lean_IR_ExpandResetReuse_eraseProjIncForAux___main___spec__1(x_2);
switch (lean_obj_tag(x_19)) {
case 0:
{
lean_object* x_20; 
lean_dec(x_16);
x_20 = lean_ctor_get(x_19, 2);
lean_inc(x_20);
switch (lean_obj_tag(x_20)) {
case 4:
{
lean_dec(x_20);
x_11 = x_19;
goto block_15;
}
case 5:
{
lean_dec(x_20);
x_11 = x_19;
goto block_15;
}
default: 
{
lean_object* x_21; 
lean_dec(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_5 = x_21;
goto block_10;
}
}
}
case 6:
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
x_25 = lean_ctor_get(x_19, 2);
lean_dec(x_25);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_nat_dec_eq(x_24, x_26);
x_28 = 1;
x_29 = l_Bool_DecidableEq(x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_nat_sub(x_16, x_17);
lean_dec(x_16);
x_31 = l_Lean_IR_Inhabited;
x_32 = lean_array_get(x_31, x_2, x_30);
lean_dec(x_30);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_32, 2);
lean_inc(x_33);
if (lean_obj_tag(x_33) == 3)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_nat_dec_eq(x_34, x_23);
lean_dec(x_34);
if (x_37 == 0)
{
uint8_t x_38; 
lean_dec(x_36);
x_38 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_35);
lean_dec(x_32);
lean_free_object(x_19);
lean_dec(x_24);
lean_dec(x_23);
x_39 = lean_box(0);
x_5 = x_39;
goto block_10;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_47; 
x_40 = lean_array_pop(x_2);
x_41 = lean_array_pop(x_40);
lean_inc(x_23);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_23);
x_43 = lean_array_set(x_3, x_35, x_42);
lean_dec(x_35);
x_44 = lean_array_push(x_4, x_32);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_dec_eq(x_24, x_45);
x_47 = l_Bool_DecidableEq(x_46, x_28);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_nat_sub(x_24, x_45);
lean_dec(x_24);
x_49 = lean_box(13);
lean_ctor_set(x_19, 2, x_49);
lean_ctor_set(x_19, 1, x_48);
x_50 = lean_array_push(x_44, x_19);
x_2 = x_41;
x_3 = x_43;
x_4 = x_50;
goto _start;
}
else
{
lean_free_object(x_19);
lean_dec(x_24);
lean_dec(x_23);
x_2 = x_41;
x_3 = x_43;
x_4 = x_44;
goto _start;
}
}
}
else
{
uint8_t x_53; uint8_t x_54; 
x_53 = lean_nat_dec_eq(x_1, x_36);
lean_dec(x_36);
x_54 = l_Bool_DecidableEq(x_53, x_28);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_35);
lean_dec(x_32);
lean_free_object(x_19);
lean_dec(x_24);
lean_dec(x_23);
x_55 = lean_box(0);
x_5 = x_55;
goto block_10;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_63; 
x_56 = lean_array_pop(x_2);
x_57 = lean_array_pop(x_56);
lean_inc(x_23);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_23);
x_59 = lean_array_set(x_3, x_35, x_58);
lean_dec(x_35);
x_60 = lean_array_push(x_4, x_32);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_dec_eq(x_24, x_61);
x_63 = l_Bool_DecidableEq(x_62, x_28);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_nat_sub(x_24, x_61);
lean_dec(x_24);
x_65 = lean_box(13);
lean_ctor_set(x_19, 2, x_65);
lean_ctor_set(x_19, 1, x_64);
x_66 = lean_array_push(x_60, x_19);
x_2 = x_57;
x_3 = x_59;
x_4 = x_66;
goto _start;
}
else
{
lean_free_object(x_19);
lean_dec(x_24);
lean_dec(x_23);
x_2 = x_57;
x_3 = x_59;
x_4 = x_60;
goto _start;
}
}
}
}
else
{
lean_object* x_69; 
lean_dec(x_33);
lean_dec(x_32);
lean_free_object(x_19);
lean_dec(x_24);
lean_dec(x_23);
x_69 = lean_box(0);
x_5 = x_69;
goto block_10;
}
}
else
{
lean_object* x_70; 
lean_dec(x_32);
lean_free_object(x_19);
lean_dec(x_24);
lean_dec(x_23);
x_70 = lean_box(0);
x_5 = x_70;
goto block_10;
}
}
else
{
lean_object* x_71; 
lean_free_object(x_19);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_16);
x_71 = lean_box(0);
x_5 = x_71;
goto block_10;
}
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; uint8_t x_75; lean_object* x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; 
x_72 = lean_ctor_get(x_19, 0);
x_73 = lean_ctor_get(x_19, 1);
x_74 = lean_ctor_get_uint8(x_19, sizeof(void*)*3);
x_75 = lean_ctor_get_uint8(x_19, sizeof(void*)*3 + 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_19);
x_76 = lean_unsigned_to_nat(0u);
x_77 = lean_nat_dec_eq(x_73, x_76);
x_78 = 1;
x_79 = l_Bool_DecidableEq(x_77, x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_nat_sub(x_16, x_17);
lean_dec(x_16);
x_81 = l_Lean_IR_Inhabited;
x_82 = lean_array_get(x_81, x_2, x_80);
lean_dec(x_80);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_82, 2);
lean_inc(x_83);
if (lean_obj_tag(x_83) == 3)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_84 = lean_ctor_get(x_82, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
lean_dec(x_83);
x_87 = lean_nat_dec_eq(x_84, x_72);
lean_dec(x_84);
if (x_87 == 0)
{
uint8_t x_88; 
lean_dec(x_86);
x_88 = l_String_anyAux___main___at_String_all___spec__1___closed__1;
if (x_88 == 0)
{
lean_object* x_89; 
lean_dec(x_85);
lean_dec(x_82);
lean_dec(x_73);
lean_dec(x_72);
x_89 = lean_box(0);
x_5 = x_89;
goto block_10;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; uint8_t x_97; 
x_90 = lean_array_pop(x_2);
x_91 = lean_array_pop(x_90);
lean_inc(x_72);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_72);
x_93 = lean_array_set(x_3, x_85, x_92);
lean_dec(x_85);
x_94 = lean_array_push(x_4, x_82);
x_95 = lean_unsigned_to_nat(1u);
x_96 = lean_nat_dec_eq(x_73, x_95);
x_97 = l_Bool_DecidableEq(x_96, x_78);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_nat_sub(x_73, x_95);
lean_dec(x_73);
x_99 = lean_box(13);
x_100 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_100, 0, x_72);
lean_ctor_set(x_100, 1, x_98);
lean_ctor_set(x_100, 2, x_99);
lean_ctor_set_uint8(x_100, sizeof(void*)*3, x_74);
lean_ctor_set_uint8(x_100, sizeof(void*)*3 + 1, x_75);
x_101 = lean_array_push(x_94, x_100);
x_2 = x_91;
x_3 = x_93;
x_4 = x_101;
goto _start;
}
else
{
lean_dec(x_73);
lean_dec(x_72);
x_2 = x_91;
x_3 = x_93;
x_4 = x_94;
goto _start;
}
}
}
else
{
uint8_t x_104; uint8_t x_105; 
x_104 = lean_nat_dec_eq(x_1, x_86);
lean_dec(x_86);
x_105 = l_Bool_DecidableEq(x_104, x_78);
if (x_105 == 0)
{
lean_object* x_106; 
lean_dec(x_85);
lean_dec(x_82);
lean_dec(x_73);
lean_dec(x_72);
x_106 = lean_box(0);
x_5 = x_106;
goto block_10;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; uint8_t x_114; 
x_107 = lean_array_pop(x_2);
x_108 = lean_array_pop(x_107);
lean_inc(x_72);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_72);
x_110 = lean_array_set(x_3, x_85, x_109);
lean_dec(x_85);
x_111 = lean_array_push(x_4, x_82);
x_112 = lean_unsigned_to_nat(1u);
x_113 = lean_nat_dec_eq(x_73, x_112);
x_114 = l_Bool_DecidableEq(x_113, x_78);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_115 = lean_nat_sub(x_73, x_112);
lean_dec(x_73);
x_116 = lean_box(13);
x_117 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_117, 0, x_72);
lean_ctor_set(x_117, 1, x_115);
lean_ctor_set(x_117, 2, x_116);
lean_ctor_set_uint8(x_117, sizeof(void*)*3, x_74);
lean_ctor_set_uint8(x_117, sizeof(void*)*3 + 1, x_75);
x_118 = lean_array_push(x_111, x_117);
x_2 = x_108;
x_3 = x_110;
x_4 = x_118;
goto _start;
}
else
{
lean_dec(x_73);
lean_dec(x_72);
x_2 = x_108;
x_3 = x_110;
x_4 = x_111;
goto _start;
}
}
}
}
else
{
lean_object* x_121; 
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_73);
lean_dec(x_72);
x_121 = lean_box(0);
x_5 = x_121;
goto block_10;
}
}
else
{
lean_object* x_122; 
lean_dec(x_82);
lean_dec(x_73);
lean_dec(x_72);
x_122 = lean_box(0);
x_5 = x_122;
goto block_10;
}
}
else
{
lean_object* x_123; 
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_16);
x_123 = lean_box(0);
x_5 = x_123;
goto block_10;
}
}
}
default: 
{
lean_object* x_124; 
lean_dec(x_19);
lean_dec(x_16);
x_124 = lean_box(0);
x_5 = x_124;
goto block_10;
}
}
}
else
{
lean_object* x_125; 
lean_dec(x_16);
x_125 = lean_box(0);
x_5 = x_125;
goto block_10;
}
block_10:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_reverseAux___main___rarg(x_4, x_6);
x_8 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_7, x_7, x_6, x_2);
lean_dec(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
block_15:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_pop(x_2);
x_13 = lean_array_push(x_4, x_11);
x_2 = x_12;
x_4 = x_13;
goto _start;
}
}
}
lean_object* l_Array_back___at_Lean_IR_ExpandResetReuse_eraseProjIncForAux___main___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Array_back___at_Lean_IR_ExpandResetReuse_eraseProjIncForAux___main___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___main(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncForAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ExpandResetReuse_eraseProjIncForAux(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncFor(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_box(0);
x_5 = lean_mk_array(x_1, x_4);
x_6 = l_Array_empty___closed__1;
x_7 = l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___main(x_2, x_3, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncFor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ExpandResetReuse_eraseProjIncFor(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_ExpandResetReuse_reuseToCtor___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
x_16 = l_Lean_IR_ExpandResetReuse_reuseToCtor___main(x_1, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = x_17;
x_19 = lean_array_fset(x_11, x_2, x_18);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_8, 0);
lean_inc(x_21);
x_22 = l_Lean_IR_ExpandResetReuse_reuseToCtor___main(x_1, x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = x_23;
x_25 = lean_array_fset(x_11, x_2, x_24);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_25;
goto _start;
}
}
}
}
lean_object* l_Lean_IR_ExpandResetReuse_reuseToCtor___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 2)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; 
x_15 = lean_ctor_get(x_2, 3);
x_16 = lean_ctor_get(x_2, 2);
lean_dec(x_16);
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_13, 2);
lean_inc(x_19);
x_20 = lean_nat_dec_eq(x_1, x_17);
lean_dec(x_17);
x_21 = 1;
x_22 = l_Bool_DecidableEq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_19);
lean_dec(x_18);
x_23 = l_Lean_IR_ExpandResetReuse_reuseToCtor___main(x_1, x_15);
lean_ctor_set(x_2, 3, x_23);
return x_2;
}
else
{
lean_object* x_24; 
lean_dec(x_13);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_19);
lean_ctor_set(x_2, 2, x_24);
return x_2;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_ctor_get(x_2, 3);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_2);
x_28 = lean_ctor_get(x_13, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_13, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_13, 2);
lean_inc(x_30);
x_31 = lean_nat_dec_eq(x_1, x_28);
lean_dec(x_28);
x_32 = 1;
x_33 = l_Bool_DecidableEq(x_31, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_30);
lean_dec(x_29);
x_34 = l_Lean_IR_ExpandResetReuse_reuseToCtor___main(x_1, x_27);
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_25);
lean_ctor_set(x_35, 1, x_26);
lean_ctor_set(x_35, 2, x_13);
lean_ctor_set(x_35, 3, x_34);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_13);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_30);
x_37 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_37, 0, x_25);
lean_ctor_set(x_37, 1, x_26);
lean_ctor_set(x_37, 2, x_36);
lean_ctor_set(x_37, 3, x_27);
return x_37;
}
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_2);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_2, 3);
x_40 = lean_ctor_get(x_2, 2);
lean_dec(x_40);
x_41 = l_Lean_IR_ExpandResetReuse_reuseToCtor___main(x_1, x_39);
lean_ctor_set(x_2, 3, x_41);
return x_2;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_2, 0);
x_43 = lean_ctor_get(x_2, 1);
x_44 = lean_ctor_get(x_2, 3);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_2);
x_45 = l_Lean_IR_ExpandResetReuse_reuseToCtor___main(x_1, x_44);
x_46 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_43);
lean_ctor_set(x_46, 2, x_13);
lean_ctor_set(x_46, 3, x_45);
return x_46;
}
}
}
case 7:
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_2);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; 
x_48 = lean_ctor_get(x_2, 0);
x_49 = lean_ctor_get(x_2, 1);
x_50 = lean_ctor_get(x_2, 2);
x_51 = lean_nat_dec_eq(x_1, x_48);
x_52 = 1;
x_53 = l_Bool_DecidableEq(x_51, x_52);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = l_Lean_IR_ExpandResetReuse_reuseToCtor___main(x_1, x_50);
lean_ctor_set(x_2, 2, x_54);
return x_2;
}
else
{
lean_free_object(x_2);
lean_dec(x_49);
lean_dec(x_48);
return x_50;
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_58; lean_object* x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; 
x_55 = lean_ctor_get(x_2, 0);
x_56 = lean_ctor_get(x_2, 1);
x_57 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_58 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_59 = lean_ctor_get(x_2, 2);
lean_inc(x_59);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_2);
x_60 = lean_nat_dec_eq(x_1, x_55);
x_61 = 1;
x_62 = l_Bool_DecidableEq(x_60, x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
x_63 = l_Lean_IR_ExpandResetReuse_reuseToCtor___main(x_1, x_59);
x_64 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_64, 0, x_55);
lean_ctor_set(x_64, 1, x_56);
lean_ctor_set(x_64, 2, x_63);
lean_ctor_set_uint8(x_64, sizeof(void*)*3, x_57);
lean_ctor_set_uint8(x_64, sizeof(void*)*3 + 1, x_58);
return x_64;
}
else
{
lean_dec(x_56);
lean_dec(x_55);
return x_59;
}
}
}
case 10:
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_2);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_2, 3);
x_67 = lean_unsigned_to_nat(0u);
x_68 = l_Array_umapMAux___main___at_Lean_IR_ExpandResetReuse_reuseToCtor___main___spec__1(x_1, x_67, x_66);
lean_ctor_set(x_2, 3, x_68);
return x_2;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_69 = lean_ctor_get(x_2, 0);
x_70 = lean_ctor_get(x_2, 1);
x_71 = lean_ctor_get(x_2, 2);
x_72 = lean_ctor_get(x_2, 3);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_2);
x_73 = lean_unsigned_to_nat(0u);
x_74 = l_Array_umapMAux___main___at_Lean_IR_ExpandResetReuse_reuseToCtor___main___spec__1(x_1, x_73, x_72);
x_75 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_75, 0, x_69);
lean_ctor_set(x_75, 1, x_70);
lean_ctor_set(x_75, 2, x_71);
lean_ctor_set(x_75, 3, x_74);
return x_75;
}
}
default: 
{
lean_object* x_76; 
x_76 = lean_box(0);
x_3 = x_76;
goto block_12;
}
}
block_12:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; 
lean_dec(x_3);
x_4 = l_Lean_IR_FnBody_isTerminal(x_2);
x_5 = 1;
x_6 = l_Bool_DecidableEq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_IR_FnBody_body(x_2);
x_8 = lean_box(13);
x_9 = l_Lean_IR_FnBody_setBody(x_2, x_8);
x_10 = l_Lean_IR_ExpandResetReuse_reuseToCtor___main(x_1, x_7);
x_11 = l_Lean_IR_FnBody_setBody(x_9, x_10);
return x_11;
}
else
{
return x_2;
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_ExpandResetReuse_reuseToCtor___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at_Lean_IR_ExpandResetReuse_reuseToCtor___main___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_IR_ExpandResetReuse_reuseToCtor___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ExpandResetReuse_reuseToCtor___main(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_IR_ExpandResetReuse_reuseToCtor(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ExpandResetReuse_reuseToCtor___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_IR_ExpandResetReuse_reuseToCtor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_ExpandResetReuse_mkSlowPath___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_array_fget(x_2, x_3);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_3, x_8);
lean_dec(x_3);
if (lean_obj_tag(x_7) == 0)
{
x_3 = x_9;
goto _start;
}
else
{
lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
x_12 = 1;
x_13 = 0;
x_14 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_8);
lean_ctor_set(x_14, 2, x_4);
lean_ctor_set_uint8(x_14, sizeof(void*)*3, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 1, x_13);
x_3 = x_9;
x_4 = x_14;
goto _start;
}
}
}
}
lean_object* l_Lean_IR_ExpandResetReuse_mkSlowPath(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = l_Lean_IR_ExpandResetReuse_reuseToCtor___main(x_1, x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = 1;
x_8 = 0;
x_9 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_5);
lean_ctor_set_uint8(x_9, sizeof(void*)*3, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*3 + 1, x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_iterateMAux___main___at_Lean_IR_ExpandResetReuse_mkSlowPath___spec__1(x_3, x_3, x_10, x_9);
return x_11;
}
}
lean_object* l_Array_iterateMAux___main___at_Lean_IR_ExpandResetReuse_mkSlowPath___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_iterateMAux___main___at_Lean_IR_ExpandResetReuse_mkSlowPath___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_ExpandResetReuse_mkSlowPath___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ExpandResetReuse_mkSlowPath(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_ExpandResetReuse_mkFresh___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
lean_object* l_Lean_IR_ExpandResetReuse_mkFresh(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_ExpandResetReuse_mkFresh___rarg), 1, 0);
return x_2;
}
}
lean_object* l_Lean_IR_ExpandResetReuse_mkFresh___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_ExpandResetReuse_mkFresh(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Nat_foldMAux___main___at_Lean_IR_ExpandResetReuse_releaseUnreadFields___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_4, x_10);
lean_dec(x_4);
x_12 = lean_nat_sub(x_3, x_11);
x_13 = lean_nat_sub(x_12, x_10);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = lean_array_get(x_14, x_2, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = l_Lean_IR_ExpandResetReuse_mkFresh___rarg(x_7);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_1);
x_19 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_1);
x_20 = 1;
x_21 = 0;
lean_inc(x_17);
x_22 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_10);
lean_ctor_set(x_22, 2, x_5);
lean_ctor_set_uint8(x_22, sizeof(void*)*3, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*3 + 1, x_21);
x_23 = lean_box(7);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_17);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_19);
lean_ctor_set(x_24, 3, x_22);
x_4 = x_11;
x_5 = x_24;
x_7 = x_18;
goto _start;
}
else
{
lean_dec(x_15);
lean_dec(x_13);
x_4 = x_11;
goto _start;
}
}
else
{
lean_object* x_27; 
lean_dec(x_4);
lean_dec(x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_7);
return x_27;
}
}
}
lean_object* l_Lean_IR_ExpandResetReuse_releaseUnreadFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_get_size(x_2);
lean_inc(x_6);
x_7 = l_Nat_foldMAux___main___at_Lean_IR_ExpandResetReuse_releaseUnreadFields___spec__1(x_1, x_2, x_6, x_6, x_3, x_4, x_5);
lean_dec(x_6);
return x_7;
}
}
lean_object* l_Nat_foldMAux___main___at_Lean_IR_ExpandResetReuse_releaseUnreadFields___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_foldMAux___main___at_Lean_IR_ExpandResetReuse_releaseUnreadFields___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Lean_IR_ExpandResetReuse_releaseUnreadFields___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ExpandResetReuse_releaseUnreadFields(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Nat_foldAux___main___at_Lean_IR_ExpandResetReuse_setFields___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_4, x_8);
x_10 = lean_nat_sub(x_3, x_4);
lean_dec(x_4);
x_11 = l_Lean_IR_Arg_Inhabited;
x_12 = lean_array_get(x_11, x_2, x_10);
lean_inc(x_1);
x_13 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_12);
lean_ctor_set(x_13, 3, x_5);
x_4 = x_9;
x_5 = x_13;
goto _start;
}
else
{
lean_dec(x_4);
lean_dec(x_1);
return x_5;
}
}
}
lean_object* l_Lean_IR_ExpandResetReuse_setFields(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_array_get_size(x_2);
lean_inc(x_4);
x_5 = l_Nat_foldAux___main___at_Lean_IR_ExpandResetReuse_setFields___spec__1(x_1, x_2, x_4, x_4, x_3);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Nat_foldAux___main___at_Lean_IR_ExpandResetReuse_setFields___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_foldAux___main___at_Lean_IR_ExpandResetReuse_setFields___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_IR_ExpandResetReuse_setFields___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ExpandResetReuse_setFields(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_AssocList_find___main___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__2(lean_object* x_1, lean_object* x_2) {
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
x_7 = lean_nat_dec_eq(x_4, x_1);
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
lean_object* l_HashMapImp_find___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; size_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_usize_of_nat(x_2);
x_6 = lean_usize_modn(x_5, x_4);
lean_dec(x_4);
x_7 = lean_array_uget(x_3, x_6);
x_8 = l_AssocList_find___main___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__2(x_2, x_7);
lean_dec(x_7);
return x_8;
}
}
uint8_t l_Lean_IR_ExpandResetReuse_isSelfSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = l_HashMapImp_find___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__1(x_1, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
if (lean_obj_tag(x_8) == 3)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_nat_dec_eq(x_9, x_3);
lean_dec(x_9);
if (x_11 == 0)
{
uint8_t x_12; 
lean_dec(x_10);
x_12 = 0;
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_eq(x_10, x_2);
lean_dec(x_10);
return x_13;
}
}
else
{
uint8_t x_14; 
lean_dec(x_8);
x_14 = 0;
return x_14;
}
}
}
else
{
uint8_t x_15; 
x_15 = 0;
return x_15;
}
}
}
lean_object* l_AssocList_find___main___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_AssocList_find___main___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_HashMapImp_find___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HashMapImp_find___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_IR_ExpandResetReuse_isSelfSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Lean_IR_ExpandResetReuse_isSelfSet(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
uint8_t l_Lean_IR_ExpandResetReuse_isSelfUSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_HashMapImp_find___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__1(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = 0;
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
if (lean_obj_tag(x_7) == 4)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_nat_dec_eq(x_8, x_3);
lean_dec(x_8);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_9);
x_11 = 0;
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_eq(x_9, x_2);
lean_dec(x_9);
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_7);
x_13 = 0;
return x_13;
}
}
}
}
lean_object* l_Lean_IR_ExpandResetReuse_isSelfUSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Lean_IR_ExpandResetReuse_isSelfUSet(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
uint8_t l_Lean_IR_ExpandResetReuse_isSelfSSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_HashMapImp_find___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__1(x_1, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
if (lean_obj_tag(x_8) == 5)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 2);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_nat_dec_eq(x_3, x_9);
lean_dec(x_9);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_11);
lean_dec(x_10);
x_13 = 0;
return x_13;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_eq(x_10, x_4);
lean_dec(x_10);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_11);
x_15 = 0;
return x_15;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_eq(x_11, x_2);
lean_dec(x_11);
return x_16;
}
}
}
else
{
uint8_t x_17; 
lean_dec(x_8);
x_17 = 0;
return x_17;
}
}
}
}
lean_object* l_Lean_IR_ExpandResetReuse_isSelfSSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Lean_IR_ExpandResetReuse_isSelfSSet(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_ExpandResetReuse_removeSelfSet___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
x_16 = l_Lean_IR_ExpandResetReuse_removeSelfSet___main(x_1, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = x_17;
x_19 = lean_array_fset(x_11, x_2, x_18);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_8, 0);
lean_inc(x_21);
x_22 = l_Lean_IR_ExpandResetReuse_removeSelfSet___main(x_1, x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = x_23;
x_25 = lean_array_fset(x_11, x_2, x_24);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_25;
goto _start;
}
}
}
}
lean_object* l_Lean_IR_ExpandResetReuse_removeSelfSet___main(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
switch (lean_obj_tag(x_2)) {
case 2:
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_ctor_get(x_2, 2);
x_17 = lean_ctor_get(x_2, 3);
x_18 = l_Lean_IR_ExpandResetReuse_isSelfSet(x_1, x_14, x_15, x_16);
x_19 = 1;
x_20 = l_Bool_DecidableEq(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = l_Lean_IR_ExpandResetReuse_removeSelfSet___main(x_1, x_17);
lean_ctor_set(x_2, 3, x_21);
return x_2;
}
else
{
lean_free_object(x_2);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_2 = x_17;
goto _start;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_ctor_get(x_2, 1);
x_25 = lean_ctor_get(x_2, 2);
x_26 = lean_ctor_get(x_2, 3);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_2);
x_27 = l_Lean_IR_ExpandResetReuse_isSelfSet(x_1, x_23, x_24, x_25);
x_28 = 1;
x_29 = l_Bool_DecidableEq(x_27, x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lean_IR_ExpandResetReuse_removeSelfSet___main(x_1, x_26);
x_31 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_31, 0, x_23);
lean_ctor_set(x_31, 1, x_24);
lean_ctor_set(x_31, 2, x_25);
lean_ctor_set(x_31, 3, x_30);
return x_31;
}
else
{
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
x_2 = x_26;
goto _start;
}
}
}
case 4:
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_2);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; 
x_34 = lean_ctor_get(x_2, 0);
x_35 = lean_ctor_get(x_2, 1);
x_36 = lean_ctor_get(x_2, 2);
x_37 = lean_ctor_get(x_2, 3);
x_38 = l_Lean_IR_ExpandResetReuse_isSelfUSet(x_1, x_34, x_35, x_36);
x_39 = 1;
x_40 = l_Bool_DecidableEq(x_38, x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = l_Lean_IR_ExpandResetReuse_removeSelfSet___main(x_1, x_37);
lean_ctor_set(x_2, 3, x_41);
return x_2;
}
else
{
lean_free_object(x_2);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
x_2 = x_37;
goto _start;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; 
x_43 = lean_ctor_get(x_2, 0);
x_44 = lean_ctor_get(x_2, 1);
x_45 = lean_ctor_get(x_2, 2);
x_46 = lean_ctor_get(x_2, 3);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_2);
x_47 = l_Lean_IR_ExpandResetReuse_isSelfUSet(x_1, x_43, x_44, x_45);
x_48 = 1;
x_49 = l_Bool_DecidableEq(x_47, x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = l_Lean_IR_ExpandResetReuse_removeSelfSet___main(x_1, x_46);
x_51 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_51, 0, x_43);
lean_ctor_set(x_51, 1, x_44);
lean_ctor_set(x_51, 2, x_45);
lean_ctor_set(x_51, 3, x_50);
return x_51;
}
else
{
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
x_2 = x_46;
goto _start;
}
}
}
case 5:
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_2);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; 
x_54 = lean_ctor_get(x_2, 0);
x_55 = lean_ctor_get(x_2, 1);
x_56 = lean_ctor_get(x_2, 2);
x_57 = lean_ctor_get(x_2, 3);
x_58 = lean_ctor_get(x_2, 4);
x_59 = lean_ctor_get(x_2, 5);
x_60 = l_Lean_IR_ExpandResetReuse_isSelfSSet(x_1, x_54, x_55, x_56, x_57);
x_61 = 1;
x_62 = l_Bool_DecidableEq(x_60, x_61);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = l_Lean_IR_ExpandResetReuse_removeSelfSet___main(x_1, x_59);
lean_ctor_set(x_2, 5, x_63);
return x_2;
}
else
{
lean_free_object(x_2);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
x_2 = x_59;
goto _start;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; 
x_65 = lean_ctor_get(x_2, 0);
x_66 = lean_ctor_get(x_2, 1);
x_67 = lean_ctor_get(x_2, 2);
x_68 = lean_ctor_get(x_2, 3);
x_69 = lean_ctor_get(x_2, 4);
x_70 = lean_ctor_get(x_2, 5);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_2);
x_71 = l_Lean_IR_ExpandResetReuse_isSelfSSet(x_1, x_65, x_66, x_67, x_68);
x_72 = 1;
x_73 = l_Bool_DecidableEq(x_71, x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = l_Lean_IR_ExpandResetReuse_removeSelfSet___main(x_1, x_70);
x_75 = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(x_75, 0, x_65);
lean_ctor_set(x_75, 1, x_66);
lean_ctor_set(x_75, 2, x_67);
lean_ctor_set(x_75, 3, x_68);
lean_ctor_set(x_75, 4, x_69);
lean_ctor_set(x_75, 5, x_74);
return x_75;
}
else
{
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
x_2 = x_70;
goto _start;
}
}
}
case 10:
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_2);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_2, 3);
x_79 = lean_unsigned_to_nat(0u);
x_80 = l_Array_umapMAux___main___at_Lean_IR_ExpandResetReuse_removeSelfSet___main___spec__1(x_1, x_79, x_78);
lean_ctor_set(x_2, 3, x_80);
return x_2;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_81 = lean_ctor_get(x_2, 0);
x_82 = lean_ctor_get(x_2, 1);
x_83 = lean_ctor_get(x_2, 2);
x_84 = lean_ctor_get(x_2, 3);
lean_inc(x_84);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_2);
x_85 = lean_unsigned_to_nat(0u);
x_86 = l_Array_umapMAux___main___at_Lean_IR_ExpandResetReuse_removeSelfSet___main___spec__1(x_1, x_85, x_84);
x_87 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_87, 0, x_81);
lean_ctor_set(x_87, 1, x_82);
lean_ctor_set(x_87, 2, x_83);
lean_ctor_set(x_87, 3, x_86);
return x_87;
}
}
default: 
{
lean_object* x_88; 
x_88 = lean_box(0);
x_3 = x_88;
goto block_12;
}
}
block_12:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; 
lean_dec(x_3);
x_4 = l_Lean_IR_FnBody_isTerminal(x_2);
x_5 = 1;
x_6 = l_Bool_DecidableEq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l_Lean_IR_FnBody_body(x_2);
x_8 = lean_box(13);
x_9 = l_Lean_IR_FnBody_setBody(x_2, x_8);
x_10 = l_Lean_IR_ExpandResetReuse_removeSelfSet___main(x_1, x_7);
x_11 = l_Lean_IR_FnBody_setBody(x_9, x_10);
return x_11;
}
else
{
return x_2;
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_ExpandResetReuse_removeSelfSet___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at_Lean_IR_ExpandResetReuse_removeSelfSet___main___spec__1(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Lean_IR_ExpandResetReuse_removeSelfSet___main___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ExpandResetReuse_removeSelfSet___main(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_IR_ExpandResetReuse_removeSelfSet(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ExpandResetReuse_removeSelfSet___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_IR_ExpandResetReuse_removeSelfSet___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_ExpandResetReuse_reuseToSet___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_5);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
x_8 = l_Array_empty___closed__1;
x_9 = x_5;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_array_fget(x_5, x_4);
x_11 = lean_box(0);
lean_inc(x_10);
x_12 = x_11;
x_13 = lean_array_fset(x_5, x_4, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_4, x_14);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_3);
x_18 = l_Lean_IR_ExpandResetReuse_reuseToSet___main(x_1, x_2, x_3, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = x_19;
x_21 = lean_array_fset(x_13, x_4, x_20);
lean_dec(x_4);
x_4 = x_15;
x_5 = x_21;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_10, 0);
lean_inc(x_23);
lean_inc(x_3);
x_24 = l_Lean_IR_ExpandResetReuse_reuseToSet___main(x_1, x_2, x_3, x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = x_25;
x_27 = lean_array_fset(x_13, x_4, x_26);
lean_dec(x_4);
x_4 = x_15;
x_5 = x_27;
goto _start;
}
}
}
}
lean_object* l_Lean_IR_ExpandResetReuse_reuseToSet___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_4, 2);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 2)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_4);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; 
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
x_19 = lean_ctor_get(x_4, 3);
x_20 = lean_ctor_get(x_4, 2);
lean_dec(x_20);
x_21 = lean_ctor_get(x_15, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
x_23 = lean_ctor_get_uint8(x_15, sizeof(void*)*3);
x_24 = lean_ctor_get(x_15, 2);
lean_inc(x_24);
x_25 = lean_nat_dec_eq(x_2, x_21);
lean_dec(x_21);
x_26 = 1;
x_27 = l_Bool_DecidableEq(x_25, x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_24);
lean_dec(x_22);
x_28 = l_Lean_IR_ExpandResetReuse_reuseToSet___main(x_1, x_2, x_3, x_19);
lean_ctor_set(x_4, 3, x_28);
return x_4;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_free_object(x_4);
lean_dec(x_18);
lean_dec(x_15);
lean_inc(x_3);
x_29 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_17, x_3, x_19);
lean_dec(x_17);
lean_inc(x_3);
x_30 = l_Lean_IR_ExpandResetReuse_setFields(x_3, x_24, x_29);
lean_dec(x_24);
x_31 = l_Bool_DecidableEq(x_23, x_26);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_22);
lean_dec(x_3);
x_32 = l_Lean_IR_ExpandResetReuse_removeSelfSet___main(x_1, x_30);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_22, 1);
lean_inc(x_33);
lean_dec(x_22);
x_34 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_34, 0, x_3);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_30);
x_35 = l_Lean_IR_ExpandResetReuse_removeSelfSet___main(x_1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; 
x_36 = lean_ctor_get(x_4, 0);
x_37 = lean_ctor_get(x_4, 1);
x_38 = lean_ctor_get(x_4, 3);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_4);
x_39 = lean_ctor_get(x_15, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_15, 1);
lean_inc(x_40);
x_41 = lean_ctor_get_uint8(x_15, sizeof(void*)*3);
x_42 = lean_ctor_get(x_15, 2);
lean_inc(x_42);
x_43 = lean_nat_dec_eq(x_2, x_39);
lean_dec(x_39);
x_44 = 1;
x_45 = l_Bool_DecidableEq(x_43, x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_42);
lean_dec(x_40);
x_46 = l_Lean_IR_ExpandResetReuse_reuseToSet___main(x_1, x_2, x_3, x_38);
x_47 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_47, 0, x_36);
lean_ctor_set(x_47, 1, x_37);
lean_ctor_set(x_47, 2, x_15);
lean_ctor_set(x_47, 3, x_46);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_37);
lean_dec(x_15);
lean_inc(x_3);
x_48 = l_Lean_IR_MapVars_mapFnBody___main___at_Lean_IR_FnBody_replaceVar___spec__1(x_36, x_3, x_38);
lean_dec(x_36);
lean_inc(x_3);
x_49 = l_Lean_IR_ExpandResetReuse_setFields(x_3, x_42, x_48);
lean_dec(x_42);
x_50 = l_Bool_DecidableEq(x_41, x_44);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_40);
lean_dec(x_3);
x_51 = l_Lean_IR_ExpandResetReuse_removeSelfSet___main(x_1, x_49);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_40, 1);
lean_inc(x_52);
lean_dec(x_40);
x_53 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_53, 0, x_3);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_53, 2, x_49);
x_54 = l_Lean_IR_ExpandResetReuse_removeSelfSet___main(x_1, x_53);
return x_54;
}
}
}
}
else
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_4);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_4, 3);
x_57 = lean_ctor_get(x_4, 2);
lean_dec(x_57);
x_58 = l_Lean_IR_ExpandResetReuse_reuseToSet___main(x_1, x_2, x_3, x_56);
lean_ctor_set(x_4, 3, x_58);
return x_4;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_4, 0);
x_60 = lean_ctor_get(x_4, 1);
x_61 = lean_ctor_get(x_4, 3);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_4);
x_62 = l_Lean_IR_ExpandResetReuse_reuseToSet___main(x_1, x_2, x_3, x_61);
x_63 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_63, 0, x_59);
lean_ctor_set(x_63, 1, x_60);
lean_ctor_set(x_63, 2, x_15);
lean_ctor_set(x_63, 3, x_62);
return x_63;
}
}
}
case 7:
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_4);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; 
x_65 = lean_ctor_get(x_4, 0);
x_66 = lean_ctor_get(x_4, 1);
x_67 = lean_ctor_get(x_4, 2);
x_68 = lean_nat_dec_eq(x_2, x_65);
x_69 = 1;
x_70 = l_Bool_DecidableEq(x_68, x_69);
if (x_70 == 0)
{
lean_object* x_71; 
x_71 = l_Lean_IR_ExpandResetReuse_reuseToSet___main(x_1, x_2, x_3, x_67);
lean_ctor_set(x_4, 2, x_71);
return x_4;
}
else
{
lean_object* x_72; 
lean_free_object(x_4);
lean_dec(x_66);
lean_dec(x_65);
x_72 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_72, 0, x_3);
lean_ctor_set(x_72, 1, x_67);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_76; lean_object* x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; 
x_73 = lean_ctor_get(x_4, 0);
x_74 = lean_ctor_get(x_4, 1);
x_75 = lean_ctor_get_uint8(x_4, sizeof(void*)*3);
x_76 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 1);
x_77 = lean_ctor_get(x_4, 2);
lean_inc(x_77);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_4);
x_78 = lean_nat_dec_eq(x_2, x_73);
x_79 = 1;
x_80 = l_Bool_DecidableEq(x_78, x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = l_Lean_IR_ExpandResetReuse_reuseToSet___main(x_1, x_2, x_3, x_77);
x_82 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_82, 0, x_73);
lean_ctor_set(x_82, 1, x_74);
lean_ctor_set(x_82, 2, x_81);
lean_ctor_set_uint8(x_82, sizeof(void*)*3, x_75);
lean_ctor_set_uint8(x_82, sizeof(void*)*3 + 1, x_76);
return x_82;
}
else
{
lean_object* x_83; 
lean_dec(x_74);
lean_dec(x_73);
x_83 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_83, 0, x_3);
lean_ctor_set(x_83, 1, x_77);
return x_83;
}
}
}
case 10:
{
uint8_t x_84; 
x_84 = !lean_is_exclusive(x_4);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_4, 3);
x_86 = lean_unsigned_to_nat(0u);
x_87 = l_Array_umapMAux___main___at_Lean_IR_ExpandResetReuse_reuseToSet___main___spec__1(x_1, x_2, x_3, x_86, x_85);
lean_ctor_set(x_4, 3, x_87);
return x_4;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_88 = lean_ctor_get(x_4, 0);
x_89 = lean_ctor_get(x_4, 1);
x_90 = lean_ctor_get(x_4, 2);
x_91 = lean_ctor_get(x_4, 3);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_4);
x_92 = lean_unsigned_to_nat(0u);
x_93 = l_Array_umapMAux___main___at_Lean_IR_ExpandResetReuse_reuseToSet___main___spec__1(x_1, x_2, x_3, x_92, x_91);
x_94 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_94, 0, x_88);
lean_ctor_set(x_94, 1, x_89);
lean_ctor_set(x_94, 2, x_90);
lean_ctor_set(x_94, 3, x_93);
return x_94;
}
}
default: 
{
lean_object* x_95; 
x_95 = lean_box(0);
x_5 = x_95;
goto block_14;
}
}
block_14:
{
uint8_t x_6; uint8_t x_7; uint8_t x_8; 
lean_dec(x_5);
x_6 = l_Lean_IR_FnBody_isTerminal(x_4);
x_7 = 1;
x_8 = l_Bool_DecidableEq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = l_Lean_IR_FnBody_body(x_4);
x_10 = lean_box(13);
x_11 = l_Lean_IR_FnBody_setBody(x_4, x_10);
x_12 = l_Lean_IR_ExpandResetReuse_reuseToSet___main(x_1, x_2, x_3, x_9);
x_13 = l_Lean_IR_FnBody_setBody(x_11, x_12);
return x_13;
}
else
{
lean_dec(x_3);
return x_4;
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_ExpandResetReuse_reuseToSet___main___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_umapMAux___main___at_Lean_IR_ExpandResetReuse_reuseToSet___main___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* l_Lean_IR_ExpandResetReuse_reuseToSet___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ExpandResetReuse_reuseToSet___main(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_ExpandResetReuse_reuseToSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ExpandResetReuse_reuseToSet___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_IR_ExpandResetReuse_reuseToSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Lean_IR_ExpandResetReuse_mkFastPath(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_2);
x_7 = l_Lean_IR_ExpandResetReuse_reuseToSet___main(x_5, x_1, x_2, x_4);
x_8 = l_Lean_IR_ExpandResetReuse_releaseUnreadFields(x_2, x_3, x_7, x_5, x_6);
return x_8;
}
}
lean_object* l_Lean_IR_ExpandResetReuse_mkFastPath___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_ExpandResetReuse_mkFastPath(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_IR_ExpandResetReuse_expand(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_9 = l_Lean_IR_ExpandResetReuse_eraseProjIncFor(x_4, x_5, x_2);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_6);
lean_inc(x_5);
x_12 = l_Lean_IR_ExpandResetReuse_mkSlowPath(x_3, x_5, x_11, x_6);
lean_inc(x_5);
x_13 = l_Lean_IR_ExpandResetReuse_mkFastPath(x_3, x_5, x_11, x_6, x_7, x_8);
lean_dec(x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Array_empty___closed__1;
x_17 = lean_apply_4(x_1, x_14, x_16, x_7, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_IR_ExpandResetReuse_mkFresh___rarg(x_19);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(x_23, 0, x_5);
lean_inc(x_22);
x_24 = l_Lean_IR_mkIf(x_22, x_12, x_18);
x_25 = lean_box(1);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_22);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_23);
lean_ctor_set(x_26, 3, x_24);
x_27 = l_Lean_IR_reshape(x_10, x_26);
lean_ctor_set(x_20, 0, x_27);
return x_20;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_20, 0);
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_20);
x_30 = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(x_30, 0, x_5);
lean_inc(x_28);
x_31 = l_Lean_IR_mkIf(x_28, x_12, x_18);
x_32 = lean_box(1);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_30);
lean_ctor_set(x_33, 3, x_31);
x_34 = l_Lean_IR_reshape(x_10, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_29);
return x_35;
}
}
}
lean_object* l_Lean_IR_ExpandResetReuse_expand___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_IR_ExpandResetReuse_expand(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_IR_ExpandResetReuse_searchAndExpand___main___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_nat_dec_lt(x_1, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = l_Array_empty___closed__1;
x_8 = x_2;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_array_fget(x_2, x_1);
x_11 = lean_box(0);
lean_inc(x_10);
x_12 = x_11;
x_13 = lean_array_fset(x_2, x_1, x_12);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
x_16 = l_Array_empty___closed__1;
lean_inc(x_3);
x_17 = l_Lean_IR_ExpandResetReuse_searchAndExpand___main(x_15, x_16, x_3, x_4);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_1, x_21);
x_23 = x_20;
x_24 = lean_array_fset(x_13, x_1, x_23);
lean_dec(x_1);
x_1 = x_22;
x_2 = x_24;
x_4 = x_19;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_26 = lean_ctor_get(x_10, 0);
lean_inc(x_26);
x_27 = l_Array_empty___closed__1;
lean_inc(x_3);
x_28 = l_Lean_IR_ExpandResetReuse_searchAndExpand___main(x_26, x_27, x_3, x_4);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_29);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_1, x_32);
x_34 = x_31;
x_35 = lean_array_fset(x_13, x_1, x_34);
lean_dec(x_1);
x_1 = x_33;
x_2 = x_35;
x_4 = x_30;
goto _start;
}
}
}
}
lean_object* _init_l_Lean_IR_ExpandResetReuse_searchAndExpand___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_ExpandResetReuse_searchAndExpand___main), 4, 0);
return x_1;
}
}
lean_object* l_Lean_IR_ExpandResetReuse_searchAndExpand___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 3);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
lean_inc(x_17);
x_20 = l_Lean_IR_ExpandResetReuse_consumed___main(x_16, x_17);
x_21 = 1;
x_22 = l_Bool_DecidableEq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
x_23 = l_Lean_IR_push(x_2, x_1);
x_1 = x_17;
x_2 = x_23;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_1);
x_25 = l_Lean_IR_ExpandResetReuse_searchAndExpand___main___closed__1;
x_26 = l_Lean_IR_ExpandResetReuse_expand(x_25, x_2, x_16, x_18, x_19, x_17, x_3, x_4);
lean_dec(x_16);
return x_26;
}
}
else
{
lean_object* x_27; 
lean_dec(x_15);
x_27 = lean_box(0);
x_5 = x_27;
goto block_14;
}
}
case 1:
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_1);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_1, 2);
x_30 = lean_ctor_get(x_1, 3);
x_31 = l_Array_empty___closed__1;
lean_inc(x_3);
x_32 = l_Lean_IR_ExpandResetReuse_searchAndExpand___main(x_29, x_31, x_3, x_4);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_box(13);
lean_ctor_set(x_1, 3, x_35);
lean_ctor_set(x_1, 2, x_33);
x_36 = l_Lean_IR_push(x_2, x_1);
x_1 = x_30;
x_2 = x_36;
x_4 = x_34;
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_38 = lean_ctor_get(x_1, 0);
x_39 = lean_ctor_get(x_1, 1);
x_40 = lean_ctor_get(x_1, 2);
x_41 = lean_ctor_get(x_1, 3);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_1);
x_42 = l_Array_empty___closed__1;
lean_inc(x_3);
x_43 = l_Lean_IR_ExpandResetReuse_searchAndExpand___main(x_40, x_42, x_3, x_4);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_box(13);
x_47 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_47, 0, x_38);
lean_ctor_set(x_47, 1, x_39);
lean_ctor_set(x_47, 2, x_44);
lean_ctor_set(x_47, 3, x_46);
x_48 = l_Lean_IR_push(x_2, x_47);
x_1 = x_41;
x_2 = x_48;
x_4 = x_45;
goto _start;
}
}
case 10:
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_1);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_1, 3);
x_52 = lean_unsigned_to_nat(0u);
x_53 = l_Array_umapMAux___main___at_Lean_IR_ExpandResetReuse_searchAndExpand___main___spec__1(x_52, x_51, x_3, x_4);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_53, 0);
lean_ctor_set(x_1, 3, x_55);
x_56 = l_Lean_IR_reshape(x_2, x_1);
lean_ctor_set(x_53, 0, x_56);
return x_53;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_53, 0);
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_53);
lean_ctor_set(x_1, 3, x_57);
x_59 = l_Lean_IR_reshape(x_2, x_1);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_61 = lean_ctor_get(x_1, 0);
x_62 = lean_ctor_get(x_1, 1);
x_63 = lean_ctor_get(x_1, 2);
x_64 = lean_ctor_get(x_1, 3);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_1);
x_65 = lean_unsigned_to_nat(0u);
x_66 = l_Array_umapMAux___main___at_Lean_IR_ExpandResetReuse_searchAndExpand___main___spec__1(x_65, x_64, x_3, x_4);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_69 = x_66;
} else {
 lean_dec_ref(x_66);
 x_69 = lean_box(0);
}
x_70 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_70, 0, x_61);
lean_ctor_set(x_70, 1, x_62);
lean_ctor_set(x_70, 2, x_63);
lean_ctor_set(x_70, 3, x_67);
x_71 = l_Lean_IR_reshape(x_2, x_70);
if (lean_is_scalar(x_69)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_69;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_68);
return x_72;
}
}
default: 
{
lean_object* x_73; 
x_73 = lean_box(0);
x_5 = x_73;
goto block_14;
}
}
block_14:
{
uint8_t x_6; uint8_t x_7; uint8_t x_8; 
lean_dec(x_5);
x_6 = l_Lean_IR_FnBody_isTerminal(x_1);
x_7 = 1;
x_8 = l_Bool_DecidableEq(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_IR_FnBody_body(x_1);
x_10 = l_Lean_IR_push(x_2, x_1);
x_1 = x_9;
x_2 = x_10;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
x_12 = l_Lean_IR_reshape(x_2, x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
}
}
}
lean_object* l_Lean_IR_ExpandResetReuse_searchAndExpand(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ExpandResetReuse_searchAndExpand___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_IR_ExpandResetReuse_main(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
lean_inc(x_1);
x_6 = l_Lean_IR_ExpandResetReuse_mkProjMap(x_1);
x_7 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_8 = l_Lean_IR_MaxIndex_collectDecl(x_1, x_7);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_1, 3);
lean_dec(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_dec(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 0);
lean_dec(x_13);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_8, x_14);
lean_dec(x_8);
x_16 = l_Array_empty___closed__1;
x_17 = l_Lean_IR_ExpandResetReuse_searchAndExpand___main(x_5, x_16, x_6, x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
lean_ctor_set(x_1, 3, x_18);
return x_1;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_1);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_8, x_19);
lean_dec(x_8);
x_21 = l_Array_empty___closed__1;
x_22 = l_Lean_IR_ExpandResetReuse_searchAndExpand___main(x_5, x_21, x_6, x_20);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_2);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 2, x_4);
lean_ctor_set(x_24, 3, x_23);
return x_24;
}
}
else
{
return x_1;
}
}
}
lean_object* l_Lean_IR_Decl_expandResetReuse(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_IR_ExpandResetReuse_main(x_1);
x_3 = l_Lean_IR_Decl_normalizeIds(x_2);
return x_3;
}
}
lean_object* initialize_Init_Control_State(lean_object*);
lean_object* initialize_Init_Control_Reader(lean_object*);
lean_object* initialize_Init_Data_Nat(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_CompilerM(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_NormIds(lean_object*);
lean_object* initialize_Init_Lean_Compiler_IR_FreeVars(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Compiler_IR_ExpandResetReuse(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Control_State(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Control_Reader(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_CompilerM(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_NormIds(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Compiler_IR_FreeVars(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_ExpandResetReuse_mkProjMap___closed__1 = _init_l_Lean_IR_ExpandResetReuse_mkProjMap___closed__1();
lean_mark_persistent(l_Lean_IR_ExpandResetReuse_mkProjMap___closed__1);
l_Lean_IR_ExpandResetReuse_searchAndExpand___main___closed__1 = _init_l_Lean_IR_ExpandResetReuse_searchAndExpand___main___closed__1();
lean_mark_persistent(l_Lean_IR_ExpandResetReuse_searchAndExpand___main___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
