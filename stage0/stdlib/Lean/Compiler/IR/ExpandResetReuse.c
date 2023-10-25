// Lean compiler output
// Module: Lean.Compiler.IR.ExpandResetReuse
// Imports: Init Lean.Compiler.IR.CompilerM Lean.Compiler.IR.NormIds Lean.Compiler.IR.FreeVars
#include <lean/lean.h>
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
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncFor(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__outOfBounds___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_Lean_IR_ExpandResetReuse_setFields___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncForAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncFor___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_reuseToCtor___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_isSelfSSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_releaseUnreadFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_IR_push(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__2(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_removeSelfSet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lean_IR_ExpandResetReuse_releaseUnreadFields___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_removeSelfSet___spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_FnBody_isTerminal(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_reuseToCtor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_reuseToSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedFnBody;
lean_object* l_Lean_IR_FnBody_replaceVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_expandResetReuse(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_setFields(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkSlowPath(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkProjMap(lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_Lean_IR_ExpandResetReuse_setFields___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_searchAndExpand___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Array_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_searchAndExpand(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkFresh(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_reuseToSet(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkFresh___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncFor___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
lean_object* l_Lean_IR_FnBody_body(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkFastPath(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_ExpandResetReuse_consumed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_reuseToCtor___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_main(lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_ExpandResetReuse_isSelfSet(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__2(lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedArg;
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_IR_ExpandResetReuse_mkProjMap___spec__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_IR_ExpandResetReuse_consumed___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_reuseToSet___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_hashmap_mk_idx(lean_object*, uint64_t);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
lean_object* l_Lean_IR_mkIf(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_consumed___boxed(lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_setBody(lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_updateBody_x21(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkFastPath___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_removeSelfSet___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_releaseUnreadFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_ExpandResetReuse_isSelfSSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_ExpandResetReuse_mkSlowPath___spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_AltCore_body(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Array_back___rarg(lean_object*, lean_object*);
lean_object* l_Lean_IR_MaxIndex_collectDecl(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_ExpandResetReuse_isSelfUSet(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkHashMapImp___rarg(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_reuseToCtor___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_searchAndExpand___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_setFields___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_isSelfUSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__5___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__6(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExpandResetReuse_searchAndExpand___closed__1;
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lean_IR_ExpandResetReuse_releaseUnreadFields___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_IR_ExpandResetReuse_consumed___spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_ExpandResetReuse_mkSlowPath___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_reuseToSet___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_IR_reshape(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_normalizeIds(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_expand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_isSelfSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkFresh___rarg(lean_object*);
lean_object* l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_IR_ExpandResetReuse_mkProjMap___spec__1(lean_object*);
LEAN_EXPORT uint8_t l_Lean_AssocList_contains___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__2(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_5);
x_8 = lean_apply_1(x_1, x_5);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_10 = lean_hashmap_mk_idx(x_7, x_9);
x_11 = lean_array_uget(x_2, x_10);
lean_ctor_set(x_3, 2, x_11);
x_12 = lean_array_uset(x_2, x_10, x_3);
x_2 = x_12;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_ctor_get(x_3, 2);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_17 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_14);
x_18 = lean_apply_1(x_1, x_14);
x_19 = lean_unbox_uint64(x_18);
lean_dec(x_18);
x_20 = lean_hashmap_mk_idx(x_17, x_19);
x_21 = lean_array_uget(x_2, x_20);
x_22 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_15);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_array_uset(x_2, x_20, x_22);
x_2 = x_23;
x_3 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_foldlM___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__5___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__6(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = lean_uint64_of_nat(x_4);
x_8 = lean_hashmap_mk_idx(x_6, x_7);
x_9 = lean_array_uget(x_1, x_8);
lean_ctor_set(x_2, 2, x_9);
x_10 = lean_array_uset(x_1, x_8, x_2);
x_1 = x_10;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
x_15 = lean_array_get_size(x_1);
x_16 = lean_uint64_of_nat(x_12);
x_17 = lean_hashmap_mk_idx(x_15, x_16);
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
LEAN_EXPORT lean_object* l_Lean_HashMapImp_moveEntries___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Lean_AssocList_foldlM___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__5___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__6(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Lean_HashMapImp_expand___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__3(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Lean_HashMapImp_moveEntries___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__4(x_8, x_2, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_replace___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_3, 2);
x_9 = lean_nat_dec_eq(x_6, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l_Lean_AssocList_replace___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__7(x_1, x_2, x_8);
lean_ctor_set(x_3, 2, x_10);
return x_3;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_14 = lean_nat_dec_eq(x_11, x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_AssocList_replace___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__7(x_1, x_2, x_13);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_13);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HashMap_insert___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; size_t x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_uint64_of_nat(x_2);
lean_inc(x_7);
x_9 = lean_hashmap_mk_idx(x_7, x_8);
x_10 = lean_array_uget(x_6, x_9);
x_11 = l_Lean_AssocList_contains___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__2(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_5, x_12);
lean_dec(x_5);
x_14 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_3);
lean_ctor_set(x_14, 2, x_10);
x_15 = lean_array_uset(x_6, x_9, x_14);
x_16 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_13);
x_17 = lean_nat_dec_le(x_16, x_7);
lean_dec(x_7);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_free_object(x_1);
x_18 = l_Lean_HashMapImp_expand___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__3(x_13, x_15);
return x_18;
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
lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
x_19 = l_Lean_AssocList_replace___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__7(x_2, x_3, x_10);
x_20 = lean_array_uset(x_6, x_9, x_19);
lean_ctor_set(x_1, 1, x_20);
return x_1;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint64_t x_24; size_t x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_ctor_get(x_1, 0);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_1);
x_23 = lean_array_get_size(x_22);
x_24 = lean_uint64_of_nat(x_2);
lean_inc(x_23);
x_25 = lean_hashmap_mk_idx(x_23, x_24);
x_26 = lean_array_uget(x_22, x_25);
x_27 = l_Lean_AssocList_contains___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__2(x_2, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_21, x_28);
lean_dec(x_21);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_3);
lean_ctor_set(x_30, 2, x_26);
x_31 = lean_array_uset(x_22, x_25, x_30);
x_32 = l___private_Lean_Data_HashMap_0__Lean_numBucketsForCapacity(x_29);
x_33 = lean_nat_dec_le(x_32, x_23);
lean_dec(x_23);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = l_Lean_HashMapImp_expand___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__3(x_29, x_31);
return x_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_31);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_23);
x_36 = l_Lean_AssocList_replace___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__7(x_2, x_3, x_26);
x_37 = lean_array_uset(x_22, x_25, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_21);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 3:
{
lean_object* x_4; 
x_4 = l_Lean_HashMap_insert___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(x_3, x_1, x_2);
return x_4;
}
case 4:
{
lean_object* x_5; 
x_5 = l_Lean_HashMap_insert___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(x_3, x_1, x_2);
return x_5;
}
case 5:
{
lean_object* x_6; 
x_6 = l_Lean_HashMap_insert___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(x_3, x_1, x_2);
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
LEAN_EXPORT lean_object* l_Lean_AssocList_contains___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_AssocList_contains___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_IR_AltCore_body(x_6);
lean_dec(x_6);
x_8 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody(x_7, x_4);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_8;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 3);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody(x_5, x_2);
switch (lean_obj_tag(x_4)) {
case 3:
{
lean_object* x_7; 
x_7 = l_Lean_HashMap_insert___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(x_6, x_3, x_4);
return x_7;
}
case 4:
{
lean_object* x_8; 
x_8 = l_Lean_HashMap_insert___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(x_6, x_3, x_4);
return x_8;
}
case 5:
{
lean_object* x_9; 
x_9 = l_Lean_HashMap_insert___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(x_6, x_3, x_4);
return x_9;
}
default: 
{
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
}
case 1:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody(x_11, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
case 10:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_array_get_size(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_dec_lt(x_16, x_15);
if (x_17 == 0)
{
lean_dec(x_15);
lean_dec(x_14);
return x_2;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_15, x_15);
if (x_18 == 0)
{
lean_dec(x_15);
lean_dec(x_14);
return x_2;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = 0;
x_20 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_21 = l_Array_foldlMUnsafe_fold___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___spec__1(x_14, x_19, x_20, x_2);
lean_dec(x_14);
return x_21;
}
}
}
default: 
{
uint8_t x_22; 
x_22 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = l_Lean_IR_FnBody_body(x_1);
lean_dec(x_1);
x_1 = x_23;
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
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_IR_ExpandResetReuse_mkProjMap___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMapImp___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkProjMap(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_unsigned_to_nat(8u);
x_4 = l_Lean_mkHashMapImp___rarg(x_3);
x_5 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_unsigned_to_nat(8u);
x_7 = l_Lean_mkHashMapImp___rarg(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkHashMap___at_Lean_IR_ExpandResetReuse_mkProjMap___spec__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_mkHashMap___at_Lean_IR_ExpandResetReuse_mkProjMap___spec__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_IR_ExpandResetReuse_consumed___spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lean_IR_AltCore_body(x_6);
lean_dec(x_6);
x_8 = l_Lean_IR_ExpandResetReuse_consumed(x_1, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = 1;
return x_9;
}
else
{
size_t x_10; size_t x_11; 
x_10 = 1;
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
goto _start;
}
}
else
{
uint8_t x_13; 
x_13 = 0;
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_Lean_IR_ExpandResetReuse_consumed(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 2)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 3);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_nat_dec_eq(x_1, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
x_2 = x_4;
goto _start;
}
else
{
uint8_t x_8; 
lean_dec(x_4);
x_8 = 1;
return x_8;
}
}
else
{
lean_object* x_9; 
lean_dec(x_3);
x_9 = lean_ctor_get(x_2, 3);
lean_inc(x_9);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
}
case 7:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 2);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_nat_dec_eq(x_1, x_11);
lean_dec(x_11);
if (x_13 == 0)
{
x_2 = x_12;
goto _start;
}
else
{
uint8_t x_15; 
lean_dec(x_12);
x_15 = 1;
return x_15;
}
}
case 10:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_2, 3);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_array_get_size(x_16);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_lt(x_18, x_17);
if (x_19 == 0)
{
uint8_t x_20; 
lean_dec(x_17);
lean_dec(x_16);
x_20 = 1;
return x_20;
}
else
{
size_t x_21; size_t x_22; uint8_t x_23; 
x_21 = 0;
x_22 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_23 = l_Array_anyMUnsafe_any___at_Lean_IR_ExpandResetReuse_consumed___spec__1(x_1, x_16, x_21, x_22);
lean_dec(x_16);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = 1;
return x_24;
}
else
{
uint8_t x_25; 
x_25 = 0;
return x_25;
}
}
}
default: 
{
uint8_t x_26; 
x_26 = l_Lean_IR_FnBody_isTerminal(x_2);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = l_Lean_IR_FnBody_body(x_2);
lean_dec(x_2);
x_2 = x_27;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_2);
x_29 = 0;
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_IR_ExpandResetReuse_consumed___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at_Lean_IR_ExpandResetReuse_consumed___spec__1(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_consumed___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_IR_ExpandResetReuse_consumed(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncForAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_unsigned_to_nat(2u);
x_7 = lean_nat_dec_lt(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_IR_instInhabitedFnBody;
x_9 = l_Array_back___rarg(x_8, x_2);
switch (lean_obj_tag(x_9)) {
case 0:
{
lean_object* x_10; 
lean_dec(x_5);
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
switch (lean_obj_tag(x_10)) {
case 4:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_10);
x_11 = lean_array_pop(x_2);
x_12 = lean_array_push(x_4, x_9);
x_2 = x_11;
x_4 = x_12;
goto _start;
}
case 5:
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_10);
x_14 = lean_array_pop(x_2);
x_15 = lean_array_push(x_4, x_9);
x_2 = x_14;
x_4 = x_15;
goto _start;
}
default: 
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_10);
lean_dec(x_9);
x_17 = l_Array_reverse___rarg(x_4);
x_18 = l_Array_append___rarg(x_2, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_3);
return x_19;
}
}
}
case 6:
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_58; uint8_t x_59; 
x_20 = lean_ctor_get(x_9, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
x_22 = lean_ctor_get_uint8(x_9, sizeof(void*)*3);
x_23 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 1);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 lean_ctor_release(x_9, 2);
 x_24 = x_9;
} else {
 lean_dec_ref(x_9);
 x_24 = lean_box(0);
}
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_nat_dec_eq(x_21, x_58);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_nat_sub(x_5, x_6);
x_61 = lean_nat_dec_lt(x_60, x_5);
lean_dec(x_5);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_60);
x_62 = l___private_Init_Util_0__outOfBounds___rarg(x_8);
x_25 = x_62;
goto block_57;
}
else
{
lean_object* x_63; 
x_63 = lean_array_fget(x_2, x_60);
lean_dec(x_60);
x_25 = x_63;
goto block_57;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_5);
x_64 = l_Array_reverse___rarg(x_4);
x_65 = l_Array_append___rarg(x_2, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_3);
return x_66;
}
block_57:
{
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 2);
lean_inc(x_26);
if (lean_obj_tag(x_26) == 3)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_nat_dec_eq(x_27, x_20);
lean_dec(x_27);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_20);
x_31 = l_Array_reverse___rarg(x_4);
x_32 = l_Array_append___rarg(x_2, x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_3);
return x_33;
}
else
{
uint8_t x_34; 
x_34 = lean_nat_dec_eq(x_1, x_29);
lean_dec(x_29);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_28);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_20);
x_35 = l_Array_reverse___rarg(x_4);
x_36 = l_Array_append___rarg(x_2, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_3);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_38 = lean_array_pop(x_2);
x_39 = lean_array_pop(x_38);
lean_inc(x_20);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_20);
x_41 = lean_array_set(x_3, x_28, x_40);
lean_dec(x_28);
x_42 = lean_array_push(x_4, x_25);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_dec_eq(x_21, x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_nat_sub(x_21, x_43);
lean_dec(x_21);
x_46 = lean_box(13);
if (lean_is_scalar(x_24)) {
 x_47 = lean_alloc_ctor(6, 3, 2);
} else {
 x_47 = x_24;
}
lean_ctor_set(x_47, 0, x_20);
lean_ctor_set(x_47, 1, x_45);
lean_ctor_set(x_47, 2, x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*3, x_22);
lean_ctor_set_uint8(x_47, sizeof(void*)*3 + 1, x_23);
x_48 = lean_array_push(x_42, x_47);
x_2 = x_39;
x_3 = x_41;
x_4 = x_48;
goto _start;
}
else
{
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_20);
x_2 = x_39;
x_3 = x_41;
x_4 = x_42;
goto _start;
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_20);
x_51 = l_Array_reverse___rarg(x_4);
x_52 = l_Array_append___rarg(x_2, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_3);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_20);
x_54 = l_Array_reverse___rarg(x_4);
x_55 = l_Array_append___rarg(x_2, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_3);
return x_56;
}
}
}
default: 
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_9);
lean_dec(x_5);
x_67 = l_Array_reverse___rarg(x_4);
x_68 = l_Array_append___rarg(x_2, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_3);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_5);
x_70 = l_Array_reverse___rarg(x_4);
x_71 = l_Array_append___rarg(x_2, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_3);
return x_72;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ExpandResetReuse_eraseProjIncForAux(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_IR_ExpandResetReuse_eraseProjIncFor___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncFor(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_box(0);
x_5 = lean_mk_array(x_1, x_4);
x_6 = l_Lean_IR_ExpandResetReuse_eraseProjIncFor___closed__1;
x_7 = l_Lean_IR_ExpandResetReuse_eraseProjIncForAux(x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncFor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ExpandResetReuse_eraseProjIncFor(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_reuseToCtor___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_6, 1);
x_13 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_12);
lean_ctor_set(x_6, 1, x_13);
x_14 = lean_array_uset(x_8, x_3, x_6);
x_3 = x_10;
x_4 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_6, 0);
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_6);
x_18 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_array_uset(x_8, x_3, x_19);
x_3 = x_10;
x_4 = x_20;
goto _start;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_6);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_6, 0);
x_24 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_23);
lean_ctor_set(x_6, 0, x_24);
x_25 = lean_array_uset(x_8, x_3, x_6);
x_3 = x_10;
x_4 = x_25;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_6, 0);
lean_inc(x_27);
lean_dec(x_6);
x_28 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_27);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_array_uset(x_8, x_3, x_29);
x_3 = x_10;
x_4 = x_30;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_reuseToCtor(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
if (lean_obj_tag(x_3) == 2)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_2, 3);
x_6 = lean_ctor_get(x_2, 2);
lean_dec(x_6);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 2);
lean_inc(x_9);
x_10 = lean_nat_dec_eq(x_1, x_7);
lean_dec(x_7);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_9);
lean_dec(x_8);
x_11 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_5);
lean_ctor_set(x_2, 3, x_11);
return x_2;
}
else
{
lean_object* x_12; 
lean_dec(x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_2, 2, x_12);
return x_2;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_2, 3);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 2);
lean_inc(x_18);
x_19 = lean_nat_dec_eq(x_1, x_16);
lean_dec(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_18);
lean_dec(x_17);
x_20 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_15);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_14);
lean_ctor_set(x_21, 2, x_3);
lean_ctor_set(x_21, 3, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_3);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_18);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_13);
lean_ctor_set(x_23, 1, x_14);
lean_ctor_set(x_23, 2, x_22);
lean_ctor_set(x_23, 3, x_15);
return x_23;
}
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_2);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_2, 3);
x_26 = lean_ctor_get(x_2, 2);
lean_dec(x_26);
x_27 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_25);
lean_ctor_set(x_2, 3, x_27);
return x_2;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_2, 0);
x_29 = lean_ctor_get(x_2, 1);
x_30 = lean_ctor_get(x_2, 3);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_2);
x_31 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_30);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_29);
lean_ctor_set(x_32, 2, x_3);
lean_ctor_set(x_32, 3, x_31);
return x_32;
}
}
}
case 7:
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_2);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_2, 0);
x_35 = lean_ctor_get(x_2, 1);
x_36 = lean_ctor_get(x_2, 2);
x_37 = lean_nat_dec_eq(x_1, x_34);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_36);
lean_ctor_set(x_2, 2, x_38);
return x_2;
}
else
{
lean_free_object(x_2);
lean_dec(x_35);
lean_dec(x_34);
return x_36;
}
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_42; lean_object* x_43; uint8_t x_44; 
x_39 = lean_ctor_get(x_2, 0);
x_40 = lean_ctor_get(x_2, 1);
x_41 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_42 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 1);
x_43 = lean_ctor_get(x_2, 2);
lean_inc(x_43);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_2);
x_44 = lean_nat_dec_eq(x_1, x_39);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_43);
x_46 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_46, 0, x_39);
lean_ctor_set(x_46, 1, x_40);
lean_ctor_set(x_46, 2, x_45);
lean_ctor_set_uint8(x_46, sizeof(void*)*3, x_41);
lean_ctor_set_uint8(x_46, sizeof(void*)*3 + 1, x_42);
return x_46;
}
else
{
lean_dec(x_40);
lean_dec(x_39);
return x_43;
}
}
}
case 10:
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_2);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; size_t x_50; size_t x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_2, 3);
x_49 = lean_array_get_size(x_48);
x_50 = lean_usize_of_nat(x_49);
lean_dec(x_49);
x_51 = 0;
x_52 = l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_reuseToCtor___spec__1(x_1, x_50, x_51, x_48);
lean_ctor_set(x_2, 3, x_52);
return x_2;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; size_t x_58; size_t x_59; lean_object* x_60; lean_object* x_61; 
x_53 = lean_ctor_get(x_2, 0);
x_54 = lean_ctor_get(x_2, 1);
x_55 = lean_ctor_get(x_2, 2);
x_56 = lean_ctor_get(x_2, 3);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_2);
x_57 = lean_array_get_size(x_56);
x_58 = lean_usize_of_nat(x_57);
lean_dec(x_57);
x_59 = 0;
x_60 = l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_reuseToCtor___spec__1(x_1, x_58, x_59, x_56);
x_61 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_61, 0, x_53);
lean_ctor_set(x_61, 1, x_54);
lean_ctor_set(x_61, 2, x_55);
lean_ctor_set(x_61, 3, x_60);
return x_61;
}
}
default: 
{
uint8_t x_62; 
x_62 = l_Lean_IR_FnBody_isTerminal(x_2);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = l_Lean_IR_FnBody_body(x_2);
x_64 = lean_box(13);
x_65 = l_Lean_IR_FnBody_setBody(x_2, x_64);
x_66 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_63);
x_67 = l_Lean_IR_FnBody_setBody(x_65, x_66);
return x_67;
}
else
{
return x_2;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_reuseToCtor___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_reuseToCtor___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_reuseToCtor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_ExpandResetReuse_mkSlowPath___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
if (lean_obj_tag(x_6) == 0)
{
x_2 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_unsigned_to_nat(1u);
x_12 = 1;
x_13 = 0;
x_14 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_4);
lean_ctor_set_uint8(x_14, sizeof(void*)*3, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*3 + 1, x_13);
x_2 = x_8;
x_4 = x_14;
goto _start;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkSlowPath(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_5 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_4);
lean_dec(x_1);
x_6 = lean_unsigned_to_nat(1u);
x_7 = 1;
x_8 = 0;
x_9 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_5);
lean_ctor_set_uint8(x_9, sizeof(void*)*3, x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*3 + 1, x_8);
x_10 = lean_array_get_size(x_3);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_lt(x_11, x_10);
if (x_12 == 0)
{
lean_dec(x_10);
lean_dec(x_3);
return x_9;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_10, x_10);
if (x_13 == 0)
{
lean_dec(x_10);
lean_dec(x_3);
return x_9;
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_16 = l_Array_foldlMUnsafe_fold___at_Lean_IR_ExpandResetReuse_mkSlowPath___spec__1(x_3, x_14, x_15, x_9);
lean_dec(x_3);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_ExpandResetReuse_mkSlowPath___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_IR_ExpandResetReuse_mkSlowPath___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkFresh___rarg(lean_object* x_1) {
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
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkFresh(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_IR_ExpandResetReuse_mkFresh___rarg), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkFresh___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_ExpandResetReuse_mkFresh(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lean_IR_ExpandResetReuse_releaseUnreadFields___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_releaseUnreadFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_get_size(x_2);
lean_inc(x_6);
x_7 = l_Nat_foldM_loop___at_Lean_IR_ExpandResetReuse_releaseUnreadFields___spec__1(x_1, x_2, x_6, x_6, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lean_IR_ExpandResetReuse_releaseUnreadFields___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_foldM_loop___at_Lean_IR_ExpandResetReuse_releaseUnreadFields___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_releaseUnreadFields___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ExpandResetReuse_releaseUnreadFields(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_Lean_IR_ExpandResetReuse_setFields___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_4, x_8);
lean_dec(x_4);
x_10 = lean_nat_add(x_9, x_8);
x_11 = lean_nat_sub(x_3, x_10);
lean_dec(x_10);
x_12 = l_Lean_IR_instInhabitedArg;
x_13 = lean_array_get(x_12, x_2, x_11);
lean_inc(x_1);
x_14 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set(x_14, 3, x_5);
x_4 = x_9;
x_5 = x_14;
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
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_setFields(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_array_get_size(x_2);
lean_inc(x_4);
x_5 = l_Nat_foldTR_loop___at_Lean_IR_ExpandResetReuse_setFields___spec__1(x_1, x_2, x_4, x_4, x_3);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_Lean_IR_ExpandResetReuse_setFields___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_foldTR_loop___at_Lean_IR_ExpandResetReuse_setFields___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_setFields___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ExpandResetReuse_setFields(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__2(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_HashMapImp_find_x3f___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; size_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_uint64_of_nat(x_2);
x_6 = lean_hashmap_mk_idx(x_4, x_5);
x_7 = lean_array_uget(x_3, x_6);
lean_dec(x_3);
x_8 = l_Lean_AssocList_find_x3f___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__2(x_2, x_7);
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_ExpandResetReuse_isSelfSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l_Lean_HashMapImp_find_x3f___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__1(x_1, x_5);
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
lean_dec(x_1);
x_15 = 0;
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_find_x3f___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_AssocList_find_x3f___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_isSelfSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Lean_IR_ExpandResetReuse_isSelfSet(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_ExpandResetReuse_isSelfUSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_HashMapImp_find_x3f___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__1(x_1, x_4);
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
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_isSelfUSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = l_Lean_IR_ExpandResetReuse_isSelfUSet(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_ExpandResetReuse_isSelfSSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_HashMapImp_find_x3f___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__1(x_1, x_5);
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
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_isSelfSSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Lean_IR_ExpandResetReuse_isSelfSSet(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_removeSelfSet___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_4, x_3, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_6, 1);
lean_inc(x_1);
x_13 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_12);
lean_ctor_set(x_6, 1, x_13);
x_14 = lean_array_uset(x_8, x_3, x_6);
x_3 = x_10;
x_4 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_6, 0);
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_6);
lean_inc(x_1);
x_18 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_array_uset(x_8, x_3, x_19);
x_3 = x_10;
x_4 = x_20;
goto _start;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_6);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_6, 0);
lean_inc(x_1);
x_24 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_23);
lean_ctor_set(x_6, 0, x_24);
x_25 = lean_array_uset(x_8, x_3, x_6);
x_3 = x_10;
x_4 = x_25;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_6, 0);
lean_inc(x_27);
lean_dec(x_6);
lean_inc(x_1);
x_28 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_27);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_array_uset(x_8, x_3, x_29);
x_3 = x_10;
x_4 = x_30;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_removeSelfSet(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
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
lean_inc(x_6);
lean_inc(x_1);
x_8 = l_Lean_IR_ExpandResetReuse_isSelfSet(x_1, x_4, x_5, x_6);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_7);
lean_ctor_set(x_2, 3, x_9);
return x_2;
}
else
{
lean_free_object(x_2);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_2 = x_7;
goto _start;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_ctor_get(x_2, 2);
x_14 = lean_ctor_get(x_2, 3);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
lean_inc(x_13);
lean_inc(x_1);
x_15 = l_Lean_IR_ExpandResetReuse_isSelfSet(x_1, x_11, x_12, x_13);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_14);
x_17 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_12);
lean_ctor_set(x_17, 2, x_13);
lean_ctor_set(x_17, 3, x_16);
return x_17;
}
else
{
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_2 = x_14;
goto _start;
}
}
}
case 4:
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_2);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_ctor_get(x_2, 2);
x_23 = lean_ctor_get(x_2, 3);
lean_inc(x_22);
lean_inc(x_1);
x_24 = l_Lean_IR_ExpandResetReuse_isSelfUSet(x_1, x_20, x_21, x_22);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_23);
lean_ctor_set(x_2, 3, x_25);
return x_2;
}
else
{
lean_free_object(x_2);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
x_2 = x_23;
goto _start;
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
lean_inc(x_29);
lean_inc(x_1);
x_31 = l_Lean_IR_ExpandResetReuse_isSelfUSet(x_1, x_27, x_28, x_29);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_30);
x_33 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_33, 0, x_27);
lean_ctor_set(x_33, 1, x_28);
lean_ctor_set(x_33, 2, x_29);
lean_ctor_set(x_33, 3, x_32);
return x_33;
}
else
{
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
x_2 = x_30;
goto _start;
}
}
}
case 5:
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_2);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_36 = lean_ctor_get(x_2, 0);
x_37 = lean_ctor_get(x_2, 1);
x_38 = lean_ctor_get(x_2, 2);
x_39 = lean_ctor_get(x_2, 3);
x_40 = lean_ctor_get(x_2, 4);
x_41 = lean_ctor_get(x_2, 5);
lean_inc(x_39);
lean_inc(x_1);
x_42 = l_Lean_IR_ExpandResetReuse_isSelfSSet(x_1, x_36, x_37, x_38, x_39);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_41);
lean_ctor_set(x_2, 5, x_43);
return x_2;
}
else
{
lean_free_object(x_2);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
x_2 = x_41;
goto _start;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_45 = lean_ctor_get(x_2, 0);
x_46 = lean_ctor_get(x_2, 1);
x_47 = lean_ctor_get(x_2, 2);
x_48 = lean_ctor_get(x_2, 3);
x_49 = lean_ctor_get(x_2, 4);
x_50 = lean_ctor_get(x_2, 5);
lean_inc(x_50);
lean_inc(x_49);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_2);
lean_inc(x_48);
lean_inc(x_1);
x_51 = l_Lean_IR_ExpandResetReuse_isSelfSSet(x_1, x_45, x_46, x_47, x_48);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_50);
x_53 = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(x_53, 0, x_45);
lean_ctor_set(x_53, 1, x_46);
lean_ctor_set(x_53, 2, x_47);
lean_ctor_set(x_53, 3, x_48);
lean_ctor_set(x_53, 4, x_49);
lean_ctor_set(x_53, 5, x_52);
return x_53;
}
else
{
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
x_2 = x_50;
goto _start;
}
}
}
case 10:
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_2);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; size_t x_58; size_t x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_2, 3);
x_57 = lean_array_get_size(x_56);
x_58 = lean_usize_of_nat(x_57);
lean_dec(x_57);
x_59 = 0;
x_60 = l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_removeSelfSet___spec__1(x_1, x_58, x_59, x_56);
lean_ctor_set(x_2, 3, x_60);
return x_2;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; size_t x_66; size_t x_67; lean_object* x_68; lean_object* x_69; 
x_61 = lean_ctor_get(x_2, 0);
x_62 = lean_ctor_get(x_2, 1);
x_63 = lean_ctor_get(x_2, 2);
x_64 = lean_ctor_get(x_2, 3);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_2);
x_65 = lean_array_get_size(x_64);
x_66 = lean_usize_of_nat(x_65);
lean_dec(x_65);
x_67 = 0;
x_68 = l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_removeSelfSet___spec__1(x_1, x_66, x_67, x_64);
x_69 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_69, 0, x_61);
lean_ctor_set(x_69, 1, x_62);
lean_ctor_set(x_69, 2, x_63);
lean_ctor_set(x_69, 3, x_68);
return x_69;
}
}
default: 
{
uint8_t x_70; 
x_70 = l_Lean_IR_FnBody_isTerminal(x_2);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = l_Lean_IR_FnBody_body(x_2);
x_72 = lean_box(13);
x_73 = l_Lean_IR_FnBody_setBody(x_2, x_72);
x_74 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_71);
x_75 = l_Lean_IR_FnBody_setBody(x_73, x_74);
return x_75;
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_removeSelfSet___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_removeSelfSet___spec__1(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_reuseToSet___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_5, x_4);
if (x_7 == 0)
{
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_8 = lean_array_uget(x_6, x_5);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_uset(x_6, x_5, x_9);
x_11 = 1;
x_12 = lean_usize_add(x_5, x_11);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_3);
lean_inc(x_1);
x_15 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_14);
lean_ctor_set(x_8, 1, x_15);
x_16 = lean_array_uset(x_10, x_5, x_8);
x_5 = x_12;
x_6 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_8, 0);
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_8);
lean_inc(x_3);
lean_inc(x_1);
x_20 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_array_uset(x_10, x_5, x_21);
x_5 = x_12;
x_6 = x_22;
goto _start;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_8);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_8, 0);
lean_inc(x_3);
lean_inc(x_1);
x_26 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_25);
lean_ctor_set(x_8, 0, x_26);
x_27 = lean_array_uset(x_10, x_5, x_8);
x_5 = x_12;
x_6 = x_27;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_8, 0);
lean_inc(x_29);
lean_dec(x_8);
lean_inc(x_3);
lean_inc(x_1);
x_30 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_29);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_array_uset(x_10, x_5, x_31);
x_5 = x_12;
x_6 = x_32;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_reuseToSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_4, 2);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 2)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; uint8_t x_15; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_ctor_get(x_4, 3);
x_10 = lean_ctor_get(x_4, 2);
lean_dec(x_10);
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
x_14 = lean_ctor_get(x_5, 2);
lean_inc(x_14);
x_15 = lean_nat_dec_eq(x_2, x_11);
lean_dec(x_11);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_dec(x_12);
x_16 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_9);
lean_ctor_set(x_4, 3, x_16);
return x_4;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_free_object(x_4);
lean_dec(x_8);
lean_dec(x_5);
lean_inc(x_3);
x_17 = l_Lean_IR_FnBody_replaceVar(x_7, x_3, x_9);
lean_inc(x_3);
x_18 = l_Lean_IR_ExpandResetReuse_setFields(x_3, x_14, x_17);
lean_dec(x_14);
if (x_13 == 0)
{
lean_object* x_19; 
lean_dec(x_12);
lean_dec(x_3);
x_19 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_21, 0, x_3);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_18);
x_22 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; uint8_t x_30; 
x_23 = lean_ctor_get(x_4, 0);
x_24 = lean_ctor_get(x_4, 1);
x_25 = lean_ctor_get(x_4, 3);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_4);
x_26 = lean_ctor_get(x_5, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_5, 1);
lean_inc(x_27);
x_28 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
x_29 = lean_ctor_get(x_5, 2);
lean_inc(x_29);
x_30 = lean_nat_dec_eq(x_2, x_26);
lean_dec(x_26);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_29);
lean_dec(x_27);
x_31 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_25);
x_32 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_32, 0, x_23);
lean_ctor_set(x_32, 1, x_24);
lean_ctor_set(x_32, 2, x_5);
lean_ctor_set(x_32, 3, x_31);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_24);
lean_dec(x_5);
lean_inc(x_3);
x_33 = l_Lean_IR_FnBody_replaceVar(x_23, x_3, x_25);
lean_inc(x_3);
x_34 = l_Lean_IR_ExpandResetReuse_setFields(x_3, x_29, x_33);
lean_dec(x_29);
if (x_28 == 0)
{
lean_object* x_35; 
lean_dec(x_27);
lean_dec(x_3);
x_35 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_34);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_27, 1);
lean_inc(x_36);
lean_dec(x_27);
x_37 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_37, 0, x_3);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_37, 2, x_34);
x_38 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_37);
return x_38;
}
}
}
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_4);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_4, 3);
x_41 = lean_ctor_get(x_4, 2);
lean_dec(x_41);
x_42 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_40);
lean_ctor_set(x_4, 3, x_42);
return x_4;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_4, 0);
x_44 = lean_ctor_get(x_4, 1);
x_45 = lean_ctor_get(x_4, 3);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_4);
x_46 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_45);
x_47 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set(x_47, 1, x_44);
lean_ctor_set(x_47, 2, x_5);
lean_ctor_set(x_47, 3, x_46);
return x_47;
}
}
}
case 7:
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_4);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_4, 0);
x_50 = lean_ctor_get(x_4, 1);
x_51 = lean_ctor_get(x_4, 2);
x_52 = lean_nat_dec_eq(x_2, x_49);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_51);
lean_ctor_set(x_4, 2, x_53);
return x_4;
}
else
{
lean_object* x_54; 
lean_free_object(x_4);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_1);
x_54 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_54, 0, x_3);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_58; lean_object* x_59; uint8_t x_60; 
x_55 = lean_ctor_get(x_4, 0);
x_56 = lean_ctor_get(x_4, 1);
x_57 = lean_ctor_get_uint8(x_4, sizeof(void*)*3);
x_58 = lean_ctor_get_uint8(x_4, sizeof(void*)*3 + 1);
x_59 = lean_ctor_get(x_4, 2);
lean_inc(x_59);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_4);
x_60 = lean_nat_dec_eq(x_2, x_55);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_59);
x_62 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_62, 0, x_55);
lean_ctor_set(x_62, 1, x_56);
lean_ctor_set(x_62, 2, x_61);
lean_ctor_set_uint8(x_62, sizeof(void*)*3, x_57);
lean_ctor_set_uint8(x_62, sizeof(void*)*3 + 1, x_58);
return x_62;
}
else
{
lean_object* x_63; 
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_1);
x_63 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_63, 0, x_3);
lean_ctor_set(x_63, 1, x_59);
return x_63;
}
}
}
case 10:
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_4);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; size_t x_67; size_t x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_4, 3);
x_66 = lean_array_get_size(x_65);
x_67 = lean_usize_of_nat(x_66);
lean_dec(x_66);
x_68 = 0;
x_69 = l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_reuseToSet___spec__1(x_1, x_2, x_3, x_67, x_68, x_65);
lean_ctor_set(x_4, 3, x_69);
return x_4;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; size_t x_75; size_t x_76; lean_object* x_77; lean_object* x_78; 
x_70 = lean_ctor_get(x_4, 0);
x_71 = lean_ctor_get(x_4, 1);
x_72 = lean_ctor_get(x_4, 2);
x_73 = lean_ctor_get(x_4, 3);
lean_inc(x_73);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_4);
x_74 = lean_array_get_size(x_73);
x_75 = lean_usize_of_nat(x_74);
lean_dec(x_74);
x_76 = 0;
x_77 = l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_reuseToSet___spec__1(x_1, x_2, x_3, x_75, x_76, x_73);
x_78 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_78, 0, x_70);
lean_ctor_set(x_78, 1, x_71);
lean_ctor_set(x_78, 2, x_72);
lean_ctor_set(x_78, 3, x_77);
return x_78;
}
}
default: 
{
uint8_t x_79; 
x_79 = l_Lean_IR_FnBody_isTerminal(x_4);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = l_Lean_IR_FnBody_body(x_4);
x_81 = lean_box(13);
x_82 = l_Lean_IR_FnBody_setBody(x_4, x_81);
x_83 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_80);
x_84 = l_Lean_IR_FnBody_setBody(x_82, x_83);
return x_84;
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_reuseToSet___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_reuseToSet___spec__1(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_reuseToSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkFastPath(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_2);
lean_inc(x_5);
x_7 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_5, x_1, x_2, x_4);
x_8 = l_Lean_IR_ExpandResetReuse_releaseUnreadFields(x_2, x_3, x_7, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkFastPath___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_ExpandResetReuse_mkFastPath(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_expand(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_inc(x_11);
lean_inc(x_5);
lean_inc(x_3);
x_12 = l_Lean_IR_ExpandResetReuse_mkSlowPath(x_3, x_5, x_11, x_6);
lean_inc(x_7);
lean_inc(x_5);
x_13 = l_Lean_IR_ExpandResetReuse_mkFastPath(x_3, x_5, x_11, x_6, x_7, x_8);
lean_dec(x_11);
lean_dec(x_3);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_IR_ExpandResetReuse_eraseProjIncFor___closed__1;
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_searchAndExpand___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_2, x_1);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_5);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_array_uget(x_3, x_2);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_uset(x_3, x_2, x_9);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_8, 1);
x_13 = l_Lean_IR_ExpandResetReuse_eraseProjIncFor___closed__1;
lean_inc(x_4);
x_14 = l_Lean_IR_ExpandResetReuse_searchAndExpand(x_12, x_13, x_4, x_5);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_ctor_set(x_8, 1, x_15);
x_17 = 1;
x_18 = lean_usize_add(x_2, x_17);
x_19 = lean_array_uset(x_10, x_2, x_8);
x_2 = x_18;
x_3 = x_19;
x_5 = x_16;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_8, 0);
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_8);
x_23 = l_Lean_IR_ExpandResetReuse_eraseProjIncFor___closed__1;
lean_inc(x_4);
x_24 = l_Lean_IR_ExpandResetReuse_searchAndExpand(x_22, x_23, x_4, x_5);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_25);
x_28 = 1;
x_29 = lean_usize_add(x_2, x_28);
x_30 = lean_array_uset(x_10, x_2, x_27);
x_2 = x_29;
x_3 = x_30;
x_5 = x_26;
goto _start;
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_8);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; lean_object* x_40; 
x_33 = lean_ctor_get(x_8, 0);
x_34 = l_Lean_IR_ExpandResetReuse_eraseProjIncFor___closed__1;
lean_inc(x_4);
x_35 = l_Lean_IR_ExpandResetReuse_searchAndExpand(x_33, x_34, x_4, x_5);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_ctor_set(x_8, 0, x_36);
x_38 = 1;
x_39 = lean_usize_add(x_2, x_38);
x_40 = lean_array_uset(x_10, x_2, x_8);
x_2 = x_39;
x_3 = x_40;
x_5 = x_37;
goto _start;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; size_t x_48; size_t x_49; lean_object* x_50; 
x_42 = lean_ctor_get(x_8, 0);
lean_inc(x_42);
lean_dec(x_8);
x_43 = l_Lean_IR_ExpandResetReuse_eraseProjIncFor___closed__1;
lean_inc(x_4);
x_44 = l_Lean_IR_ExpandResetReuse_searchAndExpand(x_42, x_43, x_4, x_5);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_45);
x_48 = 1;
x_49 = lean_usize_add(x_2, x_48);
x_50 = lean_array_uset(x_10, x_2, x_47);
x_2 = x_49;
x_3 = x_50;
x_5 = x_46;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_IR_ExpandResetReuse_searchAndExpand___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_IR_ExpandResetReuse_searchAndExpand), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_searchAndExpand(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
lean_inc(x_7);
x_10 = l_Lean_IR_ExpandResetReuse_consumed(x_6, x_7);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_11 = l_Lean_IR_push(x_2, x_1);
x_1 = x_7;
x_2 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_13 = l_Lean_IR_ExpandResetReuse_searchAndExpand___closed__1;
x_14 = l_Lean_IR_ExpandResetReuse_expand(x_13, x_2, x_6, x_8, x_9, x_7, x_3, x_4);
return x_14;
}
}
else
{
uint8_t x_15; 
lean_dec(x_5);
x_15 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Lean_IR_FnBody_body(x_1);
x_17 = l_Lean_IR_push(x_2, x_1);
x_1 = x_16;
x_2 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_3);
x_19 = l_Lean_IR_reshape(x_2, x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_4);
return x_20;
}
}
}
case 1:
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_1);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_1, 2);
x_23 = lean_ctor_get(x_1, 3);
x_24 = l_Lean_IR_ExpandResetReuse_eraseProjIncFor___closed__1;
lean_inc(x_3);
x_25 = l_Lean_IR_ExpandResetReuse_searchAndExpand(x_22, x_24, x_3, x_4);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_box(13);
lean_ctor_set(x_1, 3, x_28);
lean_ctor_set(x_1, 2, x_26);
x_29 = l_Lean_IR_push(x_2, x_1);
x_1 = x_23;
x_2 = x_29;
x_4 = x_27;
goto _start;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_31 = lean_ctor_get(x_1, 0);
x_32 = lean_ctor_get(x_1, 1);
x_33 = lean_ctor_get(x_1, 2);
x_34 = lean_ctor_get(x_1, 3);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_1);
x_35 = l_Lean_IR_ExpandResetReuse_eraseProjIncFor___closed__1;
lean_inc(x_3);
x_36 = l_Lean_IR_ExpandResetReuse_searchAndExpand(x_33, x_35, x_3, x_4);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_box(13);
x_40 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_40, 0, x_31);
lean_ctor_set(x_40, 1, x_32);
lean_ctor_set(x_40, 2, x_37);
lean_ctor_set(x_40, 3, x_39);
x_41 = l_Lean_IR_push(x_2, x_40);
x_1 = x_34;
x_2 = x_41;
x_4 = x_38;
goto _start;
}
}
case 10:
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_1);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; lean_object* x_48; uint8_t x_49; 
x_44 = lean_ctor_get(x_1, 3);
x_45 = lean_array_get_size(x_44);
x_46 = lean_usize_of_nat(x_45);
lean_dec(x_45);
x_47 = 0;
x_48 = l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_searchAndExpand___spec__1(x_46, x_47, x_44, x_3, x_4);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_48, 0);
lean_ctor_set(x_1, 3, x_50);
x_51 = l_Lean_IR_reshape(x_2, x_1);
lean_ctor_set(x_48, 0, x_51);
return x_48;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_48, 0);
x_53 = lean_ctor_get(x_48, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_48);
lean_ctor_set(x_1, 3, x_52);
x_54 = l_Lean_IR_reshape(x_2, x_1);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; size_t x_61; size_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_56 = lean_ctor_get(x_1, 0);
x_57 = lean_ctor_get(x_1, 1);
x_58 = lean_ctor_get(x_1, 2);
x_59 = lean_ctor_get(x_1, 3);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_1);
x_60 = lean_array_get_size(x_59);
x_61 = lean_usize_of_nat(x_60);
lean_dec(x_60);
x_62 = 0;
x_63 = l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_searchAndExpand___spec__1(x_61, x_62, x_59, x_3, x_4);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_66 = x_63;
} else {
 lean_dec_ref(x_63);
 x_66 = lean_box(0);
}
x_67 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_67, 0, x_56);
lean_ctor_set(x_67, 1, x_57);
lean_ctor_set(x_67, 2, x_58);
lean_ctor_set(x_67, 3, x_64);
x_68 = l_Lean_IR_reshape(x_2, x_67);
if (lean_is_scalar(x_66)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_66;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_65);
return x_69;
}
}
default: 
{
uint8_t x_70; 
x_70 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = l_Lean_IR_FnBody_body(x_1);
x_72 = l_Lean_IR_push(x_2, x_1);
x_1 = x_71;
x_2 = x_72;
goto _start;
}
else
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_3);
x_74 = l_Lean_IR_reshape(x_2, x_1);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_4);
return x_75;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_searchAndExpand___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_searchAndExpand___spec__1(x_6, x_7, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_main(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
lean_inc(x_1);
x_3 = l_Lean_IR_ExpandResetReuse_mkProjMap(x_1);
x_4 = lean_unsigned_to_nat(0u);
lean_inc(x_1);
x_5 = l_Lean_IR_MaxIndex_collectDecl(x_1, x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_5, x_6);
lean_dec(x_5);
x_8 = l_Lean_IR_ExpandResetReuse_eraseProjIncFor___closed__1;
x_9 = l_Lean_IR_ExpandResetReuse_searchAndExpand(x_2, x_8, x_3, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_IR_Decl_updateBody_x21(x_1, x_10);
return x_11;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_Decl_expandResetReuse(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_IR_ExpandResetReuse_main(x_1);
x_3 = l_Lean_IR_Decl_normalizeIds(x_2);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_NormIds(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_FreeVars(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_ExpandResetReuse(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_NormIds(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_FreeVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_ExpandResetReuse_eraseProjIncFor___closed__1 = _init_l_Lean_IR_ExpandResetReuse_eraseProjIncFor___closed__1();
lean_mark_persistent(l_Lean_IR_ExpandResetReuse_eraseProjIncFor___closed__1);
l_Lean_IR_ExpandResetReuse_searchAndExpand___closed__1 = _init_l_Lean_IR_ExpandResetReuse_searchAndExpand___closed__1();
lean_mark_persistent(l_Lean_IR_ExpandResetReuse_searchAndExpand___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
