// Lean compiler output
// Module: Lean.Compiler.IR.ExpandResetReuse
// Imports: Lean.Compiler.IR.CompilerM Lean.Compiler.IR.NormIds Lean.Compiler.IR.FreeVars
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
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncFor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_Lean_IR_ExpandResetReuse_setFields___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncForAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkSlowPath___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncFor___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_reuseToCtor___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_isSelfSSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_releaseUnreadFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_IR_push(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_removeSelfSet___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_expand___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_removeSelfSet(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lean_IR_ExpandResetReuse_releaseUnreadFields___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_removeSelfSet___spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_IR_FnBody_isTerminal(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_reuseToCtor(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_reuseToSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedFnBody;
lean_object* l_Lean_IR_FnBody_replaceVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_Decl_expandResetReuse(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_setFields(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkSlowPath(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkProjMap(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_Lean_IR_ExpandResetReuse_setFields___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_searchAndExpand___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__1___boxed(lean_object*, lean_object*);
lean_object* l_Array_reverse___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_searchAndExpand(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkFresh(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_reuseToSet(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkFresh___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncFor___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_body(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkFastPath(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_ExpandResetReuse_consumed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_reuseToCtor___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_main(lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_ExpandResetReuse_isSelfSet(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExpandResetReuse_mkProjMap___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_IR_ExpandResetReuse_consumed___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_reuseToSet___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_IR_mkIf(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_consumed___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExpandResetReuse_mkProjMap___closed__2;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_IR_FnBody_setBody(lean_object*, lean_object*);
lean_object* l_Lean_IR_Decl_updateBody_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__3(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkFastPath___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_removeSelfSet___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__4___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_releaseUnreadFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_ExpandResetReuse_isSelfSSet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_ExpandResetReuse_mkSlowPath___spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Lean_IR_AltCore_body(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Array_back_x21___rarg(lean_object*, lean_object*);
lean_object* l_Lean_IR_MaxIndex_collectDecl(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_ExpandResetReuse_isSelfUSet(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExpandResetReuse_mkProjMap___closed__1;
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_reuseToCtor___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_eraseProjIncForAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_searchAndExpand___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_setFields___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_isSelfUSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_IR_ExpandResetReuse_searchAndExpand___closed__1;
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lean_IR_ExpandResetReuse_releaseUnreadFields___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_Lean_IR_ExpandResetReuse_consumed___spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_ExpandResetReuse_mkSlowPath___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_reuseToSet___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_IR_reshape(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_IR_Decl_normalizeIds(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_expand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_isSelfSet___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkFresh___rarg(lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 2);
x_7 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_5);
x_8 = lean_apply_1(x_1, x_5);
x_9 = lean_unbox_uint64(x_8);
lean_dec(x_8);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget(x_2, x_20);
lean_ctor_set(x_3, 2, x_21);
x_22 = lean_array_uset(x_2, x_20, x_3);
x_2 = x_22;
x_3 = x_6;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; size_t x_36; size_t x_37; size_t x_38; size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_24 = lean_ctor_get(x_3, 0);
x_25 = lean_ctor_get(x_3, 1);
x_26 = lean_ctor_get(x_3, 2);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_3);
x_27 = lean_array_get_size(x_2);
lean_inc(x_1);
lean_inc(x_24);
x_28 = lean_apply_1(x_1, x_24);
x_29 = lean_unbox_uint64(x_28);
lean_dec(x_28);
x_30 = 32;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = 16;
x_34 = lean_uint64_shift_right(x_32, x_33);
x_35 = lean_uint64_xor(x_32, x_34);
x_36 = lean_uint64_to_usize(x_35);
x_37 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_38 = 1;
x_39 = lean_usize_sub(x_37, x_38);
x_40 = lean_usize_land(x_36, x_39);
x_41 = lean_array_uget(x_2, x_40);
x_42 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_42, 0, x_24);
lean_ctor_set(x_42, 1, x_25);
lean_ctor_set(x_42, 2, x_41);
x_43 = lean_array_uset(x_2, x_40, x_42);
x_2 = x_43;
x_3 = x_26;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__4___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__5(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = lean_uint64_of_nat(x_4);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_1, x_18);
lean_ctor_set(x_2, 2, x_19);
x_20 = lean_array_uset(x_1, x_18, x_2);
x_1 = x_20;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
x_24 = lean_ctor_get(x_2, 2);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
x_25 = lean_array_get_size(x_1);
x_26 = lean_uint64_of_nat(x_22);
x_27 = 32;
x_28 = lean_uint64_shift_right(x_26, x_27);
x_29 = lean_uint64_xor(x_26, x_28);
x_30 = 16;
x_31 = lean_uint64_shift_right(x_29, x_30);
x_32 = lean_uint64_xor(x_29, x_31);
x_33 = lean_uint64_to_usize(x_32);
x_34 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_35 = 1;
x_36 = lean_usize_sub(x_34, x_35);
x_37 = lean_usize_land(x_33, x_36);
x_38 = lean_array_uget(x_1, x_37);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_22);
lean_ctor_set(x_39, 1, x_23);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_array_uset(x_1, x_37, x_39);
x_1 = x_40;
x_2 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__4___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__5(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = lean_mk_array(x_4, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__3(x_7, x_1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_10 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__6(x_1, x_2, x_8);
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
x_15 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__6(x_1, x_2, x_13);
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
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 3:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; uint8_t x_21; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_uint64_of_nat(x_1);
x_9 = 32;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = 16;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = lean_uint64_to_usize(x_14);
x_16 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_17 = 1;
x_18 = lean_usize_sub(x_16, x_17);
x_19 = lean_usize_land(x_15, x_18);
x_20 = lean_array_uget(x_6, x_19);
x_21 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(x_1, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_5, x_22);
lean_dec(x_5);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_2);
lean_ctor_set(x_24, 2, x_20);
x_25 = lean_array_uset(x_6, x_19, x_24);
x_26 = lean_unsigned_to_nat(4u);
x_27 = lean_nat_mul(x_23, x_26);
x_28 = lean_unsigned_to_nat(3u);
x_29 = lean_nat_div(x_27, x_28);
lean_dec(x_27);
x_30 = lean_array_get_size(x_25);
x_31 = lean_nat_dec_le(x_29, x_30);
lean_dec(x_30);
lean_dec(x_29);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__2(x_25);
lean_ctor_set(x_3, 1, x_32);
lean_ctor_set(x_3, 0, x_23);
return x_3;
}
else
{
lean_ctor_set(x_3, 1, x_25);
lean_ctor_set(x_3, 0, x_23);
return x_3;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_box(0);
x_34 = lean_array_uset(x_6, x_19, x_33);
x_35 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__6(x_1, x_2, x_20);
x_36 = lean_array_uset(x_34, x_19, x_35);
lean_ctor_set(x_3, 1, x_36);
return x_3;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint64_t x_40; uint64_t x_41; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; size_t x_47; size_t x_48; size_t x_49; size_t x_50; size_t x_51; lean_object* x_52; uint8_t x_53; 
x_37 = lean_ctor_get(x_3, 0);
x_38 = lean_ctor_get(x_3, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_3);
x_39 = lean_array_get_size(x_38);
x_40 = lean_uint64_of_nat(x_1);
x_41 = 32;
x_42 = lean_uint64_shift_right(x_40, x_41);
x_43 = lean_uint64_xor(x_40, x_42);
x_44 = 16;
x_45 = lean_uint64_shift_right(x_43, x_44);
x_46 = lean_uint64_xor(x_43, x_45);
x_47 = lean_uint64_to_usize(x_46);
x_48 = lean_usize_of_nat(x_39);
lean_dec(x_39);
x_49 = 1;
x_50 = lean_usize_sub(x_48, x_49);
x_51 = lean_usize_land(x_47, x_50);
x_52 = lean_array_uget(x_38, x_51);
x_53 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(x_1, x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_54 = lean_unsigned_to_nat(1u);
x_55 = lean_nat_add(x_37, x_54);
lean_dec(x_37);
x_56 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_2);
lean_ctor_set(x_56, 2, x_52);
x_57 = lean_array_uset(x_38, x_51, x_56);
x_58 = lean_unsigned_to_nat(4u);
x_59 = lean_nat_mul(x_55, x_58);
x_60 = lean_unsigned_to_nat(3u);
x_61 = lean_nat_div(x_59, x_60);
lean_dec(x_59);
x_62 = lean_array_get_size(x_57);
x_63 = lean_nat_dec_le(x_61, x_62);
lean_dec(x_62);
lean_dec(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__2(x_57);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_55);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_55);
lean_ctor_set(x_66, 1, x_57);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_box(0);
x_68 = lean_array_uset(x_38, x_51, x_67);
x_69 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__6(x_1, x_2, x_52);
x_70 = lean_array_uset(x_68, x_51, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_37);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
case 4:
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_3);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint64_t x_76; uint64_t x_77; uint64_t x_78; uint64_t x_79; uint64_t x_80; uint64_t x_81; uint64_t x_82; size_t x_83; size_t x_84; size_t x_85; size_t x_86; size_t x_87; lean_object* x_88; uint8_t x_89; 
x_73 = lean_ctor_get(x_3, 0);
x_74 = lean_ctor_get(x_3, 1);
x_75 = lean_array_get_size(x_74);
x_76 = lean_uint64_of_nat(x_1);
x_77 = 32;
x_78 = lean_uint64_shift_right(x_76, x_77);
x_79 = lean_uint64_xor(x_76, x_78);
x_80 = 16;
x_81 = lean_uint64_shift_right(x_79, x_80);
x_82 = lean_uint64_xor(x_79, x_81);
x_83 = lean_uint64_to_usize(x_82);
x_84 = lean_usize_of_nat(x_75);
lean_dec(x_75);
x_85 = 1;
x_86 = lean_usize_sub(x_84, x_85);
x_87 = lean_usize_land(x_83, x_86);
x_88 = lean_array_uget(x_74, x_87);
x_89 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(x_1, x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_90 = lean_unsigned_to_nat(1u);
x_91 = lean_nat_add(x_73, x_90);
lean_dec(x_73);
x_92 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_92, 0, x_1);
lean_ctor_set(x_92, 1, x_2);
lean_ctor_set(x_92, 2, x_88);
x_93 = lean_array_uset(x_74, x_87, x_92);
x_94 = lean_unsigned_to_nat(4u);
x_95 = lean_nat_mul(x_91, x_94);
x_96 = lean_unsigned_to_nat(3u);
x_97 = lean_nat_div(x_95, x_96);
lean_dec(x_95);
x_98 = lean_array_get_size(x_93);
x_99 = lean_nat_dec_le(x_97, x_98);
lean_dec(x_98);
lean_dec(x_97);
if (x_99 == 0)
{
lean_object* x_100; 
x_100 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__2(x_93);
lean_ctor_set(x_3, 1, x_100);
lean_ctor_set(x_3, 0, x_91);
return x_3;
}
else
{
lean_ctor_set(x_3, 1, x_93);
lean_ctor_set(x_3, 0, x_91);
return x_3;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_box(0);
x_102 = lean_array_uset(x_74, x_87, x_101);
x_103 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__6(x_1, x_2, x_88);
x_104 = lean_array_uset(x_102, x_87, x_103);
lean_ctor_set(x_3, 1, x_104);
return x_3;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; uint64_t x_108; uint64_t x_109; uint64_t x_110; uint64_t x_111; uint64_t x_112; uint64_t x_113; uint64_t x_114; size_t x_115; size_t x_116; size_t x_117; size_t x_118; size_t x_119; lean_object* x_120; uint8_t x_121; 
x_105 = lean_ctor_get(x_3, 0);
x_106 = lean_ctor_get(x_3, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_3);
x_107 = lean_array_get_size(x_106);
x_108 = lean_uint64_of_nat(x_1);
x_109 = 32;
x_110 = lean_uint64_shift_right(x_108, x_109);
x_111 = lean_uint64_xor(x_108, x_110);
x_112 = 16;
x_113 = lean_uint64_shift_right(x_111, x_112);
x_114 = lean_uint64_xor(x_111, x_113);
x_115 = lean_uint64_to_usize(x_114);
x_116 = lean_usize_of_nat(x_107);
lean_dec(x_107);
x_117 = 1;
x_118 = lean_usize_sub(x_116, x_117);
x_119 = lean_usize_land(x_115, x_118);
x_120 = lean_array_uget(x_106, x_119);
x_121 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(x_1, x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_122 = lean_unsigned_to_nat(1u);
x_123 = lean_nat_add(x_105, x_122);
lean_dec(x_105);
x_124 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_124, 0, x_1);
lean_ctor_set(x_124, 1, x_2);
lean_ctor_set(x_124, 2, x_120);
x_125 = lean_array_uset(x_106, x_119, x_124);
x_126 = lean_unsigned_to_nat(4u);
x_127 = lean_nat_mul(x_123, x_126);
x_128 = lean_unsigned_to_nat(3u);
x_129 = lean_nat_div(x_127, x_128);
lean_dec(x_127);
x_130 = lean_array_get_size(x_125);
x_131 = lean_nat_dec_le(x_129, x_130);
lean_dec(x_130);
lean_dec(x_129);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; 
x_132 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__2(x_125);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_123);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
else
{
lean_object* x_134; 
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_123);
lean_ctor_set(x_134, 1, x_125);
return x_134;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_135 = lean_box(0);
x_136 = lean_array_uset(x_106, x_119, x_135);
x_137 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__6(x_1, x_2, x_120);
x_138 = lean_array_uset(x_136, x_119, x_137);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_105);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
case 5:
{
uint8_t x_140; 
x_140 = !lean_is_exclusive(x_3);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; uint64_t x_144; uint64_t x_145; uint64_t x_146; uint64_t x_147; uint64_t x_148; uint64_t x_149; uint64_t x_150; size_t x_151; size_t x_152; size_t x_153; size_t x_154; size_t x_155; lean_object* x_156; uint8_t x_157; 
x_141 = lean_ctor_get(x_3, 0);
x_142 = lean_ctor_get(x_3, 1);
x_143 = lean_array_get_size(x_142);
x_144 = lean_uint64_of_nat(x_1);
x_145 = 32;
x_146 = lean_uint64_shift_right(x_144, x_145);
x_147 = lean_uint64_xor(x_144, x_146);
x_148 = 16;
x_149 = lean_uint64_shift_right(x_147, x_148);
x_150 = lean_uint64_xor(x_147, x_149);
x_151 = lean_uint64_to_usize(x_150);
x_152 = lean_usize_of_nat(x_143);
lean_dec(x_143);
x_153 = 1;
x_154 = lean_usize_sub(x_152, x_153);
x_155 = lean_usize_land(x_151, x_154);
x_156 = lean_array_uget(x_142, x_155);
x_157 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(x_1, x_156);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; 
x_158 = lean_unsigned_to_nat(1u);
x_159 = lean_nat_add(x_141, x_158);
lean_dec(x_141);
x_160 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_160, 0, x_1);
lean_ctor_set(x_160, 1, x_2);
lean_ctor_set(x_160, 2, x_156);
x_161 = lean_array_uset(x_142, x_155, x_160);
x_162 = lean_unsigned_to_nat(4u);
x_163 = lean_nat_mul(x_159, x_162);
x_164 = lean_unsigned_to_nat(3u);
x_165 = lean_nat_div(x_163, x_164);
lean_dec(x_163);
x_166 = lean_array_get_size(x_161);
x_167 = lean_nat_dec_le(x_165, x_166);
lean_dec(x_166);
lean_dec(x_165);
if (x_167 == 0)
{
lean_object* x_168; 
x_168 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__2(x_161);
lean_ctor_set(x_3, 1, x_168);
lean_ctor_set(x_3, 0, x_159);
return x_3;
}
else
{
lean_ctor_set(x_3, 1, x_161);
lean_ctor_set(x_3, 0, x_159);
return x_3;
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_169 = lean_box(0);
x_170 = lean_array_uset(x_142, x_155, x_169);
x_171 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__6(x_1, x_2, x_156);
x_172 = lean_array_uset(x_170, x_155, x_171);
lean_ctor_set(x_3, 1, x_172);
return x_3;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; uint64_t x_176; uint64_t x_177; uint64_t x_178; uint64_t x_179; uint64_t x_180; uint64_t x_181; uint64_t x_182; size_t x_183; size_t x_184; size_t x_185; size_t x_186; size_t x_187; lean_object* x_188; uint8_t x_189; 
x_173 = lean_ctor_get(x_3, 0);
x_174 = lean_ctor_get(x_3, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_3);
x_175 = lean_array_get_size(x_174);
x_176 = lean_uint64_of_nat(x_1);
x_177 = 32;
x_178 = lean_uint64_shift_right(x_176, x_177);
x_179 = lean_uint64_xor(x_176, x_178);
x_180 = 16;
x_181 = lean_uint64_shift_right(x_179, x_180);
x_182 = lean_uint64_xor(x_179, x_181);
x_183 = lean_uint64_to_usize(x_182);
x_184 = lean_usize_of_nat(x_175);
lean_dec(x_175);
x_185 = 1;
x_186 = lean_usize_sub(x_184, x_185);
x_187 = lean_usize_land(x_183, x_186);
x_188 = lean_array_uget(x_174, x_187);
x_189 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(x_1, x_188);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; 
x_190 = lean_unsigned_to_nat(1u);
x_191 = lean_nat_add(x_173, x_190);
lean_dec(x_173);
x_192 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_192, 0, x_1);
lean_ctor_set(x_192, 1, x_2);
lean_ctor_set(x_192, 2, x_188);
x_193 = lean_array_uset(x_174, x_187, x_192);
x_194 = lean_unsigned_to_nat(4u);
x_195 = lean_nat_mul(x_191, x_194);
x_196 = lean_unsigned_to_nat(3u);
x_197 = lean_nat_div(x_195, x_196);
lean_dec(x_195);
x_198 = lean_array_get_size(x_193);
x_199 = lean_nat_dec_le(x_197, x_198);
lean_dec(x_198);
lean_dec(x_197);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; 
x_200 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__2(x_193);
x_201 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_201, 0, x_191);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
else
{
lean_object* x_202; 
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_191);
lean_ctor_set(x_202, 1, x_193);
return x_202;
}
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_203 = lean_box(0);
x_204 = lean_array_uset(x_174, x_187, x_203);
x_205 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__6(x_1, x_2, x_188);
x_206 = lean_array_uset(x_204, x_187, x_205);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_173);
lean_ctor_set(x_207, 1, x_206);
return x_207;
}
}
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(x_1, x_2);
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
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; size_t x_18; size_t x_19; size_t x_20; size_t x_21; size_t x_22; lean_object* x_23; uint8_t x_24; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_array_get_size(x_9);
x_11 = lean_uint64_of_nat(x_3);
x_12 = 32;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = 16;
x_16 = lean_uint64_shift_right(x_14, x_15);
x_17 = lean_uint64_xor(x_14, x_16);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_20 = 1;
x_21 = lean_usize_sub(x_19, x_20);
x_22 = lean_usize_land(x_18, x_21);
x_23 = lean_array_uget(x_9, x_22);
x_24 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(x_3, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_8, x_25);
lean_dec(x_8);
x_27 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_27, 0, x_3);
lean_ctor_set(x_27, 1, x_4);
lean_ctor_set(x_27, 2, x_23);
x_28 = lean_array_uset(x_9, x_22, x_27);
x_29 = lean_unsigned_to_nat(4u);
x_30 = lean_nat_mul(x_26, x_29);
x_31 = lean_unsigned_to_nat(3u);
x_32 = lean_nat_div(x_30, x_31);
lean_dec(x_30);
x_33 = lean_array_get_size(x_28);
x_34 = lean_nat_dec_le(x_32, x_33);
lean_dec(x_33);
lean_dec(x_32);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__2(x_28);
lean_ctor_set(x_6, 1, x_35);
lean_ctor_set(x_6, 0, x_26);
return x_6;
}
else
{
lean_ctor_set(x_6, 1, x_28);
lean_ctor_set(x_6, 0, x_26);
return x_6;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_box(0);
x_37 = lean_array_uset(x_9, x_22, x_36);
x_38 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__6(x_3, x_4, x_23);
x_39 = lean_array_uset(x_37, x_22, x_38);
lean_ctor_set(x_6, 1, x_39);
return x_6;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; size_t x_50; size_t x_51; size_t x_52; size_t x_53; size_t x_54; lean_object* x_55; uint8_t x_56; 
x_40 = lean_ctor_get(x_6, 0);
x_41 = lean_ctor_get(x_6, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_6);
x_42 = lean_array_get_size(x_41);
x_43 = lean_uint64_of_nat(x_3);
x_44 = 32;
x_45 = lean_uint64_shift_right(x_43, x_44);
x_46 = lean_uint64_xor(x_43, x_45);
x_47 = 16;
x_48 = lean_uint64_shift_right(x_46, x_47);
x_49 = lean_uint64_xor(x_46, x_48);
x_50 = lean_uint64_to_usize(x_49);
x_51 = lean_usize_of_nat(x_42);
lean_dec(x_42);
x_52 = 1;
x_53 = lean_usize_sub(x_51, x_52);
x_54 = lean_usize_land(x_50, x_53);
x_55 = lean_array_uget(x_41, x_54);
x_56 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(x_3, x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_add(x_40, x_57);
lean_dec(x_40);
x_59 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_59, 0, x_3);
lean_ctor_set(x_59, 1, x_4);
lean_ctor_set(x_59, 2, x_55);
x_60 = lean_array_uset(x_41, x_54, x_59);
x_61 = lean_unsigned_to_nat(4u);
x_62 = lean_nat_mul(x_58, x_61);
x_63 = lean_unsigned_to_nat(3u);
x_64 = lean_nat_div(x_62, x_63);
lean_dec(x_62);
x_65 = lean_array_get_size(x_60);
x_66 = lean_nat_dec_le(x_64, x_65);
lean_dec(x_65);
lean_dec(x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__2(x_60);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_58);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_58);
lean_ctor_set(x_69, 1, x_60);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_70 = lean_box(0);
x_71 = lean_array_uset(x_41, x_54, x_70);
x_72 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__6(x_3, x_4, x_55);
x_73 = lean_array_uset(x_71, x_54, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_40);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
case 4:
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_6);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint64_t x_79; uint64_t x_80; uint64_t x_81; uint64_t x_82; uint64_t x_83; uint64_t x_84; uint64_t x_85; size_t x_86; size_t x_87; size_t x_88; size_t x_89; size_t x_90; lean_object* x_91; uint8_t x_92; 
x_76 = lean_ctor_get(x_6, 0);
x_77 = lean_ctor_get(x_6, 1);
x_78 = lean_array_get_size(x_77);
x_79 = lean_uint64_of_nat(x_3);
x_80 = 32;
x_81 = lean_uint64_shift_right(x_79, x_80);
x_82 = lean_uint64_xor(x_79, x_81);
x_83 = 16;
x_84 = lean_uint64_shift_right(x_82, x_83);
x_85 = lean_uint64_xor(x_82, x_84);
x_86 = lean_uint64_to_usize(x_85);
x_87 = lean_usize_of_nat(x_78);
lean_dec(x_78);
x_88 = 1;
x_89 = lean_usize_sub(x_87, x_88);
x_90 = lean_usize_land(x_86, x_89);
x_91 = lean_array_uget(x_77, x_90);
x_92 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(x_3, x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_93 = lean_unsigned_to_nat(1u);
x_94 = lean_nat_add(x_76, x_93);
lean_dec(x_76);
x_95 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_95, 0, x_3);
lean_ctor_set(x_95, 1, x_4);
lean_ctor_set(x_95, 2, x_91);
x_96 = lean_array_uset(x_77, x_90, x_95);
x_97 = lean_unsigned_to_nat(4u);
x_98 = lean_nat_mul(x_94, x_97);
x_99 = lean_unsigned_to_nat(3u);
x_100 = lean_nat_div(x_98, x_99);
lean_dec(x_98);
x_101 = lean_array_get_size(x_96);
x_102 = lean_nat_dec_le(x_100, x_101);
lean_dec(x_101);
lean_dec(x_100);
if (x_102 == 0)
{
lean_object* x_103; 
x_103 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__2(x_96);
lean_ctor_set(x_6, 1, x_103);
lean_ctor_set(x_6, 0, x_94);
return x_6;
}
else
{
lean_ctor_set(x_6, 1, x_96);
lean_ctor_set(x_6, 0, x_94);
return x_6;
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_104 = lean_box(0);
x_105 = lean_array_uset(x_77, x_90, x_104);
x_106 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__6(x_3, x_4, x_91);
x_107 = lean_array_uset(x_105, x_90, x_106);
lean_ctor_set(x_6, 1, x_107);
return x_6;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint64_t x_111; uint64_t x_112; uint64_t x_113; uint64_t x_114; uint64_t x_115; uint64_t x_116; uint64_t x_117; size_t x_118; size_t x_119; size_t x_120; size_t x_121; size_t x_122; lean_object* x_123; uint8_t x_124; 
x_108 = lean_ctor_get(x_6, 0);
x_109 = lean_ctor_get(x_6, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_6);
x_110 = lean_array_get_size(x_109);
x_111 = lean_uint64_of_nat(x_3);
x_112 = 32;
x_113 = lean_uint64_shift_right(x_111, x_112);
x_114 = lean_uint64_xor(x_111, x_113);
x_115 = 16;
x_116 = lean_uint64_shift_right(x_114, x_115);
x_117 = lean_uint64_xor(x_114, x_116);
x_118 = lean_uint64_to_usize(x_117);
x_119 = lean_usize_of_nat(x_110);
lean_dec(x_110);
x_120 = 1;
x_121 = lean_usize_sub(x_119, x_120);
x_122 = lean_usize_land(x_118, x_121);
x_123 = lean_array_uget(x_109, x_122);
x_124 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(x_3, x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_125 = lean_unsigned_to_nat(1u);
x_126 = lean_nat_add(x_108, x_125);
lean_dec(x_108);
x_127 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_127, 0, x_3);
lean_ctor_set(x_127, 1, x_4);
lean_ctor_set(x_127, 2, x_123);
x_128 = lean_array_uset(x_109, x_122, x_127);
x_129 = lean_unsigned_to_nat(4u);
x_130 = lean_nat_mul(x_126, x_129);
x_131 = lean_unsigned_to_nat(3u);
x_132 = lean_nat_div(x_130, x_131);
lean_dec(x_130);
x_133 = lean_array_get_size(x_128);
x_134 = lean_nat_dec_le(x_132, x_133);
lean_dec(x_133);
lean_dec(x_132);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; 
x_135 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__2(x_128);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_126);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
else
{
lean_object* x_137; 
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_126);
lean_ctor_set(x_137, 1, x_128);
return x_137;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_138 = lean_box(0);
x_139 = lean_array_uset(x_109, x_122, x_138);
x_140 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__6(x_3, x_4, x_123);
x_141 = lean_array_uset(x_139, x_122, x_140);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_108);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
case 5:
{
uint8_t x_143; 
x_143 = !lean_is_exclusive(x_6);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; uint64_t x_147; uint64_t x_148; uint64_t x_149; uint64_t x_150; uint64_t x_151; uint64_t x_152; uint64_t x_153; size_t x_154; size_t x_155; size_t x_156; size_t x_157; size_t x_158; lean_object* x_159; uint8_t x_160; 
x_144 = lean_ctor_get(x_6, 0);
x_145 = lean_ctor_get(x_6, 1);
x_146 = lean_array_get_size(x_145);
x_147 = lean_uint64_of_nat(x_3);
x_148 = 32;
x_149 = lean_uint64_shift_right(x_147, x_148);
x_150 = lean_uint64_xor(x_147, x_149);
x_151 = 16;
x_152 = lean_uint64_shift_right(x_150, x_151);
x_153 = lean_uint64_xor(x_150, x_152);
x_154 = lean_uint64_to_usize(x_153);
x_155 = lean_usize_of_nat(x_146);
lean_dec(x_146);
x_156 = 1;
x_157 = lean_usize_sub(x_155, x_156);
x_158 = lean_usize_land(x_154, x_157);
x_159 = lean_array_uget(x_145, x_158);
x_160 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(x_3, x_159);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_161 = lean_unsigned_to_nat(1u);
x_162 = lean_nat_add(x_144, x_161);
lean_dec(x_144);
x_163 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_163, 0, x_3);
lean_ctor_set(x_163, 1, x_4);
lean_ctor_set(x_163, 2, x_159);
x_164 = lean_array_uset(x_145, x_158, x_163);
x_165 = lean_unsigned_to_nat(4u);
x_166 = lean_nat_mul(x_162, x_165);
x_167 = lean_unsigned_to_nat(3u);
x_168 = lean_nat_div(x_166, x_167);
lean_dec(x_166);
x_169 = lean_array_get_size(x_164);
x_170 = lean_nat_dec_le(x_168, x_169);
lean_dec(x_169);
lean_dec(x_168);
if (x_170 == 0)
{
lean_object* x_171; 
x_171 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__2(x_164);
lean_ctor_set(x_6, 1, x_171);
lean_ctor_set(x_6, 0, x_162);
return x_6;
}
else
{
lean_ctor_set(x_6, 1, x_164);
lean_ctor_set(x_6, 0, x_162);
return x_6;
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_172 = lean_box(0);
x_173 = lean_array_uset(x_145, x_158, x_172);
x_174 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__6(x_3, x_4, x_159);
x_175 = lean_array_uset(x_173, x_158, x_174);
lean_ctor_set(x_6, 1, x_175);
return x_6;
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; uint64_t x_179; uint64_t x_180; uint64_t x_181; uint64_t x_182; uint64_t x_183; uint64_t x_184; uint64_t x_185; size_t x_186; size_t x_187; size_t x_188; size_t x_189; size_t x_190; lean_object* x_191; uint8_t x_192; 
x_176 = lean_ctor_get(x_6, 0);
x_177 = lean_ctor_get(x_6, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_6);
x_178 = lean_array_get_size(x_177);
x_179 = lean_uint64_of_nat(x_3);
x_180 = 32;
x_181 = lean_uint64_shift_right(x_179, x_180);
x_182 = lean_uint64_xor(x_179, x_181);
x_183 = 16;
x_184 = lean_uint64_shift_right(x_182, x_183);
x_185 = lean_uint64_xor(x_182, x_184);
x_186 = lean_uint64_to_usize(x_185);
x_187 = lean_usize_of_nat(x_178);
lean_dec(x_178);
x_188 = 1;
x_189 = lean_usize_sub(x_187, x_188);
x_190 = lean_usize_land(x_186, x_189);
x_191 = lean_array_uget(x_177, x_190);
x_192 = l_Std_DHashMap_Internal_AssocList_contains___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__1(x_3, x_191);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_193 = lean_unsigned_to_nat(1u);
x_194 = lean_nat_add(x_176, x_193);
lean_dec(x_176);
x_195 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_195, 0, x_3);
lean_ctor_set(x_195, 1, x_4);
lean_ctor_set(x_195, 2, x_191);
x_196 = lean_array_uset(x_177, x_190, x_195);
x_197 = lean_unsigned_to_nat(4u);
x_198 = lean_nat_mul(x_194, x_197);
x_199 = lean_unsigned_to_nat(3u);
x_200 = lean_nat_div(x_198, x_199);
lean_dec(x_198);
x_201 = lean_array_get_size(x_196);
x_202 = lean_nat_dec_le(x_200, x_201);
lean_dec(x_201);
lean_dec(x_200);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; 
x_203 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__2(x_196);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_194);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
else
{
lean_object* x_205; 
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_194);
lean_ctor_set(x_205, 1, x_196);
return x_205;
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_206 = lean_box(0);
x_207 = lean_array_uset(x_177, x_190, x_206);
x_208 = l_Std_DHashMap_Internal_AssocList_replace___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectVDecl___spec__6(x_3, x_4, x_191);
x_209 = lean_array_uset(x_207, x_190, x_208);
x_210 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_210, 0, x_176);
lean_ctor_set(x_210, 1, x_209);
return x_210;
}
}
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
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_1, 2);
lean_inc(x_211);
x_212 = lean_ctor_get(x_1, 3);
lean_inc(x_212);
lean_dec(x_1);
x_213 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody(x_212, x_2);
x_1 = x_211;
x_2 = x_213;
goto _start;
}
case 10:
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; 
x_215 = lean_ctor_get(x_1, 3);
lean_inc(x_215);
lean_dec(x_1);
x_216 = lean_array_get_size(x_215);
x_217 = lean_unsigned_to_nat(0u);
x_218 = lean_nat_dec_lt(x_217, x_216);
if (x_218 == 0)
{
lean_dec(x_216);
lean_dec(x_215);
return x_2;
}
else
{
uint8_t x_219; 
x_219 = lean_nat_dec_le(x_216, x_216);
if (x_219 == 0)
{
lean_dec(x_216);
lean_dec(x_215);
return x_2;
}
else
{
size_t x_220; size_t x_221; lean_object* x_222; 
x_220 = 0;
x_221 = lean_usize_of_nat(x_216);
lean_dec(x_216);
x_222 = l_Array_foldlMUnsafe_fold___at_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody___spec__1(x_215, x_220, x_221, x_2);
lean_dec(x_215);
return x_222;
}
}
}
default: 
{
uint8_t x_223; 
x_223 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_223 == 0)
{
lean_object* x_224; 
x_224 = l_Lean_IR_FnBody_body(x_1);
lean_dec(x_1);
x_1 = x_224;
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
static lean_object* _init_l_Lean_IR_ExpandResetReuse_mkProjMap___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(10u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = l_Nat_nextPowerOfTwo_go(x_1, x_2, lean_box(0));
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ExpandResetReuse_mkProjMap___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_IR_ExpandResetReuse_mkProjMap___closed__1;
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_IR_ExpandResetReuse_mkProjMap___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_IR_ExpandResetReuse_mkProjMap___closed__2;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkProjMap(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_ctor_get(x_1, 3);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Lean_IR_ExpandResetReuse_mkProjMap___closed__3;
x_4 = l_Lean_IR_ExpandResetReuse_CollectProjMap_collectFnBody(x_2, x_3);
return x_4;
}
else
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = l_Lean_IR_ExpandResetReuse_mkProjMap___closed__3;
return x_5;
}
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
x_9 = l_Array_back_x21___rarg(x_8, x_2);
switch (lean_obj_tag(x_9)) {
case 0:
{
lean_object* x_10; 
lean_dec(x_5);
x_10 = lean_ctor_get(x_9, 2);
lean_inc(x_10);
switch (lean_obj_tag(x_10)) {
case 0:
{
uint8_t x_11; 
lean_dec(x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = l_Array_reverse___rarg(x_4);
x_15 = l_Array_append___rarg(x_2, x_14);
lean_dec(x_14);
lean_ctor_set(x_10, 1, x_3);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_10);
x_16 = l_Array_reverse___rarg(x_4);
x_17 = l_Array_append___rarg(x_2, x_16);
lean_dec(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_3);
return x_18;
}
}
case 2:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_10);
lean_dec(x_9);
x_19 = l_Array_reverse___rarg(x_4);
x_20 = l_Array_append___rarg(x_2, x_19);
lean_dec(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_3);
return x_21;
}
case 4:
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_10);
x_22 = lean_array_pop(x_2);
x_23 = lean_array_push(x_4, x_9);
x_2 = x_22;
x_4 = x_23;
goto _start;
}
case 5:
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_10);
x_25 = lean_array_pop(x_2);
x_26 = lean_array_push(x_4, x_9);
x_2 = x_25;
x_4 = x_26;
goto _start;
}
case 10:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_10);
lean_dec(x_9);
x_28 = l_Array_reverse___rarg(x_4);
x_29 = l_Array_append___rarg(x_2, x_28);
lean_dec(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_3);
return x_30;
}
case 11:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_10);
lean_dec(x_9);
x_31 = l_Array_reverse___rarg(x_4);
x_32 = l_Array_append___rarg(x_2, x_31);
lean_dec(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_3);
return x_33;
}
case 12:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_10);
lean_dec(x_9);
x_34 = l_Array_reverse___rarg(x_4);
x_35 = l_Array_append___rarg(x_2, x_34);
lean_dec(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_3);
return x_36;
}
default: 
{
uint8_t x_37; 
lean_dec(x_9);
x_37 = !lean_is_exclusive(x_10);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_10, 1);
lean_dec(x_38);
x_39 = lean_ctor_get(x_10, 0);
lean_dec(x_39);
x_40 = l_Array_reverse___rarg(x_4);
x_41 = l_Array_append___rarg(x_2, x_40);
lean_dec(x_40);
lean_ctor_set_tag(x_10, 0);
lean_ctor_set(x_10, 1, x_3);
lean_ctor_set(x_10, 0, x_41);
return x_10;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_10);
x_42 = l_Array_reverse___rarg(x_4);
x_43 = l_Array_append___rarg(x_2, x_42);
lean_dec(x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_3);
return x_44;
}
}
}
}
case 6:
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_9);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_46 = lean_ctor_get(x_9, 0);
x_47 = lean_ctor_get(x_9, 1);
x_48 = lean_ctor_get(x_9, 2);
lean_dec(x_48);
x_49 = lean_unsigned_to_nat(0u);
x_50 = lean_nat_dec_eq(x_47, x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_nat_sub(x_5, x_6);
lean_dec(x_5);
x_52 = lean_array_fget(x_2, x_51);
lean_dec(x_51);
switch (lean_obj_tag(x_52)) {
case 0:
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_52, 2);
lean_inc(x_53);
switch (lean_obj_tag(x_53)) {
case 0:
{
uint8_t x_54; 
lean_dec(x_52);
lean_free_object(x_9);
lean_dec(x_47);
lean_dec(x_46);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_53, 1);
lean_dec(x_55);
x_56 = lean_ctor_get(x_53, 0);
lean_dec(x_56);
x_57 = l_Array_reverse___rarg(x_4);
x_58 = l_Array_append___rarg(x_2, x_57);
lean_dec(x_57);
lean_ctor_set(x_53, 1, x_3);
lean_ctor_set(x_53, 0, x_58);
return x_53;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_53);
x_59 = l_Array_reverse___rarg(x_4);
x_60 = l_Array_append___rarg(x_2, x_59);
lean_dec(x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_3);
return x_61;
}
}
case 2:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_53);
lean_dec(x_52);
lean_free_object(x_9);
lean_dec(x_47);
lean_dec(x_46);
x_62 = l_Array_reverse___rarg(x_4);
x_63 = l_Array_append___rarg(x_2, x_62);
lean_dec(x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_3);
return x_64;
}
case 3:
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_52, 0);
lean_inc(x_65);
x_66 = !lean_is_exclusive(x_53);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = lean_ctor_get(x_53, 0);
x_68 = lean_ctor_get(x_53, 1);
x_69 = lean_nat_dec_eq(x_65, x_46);
lean_dec(x_65);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_52);
lean_free_object(x_9);
lean_dec(x_47);
lean_dec(x_46);
x_70 = l_Array_reverse___rarg(x_4);
x_71 = l_Array_append___rarg(x_2, x_70);
lean_dec(x_70);
lean_ctor_set_tag(x_53, 0);
lean_ctor_set(x_53, 1, x_3);
lean_ctor_set(x_53, 0, x_71);
return x_53;
}
else
{
uint8_t x_72; 
x_72 = lean_nat_dec_eq(x_1, x_68);
lean_dec(x_68);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_67);
lean_dec(x_52);
lean_free_object(x_9);
lean_dec(x_47);
lean_dec(x_46);
x_73 = l_Array_reverse___rarg(x_4);
x_74 = l_Array_append___rarg(x_2, x_73);
lean_dec(x_73);
lean_ctor_set_tag(x_53, 0);
lean_ctor_set(x_53, 1, x_3);
lean_ctor_set(x_53, 0, x_74);
return x_53;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
lean_free_object(x_53);
x_75 = lean_array_pop(x_2);
x_76 = lean_array_pop(x_75);
lean_inc(x_46);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_46);
x_78 = lean_array_set(x_3, x_67, x_77);
lean_dec(x_67);
x_79 = lean_array_push(x_4, x_52);
x_80 = lean_unsigned_to_nat(1u);
x_81 = lean_nat_dec_eq(x_47, x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_nat_sub(x_47, x_80);
lean_dec(x_47);
x_83 = lean_box(13);
lean_ctor_set(x_9, 2, x_83);
lean_ctor_set(x_9, 1, x_82);
x_84 = lean_array_push(x_79, x_9);
x_2 = x_76;
x_3 = x_78;
x_4 = x_84;
goto _start;
}
else
{
lean_free_object(x_9);
lean_dec(x_47);
lean_dec(x_46);
x_2 = x_76;
x_3 = x_78;
x_4 = x_79;
goto _start;
}
}
}
}
else
{
lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_87 = lean_ctor_get(x_53, 0);
x_88 = lean_ctor_get(x_53, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_53);
x_89 = lean_nat_dec_eq(x_65, x_46);
lean_dec(x_65);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_52);
lean_free_object(x_9);
lean_dec(x_47);
lean_dec(x_46);
x_90 = l_Array_reverse___rarg(x_4);
x_91 = l_Array_append___rarg(x_2, x_90);
lean_dec(x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_3);
return x_92;
}
else
{
uint8_t x_93; 
x_93 = lean_nat_dec_eq(x_1, x_88);
lean_dec(x_88);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_87);
lean_dec(x_52);
lean_free_object(x_9);
lean_dec(x_47);
lean_dec(x_46);
x_94 = l_Array_reverse___rarg(x_4);
x_95 = l_Array_append___rarg(x_2, x_94);
lean_dec(x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_3);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_97 = lean_array_pop(x_2);
x_98 = lean_array_pop(x_97);
lean_inc(x_46);
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_46);
x_100 = lean_array_set(x_3, x_87, x_99);
lean_dec(x_87);
x_101 = lean_array_push(x_4, x_52);
x_102 = lean_unsigned_to_nat(1u);
x_103 = lean_nat_dec_eq(x_47, x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_nat_sub(x_47, x_102);
lean_dec(x_47);
x_105 = lean_box(13);
lean_ctor_set(x_9, 2, x_105);
lean_ctor_set(x_9, 1, x_104);
x_106 = lean_array_push(x_101, x_9);
x_2 = x_98;
x_3 = x_100;
x_4 = x_106;
goto _start;
}
else
{
lean_free_object(x_9);
lean_dec(x_47);
lean_dec(x_46);
x_2 = x_98;
x_3 = x_100;
x_4 = x_101;
goto _start;
}
}
}
}
}
case 5:
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_53);
lean_dec(x_52);
lean_free_object(x_9);
lean_dec(x_47);
lean_dec(x_46);
x_109 = l_Array_reverse___rarg(x_4);
x_110 = l_Array_append___rarg(x_2, x_109);
lean_dec(x_109);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_3);
return x_111;
}
case 10:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_53);
lean_dec(x_52);
lean_free_object(x_9);
lean_dec(x_47);
lean_dec(x_46);
x_112 = l_Array_reverse___rarg(x_4);
x_113 = l_Array_append___rarg(x_2, x_112);
lean_dec(x_112);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_3);
return x_114;
}
case 11:
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_53);
lean_dec(x_52);
lean_free_object(x_9);
lean_dec(x_47);
lean_dec(x_46);
x_115 = l_Array_reverse___rarg(x_4);
x_116 = l_Array_append___rarg(x_2, x_115);
lean_dec(x_115);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_3);
return x_117;
}
case 12:
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_53);
lean_dec(x_52);
lean_free_object(x_9);
lean_dec(x_47);
lean_dec(x_46);
x_118 = l_Array_reverse___rarg(x_4);
x_119 = l_Array_append___rarg(x_2, x_118);
lean_dec(x_118);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_119);
lean_ctor_set(x_120, 1, x_3);
return x_120;
}
default: 
{
uint8_t x_121; 
lean_dec(x_52);
lean_free_object(x_9);
lean_dec(x_47);
lean_dec(x_46);
x_121 = !lean_is_exclusive(x_53);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_122 = lean_ctor_get(x_53, 1);
lean_dec(x_122);
x_123 = lean_ctor_get(x_53, 0);
lean_dec(x_123);
x_124 = l_Array_reverse___rarg(x_4);
x_125 = l_Array_append___rarg(x_2, x_124);
lean_dec(x_124);
lean_ctor_set_tag(x_53, 0);
lean_ctor_set(x_53, 1, x_3);
lean_ctor_set(x_53, 0, x_125);
return x_53;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_53);
x_126 = l_Array_reverse___rarg(x_4);
x_127 = l_Array_append___rarg(x_2, x_126);
lean_dec(x_126);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_3);
return x_128;
}
}
}
}
case 8:
{
uint8_t x_129; 
lean_free_object(x_9);
lean_dec(x_47);
lean_dec(x_46);
x_129 = !lean_is_exclusive(x_52);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_130 = lean_ctor_get(x_52, 1);
lean_dec(x_130);
x_131 = lean_ctor_get(x_52, 0);
lean_dec(x_131);
x_132 = l_Array_reverse___rarg(x_4);
x_133 = l_Array_append___rarg(x_2, x_132);
lean_dec(x_132);
lean_ctor_set_tag(x_52, 0);
lean_ctor_set(x_52, 1, x_3);
lean_ctor_set(x_52, 0, x_133);
return x_52;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_52);
x_134 = l_Array_reverse___rarg(x_4);
x_135 = l_Array_append___rarg(x_2, x_134);
lean_dec(x_134);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_3);
return x_136;
}
}
case 9:
{
uint8_t x_137; 
lean_free_object(x_9);
lean_dec(x_47);
lean_dec(x_46);
x_137 = !lean_is_exclusive(x_52);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_138 = lean_ctor_get(x_52, 1);
lean_dec(x_138);
x_139 = lean_ctor_get(x_52, 0);
lean_dec(x_139);
x_140 = l_Array_reverse___rarg(x_4);
x_141 = l_Array_append___rarg(x_2, x_140);
lean_dec(x_140);
lean_ctor_set_tag(x_52, 0);
lean_ctor_set(x_52, 1, x_3);
lean_ctor_set(x_52, 0, x_141);
return x_52;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_52);
x_142 = l_Array_reverse___rarg(x_4);
x_143 = l_Array_append___rarg(x_2, x_142);
lean_dec(x_142);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_3);
return x_144;
}
}
case 12:
{
uint8_t x_145; 
lean_free_object(x_9);
lean_dec(x_47);
lean_dec(x_46);
x_145 = !lean_is_exclusive(x_52);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_146 = lean_ctor_get(x_52, 1);
lean_dec(x_146);
x_147 = lean_ctor_get(x_52, 0);
lean_dec(x_147);
x_148 = l_Array_reverse___rarg(x_4);
x_149 = l_Array_append___rarg(x_2, x_148);
lean_dec(x_148);
lean_ctor_set_tag(x_52, 0);
lean_ctor_set(x_52, 1, x_3);
lean_ctor_set(x_52, 0, x_149);
return x_52;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_52);
x_150 = l_Array_reverse___rarg(x_4);
x_151 = l_Array_append___rarg(x_2, x_150);
lean_dec(x_150);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_3);
return x_152;
}
}
default: 
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_52);
lean_free_object(x_9);
lean_dec(x_47);
lean_dec(x_46);
x_153 = l_Array_reverse___rarg(x_4);
x_154 = l_Array_append___rarg(x_2, x_153);
lean_dec(x_153);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_3);
return x_155;
}
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_free_object(x_9);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_5);
x_156 = l_Array_reverse___rarg(x_4);
x_157 = l_Array_append___rarg(x_2, x_156);
lean_dec(x_156);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_3);
return x_158;
}
}
else
{
lean_object* x_159; lean_object* x_160; uint8_t x_161; uint8_t x_162; lean_object* x_163; uint8_t x_164; 
x_159 = lean_ctor_get(x_9, 0);
x_160 = lean_ctor_get(x_9, 1);
x_161 = lean_ctor_get_uint8(x_9, sizeof(void*)*3);
x_162 = lean_ctor_get_uint8(x_9, sizeof(void*)*3 + 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_9);
x_163 = lean_unsigned_to_nat(0u);
x_164 = lean_nat_dec_eq(x_160, x_163);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_nat_sub(x_5, x_6);
lean_dec(x_5);
x_166 = lean_array_fget(x_2, x_165);
lean_dec(x_165);
switch (lean_obj_tag(x_166)) {
case 0:
{
lean_object* x_167; 
x_167 = lean_ctor_get(x_166, 2);
lean_inc(x_167);
switch (lean_obj_tag(x_167)) {
case 0:
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_166);
lean_dec(x_160);
lean_dec(x_159);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_168 = x_167;
} else {
 lean_dec_ref(x_167);
 x_168 = lean_box(0);
}
x_169 = l_Array_reverse___rarg(x_4);
x_170 = l_Array_append___rarg(x_2, x_169);
lean_dec(x_169);
if (lean_is_scalar(x_168)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_168;
}
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_3);
return x_171;
}
case 2:
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_160);
lean_dec(x_159);
x_172 = l_Array_reverse___rarg(x_4);
x_173 = l_Array_append___rarg(x_2, x_172);
lean_dec(x_172);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_3);
return x_174;
}
case 3:
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_175 = lean_ctor_get(x_166, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_167, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_167, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_178 = x_167;
} else {
 lean_dec_ref(x_167);
 x_178 = lean_box(0);
}
x_179 = lean_nat_dec_eq(x_175, x_159);
lean_dec(x_175);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_177);
lean_dec(x_176);
lean_dec(x_166);
lean_dec(x_160);
lean_dec(x_159);
x_180 = l_Array_reverse___rarg(x_4);
x_181 = l_Array_append___rarg(x_2, x_180);
lean_dec(x_180);
if (lean_is_scalar(x_178)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_178;
 lean_ctor_set_tag(x_182, 0);
}
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_3);
return x_182;
}
else
{
uint8_t x_183; 
x_183 = lean_nat_dec_eq(x_1, x_177);
lean_dec(x_177);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_176);
lean_dec(x_166);
lean_dec(x_160);
lean_dec(x_159);
x_184 = l_Array_reverse___rarg(x_4);
x_185 = l_Array_append___rarg(x_2, x_184);
lean_dec(x_184);
if (lean_is_scalar(x_178)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_178;
 lean_ctor_set_tag(x_186, 0);
}
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_3);
return x_186;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; uint8_t x_193; 
lean_dec(x_178);
x_187 = lean_array_pop(x_2);
x_188 = lean_array_pop(x_187);
lean_inc(x_159);
x_189 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_189, 0, x_159);
x_190 = lean_array_set(x_3, x_176, x_189);
lean_dec(x_176);
x_191 = lean_array_push(x_4, x_166);
x_192 = lean_unsigned_to_nat(1u);
x_193 = lean_nat_dec_eq(x_160, x_192);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_194 = lean_nat_sub(x_160, x_192);
lean_dec(x_160);
x_195 = lean_box(13);
x_196 = lean_alloc_ctor(6, 3, 2);
lean_ctor_set(x_196, 0, x_159);
lean_ctor_set(x_196, 1, x_194);
lean_ctor_set(x_196, 2, x_195);
lean_ctor_set_uint8(x_196, sizeof(void*)*3, x_161);
lean_ctor_set_uint8(x_196, sizeof(void*)*3 + 1, x_162);
x_197 = lean_array_push(x_191, x_196);
x_2 = x_188;
x_3 = x_190;
x_4 = x_197;
goto _start;
}
else
{
lean_dec(x_160);
lean_dec(x_159);
x_2 = x_188;
x_3 = x_190;
x_4 = x_191;
goto _start;
}
}
}
}
case 5:
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_160);
lean_dec(x_159);
x_200 = l_Array_reverse___rarg(x_4);
x_201 = l_Array_append___rarg(x_2, x_200);
lean_dec(x_200);
x_202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_3);
return x_202;
}
case 10:
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_160);
lean_dec(x_159);
x_203 = l_Array_reverse___rarg(x_4);
x_204 = l_Array_append___rarg(x_2, x_203);
lean_dec(x_203);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_3);
return x_205;
}
case 11:
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_160);
lean_dec(x_159);
x_206 = l_Array_reverse___rarg(x_4);
x_207 = l_Array_append___rarg(x_2, x_206);
lean_dec(x_206);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_3);
return x_208;
}
case 12:
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_160);
lean_dec(x_159);
x_209 = l_Array_reverse___rarg(x_4);
x_210 = l_Array_append___rarg(x_2, x_209);
lean_dec(x_209);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_3);
return x_211;
}
default: 
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_166);
lean_dec(x_160);
lean_dec(x_159);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_212 = x_167;
} else {
 lean_dec_ref(x_167);
 x_212 = lean_box(0);
}
x_213 = l_Array_reverse___rarg(x_4);
x_214 = l_Array_append___rarg(x_2, x_213);
lean_dec(x_213);
if (lean_is_scalar(x_212)) {
 x_215 = lean_alloc_ctor(0, 2, 0);
} else {
 x_215 = x_212;
 lean_ctor_set_tag(x_215, 0);
}
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_3);
return x_215;
}
}
}
case 8:
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_160);
lean_dec(x_159);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_216 = x_166;
} else {
 lean_dec_ref(x_166);
 x_216 = lean_box(0);
}
x_217 = l_Array_reverse___rarg(x_4);
x_218 = l_Array_append___rarg(x_2, x_217);
lean_dec(x_217);
if (lean_is_scalar(x_216)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_216;
 lean_ctor_set_tag(x_219, 0);
}
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_3);
return x_219;
}
case 9:
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_dec(x_160);
lean_dec(x_159);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_220 = x_166;
} else {
 lean_dec_ref(x_166);
 x_220 = lean_box(0);
}
x_221 = l_Array_reverse___rarg(x_4);
x_222 = l_Array_append___rarg(x_2, x_221);
lean_dec(x_221);
if (lean_is_scalar(x_220)) {
 x_223 = lean_alloc_ctor(0, 2, 0);
} else {
 x_223 = x_220;
 lean_ctor_set_tag(x_223, 0);
}
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_3);
return x_223;
}
case 12:
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_160);
lean_dec(x_159);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_224 = x_166;
} else {
 lean_dec_ref(x_166);
 x_224 = lean_box(0);
}
x_225 = l_Array_reverse___rarg(x_4);
x_226 = l_Array_append___rarg(x_2, x_225);
lean_dec(x_225);
if (lean_is_scalar(x_224)) {
 x_227 = lean_alloc_ctor(0, 2, 0);
} else {
 x_227 = x_224;
 lean_ctor_set_tag(x_227, 0);
}
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_3);
return x_227;
}
default: 
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_166);
lean_dec(x_160);
lean_dec(x_159);
x_228 = l_Array_reverse___rarg(x_4);
x_229 = l_Array_append___rarg(x_2, x_228);
lean_dec(x_228);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_3);
return x_230;
}
}
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_5);
x_231 = l_Array_reverse___rarg(x_4);
x_232 = l_Array_append___rarg(x_2, x_231);
lean_dec(x_231);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_3);
return x_233;
}
}
}
default: 
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_9);
lean_dec(x_5);
x_234 = l_Array_reverse___rarg(x_4);
x_235 = l_Array_append___rarg(x_2, x_234);
lean_dec(x_234);
x_236 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_3);
return x_236;
}
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_dec(x_5);
x_237 = l_Array_reverse___rarg(x_4);
x_238 = l_Array_append___rarg(x_2, x_237);
lean_dec(x_237);
x_239 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_239, 0, x_238);
lean_ctor_set(x_239, 1, x_3);
return x_239;
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
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
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
lean_object* x_48; size_t x_49; size_t x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_2, 3);
x_49 = lean_array_size(x_48);
x_50 = 0;
x_51 = l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_reuseToCtor___spec__1(x_1, x_49, x_50, x_48);
lean_ctor_set(x_2, 3, x_51);
return x_2;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; size_t x_56; size_t x_57; lean_object* x_58; lean_object* x_59; 
x_52 = lean_ctor_get(x_2, 0);
x_53 = lean_ctor_get(x_2, 1);
x_54 = lean_ctor_get(x_2, 2);
x_55 = lean_ctor_get(x_2, 3);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_2);
x_56 = lean_array_size(x_55);
x_57 = 0;
x_58 = l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_reuseToCtor___spec__1(x_1, x_56, x_57, x_55);
x_59 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_59, 0, x_52);
lean_ctor_set(x_59, 1, x_53);
lean_ctor_set(x_59, 2, x_54);
lean_ctor_set(x_59, 3, x_58);
return x_59;
}
}
default: 
{
uint8_t x_60; 
x_60 = l_Lean_IR_FnBody_isTerminal(x_2);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_61 = l_Lean_IR_FnBody_body(x_2);
x_62 = lean_box(13);
x_63 = l_Lean_IR_FnBody_setBody(x_2, x_62);
x_64 = l_Lean_IR_ExpandResetReuse_reuseToCtor(x_1, x_61);
x_65 = l_Lean_IR_FnBody_setBody(x_63, x_64);
return x_65;
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
return x_9;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_10, x_10);
if (x_13 == 0)
{
lean_dec(x_10);
return x_9;
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = 0;
x_15 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_16 = l_Array_foldlMUnsafe_fold___at_Lean_IR_ExpandResetReuse_mkSlowPath___spec__1(x_3, x_14, x_15, x_9);
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
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkSlowPath___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ExpandResetReuse_mkSlowPath(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
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
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lean_IR_ExpandResetReuse_releaseUnreadFields___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_4, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_4, x_11);
lean_dec(x_4);
x_13 = lean_nat_sub(x_3, x_12);
x_14 = lean_nat_sub(x_13, x_11);
lean_dec(x_13);
x_15 = lean_array_fget(x_2, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = l_Lean_IR_ExpandResetReuse_mkFresh___rarg(x_8);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_1);
lean_ctor_set_tag(x_16, 3);
lean_ctor_set(x_16, 1, x_1);
lean_ctor_set(x_16, 0, x_14);
x_20 = 1;
x_21 = 0;
lean_inc(x_18);
x_22 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_11);
lean_ctor_set(x_22, 2, x_6);
lean_ctor_set_uint8(x_22, sizeof(void*)*3, x_20);
lean_ctor_set_uint8(x_22, sizeof(void*)*3 + 1, x_21);
x_23 = lean_box(7);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_16);
lean_ctor_set(x_24, 3, x_22);
x_4 = x_12;
x_5 = lean_box(0);
x_6 = x_24;
x_8 = x_19;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_26 = lean_ctor_get(x_16, 0);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_16);
lean_inc(x_1);
x_28 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_28, 0, x_14);
lean_ctor_set(x_28, 1, x_1);
x_29 = 1;
x_30 = 0;
lean_inc(x_26);
x_31 = lean_alloc_ctor(7, 3, 2);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_11);
lean_ctor_set(x_31, 2, x_6);
lean_ctor_set_uint8(x_31, sizeof(void*)*3, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*3 + 1, x_30);
x_32 = lean_box(7);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_26);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_28);
lean_ctor_set(x_33, 3, x_31);
x_4 = x_12;
x_5 = lean_box(0);
x_6 = x_33;
x_8 = x_27;
goto _start;
}
}
else
{
lean_dec(x_15);
lean_dec(x_14);
x_4 = x_12;
x_5 = lean_box(0);
goto _start;
}
}
else
{
lean_object* x_36; 
lean_dec(x_4);
lean_dec(x_1);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_6);
lean_ctor_set(x_36, 1, x_8);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_releaseUnreadFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_get_size(x_2);
lean_inc(x_6);
x_7 = l_Nat_foldM_loop___at_Lean_IR_ExpandResetReuse_releaseUnreadFields___spec__1(x_1, x_2, x_6, x_6, lean_box(0), x_3, x_4, x_5);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_foldM_loop___at_Lean_IR_ExpandResetReuse_releaseUnreadFields___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Nat_foldM_loop___at_Lean_IR_ExpandResetReuse_releaseUnreadFields___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_releaseUnreadFields___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ExpandResetReuse_releaseUnreadFields(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_Lean_IR_ExpandResetReuse_setFields___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
x_11 = lean_nat_add(x_10, x_9);
x_12 = lean_nat_sub(x_3, x_11);
lean_dec(x_11);
x_13 = lean_array_fget(x_2, x_12);
lean_inc(x_1);
x_14 = lean_alloc_ctor(2, 4, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_14, 2, x_13);
lean_ctor_set(x_14, 3, x_6);
x_4 = x_10;
x_5 = lean_box(0);
x_6 = x_14;
goto _start;
}
else
{
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_setFields(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_array_get_size(x_2);
lean_inc(x_4);
x_5 = l_Nat_foldTR_loop___at_Lean_IR_ExpandResetReuse_setFields___spec__1(x_1, x_2, x_4, x_4, lean_box(0), x_3);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_foldTR_loop___at_Lean_IR_ExpandResetReuse_setFields___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Nat_foldTR_loop___at_Lean_IR_ExpandResetReuse_setFields___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__1(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT uint8_t l_Lean_IR_ExpandResetReuse_isSelfSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_uint64_of_nat(x_5);
x_9 = 32;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = 16;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = lean_uint64_to_usize(x_14);
x_16 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_17 = 1;
x_18 = lean_usize_sub(x_16, x_17);
x_19 = lean_usize_land(x_15, x_18);
x_20 = lean_array_uget(x_6, x_19);
x_21 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__1(x_5, x_20);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = 0;
return x_22;
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
if (lean_obj_tag(x_23) == 3)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_nat_dec_eq(x_24, x_3);
lean_dec(x_24);
if (x_26 == 0)
{
uint8_t x_27; 
lean_dec(x_25);
x_27 = 0;
return x_27;
}
else
{
uint8_t x_28; 
x_28 = lean_nat_dec_eq(x_25, x_2);
lean_dec(x_25);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_23);
x_29 = 0;
return x_29;
}
}
}
else
{
uint8_t x_30; 
x_30 = 0;
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__1(x_1, x_2);
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
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_ExpandResetReuse_isSelfUSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; lean_object* x_19; lean_object* x_20; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_array_get_size(x_5);
x_7 = lean_uint64_of_nat(x_4);
x_8 = 32;
x_9 = lean_uint64_shift_right(x_7, x_8);
x_10 = lean_uint64_xor(x_7, x_9);
x_11 = 16;
x_12 = lean_uint64_shift_right(x_10, x_11);
x_13 = lean_uint64_xor(x_10, x_12);
x_14 = lean_uint64_to_usize(x_13);
x_15 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_16 = 1;
x_17 = lean_usize_sub(x_15, x_16);
x_18 = lean_usize_land(x_14, x_17);
x_19 = lean_array_uget(x_5, x_18);
x_20 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__1(x_4, x_19);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = 0;
return x_21;
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
if (lean_obj_tag(x_22) == 4)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_nat_dec_eq(x_23, x_3);
lean_dec(x_23);
if (x_25 == 0)
{
uint8_t x_26; 
lean_dec(x_24);
x_26 = 0;
return x_26;
}
else
{
uint8_t x_27; 
x_27 = lean_nat_dec_eq(x_24, x_2);
lean_dec(x_24);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_22);
x_28 = 0;
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_isSelfUSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
LEAN_EXPORT uint8_t l_Lean_IR_ExpandResetReuse_isSelfSSet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; size_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_array_get_size(x_6);
x_8 = lean_uint64_of_nat(x_5);
x_9 = 32;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = 16;
x_13 = lean_uint64_shift_right(x_11, x_12);
x_14 = lean_uint64_xor(x_11, x_13);
x_15 = lean_uint64_to_usize(x_14);
x_16 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_17 = 1;
x_18 = lean_usize_sub(x_16, x_17);
x_19 = lean_usize_land(x_15, x_18);
x_20 = lean_array_uget(x_6, x_19);
x_21 = l_Std_DHashMap_Internal_AssocList_get_x3f___at_Lean_IR_ExpandResetReuse_isSelfSet___spec__1(x_5, x_20);
lean_dec(x_20);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = 0;
return x_22;
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
if (lean_obj_tag(x_23) == 5)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 2);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_nat_dec_eq(x_3, x_24);
lean_dec(x_24);
if (x_27 == 0)
{
uint8_t x_28; 
lean_dec(x_26);
lean_dec(x_25);
x_28 = 0;
return x_28;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_eq(x_25, x_4);
lean_dec(x_25);
if (x_29 == 0)
{
uint8_t x_30; 
lean_dec(x_26);
x_30 = 0;
return x_30;
}
else
{
uint8_t x_31; 
x_31 = lean_nat_dec_eq(x_26, x_2);
lean_dec(x_26);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_23);
x_32 = 0;
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_isSelfSSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_removeSelfSet___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_object* x_56; size_t x_57; size_t x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_2, 3);
x_57 = lean_array_size(x_56);
x_58 = 0;
x_59 = l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_removeSelfSet___spec__1(x_1, x_57, x_58, x_56);
lean_ctor_set(x_2, 3, x_59);
return x_2;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; size_t x_64; size_t x_65; lean_object* x_66; lean_object* x_67; 
x_60 = lean_ctor_get(x_2, 0);
x_61 = lean_ctor_get(x_2, 1);
x_62 = lean_ctor_get(x_2, 2);
x_63 = lean_ctor_get(x_2, 3);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_2);
x_64 = lean_array_size(x_63);
x_65 = 0;
x_66 = l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_removeSelfSet___spec__1(x_1, x_64, x_65, x_63);
x_67 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_67, 0, x_60);
lean_ctor_set(x_67, 1, x_61);
lean_ctor_set(x_67, 2, x_62);
lean_ctor_set(x_67, 3, x_66);
return x_67;
}
}
default: 
{
uint8_t x_68; 
x_68 = l_Lean_IR_FnBody_isTerminal(x_2);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = l_Lean_IR_FnBody_body(x_2);
x_70 = lean_box(13);
x_71 = l_Lean_IR_FnBody_setBody(x_2, x_70);
x_72 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_69);
x_73 = l_Lean_IR_FnBody_setBody(x_71, x_72);
return x_73;
}
else
{
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
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_removeSelfSet___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ExpandResetReuse_removeSelfSet(x_1, x_2);
lean_dec(x_1);
return x_3;
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
lean_object* x_65; size_t x_66; size_t x_67; lean_object* x_68; 
x_65 = lean_ctor_get(x_4, 3);
x_66 = lean_array_size(x_65);
x_67 = 0;
x_68 = l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_reuseToSet___spec__1(x_1, x_2, x_3, x_66, x_67, x_65);
lean_ctor_set(x_4, 3, x_68);
return x_4;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; lean_object* x_76; 
x_69 = lean_ctor_get(x_4, 0);
x_70 = lean_ctor_get(x_4, 1);
x_71 = lean_ctor_get(x_4, 2);
x_72 = lean_ctor_get(x_4, 3);
lean_inc(x_72);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_4);
x_73 = lean_array_size(x_72);
x_74 = 0;
x_75 = l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_reuseToSet___spec__1(x_1, x_2, x_3, x_73, x_74, x_72);
x_76 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_76, 0, x_69);
lean_ctor_set(x_76, 1, x_70);
lean_ctor_set(x_76, 2, x_71);
lean_ctor_set(x_76, 3, x_75);
return x_76;
}
}
default: 
{
uint8_t x_77; 
x_77 = l_Lean_IR_FnBody_isTerminal(x_4);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = l_Lean_IR_FnBody_body(x_4);
x_79 = lean_box(13);
x_80 = l_Lean_IR_FnBody_setBody(x_4, x_79);
x_81 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_78);
x_82 = l_Lean_IR_FnBody_setBody(x_80, x_81);
return x_82;
}
else
{
lean_dec(x_3);
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
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_reuseToSet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ExpandResetReuse_reuseToSet(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_mkFastPath(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_2);
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
lean_dec(x_5);
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
LEAN_EXPORT lean_object* l_Lean_IR_ExpandResetReuse_expand___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_IR_ExpandResetReuse_expand(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
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
switch (lean_obj_tag(x_5)) {
case 0:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_5, 1);
lean_dec(x_7);
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_free_object(x_5);
x_10 = l_Lean_IR_FnBody_body(x_1);
x_11 = l_Lean_IR_push(x_2, x_1);
x_1 = x_10;
x_2 = x_11;
goto _start;
}
else
{
lean_object* x_13; 
lean_dec(x_3);
x_13 = l_Lean_IR_reshape(x_2, x_1);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 0, x_13);
return x_5;
}
}
else
{
uint8_t x_14; 
lean_dec(x_5);
x_14 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_IR_FnBody_body(x_1);
x_16 = l_Lean_IR_push(x_2, x_1);
x_1 = x_15;
x_2 = x_16;
goto _start;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
x_18 = l_Lean_IR_reshape(x_2, x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_4);
return x_19;
}
}
}
case 1:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 3);
lean_inc(x_21);
x_22 = lean_ctor_get(x_5, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_5, 1);
lean_inc(x_23);
lean_dec(x_5);
lean_inc(x_21);
x_24 = l_Lean_IR_ExpandResetReuse_consumed(x_20, x_21);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_20);
x_25 = l_Lean_IR_push(x_2, x_1);
x_1 = x_21;
x_2 = x_25;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_1);
x_27 = l_Lean_IR_ExpandResetReuse_searchAndExpand___closed__1;
x_28 = l_Lean_IR_ExpandResetReuse_expand(x_27, x_2, x_20, x_22, x_23, x_21, x_3, x_4);
lean_dec(x_20);
return x_28;
}
}
case 2:
{
uint8_t x_29; 
lean_dec(x_5);
x_29 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lean_IR_FnBody_body(x_1);
x_31 = l_Lean_IR_push(x_2, x_1);
x_1 = x_30;
x_2 = x_31;
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_3);
x_33 = l_Lean_IR_reshape(x_2, x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_4);
return x_34;
}
}
case 5:
{
uint8_t x_35; 
lean_dec(x_5);
x_35 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = l_Lean_IR_FnBody_body(x_1);
x_37 = l_Lean_IR_push(x_2, x_1);
x_1 = x_36;
x_2 = x_37;
goto _start;
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_3);
x_39 = l_Lean_IR_reshape(x_2, x_1);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_4);
return x_40;
}
}
case 10:
{
uint8_t x_41; 
lean_dec(x_5);
x_41 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = l_Lean_IR_FnBody_body(x_1);
x_43 = l_Lean_IR_push(x_2, x_1);
x_1 = x_42;
x_2 = x_43;
goto _start;
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_3);
x_45 = l_Lean_IR_reshape(x_2, x_1);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_4);
return x_46;
}
}
case 11:
{
uint8_t x_47; 
lean_dec(x_5);
x_47 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = l_Lean_IR_FnBody_body(x_1);
x_49 = l_Lean_IR_push(x_2, x_1);
x_1 = x_48;
x_2 = x_49;
goto _start;
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_3);
x_51 = l_Lean_IR_reshape(x_2, x_1);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_4);
return x_52;
}
}
case 12:
{
uint8_t x_53; 
lean_dec(x_5);
x_53 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = l_Lean_IR_FnBody_body(x_1);
x_55 = l_Lean_IR_push(x_2, x_1);
x_1 = x_54;
x_2 = x_55;
goto _start;
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_3);
x_57 = l_Lean_IR_reshape(x_2, x_1);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_4);
return x_58;
}
}
default: 
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_5);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_ctor_get(x_5, 1);
lean_dec(x_60);
x_61 = lean_ctor_get(x_5, 0);
lean_dec(x_61);
x_62 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_free_object(x_5);
x_63 = l_Lean_IR_FnBody_body(x_1);
x_64 = l_Lean_IR_push(x_2, x_1);
x_1 = x_63;
x_2 = x_64;
goto _start;
}
else
{
lean_object* x_66; 
lean_dec(x_3);
x_66 = l_Lean_IR_reshape(x_2, x_1);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 1, x_4);
lean_ctor_set(x_5, 0, x_66);
return x_5;
}
}
else
{
uint8_t x_67; 
lean_dec(x_5);
x_67 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = l_Lean_IR_FnBody_body(x_1);
x_69 = l_Lean_IR_push(x_2, x_1);
x_1 = x_68;
x_2 = x_69;
goto _start;
}
else
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_3);
x_71 = l_Lean_IR_reshape(x_2, x_1);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_4);
return x_72;
}
}
}
}
}
case 1:
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_1);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_74 = lean_ctor_get(x_1, 2);
x_75 = lean_ctor_get(x_1, 3);
x_76 = l_Lean_IR_ExpandResetReuse_eraseProjIncFor___closed__1;
lean_inc(x_3);
x_77 = l_Lean_IR_ExpandResetReuse_searchAndExpand(x_74, x_76, x_3, x_4);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_box(13);
lean_ctor_set(x_1, 3, x_80);
lean_ctor_set(x_1, 2, x_78);
x_81 = l_Lean_IR_push(x_2, x_1);
x_1 = x_75;
x_2 = x_81;
x_4 = x_79;
goto _start;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_83 = lean_ctor_get(x_1, 0);
x_84 = lean_ctor_get(x_1, 1);
x_85 = lean_ctor_get(x_1, 2);
x_86 = lean_ctor_get(x_1, 3);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_1);
x_87 = l_Lean_IR_ExpandResetReuse_eraseProjIncFor___closed__1;
lean_inc(x_3);
x_88 = l_Lean_IR_ExpandResetReuse_searchAndExpand(x_85, x_87, x_3, x_4);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_box(13);
x_92 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_92, 0, x_83);
lean_ctor_set(x_92, 1, x_84);
lean_ctor_set(x_92, 2, x_89);
lean_ctor_set(x_92, 3, x_91);
x_93 = l_Lean_IR_push(x_2, x_92);
x_1 = x_86;
x_2 = x_93;
x_4 = x_90;
goto _start;
}
}
case 10:
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_1);
if (x_95 == 0)
{
lean_object* x_96; size_t x_97; size_t x_98; lean_object* x_99; uint8_t x_100; 
x_96 = lean_ctor_get(x_1, 3);
x_97 = lean_array_size(x_96);
x_98 = 0;
x_99 = l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_searchAndExpand___spec__1(x_97, x_98, x_96, x_3, x_4);
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_99, 0);
lean_ctor_set(x_1, 3, x_101);
x_102 = l_Lean_IR_reshape(x_2, x_1);
lean_ctor_set(x_99, 0, x_102);
return x_99;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_103 = lean_ctor_get(x_99, 0);
x_104 = lean_ctor_get(x_99, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_99);
lean_ctor_set(x_1, 3, x_103);
x_105 = l_Lean_IR_reshape(x_2, x_1);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; size_t x_111; size_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_107 = lean_ctor_get(x_1, 0);
x_108 = lean_ctor_get(x_1, 1);
x_109 = lean_ctor_get(x_1, 2);
x_110 = lean_ctor_get(x_1, 3);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_1);
x_111 = lean_array_size(x_110);
x_112 = 0;
x_113 = l_Array_mapMUnsafe_map___at_Lean_IR_ExpandResetReuse_searchAndExpand___spec__1(x_111, x_112, x_110, x_3, x_4);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_116 = x_113;
} else {
 lean_dec_ref(x_113);
 x_116 = lean_box(0);
}
x_117 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_117, 0, x_107);
lean_ctor_set(x_117, 1, x_108);
lean_ctor_set(x_117, 2, x_109);
lean_ctor_set(x_117, 3, x_114);
x_118 = l_Lean_IR_reshape(x_2, x_117);
if (lean_is_scalar(x_116)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_116;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_115);
return x_119;
}
}
default: 
{
uint8_t x_120; 
x_120 = l_Lean_IR_FnBody_isTerminal(x_1);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; 
x_121 = l_Lean_IR_FnBody_body(x_1);
x_122 = l_Lean_IR_push(x_2, x_1);
x_1 = x_121;
x_2 = x_122;
goto _start;
}
else
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_3);
x_124 = l_Lean_IR_reshape(x_2, x_1);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_4);
return x_125;
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
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_NormIds(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_FreeVars(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_ExpandResetReuse(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_IR_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_NormIds(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_FreeVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_ExpandResetReuse_mkProjMap___closed__1 = _init_l_Lean_IR_ExpandResetReuse_mkProjMap___closed__1();
lean_mark_persistent(l_Lean_IR_ExpandResetReuse_mkProjMap___closed__1);
l_Lean_IR_ExpandResetReuse_mkProjMap___closed__2 = _init_l_Lean_IR_ExpandResetReuse_mkProjMap___closed__2();
lean_mark_persistent(l_Lean_IR_ExpandResetReuse_mkProjMap___closed__2);
l_Lean_IR_ExpandResetReuse_mkProjMap___closed__3 = _init_l_Lean_IR_ExpandResetReuse_mkProjMap___closed__3();
lean_mark_persistent(l_Lean_IR_ExpandResetReuse_mkProjMap___closed__3);
l_Lean_IR_ExpandResetReuse_eraseProjIncFor___closed__1 = _init_l_Lean_IR_ExpandResetReuse_eraseProjIncFor___closed__1();
lean_mark_persistent(l_Lean_IR_ExpandResetReuse_eraseProjIncFor___closed__1);
l_Lean_IR_ExpandResetReuse_searchAndExpand___closed__1 = _init_l_Lean_IR_ExpandResetReuse_searchAndExpand___closed__1();
lean_mark_persistent(l_Lean_IR_ExpandResetReuse_searchAndExpand___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
