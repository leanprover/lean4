// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Rewrite
// Imports: Lean.Elab.Tactic.Simp Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Basic Lean.Elab.Tactic.BVDecide.Frontend.Attr
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_Simp_getSEvalSimprocs___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_bvNormalizeExt;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__6;
extern lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_bvNormalizeSimprocExt;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___closed__0;
uint8_t l_Array_isEmpty___redArg(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpGoal(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__3;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_MVarId_getNondepPropHyps_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__4;
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Meta_getSimpCongrTheorems___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__11;
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__7;
lean_object* l_Lean_Meta_getSEvalTheorems___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getPropHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__8;
lean_object* l_Lean_Meta_Simp_mkContext___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___closed__1;
uint64_t l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_SimprocExtension_getSimprocs___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__0;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__5;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_MVarId_getNondepPropHyps_spec__6___redArg(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__1;
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__9;
lean_object* l_Lean_Meta_SimpExtension_getTheorems___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps___lam__0___closed__0;
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__10;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_2, x_3);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; size_t x_28; size_t x_29; size_t x_30; size_t x_31; size_t x_32; lean_object* x_33; uint8_t x_34; 
x_14 = lean_st_ref_get(x_5, x_6);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_array_uget(x_1, x_2);
x_20 = lean_array_get_size(x_18);
x_21 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_19);
x_22 = 32;
x_23 = lean_uint64_shift_right(x_21, x_22);
x_24 = lean_uint64_xor(x_21, x_23);
x_25 = 16;
x_26 = lean_uint64_shift_right(x_24, x_25);
x_27 = lean_uint64_xor(x_24, x_26);
x_28 = lean_uint64_to_usize(x_27);
x_29 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_30 = 1;
x_31 = lean_usize_sub(x_29, x_30);
x_32 = lean_usize_land(x_28, x_31);
x_33 = lean_array_uget(x_18, x_32);
lean_dec(x_18);
x_34 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_MVarId_getNondepPropHyps_spec__0___redArg(x_19, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_array_push(x_4, x_19);
x_7 = x_35;
x_8 = x_17;
goto block_12;
}
else
{
lean_dec(x_19);
x_7 = x_4;
x_8 = x_17;
goto block_12;
}
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_4);
lean_ctor_set(x_36, 1, x_6);
return x_36;
}
block_12:
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_7;
x_6 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_6, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_18; 
x_18 = lean_usize_dec_eq(x_2, x_3);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; size_t x_37; lean_object* x_38; uint8_t x_39; 
x_19 = lean_st_ref_get(x_6, x_11);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_array_uget(x_1, x_2);
x_25 = lean_array_get_size(x_23);
x_26 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_24);
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
x_38 = lean_array_uget(x_23, x_37);
lean_dec(x_23);
x_39 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_MVarId_getNondepPropHyps_spec__0___redArg(x_24, x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_array_push(x_4, x_24);
x_12 = x_40;
x_13 = x_22;
goto block_17;
}
else
{
lean_dec(x_24);
x_12 = x_4;
x_13 = x_22;
goto block_17;
}
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_4);
lean_ctor_set(x_41, 1, x_11);
return x_41;
}
block_17:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = 1;
x_15 = lean_usize_add(x_2, x_14);
x_16 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0___redArg(x_1, x_15, x_3, x_12, x_6, x_13);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__2___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__2___redArg___lam__0), 8, 3);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_4);
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp___redArg(x_1, x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps___lam__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_8 = l_Lean_Meta_getPropHyps(x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get_size(x_10);
x_14 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps___lam__0___closed__0;
x_15 = lean_nat_dec_lt(x_12, x_13);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_13, x_13);
if (x_16 == 0)
{
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
lean_free_object(x_8);
x_17 = 0;
x_18 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_19 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__0(x_10, x_17, x_18, x_14, x_1, x_2, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_10);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_array_get_size(x_20);
x_24 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps___lam__0___closed__0;
x_25 = lean_nat_dec_lt(x_22, x_23);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_21);
return x_26;
}
else
{
uint8_t x_27; 
x_27 = lean_nat_dec_le(x_23, x_23);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_21);
return x_28;
}
else
{
size_t x_29; size_t x_30; lean_object* x_31; 
x_29 = 0;
x_30 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_31 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__0(x_20, x_29, x_30, x_24, x_1, x_2, x_3, x_4, x_5, x_6, x_21);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_20);
return x_31;
}
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps___lam__0___boxed), 7, 0);
x_10 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__2___redArg(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0___redArg(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__0_spec__0(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__0(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; size_t x_35; size_t x_36; size_t x_37; size_t x_38; size_t x_39; lean_object* x_40; uint8_t x_41; 
lean_dec(x_4);
x_8 = lean_st_ref_take(x_5, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_9, 2);
lean_inc(x_13);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 lean_ctor_release(x_9, 2);
 x_14 = x_9;
} else {
 lean_dec_ref(x_9);
 x_14 = lean_box(0);
}
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
x_17 = lean_array_uget(x_1, x_2);
x_18 = lean_box(0);
x_27 = lean_array_get_size(x_16);
x_28 = l_Lean_hashFVarId____x40_Lean_Expr___hyg_1561_(x_17);
x_29 = 32;
x_30 = lean_uint64_shift_right(x_28, x_29);
x_31 = lean_uint64_xor(x_28, x_30);
x_32 = 16;
x_33 = lean_uint64_shift_right(x_31, x_32);
x_34 = lean_uint64_xor(x_31, x_33);
x_35 = lean_uint64_to_usize(x_34);
x_36 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_37 = 1;
x_38 = lean_usize_sub(x_36, x_37);
x_39 = lean_usize_land(x_35, x_38);
x_40 = lean_array_uget(x_16, x_39);
x_41 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_MVarId_getNondepPropHyps_spec__0___redArg(x_17, x_40);
if (x_41 == 0)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_10);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_43 = lean_ctor_get(x_10, 1);
lean_dec(x_43);
x_44 = lean_ctor_get(x_10, 0);
lean_dec(x_44);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_add(x_15, x_45);
lean_dec(x_15);
x_47 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_47, 0, x_17);
lean_ctor_set(x_47, 1, x_18);
lean_ctor_set(x_47, 2, x_40);
x_48 = lean_array_uset(x_16, x_39, x_47);
x_49 = lean_unsigned_to_nat(4u);
x_50 = lean_nat_mul(x_46, x_49);
x_51 = lean_unsigned_to_nat(3u);
x_52 = lean_nat_div(x_50, x_51);
lean_dec(x_50);
x_53 = lean_array_get_size(x_48);
x_54 = lean_nat_dec_le(x_52, x_53);
lean_dec(x_53);
lean_dec(x_52);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_MVarId_getNondepPropHyps_spec__6___redArg(x_48);
lean_ctor_set(x_10, 1, x_55);
lean_ctor_set(x_10, 0, x_46);
x_19 = x_10;
goto block_26;
}
else
{
lean_ctor_set(x_10, 1, x_48);
lean_ctor_set(x_10, 0, x_46);
x_19 = x_10;
goto block_26;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_dec(x_10);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_add(x_15, x_56);
lean_dec(x_15);
x_58 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_58, 0, x_17);
lean_ctor_set(x_58, 1, x_18);
lean_ctor_set(x_58, 2, x_40);
x_59 = lean_array_uset(x_16, x_39, x_58);
x_60 = lean_unsigned_to_nat(4u);
x_61 = lean_nat_mul(x_57, x_60);
x_62 = lean_unsigned_to_nat(3u);
x_63 = lean_nat_div(x_61, x_62);
lean_dec(x_61);
x_64 = lean_array_get_size(x_59);
x_65 = lean_nat_dec_le(x_63, x_64);
lean_dec(x_64);
lean_dec(x_63);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_MVarId_getNondepPropHyps_spec__6___redArg(x_59);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_57);
lean_ctor_set(x_67, 1, x_66);
x_19 = x_67;
goto block_26;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_57);
lean_ctor_set(x_68, 1, x_59);
x_19 = x_68;
goto block_26;
}
}
}
else
{
lean_dec(x_40);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_19 = x_10;
goto block_26;
}
block_26:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; size_t x_24; 
if (lean_is_scalar(x_14)) {
 x_20 = lean_alloc_ctor(0, 3, 0);
} else {
 x_20 = x_14;
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_12);
lean_ctor_set(x_20, 2, x_13);
x_21 = lean_st_ref_set(x_5, x_20, x_11);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = 1;
x_24 = lean_usize_add(x_2, x_23);
x_2 = x_24;
x_4 = x_18;
x_6 = x_22;
goto _start;
}
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_4);
lean_ctor_set(x_69, 1, x_6);
return x_69;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_spec__0___redArg(x_1, x_2, x_3, x_4, x_6, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_getPropHyps(x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_array_get_size(x_11);
x_14 = lean_box(0);
x_15 = lean_nat_dec_lt(x_1, x_13);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_13, x_13);
if (x_16 == 0)
{
lean_dec(x_13);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
lean_free_object(x_9);
x_17 = 0;
x_18 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_19 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_spec__0___redArg(x_11, x_17, x_18, x_14, x_3, x_12);
lean_dec(x_11);
return x_19;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_9, 0);
x_21 = lean_ctor_get(x_9, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_9);
x_22 = lean_array_get_size(x_20);
x_23 = lean_box(0);
x_24 = lean_nat_dec_lt(x_1, x_22);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_22);
lean_dec(x_20);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
else
{
uint8_t x_26; 
x_26 = lean_nat_dec_le(x_22, x_22);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_22);
lean_dec(x_20);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_21);
return x_27;
}
else
{
size_t x_28; size_t x_29; lean_object* x_30; 
x_28 = 0;
x_29 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_30 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_spec__0___redArg(x_20, x_28, x_29, x_23, x_3, x_21);
lean_dec(x_20);
return x_30;
}
}
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_9);
if (x_31 == 0)
{
return x_9;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_9, 0);
x_33 = lean_ctor_get(x_9, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_9);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_bvNormalizeExt;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_bvNormalizeSimprocExt;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__4;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__9() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__7;
x_4 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__8;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__9;
x_2 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__6;
x_3 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__4;
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_2);
lean_ctor_set(x_4, 3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__10;
x_2 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__5;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_9 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__0;
x_10 = l_Lean_Meta_SimpExtension_getTheorems___redArg(x_9, x_7, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__1;
x_14 = l_Lean_Meta_Simp_SimprocExtension_getSimprocs___redArg(x_13, x_7, x_12);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Meta_getSEvalTheorems___redArg(x_7, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Meta_Simp_getSEvalSimprocs___redArg(x_7, x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Meta_getSimpCongrTheorems___redArg(x_7, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_2, 1);
lean_inc(x_26);
x_27 = lean_unsigned_to_nat(2u);
x_28 = lean_box(0);
x_29 = lean_box(1);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 23);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_27);
x_32 = lean_unbox(x_28);
lean_ctor_set_uint8(x_31, sizeof(void*)*2, x_32);
x_33 = lean_unbox(x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*2 + 1, x_33);
x_34 = lean_unbox(x_28);
lean_ctor_set_uint8(x_31, sizeof(void*)*2 + 2, x_34);
x_35 = lean_unbox(x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*2 + 3, x_35);
x_36 = lean_unbox(x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*2 + 4, x_36);
x_37 = lean_unbox(x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*2 + 5, x_37);
x_38 = lean_unbox(x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*2 + 6, x_38);
x_39 = lean_unbox(x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*2 + 7, x_39);
x_40 = lean_unbox(x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*2 + 8, x_40);
x_41 = lean_unbox(x_28);
lean_ctor_set_uint8(x_31, sizeof(void*)*2 + 9, x_41);
x_42 = lean_unbox(x_28);
lean_ctor_set_uint8(x_31, sizeof(void*)*2 + 10, x_42);
x_43 = lean_unbox(x_28);
lean_ctor_set_uint8(x_31, sizeof(void*)*2 + 11, x_43);
x_44 = lean_unbox(x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*2 + 12, x_44);
x_45 = lean_unbox(x_28);
lean_ctor_set_uint8(x_31, sizeof(void*)*2 + 13, x_45);
x_46 = lean_unbox(x_28);
lean_ctor_set_uint8(x_31, sizeof(void*)*2 + 14, x_46);
x_47 = lean_unbox(x_28);
lean_ctor_set_uint8(x_31, sizeof(void*)*2 + 15, x_47);
x_48 = lean_unbox(x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*2 + 16, x_48);
x_49 = lean_unbox(x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*2 + 17, x_49);
x_50 = lean_unbox(x_28);
lean_ctor_set_uint8(x_31, sizeof(void*)*2 + 18, x_50);
x_51 = lean_unbox(x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*2 + 19, x_51);
x_52 = lean_unbox(x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*2 + 20, x_52);
x_53 = lean_unbox(x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*2 + 21, x_53);
x_54 = lean_unbox(x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*2 + 22, x_54);
x_55 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__2;
x_56 = lean_array_push(x_55, x_11);
x_57 = lean_array_push(x_56, x_18);
x_58 = l_Lean_Meta_Simp_mkContext___redArg(x_31, x_57, x_24, x_4, x_7, x_25);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_61 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_60);
if (lean_obj_tag(x_61) == 0)
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = lean_ctor_get(x_61, 0);
x_64 = lean_ctor_get(x_61, 1);
x_65 = l_Array_isEmpty___redArg(x_63);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; 
lean_free_object(x_61);
x_66 = lean_array_push(x_55, x_15);
x_67 = lean_array_push(x_66, x_21);
x_68 = lean_box(0);
x_69 = lean_unsigned_to_nat(0u);
x_70 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__11;
x_71 = lean_unbox(x_29);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_72 = l_Lean_Meta_simpGoal(x_1, x_59, x_67, x_68, x_71, x_63, x_70, x_4, x_5, x_6, x_7, x_64);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec(x_73);
if (lean_obj_tag(x_74) == 0)
{
uint8_t x_75; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_75 = !lean_is_exclusive(x_72);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_72, 0);
lean_dec(x_76);
x_77 = lean_box(0);
lean_ctor_set(x_72, 0, x_77);
return x_72;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_72, 1);
lean_inc(x_78);
lean_dec(x_72);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
else
{
uint8_t x_81; 
x_81 = !lean_is_exclusive(x_74);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_74, 0);
x_83 = lean_ctor_get(x_72, 1);
lean_inc(x_83);
lean_dec(x_72);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__0___boxed), 8, 1);
lean_closure_set(x_85, 0, x_69);
lean_inc(x_84);
x_86 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__2___redArg(x_84, x_85, x_2, x_3, x_4, x_5, x_6, x_7, x_83);
if (lean_obj_tag(x_86) == 0)
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_86, 0);
lean_dec(x_88);
lean_ctor_set(x_74, 0, x_84);
lean_ctor_set(x_86, 0, x_74);
return x_86;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_86, 1);
lean_inc(x_89);
lean_dec(x_86);
lean_ctor_set(x_74, 0, x_84);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_74);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
else
{
uint8_t x_91; 
lean_dec(x_84);
lean_free_object(x_74);
x_91 = !lean_is_exclusive(x_86);
if (x_91 == 0)
{
return x_86;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_86, 0);
x_93 = lean_ctor_get(x_86, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_86);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_95 = lean_ctor_get(x_74, 0);
lean_inc(x_95);
lean_dec(x_74);
x_96 = lean_ctor_get(x_72, 1);
lean_inc(x_96);
lean_dec(x_72);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__0___boxed), 8, 1);
lean_closure_set(x_98, 0, x_69);
lean_inc(x_97);
x_99 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__2___redArg(x_97, x_98, x_2, x_3, x_4, x_5, x_6, x_7, x_96);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_101 = x_99;
} else {
 lean_dec_ref(x_99);
 x_101 = lean_box(0);
}
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_97);
if (lean_is_scalar(x_101)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_101;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_100);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_97);
x_104 = lean_ctor_get(x_99, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_99, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_106 = x_99;
} else {
 lean_dec_ref(x_99);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_108 = !lean_is_exclusive(x_72);
if (x_108 == 0)
{
return x_72;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_72, 0);
x_110 = lean_ctor_get(x_72, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_72);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
lean_object* x_112; 
lean_dec(x_63);
lean_dec(x_59);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_1);
lean_ctor_set(x_61, 0, x_112);
return x_61;
}
}
else
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_113 = lean_ctor_get(x_61, 0);
x_114 = lean_ctor_get(x_61, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_61);
x_115 = l_Array_isEmpty___redArg(x_113);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; 
x_116 = lean_array_push(x_55, x_15);
x_117 = lean_array_push(x_116, x_21);
x_118 = lean_box(0);
x_119 = lean_unsigned_to_nat(0u);
x_120 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__11;
x_121 = lean_unbox(x_29);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_122 = l_Lean_Meta_simpGoal(x_1, x_59, x_117, x_118, x_121, x_113, x_120, x_4, x_5, x_6, x_7, x_114);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
lean_dec(x_123);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_125 = lean_ctor_get(x_122, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_126 = x_122;
} else {
 lean_dec_ref(x_122);
 x_126 = lean_box(0);
}
x_127 = lean_box(0);
if (lean_is_scalar(x_126)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_126;
}
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_125);
return x_128;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_129 = lean_ctor_get(x_124, 0);
lean_inc(x_129);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 x_130 = x_124;
} else {
 lean_dec_ref(x_124);
 x_130 = lean_box(0);
}
x_131 = lean_ctor_get(x_122, 1);
lean_inc(x_131);
lean_dec(x_122);
x_132 = lean_ctor_get(x_129, 1);
lean_inc(x_132);
lean_dec(x_129);
x_133 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__0___boxed), 8, 1);
lean_closure_set(x_133, 0, x_119);
lean_inc(x_132);
x_134 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps_spec__2___redArg(x_132, x_133, x_2, x_3, x_4, x_5, x_6, x_7, x_131);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_136 = x_134;
} else {
 lean_dec_ref(x_134);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_137 = lean_alloc_ctor(1, 1, 0);
} else {
 x_137 = x_130;
}
lean_ctor_set(x_137, 0, x_132);
if (lean_is_scalar(x_136)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_136;
}
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_135);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_132);
lean_dec(x_130);
x_139 = lean_ctor_get(x_134, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_134, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_141 = x_134;
} else {
 lean_dec_ref(x_134);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_143 = lean_ctor_get(x_122, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_122, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_145 = x_122;
} else {
 lean_dec_ref(x_122);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_143);
lean_ctor_set(x_146, 1, x_144);
return x_146;
}
}
else
{
lean_object* x_147; lean_object* x_148; 
lean_dec(x_113);
lean_dec(x_59);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_147 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_147, 0, x_1);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_114);
return x_148;
}
}
}
else
{
uint8_t x_149; 
lean_dec(x_59);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_149 = !lean_is_exclusive(x_61);
if (x_149 == 0)
{
return x_61;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_61, 0);
x_151 = lean_ctor_get(x_61, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_61);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("rewriteRules", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1), 8, 0);
x_2 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_spec__0___redArg(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_spec__0(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
lean_object* initialize_Lean_Elab_Tactic_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Attr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Rewrite(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_Attr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps___lam__0___closed__0 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps___lam__0___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass_getHyps___lam__0___closed__0);
l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__0 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__0);
l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__1 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__1);
l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__2 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__2);
l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__3 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__3);
l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__4 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__4();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__4);
l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__5 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__5();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__5);
l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__6 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__6();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__6);
l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__7 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__7();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__7);
l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__8 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__8();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__8);
l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__9 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__9();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__9);
l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__10 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__10();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__10);
l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__11 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__11();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___lam__1___closed__11);
l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___closed__0 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___closed__0();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___closed__0);
l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___closed__1 = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass___closed__1);
l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_rewriteRulesPass);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
