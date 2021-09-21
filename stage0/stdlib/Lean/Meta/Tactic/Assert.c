// Lean compiler output
// Module: Lean.Meta.Tactic.Assert
// Imports: Init Lean.Meta.Tactic.Util Lean.Meta.Tactic.FVarSubst Lean.Meta.Tactic.Intro Lean.Meta.Tactic.Revert
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
LEAN_EXPORT lean_object* l_Lean_Meta_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_assertHypotheses___spec__1(lean_object*, size_t, size_t, lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_assertHypotheses___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Meta_assert___closed__2;
lean_object* l_Array_append___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_assertHypotheses___closed__2;
static lean_object* l_Lean_Meta_assertHypotheses___closed__1;
lean_object* lean_local_ctx_erase(lean_object*, lean_object*);
size_t l_USize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_define(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_get_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_assertHypotheses___spec__2(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_assertAfter___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_PersistentArray_foldlM___at_Lean_Meta_assertAfter___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_assert___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_shiftRight(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_assertAfter___spec__10(lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Meta_assert___closed__1;
lean_object* l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1(size_t, size_t, lean_object*);
static lean_object* l_Lean_Meta_assertAfter___closed__2;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_assertAfter___spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_assertAfter___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_assertAfter___spec__6(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_Meta_assertAfter___spec__3(lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_assertAfter___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_foldAux___at_Lean_Meta_assertAfter___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_assertHypotheses___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_assert___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t l_USize_shiftLeft(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_define___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_assertHypotheses___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_Meta_getLocalInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_assertAfter___spec__5(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_assertHypotheses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_assertAfter___spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_Meta_assertAfter___spec__4(lean_object*, lean_object*);
size_t l_USize_land(size_t, size_t);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_assertAfter___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_assertExt___lambda__1___closed__2;
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_assertHypotheses___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_assertExt___lambda__1___closed__1;
extern lean_object* l_Lean_instInhabitedFVarId;
LEAN_EXPORT lean_object* l_Lean_Meta_assertExt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_index(lean_object*);
lean_object* l_Lean_Meta_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_assertExt___lambda__1___closed__3;
LEAN_EXPORT lean_object* l_Nat_foldAux___at_Lean_Meta_assertAfter___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at_Lean_Meta_assertAfter___spec__1(lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___at___private_Lean_Class_0__Lean_checkOutParam___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_define___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_assertExt___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_define___closed__1;
lean_object* l_Lean_mkLet(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_assertAfter___spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_object* l_Lean_Meta_assertAfter___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_define___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_assertAfter___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_Meta_assertAfter___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_assertAfter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_Meta_assertAfter___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_assertAfter___lambda__1___closed__2;
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Std_instInhabitedPersistentArrayNode(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_assertAfter___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isLet(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_assert___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_7);
lean_inc(x_1);
x_11 = l_Lean_Meta_checkNotAssigned(x_1, x_2, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
lean_inc(x_1);
x_13 = l_Lean_Meta_getMVarTag(x_1, x_6, x_7, x_8, x_9, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_1);
x_16 = l_Lean_Meta_getMVarType(x_1, x_6, x_7, x_8, x_9, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 0;
x_20 = l_Lean_mkForall(x_3, x_19, x_4, x_17);
lean_inc(x_6);
x_21 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_20, x_14, x_6, x_7, x_8, x_9, x_18);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_22);
x_24 = l_Lean_mkApp(x_22, x_5);
x_25 = l_Lean_Meta_assignExprMVar(x_1, x_24, x_6, x_7, x_8, x_9, x_23);
lean_dec(x_7);
lean_dec(x_6);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = l_Lean_Expr_mvarId_x21(x_22);
lean_dec(x_22);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = l_Lean_Expr_mvarId_x21(x_22);
lean_dec(x_22);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_16);
if (x_32 == 0)
{
return x_16;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_16, 0);
x_34 = lean_ctor_get(x_16, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_16);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_13);
if (x_36 == 0)
{
return x_13;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_13, 0);
x_38 = lean_ctor_get(x_13, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_13);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_11);
if (x_40 == 0)
{
return x_11;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_11, 0);
x_42 = lean_ctor_get(x_11, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_11);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
static lean_object* _init_l_Lean_Meta_assert___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("assert");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_assert___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_assert___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_assert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_Meta_assert___closed__2;
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_assert___lambda__1___boxed), 10, 5);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_10);
lean_closure_set(x_11, 2, x_2);
lean_closure_set(x_11, 3, x_3);
lean_closure_set(x_11, 4, x_4);
x_12 = l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(x_1, x_11, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_assert___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_assert___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_define___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_7);
lean_inc(x_1);
x_11 = l_Lean_Meta_checkNotAssigned(x_1, x_2, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
lean_inc(x_1);
x_13 = l_Lean_Meta_getMVarTag(x_1, x_6, x_7, x_8, x_9, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_1);
x_16 = l_Lean_Meta_getMVarType(x_1, x_6, x_7, x_8, x_9, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = 0;
x_20 = l_Lean_mkLet(x_3, x_4, x_5, x_17, x_19);
lean_inc(x_6);
x_21 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_20, x_14, x_6, x_7, x_8, x_9, x_18);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_22);
x_24 = l_Lean_Meta_assignExprMVar(x_1, x_22, x_6, x_7, x_8, x_9, x_23);
lean_dec(x_7);
lean_dec(x_6);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
x_27 = l_Lean_Expr_mvarId_x21(x_22);
lean_dec(x_22);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 1);
lean_inc(x_28);
lean_dec(x_24);
x_29 = l_Lean_Expr_mvarId_x21(x_22);
lean_dec(x_22);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_16);
if (x_31 == 0)
{
return x_16;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_16, 0);
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_16);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_13);
if (x_35 == 0)
{
return x_13;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_13, 0);
x_37 = lean_ctor_get(x_13, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_13);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_11);
if (x_39 == 0)
{
return x_11;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_11, 0);
x_41 = lean_ctor_get(x_11, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_11);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
static lean_object* _init_l_Lean_Meta_define___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("define");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_define___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_define___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_define(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_Meta_define___closed__2;
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_define___lambda__1___boxed), 10, 5);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_10);
lean_closure_set(x_11, 2, x_2);
lean_closure_set(x_11, 3, x_3);
lean_closure_set(x_11, 4, x_4);
x_12 = l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(x_1, x_11, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_define___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_define___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_assertExt___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Eq");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_assertExt___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_assertExt___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_assertExt___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_mkBVar(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_assertExt___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_8);
lean_inc(x_1);
x_12 = l_Lean_Meta_checkNotAssigned(x_1, x_2, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_1);
x_14 = l_Lean_Meta_getMVarTag(x_1, x_7, x_8, x_9, x_10, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_1);
x_17 = l_Lean_Meta_getMVarType(x_1, x_7, x_8, x_9, x_10, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
x_20 = l_Lean_Meta_getLevel(x_3, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_Meta_assertExt___lambda__1___closed__2;
x_26 = l_Lean_mkConst(x_25, x_24);
x_27 = l_Lean_Meta_assertExt___lambda__1___closed__3;
lean_inc(x_4);
lean_inc(x_3);
x_28 = l_Lean_mkApp3(x_26, x_3, x_27, x_4);
x_29 = 0;
x_30 = l_Lean_mkForall(x_5, x_29, x_28, x_18);
x_31 = l_Lean_mkForall(x_6, x_29, x_3, x_30);
lean_inc(x_7);
x_32 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_31, x_15, x_7, x_8, x_9, x_10, x_22);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_4);
x_35 = l_Lean_Meta_mkEqRefl(x_4, x_7, x_8, x_9, x_10, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_33);
x_38 = l_Lean_mkAppB(x_33, x_4, x_36);
x_39 = l_Lean_Meta_assignExprMVar(x_1, x_38, x_7, x_8, x_9, x_10, x_37);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
x_42 = l_Lean_Expr_mvarId_x21(x_33);
lean_dec(x_33);
lean_ctor_set(x_39, 0, x_42);
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = l_Lean_Expr_mvarId_x21(x_33);
lean_dec(x_33);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_33);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_35);
if (x_46 == 0)
{
return x_35;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_35, 0);
x_48 = lean_ctor_get(x_35, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_35);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_20);
if (x_50 == 0)
{
return x_20;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_20, 0);
x_52 = lean_ctor_get(x_20, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_20);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_17);
if (x_54 == 0)
{
return x_17;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_17, 0);
x_56 = lean_ctor_get(x_17, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_17);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_14);
if (x_58 == 0)
{
return x_14;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_14, 0);
x_60 = lean_ctor_get(x_14, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_14);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_12);
if (x_62 == 0)
{
return x_12;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_12, 0);
x_64 = lean_ctor_get(x_12, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_12);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_assertExt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Meta_assert___closed__2;
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_assertExt___lambda__1), 11, 6);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
lean_closure_set(x_12, 2, x_3);
lean_closure_set(x_12, 3, x_4);
lean_closure_set(x_12, 4, x_5);
lean_closure_set(x_12, 5, x_2);
x_13 = l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(x_1, x_12, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_assertAfter___spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_Meta_assertAfter___spec__4(x_6, x_4);
x_8 = 1;
x_9 = x_2 + x_8;
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_assertAfter___spec__6(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = 1;
x_8 = x_2 + x_7;
if (lean_obj_tag(x_6) == 0)
{
x_2 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_Lean_LocalDecl_fvarId(x_10);
lean_dec(x_10);
x_12 = lean_array_push(x_4, x_11);
x_2 = x_8;
x_4 = x_12;
goto _start;
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_Meta_assertAfter___spec__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_array_get_size(x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
else
{
uint8_t x_7; 
x_7 = lean_nat_dec_le(x_4, x_4);
if (x_7 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
else
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_10 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_assertAfter___spec__5(x_3, x_8, x_9, x_2);
lean_dec(x_3);
return x_10;
}
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_array_get_size(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_lt(x_13, x_12);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_11);
return x_2;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_12, x_12);
if (x_15 == 0)
{
lean_dec(x_12);
lean_dec(x_11);
return x_2;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_18 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_assertAfter___spec__6(x_11, x_16, x_17, x_2);
lean_dec(x_11);
return x_18;
}
}
}
}
}
static lean_object* _init_l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_Meta_assertAfter___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Std_instInhabitedPersistentArrayNode(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_Meta_assertAfter___spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = x_2 >> x_3 % (sizeof(size_t) * 8);
x_7 = lean_usize_to_nat(x_6);
x_8 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_Meta_assertAfter___spec__3___closed__1;
x_9 = lean_array_get(x_8, x_5, x_7);
x_10 = 1;
x_11 = x_10 << x_3 % (sizeof(size_t) * 8);
x_12 = x_11 - x_10;
x_13 = x_2 & x_12;
x_14 = 5;
x_15 = x_3 - x_14;
x_16 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_Meta_assertAfter___spec__3(x_9, x_13, x_15, x_4);
lean_dec(x_9);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_7, x_17);
lean_dec(x_7);
x_19 = lean_array_get_size(x_5);
x_20 = lean_nat_dec_lt(x_18, x_19);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_18);
return x_16;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_19, x_19);
if (x_21 == 0)
{
lean_dec(x_19);
lean_dec(x_18);
return x_16;
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; 
x_22 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_23 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_24 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_assertAfter___spec__5(x_5, x_22, x_23, x_16);
return x_24;
}
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_usize_to_nat(x_2);
x_27 = lean_array_get_size(x_25);
x_28 = lean_nat_dec_lt(x_26, x_27);
if (x_28 == 0)
{
lean_dec(x_27);
lean_dec(x_26);
return x_4;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_le(x_27, x_27);
if (x_29 == 0)
{
lean_dec(x_27);
lean_dec(x_26);
return x_4;
}
else
{
size_t x_30; size_t x_31; lean_object* x_32; 
x_30 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_31 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_32 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_assertAfter___spec__6(x_25, x_30, x_31, x_4);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_PersistentArray_foldlM___at_Lean_Meta_assertAfter___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
x_7 = lean_nat_dec_le(x_6, x_3);
if (x_7 == 0)
{
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_6);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_10 = lean_ctor_get_usize(x_1, 4);
x_11 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_Meta_assertAfter___spec__3(x_8, x_9, x_10, x_2);
lean_dec(x_8);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_array_get_size(x_12);
x_14 = lean_nat_dec_lt(x_4, x_13);
if (x_14 == 0)
{
lean_dec(x_13);
lean_dec(x_12);
return x_11;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_13, x_13);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec(x_12);
return x_11;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = 0;
x_17 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_18 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_assertAfter___spec__6(x_12, x_16, x_17, x_11);
lean_dec(x_12);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_nat_sub(x_3, x_6);
lean_dec(x_6);
lean_dec(x_3);
x_21 = lean_array_get_size(x_19);
x_22 = lean_nat_dec_lt(x_20, x_21);
if (x_22 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
return x_2;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_le(x_21, x_21);
if (x_23 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
return x_2;
}
else
{
size_t x_24; size_t x_25; lean_object* x_26; 
x_24 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_25 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_26 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_assertAfter___spec__6(x_19, x_24, x_25, x_2);
lean_dec(x_19);
return x_26;
}
}
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_3);
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
x_28 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlMAux___at_Lean_Meta_assertAfter___spec__4(x_27, x_2);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
lean_dec(x_1);
x_30 = lean_array_get_size(x_29);
x_31 = lean_nat_dec_lt(x_4, x_30);
if (x_31 == 0)
{
lean_dec(x_30);
lean_dec(x_29);
return x_28;
}
else
{
uint8_t x_32; 
x_32 = lean_nat_dec_le(x_30, x_30);
if (x_32 == 0)
{
lean_dec(x_30);
lean_dec(x_29);
return x_28;
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; 
x_33 = 0;
x_34 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_35 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_assertAfter___spec__6(x_29, x_33, x_34, x_28);
lean_dec(x_29);
return x_35;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at_Lean_Meta_assertAfter___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Std_PersistentArray_foldlM___at_Lean_Meta_assertAfter___spec__2(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Nat_foldAux___at_Lean_Meta_assertAfter___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_4, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_4, x_8);
lean_dec(x_4);
x_10 = lean_nat_add(x_9, x_8);
x_11 = lean_nat_sub(x_3, x_10);
lean_dec(x_10);
x_12 = l_Lean_instInhabitedFVarId;
x_13 = lean_array_get(x_12, x_1, x_11);
x_14 = lean_array_get(x_12, x_2, x_11);
lean_dec(x_11);
x_15 = l_Lean_mkFVar(x_14);
x_16 = l_Lean_Meta_FVarSubst_insert(x_5, x_13, x_15);
x_4 = x_9;
x_5 = x_16;
goto _start;
}
else
{
lean_dec(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_assertAfter___spec__8(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_3 == x_4;
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; size_t x_10; size_t x_11; 
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_7);
lean_inc(x_1);
x_8 = l_Lean_LocalContext_get_x21(x_1, x_7);
x_9 = l_Lean_LocalDecl_isLet(x_8);
lean_dec(x_8);
x_10 = 1;
x_11 = x_3 + x_10;
if (x_9 == 0)
{
lean_object* x_12; 
x_12 = lean_array_push(x_5, x_7);
x_3 = x_11;
x_5 = x_12;
goto _start;
}
else
{
lean_dec(x_7);
x_3 = x_11;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_assertAfter___spec__9(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = x_3 == x_4;
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; size_t x_11; size_t x_12; 
x_7 = lean_array_uget(x_2, x_3);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
x_9 = l_Lean_Expr_fvarId_x21(x_8);
lean_dec(x_8);
x_10 = l_Array_contains___at___private_Lean_Class_0__Lean_checkOutParam___spec__1(x_1, x_9);
lean_dec(x_9);
x_11 = 1;
x_12 = x_3 + x_11;
if (x_10 == 0)
{
lean_object* x_13; 
x_13 = lean_array_push(x_5, x_7);
x_3 = x_12;
x_5 = x_13;
goto _start;
}
else
{
lean_dec(x_7);
x_3 = x_12;
goto _start;
}
}
else
{
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_assertAfter___spec__10(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_local_ctx_erase(x_4, x_6);
x_8 = 1;
x_9 = x_2 + x_8;
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
static lean_object* _init_l_Lean_Meta_assertAfter___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_assertAfter___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_assertAfter___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_8);
lean_inc(x_1);
x_12 = l_Lean_Meta_checkNotAssigned(x_1, x_2, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_1);
x_14 = l_Lean_Meta_getMVarTag(x_1, x_7, x_8, x_9, x_10, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_1);
x_17 = l_Lean_Meta_getMVarType(x_1, x_7, x_8, x_9, x_10, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_7);
x_20 = l_Lean_Meta_getLocalDecl(x_3, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_7, 1);
lean_inc(x_23);
x_24 = l_Lean_Meta_getLocalInstances(x_7, x_8, x_9, x_10, x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_LocalDecl_index(x_21);
lean_dec(x_21);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_27, x_28);
lean_dec(x_27);
x_30 = l_Lean_Meta_assertAfter___lambda__1___closed__1;
lean_inc(x_23);
x_31 = l_Lean_LocalContext_foldlM___at_Lean_Meta_assertAfter___spec__1(x_23, x_30, x_29);
x_32 = lean_array_get_size(x_31);
x_33 = lean_usize_of_nat(x_32);
x_34 = 0;
lean_inc(x_31);
x_35 = x_31;
x_36 = l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1(x_33, x_34, x_35);
x_37 = x_36;
x_38 = 0;
lean_inc(x_7);
x_39 = l_Lean_Meta_mkForallFVars(x_37, x_18, x_38, x_38, x_7, x_8, x_9, x_10, x_26);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = 0;
x_43 = l_Lean_mkForall(x_4, x_42, x_5, x_40);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_nat_dec_lt(x_44, x_32);
x_46 = lean_array_get_size(x_25);
x_47 = lean_nat_dec_lt(x_44, x_46);
if (x_45 == 0)
{
lean_inc(x_23);
x_48 = x_23;
goto block_105;
}
else
{
uint8_t x_106; 
x_106 = lean_nat_dec_le(x_32, x_32);
if (x_106 == 0)
{
lean_inc(x_23);
x_48 = x_23;
goto block_105;
}
else
{
lean_object* x_107; 
lean_inc(x_23);
x_107 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_assertAfter___spec__10(x_31, x_34, x_33, x_23);
x_48 = x_107;
goto block_105;
}
}
block_105:
{
lean_object* x_49; 
if (x_47 == 0)
{
lean_dec(x_46);
lean_dec(x_25);
x_49 = x_30;
goto block_101;
}
else
{
uint8_t x_102; 
x_102 = lean_nat_dec_le(x_46, x_46);
if (x_102 == 0)
{
lean_dec(x_46);
lean_dec(x_25);
x_49 = x_30;
goto block_101;
}
else
{
size_t x_103; lean_object* x_104; 
x_103 = lean_usize_of_nat(x_46);
lean_dec(x_46);
x_104 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_assertAfter___spec__9(x_31, x_25, x_34, x_103, x_30);
lean_dec(x_25);
x_49 = x_104;
goto block_101;
}
}
block_101:
{
uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = 2;
x_51 = l_Lean_Meta_mkFreshExprMVarAt(x_48, x_49, x_43, x_50, x_15, x_44, x_7, x_8, x_9, x_10, x_41);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_Meta_assertAfter___lambda__1___closed__2;
x_55 = lean_array_push(x_54, x_6);
if (x_45 == 0)
{
lean_dec(x_23);
x_56 = x_30;
goto block_98;
}
else
{
uint8_t x_99; 
x_99 = lean_nat_dec_le(x_32, x_32);
if (x_99 == 0)
{
lean_dec(x_23);
x_56 = x_30;
goto block_98;
}
else
{
lean_object* x_100; 
x_100 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_assertAfter___spec__8(x_23, x_31, x_34, x_33, x_30);
x_56 = x_100;
goto block_98;
}
}
block_98:
{
lean_object* x_57; size_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; 
x_57 = lean_array_get_size(x_56);
x_58 = lean_usize_of_nat(x_57);
lean_dec(x_57);
x_59 = x_56;
x_60 = l_Array_mapMUnsafe_map___at_Lean_LocalContext_getFVars___spec__1(x_58, x_34, x_59);
x_61 = x_60;
x_62 = l_Array_append___rarg(x_55, x_61);
lean_inc(x_52);
x_63 = l_Lean_mkAppN(x_52, x_62);
x_64 = l_Lean_Meta_assignExprMVar(x_1, x_63, x_7, x_8, x_9, x_10, x_53);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = l_Lean_Expr_mvarId_x21(x_52);
lean_dec(x_52);
x_67 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_68 = l_Lean_Meta_intro1Core(x_66, x_67, x_7, x_8, x_9, x_10, x_65);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec(x_69);
x_73 = lean_box(0);
lean_inc(x_32);
x_74 = l_Lean_Meta_introNCore(x_72, x_32, x_73, x_38, x_67, x_7, x_8, x_9, x_10, x_70);
if (lean_obj_tag(x_74) == 0)
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_76 = lean_ctor_get(x_74, 0);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_box(0);
lean_inc(x_32);
x_80 = l_Nat_foldAux___at_Lean_Meta_assertAfter___spec__7(x_31, x_77, x_32, x_32, x_79);
lean_dec(x_32);
lean_dec(x_77);
lean_dec(x_31);
x_81 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_81, 0, x_71);
lean_ctor_set(x_81, 1, x_78);
lean_ctor_set(x_81, 2, x_80);
lean_ctor_set(x_74, 0, x_81);
return x_74;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_82 = lean_ctor_get(x_74, 0);
x_83 = lean_ctor_get(x_74, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_74);
x_84 = lean_ctor_get(x_82, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_dec(x_82);
x_86 = lean_box(0);
lean_inc(x_32);
x_87 = l_Nat_foldAux___at_Lean_Meta_assertAfter___spec__7(x_31, x_84, x_32, x_32, x_86);
lean_dec(x_32);
lean_dec(x_84);
lean_dec(x_31);
x_88 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_88, 0, x_71);
lean_ctor_set(x_88, 1, x_85);
lean_ctor_set(x_88, 2, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_83);
return x_89;
}
}
else
{
uint8_t x_90; 
lean_dec(x_71);
lean_dec(x_32);
lean_dec(x_31);
x_90 = !lean_is_exclusive(x_74);
if (x_90 == 0)
{
return x_74;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_74, 0);
x_92 = lean_ctor_get(x_74, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_74);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_94 = !lean_is_exclusive(x_68);
if (x_94 == 0)
{
return x_68;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_68, 0);
x_96 = lean_ctor_get(x_68, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_68);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_39);
if (x_108 == 0)
{
return x_39;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_39, 0);
x_110 = lean_ctor_get(x_39, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_39);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_20);
if (x_112 == 0)
{
return x_20;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_20, 0);
x_114 = lean_ctor_get(x_20, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_20);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_116 = !lean_is_exclusive(x_17);
if (x_116 == 0)
{
return x_17;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_17, 0);
x_118 = lean_ctor_get(x_17, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_17);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_120 = !lean_is_exclusive(x_14);
if (x_120 == 0)
{
return x_14;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_14, 0);
x_122 = lean_ctor_get(x_14, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_14);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_12);
if (x_124 == 0)
{
return x_12;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_12, 0);
x_126 = lean_ctor_get(x_12, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_12);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
}
static lean_object* _init_l_Lean_Meta_assertAfter___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("assertAfter");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_assertAfter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_assertAfter___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_assertAfter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_Meta_assertAfter___closed__2;
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_assertAfter___lambda__1), 11, 6);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_11);
lean_closure_set(x_12, 2, x_2);
lean_closure_set(x_12, 3, x_3);
lean_closure_set(x_12, 4, x_4);
lean_closure_set(x_12, 5, x_5);
x_13 = l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(x_1, x_12, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_assertAfter___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_assertAfter___spec__5(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_assertAfter___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_assertAfter___spec__6(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_Meta_assertAfter___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_Meta_assertAfter___spec__3(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Nat_foldAux___at_Lean_Meta_assertAfter___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Nat_foldAux___at_Lean_Meta_assertAfter___spec__7(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_assertAfter___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_assertAfter___spec__8(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_assertAfter___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_assertAfter___spec__9(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_assertAfter___spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_assertAfter___spec__10(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_assertHypotheses___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 2);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_mkApp(x_4, x_7);
x_9 = 1;
x_10 = x_2 + x_9;
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
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_assertHypotheses___spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = x_2 == x_3;
if (x_5 == 0)
{
size_t x_6; size_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_6 = 1;
x_7 = x_2 - x_6;
x_8 = lean_array_uget(x_1, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = 0;
x_12 = l_Lean_mkForall(x_9, x_11, x_10, x_4);
x_2 = x_7;
x_4 = x_12;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_assertHypotheses___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_5);
lean_inc(x_1);
x_9 = l_Lean_Meta_checkNotAssigned(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_1);
x_11 = l_Lean_Meta_getMVarTag(x_1, x_4, x_5, x_6, x_7, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_1);
x_14 = l_Lean_Meta_getMVarType(x_1, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_50; uint8_t x_51; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_array_get_size(x_3);
x_50 = lean_unsigned_to_nat(0u);
x_51 = lean_nat_dec_lt(x_50, x_17);
if (x_51 == 0)
{
x_18 = x_15;
goto block_49;
}
else
{
size_t x_52; size_t x_53; lean_object* x_54; 
x_52 = lean_usize_of_nat(x_17);
x_53 = 0;
x_54 = l_Array_foldrMUnsafe_fold___at_Lean_Meta_assertHypotheses___spec__2(x_3, x_52, x_53, x_15);
x_18 = x_54;
goto block_49;
}
block_49:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_inc(x_4);
x_19 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_18, x_12, x_4, x_5, x_6, x_7, x_16);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_dec_lt(x_22, x_17);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; 
lean_inc(x_20);
x_24 = l_Lean_Meta_assignExprMVar(x_1, x_20, x_4, x_5, x_6, x_7, x_21);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_Expr_mvarId_x21(x_20);
lean_dec(x_20);
x_27 = lean_box(0);
x_28 = 0;
x_29 = 1;
x_30 = l_Lean_Meta_introNCore(x_26, x_17, x_27, x_28, x_29, x_4, x_5, x_6, x_7, x_25);
return x_30;
}
else
{
uint8_t x_31; 
x_31 = lean_nat_dec_le(x_17, x_17);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; 
lean_inc(x_20);
x_32 = l_Lean_Meta_assignExprMVar(x_1, x_20, x_4, x_5, x_6, x_7, x_21);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l_Lean_Expr_mvarId_x21(x_20);
lean_dec(x_20);
x_35 = lean_box(0);
x_36 = 0;
x_37 = 1;
x_38 = l_Lean_Meta_introNCore(x_34, x_17, x_35, x_36, x_37, x_4, x_5, x_6, x_7, x_33);
return x_38;
}
else
{
size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_47; lean_object* x_48; 
x_39 = 0;
x_40 = lean_usize_of_nat(x_17);
lean_inc(x_20);
x_41 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_assertHypotheses___spec__1(x_3, x_39, x_40, x_20);
x_42 = l_Lean_Meta_assignExprMVar(x_1, x_41, x_4, x_5, x_6, x_7, x_21);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = l_Lean_Expr_mvarId_x21(x_20);
lean_dec(x_20);
x_45 = lean_box(0);
x_46 = 0;
x_47 = 1;
x_48 = l_Lean_Meta_introNCore(x_44, x_17, x_45, x_46, x_47, x_4, x_5, x_6, x_7, x_43);
return x_48;
}
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_14);
if (x_55 == 0)
{
return x_14;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_14, 0);
x_57 = lean_ctor_get(x_14, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_14);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_11);
if (x_59 == 0)
{
return x_11;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_11, 0);
x_61 = lean_ctor_get(x_11, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_11);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_9);
if (x_63 == 0)
{
return x_9;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_9, 0);
x_65 = lean_ctor_get(x_9, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_9);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
static lean_object* _init_l_Lean_Meta_assertHypotheses___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("assertHypotheses");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_assertHypotheses___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_assertHypotheses___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_assertHypotheses(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Array_isEmpty___rarg(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = l_Lean_Meta_assertHypotheses___closed__2;
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_assertHypotheses___lambda__1___boxed), 8, 3);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_9);
lean_closure_set(x_10, 2, x_2);
x_11 = l_Lean_Meta_withMVarContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__1___rarg(x_1, x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = l_Lean_Meta_assertAfter___lambda__1___closed__1;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_7);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Meta_assertHypotheses___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at_Lean_Meta_assertHypotheses___spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_Lean_Meta_assertHypotheses___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldrMUnsafe_fold___at_Lean_Meta_assertHypotheses___spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_assertHypotheses___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_assertHypotheses___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_FVarSubst(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Intro(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Revert(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Assert(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_FVarSubst(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Intro(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Revert(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_assert___closed__1 = _init_l_Lean_Meta_assert___closed__1();
lean_mark_persistent(l_Lean_Meta_assert___closed__1);
l_Lean_Meta_assert___closed__2 = _init_l_Lean_Meta_assert___closed__2();
lean_mark_persistent(l_Lean_Meta_assert___closed__2);
l_Lean_Meta_define___closed__1 = _init_l_Lean_Meta_define___closed__1();
lean_mark_persistent(l_Lean_Meta_define___closed__1);
l_Lean_Meta_define___closed__2 = _init_l_Lean_Meta_define___closed__2();
lean_mark_persistent(l_Lean_Meta_define___closed__2);
l_Lean_Meta_assertExt___lambda__1___closed__1 = _init_l_Lean_Meta_assertExt___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_assertExt___lambda__1___closed__1);
l_Lean_Meta_assertExt___lambda__1___closed__2 = _init_l_Lean_Meta_assertExt___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_assertExt___lambda__1___closed__2);
l_Lean_Meta_assertExt___lambda__1___closed__3 = _init_l_Lean_Meta_assertExt___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_assertExt___lambda__1___closed__3);
l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_Meta_assertAfter___spec__3___closed__1 = _init_l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_Meta_assertAfter___spec__3___closed__1();
lean_mark_persistent(l___private_Std_Data_PersistentArray_0__Std_PersistentArray_foldlFromMAux___at_Lean_Meta_assertAfter___spec__3___closed__1);
l_Lean_Meta_assertAfter___lambda__1___closed__1 = _init_l_Lean_Meta_assertAfter___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_assertAfter___lambda__1___closed__1);
l_Lean_Meta_assertAfter___lambda__1___closed__2 = _init_l_Lean_Meta_assertAfter___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_assertAfter___lambda__1___closed__2);
l_Lean_Meta_assertAfter___closed__1 = _init_l_Lean_Meta_assertAfter___closed__1();
lean_mark_persistent(l_Lean_Meta_assertAfter___closed__1);
l_Lean_Meta_assertAfter___closed__2 = _init_l_Lean_Meta_assertAfter___closed__2();
lean_mark_persistent(l_Lean_Meta_assertAfter___closed__2);
l_Lean_Meta_assertHypotheses___closed__1 = _init_l_Lean_Meta_assertHypotheses___closed__1();
lean_mark_persistent(l_Lean_Meta_assertHypotheses___closed__1);
l_Lean_Meta_assertHypotheses___closed__2 = _init_l_Lean_Meta_assertHypotheses___closed__2();
lean_mark_persistent(l_Lean_Meta_assertHypotheses___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
