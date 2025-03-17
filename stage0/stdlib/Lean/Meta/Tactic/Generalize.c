// Lean compiler output
// Module: Lean.Meta.Tactic.Generalize
// Imports: Lean.Meta.KAbstract Lean.Meta.Tactic.Util Lean.Meta.Tactic.Intro Lean.Meta.Tactic.FVarSubst Lean.Meta.Tactic.Revert
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___closed__1;
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___rarg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_generalizeHyp___spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lambda__3___closed__4;
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_generalize(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeCorrect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedGeneralizeArg___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_generalizeHyp___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_arrowDomainsN___spec__6___rarg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_generalizeHyp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_MVarId_generalizeHyp___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_generalizeHyp(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_revert(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_generalizeHyp___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_generalizeHyp___spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_generalizeHyp___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lambda__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_generalizeHyp___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__2;
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_generalizeHyp___spec__4(uint8_t, size_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___spec__1(size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_generalizeHyp___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_generalizeHyp___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_generalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
static lean_object* l_Lean_Meta_instInhabitedGeneralizeArg___closed__4;
lean_object* lean_array_mk(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___closed__2;
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_Meta_instInhabitedGeneralizeArg___closed__2;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_MVarId_generalizeHyp___spec__2(uint8_t, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lambda__3___closed__3;
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___spec__2(lean_object*, size_t, size_t);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedGeneralizeArg;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lean_Meta_instInhabitedGeneralizeArg___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lambda__3___closed__2;
uint8_t l_Array_isEmpty___rarg(lean_object*);
static lean_object* _init_l_Lean_Meta_instInhabitedGeneralizeArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedGeneralizeArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_instInhabitedGeneralizeArg___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedGeneralizeArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_instInhabitedGeneralizeArg___closed__2;
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedGeneralizeArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_instInhabitedGeneralizeArg___closed__3;
x_3 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedGeneralizeArg() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_instInhabitedGeneralizeArg___closed__4;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_6);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get_uint64(x_6, sizeof(void*)*7);
lean_ctor_set_uint8(x_12, 9, x_1);
x_15 = 2;
x_16 = lean_uint64_shift_right(x_14, x_15);
x_17 = lean_uint64_shift_left(x_16, x_15);
x_18 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
x_19 = lean_uint64_lor(x_17, x_18);
lean_ctor_set_uint64(x_6, sizeof(void*)*7, x_19);
x_20 = lean_box(0);
x_21 = l_Lean_Meta_kabstract(x_2, x_3, x_20, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = 0;
x_25 = l_Lean_Expr_forallE___override(x_5, x_4, x_23, x_24);
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = 0;
x_29 = l_Lean_Expr_forallE___override(x_5, x_4, x_26, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_5);
lean_dec(x_4);
x_31 = !lean_is_exclusive(x_21);
if (x_31 == 0)
{
return x_21;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_21, 0);
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_21);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint64_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; uint64_t x_54; uint64_t x_55; uint64_t x_56; uint64_t x_57; uint64_t x_58; lean_object* x_59; lean_object* x_60; 
x_35 = lean_ctor_get_uint64(x_6, sizeof(void*)*7);
x_36 = lean_ctor_get_uint8(x_12, 0);
x_37 = lean_ctor_get_uint8(x_12, 1);
x_38 = lean_ctor_get_uint8(x_12, 2);
x_39 = lean_ctor_get_uint8(x_12, 3);
x_40 = lean_ctor_get_uint8(x_12, 4);
x_41 = lean_ctor_get_uint8(x_12, 5);
x_42 = lean_ctor_get_uint8(x_12, 6);
x_43 = lean_ctor_get_uint8(x_12, 7);
x_44 = lean_ctor_get_uint8(x_12, 8);
x_45 = lean_ctor_get_uint8(x_12, 10);
x_46 = lean_ctor_get_uint8(x_12, 11);
x_47 = lean_ctor_get_uint8(x_12, 12);
x_48 = lean_ctor_get_uint8(x_12, 13);
x_49 = lean_ctor_get_uint8(x_12, 14);
x_50 = lean_ctor_get_uint8(x_12, 15);
x_51 = lean_ctor_get_uint8(x_12, 16);
x_52 = lean_ctor_get_uint8(x_12, 17);
lean_dec(x_12);
x_53 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_53, 0, x_36);
lean_ctor_set_uint8(x_53, 1, x_37);
lean_ctor_set_uint8(x_53, 2, x_38);
lean_ctor_set_uint8(x_53, 3, x_39);
lean_ctor_set_uint8(x_53, 4, x_40);
lean_ctor_set_uint8(x_53, 5, x_41);
lean_ctor_set_uint8(x_53, 6, x_42);
lean_ctor_set_uint8(x_53, 7, x_43);
lean_ctor_set_uint8(x_53, 8, x_44);
lean_ctor_set_uint8(x_53, 9, x_1);
lean_ctor_set_uint8(x_53, 10, x_45);
lean_ctor_set_uint8(x_53, 11, x_46);
lean_ctor_set_uint8(x_53, 12, x_47);
lean_ctor_set_uint8(x_53, 13, x_48);
lean_ctor_set_uint8(x_53, 14, x_49);
lean_ctor_set_uint8(x_53, 15, x_50);
lean_ctor_set_uint8(x_53, 16, x_51);
lean_ctor_set_uint8(x_53, 17, x_52);
x_54 = 2;
x_55 = lean_uint64_shift_right(x_35, x_54);
x_56 = lean_uint64_shift_left(x_55, x_54);
x_57 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
x_58 = lean_uint64_lor(x_56, x_57);
lean_ctor_set(x_6, 0, x_53);
lean_ctor_set_uint64(x_6, sizeof(void*)*7, x_58);
x_59 = lean_box(0);
x_60 = l_Lean_Meta_kabstract(x_2, x_3, x_59, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_63 = x_60;
} else {
 lean_dec_ref(x_60);
 x_63 = lean_box(0);
}
x_64 = 0;
x_65 = l_Lean_Expr_forallE___override(x_5, x_4, x_61, x_64);
if (lean_is_scalar(x_63)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_63;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_62);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_5);
lean_dec(x_4);
x_67 = lean_ctor_get(x_60, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_60, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_69 = x_60;
} else {
 lean_dec_ref(x_60);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
}
else
{
lean_object* x_71; uint64_t x_72; uint8_t x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; uint8_t x_96; uint8_t x_97; uint8_t x_98; lean_object* x_99; lean_object* x_100; uint64_t x_101; uint64_t x_102; uint64_t x_103; uint64_t x_104; uint64_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_71 = lean_ctor_get(x_6, 0);
x_72 = lean_ctor_get_uint64(x_6, sizeof(void*)*7);
x_73 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 8);
x_74 = lean_ctor_get(x_6, 1);
x_75 = lean_ctor_get(x_6, 2);
x_76 = lean_ctor_get(x_6, 3);
x_77 = lean_ctor_get(x_6, 4);
x_78 = lean_ctor_get(x_6, 5);
x_79 = lean_ctor_get(x_6, 6);
x_80 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 9);
x_81 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 10);
lean_inc(x_79);
lean_inc(x_78);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
lean_inc(x_71);
lean_dec(x_6);
x_82 = lean_ctor_get_uint8(x_71, 0);
x_83 = lean_ctor_get_uint8(x_71, 1);
x_84 = lean_ctor_get_uint8(x_71, 2);
x_85 = lean_ctor_get_uint8(x_71, 3);
x_86 = lean_ctor_get_uint8(x_71, 4);
x_87 = lean_ctor_get_uint8(x_71, 5);
x_88 = lean_ctor_get_uint8(x_71, 6);
x_89 = lean_ctor_get_uint8(x_71, 7);
x_90 = lean_ctor_get_uint8(x_71, 8);
x_91 = lean_ctor_get_uint8(x_71, 10);
x_92 = lean_ctor_get_uint8(x_71, 11);
x_93 = lean_ctor_get_uint8(x_71, 12);
x_94 = lean_ctor_get_uint8(x_71, 13);
x_95 = lean_ctor_get_uint8(x_71, 14);
x_96 = lean_ctor_get_uint8(x_71, 15);
x_97 = lean_ctor_get_uint8(x_71, 16);
x_98 = lean_ctor_get_uint8(x_71, 17);
if (lean_is_exclusive(x_71)) {
 x_99 = x_71;
} else {
 lean_dec_ref(x_71);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(0, 0, 18);
} else {
 x_100 = x_99;
}
lean_ctor_set_uint8(x_100, 0, x_82);
lean_ctor_set_uint8(x_100, 1, x_83);
lean_ctor_set_uint8(x_100, 2, x_84);
lean_ctor_set_uint8(x_100, 3, x_85);
lean_ctor_set_uint8(x_100, 4, x_86);
lean_ctor_set_uint8(x_100, 5, x_87);
lean_ctor_set_uint8(x_100, 6, x_88);
lean_ctor_set_uint8(x_100, 7, x_89);
lean_ctor_set_uint8(x_100, 8, x_90);
lean_ctor_set_uint8(x_100, 9, x_1);
lean_ctor_set_uint8(x_100, 10, x_91);
lean_ctor_set_uint8(x_100, 11, x_92);
lean_ctor_set_uint8(x_100, 12, x_93);
lean_ctor_set_uint8(x_100, 13, x_94);
lean_ctor_set_uint8(x_100, 14, x_95);
lean_ctor_set_uint8(x_100, 15, x_96);
lean_ctor_set_uint8(x_100, 16, x_97);
lean_ctor_set_uint8(x_100, 17, x_98);
x_101 = 2;
x_102 = lean_uint64_shift_right(x_72, x_101);
x_103 = lean_uint64_shift_left(x_102, x_101);
x_104 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
x_105 = lean_uint64_lor(x_103, x_104);
x_106 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_106, 0, x_100);
lean_ctor_set(x_106, 1, x_74);
lean_ctor_set(x_106, 2, x_75);
lean_ctor_set(x_106, 3, x_76);
lean_ctor_set(x_106, 4, x_77);
lean_ctor_set(x_106, 5, x_78);
lean_ctor_set(x_106, 6, x_79);
lean_ctor_set_uint64(x_106, sizeof(void*)*7, x_105);
lean_ctor_set_uint8(x_106, sizeof(void*)*7 + 8, x_73);
lean_ctor_set_uint8(x_106, sizeof(void*)*7 + 9, x_80);
lean_ctor_set_uint8(x_106, sizeof(void*)*7 + 10, x_81);
x_107 = lean_box(0);
x_108 = l_Lean_Meta_kabstract(x_2, x_3, x_107, x_106, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_111 = x_108;
} else {
 lean_dec_ref(x_108);
 x_111 = lean_box(0);
}
x_112 = 0;
x_113 = l_Lean_Expr_forallE___override(x_5, x_4, x_109, x_112);
if (lean_is_scalar(x_111)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_111;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_110);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_5);
lean_dec(x_4);
x_115 = lean_ctor_get(x_108, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_108, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_117 = x_108;
} else {
 lean_dec_ref(x_108);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("x", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_1);
x_11 = lean_nat_dec_lt(x_4, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_array_fget(x_1, x_4);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_14, x_5, x_6, x_7, x_8, x_9);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_16);
x_18 = lean_infer_type(x_16, x_5, x_6, x_7, x_8, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_19, x_5, x_6, x_7, x_8, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_4, x_24);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_26 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go(x_1, x_2, x_3, x_25, x_5, x_6, x_7, x_8, x_23);
lean_dec(x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
lean_dec(x_13);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___closed__2;
x_31 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_30, x_7, x_8, x_29);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___lambda__1(x_2, x_28, x_16, x_22, x_32, x_5, x_6, x_7, x_8, x_33);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_26, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_26, 1);
lean_inc(x_36);
lean_dec(x_26);
x_37 = lean_ctor_get(x_27, 0);
lean_inc(x_37);
lean_dec(x_27);
x_38 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___lambda__1(x_2, x_35, x_16, x_22, x_37, x_5, x_6, x_7, x_8, x_36);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_39 = !lean_is_exclusive(x_26);
if (x_39 == 0)
{
return x_26;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_26, 0);
x_41 = lean_ctor_get(x_26, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_26);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_43 = !lean_is_exclusive(x_18);
if (x_43 == 0)
{
return x_18;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_18, 0);
x_45 = lean_ctor_get(x_18, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_18);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___lambda__1(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_6);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_6, 1);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_1, x_15);
x_17 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27(x_2, x_3, x_4, x_16, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 1, x_21);
lean_ctor_set(x_6, 0, x_14);
x_23 = 0;
x_24 = l_Lean_Expr_forallE___override(x_5, x_13, x_22, x_23);
lean_ctor_set(x_19, 1, x_24);
lean_ctor_set(x_19, 0, x_6);
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 1, x_25);
lean_ctor_set(x_6, 0, x_14);
x_27 = 0;
x_28 = l_Lean_Expr_forallE___override(x_5, x_13, x_26, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_6);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_17, 0, x_29);
return x_17;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_ctor_get(x_17, 0);
x_31 = lean_ctor_get(x_17, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_17);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_34 = x_30;
} else {
 lean_dec_ref(x_30);
 x_34 = lean_box(0);
}
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 1, x_32);
lean_ctor_set(x_6, 0, x_14);
x_35 = 0;
x_36 = l_Lean_Expr_forallE___override(x_5, x_13, x_33, x_35);
if (lean_is_scalar(x_34)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_34;
}
lean_ctor_set(x_37, 0, x_6);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_31);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_free_object(x_6);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
x_39 = !lean_is_exclusive(x_17);
if (x_39 == 0)
{
return x_17;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_17, 0);
x_41 = lean_ctor_get(x_17, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_17);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_6, 0);
x_44 = lean_ctor_get(x_6, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_6);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_add(x_1, x_45);
x_47 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27(x_2, x_3, x_4, x_46, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_50 = x_47;
} else {
 lean_dec_ref(x_47);
 x_50 = lean_box(0);
}
x_51 = lean_ctor_get(x_48, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_53 = x_48;
} else {
 lean_dec_ref(x_48);
 x_53 = lean_box(0);
}
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_44);
lean_ctor_set(x_54, 1, x_51);
x_55 = 0;
x_56 = l_Lean_Expr_forallE___override(x_5, x_43, x_52, x_55);
if (lean_is_scalar(x_53)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_53;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
if (lean_is_scalar(x_50)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_50;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_49);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_5);
x_59 = lean_ctor_get(x_47, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_47, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_61 = x_47;
} else {
 lean_dec_ref(x_47);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_2);
x_11 = lean_nat_dec_lt(x_4, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = l_Lean_Meta_instInhabitedGeneralizeArg;
x_16 = lean_array_get(x_15, x_1, x_4);
x_17 = lean_ctor_get(x_16, 2);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_4, x_18);
lean_dec(x_4);
x_4 = x_19;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_array_fget(x_2, x_4);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_22);
x_23 = lean_infer_type(x_22, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_16, 0);
lean_inc(x_26);
lean_dec(x_16);
x_27 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_26, x_5, x_6, x_7, x_8, x_25);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_28);
x_30 = lean_infer_type(x_28, x_5, x_6, x_7, x_8, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_31, x_5, x_6, x_7, x_8, x_32);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_37 = l_Lean_Meta_isExprDefEq(x_24, x_35, x_5, x_6, x_7, x_8, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_28);
x_41 = l_Lean_Meta_mkHEq(x_28, x_22, x_5, x_6, x_7, x_8, x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_44 = l_Lean_Meta_mkHEqRefl(x_28, x_5, x_6, x_7, x_8, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
lean_ctor_set(x_33, 1, x_45);
lean_ctor_set(x_33, 0, x_42);
x_47 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27___lambda__1(x_4, x_1, x_2, x_3, x_21, x_33, x_5, x_6, x_7, x_8, x_46);
lean_dec(x_4);
return x_47;
}
else
{
uint8_t x_48; 
lean_dec(x_42);
lean_free_object(x_33);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_48 = !lean_is_exclusive(x_44);
if (x_48 == 0)
{
return x_44;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_44, 0);
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_44);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_free_object(x_33);
lean_dec(x_28);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_52 = !lean_is_exclusive(x_41);
if (x_52 == 0)
{
return x_41;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_41, 0);
x_54 = lean_ctor_get(x_41, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_41);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_37, 1);
lean_inc(x_56);
lean_dec(x_37);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_28);
x_57 = l_Lean_Meta_mkEq(x_28, x_22, x_5, x_6, x_7, x_8, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_60 = l_Lean_Meta_mkEqRefl(x_28, x_5, x_6, x_7, x_8, x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
lean_ctor_set(x_33, 1, x_61);
lean_ctor_set(x_33, 0, x_58);
x_63 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27___lambda__1(x_4, x_1, x_2, x_3, x_21, x_33, x_5, x_6, x_7, x_8, x_62);
lean_dec(x_4);
return x_63;
}
else
{
uint8_t x_64; 
lean_dec(x_58);
lean_free_object(x_33);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_64 = !lean_is_exclusive(x_60);
if (x_64 == 0)
{
return x_60;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_60, 0);
x_66 = lean_ctor_get(x_60, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_60);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_free_object(x_33);
lean_dec(x_28);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_68 = !lean_is_exclusive(x_57);
if (x_68 == 0)
{
return x_57;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_57, 0);
x_70 = lean_ctor_get(x_57, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_57);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
else
{
uint8_t x_72; 
lean_free_object(x_33);
lean_dec(x_28);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_72 = !lean_is_exclusive(x_37);
if (x_72 == 0)
{
return x_37;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_37, 0);
x_74 = lean_ctor_get(x_37, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_37);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_33, 0);
x_77 = lean_ctor_get(x_33, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_33);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_78 = l_Lean_Meta_isExprDefEq(x_24, x_76, x_5, x_6, x_7, x_8, x_77);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_unbox(x_79);
lean_dec(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_dec(x_78);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_28);
x_82 = l_Lean_Meta_mkHEq(x_28, x_22, x_5, x_6, x_7, x_8, x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_85 = l_Lean_Meta_mkHEqRefl(x_28, x_5, x_6, x_7, x_8, x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_83);
lean_ctor_set(x_88, 1, x_86);
x_89 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27___lambda__1(x_4, x_1, x_2, x_3, x_21, x_88, x_5, x_6, x_7, x_8, x_87);
lean_dec(x_4);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_83);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_90 = lean_ctor_get(x_85, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_85, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_92 = x_85;
} else {
 lean_dec_ref(x_85);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_28);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_94 = lean_ctor_get(x_82, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_82, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_96 = x_82;
} else {
 lean_dec_ref(x_82);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_78, 1);
lean_inc(x_98);
lean_dec(x_78);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_28);
x_99 = l_Lean_Meta_mkEq(x_28, x_22, x_5, x_6, x_7, x_8, x_98);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_102 = l_Lean_Meta_mkEqRefl(x_28, x_5, x_6, x_7, x_8, x_101);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_100);
lean_ctor_set(x_105, 1, x_103);
x_106 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27___lambda__1(x_4, x_1, x_2, x_3, x_21, x_105, x_5, x_6, x_7, x_8, x_104);
lean_dec(x_4);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_100);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_107 = lean_ctor_get(x_102, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_102, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_109 = x_102;
} else {
 lean_dec_ref(x_102);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_28);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_111 = lean_ctor_get(x_99, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_99, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_113 = x_99;
} else {
 lean_dec_ref(x_99);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_111);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_28);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_115 = lean_ctor_get(x_78, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_78, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_117 = x_78;
} else {
 lean_dec_ref(x_78);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(1, 2, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_28);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_119 = !lean_is_exclusive(x_30);
if (x_119 == 0)
{
return x_30;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_30, 0);
x_121 = lean_ctor_get(x_30, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_30);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_123 = !lean_is_exclusive(x_23);
if (x_123 == 0)
{
return x_23;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_23, 0);
x_125 = lean_ctor_get(x_23, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_23);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___spec__2(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_array_uget(x_1, x_2);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_6) == 0)
{
size_t x_7; size_t x_8; 
x_7 = 1;
x_8 = lean_usize_add(x_2, x_7);
x_2 = x_8;
goto _start;
}
else
{
uint8_t x_10; 
lean_dec(x_6);
x_10 = 1;
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(0u);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_10 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go_x27(x_1, x_2, x_3, x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 1);
x_16 = 0;
x_17 = 1;
x_18 = 1;
x_19 = l_Lean_Meta_mkForallFVars(x_2, x_15, x_16, x_17, x_18, x_4, x_5, x_6, x_7, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_ctor_set(x_11, 1, x_21);
lean_ctor_set(x_19, 0, x_11);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_19);
lean_ctor_set(x_11, 1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_free_object(x_11);
lean_dec(x_14);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
return x_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_19);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; 
x_29 = lean_ctor_get(x_11, 0);
x_30 = lean_ctor_get(x_11, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_11);
x_31 = 0;
x_32 = 1;
x_33 = 1;
x_34 = l_Lean_Meta_mkForallFVars(x_2, x_30, x_31, x_32, x_33, x_4, x_5, x_6, x_7, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_37 = x_34;
} else {
 lean_dec_ref(x_34);
 x_37 = lean_box(0);
}
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_29);
lean_ctor_set(x_38, 1, x_35);
if (lean_is_scalar(x_37)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_37;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_36);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_29);
x_40 = lean_ctor_get(x_34, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_34, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_42 = x_34;
} else {
 lean_dec_ref(x_34);
 x_42 = lean_box(0);
}
if (lean_is_scalar(x_42)) {
 x_43 = lean_alloc_ctor(1, 2, 0);
} else {
 x_43 = x_42;
}
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_44 = !lean_is_exclusive(x_10);
if (x_44 == 0)
{
return x_10;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_10, 0);
x_46 = lean_ctor_get(x_10, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_10);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_28; uint8_t x_29; 
x_11 = lean_array_size(x_1);
x_12 = 0;
lean_inc(x_1);
x_13 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___spec__1(x_11, x_12, x_1);
x_14 = lean_array_get_size(x_1);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_nat_dec_lt(x_28, x_14);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_1);
x_30 = lean_box(0);
x_15 = x_30;
goto block_27;
}
else
{
size_t x_31; uint8_t x_32; 
x_31 = lean_usize_of_nat(x_14);
x_32 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___spec__2(x_1, x_12, x_31);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_1);
x_33 = lean_box(0);
x_15 = x_33;
goto block_27;
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
lean_inc(x_14);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_14);
x_35 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lambda__1___boxed), 8, 1);
lean_closure_set(x_35, 0, x_1);
x_36 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_37 = l_Lean_Meta_forallBoundedTelescope___at_Lean_Meta_arrowDomainsN___spec__6___rarg(x_2, x_34, x_35, x_36, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
lean_inc(x_6);
x_42 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_41, x_3, x_6, x_7, x_8, x_9, x_39);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_43);
x_45 = l_Lean_mkAppN(x_43, x_13);
lean_dec(x_13);
lean_inc(x_40);
x_46 = lean_array_mk(x_40);
x_47 = l_Lean_mkAppN(x_45, x_46);
lean_dec(x_46);
x_48 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_4, x_47, x_6, x_7, x_8, x_9, x_44);
x_49 = lean_ctor_get(x_48, 1);
lean_inc(x_49);
lean_dec(x_48);
x_50 = l_Lean_Expr_mvarId_x21(x_43);
lean_dec(x_43);
x_51 = l_List_lengthTRAux___rarg(x_40, x_28);
lean_dec(x_40);
x_52 = lean_nat_add(x_14, x_51);
lean_dec(x_51);
lean_dec(x_14);
x_53 = lean_box(0);
x_54 = 1;
x_55 = l_Lean_Meta_introNCore(x_50, x_52, x_53, x_36, x_54, x_6, x_7, x_8, x_9, x_49);
return x_55;
}
else
{
uint8_t x_56; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_56 = !lean_is_exclusive(x_37);
if (x_56 == 0)
{
return x_37;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_37, 0);
x_58 = lean_ctor_get(x_37, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_37);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
block_27:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; 
lean_dec(x_15);
lean_inc(x_6);
x_16 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_2, x_3, x_6, x_7, x_8, x_9, x_10);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_17);
x_19 = l_Lean_mkAppN(x_17, x_13);
lean_dec(x_13);
x_20 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_4, x_19, x_6, x_7, x_8, x_9, x_18);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_Expr_mvarId_x21(x_17);
lean_dec(x_17);
x_23 = lean_box(0);
x_24 = 0;
x_25 = 1;
x_26 = l_Lean_Meta_introNCore(x_22, x_14, x_23, x_24, x_25, x_6, x_7, x_8, x_9, x_21);
return x_26;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("result is not type correct", 26, 26);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lambda__3___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lambda__3___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
lean_inc(x_1);
x_12 = l_Lean_MVarId_getTag(x_1, x_5, x_6, x_7, x_8, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_1);
x_15 = l_Lean_MVarId_getType(x_1, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_16, x_5, x_6, x_7, x_8, x_17);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_23 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go(x_3, x_4, x_20, x_22, x_5, x_6, x_7, x_8, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_24);
x_26 = l_Lean_Meta_isTypeCorrect(x_24, x_5, x_6, x_7, x_8, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_13);
lean_dec(x_3);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = l_Lean_indentExpr(x_24);
x_31 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lambda__3___closed__2;
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_30);
lean_ctor_set(x_18, 0, x_31);
x_32 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lambda__3___closed__4;
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_18);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_34, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
return x_35;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_35);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_free_object(x_18);
lean_dec(x_2);
x_40 = lean_ctor_get(x_26, 1);
lean_inc(x_40);
lean_dec(x_26);
x_41 = lean_box(0);
x_42 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lambda__2(x_3, x_24, x_13, x_1, x_41, x_5, x_6, x_7, x_8, x_40);
return x_42;
}
}
else
{
uint8_t x_43; 
lean_dec(x_24);
lean_free_object(x_18);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_26);
if (x_43 == 0)
{
return x_26;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_26, 0);
x_45 = lean_ctor_get(x_26, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_26);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_free_object(x_18);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_23);
if (x_47 == 0)
{
return x_23;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_23, 0);
x_49 = lean_ctor_get(x_23, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_23);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_18, 0);
x_52 = lean_ctor_get(x_18, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_18);
x_53 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_54 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go(x_3, x_4, x_51, x_53, x_5, x_6, x_7, x_8, x_52);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_55);
x_57 = l_Lean_Meta_isTypeCorrect(x_55, x_5, x_6, x_7, x_8, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_unbox(x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_13);
lean_dec(x_3);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = l_Lean_indentExpr(x_55);
x_62 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lambda__3___closed__2;
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lambda__3___closed__4;
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_66, x_5, x_6, x_7, x_8, x_60);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_70 = x_67;
} else {
 lean_dec_ref(x_67);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_2);
x_72 = lean_ctor_get(x_57, 1);
lean_inc(x_72);
lean_dec(x_57);
x_73 = lean_box(0);
x_74 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lambda__2(x_3, x_55, x_13, x_1, x_73, x_5, x_6, x_7, x_8, x_72);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_55);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_75 = lean_ctor_get(x_57, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_57, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_77 = x_57;
} else {
 lean_dec_ref(x_57);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_79 = lean_ctor_get(x_54, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_54, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_81 = x_54;
} else {
 lean_dec_ref(x_54);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_15);
if (x_83 == 0)
{
return x_15;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_15, 0);
x_85 = lean_ctor_get(x_15, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_15);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_12);
if (x_87 == 0)
{
return x_12;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_12, 0);
x_89 = lean_ctor_get(x_12, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_12);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_10);
if (x_91 == 0)
{
return x_10;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_10, 0);
x_93 = lean_ctor_get(x_10, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_10);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("generalize", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__2;
x_10 = lean_box(x_3);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lambda__3___boxed), 9, 4);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_9);
lean_closure_set(x_11, 2, x_2);
lean_closure_set(x_11, 3, x_10);
x_12 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_11, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___spec__2(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lambda__3(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_generalize(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_generalize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_MVarId_generalize(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_generalizeHyp___spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_2, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_array_uget(x_3, x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uset(x_3, x_2, x_12);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_15, x_4, x_5, x_6, x_7, x_8);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_ctor_set(x_11, 0, x_17);
x_19 = 1;
x_20 = lean_usize_add(x_2, x_19);
x_21 = lean_array_uset(x_13, x_2, x_11);
x_2 = x_20;
x_3 = x_21;
x_8 = x_18;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_11, 0);
x_24 = lean_ctor_get(x_11, 1);
x_25 = lean_ctor_get(x_11, 2);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_11);
x_26 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_23, x_4, x_5, x_6, x_7, x_8);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_25);
x_30 = 1;
x_31 = lean_usize_add(x_2, x_30);
x_32 = lean_array_uset(x_13, x_2, x_29);
x_2 = x_31;
x_3 = x_32;
x_8 = x_28;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_MVarId_generalizeHyp___spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_4, x_5);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint64_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_12 = lean_array_uget(x_3, x_4);
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get_uint64(x_6, sizeof(void*)*7);
x_16 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 8);
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_6, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_6, 3);
lean_inc(x_19);
x_20 = lean_ctor_get(x_6, 4);
lean_inc(x_20);
x_21 = lean_ctor_get(x_6, 5);
lean_inc(x_21);
x_22 = lean_ctor_get(x_6, 6);
lean_inc(x_22);
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
uint8_t x_24; uint8_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 9);
x_25 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 10);
lean_ctor_set_uint8(x_13, 9, x_1);
x_26 = 2;
x_27 = lean_uint64_shift_right(x_15, x_26);
x_28 = lean_uint64_shift_left(x_27, x_26);
x_29 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
x_30 = lean_uint64_lor(x_28, x_29);
x_31 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_31, 0, x_13);
lean_ctor_set(x_31, 1, x_17);
lean_ctor_set(x_31, 2, x_18);
lean_ctor_set(x_31, 3, x_19);
lean_ctor_set(x_31, 4, x_20);
lean_ctor_set(x_31, 5, x_21);
lean_ctor_set(x_31, 6, x_22);
lean_ctor_set_uint64(x_31, sizeof(void*)*7, x_30);
lean_ctor_set_uint8(x_31, sizeof(void*)*7 + 8, x_16);
lean_ctor_set_uint8(x_31, sizeof(void*)*7 + 9, x_24);
lean_ctor_set_uint8(x_31, sizeof(void*)*7 + 10, x_25);
x_32 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_33 = l_Lean_Meta_kabstract(x_2, x_14, x_32, x_31, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
x_37 = l_Lean_Expr_hasLooseBVars(x_35);
lean_dec(x_35);
if (x_37 == 0)
{
size_t x_38; size_t x_39; 
lean_free_object(x_33);
x_38 = 1;
x_39 = lean_usize_add(x_4, x_38);
x_4 = x_39;
x_10 = x_36;
goto _start;
}
else
{
uint8_t x_41; lean_object* x_42; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_41 = 1;
x_42 = lean_box(x_41);
lean_ctor_set(x_33, 0, x_42);
return x_33;
}
}
else
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_33, 0);
x_44 = lean_ctor_get(x_33, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_33);
x_45 = l_Lean_Expr_hasLooseBVars(x_43);
lean_dec(x_43);
if (x_45 == 0)
{
size_t x_46; size_t x_47; 
x_46 = 1;
x_47 = lean_usize_add(x_4, x_46);
x_4 = x_47;
x_10 = x_44;
goto _start;
}
else
{
uint8_t x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_49 = 1;
x_50 = lean_box(x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_44);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_33);
if (x_52 == 0)
{
return x_33;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_33, 0);
x_54 = lean_ctor_get(x_33, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_33);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; lean_object* x_75; uint64_t x_76; uint64_t x_77; uint64_t x_78; uint64_t x_79; uint64_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_56 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 9);
x_57 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 10);
x_58 = lean_ctor_get_uint8(x_13, 0);
x_59 = lean_ctor_get_uint8(x_13, 1);
x_60 = lean_ctor_get_uint8(x_13, 2);
x_61 = lean_ctor_get_uint8(x_13, 3);
x_62 = lean_ctor_get_uint8(x_13, 4);
x_63 = lean_ctor_get_uint8(x_13, 5);
x_64 = lean_ctor_get_uint8(x_13, 6);
x_65 = lean_ctor_get_uint8(x_13, 7);
x_66 = lean_ctor_get_uint8(x_13, 8);
x_67 = lean_ctor_get_uint8(x_13, 10);
x_68 = lean_ctor_get_uint8(x_13, 11);
x_69 = lean_ctor_get_uint8(x_13, 12);
x_70 = lean_ctor_get_uint8(x_13, 13);
x_71 = lean_ctor_get_uint8(x_13, 14);
x_72 = lean_ctor_get_uint8(x_13, 15);
x_73 = lean_ctor_get_uint8(x_13, 16);
x_74 = lean_ctor_get_uint8(x_13, 17);
lean_dec(x_13);
x_75 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_75, 0, x_58);
lean_ctor_set_uint8(x_75, 1, x_59);
lean_ctor_set_uint8(x_75, 2, x_60);
lean_ctor_set_uint8(x_75, 3, x_61);
lean_ctor_set_uint8(x_75, 4, x_62);
lean_ctor_set_uint8(x_75, 5, x_63);
lean_ctor_set_uint8(x_75, 6, x_64);
lean_ctor_set_uint8(x_75, 7, x_65);
lean_ctor_set_uint8(x_75, 8, x_66);
lean_ctor_set_uint8(x_75, 9, x_1);
lean_ctor_set_uint8(x_75, 10, x_67);
lean_ctor_set_uint8(x_75, 11, x_68);
lean_ctor_set_uint8(x_75, 12, x_69);
lean_ctor_set_uint8(x_75, 13, x_70);
lean_ctor_set_uint8(x_75, 14, x_71);
lean_ctor_set_uint8(x_75, 15, x_72);
lean_ctor_set_uint8(x_75, 16, x_73);
lean_ctor_set_uint8(x_75, 17, x_74);
x_76 = 2;
x_77 = lean_uint64_shift_right(x_15, x_76);
x_78 = lean_uint64_shift_left(x_77, x_76);
x_79 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
x_80 = lean_uint64_lor(x_78, x_79);
x_81 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_81, 0, x_75);
lean_ctor_set(x_81, 1, x_17);
lean_ctor_set(x_81, 2, x_18);
lean_ctor_set(x_81, 3, x_19);
lean_ctor_set(x_81, 4, x_20);
lean_ctor_set(x_81, 5, x_21);
lean_ctor_set(x_81, 6, x_22);
lean_ctor_set_uint64(x_81, sizeof(void*)*7, x_80);
lean_ctor_set_uint8(x_81, sizeof(void*)*7 + 8, x_16);
lean_ctor_set_uint8(x_81, sizeof(void*)*7 + 9, x_56);
lean_ctor_set_uint8(x_81, sizeof(void*)*7 + 10, x_57);
x_82 = lean_box(0);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_83 = l_Lean_Meta_kabstract(x_2, x_14, x_82, x_81, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_86 = x_83;
} else {
 lean_dec_ref(x_83);
 x_86 = lean_box(0);
}
x_87 = l_Lean_Expr_hasLooseBVars(x_84);
lean_dec(x_84);
if (x_87 == 0)
{
size_t x_88; size_t x_89; 
lean_dec(x_86);
x_88 = 1;
x_89 = lean_usize_add(x_4, x_88);
x_4 = x_89;
x_10 = x_85;
goto _start;
}
else
{
uint8_t x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_91 = 1;
x_92 = lean_box(x_91);
if (lean_is_scalar(x_86)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_86;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_85);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_94 = lean_ctor_get(x_83, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_83, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_96 = x_83;
} else {
 lean_dec_ref(x_83);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
}
else
{
uint8_t x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_98 = 0;
x_99 = lean_box(x_98);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_10);
return x_100;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_generalizeHyp___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_5, x_4);
if (x_7 == 0)
{
return x_6;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_uget(x_3, x_5);
x_9 = !lean_is_exclusive(x_6);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_6, 0);
x_11 = lean_ctor_get(x_6, 1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 2);
lean_inc(x_14);
x_15 = lean_nat_dec_lt(x_13, x_14);
if (x_15 == 0)
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_8);
return x_6;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; 
x_17 = lean_ctor_get(x_10, 2);
lean_dec(x_17);
x_18 = lean_ctor_get(x_10, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_10, 0);
lean_dec(x_19);
x_20 = lean_array_fget(x_12, x_13);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_13, x_21);
lean_dec(x_13);
lean_ctor_set(x_10, 1, x_22);
x_23 = l_Lean_Expr_fvar___override(x_20);
x_24 = l_Lean_Meta_FVarSubst_insert(x_11, x_8, x_23);
lean_ctor_set(x_6, 1, x_24);
x_25 = 1;
x_26 = lean_usize_add(x_5, x_25);
x_5 = x_26;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; size_t x_34; size_t x_35; 
lean_dec(x_10);
x_28 = lean_array_fget(x_12, x_13);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_13, x_29);
lean_dec(x_13);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_12);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_14);
x_32 = l_Lean_Expr_fvar___override(x_28);
x_33 = l_Lean_Meta_FVarSubst_insert(x_11, x_8, x_32);
lean_ctor_set(x_6, 1, x_33);
lean_ctor_set(x_6, 0, x_31);
x_34 = 1;
x_35 = lean_usize_add(x_5, x_34);
x_5 = x_35;
goto _start;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_37 = lean_ctor_get(x_6, 0);
x_38 = lean_ctor_get(x_6, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_6);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_37, 2);
lean_inc(x_41);
x_42 = lean_nat_dec_lt(x_40, x_41);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_8);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_38);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; size_t x_52; size_t x_53; 
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 x_44 = x_37;
} else {
 lean_dec_ref(x_37);
 x_44 = lean_box(0);
}
x_45 = lean_array_fget(x_39, x_40);
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_add(x_40, x_46);
lean_dec(x_40);
if (lean_is_scalar(x_44)) {
 x_48 = lean_alloc_ctor(0, 3, 0);
} else {
 x_48 = x_44;
}
lean_ctor_set(x_48, 0, x_39);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_48, 2, x_41);
x_49 = l_Lean_Expr_fvar___override(x_45);
x_50 = l_Lean_Meta_FVarSubst_insert(x_38, x_8, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_50);
x_52 = 1;
x_53 = lean_usize_add(x_5, x_52);
x_5 = x_53;
x_6 = x_51;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_generalizeHyp___spec__4(uint8_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_5, x_6);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_uget(x_4, x_5);
lean_inc(x_8);
lean_inc(x_14);
x_15 = l_Lean_FVarId_getType(x_14, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_16, x_8, x_9, x_10, x_11, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_array_get_size(x_3);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_dec_lt(x_22, x_21);
if (x_23 == 0)
{
size_t x_24; size_t x_25; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_14);
x_24 = 1;
x_25 = lean_usize_add(x_5, x_24);
x_5 = x_25;
x_12 = x_20;
goto _start;
}
else
{
size_t x_27; lean_object* x_28; 
x_27 = lean_usize_of_nat(x_21);
lean_dec(x_21);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_28 = l_Array_anyMUnsafe_any___at_Lean_MVarId_generalizeHyp___spec__2(x_1, x_19, x_3, x_2, x_27, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; size_t x_32; size_t x_33; 
lean_dec(x_14);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = 1;
x_33 = lean_usize_add(x_5, x_32);
x_5 = x_33;
x_12 = x_31;
goto _start;
}
else
{
lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; 
x_35 = lean_ctor_get(x_28, 1);
lean_inc(x_35);
lean_dec(x_28);
x_36 = lean_array_push(x_7, x_14);
x_37 = 1;
x_38 = lean_usize_add(x_5, x_37);
x_5 = x_38;
x_7 = x_36;
x_12 = x_35;
goto _start;
}
}
else
{
uint8_t x_40; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_40 = !lean_is_exclusive(x_28);
if (x_40 == 0)
{
return x_28;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_28, 0);
x_42 = lean_ctor_get(x_28, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_28);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_44 = !lean_is_exclusive(x_15);
if (x_44 == 0)
{
return x_15;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_15, 0);
x_46 = lean_ctor_get(x_15, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_15);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_7);
lean_ctor_set(x_48, 1, x_12);
return x_48;
}
}
}
static lean_object* _init_l_Lean_MVarId_generalizeHyp___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_generalizeHyp___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_12 = lean_array_size(x_1);
x_13 = 0;
x_14 = l_Array_mapMUnsafe_map___at_Lean_MVarId_generalizeHyp___spec__1(x_12, x_13, x_1, x_7, x_8, x_9, x_10, x_11);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_array_get_size(x_2);
x_18 = lean_box(0);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_lt(x_19, x_17);
if (x_20 == 0)
{
lean_object* x_141; 
lean_dec(x_17);
x_141 = l_Lean_MVarId_generalizeHyp___lambda__1___closed__1;
x_21 = x_141;
x_22 = x_16;
goto block_140;
}
else
{
uint8_t x_142; 
x_142 = lean_nat_dec_le(x_17, x_17);
if (x_142 == 0)
{
lean_object* x_143; 
lean_dec(x_17);
x_143 = l_Lean_MVarId_generalizeHyp___lambda__1___closed__1;
x_21 = x_143;
x_22 = x_16;
goto block_140;
}
else
{
size_t x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_145 = l_Lean_MVarId_generalizeHyp___lambda__1___closed__1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_146 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_generalizeHyp___spec__4(x_4, x_13, x_15, x_2, x_13, x_144, x_145, x_7, x_8, x_9, x_10, x_16);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_21 = x_147;
x_22 = x_148;
goto block_140;
}
else
{
uint8_t x_149; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_149 = !lean_is_exclusive(x_146);
if (x_149 == 0)
{
return x_146;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_146, 0);
x_151 = lean_ctor_get(x_146, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_146);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
}
block_140:
{
uint8_t x_23; uint8_t x_24; lean_object* x_25; 
x_23 = 1;
x_24 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_25 = l_Lean_MVarId_revert(x_3, x_21, x_23, x_24, x_7, x_8, x_9, x_10, x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_26, 0);
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_31 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(x_30, x_15, x_4, x_7, x_8, x_9, x_10, x_27);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = !lean_is_exclusive(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_32, 0);
x_36 = lean_ctor_get(x_32, 1);
x_37 = lean_array_get_size(x_29);
x_38 = l_Lean_Meta_introNCore(x_36, x_37, x_18, x_24, x_23, x_7, x_8, x_9, x_10, x_33);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_array_get_size(x_42);
x_44 = l_Array_toSubarray___rarg(x_42, x_19, x_43);
x_45 = lean_box(0);
lean_ctor_set(x_26, 1, x_5);
lean_ctor_set(x_26, 0, x_44);
x_46 = lean_array_size(x_29);
x_47 = l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_generalizeHyp___spec__3(x_29, x_45, x_29, x_46, x_13, x_26);
lean_dec(x_29);
lean_ctor_set(x_40, 0, x_35);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
lean_ctor_set(x_32, 1, x_40);
lean_ctor_set(x_32, 0, x_48);
lean_ctor_set(x_38, 0, x_32);
return x_38;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; size_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_49 = lean_ctor_get(x_40, 0);
x_50 = lean_ctor_get(x_40, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_40);
x_51 = lean_array_get_size(x_49);
x_52 = l_Array_toSubarray___rarg(x_49, x_19, x_51);
x_53 = lean_box(0);
lean_ctor_set(x_26, 1, x_5);
lean_ctor_set(x_26, 0, x_52);
x_54 = lean_array_size(x_29);
x_55 = l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_generalizeHyp___spec__3(x_29, x_53, x_29, x_54, x_13, x_26);
lean_dec(x_29);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_35);
lean_ctor_set(x_56, 1, x_50);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
lean_ctor_set(x_32, 1, x_56);
lean_ctor_set(x_32, 0, x_57);
lean_ctor_set(x_38, 0, x_32);
return x_38;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; size_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_58 = lean_ctor_get(x_38, 0);
x_59 = lean_ctor_get(x_38, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_38);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_62 = x_58;
} else {
 lean_dec_ref(x_58);
 x_62 = lean_box(0);
}
x_63 = lean_array_get_size(x_60);
x_64 = l_Array_toSubarray___rarg(x_60, x_19, x_63);
x_65 = lean_box(0);
lean_ctor_set(x_26, 1, x_5);
lean_ctor_set(x_26, 0, x_64);
x_66 = lean_array_size(x_29);
x_67 = l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_generalizeHyp___spec__3(x_29, x_65, x_29, x_66, x_13, x_26);
lean_dec(x_29);
if (lean_is_scalar(x_62)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_62;
}
lean_ctor_set(x_68, 0, x_35);
lean_ctor_set(x_68, 1, x_61);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
lean_ctor_set(x_32, 1, x_68);
lean_ctor_set(x_32, 0, x_69);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_32);
lean_ctor_set(x_70, 1, x_59);
return x_70;
}
}
else
{
uint8_t x_71; 
lean_free_object(x_32);
lean_dec(x_35);
lean_free_object(x_26);
lean_dec(x_29);
lean_dec(x_5);
x_71 = !lean_is_exclusive(x_38);
if (x_71 == 0)
{
return x_38;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_38, 0);
x_73 = lean_ctor_get(x_38, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_38);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_32, 0);
x_76 = lean_ctor_get(x_32, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_32);
x_77 = lean_array_get_size(x_29);
x_78 = l_Lean_Meta_introNCore(x_76, x_77, x_18, x_24, x_23, x_7, x_8, x_9, x_10, x_33);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; size_t x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_81 = x_78;
} else {
 lean_dec_ref(x_78);
 x_81 = lean_box(0);
}
x_82 = lean_ctor_get(x_79, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_79, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_84 = x_79;
} else {
 lean_dec_ref(x_79);
 x_84 = lean_box(0);
}
x_85 = lean_array_get_size(x_82);
x_86 = l_Array_toSubarray___rarg(x_82, x_19, x_85);
x_87 = lean_box(0);
lean_ctor_set(x_26, 1, x_5);
lean_ctor_set(x_26, 0, x_86);
x_88 = lean_array_size(x_29);
x_89 = l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_generalizeHyp___spec__3(x_29, x_87, x_29, x_88, x_13, x_26);
lean_dec(x_29);
if (lean_is_scalar(x_84)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_84;
}
lean_ctor_set(x_90, 0, x_75);
lean_ctor_set(x_90, 1, x_83);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
if (lean_is_scalar(x_81)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_81;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_80);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_75);
lean_free_object(x_26);
lean_dec(x_29);
lean_dec(x_5);
x_94 = lean_ctor_get(x_78, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_78, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_96 = x_78;
} else {
 lean_dec_ref(x_78);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_free_object(x_26);
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_98 = !lean_is_exclusive(x_31);
if (x_98 == 0)
{
return x_31;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_31, 0);
x_100 = lean_ctor_get(x_31, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_31);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_26, 0);
x_103 = lean_ctor_get(x_26, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_26);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_104 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(x_103, x_15, x_4, x_7, x_8, x_9, x_10, x_27);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_ctor_get(x_105, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_105, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_109 = x_105;
} else {
 lean_dec_ref(x_105);
 x_109 = lean_box(0);
}
x_110 = lean_array_get_size(x_102);
x_111 = l_Lean_Meta_introNCore(x_108, x_110, x_18, x_24, x_23, x_7, x_8, x_9, x_10, x_106);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; size_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_114 = x_111;
} else {
 lean_dec_ref(x_111);
 x_114 = lean_box(0);
}
x_115 = lean_ctor_get(x_112, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_112, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_117 = x_112;
} else {
 lean_dec_ref(x_112);
 x_117 = lean_box(0);
}
x_118 = lean_array_get_size(x_115);
x_119 = l_Array_toSubarray___rarg(x_115, x_19, x_118);
x_120 = lean_box(0);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_5);
x_122 = lean_array_size(x_102);
x_123 = l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_generalizeHyp___spec__3(x_102, x_120, x_102, x_122, x_13, x_121);
lean_dec(x_102);
if (lean_is_scalar(x_117)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_117;
}
lean_ctor_set(x_124, 0, x_107);
lean_ctor_set(x_124, 1, x_116);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
if (lean_is_scalar(x_109)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_109;
}
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_124);
if (lean_is_scalar(x_114)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_114;
}
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_113);
return x_127;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_109);
lean_dec(x_107);
lean_dec(x_102);
lean_dec(x_5);
x_128 = lean_ctor_get(x_111, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_111, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_130 = x_111;
} else {
 lean_dec_ref(x_111);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(1, 2, 0);
} else {
 x_131 = x_130;
}
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_129);
return x_131;
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_102);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_132 = lean_ctor_get(x_104, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_104, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_134 = x_104;
} else {
 lean_dec_ref(x_104);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_132);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
}
}
else
{
uint8_t x_136; 
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_136 = !lean_is_exclusive(x_25);
if (x_136 == 0)
{
return x_25;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_25, 0);
x_138 = lean_ctor_get(x_25, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_25);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_generalizeHyp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = l_Array_isEmpty___rarg(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = l_Lean_MVarId_generalizeHyp___lambda__1(x_2, x_3, x_1, x_5, x_4, x_12, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore(x_1, x_2, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_4);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_MVarId_generalizeHyp___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Array_mapMUnsafe_map___at_Lean_MVarId_generalizeHyp___spec__1(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_Lean_MVarId_generalizeHyp___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_anyMUnsafe_any___at_Lean_MVarId_generalizeHyp___spec__2(x_11, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_generalizeHyp___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_forIn_x27Unsafe_loop___at_Lean_MVarId_generalizeHyp___spec__3(x_1, x_2, x_3, x_7, x_8, x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_MVarId_generalizeHyp___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_17 = l_Array_foldlMUnsafe_fold___at_Lean_MVarId_generalizeHyp___spec__4(x_13, x_14, x_3, x_4, x_15, x_16, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_3);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_generalizeHyp___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Lean_MVarId_generalizeHyp___lambda__1(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_generalizeHyp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = l_Lean_MVarId_generalizeHyp(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
return x_12;
}
}
lean_object* initialize_Lean_Meta_KAbstract(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Intro(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_FVarSubst(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Revert(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Generalize(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_KAbstract(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Intro(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_FVarSubst(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Revert(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_instInhabitedGeneralizeArg___closed__1 = _init_l_Lean_Meta_instInhabitedGeneralizeArg___closed__1();
lean_mark_persistent(l_Lean_Meta_instInhabitedGeneralizeArg___closed__1);
l_Lean_Meta_instInhabitedGeneralizeArg___closed__2 = _init_l_Lean_Meta_instInhabitedGeneralizeArg___closed__2();
lean_mark_persistent(l_Lean_Meta_instInhabitedGeneralizeArg___closed__2);
l_Lean_Meta_instInhabitedGeneralizeArg___closed__3 = _init_l_Lean_Meta_instInhabitedGeneralizeArg___closed__3();
lean_mark_persistent(l_Lean_Meta_instInhabitedGeneralizeArg___closed__3);
l_Lean_Meta_instInhabitedGeneralizeArg___closed__4 = _init_l_Lean_Meta_instInhabitedGeneralizeArg___closed__4();
lean_mark_persistent(l_Lean_Meta_instInhabitedGeneralizeArg___closed__4);
l_Lean_Meta_instInhabitedGeneralizeArg = _init_l_Lean_Meta_instInhabitedGeneralizeArg();
lean_mark_persistent(l_Lean_Meta_instInhabitedGeneralizeArg);
l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___closed__1 = _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___closed__1);
l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___closed__2 = _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore_go___closed__2);
l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lambda__3___closed__1 = _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lambda__3___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lambda__3___closed__1);
l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lambda__3___closed__2 = _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lambda__3___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lambda__3___closed__2);
l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lambda__3___closed__3 = _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lambda__3___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lambda__3___closed__3);
l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lambda__3___closed__4 = _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lambda__3___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___lambda__3___closed__4);
l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__1 = _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__1);
l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__2 = _init_l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Generalize_0__Lean_Meta_generalizeCore___closed__2);
l_Lean_MVarId_generalizeHyp___lambda__1___closed__1 = _init_l_Lean_MVarId_generalizeHyp___lambda__1___closed__1();
lean_mark_persistent(l_Lean_MVarId_generalizeHyp___lambda__1___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
