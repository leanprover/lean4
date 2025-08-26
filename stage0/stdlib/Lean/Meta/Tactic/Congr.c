// Lean compiler output
// Module: Lean.Meta.Tactic.Congr
// Imports: Lean.Meta.CongrTheorems Lean.Meta.Tactic.Assert Lean.Meta.Tactic.Apply Lean.Meta.Tactic.Clear Lean.Meta.Tactic.Refl Lean.Meta.Tactic.Assumption
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
lean_object* l_Lean_MVarId_assumptionCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_post___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_congrImplies_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_MVarId_congrImplies_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_congr_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__1;
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* l_Lean_Meta_getTransparency___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_eqOfHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_congrCore___closed__1;
lean_object* l_Lean_MVarId_getType_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_congr_x3f___lam__0___closed__0;
lean_object* l_Lean_MVarId_refl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_____private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go_spec__0(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_congrImplies_x3f___lam__0___closed__4;
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_post(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_heqOfEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_MVarId_congrImplies_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_congrImplies_x3f___lam__0___closed__0;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__0;
static lean_object* l_Lean_MVarId_congrImplies_x3f___lam__0___closed__1;
static lean_object* l_Lean_MVarId_congr_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_MVarId_congrN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_hcongr_x3f___lam__0___closed__0;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___Lean_commitWhenSomeNoEx_x3f___at___Lean_MVarId_congr_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_List_forM___at_____private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_congr_x3f___lam__0___closed__1;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_congrImplies_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_MVarId_congrImplies_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHCongrWithArity(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_hcongr_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_congrN(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_congrImplies_x3f___lam__0___closed__3;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_congrPre(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_congrCore___closed__2;
lean_object* l_Lean_Core_mkFreshUserName(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___Lean_MVarId_congrImplies_x3f_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_MVarId_congrImplies_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___Lean_commitWhenSomeNoEx_x3f___at___Lean_MVarId_congr_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitWhenSomeNoEx_x3f___at___Lean_MVarId_congr_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_congrN___closed__0;
LEAN_EXPORT lean_object* l_Lean_MVarId_hcongr_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_hcongr_x3f___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_commitWhenSomeNoEx_x3f___at___Lean_MVarId_congr_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_MVarId_congrImplies_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_congr_x3f___closed__0;
static uint64_t l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__2;
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_congr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_mkCongrSimp_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
lean_object* l_Lean_MVarId_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_MVarId_congr_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Meta_beqTransparencyMode____x40_Init_MetaTypes_2581322616____hygCtx___hyg_9_(uint8_t, uint8_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___Lean_MVarId_congrImplies_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_MVarId_congr_x3f_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_congrCore___closed__3;
LEAN_EXPORT lean_object* l_Lean_MVarId_hcongr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_congrImplies_x3f___closed__1;
static lean_object* l_Lean_MVarId_congrImplies_x3f___closed__0;
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
static lean_object* l_Lean_MVarId_congrCore___closed__0;
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_congrImplies_x3f___lam__0___closed__2;
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_congrCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_MVarId_congrImplies_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_____private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_hrefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_congrPre(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_7 = l_Lean_MVarId_heqOfEq(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_35; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_10 = x_7;
} else {
 lean_dec_ref(x_7);
 x_10 = lean_box(0);
}
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_8);
x_35 = l_Lean_MVarId_refl(x_8, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_ctor_set(x_35, 0, x_38);
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_59; 
x_42 = lean_ctor_get(x_35, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_35, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_44 = x_35;
} else {
 lean_dec_ref(x_35);
 x_44 = lean_box(0);
}
x_59 = l_Lean_Exception_isInterrupt(x_42);
if (x_59 == 0)
{
uint8_t x_60; 
x_60 = l_Lean_Exception_isRuntime(x_42);
x_45 = x_60;
goto block_58;
}
else
{
x_45 = x_59;
goto block_58;
}
block_58:
{
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_44);
lean_dec(x_42);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_8);
x_46 = l_Lean_MVarId_hrefl(x_8, x_2, x_3, x_4, x_5, x_43);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_47; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
x_49 = lean_box(0);
lean_ctor_set(x_46, 0, x_49);
return x_46;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_46, 1);
lean_inc(x_50);
lean_dec(x_46);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = lean_ctor_get(x_46, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_46, 1);
lean_inc(x_54);
lean_dec_ref(x_46);
x_55 = l_Lean_Exception_isInterrupt(x_53);
if (x_55 == 0)
{
uint8_t x_56; 
x_56 = l_Lean_Exception_isRuntime(x_53);
x_11 = x_53;
x_12 = x_54;
x_13 = x_56;
goto block_34;
}
else
{
x_11 = x_53;
x_12 = x_54;
x_13 = x_55;
goto block_34;
}
}
}
else
{
lean_object* x_57; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
if (lean_is_scalar(x_44)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_44;
}
lean_ctor_set(x_57, 0, x_42);
lean_ctor_set(x_57, 1, x_43);
return x_57;
}
}
}
block_34:
{
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec_ref(x_11);
lean_dec(x_10);
lean_inc(x_8);
x_14 = l_Lean_MVarId_assumptionCore(x_8, x_2, x_3, x_4, x_5, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_8);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_8);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_14, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_14, 0, x_25);
return x_14;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_8);
x_29 = !lean_is_exclusive(x_14);
if (x_29 == 0)
{
return x_14;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_14, 0);
x_31 = lean_ctor_get(x_14, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_14);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
if (lean_is_scalar(x_10)) {
 x_33 = lean_alloc_ctor(1, 2, 0);
} else {
 x_33 = x_10;
 lean_ctor_set_tag(x_33, 1);
}
lean_ctor_set(x_33, 0, x_11);
lean_ctor_set(x_33, 1, x_12);
return x_33;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_61 = !lean_is_exclusive(x_7);
if (x_61 == 0)
{
return x_7;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_7, 0);
x_63 = lean_ctor_get(x_7, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_7);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_____private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_9 = l_List_reverse___redArg(x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_1);
x_14 = l_Lean_MVarId_tryClear(x_12, x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_15);
{
lean_object* _tmp_1 = x_13;
lean_object* _tmp_2 = x_2;
lean_object* _tmp_7 = x_16;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_8 = _tmp_7;
}
goto _start;
}
else
{
uint8_t x_18; 
lean_free_object(x_2);
lean_dec(x_13);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_14);
if (x_18 == 0)
{
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 0);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_14);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_2, 0);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_2);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_1);
x_24 = l_Lean_MVarId_tryClear(x_22, x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec_ref(x_24);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_3);
x_2 = x_23;
x_3 = x_27;
x_8 = x_26;
goto _start;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_23);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_31 = x_24;
} else {
 lean_dec_ref(x_24);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(1, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("h_congr_thm", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__2() {
_start:
{
uint8_t x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_1 = 1;
x_2 = 0;
x_3 = 0;
x_4 = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(x_4, 0, x_3);
lean_ctor_set_uint8(x_4, 1, x_2);
lean_ctor_set_uint8(x_4, 2, x_2);
lean_ctor_set_uint8(x_4, 3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__1;
lean_inc(x_6);
lean_inc_ref(x_5);
x_9 = l_Lean_Core_mkFreshUserName(x_8, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_ctor_get(x_2, 0);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_13);
lean_dec_ref(x_2);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_14 = l_Lean_MVarId_assert(x_1, x_10, x_12, x_13, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
x_17 = 1;
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_18 = l_Lean_Meta_intro1Core(x_15, x_17, x_3, x_4, x_5, x_6, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
lean_inc(x_21);
x_23 = l_Lean_mkFVar(x_21);
x_24 = l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__2;
x_25 = lean_box(0);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_26 = l_Lean_MVarId_apply(x_22, x_23, x_24, x_25, x_3, x_4, x_5, x_6, x_20);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = lean_box(0);
x_30 = l_List_mapM_loop___at_____private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f_spec__0(x_21, x_27, x_29, x_3, x_4, x_5, x_6, x_28);
return x_30;
}
else
{
lean_dec(x_21);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_26;
}
}
else
{
uint8_t x_31; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_31 = !lean_is_exclusive(x_18);
if (x_31 == 0)
{
return x_18;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_18, 0);
x_33 = lean_ctor_get(x_18, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_18);
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
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_35 = !lean_is_exclusive(x_14);
if (x_35 == 0)
{
return x_14;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_14, 0);
x_37 = lean_ctor_get(x_14, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_14);
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
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_9);
if (x_39 == 0)
{
return x_9;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_9, 0);
x_41 = lean_ctor_get(x_9, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_9);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___Lean_commitWhenSomeNoEx_x3f___at___Lean_MVarId_congr_x3f_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_saveState___redArg(x_3, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_25; lean_object* x_26; lean_object* x_30; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_10 = x_7;
} else {
 lean_dec_ref(x_7);
 x_10 = lean_box(0);
}
lean_inc(x_5);
lean_inc(x_3);
x_30 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec_ref(x_30);
x_33 = l_Lean_Meta_SavedState_restore___redArg(x_8, x_3, x_5, x_32);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set(x_33, 0, x_31);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_33, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_dec_ref(x_33);
x_25 = x_38;
x_26 = x_39;
goto block_29;
}
}
else
{
lean_dec_ref(x_31);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
return x_30;
}
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_30, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_30, 1);
lean_inc(x_41);
lean_dec_ref(x_30);
x_25 = x_40;
x_26 = x_41;
goto block_29;
}
block_24:
{
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
x_14 = l_Lean_Meta_SavedState_restore___redArg(x_8, x_3, x_5, x_12);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_8);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_11);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec_ref(x_11);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
if (lean_is_scalar(x_10)) {
 x_23 = lean_alloc_ctor(1, 2, 0);
} else {
 x_23 = x_10;
 lean_ctor_set_tag(x_23, 1);
}
lean_ctor_set(x_23, 0, x_11);
lean_ctor_set(x_23, 1, x_12);
return x_23;
}
}
block_29:
{
uint8_t x_27; 
x_27 = l_Lean_Exception_isInterrupt(x_25);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = l_Lean_Exception_isRuntime(x_25);
x_11 = x_25;
x_12 = x_26;
x_13 = x_28;
goto block_24;
}
else
{
x_11 = x_25;
x_12 = x_26;
x_13 = x_27;
goto block_24;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_42 = !lean_is_exclusive(x_7);
if (x_42 == 0)
{
return x_7;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_7, 0);
x_44 = lean_ctor_get(x_7, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_7);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSome_x3f___at___Lean_commitWhenSomeNoEx_x3f___at___Lean_MVarId_congr_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_commitWhenSome_x3f___at___Lean_commitWhenSomeNoEx_x3f___at___Lean_MVarId_congr_x3f_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSomeNoEx_x3f___at___Lean_MVarId_congr_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_commitWhenSome_x3f___at___Lean_commitWhenSomeNoEx_x3f___at___Lean_MVarId_congr_x3f_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_18; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
x_18 = l_Lean_Exception_isInterrupt(x_8);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = l_Lean_Exception_isRuntime(x_8);
lean_dec(x_8);
x_10 = x_19;
goto block_17;
}
else
{
lean_dec(x_8);
x_10 = x_18;
goto block_17;
}
block_17:
{
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_7, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_7);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_9);
return x_16;
}
}
else
{
lean_dec(x_9);
return x_7;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhenSomeNoEx_x3f___at___Lean_MVarId_congr_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_commitWhenSomeNoEx_x3f___at___Lean_MVarId_congr_x3f_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_MVarId_congr_x3f_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_MVarId_congr_x3f_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_withContext___at___Lean_MVarId_congr_x3f_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_MVarId_congr_x3f___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_congr_x3f___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_congr_x3f___lam__0___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_congr_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec_ref(x_8);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_1);
x_10 = l_Lean_MVarId_getType_x27(x_1, x_3, x_4, x_5, x_6, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = l_Lean_MVarId_congr_x3f___lam__0___closed__1;
x_15 = lean_unsigned_to_nat(3u);
x_16 = l_Lean_Expr_isAppOfArity(x_12, x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_17 = lean_box(0);
lean_ctor_set(x_10, 0, x_17);
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = l_Lean_Expr_appFn_x21(x_12);
lean_dec(x_12);
x_19 = l_Lean_Expr_appArg_x21(x_18);
lean_dec_ref(x_18);
x_20 = l_Lean_Expr_cleanupAnnotations(x_19);
x_21 = l_Lean_Expr_isApp(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec_ref(x_20);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_22 = lean_box(0);
lean_ctor_set(x_10, 0, x_22);
return x_10;
}
else
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_free_object(x_10);
x_23 = l_Lean_Expr_getAppFn(x_20);
x_24 = 0;
x_25 = l_Lean_Expr_getAppNumArgs(x_20);
lean_dec_ref(x_20);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_27 = l_Lean_Meta_mkCongrSimp_x3f(x_23, x_24, x_26, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 0);
lean_dec(x_30);
x_31 = lean_box(0);
lean_ctor_set(x_27, 0, x_31);
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_dec(x_27);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_27, 1);
lean_inc(x_35);
lean_dec_ref(x_27);
x_36 = !lean_is_exclusive(x_28);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_28, 0);
x_38 = l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f(x_1, x_37, x_3, x_4, x_5, x_6, x_35);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_ctor_set(x_28, 0, x_40);
lean_ctor_set(x_38, 0, x_28);
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_38, 0);
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_38);
lean_ctor_set(x_28, 0, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_28);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_free_object(x_28);
x_44 = !lean_is_exclusive(x_38);
if (x_44 == 0)
{
return x_38;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_38, 0);
x_46 = lean_ctor_get(x_38, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_38);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_28, 0);
lean_inc(x_48);
lean_dec(x_28);
x_49 = l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f(x_1, x_48, x_3, x_4, x_5, x_6, x_35);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_52 = x_49;
} else {
 lean_dec_ref(x_49);
 x_52 = lean_box(0);
}
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_50);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_49, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_57 = x_49;
} else {
 lean_dec_ref(x_49);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_27);
if (x_59 == 0)
{
return x_27;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_27, 0);
x_61 = lean_ctor_get(x_27, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_27);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_63 = lean_ctor_get(x_10, 0);
x_64 = lean_ctor_get(x_10, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_10);
x_65 = l_Lean_MVarId_congr_x3f___lam__0___closed__1;
x_66 = lean_unsigned_to_nat(3u);
x_67 = l_Lean_Expr_isAppOfArity(x_63, x_65, x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_63);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_64);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_70 = l_Lean_Expr_appFn_x21(x_63);
lean_dec(x_63);
x_71 = l_Lean_Expr_appArg_x21(x_70);
lean_dec_ref(x_70);
x_72 = l_Lean_Expr_cleanupAnnotations(x_71);
x_73 = l_Lean_Expr_isApp(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
lean_dec_ref(x_72);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_64);
return x_75;
}
else
{
lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = l_Lean_Expr_getAppFn(x_72);
x_77 = 0;
x_78 = l_Lean_Expr_getAppNumArgs(x_72);
lean_dec_ref(x_72);
x_79 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_79, 0, x_78);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_80 = l_Lean_Meta_mkCongrSimp_x3f(x_76, x_77, x_79, x_3, x_4, x_5, x_6, x_64);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_83 = x_80;
} else {
 lean_dec_ref(x_80);
 x_83 = lean_box(0);
}
x_84 = lean_box(0);
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_83;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_82);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_80, 1);
lean_inc(x_86);
lean_dec_ref(x_80);
x_87 = lean_ctor_get(x_81, 0);
lean_inc(x_87);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 x_88 = x_81;
} else {
 lean_dec_ref(x_81);
 x_88 = lean_box(0);
}
x_89 = l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f(x_1, x_87, x_3, x_4, x_5, x_6, x_86);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_92 = x_89;
} else {
 lean_dec_ref(x_89);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_93 = lean_alloc_ctor(1, 1, 0);
} else {
 x_93 = x_88;
}
lean_ctor_set(x_93, 0, x_90);
if (lean_is_scalar(x_92)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_92;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_91);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_88);
x_95 = lean_ctor_get(x_89, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_89, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_97 = x_89;
} else {
 lean_dec_ref(x_89);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_99 = lean_ctor_get(x_80, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_80, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_101 = x_80;
} else {
 lean_dec_ref(x_80);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
}
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_103 = !lean_is_exclusive(x_10);
if (x_103 == 0)
{
return x_10;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_10, 0);
x_105 = lean_ctor_get(x_10, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_10);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_8);
if (x_107 == 0)
{
return x_8;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_8, 0);
x_109 = lean_ctor_get(x_8, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_8);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
}
static lean_object* _init_l_Lean_MVarId_congr_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("congr", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_congr_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_congr_x3f___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_congr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_MVarId_congr_x3f___closed__1;
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_MVarId_congr_x3f___lam__0), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_commitWhenSomeNoEx_x3f___at___Lean_MVarId_congr_x3f_spec__0), 7, 2);
lean_closure_set(x_9, 0, lean_box(0));
lean_closure_set(x_9, 1, x_8);
x_10 = l_Lean_MVarId_withContext___at___Lean_MVarId_congr_x3f_spec__2___redArg(x_1, x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
static lean_object* _init_l_Lean_MVarId_hcongr_x3f___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HEq", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_hcongr_x3f___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_hcongr_x3f___lam__0___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_hcongr_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_7 = l_Lean_MVarId_getType_x27(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = l_Lean_MVarId_hcongr_x3f___lam__0___closed__1;
x_12 = lean_unsigned_to_nat(4u);
x_13 = l_Lean_Expr_isAppOfArity(x_9, x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = l_Lean_Expr_appFn_x21(x_9);
lean_dec(x_9);
x_16 = l_Lean_Expr_appFn_x21(x_15);
lean_dec_ref(x_15);
x_17 = l_Lean_Expr_appArg_x21(x_16);
lean_dec_ref(x_16);
x_18 = l_Lean_Expr_cleanupAnnotations(x_17);
x_19 = l_Lean_Expr_isApp(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec_ref(x_18);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_20 = lean_box(0);
lean_ctor_set(x_7, 0, x_20);
return x_7;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_free_object(x_7);
x_21 = l_Lean_Expr_getAppFn(x_18);
x_22 = l_Lean_Expr_getAppNumArgs(x_18);
lean_dec_ref(x_18);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_23 = l_Lean_Meta_mkHCongrWithArity(x_21, x_22, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
x_26 = l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f(x_1, x_24, x_2, x_3, x_4, x_5, x_25);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_26, 0);
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_26);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_26);
if (x_34 == 0)
{
return x_26;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_26, 0);
x_36 = lean_ctor_get(x_26, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_26);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_23);
if (x_38 == 0)
{
return x_23;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_23, 0);
x_40 = lean_ctor_get(x_23, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_23);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_42 = lean_ctor_get(x_7, 0);
x_43 = lean_ctor_get(x_7, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_7);
x_44 = l_Lean_MVarId_hcongr_x3f___lam__0___closed__1;
x_45 = lean_unsigned_to_nat(4u);
x_46 = l_Lean_Expr_isAppOfArity(x_42, x_44, x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_42);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_43);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_49 = l_Lean_Expr_appFn_x21(x_42);
lean_dec(x_42);
x_50 = l_Lean_Expr_appFn_x21(x_49);
lean_dec_ref(x_49);
x_51 = l_Lean_Expr_appArg_x21(x_50);
lean_dec_ref(x_50);
x_52 = l_Lean_Expr_cleanupAnnotations(x_51);
x_53 = l_Lean_Expr_isApp(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec_ref(x_52);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_43);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = l_Lean_Expr_getAppFn(x_52);
x_57 = l_Lean_Expr_getAppNumArgs(x_52);
lean_dec_ref(x_52);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_58 = l_Lean_Meta_mkHCongrWithArity(x_56, x_57, x_2, x_3, x_4, x_5, x_43);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec_ref(x_58);
x_61 = l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f(x_1, x_59, x_2, x_3, x_4, x_5, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_64 = x_61;
} else {
 lean_dec_ref(x_61);
 x_64 = lean_box(0);
}
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_62);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_61, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_61, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_69 = x_61;
} else {
 lean_dec_ref(x_61);
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
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_71 = lean_ctor_get(x_58, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_58, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_73 = x_58;
} else {
 lean_dec_ref(x_58);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_7);
if (x_75 == 0)
{
return x_7;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_7, 0);
x_77 = lean_ctor_get(x_7, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_7);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_hcongr_x3f___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec_ref(x_8);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_10 = l_Lean_MVarId_eqOfHEq(x_1, x_3, x_4, x_5, x_6, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
lean_inc(x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_MVarId_hcongr_x3f___lam__0), 6, 1);
lean_closure_set(x_13, 0, x_11);
x_14 = l_Lean_MVarId_withContext___at___Lean_MVarId_congr_x3f_spec__2___redArg(x_11, x_13, x_3, x_4, x_5, x_6, x_12);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
uint8_t x_19; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_8);
if (x_19 == 0)
{
return x_8;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_8, 0);
x_21 = lean_ctor_get(x_8, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_8);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_hcongr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_MVarId_congr_x3f___closed__1;
x_8 = lean_alloc_closure((void*)(l_Lean_MVarId_hcongr_x3f___lam__1), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
x_9 = l_Lean_commitWhenSomeNoEx_x3f___at___Lean_MVarId_congr_x3f_spec__0___redArg(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_MVarId_congrImplies_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_get(x_3, x_10);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_2, 2);
x_17 = lean_ctor_get(x_4, 2);
lean_inc(x_17);
lean_inc_ref(x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_16);
lean_ctor_set(x_18, 3, x_17);
lean_ctor_set_tag(x_7, 3);
lean_ctor_set(x_7, 1, x_1);
lean_ctor_set(x_7, 0, x_18);
lean_ctor_set(x_12, 0, x_7);
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
x_21 = lean_ctor_get(x_19, 0);
lean_inc_ref(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_2, 2);
x_23 = lean_ctor_get(x_4, 2);
lean_inc(x_23);
lean_inc_ref(x_22);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set_tag(x_7, 3);
lean_ctor_set(x_7, 1, x_1);
lean_ctor_set(x_7, 0, x_24);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_7);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_28 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_28);
lean_dec(x_26);
x_29 = lean_st_ref_get(x_3, x_27);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_32 = x_29;
} else {
 lean_dec_ref(x_29);
 x_32 = lean_box(0);
}
x_33 = lean_ctor_get(x_30, 0);
lean_inc_ref(x_33);
lean_dec(x_30);
x_34 = lean_ctor_get(x_2, 2);
x_35 = lean_ctor_get(x_4, 2);
lean_inc(x_35);
lean_inc_ref(x_34);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_33);
lean_ctor_set(x_36, 2, x_34);
lean_ctor_set(x_36, 3, x_35);
x_37 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_1);
if (lean_is_scalar(x_32)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_32;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_31);
return x_38;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_MVarId_congrImplies_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_4, 5);
x_8 = l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_MVarId_congrImplies_x3f_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_MVarId_congrImplies_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___Lean_MVarId_congrImplies_x3f_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___Lean_MVarId_congrImplies_x3f_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_saveState___redArg(x_3, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
lean_inc(x_5);
lean_inc(x_3);
x_10 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_35; 
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_20 = x_10;
} else {
 lean_dec_ref(x_10);
 x_20 = lean_box(0);
}
x_35 = l_Lean_Exception_isInterrupt(x_18);
if (x_35 == 0)
{
uint8_t x_36; 
x_36 = l_Lean_Exception_isRuntime(x_18);
x_21 = x_36;
goto block_34;
}
else
{
x_21 = x_35;
goto block_34;
}
block_34:
{
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_20);
lean_dec(x_18);
x_22 = l_Lean_Meta_SavedState_restore___redArg(x_8, x_3, x_5, x_19);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_8);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_22);
if (x_29 == 0)
{
return x_22;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_22, 0);
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_22);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
if (lean_is_scalar(x_20)) {
 x_33 = lean_alloc_ctor(1, 2, 0);
} else {
 x_33 = x_20;
}
lean_ctor_set(x_33, 0, x_18);
lean_ctor_set(x_33, 1, x_19);
return x_33;
}
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_37 = !lean_is_exclusive(x_7);
if (x_37 == 0)
{
return x_7;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_7, 0);
x_39 = lean_ctor_get(x_7, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_7);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___Lean_MVarId_congrImplies_x3f_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_observing_x3f___at___Lean_MVarId_congrImplies_x3f_spec__2___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_MVarId_congrImplies_x3f___lam__0___closed__0() {
_start:
{
uint8_t x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 1;
x_3 = 0;
x_4 = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(x_4, 0, x_3);
lean_ctor_set_uint8(x_4, 1, x_2);
lean_ctor_set_uint8(x_4, 2, x_1);
lean_ctor_set_uint8(x_4, 3, x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_MVarId_congrImplies_x3f___lam__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Internal error: Expected at least two goals after applying `", 60, 60);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_congrImplies_x3f___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_congrImplies_x3f___lam__0___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_congrImplies_x3f___lam__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("`, but unexpectedly found fewer", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_congrImplies_x3f___lam__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_congrImplies_x3f___lam__0___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_congrImplies_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc_ref(x_5);
lean_inc(x_1);
x_8 = l_Lean_Meta_mkConstWithFreshMVarLevels(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = 0;
x_12 = l_Lean_MVarId_congrImplies_x3f___lam__0___closed__0;
x_13 = lean_box(0);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_14 = l_Lean_MVarId_apply(x_2, x_9, x_12, x_13, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
if (lean_obj_tag(x_16) == 0)
{
lean_free_object(x_14);
x_18 = x_3;
x_19 = x_4;
x_20 = x_5;
x_21 = x_6;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_16, 1);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
lean_free_object(x_14);
lean_dec_ref(x_16);
x_18 = x_3;
x_19 = x_4;
x_20 = x_5;
x_21 = x_6;
goto block_28;
}
else
{
uint8_t x_30; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_16);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_16, 1);
lean_dec(x_31);
x_32 = !lean_is_exclusive(x_29);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_29, 1);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_29, 1, x_34);
return x_14;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 0);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_16, 1, x_37);
return x_14;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_16, 0);
lean_inc(x_38);
lean_dec(x_16);
x_39 = lean_ctor_get(x_29, 0);
lean_inc(x_39);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_40 = x_29;
} else {
 lean_dec_ref(x_29);
 x_40 = lean_box(0);
}
x_41 = lean_box(0);
if (lean_is_scalar(x_40)) {
 x_42 = lean_alloc_ctor(1, 2, 0);
} else {
 x_42 = x_40;
}
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_38);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_14, 0, x_43);
return x_14;
}
}
}
block_28:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = l_Lean_MVarId_congrImplies_x3f___lam__0___closed__2;
x_23 = l_Lean_MessageData_ofConstName(x_1, x_11);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_MVarId_congrImplies_x3f___lam__0___closed__4;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_throwError___at___Lean_MVarId_congrImplies_x3f_spec__0___redArg(x_26, x_18, x_19, x_20, x_21, x_17);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
return x_27;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_14, 0);
x_45 = lean_ctor_get(x_14, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_14);
if (lean_obj_tag(x_44) == 0)
{
x_46 = x_3;
x_47 = x_4;
x_48 = x_5;
x_49 = x_6;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_44, 1);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 0)
{
lean_dec_ref(x_44);
x_46 = x_3;
x_47 = x_4;
x_48 = x_5;
x_49 = x_6;
goto block_56;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_58 = lean_ctor_get(x_44, 0);
lean_inc(x_58);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_59 = x_44;
} else {
 lean_dec_ref(x_44);
 x_59 = lean_box(0);
}
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_61 = x_57;
} else {
 lean_dec_ref(x_57);
 x_61 = lean_box(0);
}
x_62 = lean_box(0);
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(1, 2, 0);
} else {
 x_63 = x_61;
}
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_62);
if (lean_is_scalar(x_59)) {
 x_64 = lean_alloc_ctor(1, 2, 0);
} else {
 x_64 = x_59;
}
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_45);
return x_65;
}
}
block_56:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = l_Lean_MVarId_congrImplies_x3f___lam__0___closed__2;
x_51 = l_Lean_MessageData_ofConstName(x_1, x_11);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_MVarId_congrImplies_x3f___lam__0___closed__4;
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_throwError___at___Lean_MVarId_congrImplies_x3f_spec__0___redArg(x_54, x_46, x_47, x_48, x_49, x_45);
lean_dec(x_49);
lean_dec_ref(x_48);
lean_dec(x_47);
lean_dec_ref(x_46);
return x_55;
}
}
}
else
{
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_14;
}
}
else
{
uint8_t x_66; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_8);
if (x_66 == 0)
{
return x_8;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_8, 0);
x_68 = lean_ctor_get(x_8, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_8);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
}
static lean_object* _init_l_Lean_MVarId_congrImplies_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("implies_congr", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_congrImplies_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_congrImplies_x3f___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_congrImplies_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_MVarId_congrImplies_x3f___closed__1;
x_8 = lean_alloc_closure((void*)(l_Lean_MVarId_congrImplies_x3f___lam__0), 7, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Lean_observing_x3f___at___Lean_MVarId_congrImplies_x3f_spec__2___redArg(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_MVarId_congrImplies_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___Lean_throwError___at___Lean_MVarId_congrImplies_x3f_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_MVarId_congrImplies_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___Lean_MVarId_congrImplies_x3f_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_MVarId_congrImplies_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwError___at___Lean_MVarId_congrImplies_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
static lean_object* _init_l_Lean_MVarId_congrCore___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Failed to apply congruence", 26, 26);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_congrCore___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_congrCore___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_congrCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_congrCore___closed__1;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_congrCore___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_congrCore___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_congrCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_7 = l_Lean_MVarId_congr_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_10 = l_Lean_MVarId_hcongr_x3f(x_1, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_13 = l_Lean_MVarId_congrImplies_x3f(x_1, x_2, x_3, x_4, x_5, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = l_Lean_MVarId_congr_x3f___closed__1;
x_17 = l_Lean_MVarId_congrCore___closed__3;
x_18 = l_Lean_Meta_throwTacticEx___redArg(x_16, x_1, x_17, x_2, x_3, x_4, x_5, x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_13, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec_ref(x_14);
lean_ctor_set(x_13, 0, x_21);
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec(x_13);
x_23 = lean_ctor_get(x_14, 0);
lean_inc(x_23);
lean_dec_ref(x_14);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_13);
if (x_25 == 0)
{
return x_13;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_13, 0);
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_13);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_10);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_10, 0);
lean_dec(x_30);
x_31 = lean_ctor_get(x_11, 0);
lean_inc(x_31);
lean_dec_ref(x_11);
lean_ctor_set(x_10, 0, x_31);
return x_10;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_10, 1);
lean_inc(x_32);
lean_dec(x_10);
x_33 = lean_ctor_get(x_11, 0);
lean_inc(x_33);
lean_dec_ref(x_11);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_10);
if (x_35 == 0)
{
return x_10;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_10, 0);
x_37 = lean_ctor_get(x_10, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_10);
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
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_7);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_7, 0);
lean_dec(x_40);
x_41 = lean_ctor_get(x_8, 0);
lean_inc(x_41);
lean_dec_ref(x_8);
lean_ctor_set(x_7, 0, x_41);
return x_7;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_7, 1);
lean_inc(x_42);
lean_dec(x_7);
x_43 = lean_ctor_get(x_8, 0);
lean_inc(x_43);
lean_dec_ref(x_8);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_7);
if (x_45 == 0)
{
return x_7;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_7, 0);
x_47 = lean_ctor_get(x_7, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_7);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_post(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_getTransparency___redArg(x_4, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
if (x_1 == 0)
{
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
goto block_23;
}
else
{
uint8_t x_24; uint8_t x_25; uint8_t x_26; 
x_24 = 2;
x_25 = lean_unbox(x_10);
lean_dec(x_10);
x_26 = l_Lean_Meta_beqTransparencyMode____x40_Init_MetaTypes_2581322616____hygCtx___hyg_9_(x_25, x_24);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = l_Lean_MVarId_congrPre(x_2, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 0);
lean_dec(x_30);
x_31 = lean_box(0);
lean_ctor_set(x_27, 0, x_31);
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_dec(x_27);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_35 = lean_ctor_get(x_27, 1);
lean_inc(x_35);
lean_dec_ref(x_27);
x_36 = lean_ctor_get(x_28, 0);
lean_inc(x_36);
lean_dec_ref(x_28);
x_37 = lean_st_ref_take(x_3, x_35);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec_ref(x_37);
x_40 = lean_array_push(x_38, x_36);
x_41 = lean_st_ref_set(x_3, x_40, x_39);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
x_44 = lean_box(0);
lean_ctor_set(x_41, 0, x_44);
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
lean_dec(x_41);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_27);
if (x_48 == 0)
{
return x_27;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_27, 0);
x_50 = lean_ctor_get(x_27, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_27);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
goto block_23;
}
}
block_23:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_st_ref_take(x_3, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_array_push(x_13, x_2);
x_16 = lean_st_ref_set(x_3, x_15, x_14);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_9);
if (x_52 == 0)
{
return x_9;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_9, 0);
x_54 = lean_ctor_get(x_9, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_9);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_post___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_post(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_____private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go_spec__0(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_4, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_dec_ref(x_4);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_15 = l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go(x_1, x_2, x_3, x_13, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec_ref(x_15);
x_4 = x_14;
x_10 = x_16;
goto _start;
}
else
{
lean_dec(x_14);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_15;
}
}
}
}
static uint64_t _init_l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go___closed__0() {
_start:
{
uint8_t x_1; uint64_t x_2; 
x_1 = 2;
x_2 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_31; lean_object* x_32; 
if (x_1 == 0)
{
x_11 = x_4;
x_12 = x_10;
goto block_30;
}
else
{
lean_object* x_37; uint8_t x_38; 
x_37 = l_Lean_Meta_Context_config(x_6);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; uint64_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_39 = lean_ctor_get_uint8(x_6, sizeof(void*)*7);
x_40 = lean_ctor_get(x_6, 1);
x_41 = lean_ctor_get(x_6, 2);
x_42 = lean_ctor_get(x_6, 3);
x_43 = lean_ctor_get(x_6, 4);
x_44 = lean_ctor_get(x_6, 5);
x_45 = lean_ctor_get(x_6, 6);
x_46 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 1);
x_47 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 2);
x_48 = 2;
lean_ctor_set_uint8(x_37, 9, x_48);
x_49 = l_Lean_Meta_Context_configKey(x_6);
x_50 = 2;
x_51 = lean_uint64_shift_right(x_49, x_50);
x_52 = lean_uint64_shift_left(x_51, x_50);
x_53 = l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go___closed__0;
x_54 = lean_uint64_lor(x_52, x_53);
x_55 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_55, 0, x_37);
lean_ctor_set_uint64(x_55, sizeof(void*)*1, x_54);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc_ref(x_42);
lean_inc_ref(x_41);
lean_inc(x_40);
x_56 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_40);
lean_ctor_set(x_56, 2, x_41);
lean_ctor_set(x_56, 3, x_42);
lean_ctor_set(x_56, 4, x_43);
lean_ctor_set(x_56, 5, x_44);
lean_ctor_set(x_56, 6, x_45);
lean_ctor_set_uint8(x_56, sizeof(void*)*7, x_39);
lean_ctor_set_uint8(x_56, sizeof(void*)*7 + 1, x_46);
lean_ctor_set_uint8(x_56, sizeof(void*)*7 + 2, x_47);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
x_57 = l_Lean_MVarId_congrPre(x_4, x_56, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec_ref(x_57);
x_31 = x_58;
x_32 = x_59;
goto block_36;
}
else
{
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
lean_dec_ref(x_57);
x_31 = x_60;
x_32 = x_61;
goto block_36;
}
else
{
uint8_t x_62; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_62 = !lean_is_exclusive(x_57);
if (x_62 == 0)
{
return x_57;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_57, 0);
x_64 = lean_ctor_get(x_57, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_57);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
else
{
uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; uint8_t x_92; uint8_t x_93; lean_object* x_94; uint64_t x_95; uint64_t x_96; uint64_t x_97; uint64_t x_98; uint64_t x_99; uint64_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_66 = lean_ctor_get_uint8(x_37, 0);
x_67 = lean_ctor_get_uint8(x_37, 1);
x_68 = lean_ctor_get_uint8(x_37, 2);
x_69 = lean_ctor_get_uint8(x_37, 3);
x_70 = lean_ctor_get_uint8(x_37, 4);
x_71 = lean_ctor_get_uint8(x_37, 5);
x_72 = lean_ctor_get_uint8(x_37, 6);
x_73 = lean_ctor_get_uint8(x_37, 7);
x_74 = lean_ctor_get_uint8(x_37, 8);
x_75 = lean_ctor_get_uint8(x_37, 10);
x_76 = lean_ctor_get_uint8(x_37, 11);
x_77 = lean_ctor_get_uint8(x_37, 12);
x_78 = lean_ctor_get_uint8(x_37, 13);
x_79 = lean_ctor_get_uint8(x_37, 14);
x_80 = lean_ctor_get_uint8(x_37, 15);
x_81 = lean_ctor_get_uint8(x_37, 16);
x_82 = lean_ctor_get_uint8(x_37, 17);
x_83 = lean_ctor_get_uint8(x_37, 18);
lean_dec(x_37);
x_84 = lean_ctor_get_uint8(x_6, sizeof(void*)*7);
x_85 = lean_ctor_get(x_6, 1);
x_86 = lean_ctor_get(x_6, 2);
x_87 = lean_ctor_get(x_6, 3);
x_88 = lean_ctor_get(x_6, 4);
x_89 = lean_ctor_get(x_6, 5);
x_90 = lean_ctor_get(x_6, 6);
x_91 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 1);
x_92 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 2);
x_93 = 2;
x_94 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_94, 0, x_66);
lean_ctor_set_uint8(x_94, 1, x_67);
lean_ctor_set_uint8(x_94, 2, x_68);
lean_ctor_set_uint8(x_94, 3, x_69);
lean_ctor_set_uint8(x_94, 4, x_70);
lean_ctor_set_uint8(x_94, 5, x_71);
lean_ctor_set_uint8(x_94, 6, x_72);
lean_ctor_set_uint8(x_94, 7, x_73);
lean_ctor_set_uint8(x_94, 8, x_74);
lean_ctor_set_uint8(x_94, 9, x_93);
lean_ctor_set_uint8(x_94, 10, x_75);
lean_ctor_set_uint8(x_94, 11, x_76);
lean_ctor_set_uint8(x_94, 12, x_77);
lean_ctor_set_uint8(x_94, 13, x_78);
lean_ctor_set_uint8(x_94, 14, x_79);
lean_ctor_set_uint8(x_94, 15, x_80);
lean_ctor_set_uint8(x_94, 16, x_81);
lean_ctor_set_uint8(x_94, 17, x_82);
lean_ctor_set_uint8(x_94, 18, x_83);
x_95 = l_Lean_Meta_Context_configKey(x_6);
x_96 = 2;
x_97 = lean_uint64_shift_right(x_95, x_96);
x_98 = lean_uint64_shift_left(x_97, x_96);
x_99 = l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go___closed__0;
x_100 = lean_uint64_lor(x_98, x_99);
x_101 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_101, 0, x_94);
lean_ctor_set_uint64(x_101, sizeof(void*)*1, x_100);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc_ref(x_87);
lean_inc_ref(x_86);
lean_inc(x_85);
x_102 = lean_alloc_ctor(0, 7, 3);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_85);
lean_ctor_set(x_102, 2, x_86);
lean_ctor_set(x_102, 3, x_87);
lean_ctor_set(x_102, 4, x_88);
lean_ctor_set(x_102, 5, x_89);
lean_ctor_set(x_102, 6, x_90);
lean_ctor_set_uint8(x_102, sizeof(void*)*7, x_84);
lean_ctor_set_uint8(x_102, sizeof(void*)*7 + 1, x_91);
lean_ctor_set_uint8(x_102, sizeof(void*)*7 + 2, x_92);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
x_103 = l_Lean_MVarId_congrPre(x_4, x_102, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec_ref(x_103);
x_31 = x_104;
x_32 = x_105;
goto block_36;
}
else
{
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_103, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_103, 1);
lean_inc(x_107);
lean_dec_ref(x_103);
x_31 = x_106;
x_32 = x_107;
goto block_36;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_108 = lean_ctor_get(x_103, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_103, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_110 = x_103;
} else {
 lean_dec_ref(x_103);
 x_110 = lean_box(0);
}
if (lean_is_scalar(x_110)) {
 x_111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_111 = x_110;
}
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
return x_111;
}
}
}
}
block_30:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_3, x_13);
if (x_14 == 1)
{
lean_object* x_15; 
x_15 = l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_post(x_2, x_11, x_5, x_6, x_7, x_8, x_9, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_inc(x_11);
x_16 = lean_alloc_closure((void*)(l_Lean_MVarId_congrCore), 6, 1);
lean_closure_set(x_16, 0, x_11);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_17 = l_Lean_observing_x3f___at___Lean_MVarId_congrImplies_x3f_spec__2___redArg(x_16, x_6, x_7, x_8, x_9, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec_ref(x_17);
x_20 = l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_post(x_2, x_11, x_5, x_6, x_7, x_8, x_9, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_11);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec_ref(x_17);
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec_ref(x_18);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_sub(x_3, x_23);
x_25 = l_List_forM___at_____private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go_spec__0(x_1, x_2, x_24, x_22, x_5, x_6, x_7, x_8, x_9, x_21);
lean_dec(x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_17);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
block_36:
{
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
else
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_31, 0);
lean_inc(x_35);
lean_dec_ref(x_31);
x_11 = x_35;
x_12 = x_32;
goto block_30;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at_____private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_1);
x_12 = lean_unbox(x_2);
x_13 = l_List_forM___at_____private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go_spec__0(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_1);
x_12 = lean_unbox(x_2);
x_13 = l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_3);
return x_13;
}
}
static lean_object* _init_l_Lean_MVarId_congrN___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_congrN(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = l_Lean_MVarId_congrN___closed__0;
x_11 = lean_st_mk_ref(x_10, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go(x_3, x_4, x_2, x_1, x_12, x_5, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_st_ref_get(x_12, x_15);
lean_dec(x_12);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_array_to_list(x_18);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = lean_array_to_list(x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_12);
x_24 = !lean_is_exclusive(x_14);
if (x_24 == 0)
{
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_congrN___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_3);
x_11 = lean_unbox(x_4);
x_12 = l_Lean_MVarId_congrN(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_12;
}
}
lean_object* initialize_Lean_Meta_CongrTheorems(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Assert(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Clear(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Refl(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Congr(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_CongrTheorems(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assert(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Apply(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Clear(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Refl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assumption(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__0 = _init_l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__0);
l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__1 = _init_l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__1);
l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__2 = _init_l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Congr_0__Lean_applyCongrThm_x3f___closed__2);
l_Lean_MVarId_congr_x3f___lam__0___closed__0 = _init_l_Lean_MVarId_congr_x3f___lam__0___closed__0();
lean_mark_persistent(l_Lean_MVarId_congr_x3f___lam__0___closed__0);
l_Lean_MVarId_congr_x3f___lam__0___closed__1 = _init_l_Lean_MVarId_congr_x3f___lam__0___closed__1();
lean_mark_persistent(l_Lean_MVarId_congr_x3f___lam__0___closed__1);
l_Lean_MVarId_congr_x3f___closed__0 = _init_l_Lean_MVarId_congr_x3f___closed__0();
lean_mark_persistent(l_Lean_MVarId_congr_x3f___closed__0);
l_Lean_MVarId_congr_x3f___closed__1 = _init_l_Lean_MVarId_congr_x3f___closed__1();
lean_mark_persistent(l_Lean_MVarId_congr_x3f___closed__1);
l_Lean_MVarId_hcongr_x3f___lam__0___closed__0 = _init_l_Lean_MVarId_hcongr_x3f___lam__0___closed__0();
lean_mark_persistent(l_Lean_MVarId_hcongr_x3f___lam__0___closed__0);
l_Lean_MVarId_hcongr_x3f___lam__0___closed__1 = _init_l_Lean_MVarId_hcongr_x3f___lam__0___closed__1();
lean_mark_persistent(l_Lean_MVarId_hcongr_x3f___lam__0___closed__1);
l_Lean_MVarId_congrImplies_x3f___lam__0___closed__0 = _init_l_Lean_MVarId_congrImplies_x3f___lam__0___closed__0();
lean_mark_persistent(l_Lean_MVarId_congrImplies_x3f___lam__0___closed__0);
l_Lean_MVarId_congrImplies_x3f___lam__0___closed__1 = _init_l_Lean_MVarId_congrImplies_x3f___lam__0___closed__1();
lean_mark_persistent(l_Lean_MVarId_congrImplies_x3f___lam__0___closed__1);
l_Lean_MVarId_congrImplies_x3f___lam__0___closed__2 = _init_l_Lean_MVarId_congrImplies_x3f___lam__0___closed__2();
lean_mark_persistent(l_Lean_MVarId_congrImplies_x3f___lam__0___closed__2);
l_Lean_MVarId_congrImplies_x3f___lam__0___closed__3 = _init_l_Lean_MVarId_congrImplies_x3f___lam__0___closed__3();
lean_mark_persistent(l_Lean_MVarId_congrImplies_x3f___lam__0___closed__3);
l_Lean_MVarId_congrImplies_x3f___lam__0___closed__4 = _init_l_Lean_MVarId_congrImplies_x3f___lam__0___closed__4();
lean_mark_persistent(l_Lean_MVarId_congrImplies_x3f___lam__0___closed__4);
l_Lean_MVarId_congrImplies_x3f___closed__0 = _init_l_Lean_MVarId_congrImplies_x3f___closed__0();
lean_mark_persistent(l_Lean_MVarId_congrImplies_x3f___closed__0);
l_Lean_MVarId_congrImplies_x3f___closed__1 = _init_l_Lean_MVarId_congrImplies_x3f___closed__1();
lean_mark_persistent(l_Lean_MVarId_congrImplies_x3f___closed__1);
l_Lean_MVarId_congrCore___closed__0 = _init_l_Lean_MVarId_congrCore___closed__0();
lean_mark_persistent(l_Lean_MVarId_congrCore___closed__0);
l_Lean_MVarId_congrCore___closed__1 = _init_l_Lean_MVarId_congrCore___closed__1();
lean_mark_persistent(l_Lean_MVarId_congrCore___closed__1);
l_Lean_MVarId_congrCore___closed__2 = _init_l_Lean_MVarId_congrCore___closed__2();
lean_mark_persistent(l_Lean_MVarId_congrCore___closed__2);
l_Lean_MVarId_congrCore___closed__3 = _init_l_Lean_MVarId_congrCore___closed__3();
lean_mark_persistent(l_Lean_MVarId_congrCore___closed__3);
l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go___closed__0 = _init_l___private_Lean_Meta_Tactic_Congr_0__Lean_MVarId_congrN_go___closed__0();
l_Lean_MVarId_congrN___closed__0 = _init_l_Lean_MVarId_congrN___closed__0();
lean_mark_persistent(l_Lean_MVarId_congrN___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
