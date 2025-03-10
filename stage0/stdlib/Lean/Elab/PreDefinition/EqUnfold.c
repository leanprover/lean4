// Lean compiler output
// Module: Lean.Elab.PreDefinition.EqUnfold
// Imports: Lean.Meta.Eqns Lean.Meta.Tactic.Util Lean.Meta.Tactic.Rfl Lean.Meta.Tactic.Intro Lean.Meta.Tactic.Apply
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
lean_object* l_Lean_registerReservedNameAction(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_tryURefl___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__6___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__8;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__9;
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_tryURefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_tryURefl___closed__3;
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__4;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__2;
lean_object* l_Lean_Meta_forallTelescope___at_Lean_Meta_mapForallTelescope_x27___spec__1___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__2___closed__4;
lean_object* l_Lean_mkConstWithLevelParams___at_Lean_Meta_registerCoercion___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_refl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__3___closed__1;
static lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__3___closed__2;
static lean_object* l_Lean_Meta_tryURefl___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
extern lean_object* l_Lean_maxRecDepth;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
extern lean_object* l_Lean_Meta_smartUnfolding;
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_getConstUnfoldEqnFor_x3f___spec__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__1;
lean_object* l_Array_reverse___rarg(lean_object*);
lean_object* l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__2___closed__2;
lean_object* l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__5;
static lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__6___closed__3;
lean_object* l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_matchesInstance___spec__1___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__2___closed__3;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__10;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_tryURefl___lambda__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lean_Meta_getConstUnfoldEqnFor_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_levelZero;
static lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__2___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lean_Meta_getConstUnfoldEqnFor_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_getConstUnfoldEqnFor_x3f___spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_tryURefl___closed__2;
uint8_t l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_diagnostics;
static lean_object* l_Lean_Meta_tryURefl___closed__1;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
static lean_object* l_Lean_Meta_tryURefl___closed__4;
lean_object* l_Lean_Meta_instInhabitedMetaM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__7;
lean_object* l_Lean_Meta_realizeConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_getConstUnfoldEqnFor_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__6;
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__6___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_getConstUnfoldEqnFor_x3f___spec__3___closed__2;
extern lean_object* l_Lean_Meta_eqUnfoldThmSuffix;
static lean_object* l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__11;
static uint64_t l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__3;
uint8_t l_Lean_Environment_isSafeDefinition(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742_(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____closed__1;
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
static lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__2___closed__1;
static lean_object* l_panic___at_Lean_Meta_getConstUnfoldEqnFor_x3f___spec__1___closed__1;
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
static lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__6___closed__4;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_getConstUnfoldEqnFor_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__12;
lean_object* l_Lean_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_tryURefl___lambda__1___closed__1;
lean_object* l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_set___at_Lean_Environment_realizeConst___spec__2(lean_object*, lean_object*, uint8_t);
static lean_object* _init_l_Lean_Meta_tryURefl___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxRecDepth;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_tryURefl___lambda__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_7, 4);
lean_dec(x_11);
x_12 = lean_ctor_get(x_7, 2);
lean_dec(x_12);
x_13 = l_Lean_Meta_tryURefl___lambda__1___closed__1;
x_14 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_13);
lean_ctor_set(x_7, 4, x_14);
lean_ctor_set(x_7, 2, x_1);
lean_ctor_set_uint8(x_7, sizeof(void*)*12, x_2);
x_15 = l_Lean_MVarId_refl(x_3, x_4, x_5, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
x_18 = 1;
x_19 = lean_box(x_18);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
else
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = 1;
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_15, 0);
x_26 = l_Lean_Exception_isInterrupt(x_25);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = l_Lean_Exception_isRuntime(x_25);
if (x_27 == 0)
{
uint8_t x_28; lean_object* x_29; 
lean_dec(x_25);
x_28 = 0;
x_29 = lean_box(x_28);
lean_ctor_set_tag(x_15, 0);
lean_ctor_set(x_15, 0, x_29);
return x_15;
}
else
{
return x_15;
}
}
else
{
return x_15;
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_15, 0);
x_31 = lean_ctor_get(x_15, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_15);
x_32 = l_Lean_Exception_isInterrupt(x_30);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = l_Lean_Exception_isRuntime(x_30);
if (x_33 == 0)
{
uint8_t x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_30);
x_34 = 0;
x_35 = lean_box(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_31);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_30);
lean_ctor_set(x_37, 1, x_31);
return x_37;
}
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_30);
lean_ctor_set(x_38, 1, x_31);
return x_38;
}
}
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_39 = lean_ctor_get(x_7, 0);
x_40 = lean_ctor_get(x_7, 1);
x_41 = lean_ctor_get(x_7, 3);
x_42 = lean_ctor_get(x_7, 5);
x_43 = lean_ctor_get(x_7, 6);
x_44 = lean_ctor_get(x_7, 7);
x_45 = lean_ctor_get(x_7, 8);
x_46 = lean_ctor_get(x_7, 9);
x_47 = lean_ctor_get(x_7, 10);
x_48 = lean_ctor_get(x_7, 11);
x_49 = lean_ctor_get_uint8(x_7, sizeof(void*)*12 + 1);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_7);
x_50 = l_Lean_Meta_tryURefl___lambda__1___closed__1;
x_51 = l_Lean_Option_get___at_Lean_profiler_threshold_getSecs___spec__1(x_1, x_50);
x_52 = lean_alloc_ctor(0, 12, 2);
lean_ctor_set(x_52, 0, x_39);
lean_ctor_set(x_52, 1, x_40);
lean_ctor_set(x_52, 2, x_1);
lean_ctor_set(x_52, 3, x_41);
lean_ctor_set(x_52, 4, x_51);
lean_ctor_set(x_52, 5, x_42);
lean_ctor_set(x_52, 6, x_43);
lean_ctor_set(x_52, 7, x_44);
lean_ctor_set(x_52, 8, x_45);
lean_ctor_set(x_52, 9, x_46);
lean_ctor_set(x_52, 10, x_47);
lean_ctor_set(x_52, 11, x_48);
lean_ctor_set_uint8(x_52, sizeof(void*)*12, x_2);
lean_ctor_set_uint8(x_52, sizeof(void*)*12 + 1, x_49);
x_53 = l_Lean_MVarId_refl(x_3, x_4, x_5, x_52, x_8, x_9);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_55 = x_53;
} else {
 lean_dec_ref(x_53);
 x_55 = lean_box(0);
}
x_56 = 1;
x_57 = lean_box(x_56);
if (lean_is_scalar(x_55)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_55;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_54);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_59 = lean_ctor_get(x_53, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_53, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_61 = x_53;
} else {
 lean_dec_ref(x_53);
 x_61 = lean_box(0);
}
x_62 = l_Lean_Exception_isInterrupt(x_59);
if (x_62 == 0)
{
uint8_t x_63; 
x_63 = l_Lean_Exception_isRuntime(x_59);
if (x_63 == 0)
{
uint8_t x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_59);
x_64 = 0;
x_65 = lean_box(x_64);
if (lean_is_scalar(x_61)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_61;
 lean_ctor_set_tag(x_66, 0);
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_60);
return x_66;
}
else
{
lean_object* x_67; 
if (lean_is_scalar(x_61)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_61;
}
lean_ctor_set(x_67, 0, x_59);
lean_ctor_set(x_67, 1, x_60);
return x_67;
}
}
else
{
lean_object* x_68; 
if (lean_is_scalar(x_61)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_61;
}
lean_ctor_set(x_68, 0, x_59);
lean_ctor_set(x_68, 1, x_60);
return x_68;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_tryURefl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_smartUnfolding;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_tryURefl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_diagnostics;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_tryURefl___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_tryURefl___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_tryURefl___closed__3;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_tryURefl___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_tryURefl___closed__4;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_tryURefl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; 
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = l_Lean_Meta_tryURefl___closed__1;
x_9 = 0;
x_10 = l_Lean_Option_set___at_Lean_Environment_realizeConst___spec__2(x_7, x_8, x_9);
x_11 = l_Lean_Meta_tryURefl___closed__2;
x_12 = l_Lean_Option_get___at___private_Lean_Util_Profile_0__Lean_get__profiler___spec__1(x_10, x_11);
x_13 = lean_st_ref_get(x_5, x_6);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Kernel_isDiagnosticsEnabled(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
if (x_12 == 0)
{
uint8_t x_48; 
x_48 = 1;
x_18 = x_48;
goto block_47;
}
else
{
x_18 = x_9;
goto block_47;
}
}
else
{
if (x_12 == 0)
{
x_18 = x_9;
goto block_47;
}
else
{
uint8_t x_49; 
x_49 = 1;
x_18 = x_49;
goto block_47;
}
}
block_47:
{
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_st_ref_take(x_5, x_15);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_ctor_get(x_20, 4);
lean_dec(x_24);
x_25 = l_Lean_Kernel_enableDiag(x_23, x_12);
x_26 = l_Lean_Meta_tryURefl___closed__5;
lean_ctor_set(x_20, 4, x_26);
lean_ctor_set(x_20, 0, x_25);
x_27 = lean_st_ref_set(x_5, x_20, x_21);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_box(0);
x_30 = l_Lean_Meta_tryURefl___lambda__1(x_10, x_12, x_1, x_2, x_3, x_29, x_4, x_5, x_28);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_31 = lean_ctor_get(x_20, 0);
x_32 = lean_ctor_get(x_20, 1);
x_33 = lean_ctor_get(x_20, 2);
x_34 = lean_ctor_get(x_20, 3);
x_35 = lean_ctor_get(x_20, 5);
x_36 = lean_ctor_get(x_20, 6);
x_37 = lean_ctor_get(x_20, 7);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_20);
x_38 = l_Lean_Kernel_enableDiag(x_31, x_12);
x_39 = l_Lean_Meta_tryURefl___closed__5;
x_40 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_32);
lean_ctor_set(x_40, 2, x_33);
lean_ctor_set(x_40, 3, x_34);
lean_ctor_set(x_40, 4, x_39);
lean_ctor_set(x_40, 5, x_35);
lean_ctor_set(x_40, 6, x_36);
lean_ctor_set(x_40, 7, x_37);
x_41 = lean_st_ref_set(x_5, x_40, x_21);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_box(0);
x_44 = l_Lean_Meta_tryURefl___lambda__1(x_10, x_12, x_1, x_2, x_3, x_43, x_4, x_5, x_42);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_box(0);
x_46 = l_Lean_Meta_tryURefl___lambda__1(x_10, x_12, x_1, x_2, x_3, x_45, x_4, x_5, x_15);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_tryURefl___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_Meta_tryURefl___lambda__1(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
return x_11;
}
}
static lean_object* _init_l_panic___at_Lean_Meta_getConstUnfoldEqnFor_x3f___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instInhabitedMetaM___boxed), 5, 1);
lean_closure_set(x_1, 0, lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at_Lean_Meta_getConstUnfoldEqnFor_x3f___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_panic___at_Lean_Meta_getConstUnfoldEqnFor_x3f___spec__1___closed__1;
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_Lean_Meta_getConstUnfoldEqnFor_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_6, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_6, x_10);
lean_dec(x_6);
x_12 = lean_array_fget(x_4, x_11);
x_13 = lean_array_fget(x_5, x_11);
x_14 = lean_expr_eqv(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_11);
x_15 = 0;
return x_15;
}
else
{
x_3 = lean_box(0);
x_6 = x_11;
x_7 = lean_box(0);
goto _start;
}
}
else
{
uint8_t x_17; 
lean_dec(x_6);
x_17 = 1;
return x_17;
}
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_getConstUnfoldEqnFor_x3f___spec__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("funext", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_getConstUnfoldEqnFor_x3f___spec__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_getConstUnfoldEqnFor_x3f___spec__3___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_getConstUnfoldEqnFor_x3f___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_14 = lean_array_uget(x_3, x_5);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_array_mk(x_16);
x_18 = 0;
x_19 = 1;
x_20 = 1;
x_21 = l_Lean_Meta_mkLambdaFVars(x_17, x_6, x_18, x_19, x_18, x_20, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_15);
x_25 = lean_array_mk(x_24);
x_26 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_getConstUnfoldEqnFor_x3f___spec__3___closed__2;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_27 = l_Lean_Meta_mkAppM(x_26, x_25, x_7, x_8, x_9, x_10, x_23);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = 1;
x_31 = lean_usize_add(x_5, x_30);
x_5 = x_31;
x_6 = x_28;
x_11 = x_29;
goto _start;
}
else
{
uint8_t x_33; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_33 = !lean_is_exclusive(x_27);
if (x_33 == 0)
{
return x_27;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_27, 0);
x_35 = lean_ctor_get(x_27, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_27);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_37 = !lean_is_exclusive(x_21);
if (x_37 == 0)
{
return x_21;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_21, 0);
x_39 = lean_ctor_get(x_21, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_21);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_10 = 0;
x_11 = 1;
x_12 = 1;
x_13 = l_Lean_Meta_mkLambdaFVars(x_1, x_2, x_10, x_11, x_10, x_12, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Expr_getAppFn(x_3);
x_17 = l_Lean_Meta_mkEq(x_16, x_14, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_17);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_26 = !lean_is_exclusive(x_13);
if (x_26 == 0)
{
return x_13;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_13, 0);
x_28 = lean_ctor_get(x_13, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_13);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
static lean_object* _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__2___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Unexpected unfold theorem type ", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__2___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__2___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__2___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l___private_Lean_Expr_0__Lean_Expr_getAppNumArgsAux(x_3, x_12);
x_14 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__2___closed__1;
lean_inc(x_13);
x_15 = lean_mk_array(x_13, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_13, x_16);
lean_dec(x_13);
lean_inc(x_3);
x_18 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_3, x_15, x_17);
x_19 = lean_array_get_size(x_18);
x_20 = lean_array_get_size(x_1);
x_21 = lean_nat_dec_eq(x_19, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_3);
lean_dec(x_2);
x_22 = l_Lean_MessageData_ofExpr(x_4);
x_23 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__2___closed__3;
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__2___closed__5;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_26, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_27);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
uint8_t x_32; 
x_32 = l_Array_isEqvAux___at_Lean_Meta_getConstUnfoldEqnFor_x3f___spec__2(x_1, x_5, lean_box(0), x_18, x_1, x_19, lean_box(0));
lean_dec(x_18);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_dec(x_3);
lean_dec(x_2);
x_33 = l_Lean_MessageData_ofExpr(x_4);
x_34 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__2___closed__3;
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
x_36 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__2___closed__5;
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_37, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
return x_38;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_38);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_4);
x_43 = lean_box(0);
x_44 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__1(x_1, x_2, x_3, x_43, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_44;
}
}
}
}
static lean_object* _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__3___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__3___closed__2;
x_11 = lean_unsigned_to_nat(3u);
x_12 = l_Lean_Expr_isAppOfArity(x_4, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = l_Lean_MessageData_ofExpr(x_1);
x_14 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__2___closed__3;
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
x_16 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__2___closed__5;
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___at_Lean_Expr_abstractRangeM___spec__1(x_17, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = l_Lean_Expr_appFn_x21(x_4);
x_20 = l_Lean_Expr_appArg_x21(x_19);
lean_dec(x_19);
x_21 = l_Lean_Expr_appArg_x21(x_4);
x_22 = l_Lean_Expr_getAppFn(x_20);
x_23 = l_Lean_Expr_isConstOf(x_22, x_2);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_21);
lean_dec(x_20);
x_24 = l_Lean_MessageData_ofExpr(x_1);
x_25 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__2___closed__3;
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
x_27 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__2___closed__5;
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_throwError___at___private_Lean_Meta_InferType_0__Lean_Meta_inferProjType___spec__1(x_28, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
return x_29;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_29);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_box(0);
x_35 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__2(x_3, x_21, x_20, x_1, x_4, x_34, x_5, x_6, x_7, x_8, x_9);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_mkConstWithLevelParams___at_Lean_Meta_registerCoercion___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_mkAppN(x_10, x_2);
x_13 = lean_box(0);
x_14 = l_Array_reverse___rarg(x_2);
x_15 = lean_array_size(x_14);
x_16 = 0;
x_17 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_getConstUnfoldEqnFor_x3f___spec__3(x_13, x_14, x_14, x_15, x_16, x_12, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_14);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_17);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_9);
if (x_26 == 0)
{
return x_9;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_9, 0);
x_28 = lean_ctor_get(x_9, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_9);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_box(0);
lean_inc(x_4);
x_10 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_1, x_9, x_4, x_5, x_6, x_7, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Expr_mvarId_x21(x_11);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_14 = l_Lean_Meta_tryURefl(x_13, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
lean_dec(x_11);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__4___boxed), 8, 1);
lean_closure_set(x_18, 0, x_2);
x_19 = 0;
x_20 = l_Lean_Meta_forallTelescope___at_Lean_Meta_mapForallTelescope_x27___spec__1___rarg(x_3, x_18, x_19, x_4, x_5, x_6, x_7, x_17);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_dec(x_14);
x_22 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_11, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_14);
if (x_23 == 0)
{
return x_14;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_14, 0);
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_14);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
static lean_object* _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__6___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.PreDefinition.EqUnfold", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__6___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.getConstUnfoldEqnFor\?", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__6___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__6___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__6___closed__1;
x_2 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__6___closed__2;
x_3 = lean_unsigned_to_nat(30u);
x_4 = lean_unsigned_to_nat(74u);
x_5 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__6___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = 1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_9 = l_Lean_Meta_getUnfoldEqnFor_x3f(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__6___closed__4;
x_13 = l_panic___at_Lean_Meta_getConstUnfoldEqnFor_x3f___spec__1(x_12, x_3, x_4, x_5, x_6, x_11);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
x_17 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_16, x_3, x_4, x_5, x_6, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_ConstantInfo_type(x_18);
lean_inc(x_20);
x_21 = lean_alloc_closure((void*)(l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__3___boxed), 9, 2);
lean_closure_set(x_21, 0, x_20);
lean_closure_set(x_21, 1, x_1);
x_22 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_20);
x_23 = l_Lean_Meta_forallTelescope___at_Lean_Meta_mapForallTelescope_x27___spec__1___rarg(x_20, x_21, x_22, x_3, x_4, x_5, x_6, x_19);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__5), 8, 3);
lean_closure_set(x_26, 0, x_24);
lean_closure_set(x_26, 1, x_16);
lean_closure_set(x_26, 2, x_20);
lean_inc(x_6);
lean_inc(x_5);
x_27 = l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_matchesInstance___spec__1___rarg(x_26, x_22, x_3, x_4, x_5, x_6, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_ConstantInfo_levelParams(x_18);
lean_dec(x_18);
lean_inc(x_2);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_2);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_24);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_28);
lean_ctor_set(x_34, 2, x_33);
lean_ctor_set_tag(x_10, 2);
lean_ctor_set(x_10, 0, x_34);
x_35 = l_Lean_addDecl(x_10, x_5, x_6, x_29);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_24);
lean_dec(x_18);
lean_free_object(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_27);
if (x_36 == 0)
{
return x_27;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_27, 0);
x_38 = lean_ctor_get(x_27, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_27);
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
lean_dec(x_20);
lean_dec(x_18);
lean_free_object(x_10);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_23);
if (x_40 == 0)
{
return x_23;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_23, 0);
x_42 = lean_ctor_get(x_23, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_23);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_free_object(x_10);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_17);
if (x_44 == 0)
{
return x_17;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_17, 0);
x_46 = lean_ctor_get(x_17, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_17);
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
x_48 = lean_ctor_get(x_10, 0);
lean_inc(x_48);
lean_dec(x_10);
lean_inc(x_48);
x_49 = l_Lean_getConstInfo___at_Lean_Meta_mkConstWithFreshMVarLevels___spec__1(x_48, x_3, x_4, x_5, x_6, x_14);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Lean_ConstantInfo_type(x_50);
lean_inc(x_52);
x_53 = lean_alloc_closure((void*)(l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__3___boxed), 9, 2);
lean_closure_set(x_53, 0, x_52);
lean_closure_set(x_53, 1, x_1);
x_54 = 0;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_52);
x_55 = l_Lean_Meta_forallTelescope___at_Lean_Meta_mapForallTelescope_x27___spec__1___rarg(x_52, x_53, x_54, x_3, x_4, x_5, x_6, x_51);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
lean_inc(x_56);
x_58 = lean_alloc_closure((void*)(l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__5), 8, 3);
lean_closure_set(x_58, 0, x_56);
lean_closure_set(x_58, 1, x_48);
lean_closure_set(x_58, 2, x_52);
lean_inc(x_6);
lean_inc(x_5);
x_59 = l_Lean_Meta_withNewMCtxDepth___at_Lean_Meta_matchesInstance___spec__1___rarg(x_58, x_54, x_3, x_4, x_5, x_6, x_57);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Lean_ConstantInfo_levelParams(x_50);
lean_dec(x_50);
lean_inc(x_2);
x_63 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_63, 0, x_2);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_63, 2, x_56);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_2);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_60);
lean_ctor_set(x_66, 2, x_65);
x_67 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_68 = l_Lean_addDecl(x_67, x_5, x_6, x_61);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_56);
lean_dec(x_50);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_69 = lean_ctor_get(x_59, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_59, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_71 = x_59;
} else {
 lean_dec_ref(x_59);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_52);
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_73 = lean_ctor_get(x_55, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_55, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_75 = x_55;
} else {
 lean_dec_ref(x_55);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_48);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_77 = lean_ctor_get(x_49, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_49, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_79 = x_49;
} else {
 lean_dec_ref(x_49);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_9);
if (x_81 == 0)
{
return x_9;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_9, 0);
x_83 = lean_ctor_get(x_9, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_9);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lean_Meta_eqUnfoldThmSuffix;
lean_inc(x_1);
x_9 = l_Lean_Name_str___override(x_1, x_8);
lean_inc(x_9);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__6), 7, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_9);
lean_inc(x_9);
x_11 = l_Lean_Meta_realizeConst(x_1, x_9, x_10, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_9);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_9);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 1;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l_Lean_Meta_getUnfoldEqnFor_x3f(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = lean_box(0);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_dec(x_8);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_9);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_dec(x_8);
x_17 = lean_box(0);
x_18 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__7(x_1, x_17, x_2, x_3, x_4, x_5, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_Lean_Meta_getConstUnfoldEqnFor_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = l_Array_isEqvAux___at_Lean_Meta_getConstUnfoldEqnFor_x3f___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_getConstUnfoldEqnFor_x3f___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_getConstUnfoldEqnFor_x3f___spec__3(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_5 = 0;
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__1___boxed), 4, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__2() {
_start:
{
uint8_t x_1; uint8_t x_2; uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_1 = 0;
x_2 = 1;
x_3 = 1;
x_4 = 0;
x_5 = 2;
x_6 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_6, 0, x_1);
lean_ctor_set_uint8(x_6, 1, x_1);
lean_ctor_set_uint8(x_6, 2, x_1);
lean_ctor_set_uint8(x_6, 3, x_1);
lean_ctor_set_uint8(x_6, 4, x_1);
lean_ctor_set_uint8(x_6, 5, x_2);
lean_ctor_set_uint8(x_6, 6, x_2);
lean_ctor_set_uint8(x_6, 7, x_1);
lean_ctor_set_uint8(x_6, 8, x_2);
lean_ctor_set_uint8(x_6, 9, x_3);
lean_ctor_set_uint8(x_6, 10, x_4);
lean_ctor_set_uint8(x_6, 11, x_2);
lean_ctor_set_uint8(x_6, 12, x_2);
lean_ctor_set_uint8(x_6, 13, x_2);
lean_ctor_set_uint8(x_6, 14, x_5);
lean_ctor_set_uint8(x_6, 15, x_2);
lean_ctor_set_uint8(x_6, 16, x_2);
lean_ctor_set_uint8(x_6, 17, x_2);
return x_6;
}
}
static uint64_t _init_l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__3() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__2;
x_2 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__6() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__5;
x_3 = l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__4;
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_tryURefl___closed__4;
x_3 = l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__6;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__2;
x_4 = l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__3;
x_5 = 0;
x_6 = l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__7;
x_7 = l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__8;
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_1);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_7);
lean_ctor_set(x_9, 4, x_2);
lean_ctor_set(x_9, 5, x_8);
lean_ctor_set(x_9, 6, x_2);
lean_ctor_set_uint64(x_9, sizeof(void*)*7, x_4);
lean_ctor_set_uint8(x_9, sizeof(void*)*7 + 8, x_5);
lean_ctor_set_uint8(x_9, sizeof(void*)*7 + 9, x_5);
lean_ctor_set_uint8(x_9, sizeof(void*)*7 + 10, x_5);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Meta_tryURefl___closed__4;
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_1);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 3, x_2);
lean_ctor_set(x_3, 4, x_2);
lean_ctor_set(x_3, 5, x_2);
lean_ctor_set(x_3, 6, x_2);
lean_ctor_set(x_3, 7, x_2);
lean_ctor_set(x_3, 8, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_tryURefl___closed__4;
x_2 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
lean_ctor_set(x_2, 4, x_1);
lean_ctor_set(x_2, 5, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_tryURefl___closed__4;
x_2 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__10;
x_3 = l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__11;
x_4 = l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__6;
x_5 = l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__12;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_1);
lean_ctor_set(x_6, 3, x_4);
lean_ctor_set(x_6, 4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__1;
x_8 = l_Lean_Meta_eqUnfoldThmSuffix;
x_9 = lean_string_dec_eq(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_10 = lean_box(0);
x_11 = lean_apply_4(x_7, x_10, x_4, x_5, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__13;
x_13 = lean_st_mk_ref(x_12, x_6);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__9;
lean_inc(x_14);
x_17 = l_Lean_Meta_getConstUnfoldEqnFor_x3f(x_2, x_16, x_14, x_4, x_5, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_get(x_14, x_19);
lean_dec(x_14);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = 0;
x_24 = lean_box(x_23);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = 0;
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_18);
x_29 = !lean_is_exclusive(x_20);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_20, 0);
lean_dec(x_30);
x_31 = 1;
x_32 = lean_box(x_31);
lean_ctor_set(x_20, 0, x_32);
return x_20;
}
else
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_20, 1);
lean_inc(x_33);
lean_dec(x_20);
x_34 = 1;
x_35 = lean_box(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_14);
x_37 = !lean_is_exclusive(x_17);
if (x_37 == 0)
{
return x_17;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_17, 0);
x_39 = lean_ctor_get(x_17, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_17);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_st_ref_get(x_3, x_4);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_5);
x_12 = l_Lean_Environment_isSafeDefinition(x_11, x_5);
if (x_12 == 0)
{
uint8_t x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_13 = 0;
x_14 = lean_box(x_13);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_free_object(x_7);
x_15 = lean_box(0);
x_16 = l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2(x_6, x_5, x_15, x_2, x_3, x_10);
lean_dec(x_6);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_7, 0);
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_7);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_5);
x_20 = l_Lean_Environment_isSafeDefinition(x_19, x_5);
if (x_20 == 0)
{
uint8_t x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_21 = 0;
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box(0);
x_25 = l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2(x_6, x_5, x_24, x_2, x_3, x_18);
lean_dec(x_6);
return x_25;
}
}
}
else
{
uint8_t x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = 0;
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_4);
return x_28;
}
}
}
static lean_object* _init_l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__3), 4, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____closed__1;
x_3 = l_Lean_registerReservedNameAction(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_7;
}
}
lean_object* initialize_Lean_Meta_Eqns(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Rfl(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Intro(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_EqUnfold(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Eqns(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Rfl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Intro(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Apply(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_tryURefl___lambda__1___closed__1 = _init_l_Lean_Meta_tryURefl___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_tryURefl___lambda__1___closed__1);
l_Lean_Meta_tryURefl___closed__1 = _init_l_Lean_Meta_tryURefl___closed__1();
lean_mark_persistent(l_Lean_Meta_tryURefl___closed__1);
l_Lean_Meta_tryURefl___closed__2 = _init_l_Lean_Meta_tryURefl___closed__2();
lean_mark_persistent(l_Lean_Meta_tryURefl___closed__2);
l_Lean_Meta_tryURefl___closed__3 = _init_l_Lean_Meta_tryURefl___closed__3();
lean_mark_persistent(l_Lean_Meta_tryURefl___closed__3);
l_Lean_Meta_tryURefl___closed__4 = _init_l_Lean_Meta_tryURefl___closed__4();
lean_mark_persistent(l_Lean_Meta_tryURefl___closed__4);
l_Lean_Meta_tryURefl___closed__5 = _init_l_Lean_Meta_tryURefl___closed__5();
lean_mark_persistent(l_Lean_Meta_tryURefl___closed__5);
l_panic___at_Lean_Meta_getConstUnfoldEqnFor_x3f___spec__1___closed__1 = _init_l_panic___at_Lean_Meta_getConstUnfoldEqnFor_x3f___spec__1___closed__1();
lean_mark_persistent(l_panic___at_Lean_Meta_getConstUnfoldEqnFor_x3f___spec__1___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_getConstUnfoldEqnFor_x3f___spec__3___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_getConstUnfoldEqnFor_x3f___spec__3___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_getConstUnfoldEqnFor_x3f___spec__3___closed__1);
l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_getConstUnfoldEqnFor_x3f___spec__3___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_getConstUnfoldEqnFor_x3f___spec__3___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at_Lean_Meta_getConstUnfoldEqnFor_x3f___spec__3___closed__2);
l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__2___closed__1 = _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__2___closed__1);
l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__2___closed__2 = _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__2___closed__2);
l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__2___closed__3 = _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__2___closed__3);
l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__2___closed__4 = _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__2___closed__4);
l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__2___closed__5 = _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__2___closed__5);
l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__3___closed__1 = _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__3___closed__1);
l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__3___closed__2 = _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__3___closed__2);
l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__6___closed__1 = _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__6___closed__1();
lean_mark_persistent(l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__6___closed__1);
l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__6___closed__2 = _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__6___closed__2();
lean_mark_persistent(l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__6___closed__2);
l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__6___closed__3 = _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__6___closed__3();
lean_mark_persistent(l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__6___closed__3);
l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__6___closed__4 = _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__6___closed__4();
lean_mark_persistent(l_Lean_Meta_getConstUnfoldEqnFor_x3f___lambda__6___closed__4);
l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__1);
l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__2 = _init_l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__2);
l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__3 = _init_l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__3();
l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__4 = _init_l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__4();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__4);
l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__5 = _init_l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__5();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__5);
l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__6 = _init_l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__6();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__6);
l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__7 = _init_l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__7();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__7);
l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__8 = _init_l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__8();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__8);
l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__9 = _init_l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__9();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__9);
l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__10 = _init_l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__10();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__10);
l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__11 = _init_l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__11();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__11);
l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__12 = _init_l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__12();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__12);
l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__13 = _init_l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__13();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____lambda__2___closed__13);
l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____closed__1 = _init_l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____closed__1();
lean_mark_persistent(l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742____closed__1);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_742_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
