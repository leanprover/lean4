// Lean compiler output
// Module: Lean.Elab.PreDefinition.EqUnfold
// Imports: Lean.Meta.Eqns Lean.Meta.Tactic.Util Lean.Meta.Tactic.Rfl Lean.Meta.Tactic.Intro Lean.Meta.Tactic.Apply Lean.DefEqAttrib
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
static lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__6;
lean_object* l_Lean_registerReservedNameAction(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__8;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__0;
static lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__5;
static lean_object* l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__16;
lean_object* l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
static lean_object* l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__19;
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
static lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__1;
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_tryURefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_tryURefl___closed__3;
static lean_object* l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__20;
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at___Lean_Meta_congrArg_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__11;
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__5;
lean_object* l_Lean_MVarId_refl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_inferDefEqAttr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_tryURefl___closed__5;
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__21;
static lean_object* l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__18;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
extern lean_object* l_Lean_Meta_smartUnfolding;
static lean_object* l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__3;
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
static lean_object* l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__0;
static lean_object* l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__14;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0(uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__4;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_tryURefl___closed__0;
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___closed__3;
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__3;
lean_object* l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_privateToUserName(lean_object*);
lean_object* l_Lean_Meta_mkEqLikeNameFor(lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__7;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__3;
static lean_object* l_Lean_Meta_tryURefl___closed__2;
static lean_object* l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__23;
extern lean_object* l_Lean_diagnostics;
static lean_object* l_Lean_Meta_tryURefl___closed__1;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
static lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__2;
static lean_object* l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__9;
static lean_object* l_Lean_Meta_tryURefl___closed__4;
lean_object* l_Lean_Meta_realizeConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__6;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0___closed__1;
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__2;
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(lean_object*, lean_object*, uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__0;
uint8_t l_Lean_Environment_isSafeDefinition(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0___closed__0;
lean_object* l_Lean_Expr_getAppFn(lean_object*);
static lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__5;
lean_object* l_Lean_Meta_forallTelescope___at___Lean_Meta_mapForallTelescope_x27_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__12;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getUnfoldEqnFor_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__17;
static lean_object* l_Lean_Meta_initFn___lam__0___closed__0____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871_;
size_t lean_usize_add(size_t, size_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__1;
static lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__2;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__4;
static lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___closed__2;
static lean_object* l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__15;
LEAN_EXPORT lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___closed__0;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__1;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871_(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__22;
lean_object* l_Lean_mkConstWithLevelParams___at___Lean_Meta_registerCoercion_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__6;
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
static lean_object* l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__13;
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEqvAux___at___Lean_Meta_beqAbstractMVarsResult____x40_Lean_Meta_Basic___hyg_1771__spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_tryURefl___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_smartUnfolding;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_tryURefl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_diagnostics;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_tryURefl___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_maxRecDepth;
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
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_73; uint8_t x_98; 
x_13 = lean_st_ref_get(x_5, x_6);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_16);
x_17 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_17);
x_18 = lean_ctor_get(x_4, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_4, 3);
lean_inc(x_19);
x_20 = lean_ctor_get(x_4, 5);
lean_inc(x_20);
x_21 = lean_ctor_get(x_4, 6);
lean_inc(x_21);
x_22 = lean_ctor_get(x_4, 7);
lean_inc(x_22);
x_23 = lean_ctor_get(x_4, 8);
lean_inc(x_23);
x_24 = lean_ctor_get(x_4, 9);
lean_inc(x_24);
x_25 = lean_ctor_get(x_4, 10);
lean_inc(x_25);
x_26 = lean_ctor_get(x_4, 11);
lean_inc(x_26);
x_27 = lean_ctor_get_uint8(x_4, sizeof(void*)*13 + 1);
x_28 = lean_ctor_get(x_4, 12);
lean_inc_ref(x_28);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 lean_ctor_release(x_4, 2);
 lean_ctor_release(x_4, 3);
 lean_ctor_release(x_4, 4);
 lean_ctor_release(x_4, 5);
 lean_ctor_release(x_4, 6);
 lean_ctor_release(x_4, 7);
 lean_ctor_release(x_4, 8);
 lean_ctor_release(x_4, 9);
 lean_ctor_release(x_4, 10);
 lean_ctor_release(x_4, 11);
 lean_ctor_release(x_4, 12);
 x_29 = x_4;
} else {
 lean_dec_ref(x_4);
 x_29 = lean_box(0);
}
x_30 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_30);
lean_dec(x_14);
x_31 = l_Lean_Meta_tryURefl___closed__0;
x_32 = 0;
x_33 = l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(x_18, x_31, x_32);
x_34 = l_Lean_Meta_tryURefl___closed__1;
x_35 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_33, x_34);
x_98 = l_Lean_Kernel_isDiagnosticsEnabled(x_30);
lean_dec_ref(x_30);
if (x_98 == 0)
{
if (x_35 == 0)
{
x_36 = x_16;
x_37 = x_17;
x_38 = x_19;
x_39 = x_20;
x_40 = x_21;
x_41 = x_22;
x_42 = x_23;
x_43 = x_24;
x_44 = x_25;
x_45 = x_26;
x_46 = x_27;
x_47 = x_28;
x_48 = x_5;
x_49 = x_15;
goto block_72;
}
else
{
x_73 = x_98;
goto block_97;
}
}
else
{
x_73 = x_35;
goto block_97;
}
block_12:
{
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec_ref(x_8);
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
return x_8;
}
}
block_72:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = l_Lean_Meta_tryURefl___closed__2;
x_51 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_33, x_50);
if (lean_is_scalar(x_29)) {
 x_52 = lean_alloc_ctor(0, 13, 2);
} else {
 x_52 = x_29;
}
lean_ctor_set(x_52, 0, x_36);
lean_ctor_set(x_52, 1, x_37);
lean_ctor_set(x_52, 2, x_33);
lean_ctor_set(x_52, 3, x_38);
lean_ctor_set(x_52, 4, x_51);
lean_ctor_set(x_52, 5, x_39);
lean_ctor_set(x_52, 6, x_40);
lean_ctor_set(x_52, 7, x_41);
lean_ctor_set(x_52, 8, x_42);
lean_ctor_set(x_52, 9, x_43);
lean_ctor_set(x_52, 10, x_44);
lean_ctor_set(x_52, 11, x_45);
lean_ctor_set(x_52, 12, x_47);
lean_ctor_set_uint8(x_52, sizeof(void*)*13, x_35);
lean_ctor_set_uint8(x_52, sizeof(void*)*13 + 1, x_46);
x_53 = l_Lean_MVarId_refl(x_1, x_2, x_3, x_52, x_48, x_49);
if (lean_obj_tag(x_53) == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_53, 0);
lean_dec(x_55);
x_56 = 1;
x_57 = lean_box(x_56);
lean_ctor_set(x_53, 0, x_57);
return x_53;
}
else
{
lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
lean_dec(x_53);
x_59 = 1;
x_60 = lean_box(x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_58);
return x_61;
}
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_53);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = lean_ctor_get(x_53, 0);
x_64 = lean_ctor_get(x_53, 1);
lean_inc(x_64);
lean_inc(x_63);
x_65 = l_Lean_Exception_isInterrupt(x_63);
if (x_65 == 0)
{
uint8_t x_66; 
x_66 = l_Lean_Exception_isRuntime(x_63);
lean_dec(x_63);
x_7 = x_64;
x_8 = x_53;
x_9 = x_66;
goto block_12;
}
else
{
lean_dec(x_63);
x_7 = x_64;
x_8 = x_53;
x_9 = x_65;
goto block_12;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_67 = lean_ctor_get(x_53, 0);
x_68 = lean_ctor_get(x_53, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_53);
lean_inc(x_68);
lean_inc(x_67);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_Exception_isInterrupt(x_67);
if (x_70 == 0)
{
uint8_t x_71; 
x_71 = l_Lean_Exception_isRuntime(x_67);
lean_dec(x_67);
x_7 = x_68;
x_8 = x_69;
x_9 = x_71;
goto block_12;
}
else
{
lean_dec(x_67);
x_7 = x_68;
x_8 = x_69;
x_9 = x_70;
goto block_12;
}
}
}
}
block_97:
{
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_74 = lean_st_ref_take(x_5, x_15);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec_ref(x_74);
x_77 = !lean_is_exclusive(x_75);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_78 = lean_ctor_get(x_75, 0);
x_79 = lean_ctor_get(x_75, 5);
lean_dec(x_79);
x_80 = l_Lean_Kernel_enableDiag(x_78, x_35);
x_81 = l_Lean_Meta_tryURefl___closed__5;
lean_ctor_set(x_75, 5, x_81);
lean_ctor_set(x_75, 0, x_80);
x_82 = lean_st_ref_set(x_5, x_75, x_76);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec_ref(x_82);
x_36 = x_16;
x_37 = x_17;
x_38 = x_19;
x_39 = x_20;
x_40 = x_21;
x_41 = x_22;
x_42 = x_23;
x_43 = x_24;
x_44 = x_25;
x_45 = x_26;
x_46 = x_27;
x_47 = x_28;
x_48 = x_5;
x_49 = x_83;
goto block_72;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_84 = lean_ctor_get(x_75, 0);
x_85 = lean_ctor_get(x_75, 1);
x_86 = lean_ctor_get(x_75, 2);
x_87 = lean_ctor_get(x_75, 3);
x_88 = lean_ctor_get(x_75, 4);
x_89 = lean_ctor_get(x_75, 6);
x_90 = lean_ctor_get(x_75, 7);
x_91 = lean_ctor_get(x_75, 8);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_75);
x_92 = l_Lean_Kernel_enableDiag(x_84, x_35);
x_93 = l_Lean_Meta_tryURefl___closed__5;
x_94 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_85);
lean_ctor_set(x_94, 2, x_86);
lean_ctor_set(x_94, 3, x_87);
lean_ctor_set(x_94, 4, x_88);
lean_ctor_set(x_94, 5, x_93);
lean_ctor_set(x_94, 6, x_89);
lean_ctor_set(x_94, 7, x_90);
lean_ctor_set(x_94, 8, x_91);
x_95 = lean_st_ref_set(x_5, x_94, x_76);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec_ref(x_95);
x_36 = x_16;
x_37 = x_17;
x_38 = x_19;
x_39 = x_20;
x_40 = x_21;
x_41 = x_22;
x_42 = x_23;
x_43 = x_24;
x_44 = x_25;
x_45 = x_26;
x_46 = x_27;
x_47 = x_28;
x_48 = x_5;
x_49 = x_96;
goto block_72;
}
}
else
{
x_36 = x_16;
x_37 = x_17;
x_38 = x_19;
x_39 = x_20;
x_40 = x_21;
x_41 = x_22;
x_42 = x_23;
x_43 = x_24;
x_44 = x_25;
x_45 = x_26;
x_46 = x_27;
x_47 = x_28;
x_48 = x_5;
x_49 = x_15;
goto block_72;
}
}
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("funext", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0___closed__1;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0(uint8_t x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_14 = lean_array_uget(x_3, x_5);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0___closed__0;
x_16 = lean_array_push(x_15, x_14);
x_17 = 1;
x_18 = l_Lean_Meta_mkLambdaFVars(x_16, x_6, x_1, x_2, x_1, x_2, x_17, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0___closed__2;
x_22 = lean_array_push(x_15, x_19);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_23 = l_Lean_Meta_mkAppM(x_21, x_22, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; size_t x_26; size_t x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
x_26 = 1;
x_27 = lean_usize_add(x_5, x_26);
x_5 = x_27;
x_6 = x_24;
x_11 = x_25;
goto _start;
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_23;
}
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_18;
}
}
}
}
static lean_object* _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Unexpected unfold theorem type ", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__4;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__5;
x_29 = lean_unsigned_to_nat(3u);
x_30 = l_Lean_Expr_isAppOfArity(x_6, x_28, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec_ref(x_5);
x_31 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__1;
x_32 = l_Lean_MessageData_ofExpr(x_1);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__3;
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_35, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = l_Lean_Expr_appFn_x21(x_6);
x_38 = l_Lean_Expr_appArg_x21(x_37);
lean_dec_ref(x_37);
x_39 = l_Lean_Expr_appArg_x21(x_6);
x_40 = l_Lean_Expr_getAppFn(x_38);
x_41 = l_Lean_Expr_isConstOf(x_40, x_4);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
lean_dec_ref(x_40);
lean_dec_ref(x_39);
lean_dec_ref(x_38);
lean_dec_ref(x_5);
x_42 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__1;
x_43 = l_Lean_MessageData_ofExpr(x_1);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__3;
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_46, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
return x_47;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_47);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_52 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__6;
x_53 = l_Lean_Expr_getAppNumArgs(x_38);
lean_inc(x_53);
x_54 = lean_mk_array(x_53, x_52);
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_nat_sub(x_53, x_55);
lean_dec(x_53);
x_57 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_38, x_54, x_56);
x_58 = lean_array_get_size(x_57);
x_59 = lean_array_get_size(x_5);
x_60 = lean_nat_dec_eq(x_58, x_59);
lean_dec(x_59);
if (x_60 == 0)
{
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec_ref(x_40);
lean_dec_ref(x_39);
lean_dec_ref(x_5);
x_12 = x_10;
x_13 = x_7;
x_14 = x_11;
x_15 = x_8;
x_16 = x_9;
goto block_27;
}
else
{
uint8_t x_61; 
x_61 = l_Array_isEqvAux___at___Lean_Meta_beqAbstractMVarsResult____x40_Lean_Meta_Basic___hyg_1771__spec__1___redArg(x_57, x_5, x_58);
lean_dec_ref(x_57);
if (x_61 == 0)
{
lean_dec_ref(x_40);
lean_dec_ref(x_39);
lean_dec_ref(x_5);
x_12 = x_10;
x_13 = x_7;
x_14 = x_11;
x_15 = x_8;
x_16 = x_9;
goto block_27;
}
else
{
uint8_t x_62; lean_object* x_63; 
lean_dec_ref(x_1);
x_62 = 1;
x_63 = l_Lean_Meta_mkLambdaFVars(x_5, x_39, x_2, x_3, x_2, x_3, x_62, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec_ref(x_63);
x_66 = l_Lean_Meta_mkEq(x_40, x_64, x_7, x_8, x_9, x_10, x_65);
return x_66;
}
else
{
lean_dec_ref(x_40);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
return x_63;
}
}
}
}
}
block_27:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_17 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__1;
x_18 = l_Lean_MessageData_ofExpr(x_1);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__3;
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_21, x_13, x_15, x_16, x_12, x_14);
lean_dec(x_12);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_13);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_22);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__1(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_mkConstWithLevelParams___at___Lean_Meta_registerCoercion_spec__0(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = l_Lean_mkAppN(x_12, x_4);
x_15 = l_Array_reverse___redArg(x_4);
x_16 = lean_array_size(x_15);
x_17 = 0;
x_18 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0(x_2, x_3, x_15, x_16, x_17, x_14, x_6, x_7, x_8, x_9, x_13);
lean_dec_ref(x_15);
return x_18;
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_inc_ref(x_6);
x_11 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_1, x_2, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = l_Lean_Expr_mvarId_x21(x_12);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_15 = l_Lean_Meta_tryURefl(x_14, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_12);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec_ref(x_15);
x_19 = l_Lean_Meta_forallTelescope___at___Lean_Meta_mapForallTelescope_x27_spec__0___redArg(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_18);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec_ref(x_15);
x_21 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_mkLevelErrorMessageCore_spec__1___redArg(x_12, x_7, x_20);
lean_dec(x_7);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_15);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
static lean_object* _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Elab.PreDefinition.EqUnfold", 32, 32);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean.Meta.getConstUnfoldEqnFor\?", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___closed__2;
x_2 = lean_unsigned_to_nat(74u);
x_3 = lean_unsigned_to_nat(32u);
x_4 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___closed__1;
x_5 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___closed__0;
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_1);
x_10 = l_Lean_Meta_getUnfoldEqnFor_x3f(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_1);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___closed__3;
x_14 = l_panic___at___Lean_Meta_congrArg_x3f_spec__0(x_13, x_5, x_6, x_7, x_8, x_12);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec_ref(x_10);
x_16 = !lean_is_exclusive(x_11);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_11, 0);
lean_inc(x_17);
x_18 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_17, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec_ref(x_18);
x_21 = l_Lean_ConstantInfo_type(x_19);
x_22 = lean_box(x_3);
x_23 = lean_box(x_2);
lean_inc_ref(x_21);
x_24 = lean_alloc_closure((void*)(l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___boxed), 11, 4);
lean_closure_set(x_24, 0, x_21);
lean_closure_set(x_24, 1, x_22);
lean_closure_set(x_24, 2, x_23);
lean_closure_set(x_24, 3, x_1);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_21);
x_25 = l_Lean_Meta_forallTelescope___at___Lean_Meta_mapForallTelescope_x27_spec__0___redArg(x_21, x_24, x_3, x_5, x_6, x_7, x_8, x_20);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = lean_box(x_3);
x_29 = lean_box(x_2);
x_30 = lean_alloc_closure((void*)(l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__1___boxed), 10, 3);
lean_closure_set(x_30, 0, x_17);
lean_closure_set(x_30, 1, x_28);
lean_closure_set(x_30, 2, x_29);
x_31 = lean_box(0);
x_32 = lean_box(x_3);
lean_inc(x_26);
x_33 = lean_alloc_closure((void*)(l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__2___boxed), 10, 5);
lean_closure_set(x_33, 0, x_26);
lean_closure_set(x_33, 1, x_31);
lean_closure_set(x_33, 2, x_21);
lean_closure_set(x_33, 3, x_30);
lean_closure_set(x_33, 4, x_32);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_34 = l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(x_33, x_3, x_5, x_6, x_7, x_8, x_27);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec_ref(x_34);
x_37 = l_Lean_ConstantInfo_levelParams(x_19);
lean_dec(x_19);
lean_inc(x_4);
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_4);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_38, 2, x_26);
x_39 = lean_box(0);
lean_inc(x_4);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_4);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_35);
lean_ctor_set(x_41, 2, x_40);
lean_ctor_set_tag(x_11, 2);
lean_ctor_set(x_11, 0, x_41);
lean_inc(x_8);
lean_inc_ref(x_7);
x_42 = l_Lean_addDecl(x_11, x_7, x_8, x_36);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec_ref(x_42);
x_44 = l_Lean_inferDefEqAttr(x_4, x_5, x_6, x_7, x_8, x_43);
return x_44;
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_42;
}
}
else
{
uint8_t x_45; 
lean_dec(x_26);
lean_dec(x_19);
lean_free_object(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_45 = !lean_is_exclusive(x_34);
if (x_45 == 0)
{
return x_34;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_34, 0);
x_47 = lean_ctor_get(x_34, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_34);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec_ref(x_21);
lean_dec(x_19);
lean_free_object(x_11);
lean_dec(x_17);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_49 = !lean_is_exclusive(x_25);
if (x_49 == 0)
{
return x_25;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_25, 0);
x_51 = lean_ctor_get(x_25, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_25);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_free_object(x_11);
lean_dec(x_17);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_18);
if (x_53 == 0)
{
return x_18;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_18, 0);
x_55 = lean_ctor_get(x_18, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_18);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_11, 0);
lean_inc(x_57);
lean_dec(x_11);
lean_inc(x_57);
x_58 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_57, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec_ref(x_58);
x_61 = l_Lean_ConstantInfo_type(x_59);
x_62 = lean_box(x_3);
x_63 = lean_box(x_2);
lean_inc_ref(x_61);
x_64 = lean_alloc_closure((void*)(l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___boxed), 11, 4);
lean_closure_set(x_64, 0, x_61);
lean_closure_set(x_64, 1, x_62);
lean_closure_set(x_64, 2, x_63);
lean_closure_set(x_64, 3, x_1);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_61);
x_65 = l_Lean_Meta_forallTelescope___at___Lean_Meta_mapForallTelescope_x27_spec__0___redArg(x_61, x_64, x_3, x_5, x_6, x_7, x_8, x_60);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec_ref(x_65);
x_68 = lean_box(x_3);
x_69 = lean_box(x_2);
x_70 = lean_alloc_closure((void*)(l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__1___boxed), 10, 3);
lean_closure_set(x_70, 0, x_57);
lean_closure_set(x_70, 1, x_68);
lean_closure_set(x_70, 2, x_69);
x_71 = lean_box(0);
x_72 = lean_box(x_3);
lean_inc(x_66);
x_73 = lean_alloc_closure((void*)(l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__2___boxed), 10, 5);
lean_closure_set(x_73, 0, x_66);
lean_closure_set(x_73, 1, x_71);
lean_closure_set(x_73, 2, x_61);
lean_closure_set(x_73, 3, x_70);
lean_closure_set(x_73, 4, x_72);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_74 = l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(x_73, x_3, x_5, x_6, x_7, x_8, x_67);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec_ref(x_74);
x_77 = l_Lean_ConstantInfo_levelParams(x_59);
lean_dec(x_59);
lean_inc(x_4);
x_78 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_78, 0, x_4);
lean_ctor_set(x_78, 1, x_77);
lean_ctor_set(x_78, 2, x_66);
x_79 = lean_box(0);
lean_inc(x_4);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_4);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_75);
lean_ctor_set(x_81, 2, x_80);
x_82 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_82, 0, x_81);
lean_inc(x_8);
lean_inc_ref(x_7);
x_83 = l_Lean_addDecl(x_82, x_7, x_8, x_76);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec_ref(x_83);
x_85 = l_Lean_inferDefEqAttr(x_4, x_5, x_6, x_7, x_8, x_84);
return x_85;
}
else
{
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_83;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_66);
lean_dec(x_59);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_86 = lean_ctor_get(x_74, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_74, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_88 = x_74;
} else {
 lean_dec_ref(x_74);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec_ref(x_61);
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_90 = lean_ctor_get(x_65, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_65, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_92 = x_65;
} else {
 lean_dec_ref(x_65);
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
lean_dec(x_57);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_94 = lean_ctor_get(x_58, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_58, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_96 = x_58;
} else {
 lean_dec_ref(x_58);
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
}
else
{
uint8_t x_98; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_10);
if (x_98 == 0)
{
return x_10;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_10, 0);
x_100 = lean_ctor_get(x_10, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_10);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
}
static lean_object* _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ReservedNameAction", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("getConstUnfoldEqnFor\? ", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" failed, no unfold theorem available", 36, 36);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__4;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_unfold", 9, 9);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = 1;
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
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
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_8, 0);
lean_dec(x_12);
x_13 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__1;
x_14 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_13, x_4, x_11);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_free_object(x_8);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
lean_ctor_set(x_14, 0, x_9);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_dec_ref(x_14);
x_22 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__3;
x_23 = l_Lean_MessageData_ofName(x_1);
lean_ctor_set_tag(x_8, 7);
lean_ctor_set(x_8, 1, x_23);
lean_ctor_set(x_8, 0, x_22);
x_24 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__5;
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_8);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_13, x_25, x_2, x_3, x_4, x_5, x_21);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_9);
return x_26;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_9);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_8, 1);
lean_inc(x_31);
lean_dec(x_8);
x_32 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__1;
x_33 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0___redArg(x_32, x_4, x_31);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_37 = x_33;
} else {
 lean_dec_ref(x_33);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_9);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_dec_ref(x_33);
x_40 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__3;
x_41 = l_Lean_MessageData_ofName(x_1);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__5;
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_32, x_44, x_2, x_3, x_4, x_5, x_39);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_9);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
else
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_8, 1);
lean_inc(x_49);
lean_dec_ref(x_8);
x_50 = !lean_is_exclusive(x_9);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_51 = lean_ctor_get(x_9, 0);
lean_dec(x_51);
x_52 = lean_st_ref_get(x_5, x_49);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec_ref(x_52);
x_55 = lean_ctor_get(x_53, 0);
lean_inc_ref(x_55);
lean_dec(x_53);
x_56 = 0;
x_57 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__6;
lean_inc(x_1);
x_58 = l_Lean_Meta_mkEqLikeNameFor(x_55, x_1, x_57);
x_59 = lean_box(x_7);
x_60 = lean_box(x_56);
lean_inc(x_58);
lean_inc(x_1);
x_61 = lean_alloc_closure((void*)(l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___boxed), 9, 4);
lean_closure_set(x_61, 0, x_1);
lean_closure_set(x_61, 1, x_59);
lean_closure_set(x_61, 2, x_60);
lean_closure_set(x_61, 3, x_58);
lean_inc(x_58);
x_62 = l_Lean_Meta_realizeConst(x_1, x_58, x_61, x_2, x_3, x_4, x_5, x_54);
if (lean_obj_tag(x_62) == 0)
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_62, 0);
lean_dec(x_64);
lean_ctor_set(x_9, 0, x_58);
lean_ctor_set(x_62, 0, x_9);
return x_62;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
lean_ctor_set(x_9, 0, x_58);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_9);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
else
{
uint8_t x_67; 
lean_dec(x_58);
lean_free_object(x_9);
x_67 = !lean_is_exclusive(x_62);
if (x_67 == 0)
{
return x_62;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_62, 0);
x_69 = lean_ctor_get(x_62, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_62);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_9);
x_71 = lean_st_ref_get(x_5, x_49);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec_ref(x_71);
x_74 = lean_ctor_get(x_72, 0);
lean_inc_ref(x_74);
lean_dec(x_72);
x_75 = 0;
x_76 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__6;
lean_inc(x_1);
x_77 = l_Lean_Meta_mkEqLikeNameFor(x_74, x_1, x_76);
x_78 = lean_box(x_7);
x_79 = lean_box(x_75);
lean_inc(x_77);
lean_inc(x_1);
x_80 = lean_alloc_closure((void*)(l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___boxed), 9, 4);
lean_closure_set(x_80, 0, x_1);
lean_closure_set(x_80, 1, x_78);
lean_closure_set(x_80, 2, x_79);
lean_closure_set(x_80, 3, x_77);
lean_inc(x_77);
x_81 = l_Lean_Meta_realizeConst(x_1, x_77, x_80, x_2, x_3, x_4, x_5, x_73);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_83 = x_81;
} else {
 lean_dec_ref(x_81);
 x_83 = lean_box(0);
}
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_77);
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
lean_dec(x_77);
x_86 = lean_ctor_get(x_81, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_81, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_88 = x_81;
} else {
 lean_dec_ref(x_81);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
}
}
else
{
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_12 = lean_unbox(x_1);
x_13 = lean_unbox(x_2);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0(x_12, x_13, x_3, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_2);
x_13 = lean_unbox(x_3);
x_14 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_2);
x_12 = lean_unbox(x_3);
x_13 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__1(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
x_12 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__2(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_2);
x_11 = lean_unbox(x_3);
x_12 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__6;
x_2 = l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__5;
x_3 = l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__4;
x_4 = l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__3;
x_5 = l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__2;
x_6 = l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__1;
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_8, 2, x_7);
lean_ctor_set(x_8, 3, x_6);
lean_ctor_set(x_8, 4, x_5);
lean_ctor_set(x_8, 5, x_4);
lean_ctor_set(x_8, 6, x_3);
lean_ctor_set(x_8, 7, x_2);
lean_ctor_set(x_8, 8, x_1);
return x_8;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__11;
x_2 = l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__10;
x_3 = l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__9;
x_4 = l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__8;
x_5 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_4);
lean_ctor_set(x_5, 4, x_1);
lean_ctor_set(x_5, 5, x_1);
return x_5;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__13;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__15() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__13;
x_4 = l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__14;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__16;
x_2 = l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__1;
x_3 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
return x_3;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__17;
x_2 = l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__15;
x_3 = lean_box(0);
x_4 = l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__12;
x_5 = l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__7;
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__0;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__13;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__21() {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__13;
x_4 = l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__20;
x_5 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set(x_5, 3, x_2);
lean_ctor_set_usize(x_5, 4, x_1);
return x_5;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__21;
x_3 = l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__19;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_18; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_10);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
lean_dec_ref(x_7);
x_19 = lean_ctor_get(x_6, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_6, 1);
lean_inc(x_20);
lean_dec(x_6);
lean_inc(x_19);
lean_inc_ref(x_1);
x_21 = l_Lean_Environment_isSafeDefinition(x_1, x_19);
if (x_21 == 0)
{
lean_dec(x_19);
lean_inc_ref(x_3);
{
lean_object* _tmp_5 = x_20;
lean_object* _tmp_6 = x_3;
x_6 = _tmp_5;
x_7 = _tmp_6;
}
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; lean_object* x_36; uint64_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_20);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_27 = lean_box(0);
x_28 = lean_unsigned_to_nat(0u);
x_29 = l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__18;
x_30 = lean_st_mk_ref(x_29, x_10);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec_ref(x_30);
x_33 = 1;
x_34 = 0;
x_35 = 2;
x_36 = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(x_36, 0, x_4);
lean_ctor_set_uint8(x_36, 1, x_4);
lean_ctor_set_uint8(x_36, 2, x_4);
lean_ctor_set_uint8(x_36, 3, x_4);
lean_ctor_set_uint8(x_36, 4, x_4);
lean_ctor_set_uint8(x_36, 5, x_5);
lean_ctor_set_uint8(x_36, 6, x_5);
lean_ctor_set_uint8(x_36, 7, x_4);
lean_ctor_set_uint8(x_36, 8, x_5);
lean_ctor_set_uint8(x_36, 9, x_33);
lean_ctor_set_uint8(x_36, 10, x_34);
lean_ctor_set_uint8(x_36, 11, x_5);
lean_ctor_set_uint8(x_36, 12, x_5);
lean_ctor_set_uint8(x_36, 13, x_5);
lean_ctor_set_uint8(x_36, 14, x_35);
lean_ctor_set_uint8(x_36, 15, x_5);
lean_ctor_set_uint8(x_36, 16, x_5);
lean_ctor_set_uint8(x_36, 17, x_5);
lean_ctor_set_uint8(x_36, 18, x_5);
x_37 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_36);
x_38 = l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__22;
x_39 = l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__23;
x_40 = lean_box(0);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_27);
lean_ctor_set(x_42, 2, x_38);
lean_ctor_set(x_42, 3, x_39);
lean_ctor_set(x_42, 4, x_40);
lean_ctor_set(x_42, 5, x_28);
lean_ctor_set(x_42, 6, x_41);
lean_ctor_set_uint64(x_42, sizeof(void*)*7, x_37);
lean_ctor_set_uint8(x_42, sizeof(void*)*7 + 8, x_4);
lean_ctor_set_uint8(x_42, sizeof(void*)*7 + 9, x_4);
lean_ctor_set_uint8(x_42, sizeof(void*)*7 + 10, x_4);
lean_inc(x_31);
x_43 = l_Lean_Meta_getConstUnfoldEqnFor_x3f(x_19, x_42, x_31, x_8, x_9, x_32);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec_ref(x_43);
x_46 = lean_st_ref_get(x_31, x_45);
lean_dec(x_31);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec_ref(x_46);
x_22 = x_44;
x_23 = x_47;
goto block_25;
}
else
{
lean_dec(x_31);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_43, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
lean_dec_ref(x_43);
x_22 = x_48;
x_23 = x_49;
goto block_25;
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_43);
if (x_50 == 0)
{
return x_43;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_43, 0);
x_52 = lean_ctor_get(x_43, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_43);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
block_25:
{
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_24; 
x_24 = 0;
x_11 = x_23;
x_12 = x_24;
goto block_17;
}
else
{
lean_dec(x_22);
x_11 = x_23;
x_12 = x_21;
goto block_17;
}
}
}
block_17:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_box(x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_7, x_8, x_10, x_11, x_12);
return x_13;
}
}
static lean_object* _init_l_Lean_Meta_initFn___lam__0___closed__0____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn___lam__0____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_11);
lean_dec(x_1);
x_12 = l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__6;
x_13 = lean_string_dec_eq(x_11, x_12);
lean_dec_ref(x_11);
if (x_13 == 0)
{
lean_dec(x_10);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = x_4;
goto block_9;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_st_ref_get(x_3, x_4);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_16, 0);
lean_inc_ref(x_18);
lean_dec(x_16);
x_19 = 0;
x_20 = l_Lean_Environment_setExporting(x_18, x_19);
lean_inc(x_10);
x_21 = l_Lean_privateToUserName(x_10);
x_22 = lean_box(0);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 1, x_22);
lean_ctor_set(x_14, 0, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_10);
lean_ctor_set(x_23, 1, x_14);
x_24 = lean_box(0);
x_25 = l_Lean_Meta_initFn___lam__0___closed__0____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871_;
x_26 = l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg(x_20, x_24, x_25, x_19, x_13, x_23, x_25, x_2, x_3, x_17);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec_ref(x_26);
x_5 = x_29;
goto block_9;
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_26);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_26, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_28, 0);
lean_inc(x_32);
lean_dec(x_28);
lean_ctor_set(x_26, 0, x_32);
return x_26;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_dec(x_26);
x_34 = lean_ctor_get(x_28, 0);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_26);
if (x_36 == 0)
{
return x_26;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_26, 0);
x_38 = lean_ctor_get(x_26, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_26);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_40 = lean_ctor_get(x_14, 0);
x_41 = lean_ctor_get(x_14, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_14);
x_42 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_42);
lean_dec(x_40);
x_43 = 0;
x_44 = l_Lean_Environment_setExporting(x_42, x_43);
lean_inc(x_10);
x_45 = l_Lean_privateToUserName(x_10);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_10);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_box(0);
x_50 = l_Lean_Meta_initFn___lam__0___closed__0____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871_;
x_51 = l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg(x_44, x_49, x_50, x_43, x_13, x_48, x_50, x_2, x_3, x_41);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec(x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec_ref(x_51);
x_5 = x_54;
goto block_9;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_51, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_56 = x_51;
} else {
 lean_dec_ref(x_51);
 x_56 = lean_box(0);
}
x_57 = lean_ctor_get(x_53, 0);
lean_inc(x_57);
lean_dec(x_53);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_51, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_51, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_61 = x_51;
} else {
 lean_dec_ref(x_51);
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
else
{
uint8_t x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_63 = 0;
x_64 = lean_box(x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_4);
return x_65;
}
block_9:
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_6 = 0;
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_initFn___lam__0____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871_), 4, 0);
x_3 = l_Lean_registerReservedNameAction(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_4);
x_12 = lean_unbox(x_5);
x_13 = l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg(x_1, x_2, x_3, x_11, x_12, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_4);
x_14 = lean_unbox(x_5);
x_15 = l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0(x_1, x_2, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
return x_15;
}
}
lean_object* initialize_Lean_Meta_Eqns(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Rfl(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Intro(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_DefEqAttrib(uint8_t builtin, lean_object*);
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
res = initialize_Lean_DefEqAttrib(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_tryURefl___closed__0 = _init_l_Lean_Meta_tryURefl___closed__0();
lean_mark_persistent(l_Lean_Meta_tryURefl___closed__0);
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
l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0___closed__0 = _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0___closed__0();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0___closed__0);
l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0___closed__1 = _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0___closed__1();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0___closed__1);
l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0___closed__2 = _init_l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0___closed__2();
lean_mark_persistent(l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_getConstUnfoldEqnFor_x3f_spec__0___closed__2);
l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__0 = _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__0();
lean_mark_persistent(l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__0);
l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__1 = _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__1();
lean_mark_persistent(l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__1);
l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__2 = _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__2();
lean_mark_persistent(l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__2);
l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__3 = _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__3();
lean_mark_persistent(l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__3);
l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__4 = _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__4();
lean_mark_persistent(l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__4);
l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__5 = _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__5();
lean_mark_persistent(l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__5);
l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__6 = _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__6();
lean_mark_persistent(l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__0___closed__6);
l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___closed__0 = _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___closed__0();
lean_mark_persistent(l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___closed__0);
l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___closed__1 = _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___closed__1();
lean_mark_persistent(l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___closed__1);
l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___closed__2 = _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___closed__2();
lean_mark_persistent(l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___closed__2);
l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___closed__3 = _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___closed__3();
lean_mark_persistent(l_Lean_Meta_getConstUnfoldEqnFor_x3f___lam__3___closed__3);
l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__0 = _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__0();
lean_mark_persistent(l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__0);
l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__1 = _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__1();
lean_mark_persistent(l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__1);
l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__2 = _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__2();
lean_mark_persistent(l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__2);
l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__3 = _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__3();
lean_mark_persistent(l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__3);
l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__4 = _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__4();
lean_mark_persistent(l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__4);
l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__5 = _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__5();
lean_mark_persistent(l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__5);
l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__6 = _init_l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__6();
lean_mark_persistent(l_Lean_Meta_getConstUnfoldEqnFor_x3f___closed__6);
l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__0 = _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__0();
lean_mark_persistent(l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__0);
l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__1 = _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__1();
lean_mark_persistent(l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__1);
l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__2 = _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__2();
lean_mark_persistent(l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__2);
l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__3 = _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__3();
lean_mark_persistent(l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__3);
l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__4 = _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__4();
lean_mark_persistent(l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__4);
l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__5 = _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__5();
lean_mark_persistent(l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__5);
l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__6 = _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__6();
lean_mark_persistent(l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__6);
l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__7 = _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__7();
lean_mark_persistent(l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__7);
l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__8 = _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__8();
lean_mark_persistent(l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__8);
l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__9 = _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__9();
lean_mark_persistent(l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__9);
l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__10 = _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__10();
lean_mark_persistent(l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__10);
l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__11 = _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__11();
lean_mark_persistent(l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__11);
l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__12 = _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__12();
lean_mark_persistent(l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__12);
l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__13 = _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__13();
lean_mark_persistent(l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__13);
l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__14 = _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__14();
lean_mark_persistent(l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__14);
l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__15 = _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__15();
lean_mark_persistent(l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__15);
l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__16 = _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__16();
lean_mark_persistent(l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__16);
l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__17 = _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__17();
lean_mark_persistent(l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__17);
l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__18 = _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__18();
lean_mark_persistent(l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__18);
l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__19 = _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__19();
lean_mark_persistent(l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__19);
l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__20 = _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__20();
lean_mark_persistent(l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__20);
l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__21 = _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__21();
lean_mark_persistent(l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__21);
l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__22 = _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__22();
lean_mark_persistent(l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__22);
l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__23 = _init_l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__23();
lean_mark_persistent(l_List_forIn_x27_loop___at___Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871__spec__0___redArg___closed__23);
l_Lean_Meta_initFn___lam__0___closed__0____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871_ = _init_l_Lean_Meta_initFn___lam__0___closed__0____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871_();
lean_mark_persistent(l_Lean_Meta_initFn___lam__0___closed__0____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871_);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Elab_PreDefinition_EqUnfold___hyg_871_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
