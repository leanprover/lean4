// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.ForallProp
// Imports: Init.Grind.Lemmas Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Grind.Internalize Lean.Meta.Tactic.Grind.Simp Lean.Meta.Tactic.Grind.EqResolution Lean.Meta.Tactic.Grind.SynthInstance
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
static lean_object* l_Lean_Meta_Grind_simpForall___closed__37;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___closed__0;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__34;
lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__12;
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__6;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36___closed__5____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__29;
lean_object* l_Lean_Meta_Grind_addNewRawFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__1;
lean_object* l_Lean_Meta_Grind_synthInstanceMeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__16;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36___closed__2____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_;
static lean_object* l_Lean_Meta_Grind_propagateExistsDown___closed__5;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__31___closed__5____x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_;
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__2;
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__7;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__25;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__3;
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static double l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__0;
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at_____private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__0(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__6;
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__19;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at_____private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__5;
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__5;
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__20;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f___closed__1;
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__3;
lean_object* l_Lean_Expr_bvar___override(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at_____private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__1(lean_object*, lean_object*, size_t, size_t);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__31___closed__0____x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_;
lean_object* l_Lean_Meta_Grind_pushEqCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateExistsDown___closed__0;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_propagateForallPropUp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__2;
static lean_object* l_Lean_Meta_Grind_propagateExistsDown___closed__3;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__12;
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__1;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__6;
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__30;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36___closed__0____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__8;
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__0;
static lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__6;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36___closed__1____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_;
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_activateTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__31___closed__2____x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__3;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__1;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__11;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__9;
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_Grind_simpForall_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__8;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__15;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__41;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__21;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__27;
uint8_t lean_expr_eqv(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__3;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__8;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__10;
static lean_object* l_Lean_Meta_Grind_propagateExistsDown___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__22;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__2;
static lean_object* l_Lean_Meta_Grind_propagateExistsDown___closed__6;
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__0;
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__12;
static lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__5;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__17;
lean_object* l_Lean_Meta_Grind_eqResolution(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__1;
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__31;
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__7;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__18;
lean_object* l_Lean_Meta_Simp_Simprocs_add(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__4;
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__12;
lean_object* l_Lean_Meta_Grind_pushEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__31___closed__4____x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0;
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__1;
lean_object* l_Lean_Meta_Grind_isEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36___closed__6____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__10;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__3;
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__11;
lean_object* lean_expr_lift_loose_bvars(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__13;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateExistsDown___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1____x40_Lean_Meta_Tactic_Grind_ForallProp_115310127____hygCtx___hyg_8_(lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__12;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_propagateForallPropUp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__28;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__9;
static lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__9;
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__13;
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__8;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__23;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateExistsDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqFalseCore(lean_object*, lean_object*);
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__11;
lean_object* l_Lean_mkOr(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__6;
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__35;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addForallSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___Lean_Meta_Grind_simpForall_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__36;
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_Meta_Grind_mkEMatchTheoremUsingSingletonPatterns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__38;
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__0;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__40;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__3;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36___closed__4____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__31____x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_(lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4;
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_mkAnd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addForallSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateExistsDown___closed__7;
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f(lean_object*);
lean_object* l_Lean_Meta_Grind_alreadyInternalized___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__14;
lean_object* l_Lean_Meta_Grind_getSymbolPriorities___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqTrueProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__2;
lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__0;
static lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__10;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__13;
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__9;
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__2;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__26;
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__13;
lean_object* l_Lean_Meta_Grind_isEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36___closed__3____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__31___closed__1____x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__5;
lean_object* l_Lean_Meta_Grind_pushEqFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__4;
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__39;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__24;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__4;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__8;
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateExistsDown___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___Lean_Meta_Grind_simpForall_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f___closed__0;
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_Grind_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__0;
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__0;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__33;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__9;
static lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__7;
LEAN_EXPORT lean_object* l_List_beq___at_____private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateExistsDown___closed__1;
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__11;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__32;
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__11;
static lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__2;
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_Grind_simpForall_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__7;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__31___closed__3____x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_;
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__10;
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_false_of_imp_eq_true", 23, 23);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__2;
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1;
x_3 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__3;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("imp_eq_of_eq_true_right", 23, 23);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__5;
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1;
x_3 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__6;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("imp_eq_of_eq_true_left", 22, 22);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__8;
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1;
x_3 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__9;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("imp_eq_of_eq_false_left", 23, 23);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__11;
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1;
x_3 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__12;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_45; uint8_t x_74; lean_object* x_75; lean_object* x_100; lean_object* x_128; 
x_128 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_3, x_4, x_12);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; uint8_t x_130; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_unbox(x_129);
lean_dec(x_129);
if (x_130 == 0)
{
uint8_t x_131; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_131 = !lean_is_exclusive(x_128);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_128, 0);
lean_dec(x_132);
x_133 = lean_box(0);
lean_ctor_set(x_128, 0, x_133);
return x_128;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_128, 1);
lean_inc(x_134);
lean_dec(x_128);
x_135 = lean_box(0);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_128, 1);
lean_inc(x_137);
lean_dec_ref(x_128);
lean_inc_ref(x_2);
x_138 = l_Lean_Meta_Grind_isEqFalse___redArg(x_2, x_4, x_6, x_10, x_11, x_137);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; uint8_t x_140; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_unbox(x_139);
lean_dec(x_139);
if (x_140 == 0)
{
x_100 = x_138;
goto block_127;
}
else
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_138, 1);
lean_inc(x_141);
lean_dec_ref(x_138);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_3);
x_142 = l_Lean_Meta_isProp(x_3, x_8, x_9, x_10, x_11, x_141);
x_100 = x_142;
goto block_127;
}
}
else
{
x_100 = x_138;
goto block_127;
}
}
}
else
{
uint8_t x_143; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_143 = !lean_is_exclusive(x_128);
if (x_143 == 0)
{
return x_128;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_128, 0);
x_145 = lean_ctor_get(x_128, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_128);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
block_44:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 0);
x_15 = lean_unbox(x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set(x_13, 0, x_18);
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_dec(x_13);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
lean_dec_ref(x_13);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_23 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec_ref(x_23);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_26 = l_Lean_Meta_Grind_mkEqFalseProof(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec_ref(x_26);
x_29 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4;
lean_inc_ref(x_2);
x_30 = l_Lean_mkApp4(x_29, x_2, x_3, x_24, x_27);
x_31 = l_Lean_Meta_Grind_pushEqFalse(x_2, x_30, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_28);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_31;
}
else
{
uint8_t x_32; 
lean_dec(x_24);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_32 = !lean_is_exclusive(x_26);
if (x_32 == 0)
{
return x_26;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_26, 0);
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_26);
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
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_36 = !lean_is_exclusive(x_23);
if (x_36 == 0)
{
return x_23;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_23, 0);
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_23);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_40 = !lean_is_exclusive(x_13);
if (x_40 == 0)
{
return x_13;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_13, 0);
x_42 = lean_ctor_get(x_13, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_13);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
block_73:
{
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_45, 0);
x_47 = lean_unbox(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec_ref(x_45);
lean_inc_ref(x_3);
x_49 = l_Lean_Meta_Grind_isEqFalse___redArg(x_3, x_4, x_6, x_10, x_11, x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_unbox(x_50);
lean_dec(x_50);
if (x_51 == 0)
{
x_13 = x_49;
goto block_44;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec_ref(x_49);
lean_inc_ref(x_1);
x_53 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_4, x_6, x_10, x_11, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_unbox(x_54);
lean_dec(x_54);
if (x_55 == 0)
{
x_13 = x_53;
goto block_44;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec_ref(x_53);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_2);
x_57 = l_Lean_Meta_isProp(x_2, x_8, x_9, x_10, x_11, x_56);
x_13 = x_57;
goto block_44;
}
}
else
{
x_13 = x_53;
goto block_44;
}
}
}
else
{
x_13 = x_49;
goto block_44;
}
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_45, 1);
lean_inc(x_58);
lean_dec_ref(x_45);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_59 = l_Lean_Meta_Grind_mkEqTrueProof(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec_ref(x_59);
x_62 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__7;
x_63 = l_Lean_mkApp3(x_62, x_2, x_3, x_60);
x_64 = l_Lean_Meta_Grind_pushEqTrue(x_1, x_63, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_61);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_64;
}
else
{
uint8_t x_65; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_65 = !lean_is_exclusive(x_59);
if (x_65 == 0)
{
return x_59;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_59, 0);
x_67 = lean_ctor_get(x_59, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_59);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_69 = !lean_is_exclusive(x_45);
if (x_69 == 0)
{
return x_45;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_45, 0);
x_71 = lean_ctor_get(x_45, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_45);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
block_99:
{
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_75, 0);
x_77 = lean_unbox(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_dec_ref(x_75);
lean_inc_ref(x_3);
x_79 = l_Lean_Meta_Grind_isEqTrue___redArg(x_3, x_4, x_6, x_10, x_11, x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_unbox(x_80);
lean_dec(x_80);
if (x_81 == 0)
{
x_45 = x_79;
goto block_73;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec_ref(x_79);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_2);
x_83 = l_Lean_Meta_isProp(x_2, x_8, x_9, x_10, x_11, x_82);
x_45 = x_83;
goto block_73;
}
}
else
{
x_45 = x_79;
goto block_73;
}
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_75, 1);
lean_inc(x_84);
lean_dec_ref(x_75);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_2);
x_85 = l_Lean_Meta_Grind_mkEqTrueProof(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec_ref(x_85);
x_88 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__10;
lean_inc_ref(x_3);
x_89 = l_Lean_mkApp3(x_88, x_2, x_3, x_86);
x_90 = l_Lean_Meta_Grind_pushEqCore(x_1, x_3, x_89, x_74, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_87);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_90;
}
else
{
uint8_t x_91; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_91 = !lean_is_exclusive(x_85);
if (x_91 == 0)
{
return x_85;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_85, 0);
x_93 = lean_ctor_get(x_85, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_85);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_95 = !lean_is_exclusive(x_75);
if (x_95 == 0)
{
return x_75;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_75, 0);
x_97 = lean_ctor_get(x_75, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_75);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
block_127:
{
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_ctor_get(x_100, 0);
x_102 = lean_unbox(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
lean_inc(x_101);
x_103 = lean_ctor_get(x_100, 1);
lean_inc(x_103);
lean_dec_ref(x_100);
lean_inc_ref(x_2);
x_104 = l_Lean_Meta_Grind_isEqTrue___redArg(x_2, x_4, x_6, x_10, x_11, x_103);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; uint8_t x_106; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_unbox(x_105);
lean_dec(x_105);
if (x_106 == 0)
{
uint8_t x_107; 
x_107 = lean_unbox(x_101);
lean_dec(x_101);
x_74 = x_107;
x_75 = x_104;
goto block_99;
}
else
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_108 = lean_ctor_get(x_104, 1);
lean_inc(x_108);
lean_dec_ref(x_104);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_3);
x_109 = l_Lean_Meta_isProp(x_3, x_8, x_9, x_10, x_11, x_108);
x_110 = lean_unbox(x_101);
lean_dec(x_101);
x_74 = x_110;
x_75 = x_109;
goto block_99;
}
}
else
{
uint8_t x_111; 
x_111 = lean_unbox(x_101);
lean_dec(x_101);
x_74 = x_111;
x_75 = x_104;
goto block_99;
}
}
else
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_100, 1);
lean_inc(x_112);
lean_dec_ref(x_100);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc_ref(x_2);
x_113 = l_Lean_Meta_Grind_mkEqFalseProof(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_112);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec_ref(x_113);
x_116 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__13;
x_117 = l_Lean_mkApp3(x_116, x_2, x_3, x_114);
x_118 = l_Lean_Meta_Grind_pushEqTrue(x_1, x_117, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_115);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_118;
}
else
{
uint8_t x_119; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_119 = !lean_is_exclusive(x_113);
if (x_119 == 0)
{
return x_113;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_113, 0);
x_121 = lean_ctor_get(x_113, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_113);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
}
else
{
uint8_t x_123; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_123 = !lean_is_exclusive(x_100);
if (x_123 == 0)
{
return x_100;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_100, 0);
x_125 = lean_ctor_get(x_100, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_100);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 13);
x_6 = l_Lean_checkTraceOption(x_5, x_4, x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_propagateForallPropUp_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(x_1, x_8, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
static double _init_l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1_spec__1(x_2, x_3, x_4, x_5, x_6, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec_ref(x_9);
x_12 = lean_st_ref_take(x_6, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 4);
lean_inc_ref(x_14);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_12, 1);
x_17 = lean_ctor_get(x_12, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_13, 4);
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
lean_object* x_21; double x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_21 = lean_ctor_get(x_14, 0);
x_22 = l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__0;
x_23 = 0;
x_24 = l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__1;
x_25 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set_float(x_25, sizeof(void*)*2, x_22);
lean_ctor_set_float(x_25, sizeof(void*)*2 + 8, x_22);
lean_ctor_set_uint8(x_25, sizeof(void*)*2 + 16, x_23);
x_26 = l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__2;
x_27 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_10);
lean_ctor_set(x_27, 2, x_26);
lean_inc(x_8);
lean_ctor_set(x_12, 1, x_27);
lean_ctor_set(x_12, 0, x_8);
x_28 = l_Lean_PersistentArray_push___redArg(x_21, x_12);
lean_ctor_set(x_14, 0, x_28);
x_29 = lean_st_ref_set(x_6, x_13, x_16);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
x_32 = lean_box(0);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
uint64_t x_36; lean_object* x_37; double x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_36 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_37 = lean_ctor_get(x_14, 0);
lean_inc(x_37);
lean_dec(x_14);
x_38 = l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__0;
x_39 = 0;
x_40 = l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__1;
x_41 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set_float(x_41, sizeof(void*)*2, x_38);
lean_ctor_set_float(x_41, sizeof(void*)*2 + 8, x_38);
lean_ctor_set_uint8(x_41, sizeof(void*)*2 + 16, x_39);
x_42 = l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__2;
x_43 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_10);
lean_ctor_set(x_43, 2, x_42);
lean_inc(x_8);
lean_ctor_set(x_12, 1, x_43);
lean_ctor_set(x_12, 0, x_8);
x_44 = l_Lean_PersistentArray_push___redArg(x_37, x_12);
x_45 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set_uint64(x_45, sizeof(void*)*1, x_36);
lean_ctor_set(x_13, 4, x_45);
x_46 = lean_st_ref_set(x_6, x_13, x_16);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_48 = x_46;
} else {
 lean_dec_ref(x_46);
 x_48 = lean_box(0);
}
x_49 = lean_box(0);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint64_t x_59; lean_object* x_60; lean_object* x_61; double x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_51 = lean_ctor_get(x_13, 0);
x_52 = lean_ctor_get(x_13, 1);
x_53 = lean_ctor_get(x_13, 2);
x_54 = lean_ctor_get(x_13, 3);
x_55 = lean_ctor_get(x_13, 5);
x_56 = lean_ctor_get(x_13, 6);
x_57 = lean_ctor_get(x_13, 7);
x_58 = lean_ctor_get(x_13, 8);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_13);
x_59 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_60 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_60);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_61 = x_14;
} else {
 lean_dec_ref(x_14);
 x_61 = lean_box(0);
}
x_62 = l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__0;
x_63 = 0;
x_64 = l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__1;
x_65 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_65, 0, x_1);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set_float(x_65, sizeof(void*)*2, x_62);
lean_ctor_set_float(x_65, sizeof(void*)*2 + 8, x_62);
lean_ctor_set_uint8(x_65, sizeof(void*)*2 + 16, x_63);
x_66 = l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__2;
x_67 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_10);
lean_ctor_set(x_67, 2, x_66);
lean_inc(x_8);
lean_ctor_set(x_12, 1, x_67);
lean_ctor_set(x_12, 0, x_8);
x_68 = l_Lean_PersistentArray_push___redArg(x_60, x_12);
if (lean_is_scalar(x_61)) {
 x_69 = lean_alloc_ctor(0, 1, 8);
} else {
 x_69 = x_61;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set_uint64(x_69, sizeof(void*)*1, x_59);
x_70 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_70, 0, x_51);
lean_ctor_set(x_70, 1, x_52);
lean_ctor_set(x_70, 2, x_53);
lean_ctor_set(x_70, 3, x_54);
lean_ctor_set(x_70, 4, x_69);
lean_ctor_set(x_70, 5, x_55);
lean_ctor_set(x_70, 6, x_56);
lean_ctor_set(x_70, 7, x_57);
lean_ctor_set(x_70, 8, x_58);
x_71 = lean_st_ref_set(x_6, x_70, x_16);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_73 = x_71;
} else {
 lean_dec_ref(x_71);
 x_73 = lean_box(0);
}
x_74 = lean_box(0);
if (lean_is_scalar(x_73)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_73;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_72);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint64_t x_86; lean_object* x_87; lean_object* x_88; double x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_76 = lean_ctor_get(x_12, 1);
lean_inc(x_76);
lean_dec(x_12);
x_77 = lean_ctor_get(x_13, 0);
lean_inc_ref(x_77);
x_78 = lean_ctor_get(x_13, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_13, 2);
lean_inc_ref(x_79);
x_80 = lean_ctor_get(x_13, 3);
lean_inc_ref(x_80);
x_81 = lean_ctor_get(x_13, 5);
lean_inc_ref(x_81);
x_82 = lean_ctor_get(x_13, 6);
lean_inc_ref(x_82);
x_83 = lean_ctor_get(x_13, 7);
lean_inc_ref(x_83);
x_84 = lean_ctor_get(x_13, 8);
lean_inc_ref(x_84);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 lean_ctor_release(x_13, 2);
 lean_ctor_release(x_13, 3);
 lean_ctor_release(x_13, 4);
 lean_ctor_release(x_13, 5);
 lean_ctor_release(x_13, 6);
 lean_ctor_release(x_13, 7);
 lean_ctor_release(x_13, 8);
 x_85 = x_13;
} else {
 lean_dec_ref(x_13);
 x_85 = lean_box(0);
}
x_86 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_87 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_87);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 x_88 = x_14;
} else {
 lean_dec_ref(x_14);
 x_88 = lean_box(0);
}
x_89 = l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__0;
x_90 = 0;
x_91 = l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__1;
x_92 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_92, 0, x_1);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set_float(x_92, sizeof(void*)*2, x_89);
lean_ctor_set_float(x_92, sizeof(void*)*2 + 8, x_89);
lean_ctor_set_uint8(x_92, sizeof(void*)*2 + 16, x_90);
x_93 = l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__2;
x_94 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_10);
lean_ctor_set(x_94, 2, x_93);
lean_inc(x_8);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_8);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Lean_PersistentArray_push___redArg(x_87, x_95);
if (lean_is_scalar(x_88)) {
 x_97 = lean_alloc_ctor(0, 1, 8);
} else {
 x_97 = x_88;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set_uint64(x_97, sizeof(void*)*1, x_86);
if (lean_is_scalar(x_85)) {
 x_98 = lean_alloc_ctor(0, 9, 0);
} else {
 x_98 = x_85;
}
lean_ctor_set(x_98, 0, x_77);
lean_ctor_set(x_98, 1, x_78);
lean_ctor_set(x_98, 2, x_79);
lean_ctor_set(x_98, 3, x_80);
lean_ctor_set(x_98, 4, x_97);
lean_ctor_set(x_98, 5, x_81);
lean_ctor_set(x_98, 6, x_82);
lean_ctor_set(x_98, 7, x_83);
lean_ctor_set(x_98, 8, x_84);
x_99 = lean_st_ref_set(x_6, x_98, x_76);
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
x_102 = lean_box(0);
if (lean_is_scalar(x_101)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_101;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_100);
return x_103;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(x_1, x_2, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("forall_propagator", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_propagateForallPropUp___closed__0;
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1;
x_3 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_propagateForallPropUp___closed__1;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("forallPropagator", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_propagateForallPropUp___closed__5;
x_2 = l_Lean_Meta_Grind_propagateForallPropUp___closed__4;
x_3 = l_Lean_Meta_Grind_propagateForallPropUp___closed__3;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("q': ", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_propagateForallPropUp___closed__7;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" for", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_propagateForallPropUp___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("isEqTrue, ", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_propagateForallPropUp___closed__12;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_209; lean_object* x_210; uint8_t x_211; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_1, 2);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_40 = l_Lean_Meta_Grind_propagateForallPropUp___closed__6;
x_209 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(x_40, x_8, x_10);
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_unbox(x_210);
lean_dec(x_210);
if (x_211 == 0)
{
lean_object* x_212; 
x_212 = lean_ctor_get(x_209, 1);
lean_inc(x_212);
lean_dec_ref(x_209);
x_147 = x_2;
x_148 = x_3;
x_149 = x_4;
x_150 = x_5;
x_151 = x_6;
x_152 = x_7;
x_153 = x_8;
x_154 = x_9;
x_155 = x_212;
goto block_208;
}
else
{
uint8_t x_213; 
x_213 = !lean_is_exclusive(x_209);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_214 = lean_ctor_get(x_209, 1);
x_215 = lean_ctor_get(x_209, 0);
lean_dec(x_215);
x_216 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_214);
if (lean_obj_tag(x_216) == 0)
{
uint8_t x_217; 
x_217 = !lean_is_exclusive(x_216);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_218 = lean_ctor_get(x_216, 1);
x_219 = lean_ctor_get(x_216, 0);
lean_dec(x_219);
x_220 = l_Lean_Meta_Grind_propagateForallPropUp___closed__11;
lean_inc_ref(x_1);
x_221 = l_Lean_MessageData_ofExpr(x_1);
lean_ctor_set_tag(x_216, 7);
lean_ctor_set(x_216, 1, x_221);
lean_ctor_set(x_216, 0, x_220);
lean_ctor_set_tag(x_209, 7);
lean_ctor_set(x_209, 1, x_220);
lean_ctor_set(x_209, 0, x_216);
x_222 = l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(x_40, x_209, x_6, x_7, x_8, x_9, x_218);
x_223 = lean_ctor_get(x_222, 1);
lean_inc(x_223);
lean_dec_ref(x_222);
x_147 = x_2;
x_148 = x_3;
x_149 = x_4;
x_150 = x_5;
x_151 = x_6;
x_152 = x_7;
x_153 = x_8;
x_154 = x_9;
x_155 = x_223;
goto block_208;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_224 = lean_ctor_get(x_216, 1);
lean_inc(x_224);
lean_dec(x_216);
x_225 = l_Lean_Meta_Grind_propagateForallPropUp___closed__11;
lean_inc_ref(x_1);
x_226 = l_Lean_MessageData_ofExpr(x_1);
x_227 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
lean_ctor_set_tag(x_209, 7);
lean_ctor_set(x_209, 1, x_225);
lean_ctor_set(x_209, 0, x_227);
x_228 = l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(x_40, x_209, x_6, x_7, x_8, x_9, x_224);
x_229 = lean_ctor_get(x_228, 1);
lean_inc(x_229);
lean_dec_ref(x_228);
x_147 = x_2;
x_148 = x_3;
x_149 = x_4;
x_150 = x_5;
x_151 = x_6;
x_152 = x_7;
x_153 = x_8;
x_154 = x_9;
x_155 = x_229;
goto block_208;
}
}
else
{
lean_free_object(x_209);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_216;
}
}
else
{
lean_object* x_230; lean_object* x_231; 
x_230 = lean_ctor_get(x_209, 1);
lean_inc(x_230);
lean_dec(x_209);
x_231 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_230);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_232 = lean_ctor_get(x_231, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_233 = x_231;
} else {
 lean_dec_ref(x_231);
 x_233 = lean_box(0);
}
x_234 = l_Lean_Meta_Grind_propagateForallPropUp___closed__11;
lean_inc_ref(x_1);
x_235 = l_Lean_MessageData_ofExpr(x_1);
if (lean_is_scalar(x_233)) {
 x_236 = lean_alloc_ctor(7, 2, 0);
} else {
 x_236 = x_233;
 lean_ctor_set_tag(x_236, 7);
}
lean_ctor_set(x_236, 0, x_234);
lean_ctor_set(x_236, 1, x_235);
x_237 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_237, 0, x_236);
lean_ctor_set(x_237, 1, x_234);
x_238 = l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(x_40, x_237, x_6, x_7, x_8, x_9, x_232);
x_239 = lean_ctor_get(x_238, 1);
lean_inc(x_239);
lean_dec_ref(x_238);
x_147 = x_2;
x_148 = x_3;
x_149 = x_4;
x_150 = x_5;
x_151 = x_6;
x_152 = x_7;
x_153 = x_8;
x_154 = x_9;
x_155 = x_239;
goto block_208;
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_231;
}
}
}
block_39:
{
lean_object* x_29; 
lean_inc(x_27);
lean_inc_ref(x_26);
lean_inc(x_25);
lean_inc_ref(x_24);
x_29 = l_Lean_Meta_Simp_Result_getProof(x_16, x_24, x_25, x_26, x_27, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec_ref(x_29);
x_32 = l_Lean_Meta_Grind_propagateForallPropUp___closed__2;
lean_inc_ref(x_19);
lean_inc_ref(x_12);
x_33 = l_Lean_mkApp5(x_32, x_12, x_15, x_19, x_18, x_30);
x_34 = l_Lean_Meta_Grind_pushEqCore(x_1, x_19, x_33, x_17, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_31);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_15);
lean_dec_ref(x_1);
x_35 = !lean_is_exclusive(x_29);
if (x_35 == 0)
{
return x_29;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_29, 0);
x_37 = lean_ctor_get(x_29, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_29);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
block_146:
{
lean_object* x_51; 
lean_inc(x_49);
lean_inc_ref(x_48);
lean_inc(x_47);
lean_inc_ref(x_46);
lean_inc(x_45);
lean_inc_ref(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc_ref(x_12);
x_51 = l_Lean_Meta_Grind_mkEqTrueProof(x_12, x_42, x_43, x_44, x_45, x_46, x_47, x_48, x_49, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec_ref(x_51);
lean_inc(x_52);
lean_inc_ref(x_12);
x_54 = l_Lean_Meta_mkOfEqTrueCore(x_12, x_52);
x_55 = lean_expr_instantiate1(x_13, x_54);
lean_dec_ref(x_54);
lean_inc(x_49);
lean_inc_ref(x_48);
lean_inc(x_47);
lean_inc_ref(x_46);
lean_inc(x_45);
lean_inc_ref(x_44);
lean_inc(x_43);
lean_inc(x_42);
x_56 = l_Lean_Meta_Grind_preprocess(x_55, x_42, x_43, x_44, x_45, x_46, x_47, x_48, x_49, x_53);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec_ref(x_56);
x_59 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_42, x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec_ref(x_59);
x_62 = lean_ctor_get(x_57, 0);
lean_inc_ref(x_62);
x_63 = lean_box(0);
lean_inc(x_49);
lean_inc_ref(x_48);
lean_inc(x_47);
lean_inc_ref(x_46);
lean_inc(x_45);
lean_inc_ref(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc_ref(x_62);
x_64 = lean_grind_internalize(x_62, x_60, x_63, x_42, x_43, x_44, x_45, x_46, x_47, x_48, x_49, x_61);
if (lean_obj_tag(x_64) == 0)
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_66 = lean_ctor_get(x_64, 1);
x_67 = lean_ctor_get(x_64, 0);
lean_dec(x_67);
x_68 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(x_40, x_48, x_66);
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_70 = lean_ctor_get(x_68, 0);
x_71 = lean_ctor_get(x_68, 1);
lean_inc_ref(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
x_72 = l_Lean_mkLambda(x_11, x_14, x_12, x_13);
x_73 = lean_unbox(x_70);
lean_dec(x_70);
if (x_73 == 0)
{
lean_free_object(x_68);
lean_free_object(x_64);
x_15 = x_72;
x_16 = x_57;
x_17 = x_41;
x_18 = x_52;
x_19 = x_62;
x_20 = x_42;
x_21 = x_43;
x_22 = x_44;
x_23 = x_45;
x_24 = x_46;
x_25 = x_47;
x_26 = x_48;
x_27 = x_49;
x_28 = x_71;
goto block_39;
}
else
{
lean_object* x_74; 
x_74 = l_Lean_Meta_Grind_updateLastTag(x_42, x_43, x_44, x_45, x_46, x_47, x_48, x_49, x_71);
if (lean_obj_tag(x_74) == 0)
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_76 = lean_ctor_get(x_74, 1);
x_77 = lean_ctor_get(x_74, 0);
lean_dec(x_77);
x_78 = l_Lean_Meta_Grind_propagateForallPropUp___closed__8;
lean_inc_ref(x_62);
x_79 = l_Lean_MessageData_ofExpr(x_62);
lean_ctor_set_tag(x_74, 7);
lean_ctor_set(x_74, 1, x_79);
lean_ctor_set(x_74, 0, x_78);
x_80 = l_Lean_Meta_Grind_propagateForallPropUp___closed__10;
lean_ctor_set_tag(x_68, 7);
lean_ctor_set(x_68, 1, x_80);
lean_ctor_set(x_68, 0, x_74);
lean_inc_ref(x_1);
x_81 = l_Lean_indentExpr(x_1);
lean_ctor_set_tag(x_64, 7);
lean_ctor_set(x_64, 1, x_81);
lean_ctor_set(x_64, 0, x_68);
x_82 = l_Lean_Meta_Grind_propagateForallPropUp___closed__11;
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_64);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(x_40, x_83, x_46, x_47, x_48, x_49, x_76);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec_ref(x_84);
x_15 = x_72;
x_16 = x_57;
x_17 = x_41;
x_18 = x_52;
x_19 = x_62;
x_20 = x_42;
x_21 = x_43;
x_22 = x_44;
x_23 = x_45;
x_24 = x_46;
x_25 = x_47;
x_26 = x_48;
x_27 = x_49;
x_28 = x_85;
goto block_39;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_86 = lean_ctor_get(x_74, 1);
lean_inc(x_86);
lean_dec(x_74);
x_87 = l_Lean_Meta_Grind_propagateForallPropUp___closed__8;
lean_inc_ref(x_62);
x_88 = l_Lean_MessageData_ofExpr(x_62);
x_89 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = l_Lean_Meta_Grind_propagateForallPropUp___closed__10;
lean_ctor_set_tag(x_68, 7);
lean_ctor_set(x_68, 1, x_90);
lean_ctor_set(x_68, 0, x_89);
lean_inc_ref(x_1);
x_91 = l_Lean_indentExpr(x_1);
lean_ctor_set_tag(x_64, 7);
lean_ctor_set(x_64, 1, x_91);
lean_ctor_set(x_64, 0, x_68);
x_92 = l_Lean_Meta_Grind_propagateForallPropUp___closed__11;
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_64);
lean_ctor_set(x_93, 1, x_92);
x_94 = l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(x_40, x_93, x_46, x_47, x_48, x_49, x_86);
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec_ref(x_94);
x_15 = x_72;
x_16 = x_57;
x_17 = x_41;
x_18 = x_52;
x_19 = x_62;
x_20 = x_42;
x_21 = x_43;
x_22 = x_44;
x_23 = x_45;
x_24 = x_46;
x_25 = x_47;
x_26 = x_48;
x_27 = x_49;
x_28 = x_95;
goto block_39;
}
}
else
{
lean_dec_ref(x_72);
lean_free_object(x_68);
lean_free_object(x_64);
lean_dec_ref(x_62);
lean_dec(x_57);
lean_dec(x_52);
lean_dec(x_49);
lean_dec_ref(x_48);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec_ref(x_1);
return x_74;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_96 = lean_ctor_get(x_68, 0);
x_97 = lean_ctor_get(x_68, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_68);
lean_inc_ref(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
x_98 = l_Lean_mkLambda(x_11, x_14, x_12, x_13);
x_99 = lean_unbox(x_96);
lean_dec(x_96);
if (x_99 == 0)
{
lean_free_object(x_64);
x_15 = x_98;
x_16 = x_57;
x_17 = x_41;
x_18 = x_52;
x_19 = x_62;
x_20 = x_42;
x_21 = x_43;
x_22 = x_44;
x_23 = x_45;
x_24 = x_46;
x_25 = x_47;
x_26 = x_48;
x_27 = x_49;
x_28 = x_97;
goto block_39;
}
else
{
lean_object* x_100; 
x_100 = l_Lean_Meta_Grind_updateLastTag(x_42, x_43, x_44, x_45, x_46, x_47, x_48, x_49, x_97);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_102 = x_100;
} else {
 lean_dec_ref(x_100);
 x_102 = lean_box(0);
}
x_103 = l_Lean_Meta_Grind_propagateForallPropUp___closed__8;
lean_inc_ref(x_62);
x_104 = l_Lean_MessageData_ofExpr(x_62);
if (lean_is_scalar(x_102)) {
 x_105 = lean_alloc_ctor(7, 2, 0);
} else {
 x_105 = x_102;
 lean_ctor_set_tag(x_105, 7);
}
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_106 = l_Lean_Meta_Grind_propagateForallPropUp___closed__10;
x_107 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
lean_inc_ref(x_1);
x_108 = l_Lean_indentExpr(x_1);
lean_ctor_set_tag(x_64, 7);
lean_ctor_set(x_64, 1, x_108);
lean_ctor_set(x_64, 0, x_107);
x_109 = l_Lean_Meta_Grind_propagateForallPropUp___closed__11;
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_64);
lean_ctor_set(x_110, 1, x_109);
x_111 = l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(x_40, x_110, x_46, x_47, x_48, x_49, x_101);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec_ref(x_111);
x_15 = x_98;
x_16 = x_57;
x_17 = x_41;
x_18 = x_52;
x_19 = x_62;
x_20 = x_42;
x_21 = x_43;
x_22 = x_44;
x_23 = x_45;
x_24 = x_46;
x_25 = x_47;
x_26 = x_48;
x_27 = x_49;
x_28 = x_112;
goto block_39;
}
else
{
lean_dec_ref(x_98);
lean_free_object(x_64);
lean_dec_ref(x_62);
lean_dec(x_57);
lean_dec(x_52);
lean_dec(x_49);
lean_dec_ref(x_48);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec_ref(x_1);
return x_100;
}
}
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_113 = lean_ctor_get(x_64, 1);
lean_inc(x_113);
lean_dec(x_64);
x_114 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(x_40, x_48, x_113);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_117 = x_114;
} else {
 lean_dec_ref(x_114);
 x_117 = lean_box(0);
}
lean_inc_ref(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
x_118 = l_Lean_mkLambda(x_11, x_14, x_12, x_13);
x_119 = lean_unbox(x_115);
lean_dec(x_115);
if (x_119 == 0)
{
lean_dec(x_117);
x_15 = x_118;
x_16 = x_57;
x_17 = x_41;
x_18 = x_52;
x_19 = x_62;
x_20 = x_42;
x_21 = x_43;
x_22 = x_44;
x_23 = x_45;
x_24 = x_46;
x_25 = x_47;
x_26 = x_48;
x_27 = x_49;
x_28 = x_116;
goto block_39;
}
else
{
lean_object* x_120; 
x_120 = l_Lean_Meta_Grind_updateLastTag(x_42, x_43, x_44, x_45, x_46, x_47, x_48, x_49, x_116);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_122 = x_120;
} else {
 lean_dec_ref(x_120);
 x_122 = lean_box(0);
}
x_123 = l_Lean_Meta_Grind_propagateForallPropUp___closed__8;
lean_inc_ref(x_62);
x_124 = l_Lean_MessageData_ofExpr(x_62);
if (lean_is_scalar(x_122)) {
 x_125 = lean_alloc_ctor(7, 2, 0);
} else {
 x_125 = x_122;
 lean_ctor_set_tag(x_125, 7);
}
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
x_126 = l_Lean_Meta_Grind_propagateForallPropUp___closed__10;
if (lean_is_scalar(x_117)) {
 x_127 = lean_alloc_ctor(7, 2, 0);
} else {
 x_127 = x_117;
 lean_ctor_set_tag(x_127, 7);
}
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
lean_inc_ref(x_1);
x_128 = l_Lean_indentExpr(x_1);
x_129 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
x_130 = l_Lean_Meta_Grind_propagateForallPropUp___closed__11;
x_131 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
x_132 = l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(x_40, x_131, x_46, x_47, x_48, x_49, x_121);
x_133 = lean_ctor_get(x_132, 1);
lean_inc(x_133);
lean_dec_ref(x_132);
x_15 = x_118;
x_16 = x_57;
x_17 = x_41;
x_18 = x_52;
x_19 = x_62;
x_20 = x_42;
x_21 = x_43;
x_22 = x_44;
x_23 = x_45;
x_24 = x_46;
x_25 = x_47;
x_26 = x_48;
x_27 = x_49;
x_28 = x_133;
goto block_39;
}
else
{
lean_dec_ref(x_118);
lean_dec(x_117);
lean_dec_ref(x_62);
lean_dec(x_57);
lean_dec(x_52);
lean_dec(x_49);
lean_dec_ref(x_48);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec_ref(x_1);
return x_120;
}
}
}
}
else
{
lean_dec_ref(x_62);
lean_dec(x_57);
lean_dec(x_52);
lean_dec(x_49);
lean_dec_ref(x_48);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec_ref(x_1);
return x_64;
}
}
else
{
uint8_t x_134; 
lean_dec(x_57);
lean_dec(x_52);
lean_dec(x_49);
lean_dec_ref(x_48);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec_ref(x_1);
x_134 = !lean_is_exclusive(x_59);
if (x_134 == 0)
{
return x_59;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_59, 0);
x_136 = lean_ctor_get(x_59, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_59);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
}
else
{
uint8_t x_138; 
lean_dec(x_52);
lean_dec(x_49);
lean_dec_ref(x_48);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec_ref(x_1);
x_138 = !lean_is_exclusive(x_56);
if (x_138 == 0)
{
return x_56;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_56, 0);
x_140 = lean_ctor_get(x_56, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_56);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
else
{
uint8_t x_142; 
lean_dec(x_49);
lean_dec_ref(x_48);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec_ref(x_1);
x_142 = !lean_is_exclusive(x_51);
if (x_142 == 0)
{
return x_51;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_51, 0);
x_144 = lean_ctor_get(x_51, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_51);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
block_208:
{
uint8_t x_156; 
x_156 = l_Lean_Expr_hasLooseBVars(x_13);
if (x_156 == 0)
{
lean_object* x_157; 
lean_inc_ref(x_13);
lean_inc_ref(x_12);
x_157 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp(x_1, x_12, x_13, x_147, x_148, x_149, x_150, x_151, x_152, x_153, x_154, x_155);
return x_157;
}
else
{
lean_object* x_158; 
lean_inc_ref(x_12);
x_158 = l_Lean_Meta_Grind_isEqTrue___redArg(x_12, x_147, x_149, x_153, x_154, x_155);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; uint8_t x_160; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_unbox(x_159);
lean_dec(x_159);
if (x_160 == 0)
{
uint8_t x_161; 
lean_dec(x_154);
lean_dec_ref(x_153);
lean_dec(x_152);
lean_dec_ref(x_151);
lean_dec(x_150);
lean_dec_ref(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec_ref(x_1);
x_161 = !lean_is_exclusive(x_158);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_158, 0);
lean_dec(x_162);
x_163 = lean_box(0);
lean_ctor_set(x_158, 0, x_163);
return x_158;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_158, 1);
lean_inc(x_164);
lean_dec(x_158);
x_165 = lean_box(0);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_164);
return x_166;
}
}
else
{
lean_object* x_167; lean_object* x_168; uint8_t x_169; 
x_167 = lean_ctor_get(x_158, 1);
lean_inc(x_167);
lean_dec_ref(x_158);
x_168 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(x_40, x_153, x_167);
x_169 = !lean_is_exclusive(x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; uint8_t x_172; uint8_t x_173; 
x_170 = lean_ctor_get(x_168, 0);
x_171 = lean_ctor_get(x_168, 1);
x_172 = 0;
x_173 = lean_unbox(x_170);
lean_dec(x_170);
if (x_173 == 0)
{
lean_free_object(x_168);
x_41 = x_172;
x_42 = x_147;
x_43 = x_148;
x_44 = x_149;
x_45 = x_150;
x_46 = x_151;
x_47 = x_152;
x_48 = x_153;
x_49 = x_154;
x_50 = x_171;
goto block_146;
}
else
{
lean_object* x_174; 
x_174 = l_Lean_Meta_Grind_updateLastTag(x_147, x_148, x_149, x_150, x_151, x_152, x_153, x_154, x_171);
if (lean_obj_tag(x_174) == 0)
{
uint8_t x_175; 
x_175 = !lean_is_exclusive(x_174);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_176 = lean_ctor_get(x_174, 1);
x_177 = lean_ctor_get(x_174, 0);
lean_dec(x_177);
x_178 = l_Lean_Meta_Grind_propagateForallPropUp___closed__13;
lean_inc_ref(x_1);
x_179 = l_Lean_MessageData_ofExpr(x_1);
lean_ctor_set_tag(x_174, 7);
lean_ctor_set(x_174, 1, x_179);
lean_ctor_set(x_174, 0, x_178);
x_180 = l_Lean_Meta_Grind_propagateForallPropUp___closed__11;
lean_ctor_set_tag(x_168, 7);
lean_ctor_set(x_168, 1, x_180);
lean_ctor_set(x_168, 0, x_174);
x_181 = l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(x_40, x_168, x_151, x_152, x_153, x_154, x_176);
x_182 = lean_ctor_get(x_181, 1);
lean_inc(x_182);
lean_dec_ref(x_181);
x_41 = x_172;
x_42 = x_147;
x_43 = x_148;
x_44 = x_149;
x_45 = x_150;
x_46 = x_151;
x_47 = x_152;
x_48 = x_153;
x_49 = x_154;
x_50 = x_182;
goto block_146;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_183 = lean_ctor_get(x_174, 1);
lean_inc(x_183);
lean_dec(x_174);
x_184 = l_Lean_Meta_Grind_propagateForallPropUp___closed__13;
lean_inc_ref(x_1);
x_185 = l_Lean_MessageData_ofExpr(x_1);
x_186 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
x_187 = l_Lean_Meta_Grind_propagateForallPropUp___closed__11;
lean_ctor_set_tag(x_168, 7);
lean_ctor_set(x_168, 1, x_187);
lean_ctor_set(x_168, 0, x_186);
x_188 = l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(x_40, x_168, x_151, x_152, x_153, x_154, x_183);
x_189 = lean_ctor_get(x_188, 1);
lean_inc(x_189);
lean_dec_ref(x_188);
x_41 = x_172;
x_42 = x_147;
x_43 = x_148;
x_44 = x_149;
x_45 = x_150;
x_46 = x_151;
x_47 = x_152;
x_48 = x_153;
x_49 = x_154;
x_50 = x_189;
goto block_146;
}
}
else
{
lean_free_object(x_168);
lean_dec(x_154);
lean_dec_ref(x_153);
lean_dec(x_152);
lean_dec_ref(x_151);
lean_dec(x_150);
lean_dec_ref(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec_ref(x_1);
return x_174;
}
}
}
else
{
lean_object* x_190; lean_object* x_191; uint8_t x_192; uint8_t x_193; 
x_190 = lean_ctor_get(x_168, 0);
x_191 = lean_ctor_get(x_168, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_168);
x_192 = 0;
x_193 = lean_unbox(x_190);
lean_dec(x_190);
if (x_193 == 0)
{
x_41 = x_192;
x_42 = x_147;
x_43 = x_148;
x_44 = x_149;
x_45 = x_150;
x_46 = x_151;
x_47 = x_152;
x_48 = x_153;
x_49 = x_154;
x_50 = x_191;
goto block_146;
}
else
{
lean_object* x_194; 
x_194 = l_Lean_Meta_Grind_updateLastTag(x_147, x_148, x_149, x_150, x_151, x_152, x_153, x_154, x_191);
if (lean_obj_tag(x_194) == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_195 = lean_ctor_get(x_194, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 x_196 = x_194;
} else {
 lean_dec_ref(x_194);
 x_196 = lean_box(0);
}
x_197 = l_Lean_Meta_Grind_propagateForallPropUp___closed__13;
lean_inc_ref(x_1);
x_198 = l_Lean_MessageData_ofExpr(x_1);
if (lean_is_scalar(x_196)) {
 x_199 = lean_alloc_ctor(7, 2, 0);
} else {
 x_199 = x_196;
 lean_ctor_set_tag(x_199, 7);
}
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
x_200 = l_Lean_Meta_Grind_propagateForallPropUp___closed__11;
x_201 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
x_202 = l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(x_40, x_201, x_151, x_152, x_153, x_154, x_195);
x_203 = lean_ctor_get(x_202, 1);
lean_inc(x_203);
lean_dec_ref(x_202);
x_41 = x_192;
x_42 = x_147;
x_43 = x_148;
x_44 = x_149;
x_45 = x_150;
x_46 = x_151;
x_47 = x_152;
x_48 = x_153;
x_49 = x_154;
x_50 = x_203;
goto block_146;
}
else
{
lean_dec(x_154);
lean_dec_ref(x_153);
lean_dec(x_152);
lean_dec_ref(x_151);
lean_dec(x_150);
lean_dec_ref(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec_ref(x_1);
return x_194;
}
}
}
}
}
else
{
uint8_t x_204; 
lean_dec(x_154);
lean_dec_ref(x_153);
lean_dec(x_152);
lean_dec_ref(x_151);
lean_dec(x_150);
lean_dec_ref(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec_ref(x_1);
x_204 = !lean_is_exclusive(x_158);
if (x_204 == 0)
{
return x_158;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_158, 0);
x_206 = lean_ctor_get(x_158, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_158);
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
return x_207;
}
}
}
}
}
else
{
lean_object* x_240; lean_object* x_241; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_240 = lean_box(0);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_240);
lean_ctor_set(x_241, 1, x_10);
return x_241;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_propagateForallPropUp_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_propagateForallPropUp_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_true", 7, 7);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = l_Lean_Expr_isApp(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec_ref(x_2);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
lean_inc_ref(x_2);
x_5 = l_Lean_Expr_appFnCleanup___redArg(x_2);
x_6 = l_Lean_Expr_isApp(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec_ref(x_5);
lean_dec_ref(x_2);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Lean_Expr_appFnCleanup___redArg(x_5);
x_9 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f___closed__1;
x_10 = l_Lean_Expr_isConstOf(x_8, x_9);
lean_dec_ref(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec_ref(x_2);
x_11 = lean_box(0);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_12);
lean_dec_ref(x_2);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec_ref(x_12);
x_15 = lean_box(0);
return x_15;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___closed__0;
x_11 = 0;
x_12 = l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(x_1, x_10, x_2, x_3, x_4, x_11, x_11, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_23; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
x_23 = l_Lean_Exception_isInterrupt(x_13);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = l_Lean_Exception_isRuntime(x_13);
lean_dec(x_13);
x_15 = x_24;
goto block_22;
}
else
{
lean_dec(x_13);
x_15 = x_23;
goto block_22;
}
block_22:
{
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_12);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 1);
lean_dec(x_17);
x_18 = lean_ctor_get(x_12, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set_tag(x_12, 0);
lean_ctor_set(x_12, 0, x_19);
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_12);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_14);
return x_21;
}
}
else
{
lean_dec(x_14);
return x_12;
}
}
}
}
}
LEAN_EXPORT uint8_t l_List_beq___at_____private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = lean_expr_eqv(x_6, x_8);
if (x_10 == 0)
{
return x_10;
}
else
{
x_1 = x_7;
x_2 = x_9;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at_____private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 3);
x_7 = lean_array_uget(x_2, x_3);
x_8 = l_List_beq___at_____private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__0(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
size_t x_9; size_t x_10; 
x_9 = 1;
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
else
{
return x_8;
}
}
else
{
uint8_t x_12; 
x_12 = 0;
return x_12;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_4);
x_6 = 1;
return x_6;
}
else
{
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
size_t x_7; size_t x_8; uint8_t x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at_____private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__1(x_2, x_1, x_7, x_8);
if (x_9 == 0)
{
return x_5;
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at_____private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_beq___at_____private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at_____private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at_____private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__1(x_1, x_2, x_5, x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; uint8_t x_21; 
x_21 = lean_usize_dec_lt(x_4, x_3);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_5);
lean_ctor_set(x_22, 1, x_14);
return x_22;
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_array_uget(x_2, x_4);
x_24 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(x_5, x_23);
if (x_24 == 0)
{
lean_dec_ref(x_23);
x_15 = x_5;
x_16 = x_14;
goto block_20;
}
else
{
lean_object* x_25; 
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
lean_inc_ref(x_23);
x_25 = l_Lean_Meta_Grind_activateTheorem(x_23, x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = lean_ctor_get(x_23, 3);
lean_inc(x_27);
lean_dec_ref(x_23);
x_28 = lean_array_push(x_5, x_27);
x_15 = x_28;
x_16 = x_26;
goto block_20;
}
else
{
uint8_t x_29; 
lean_dec_ref(x_23);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_25);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
block_20:
{
size_t x_17; size_t x_18; 
x_17 = 1;
x_18 = lean_usize_add(x_4, x_17);
x_4 = x_18;
x_5 = x_15;
x_14 = x_16;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("failed to create E-match local theorem for", 42, 42);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__0;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("local", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_140; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_140 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_210; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec_ref(x_140);
lean_inc(x_141);
x_210 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f(x_141);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; uint8_t x_215; 
x_211 = lean_st_ref_take(x_2, x_142);
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_212, 12);
lean_inc_ref(x_213);
x_214 = lean_ctor_get(x_211, 1);
lean_inc(x_214);
lean_dec_ref(x_211);
x_215 = !lean_is_exclusive(x_212);
if (x_215 == 0)
{
lean_object* x_216; uint8_t x_217; 
x_216 = lean_ctor_get(x_212, 12);
lean_dec(x_216);
x_217 = !lean_is_exclusive(x_213);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_218 = lean_ctor_get(x_213, 7);
x_219 = lean_unsigned_to_nat(1u);
x_220 = lean_nat_add(x_218, x_219);
lean_ctor_set(x_213, 7, x_220);
x_221 = lean_st_ref_set(x_2, x_212, x_214);
x_222 = lean_ctor_get(x_221, 1);
lean_inc(x_222);
lean_dec_ref(x_221);
x_223 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__3;
x_224 = lean_name_append_index_after(x_223, x_218);
x_225 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_225, 0, x_224);
x_143 = x_225;
x_144 = x_2;
x_145 = x_3;
x_146 = x_4;
x_147 = x_5;
x_148 = x_6;
x_149 = x_7;
x_150 = x_8;
x_151 = x_9;
x_152 = x_222;
goto block_209;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_226 = lean_ctor_get(x_213, 0);
x_227 = lean_ctor_get(x_213, 1);
x_228 = lean_ctor_get(x_213, 2);
x_229 = lean_ctor_get(x_213, 3);
x_230 = lean_ctor_get(x_213, 4);
x_231 = lean_ctor_get(x_213, 5);
x_232 = lean_ctor_get(x_213, 6);
x_233 = lean_ctor_get(x_213, 7);
x_234 = lean_ctor_get(x_213, 8);
lean_inc(x_234);
lean_inc(x_233);
lean_inc(x_232);
lean_inc(x_231);
lean_inc(x_230);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
lean_dec(x_213);
x_235 = lean_unsigned_to_nat(1u);
x_236 = lean_nat_add(x_233, x_235);
x_237 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_237, 0, x_226);
lean_ctor_set(x_237, 1, x_227);
lean_ctor_set(x_237, 2, x_228);
lean_ctor_set(x_237, 3, x_229);
lean_ctor_set(x_237, 4, x_230);
lean_ctor_set(x_237, 5, x_231);
lean_ctor_set(x_237, 6, x_232);
lean_ctor_set(x_237, 7, x_236);
lean_ctor_set(x_237, 8, x_234);
lean_ctor_set(x_212, 12, x_237);
x_238 = lean_st_ref_set(x_2, x_212, x_214);
x_239 = lean_ctor_get(x_238, 1);
lean_inc(x_239);
lean_dec_ref(x_238);
x_240 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__3;
x_241 = lean_name_append_index_after(x_240, x_233);
x_242 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_242, 0, x_241);
x_143 = x_242;
x_144 = x_2;
x_145 = x_3;
x_146 = x_4;
x_147 = x_5;
x_148 = x_6;
x_149 = x_7;
x_150 = x_8;
x_151 = x_9;
x_152 = x_239;
goto block_209;
}
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_243 = lean_ctor_get(x_212, 0);
x_244 = lean_ctor_get(x_212, 1);
x_245 = lean_ctor_get(x_212, 2);
x_246 = lean_ctor_get(x_212, 3);
x_247 = lean_ctor_get(x_212, 4);
x_248 = lean_ctor_get(x_212, 5);
x_249 = lean_ctor_get(x_212, 6);
x_250 = lean_ctor_get(x_212, 7);
x_251 = lean_ctor_get_uint8(x_212, sizeof(void*)*17);
x_252 = lean_ctor_get(x_212, 8);
x_253 = lean_ctor_get(x_212, 9);
x_254 = lean_ctor_get(x_212, 10);
x_255 = lean_ctor_get(x_212, 11);
x_256 = lean_ctor_get(x_212, 13);
x_257 = lean_ctor_get(x_212, 14);
x_258 = lean_ctor_get(x_212, 15);
x_259 = lean_ctor_get(x_212, 16);
lean_inc(x_259);
lean_inc(x_258);
lean_inc(x_257);
lean_inc(x_256);
lean_inc(x_255);
lean_inc(x_254);
lean_inc(x_253);
lean_inc(x_252);
lean_inc(x_250);
lean_inc(x_249);
lean_inc(x_248);
lean_inc(x_247);
lean_inc(x_246);
lean_inc(x_245);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_212);
x_260 = lean_ctor_get(x_213, 0);
lean_inc_ref(x_260);
x_261 = lean_ctor_get(x_213, 1);
lean_inc(x_261);
x_262 = lean_ctor_get(x_213, 2);
lean_inc_ref(x_262);
x_263 = lean_ctor_get(x_213, 3);
lean_inc_ref(x_263);
x_264 = lean_ctor_get(x_213, 4);
lean_inc(x_264);
x_265 = lean_ctor_get(x_213, 5);
lean_inc(x_265);
x_266 = lean_ctor_get(x_213, 6);
lean_inc_ref(x_266);
x_267 = lean_ctor_get(x_213, 7);
lean_inc(x_267);
x_268 = lean_ctor_get(x_213, 8);
lean_inc_ref(x_268);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 lean_ctor_release(x_213, 2);
 lean_ctor_release(x_213, 3);
 lean_ctor_release(x_213, 4);
 lean_ctor_release(x_213, 5);
 lean_ctor_release(x_213, 6);
 lean_ctor_release(x_213, 7);
 lean_ctor_release(x_213, 8);
 x_269 = x_213;
} else {
 lean_dec_ref(x_213);
 x_269 = lean_box(0);
}
x_270 = lean_unsigned_to_nat(1u);
x_271 = lean_nat_add(x_267, x_270);
if (lean_is_scalar(x_269)) {
 x_272 = lean_alloc_ctor(0, 9, 0);
} else {
 x_272 = x_269;
}
lean_ctor_set(x_272, 0, x_260);
lean_ctor_set(x_272, 1, x_261);
lean_ctor_set(x_272, 2, x_262);
lean_ctor_set(x_272, 3, x_263);
lean_ctor_set(x_272, 4, x_264);
lean_ctor_set(x_272, 5, x_265);
lean_ctor_set(x_272, 6, x_266);
lean_ctor_set(x_272, 7, x_271);
lean_ctor_set(x_272, 8, x_268);
x_273 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_273, 0, x_243);
lean_ctor_set(x_273, 1, x_244);
lean_ctor_set(x_273, 2, x_245);
lean_ctor_set(x_273, 3, x_246);
lean_ctor_set(x_273, 4, x_247);
lean_ctor_set(x_273, 5, x_248);
lean_ctor_set(x_273, 6, x_249);
lean_ctor_set(x_273, 7, x_250);
lean_ctor_set(x_273, 8, x_252);
lean_ctor_set(x_273, 9, x_253);
lean_ctor_set(x_273, 10, x_254);
lean_ctor_set(x_273, 11, x_255);
lean_ctor_set(x_273, 12, x_272);
lean_ctor_set(x_273, 13, x_256);
lean_ctor_set(x_273, 14, x_257);
lean_ctor_set(x_273, 15, x_258);
lean_ctor_set(x_273, 16, x_259);
lean_ctor_set_uint8(x_273, sizeof(void*)*17, x_251);
x_274 = lean_st_ref_set(x_2, x_273, x_214);
x_275 = lean_ctor_get(x_274, 1);
lean_inc(x_275);
lean_dec_ref(x_274);
x_276 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__3;
x_277 = lean_name_append_index_after(x_276, x_267);
x_278 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_278, 0, x_277);
x_143 = x_278;
x_144 = x_2;
x_145 = x_3;
x_146 = x_4;
x_147 = x_5;
x_148 = x_6;
x_149 = x_7;
x_150 = x_8;
x_151 = x_9;
x_152 = x_275;
goto block_209;
}
}
else
{
uint8_t x_279; 
x_279 = !lean_is_exclusive(x_210);
if (x_279 == 0)
{
x_143 = x_210;
x_144 = x_2;
x_145 = x_3;
x_146 = x_4;
x_147 = x_5;
x_148 = x_6;
x_149 = x_7;
x_150 = x_8;
x_151 = x_9;
x_152 = x_142;
goto block_209;
}
else
{
lean_object* x_280; lean_object* x_281; 
x_280 = lean_ctor_get(x_210, 0);
lean_inc(x_280);
lean_dec(x_210);
x_281 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_281, 0, x_280);
x_143 = x_281;
x_144 = x_2;
x_145 = x_3;
x_146 = x_4;
x_147 = x_5;
x_148 = x_6;
x_149 = x_7;
x_150 = x_8;
x_151 = x_9;
x_152 = x_142;
goto block_209;
}
}
block_209:
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_153 = lean_st_ref_get(x_144, x_152);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec_ref(x_153);
x_156 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_144, x_155);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec_ref(x_156);
x_159 = l_Lean_Meta_Grind_getSymbolPriorities___redArg(x_146, x_158);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; lean_object* x_166; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec_ref(x_159);
lean_inc_ref(x_1);
x_162 = l_Lean_Meta_mkOfEqTrueCore(x_1, x_141);
x_163 = lean_unsigned_to_nat(1000u);
x_164 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___closed__0;
x_165 = 0;
lean_inc(x_151);
lean_inc_ref(x_150);
lean_inc(x_149);
lean_inc_ref(x_148);
lean_inc(x_160);
lean_inc_ref(x_162);
lean_inc_ref(x_143);
x_166 = l_Lean_Meta_Grind_mkEMatchTheoremUsingSingletonPatterns(x_143, x_164, x_162, x_163, x_160, x_165, x_148, x_149, x_150, x_151, x_161);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; size_t x_169; size_t x_170; lean_object* x_171; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec_ref(x_166);
x_169 = lean_array_size(x_167);
x_170 = 0;
lean_inc(x_151);
lean_inc_ref(x_150);
lean_inc(x_149);
lean_inc_ref(x_148);
lean_inc(x_147);
lean_inc_ref(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_157);
x_171 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0(x_157, x_167, x_169, x_170, x_164, x_144, x_145, x_146, x_147, x_148, x_149, x_150, x_151, x_168);
lean_dec(x_167);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec_ref(x_171);
x_174 = lean_box(6);
lean_inc(x_151);
lean_inc_ref(x_150);
lean_inc(x_149);
lean_inc_ref(x_148);
lean_inc(x_160);
lean_inc_ref(x_162);
lean_inc_ref(x_143);
x_175 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(x_143, x_162, x_174, x_160, x_148, x_149, x_150, x_151, x_173);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_154, 12);
lean_inc_ref(x_176);
lean_dec(x_154);
x_177 = lean_ctor_get(x_176, 3);
lean_inc_ref(x_177);
lean_dec_ref(x_176);
x_178 = lean_ctor_get(x_175, 0);
lean_inc(x_178);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_ctor_get(x_175, 1);
lean_inc(x_179);
lean_dec_ref(x_175);
x_180 = lean_ctor_get(x_177, 2);
lean_inc(x_180);
lean_dec_ref(x_177);
x_110 = x_165;
x_111 = x_162;
x_112 = x_160;
x_113 = x_143;
x_114 = x_180;
x_115 = x_157;
x_116 = x_172;
x_117 = x_144;
x_118 = x_145;
x_119 = x_146;
x_120 = x_147;
x_121 = x_148;
x_122 = x_149;
x_123 = x_150;
x_124 = x_151;
x_125 = x_179;
goto block_139;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_181 = lean_ctor_get(x_175, 1);
lean_inc(x_181);
lean_dec_ref(x_175);
x_182 = lean_ctor_get(x_177, 2);
lean_inc(x_182);
lean_dec_ref(x_177);
x_183 = lean_ctor_get(x_178, 0);
lean_inc(x_183);
lean_dec_ref(x_178);
x_184 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(x_172, x_183);
if (x_184 == 0)
{
lean_dec(x_183);
x_110 = x_165;
x_111 = x_162;
x_112 = x_160;
x_113 = x_143;
x_114 = x_182;
x_115 = x_157;
x_116 = x_172;
x_117 = x_144;
x_118 = x_145;
x_119 = x_146;
x_120 = x_147;
x_121 = x_148;
x_122 = x_149;
x_123 = x_150;
x_124 = x_151;
x_125 = x_181;
goto block_139;
}
else
{
lean_object* x_185; 
lean_inc(x_151);
lean_inc_ref(x_150);
lean_inc(x_149);
lean_inc_ref(x_148);
lean_inc(x_147);
lean_inc_ref(x_146);
lean_inc(x_145);
lean_inc(x_144);
lean_inc(x_157);
lean_inc(x_183);
x_185 = l_Lean_Meta_Grind_activateTheorem(x_183, x_157, x_144, x_145, x_146, x_147, x_148, x_149, x_150, x_151, x_181);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_185, 1);
lean_inc(x_186);
lean_dec_ref(x_185);
x_187 = lean_ctor_get(x_183, 3);
lean_inc(x_187);
lean_dec(x_183);
x_188 = lean_array_push(x_172, x_187);
x_110 = x_165;
x_111 = x_162;
x_112 = x_160;
x_113 = x_143;
x_114 = x_182;
x_115 = x_157;
x_116 = x_188;
x_117 = x_144;
x_118 = x_145;
x_119 = x_146;
x_120 = x_147;
x_121 = x_148;
x_122 = x_149;
x_123 = x_150;
x_124 = x_151;
x_125 = x_186;
goto block_139;
}
else
{
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_172);
lean_dec_ref(x_162);
lean_dec(x_160);
lean_dec(x_157);
lean_dec(x_151);
lean_dec_ref(x_150);
lean_dec(x_149);
lean_dec_ref(x_148);
lean_dec(x_147);
lean_dec_ref(x_146);
lean_dec(x_145);
lean_dec(x_144);
lean_dec_ref(x_143);
lean_dec_ref(x_1);
return x_185;
}
}
}
}
else
{
uint8_t x_189; 
lean_dec(x_172);
lean_dec_ref(x_162);
lean_dec(x_160);
lean_dec(x_157);
lean_dec(x_154);
lean_dec(x_151);
lean_dec_ref(x_150);
lean_dec(x_149);
lean_dec_ref(x_148);
lean_dec(x_147);
lean_dec_ref(x_146);
lean_dec(x_145);
lean_dec(x_144);
lean_dec_ref(x_143);
lean_dec_ref(x_1);
x_189 = !lean_is_exclusive(x_175);
if (x_189 == 0)
{
return x_175;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_175, 0);
x_191 = lean_ctor_get(x_175, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_175);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
}
}
else
{
uint8_t x_193; 
lean_dec_ref(x_162);
lean_dec(x_160);
lean_dec(x_157);
lean_dec(x_154);
lean_dec(x_151);
lean_dec_ref(x_150);
lean_dec(x_149);
lean_dec_ref(x_148);
lean_dec(x_147);
lean_dec_ref(x_146);
lean_dec(x_145);
lean_dec(x_144);
lean_dec_ref(x_143);
lean_dec_ref(x_1);
x_193 = !lean_is_exclusive(x_171);
if (x_193 == 0)
{
return x_171;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_171, 0);
x_195 = lean_ctor_get(x_171, 1);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_171);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
return x_196;
}
}
}
else
{
uint8_t x_197; 
lean_dec_ref(x_162);
lean_dec(x_160);
lean_dec(x_157);
lean_dec(x_154);
lean_dec(x_151);
lean_dec_ref(x_150);
lean_dec(x_149);
lean_dec_ref(x_148);
lean_dec(x_147);
lean_dec_ref(x_146);
lean_dec(x_145);
lean_dec(x_144);
lean_dec_ref(x_143);
lean_dec_ref(x_1);
x_197 = !lean_is_exclusive(x_166);
if (x_197 == 0)
{
return x_166;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_166, 0);
x_199 = lean_ctor_get(x_166, 1);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_166);
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
return x_200;
}
}
}
else
{
uint8_t x_201; 
lean_dec(x_157);
lean_dec(x_154);
lean_dec(x_151);
lean_dec_ref(x_150);
lean_dec(x_149);
lean_dec_ref(x_148);
lean_dec(x_147);
lean_dec_ref(x_146);
lean_dec(x_145);
lean_dec(x_144);
lean_dec_ref(x_143);
lean_dec(x_141);
lean_dec_ref(x_1);
x_201 = !lean_is_exclusive(x_159);
if (x_201 == 0)
{
return x_159;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_159, 0);
x_203 = lean_ctor_get(x_159, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_159);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
}
}
else
{
uint8_t x_205; 
lean_dec(x_154);
lean_dec(x_151);
lean_dec_ref(x_150);
lean_dec(x_149);
lean_dec_ref(x_148);
lean_dec(x_147);
lean_dec_ref(x_146);
lean_dec(x_145);
lean_dec(x_144);
lean_dec_ref(x_143);
lean_dec(x_141);
lean_dec_ref(x_1);
x_205 = !lean_is_exclusive(x_156);
if (x_205 == 0)
{
return x_156;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_156, 0);
x_207 = lean_ctor_get(x_156, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_156);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
}
}
else
{
uint8_t x_282; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_282 = !lean_is_exclusive(x_140);
if (x_282 == 0)
{
return x_140;
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_283 = lean_ctor_get(x_140, 0);
x_284 = lean_ctor_get(x_140, 1);
lean_inc(x_284);
lean_inc(x_283);
lean_dec(x_140);
x_285 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_285, 0, x_283);
lean_ctor_set(x_285, 1, x_284);
return x_285;
}
}
block_74:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_st_ref_get(x_12, x_20);
lean_dec(x_12);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 12);
lean_inc_ref(x_23);
lean_dec(x_22);
x_24 = lean_ctor_get(x_23, 3);
lean_inc_ref(x_24);
lean_dec_ref(x_23);
x_25 = !lean_is_exclusive(x_21);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_21, 1);
x_27 = lean_ctor_get(x_21, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_24, 2);
lean_inc(x_28);
lean_dec_ref(x_24);
x_29 = lean_nat_dec_eq(x_28, x_11);
lean_dec(x_11);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_1);
x_30 = lean_box(0);
lean_ctor_set(x_21, 0, x_30);
return x_21;
}
else
{
lean_object* x_31; 
lean_free_object(x_21);
x_31 = l_Lean_Meta_Grind_getConfig___redArg(x_14, x_26);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get_uint8(x_32, sizeof(void*)*7 + 11);
lean_dec(x_32);
if (x_33 == 0)
{
uint8_t x_34; 
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_1);
x_34 = !lean_is_exclusive(x_31);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_31, 0);
lean_dec(x_35);
x_36 = lean_box(0);
lean_ctor_set(x_31, 0, x_36);
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_31, 1);
lean_inc(x_40);
lean_dec_ref(x_31);
x_41 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1;
x_42 = l_Lean_indentExpr(x_1);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Meta_Grind_propagateForallPropUp___closed__11;
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_Meta_Grind_reportIssue(x_45, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_40);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_1);
x_47 = !lean_is_exclusive(x_31);
if (x_47 == 0)
{
return x_31;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_31, 0);
x_49 = lean_ctor_get(x_31, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_31);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = lean_ctor_get(x_21, 1);
lean_inc(x_51);
lean_dec(x_21);
x_52 = lean_ctor_get(x_24, 2);
lean_inc(x_52);
lean_dec_ref(x_24);
x_53 = lean_nat_dec_eq(x_52, x_11);
lean_dec(x_11);
lean_dec(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_1);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_51);
return x_55;
}
else
{
lean_object* x_56; 
x_56 = l_Lean_Meta_Grind_getConfig___redArg(x_14, x_51);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get_uint8(x_57, sizeof(void*)*7 + 11);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_1);
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_60 = x_56;
} else {
 lean_dec_ref(x_56);
 x_60 = lean_box(0);
}
x_61 = lean_box(0);
if (lean_is_scalar(x_60)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_60;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_59);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_63 = lean_ctor_get(x_56, 1);
lean_inc(x_63);
lean_dec_ref(x_56);
x_64 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1;
x_65 = l_Lean_indentExpr(x_1);
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lean_Meta_Grind_propagateForallPropUp___closed__11;
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_Meta_Grind_reportIssue(x_68, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_63);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_1);
x_70 = lean_ctor_get(x_56, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_56, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_72 = x_56;
} else {
 lean_dec_ref(x_56);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
}
block_109:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_90 = lean_st_ref_get(x_81, x_89);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_91, 12);
lean_inc_ref(x_92);
lean_dec(x_91);
x_93 = lean_ctor_get(x_92, 3);
lean_inc_ref(x_93);
lean_dec_ref(x_92);
x_94 = lean_ctor_get(x_90, 1);
lean_inc(x_94);
lean_dec_ref(x_90);
x_95 = lean_ctor_get(x_93, 2);
lean_inc(x_95);
lean_dec_ref(x_93);
x_96 = lean_nat_dec_eq(x_95, x_80);
lean_dec(x_95);
if (x_96 == 0)
{
lean_dec(x_79);
lean_dec_ref(x_78);
lean_dec_ref(x_77);
lean_dec_ref(x_76);
x_11 = x_80;
x_12 = x_81;
x_13 = x_82;
x_14 = x_83;
x_15 = x_84;
x_16 = x_85;
x_17 = x_86;
x_18 = x_87;
x_19 = x_88;
x_20 = x_94;
goto block_74;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(x_97, 0, x_75);
lean_inc(x_88);
lean_inc_ref(x_87);
lean_inc(x_86);
lean_inc_ref(x_85);
x_98 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(x_78, x_76, x_97, x_77, x_85, x_86, x_87, x_88, x_94);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; 
lean_dec(x_79);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec_ref(x_98);
x_11 = x_80;
x_12 = x_81;
x_13 = x_82;
x_14 = x_83;
x_15 = x_84;
x_16 = x_85;
x_17 = x_86;
x_18 = x_87;
x_19 = x_88;
x_20 = x_100;
goto block_74;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_98, 1);
lean_inc(x_101);
lean_dec_ref(x_98);
x_102 = lean_ctor_get(x_99, 0);
lean_inc(x_102);
lean_dec_ref(x_99);
lean_inc(x_88);
lean_inc_ref(x_87);
lean_inc(x_86);
lean_inc_ref(x_85);
lean_inc(x_84);
lean_inc_ref(x_83);
lean_inc(x_82);
lean_inc(x_81);
x_103 = l_Lean_Meta_Grind_activateTheorem(x_102, x_79, x_81, x_82, x_83, x_84, x_85, x_86, x_87, x_88, x_101);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec_ref(x_103);
x_11 = x_80;
x_12 = x_81;
x_13 = x_82;
x_14 = x_83;
x_15 = x_84;
x_16 = x_85;
x_17 = x_86;
x_18 = x_87;
x_19 = x_88;
x_20 = x_104;
goto block_74;
}
else
{
lean_dec(x_88);
lean_dec_ref(x_87);
lean_dec(x_86);
lean_dec_ref(x_85);
lean_dec(x_84);
lean_dec_ref(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec_ref(x_1);
return x_103;
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_88);
lean_dec_ref(x_87);
lean_dec(x_86);
lean_dec_ref(x_85);
lean_dec(x_84);
lean_dec_ref(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_79);
lean_dec_ref(x_1);
x_105 = !lean_is_exclusive(x_98);
if (x_105 == 0)
{
return x_98;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_98, 0);
x_107 = lean_ctor_get(x_98, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_98);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
}
block_139:
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_box(7);
lean_inc(x_124);
lean_inc_ref(x_123);
lean_inc(x_122);
lean_inc_ref(x_121);
lean_inc_ref(x_112);
lean_inc_ref(x_111);
lean_inc_ref(x_113);
x_127 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(x_113, x_111, x_126, x_112, x_121, x_122, x_123, x_124, x_125);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; 
lean_dec_ref(x_116);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec_ref(x_127);
x_75 = x_110;
x_76 = x_111;
x_77 = x_112;
x_78 = x_113;
x_79 = x_115;
x_80 = x_114;
x_81 = x_117;
x_82 = x_118;
x_83 = x_119;
x_84 = x_120;
x_85 = x_121;
x_86 = x_122;
x_87 = x_123;
x_88 = x_124;
x_89 = x_129;
goto block_109;
}
else
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_130 = lean_ctor_get(x_127, 1);
lean_inc(x_130);
lean_dec_ref(x_127);
x_131 = lean_ctor_get(x_128, 0);
lean_inc(x_131);
lean_dec_ref(x_128);
x_132 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(x_116, x_131);
lean_dec_ref(x_116);
if (x_132 == 0)
{
lean_dec(x_131);
x_75 = x_110;
x_76 = x_111;
x_77 = x_112;
x_78 = x_113;
x_79 = x_115;
x_80 = x_114;
x_81 = x_117;
x_82 = x_118;
x_83 = x_119;
x_84 = x_120;
x_85 = x_121;
x_86 = x_122;
x_87 = x_123;
x_88 = x_124;
x_89 = x_130;
goto block_109;
}
else
{
lean_object* x_133; 
lean_inc(x_124);
lean_inc_ref(x_123);
lean_inc(x_122);
lean_inc_ref(x_121);
lean_inc(x_120);
lean_inc_ref(x_119);
lean_inc(x_118);
lean_inc(x_117);
lean_inc(x_115);
x_133 = l_Lean_Meta_Grind_activateTheorem(x_131, x_115, x_117, x_118, x_119, x_120, x_121, x_122, x_123, x_124, x_130);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; 
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
lean_dec_ref(x_133);
x_75 = x_110;
x_76 = x_111;
x_77 = x_112;
x_78 = x_113;
x_79 = x_115;
x_80 = x_114;
x_81 = x_117;
x_82 = x_118;
x_83 = x_119;
x_84 = x_120;
x_85 = x_121;
x_86 = x_122;
x_87 = x_123;
x_88 = x_124;
x_89 = x_134;
goto block_109;
}
else
{
lean_dec(x_124);
lean_dec_ref(x_123);
lean_dec(x_122);
lean_dec_ref(x_121);
lean_dec(x_120);
lean_dec_ref(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_dec(x_115);
lean_dec(x_114);
lean_dec_ref(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_111);
lean_dec_ref(x_1);
return x_133;
}
}
}
}
else
{
uint8_t x_135; 
lean_dec(x_124);
lean_dec_ref(x_123);
lean_dec(x_122);
lean_dec_ref(x_121);
lean_dec(x_120);
lean_dec_ref(x_119);
lean_dec(x_118);
lean_dec(x_117);
lean_dec_ref(x_116);
lean_dec(x_115);
lean_dec(x_114);
lean_dec_ref(x_113);
lean_dec_ref(x_112);
lean_dec_ref(x_111);
lean_dec_ref(x_1);
x_135 = !lean_is_exclusive(x_127);
if (x_135 == 0)
{
return x_127;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_127, 0);
x_137 = lean_ctor_get(x_127, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_127);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_17 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0(x_1, x_2, x_15, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_2);
return x_17;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eqResolution", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_propagateForallPropDown___closed__0;
x_2 = l_Lean_Meta_Grind_propagateForallPropUp___closed__3;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_propagateForallPropDown___closed__2;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Exists", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_propagateForallPropDown___closed__4;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("of_forall_eq_false", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_propagateForallPropDown___closed__6;
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1;
x_3 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_true_of_imp_eq_false", 23, 23);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_propagateForallPropDown___closed__8;
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1;
x_3 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_propagateForallPropDown___closed__9;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("eq_false_of_imp_eq_false", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_propagateForallPropDown___closed__11;
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1;
x_3 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_propagateForallPropDown___closed__12;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropDown(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_47; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_1, 2);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_inc_ref(x_1);
x_47 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_4, x_8, x_9, x_10);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_unbox(x_48);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_47, 1);
lean_inc(x_50);
lean_dec_ref(x_47);
lean_inc_ref(x_1);
x_51 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_4, x_8, x_9, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_unbox(x_52);
lean_dec(x_52);
if (x_53 == 0)
{
uint8_t x_54; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_54 = !lean_is_exclusive(x_51);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_51, 0);
lean_dec(x_55);
x_56 = lean_box(0);
lean_ctor_set(x_51, 0, x_56);
return x_51;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_51, 1);
lean_inc(x_57);
lean_dec(x_51);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_51, 1);
lean_inc(x_60);
lean_dec_ref(x_51);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_1);
x_61 = l_Lean_Meta_Grind_eqResolution(x_1, x_6, x_7, x_8, x_9, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec_ref(x_61);
x_64 = l_Lean_Expr_hasLooseBVars(x_13);
if (x_64 == 0)
{
lean_object* x_65; 
lean_inc_ref(x_13);
lean_inc_ref(x_12);
x_65 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_13, x_2, x_63);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_unbox(x_66);
lean_dec(x_66);
if (x_67 == 0)
{
uint8_t x_68; 
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_68 = !lean_is_exclusive(x_65);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_65, 0);
lean_dec(x_69);
x_70 = lean_box(0);
lean_ctor_set(x_65, 0, x_70);
return x_65;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_65, 1);
lean_inc(x_71);
lean_dec(x_65);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_65, 1);
lean_inc(x_74);
lean_dec_ref(x_65);
lean_inc_ref(x_13);
x_75 = l_Lean_Meta_Grind_isEqFalse___redArg(x_13, x_2, x_4, x_8, x_9, x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_unbox(x_76);
lean_dec(x_76);
if (x_77 == 0)
{
x_15 = x_75;
goto block_46;
}
else
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
lean_dec_ref(x_75);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_12);
x_79 = l_Lean_Meta_isProp(x_12, x_6, x_7, x_8, x_9, x_78);
x_15 = x_79;
goto block_46;
}
}
else
{
x_15 = x_75;
goto block_46;
}
}
}
else
{
uint8_t x_80; 
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_80 = !lean_is_exclusive(x_65);
if (x_80 == 0)
{
return x_65;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_65, 0);
x_82 = lean_ctor_get(x_65, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_65);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_12);
x_84 = l_Lean_Meta_isProp(x_12, x_6, x_7, x_8, x_9, x_63);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; uint8_t x_86; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_unbox(x_85);
lean_dec(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_84, 1);
lean_inc(x_87);
lean_dec_ref(x_84);
x_88 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_87);
return x_88;
}
else
{
uint8_t x_89; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_89 = !lean_is_exclusive(x_84);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_84, 0);
lean_dec(x_90);
x_91 = lean_box(0);
lean_ctor_set(x_84, 0, x_91);
return x_84;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_84, 1);
lean_inc(x_92);
lean_dec(x_84);
x_93 = lean_box(0);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_95 = !lean_is_exclusive(x_84);
if (x_95 == 0)
{
return x_84;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_84, 0);
x_97 = lean_ctor_get(x_84, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_84);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
x_99 = lean_ctor_get(x_62, 0);
lean_inc(x_99);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 x_100 = x_62;
} else {
 lean_dec_ref(x_62);
 x_100 = lean_box(0);
}
x_101 = lean_ctor_get(x_61, 1);
lean_inc(x_101);
lean_dec_ref(x_61);
x_102 = !lean_is_exclusive(x_99);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_103 = lean_ctor_get(x_99, 0);
x_104 = lean_ctor_get(x_99, 1);
x_133 = l_Lean_Meta_Grind_propagateForallPropDown___closed__1;
x_134 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(x_133, x_8, x_101);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_unbox(x_135);
lean_dec(x_135);
if (x_136 == 0)
{
lean_object* x_137; 
lean_free_object(x_99);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
lean_dec_ref(x_134);
x_105 = x_2;
x_106 = x_3;
x_107 = x_4;
x_108 = x_5;
x_109 = x_6;
x_110 = x_7;
x_111 = x_8;
x_112 = x_9;
x_113 = x_137;
goto block_132;
}
else
{
uint8_t x_138; 
x_138 = !lean_is_exclusive(x_134);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_134, 1);
x_140 = lean_ctor_get(x_134, 0);
lean_dec(x_140);
x_141 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_139);
if (lean_obj_tag(x_141) == 0)
{
uint8_t x_142; 
x_142 = !lean_is_exclusive(x_141);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_143 = lean_ctor_get(x_141, 1);
x_144 = lean_ctor_get(x_141, 0);
lean_dec(x_144);
x_145 = l_Lean_Meta_Grind_propagateForallPropUp___closed__11;
lean_inc_ref(x_1);
x_146 = l_Lean_MessageData_ofExpr(x_1);
lean_ctor_set_tag(x_141, 7);
lean_ctor_set(x_141, 1, x_146);
lean_ctor_set(x_141, 0, x_145);
x_147 = l_Lean_Meta_Grind_propagateForallPropDown___closed__3;
lean_ctor_set_tag(x_134, 7);
lean_ctor_set(x_134, 1, x_147);
lean_ctor_set(x_134, 0, x_141);
lean_inc(x_103);
x_148 = l_Lean_MessageData_ofExpr(x_103);
lean_ctor_set_tag(x_99, 7);
lean_ctor_set(x_99, 1, x_148);
lean_ctor_set(x_99, 0, x_134);
x_149 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_149, 0, x_99);
lean_ctor_set(x_149, 1, x_145);
x_150 = l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(x_133, x_149, x_6, x_7, x_8, x_9, x_143);
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
lean_dec_ref(x_150);
x_105 = x_2;
x_106 = x_3;
x_107 = x_4;
x_108 = x_5;
x_109 = x_6;
x_110 = x_7;
x_111 = x_8;
x_112 = x_9;
x_113 = x_151;
goto block_132;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_152 = lean_ctor_get(x_141, 1);
lean_inc(x_152);
lean_dec(x_141);
x_153 = l_Lean_Meta_Grind_propagateForallPropUp___closed__11;
lean_inc_ref(x_1);
x_154 = l_Lean_MessageData_ofExpr(x_1);
x_155 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
x_156 = l_Lean_Meta_Grind_propagateForallPropDown___closed__3;
lean_ctor_set_tag(x_134, 7);
lean_ctor_set(x_134, 1, x_156);
lean_ctor_set(x_134, 0, x_155);
lean_inc(x_103);
x_157 = l_Lean_MessageData_ofExpr(x_103);
lean_ctor_set_tag(x_99, 7);
lean_ctor_set(x_99, 1, x_157);
lean_ctor_set(x_99, 0, x_134);
x_158 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_158, 0, x_99);
lean_ctor_set(x_158, 1, x_153);
x_159 = l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(x_133, x_158, x_6, x_7, x_8, x_9, x_152);
x_160 = lean_ctor_get(x_159, 1);
lean_inc(x_160);
lean_dec_ref(x_159);
x_105 = x_2;
x_106 = x_3;
x_107 = x_4;
x_108 = x_5;
x_109 = x_6;
x_110 = x_7;
x_111 = x_8;
x_112 = x_9;
x_113 = x_160;
goto block_132;
}
}
else
{
lean_free_object(x_134);
lean_free_object(x_99);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_100);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_141;
}
}
else
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_134, 1);
lean_inc(x_161);
lean_dec(x_134);
x_162 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_161);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_164 = x_162;
} else {
 lean_dec_ref(x_162);
 x_164 = lean_box(0);
}
x_165 = l_Lean_Meta_Grind_propagateForallPropUp___closed__11;
lean_inc_ref(x_1);
x_166 = l_Lean_MessageData_ofExpr(x_1);
if (lean_is_scalar(x_164)) {
 x_167 = lean_alloc_ctor(7, 2, 0);
} else {
 x_167 = x_164;
 lean_ctor_set_tag(x_167, 7);
}
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
x_168 = l_Lean_Meta_Grind_propagateForallPropDown___closed__3;
x_169 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
lean_inc(x_103);
x_170 = l_Lean_MessageData_ofExpr(x_103);
lean_ctor_set_tag(x_99, 7);
lean_ctor_set(x_99, 1, x_170);
lean_ctor_set(x_99, 0, x_169);
x_171 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_171, 0, x_99);
lean_ctor_set(x_171, 1, x_165);
x_172 = l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(x_133, x_171, x_6, x_7, x_8, x_9, x_163);
x_173 = lean_ctor_get(x_172, 1);
lean_inc(x_173);
lean_dec_ref(x_172);
x_105 = x_2;
x_106 = x_3;
x_107 = x_4;
x_108 = x_5;
x_109 = x_6;
x_110 = x_7;
x_111 = x_8;
x_112 = x_9;
x_113 = x_173;
goto block_132;
}
else
{
lean_free_object(x_99);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_100);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_162;
}
}
}
block_132:
{
lean_object* x_114; 
lean_inc(x_112);
lean_inc_ref(x_111);
lean_inc(x_110);
lean_inc_ref(x_109);
lean_inc(x_108);
lean_inc_ref(x_107);
lean_inc(x_106);
lean_inc(x_105);
lean_inc_ref(x_1);
x_114 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_105, x_106, x_107, x_108, x_109, x_110, x_111, x_112, x_113);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec_ref(x_114);
x_117 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_105, x_116);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec_ref(x_117);
lean_inc_ref(x_1);
x_120 = l_Lean_Meta_mkOfEqTrueCore(x_1, x_115);
x_121 = l_Lean_Expr_app___override(x_104, x_120);
if (lean_is_scalar(x_100)) {
 x_122 = lean_alloc_ctor(4, 1, 0);
} else {
 x_122 = x_100;
 lean_ctor_set_tag(x_122, 4);
}
lean_ctor_set(x_122, 0, x_1);
x_123 = l_Lean_Meta_Grind_addNewRawFact(x_121, x_103, x_118, x_122, x_105, x_106, x_107, x_108, x_109, x_110, x_111, x_112, x_119);
lean_dec(x_108);
lean_dec_ref(x_107);
lean_dec(x_106);
lean_dec(x_105);
return x_123;
}
else
{
uint8_t x_124; 
lean_dec(x_115);
lean_dec(x_112);
lean_dec_ref(x_111);
lean_dec(x_110);
lean_dec_ref(x_109);
lean_dec(x_108);
lean_dec_ref(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_100);
lean_dec_ref(x_1);
x_124 = !lean_is_exclusive(x_117);
if (x_124 == 0)
{
return x_117;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_117, 0);
x_126 = lean_ctor_get(x_117, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_117);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_112);
lean_dec_ref(x_111);
lean_dec(x_110);
lean_dec_ref(x_109);
lean_dec(x_108);
lean_dec_ref(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_100);
lean_dec_ref(x_1);
x_128 = !lean_is_exclusive(x_114);
if (x_128 == 0)
{
return x_114;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_114, 0);
x_130 = lean_ctor_get(x_114, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_114);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; 
x_174 = lean_ctor_get(x_99, 0);
x_175 = lean_ctor_get(x_99, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_99);
x_204 = l_Lean_Meta_Grind_propagateForallPropDown___closed__1;
x_205 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(x_204, x_8, x_101);
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_unbox(x_206);
lean_dec(x_206);
if (x_207 == 0)
{
lean_object* x_208; 
x_208 = lean_ctor_get(x_205, 1);
lean_inc(x_208);
lean_dec_ref(x_205);
x_176 = x_2;
x_177 = x_3;
x_178 = x_4;
x_179 = x_5;
x_180 = x_6;
x_181 = x_7;
x_182 = x_8;
x_183 = x_9;
x_184 = x_208;
goto block_203;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_205, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_210 = x_205;
} else {
 lean_dec_ref(x_205);
 x_210 = lean_box(0);
}
x_211 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_209);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_212 = lean_ctor_get(x_211, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_213 = x_211;
} else {
 lean_dec_ref(x_211);
 x_213 = lean_box(0);
}
x_214 = l_Lean_Meta_Grind_propagateForallPropUp___closed__11;
lean_inc_ref(x_1);
x_215 = l_Lean_MessageData_ofExpr(x_1);
if (lean_is_scalar(x_213)) {
 x_216 = lean_alloc_ctor(7, 2, 0);
} else {
 x_216 = x_213;
 lean_ctor_set_tag(x_216, 7);
}
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set(x_216, 1, x_215);
x_217 = l_Lean_Meta_Grind_propagateForallPropDown___closed__3;
if (lean_is_scalar(x_210)) {
 x_218 = lean_alloc_ctor(7, 2, 0);
} else {
 x_218 = x_210;
 lean_ctor_set_tag(x_218, 7);
}
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
lean_inc(x_174);
x_219 = l_Lean_MessageData_ofExpr(x_174);
x_220 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
x_221 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_221, 0, x_220);
lean_ctor_set(x_221, 1, x_214);
x_222 = l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(x_204, x_221, x_6, x_7, x_8, x_9, x_212);
x_223 = lean_ctor_get(x_222, 1);
lean_inc(x_223);
lean_dec_ref(x_222);
x_176 = x_2;
x_177 = x_3;
x_178 = x_4;
x_179 = x_5;
x_180 = x_6;
x_181 = x_7;
x_182 = x_8;
x_183 = x_9;
x_184 = x_223;
goto block_203;
}
else
{
lean_dec(x_210);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_100);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_211;
}
}
block_203:
{
lean_object* x_185; 
lean_inc(x_183);
lean_inc_ref(x_182);
lean_inc(x_181);
lean_inc_ref(x_180);
lean_inc(x_179);
lean_inc_ref(x_178);
lean_inc(x_177);
lean_inc(x_176);
lean_inc_ref(x_1);
x_185 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_176, x_177, x_178, x_179, x_180, x_181, x_182, x_183, x_184);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec_ref(x_185);
x_188 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_176, x_187);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec_ref(x_188);
lean_inc_ref(x_1);
x_191 = l_Lean_Meta_mkOfEqTrueCore(x_1, x_186);
x_192 = l_Lean_Expr_app___override(x_175, x_191);
if (lean_is_scalar(x_100)) {
 x_193 = lean_alloc_ctor(4, 1, 0);
} else {
 x_193 = x_100;
 lean_ctor_set_tag(x_193, 4);
}
lean_ctor_set(x_193, 0, x_1);
x_194 = l_Lean_Meta_Grind_addNewRawFact(x_192, x_174, x_189, x_193, x_176, x_177, x_178, x_179, x_180, x_181, x_182, x_183, x_190);
lean_dec(x_179);
lean_dec_ref(x_178);
lean_dec(x_177);
lean_dec(x_176);
return x_194;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_186);
lean_dec(x_183);
lean_dec_ref(x_182);
lean_dec(x_181);
lean_dec_ref(x_180);
lean_dec(x_179);
lean_dec_ref(x_178);
lean_dec(x_177);
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_100);
lean_dec_ref(x_1);
x_195 = lean_ctor_get(x_188, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_188, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_197 = x_188;
} else {
 lean_dec_ref(x_188);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(1, 2, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_196);
return x_198;
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_183);
lean_dec_ref(x_182);
lean_dec(x_181);
lean_dec_ref(x_180);
lean_dec(x_179);
lean_dec_ref(x_178);
lean_dec(x_177);
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_100);
lean_dec_ref(x_1);
x_199 = lean_ctor_get(x_185, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_185, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_201 = x_185;
} else {
 lean_dec_ref(x_185);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(1, 2, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_199);
lean_ctor_set(x_202, 1, x_200);
return x_202;
}
}
}
}
}
else
{
uint8_t x_224; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_224 = !lean_is_exclusive(x_61);
if (x_224 == 0)
{
return x_61;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_61, 0);
x_226 = lean_ctor_get(x_61, 1);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_61);
x_227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
return x_227;
}
}
}
}
else
{
uint8_t x_228; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_228 = !lean_is_exclusive(x_51);
if (x_228 == 0)
{
return x_51;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = lean_ctor_get(x_51, 0);
x_230 = lean_ctor_get(x_51, 1);
lean_inc(x_230);
lean_inc(x_229);
lean_dec(x_51);
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_230);
return x_231;
}
}
}
else
{
lean_object* x_232; lean_object* x_233; 
x_232 = lean_ctor_get(x_47, 1);
lean_inc(x_232);
lean_dec_ref(x_47);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_12);
x_233 = l_Lean_Meta_isProp(x_12, x_6, x_7, x_8, x_9, x_232);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; uint8_t x_271; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec_ref(x_233);
x_271 = l_Lean_Expr_hasLooseBVars(x_13);
if (x_271 == 0)
{
uint8_t x_272; 
x_272 = lean_unbox(x_234);
lean_dec(x_234);
if (x_272 == 0)
{
goto block_270;
}
else
{
if (x_271 == 0)
{
lean_object* x_273; 
lean_inc_ref(x_13);
lean_inc_ref(x_12);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_273 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_235);
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_273, 1);
lean_inc(x_275);
lean_dec_ref(x_273);
x_276 = l_Lean_Meta_Grind_propagateForallPropDown___closed__10;
lean_inc(x_274);
lean_inc_ref(x_13);
lean_inc_ref(x_12);
x_277 = l_Lean_mkApp3(x_276, x_12, x_13, x_274);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_12);
x_278 = l_Lean_Meta_Grind_pushEqTrue(x_12, x_277, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_275);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_279 = lean_ctor_get(x_278, 1);
lean_inc(x_279);
lean_dec_ref(x_278);
x_280 = l_Lean_Meta_Grind_propagateForallPropDown___closed__13;
lean_inc_ref(x_13);
x_281 = l_Lean_mkApp3(x_280, x_12, x_13, x_274);
x_282 = l_Lean_Meta_Grind_pushEqFalse(x_13, x_281, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_279);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_282;
}
else
{
lean_dec(x_274);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_278;
}
}
else
{
uint8_t x_283; 
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_283 = !lean_is_exclusive(x_273);
if (x_283 == 0)
{
return x_273;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_284 = lean_ctor_get(x_273, 0);
x_285 = lean_ctor_get(x_273, 1);
lean_inc(x_285);
lean_inc(x_284);
lean_dec(x_273);
x_286 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_286, 0, x_284);
lean_ctor_set(x_286, 1, x_285);
return x_286;
}
}
}
else
{
goto block_270;
}
}
}
else
{
lean_dec(x_234);
goto block_270;
}
block_270:
{
lean_object* x_236; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_12);
x_236 = l_Lean_Meta_getLevel(x_12, x_6, x_7, x_8, x_9, x_235);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_236, 1);
lean_inc(x_238);
lean_dec_ref(x_236);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_239 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_238);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_239, 1);
lean_inc(x_241);
lean_dec_ref(x_239);
x_242 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2, x_241);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
lean_dec_ref(x_242);
x_245 = l_Lean_Meta_Grind_propagateForallPropDown___closed__5;
x_246 = lean_box(0);
x_247 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_247, 0, x_237);
lean_ctor_set(x_247, 1, x_246);
lean_inc_ref(x_247);
x_248 = l_Lean_mkConst(x_245, x_247);
lean_inc_ref(x_13);
x_249 = l_Lean_mkNot(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
x_250 = l_Lean_mkLambda(x_11, x_14, x_12, x_249);
lean_inc_ref(x_12);
x_251 = l_Lean_mkAppB(x_248, x_12, x_250);
x_252 = l_Lean_Meta_Grind_propagateForallPropDown___closed__7;
x_253 = l_Lean_mkConst(x_252, x_247);
lean_inc_ref(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
x_254 = l_Lean_mkLambda(x_11, x_14, x_12, x_13);
lean_inc_ref(x_12);
x_255 = l_Lean_mkApp3(x_253, x_12, x_254, x_240);
x_256 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_256, 0, x_1);
x_257 = l_Lean_Meta_Grind_addNewRawFact(x_255, x_251, x_243, x_256, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_244);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_257;
}
else
{
uint8_t x_258; 
lean_dec(x_240);
lean_dec(x_237);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_258 = !lean_is_exclusive(x_242);
if (x_258 == 0)
{
return x_242;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_259 = lean_ctor_get(x_242, 0);
x_260 = lean_ctor_get(x_242, 1);
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_242);
x_261 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_261, 0, x_259);
lean_ctor_set(x_261, 1, x_260);
return x_261;
}
}
}
else
{
uint8_t x_262; 
lean_dec(x_237);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_262 = !lean_is_exclusive(x_239);
if (x_262 == 0)
{
return x_239;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_263 = lean_ctor_get(x_239, 0);
x_264 = lean_ctor_get(x_239, 1);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_239);
x_265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_265, 0, x_263);
lean_ctor_set(x_265, 1, x_264);
return x_265;
}
}
}
else
{
uint8_t x_266; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_266 = !lean_is_exclusive(x_236);
if (x_266 == 0)
{
return x_236;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_267 = lean_ctor_get(x_236, 0);
x_268 = lean_ctor_get(x_236, 1);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_236);
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
return x_269;
}
}
}
}
else
{
uint8_t x_287; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_287 = !lean_is_exclusive(x_233);
if (x_287 == 0)
{
return x_233;
}
else
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_288 = lean_ctor_get(x_233, 0);
x_289 = lean_ctor_get(x_233, 1);
lean_inc(x_289);
lean_inc(x_288);
lean_dec(x_233);
x_290 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_290, 0, x_288);
lean_ctor_set(x_290, 1, x_289);
return x_290;
}
}
}
}
else
{
uint8_t x_291; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_291 = !lean_is_exclusive(x_47);
if (x_291 == 0)
{
return x_47;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_292 = lean_ctor_get(x_47, 0);
x_293 = lean_ctor_get(x_47, 1);
lean_inc(x_293);
lean_inc(x_292);
lean_dec(x_47);
x_294 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_294, 0, x_292);
lean_ctor_set(x_294, 1, x_293);
return x_294;
}
}
block_46:
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
x_17 = lean_unbox(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_dec_ref(x_15);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_25 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_13);
x_28 = l_Lean_Meta_Grind_mkEqFalseProof(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec_ref(x_28);
x_31 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4;
lean_inc_ref(x_12);
x_32 = l_Lean_mkApp4(x_31, x_12, x_13, x_26, x_29);
x_33 = l_Lean_Meta_Grind_pushEqFalse(x_12, x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_30);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_26);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_28);
if (x_34 == 0)
{
return x_28;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_28, 0);
x_36 = lean_ctor_get(x_28, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_28);
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
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_25);
if (x_38 == 0)
{
return x_25;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_25, 0);
x_40 = lean_ctor_get(x_25, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_25);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_42 = !lean_is_exclusive(x_15);
if (x_42 == 0)
{
return x_15;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_15, 0);
x_44 = lean_ctor_get(x_15, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_15);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
else
{
lean_object* x_295; lean_object* x_296; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_295 = lean_box(0);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_10);
return x_296;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateExistsDown___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Not", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateExistsDown___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_propagateExistsDown___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateExistsDown___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_propagateExistsDown___closed__1;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateExistsDown___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Expr_bvar___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateExistsDown___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("x", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateExistsDown___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_propagateExistsDown___closed__4;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateExistsDown___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("forall_not_of_not_exists", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateExistsDown___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_propagateExistsDown___closed__6;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateExistsDown(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; 
lean_inc_ref(x_1);
x_15 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_4, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_18 = !lean_is_exclusive(x_15);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_15, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_15, 0, x_20);
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_dec_ref(x_15);
lean_inc_ref(x_1);
x_25 = l_Lean_Expr_cleanupAnnotations(x_1);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec_ref(x_25);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_11 = x_24;
goto block_14;
}
else
{
lean_object* x_27; uint8_t x_28; 
lean_inc_ref(x_25);
x_27 = l_Lean_Expr_appFnCleanup___redArg(x_25);
x_28 = l_Lean_Expr_isApp(x_27);
if (x_28 == 0)
{
lean_dec_ref(x_27);
lean_dec_ref(x_25);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_11 = x_24;
goto block_14;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_inc_ref(x_27);
x_29 = l_Lean_Expr_appFnCleanup___redArg(x_27);
x_30 = l_Lean_Meta_Grind_propagateForallPropDown___closed__5;
x_31 = l_Lean_Expr_isConstOf(x_29, x_30);
if (x_31 == 0)
{
lean_dec_ref(x_29);
lean_dec_ref(x_27);
lean_dec_ref(x_25);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_11 = x_24;
goto block_14;
}
else
{
lean_object* x_32; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_32 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_24);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec_ref(x_32);
x_35 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec_ref(x_35);
x_38 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_38);
lean_dec_ref(x_25);
x_39 = lean_ctor_get(x_27, 1);
lean_inc_ref(x_39);
lean_dec_ref(x_27);
x_40 = l_Lean_Expr_constLevels_x21(x_29);
lean_dec_ref(x_29);
x_41 = l_Lean_Meta_Grind_propagateExistsDown___closed__2;
x_42 = l_Lean_Meta_Grind_propagateExistsDown___closed__3;
lean_inc_ref(x_38);
x_43 = l_Lean_Expr_app___override(x_38, x_42);
x_44 = l_Lean_Expr_headBeta(x_43);
x_45 = l_Lean_Expr_app___override(x_41, x_44);
x_46 = l_Lean_Meta_Grind_propagateExistsDown___closed__5;
x_47 = 0;
lean_inc_ref(x_39);
x_48 = l_Lean_mkForall(x_46, x_47, x_39, x_45);
x_49 = l_Lean_Meta_Grind_propagateExistsDown___closed__7;
x_50 = l_Lean_mkConst(x_49, x_40);
lean_inc_ref(x_1);
x_51 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_33);
x_52 = l_Lean_mkApp3(x_50, x_39, x_38, x_51);
x_53 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_53, 0, x_1);
x_54 = l_Lean_Meta_Grind_addNewRawFact(x_52, x_48, x_36, x_53, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_37);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_54;
}
else
{
uint8_t x_55; 
lean_dec(x_33);
lean_dec_ref(x_29);
lean_dec_ref(x_27);
lean_dec_ref(x_25);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_55 = !lean_is_exclusive(x_35);
if (x_55 == 0)
{
return x_35;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_35, 0);
x_57 = lean_ctor_get(x_35, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_35);
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
lean_dec_ref(x_29);
lean_dec_ref(x_27);
lean_dec_ref(x_25);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_59 = !lean_is_exclusive(x_32);
if (x_59 == 0)
{
return x_32;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_32, 0);
x_61 = lean_ctor_get(x_32, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_32);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_63 = !lean_is_exclusive(x_15);
if (x_63 == 0)
{
return x_15;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_15, 0);
x_65 = lean_ctor_get(x_15, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_15);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateExistsDown___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1____x40_Lean_Meta_Tactic_Grind_ForallProp_115310127____hygCtx___hyg_8_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_Grind_propagateForallPropDown___closed__5;
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateExistsDown), 10, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(x_2, x_3, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("a", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("False", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__3;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_4);
lean_inc_ref(x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
lean_inc(x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = l_Lean_Meta_Grind_propagateExistsDown___closed__1;
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Expr_isAppOfArity(x_1, x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_box(0);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__1;
x_13 = l_Lean_Expr_appArg_x21(x_1);
x_14 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__4;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_5, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___lam__0), 10, 4);
lean_closure_set(x_14, 0, x_4);
lean_closure_set(x_14, 1, x_6);
lean_closure_set(x_14, 2, x_7);
lean_closure_set(x_14, 3, x_8);
x_15 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), x_1, x_2, x_3, x_14, x_5, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_15);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_Grind_simpForall_spec__0_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___Lean_Meta_Grind_simpForall_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = 0;
x_13 = 0;
x_14 = l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg(x_1, x_12, x_2, x_3, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___Lean_Meta_Grind_simpForall_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_withLocalDeclD___at___Lean_Meta_Grind_simpForall_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_expr_instantiate1(x_1, x_2);
x_12 = l_Lean_Meta_getLevel(x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Or", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_simpForall___closed__1;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("And", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_simpForall___closed__3;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("forall_and", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_simpForall___closed__5;
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1;
x_3 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("forall_or_forall", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_simpForall___closed__7;
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1;
x_3 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("forall_forall_or", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_simpForall___closed__9;
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1;
x_3 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("True", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_simpForall___closed__11;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_simpForall___closed__12;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("imp_self_eq", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_simpForall___closed__14;
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1;
x_3 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_simpForall___closed__15;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("forall_imp_eq_or", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_simpForall___closed__17;
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1;
x_3 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("imp_true_eq", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_simpForall___closed__19;
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1;
x_3 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_simpForall___closed__20;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__22() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("imp_false_eq", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_simpForall___closed__22;
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1;
x_3 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_simpForall___closed__23;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true_imp_eq", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_simpForall___closed__25;
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1;
x_3 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__27() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_simpForall___closed__26;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__28() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("false_imp_eq", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_simpForall___closed__28;
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1;
x_3 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__30() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_simpForall___closed__29;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__31() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("intro", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_simpForall___closed__31;
x_2 = l_Lean_Meta_Grind_simpForall___closed__11;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__33() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_simpForall___closed__32;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__34() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("forall_true", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_simpForall___closed__34;
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1;
x_3 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__36() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_simpForall___closed__35;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__37() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Level_ofNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__38() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_simpForall___closed__37;
x_2 = l_Lean_mkSort(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__39() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("forall_false", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__40() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_simpForall___closed__39;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpForall___closed__41() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_simpForall___closed__40;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; uint8_t x_460; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_16);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec_ref(x_1);
x_460 = l_Lean_Expr_hasLooseBVars(x_16);
if (x_460 == 0)
{
lean_object* x_461; 
lean_inc_ref(x_15);
x_461 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_15, x_6, x_9);
if (lean_obj_tag(x_461) == 0)
{
lean_object* x_462; lean_object* x_463; uint8_t x_464; lean_object* x_465; lean_object* x_490; lean_object* x_491; uint8_t x_492; 
x_462 = lean_ctor_get(x_461, 0);
lean_inc(x_462);
x_463 = lean_ctor_get(x_461, 1);
lean_inc(x_463);
lean_dec_ref(x_461);
x_464 = 1;
x_490 = l_Lean_Expr_cleanupAnnotations(x_462);
x_491 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__3;
x_492 = l_Lean_Expr_isConstOf(x_490, x_491);
if (x_492 == 0)
{
lean_object* x_493; uint8_t x_494; 
x_493 = l_Lean_Meta_Grind_simpForall___closed__12;
x_494 = l_Lean_Expr_isConstOf(x_490, x_493);
lean_dec_ref(x_490);
if (x_494 == 0)
{
if (lean_obj_tag(x_15) == 7)
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; uint8_t x_498; uint8_t x_499; lean_object* x_500; uint8_t x_542; 
x_495 = lean_ctor_get(x_15, 0);
x_496 = lean_ctor_get(x_15, 1);
x_497 = lean_ctor_get(x_15, 2);
x_498 = lean_ctor_get_uint8(x_15, sizeof(void*)*3 + 8);
x_542 = l_Lean_Expr_hasLooseBVars(x_497);
if (x_542 == 0)
{
x_499 = x_542;
x_500 = x_463;
goto block_541;
}
else
{
lean_object* x_543; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_15);
x_543 = l_Lean_Meta_isProp(x_15, x_5, x_6, x_7, x_8, x_463);
if (lean_obj_tag(x_543) == 0)
{
lean_object* x_544; lean_object* x_545; uint8_t x_546; 
x_544 = lean_ctor_get(x_543, 0);
lean_inc(x_544);
x_545 = lean_ctor_get(x_543, 1);
lean_inc(x_545);
lean_dec_ref(x_543);
x_546 = lean_unbox(x_544);
lean_dec(x_544);
x_499 = x_546;
x_500 = x_545;
goto block_541;
}
else
{
uint8_t x_547; 
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_547 = !lean_is_exclusive(x_543);
if (x_547 == 0)
{
return x_543;
}
else
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; 
x_548 = lean_ctor_get(x_543, 0);
x_549 = lean_ctor_get(x_543, 1);
lean_inc(x_549);
lean_inc(x_548);
lean_dec(x_543);
x_550 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_550, 0, x_548);
lean_ctor_set(x_550, 1, x_549);
return x_550;
}
}
}
block_541:
{
if (x_499 == 0)
{
x_447 = x_2;
x_448 = x_3;
x_449 = x_4;
x_450 = x_5;
x_451 = x_6;
x_452 = x_7;
x_453 = x_8;
x_454 = x_500;
goto block_459;
}
else
{
lean_object* x_501; 
lean_inc_ref(x_497);
lean_inc_ref(x_496);
lean_inc(x_495);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_inc_ref(x_496);
x_501 = l_Lean_Meta_getLevel(x_496, x_5, x_6, x_7, x_8, x_500);
if (lean_obj_tag(x_501) == 0)
{
uint8_t x_502; 
x_502 = !lean_is_exclusive(x_501);
if (x_502 == 0)
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; 
x_503 = lean_ctor_get(x_501, 0);
lean_inc_ref(x_497);
lean_inc_ref(x_496);
lean_inc(x_495);
x_504 = l_Lean_mkLambda(x_495, x_498, x_496, x_497);
x_505 = l_Lean_Meta_Grind_propagateForallPropDown___closed__5;
x_506 = lean_box(0);
x_507 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_507, 0, x_503);
lean_ctor_set(x_507, 1, x_506);
lean_inc_ref(x_507);
x_508 = l_Lean_mkConst(x_505, x_507);
x_509 = l_Lean_mkNot(x_497);
lean_inc_ref(x_496);
x_510 = l_Lean_mkLambda(x_495, x_498, x_496, x_509);
lean_inc_ref(x_496);
x_511 = l_Lean_mkAppB(x_508, x_496, x_510);
lean_inc_ref(x_16);
x_512 = l_Lean_mkOr(x_511, x_16);
x_513 = l_Lean_Meta_Grind_simpForall___closed__18;
x_514 = l_Lean_mkConst(x_513, x_507);
x_515 = l_Lean_mkApp3(x_514, x_496, x_504, x_16);
x_516 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_516, 0, x_515);
x_517 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_517, 0, x_512);
lean_ctor_set(x_517, 1, x_516);
lean_ctor_set_uint8(x_517, sizeof(void*)*2, x_464);
x_518 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_518, 0, x_517);
lean_ctor_set(x_501, 0, x_518);
return x_501;
}
else
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; 
x_519 = lean_ctor_get(x_501, 0);
x_520 = lean_ctor_get(x_501, 1);
lean_inc(x_520);
lean_inc(x_519);
lean_dec(x_501);
lean_inc_ref(x_497);
lean_inc_ref(x_496);
lean_inc(x_495);
x_521 = l_Lean_mkLambda(x_495, x_498, x_496, x_497);
x_522 = l_Lean_Meta_Grind_propagateForallPropDown___closed__5;
x_523 = lean_box(0);
x_524 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_524, 0, x_519);
lean_ctor_set(x_524, 1, x_523);
lean_inc_ref(x_524);
x_525 = l_Lean_mkConst(x_522, x_524);
x_526 = l_Lean_mkNot(x_497);
lean_inc_ref(x_496);
x_527 = l_Lean_mkLambda(x_495, x_498, x_496, x_526);
lean_inc_ref(x_496);
x_528 = l_Lean_mkAppB(x_525, x_496, x_527);
lean_inc_ref(x_16);
x_529 = l_Lean_mkOr(x_528, x_16);
x_530 = l_Lean_Meta_Grind_simpForall___closed__18;
x_531 = l_Lean_mkConst(x_530, x_524);
x_532 = l_Lean_mkApp3(x_531, x_496, x_521, x_16);
x_533 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_533, 0, x_532);
x_534 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_534, 0, x_529);
lean_ctor_set(x_534, 1, x_533);
lean_ctor_set_uint8(x_534, sizeof(void*)*2, x_464);
x_535 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_535, 0, x_534);
x_536 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_536, 0, x_535);
lean_ctor_set(x_536, 1, x_520);
return x_536;
}
}
else
{
uint8_t x_537; 
lean_dec_ref(x_497);
lean_dec_ref(x_496);
lean_dec(x_495);
lean_dec_ref(x_16);
x_537 = !lean_is_exclusive(x_501);
if (x_537 == 0)
{
return x_501;
}
else
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; 
x_538 = lean_ctor_get(x_501, 0);
x_539 = lean_ctor_get(x_501, 1);
lean_inc(x_539);
lean_inc(x_538);
lean_dec(x_501);
x_540 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_540, 0, x_538);
lean_ctor_set(x_540, 1, x_539);
return x_540;
}
}
}
}
}
else
{
lean_object* x_551; 
lean_inc_ref(x_16);
x_551 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_16, x_6, x_463);
if (lean_obj_tag(x_551) == 0)
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; uint8_t x_555; 
x_552 = lean_ctor_get(x_551, 0);
lean_inc(x_552);
x_553 = lean_ctor_get(x_551, 1);
lean_inc(x_553);
lean_dec_ref(x_551);
x_554 = l_Lean_Expr_cleanupAnnotations(x_552);
x_555 = l_Lean_Expr_isConstOf(x_554, x_491);
if (x_555 == 0)
{
uint8_t x_556; 
x_556 = l_Lean_Expr_isConstOf(x_554, x_493);
lean_dec_ref(x_554);
if (x_556 == 0)
{
lean_object* x_557; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_15);
x_557 = l_Lean_Meta_isProp(x_15, x_5, x_6, x_7, x_8, x_553);
if (lean_obj_tag(x_557) == 0)
{
lean_object* x_558; uint8_t x_559; 
x_558 = lean_ctor_get(x_557, 0);
lean_inc(x_558);
x_559 = lean_unbox(x_558);
lean_dec(x_558);
if (x_559 == 0)
{
x_465 = x_557;
goto block_489;
}
else
{
lean_object* x_560; lean_object* x_561; 
x_560 = lean_ctor_get(x_557, 1);
lean_inc(x_560);
lean_dec_ref(x_557);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_16);
lean_inc_ref(x_15);
x_561 = l_Lean_Meta_isExprDefEq(x_15, x_16, x_5, x_6, x_7, x_8, x_560);
x_465 = x_561;
goto block_489;
}
}
else
{
x_465 = x_557;
goto block_489;
}
}
else
{
lean_object* x_562; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_15);
x_562 = l_Lean_Meta_isProp(x_15, x_5, x_6, x_7, x_8, x_553);
if (lean_obj_tag(x_562) == 0)
{
lean_object* x_563; uint8_t x_564; 
x_563 = lean_ctor_get(x_562, 0);
lean_inc(x_563);
x_564 = lean_unbox(x_563);
lean_dec(x_563);
if (x_564 == 0)
{
lean_object* x_565; 
x_565 = lean_ctor_get(x_562, 1);
lean_inc(x_565);
lean_dec_ref(x_562);
x_447 = x_2;
x_448 = x_3;
x_449 = x_4;
x_450 = x_5;
x_451 = x_6;
x_452 = x_7;
x_453 = x_8;
x_454 = x_565;
goto block_459;
}
else
{
uint8_t x_566; 
lean_dec_ref(x_16);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_566 = !lean_is_exclusive(x_562);
if (x_566 == 0)
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; 
x_567 = lean_ctor_get(x_562, 0);
lean_dec(x_567);
x_568 = l_Lean_Meta_Grind_simpForall___closed__13;
x_569 = l_Lean_Meta_Grind_simpForall___closed__21;
x_570 = l_Lean_Expr_app___override(x_569, x_15);
x_571 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_571, 0, x_570);
x_572 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_572, 0, x_568);
lean_ctor_set(x_572, 1, x_571);
lean_ctor_set_uint8(x_572, sizeof(void*)*2, x_464);
x_573 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_573, 0, x_572);
lean_ctor_set(x_562, 0, x_573);
return x_562;
}
else
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; 
x_574 = lean_ctor_get(x_562, 1);
lean_inc(x_574);
lean_dec(x_562);
x_575 = l_Lean_Meta_Grind_simpForall___closed__13;
x_576 = l_Lean_Meta_Grind_simpForall___closed__21;
x_577 = l_Lean_Expr_app___override(x_576, x_15);
x_578 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_578, 0, x_577);
x_579 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_579, 0, x_575);
lean_ctor_set(x_579, 1, x_578);
lean_ctor_set_uint8(x_579, sizeof(void*)*2, x_464);
x_580 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_580, 0, x_579);
x_581 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_581, 0, x_580);
lean_ctor_set(x_581, 1, x_574);
return x_581;
}
}
}
else
{
uint8_t x_582; 
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_582 = !lean_is_exclusive(x_562);
if (x_582 == 0)
{
return x_562;
}
else
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; 
x_583 = lean_ctor_get(x_562, 0);
x_584 = lean_ctor_get(x_562, 1);
lean_inc(x_584);
lean_inc(x_583);
lean_dec(x_562);
x_585 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_585, 0, x_583);
lean_ctor_set(x_585, 1, x_584);
return x_585;
}
}
}
}
else
{
lean_object* x_586; 
lean_dec_ref(x_554);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_15);
x_586 = l_Lean_Meta_isProp(x_15, x_5, x_6, x_7, x_8, x_553);
if (lean_obj_tag(x_586) == 0)
{
lean_object* x_587; uint8_t x_588; 
x_587 = lean_ctor_get(x_586, 0);
lean_inc(x_587);
x_588 = lean_unbox(x_587);
lean_dec(x_587);
if (x_588 == 0)
{
lean_object* x_589; 
x_589 = lean_ctor_get(x_586, 1);
lean_inc(x_589);
lean_dec_ref(x_586);
x_447 = x_2;
x_448 = x_3;
x_449 = x_4;
x_450 = x_5;
x_451 = x_6;
x_452 = x_7;
x_453 = x_8;
x_454 = x_589;
goto block_459;
}
else
{
uint8_t x_590; 
lean_dec_ref(x_16);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_590 = !lean_is_exclusive(x_586);
if (x_590 == 0)
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; 
x_591 = lean_ctor_get(x_586, 0);
lean_dec(x_591);
lean_inc_ref(x_15);
x_592 = l_Lean_mkNot(x_15);
x_593 = l_Lean_Meta_Grind_simpForall___closed__24;
x_594 = l_Lean_Expr_app___override(x_593, x_15);
x_595 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_595, 0, x_594);
x_596 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_596, 0, x_592);
lean_ctor_set(x_596, 1, x_595);
lean_ctor_set_uint8(x_596, sizeof(void*)*2, x_464);
x_597 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_597, 0, x_596);
lean_ctor_set(x_586, 0, x_597);
return x_586;
}
else
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; 
x_598 = lean_ctor_get(x_586, 1);
lean_inc(x_598);
lean_dec(x_586);
lean_inc_ref(x_15);
x_599 = l_Lean_mkNot(x_15);
x_600 = l_Lean_Meta_Grind_simpForall___closed__24;
x_601 = l_Lean_Expr_app___override(x_600, x_15);
x_602 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_602, 0, x_601);
x_603 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_603, 0, x_599);
lean_ctor_set(x_603, 1, x_602);
lean_ctor_set_uint8(x_603, sizeof(void*)*2, x_464);
x_604 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_604, 0, x_603);
x_605 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_605, 0, x_604);
lean_ctor_set(x_605, 1, x_598);
return x_605;
}
}
}
else
{
uint8_t x_606; 
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_606 = !lean_is_exclusive(x_586);
if (x_606 == 0)
{
return x_586;
}
else
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; 
x_607 = lean_ctor_get(x_586, 0);
x_608 = lean_ctor_get(x_586, 1);
lean_inc(x_608);
lean_inc(x_607);
lean_dec(x_586);
x_609 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_609, 0, x_607);
lean_ctor_set(x_609, 1, x_608);
return x_609;
}
}
}
}
else
{
uint8_t x_610; 
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_610 = !lean_is_exclusive(x_551);
if (x_610 == 0)
{
return x_551;
}
else
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; 
x_611 = lean_ctor_get(x_551, 0);
x_612 = lean_ctor_get(x_551, 1);
lean_inc(x_612);
lean_inc(x_611);
lean_dec(x_551);
x_613 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_613, 0, x_611);
lean_ctor_set(x_613, 1, x_612);
return x_613;
}
}
}
}
else
{
lean_object* x_614; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_16);
x_614 = l_Lean_Meta_isProp(x_16, x_5, x_6, x_7, x_8, x_463);
if (lean_obj_tag(x_614) == 0)
{
lean_object* x_615; uint8_t x_616; 
x_615 = lean_ctor_get(x_614, 0);
lean_inc(x_615);
x_616 = lean_unbox(x_615);
lean_dec(x_615);
if (x_616 == 0)
{
lean_object* x_617; 
x_617 = lean_ctor_get(x_614, 1);
lean_inc(x_617);
lean_dec_ref(x_614);
x_447 = x_2;
x_448 = x_3;
x_449 = x_4;
x_450 = x_5;
x_451 = x_6;
x_452 = x_7;
x_453 = x_8;
x_454 = x_617;
goto block_459;
}
else
{
uint8_t x_618; 
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_618 = !lean_is_exclusive(x_614);
if (x_618 == 0)
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; 
x_619 = lean_ctor_get(x_614, 0);
lean_dec(x_619);
x_620 = l_Lean_Meta_Grind_simpForall___closed__27;
lean_inc_ref(x_16);
x_621 = l_Lean_Expr_app___override(x_620, x_16);
x_622 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_622, 0, x_621);
x_623 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_623, 0, x_16);
lean_ctor_set(x_623, 1, x_622);
lean_ctor_set_uint8(x_623, sizeof(void*)*2, x_464);
x_624 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_624, 0, x_623);
lean_ctor_set(x_614, 0, x_624);
return x_614;
}
else
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; 
x_625 = lean_ctor_get(x_614, 1);
lean_inc(x_625);
lean_dec(x_614);
x_626 = l_Lean_Meta_Grind_simpForall___closed__27;
lean_inc_ref(x_16);
x_627 = l_Lean_Expr_app___override(x_626, x_16);
x_628 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_628, 0, x_627);
x_629 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_629, 0, x_16);
lean_ctor_set(x_629, 1, x_628);
lean_ctor_set_uint8(x_629, sizeof(void*)*2, x_464);
x_630 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_630, 0, x_629);
x_631 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_631, 0, x_630);
lean_ctor_set(x_631, 1, x_625);
return x_631;
}
}
}
else
{
uint8_t x_632; 
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_632 = !lean_is_exclusive(x_614);
if (x_632 == 0)
{
return x_614;
}
else
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; 
x_633 = lean_ctor_get(x_614, 0);
x_634 = lean_ctor_get(x_614, 1);
lean_inc(x_634);
lean_inc(x_633);
lean_dec(x_614);
x_635 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_635, 0, x_633);
lean_ctor_set(x_635, 1, x_634);
return x_635;
}
}
}
}
else
{
lean_object* x_636; 
lean_dec_ref(x_490);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_16);
x_636 = l_Lean_Meta_isProp(x_16, x_5, x_6, x_7, x_8, x_463);
if (lean_obj_tag(x_636) == 0)
{
lean_object* x_637; uint8_t x_638; 
x_637 = lean_ctor_get(x_636, 0);
lean_inc(x_637);
x_638 = lean_unbox(x_637);
lean_dec(x_637);
if (x_638 == 0)
{
lean_object* x_639; 
x_639 = lean_ctor_get(x_636, 1);
lean_inc(x_639);
lean_dec_ref(x_636);
x_447 = x_2;
x_448 = x_3;
x_449 = x_4;
x_450 = x_5;
x_451 = x_6;
x_452 = x_7;
x_453 = x_8;
x_454 = x_639;
goto block_459;
}
else
{
uint8_t x_640; 
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_640 = !lean_is_exclusive(x_636);
if (x_640 == 0)
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; 
x_641 = lean_ctor_get(x_636, 0);
lean_dec(x_641);
x_642 = l_Lean_Meta_Grind_simpForall___closed__13;
x_643 = l_Lean_Meta_Grind_simpForall___closed__30;
x_644 = l_Lean_Expr_app___override(x_643, x_16);
x_645 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_645, 0, x_644);
x_646 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_646, 0, x_642);
lean_ctor_set(x_646, 1, x_645);
lean_ctor_set_uint8(x_646, sizeof(void*)*2, x_464);
x_647 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_647, 0, x_646);
lean_ctor_set(x_636, 0, x_647);
return x_636;
}
else
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; 
x_648 = lean_ctor_get(x_636, 1);
lean_inc(x_648);
lean_dec(x_636);
x_649 = l_Lean_Meta_Grind_simpForall___closed__13;
x_650 = l_Lean_Meta_Grind_simpForall___closed__30;
x_651 = l_Lean_Expr_app___override(x_650, x_16);
x_652 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_652, 0, x_651);
x_653 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_653, 0, x_649);
lean_ctor_set(x_653, 1, x_652);
lean_ctor_set_uint8(x_653, sizeof(void*)*2, x_464);
x_654 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_654, 0, x_653);
x_655 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_655, 0, x_654);
lean_ctor_set(x_655, 1, x_648);
return x_655;
}
}
}
else
{
uint8_t x_656; 
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_656 = !lean_is_exclusive(x_636);
if (x_656 == 0)
{
return x_636;
}
else
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; 
x_657 = lean_ctor_get(x_636, 0);
x_658 = lean_ctor_get(x_636, 1);
lean_inc(x_658);
lean_inc(x_657);
lean_dec(x_636);
x_659 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_659, 0, x_657);
lean_ctor_set(x_659, 1, x_658);
return x_659;
}
}
}
block_489:
{
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; uint8_t x_467; 
x_466 = lean_ctor_get(x_465, 0);
x_467 = lean_unbox(x_466);
if (x_467 == 0)
{
lean_object* x_468; 
x_468 = lean_ctor_get(x_465, 1);
lean_inc(x_468);
lean_dec_ref(x_465);
x_447 = x_2;
x_448 = x_3;
x_449 = x_4;
x_450 = x_5;
x_451 = x_6;
x_452 = x_7;
x_453 = x_8;
x_454 = x_468;
goto block_459;
}
else
{
uint8_t x_469; 
lean_dec_ref(x_16);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_469 = !lean_is_exclusive(x_465);
if (x_469 == 0)
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; 
x_470 = lean_ctor_get(x_465, 0);
lean_dec(x_470);
x_471 = l_Lean_Meta_Grind_simpForall___closed__13;
x_472 = l_Lean_Meta_Grind_simpForall___closed__16;
x_473 = l_Lean_Expr_app___override(x_472, x_15);
x_474 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_474, 0, x_473);
x_475 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_475, 0, x_471);
lean_ctor_set(x_475, 1, x_474);
lean_ctor_set_uint8(x_475, sizeof(void*)*2, x_464);
x_476 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_476, 0, x_475);
lean_ctor_set(x_465, 0, x_476);
return x_465;
}
else
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; 
x_477 = lean_ctor_get(x_465, 1);
lean_inc(x_477);
lean_dec(x_465);
x_478 = l_Lean_Meta_Grind_simpForall___closed__13;
x_479 = l_Lean_Meta_Grind_simpForall___closed__16;
x_480 = l_Lean_Expr_app___override(x_479, x_15);
x_481 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_481, 0, x_480);
x_482 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_482, 0, x_478);
lean_ctor_set(x_482, 1, x_481);
lean_ctor_set_uint8(x_482, sizeof(void*)*2, x_464);
x_483 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_483, 0, x_482);
x_484 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_484, 0, x_483);
lean_ctor_set(x_484, 1, x_477);
return x_484;
}
}
}
else
{
uint8_t x_485; 
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_485 = !lean_is_exclusive(x_465);
if (x_485 == 0)
{
return x_465;
}
else
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; 
x_486 = lean_ctor_get(x_465, 0);
x_487 = lean_ctor_get(x_465, 1);
lean_inc(x_487);
lean_inc(x_486);
lean_dec(x_465);
x_488 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_488, 0, x_486);
lean_ctor_set(x_488, 1, x_487);
return x_488;
}
}
}
}
else
{
uint8_t x_660; 
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_660 = !lean_is_exclusive(x_461);
if (x_660 == 0)
{
return x_461;
}
else
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; 
x_661 = lean_ctor_get(x_461, 0);
x_662 = lean_ctor_get(x_461, 1);
lean_inc(x_662);
lean_inc(x_661);
lean_dec(x_461);
x_663 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_663, 0, x_661);
lean_ctor_set(x_663, 1, x_662);
return x_663;
}
}
}
else
{
lean_object* x_664; 
lean_inc_ref(x_15);
x_664 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_15, x_6, x_9);
if (lean_obj_tag(x_664) == 0)
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; uint8_t x_669; 
x_665 = lean_ctor_get(x_664, 0);
lean_inc(x_665);
x_666 = lean_ctor_get(x_664, 1);
lean_inc(x_666);
lean_dec_ref(x_664);
x_667 = l_Lean_Expr_cleanupAnnotations(x_665);
x_668 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__3;
x_669 = l_Lean_Expr_isConstOf(x_667, x_668);
if (x_669 == 0)
{
lean_object* x_670; uint8_t x_671; 
x_670 = l_Lean_Meta_Grind_simpForall___closed__12;
x_671 = l_Lean_Expr_isConstOf(x_667, x_670);
lean_dec_ref(x_667);
if (x_671 == 0)
{
x_447 = x_2;
x_448 = x_3;
x_449 = x_4;
x_450 = x_5;
x_451 = x_6;
x_452 = x_7;
x_453 = x_8;
x_454 = x_666;
goto block_459;
}
else
{
lean_object* x_672; lean_object* x_673; lean_object* x_674; 
x_672 = l_Lean_Meta_Grind_simpForall___closed__33;
x_673 = lean_expr_instantiate1(x_16, x_672);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_673);
x_674 = l_Lean_Meta_isProp(x_673, x_5, x_6, x_7, x_8, x_666);
if (lean_obj_tag(x_674) == 0)
{
lean_object* x_675; uint8_t x_676; 
x_675 = lean_ctor_get(x_674, 0);
lean_inc(x_675);
x_676 = lean_unbox(x_675);
lean_dec(x_675);
if (x_676 == 0)
{
lean_object* x_677; 
lean_dec_ref(x_673);
x_677 = lean_ctor_get(x_674, 1);
lean_inc(x_677);
lean_dec_ref(x_674);
x_447 = x_2;
x_448 = x_3;
x_449 = x_4;
x_450 = x_5;
x_451 = x_6;
x_452 = x_7;
x_453 = x_8;
x_454 = x_677;
goto block_459;
}
else
{
uint8_t x_678; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_678 = !lean_is_exclusive(x_674);
if (x_678 == 0)
{
lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; 
x_679 = lean_ctor_get(x_674, 0);
lean_dec(x_679);
x_680 = l_Lean_mkLambda(x_14, x_17, x_15, x_16);
x_681 = l_Lean_Meta_Grind_simpForall___closed__36;
x_682 = l_Lean_Expr_app___override(x_681, x_680);
x_683 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_683, 0, x_682);
x_684 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_684, 0, x_673);
lean_ctor_set(x_684, 1, x_683);
lean_ctor_set_uint8(x_684, sizeof(void*)*2, x_460);
x_685 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_685, 0, x_684);
lean_ctor_set(x_674, 0, x_685);
return x_674;
}
else
{
lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; 
x_686 = lean_ctor_get(x_674, 1);
lean_inc(x_686);
lean_dec(x_674);
x_687 = l_Lean_mkLambda(x_14, x_17, x_15, x_16);
x_688 = l_Lean_Meta_Grind_simpForall___closed__36;
x_689 = l_Lean_Expr_app___override(x_688, x_687);
x_690 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_690, 0, x_689);
x_691 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_691, 0, x_673);
lean_ctor_set(x_691, 1, x_690);
lean_ctor_set_uint8(x_691, sizeof(void*)*2, x_460);
x_692 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_692, 0, x_691);
x_693 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_693, 0, x_692);
lean_ctor_set(x_693, 1, x_686);
return x_693;
}
}
}
else
{
uint8_t x_694; 
lean_dec_ref(x_673);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_694 = !lean_is_exclusive(x_674);
if (x_694 == 0)
{
return x_674;
}
else
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; 
x_695 = lean_ctor_get(x_674, 0);
x_696 = lean_ctor_get(x_674, 1);
lean_inc(x_696);
lean_inc(x_695);
lean_dec(x_674);
x_697 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_697, 0, x_695);
lean_ctor_set(x_697, 1, x_696);
return x_697;
}
}
}
}
else
{
lean_object* x_698; lean_object* x_699; 
lean_dec_ref(x_667);
lean_inc_ref(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
x_698 = l_Lean_mkLambda(x_14, x_17, x_15, x_16);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_698);
x_699 = lean_infer_type(x_698, x_5, x_6, x_7, x_8, x_666);
if (lean_obj_tag(x_699) == 0)
{
lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; 
x_700 = lean_ctor_get(x_699, 0);
lean_inc(x_700);
x_701 = lean_ctor_get(x_699, 1);
lean_inc(x_701);
lean_dec_ref(x_699);
x_702 = l_Lean_Meta_Grind_simpForall___closed__38;
lean_inc_ref(x_15);
lean_inc(x_14);
x_703 = l_Lean_mkForall(x_14, x_17, x_15, x_702);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_704 = l_Lean_Meta_isExprDefEq(x_700, x_703, x_5, x_6, x_7, x_8, x_701);
if (lean_obj_tag(x_704) == 0)
{
lean_object* x_705; uint8_t x_706; 
x_705 = lean_ctor_get(x_704, 0);
lean_inc(x_705);
x_706 = lean_unbox(x_705);
lean_dec(x_705);
if (x_706 == 0)
{
lean_object* x_707; 
lean_dec_ref(x_698);
x_707 = lean_ctor_get(x_704, 1);
lean_inc(x_707);
lean_dec_ref(x_704);
x_447 = x_2;
x_448 = x_3;
x_449 = x_4;
x_450 = x_5;
x_451 = x_6;
x_452 = x_7;
x_453 = x_8;
x_454 = x_707;
goto block_459;
}
else
{
uint8_t x_708; 
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_708 = !lean_is_exclusive(x_704);
if (x_708 == 0)
{
lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; 
x_709 = lean_ctor_get(x_704, 0);
lean_dec(x_709);
x_710 = l_Lean_Meta_Grind_simpForall___closed__13;
x_711 = l_Lean_Meta_Grind_simpForall___closed__41;
x_712 = l_Lean_Expr_app___override(x_711, x_698);
x_713 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_713, 0, x_712);
x_714 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_714, 0, x_710);
lean_ctor_set(x_714, 1, x_713);
lean_ctor_set_uint8(x_714, sizeof(void*)*2, x_460);
x_715 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_715, 0, x_714);
lean_ctor_set(x_704, 0, x_715);
return x_704;
}
else
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; 
x_716 = lean_ctor_get(x_704, 1);
lean_inc(x_716);
lean_dec(x_704);
x_717 = l_Lean_Meta_Grind_simpForall___closed__13;
x_718 = l_Lean_Meta_Grind_simpForall___closed__41;
x_719 = l_Lean_Expr_app___override(x_718, x_698);
x_720 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_720, 0, x_719);
x_721 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_721, 0, x_717);
lean_ctor_set(x_721, 1, x_720);
lean_ctor_set_uint8(x_721, sizeof(void*)*2, x_460);
x_722 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_722, 0, x_721);
x_723 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_723, 0, x_722);
lean_ctor_set(x_723, 1, x_716);
return x_723;
}
}
}
else
{
uint8_t x_724; 
lean_dec_ref(x_698);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_724 = !lean_is_exclusive(x_704);
if (x_724 == 0)
{
return x_704;
}
else
{
lean_object* x_725; lean_object* x_726; lean_object* x_727; 
x_725 = lean_ctor_get(x_704, 0);
x_726 = lean_ctor_get(x_704, 1);
lean_inc(x_726);
lean_inc(x_725);
lean_dec(x_704);
x_727 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_727, 0, x_725);
lean_ctor_set(x_727, 1, x_726);
return x_727;
}
}
}
else
{
uint8_t x_728; 
lean_dec_ref(x_698);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_728 = !lean_is_exclusive(x_699);
if (x_728 == 0)
{
return x_699;
}
else
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; 
x_729 = lean_ctor_get(x_699, 0);
x_730 = lean_ctor_get(x_699, 1);
lean_inc(x_730);
lean_inc(x_729);
lean_dec(x_699);
x_731 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_731, 0, x_729);
lean_ctor_set(x_731, 1, x_730);
return x_731;
}
}
}
}
else
{
uint8_t x_732; 
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_732 = !lean_is_exclusive(x_664);
if (x_732 == 0)
{
return x_664;
}
else
{
lean_object* x_733; lean_object* x_734; lean_object* x_735; 
x_733 = lean_ctor_get(x_664, 0);
x_734 = lean_ctor_get(x_664, 1);
lean_inc(x_734);
lean_inc(x_733);
lean_dec(x_664);
x_735 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_735, 0, x_733);
lean_ctor_set(x_735, 1, x_734);
return x_735;
}
}
}
block_446:
{
if (x_26 == 0)
{
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_18);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
x_10 = x_19;
goto block_13;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = l_Lean_Expr_appFn_x21(x_16);
x_28 = l_Lean_Expr_appFn_x21(x_27);
if (lean_obj_tag(x_28) == 4)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = l_Lean_Meta_Grind_simpForall___closed__2;
x_31 = lean_name_eq(x_29, x_30);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; 
lean_dec(x_25);
lean_dec_ref(x_22);
lean_dec(x_20);
x_32 = l_Lean_Meta_Grind_simpForall___closed__4;
x_33 = lean_name_eq(x_29, x_32);
lean_dec(x_29);
if (x_33 == 0)
{
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec(x_21);
lean_dec_ref(x_18);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
x_10 = x_19;
goto block_13;
}
else
{
lean_object* x_34; 
lean_inc_ref(x_15);
x_34 = l_Lean_Meta_getLevel(x_15, x_24, x_23, x_18, x_21, x_19);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = l_Lean_Expr_appArg_x21(x_27);
lean_dec_ref(x_27);
x_38 = l_Lean_Expr_appArg_x21(x_16);
lean_dec_ref(x_16);
lean_inc_ref(x_37);
lean_inc_ref(x_15);
lean_inc(x_14);
x_39 = l_Lean_mkLambda(x_14, x_17, x_15, x_37);
lean_inc_ref(x_38);
lean_inc_ref(x_15);
lean_inc(x_14);
x_40 = l_Lean_mkLambda(x_14, x_17, x_15, x_38);
lean_inc_ref(x_15);
lean_inc(x_14);
x_41 = l_Lean_mkForall(x_14, x_17, x_15, x_37);
lean_inc_ref(x_15);
x_42 = l_Lean_mkForall(x_14, x_17, x_15, x_38);
x_43 = l_Lean_mkAnd(x_41, x_42);
x_44 = l_Lean_Meta_Grind_simpForall___closed__6;
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_36);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_mkConst(x_44, x_46);
x_48 = l_Lean_mkApp3(x_47, x_15, x_39, x_40);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_50, 0, x_43);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*2, x_26);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_34, 0, x_51);
return x_34;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_52 = lean_ctor_get(x_34, 0);
x_53 = lean_ctor_get(x_34, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_34);
x_54 = l_Lean_Expr_appArg_x21(x_27);
lean_dec_ref(x_27);
x_55 = l_Lean_Expr_appArg_x21(x_16);
lean_dec_ref(x_16);
lean_inc_ref(x_54);
lean_inc_ref(x_15);
lean_inc(x_14);
x_56 = l_Lean_mkLambda(x_14, x_17, x_15, x_54);
lean_inc_ref(x_55);
lean_inc_ref(x_15);
lean_inc(x_14);
x_57 = l_Lean_mkLambda(x_14, x_17, x_15, x_55);
lean_inc_ref(x_15);
lean_inc(x_14);
x_58 = l_Lean_mkForall(x_14, x_17, x_15, x_54);
lean_inc_ref(x_15);
x_59 = l_Lean_mkForall(x_14, x_17, x_15, x_55);
x_60 = l_Lean_mkAnd(x_58, x_59);
x_61 = l_Lean_Meta_Grind_simpForall___closed__6;
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_52);
lean_ctor_set(x_63, 1, x_62);
x_64 = l_Lean_mkConst(x_61, x_63);
x_65 = l_Lean_mkApp3(x_64, x_15, x_56, x_57);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_67, 0, x_60);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set_uint8(x_67, sizeof(void*)*2, x_26);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_53);
return x_69;
}
}
else
{
uint8_t x_70; 
lean_dec_ref(x_27);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
x_70 = !lean_is_exclusive(x_34);
if (x_70 == 0)
{
return x_34;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_34, 0);
x_72 = lean_ctor_get(x_34, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_34);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_29);
x_74 = l_Lean_Expr_appArg_x21(x_27);
lean_dec_ref(x_27);
x_75 = l_Lean_Expr_appArg_x21(x_16);
lean_dec_ref(x_16);
x_76 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f(x_74);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; 
x_77 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f(x_75);
lean_dec_ref(x_75);
if (lean_obj_tag(x_77) == 0)
{
lean_dec_ref(x_74);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_18);
lean_dec_ref(x_15);
lean_dec(x_14);
x_10 = x_19;
goto block_13;
}
else
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_ctor_get(x_77, 0);
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_ctor_get(x_79, 1);
x_82 = !lean_is_exclusive(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_79, 0);
x_84 = lean_ctor_get(x_81, 0);
x_85 = lean_ctor_get(x_81, 1);
lean_inc(x_21);
lean_inc_ref(x_18);
lean_inc(x_23);
lean_inc_ref(x_24);
lean_inc_ref(x_15);
x_86 = l_Lean_Meta_getLevel(x_15, x_24, x_23, x_18, x_21, x_19);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec_ref(x_86);
lean_inc(x_84);
x_89 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpForall___lam__0___boxed), 10, 1);
lean_closure_set(x_89, 0, x_84);
lean_inc_ref(x_15);
lean_inc(x_14);
x_90 = l_Lean_Meta_withLocalDeclD___at___Lean_Meta_Grind_simpForall_spec__0___redArg(x_14, x_15, x_89, x_25, x_22, x_20, x_24, x_23, x_18, x_21, x_88);
if (lean_obj_tag(x_90) == 0)
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_92 = lean_ctor_get(x_90, 0);
lean_inc_ref(x_74);
lean_inc_ref(x_15);
lean_inc(x_14);
x_93 = l_Lean_mkLambda(x_14, x_17, x_15, x_74);
x_94 = 0;
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
x_95 = l_Lean_mkLambda(x_83, x_94, x_84, x_85);
lean_inc_ref(x_15);
lean_inc(x_14);
x_96 = l_Lean_mkLambda(x_14, x_17, x_15, x_95);
lean_inc(x_84);
lean_inc_ref(x_15);
lean_inc(x_14);
x_97 = l_Lean_mkLambda(x_14, x_17, x_15, x_84);
x_98 = lean_unsigned_to_nat(0u);
x_99 = lean_unsigned_to_nat(1u);
x_100 = lean_expr_lift_loose_bvars(x_74, x_98, x_99);
lean_dec_ref(x_74);
x_101 = l_Lean_mkOr(x_100, x_85);
x_102 = l_Lean_mkForall(x_83, x_94, x_84, x_101);
lean_inc_ref(x_15);
x_103 = l_Lean_mkForall(x_14, x_17, x_15, x_102);
x_104 = l_Lean_Meta_Grind_simpForall___closed__8;
x_105 = lean_box(0);
lean_ctor_set_tag(x_81, 1);
lean_ctor_set(x_81, 1, x_105);
lean_ctor_set(x_81, 0, x_92);
lean_ctor_set_tag(x_79, 1);
lean_ctor_set(x_79, 0, x_87);
x_106 = l_Lean_mkConst(x_104, x_79);
x_107 = l_Lean_mkApp4(x_106, x_15, x_97, x_93, x_96);
lean_ctor_set(x_77, 0, x_107);
x_108 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_108, 0, x_103);
lean_ctor_set(x_108, 1, x_77);
lean_ctor_set_uint8(x_108, sizeof(void*)*2, x_26);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_90, 0, x_109);
return x_90;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_110 = lean_ctor_get(x_90, 0);
x_111 = lean_ctor_get(x_90, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_90);
lean_inc_ref(x_74);
lean_inc_ref(x_15);
lean_inc(x_14);
x_112 = l_Lean_mkLambda(x_14, x_17, x_15, x_74);
x_113 = 0;
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
x_114 = l_Lean_mkLambda(x_83, x_113, x_84, x_85);
lean_inc_ref(x_15);
lean_inc(x_14);
x_115 = l_Lean_mkLambda(x_14, x_17, x_15, x_114);
lean_inc(x_84);
lean_inc_ref(x_15);
lean_inc(x_14);
x_116 = l_Lean_mkLambda(x_14, x_17, x_15, x_84);
x_117 = lean_unsigned_to_nat(0u);
x_118 = lean_unsigned_to_nat(1u);
x_119 = lean_expr_lift_loose_bvars(x_74, x_117, x_118);
lean_dec_ref(x_74);
x_120 = l_Lean_mkOr(x_119, x_85);
x_121 = l_Lean_mkForall(x_83, x_113, x_84, x_120);
lean_inc_ref(x_15);
x_122 = l_Lean_mkForall(x_14, x_17, x_15, x_121);
x_123 = l_Lean_Meta_Grind_simpForall___closed__8;
x_124 = lean_box(0);
lean_ctor_set_tag(x_81, 1);
lean_ctor_set(x_81, 1, x_124);
lean_ctor_set(x_81, 0, x_110);
lean_ctor_set_tag(x_79, 1);
lean_ctor_set(x_79, 0, x_87);
x_125 = l_Lean_mkConst(x_123, x_79);
x_126 = l_Lean_mkApp4(x_125, x_15, x_116, x_112, x_115);
lean_ctor_set(x_77, 0, x_126);
x_127 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_127, 0, x_122);
lean_ctor_set(x_127, 1, x_77);
lean_ctor_set_uint8(x_127, sizeof(void*)*2, x_26);
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_127);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_111);
return x_129;
}
}
else
{
uint8_t x_130; 
lean_dec(x_87);
lean_free_object(x_81);
lean_dec(x_85);
lean_dec(x_84);
lean_free_object(x_79);
lean_dec(x_83);
lean_free_object(x_77);
lean_dec_ref(x_74);
lean_dec_ref(x_15);
lean_dec(x_14);
x_130 = !lean_is_exclusive(x_90);
if (x_130 == 0)
{
return x_90;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_90, 0);
x_132 = lean_ctor_get(x_90, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_90);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
else
{
uint8_t x_134; 
lean_free_object(x_81);
lean_dec(x_85);
lean_dec(x_84);
lean_free_object(x_79);
lean_dec(x_83);
lean_free_object(x_77);
lean_dec_ref(x_74);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_18);
lean_dec_ref(x_15);
lean_dec(x_14);
x_134 = !lean_is_exclusive(x_86);
if (x_134 == 0)
{
return x_86;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_86, 0);
x_136 = lean_ctor_get(x_86, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_86);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_138 = lean_ctor_get(x_79, 0);
x_139 = lean_ctor_get(x_81, 0);
x_140 = lean_ctor_get(x_81, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_81);
lean_inc(x_21);
lean_inc_ref(x_18);
lean_inc(x_23);
lean_inc_ref(x_24);
lean_inc_ref(x_15);
x_141 = l_Lean_Meta_getLevel(x_15, x_24, x_23, x_18, x_21, x_19);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_141, 1);
lean_inc(x_143);
lean_dec_ref(x_141);
lean_inc(x_139);
x_144 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpForall___lam__0___boxed), 10, 1);
lean_closure_set(x_144, 0, x_139);
lean_inc_ref(x_15);
lean_inc(x_14);
x_145 = l_Lean_Meta_withLocalDeclD___at___Lean_Meta_Grind_simpForall_spec__0___redArg(x_14, x_15, x_144, x_25, x_22, x_20, x_24, x_23, x_18, x_21, x_143);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_148 = x_145;
} else {
 lean_dec_ref(x_145);
 x_148 = lean_box(0);
}
lean_inc_ref(x_74);
lean_inc_ref(x_15);
lean_inc(x_14);
x_149 = l_Lean_mkLambda(x_14, x_17, x_15, x_74);
x_150 = 0;
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
x_151 = l_Lean_mkLambda(x_138, x_150, x_139, x_140);
lean_inc_ref(x_15);
lean_inc(x_14);
x_152 = l_Lean_mkLambda(x_14, x_17, x_15, x_151);
lean_inc(x_139);
lean_inc_ref(x_15);
lean_inc(x_14);
x_153 = l_Lean_mkLambda(x_14, x_17, x_15, x_139);
x_154 = lean_unsigned_to_nat(0u);
x_155 = lean_unsigned_to_nat(1u);
x_156 = lean_expr_lift_loose_bvars(x_74, x_154, x_155);
lean_dec_ref(x_74);
x_157 = l_Lean_mkOr(x_156, x_140);
x_158 = l_Lean_mkForall(x_138, x_150, x_139, x_157);
lean_inc_ref(x_15);
x_159 = l_Lean_mkForall(x_14, x_17, x_15, x_158);
x_160 = l_Lean_Meta_Grind_simpForall___closed__8;
x_161 = lean_box(0);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_146);
lean_ctor_set(x_162, 1, x_161);
lean_ctor_set_tag(x_79, 1);
lean_ctor_set(x_79, 1, x_162);
lean_ctor_set(x_79, 0, x_142);
x_163 = l_Lean_mkConst(x_160, x_79);
x_164 = l_Lean_mkApp4(x_163, x_15, x_153, x_149, x_152);
lean_ctor_set(x_77, 0, x_164);
x_165 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_165, 0, x_159);
lean_ctor_set(x_165, 1, x_77);
lean_ctor_set_uint8(x_165, sizeof(void*)*2, x_26);
x_166 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_166, 0, x_165);
if (lean_is_scalar(x_148)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_148;
}
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_147);
return x_167;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_142);
lean_dec(x_140);
lean_dec(x_139);
lean_free_object(x_79);
lean_dec(x_138);
lean_free_object(x_77);
lean_dec_ref(x_74);
lean_dec_ref(x_15);
lean_dec(x_14);
x_168 = lean_ctor_get(x_145, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_145, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_170 = x_145;
} else {
 lean_dec_ref(x_145);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 2, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_168);
lean_ctor_set(x_171, 1, x_169);
return x_171;
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_140);
lean_dec(x_139);
lean_free_object(x_79);
lean_dec(x_138);
lean_free_object(x_77);
lean_dec_ref(x_74);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_18);
lean_dec_ref(x_15);
lean_dec(x_14);
x_172 = lean_ctor_get(x_141, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_141, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_174 = x_141;
} else {
 lean_dec_ref(x_141);
 x_174 = lean_box(0);
}
if (lean_is_scalar(x_174)) {
 x_175 = lean_alloc_ctor(1, 2, 0);
} else {
 x_175 = x_174;
}
lean_ctor_set(x_175, 0, x_172);
lean_ctor_set(x_175, 1, x_173);
return x_175;
}
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_176 = lean_ctor_get(x_79, 1);
x_177 = lean_ctor_get(x_79, 0);
lean_inc(x_176);
lean_inc(x_177);
lean_dec(x_79);
x_178 = lean_ctor_get(x_176, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_176, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_180 = x_176;
} else {
 lean_dec_ref(x_176);
 x_180 = lean_box(0);
}
lean_inc(x_21);
lean_inc_ref(x_18);
lean_inc(x_23);
lean_inc_ref(x_24);
lean_inc_ref(x_15);
x_181 = l_Lean_Meta_getLevel(x_15, x_24, x_23, x_18, x_21, x_19);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec_ref(x_181);
lean_inc(x_178);
x_184 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpForall___lam__0___boxed), 10, 1);
lean_closure_set(x_184, 0, x_178);
lean_inc_ref(x_15);
lean_inc(x_14);
x_185 = l_Lean_Meta_withLocalDeclD___at___Lean_Meta_Grind_simpForall_spec__0___redArg(x_14, x_15, x_184, x_25, x_22, x_20, x_24, x_23, x_18, x_21, x_183);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_188 = x_185;
} else {
 lean_dec_ref(x_185);
 x_188 = lean_box(0);
}
lean_inc_ref(x_74);
lean_inc_ref(x_15);
lean_inc(x_14);
x_189 = l_Lean_mkLambda(x_14, x_17, x_15, x_74);
x_190 = 0;
lean_inc(x_179);
lean_inc(x_178);
lean_inc(x_177);
x_191 = l_Lean_mkLambda(x_177, x_190, x_178, x_179);
lean_inc_ref(x_15);
lean_inc(x_14);
x_192 = l_Lean_mkLambda(x_14, x_17, x_15, x_191);
lean_inc(x_178);
lean_inc_ref(x_15);
lean_inc(x_14);
x_193 = l_Lean_mkLambda(x_14, x_17, x_15, x_178);
x_194 = lean_unsigned_to_nat(0u);
x_195 = lean_unsigned_to_nat(1u);
x_196 = lean_expr_lift_loose_bvars(x_74, x_194, x_195);
lean_dec_ref(x_74);
x_197 = l_Lean_mkOr(x_196, x_179);
x_198 = l_Lean_mkForall(x_177, x_190, x_178, x_197);
lean_inc_ref(x_15);
x_199 = l_Lean_mkForall(x_14, x_17, x_15, x_198);
x_200 = l_Lean_Meta_Grind_simpForall___closed__8;
x_201 = lean_box(0);
if (lean_is_scalar(x_180)) {
 x_202 = lean_alloc_ctor(1, 2, 0);
} else {
 x_202 = x_180;
 lean_ctor_set_tag(x_202, 1);
}
lean_ctor_set(x_202, 0, x_186);
lean_ctor_set(x_202, 1, x_201);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_182);
lean_ctor_set(x_203, 1, x_202);
x_204 = l_Lean_mkConst(x_200, x_203);
x_205 = l_Lean_mkApp4(x_204, x_15, x_193, x_189, x_192);
lean_ctor_set(x_77, 0, x_205);
x_206 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_206, 0, x_199);
lean_ctor_set(x_206, 1, x_77);
lean_ctor_set_uint8(x_206, sizeof(void*)*2, x_26);
x_207 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_207, 0, x_206);
if (lean_is_scalar(x_188)) {
 x_208 = lean_alloc_ctor(0, 2, 0);
} else {
 x_208 = x_188;
}
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_187);
return x_208;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_182);
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_177);
lean_free_object(x_77);
lean_dec_ref(x_74);
lean_dec_ref(x_15);
lean_dec(x_14);
x_209 = lean_ctor_get(x_185, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_185, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_211 = x_185;
} else {
 lean_dec_ref(x_185);
 x_211 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_212 = lean_alloc_ctor(1, 2, 0);
} else {
 x_212 = x_211;
}
lean_ctor_set(x_212, 0, x_209);
lean_ctor_set(x_212, 1, x_210);
return x_212;
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_177);
lean_free_object(x_77);
lean_dec_ref(x_74);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_18);
lean_dec_ref(x_15);
lean_dec(x_14);
x_213 = lean_ctor_get(x_181, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_181, 1);
lean_inc(x_214);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_215 = x_181;
} else {
 lean_dec_ref(x_181);
 x_215 = lean_box(0);
}
if (lean_is_scalar(x_215)) {
 x_216 = lean_alloc_ctor(1, 2, 0);
} else {
 x_216 = x_215;
}
lean_ctor_set(x_216, 0, x_213);
lean_ctor_set(x_216, 1, x_214);
return x_216;
}
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_217 = lean_ctor_get(x_77, 0);
lean_inc(x_217);
lean_dec(x_77);
x_218 = lean_ctor_get(x_217, 1);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 0);
lean_inc(x_219);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 x_220 = x_217;
} else {
 lean_dec_ref(x_217);
 x_220 = lean_box(0);
}
x_221 = lean_ctor_get(x_218, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_218, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_223 = x_218;
} else {
 lean_dec_ref(x_218);
 x_223 = lean_box(0);
}
lean_inc(x_21);
lean_inc_ref(x_18);
lean_inc(x_23);
lean_inc_ref(x_24);
lean_inc_ref(x_15);
x_224 = l_Lean_Meta_getLevel(x_15, x_24, x_23, x_18, x_21, x_19);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
lean_dec_ref(x_224);
lean_inc(x_221);
x_227 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpForall___lam__0___boxed), 10, 1);
lean_closure_set(x_227, 0, x_221);
lean_inc_ref(x_15);
lean_inc(x_14);
x_228 = l_Lean_Meta_withLocalDeclD___at___Lean_Meta_Grind_simpForall_spec__0___redArg(x_14, x_15, x_227, x_25, x_22, x_20, x_24, x_23, x_18, x_21, x_226);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_231 = x_228;
} else {
 lean_dec_ref(x_228);
 x_231 = lean_box(0);
}
lean_inc_ref(x_74);
lean_inc_ref(x_15);
lean_inc(x_14);
x_232 = l_Lean_mkLambda(x_14, x_17, x_15, x_74);
x_233 = 0;
lean_inc(x_222);
lean_inc(x_221);
lean_inc(x_219);
x_234 = l_Lean_mkLambda(x_219, x_233, x_221, x_222);
lean_inc_ref(x_15);
lean_inc(x_14);
x_235 = l_Lean_mkLambda(x_14, x_17, x_15, x_234);
lean_inc(x_221);
lean_inc_ref(x_15);
lean_inc(x_14);
x_236 = l_Lean_mkLambda(x_14, x_17, x_15, x_221);
x_237 = lean_unsigned_to_nat(0u);
x_238 = lean_unsigned_to_nat(1u);
x_239 = lean_expr_lift_loose_bvars(x_74, x_237, x_238);
lean_dec_ref(x_74);
x_240 = l_Lean_mkOr(x_239, x_222);
x_241 = l_Lean_mkForall(x_219, x_233, x_221, x_240);
lean_inc_ref(x_15);
x_242 = l_Lean_mkForall(x_14, x_17, x_15, x_241);
x_243 = l_Lean_Meta_Grind_simpForall___closed__8;
x_244 = lean_box(0);
if (lean_is_scalar(x_223)) {
 x_245 = lean_alloc_ctor(1, 2, 0);
} else {
 x_245 = x_223;
 lean_ctor_set_tag(x_245, 1);
}
lean_ctor_set(x_245, 0, x_229);
lean_ctor_set(x_245, 1, x_244);
if (lean_is_scalar(x_220)) {
 x_246 = lean_alloc_ctor(1, 2, 0);
} else {
 x_246 = x_220;
 lean_ctor_set_tag(x_246, 1);
}
lean_ctor_set(x_246, 0, x_225);
lean_ctor_set(x_246, 1, x_245);
x_247 = l_Lean_mkConst(x_243, x_246);
x_248 = l_Lean_mkApp4(x_247, x_15, x_236, x_232, x_235);
x_249 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_249, 0, x_248);
x_250 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_250, 0, x_242);
lean_ctor_set(x_250, 1, x_249);
lean_ctor_set_uint8(x_250, sizeof(void*)*2, x_26);
x_251 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_251, 0, x_250);
if (lean_is_scalar(x_231)) {
 x_252 = lean_alloc_ctor(0, 2, 0);
} else {
 x_252 = x_231;
}
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_230);
return x_252;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_225);
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_219);
lean_dec_ref(x_74);
lean_dec_ref(x_15);
lean_dec(x_14);
x_253 = lean_ctor_get(x_228, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_228, 1);
lean_inc(x_254);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_255 = x_228;
} else {
 lean_dec_ref(x_228);
 x_255 = lean_box(0);
}
if (lean_is_scalar(x_255)) {
 x_256 = lean_alloc_ctor(1, 2, 0);
} else {
 x_256 = x_255;
}
lean_ctor_set(x_256, 0, x_253);
lean_ctor_set(x_256, 1, x_254);
return x_256;
}
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_219);
lean_dec_ref(x_74);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_18);
lean_dec_ref(x_15);
lean_dec(x_14);
x_257 = lean_ctor_get(x_224, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_224, 1);
lean_inc(x_258);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_259 = x_224;
} else {
 lean_dec_ref(x_224);
 x_259 = lean_box(0);
}
if (lean_is_scalar(x_259)) {
 x_260 = lean_alloc_ctor(1, 2, 0);
} else {
 x_260 = x_259;
}
lean_ctor_set(x_260, 0, x_257);
lean_ctor_set(x_260, 1, x_258);
return x_260;
}
}
}
}
else
{
uint8_t x_261; 
lean_dec_ref(x_74);
x_261 = !lean_is_exclusive(x_76);
if (x_261 == 0)
{
lean_object* x_262; uint8_t x_263; 
x_262 = lean_ctor_get(x_76, 0);
x_263 = !lean_is_exclusive(x_262);
if (x_263 == 0)
{
lean_object* x_264; uint8_t x_265; 
x_264 = lean_ctor_get(x_262, 1);
x_265 = !lean_is_exclusive(x_264);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_266 = lean_ctor_get(x_262, 0);
x_267 = lean_ctor_get(x_264, 0);
x_268 = lean_ctor_get(x_264, 1);
lean_inc(x_21);
lean_inc_ref(x_18);
lean_inc(x_23);
lean_inc_ref(x_24);
lean_inc_ref(x_15);
x_269 = l_Lean_Meta_getLevel(x_15, x_24, x_23, x_18, x_21, x_19);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
lean_dec_ref(x_269);
lean_inc(x_267);
x_272 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpForall___lam__0___boxed), 10, 1);
lean_closure_set(x_272, 0, x_267);
lean_inc_ref(x_15);
lean_inc(x_14);
x_273 = l_Lean_Meta_withLocalDeclD___at___Lean_Meta_Grind_simpForall_spec__0___redArg(x_14, x_15, x_272, x_25, x_22, x_20, x_24, x_23, x_18, x_21, x_271);
if (lean_obj_tag(x_273) == 0)
{
uint8_t x_274; 
x_274 = !lean_is_exclusive(x_273);
if (x_274 == 0)
{
lean_object* x_275; lean_object* x_276; uint8_t x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_275 = lean_ctor_get(x_273, 0);
lean_inc_ref(x_75);
lean_inc_ref(x_15);
lean_inc(x_14);
x_276 = l_Lean_mkLambda(x_14, x_17, x_15, x_75);
x_277 = 0;
lean_inc(x_268);
lean_inc(x_267);
lean_inc(x_266);
x_278 = l_Lean_mkLambda(x_266, x_277, x_267, x_268);
lean_inc_ref(x_15);
lean_inc(x_14);
x_279 = l_Lean_mkLambda(x_14, x_17, x_15, x_278);
lean_inc(x_267);
lean_inc_ref(x_15);
lean_inc(x_14);
x_280 = l_Lean_mkLambda(x_14, x_17, x_15, x_267);
x_281 = lean_unsigned_to_nat(0u);
x_282 = lean_unsigned_to_nat(1u);
x_283 = lean_expr_lift_loose_bvars(x_75, x_281, x_282);
lean_dec_ref(x_75);
x_284 = l_Lean_mkOr(x_268, x_283);
x_285 = l_Lean_mkForall(x_266, x_277, x_267, x_284);
lean_inc_ref(x_15);
x_286 = l_Lean_mkForall(x_14, x_17, x_15, x_285);
x_287 = l_Lean_Meta_Grind_simpForall___closed__10;
x_288 = lean_box(0);
lean_ctor_set_tag(x_264, 1);
lean_ctor_set(x_264, 1, x_288);
lean_ctor_set(x_264, 0, x_275);
lean_ctor_set_tag(x_262, 1);
lean_ctor_set(x_262, 0, x_270);
x_289 = l_Lean_mkConst(x_287, x_262);
x_290 = l_Lean_mkApp4(x_289, x_15, x_280, x_276, x_279);
lean_ctor_set(x_76, 0, x_290);
x_291 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_291, 0, x_286);
lean_ctor_set(x_291, 1, x_76);
lean_ctor_set_uint8(x_291, sizeof(void*)*2, x_26);
x_292 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_273, 0, x_292);
return x_273;
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; uint8_t x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_293 = lean_ctor_get(x_273, 0);
x_294 = lean_ctor_get(x_273, 1);
lean_inc(x_294);
lean_inc(x_293);
lean_dec(x_273);
lean_inc_ref(x_75);
lean_inc_ref(x_15);
lean_inc(x_14);
x_295 = l_Lean_mkLambda(x_14, x_17, x_15, x_75);
x_296 = 0;
lean_inc(x_268);
lean_inc(x_267);
lean_inc(x_266);
x_297 = l_Lean_mkLambda(x_266, x_296, x_267, x_268);
lean_inc_ref(x_15);
lean_inc(x_14);
x_298 = l_Lean_mkLambda(x_14, x_17, x_15, x_297);
lean_inc(x_267);
lean_inc_ref(x_15);
lean_inc(x_14);
x_299 = l_Lean_mkLambda(x_14, x_17, x_15, x_267);
x_300 = lean_unsigned_to_nat(0u);
x_301 = lean_unsigned_to_nat(1u);
x_302 = lean_expr_lift_loose_bvars(x_75, x_300, x_301);
lean_dec_ref(x_75);
x_303 = l_Lean_mkOr(x_268, x_302);
x_304 = l_Lean_mkForall(x_266, x_296, x_267, x_303);
lean_inc_ref(x_15);
x_305 = l_Lean_mkForall(x_14, x_17, x_15, x_304);
x_306 = l_Lean_Meta_Grind_simpForall___closed__10;
x_307 = lean_box(0);
lean_ctor_set_tag(x_264, 1);
lean_ctor_set(x_264, 1, x_307);
lean_ctor_set(x_264, 0, x_293);
lean_ctor_set_tag(x_262, 1);
lean_ctor_set(x_262, 0, x_270);
x_308 = l_Lean_mkConst(x_306, x_262);
x_309 = l_Lean_mkApp4(x_308, x_15, x_299, x_295, x_298);
lean_ctor_set(x_76, 0, x_309);
x_310 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_310, 0, x_305);
lean_ctor_set(x_310, 1, x_76);
lean_ctor_set_uint8(x_310, sizeof(void*)*2, x_26);
x_311 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_311, 0, x_310);
x_312 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_312, 0, x_311);
lean_ctor_set(x_312, 1, x_294);
return x_312;
}
}
else
{
uint8_t x_313; 
lean_dec(x_270);
lean_free_object(x_264);
lean_dec(x_268);
lean_dec(x_267);
lean_free_object(x_262);
lean_dec(x_266);
lean_free_object(x_76);
lean_dec_ref(x_75);
lean_dec_ref(x_15);
lean_dec(x_14);
x_313 = !lean_is_exclusive(x_273);
if (x_313 == 0)
{
return x_273;
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_314 = lean_ctor_get(x_273, 0);
x_315 = lean_ctor_get(x_273, 1);
lean_inc(x_315);
lean_inc(x_314);
lean_dec(x_273);
x_316 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_316, 0, x_314);
lean_ctor_set(x_316, 1, x_315);
return x_316;
}
}
}
else
{
uint8_t x_317; 
lean_free_object(x_264);
lean_dec(x_268);
lean_dec(x_267);
lean_free_object(x_262);
lean_dec(x_266);
lean_free_object(x_76);
lean_dec_ref(x_75);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_18);
lean_dec_ref(x_15);
lean_dec(x_14);
x_317 = !lean_is_exclusive(x_269);
if (x_317 == 0)
{
return x_269;
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_318 = lean_ctor_get(x_269, 0);
x_319 = lean_ctor_get(x_269, 1);
lean_inc(x_319);
lean_inc(x_318);
lean_dec(x_269);
x_320 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_320, 0, x_318);
lean_ctor_set(x_320, 1, x_319);
return x_320;
}
}
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_321 = lean_ctor_get(x_262, 0);
x_322 = lean_ctor_get(x_264, 0);
x_323 = lean_ctor_get(x_264, 1);
lean_inc(x_323);
lean_inc(x_322);
lean_dec(x_264);
lean_inc(x_21);
lean_inc_ref(x_18);
lean_inc(x_23);
lean_inc_ref(x_24);
lean_inc_ref(x_15);
x_324 = l_Lean_Meta_getLevel(x_15, x_24, x_23, x_18, x_21, x_19);
if (lean_obj_tag(x_324) == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_325 = lean_ctor_get(x_324, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_324, 1);
lean_inc(x_326);
lean_dec_ref(x_324);
lean_inc(x_322);
x_327 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpForall___lam__0___boxed), 10, 1);
lean_closure_set(x_327, 0, x_322);
lean_inc_ref(x_15);
lean_inc(x_14);
x_328 = l_Lean_Meta_withLocalDeclD___at___Lean_Meta_Grind_simpForall_spec__0___redArg(x_14, x_15, x_327, x_25, x_22, x_20, x_24, x_23, x_18, x_21, x_326);
if (lean_obj_tag(x_328) == 0)
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; uint8_t x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_328, 1);
lean_inc(x_330);
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 lean_ctor_release(x_328, 1);
 x_331 = x_328;
} else {
 lean_dec_ref(x_328);
 x_331 = lean_box(0);
}
lean_inc_ref(x_75);
lean_inc_ref(x_15);
lean_inc(x_14);
x_332 = l_Lean_mkLambda(x_14, x_17, x_15, x_75);
x_333 = 0;
lean_inc(x_323);
lean_inc(x_322);
lean_inc(x_321);
x_334 = l_Lean_mkLambda(x_321, x_333, x_322, x_323);
lean_inc_ref(x_15);
lean_inc(x_14);
x_335 = l_Lean_mkLambda(x_14, x_17, x_15, x_334);
lean_inc(x_322);
lean_inc_ref(x_15);
lean_inc(x_14);
x_336 = l_Lean_mkLambda(x_14, x_17, x_15, x_322);
x_337 = lean_unsigned_to_nat(0u);
x_338 = lean_unsigned_to_nat(1u);
x_339 = lean_expr_lift_loose_bvars(x_75, x_337, x_338);
lean_dec_ref(x_75);
x_340 = l_Lean_mkOr(x_323, x_339);
x_341 = l_Lean_mkForall(x_321, x_333, x_322, x_340);
lean_inc_ref(x_15);
x_342 = l_Lean_mkForall(x_14, x_17, x_15, x_341);
x_343 = l_Lean_Meta_Grind_simpForall___closed__10;
x_344 = lean_box(0);
x_345 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_345, 0, x_329);
lean_ctor_set(x_345, 1, x_344);
lean_ctor_set_tag(x_262, 1);
lean_ctor_set(x_262, 1, x_345);
lean_ctor_set(x_262, 0, x_325);
x_346 = l_Lean_mkConst(x_343, x_262);
x_347 = l_Lean_mkApp4(x_346, x_15, x_336, x_332, x_335);
lean_ctor_set(x_76, 0, x_347);
x_348 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_348, 0, x_342);
lean_ctor_set(x_348, 1, x_76);
lean_ctor_set_uint8(x_348, sizeof(void*)*2, x_26);
x_349 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_349, 0, x_348);
if (lean_is_scalar(x_331)) {
 x_350 = lean_alloc_ctor(0, 2, 0);
} else {
 x_350 = x_331;
}
lean_ctor_set(x_350, 0, x_349);
lean_ctor_set(x_350, 1, x_330);
return x_350;
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
lean_dec(x_325);
lean_dec(x_323);
lean_dec(x_322);
lean_free_object(x_262);
lean_dec(x_321);
lean_free_object(x_76);
lean_dec_ref(x_75);
lean_dec_ref(x_15);
lean_dec(x_14);
x_351 = lean_ctor_get(x_328, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_328, 1);
lean_inc(x_352);
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 lean_ctor_release(x_328, 1);
 x_353 = x_328;
} else {
 lean_dec_ref(x_328);
 x_353 = lean_box(0);
}
if (lean_is_scalar(x_353)) {
 x_354 = lean_alloc_ctor(1, 2, 0);
} else {
 x_354 = x_353;
}
lean_ctor_set(x_354, 0, x_351);
lean_ctor_set(x_354, 1, x_352);
return x_354;
}
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
lean_dec(x_323);
lean_dec(x_322);
lean_free_object(x_262);
lean_dec(x_321);
lean_free_object(x_76);
lean_dec_ref(x_75);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_18);
lean_dec_ref(x_15);
lean_dec(x_14);
x_355 = lean_ctor_get(x_324, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_324, 1);
lean_inc(x_356);
if (lean_is_exclusive(x_324)) {
 lean_ctor_release(x_324, 0);
 lean_ctor_release(x_324, 1);
 x_357 = x_324;
} else {
 lean_dec_ref(x_324);
 x_357 = lean_box(0);
}
if (lean_is_scalar(x_357)) {
 x_358 = lean_alloc_ctor(1, 2, 0);
} else {
 x_358 = x_357;
}
lean_ctor_set(x_358, 0, x_355);
lean_ctor_set(x_358, 1, x_356);
return x_358;
}
}
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_359 = lean_ctor_get(x_262, 1);
x_360 = lean_ctor_get(x_262, 0);
lean_inc(x_359);
lean_inc(x_360);
lean_dec(x_262);
x_361 = lean_ctor_get(x_359, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_359, 1);
lean_inc(x_362);
if (lean_is_exclusive(x_359)) {
 lean_ctor_release(x_359, 0);
 lean_ctor_release(x_359, 1);
 x_363 = x_359;
} else {
 lean_dec_ref(x_359);
 x_363 = lean_box(0);
}
lean_inc(x_21);
lean_inc_ref(x_18);
lean_inc(x_23);
lean_inc_ref(x_24);
lean_inc_ref(x_15);
x_364 = l_Lean_Meta_getLevel(x_15, x_24, x_23, x_18, x_21, x_19);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_365 = lean_ctor_get(x_364, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_364, 1);
lean_inc(x_366);
lean_dec_ref(x_364);
lean_inc(x_361);
x_367 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpForall___lam__0___boxed), 10, 1);
lean_closure_set(x_367, 0, x_361);
lean_inc_ref(x_15);
lean_inc(x_14);
x_368 = l_Lean_Meta_withLocalDeclD___at___Lean_Meta_Grind_simpForall_spec__0___redArg(x_14, x_15, x_367, x_25, x_22, x_20, x_24, x_23, x_18, x_21, x_366);
if (lean_obj_tag(x_368) == 0)
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; uint8_t x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_369 = lean_ctor_get(x_368, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_368, 1);
lean_inc(x_370);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 lean_ctor_release(x_368, 1);
 x_371 = x_368;
} else {
 lean_dec_ref(x_368);
 x_371 = lean_box(0);
}
lean_inc_ref(x_75);
lean_inc_ref(x_15);
lean_inc(x_14);
x_372 = l_Lean_mkLambda(x_14, x_17, x_15, x_75);
x_373 = 0;
lean_inc(x_362);
lean_inc(x_361);
lean_inc(x_360);
x_374 = l_Lean_mkLambda(x_360, x_373, x_361, x_362);
lean_inc_ref(x_15);
lean_inc(x_14);
x_375 = l_Lean_mkLambda(x_14, x_17, x_15, x_374);
lean_inc(x_361);
lean_inc_ref(x_15);
lean_inc(x_14);
x_376 = l_Lean_mkLambda(x_14, x_17, x_15, x_361);
x_377 = lean_unsigned_to_nat(0u);
x_378 = lean_unsigned_to_nat(1u);
x_379 = lean_expr_lift_loose_bvars(x_75, x_377, x_378);
lean_dec_ref(x_75);
x_380 = l_Lean_mkOr(x_362, x_379);
x_381 = l_Lean_mkForall(x_360, x_373, x_361, x_380);
lean_inc_ref(x_15);
x_382 = l_Lean_mkForall(x_14, x_17, x_15, x_381);
x_383 = l_Lean_Meta_Grind_simpForall___closed__10;
x_384 = lean_box(0);
if (lean_is_scalar(x_363)) {
 x_385 = lean_alloc_ctor(1, 2, 0);
} else {
 x_385 = x_363;
 lean_ctor_set_tag(x_385, 1);
}
lean_ctor_set(x_385, 0, x_369);
lean_ctor_set(x_385, 1, x_384);
x_386 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_386, 0, x_365);
lean_ctor_set(x_386, 1, x_385);
x_387 = l_Lean_mkConst(x_383, x_386);
x_388 = l_Lean_mkApp4(x_387, x_15, x_376, x_372, x_375);
lean_ctor_set(x_76, 0, x_388);
x_389 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_389, 0, x_382);
lean_ctor_set(x_389, 1, x_76);
lean_ctor_set_uint8(x_389, sizeof(void*)*2, x_26);
x_390 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_390, 0, x_389);
if (lean_is_scalar(x_371)) {
 x_391 = lean_alloc_ctor(0, 2, 0);
} else {
 x_391 = x_371;
}
lean_ctor_set(x_391, 0, x_390);
lean_ctor_set(x_391, 1, x_370);
return x_391;
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
lean_dec(x_365);
lean_dec(x_363);
lean_dec(x_362);
lean_dec(x_361);
lean_dec(x_360);
lean_free_object(x_76);
lean_dec_ref(x_75);
lean_dec_ref(x_15);
lean_dec(x_14);
x_392 = lean_ctor_get(x_368, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_368, 1);
lean_inc(x_393);
if (lean_is_exclusive(x_368)) {
 lean_ctor_release(x_368, 0);
 lean_ctor_release(x_368, 1);
 x_394 = x_368;
} else {
 lean_dec_ref(x_368);
 x_394 = lean_box(0);
}
if (lean_is_scalar(x_394)) {
 x_395 = lean_alloc_ctor(1, 2, 0);
} else {
 x_395 = x_394;
}
lean_ctor_set(x_395, 0, x_392);
lean_ctor_set(x_395, 1, x_393);
return x_395;
}
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
lean_dec(x_363);
lean_dec(x_362);
lean_dec(x_361);
lean_dec(x_360);
lean_free_object(x_76);
lean_dec_ref(x_75);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_18);
lean_dec_ref(x_15);
lean_dec(x_14);
x_396 = lean_ctor_get(x_364, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_364, 1);
lean_inc(x_397);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 lean_ctor_release(x_364, 1);
 x_398 = x_364;
} else {
 lean_dec_ref(x_364);
 x_398 = lean_box(0);
}
if (lean_is_scalar(x_398)) {
 x_399 = lean_alloc_ctor(1, 2, 0);
} else {
 x_399 = x_398;
}
lean_ctor_set(x_399, 0, x_396);
lean_ctor_set(x_399, 1, x_397);
return x_399;
}
}
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_400 = lean_ctor_get(x_76, 0);
lean_inc(x_400);
lean_dec(x_76);
x_401 = lean_ctor_get(x_400, 1);
lean_inc(x_401);
x_402 = lean_ctor_get(x_400, 0);
lean_inc(x_402);
if (lean_is_exclusive(x_400)) {
 lean_ctor_release(x_400, 0);
 lean_ctor_release(x_400, 1);
 x_403 = x_400;
} else {
 lean_dec_ref(x_400);
 x_403 = lean_box(0);
}
x_404 = lean_ctor_get(x_401, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_401, 1);
lean_inc(x_405);
if (lean_is_exclusive(x_401)) {
 lean_ctor_release(x_401, 0);
 lean_ctor_release(x_401, 1);
 x_406 = x_401;
} else {
 lean_dec_ref(x_401);
 x_406 = lean_box(0);
}
lean_inc(x_21);
lean_inc_ref(x_18);
lean_inc(x_23);
lean_inc_ref(x_24);
lean_inc_ref(x_15);
x_407 = l_Lean_Meta_getLevel(x_15, x_24, x_23, x_18, x_21, x_19);
if (lean_obj_tag(x_407) == 0)
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_407, 1);
lean_inc(x_409);
lean_dec_ref(x_407);
lean_inc(x_404);
x_410 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpForall___lam__0___boxed), 10, 1);
lean_closure_set(x_410, 0, x_404);
lean_inc_ref(x_15);
lean_inc(x_14);
x_411 = l_Lean_Meta_withLocalDeclD___at___Lean_Meta_Grind_simpForall_spec__0___redArg(x_14, x_15, x_410, x_25, x_22, x_20, x_24, x_23, x_18, x_21, x_409);
if (lean_obj_tag(x_411) == 0)
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; uint8_t x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_411, 1);
lean_inc(x_413);
if (lean_is_exclusive(x_411)) {
 lean_ctor_release(x_411, 0);
 lean_ctor_release(x_411, 1);
 x_414 = x_411;
} else {
 lean_dec_ref(x_411);
 x_414 = lean_box(0);
}
lean_inc_ref(x_75);
lean_inc_ref(x_15);
lean_inc(x_14);
x_415 = l_Lean_mkLambda(x_14, x_17, x_15, x_75);
x_416 = 0;
lean_inc(x_405);
lean_inc(x_404);
lean_inc(x_402);
x_417 = l_Lean_mkLambda(x_402, x_416, x_404, x_405);
lean_inc_ref(x_15);
lean_inc(x_14);
x_418 = l_Lean_mkLambda(x_14, x_17, x_15, x_417);
lean_inc(x_404);
lean_inc_ref(x_15);
lean_inc(x_14);
x_419 = l_Lean_mkLambda(x_14, x_17, x_15, x_404);
x_420 = lean_unsigned_to_nat(0u);
x_421 = lean_unsigned_to_nat(1u);
x_422 = lean_expr_lift_loose_bvars(x_75, x_420, x_421);
lean_dec_ref(x_75);
x_423 = l_Lean_mkOr(x_405, x_422);
x_424 = l_Lean_mkForall(x_402, x_416, x_404, x_423);
lean_inc_ref(x_15);
x_425 = l_Lean_mkForall(x_14, x_17, x_15, x_424);
x_426 = l_Lean_Meta_Grind_simpForall___closed__10;
x_427 = lean_box(0);
if (lean_is_scalar(x_406)) {
 x_428 = lean_alloc_ctor(1, 2, 0);
} else {
 x_428 = x_406;
 lean_ctor_set_tag(x_428, 1);
}
lean_ctor_set(x_428, 0, x_412);
lean_ctor_set(x_428, 1, x_427);
if (lean_is_scalar(x_403)) {
 x_429 = lean_alloc_ctor(1, 2, 0);
} else {
 x_429 = x_403;
 lean_ctor_set_tag(x_429, 1);
}
lean_ctor_set(x_429, 0, x_408);
lean_ctor_set(x_429, 1, x_428);
x_430 = l_Lean_mkConst(x_426, x_429);
x_431 = l_Lean_mkApp4(x_430, x_15, x_419, x_415, x_418);
x_432 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_432, 0, x_431);
x_433 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_433, 0, x_425);
lean_ctor_set(x_433, 1, x_432);
lean_ctor_set_uint8(x_433, sizeof(void*)*2, x_26);
x_434 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_434, 0, x_433);
if (lean_is_scalar(x_414)) {
 x_435 = lean_alloc_ctor(0, 2, 0);
} else {
 x_435 = x_414;
}
lean_ctor_set(x_435, 0, x_434);
lean_ctor_set(x_435, 1, x_413);
return x_435;
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
lean_dec(x_408);
lean_dec(x_406);
lean_dec(x_405);
lean_dec(x_404);
lean_dec(x_403);
lean_dec(x_402);
lean_dec_ref(x_75);
lean_dec_ref(x_15);
lean_dec(x_14);
x_436 = lean_ctor_get(x_411, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_411, 1);
lean_inc(x_437);
if (lean_is_exclusive(x_411)) {
 lean_ctor_release(x_411, 0);
 lean_ctor_release(x_411, 1);
 x_438 = x_411;
} else {
 lean_dec_ref(x_411);
 x_438 = lean_box(0);
}
if (lean_is_scalar(x_438)) {
 x_439 = lean_alloc_ctor(1, 2, 0);
} else {
 x_439 = x_438;
}
lean_ctor_set(x_439, 0, x_436);
lean_ctor_set(x_439, 1, x_437);
return x_439;
}
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; 
lean_dec(x_406);
lean_dec(x_405);
lean_dec(x_404);
lean_dec(x_403);
lean_dec(x_402);
lean_dec_ref(x_75);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_18);
lean_dec_ref(x_15);
lean_dec(x_14);
x_440 = lean_ctor_get(x_407, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_407, 1);
lean_inc(x_441);
if (lean_is_exclusive(x_407)) {
 lean_ctor_release(x_407, 0);
 lean_ctor_release(x_407, 1);
 x_442 = x_407;
} else {
 lean_dec_ref(x_407);
 x_442 = lean_box(0);
}
if (lean_is_scalar(x_442)) {
 x_443 = lean_alloc_ctor(1, 2, 0);
} else {
 x_443 = x_442;
}
lean_ctor_set(x_443, 0, x_440);
lean_ctor_set(x_443, 1, x_441);
return x_443;
}
}
}
}
}
else
{
lean_object* x_444; lean_object* x_445; 
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_18);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
x_444 = l_Lean_Meta_Grind_simpForall___closed__0;
x_445 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_445, 0, x_444);
lean_ctor_set(x_445, 1, x_19);
return x_445;
}
}
}
block_459:
{
uint8_t x_455; 
x_455 = l_Lean_Expr_isApp(x_16);
if (x_455 == 0)
{
x_18 = x_452;
x_19 = x_454;
x_20 = x_449;
x_21 = x_453;
x_22 = x_448;
x_23 = x_451;
x_24 = x_450;
x_25 = x_447;
x_26 = x_455;
goto block_446;
}
else
{
lean_object* x_456; lean_object* x_457; uint8_t x_458; 
x_456 = l_Lean_Expr_getAppNumArgs(x_16);
x_457 = lean_unsigned_to_nat(2u);
x_458 = lean_nat_dec_eq(x_456, x_457);
lean_dec(x_456);
x_18 = x_452;
x_19 = x_454;
x_20 = x_449;
x_21 = x_453;
x_22 = x_448;
x_23 = x_451;
x_24 = x_450;
x_25 = x_447;
x_26 = x_458;
goto block_446;
}
}
}
else
{
lean_object* x_736; lean_object* x_737; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_736 = l_Lean_Meta_Grind_simpForall___closed__0;
x_737 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_737, 0, x_736);
lean_ctor_set(x_737, 1, x_9);
return x_737;
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Meta_Grind_simpForall___closed__0;
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_2);
x_15 = lean_unbox(x_5);
x_16 = l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg(x_1, x_14, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_Grind_simpForall_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_3);
x_16 = lean_unbox(x_6);
x_17 = l_Lean_Meta_withLocalDecl___at___Lean_Meta_withLocalDeclD___at___Lean_Meta_Grind_simpForall_spec__0_spec__0(x_1, x_2, x_15, x_4, x_5, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_simpForall___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_11;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__31___closed__0____x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__31___closed__1____x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpForall", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__31___closed__2____x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__31___closed__1____x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_;
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1;
x_3 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__31___closed__0____x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_;
x_4 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__31___closed__3____x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__31___closed__4____x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(5);
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__31___closed__3____x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__31___closed__5____x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__31___closed__4____x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__31____x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__31___closed__2____x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_;
x_3 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__31___closed__5____x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_;
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpForall), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpExists___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nonempty", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpExists___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_simpExists___redArg___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpExists___redArg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exists_const", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpExists___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_simpExists___redArg___closed__2;
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1;
x_3 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpExists___redArg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exists_prop", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpExists___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_simpExists___redArg___closed__4;
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1;
x_3 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpExists___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_simpExists___redArg___closed__5;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpExists___redArg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exists_and_right", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpExists___redArg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_simpExists___redArg___closed__7;
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1;
x_3 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpExists___redArg___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exists_and_left", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpExists___redArg___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_simpExists___redArg___closed__9;
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1;
x_3 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpExists___redArg___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exists_or", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_simpExists___redArg___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_simpExists___redArg___closed__11;
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1;
x_3 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_11; lean_object* x_15; uint8_t x_16; 
x_15 = l_Lean_Expr_cleanupAnnotations(x_1);
x_16 = l_Lean_Expr_isApp(x_15);
if (x_16 == 0)
{
lean_dec_ref(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_11 = x_6;
goto block_14;
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_inc_ref(x_15);
x_17 = l_Lean_Expr_appFnCleanup___redArg(x_15);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_dec_ref(x_17);
lean_dec_ref(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_11 = x_6;
goto block_14;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_inc_ref(x_17);
x_19 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_20 = l_Lean_Meta_Grind_propagateForallPropDown___closed__5;
x_21 = l_Lean_Expr_isConstOf(x_19, x_20);
if (x_21 == 0)
{
lean_dec_ref(x_19);
lean_dec_ref(x_17);
lean_dec_ref(x_15);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_11 = x_6;
goto block_14;
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_22);
lean_dec_ref(x_15);
if (lean_obj_tag(x_22) == 6)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_94; uint8_t x_95; lean_object* x_96; uint8_t x_97; uint8_t x_124; uint8_t x_154; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 2);
lean_inc_ref(x_24);
lean_dec_ref(x_22);
x_25 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_25);
lean_dec_ref(x_17);
x_154 = l_Lean_Expr_isApp(x_24);
if (x_154 == 0)
{
x_124 = x_154;
goto block_153;
}
else
{
lean_object* x_155; lean_object* x_156; uint8_t x_157; 
x_155 = l_Lean_Expr_getAppNumArgs(x_24);
x_156 = lean_unsigned_to_nat(2u);
x_157 = lean_nat_dec_eq(x_155, x_156);
lean_dec(x_155);
x_124 = x_157;
goto block_153;
}
block_93:
{
uint8_t x_31; 
x_31 = l_Lean_Expr_hasLooseBVars(x_24);
if (x_31 == 0)
{
if (x_21 == 0)
{
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_19);
x_7 = x_30;
goto block_10;
}
else
{
lean_object* x_32; 
lean_inc(x_29);
lean_inc_ref(x_28);
lean_inc(x_27);
lean_inc_ref(x_26);
lean_inc_ref(x_25);
x_32 = l_Lean_Meta_isProp(x_25, x_26, x_27, x_28, x_29, x_30);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec_ref(x_32);
x_36 = l_Lean_Expr_constLevels_x21(x_19);
lean_dec_ref(x_19);
x_37 = l_Lean_Meta_Grind_simpExists___redArg___closed__1;
lean_inc(x_36);
x_38 = l_Lean_mkConst(x_37, x_36);
lean_inc_ref(x_25);
x_39 = l_Lean_Expr_app___override(x_38, x_25);
x_40 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_39, x_26, x_27, x_28, x_29, x_35);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
lean_dec(x_36);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec_ref(x_40);
x_7 = x_42;
goto block_10;
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_40);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_40, 0);
lean_dec(x_44);
x_45 = !lean_is_exclusive(x_41);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_41, 0);
x_47 = l_Lean_Meta_Grind_simpExists___redArg___closed__3;
x_48 = l_Lean_mkConst(x_47, x_36);
lean_inc_ref(x_24);
x_49 = l_Lean_mkApp3(x_48, x_25, x_46, x_24);
lean_ctor_set(x_41, 0, x_49);
x_50 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_50, 0, x_24);
lean_ctor_set(x_50, 1, x_41);
lean_ctor_set_uint8(x_50, sizeof(void*)*2, x_21);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_40, 0, x_51);
return x_40;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_52 = lean_ctor_get(x_41, 0);
lean_inc(x_52);
lean_dec(x_41);
x_53 = l_Lean_Meta_Grind_simpExists___redArg___closed__3;
x_54 = l_Lean_mkConst(x_53, x_36);
lean_inc_ref(x_24);
x_55 = l_Lean_mkApp3(x_54, x_25, x_52, x_24);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_57, 0, x_24);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set_uint8(x_57, sizeof(void*)*2, x_21);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_40, 0, x_58);
return x_40;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_59 = lean_ctor_get(x_40, 1);
lean_inc(x_59);
lean_dec(x_40);
x_60 = lean_ctor_get(x_41, 0);
lean_inc(x_60);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_61 = x_41;
} else {
 lean_dec_ref(x_41);
 x_61 = lean_box(0);
}
x_62 = l_Lean_Meta_Grind_simpExists___redArg___closed__3;
x_63 = l_Lean_mkConst(x_62, x_36);
lean_inc_ref(x_24);
x_64 = l_Lean_mkApp3(x_63, x_25, x_60, x_24);
if (lean_is_scalar(x_61)) {
 x_65 = lean_alloc_ctor(1, 1, 0);
} else {
 x_65 = x_61;
}
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_66, 0, x_24);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set_uint8(x_66, sizeof(void*)*2, x_21);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_59);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_36);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
x_69 = !lean_is_exclusive(x_40);
if (x_69 == 0)
{
return x_40;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_40, 0);
x_71 = lean_ctor_get(x_40, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_40);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_19);
x_73 = !lean_is_exclusive(x_32);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_74 = lean_ctor_get(x_32, 0);
lean_dec(x_74);
lean_inc_ref(x_24);
lean_inc_ref(x_25);
x_75 = l_Lean_mkAnd(x_25, x_24);
x_76 = l_Lean_Meta_Grind_simpExists___redArg___closed__6;
x_77 = l_Lean_mkAppB(x_76, x_25, x_24);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_79 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_79, 0, x_75);
lean_ctor_set(x_79, 1, x_78);
lean_ctor_set_uint8(x_79, sizeof(void*)*2, x_21);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_32, 0, x_80);
return x_32;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_81 = lean_ctor_get(x_32, 1);
lean_inc(x_81);
lean_dec(x_32);
lean_inc_ref(x_24);
lean_inc_ref(x_25);
x_82 = l_Lean_mkAnd(x_25, x_24);
x_83 = l_Lean_Meta_Grind_simpExists___redArg___closed__6;
x_84 = l_Lean_mkAppB(x_83, x_25, x_24);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_86, 0, x_82);
lean_ctor_set(x_86, 1, x_85);
lean_ctor_set_uint8(x_86, sizeof(void*)*2, x_21);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_81);
return x_88;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_19);
x_89 = !lean_is_exclusive(x_32);
if (x_89 == 0)
{
return x_32;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_32, 0);
x_91 = lean_ctor_get(x_32, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_32);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
}
else
{
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_19);
x_7 = x_30;
goto block_10;
}
}
block_123:
{
if (x_97 == 0)
{
uint8_t x_98; 
x_98 = l_Lean_Expr_hasLooseBVars(x_94);
if (x_98 == 0)
{
if (x_95 == 0)
{
lean_dec_ref(x_96);
lean_dec_ref(x_94);
lean_dec(x_23);
x_26 = x_2;
x_27 = x_3;
x_28 = x_4;
x_29 = x_5;
x_30 = x_6;
goto block_93;
}
else
{
uint8_t x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec_ref(x_24);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_99 = 0;
lean_inc_ref(x_25);
x_100 = l_Lean_mkLambda(x_23, x_99, x_25, x_96);
lean_inc_ref(x_100);
lean_inc_ref(x_25);
lean_inc_ref(x_19);
x_101 = l_Lean_mkAppB(x_19, x_25, x_100);
lean_inc_ref(x_94);
x_102 = l_Lean_mkAnd(x_101, x_94);
x_103 = l_Lean_Expr_constLevels_x21(x_19);
lean_dec_ref(x_19);
x_104 = l_Lean_Meta_Grind_simpExists___redArg___closed__8;
x_105 = l_Lean_mkConst(x_104, x_103);
x_106 = l_Lean_mkApp3(x_105, x_25, x_100, x_94);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_108 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_108, 0, x_102);
lean_ctor_set(x_108, 1, x_107);
lean_ctor_set_uint8(x_108, sizeof(void*)*2, x_21);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_108);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_6);
return x_110;
}
}
else
{
lean_dec_ref(x_96);
lean_dec_ref(x_94);
lean_dec(x_23);
x_26 = x_2;
x_27 = x_3;
x_28 = x_4;
x_29 = x_5;
x_30 = x_6;
goto block_93;
}
}
else
{
uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec_ref(x_24);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_111 = 0;
lean_inc_ref(x_25);
x_112 = l_Lean_mkLambda(x_23, x_111, x_25, x_94);
lean_inc_ref(x_112);
lean_inc_ref(x_25);
lean_inc_ref(x_19);
x_113 = l_Lean_mkAppB(x_19, x_25, x_112);
lean_inc_ref(x_96);
x_114 = l_Lean_mkAnd(x_96, x_113);
x_115 = l_Lean_Expr_constLevels_x21(x_19);
lean_dec_ref(x_19);
x_116 = l_Lean_Meta_Grind_simpExists___redArg___closed__10;
x_117 = l_Lean_mkConst(x_116, x_115);
x_118 = l_Lean_mkApp3(x_117, x_25, x_112, x_96);
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_118);
x_120 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_120, 0, x_114);
lean_ctor_set(x_120, 1, x_119);
lean_ctor_set_uint8(x_120, sizeof(void*)*2, x_21);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_120);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_6);
return x_122;
}
}
block_153:
{
if (x_124 == 0)
{
lean_dec(x_23);
x_26 = x_2;
x_27 = x_3;
x_28 = x_4;
x_29 = x_5;
x_30 = x_6;
goto block_93;
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = l_Lean_Expr_appFn_x21(x_24);
x_126 = l_Lean_Expr_appFn_x21(x_125);
if (lean_obj_tag(x_126) == 4)
{
lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
lean_dec_ref(x_126);
x_128 = l_Lean_Meta_Grind_simpForall___closed__2;
x_129 = lean_name_eq(x_127, x_128);
if (x_129 == 0)
{
lean_object* x_130; uint8_t x_131; 
x_130 = l_Lean_Meta_Grind_simpForall___closed__4;
x_131 = lean_name_eq(x_127, x_130);
lean_dec(x_127);
if (x_131 == 0)
{
lean_dec_ref(x_125);
lean_dec(x_23);
x_26 = x_2;
x_27 = x_3;
x_28 = x_4;
x_29 = x_5;
x_30 = x_6;
goto block_93;
}
else
{
lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_132 = l_Lean_Expr_appArg_x21(x_125);
lean_dec_ref(x_125);
x_133 = l_Lean_Expr_appArg_x21(x_24);
x_134 = l_Lean_Expr_hasLooseBVars(x_132);
if (x_134 == 0)
{
x_94 = x_133;
x_95 = x_131;
x_96 = x_132;
x_97 = x_131;
goto block_123;
}
else
{
x_94 = x_133;
x_95 = x_131;
x_96 = x_132;
x_97 = x_129;
goto block_123;
}
}
}
else
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_127);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_135 = l_Lean_Expr_appArg_x21(x_125);
lean_dec_ref(x_125);
x_136 = l_Lean_Expr_appArg_x21(x_24);
lean_dec_ref(x_24);
x_137 = 0;
lean_inc_ref(x_25);
lean_inc(x_23);
x_138 = l_Lean_mkLambda(x_23, x_137, x_25, x_135);
lean_inc_ref(x_25);
x_139 = l_Lean_mkLambda(x_23, x_137, x_25, x_136);
x_140 = l_Lean_Expr_constLevels_x21(x_19);
lean_inc_ref(x_138);
lean_inc_ref(x_25);
lean_inc_ref(x_19);
x_141 = l_Lean_mkAppB(x_19, x_25, x_138);
lean_inc_ref(x_139);
lean_inc_ref(x_25);
x_142 = l_Lean_mkAppB(x_19, x_25, x_139);
x_143 = l_Lean_mkOr(x_141, x_142);
x_144 = l_Lean_Meta_Grind_simpExists___redArg___closed__12;
x_145 = l_Lean_mkConst(x_144, x_140);
x_146 = l_Lean_mkApp3(x_145, x_25, x_138, x_139);
x_147 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_147, 0, x_146);
x_148 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_148, 0, x_143);
lean_ctor_set(x_148, 1, x_147);
lean_ctor_set_uint8(x_148, sizeof(void*)*2, x_21);
x_149 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_149, 0, x_148);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_6);
return x_150;
}
}
else
{
lean_object* x_151; lean_object* x_152; 
lean_dec_ref(x_126);
lean_dec_ref(x_125);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_19);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_151 = l_Lean_Meta_Grind_simpForall___closed__0;
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_6);
return x_152;
}
}
}
}
else
{
lean_object* x_158; lean_object* x_159; 
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec_ref(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_158 = l_Lean_Meta_Grind_simpForall___closed__0;
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_6);
return x_159;
}
}
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Meta_Grind_simpForall___closed__0;
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Meta_Grind_simpForall___closed__0;
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_simpExists___redArg(x_1, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_simpExists(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36___closed__0____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpExists", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36___closed__1____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36___closed__0____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_;
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1;
x_3 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__31___closed__0____x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_;
x_4 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36___closed__2____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = l_Lean_Meta_Grind_propagateForallPropDown___closed__5;
x_3 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36___closed__3____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36___closed__4____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36___closed__2____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_;
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36___closed__3____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36___closed__5____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36___closed__4____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36___closed__6____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36___closed__5____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36___closed__1____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_;
x_3 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36___closed__6____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_;
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpExists___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addForallSimproc(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__31___closed__2____x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_;
x_6 = 1;
x_7 = l_Lean_Meta_Simp_Simprocs_add(x_1, x_5, x_6, x_2, x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec_ref(x_7);
x_10 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36___closed__1____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_;
x_11 = l_Lean_Meta_Simp_Simprocs_add(x_8, x_10, x_6, x_2, x_3, x_9);
return x_11;
}
else
{
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addForallSimproc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_addForallSimproc(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
lean_object* initialize_Init_Grind_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Internalize(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_EqResolution(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_SynthInstance(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_ForallProp(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Internalize(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_EqResolution(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__2);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__3);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__5 = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__5);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__6 = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__6();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__6);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__7 = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__7();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__7);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__8 = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__8();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__8);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__9 = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__9();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__9);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__10 = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__10();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__10);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__11 = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__11();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__11);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__12 = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__12();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__12);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__13 = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__13();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__13);
l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__0 = _init_l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__0();
l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__1 = _init_l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__1();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__1);
l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__2 = _init_l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__2();
lean_mark_persistent(l_Lean_addTrace___at___Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__2);
l_Lean_Meta_Grind_propagateForallPropUp___closed__0 = _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropUp___closed__0);
l_Lean_Meta_Grind_propagateForallPropUp___closed__1 = _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropUp___closed__1);
l_Lean_Meta_Grind_propagateForallPropUp___closed__2 = _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropUp___closed__2);
l_Lean_Meta_Grind_propagateForallPropUp___closed__3 = _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropUp___closed__3);
l_Lean_Meta_Grind_propagateForallPropUp___closed__4 = _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropUp___closed__4);
l_Lean_Meta_Grind_propagateForallPropUp___closed__5 = _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropUp___closed__5);
l_Lean_Meta_Grind_propagateForallPropUp___closed__6 = _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropUp___closed__6);
l_Lean_Meta_Grind_propagateForallPropUp___closed__7 = _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropUp___closed__7);
l_Lean_Meta_Grind_propagateForallPropUp___closed__8 = _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropUp___closed__8);
l_Lean_Meta_Grind_propagateForallPropUp___closed__9 = _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropUp___closed__9);
l_Lean_Meta_Grind_propagateForallPropUp___closed__10 = _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__10();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropUp___closed__10);
l_Lean_Meta_Grind_propagateForallPropUp___closed__11 = _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__11();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropUp___closed__11);
l_Lean_Meta_Grind_propagateForallPropUp___closed__12 = _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__12();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropUp___closed__12);
l_Lean_Meta_Grind_propagateForallPropUp___closed__13 = _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__13();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropUp___closed__13);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f___closed__0);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f___closed__1);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___closed__0);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__0);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__2);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__3);
l_Lean_Meta_Grind_propagateForallPropDown___closed__0 = _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropDown___closed__0);
l_Lean_Meta_Grind_propagateForallPropDown___closed__1 = _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropDown___closed__1);
l_Lean_Meta_Grind_propagateForallPropDown___closed__2 = _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropDown___closed__2);
l_Lean_Meta_Grind_propagateForallPropDown___closed__3 = _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropDown___closed__3);
l_Lean_Meta_Grind_propagateForallPropDown___closed__4 = _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropDown___closed__4);
l_Lean_Meta_Grind_propagateForallPropDown___closed__5 = _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropDown___closed__5);
l_Lean_Meta_Grind_propagateForallPropDown___closed__6 = _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropDown___closed__6);
l_Lean_Meta_Grind_propagateForallPropDown___closed__7 = _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropDown___closed__7);
l_Lean_Meta_Grind_propagateForallPropDown___closed__8 = _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropDown___closed__8);
l_Lean_Meta_Grind_propagateForallPropDown___closed__9 = _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropDown___closed__9);
l_Lean_Meta_Grind_propagateForallPropDown___closed__10 = _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__10();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropDown___closed__10);
l_Lean_Meta_Grind_propagateForallPropDown___closed__11 = _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__11();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropDown___closed__11);
l_Lean_Meta_Grind_propagateForallPropDown___closed__12 = _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__12();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropDown___closed__12);
l_Lean_Meta_Grind_propagateForallPropDown___closed__13 = _init_l_Lean_Meta_Grind_propagateForallPropDown___closed__13();
lean_mark_persistent(l_Lean_Meta_Grind_propagateForallPropDown___closed__13);
l_Lean_Meta_Grind_propagateExistsDown___closed__0 = _init_l_Lean_Meta_Grind_propagateExistsDown___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_propagateExistsDown___closed__0);
l_Lean_Meta_Grind_propagateExistsDown___closed__1 = _init_l_Lean_Meta_Grind_propagateExistsDown___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_propagateExistsDown___closed__1);
l_Lean_Meta_Grind_propagateExistsDown___closed__2 = _init_l_Lean_Meta_Grind_propagateExistsDown___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_propagateExistsDown___closed__2);
l_Lean_Meta_Grind_propagateExistsDown___closed__3 = _init_l_Lean_Meta_Grind_propagateExistsDown___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_propagateExistsDown___closed__3);
l_Lean_Meta_Grind_propagateExistsDown___closed__4 = _init_l_Lean_Meta_Grind_propagateExistsDown___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_propagateExistsDown___closed__4);
l_Lean_Meta_Grind_propagateExistsDown___closed__5 = _init_l_Lean_Meta_Grind_propagateExistsDown___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_propagateExistsDown___closed__5);
l_Lean_Meta_Grind_propagateExistsDown___closed__6 = _init_l_Lean_Meta_Grind_propagateExistsDown___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_propagateExistsDown___closed__6);
l_Lean_Meta_Grind_propagateExistsDown___closed__7 = _init_l_Lean_Meta_Grind_propagateExistsDown___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_propagateExistsDown___closed__7);
if (builtin) {res = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateExistsDown___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1____x40_Lean_Meta_Tactic_Grind_ForallProp_115310127____hygCtx___hyg_8_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__0 = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__0();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__0);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__1 = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__1);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__2 = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__2);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__3 = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__3);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__4 = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__4);
l_Lean_Meta_Grind_simpForall___closed__0 = _init_l_Lean_Meta_Grind_simpForall___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_simpForall___closed__0);
l_Lean_Meta_Grind_simpForall___closed__1 = _init_l_Lean_Meta_Grind_simpForall___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_simpForall___closed__1);
l_Lean_Meta_Grind_simpForall___closed__2 = _init_l_Lean_Meta_Grind_simpForall___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_simpForall___closed__2);
l_Lean_Meta_Grind_simpForall___closed__3 = _init_l_Lean_Meta_Grind_simpForall___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_simpForall___closed__3);
l_Lean_Meta_Grind_simpForall___closed__4 = _init_l_Lean_Meta_Grind_simpForall___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_simpForall___closed__4);
l_Lean_Meta_Grind_simpForall___closed__5 = _init_l_Lean_Meta_Grind_simpForall___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_simpForall___closed__5);
l_Lean_Meta_Grind_simpForall___closed__6 = _init_l_Lean_Meta_Grind_simpForall___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_simpForall___closed__6);
l_Lean_Meta_Grind_simpForall___closed__7 = _init_l_Lean_Meta_Grind_simpForall___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_simpForall___closed__7);
l_Lean_Meta_Grind_simpForall___closed__8 = _init_l_Lean_Meta_Grind_simpForall___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_simpForall___closed__8);
l_Lean_Meta_Grind_simpForall___closed__9 = _init_l_Lean_Meta_Grind_simpForall___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_simpForall___closed__9);
l_Lean_Meta_Grind_simpForall___closed__10 = _init_l_Lean_Meta_Grind_simpForall___closed__10();
lean_mark_persistent(l_Lean_Meta_Grind_simpForall___closed__10);
l_Lean_Meta_Grind_simpForall___closed__11 = _init_l_Lean_Meta_Grind_simpForall___closed__11();
lean_mark_persistent(l_Lean_Meta_Grind_simpForall___closed__11);
l_Lean_Meta_Grind_simpForall___closed__12 = _init_l_Lean_Meta_Grind_simpForall___closed__12();
lean_mark_persistent(l_Lean_Meta_Grind_simpForall___closed__12);
l_Lean_Meta_Grind_simpForall___closed__13 = _init_l_Lean_Meta_Grind_simpForall___closed__13();
lean_mark_persistent(l_Lean_Meta_Grind_simpForall___closed__13);
l_Lean_Meta_Grind_simpForall___closed__14 = _init_l_Lean_Meta_Grind_simpForall___closed__14();
lean_mark_persistent(l_Lean_Meta_Grind_simpForall___closed__14);
l_Lean_Meta_Grind_simpForall___closed__15 = _init_l_Lean_Meta_Grind_simpForall___closed__15();
lean_mark_persistent(l_Lean_Meta_Grind_simpForall___closed__15);
l_Lean_Meta_Grind_simpForall___closed__16 = _init_l_Lean_Meta_Grind_simpForall___closed__16();
lean_mark_persistent(l_Lean_Meta_Grind_simpForall___closed__16);
l_Lean_Meta_Grind_simpForall___closed__17 = _init_l_Lean_Meta_Grind_simpForall___closed__17();
lean_mark_persistent(l_Lean_Meta_Grind_simpForall___closed__17);
l_Lean_Meta_Grind_simpForall___closed__18 = _init_l_Lean_Meta_Grind_simpForall___closed__18();
lean_mark_persistent(l_Lean_Meta_Grind_simpForall___closed__18);
l_Lean_Meta_Grind_simpForall___closed__19 = _init_l_Lean_Meta_Grind_simpForall___closed__19();
lean_mark_persistent(l_Lean_Meta_Grind_simpForall___closed__19);
l_Lean_Meta_Grind_simpForall___closed__20 = _init_l_Lean_Meta_Grind_simpForall___closed__20();
lean_mark_persistent(l_Lean_Meta_Grind_simpForall___closed__20);
l_Lean_Meta_Grind_simpForall___closed__21 = _init_l_Lean_Meta_Grind_simpForall___closed__21();
lean_mark_persistent(l_Lean_Meta_Grind_simpForall___closed__21);
l_Lean_Meta_Grind_simpForall___closed__22 = _init_l_Lean_Meta_Grind_simpForall___closed__22();
lean_mark_persistent(l_Lean_Meta_Grind_simpForall___closed__22);
l_Lean_Meta_Grind_simpForall___closed__23 = _init_l_Lean_Meta_Grind_simpForall___closed__23();
lean_mark_persistent(l_Lean_Meta_Grind_simpForall___closed__23);
l_Lean_Meta_Grind_simpForall___closed__24 = _init_l_Lean_Meta_Grind_simpForall___closed__24();
lean_mark_persistent(l_Lean_Meta_Grind_simpForall___closed__24);
l_Lean_Meta_Grind_simpForall___closed__25 = _init_l_Lean_Meta_Grind_simpForall___closed__25();
lean_mark_persistent(l_Lean_Meta_Grind_simpForall___closed__25);
l_Lean_Meta_Grind_simpForall___closed__26 = _init_l_Lean_Meta_Grind_simpForall___closed__26();
lean_mark_persistent(l_Lean_Meta_Grind_simpForall___closed__26);
l_Lean_Meta_Grind_simpForall___closed__27 = _init_l_Lean_Meta_Grind_simpForall___closed__27();
lean_mark_persistent(l_Lean_Meta_Grind_simpForall___closed__27);
l_Lean_Meta_Grind_simpForall___closed__28 = _init_l_Lean_Meta_Grind_simpForall___closed__28();
lean_mark_persistent(l_Lean_Meta_Grind_simpForall___closed__28);
l_Lean_Meta_Grind_simpForall___closed__29 = _init_l_Lean_Meta_Grind_simpForall___closed__29();
lean_mark_persistent(l_Lean_Meta_Grind_simpForall___closed__29);
l_Lean_Meta_Grind_simpForall___closed__30 = _init_l_Lean_Meta_Grind_simpForall___closed__30();
lean_mark_persistent(l_Lean_Meta_Grind_simpForall___closed__30);
l_Lean_Meta_Grind_simpForall___closed__31 = _init_l_Lean_Meta_Grind_simpForall___closed__31();
lean_mark_persistent(l_Lean_Meta_Grind_simpForall___closed__31);
l_Lean_Meta_Grind_simpForall___closed__32 = _init_l_Lean_Meta_Grind_simpForall___closed__32();
lean_mark_persistent(l_Lean_Meta_Grind_simpForall___closed__32);
l_Lean_Meta_Grind_simpForall___closed__33 = _init_l_Lean_Meta_Grind_simpForall___closed__33();
lean_mark_persistent(l_Lean_Meta_Grind_simpForall___closed__33);
l_Lean_Meta_Grind_simpForall___closed__34 = _init_l_Lean_Meta_Grind_simpForall___closed__34();
lean_mark_persistent(l_Lean_Meta_Grind_simpForall___closed__34);
l_Lean_Meta_Grind_simpForall___closed__35 = _init_l_Lean_Meta_Grind_simpForall___closed__35();
lean_mark_persistent(l_Lean_Meta_Grind_simpForall___closed__35);
l_Lean_Meta_Grind_simpForall___closed__36 = _init_l_Lean_Meta_Grind_simpForall___closed__36();
lean_mark_persistent(l_Lean_Meta_Grind_simpForall___closed__36);
l_Lean_Meta_Grind_simpForall___closed__37 = _init_l_Lean_Meta_Grind_simpForall___closed__37();
lean_mark_persistent(l_Lean_Meta_Grind_simpForall___closed__37);
l_Lean_Meta_Grind_simpForall___closed__38 = _init_l_Lean_Meta_Grind_simpForall___closed__38();
lean_mark_persistent(l_Lean_Meta_Grind_simpForall___closed__38);
l_Lean_Meta_Grind_simpForall___closed__39 = _init_l_Lean_Meta_Grind_simpForall___closed__39();
lean_mark_persistent(l_Lean_Meta_Grind_simpForall___closed__39);
l_Lean_Meta_Grind_simpForall___closed__40 = _init_l_Lean_Meta_Grind_simpForall___closed__40();
lean_mark_persistent(l_Lean_Meta_Grind_simpForall___closed__40);
l_Lean_Meta_Grind_simpForall___closed__41 = _init_l_Lean_Meta_Grind_simpForall___closed__41();
lean_mark_persistent(l_Lean_Meta_Grind_simpForall___closed__41);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__31___closed__0____x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_ = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__31___closed__0____x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__31___closed__0____x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__31___closed__1____x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_ = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__31___closed__1____x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__31___closed__1____x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__31___closed__2____x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_ = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__31___closed__2____x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__31___closed__2____x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__31___closed__3____x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_ = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__31___closed__3____x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__31___closed__3____x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__31___closed__4____x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_ = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__31___closed__4____x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__31___closed__4____x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__31___closed__5____x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_ = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__31___closed__5____x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__31___closed__5____x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_);
if (builtin) {res = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__31____x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Meta_Grind_simpExists___redArg___closed__0 = _init_l_Lean_Meta_Grind_simpExists___redArg___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_simpExists___redArg___closed__0);
l_Lean_Meta_Grind_simpExists___redArg___closed__1 = _init_l_Lean_Meta_Grind_simpExists___redArg___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_simpExists___redArg___closed__1);
l_Lean_Meta_Grind_simpExists___redArg___closed__2 = _init_l_Lean_Meta_Grind_simpExists___redArg___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_simpExists___redArg___closed__2);
l_Lean_Meta_Grind_simpExists___redArg___closed__3 = _init_l_Lean_Meta_Grind_simpExists___redArg___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_simpExists___redArg___closed__3);
l_Lean_Meta_Grind_simpExists___redArg___closed__4 = _init_l_Lean_Meta_Grind_simpExists___redArg___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_simpExists___redArg___closed__4);
l_Lean_Meta_Grind_simpExists___redArg___closed__5 = _init_l_Lean_Meta_Grind_simpExists___redArg___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_simpExists___redArg___closed__5);
l_Lean_Meta_Grind_simpExists___redArg___closed__6 = _init_l_Lean_Meta_Grind_simpExists___redArg___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_simpExists___redArg___closed__6);
l_Lean_Meta_Grind_simpExists___redArg___closed__7 = _init_l_Lean_Meta_Grind_simpExists___redArg___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_simpExists___redArg___closed__7);
l_Lean_Meta_Grind_simpExists___redArg___closed__8 = _init_l_Lean_Meta_Grind_simpExists___redArg___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_simpExists___redArg___closed__8);
l_Lean_Meta_Grind_simpExists___redArg___closed__9 = _init_l_Lean_Meta_Grind_simpExists___redArg___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_simpExists___redArg___closed__9);
l_Lean_Meta_Grind_simpExists___redArg___closed__10 = _init_l_Lean_Meta_Grind_simpExists___redArg___closed__10();
lean_mark_persistent(l_Lean_Meta_Grind_simpExists___redArg___closed__10);
l_Lean_Meta_Grind_simpExists___redArg___closed__11 = _init_l_Lean_Meta_Grind_simpExists___redArg___closed__11();
lean_mark_persistent(l_Lean_Meta_Grind_simpExists___redArg___closed__11);
l_Lean_Meta_Grind_simpExists___redArg___closed__12 = _init_l_Lean_Meta_Grind_simpExists___redArg___closed__12();
lean_mark_persistent(l_Lean_Meta_Grind_simpExists___redArg___closed__12);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36___closed__0____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_ = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36___closed__0____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36___closed__0____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36___closed__1____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_ = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36___closed__1____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36___closed__1____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36___closed__2____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_ = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36___closed__2____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36___closed__2____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36___closed__3____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_ = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36___closed__3____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36___closed__3____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36___closed__4____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_ = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36___closed__4____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36___closed__4____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36___closed__5____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_ = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36___closed__5____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36___closed__5____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36___closed__6____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_ = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36___closed__6____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36___closed__6____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_);
if (builtin) {res = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__36____x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
