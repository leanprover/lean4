// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.ForallProp
// Imports: public import Lean.Meta.Tactic.Grind.Types public import Init.Grind.Propagator import Init.Simproc import Init.Grind.Norm import Lean.Meta.Tactic.Grind.PropagatorAttr import Lean.Meta.Tactic.Grind.Propagate import Lean.Meta.Tactic.Grind.Internalize import Lean.Meta.Tactic.Grind.Simp import Lean.Meta.Tactic.Grind.Anchor import Lean.Meta.Tactic.Grind.EqResolution import Lean.Meta.Tactic.Grind.SynthInstance
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
static lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__1;
lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__12;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__6;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__29;
lean_object* l_Lean_Meta_Grind_addNewRawFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_AnchorRef_matches(lean_object*, uint64_t);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__1;
lean_object* l_Lean_Meta_Grind_synthInstanceMeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__16;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateExistsDown___closed__5;
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__2;
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__7;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__25;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__5_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__3;
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static double l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__0;
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__5_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_;
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__0(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__6;
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__19;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__5;
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__5;
uint8_t lean_usize_dec_eq(size_t, size_t);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__20;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__3;
lean_object* l_Lean_Expr_bvar___override(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__1(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_Meta_Grind_getAnchor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getAnchorRefs___redArg(lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateExistsDown___closed__0;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__2;
static lean_object* l_Lean_Meta_Grind_propagateExistsDown___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateExistsDown___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_115310127____hygCtx___hyg_8_();
static lean_object* l_Lean_Meta_Grind_simpForall___closed__12;
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__1;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__6;
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__30;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof_spec__0(uint64_t, lean_object*, size_t, size_t);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__0;
static lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_activateTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__3;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__1;
size_t lean_usize_of_nat(lean_object*);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__11;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__9;
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__8;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__15;
lean_object* lean_st_ref_take(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_();
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateExistsDown___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_115310127____hygCtx___hyg_8____boxed(lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__2;
static lean_object* l_Lean_Meta_Grind_propagateExistsDown___closed__6;
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__0;
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__12;
static lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__5;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__17;
lean_object* l_Lean_Meta_Grind_eqResolution(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__1;
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_();
double lean_float_of_nat(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_;
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__31;
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__7;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__18;
lean_object* l_Lean_Meta_Simp_Simprocs_add(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__4;
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__12;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0;
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__10;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__3;
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__11;
lean_object* lean_expr_lift_loose_bvars(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__13;
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__12;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__28;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__9;
static lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__9;
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__13;
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__8;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__23;
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11____boxed(lean_object*);
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
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addForallSimproc(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkForall(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__36;
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_Meta_Grind_mkEMatchTheoremUsingSingletonPatterns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__38;
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__0;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__40;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__3;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__4_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__4;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4;
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_mkAnd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addForallSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateExistsDown___closed__7;
static lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__0;
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f(lean_object*);
lean_object* l_Lean_Meta_Grind_alreadyInternalized___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__14;
lean_object* l_Lean_Meta_Grind_getSymbolPriorities___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqTrueProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__2;
lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__0;
static lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__10;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__13;
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__9;
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__2;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__26;
lean_object* l_Lean_Meta_Grind_isEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__4_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__5;
static lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__4;
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__39;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__24;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__4;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__8;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__6_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_;
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateExistsDown___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateExistsDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f___closed__0;
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_grind_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__0;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_;
uint8_t lean_usize_dec_lt(size_t, size_t);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__0;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10____boxed(lean_object*);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__33;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__9;
static lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__7;
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateExistsDown___closed__1;
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__11;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__32;
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__11;
static lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__2;
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__2;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__7;
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
lean_object* x_14; lean_object* x_53; uint8_t x_75; lean_object* x_76; lean_object* x_95; lean_object* x_117; 
x_117 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_3, x_4);
if (lean_obj_tag(x_117) == 0)
{
uint8_t x_118; 
x_118 = !lean_is_exclusive(x_117);
if (x_118 == 0)
{
lean_object* x_119; uint8_t x_120; 
x_119 = lean_ctor_get(x_117, 0);
x_120 = lean_unbox(x_119);
lean_dec(x_119);
if (x_120 == 0)
{
lean_object* x_121; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_121 = lean_box(0);
lean_ctor_set(x_117, 0, x_121);
return x_117;
}
else
{
lean_object* x_122; 
lean_free_object(x_117);
lean_inc_ref(x_2);
x_122 = l_Lean_Meta_Grind_isEqFalse___redArg(x_2, x_4, x_6, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; uint8_t x_124; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_unbox(x_123);
lean_dec(x_123);
if (x_124 == 0)
{
x_95 = x_122;
goto block_116;
}
else
{
lean_object* x_125; 
lean_dec_ref(x_122);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_3);
x_125 = l_Lean_Meta_isProp(x_3, x_9, x_10, x_11, x_12);
x_95 = x_125;
goto block_116;
}
}
else
{
x_95 = x_122;
goto block_116;
}
}
}
else
{
lean_object* x_126; uint8_t x_127; 
x_126 = lean_ctor_get(x_117, 0);
lean_inc(x_126);
lean_dec(x_117);
x_127 = lean_unbox(x_126);
lean_dec(x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_128 = lean_box(0);
x_129 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_129, 0, x_128);
return x_129;
}
else
{
lean_object* x_130; 
lean_inc_ref(x_2);
x_130 = l_Lean_Meta_Grind_isEqFalse___redArg(x_2, x_4, x_6, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; uint8_t x_132; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_unbox(x_131);
lean_dec(x_131);
if (x_132 == 0)
{
x_95 = x_130;
goto block_116;
}
else
{
lean_object* x_133; 
lean_dec_ref(x_130);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_3);
x_133 = l_Lean_Meta_isProp(x_3, x_9, x_10, x_11, x_12);
x_95 = x_133;
goto block_116;
}
}
else
{
x_95 = x_130;
goto block_116;
}
}
}
}
else
{
uint8_t x_134; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_134 = !lean_is_exclusive(x_117);
if (x_134 == 0)
{
return x_117;
}
else
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_117, 0);
lean_inc(x_135);
lean_dec(x_117);
x_136 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_136, 0, x_135);
return x_136;
}
}
block_52:
{
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_18 = lean_box(0);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; 
lean_free_object(x_14);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_19 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_6);
lean_inc(x_4);
lean_inc_ref(x_3);
x_21 = l_Lean_Meta_Grind_mkEqFalseProof(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4;
lean_inc_ref(x_2);
x_24 = l_Lean_mkApp4(x_23, x_2, x_3, x_20, x_22);
x_25 = l_Lean_Meta_Grind_pushEqFalse___redArg(x_2, x_24, x_4, x_6, x_9, x_10, x_11, x_12);
lean_dec_ref(x_6);
lean_dec(x_4);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_20);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_21, 0);
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_29 = !lean_is_exclusive(x_19);
if (x_29 == 0)
{
return x_19;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_19, 0);
lean_inc(x_30);
lean_dec(x_19);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_14, 0);
lean_inc(x_32);
lean_dec(x_14);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
else
{
lean_object* x_36; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_36 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_6);
lean_inc(x_4);
lean_inc_ref(x_3);
x_38 = l_Lean_Meta_Grind_mkEqFalseProof(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
x_40 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4;
lean_inc_ref(x_2);
x_41 = l_Lean_mkApp4(x_40, x_2, x_3, x_37, x_39);
x_42 = l_Lean_Meta_Grind_pushEqFalse___redArg(x_2, x_41, x_4, x_6, x_9, x_10, x_11, x_12);
lean_dec_ref(x_6);
lean_dec(x_4);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_37);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_43 = lean_ctor_get(x_38, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 x_44 = x_38;
} else {
 lean_dec_ref(x_38);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(1, 1, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_43);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_46 = lean_ctor_get(x_36, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 x_47 = x_36;
} else {
 lean_dec_ref(x_36);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 1, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_46);
return x_48;
}
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_49 = !lean_is_exclusive(x_14);
if (x_49 == 0)
{
return x_14;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_14, 0);
lean_inc(x_50);
lean_dec(x_14);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
}
block_74:
{
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec_ref(x_53);
x_55 = lean_unbox(x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_inc_ref(x_3);
x_56 = l_Lean_Meta_Grind_isEqFalse___redArg(x_3, x_4, x_6, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_unbox(x_57);
lean_dec(x_57);
if (x_58 == 0)
{
x_14 = x_56;
goto block_52;
}
else
{
lean_object* x_59; 
lean_dec_ref(x_56);
lean_inc_ref(x_1);
x_59 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_4, x_6, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_unbox(x_60);
lean_dec(x_60);
if (x_61 == 0)
{
x_14 = x_59;
goto block_52;
}
else
{
lean_object* x_62; 
lean_dec_ref(x_59);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_2);
x_62 = l_Lean_Meta_isProp(x_2, x_9, x_10, x_11, x_12);
x_14 = x_62;
goto block_52;
}
}
else
{
x_14 = x_59;
goto block_52;
}
}
}
else
{
x_14 = x_56;
goto block_52;
}
}
else
{
lean_object* x_63; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_6);
lean_inc(x_4);
lean_inc_ref(x_3);
x_63 = l_Lean_Meta_Grind_mkEqTrueProof(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
x_65 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__7;
x_66 = l_Lean_mkApp3(x_65, x_2, x_3, x_64);
x_67 = l_Lean_Meta_Grind_pushEqTrue___redArg(x_1, x_66, x_4, x_6, x_9, x_10, x_11, x_12);
lean_dec_ref(x_6);
lean_dec(x_4);
return x_67;
}
else
{
uint8_t x_68; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_68 = !lean_is_exclusive(x_63);
if (x_68 == 0)
{
return x_63;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_63, 0);
lean_inc(x_69);
lean_dec(x_63);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_71 = !lean_is_exclusive(x_53);
if (x_71 == 0)
{
return x_53;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_53, 0);
lean_inc(x_72);
lean_dec(x_53);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
}
block_94:
{
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec_ref(x_76);
x_78 = lean_unbox(x_77);
lean_dec(x_77);
if (x_78 == 0)
{
lean_object* x_79; 
lean_inc_ref(x_3);
x_79 = l_Lean_Meta_Grind_isEqTrue___redArg(x_3, x_4, x_6, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_unbox(x_80);
lean_dec(x_80);
if (x_81 == 0)
{
x_53 = x_79;
goto block_74;
}
else
{
lean_object* x_82; 
lean_dec_ref(x_79);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_2);
x_82 = l_Lean_Meta_isProp(x_2, x_9, x_10, x_11, x_12);
x_53 = x_82;
goto block_74;
}
}
else
{
x_53 = x_79;
goto block_74;
}
}
else
{
lean_object* x_83; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_6);
lean_inc(x_4);
lean_inc_ref(x_2);
x_83 = l_Lean_Meta_Grind_mkEqTrueProof(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
x_85 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__10;
lean_inc_ref(x_3);
x_86 = l_Lean_mkApp3(x_85, x_2, x_3, x_84);
x_87 = l_Lean_Meta_Grind_pushEqCore___redArg(x_1, x_3, x_86, x_75, x_4, x_6, x_9, x_10, x_11, x_12);
lean_dec_ref(x_6);
lean_dec(x_4);
return x_87;
}
else
{
uint8_t x_88; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_88 = !lean_is_exclusive(x_83);
if (x_88 == 0)
{
return x_83;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_83, 0);
lean_inc(x_89);
lean_dec(x_83);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
return x_90;
}
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_91 = !lean_is_exclusive(x_76);
if (x_91 == 0)
{
return x_76;
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_76, 0);
lean_inc(x_92);
lean_dec(x_76);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
return x_93;
}
}
}
block_116:
{
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; uint8_t x_97; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
lean_dec_ref(x_95);
x_97 = lean_unbox(x_96);
if (x_97 == 0)
{
lean_object* x_98; 
lean_inc_ref(x_2);
x_98 = l_Lean_Meta_Grind_isEqTrue___redArg(x_2, x_4, x_6, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; uint8_t x_100; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_unbox(x_99);
lean_dec(x_99);
if (x_100 == 0)
{
uint8_t x_101; 
x_101 = lean_unbox(x_96);
lean_dec(x_96);
x_75 = x_101;
x_76 = x_98;
goto block_94;
}
else
{
lean_object* x_102; uint8_t x_103; 
lean_dec_ref(x_98);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_3);
x_102 = l_Lean_Meta_isProp(x_3, x_9, x_10, x_11, x_12);
x_103 = lean_unbox(x_96);
lean_dec(x_96);
x_75 = x_103;
x_76 = x_102;
goto block_94;
}
}
else
{
uint8_t x_104; 
x_104 = lean_unbox(x_96);
lean_dec(x_96);
x_75 = x_104;
x_76 = x_98;
goto block_94;
}
}
else
{
lean_object* x_105; 
lean_dec(x_96);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc_ref(x_6);
lean_inc(x_4);
lean_inc_ref(x_2);
x_105 = l_Lean_Meta_Grind_mkEqFalseProof(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
lean_dec_ref(x_105);
x_107 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__13;
x_108 = l_Lean_mkApp3(x_107, x_2, x_3, x_106);
x_109 = l_Lean_Meta_Grind_pushEqTrue___redArg(x_1, x_108, x_4, x_6, x_9, x_10, x_11, x_12);
lean_dec_ref(x_6);
lean_dec(x_4);
return x_109;
}
else
{
uint8_t x_110; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_110 = !lean_is_exclusive(x_105);
if (x_110 == 0)
{
return x_105;
}
else
{
lean_object* x_111; lean_object* x_112; 
x_111 = lean_ctor_get(x_105, 0);
lean_inc(x_111);
lean_dec(x_105);
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_111);
return x_112;
}
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_113 = !lean_is_exclusive(x_95);
if (x_113 == 0)
{
return x_95;
}
else
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_95, 0);
lean_inc(x_114);
lean_dec(x_95);
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_114);
return x_115;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
static lean_object* _init_l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trace", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 13);
x_9 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__1;
x_10 = l_Lean_Name_append(x_9, x_1);
x_11 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(x_8, x_4, x_10);
lean_dec(x_10);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(x_1, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1_spec__1(x_2, x_3, x_4, x_5, x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_st_ref_take(x_6);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 4);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; double x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__0;
x_18 = 0;
x_19 = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__1;
x_20 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set_float(x_20, sizeof(void*)*2, x_17);
lean_ctor_set_float(x_20, sizeof(void*)*2 + 8, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*2 + 16, x_18);
x_21 = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__2;
x_22 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_11);
lean_ctor_set(x_22, 2, x_21);
lean_inc(x_8);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_PersistentArray_push___redArg(x_16, x_23);
lean_ctor_set(x_14, 0, x_24);
x_25 = lean_st_ref_set(x_6, x_12);
x_26 = lean_box(0);
lean_ctor_set(x_9, 0, x_26);
return x_9;
}
else
{
uint64_t x_27; lean_object* x_28; double x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
lean_dec(x_14);
x_29 = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__0;
x_30 = 0;
x_31 = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__1;
x_32 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_float(x_32, sizeof(void*)*2, x_29);
lean_ctor_set_float(x_32, sizeof(void*)*2 + 8, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 16, x_30);
x_33 = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__2;
x_34 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_11);
lean_ctor_set(x_34, 2, x_33);
lean_inc(x_8);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_PersistentArray_push___redArg(x_28, x_35);
x_37 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set_uint64(x_37, sizeof(void*)*1, x_27);
lean_ctor_set(x_12, 4, x_37);
x_38 = lean_st_ref_set(x_6, x_12);
x_39 = lean_box(0);
lean_ctor_set(x_9, 0, x_39);
return x_9;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint64_t x_49; lean_object* x_50; lean_object* x_51; double x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_40 = lean_ctor_get(x_12, 4);
x_41 = lean_ctor_get(x_12, 0);
x_42 = lean_ctor_get(x_12, 1);
x_43 = lean_ctor_get(x_12, 2);
x_44 = lean_ctor_get(x_12, 3);
x_45 = lean_ctor_get(x_12, 5);
x_46 = lean_ctor_get(x_12, 6);
x_47 = lean_ctor_get(x_12, 7);
x_48 = lean_ctor_get(x_12, 8);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_40);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_12);
x_49 = lean_ctor_get_uint64(x_40, sizeof(void*)*1);
x_50 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_50);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_51 = x_40;
} else {
 lean_dec_ref(x_40);
 x_51 = lean_box(0);
}
x_52 = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__0;
x_53 = 0;
x_54 = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__1;
x_55 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set_float(x_55, sizeof(void*)*2, x_52);
lean_ctor_set_float(x_55, sizeof(void*)*2 + 8, x_52);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 16, x_53);
x_56 = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__2;
x_57 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_11);
lean_ctor_set(x_57, 2, x_56);
lean_inc(x_8);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_8);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_PersistentArray_push___redArg(x_50, x_58);
if (lean_is_scalar(x_51)) {
 x_60 = lean_alloc_ctor(0, 1, 8);
} else {
 x_60 = x_51;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set_uint64(x_60, sizeof(void*)*1, x_49);
x_61 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_61, 0, x_41);
lean_ctor_set(x_61, 1, x_42);
lean_ctor_set(x_61, 2, x_43);
lean_ctor_set(x_61, 3, x_44);
lean_ctor_set(x_61, 4, x_60);
lean_ctor_set(x_61, 5, x_45);
lean_ctor_set(x_61, 6, x_46);
lean_ctor_set(x_61, 7, x_47);
lean_ctor_set(x_61, 8, x_48);
x_62 = lean_st_ref_set(x_6, x_61);
x_63 = lean_box(0);
lean_ctor_set(x_9, 0, x_63);
return x_9;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint64_t x_76; lean_object* x_77; lean_object* x_78; double x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_64 = lean_ctor_get(x_9, 0);
lean_inc(x_64);
lean_dec(x_9);
x_65 = lean_st_ref_take(x_6);
x_66 = lean_ctor_get(x_65, 4);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_65, 0);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 2);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_65, 3);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_65, 5);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_65, 6);
lean_inc_ref(x_72);
x_73 = lean_ctor_get(x_65, 7);
lean_inc_ref(x_73);
x_74 = lean_ctor_get(x_65, 8);
lean_inc_ref(x_74);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 lean_ctor_release(x_65, 2);
 lean_ctor_release(x_65, 3);
 lean_ctor_release(x_65, 4);
 lean_ctor_release(x_65, 5);
 lean_ctor_release(x_65, 6);
 lean_ctor_release(x_65, 7);
 lean_ctor_release(x_65, 8);
 x_75 = x_65;
} else {
 lean_dec_ref(x_65);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get_uint64(x_66, sizeof(void*)*1);
x_77 = lean_ctor_get(x_66, 0);
lean_inc_ref(x_77);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 x_78 = x_66;
} else {
 lean_dec_ref(x_66);
 x_78 = lean_box(0);
}
x_79 = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__0;
x_80 = 0;
x_81 = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__1;
x_82 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_82, 0, x_1);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set_float(x_82, sizeof(void*)*2, x_79);
lean_ctor_set_float(x_82, sizeof(void*)*2 + 8, x_79);
lean_ctor_set_uint8(x_82, sizeof(void*)*2 + 16, x_80);
x_83 = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__2;
x_84 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_64);
lean_ctor_set(x_84, 2, x_83);
lean_inc(x_8);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_8);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_PersistentArray_push___redArg(x_77, x_85);
if (lean_is_scalar(x_78)) {
 x_87 = lean_alloc_ctor(0, 1, 8);
} else {
 x_87 = x_78;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set_uint64(x_87, sizeof(void*)*1, x_76);
if (lean_is_scalar(x_75)) {
 x_88 = lean_alloc_ctor(0, 9, 0);
} else {
 x_88 = x_75;
}
lean_ctor_set(x_88, 0, x_67);
lean_ctor_set(x_88, 1, x_68);
lean_ctor_set(x_88, 2, x_69);
lean_ctor_set(x_88, 3, x_70);
lean_ctor_set(x_88, 4, x_87);
lean_ctor_set(x_88, 5, x_71);
lean_ctor_set(x_88, 6, x_72);
lean_ctor_set(x_88, 7, x_73);
lean_ctor_set(x_88, 8, x_74);
x_89 = lean_st_ref_set(x_6, x_88);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
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
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("isEqTrue, ", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_propagateForallPropUp___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_propagateForallPropUp___closed__11;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get(x_1, 2);
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_37 = l_Lean_Meta_Grind_propagateForallPropUp___closed__6;
x_126 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(x_37, x_9);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
lean_dec_ref(x_126);
x_128 = lean_unbox(x_127);
lean_dec(x_127);
if (x_128 == 0)
{
x_83 = x_2;
x_84 = x_3;
x_85 = x_4;
x_86 = x_5;
x_87 = x_6;
x_88 = x_7;
x_89 = x_8;
x_90 = x_9;
x_91 = x_10;
x_92 = lean_box(0);
goto block_125;
}
else
{
lean_object* x_129; 
x_129 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; 
lean_dec_ref(x_129);
lean_inc_ref(x_1);
x_130 = l_Lean_MessageData_ofExpr(x_1);
x_131 = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(x_37, x_130, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_131) == 0)
{
lean_dec_ref(x_131);
x_83 = x_2;
x_84 = x_3;
x_85 = x_4;
x_86 = x_5;
x_87 = x_6;
x_88 = x_7;
x_89 = x_8;
x_90 = x_9;
x_91 = x_10;
x_92 = lean_box(0);
goto block_125;
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_131;
}
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_129;
}
}
block_36:
{
lean_object* x_28; 
lean_inc(x_26);
lean_inc_ref(x_25);
lean_inc(x_24);
lean_inc_ref(x_23);
x_28 = l_Lean_Meta_Simp_Result_getProof(x_19, x_23, x_24, x_25, x_26);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = l_Lean_Meta_Grind_propagateForallPropUp___closed__2;
lean_inc_ref(x_17);
lean_inc_ref(x_13);
x_31 = l_Lean_mkApp5(x_30, x_13, x_20, x_17, x_18, x_29);
x_32 = l_Lean_Meta_Grind_pushEqCore___redArg(x_1, x_17, x_31, x_16, x_21, x_22, x_23, x_24, x_25, x_26);
lean_dec_ref(x_22);
lean_dec(x_21);
return x_32;
}
else
{
uint8_t x_33; 
lean_dec(x_26);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec_ref(x_1);
x_33 = !lean_is_exclusive(x_28);
if (x_33 == 0)
{
return x_28;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_28, 0);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
block_82:
{
lean_object* x_49; 
lean_inc(x_47);
lean_inc_ref(x_46);
lean_inc(x_45);
lean_inc_ref(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc_ref(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc_ref(x_13);
x_49 = l_Lean_Meta_Grind_mkEqTrueProof(x_13, x_39, x_40, x_41, x_42, x_43, x_44, x_45, x_46, x_47);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
lean_inc(x_50);
lean_inc_ref(x_13);
x_51 = l_Lean_Meta_mkOfEqTrueCore(x_13, x_50);
x_52 = lean_expr_instantiate1(x_14, x_51);
lean_dec_ref(x_51);
lean_inc(x_47);
lean_inc_ref(x_46);
lean_inc(x_45);
lean_inc_ref(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc_ref(x_41);
lean_inc(x_40);
lean_inc(x_39);
x_53 = lean_grind_preprocess(x_52, x_39, x_40, x_41, x_42, x_43, x_44, x_45, x_46, x_47);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec_ref(x_53);
x_55 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_39);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
x_57 = lean_ctor_get(x_54, 0);
lean_inc_ref(x_57);
x_58 = lean_box(0);
lean_inc(x_47);
lean_inc_ref(x_46);
lean_inc(x_45);
lean_inc_ref(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc_ref(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc_ref(x_57);
x_59 = lean_grind_internalize(x_57, x_56, x_58, x_39, x_40, x_41, x_42, x_43, x_44, x_45, x_46, x_47);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
lean_dec_ref(x_59);
x_60 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(x_37, x_46);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_dec_ref(x_60);
lean_inc_ref(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
x_62 = l_Lean_mkLambda(x_12, x_15, x_13, x_14);
x_63 = lean_unbox(x_61);
lean_dec(x_61);
if (x_63 == 0)
{
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_40);
x_16 = x_38;
x_17 = x_57;
x_18 = x_50;
x_19 = x_54;
x_20 = x_62;
x_21 = x_39;
x_22 = x_41;
x_23 = x_44;
x_24 = x_45;
x_25 = x_46;
x_26 = x_47;
x_27 = lean_box(0);
goto block_36;
}
else
{
lean_object* x_64; 
x_64 = l_Lean_Meta_Grind_updateLastTag(x_39, x_40, x_41, x_42, x_43, x_44, x_45, x_46, x_47);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_40);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec_ref(x_64);
x_65 = l_Lean_Meta_Grind_propagateForallPropUp___closed__8;
lean_inc_ref(x_57);
x_66 = l_Lean_MessageData_ofExpr(x_57);
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_Meta_Grind_propagateForallPropUp___closed__10;
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
lean_inc_ref(x_1);
x_70 = l_Lean_indentExpr(x_1);
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(x_37, x_71, x_44, x_45, x_46, x_47);
if (lean_obj_tag(x_72) == 0)
{
lean_dec_ref(x_72);
x_16 = x_38;
x_17 = x_57;
x_18 = x_50;
x_19 = x_54;
x_20 = x_62;
x_21 = x_39;
x_22 = x_41;
x_23 = x_44;
x_24 = x_45;
x_25 = x_46;
x_26 = x_47;
x_27 = lean_box(0);
goto block_36;
}
else
{
lean_dec_ref(x_62);
lean_dec_ref(x_57);
lean_dec(x_54);
lean_dec(x_50);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec_ref(x_41);
lean_dec(x_39);
lean_dec_ref(x_1);
return x_72;
}
}
else
{
lean_dec_ref(x_62);
lean_dec_ref(x_57);
lean_dec(x_54);
lean_dec(x_50);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec_ref(x_41);
lean_dec(x_39);
lean_dec_ref(x_1);
return x_64;
}
}
}
else
{
lean_dec_ref(x_57);
lean_dec(x_54);
lean_dec(x_50);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec_ref(x_1);
return x_59;
}
}
else
{
uint8_t x_73; 
lean_dec(x_54);
lean_dec(x_50);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec_ref(x_1);
x_73 = !lean_is_exclusive(x_55);
if (x_73 == 0)
{
return x_55;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_55, 0);
lean_inc(x_74);
lean_dec(x_55);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_50);
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec_ref(x_1);
x_76 = !lean_is_exclusive(x_53);
if (x_76 == 0)
{
return x_53;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_53, 0);
lean_inc(x_77);
lean_dec(x_53);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_47);
lean_dec_ref(x_46);
lean_dec(x_45);
lean_dec_ref(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec_ref(x_1);
x_79 = !lean_is_exclusive(x_49);
if (x_79 == 0)
{
return x_49;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_49, 0);
lean_inc(x_80);
lean_dec(x_49);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
block_125:
{
uint8_t x_93; 
x_93 = l_Lean_Expr_hasLooseBVars(x_14);
if (x_93 == 0)
{
lean_object* x_94; 
lean_inc_ref(x_14);
lean_inc_ref(x_13);
x_94 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp(x_1, x_13, x_14, x_83, x_84, x_85, x_86, x_87, x_88, x_89, x_90, x_91);
return x_94;
}
else
{
lean_object* x_95; 
lean_inc_ref(x_13);
x_95 = l_Lean_Meta_Grind_isEqTrue___redArg(x_13, x_83, x_85, x_88, x_89, x_90, x_91);
if (lean_obj_tag(x_95) == 0)
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_ctor_get(x_95, 0);
x_98 = lean_unbox(x_97);
lean_dec(x_97);
if (x_98 == 0)
{
lean_object* x_99; 
lean_dec(x_91);
lean_dec_ref(x_90);
lean_dec(x_89);
lean_dec_ref(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec_ref(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec_ref(x_1);
x_99 = lean_box(0);
lean_ctor_set(x_95, 0, x_99);
return x_95;
}
else
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; uint8_t x_103; 
lean_free_object(x_95);
x_100 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(x_37, x_90);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
lean_dec_ref(x_100);
x_102 = 0;
x_103 = lean_unbox(x_101);
lean_dec(x_101);
if (x_103 == 0)
{
x_38 = x_102;
x_39 = x_83;
x_40 = x_84;
x_41 = x_85;
x_42 = x_86;
x_43 = x_87;
x_44 = x_88;
x_45 = x_89;
x_46 = x_90;
x_47 = x_91;
x_48 = lean_box(0);
goto block_82;
}
else
{
lean_object* x_104; 
x_104 = l_Lean_Meta_Grind_updateLastTag(x_83, x_84, x_85, x_86, x_87, x_88, x_89, x_90, x_91);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec_ref(x_104);
x_105 = l_Lean_Meta_Grind_propagateForallPropUp___closed__12;
lean_inc_ref(x_1);
x_106 = l_Lean_MessageData_ofExpr(x_1);
x_107 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
x_108 = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(x_37, x_107, x_88, x_89, x_90, x_91);
if (lean_obj_tag(x_108) == 0)
{
lean_dec_ref(x_108);
x_38 = x_102;
x_39 = x_83;
x_40 = x_84;
x_41 = x_85;
x_42 = x_86;
x_43 = x_87;
x_44 = x_88;
x_45 = x_89;
x_46 = x_90;
x_47 = x_91;
x_48 = lean_box(0);
goto block_82;
}
else
{
lean_dec(x_91);
lean_dec_ref(x_90);
lean_dec(x_89);
lean_dec_ref(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec_ref(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec_ref(x_1);
return x_108;
}
}
else
{
lean_dec(x_91);
lean_dec_ref(x_90);
lean_dec(x_89);
lean_dec_ref(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec_ref(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec_ref(x_1);
return x_104;
}
}
}
}
else
{
lean_object* x_109; uint8_t x_110; 
x_109 = lean_ctor_get(x_95, 0);
lean_inc(x_109);
lean_dec(x_95);
x_110 = lean_unbox(x_109);
lean_dec(x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_91);
lean_dec_ref(x_90);
lean_dec(x_89);
lean_dec_ref(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec_ref(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec_ref(x_1);
x_111 = lean_box(0);
x_112 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_112, 0, x_111);
return x_112;
}
else
{
lean_object* x_113; lean_object* x_114; uint8_t x_115; uint8_t x_116; 
x_113 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(x_37, x_90);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
lean_dec_ref(x_113);
x_115 = 0;
x_116 = lean_unbox(x_114);
lean_dec(x_114);
if (x_116 == 0)
{
x_38 = x_115;
x_39 = x_83;
x_40 = x_84;
x_41 = x_85;
x_42 = x_86;
x_43 = x_87;
x_44 = x_88;
x_45 = x_89;
x_46 = x_90;
x_47 = x_91;
x_48 = lean_box(0);
goto block_82;
}
else
{
lean_object* x_117; 
x_117 = l_Lean_Meta_Grind_updateLastTag(x_83, x_84, x_85, x_86, x_87, x_88, x_89, x_90, x_91);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec_ref(x_117);
x_118 = l_Lean_Meta_Grind_propagateForallPropUp___closed__12;
lean_inc_ref(x_1);
x_119 = l_Lean_MessageData_ofExpr(x_1);
x_120 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
x_121 = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(x_37, x_120, x_88, x_89, x_90, x_91);
if (lean_obj_tag(x_121) == 0)
{
lean_dec_ref(x_121);
x_38 = x_115;
x_39 = x_83;
x_40 = x_84;
x_41 = x_85;
x_42 = x_86;
x_43 = x_87;
x_44 = x_88;
x_45 = x_89;
x_46 = x_90;
x_47 = x_91;
x_48 = lean_box(0);
goto block_82;
}
else
{
lean_dec(x_91);
lean_dec_ref(x_90);
lean_dec(x_89);
lean_dec_ref(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec_ref(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec_ref(x_1);
return x_121;
}
}
else
{
lean_dec(x_91);
lean_dec_ref(x_90);
lean_dec(x_89);
lean_dec_ref(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec_ref(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec_ref(x_1);
return x_117;
}
}
}
}
}
else
{
uint8_t x_122; 
lean_dec(x_91);
lean_dec_ref(x_90);
lean_dec(x_89);
lean_dec_ref(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec_ref(x_85);
lean_dec(x_84);
lean_dec(x_83);
lean_dec_ref(x_1);
x_122 = !lean_is_exclusive(x_95);
if (x_122 == 0)
{
return x_95;
}
else
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_95, 0);
lean_inc(x_123);
lean_dec(x_95);
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_123);
return x_124;
}
}
}
}
}
else
{
lean_object* x_132; lean_object* x_133; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_132 = lean_box(0);
x_133 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_133, 0, x_132);
return x_133;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropUp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_propagateForallPropUp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(x_1, x_2, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
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
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_5);
x_6 = l_Lean_Expr_appFnCleanup___redArg(x_2);
x_7 = l_Lean_Expr_isApp(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = l_Lean_Expr_appFnCleanup___redArg(x_6);
x_10 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f___closed__1;
x_11 = l_Lean_Expr_isConstOf(x_9, x_10);
lean_dec_ref(x_9);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec_ref(x_5);
x_12 = lean_box(0);
return x_12;
}
else
{
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
lean_dec_ref(x_5);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec_ref(x_5);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_10 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___closed__0;
x_11 = 0;
x_12 = 1;
x_13 = l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(x_1, x_10, x_2, x_3, x_4, x_11, x_11, x_12, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; uint8_t x_22; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_22 = l_Lean_Exception_isInterrupt(x_14);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = l_Lean_Exception_isRuntime(x_14);
x_15 = x_23;
goto block_21;
}
else
{
lean_dec(x_14);
x_15 = x_22;
goto block_21;
}
block_21:
{
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
x_18 = lean_box(0);
lean_ctor_set_tag(x_13, 0);
lean_ctor_set(x_13, 0, x_18);
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
else
{
return x_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__0(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 3);
x_7 = lean_array_uget(x_2, x_3);
x_8 = l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__0(x_6, x_7);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__1(x_1, x_2, x_5, x_6);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_8 = lean_box(x_7);
return x_8;
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
x_6 = 1;
return x_6;
}
else
{
if (x_5 == 0)
{
return x_5;
}
else
{
size_t x_7; size_t x_8; uint8_t x_9; 
x_7 = 0;
x_8 = lean_usize_of_nat(x_4);
x_9 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__1(x_2, x_1, x_7, x_8);
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
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof_spec__0(uint64_t x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lean_Meta_Grind_AnchorRef_matches(x_6, x_1);
lean_dec(x_6);
if (x_7 == 0)
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
goto _start;
}
else
{
return x_7;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint64_t x_5; size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof_spec__0(x_5, x_2, x_6, x_7);
lean_dec_ref(x_2);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_getAnchorRefs___redArg(x_3);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_14; lean_object* x_15; 
lean_free_object(x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_15 = lean_infer_type(x_1, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l_Lean_Meta_Grind_getAnchor(x_16, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_array_get_size(x_14);
x_22 = lean_nat_dec_lt(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_19);
lean_dec(x_14);
x_23 = lean_box(x_22);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
else
{
if (x_22 == 0)
{
lean_object* x_24; 
lean_dec(x_19);
lean_dec(x_14);
x_24 = lean_box(x_22);
lean_ctor_set(x_17, 0, x_24);
return x_17;
}
else
{
size_t x_25; size_t x_26; uint64_t x_27; uint8_t x_28; lean_object* x_29; 
x_25 = 0;
x_26 = lean_usize_of_nat(x_21);
x_27 = lean_unbox_uint64(x_19);
lean_dec(x_19);
x_28 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof_spec__0(x_27, x_14, x_25, x_26);
lean_dec(x_14);
x_29 = lean_box(x_28);
lean_ctor_set(x_17, 0, x_29);
return x_17;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_17, 0);
lean_inc(x_30);
lean_dec(x_17);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_array_get_size(x_14);
x_33 = lean_nat_dec_lt(x_31, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_30);
lean_dec(x_14);
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
else
{
if (x_33 == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_30);
lean_dec(x_14);
x_36 = lean_box(x_33);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
else
{
size_t x_38; size_t x_39; uint64_t x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_38 = 0;
x_39 = lean_usize_of_nat(x_32);
x_40 = lean_unbox_uint64(x_30);
lean_dec(x_30);
x_41 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof_spec__0(x_40, x_14, x_38, x_39);
lean_dec(x_14);
x_42 = lean_box(x_41);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_14);
x_44 = !lean_is_exclusive(x_17);
if (x_44 == 0)
{
return x_17;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_17, 0);
lean_inc(x_45);
lean_dec(x_17);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_47 = !lean_is_exclusive(x_15);
if (x_47 == 0)
{
return x_15;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_15, 0);
lean_inc(x_48);
lean_dec(x_15);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; lean_object* x_51; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_50 = 1;
x_51 = lean_box(x_50);
lean_ctor_set(x_11, 0, x_51);
return x_11;
}
}
else
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_11, 0);
lean_inc(x_52);
lean_dec(x_11);
if (lean_obj_tag(x_52) == 1)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_54 = lean_infer_type(x_1, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec_ref(x_54);
x_56 = l_Lean_Meta_Grind_getAnchor(x_55, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 x_58 = x_56;
} else {
 lean_dec_ref(x_56);
 x_58 = lean_box(0);
}
x_59 = lean_unsigned_to_nat(0u);
x_60 = lean_array_get_size(x_53);
x_61 = lean_nat_dec_lt(x_59, x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_57);
lean_dec(x_53);
x_62 = lean_box(x_61);
if (lean_is_scalar(x_58)) {
 x_63 = lean_alloc_ctor(0, 1, 0);
} else {
 x_63 = x_58;
}
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
else
{
if (x_61 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_57);
lean_dec(x_53);
x_64 = lean_box(x_61);
if (lean_is_scalar(x_58)) {
 x_65 = lean_alloc_ctor(0, 1, 0);
} else {
 x_65 = x_58;
}
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
else
{
size_t x_66; size_t x_67; uint64_t x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; 
x_66 = 0;
x_67 = lean_usize_of_nat(x_60);
x_68 = lean_unbox_uint64(x_57);
lean_dec(x_57);
x_69 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof_spec__0(x_68, x_53, x_66, x_67);
lean_dec(x_53);
x_70 = lean_box(x_69);
if (lean_is_scalar(x_58)) {
 x_71 = lean_alloc_ctor(0, 1, 0);
} else {
 x_71 = x_58;
}
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_53);
x_72 = lean_ctor_get(x_56, 0);
lean_inc(x_72);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 x_73 = x_56;
} else {
 lean_dec_ref(x_56);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(1, 1, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_72);
return x_74;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_53);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_75 = lean_ctor_get(x_54, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 x_76 = x_54;
} else {
 lean_dec_ref(x_54);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 1, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_75);
return x_77;
}
}
else
{
uint8_t x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_52);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_78 = 1;
x_79 = lean_box(x_78);
x_80 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_1);
x_81 = !lean_is_exclusive(x_11);
if (x_81 == 0)
{
return x_11;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_11, 0);
lean_inc(x_82);
lean_dec(x_11);
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_82);
return x_83;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; uint8_t x_22; 
x_22 = lean_usize_dec_lt(x_4, x_3);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_5);
return x_23;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_array_uget(x_2, x_4);
x_25 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(x_5, x_24);
if (x_25 == 0)
{
lean_dec(x_24);
x_16 = x_5;
x_17 = lean_box(0);
goto block_21;
}
else
{
lean_object* x_26; 
lean_inc(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
lean_inc(x_24);
x_26 = l_Lean_Meta_Grind_activateTheorem(x_24, x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_26);
x_27 = lean_ctor_get(x_24, 3);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_array_push(x_5, x_27);
x_16 = x_28;
x_17 = lean_box(0);
goto block_21;
}
else
{
uint8_t x_29; 
lean_dec(x_24);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
}
block_21:
{
size_t x_18; size_t x_19; 
x_18 = 1;
x_19 = lean_usize_add(x_4, x_18);
x_4 = x_19;
x_5 = x_16;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_17 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_18 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0(x_1, x_2, x_16, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec_ref(x_2);
return x_18;
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_130; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_130 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_241; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
lean_dec_ref(x_130);
lean_inc(x_131);
x_241 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f(x_131);
if (lean_obj_tag(x_241) == 1)
{
uint8_t x_242; 
x_242 = !lean_is_exclusive(x_241);
if (x_242 == 0)
{
x_132 = x_241;
x_133 = x_2;
x_134 = x_3;
x_135 = x_4;
x_136 = x_5;
x_137 = x_6;
x_138 = x_7;
x_139 = x_8;
x_140 = x_9;
x_141 = x_10;
x_142 = lean_box(0);
goto block_240;
}
else
{
lean_object* x_243; lean_object* x_244; 
x_243 = lean_ctor_get(x_241, 0);
lean_inc(x_243);
lean_dec(x_241);
x_244 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_244, 0, x_243);
x_132 = x_244;
x_133 = x_2;
x_134 = x_3;
x_135 = x_4;
x_136 = x_5;
x_137 = x_6;
x_138 = x_7;
x_139 = x_8;
x_140 = x_9;
x_141 = x_10;
x_142 = lean_box(0);
goto block_240;
}
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; uint8_t x_248; 
lean_dec(x_241);
x_245 = lean_st_ref_take(x_2);
x_246 = lean_ctor_get(x_245, 0);
lean_inc_ref(x_246);
x_247 = lean_ctor_get(x_246, 13);
lean_inc_ref(x_247);
x_248 = !lean_is_exclusive(x_245);
if (x_248 == 0)
{
lean_object* x_249; uint8_t x_250; 
x_249 = lean_ctor_get(x_245, 0);
lean_dec(x_249);
x_250 = !lean_is_exclusive(x_246);
if (x_250 == 0)
{
lean_object* x_251; uint8_t x_252; 
x_251 = lean_ctor_get(x_246, 13);
lean_dec(x_251);
x_252 = !lean_is_exclusive(x_247);
if (x_252 == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_253 = lean_ctor_get(x_247, 8);
x_254 = lean_unsigned_to_nat(1u);
x_255 = lean_nat_add(x_253, x_254);
lean_ctor_set(x_247, 8, x_255);
x_256 = lean_st_ref_set(x_2, x_245);
x_257 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__3;
x_258 = lean_name_append_index_after(x_257, x_253);
x_259 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_259, 0, x_258);
x_132 = x_259;
x_133 = x_2;
x_134 = x_3;
x_135 = x_4;
x_136 = x_5;
x_137 = x_6;
x_138 = x_7;
x_139 = x_8;
x_140 = x_9;
x_141 = x_10;
x_142 = lean_box(0);
goto block_240;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_260 = lean_ctor_get(x_247, 0);
x_261 = lean_ctor_get(x_247, 1);
x_262 = lean_ctor_get(x_247, 2);
x_263 = lean_ctor_get(x_247, 3);
x_264 = lean_ctor_get(x_247, 4);
x_265 = lean_ctor_get(x_247, 5);
x_266 = lean_ctor_get(x_247, 6);
x_267 = lean_ctor_get(x_247, 7);
x_268 = lean_ctor_get(x_247, 8);
x_269 = lean_ctor_get(x_247, 9);
x_270 = lean_ctor_get(x_247, 10);
lean_inc(x_270);
lean_inc(x_269);
lean_inc(x_268);
lean_inc(x_267);
lean_inc(x_266);
lean_inc(x_265);
lean_inc(x_264);
lean_inc(x_263);
lean_inc(x_262);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_247);
x_271 = lean_unsigned_to_nat(1u);
x_272 = lean_nat_add(x_268, x_271);
x_273 = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(x_273, 0, x_260);
lean_ctor_set(x_273, 1, x_261);
lean_ctor_set(x_273, 2, x_262);
lean_ctor_set(x_273, 3, x_263);
lean_ctor_set(x_273, 4, x_264);
lean_ctor_set(x_273, 5, x_265);
lean_ctor_set(x_273, 6, x_266);
lean_ctor_set(x_273, 7, x_267);
lean_ctor_set(x_273, 8, x_272);
lean_ctor_set(x_273, 9, x_269);
lean_ctor_set(x_273, 10, x_270);
lean_ctor_set(x_246, 13, x_273);
x_274 = lean_st_ref_set(x_2, x_245);
x_275 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__3;
x_276 = lean_name_append_index_after(x_275, x_268);
x_277 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_277, 0, x_276);
x_132 = x_277;
x_133 = x_2;
x_134 = x_3;
x_135 = x_4;
x_136 = x_5;
x_137 = x_6;
x_138 = x_7;
x_139 = x_8;
x_140 = x_9;
x_141 = x_10;
x_142 = lean_box(0);
goto block_240;
}
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_278 = lean_ctor_get(x_246, 0);
x_279 = lean_ctor_get(x_246, 1);
x_280 = lean_ctor_get(x_246, 2);
x_281 = lean_ctor_get(x_246, 3);
x_282 = lean_ctor_get(x_246, 4);
x_283 = lean_ctor_get(x_246, 5);
x_284 = lean_ctor_get(x_246, 6);
x_285 = lean_ctor_get(x_246, 7);
x_286 = lean_ctor_get(x_246, 8);
x_287 = lean_ctor_get_uint8(x_246, sizeof(void*)*18);
x_288 = lean_ctor_get(x_246, 9);
x_289 = lean_ctor_get(x_246, 10);
x_290 = lean_ctor_get(x_246, 11);
x_291 = lean_ctor_get(x_246, 12);
x_292 = lean_ctor_get(x_246, 14);
x_293 = lean_ctor_get(x_246, 15);
x_294 = lean_ctor_get(x_246, 16);
x_295 = lean_ctor_get(x_246, 17);
lean_inc(x_295);
lean_inc(x_294);
lean_inc(x_293);
lean_inc(x_292);
lean_inc(x_291);
lean_inc(x_290);
lean_inc(x_289);
lean_inc(x_288);
lean_inc(x_286);
lean_inc(x_285);
lean_inc(x_284);
lean_inc(x_283);
lean_inc(x_282);
lean_inc(x_281);
lean_inc(x_280);
lean_inc(x_279);
lean_inc(x_278);
lean_dec(x_246);
x_296 = lean_ctor_get(x_247, 0);
lean_inc_ref(x_296);
x_297 = lean_ctor_get(x_247, 1);
lean_inc(x_297);
x_298 = lean_ctor_get(x_247, 2);
lean_inc_ref(x_298);
x_299 = lean_ctor_get(x_247, 3);
lean_inc_ref(x_299);
x_300 = lean_ctor_get(x_247, 4);
lean_inc(x_300);
x_301 = lean_ctor_get(x_247, 5);
lean_inc(x_301);
x_302 = lean_ctor_get(x_247, 6);
lean_inc(x_302);
x_303 = lean_ctor_get(x_247, 7);
lean_inc_ref(x_303);
x_304 = lean_ctor_get(x_247, 8);
lean_inc(x_304);
x_305 = lean_ctor_get(x_247, 9);
lean_inc_ref(x_305);
x_306 = lean_ctor_get(x_247, 10);
lean_inc_ref(x_306);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 lean_ctor_release(x_247, 2);
 lean_ctor_release(x_247, 3);
 lean_ctor_release(x_247, 4);
 lean_ctor_release(x_247, 5);
 lean_ctor_release(x_247, 6);
 lean_ctor_release(x_247, 7);
 lean_ctor_release(x_247, 8);
 lean_ctor_release(x_247, 9);
 lean_ctor_release(x_247, 10);
 x_307 = x_247;
} else {
 lean_dec_ref(x_247);
 x_307 = lean_box(0);
}
x_308 = lean_unsigned_to_nat(1u);
x_309 = lean_nat_add(x_304, x_308);
if (lean_is_scalar(x_307)) {
 x_310 = lean_alloc_ctor(0, 11, 0);
} else {
 x_310 = x_307;
}
lean_ctor_set(x_310, 0, x_296);
lean_ctor_set(x_310, 1, x_297);
lean_ctor_set(x_310, 2, x_298);
lean_ctor_set(x_310, 3, x_299);
lean_ctor_set(x_310, 4, x_300);
lean_ctor_set(x_310, 5, x_301);
lean_ctor_set(x_310, 6, x_302);
lean_ctor_set(x_310, 7, x_303);
lean_ctor_set(x_310, 8, x_309);
lean_ctor_set(x_310, 9, x_305);
lean_ctor_set(x_310, 10, x_306);
x_311 = lean_alloc_ctor(0, 18, 1);
lean_ctor_set(x_311, 0, x_278);
lean_ctor_set(x_311, 1, x_279);
lean_ctor_set(x_311, 2, x_280);
lean_ctor_set(x_311, 3, x_281);
lean_ctor_set(x_311, 4, x_282);
lean_ctor_set(x_311, 5, x_283);
lean_ctor_set(x_311, 6, x_284);
lean_ctor_set(x_311, 7, x_285);
lean_ctor_set(x_311, 8, x_286);
lean_ctor_set(x_311, 9, x_288);
lean_ctor_set(x_311, 10, x_289);
lean_ctor_set(x_311, 11, x_290);
lean_ctor_set(x_311, 12, x_291);
lean_ctor_set(x_311, 13, x_310);
lean_ctor_set(x_311, 14, x_292);
lean_ctor_set(x_311, 15, x_293);
lean_ctor_set(x_311, 16, x_294);
lean_ctor_set(x_311, 17, x_295);
lean_ctor_set_uint8(x_311, sizeof(void*)*18, x_287);
lean_ctor_set(x_245, 0, x_311);
x_312 = lean_st_ref_set(x_2, x_245);
x_313 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__3;
x_314 = lean_name_append_index_after(x_313, x_304);
x_315 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_315, 0, x_314);
x_132 = x_315;
x_133 = x_2;
x_134 = x_3;
x_135 = x_4;
x_136 = x_5;
x_137 = x_6;
x_138 = x_7;
x_139 = x_8;
x_140 = x_9;
x_141 = x_10;
x_142 = lean_box(0);
goto block_240;
}
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; uint8_t x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_316 = lean_ctor_get(x_245, 1);
lean_inc(x_316);
lean_dec(x_245);
x_317 = lean_ctor_get(x_246, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_246, 1);
lean_inc_ref(x_318);
x_319 = lean_ctor_get(x_246, 2);
lean_inc_ref(x_319);
x_320 = lean_ctor_get(x_246, 3);
lean_inc_ref(x_320);
x_321 = lean_ctor_get(x_246, 4);
lean_inc_ref(x_321);
x_322 = lean_ctor_get(x_246, 5);
lean_inc_ref(x_322);
x_323 = lean_ctor_get(x_246, 6);
lean_inc_ref(x_323);
x_324 = lean_ctor_get(x_246, 7);
lean_inc_ref(x_324);
x_325 = lean_ctor_get(x_246, 8);
lean_inc_ref(x_325);
x_326 = lean_ctor_get_uint8(x_246, sizeof(void*)*18);
x_327 = lean_ctor_get(x_246, 9);
lean_inc(x_327);
x_328 = lean_ctor_get(x_246, 10);
lean_inc_ref(x_328);
x_329 = lean_ctor_get(x_246, 11);
lean_inc_ref(x_329);
x_330 = lean_ctor_get(x_246, 12);
lean_inc_ref(x_330);
x_331 = lean_ctor_get(x_246, 14);
lean_inc_ref(x_331);
x_332 = lean_ctor_get(x_246, 15);
lean_inc_ref(x_332);
x_333 = lean_ctor_get(x_246, 16);
lean_inc_ref(x_333);
x_334 = lean_ctor_get(x_246, 17);
lean_inc_ref(x_334);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 lean_ctor_release(x_246, 2);
 lean_ctor_release(x_246, 3);
 lean_ctor_release(x_246, 4);
 lean_ctor_release(x_246, 5);
 lean_ctor_release(x_246, 6);
 lean_ctor_release(x_246, 7);
 lean_ctor_release(x_246, 8);
 lean_ctor_release(x_246, 9);
 lean_ctor_release(x_246, 10);
 lean_ctor_release(x_246, 11);
 lean_ctor_release(x_246, 12);
 lean_ctor_release(x_246, 13);
 lean_ctor_release(x_246, 14);
 lean_ctor_release(x_246, 15);
 lean_ctor_release(x_246, 16);
 lean_ctor_release(x_246, 17);
 x_335 = x_246;
} else {
 lean_dec_ref(x_246);
 x_335 = lean_box(0);
}
x_336 = lean_ctor_get(x_247, 0);
lean_inc_ref(x_336);
x_337 = lean_ctor_get(x_247, 1);
lean_inc(x_337);
x_338 = lean_ctor_get(x_247, 2);
lean_inc_ref(x_338);
x_339 = lean_ctor_get(x_247, 3);
lean_inc_ref(x_339);
x_340 = lean_ctor_get(x_247, 4);
lean_inc(x_340);
x_341 = lean_ctor_get(x_247, 5);
lean_inc(x_341);
x_342 = lean_ctor_get(x_247, 6);
lean_inc(x_342);
x_343 = lean_ctor_get(x_247, 7);
lean_inc_ref(x_343);
x_344 = lean_ctor_get(x_247, 8);
lean_inc(x_344);
x_345 = lean_ctor_get(x_247, 9);
lean_inc_ref(x_345);
x_346 = lean_ctor_get(x_247, 10);
lean_inc_ref(x_346);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 lean_ctor_release(x_247, 2);
 lean_ctor_release(x_247, 3);
 lean_ctor_release(x_247, 4);
 lean_ctor_release(x_247, 5);
 lean_ctor_release(x_247, 6);
 lean_ctor_release(x_247, 7);
 lean_ctor_release(x_247, 8);
 lean_ctor_release(x_247, 9);
 lean_ctor_release(x_247, 10);
 x_347 = x_247;
} else {
 lean_dec_ref(x_247);
 x_347 = lean_box(0);
}
x_348 = lean_unsigned_to_nat(1u);
x_349 = lean_nat_add(x_344, x_348);
if (lean_is_scalar(x_347)) {
 x_350 = lean_alloc_ctor(0, 11, 0);
} else {
 x_350 = x_347;
}
lean_ctor_set(x_350, 0, x_336);
lean_ctor_set(x_350, 1, x_337);
lean_ctor_set(x_350, 2, x_338);
lean_ctor_set(x_350, 3, x_339);
lean_ctor_set(x_350, 4, x_340);
lean_ctor_set(x_350, 5, x_341);
lean_ctor_set(x_350, 6, x_342);
lean_ctor_set(x_350, 7, x_343);
lean_ctor_set(x_350, 8, x_349);
lean_ctor_set(x_350, 9, x_345);
lean_ctor_set(x_350, 10, x_346);
if (lean_is_scalar(x_335)) {
 x_351 = lean_alloc_ctor(0, 18, 1);
} else {
 x_351 = x_335;
}
lean_ctor_set(x_351, 0, x_317);
lean_ctor_set(x_351, 1, x_318);
lean_ctor_set(x_351, 2, x_319);
lean_ctor_set(x_351, 3, x_320);
lean_ctor_set(x_351, 4, x_321);
lean_ctor_set(x_351, 5, x_322);
lean_ctor_set(x_351, 6, x_323);
lean_ctor_set(x_351, 7, x_324);
lean_ctor_set(x_351, 8, x_325);
lean_ctor_set(x_351, 9, x_327);
lean_ctor_set(x_351, 10, x_328);
lean_ctor_set(x_351, 11, x_329);
lean_ctor_set(x_351, 12, x_330);
lean_ctor_set(x_351, 13, x_350);
lean_ctor_set(x_351, 14, x_331);
lean_ctor_set(x_351, 15, x_332);
lean_ctor_set(x_351, 16, x_333);
lean_ctor_set(x_351, 17, x_334);
lean_ctor_set_uint8(x_351, sizeof(void*)*18, x_326);
x_352 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_352, 0, x_351);
lean_ctor_set(x_352, 1, x_316);
x_353 = lean_st_ref_set(x_2, x_352);
x_354 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__3;
x_355 = lean_name_append_index_after(x_354, x_344);
x_356 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_356, 0, x_355);
x_132 = x_356;
x_133 = x_2;
x_134 = x_3;
x_135 = x_4;
x_136 = x_5;
x_137 = x_6;
x_138 = x_7;
x_139 = x_8;
x_140 = x_9;
x_141 = x_10;
x_142 = lean_box(0);
goto block_240;
}
}
block_240:
{
lean_object* x_143; lean_object* x_144; 
lean_inc_ref(x_1);
x_143 = l_Lean_Meta_mkOfEqTrueCore(x_1, x_131);
lean_inc(x_141);
lean_inc_ref(x_140);
lean_inc(x_139);
lean_inc_ref(x_138);
lean_inc_ref(x_143);
x_144 = l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(x_143, x_134, x_135, x_136, x_137, x_138, x_139, x_140, x_141);
if (lean_obj_tag(x_144) == 0)
{
uint8_t x_145; 
x_145 = !lean_is_exclusive(x_144);
if (x_145 == 0)
{
lean_object* x_146; uint8_t x_147; 
x_146 = lean_ctor_get(x_144, 0);
x_147 = lean_unbox(x_146);
lean_dec(x_146);
if (x_147 == 0)
{
lean_object* x_148; 
lean_dec_ref(x_143);
lean_dec(x_141);
lean_dec_ref(x_140);
lean_dec(x_139);
lean_dec_ref(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec_ref(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec_ref(x_132);
lean_dec_ref(x_1);
x_148 = lean_box(0);
lean_ctor_set(x_144, 0, x_148);
return x_144;
}
else
{
lean_object* x_149; lean_object* x_150; 
lean_free_object(x_144);
x_149 = lean_st_ref_get(x_133);
x_150 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_133);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
lean_dec_ref(x_150);
x_152 = l_Lean_Meta_Grind_getSymbolPriorities___redArg(x_135);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
lean_dec_ref(x_152);
x_154 = lean_unsigned_to_nat(1000u);
x_155 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___closed__0;
x_156 = 0;
lean_inc(x_141);
lean_inc_ref(x_140);
lean_inc(x_139);
lean_inc_ref(x_138);
lean_inc(x_153);
lean_inc_ref(x_143);
lean_inc_ref(x_132);
x_157 = l_Lean_Meta_Grind_mkEMatchTheoremUsingSingletonPatterns(x_132, x_155, x_143, x_154, x_153, x_156, x_138, x_139, x_140, x_141);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; size_t x_159; size_t x_160; lean_object* x_161; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
lean_dec_ref(x_157);
x_159 = lean_array_size(x_158);
x_160 = 0;
lean_inc(x_141);
lean_inc_ref(x_140);
lean_inc(x_139);
lean_inc_ref(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc_ref(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_151);
x_161 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0(x_151, x_158, x_159, x_160, x_155, x_133, x_134, x_135, x_136, x_137, x_138, x_139, x_140, x_141);
lean_dec(x_158);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
lean_dec_ref(x_161);
x_163 = lean_box(6);
lean_inc(x_141);
lean_inc_ref(x_140);
lean_inc(x_139);
lean_inc_ref(x_138);
lean_inc(x_153);
lean_inc_ref(x_143);
lean_inc_ref(x_132);
x_164 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(x_132, x_143, x_163, x_153, x_138, x_139, x_140, x_141);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_165 = lean_ctor_get(x_149, 0);
lean_inc_ref(x_165);
lean_dec(x_149);
x_166 = lean_ctor_get(x_165, 13);
lean_inc_ref(x_166);
lean_dec_ref(x_165);
x_167 = lean_ctor_get(x_166, 3);
lean_inc_ref(x_167);
lean_dec_ref(x_166);
x_168 = lean_ctor_get(x_164, 0);
lean_inc(x_168);
lean_dec_ref(x_164);
if (lean_obj_tag(x_168) == 1)
{
lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_169 = lean_ctor_get(x_167, 2);
lean_inc(x_169);
lean_dec_ref(x_167);
x_170 = lean_ctor_get(x_168, 0);
lean_inc(x_170);
lean_dec_ref(x_168);
x_171 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(x_162, x_170);
if (x_171 == 0)
{
lean_dec(x_170);
x_103 = x_143;
x_104 = x_151;
x_105 = x_169;
x_106 = x_156;
x_107 = x_153;
x_108 = x_132;
x_109 = x_162;
x_110 = x_133;
x_111 = x_134;
x_112 = x_135;
x_113 = x_136;
x_114 = x_137;
x_115 = x_138;
x_116 = x_139;
x_117 = x_140;
x_118 = x_141;
x_119 = lean_box(0);
goto block_129;
}
else
{
lean_object* x_172; 
lean_inc(x_141);
lean_inc_ref(x_140);
lean_inc(x_139);
lean_inc_ref(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc_ref(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_151);
lean_inc(x_170);
x_172 = l_Lean_Meta_Grind_activateTheorem(x_170, x_151, x_133, x_134, x_135, x_136, x_137, x_138, x_139, x_140, x_141);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; 
lean_dec_ref(x_172);
x_173 = lean_ctor_get(x_170, 3);
lean_inc(x_173);
lean_dec(x_170);
x_174 = lean_array_push(x_162, x_173);
x_103 = x_143;
x_104 = x_151;
x_105 = x_169;
x_106 = x_156;
x_107 = x_153;
x_108 = x_132;
x_109 = x_174;
x_110 = x_133;
x_111 = x_134;
x_112 = x_135;
x_113 = x_136;
x_114 = x_137;
x_115 = x_138;
x_116 = x_139;
x_117 = x_140;
x_118 = x_141;
x_119 = lean_box(0);
goto block_129;
}
else
{
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_162);
lean_dec(x_153);
lean_dec(x_151);
lean_dec_ref(x_143);
lean_dec(x_141);
lean_dec_ref(x_140);
lean_dec(x_139);
lean_dec_ref(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec_ref(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec_ref(x_132);
lean_dec_ref(x_1);
return x_172;
}
}
}
else
{
lean_object* x_175; 
lean_dec(x_168);
x_175 = lean_ctor_get(x_167, 2);
lean_inc(x_175);
lean_dec_ref(x_167);
x_103 = x_143;
x_104 = x_151;
x_105 = x_175;
x_106 = x_156;
x_107 = x_153;
x_108 = x_132;
x_109 = x_162;
x_110 = x_133;
x_111 = x_134;
x_112 = x_135;
x_113 = x_136;
x_114 = x_137;
x_115 = x_138;
x_116 = x_139;
x_117 = x_140;
x_118 = x_141;
x_119 = lean_box(0);
goto block_129;
}
}
else
{
uint8_t x_176; 
lean_dec(x_162);
lean_dec(x_153);
lean_dec(x_151);
lean_dec(x_149);
lean_dec_ref(x_143);
lean_dec(x_141);
lean_dec_ref(x_140);
lean_dec(x_139);
lean_dec_ref(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec_ref(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec_ref(x_132);
lean_dec_ref(x_1);
x_176 = !lean_is_exclusive(x_164);
if (x_176 == 0)
{
return x_164;
}
else
{
lean_object* x_177; lean_object* x_178; 
x_177 = lean_ctor_get(x_164, 0);
lean_inc(x_177);
lean_dec(x_164);
x_178 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_178, 0, x_177);
return x_178;
}
}
}
else
{
uint8_t x_179; 
lean_dec(x_153);
lean_dec(x_151);
lean_dec(x_149);
lean_dec_ref(x_143);
lean_dec(x_141);
lean_dec_ref(x_140);
lean_dec(x_139);
lean_dec_ref(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec_ref(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec_ref(x_132);
lean_dec_ref(x_1);
x_179 = !lean_is_exclusive(x_161);
if (x_179 == 0)
{
return x_161;
}
else
{
lean_object* x_180; lean_object* x_181; 
x_180 = lean_ctor_get(x_161, 0);
lean_inc(x_180);
lean_dec(x_161);
x_181 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_181, 0, x_180);
return x_181;
}
}
}
else
{
uint8_t x_182; 
lean_dec(x_153);
lean_dec(x_151);
lean_dec(x_149);
lean_dec_ref(x_143);
lean_dec(x_141);
lean_dec_ref(x_140);
lean_dec(x_139);
lean_dec_ref(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec_ref(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec_ref(x_132);
lean_dec_ref(x_1);
x_182 = !lean_is_exclusive(x_157);
if (x_182 == 0)
{
return x_157;
}
else
{
lean_object* x_183; lean_object* x_184; 
x_183 = lean_ctor_get(x_157, 0);
lean_inc(x_183);
lean_dec(x_157);
x_184 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_184, 0, x_183);
return x_184;
}
}
}
else
{
uint8_t x_185; 
lean_dec(x_151);
lean_dec(x_149);
lean_dec_ref(x_143);
lean_dec(x_141);
lean_dec_ref(x_140);
lean_dec(x_139);
lean_dec_ref(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec_ref(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec_ref(x_132);
lean_dec_ref(x_1);
x_185 = !lean_is_exclusive(x_152);
if (x_185 == 0)
{
return x_152;
}
else
{
lean_object* x_186; lean_object* x_187; 
x_186 = lean_ctor_get(x_152, 0);
lean_inc(x_186);
lean_dec(x_152);
x_187 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_187, 0, x_186);
return x_187;
}
}
}
else
{
uint8_t x_188; 
lean_dec(x_149);
lean_dec_ref(x_143);
lean_dec(x_141);
lean_dec_ref(x_140);
lean_dec(x_139);
lean_dec_ref(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec_ref(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec_ref(x_132);
lean_dec_ref(x_1);
x_188 = !lean_is_exclusive(x_150);
if (x_188 == 0)
{
return x_150;
}
else
{
lean_object* x_189; lean_object* x_190; 
x_189 = lean_ctor_get(x_150, 0);
lean_inc(x_189);
lean_dec(x_150);
x_190 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_190, 0, x_189);
return x_190;
}
}
}
}
else
{
lean_object* x_191; uint8_t x_192; 
x_191 = lean_ctor_get(x_144, 0);
lean_inc(x_191);
lean_dec(x_144);
x_192 = lean_unbox(x_191);
lean_dec(x_191);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; 
lean_dec_ref(x_143);
lean_dec(x_141);
lean_dec_ref(x_140);
lean_dec(x_139);
lean_dec_ref(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec_ref(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec_ref(x_132);
lean_dec_ref(x_1);
x_193 = lean_box(0);
x_194 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_194, 0, x_193);
return x_194;
}
else
{
lean_object* x_195; lean_object* x_196; 
x_195 = lean_st_ref_get(x_133);
x_196 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_133);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
lean_dec_ref(x_196);
x_198 = l_Lean_Meta_Grind_getSymbolPriorities___redArg(x_135);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; uint8_t x_202; lean_object* x_203; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
lean_dec_ref(x_198);
x_200 = lean_unsigned_to_nat(1000u);
x_201 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___closed__0;
x_202 = 0;
lean_inc(x_141);
lean_inc_ref(x_140);
lean_inc(x_139);
lean_inc_ref(x_138);
lean_inc(x_199);
lean_inc_ref(x_143);
lean_inc_ref(x_132);
x_203 = l_Lean_Meta_Grind_mkEMatchTheoremUsingSingletonPatterns(x_132, x_201, x_143, x_200, x_199, x_202, x_138, x_139, x_140, x_141);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; size_t x_205; size_t x_206; lean_object* x_207; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
lean_dec_ref(x_203);
x_205 = lean_array_size(x_204);
x_206 = 0;
lean_inc(x_141);
lean_inc_ref(x_140);
lean_inc(x_139);
lean_inc_ref(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc_ref(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_197);
x_207 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0(x_197, x_204, x_205, x_206, x_201, x_133, x_134, x_135, x_136, x_137, x_138, x_139, x_140, x_141);
lean_dec(x_204);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
lean_dec_ref(x_207);
x_209 = lean_box(6);
lean_inc(x_141);
lean_inc_ref(x_140);
lean_inc(x_139);
lean_inc_ref(x_138);
lean_inc(x_199);
lean_inc_ref(x_143);
lean_inc_ref(x_132);
x_210 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(x_132, x_143, x_209, x_199, x_138, x_139, x_140, x_141);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_211 = lean_ctor_get(x_195, 0);
lean_inc_ref(x_211);
lean_dec(x_195);
x_212 = lean_ctor_get(x_211, 13);
lean_inc_ref(x_212);
lean_dec_ref(x_211);
x_213 = lean_ctor_get(x_212, 3);
lean_inc_ref(x_213);
lean_dec_ref(x_212);
x_214 = lean_ctor_get(x_210, 0);
lean_inc(x_214);
lean_dec_ref(x_210);
if (lean_obj_tag(x_214) == 1)
{
lean_object* x_215; lean_object* x_216; uint8_t x_217; 
x_215 = lean_ctor_get(x_213, 2);
lean_inc(x_215);
lean_dec_ref(x_213);
x_216 = lean_ctor_get(x_214, 0);
lean_inc(x_216);
lean_dec_ref(x_214);
x_217 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(x_208, x_216);
if (x_217 == 0)
{
lean_dec(x_216);
x_103 = x_143;
x_104 = x_197;
x_105 = x_215;
x_106 = x_202;
x_107 = x_199;
x_108 = x_132;
x_109 = x_208;
x_110 = x_133;
x_111 = x_134;
x_112 = x_135;
x_113 = x_136;
x_114 = x_137;
x_115 = x_138;
x_116 = x_139;
x_117 = x_140;
x_118 = x_141;
x_119 = lean_box(0);
goto block_129;
}
else
{
lean_object* x_218; 
lean_inc(x_141);
lean_inc_ref(x_140);
lean_inc(x_139);
lean_inc_ref(x_138);
lean_inc(x_137);
lean_inc(x_136);
lean_inc_ref(x_135);
lean_inc(x_134);
lean_inc(x_133);
lean_inc(x_197);
lean_inc(x_216);
x_218 = l_Lean_Meta_Grind_activateTheorem(x_216, x_197, x_133, x_134, x_135, x_136, x_137, x_138, x_139, x_140, x_141);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; 
lean_dec_ref(x_218);
x_219 = lean_ctor_get(x_216, 3);
lean_inc(x_219);
lean_dec(x_216);
x_220 = lean_array_push(x_208, x_219);
x_103 = x_143;
x_104 = x_197;
x_105 = x_215;
x_106 = x_202;
x_107 = x_199;
x_108 = x_132;
x_109 = x_220;
x_110 = x_133;
x_111 = x_134;
x_112 = x_135;
x_113 = x_136;
x_114 = x_137;
x_115 = x_138;
x_116 = x_139;
x_117 = x_140;
x_118 = x_141;
x_119 = lean_box(0);
goto block_129;
}
else
{
lean_dec(x_216);
lean_dec(x_215);
lean_dec(x_208);
lean_dec(x_199);
lean_dec(x_197);
lean_dec_ref(x_143);
lean_dec(x_141);
lean_dec_ref(x_140);
lean_dec(x_139);
lean_dec_ref(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec_ref(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec_ref(x_132);
lean_dec_ref(x_1);
return x_218;
}
}
}
else
{
lean_object* x_221; 
lean_dec(x_214);
x_221 = lean_ctor_get(x_213, 2);
lean_inc(x_221);
lean_dec_ref(x_213);
x_103 = x_143;
x_104 = x_197;
x_105 = x_221;
x_106 = x_202;
x_107 = x_199;
x_108 = x_132;
x_109 = x_208;
x_110 = x_133;
x_111 = x_134;
x_112 = x_135;
x_113 = x_136;
x_114 = x_137;
x_115 = x_138;
x_116 = x_139;
x_117 = x_140;
x_118 = x_141;
x_119 = lean_box(0);
goto block_129;
}
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec(x_208);
lean_dec(x_199);
lean_dec(x_197);
lean_dec(x_195);
lean_dec_ref(x_143);
lean_dec(x_141);
lean_dec_ref(x_140);
lean_dec(x_139);
lean_dec_ref(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec_ref(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec_ref(x_132);
lean_dec_ref(x_1);
x_222 = lean_ctor_get(x_210, 0);
lean_inc(x_222);
if (lean_is_exclusive(x_210)) {
 lean_ctor_release(x_210, 0);
 x_223 = x_210;
} else {
 lean_dec_ref(x_210);
 x_223 = lean_box(0);
}
if (lean_is_scalar(x_223)) {
 x_224 = lean_alloc_ctor(1, 1, 0);
} else {
 x_224 = x_223;
}
lean_ctor_set(x_224, 0, x_222);
return x_224;
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_199);
lean_dec(x_197);
lean_dec(x_195);
lean_dec_ref(x_143);
lean_dec(x_141);
lean_dec_ref(x_140);
lean_dec(x_139);
lean_dec_ref(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec_ref(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec_ref(x_132);
lean_dec_ref(x_1);
x_225 = lean_ctor_get(x_207, 0);
lean_inc(x_225);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 x_226 = x_207;
} else {
 lean_dec_ref(x_207);
 x_226 = lean_box(0);
}
if (lean_is_scalar(x_226)) {
 x_227 = lean_alloc_ctor(1, 1, 0);
} else {
 x_227 = x_226;
}
lean_ctor_set(x_227, 0, x_225);
return x_227;
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_199);
lean_dec(x_197);
lean_dec(x_195);
lean_dec_ref(x_143);
lean_dec(x_141);
lean_dec_ref(x_140);
lean_dec(x_139);
lean_dec_ref(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec_ref(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec_ref(x_132);
lean_dec_ref(x_1);
x_228 = lean_ctor_get(x_203, 0);
lean_inc(x_228);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 x_229 = x_203;
} else {
 lean_dec_ref(x_203);
 x_229 = lean_box(0);
}
if (lean_is_scalar(x_229)) {
 x_230 = lean_alloc_ctor(1, 1, 0);
} else {
 x_230 = x_229;
}
lean_ctor_set(x_230, 0, x_228);
return x_230;
}
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_197);
lean_dec(x_195);
lean_dec_ref(x_143);
lean_dec(x_141);
lean_dec_ref(x_140);
lean_dec(x_139);
lean_dec_ref(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec_ref(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec_ref(x_132);
lean_dec_ref(x_1);
x_231 = lean_ctor_get(x_198, 0);
lean_inc(x_231);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 x_232 = x_198;
} else {
 lean_dec_ref(x_198);
 x_232 = lean_box(0);
}
if (lean_is_scalar(x_232)) {
 x_233 = lean_alloc_ctor(1, 1, 0);
} else {
 x_233 = x_232;
}
lean_ctor_set(x_233, 0, x_231);
return x_233;
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_195);
lean_dec_ref(x_143);
lean_dec(x_141);
lean_dec_ref(x_140);
lean_dec(x_139);
lean_dec_ref(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec_ref(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec_ref(x_132);
lean_dec_ref(x_1);
x_234 = lean_ctor_get(x_196, 0);
lean_inc(x_234);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 x_235 = x_196;
} else {
 lean_dec_ref(x_196);
 x_235 = lean_box(0);
}
if (lean_is_scalar(x_235)) {
 x_236 = lean_alloc_ctor(1, 1, 0);
} else {
 x_236 = x_235;
}
lean_ctor_set(x_236, 0, x_234);
return x_236;
}
}
}
}
else
{
uint8_t x_237; 
lean_dec_ref(x_143);
lean_dec(x_141);
lean_dec_ref(x_140);
lean_dec(x_139);
lean_dec_ref(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec_ref(x_135);
lean_dec(x_134);
lean_dec(x_133);
lean_dec_ref(x_132);
lean_dec_ref(x_1);
x_237 = !lean_is_exclusive(x_144);
if (x_237 == 0)
{
return x_144;
}
else
{
lean_object* x_238; lean_object* x_239; 
x_238 = lean_ctor_get(x_144, 0);
lean_inc(x_238);
lean_dec(x_144);
x_239 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_239, 0, x_238);
return x_239;
}
}
}
}
else
{
uint8_t x_357; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_357 = !lean_is_exclusive(x_130);
if (x_357 == 0)
{
return x_130;
}
else
{
lean_object* x_358; lean_object* x_359; 
x_358 = lean_ctor_get(x_130, 0);
lean_inc(x_358);
lean_dec(x_130);
x_359 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_359, 0, x_358);
return x_359;
}
}
block_71:
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_st_ref_get(x_13);
lean_dec(x_13);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
lean_dec(x_26);
x_27 = lean_ctor_get(x_25, 13);
lean_inc_ref(x_27);
lean_dec_ref(x_25);
x_28 = lean_ctor_get(x_27, 3);
lean_inc_ref(x_28);
lean_dec_ref(x_27);
x_29 = lean_ctor_get(x_28, 2);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = lean_nat_dec_eq(x_29, x_12);
lean_dec(x_12);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_free_object(x_23);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_1);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
else
{
lean_object* x_33; 
x_33 = l_Lean_Meta_Grind_getConfig___redArg(x_15);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get_uint8(x_35, sizeof(void*)*10 + 14);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
lean_free_object(x_23);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_1);
x_37 = lean_box(0);
lean_ctor_set(x_33, 0, x_37);
return x_33;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_free_object(x_33);
x_38 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1;
x_39 = l_Lean_indentExpr(x_1);
lean_ctor_set_tag(x_23, 7);
lean_ctor_set(x_23, 1, x_39);
lean_ctor_set(x_23, 0, x_38);
x_40 = l_Lean_Meta_Grind_reportIssue(x_23, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
return x_40;
}
}
else
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_33, 0);
lean_inc(x_41);
lean_dec(x_33);
x_42 = lean_ctor_get_uint8(x_41, sizeof(void*)*10 + 14);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_free_object(x_23);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_1);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1;
x_46 = l_Lean_indentExpr(x_1);
lean_ctor_set_tag(x_23, 7);
lean_ctor_set(x_23, 1, x_46);
lean_ctor_set(x_23, 0, x_45);
x_47 = l_Lean_Meta_Grind_reportIssue(x_23, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_free_object(x_23);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_1);
x_48 = !lean_is_exclusive(x_33);
if (x_48 == 0)
{
return x_33;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_33, 0);
lean_inc(x_49);
lean_dec(x_33);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_51 = lean_ctor_get(x_23, 0);
lean_inc(x_51);
lean_dec(x_23);
x_52 = lean_ctor_get(x_51, 13);
lean_inc_ref(x_52);
lean_dec_ref(x_51);
x_53 = lean_ctor_get(x_52, 3);
lean_inc_ref(x_53);
lean_dec_ref(x_52);
x_54 = lean_ctor_get(x_53, 2);
lean_inc(x_54);
lean_dec_ref(x_53);
x_55 = lean_nat_dec_eq(x_54, x_12);
lean_dec(x_12);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_1);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
else
{
lean_object* x_58; 
x_58 = l_Lean_Meta_Grind_getConfig___redArg(x_15);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
x_61 = lean_ctor_get_uint8(x_59, sizeof(void*)*10 + 14);
lean_dec(x_59);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_1);
x_62 = lean_box(0);
if (lean_is_scalar(x_60)) {
 x_63 = lean_alloc_ctor(0, 1, 0);
} else {
 x_63 = x_60;
}
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_60);
x_64 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1;
x_65 = l_Lean_indentExpr(x_1);
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lean_Meta_Grind_reportIssue(x_66, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec_ref(x_1);
x_68 = lean_ctor_get(x_58, 0);
lean_inc(x_68);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 x_69 = x_58;
} else {
 lean_dec_ref(x_58);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 1, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_68);
return x_70;
}
}
}
}
block_102:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_88 = lean_st_ref_get(x_78);
x_89 = lean_ctor_get(x_88, 0);
lean_inc_ref(x_89);
lean_dec(x_88);
x_90 = lean_ctor_get(x_89, 13);
lean_inc_ref(x_90);
lean_dec_ref(x_89);
x_91 = lean_ctor_get(x_90, 3);
lean_inc_ref(x_91);
lean_dec_ref(x_90);
x_92 = lean_ctor_get(x_91, 2);
lean_inc(x_92);
lean_dec_ref(x_91);
x_93 = lean_nat_dec_eq(x_92, x_74);
lean_dec(x_92);
if (x_93 == 0)
{
lean_dec_ref(x_77);
lean_dec_ref(x_75);
lean_dec(x_73);
lean_dec_ref(x_72);
x_12 = x_74;
x_13 = x_78;
x_14 = x_79;
x_15 = x_80;
x_16 = x_81;
x_17 = x_82;
x_18 = x_83;
x_19 = x_84;
x_20 = x_85;
x_21 = x_86;
x_22 = lean_box(0);
goto block_71;
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(x_94, 0, x_76);
lean_inc(x_86);
lean_inc_ref(x_85);
lean_inc(x_84);
lean_inc_ref(x_83);
x_95 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(x_77, x_72, x_94, x_75, x_83, x_84, x_85, x_86);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
lean_dec_ref(x_95);
if (lean_obj_tag(x_96) == 1)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
lean_dec_ref(x_96);
lean_inc(x_86);
lean_inc_ref(x_85);
lean_inc(x_84);
lean_inc_ref(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc_ref(x_80);
lean_inc(x_79);
lean_inc(x_78);
x_98 = l_Lean_Meta_Grind_activateTheorem(x_97, x_73, x_78, x_79, x_80, x_81, x_82, x_83, x_84, x_85, x_86);
if (lean_obj_tag(x_98) == 0)
{
lean_dec_ref(x_98);
x_12 = x_74;
x_13 = x_78;
x_14 = x_79;
x_15 = x_80;
x_16 = x_81;
x_17 = x_82;
x_18 = x_83;
x_19 = x_84;
x_20 = x_85;
x_21 = x_86;
x_22 = lean_box(0);
goto block_71;
}
else
{
lean_dec(x_86);
lean_dec_ref(x_85);
lean_dec(x_84);
lean_dec_ref(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec_ref(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_74);
lean_dec_ref(x_1);
return x_98;
}
}
else
{
lean_dec(x_96);
lean_dec(x_73);
x_12 = x_74;
x_13 = x_78;
x_14 = x_79;
x_15 = x_80;
x_16 = x_81;
x_17 = x_82;
x_18 = x_83;
x_19 = x_84;
x_20 = x_85;
x_21 = x_86;
x_22 = lean_box(0);
goto block_71;
}
}
else
{
uint8_t x_99; 
lean_dec(x_86);
lean_dec_ref(x_85);
lean_dec(x_84);
lean_dec_ref(x_83);
lean_dec(x_82);
lean_dec(x_81);
lean_dec_ref(x_80);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_74);
lean_dec(x_73);
lean_dec_ref(x_1);
x_99 = !lean_is_exclusive(x_95);
if (x_99 == 0)
{
return x_95;
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_95, 0);
lean_inc(x_100);
lean_dec(x_95);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
return x_101;
}
}
}
}
block_129:
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_box(7);
lean_inc(x_118);
lean_inc_ref(x_117);
lean_inc(x_116);
lean_inc_ref(x_115);
lean_inc_ref(x_107);
lean_inc_ref(x_103);
lean_inc_ref(x_108);
x_121 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(x_108, x_103, x_120, x_107, x_115, x_116, x_117, x_118);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
lean_dec_ref(x_121);
if (lean_obj_tag(x_122) == 1)
{
lean_object* x_123; uint8_t x_124; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
lean_dec_ref(x_122);
x_124 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(x_109, x_123);
lean_dec_ref(x_109);
if (x_124 == 0)
{
lean_dec(x_123);
x_72 = x_103;
x_73 = x_104;
x_74 = x_105;
x_75 = x_107;
x_76 = x_106;
x_77 = x_108;
x_78 = x_110;
x_79 = x_111;
x_80 = x_112;
x_81 = x_113;
x_82 = x_114;
x_83 = x_115;
x_84 = x_116;
x_85 = x_117;
x_86 = x_118;
x_87 = lean_box(0);
goto block_102;
}
else
{
lean_object* x_125; 
lean_inc(x_118);
lean_inc_ref(x_117);
lean_inc(x_116);
lean_inc_ref(x_115);
lean_inc(x_114);
lean_inc(x_113);
lean_inc_ref(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_104);
x_125 = l_Lean_Meta_Grind_activateTheorem(x_123, x_104, x_110, x_111, x_112, x_113, x_114, x_115, x_116, x_117, x_118);
if (lean_obj_tag(x_125) == 0)
{
lean_dec_ref(x_125);
x_72 = x_103;
x_73 = x_104;
x_74 = x_105;
x_75 = x_107;
x_76 = x_106;
x_77 = x_108;
x_78 = x_110;
x_79 = x_111;
x_80 = x_112;
x_81 = x_113;
x_82 = x_114;
x_83 = x_115;
x_84 = x_116;
x_85 = x_117;
x_86 = x_118;
x_87 = lean_box(0);
goto block_102;
}
else
{
lean_dec(x_118);
lean_dec_ref(x_117);
lean_dec(x_116);
lean_dec_ref(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec_ref(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec_ref(x_108);
lean_dec_ref(x_107);
lean_dec(x_105);
lean_dec(x_104);
lean_dec_ref(x_103);
lean_dec_ref(x_1);
return x_125;
}
}
}
else
{
lean_dec(x_122);
lean_dec_ref(x_109);
x_72 = x_103;
x_73 = x_104;
x_74 = x_105;
x_75 = x_107;
x_76 = x_106;
x_77 = x_108;
x_78 = x_110;
x_79 = x_111;
x_80 = x_112;
x_81 = x_113;
x_82 = x_114;
x_83 = x_115;
x_84 = x_116;
x_85 = x_117;
x_86 = x_118;
x_87 = lean_box(0);
goto block_102;
}
}
else
{
uint8_t x_126; 
lean_dec(x_118);
lean_dec_ref(x_117);
lean_dec(x_116);
lean_dec_ref(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec_ref(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec_ref(x_109);
lean_dec_ref(x_108);
lean_dec_ref(x_107);
lean_dec(x_105);
lean_dec(x_104);
lean_dec_ref(x_103);
lean_dec_ref(x_1);
x_126 = !lean_is_exclusive(x_121);
if (x_126 == 0)
{
return x_121;
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_121, 0);
lean_inc(x_127);
lean_dec(x_121);
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_127);
return x_128;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
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
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_110; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get(x_1, 2);
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_inc_ref(x_1);
x_110 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_4, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; uint8_t x_112; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
lean_dec_ref(x_110);
x_112 = lean_unbox(x_111);
lean_dec(x_111);
if (x_112 == 0)
{
lean_object* x_113; 
lean_inc_ref(x_1);
x_113 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_4, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_113) == 0)
{
uint8_t x_114; 
x_114 = !lean_is_exclusive(x_113);
if (x_114 == 0)
{
lean_object* x_115; uint8_t x_116; 
x_115 = lean_ctor_get(x_113, 0);
x_116 = lean_unbox(x_115);
lean_dec(x_115);
if (x_116 == 0)
{
lean_object* x_117; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_117 = lean_box(0);
lean_ctor_set(x_113, 0, x_117);
return x_113;
}
else
{
lean_object* x_118; 
lean_free_object(x_113);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_1);
x_118 = l_Lean_Meta_Grind_eqResolution(x_1, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
lean_dec_ref(x_118);
if (lean_obj_tag(x_119) == 1)
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 x_121 = x_119;
} else {
 lean_dec_ref(x_119);
 x_121 = lean_box(0);
}
x_122 = !lean_is_exclusive(x_120);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_123 = lean_ctor_get(x_120, 0);
x_124 = lean_ctor_get(x_120, 1);
x_150 = l_Lean_Meta_Grind_propagateForallPropDown___closed__1;
x_151 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(x_150, x_9);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
lean_dec_ref(x_151);
x_153 = lean_unbox(x_152);
lean_dec(x_152);
if (x_153 == 0)
{
lean_free_object(x_120);
x_125 = x_2;
x_126 = x_3;
x_127 = x_4;
x_128 = x_5;
x_129 = x_6;
x_130 = x_7;
x_131 = x_8;
x_132 = x_9;
x_133 = x_10;
x_134 = lean_box(0);
goto block_149;
}
else
{
lean_object* x_154; 
x_154 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec_ref(x_154);
lean_inc_ref(x_1);
x_155 = l_Lean_MessageData_ofExpr(x_1);
x_156 = l_Lean_Meta_Grind_propagateForallPropDown___closed__3;
lean_ctor_set_tag(x_120, 7);
lean_ctor_set(x_120, 1, x_156);
lean_ctor_set(x_120, 0, x_155);
lean_inc(x_123);
x_157 = l_Lean_MessageData_ofExpr(x_123);
x_158 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_158, 0, x_120);
lean_ctor_set(x_158, 1, x_157);
x_159 = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(x_150, x_158, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_159) == 0)
{
lean_dec_ref(x_159);
x_125 = x_2;
x_126 = x_3;
x_127 = x_4;
x_128 = x_5;
x_129 = x_6;
x_130 = x_7;
x_131 = x_8;
x_132 = x_9;
x_133 = x_10;
x_134 = lean_box(0);
goto block_149;
}
else
{
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_121);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_159;
}
}
else
{
lean_free_object(x_120);
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_121);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_154;
}
}
block_149:
{
lean_object* x_135; 
lean_inc(x_133);
lean_inc_ref(x_132);
lean_inc(x_131);
lean_inc_ref(x_130);
lean_inc(x_129);
lean_inc(x_128);
lean_inc_ref(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc_ref(x_1);
x_135 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_125, x_126, x_127, x_128, x_129, x_130, x_131, x_132, x_133);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
lean_dec_ref(x_135);
x_137 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_125);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
lean_dec_ref(x_137);
lean_inc_ref(x_1);
x_139 = l_Lean_Meta_mkOfEqTrueCore(x_1, x_136);
x_140 = l_Lean_Expr_app___override(x_124, x_139);
lean_inc_ref(x_1);
if (lean_is_scalar(x_121)) {
 x_141 = lean_alloc_ctor(4, 1, 0);
} else {
 x_141 = x_121;
 lean_ctor_set_tag(x_141, 4);
}
lean_ctor_set(x_141, 0, x_1);
lean_inc(x_133);
lean_inc_ref(x_132);
lean_inc(x_131);
lean_inc_ref(x_130);
x_142 = l_Lean_Meta_Grind_addNewRawFact(x_140, x_123, x_138, x_141, x_125, x_126, x_127, x_128, x_129, x_130, x_131, x_132, x_133);
if (lean_obj_tag(x_142) == 0)
{
lean_dec_ref(x_142);
x_64 = x_125;
x_65 = x_126;
x_66 = x_127;
x_67 = x_128;
x_68 = x_129;
x_69 = x_130;
x_70 = x_131;
x_71 = x_132;
x_72 = x_133;
x_73 = lean_box(0);
goto block_109;
}
else
{
lean_dec(x_133);
lean_dec_ref(x_132);
lean_dec(x_131);
lean_dec_ref(x_130);
lean_dec(x_129);
lean_dec(x_128);
lean_dec_ref(x_127);
lean_dec(x_126);
lean_dec(x_125);
lean_dec_ref(x_1);
return x_142;
}
}
else
{
uint8_t x_143; 
lean_dec(x_136);
lean_dec(x_133);
lean_dec_ref(x_132);
lean_dec(x_131);
lean_dec_ref(x_130);
lean_dec(x_129);
lean_dec(x_128);
lean_dec_ref(x_127);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_121);
lean_dec_ref(x_1);
x_143 = !lean_is_exclusive(x_137);
if (x_143 == 0)
{
return x_137;
}
else
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_137, 0);
lean_inc(x_144);
lean_dec(x_137);
x_145 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_145, 0, x_144);
return x_145;
}
}
}
else
{
uint8_t x_146; 
lean_dec(x_133);
lean_dec_ref(x_132);
lean_dec(x_131);
lean_dec_ref(x_130);
lean_dec(x_129);
lean_dec(x_128);
lean_dec_ref(x_127);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_121);
lean_dec_ref(x_1);
x_146 = !lean_is_exclusive(x_135);
if (x_146 == 0)
{
return x_135;
}
else
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_ctor_get(x_135, 0);
lean_inc(x_147);
lean_dec(x_135);
x_148 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_148, 0, x_147);
return x_148;
}
}
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_160 = lean_ctor_get(x_120, 0);
x_161 = lean_ctor_get(x_120, 1);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_120);
x_187 = l_Lean_Meta_Grind_propagateForallPropDown___closed__1;
x_188 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(x_187, x_9);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
lean_dec_ref(x_188);
x_190 = lean_unbox(x_189);
lean_dec(x_189);
if (x_190 == 0)
{
x_162 = x_2;
x_163 = x_3;
x_164 = x_4;
x_165 = x_5;
x_166 = x_6;
x_167 = x_7;
x_168 = x_8;
x_169 = x_9;
x_170 = x_10;
x_171 = lean_box(0);
goto block_186;
}
else
{
lean_object* x_191; 
x_191 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec_ref(x_191);
lean_inc_ref(x_1);
x_192 = l_Lean_MessageData_ofExpr(x_1);
x_193 = l_Lean_Meta_Grind_propagateForallPropDown___closed__3;
x_194 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
lean_inc(x_160);
x_195 = l_Lean_MessageData_ofExpr(x_160);
x_196 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
x_197 = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(x_187, x_196, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_197) == 0)
{
lean_dec_ref(x_197);
x_162 = x_2;
x_163 = x_3;
x_164 = x_4;
x_165 = x_5;
x_166 = x_6;
x_167 = x_7;
x_168 = x_8;
x_169 = x_9;
x_170 = x_10;
x_171 = lean_box(0);
goto block_186;
}
else
{
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_121);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_197;
}
}
else
{
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_121);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_191;
}
}
block_186:
{
lean_object* x_172; 
lean_inc(x_170);
lean_inc_ref(x_169);
lean_inc(x_168);
lean_inc_ref(x_167);
lean_inc(x_166);
lean_inc(x_165);
lean_inc_ref(x_164);
lean_inc(x_163);
lean_inc(x_162);
lean_inc_ref(x_1);
x_172 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_162, x_163, x_164, x_165, x_166, x_167, x_168, x_169, x_170);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
lean_dec_ref(x_172);
x_174 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_162);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
lean_dec_ref(x_174);
lean_inc_ref(x_1);
x_176 = l_Lean_Meta_mkOfEqTrueCore(x_1, x_173);
x_177 = l_Lean_Expr_app___override(x_161, x_176);
lean_inc_ref(x_1);
if (lean_is_scalar(x_121)) {
 x_178 = lean_alloc_ctor(4, 1, 0);
} else {
 x_178 = x_121;
 lean_ctor_set_tag(x_178, 4);
}
lean_ctor_set(x_178, 0, x_1);
lean_inc(x_170);
lean_inc_ref(x_169);
lean_inc(x_168);
lean_inc_ref(x_167);
x_179 = l_Lean_Meta_Grind_addNewRawFact(x_177, x_160, x_175, x_178, x_162, x_163, x_164, x_165, x_166, x_167, x_168, x_169, x_170);
if (lean_obj_tag(x_179) == 0)
{
lean_dec_ref(x_179);
x_64 = x_162;
x_65 = x_163;
x_66 = x_164;
x_67 = x_165;
x_68 = x_166;
x_69 = x_167;
x_70 = x_168;
x_71 = x_169;
x_72 = x_170;
x_73 = lean_box(0);
goto block_109;
}
else
{
lean_dec(x_170);
lean_dec_ref(x_169);
lean_dec(x_168);
lean_dec_ref(x_167);
lean_dec(x_166);
lean_dec(x_165);
lean_dec_ref(x_164);
lean_dec(x_163);
lean_dec(x_162);
lean_dec_ref(x_1);
return x_179;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_173);
lean_dec(x_170);
lean_dec_ref(x_169);
lean_dec(x_168);
lean_dec_ref(x_167);
lean_dec(x_166);
lean_dec(x_165);
lean_dec_ref(x_164);
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_121);
lean_dec_ref(x_1);
x_180 = lean_ctor_get(x_174, 0);
lean_inc(x_180);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 x_181 = x_174;
} else {
 lean_dec_ref(x_174);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(1, 1, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_180);
return x_182;
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_170);
lean_dec_ref(x_169);
lean_dec(x_168);
lean_dec_ref(x_167);
lean_dec(x_166);
lean_dec(x_165);
lean_dec_ref(x_164);
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_121);
lean_dec_ref(x_1);
x_183 = lean_ctor_get(x_172, 0);
lean_inc(x_183);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 x_184 = x_172;
} else {
 lean_dec_ref(x_172);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 1, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_183);
return x_185;
}
}
}
}
else
{
lean_dec(x_119);
x_64 = x_2;
x_65 = x_3;
x_66 = x_4;
x_67 = x_5;
x_68 = x_6;
x_69 = x_7;
x_70 = x_8;
x_71 = x_9;
x_72 = x_10;
x_73 = lean_box(0);
goto block_109;
}
}
else
{
uint8_t x_198; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_198 = !lean_is_exclusive(x_118);
if (x_198 == 0)
{
return x_118;
}
else
{
lean_object* x_199; lean_object* x_200; 
x_199 = lean_ctor_get(x_118, 0);
lean_inc(x_199);
lean_dec(x_118);
x_200 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_200, 0, x_199);
return x_200;
}
}
}
}
else
{
lean_object* x_201; uint8_t x_202; 
x_201 = lean_ctor_get(x_113, 0);
lean_inc(x_201);
lean_dec(x_113);
x_202 = lean_unbox(x_201);
lean_dec(x_201);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_203 = lean_box(0);
x_204 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_204, 0, x_203);
return x_204;
}
else
{
lean_object* x_205; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_1);
x_205 = l_Lean_Meta_Grind_eqResolution(x_1, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; 
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
lean_dec_ref(x_205);
if (lean_obj_tag(x_206) == 1)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 x_208 = x_206;
} else {
 lean_dec_ref(x_206);
 x_208 = lean_box(0);
}
x_209 = lean_ctor_get(x_207, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_207, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_211 = x_207;
} else {
 lean_dec_ref(x_207);
 x_211 = lean_box(0);
}
x_237 = l_Lean_Meta_Grind_propagateForallPropDown___closed__1;
x_238 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(x_237, x_9);
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
lean_dec_ref(x_238);
x_240 = lean_unbox(x_239);
lean_dec(x_239);
if (x_240 == 0)
{
lean_dec(x_211);
x_212 = x_2;
x_213 = x_3;
x_214 = x_4;
x_215 = x_5;
x_216 = x_6;
x_217 = x_7;
x_218 = x_8;
x_219 = x_9;
x_220 = x_10;
x_221 = lean_box(0);
goto block_236;
}
else
{
lean_object* x_241; 
x_241 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_dec_ref(x_241);
lean_inc_ref(x_1);
x_242 = l_Lean_MessageData_ofExpr(x_1);
x_243 = l_Lean_Meta_Grind_propagateForallPropDown___closed__3;
if (lean_is_scalar(x_211)) {
 x_244 = lean_alloc_ctor(7, 2, 0);
} else {
 x_244 = x_211;
 lean_ctor_set_tag(x_244, 7);
}
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
lean_inc(x_209);
x_245 = l_Lean_MessageData_ofExpr(x_209);
x_246 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
x_247 = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(x_237, x_246, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_247) == 0)
{
lean_dec_ref(x_247);
x_212 = x_2;
x_213 = x_3;
x_214 = x_4;
x_215 = x_5;
x_216 = x_6;
x_217 = x_7;
x_218 = x_8;
x_219 = x_9;
x_220 = x_10;
x_221 = lean_box(0);
goto block_236;
}
else
{
lean_dec(x_210);
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_247;
}
}
else
{
lean_dec(x_211);
lean_dec(x_210);
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_241;
}
}
block_236:
{
lean_object* x_222; 
lean_inc(x_220);
lean_inc_ref(x_219);
lean_inc(x_218);
lean_inc_ref(x_217);
lean_inc(x_216);
lean_inc(x_215);
lean_inc_ref(x_214);
lean_inc(x_213);
lean_inc(x_212);
lean_inc_ref(x_1);
x_222 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_212, x_213, x_214, x_215, x_216, x_217, x_218, x_219, x_220);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
lean_dec_ref(x_222);
x_224 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_212);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
lean_dec_ref(x_224);
lean_inc_ref(x_1);
x_226 = l_Lean_Meta_mkOfEqTrueCore(x_1, x_223);
x_227 = l_Lean_Expr_app___override(x_210, x_226);
lean_inc_ref(x_1);
if (lean_is_scalar(x_208)) {
 x_228 = lean_alloc_ctor(4, 1, 0);
} else {
 x_228 = x_208;
 lean_ctor_set_tag(x_228, 4);
}
lean_ctor_set(x_228, 0, x_1);
lean_inc(x_220);
lean_inc_ref(x_219);
lean_inc(x_218);
lean_inc_ref(x_217);
x_229 = l_Lean_Meta_Grind_addNewRawFact(x_227, x_209, x_225, x_228, x_212, x_213, x_214, x_215, x_216, x_217, x_218, x_219, x_220);
if (lean_obj_tag(x_229) == 0)
{
lean_dec_ref(x_229);
x_64 = x_212;
x_65 = x_213;
x_66 = x_214;
x_67 = x_215;
x_68 = x_216;
x_69 = x_217;
x_70 = x_218;
x_71 = x_219;
x_72 = x_220;
x_73 = lean_box(0);
goto block_109;
}
else
{
lean_dec(x_220);
lean_dec_ref(x_219);
lean_dec(x_218);
lean_dec_ref(x_217);
lean_dec(x_216);
lean_dec(x_215);
lean_dec_ref(x_214);
lean_dec(x_213);
lean_dec(x_212);
lean_dec_ref(x_1);
return x_229;
}
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_dec(x_223);
lean_dec(x_220);
lean_dec_ref(x_219);
lean_dec(x_218);
lean_dec_ref(x_217);
lean_dec(x_216);
lean_dec(x_215);
lean_dec_ref(x_214);
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_210);
lean_dec(x_209);
lean_dec(x_208);
lean_dec_ref(x_1);
x_230 = lean_ctor_get(x_224, 0);
lean_inc(x_230);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 x_231 = x_224;
} else {
 lean_dec_ref(x_224);
 x_231 = lean_box(0);
}
if (lean_is_scalar(x_231)) {
 x_232 = lean_alloc_ctor(1, 1, 0);
} else {
 x_232 = x_231;
}
lean_ctor_set(x_232, 0, x_230);
return x_232;
}
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_dec(x_220);
lean_dec_ref(x_219);
lean_dec(x_218);
lean_dec_ref(x_217);
lean_dec(x_216);
lean_dec(x_215);
lean_dec_ref(x_214);
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_210);
lean_dec(x_209);
lean_dec(x_208);
lean_dec_ref(x_1);
x_233 = lean_ctor_get(x_222, 0);
lean_inc(x_233);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 x_234 = x_222;
} else {
 lean_dec_ref(x_222);
 x_234 = lean_box(0);
}
if (lean_is_scalar(x_234)) {
 x_235 = lean_alloc_ctor(1, 1, 0);
} else {
 x_235 = x_234;
}
lean_ctor_set(x_235, 0, x_233);
return x_235;
}
}
}
else
{
lean_dec(x_206);
x_64 = x_2;
x_65 = x_3;
x_66 = x_4;
x_67 = x_5;
x_68 = x_6;
x_69 = x_7;
x_70 = x_8;
x_71 = x_9;
x_72 = x_10;
x_73 = lean_box(0);
goto block_109;
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_248 = lean_ctor_get(x_205, 0);
lean_inc(x_248);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 x_249 = x_205;
} else {
 lean_dec_ref(x_205);
 x_249 = lean_box(0);
}
if (lean_is_scalar(x_249)) {
 x_250 = lean_alloc_ctor(1, 1, 0);
} else {
 x_250 = x_249;
}
lean_ctor_set(x_250, 0, x_248);
return x_250;
}
}
}
}
else
{
uint8_t x_251; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_251 = !lean_is_exclusive(x_113);
if (x_251 == 0)
{
return x_113;
}
else
{
lean_object* x_252; lean_object* x_253; 
x_252 = lean_ctor_get(x_113, 0);
lean_inc(x_252);
lean_dec(x_113);
x_253 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_253, 0, x_252);
return x_253;
}
}
}
else
{
lean_object* x_254; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_13);
x_254 = l_Lean_Meta_isProp(x_13, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; uint8_t x_285; 
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
lean_dec_ref(x_254);
x_285 = l_Lean_Expr_hasLooseBVars(x_14);
if (x_285 == 0)
{
uint8_t x_286; 
x_286 = lean_unbox(x_255);
lean_dec(x_255);
if (x_286 == 0)
{
goto block_284;
}
else
{
if (x_285 == 0)
{
lean_object* x_287; 
lean_inc_ref(x_14);
lean_inc_ref(x_13);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_4);
lean_inc(x_2);
x_287 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_287) == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
lean_dec_ref(x_287);
x_289 = l_Lean_Meta_Grind_propagateForallPropDown___closed__10;
lean_inc(x_288);
lean_inc_ref(x_14);
lean_inc_ref(x_13);
x_290 = l_Lean_mkApp3(x_289, x_13, x_14, x_288);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_13);
x_291 = l_Lean_Meta_Grind_pushEqTrue___redArg(x_13, x_290, x_2, x_4, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec_ref(x_291);
x_292 = l_Lean_Meta_Grind_propagateForallPropDown___closed__13;
lean_inc_ref(x_14);
x_293 = l_Lean_mkApp3(x_292, x_13, x_14, x_288);
x_294 = l_Lean_Meta_Grind_pushEqFalse___redArg(x_14, x_293, x_2, x_4, x_7, x_8, x_9, x_10);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_294;
}
else
{
lean_dec(x_288);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_291;
}
}
else
{
uint8_t x_295; 
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_4);
lean_dec(x_2);
x_295 = !lean_is_exclusive(x_287);
if (x_295 == 0)
{
return x_287;
}
else
{
lean_object* x_296; lean_object* x_297; 
x_296 = lean_ctor_get(x_287, 0);
lean_inc(x_296);
lean_dec(x_287);
x_297 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_297, 0, x_296);
return x_297;
}
}
}
else
{
goto block_284;
}
}
}
else
{
lean_dec(x_255);
goto block_284;
}
block_284:
{
lean_object* x_256; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_13);
x_256 = l_Lean_Meta_getLevel(x_13, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; lean_object* x_258; 
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
lean_dec_ref(x_256);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_258 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
lean_dec_ref(x_258);
lean_inc_ref(x_14);
x_260 = l_Lean_mkNot(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
x_261 = l_Lean_mkLambda(x_12, x_15, x_13, x_260);
x_262 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
lean_dec_ref(x_262);
x_264 = l_Lean_Meta_Grind_propagateForallPropDown___closed__5;
x_265 = lean_box(0);
x_266 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_266, 0, x_257);
lean_ctor_set(x_266, 1, x_265);
lean_inc_ref(x_266);
x_267 = l_Lean_mkConst(x_264, x_266);
lean_inc_ref(x_13);
x_268 = l_Lean_mkAppB(x_267, x_13, x_261);
lean_inc_ref(x_14);
lean_inc_ref(x_13);
lean_inc(x_12);
x_269 = l_Lean_mkLambda(x_12, x_15, x_13, x_14);
x_270 = l_Lean_Meta_Grind_propagateForallPropDown___closed__7;
x_271 = l_Lean_mkConst(x_270, x_266);
lean_inc_ref(x_13);
x_272 = l_Lean_mkApp3(x_271, x_13, x_269, x_259);
x_273 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_273, 0, x_1);
x_274 = l_Lean_Meta_Grind_addNewRawFact(x_272, x_268, x_263, x_273, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_274;
}
else
{
uint8_t x_275; 
lean_dec_ref(x_261);
lean_dec(x_259);
lean_dec(x_257);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_275 = !lean_is_exclusive(x_262);
if (x_275 == 0)
{
return x_262;
}
else
{
lean_object* x_276; lean_object* x_277; 
x_276 = lean_ctor_get(x_262, 0);
lean_inc(x_276);
lean_dec(x_262);
x_277 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_277, 0, x_276);
return x_277;
}
}
}
else
{
uint8_t x_278; 
lean_dec(x_257);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_278 = !lean_is_exclusive(x_258);
if (x_278 == 0)
{
return x_258;
}
else
{
lean_object* x_279; lean_object* x_280; 
x_279 = lean_ctor_get(x_258, 0);
lean_inc(x_279);
lean_dec(x_258);
x_280 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_280, 0, x_279);
return x_280;
}
}
}
else
{
uint8_t x_281; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_281 = !lean_is_exclusive(x_256);
if (x_281 == 0)
{
return x_256;
}
else
{
lean_object* x_282; lean_object* x_283; 
x_282 = lean_ctor_get(x_256, 0);
lean_inc(x_282);
lean_dec(x_256);
x_283 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_283, 0, x_282);
return x_283;
}
}
}
}
else
{
uint8_t x_298; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_298 = !lean_is_exclusive(x_254);
if (x_298 == 0)
{
return x_254;
}
else
{
lean_object* x_299; lean_object* x_300; 
x_299 = lean_ctor_get(x_254, 0);
lean_inc(x_299);
lean_dec(x_254);
x_300 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_300, 0, x_299);
return x_300;
}
}
}
}
else
{
uint8_t x_301; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_301 = !lean_is_exclusive(x_110);
if (x_301 == 0)
{
return x_110;
}
else
{
lean_object* x_302; lean_object* x_303; 
x_302 = lean_ctor_get(x_110, 0);
lean_inc(x_302);
lean_dec(x_110);
x_303 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_303, 0, x_302);
return x_303;
}
}
block_63:
{
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_unbox(x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_1);
x_29 = lean_box(0);
lean_ctor_set(x_25, 0, x_29);
return x_25;
}
else
{
lean_object* x_30; 
lean_free_object(x_25);
lean_inc(x_24);
lean_inc_ref(x_22);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_23);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_20);
lean_inc(x_21);
x_30 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_21, x_20, x_18, x_19, x_23, x_16, x_17, x_22, x_24);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
lean_inc(x_24);
lean_inc_ref(x_22);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc_ref(x_18);
lean_inc(x_21);
lean_inc_ref(x_14);
x_32 = l_Lean_Meta_Grind_mkEqFalseProof(x_14, x_21, x_20, x_18, x_19, x_23, x_16, x_17, x_22, x_24);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4;
lean_inc_ref(x_13);
x_35 = l_Lean_mkApp4(x_34, x_13, x_14, x_31, x_33);
x_36 = l_Lean_Meta_Grind_pushEqFalse___redArg(x_13, x_35, x_21, x_18, x_16, x_17, x_22, x_24);
lean_dec_ref(x_18);
lean_dec(x_21);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_31);
lean_dec(x_24);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
x_37 = !lean_is_exclusive(x_32);
if (x_37 == 0)
{
return x_32;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_32, 0);
lean_inc(x_38);
lean_dec(x_32);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
x_40 = !lean_is_exclusive(x_30);
if (x_40 == 0)
{
return x_30;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_30, 0);
lean_inc(x_41);
lean_dec(x_30);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
}
else
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_25, 0);
lean_inc(x_43);
lean_dec(x_25);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_1);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_45);
return x_46;
}
else
{
lean_object* x_47; 
lean_inc(x_24);
lean_inc_ref(x_22);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc(x_23);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_20);
lean_inc(x_21);
x_47 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_21, x_20, x_18, x_19, x_23, x_16, x_17, x_22, x_24);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
lean_inc(x_24);
lean_inc_ref(x_22);
lean_inc(x_17);
lean_inc_ref(x_16);
lean_inc_ref(x_18);
lean_inc(x_21);
lean_inc_ref(x_14);
x_49 = l_Lean_Meta_Grind_mkEqFalseProof(x_14, x_21, x_20, x_18, x_19, x_23, x_16, x_17, x_22, x_24);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
x_51 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4;
lean_inc_ref(x_13);
x_52 = l_Lean_mkApp4(x_51, x_13, x_14, x_48, x_50);
x_53 = l_Lean_Meta_Grind_pushEqFalse___redArg(x_13, x_52, x_21, x_18, x_16, x_17, x_22, x_24);
lean_dec_ref(x_18);
lean_dec(x_21);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_48);
lean_dec(x_24);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
x_54 = lean_ctor_get(x_49, 0);
lean_inc(x_54);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 x_55 = x_49;
} else {
 lean_dec_ref(x_49);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 1, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_54);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
x_57 = lean_ctor_get(x_47, 0);
lean_inc(x_57);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 x_58 = x_47;
} else {
 lean_dec_ref(x_47);
 x_58 = lean_box(0);
}
if (lean_is_scalar(x_58)) {
 x_59 = lean_alloc_ctor(1, 1, 0);
} else {
 x_59 = x_58;
}
lean_ctor_set(x_59, 0, x_57);
return x_59;
}
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_1);
x_60 = !lean_is_exclusive(x_25);
if (x_60 == 0)
{
return x_25;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_25, 0);
lean_inc(x_61);
lean_dec(x_25);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
block_109:
{
uint8_t x_74; 
x_74 = l_Lean_Expr_hasLooseBVars(x_14);
if (x_74 == 0)
{
lean_object* x_75; 
lean_inc_ref(x_14);
lean_inc_ref(x_13);
x_75 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_14, x_64);
if (lean_obj_tag(x_75) == 0)
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; uint8_t x_78; 
x_77 = lean_ctor_get(x_75, 0);
x_78 = lean_unbox(x_77);
lean_dec(x_77);
if (x_78 == 0)
{
lean_object* x_79; 
lean_dec(x_72);
lean_dec_ref(x_71);
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec_ref(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_1);
x_79 = lean_box(0);
lean_ctor_set(x_75, 0, x_79);
return x_75;
}
else
{
lean_object* x_80; 
lean_free_object(x_75);
lean_inc_ref(x_14);
x_80 = l_Lean_Meta_Grind_isEqFalse___redArg(x_14, x_64, x_66, x_69, x_70, x_71, x_72);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_unbox(x_81);
lean_dec(x_81);
if (x_82 == 0)
{
x_16 = x_69;
x_17 = x_70;
x_18 = x_66;
x_19 = x_67;
x_20 = x_65;
x_21 = x_64;
x_22 = x_71;
x_23 = x_68;
x_24 = x_72;
x_25 = x_80;
goto block_63;
}
else
{
lean_object* x_83; 
lean_dec_ref(x_80);
lean_inc(x_72);
lean_inc_ref(x_71);
lean_inc(x_70);
lean_inc_ref(x_69);
lean_inc_ref(x_13);
x_83 = l_Lean_Meta_isProp(x_13, x_69, x_70, x_71, x_72);
x_16 = x_69;
x_17 = x_70;
x_18 = x_66;
x_19 = x_67;
x_20 = x_65;
x_21 = x_64;
x_22 = x_71;
x_23 = x_68;
x_24 = x_72;
x_25 = x_83;
goto block_63;
}
}
else
{
x_16 = x_69;
x_17 = x_70;
x_18 = x_66;
x_19 = x_67;
x_20 = x_65;
x_21 = x_64;
x_22 = x_71;
x_23 = x_68;
x_24 = x_72;
x_25 = x_80;
goto block_63;
}
}
}
else
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_ctor_get(x_75, 0);
lean_inc(x_84);
lean_dec(x_75);
x_85 = lean_unbox(x_84);
lean_dec(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_72);
lean_dec_ref(x_71);
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec_ref(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_1);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_87, 0, x_86);
return x_87;
}
else
{
lean_object* x_88; 
lean_inc_ref(x_14);
x_88 = l_Lean_Meta_Grind_isEqFalse___redArg(x_14, x_64, x_66, x_69, x_70, x_71, x_72);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; uint8_t x_90; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_unbox(x_89);
lean_dec(x_89);
if (x_90 == 0)
{
x_16 = x_69;
x_17 = x_70;
x_18 = x_66;
x_19 = x_67;
x_20 = x_65;
x_21 = x_64;
x_22 = x_71;
x_23 = x_68;
x_24 = x_72;
x_25 = x_88;
goto block_63;
}
else
{
lean_object* x_91; 
lean_dec_ref(x_88);
lean_inc(x_72);
lean_inc_ref(x_71);
lean_inc(x_70);
lean_inc_ref(x_69);
lean_inc_ref(x_13);
x_91 = l_Lean_Meta_isProp(x_13, x_69, x_70, x_71, x_72);
x_16 = x_69;
x_17 = x_70;
x_18 = x_66;
x_19 = x_67;
x_20 = x_65;
x_21 = x_64;
x_22 = x_71;
x_23 = x_68;
x_24 = x_72;
x_25 = x_91;
goto block_63;
}
}
else
{
x_16 = x_69;
x_17 = x_70;
x_18 = x_66;
x_19 = x_67;
x_20 = x_65;
x_21 = x_64;
x_22 = x_71;
x_23 = x_68;
x_24 = x_72;
x_25 = x_88;
goto block_63;
}
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_72);
lean_dec_ref(x_71);
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec_ref(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_1);
x_92 = !lean_is_exclusive(x_75);
if (x_92 == 0)
{
return x_75;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_75, 0);
lean_inc(x_93);
lean_dec(x_75);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
return x_94;
}
}
}
else
{
lean_object* x_95; 
lean_inc(x_72);
lean_inc_ref(x_71);
lean_inc(x_70);
lean_inc_ref(x_69);
lean_inc_ref(x_13);
x_95 = l_Lean_Meta_isProp(x_13, x_69, x_70, x_71, x_72);
if (lean_obj_tag(x_95) == 0)
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_ctor_get(x_95, 0);
x_98 = lean_unbox(x_97);
lean_dec(x_97);
if (x_98 == 0)
{
lean_object* x_99; 
lean_free_object(x_95);
x_99 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems(x_1, x_64, x_65, x_66, x_67, x_68, x_69, x_70, x_71, x_72);
return x_99;
}
else
{
lean_object* x_100; 
lean_dec(x_72);
lean_dec_ref(x_71);
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec_ref(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec_ref(x_1);
x_100 = lean_box(0);
lean_ctor_set(x_95, 0, x_100);
return x_95;
}
}
else
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_ctor_get(x_95, 0);
lean_inc(x_101);
lean_dec(x_95);
x_102 = lean_unbox(x_101);
lean_dec(x_101);
if (x_102 == 0)
{
lean_object* x_103; 
x_103 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems(x_1, x_64, x_65, x_66, x_67, x_68, x_69, x_70, x_71, x_72);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; 
lean_dec(x_72);
lean_dec_ref(x_71);
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec_ref(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec_ref(x_1);
x_104 = lean_box(0);
x_105 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_105, 0, x_104);
return x_105;
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_72);
lean_dec_ref(x_71);
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec_ref(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec_ref(x_1);
x_106 = !lean_is_exclusive(x_95);
if (x_106 == 0)
{
return x_95;
}
else
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_95, 0);
lean_inc(x_107);
lean_dec(x_95);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
return x_108;
}
}
}
}
}
else
{
lean_object* x_304; lean_object* x_305; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_304 = lean_box(0);
x_305 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_305, 0, x_304);
return x_305;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropDown___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_propagateForallPropDown(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
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
lean_object* x_12; lean_object* x_16; 
lean_inc_ref(x_1);
x_16 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_4, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_20 = lean_box(0);
lean_ctor_set(x_16, 0, x_20);
return x_16;
}
else
{
lean_object* x_21; uint8_t x_22; 
lean_free_object(x_16);
lean_inc_ref(x_1);
x_21 = l_Lean_Expr_cleanupAnnotations(x_1);
x_22 = l_Lean_Expr_isApp(x_21);
if (x_22 == 0)
{
lean_dec_ref(x_21);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_12 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_23);
x_24 = l_Lean_Expr_appFnCleanup___redArg(x_21);
x_25 = l_Lean_Expr_isApp(x_24);
if (x_25 == 0)
{
lean_dec_ref(x_24);
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_12 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_24, 1);
lean_inc_ref(x_26);
x_27 = l_Lean_Expr_appFnCleanup___redArg(x_24);
x_28 = l_Lean_Meta_Grind_propagateForallPropDown___closed__5;
x_29 = l_Lean_Expr_isConstOf(x_27, x_28);
if (x_29 == 0)
{
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_12 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_30; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_30 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = l_Lean_Meta_Grind_propagateExistsDown___closed__2;
x_35 = l_Lean_Meta_Grind_propagateExistsDown___closed__3;
lean_inc_ref(x_23);
x_36 = l_Lean_Expr_app___override(x_23, x_35);
x_37 = l_Lean_Expr_headBeta(x_36);
x_38 = l_Lean_Expr_app___override(x_34, x_37);
x_39 = l_Lean_Meta_Grind_propagateExistsDown___closed__5;
x_40 = 0;
lean_inc_ref(x_26);
x_41 = l_Lean_mkForall(x_39, x_40, x_26, x_38);
x_42 = l_Lean_Expr_constLevels_x21(x_27);
lean_dec_ref(x_27);
x_43 = l_Lean_Meta_Grind_propagateExistsDown___closed__7;
x_44 = l_Lean_mkConst(x_43, x_42);
lean_inc_ref(x_1);
x_45 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_31);
x_46 = l_Lean_mkApp3(x_44, x_26, x_23, x_45);
x_47 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_47, 0, x_1);
x_48 = l_Lean_Meta_Grind_addNewRawFact(x_46, x_41, x_33, x_47, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_48;
}
else
{
uint8_t x_49; 
lean_dec(x_31);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_49 = !lean_is_exclusive(x_32);
if (x_49 == 0)
{
return x_32;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_32, 0);
lean_inc(x_50);
lean_dec(x_32);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec_ref(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_23);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_52 = !lean_is_exclusive(x_30);
if (x_52 == 0)
{
return x_30;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_30, 0);
lean_inc(x_53);
lean_dec(x_30);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
}
}
}
}
}
else
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_16, 0);
lean_inc(x_55);
lean_dec(x_16);
x_56 = lean_unbox(x_55);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
else
{
lean_object* x_59; uint8_t x_60; 
lean_inc_ref(x_1);
x_59 = l_Lean_Expr_cleanupAnnotations(x_1);
x_60 = l_Lean_Expr_isApp(x_59);
if (x_60 == 0)
{
lean_dec_ref(x_59);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_12 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_61 = lean_ctor_get(x_59, 1);
lean_inc_ref(x_61);
x_62 = l_Lean_Expr_appFnCleanup___redArg(x_59);
x_63 = l_Lean_Expr_isApp(x_62);
if (x_63 == 0)
{
lean_dec_ref(x_62);
lean_dec_ref(x_61);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_12 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_64 = lean_ctor_get(x_62, 1);
lean_inc_ref(x_64);
x_65 = l_Lean_Expr_appFnCleanup___redArg(x_62);
x_66 = l_Lean_Meta_Grind_propagateForallPropDown___closed__5;
x_67 = l_Lean_Expr_isConstOf(x_65, x_66);
if (x_67 == 0)
{
lean_dec_ref(x_65);
lean_dec_ref(x_64);
lean_dec_ref(x_61);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_12 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_68; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_68 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec_ref(x_68);
x_70 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec_ref(x_70);
x_72 = l_Lean_Meta_Grind_propagateExistsDown___closed__2;
x_73 = l_Lean_Meta_Grind_propagateExistsDown___closed__3;
lean_inc_ref(x_61);
x_74 = l_Lean_Expr_app___override(x_61, x_73);
x_75 = l_Lean_Expr_headBeta(x_74);
x_76 = l_Lean_Expr_app___override(x_72, x_75);
x_77 = l_Lean_Meta_Grind_propagateExistsDown___closed__5;
x_78 = 0;
lean_inc_ref(x_64);
x_79 = l_Lean_mkForall(x_77, x_78, x_64, x_76);
x_80 = l_Lean_Expr_constLevels_x21(x_65);
lean_dec_ref(x_65);
x_81 = l_Lean_Meta_Grind_propagateExistsDown___closed__7;
x_82 = l_Lean_mkConst(x_81, x_80);
lean_inc_ref(x_1);
x_83 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_69);
x_84 = l_Lean_mkApp3(x_82, x_64, x_61, x_83);
x_85 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_85, 0, x_1);
x_86 = l_Lean_Meta_Grind_addNewRawFact(x_84, x_79, x_71, x_85, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_69);
lean_dec_ref(x_65);
lean_dec_ref(x_64);
lean_dec_ref(x_61);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_87 = lean_ctor_get(x_70, 0);
lean_inc(x_87);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 x_88 = x_70;
} else {
 lean_dec_ref(x_70);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 1, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_87);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec_ref(x_65);
lean_dec_ref(x_64);
lean_dec_ref(x_61);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_90 = lean_ctor_get(x_68, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 x_91 = x_68;
} else {
 lean_dec_ref(x_68);
 x_91 = lean_box(0);
}
if (lean_is_scalar(x_91)) {
 x_92 = lean_alloc_ctor(1, 1, 0);
} else {
 x_92 = x_91;
}
lean_ctor_set(x_92, 0, x_90);
return x_92;
}
}
}
}
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_93 = !lean_is_exclusive(x_16);
if (x_93 == 0)
{
return x_16;
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_ctor_get(x_16, 0);
lean_inc(x_94);
lean_dec(x_16);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_94);
return x_95;
}
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateExistsDown___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_propagateExistsDown(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateExistsDown___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_115310127____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_Grind_propagateForallPropDown___closed__5;
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateExistsDown___boxed), 11, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateExistsDown___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_115310127____hygCtx___hyg_8____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_propagateExistsDown___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_115310127____hygCtx___hyg_8_();
return x_2;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_expr_instantiate1(x_1, x_2);
x_12 = l_Lean_Meta_getLevel(x_11, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_simpForall___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_5, x_2, x_3, x_4, x_6, x_7, x_8, x_9, lean_box(0));
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___lam__0___boxed), 10, 4);
lean_closure_set(x_14, 0, x_4);
lean_closure_set(x_14, 1, x_6);
lean_closure_set(x_14, 2, x_7);
lean_closure_set(x_14, 3, x_8);
x_15 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), x_1, x_2, x_3, x_14, x_5, x_9, x_10, x_11, x_12);
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
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_2);
x_15 = lean_unbox(x_5);
x_16 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg(x_1, x_14, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = 0;
x_13 = 0;
x_14 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg(x_1, x_12, x_2, x_3, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
x_1 = lean_mk_string_unchecked("forall_forall_or", 16, 16);
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
x_1 = lean_mk_string_unchecked("forall_or_forall", 16, 16);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; uint8_t x_410; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_16);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec_ref(x_1);
x_410 = l_Lean_Expr_hasLooseBVars(x_16);
if (x_410 == 0)
{
lean_object* x_411; 
lean_inc_ref(x_15);
x_411 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_15, x_6);
if (lean_obj_tag(x_411) == 0)
{
lean_object* x_412; uint8_t x_413; lean_object* x_414; lean_object* x_437; lean_object* x_438; uint8_t x_439; 
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
lean_dec_ref(x_411);
x_413 = 1;
x_437 = l_Lean_Expr_cleanupAnnotations(x_412);
x_438 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__3;
x_439 = l_Lean_Expr_isConstOf(x_437, x_438);
if (x_439 == 0)
{
lean_object* x_440; uint8_t x_441; 
x_440 = l_Lean_Meta_Grind_simpForall___closed__12;
x_441 = l_Lean_Expr_isConstOf(x_437, x_440);
lean_dec_ref(x_437);
if (x_441 == 0)
{
if (lean_obj_tag(x_15) == 7)
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; uint8_t x_445; uint8_t x_446; lean_object* x_447; uint8_t x_486; 
x_442 = lean_ctor_get(x_15, 0);
x_443 = lean_ctor_get(x_15, 1);
x_444 = lean_ctor_get(x_15, 2);
x_445 = lean_ctor_get_uint8(x_15, sizeof(void*)*3 + 8);
x_486 = l_Lean_Expr_hasLooseBVars(x_444);
if (x_486 == 0)
{
x_446 = x_486;
x_447 = lean_box(0);
goto block_485;
}
else
{
lean_object* x_487; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_15);
x_487 = l_Lean_Meta_isProp(x_15, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_487) == 0)
{
lean_object* x_488; uint8_t x_489; 
x_488 = lean_ctor_get(x_487, 0);
lean_inc(x_488);
lean_dec_ref(x_487);
x_489 = lean_unbox(x_488);
lean_dec(x_488);
x_446 = x_489;
x_447 = lean_box(0);
goto block_485;
}
else
{
uint8_t x_490; 
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
x_490 = !lean_is_exclusive(x_487);
if (x_490 == 0)
{
return x_487;
}
else
{
lean_object* x_491; lean_object* x_492; 
x_491 = lean_ctor_get(x_487, 0);
lean_inc(x_491);
lean_dec(x_487);
x_492 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_492, 0, x_491);
return x_492;
}
}
}
block_485:
{
if (x_446 == 0)
{
x_397 = x_2;
x_398 = x_3;
x_399 = x_4;
x_400 = x_5;
x_401 = x_6;
x_402 = x_7;
x_403 = x_8;
x_404 = lean_box(0);
goto block_409;
}
else
{
lean_object* x_448; lean_object* x_449; 
lean_inc_ref(x_444);
lean_inc_ref(x_443);
lean_inc(x_442);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_inc_ref(x_444);
lean_inc_ref(x_443);
lean_inc(x_442);
x_448 = l_Lean_mkLambda(x_442, x_445, x_443, x_444);
lean_inc_ref(x_443);
x_449 = l_Lean_Meta_getLevel(x_443, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_449) == 0)
{
uint8_t x_450; 
x_450 = !lean_is_exclusive(x_449);
if (x_450 == 0)
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
x_451 = lean_ctor_get(x_449, 0);
x_452 = l_Lean_Meta_Grind_propagateForallPropDown___closed__5;
x_453 = lean_box(0);
x_454 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_454, 0, x_451);
lean_ctor_set(x_454, 1, x_453);
lean_inc_ref(x_454);
x_455 = l_Lean_mkConst(x_452, x_454);
x_456 = l_Lean_mkNot(x_444);
lean_inc_ref(x_443);
x_457 = l_Lean_mkLambda(x_442, x_445, x_443, x_456);
lean_inc_ref(x_443);
x_458 = l_Lean_mkAppB(x_455, x_443, x_457);
lean_inc_ref(x_16);
x_459 = l_Lean_mkOr(x_458, x_16);
x_460 = l_Lean_Meta_Grind_simpForall___closed__18;
x_461 = l_Lean_mkConst(x_460, x_454);
x_462 = l_Lean_mkApp3(x_461, x_443, x_448, x_16);
x_463 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_463, 0, x_462);
x_464 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_464, 0, x_459);
lean_ctor_set(x_464, 1, x_463);
lean_ctor_set_uint8(x_464, sizeof(void*)*2, x_413);
x_465 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_465, 0, x_464);
lean_ctor_set(x_449, 0, x_465);
return x_449;
}
else
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_466 = lean_ctor_get(x_449, 0);
lean_inc(x_466);
lean_dec(x_449);
x_467 = l_Lean_Meta_Grind_propagateForallPropDown___closed__5;
x_468 = lean_box(0);
x_469 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_469, 0, x_466);
lean_ctor_set(x_469, 1, x_468);
lean_inc_ref(x_469);
x_470 = l_Lean_mkConst(x_467, x_469);
x_471 = l_Lean_mkNot(x_444);
lean_inc_ref(x_443);
x_472 = l_Lean_mkLambda(x_442, x_445, x_443, x_471);
lean_inc_ref(x_443);
x_473 = l_Lean_mkAppB(x_470, x_443, x_472);
lean_inc_ref(x_16);
x_474 = l_Lean_mkOr(x_473, x_16);
x_475 = l_Lean_Meta_Grind_simpForall___closed__18;
x_476 = l_Lean_mkConst(x_475, x_469);
x_477 = l_Lean_mkApp3(x_476, x_443, x_448, x_16);
x_478 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_478, 0, x_477);
x_479 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_479, 0, x_474);
lean_ctor_set(x_479, 1, x_478);
lean_ctor_set_uint8(x_479, sizeof(void*)*2, x_413);
x_480 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_480, 0, x_479);
x_481 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_481, 0, x_480);
return x_481;
}
}
else
{
uint8_t x_482; 
lean_dec_ref(x_448);
lean_dec_ref(x_444);
lean_dec_ref(x_443);
lean_dec(x_442);
lean_dec_ref(x_16);
x_482 = !lean_is_exclusive(x_449);
if (x_482 == 0)
{
return x_449;
}
else
{
lean_object* x_483; lean_object* x_484; 
x_483 = lean_ctor_get(x_449, 0);
lean_inc(x_483);
lean_dec(x_449);
x_484 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_484, 0, x_483);
return x_484;
}
}
}
}
}
else
{
lean_object* x_493; 
lean_inc_ref(x_16);
x_493 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_16, x_6);
if (lean_obj_tag(x_493) == 0)
{
lean_object* x_494; lean_object* x_495; uint8_t x_496; 
x_494 = lean_ctor_get(x_493, 0);
lean_inc(x_494);
lean_dec_ref(x_493);
x_495 = l_Lean_Expr_cleanupAnnotations(x_494);
x_496 = l_Lean_Expr_isConstOf(x_495, x_438);
if (x_496 == 0)
{
uint8_t x_497; 
x_497 = l_Lean_Expr_isConstOf(x_495, x_440);
lean_dec_ref(x_495);
if (x_497 == 0)
{
lean_object* x_498; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_15);
x_498 = l_Lean_Meta_isProp(x_15, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_498) == 0)
{
lean_object* x_499; uint8_t x_500; 
x_499 = lean_ctor_get(x_498, 0);
lean_inc(x_499);
x_500 = lean_unbox(x_499);
lean_dec(x_499);
if (x_500 == 0)
{
x_414 = x_498;
goto block_436;
}
else
{
lean_object* x_501; 
lean_dec_ref(x_498);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_16);
lean_inc_ref(x_15);
x_501 = l_Lean_Meta_isExprDefEq(x_15, x_16, x_5, x_6, x_7, x_8);
x_414 = x_501;
goto block_436;
}
}
else
{
x_414 = x_498;
goto block_436;
}
}
else
{
lean_object* x_502; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_15);
x_502 = l_Lean_Meta_isProp(x_15, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_502) == 0)
{
uint8_t x_503; 
x_503 = !lean_is_exclusive(x_502);
if (x_503 == 0)
{
lean_object* x_504; uint8_t x_505; 
x_504 = lean_ctor_get(x_502, 0);
x_505 = lean_unbox(x_504);
lean_dec(x_504);
if (x_505 == 0)
{
lean_free_object(x_502);
x_397 = x_2;
x_398 = x_3;
x_399 = x_4;
x_400 = x_5;
x_401 = x_6;
x_402 = x_7;
x_403 = x_8;
x_404 = lean_box(0);
goto block_409;
}
else
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; 
lean_dec_ref(x_16);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_506 = l_Lean_Meta_Grind_simpForall___closed__13;
x_507 = l_Lean_Meta_Grind_simpForall___closed__21;
x_508 = l_Lean_Expr_app___override(x_507, x_15);
x_509 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_509, 0, x_508);
x_510 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_510, 0, x_506);
lean_ctor_set(x_510, 1, x_509);
lean_ctor_set_uint8(x_510, sizeof(void*)*2, x_413);
x_511 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_511, 0, x_510);
lean_ctor_set(x_502, 0, x_511);
return x_502;
}
}
else
{
lean_object* x_512; uint8_t x_513; 
x_512 = lean_ctor_get(x_502, 0);
lean_inc(x_512);
lean_dec(x_502);
x_513 = lean_unbox(x_512);
lean_dec(x_512);
if (x_513 == 0)
{
x_397 = x_2;
x_398 = x_3;
x_399 = x_4;
x_400 = x_5;
x_401 = x_6;
x_402 = x_7;
x_403 = x_8;
x_404 = lean_box(0);
goto block_409;
}
else
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; 
lean_dec_ref(x_16);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_514 = l_Lean_Meta_Grind_simpForall___closed__13;
x_515 = l_Lean_Meta_Grind_simpForall___closed__21;
x_516 = l_Lean_Expr_app___override(x_515, x_15);
x_517 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_517, 0, x_516);
x_518 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_518, 0, x_514);
lean_ctor_set(x_518, 1, x_517);
lean_ctor_set_uint8(x_518, sizeof(void*)*2, x_413);
x_519 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_519, 0, x_518);
x_520 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_520, 0, x_519);
return x_520;
}
}
}
else
{
uint8_t x_521; 
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
x_521 = !lean_is_exclusive(x_502);
if (x_521 == 0)
{
return x_502;
}
else
{
lean_object* x_522; lean_object* x_523; 
x_522 = lean_ctor_get(x_502, 0);
lean_inc(x_522);
lean_dec(x_502);
x_523 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_523, 0, x_522);
return x_523;
}
}
}
}
else
{
lean_object* x_524; 
lean_dec_ref(x_495);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_15);
x_524 = l_Lean_Meta_isProp(x_15, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_524) == 0)
{
uint8_t x_525; 
x_525 = !lean_is_exclusive(x_524);
if (x_525 == 0)
{
lean_object* x_526; uint8_t x_527; 
x_526 = lean_ctor_get(x_524, 0);
x_527 = lean_unbox(x_526);
lean_dec(x_526);
if (x_527 == 0)
{
lean_free_object(x_524);
x_397 = x_2;
x_398 = x_3;
x_399 = x_4;
x_400 = x_5;
x_401 = x_6;
x_402 = x_7;
x_403 = x_8;
x_404 = lean_box(0);
goto block_409;
}
else
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; 
lean_dec_ref(x_16);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_inc_ref(x_15);
x_528 = l_Lean_mkNot(x_15);
x_529 = l_Lean_Meta_Grind_simpForall___closed__24;
x_530 = l_Lean_Expr_app___override(x_529, x_15);
x_531 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_531, 0, x_530);
x_532 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_532, 0, x_528);
lean_ctor_set(x_532, 1, x_531);
lean_ctor_set_uint8(x_532, sizeof(void*)*2, x_413);
x_533 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_533, 0, x_532);
lean_ctor_set(x_524, 0, x_533);
return x_524;
}
}
else
{
lean_object* x_534; uint8_t x_535; 
x_534 = lean_ctor_get(x_524, 0);
lean_inc(x_534);
lean_dec(x_524);
x_535 = lean_unbox(x_534);
lean_dec(x_534);
if (x_535 == 0)
{
x_397 = x_2;
x_398 = x_3;
x_399 = x_4;
x_400 = x_5;
x_401 = x_6;
x_402 = x_7;
x_403 = x_8;
x_404 = lean_box(0);
goto block_409;
}
else
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; 
lean_dec_ref(x_16);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_inc_ref(x_15);
x_536 = l_Lean_mkNot(x_15);
x_537 = l_Lean_Meta_Grind_simpForall___closed__24;
x_538 = l_Lean_Expr_app___override(x_537, x_15);
x_539 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_539, 0, x_538);
x_540 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_540, 0, x_536);
lean_ctor_set(x_540, 1, x_539);
lean_ctor_set_uint8(x_540, sizeof(void*)*2, x_413);
x_541 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_541, 0, x_540);
x_542 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_542, 0, x_541);
return x_542;
}
}
}
else
{
uint8_t x_543; 
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
x_543 = !lean_is_exclusive(x_524);
if (x_543 == 0)
{
return x_524;
}
else
{
lean_object* x_544; lean_object* x_545; 
x_544 = lean_ctor_get(x_524, 0);
lean_inc(x_544);
lean_dec(x_524);
x_545 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_545, 0, x_544);
return x_545;
}
}
}
}
else
{
uint8_t x_546; 
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
x_546 = !lean_is_exclusive(x_493);
if (x_546 == 0)
{
return x_493;
}
else
{
lean_object* x_547; lean_object* x_548; 
x_547 = lean_ctor_get(x_493, 0);
lean_inc(x_547);
lean_dec(x_493);
x_548 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_548, 0, x_547);
return x_548;
}
}
}
}
else
{
lean_object* x_549; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_16);
x_549 = l_Lean_Meta_isProp(x_16, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_549) == 0)
{
uint8_t x_550; 
x_550 = !lean_is_exclusive(x_549);
if (x_550 == 0)
{
lean_object* x_551; uint8_t x_552; 
x_551 = lean_ctor_get(x_549, 0);
x_552 = lean_unbox(x_551);
lean_dec(x_551);
if (x_552 == 0)
{
lean_free_object(x_549);
x_397 = x_2;
x_398 = x_3;
x_399 = x_4;
x_400 = x_5;
x_401 = x_6;
x_402 = x_7;
x_403 = x_8;
x_404 = lean_box(0);
goto block_409;
}
else
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; 
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_553 = l_Lean_Meta_Grind_simpForall___closed__27;
lean_inc_ref(x_16);
x_554 = l_Lean_Expr_app___override(x_553, x_16);
x_555 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_555, 0, x_554);
x_556 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_556, 0, x_16);
lean_ctor_set(x_556, 1, x_555);
lean_ctor_set_uint8(x_556, sizeof(void*)*2, x_413);
x_557 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_557, 0, x_556);
lean_ctor_set(x_549, 0, x_557);
return x_549;
}
}
else
{
lean_object* x_558; uint8_t x_559; 
x_558 = lean_ctor_get(x_549, 0);
lean_inc(x_558);
lean_dec(x_549);
x_559 = lean_unbox(x_558);
lean_dec(x_558);
if (x_559 == 0)
{
x_397 = x_2;
x_398 = x_3;
x_399 = x_4;
x_400 = x_5;
x_401 = x_6;
x_402 = x_7;
x_403 = x_8;
x_404 = lean_box(0);
goto block_409;
}
else
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; 
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_560 = l_Lean_Meta_Grind_simpForall___closed__27;
lean_inc_ref(x_16);
x_561 = l_Lean_Expr_app___override(x_560, x_16);
x_562 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_562, 0, x_561);
x_563 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_563, 0, x_16);
lean_ctor_set(x_563, 1, x_562);
lean_ctor_set_uint8(x_563, sizeof(void*)*2, x_413);
x_564 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_564, 0, x_563);
x_565 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_565, 0, x_564);
return x_565;
}
}
}
else
{
uint8_t x_566; 
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
x_566 = !lean_is_exclusive(x_549);
if (x_566 == 0)
{
return x_549;
}
else
{
lean_object* x_567; lean_object* x_568; 
x_567 = lean_ctor_get(x_549, 0);
lean_inc(x_567);
lean_dec(x_549);
x_568 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_568, 0, x_567);
return x_568;
}
}
}
}
else
{
lean_object* x_569; 
lean_dec_ref(x_437);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_16);
x_569 = l_Lean_Meta_isProp(x_16, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_569) == 0)
{
uint8_t x_570; 
x_570 = !lean_is_exclusive(x_569);
if (x_570 == 0)
{
lean_object* x_571; uint8_t x_572; 
x_571 = lean_ctor_get(x_569, 0);
x_572 = lean_unbox(x_571);
lean_dec(x_571);
if (x_572 == 0)
{
lean_free_object(x_569);
x_397 = x_2;
x_398 = x_3;
x_399 = x_4;
x_400 = x_5;
x_401 = x_6;
x_402 = x_7;
x_403 = x_8;
x_404 = lean_box(0);
goto block_409;
}
else
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; 
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_573 = l_Lean_Meta_Grind_simpForall___closed__13;
x_574 = l_Lean_Meta_Grind_simpForall___closed__30;
x_575 = l_Lean_Expr_app___override(x_574, x_16);
x_576 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_576, 0, x_575);
x_577 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_577, 0, x_573);
lean_ctor_set(x_577, 1, x_576);
lean_ctor_set_uint8(x_577, sizeof(void*)*2, x_413);
x_578 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_578, 0, x_577);
lean_ctor_set(x_569, 0, x_578);
return x_569;
}
}
else
{
lean_object* x_579; uint8_t x_580; 
x_579 = lean_ctor_get(x_569, 0);
lean_inc(x_579);
lean_dec(x_569);
x_580 = lean_unbox(x_579);
lean_dec(x_579);
if (x_580 == 0)
{
x_397 = x_2;
x_398 = x_3;
x_399 = x_4;
x_400 = x_5;
x_401 = x_6;
x_402 = x_7;
x_403 = x_8;
x_404 = lean_box(0);
goto block_409;
}
else
{
lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; 
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_581 = l_Lean_Meta_Grind_simpForall___closed__13;
x_582 = l_Lean_Meta_Grind_simpForall___closed__30;
x_583 = l_Lean_Expr_app___override(x_582, x_16);
x_584 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_584, 0, x_583);
x_585 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_585, 0, x_581);
lean_ctor_set(x_585, 1, x_584);
lean_ctor_set_uint8(x_585, sizeof(void*)*2, x_413);
x_586 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_586, 0, x_585);
x_587 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_587, 0, x_586);
return x_587;
}
}
}
else
{
uint8_t x_588; 
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
x_588 = !lean_is_exclusive(x_569);
if (x_588 == 0)
{
return x_569;
}
else
{
lean_object* x_589; lean_object* x_590; 
x_589 = lean_ctor_get(x_569, 0);
lean_inc(x_589);
lean_dec(x_569);
x_590 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_590, 0, x_589);
return x_590;
}
}
}
block_436:
{
if (lean_obj_tag(x_414) == 0)
{
uint8_t x_415; 
x_415 = !lean_is_exclusive(x_414);
if (x_415 == 0)
{
lean_object* x_416; uint8_t x_417; 
x_416 = lean_ctor_get(x_414, 0);
x_417 = lean_unbox(x_416);
lean_dec(x_416);
if (x_417 == 0)
{
lean_free_object(x_414);
x_397 = x_2;
x_398 = x_3;
x_399 = x_4;
x_400 = x_5;
x_401 = x_6;
x_402 = x_7;
x_403 = x_8;
x_404 = lean_box(0);
goto block_409;
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; 
lean_dec_ref(x_16);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_418 = l_Lean_Meta_Grind_simpForall___closed__13;
x_419 = l_Lean_Meta_Grind_simpForall___closed__16;
x_420 = l_Lean_Expr_app___override(x_419, x_15);
x_421 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_421, 0, x_420);
x_422 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_422, 0, x_418);
lean_ctor_set(x_422, 1, x_421);
lean_ctor_set_uint8(x_422, sizeof(void*)*2, x_413);
x_423 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_423, 0, x_422);
lean_ctor_set(x_414, 0, x_423);
return x_414;
}
}
else
{
lean_object* x_424; uint8_t x_425; 
x_424 = lean_ctor_get(x_414, 0);
lean_inc(x_424);
lean_dec(x_414);
x_425 = lean_unbox(x_424);
lean_dec(x_424);
if (x_425 == 0)
{
x_397 = x_2;
x_398 = x_3;
x_399 = x_4;
x_400 = x_5;
x_401 = x_6;
x_402 = x_7;
x_403 = x_8;
x_404 = lean_box(0);
goto block_409;
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; 
lean_dec_ref(x_16);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_426 = l_Lean_Meta_Grind_simpForall___closed__13;
x_427 = l_Lean_Meta_Grind_simpForall___closed__16;
x_428 = l_Lean_Expr_app___override(x_427, x_15);
x_429 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_429, 0, x_428);
x_430 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_430, 0, x_426);
lean_ctor_set(x_430, 1, x_429);
lean_ctor_set_uint8(x_430, sizeof(void*)*2, x_413);
x_431 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_431, 0, x_430);
x_432 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_432, 0, x_431);
return x_432;
}
}
}
else
{
uint8_t x_433; 
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
x_433 = !lean_is_exclusive(x_414);
if (x_433 == 0)
{
return x_414;
}
else
{
lean_object* x_434; lean_object* x_435; 
x_434 = lean_ctor_get(x_414, 0);
lean_inc(x_434);
lean_dec(x_414);
x_435 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_435, 0, x_434);
return x_435;
}
}
}
}
else
{
uint8_t x_591; 
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
x_591 = !lean_is_exclusive(x_411);
if (x_591 == 0)
{
return x_411;
}
else
{
lean_object* x_592; lean_object* x_593; 
x_592 = lean_ctor_get(x_411, 0);
lean_inc(x_592);
lean_dec(x_411);
x_593 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_593, 0, x_592);
return x_593;
}
}
}
else
{
lean_object* x_594; 
lean_inc_ref(x_15);
x_594 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_15, x_6);
if (lean_obj_tag(x_594) == 0)
{
lean_object* x_595; lean_object* x_596; lean_object* x_597; uint8_t x_598; 
x_595 = lean_ctor_get(x_594, 0);
lean_inc(x_595);
lean_dec_ref(x_594);
x_596 = l_Lean_Expr_cleanupAnnotations(x_595);
x_597 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__3;
x_598 = l_Lean_Expr_isConstOf(x_596, x_597);
if (x_598 == 0)
{
lean_object* x_599; uint8_t x_600; 
x_599 = l_Lean_Meta_Grind_simpForall___closed__12;
x_600 = l_Lean_Expr_isConstOf(x_596, x_599);
lean_dec_ref(x_596);
if (x_600 == 0)
{
x_397 = x_2;
x_398 = x_3;
x_399 = x_4;
x_400 = x_5;
x_401 = x_6;
x_402 = x_7;
x_403 = x_8;
x_404 = lean_box(0);
goto block_409;
}
else
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; 
x_601 = l_Lean_Meta_Grind_simpForall___closed__33;
x_602 = lean_expr_instantiate1(x_16, x_601);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_602);
x_603 = l_Lean_Meta_isProp(x_602, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_603) == 0)
{
uint8_t x_604; 
x_604 = !lean_is_exclusive(x_603);
if (x_604 == 0)
{
lean_object* x_605; uint8_t x_606; 
x_605 = lean_ctor_get(x_603, 0);
x_606 = lean_unbox(x_605);
lean_dec(x_605);
if (x_606 == 0)
{
lean_free_object(x_603);
lean_dec_ref(x_602);
x_397 = x_2;
x_398 = x_3;
x_399 = x_4;
x_400 = x_5;
x_401 = x_6;
x_402 = x_7;
x_403 = x_8;
x_404 = lean_box(0);
goto block_409;
}
else
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_607 = l_Lean_mkLambda(x_14, x_17, x_15, x_16);
x_608 = l_Lean_Meta_Grind_simpForall___closed__36;
x_609 = l_Lean_Expr_app___override(x_608, x_607);
x_610 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_610, 0, x_609);
x_611 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_611, 0, x_602);
lean_ctor_set(x_611, 1, x_610);
lean_ctor_set_uint8(x_611, sizeof(void*)*2, x_410);
x_612 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_612, 0, x_611);
lean_ctor_set(x_603, 0, x_612);
return x_603;
}
}
else
{
lean_object* x_613; uint8_t x_614; 
x_613 = lean_ctor_get(x_603, 0);
lean_inc(x_613);
lean_dec(x_603);
x_614 = lean_unbox(x_613);
lean_dec(x_613);
if (x_614 == 0)
{
lean_dec_ref(x_602);
x_397 = x_2;
x_398 = x_3;
x_399 = x_4;
x_400 = x_5;
x_401 = x_6;
x_402 = x_7;
x_403 = x_8;
x_404 = lean_box(0);
goto block_409;
}
else
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_615 = l_Lean_mkLambda(x_14, x_17, x_15, x_16);
x_616 = l_Lean_Meta_Grind_simpForall___closed__36;
x_617 = l_Lean_Expr_app___override(x_616, x_615);
x_618 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_618, 0, x_617);
x_619 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_619, 0, x_602);
lean_ctor_set(x_619, 1, x_618);
lean_ctor_set_uint8(x_619, sizeof(void*)*2, x_410);
x_620 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_620, 0, x_619);
x_621 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_621, 0, x_620);
return x_621;
}
}
}
else
{
uint8_t x_622; 
lean_dec_ref(x_602);
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
x_622 = !lean_is_exclusive(x_603);
if (x_622 == 0)
{
return x_603;
}
else
{
lean_object* x_623; lean_object* x_624; 
x_623 = lean_ctor_get(x_603, 0);
lean_inc(x_623);
lean_dec(x_603);
x_624 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_624, 0, x_623);
return x_624;
}
}
}
}
else
{
lean_object* x_625; lean_object* x_626; 
lean_dec_ref(x_596);
lean_inc_ref(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
x_625 = l_Lean_mkLambda(x_14, x_17, x_15, x_16);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_625);
x_626 = lean_infer_type(x_625, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_626) == 0)
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; 
x_627 = lean_ctor_get(x_626, 0);
lean_inc(x_627);
lean_dec_ref(x_626);
x_628 = l_Lean_Meta_Grind_simpForall___closed__38;
lean_inc_ref(x_15);
lean_inc(x_14);
x_629 = l_Lean_mkForall(x_14, x_17, x_15, x_628);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_630 = l_Lean_Meta_isExprDefEq(x_627, x_629, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_630) == 0)
{
uint8_t x_631; 
x_631 = !lean_is_exclusive(x_630);
if (x_631 == 0)
{
lean_object* x_632; uint8_t x_633; 
x_632 = lean_ctor_get(x_630, 0);
x_633 = lean_unbox(x_632);
lean_dec(x_632);
if (x_633 == 0)
{
lean_free_object(x_630);
lean_dec_ref(x_625);
x_397 = x_2;
x_398 = x_3;
x_399 = x_4;
x_400 = x_5;
x_401 = x_6;
x_402 = x_7;
x_403 = x_8;
x_404 = lean_box(0);
goto block_409;
}
else
{
lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; 
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
x_634 = l_Lean_Meta_Grind_simpForall___closed__13;
x_635 = l_Lean_Meta_Grind_simpForall___closed__41;
x_636 = l_Lean_Expr_app___override(x_635, x_625);
x_637 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_637, 0, x_636);
x_638 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_638, 0, x_634);
lean_ctor_set(x_638, 1, x_637);
lean_ctor_set_uint8(x_638, sizeof(void*)*2, x_410);
x_639 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_639, 0, x_638);
lean_ctor_set(x_630, 0, x_639);
return x_630;
}
}
else
{
lean_object* x_640; uint8_t x_641; 
x_640 = lean_ctor_get(x_630, 0);
lean_inc(x_640);
lean_dec(x_630);
x_641 = lean_unbox(x_640);
lean_dec(x_640);
if (x_641 == 0)
{
lean_dec_ref(x_625);
x_397 = x_2;
x_398 = x_3;
x_399 = x_4;
x_400 = x_5;
x_401 = x_6;
x_402 = x_7;
x_403 = x_8;
x_404 = lean_box(0);
goto block_409;
}
else
{
lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; 
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
x_642 = l_Lean_Meta_Grind_simpForall___closed__13;
x_643 = l_Lean_Meta_Grind_simpForall___closed__41;
x_644 = l_Lean_Expr_app___override(x_643, x_625);
x_645 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_645, 0, x_644);
x_646 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_646, 0, x_642);
lean_ctor_set(x_646, 1, x_645);
lean_ctor_set_uint8(x_646, sizeof(void*)*2, x_410);
x_647 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_647, 0, x_646);
x_648 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_648, 0, x_647);
return x_648;
}
}
}
else
{
uint8_t x_649; 
lean_dec_ref(x_625);
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
x_649 = !lean_is_exclusive(x_630);
if (x_649 == 0)
{
return x_630;
}
else
{
lean_object* x_650; lean_object* x_651; 
x_650 = lean_ctor_get(x_630, 0);
lean_inc(x_650);
lean_dec(x_630);
x_651 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_651, 0, x_650);
return x_651;
}
}
}
else
{
uint8_t x_652; 
lean_dec_ref(x_625);
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
x_652 = !lean_is_exclusive(x_626);
if (x_652 == 0)
{
return x_626;
}
else
{
lean_object* x_653; lean_object* x_654; 
x_653 = lean_ctor_get(x_626, 0);
lean_inc(x_653);
lean_dec(x_626);
x_654 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_654, 0, x_653);
return x_654;
}
}
}
}
else
{
uint8_t x_655; 
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
x_655 = !lean_is_exclusive(x_594);
if (x_655 == 0)
{
return x_594;
}
else
{
lean_object* x_656; lean_object* x_657; 
x_656 = lean_ctor_get(x_594, 0);
lean_inc(x_656);
lean_dec(x_594);
x_657 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_657, 0, x_656);
return x_657;
}
}
}
block_396:
{
if (x_26 == 0)
{
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
x_10 = lean_box(0);
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
lean_dec(x_24);
lean_dec(x_22);
lean_dec_ref(x_20);
x_32 = l_Lean_Meta_Grind_simpForall___closed__4;
x_33 = lean_name_eq(x_29, x_32);
lean_dec(x_29);
if (x_33 == 0)
{
lean_dec_ref(x_27);
lean_dec(x_25);
lean_dec(x_23);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
x_10 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_34 = l_Lean_Expr_appArg_x21(x_27);
lean_dec_ref(x_27);
x_35 = l_Lean_Expr_appArg_x21(x_16);
lean_dec_ref(x_16);
lean_inc_ref(x_34);
lean_inc_ref(x_15);
lean_inc(x_14);
x_36 = l_Lean_mkLambda(x_14, x_17, x_15, x_34);
lean_inc_ref(x_35);
lean_inc_ref(x_15);
lean_inc(x_14);
x_37 = l_Lean_mkLambda(x_14, x_17, x_15, x_35);
lean_inc_ref(x_15);
lean_inc(x_14);
x_38 = l_Lean_mkForall(x_14, x_17, x_15, x_34);
lean_inc_ref(x_15);
x_39 = l_Lean_mkForall(x_14, x_17, x_15, x_35);
lean_inc_ref(x_15);
x_40 = l_Lean_Meta_getLevel(x_15, x_19, x_23, x_18, x_25);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = l_Lean_mkAnd(x_38, x_39);
x_44 = l_Lean_Meta_Grind_simpForall___closed__6;
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_mkConst(x_44, x_46);
x_48 = l_Lean_mkApp3(x_47, x_15, x_36, x_37);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_50, 0, x_43);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*2, x_26);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_40, 0, x_51);
return x_40;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_52 = lean_ctor_get(x_40, 0);
lean_inc(x_52);
lean_dec(x_40);
x_53 = l_Lean_mkAnd(x_38, x_39);
x_54 = l_Lean_Meta_Grind_simpForall___closed__6;
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_52);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_mkConst(x_54, x_56);
x_58 = l_Lean_mkApp3(x_57, x_15, x_36, x_37);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_60, 0, x_53);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set_uint8(x_60, sizeof(void*)*2, x_26);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
else
{
uint8_t x_63; 
lean_dec_ref(x_39);
lean_dec_ref(x_38);
lean_dec_ref(x_37);
lean_dec_ref(x_36);
lean_dec_ref(x_15);
x_63 = !lean_is_exclusive(x_40);
if (x_63 == 0)
{
return x_40;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_40, 0);
lean_inc(x_64);
lean_dec(x_40);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
return x_65;
}
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_29);
x_66 = l_Lean_Expr_appArg_x21(x_27);
lean_dec_ref(x_27);
x_67 = l_Lean_Expr_appArg_x21(x_16);
lean_dec_ref(x_16);
x_68 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f(x_66);
if (lean_obj_tag(x_68) == 1)
{
uint8_t x_69; 
lean_dec_ref(x_66);
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_ctor_get(x_68, 0);
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_70, 1);
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_74 = lean_ctor_get(x_70, 0);
x_75 = lean_ctor_get(x_72, 0);
x_76 = lean_ctor_get(x_72, 1);
lean_inc_ref(x_67);
lean_inc_ref(x_15);
lean_inc(x_14);
x_77 = l_Lean_mkLambda(x_14, x_17, x_15, x_67);
x_78 = 0;
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_74);
x_79 = l_Lean_mkLambda(x_74, x_78, x_75, x_76);
lean_inc_ref(x_15);
lean_inc(x_14);
x_80 = l_Lean_mkLambda(x_14, x_17, x_15, x_79);
lean_inc(x_75);
lean_inc_ref(x_15);
lean_inc(x_14);
x_81 = l_Lean_mkLambda(x_14, x_17, x_15, x_75);
lean_inc(x_25);
lean_inc_ref(x_18);
lean_inc(x_23);
lean_inc_ref(x_19);
lean_inc_ref(x_15);
x_82 = l_Lean_Meta_getLevel(x_15, x_19, x_23, x_18, x_25);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec_ref(x_82);
lean_inc(x_75);
x_84 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpForall___lam__0___boxed), 10, 1);
lean_closure_set(x_84, 0, x_75);
lean_inc_ref(x_15);
lean_inc(x_14);
x_85 = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(x_14, x_15, x_84, x_22, x_20, x_24, x_19, x_23, x_18, x_25);
if (lean_obj_tag(x_85) == 0)
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_87 = lean_ctor_get(x_85, 0);
x_88 = lean_unsigned_to_nat(0u);
x_89 = lean_unsigned_to_nat(1u);
x_90 = lean_expr_lift_loose_bvars(x_67, x_88, x_89);
lean_dec_ref(x_67);
x_91 = l_Lean_mkOr(x_76, x_90);
x_92 = l_Lean_mkForall(x_74, x_78, x_75, x_91);
lean_inc_ref(x_15);
x_93 = l_Lean_mkForall(x_14, x_17, x_15, x_92);
x_94 = l_Lean_Meta_Grind_simpForall___closed__8;
x_95 = lean_box(0);
lean_ctor_set_tag(x_72, 1);
lean_ctor_set(x_72, 1, x_95);
lean_ctor_set(x_72, 0, x_87);
lean_ctor_set_tag(x_70, 1);
lean_ctor_set(x_70, 0, x_83);
x_96 = l_Lean_mkConst(x_94, x_70);
x_97 = l_Lean_mkApp4(x_96, x_15, x_81, x_77, x_80);
lean_ctor_set(x_68, 0, x_97);
x_98 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_98, 0, x_93);
lean_ctor_set(x_98, 1, x_68);
lean_ctor_set_uint8(x_98, sizeof(void*)*2, x_26);
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_85, 0, x_99);
return x_85;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_100 = lean_ctor_get(x_85, 0);
lean_inc(x_100);
lean_dec(x_85);
x_101 = lean_unsigned_to_nat(0u);
x_102 = lean_unsigned_to_nat(1u);
x_103 = lean_expr_lift_loose_bvars(x_67, x_101, x_102);
lean_dec_ref(x_67);
x_104 = l_Lean_mkOr(x_76, x_103);
x_105 = l_Lean_mkForall(x_74, x_78, x_75, x_104);
lean_inc_ref(x_15);
x_106 = l_Lean_mkForall(x_14, x_17, x_15, x_105);
x_107 = l_Lean_Meta_Grind_simpForall___closed__8;
x_108 = lean_box(0);
lean_ctor_set_tag(x_72, 1);
lean_ctor_set(x_72, 1, x_108);
lean_ctor_set(x_72, 0, x_100);
lean_ctor_set_tag(x_70, 1);
lean_ctor_set(x_70, 0, x_83);
x_109 = l_Lean_mkConst(x_107, x_70);
x_110 = l_Lean_mkApp4(x_109, x_15, x_81, x_77, x_80);
lean_ctor_set(x_68, 0, x_110);
x_111 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_111, 0, x_106);
lean_ctor_set(x_111, 1, x_68);
lean_ctor_set_uint8(x_111, sizeof(void*)*2, x_26);
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_113 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_113, 0, x_112);
return x_113;
}
}
else
{
uint8_t x_114; 
lean_dec(x_83);
lean_dec_ref(x_81);
lean_dec_ref(x_80);
lean_dec_ref(x_77);
lean_free_object(x_72);
lean_dec(x_76);
lean_dec(x_75);
lean_free_object(x_70);
lean_dec(x_74);
lean_free_object(x_68);
lean_dec_ref(x_67);
lean_dec_ref(x_15);
lean_dec(x_14);
x_114 = !lean_is_exclusive(x_85);
if (x_114 == 0)
{
return x_85;
}
else
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_85, 0);
lean_inc(x_115);
lean_dec(x_85);
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_115);
return x_116;
}
}
}
else
{
uint8_t x_117; 
lean_dec_ref(x_81);
lean_dec_ref(x_80);
lean_dec_ref(x_77);
lean_free_object(x_72);
lean_dec(x_76);
lean_dec(x_75);
lean_free_object(x_70);
lean_dec(x_74);
lean_free_object(x_68);
lean_dec_ref(x_67);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_15);
lean_dec(x_14);
x_117 = !lean_is_exclusive(x_82);
if (x_117 == 0)
{
return x_82;
}
else
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_82, 0);
lean_inc(x_118);
lean_dec(x_82);
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_118);
return x_119;
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_120 = lean_ctor_get(x_70, 0);
x_121 = lean_ctor_get(x_72, 0);
x_122 = lean_ctor_get(x_72, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_72);
lean_inc_ref(x_67);
lean_inc_ref(x_15);
lean_inc(x_14);
x_123 = l_Lean_mkLambda(x_14, x_17, x_15, x_67);
x_124 = 0;
lean_inc(x_122);
lean_inc(x_121);
lean_inc(x_120);
x_125 = l_Lean_mkLambda(x_120, x_124, x_121, x_122);
lean_inc_ref(x_15);
lean_inc(x_14);
x_126 = l_Lean_mkLambda(x_14, x_17, x_15, x_125);
lean_inc(x_121);
lean_inc_ref(x_15);
lean_inc(x_14);
x_127 = l_Lean_mkLambda(x_14, x_17, x_15, x_121);
lean_inc(x_25);
lean_inc_ref(x_18);
lean_inc(x_23);
lean_inc_ref(x_19);
lean_inc_ref(x_15);
x_128 = l_Lean_Meta_getLevel(x_15, x_19, x_23, x_18, x_25);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
lean_dec_ref(x_128);
lean_inc(x_121);
x_130 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpForall___lam__0___boxed), 10, 1);
lean_closure_set(x_130, 0, x_121);
lean_inc_ref(x_15);
lean_inc(x_14);
x_131 = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(x_14, x_15, x_130, x_22, x_20, x_24, x_19, x_23, x_18, x_25);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 x_133 = x_131;
} else {
 lean_dec_ref(x_131);
 x_133 = lean_box(0);
}
x_134 = lean_unsigned_to_nat(0u);
x_135 = lean_unsigned_to_nat(1u);
x_136 = lean_expr_lift_loose_bvars(x_67, x_134, x_135);
lean_dec_ref(x_67);
x_137 = l_Lean_mkOr(x_122, x_136);
x_138 = l_Lean_mkForall(x_120, x_124, x_121, x_137);
lean_inc_ref(x_15);
x_139 = l_Lean_mkForall(x_14, x_17, x_15, x_138);
x_140 = l_Lean_Meta_Grind_simpForall___closed__8;
x_141 = lean_box(0);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_132);
lean_ctor_set(x_142, 1, x_141);
lean_ctor_set_tag(x_70, 1);
lean_ctor_set(x_70, 1, x_142);
lean_ctor_set(x_70, 0, x_129);
x_143 = l_Lean_mkConst(x_140, x_70);
x_144 = l_Lean_mkApp4(x_143, x_15, x_127, x_123, x_126);
lean_ctor_set(x_68, 0, x_144);
x_145 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_145, 0, x_139);
lean_ctor_set(x_145, 1, x_68);
lean_ctor_set_uint8(x_145, sizeof(void*)*2, x_26);
x_146 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_146, 0, x_145);
if (lean_is_scalar(x_133)) {
 x_147 = lean_alloc_ctor(0, 1, 0);
} else {
 x_147 = x_133;
}
lean_ctor_set(x_147, 0, x_146);
return x_147;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_129);
lean_dec_ref(x_127);
lean_dec_ref(x_126);
lean_dec_ref(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_free_object(x_70);
lean_dec(x_120);
lean_free_object(x_68);
lean_dec_ref(x_67);
lean_dec_ref(x_15);
lean_dec(x_14);
x_148 = lean_ctor_get(x_131, 0);
lean_inc(x_148);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 x_149 = x_131;
} else {
 lean_dec_ref(x_131);
 x_149 = lean_box(0);
}
if (lean_is_scalar(x_149)) {
 x_150 = lean_alloc_ctor(1, 1, 0);
} else {
 x_150 = x_149;
}
lean_ctor_set(x_150, 0, x_148);
return x_150;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec_ref(x_127);
lean_dec_ref(x_126);
lean_dec_ref(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_free_object(x_70);
lean_dec(x_120);
lean_free_object(x_68);
lean_dec_ref(x_67);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_15);
lean_dec(x_14);
x_151 = lean_ctor_get(x_128, 0);
lean_inc(x_151);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 x_152 = x_128;
} else {
 lean_dec_ref(x_128);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 1, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_151);
return x_153;
}
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_154 = lean_ctor_get(x_70, 1);
x_155 = lean_ctor_get(x_70, 0);
lean_inc(x_154);
lean_inc(x_155);
lean_dec(x_70);
x_156 = lean_ctor_get(x_154, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_154, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_158 = x_154;
} else {
 lean_dec_ref(x_154);
 x_158 = lean_box(0);
}
lean_inc_ref(x_67);
lean_inc_ref(x_15);
lean_inc(x_14);
x_159 = l_Lean_mkLambda(x_14, x_17, x_15, x_67);
x_160 = 0;
lean_inc(x_157);
lean_inc(x_156);
lean_inc(x_155);
x_161 = l_Lean_mkLambda(x_155, x_160, x_156, x_157);
lean_inc_ref(x_15);
lean_inc(x_14);
x_162 = l_Lean_mkLambda(x_14, x_17, x_15, x_161);
lean_inc(x_156);
lean_inc_ref(x_15);
lean_inc(x_14);
x_163 = l_Lean_mkLambda(x_14, x_17, x_15, x_156);
lean_inc(x_25);
lean_inc_ref(x_18);
lean_inc(x_23);
lean_inc_ref(x_19);
lean_inc_ref(x_15);
x_164 = l_Lean_Meta_getLevel(x_15, x_19, x_23, x_18, x_25);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
lean_dec_ref(x_164);
lean_inc(x_156);
x_166 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpForall___lam__0___boxed), 10, 1);
lean_closure_set(x_166, 0, x_156);
lean_inc_ref(x_15);
lean_inc(x_14);
x_167 = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(x_14, x_15, x_166, x_22, x_20, x_24, x_19, x_23, x_18, x_25);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 x_169 = x_167;
} else {
 lean_dec_ref(x_167);
 x_169 = lean_box(0);
}
x_170 = lean_unsigned_to_nat(0u);
x_171 = lean_unsigned_to_nat(1u);
x_172 = lean_expr_lift_loose_bvars(x_67, x_170, x_171);
lean_dec_ref(x_67);
x_173 = l_Lean_mkOr(x_157, x_172);
x_174 = l_Lean_mkForall(x_155, x_160, x_156, x_173);
lean_inc_ref(x_15);
x_175 = l_Lean_mkForall(x_14, x_17, x_15, x_174);
x_176 = l_Lean_Meta_Grind_simpForall___closed__8;
x_177 = lean_box(0);
if (lean_is_scalar(x_158)) {
 x_178 = lean_alloc_ctor(1, 2, 0);
} else {
 x_178 = x_158;
 lean_ctor_set_tag(x_178, 1);
}
lean_ctor_set(x_178, 0, x_168);
lean_ctor_set(x_178, 1, x_177);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_165);
lean_ctor_set(x_179, 1, x_178);
x_180 = l_Lean_mkConst(x_176, x_179);
x_181 = l_Lean_mkApp4(x_180, x_15, x_163, x_159, x_162);
lean_ctor_set(x_68, 0, x_181);
x_182 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_182, 0, x_175);
lean_ctor_set(x_182, 1, x_68);
lean_ctor_set_uint8(x_182, sizeof(void*)*2, x_26);
x_183 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_183, 0, x_182);
if (lean_is_scalar(x_169)) {
 x_184 = lean_alloc_ctor(0, 1, 0);
} else {
 x_184 = x_169;
}
lean_ctor_set(x_184, 0, x_183);
return x_184;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_165);
lean_dec_ref(x_163);
lean_dec_ref(x_162);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_free_object(x_68);
lean_dec_ref(x_67);
lean_dec_ref(x_15);
lean_dec(x_14);
x_185 = lean_ctor_get(x_167, 0);
lean_inc(x_185);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 x_186 = x_167;
} else {
 lean_dec_ref(x_167);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(1, 1, 0);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_185);
return x_187;
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec_ref(x_163);
lean_dec_ref(x_162);
lean_dec_ref(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_free_object(x_68);
lean_dec_ref(x_67);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_15);
lean_dec(x_14);
x_188 = lean_ctor_get(x_164, 0);
lean_inc(x_188);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 x_189 = x_164;
} else {
 lean_dec_ref(x_164);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(1, 1, 0);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_188);
return x_190;
}
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_191 = lean_ctor_get(x_68, 0);
lean_inc(x_191);
lean_dec(x_68);
x_192 = lean_ctor_get(x_191, 1);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 0);
lean_inc(x_193);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_194 = x_191;
} else {
 lean_dec_ref(x_191);
 x_194 = lean_box(0);
}
x_195 = lean_ctor_get(x_192, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_192, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_197 = x_192;
} else {
 lean_dec_ref(x_192);
 x_197 = lean_box(0);
}
lean_inc_ref(x_67);
lean_inc_ref(x_15);
lean_inc(x_14);
x_198 = l_Lean_mkLambda(x_14, x_17, x_15, x_67);
x_199 = 0;
lean_inc(x_196);
lean_inc(x_195);
lean_inc(x_193);
x_200 = l_Lean_mkLambda(x_193, x_199, x_195, x_196);
lean_inc_ref(x_15);
lean_inc(x_14);
x_201 = l_Lean_mkLambda(x_14, x_17, x_15, x_200);
lean_inc(x_195);
lean_inc_ref(x_15);
lean_inc(x_14);
x_202 = l_Lean_mkLambda(x_14, x_17, x_15, x_195);
lean_inc(x_25);
lean_inc_ref(x_18);
lean_inc(x_23);
lean_inc_ref(x_19);
lean_inc_ref(x_15);
x_203 = l_Lean_Meta_getLevel(x_15, x_19, x_23, x_18, x_25);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
lean_dec_ref(x_203);
lean_inc(x_195);
x_205 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpForall___lam__0___boxed), 10, 1);
lean_closure_set(x_205, 0, x_195);
lean_inc_ref(x_15);
lean_inc(x_14);
x_206 = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(x_14, x_15, x_205, x_22, x_20, x_24, x_19, x_23, x_18, x_25);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 x_208 = x_206;
} else {
 lean_dec_ref(x_206);
 x_208 = lean_box(0);
}
x_209 = lean_unsigned_to_nat(0u);
x_210 = lean_unsigned_to_nat(1u);
x_211 = lean_expr_lift_loose_bvars(x_67, x_209, x_210);
lean_dec_ref(x_67);
x_212 = l_Lean_mkOr(x_196, x_211);
x_213 = l_Lean_mkForall(x_193, x_199, x_195, x_212);
lean_inc_ref(x_15);
x_214 = l_Lean_mkForall(x_14, x_17, x_15, x_213);
x_215 = l_Lean_Meta_Grind_simpForall___closed__8;
x_216 = lean_box(0);
if (lean_is_scalar(x_197)) {
 x_217 = lean_alloc_ctor(1, 2, 0);
} else {
 x_217 = x_197;
 lean_ctor_set_tag(x_217, 1);
}
lean_ctor_set(x_217, 0, x_207);
lean_ctor_set(x_217, 1, x_216);
if (lean_is_scalar(x_194)) {
 x_218 = lean_alloc_ctor(1, 2, 0);
} else {
 x_218 = x_194;
 lean_ctor_set_tag(x_218, 1);
}
lean_ctor_set(x_218, 0, x_204);
lean_ctor_set(x_218, 1, x_217);
x_219 = l_Lean_mkConst(x_215, x_218);
x_220 = l_Lean_mkApp4(x_219, x_15, x_202, x_198, x_201);
x_221 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_221, 0, x_220);
x_222 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_222, 0, x_214);
lean_ctor_set(x_222, 1, x_221);
lean_ctor_set_uint8(x_222, sizeof(void*)*2, x_26);
x_223 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_223, 0, x_222);
if (lean_is_scalar(x_208)) {
 x_224 = lean_alloc_ctor(0, 1, 0);
} else {
 x_224 = x_208;
}
lean_ctor_set(x_224, 0, x_223);
return x_224;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_204);
lean_dec_ref(x_202);
lean_dec_ref(x_201);
lean_dec_ref(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec_ref(x_67);
lean_dec_ref(x_15);
lean_dec(x_14);
x_225 = lean_ctor_get(x_206, 0);
lean_inc(x_225);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 x_226 = x_206;
} else {
 lean_dec_ref(x_206);
 x_226 = lean_box(0);
}
if (lean_is_scalar(x_226)) {
 x_227 = lean_alloc_ctor(1, 1, 0);
} else {
 x_227 = x_226;
}
lean_ctor_set(x_227, 0, x_225);
return x_227;
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec_ref(x_202);
lean_dec_ref(x_201);
lean_dec_ref(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_195);
lean_dec(x_194);
lean_dec(x_193);
lean_dec_ref(x_67);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_15);
lean_dec(x_14);
x_228 = lean_ctor_get(x_203, 0);
lean_inc(x_228);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 x_229 = x_203;
} else {
 lean_dec_ref(x_203);
 x_229 = lean_box(0);
}
if (lean_is_scalar(x_229)) {
 x_230 = lean_alloc_ctor(1, 1, 0);
} else {
 x_230 = x_229;
}
lean_ctor_set(x_230, 0, x_228);
return x_230;
}
}
}
else
{
lean_object* x_231; 
lean_dec(x_68);
x_231 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f(x_67);
lean_dec_ref(x_67);
if (lean_obj_tag(x_231) == 1)
{
uint8_t x_232; 
x_232 = !lean_is_exclusive(x_231);
if (x_232 == 0)
{
lean_object* x_233; uint8_t x_234; 
x_233 = lean_ctor_get(x_231, 0);
x_234 = !lean_is_exclusive(x_233);
if (x_234 == 0)
{
lean_object* x_235; uint8_t x_236; 
x_235 = lean_ctor_get(x_233, 1);
x_236 = !lean_is_exclusive(x_235);
if (x_236 == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_237 = lean_ctor_get(x_233, 0);
x_238 = lean_ctor_get(x_235, 0);
x_239 = lean_ctor_get(x_235, 1);
lean_inc_ref(x_66);
lean_inc_ref(x_15);
lean_inc(x_14);
x_240 = l_Lean_mkLambda(x_14, x_17, x_15, x_66);
x_241 = 0;
lean_inc(x_239);
lean_inc(x_238);
lean_inc(x_237);
x_242 = l_Lean_mkLambda(x_237, x_241, x_238, x_239);
lean_inc_ref(x_15);
lean_inc(x_14);
x_243 = l_Lean_mkLambda(x_14, x_17, x_15, x_242);
lean_inc(x_238);
lean_inc_ref(x_15);
lean_inc(x_14);
x_244 = l_Lean_mkLambda(x_14, x_17, x_15, x_238);
lean_inc(x_25);
lean_inc_ref(x_18);
lean_inc(x_23);
lean_inc_ref(x_19);
lean_inc_ref(x_15);
x_245 = l_Lean_Meta_getLevel(x_15, x_19, x_23, x_18, x_25);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
lean_dec_ref(x_245);
lean_inc(x_238);
x_247 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpForall___lam__0___boxed), 10, 1);
lean_closure_set(x_247, 0, x_238);
lean_inc_ref(x_15);
lean_inc(x_14);
x_248 = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(x_14, x_15, x_247, x_22, x_20, x_24, x_19, x_23, x_18, x_25);
if (lean_obj_tag(x_248) == 0)
{
uint8_t x_249; 
x_249 = !lean_is_exclusive(x_248);
if (x_249 == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_250 = lean_ctor_get(x_248, 0);
x_251 = lean_unsigned_to_nat(0u);
x_252 = lean_unsigned_to_nat(1u);
x_253 = lean_expr_lift_loose_bvars(x_66, x_251, x_252);
lean_dec_ref(x_66);
x_254 = l_Lean_mkOr(x_253, x_239);
x_255 = l_Lean_mkForall(x_237, x_241, x_238, x_254);
lean_inc_ref(x_15);
x_256 = l_Lean_mkForall(x_14, x_17, x_15, x_255);
x_257 = l_Lean_Meta_Grind_simpForall___closed__10;
x_258 = lean_box(0);
lean_ctor_set_tag(x_235, 1);
lean_ctor_set(x_235, 1, x_258);
lean_ctor_set(x_235, 0, x_250);
lean_ctor_set_tag(x_233, 1);
lean_ctor_set(x_233, 0, x_246);
x_259 = l_Lean_mkConst(x_257, x_233);
x_260 = l_Lean_mkApp4(x_259, x_15, x_244, x_240, x_243);
lean_ctor_set(x_231, 0, x_260);
x_261 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_261, 0, x_256);
lean_ctor_set(x_261, 1, x_231);
lean_ctor_set_uint8(x_261, sizeof(void*)*2, x_26);
x_262 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_248, 0, x_262);
return x_248;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_263 = lean_ctor_get(x_248, 0);
lean_inc(x_263);
lean_dec(x_248);
x_264 = lean_unsigned_to_nat(0u);
x_265 = lean_unsigned_to_nat(1u);
x_266 = lean_expr_lift_loose_bvars(x_66, x_264, x_265);
lean_dec_ref(x_66);
x_267 = l_Lean_mkOr(x_266, x_239);
x_268 = l_Lean_mkForall(x_237, x_241, x_238, x_267);
lean_inc_ref(x_15);
x_269 = l_Lean_mkForall(x_14, x_17, x_15, x_268);
x_270 = l_Lean_Meta_Grind_simpForall___closed__10;
x_271 = lean_box(0);
lean_ctor_set_tag(x_235, 1);
lean_ctor_set(x_235, 1, x_271);
lean_ctor_set(x_235, 0, x_263);
lean_ctor_set_tag(x_233, 1);
lean_ctor_set(x_233, 0, x_246);
x_272 = l_Lean_mkConst(x_270, x_233);
x_273 = l_Lean_mkApp4(x_272, x_15, x_244, x_240, x_243);
lean_ctor_set(x_231, 0, x_273);
x_274 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_274, 0, x_269);
lean_ctor_set(x_274, 1, x_231);
lean_ctor_set_uint8(x_274, sizeof(void*)*2, x_26);
x_275 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_275, 0, x_274);
x_276 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_276, 0, x_275);
return x_276;
}
}
else
{
uint8_t x_277; 
lean_dec(x_246);
lean_dec_ref(x_244);
lean_dec_ref(x_243);
lean_dec_ref(x_240);
lean_free_object(x_235);
lean_dec(x_239);
lean_dec(x_238);
lean_free_object(x_233);
lean_dec(x_237);
lean_free_object(x_231);
lean_dec_ref(x_66);
lean_dec_ref(x_15);
lean_dec(x_14);
x_277 = !lean_is_exclusive(x_248);
if (x_277 == 0)
{
return x_248;
}
else
{
lean_object* x_278; lean_object* x_279; 
x_278 = lean_ctor_get(x_248, 0);
lean_inc(x_278);
lean_dec(x_248);
x_279 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_279, 0, x_278);
return x_279;
}
}
}
else
{
uint8_t x_280; 
lean_dec_ref(x_244);
lean_dec_ref(x_243);
lean_dec_ref(x_240);
lean_free_object(x_235);
lean_dec(x_239);
lean_dec(x_238);
lean_free_object(x_233);
lean_dec(x_237);
lean_free_object(x_231);
lean_dec_ref(x_66);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_15);
lean_dec(x_14);
x_280 = !lean_is_exclusive(x_245);
if (x_280 == 0)
{
return x_245;
}
else
{
lean_object* x_281; lean_object* x_282; 
x_281 = lean_ctor_get(x_245, 0);
lean_inc(x_281);
lean_dec(x_245);
x_282 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_282, 0, x_281);
return x_282;
}
}
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_283 = lean_ctor_get(x_233, 0);
x_284 = lean_ctor_get(x_235, 0);
x_285 = lean_ctor_get(x_235, 1);
lean_inc(x_285);
lean_inc(x_284);
lean_dec(x_235);
lean_inc_ref(x_66);
lean_inc_ref(x_15);
lean_inc(x_14);
x_286 = l_Lean_mkLambda(x_14, x_17, x_15, x_66);
x_287 = 0;
lean_inc(x_285);
lean_inc(x_284);
lean_inc(x_283);
x_288 = l_Lean_mkLambda(x_283, x_287, x_284, x_285);
lean_inc_ref(x_15);
lean_inc(x_14);
x_289 = l_Lean_mkLambda(x_14, x_17, x_15, x_288);
lean_inc(x_284);
lean_inc_ref(x_15);
lean_inc(x_14);
x_290 = l_Lean_mkLambda(x_14, x_17, x_15, x_284);
lean_inc(x_25);
lean_inc_ref(x_18);
lean_inc(x_23);
lean_inc_ref(x_19);
lean_inc_ref(x_15);
x_291 = l_Lean_Meta_getLevel(x_15, x_19, x_23, x_18, x_25);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
lean_dec_ref(x_291);
lean_inc(x_284);
x_293 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpForall___lam__0___boxed), 10, 1);
lean_closure_set(x_293, 0, x_284);
lean_inc_ref(x_15);
lean_inc(x_14);
x_294 = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(x_14, x_15, x_293, x_22, x_20, x_24, x_19, x_23, x_18, x_25);
if (lean_obj_tag(x_294) == 0)
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
if (lean_is_exclusive(x_294)) {
 lean_ctor_release(x_294, 0);
 x_296 = x_294;
} else {
 lean_dec_ref(x_294);
 x_296 = lean_box(0);
}
x_297 = lean_unsigned_to_nat(0u);
x_298 = lean_unsigned_to_nat(1u);
x_299 = lean_expr_lift_loose_bvars(x_66, x_297, x_298);
lean_dec_ref(x_66);
x_300 = l_Lean_mkOr(x_299, x_285);
x_301 = l_Lean_mkForall(x_283, x_287, x_284, x_300);
lean_inc_ref(x_15);
x_302 = l_Lean_mkForall(x_14, x_17, x_15, x_301);
x_303 = l_Lean_Meta_Grind_simpForall___closed__10;
x_304 = lean_box(0);
x_305 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_305, 0, x_295);
lean_ctor_set(x_305, 1, x_304);
lean_ctor_set_tag(x_233, 1);
lean_ctor_set(x_233, 1, x_305);
lean_ctor_set(x_233, 0, x_292);
x_306 = l_Lean_mkConst(x_303, x_233);
x_307 = l_Lean_mkApp4(x_306, x_15, x_290, x_286, x_289);
lean_ctor_set(x_231, 0, x_307);
x_308 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_308, 0, x_302);
lean_ctor_set(x_308, 1, x_231);
lean_ctor_set_uint8(x_308, sizeof(void*)*2, x_26);
x_309 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_309, 0, x_308);
if (lean_is_scalar(x_296)) {
 x_310 = lean_alloc_ctor(0, 1, 0);
} else {
 x_310 = x_296;
}
lean_ctor_set(x_310, 0, x_309);
return x_310;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
lean_dec(x_292);
lean_dec_ref(x_290);
lean_dec_ref(x_289);
lean_dec_ref(x_286);
lean_dec(x_285);
lean_dec(x_284);
lean_free_object(x_233);
lean_dec(x_283);
lean_free_object(x_231);
lean_dec_ref(x_66);
lean_dec_ref(x_15);
lean_dec(x_14);
x_311 = lean_ctor_get(x_294, 0);
lean_inc(x_311);
if (lean_is_exclusive(x_294)) {
 lean_ctor_release(x_294, 0);
 x_312 = x_294;
} else {
 lean_dec_ref(x_294);
 x_312 = lean_box(0);
}
if (lean_is_scalar(x_312)) {
 x_313 = lean_alloc_ctor(1, 1, 0);
} else {
 x_313 = x_312;
}
lean_ctor_set(x_313, 0, x_311);
return x_313;
}
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; 
lean_dec_ref(x_290);
lean_dec_ref(x_289);
lean_dec_ref(x_286);
lean_dec(x_285);
lean_dec(x_284);
lean_free_object(x_233);
lean_dec(x_283);
lean_free_object(x_231);
lean_dec_ref(x_66);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_15);
lean_dec(x_14);
x_314 = lean_ctor_get(x_291, 0);
lean_inc(x_314);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 x_315 = x_291;
} else {
 lean_dec_ref(x_291);
 x_315 = lean_box(0);
}
if (lean_is_scalar(x_315)) {
 x_316 = lean_alloc_ctor(1, 1, 0);
} else {
 x_316 = x_315;
}
lean_ctor_set(x_316, 0, x_314);
return x_316;
}
}
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; uint8_t x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_317 = lean_ctor_get(x_233, 1);
x_318 = lean_ctor_get(x_233, 0);
lean_inc(x_317);
lean_inc(x_318);
lean_dec(x_233);
x_319 = lean_ctor_get(x_317, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_317, 1);
lean_inc(x_320);
if (lean_is_exclusive(x_317)) {
 lean_ctor_release(x_317, 0);
 lean_ctor_release(x_317, 1);
 x_321 = x_317;
} else {
 lean_dec_ref(x_317);
 x_321 = lean_box(0);
}
lean_inc_ref(x_66);
lean_inc_ref(x_15);
lean_inc(x_14);
x_322 = l_Lean_mkLambda(x_14, x_17, x_15, x_66);
x_323 = 0;
lean_inc(x_320);
lean_inc(x_319);
lean_inc(x_318);
x_324 = l_Lean_mkLambda(x_318, x_323, x_319, x_320);
lean_inc_ref(x_15);
lean_inc(x_14);
x_325 = l_Lean_mkLambda(x_14, x_17, x_15, x_324);
lean_inc(x_319);
lean_inc_ref(x_15);
lean_inc(x_14);
x_326 = l_Lean_mkLambda(x_14, x_17, x_15, x_319);
lean_inc(x_25);
lean_inc_ref(x_18);
lean_inc(x_23);
lean_inc_ref(x_19);
lean_inc_ref(x_15);
x_327 = l_Lean_Meta_getLevel(x_15, x_19, x_23, x_18, x_25);
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
lean_dec_ref(x_327);
lean_inc(x_319);
x_329 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpForall___lam__0___boxed), 10, 1);
lean_closure_set(x_329, 0, x_319);
lean_inc_ref(x_15);
lean_inc(x_14);
x_330 = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(x_14, x_15, x_329, x_22, x_20, x_24, x_19, x_23, x_18, x_25);
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 x_332 = x_330;
} else {
 lean_dec_ref(x_330);
 x_332 = lean_box(0);
}
x_333 = lean_unsigned_to_nat(0u);
x_334 = lean_unsigned_to_nat(1u);
x_335 = lean_expr_lift_loose_bvars(x_66, x_333, x_334);
lean_dec_ref(x_66);
x_336 = l_Lean_mkOr(x_335, x_320);
x_337 = l_Lean_mkForall(x_318, x_323, x_319, x_336);
lean_inc_ref(x_15);
x_338 = l_Lean_mkForall(x_14, x_17, x_15, x_337);
x_339 = l_Lean_Meta_Grind_simpForall___closed__10;
x_340 = lean_box(0);
if (lean_is_scalar(x_321)) {
 x_341 = lean_alloc_ctor(1, 2, 0);
} else {
 x_341 = x_321;
 lean_ctor_set_tag(x_341, 1);
}
lean_ctor_set(x_341, 0, x_331);
lean_ctor_set(x_341, 1, x_340);
x_342 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_342, 0, x_328);
lean_ctor_set(x_342, 1, x_341);
x_343 = l_Lean_mkConst(x_339, x_342);
x_344 = l_Lean_mkApp4(x_343, x_15, x_326, x_322, x_325);
lean_ctor_set(x_231, 0, x_344);
x_345 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_345, 0, x_338);
lean_ctor_set(x_345, 1, x_231);
lean_ctor_set_uint8(x_345, sizeof(void*)*2, x_26);
x_346 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_346, 0, x_345);
if (lean_is_scalar(x_332)) {
 x_347 = lean_alloc_ctor(0, 1, 0);
} else {
 x_347 = x_332;
}
lean_ctor_set(x_347, 0, x_346);
return x_347;
}
else
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; 
lean_dec(x_328);
lean_dec_ref(x_326);
lean_dec_ref(x_325);
lean_dec_ref(x_322);
lean_dec(x_321);
lean_dec(x_320);
lean_dec(x_319);
lean_dec(x_318);
lean_free_object(x_231);
lean_dec_ref(x_66);
lean_dec_ref(x_15);
lean_dec(x_14);
x_348 = lean_ctor_get(x_330, 0);
lean_inc(x_348);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 x_349 = x_330;
} else {
 lean_dec_ref(x_330);
 x_349 = lean_box(0);
}
if (lean_is_scalar(x_349)) {
 x_350 = lean_alloc_ctor(1, 1, 0);
} else {
 x_350 = x_349;
}
lean_ctor_set(x_350, 0, x_348);
return x_350;
}
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; 
lean_dec_ref(x_326);
lean_dec_ref(x_325);
lean_dec_ref(x_322);
lean_dec(x_321);
lean_dec(x_320);
lean_dec(x_319);
lean_dec(x_318);
lean_free_object(x_231);
lean_dec_ref(x_66);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_15);
lean_dec(x_14);
x_351 = lean_ctor_get(x_327, 0);
lean_inc(x_351);
if (lean_is_exclusive(x_327)) {
 lean_ctor_release(x_327, 0);
 x_352 = x_327;
} else {
 lean_dec_ref(x_327);
 x_352 = lean_box(0);
}
if (lean_is_scalar(x_352)) {
 x_353 = lean_alloc_ctor(1, 1, 0);
} else {
 x_353 = x_352;
}
lean_ctor_set(x_353, 0, x_351);
return x_353;
}
}
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; uint8_t x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_354 = lean_ctor_get(x_231, 0);
lean_inc(x_354);
lean_dec(x_231);
x_355 = lean_ctor_get(x_354, 1);
lean_inc(x_355);
x_356 = lean_ctor_get(x_354, 0);
lean_inc(x_356);
if (lean_is_exclusive(x_354)) {
 lean_ctor_release(x_354, 0);
 lean_ctor_release(x_354, 1);
 x_357 = x_354;
} else {
 lean_dec_ref(x_354);
 x_357 = lean_box(0);
}
x_358 = lean_ctor_get(x_355, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_355, 1);
lean_inc(x_359);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 lean_ctor_release(x_355, 1);
 x_360 = x_355;
} else {
 lean_dec_ref(x_355);
 x_360 = lean_box(0);
}
lean_inc_ref(x_66);
lean_inc_ref(x_15);
lean_inc(x_14);
x_361 = l_Lean_mkLambda(x_14, x_17, x_15, x_66);
x_362 = 0;
lean_inc(x_359);
lean_inc(x_358);
lean_inc(x_356);
x_363 = l_Lean_mkLambda(x_356, x_362, x_358, x_359);
lean_inc_ref(x_15);
lean_inc(x_14);
x_364 = l_Lean_mkLambda(x_14, x_17, x_15, x_363);
lean_inc(x_358);
lean_inc_ref(x_15);
lean_inc(x_14);
x_365 = l_Lean_mkLambda(x_14, x_17, x_15, x_358);
lean_inc(x_25);
lean_inc_ref(x_18);
lean_inc(x_23);
lean_inc_ref(x_19);
lean_inc_ref(x_15);
x_366 = l_Lean_Meta_getLevel(x_15, x_19, x_23, x_18, x_25);
if (lean_obj_tag(x_366) == 0)
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
lean_dec_ref(x_366);
lean_inc(x_358);
x_368 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpForall___lam__0___boxed), 10, 1);
lean_closure_set(x_368, 0, x_358);
lean_inc_ref(x_15);
lean_inc(x_14);
x_369 = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(x_14, x_15, x_368, x_22, x_20, x_24, x_19, x_23, x_18, x_25);
if (lean_obj_tag(x_369) == 0)
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 x_371 = x_369;
} else {
 lean_dec_ref(x_369);
 x_371 = lean_box(0);
}
x_372 = lean_unsigned_to_nat(0u);
x_373 = lean_unsigned_to_nat(1u);
x_374 = lean_expr_lift_loose_bvars(x_66, x_372, x_373);
lean_dec_ref(x_66);
x_375 = l_Lean_mkOr(x_374, x_359);
x_376 = l_Lean_mkForall(x_356, x_362, x_358, x_375);
lean_inc_ref(x_15);
x_377 = l_Lean_mkForall(x_14, x_17, x_15, x_376);
x_378 = l_Lean_Meta_Grind_simpForall___closed__10;
x_379 = lean_box(0);
if (lean_is_scalar(x_360)) {
 x_380 = lean_alloc_ctor(1, 2, 0);
} else {
 x_380 = x_360;
 lean_ctor_set_tag(x_380, 1);
}
lean_ctor_set(x_380, 0, x_370);
lean_ctor_set(x_380, 1, x_379);
if (lean_is_scalar(x_357)) {
 x_381 = lean_alloc_ctor(1, 2, 0);
} else {
 x_381 = x_357;
 lean_ctor_set_tag(x_381, 1);
}
lean_ctor_set(x_381, 0, x_367);
lean_ctor_set(x_381, 1, x_380);
x_382 = l_Lean_mkConst(x_378, x_381);
x_383 = l_Lean_mkApp4(x_382, x_15, x_365, x_361, x_364);
x_384 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_384, 0, x_383);
x_385 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_385, 0, x_377);
lean_ctor_set(x_385, 1, x_384);
lean_ctor_set_uint8(x_385, sizeof(void*)*2, x_26);
x_386 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_386, 0, x_385);
if (lean_is_scalar(x_371)) {
 x_387 = lean_alloc_ctor(0, 1, 0);
} else {
 x_387 = x_371;
}
lean_ctor_set(x_387, 0, x_386);
return x_387;
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; 
lean_dec(x_367);
lean_dec_ref(x_365);
lean_dec_ref(x_364);
lean_dec_ref(x_361);
lean_dec(x_360);
lean_dec(x_359);
lean_dec(x_358);
lean_dec(x_357);
lean_dec(x_356);
lean_dec_ref(x_66);
lean_dec_ref(x_15);
lean_dec(x_14);
x_388 = lean_ctor_get(x_369, 0);
lean_inc(x_388);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 x_389 = x_369;
} else {
 lean_dec_ref(x_369);
 x_389 = lean_box(0);
}
if (lean_is_scalar(x_389)) {
 x_390 = lean_alloc_ctor(1, 1, 0);
} else {
 x_390 = x_389;
}
lean_ctor_set(x_390, 0, x_388);
return x_390;
}
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; 
lean_dec_ref(x_365);
lean_dec_ref(x_364);
lean_dec_ref(x_361);
lean_dec(x_360);
lean_dec(x_359);
lean_dec(x_358);
lean_dec(x_357);
lean_dec(x_356);
lean_dec_ref(x_66);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_15);
lean_dec(x_14);
x_391 = lean_ctor_get(x_366, 0);
lean_inc(x_391);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 x_392 = x_366;
} else {
 lean_dec_ref(x_366);
 x_392 = lean_box(0);
}
if (lean_is_scalar(x_392)) {
 x_393 = lean_alloc_ctor(1, 1, 0);
} else {
 x_393 = x_392;
}
lean_ctor_set(x_393, 0, x_391);
return x_393;
}
}
}
else
{
lean_dec(x_231);
lean_dec_ref(x_66);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_15);
lean_dec(x_14);
x_10 = lean_box(0);
goto block_13;
}
}
}
}
else
{
lean_object* x_394; lean_object* x_395; 
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_18);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
x_394 = l_Lean_Meta_Grind_simpForall___closed__0;
x_395 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_395, 0, x_394);
return x_395;
}
}
}
block_409:
{
uint8_t x_405; 
x_405 = l_Lean_Expr_isApp(x_16);
if (x_405 == 0)
{
x_18 = x_402;
x_19 = x_400;
x_20 = x_398;
x_21 = lean_box(0);
x_22 = x_397;
x_23 = x_401;
x_24 = x_399;
x_25 = x_403;
x_26 = x_405;
goto block_396;
}
else
{
lean_object* x_406; lean_object* x_407; uint8_t x_408; 
x_406 = l_Lean_Expr_getAppNumArgs(x_16);
x_407 = lean_unsigned_to_nat(2u);
x_408 = lean_nat_dec_eq(x_406, x_407);
lean_dec(x_406);
x_18 = x_402;
x_19 = x_400;
x_20 = x_398;
x_21 = lean_box(0);
x_22 = x_397;
x_23 = x_401;
x_24 = x_399;
x_25 = x_403;
x_26 = x_408;
goto block_396;
}
}
}
else
{
lean_object* x_658; lean_object* x_659; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_658 = l_Lean_Meta_Grind_simpForall___closed__0;
x_659 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_659, 0, x_658);
return x_659;
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Meta_Grind_simpForall___closed__0;
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_simpForall(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_3);
x_16 = lean_unbox(x_6);
x_17 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0(x_1, x_2, x_15, x_4, x_5, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpForall", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_;
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1;
x_3 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_;
x_4 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__4_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(5);
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__5_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__4_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_;
x_3 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__5_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_;
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpForall___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_();
return x_2;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_7 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc_ref(x_17);
x_18 = l_Lean_Expr_appFnCleanup___redArg(x_15);
x_19 = l_Lean_Expr_isApp(x_18);
if (x_19 == 0)
{
lean_dec_ref(x_18);
lean_dec_ref(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_7 = lean_box(0);
goto block_10;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc_ref(x_20);
x_21 = l_Lean_Expr_appFnCleanup___redArg(x_18);
x_22 = l_Lean_Meta_Grind_propagateForallPropDown___closed__5;
x_23 = l_Lean_Expr_isConstOf(x_21, x_22);
if (x_23 == 0)
{
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_7 = lean_box(0);
goto block_10;
}
else
{
if (lean_obj_tag(x_17) == 6)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; uint8_t x_138; uint8_t x_168; 
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_17, 2);
lean_inc_ref(x_25);
lean_dec_ref(x_17);
x_168 = l_Lean_Expr_isApp(x_25);
if (x_168 == 0)
{
x_138 = x_168;
goto block_167;
}
else
{
lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_169 = l_Lean_Expr_getAppNumArgs(x_25);
x_170 = lean_unsigned_to_nat(2u);
x_171 = lean_nat_dec_eq(x_169, x_170);
lean_dec(x_169);
x_138 = x_171;
goto block_167;
}
block_107:
{
uint8_t x_31; 
x_31 = l_Lean_Expr_hasLooseBVars(x_25);
if (x_31 == 0)
{
if (x_23 == 0)
{
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_32; 
lean_inc(x_29);
lean_inc_ref(x_28);
lean_inc(x_27);
lean_inc_ref(x_26);
lean_inc_ref(x_20);
x_32 = l_Lean_Meta_isProp(x_20, x_26, x_27, x_28, x_29);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_free_object(x_32);
x_36 = l_Lean_Expr_constLevels_x21(x_21);
lean_dec_ref(x_21);
x_37 = l_Lean_Meta_Grind_simpExists___redArg___closed__1;
lean_inc(x_36);
x_38 = l_Lean_mkConst(x_37, x_36);
lean_inc_ref(x_20);
x_39 = l_Lean_Expr_app___override(x_38, x_20);
x_40 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_39, x_26, x_27, x_28, x_29);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
if (lean_obj_tag(x_42) == 1)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = l_Lean_Meta_Grind_simpExists___redArg___closed__3;
x_46 = l_Lean_mkConst(x_45, x_36);
lean_inc_ref(x_25);
x_47 = l_Lean_mkApp3(x_46, x_20, x_44, x_25);
lean_ctor_set(x_42, 0, x_47);
x_48 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_48, 0, x_25);
lean_ctor_set(x_48, 1, x_42);
lean_ctor_set_uint8(x_48, sizeof(void*)*2, x_23);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_40, 0, x_49);
return x_40;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = lean_ctor_get(x_42, 0);
lean_inc(x_50);
lean_dec(x_42);
x_51 = l_Lean_Meta_Grind_simpExists___redArg___closed__3;
x_52 = l_Lean_mkConst(x_51, x_36);
lean_inc_ref(x_25);
x_53 = l_Lean_mkApp3(x_52, x_20, x_50, x_25);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_55, 0, x_25);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*2, x_23);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_40, 0, x_56);
return x_40;
}
}
else
{
lean_free_object(x_40);
lean_dec(x_42);
lean_dec(x_36);
lean_dec_ref(x_25);
lean_dec_ref(x_20);
x_11 = lean_box(0);
goto block_14;
}
}
else
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_40, 0);
lean_inc(x_57);
lean_dec(x_40);
if (lean_obj_tag(x_57) == 1)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 x_59 = x_57;
} else {
 lean_dec_ref(x_57);
 x_59 = lean_box(0);
}
x_60 = l_Lean_Meta_Grind_simpExists___redArg___closed__3;
x_61 = l_Lean_mkConst(x_60, x_36);
lean_inc_ref(x_25);
x_62 = l_Lean_mkApp3(x_61, x_20, x_58, x_25);
if (lean_is_scalar(x_59)) {
 x_63 = lean_alloc_ctor(1, 1, 0);
} else {
 x_63 = x_59;
}
lean_ctor_set(x_63, 0, x_62);
x_64 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_64, 0, x_25);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set_uint8(x_64, sizeof(void*)*2, x_23);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
else
{
lean_dec(x_57);
lean_dec(x_36);
lean_dec_ref(x_25);
lean_dec_ref(x_20);
x_11 = lean_box(0);
goto block_14;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_36);
lean_dec_ref(x_25);
lean_dec_ref(x_20);
x_67 = !lean_is_exclusive(x_40);
if (x_67 == 0)
{
return x_40;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_40, 0);
lean_inc(x_68);
lean_dec(x_40);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_21);
lean_inc_ref(x_25);
lean_inc_ref(x_20);
x_70 = l_Lean_mkAnd(x_20, x_25);
x_71 = l_Lean_Meta_Grind_simpExists___redArg___closed__6;
x_72 = l_Lean_mkAppB(x_71, x_20, x_25);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_74, 0, x_70);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set_uint8(x_74, sizeof(void*)*2, x_23);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_32, 0, x_75);
return x_32;
}
}
else
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_32, 0);
lean_inc(x_76);
lean_dec(x_32);
x_77 = lean_unbox(x_76);
lean_dec(x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = l_Lean_Expr_constLevels_x21(x_21);
lean_dec_ref(x_21);
x_79 = l_Lean_Meta_Grind_simpExists___redArg___closed__1;
lean_inc(x_78);
x_80 = l_Lean_mkConst(x_79, x_78);
lean_inc_ref(x_20);
x_81 = l_Lean_Expr_app___override(x_80, x_20);
x_82 = l_Lean_Meta_Grind_synthInstanceMeta_x3f(x_81, x_26, x_27, x_28, x_29);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 x_84 = x_82;
} else {
 lean_dec_ref(x_82);
 x_84 = lean_box(0);
}
if (lean_obj_tag(x_83) == 1)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_85 = lean_ctor_get(x_83, 0);
lean_inc(x_85);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 x_86 = x_83;
} else {
 lean_dec_ref(x_83);
 x_86 = lean_box(0);
}
x_87 = l_Lean_Meta_Grind_simpExists___redArg___closed__3;
x_88 = l_Lean_mkConst(x_87, x_78);
lean_inc_ref(x_25);
x_89 = l_Lean_mkApp3(x_88, x_20, x_85, x_25);
if (lean_is_scalar(x_86)) {
 x_90 = lean_alloc_ctor(1, 1, 0);
} else {
 x_90 = x_86;
}
lean_ctor_set(x_90, 0, x_89);
x_91 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_91, 0, x_25);
lean_ctor_set(x_91, 1, x_90);
lean_ctor_set_uint8(x_91, sizeof(void*)*2, x_23);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
if (lean_is_scalar(x_84)) {
 x_93 = lean_alloc_ctor(0, 1, 0);
} else {
 x_93 = x_84;
}
lean_ctor_set(x_93, 0, x_92);
return x_93;
}
else
{
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_78);
lean_dec_ref(x_25);
lean_dec_ref(x_20);
x_11 = lean_box(0);
goto block_14;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_78);
lean_dec_ref(x_25);
lean_dec_ref(x_20);
x_94 = lean_ctor_get(x_82, 0);
lean_inc(x_94);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 x_95 = x_82;
} else {
 lean_dec_ref(x_82);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 1, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_94);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_21);
lean_inc_ref(x_25);
lean_inc_ref(x_20);
x_97 = l_Lean_mkAnd(x_20, x_25);
x_98 = l_Lean_Meta_Grind_simpExists___redArg___closed__6;
x_99 = l_Lean_mkAppB(x_98, x_20, x_25);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
x_101 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_101, 0, x_97);
lean_ctor_set(x_101, 1, x_100);
lean_ctor_set_uint8(x_101, sizeof(void*)*2, x_23);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_103 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_103, 0, x_102);
return x_103;
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_29);
lean_dec_ref(x_28);
lean_dec(x_27);
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
x_104 = !lean_is_exclusive(x_32);
if (x_104 == 0)
{
return x_32;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_32, 0);
lean_inc(x_105);
lean_dec(x_32);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_105);
return x_106;
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
lean_dec_ref(x_21);
lean_dec_ref(x_20);
x_11 = lean_box(0);
goto block_14;
}
}
block_137:
{
if (x_111 == 0)
{
uint8_t x_112; 
x_112 = l_Lean_Expr_hasLooseBVars(x_109);
if (x_112 == 0)
{
if (x_108 == 0)
{
lean_dec_ref(x_110);
lean_dec_ref(x_109);
lean_dec(x_24);
x_26 = x_2;
x_27 = x_3;
x_28 = x_4;
x_29 = x_5;
x_30 = lean_box(0);
goto block_107;
}
else
{
uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec_ref(x_25);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_113 = 0;
lean_inc_ref(x_20);
x_114 = l_Lean_mkLambda(x_24, x_113, x_20, x_110);
lean_inc_ref(x_114);
lean_inc_ref(x_20);
lean_inc_ref(x_21);
x_115 = l_Lean_mkAppB(x_21, x_20, x_114);
lean_inc_ref(x_109);
x_116 = l_Lean_mkAnd(x_115, x_109);
x_117 = l_Lean_Expr_constLevels_x21(x_21);
lean_dec_ref(x_21);
x_118 = l_Lean_Meta_Grind_simpExists___redArg___closed__8;
x_119 = l_Lean_mkConst(x_118, x_117);
x_120 = l_Lean_mkApp3(x_119, x_20, x_114, x_109);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_120);
x_122 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_122, 0, x_116);
lean_ctor_set(x_122, 1, x_121);
lean_ctor_set_uint8(x_122, sizeof(void*)*2, x_23);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_122);
x_124 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_124, 0, x_123);
return x_124;
}
}
else
{
lean_dec_ref(x_110);
lean_dec_ref(x_109);
lean_dec(x_24);
x_26 = x_2;
x_27 = x_3;
x_28 = x_4;
x_29 = x_5;
x_30 = lean_box(0);
goto block_107;
}
}
else
{
uint8_t x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec_ref(x_25);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_125 = 0;
lean_inc_ref(x_20);
x_126 = l_Lean_mkLambda(x_24, x_125, x_20, x_109);
lean_inc_ref(x_126);
lean_inc_ref(x_20);
lean_inc_ref(x_21);
x_127 = l_Lean_mkAppB(x_21, x_20, x_126);
lean_inc_ref(x_110);
x_128 = l_Lean_mkAnd(x_110, x_127);
x_129 = l_Lean_Expr_constLevels_x21(x_21);
lean_dec_ref(x_21);
x_130 = l_Lean_Meta_Grind_simpExists___redArg___closed__10;
x_131 = l_Lean_mkConst(x_130, x_129);
x_132 = l_Lean_mkApp3(x_131, x_20, x_126, x_110);
x_133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_133, 0, x_132);
x_134 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_134, 0, x_128);
lean_ctor_set(x_134, 1, x_133);
lean_ctor_set_uint8(x_134, sizeof(void*)*2, x_23);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_134);
x_136 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_136, 0, x_135);
return x_136;
}
}
block_167:
{
if (x_138 == 0)
{
lean_dec(x_24);
x_26 = x_2;
x_27 = x_3;
x_28 = x_4;
x_29 = x_5;
x_30 = lean_box(0);
goto block_107;
}
else
{
lean_object* x_139; lean_object* x_140; 
x_139 = l_Lean_Expr_appFn_x21(x_25);
x_140 = l_Lean_Expr_appFn_x21(x_139);
if (lean_obj_tag(x_140) == 4)
{
lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
lean_dec_ref(x_140);
x_142 = l_Lean_Meta_Grind_simpForall___closed__2;
x_143 = lean_name_eq(x_141, x_142);
if (x_143 == 0)
{
lean_object* x_144; uint8_t x_145; 
x_144 = l_Lean_Meta_Grind_simpForall___closed__4;
x_145 = lean_name_eq(x_141, x_144);
lean_dec(x_141);
if (x_145 == 0)
{
lean_dec_ref(x_139);
lean_dec(x_24);
x_26 = x_2;
x_27 = x_3;
x_28 = x_4;
x_29 = x_5;
x_30 = lean_box(0);
goto block_107;
}
else
{
lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_146 = l_Lean_Expr_appArg_x21(x_139);
lean_dec_ref(x_139);
x_147 = l_Lean_Expr_appArg_x21(x_25);
x_148 = l_Lean_Expr_hasLooseBVars(x_146);
if (x_148 == 0)
{
x_108 = x_145;
x_109 = x_147;
x_110 = x_146;
x_111 = x_145;
goto block_137;
}
else
{
x_108 = x_145;
x_109 = x_147;
x_110 = x_146;
x_111 = x_143;
goto block_137;
}
}
}
else
{
lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_141);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_149 = l_Lean_Expr_appArg_x21(x_139);
lean_dec_ref(x_139);
x_150 = l_Lean_Expr_appArg_x21(x_25);
lean_dec_ref(x_25);
x_151 = 0;
lean_inc_ref(x_20);
lean_inc(x_24);
x_152 = l_Lean_mkLambda(x_24, x_151, x_20, x_149);
lean_inc_ref(x_20);
x_153 = l_Lean_mkLambda(x_24, x_151, x_20, x_150);
x_154 = l_Lean_Expr_constLevels_x21(x_21);
lean_inc_ref(x_152);
lean_inc_ref(x_20);
lean_inc_ref(x_21);
x_155 = l_Lean_mkAppB(x_21, x_20, x_152);
lean_inc_ref(x_153);
lean_inc_ref(x_20);
x_156 = l_Lean_mkAppB(x_21, x_20, x_153);
x_157 = l_Lean_mkOr(x_155, x_156);
x_158 = l_Lean_Meta_Grind_simpExists___redArg___closed__12;
x_159 = l_Lean_mkConst(x_158, x_154);
x_160 = l_Lean_mkApp3(x_159, x_20, x_152, x_153);
x_161 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_161, 0, x_160);
x_162 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_162, 0, x_157);
lean_ctor_set(x_162, 1, x_161);
lean_ctor_set_uint8(x_162, sizeof(void*)*2, x_23);
x_163 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_163, 0, x_162);
x_164 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_164, 0, x_163);
return x_164;
}
}
else
{
lean_object* x_165; lean_object* x_166; 
lean_dec_ref(x_140);
lean_dec_ref(x_139);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_165 = l_Lean_Meta_Grind_simpForall___closed__0;
x_166 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_166, 0, x_165);
return x_166;
}
}
}
}
else
{
lean_object* x_172; lean_object* x_173; 
lean_dec_ref(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_172 = l_Lean_Meta_Grind_simpForall___closed__0;
x_173 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_173, 0, x_172);
return x_173;
}
}
}
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Meta_Grind_simpForall___closed__0;
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Meta_Grind_simpForall___closed__0;
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Grind_simpExists___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_simpExists___redArg(x_1, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_simpExists(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpExists", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_;
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1;
x_3 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_;
x_4 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_() {
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
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__4_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_;
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__5_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__4_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__6_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__5_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_;
x_3 = lean_array_push(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_;
x_3 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__6_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_;
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpExists___boxed), 9, 0);
x_5 = l_Lean_Meta_Simp_registerBuiltinSimproc(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addForallSimproc(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_;
x_6 = 1;
x_7 = l_Lean_Meta_Simp_Simprocs_add(x_1, x_5, x_6, x_2, x_3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_;
x_10 = l_Lean_Meta_Simp_Simprocs_add(x_8, x_9, x_6, x_2, x_3);
return x_10;
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
x_5 = l_Lean_Meta_Grind_addForallSimproc(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Init_Grind_Propagator(uint8_t builtin);
lean_object* initialize_Init_Simproc(uint8_t builtin);
lean_object* initialize_Init_Grind_Norm(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Propagate(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Internalize(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Anchor(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_EqResolution(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_SynthInstance(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_ForallProp(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Propagator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Simproc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Norm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Propagate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Internalize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Anchor(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_EqResolution(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
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
l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__0 = _init_l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__0);
l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__1 = _init_l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__1();
lean_mark_persistent(l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg___closed__1);
l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__0 = _init_l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__0();
l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__1 = _init_l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__1();
lean_mark_persistent(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__1);
l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__2 = _init_l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__2();
lean_mark_persistent(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__2);
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
if (builtin) {res = l_Lean_Meta_Grind_propagateExistsDown___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_115310127____hygCtx___hyg_8_();
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
l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_ = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_ = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_ = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_ = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__4_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_ = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__4_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__4_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__5_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_ = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__5_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__5_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_);
if (builtin) {res = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_();
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
l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_ = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_ = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_ = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__2_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_ = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__3_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__4_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_ = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__4_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__4_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__5_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_ = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__5_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__5_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_);
l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__6_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_ = _init_l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__6_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__6_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_);
if (builtin) {res = l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
