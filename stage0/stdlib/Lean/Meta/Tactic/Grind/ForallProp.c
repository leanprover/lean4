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
lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__12;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__6;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__29;
lean_object* l_Lean_Meta_Grind_addNewRawFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_AnchorRef_matches(lean_object*, uint64_t);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__1;
lean_object* l_Lean_Meta_Grind_synthInstanceMeta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__16;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateExistsDown___closed__5;
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__2;
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__7;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__5_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_;
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__0(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__6;
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__3;
lean_object* l_Lean_Expr_bvar___override(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat_spec__1(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_Meta_Grind_getAnchor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getAnchorRefs___redArg(lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateExistsDown___closed__0;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Grind_activateTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__3;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_;
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__1;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__10;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__3;
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkNot(lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__11;
lean_object* lean_expr_lift_loose_bvars(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__13;
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__12;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__28;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_updateLastTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateExistsDown(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Grind_mkEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpForall_declare__34___closed__0_00___x40_Lean_Meta_Tactic_Grind_ForallProp_4143869776____hygCtx___hyg_11_;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f(lean_object*);
lean_object* l_Lean_Meta_Grind_alreadyInternalized___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__14;
lean_object* l_Lean_Meta_Grind_getSymbolPriorities___redArg(lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqTrueProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__2;
lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__0;
static lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__10;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__13;
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__9;
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__2;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__26;
lean_object* l_Lean_Meta_Grind_isEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__4_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropUp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__5;
static lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__4;
size_t lean_usize_add(size_t, size_t);
static lean_object* l_Lean_Meta_Grind_simpForall___closed__39;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__24;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__4;
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateForallPropUp___closed__8;
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0____regBuiltin_Lean_Meta_Grind_simpExists_declare__39___closed__6_00___x40_Lean_Meta_Tactic_Grind_ForallProp_173604616____hygCtx___hyg_10_;
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateExistsDown___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropUp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateExistsDown___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f___closed__0;
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_Grind_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_propagateExistsDown___closed__1;
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_simpExists___redArg___closed__11;
static lean_object* l_Lean_Meta_Grind_simpForall___closed__32;
static lean_object* l_Lean_Meta_Grind_propagateForallPropDown___closed__11;
static lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg___closed__2;
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_52; uint8_t x_74; lean_object* x_75; lean_object* x_94; lean_object* x_116; 
x_116 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_3, x_4);
if (lean_obj_tag(x_116) == 0)
{
uint8_t x_117; 
x_117 = !lean_is_exclusive(x_116);
if (x_117 == 0)
{
lean_object* x_118; uint8_t x_119; 
x_118 = lean_ctor_get(x_116, 0);
x_119 = lean_unbox(x_118);
lean_dec(x_118);
if (x_119 == 0)
{
lean_object* x_120; 
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
x_120 = lean_box(0);
lean_ctor_set(x_116, 0, x_120);
return x_116;
}
else
{
lean_object* x_121; 
lean_free_object(x_116);
lean_inc_ref(x_2);
x_121 = l_Lean_Meta_Grind_isEqFalse___redArg(x_2, x_4, x_6, x_10, x_11);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; uint8_t x_123; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_unbox(x_122);
lean_dec(x_122);
if (x_123 == 0)
{
x_94 = x_121;
goto block_115;
}
else
{
lean_object* x_124; 
lean_dec_ref(x_121);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_3);
x_124 = l_Lean_Meta_isProp(x_3, x_8, x_9, x_10, x_11);
x_94 = x_124;
goto block_115;
}
}
else
{
x_94 = x_121;
goto block_115;
}
}
}
else
{
lean_object* x_125; uint8_t x_126; 
x_125 = lean_ctor_get(x_116, 0);
lean_inc(x_125);
lean_dec(x_116);
x_126 = lean_unbox(x_125);
lean_dec(x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
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
x_127 = lean_box(0);
x_128 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_128, 0, x_127);
return x_128;
}
else
{
lean_object* x_129; 
lean_inc_ref(x_2);
x_129 = l_Lean_Meta_Grind_isEqFalse___redArg(x_2, x_4, x_6, x_10, x_11);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; uint8_t x_131; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_unbox(x_130);
lean_dec(x_130);
if (x_131 == 0)
{
x_94 = x_129;
goto block_115;
}
else
{
lean_object* x_132; 
lean_dec_ref(x_129);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_3);
x_132 = l_Lean_Meta_isProp(x_3, x_8, x_9, x_10, x_11);
x_94 = x_132;
goto block_115;
}
}
else
{
x_94 = x_129;
goto block_115;
}
}
}
}
else
{
uint8_t x_133; 
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
x_133 = !lean_is_exclusive(x_116);
if (x_133 == 0)
{
return x_116;
}
else
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_116, 0);
lean_inc(x_134);
lean_dec(x_116);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_134);
return x_135;
}
}
block_51:
{
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
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
x_17 = lean_box(0);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; 
lean_free_object(x_13);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_18 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc(x_4);
lean_inc_ref(x_3);
x_20 = l_Lean_Meta_Grind_mkEqFalseProof(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4;
lean_inc_ref(x_2);
x_23 = l_Lean_mkApp4(x_22, x_2, x_3, x_19, x_21);
x_24 = l_Lean_Meta_Grind_pushEqFalse___redArg(x_2, x_23, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec(x_4);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_20, 0);
lean_inc(x_26);
lean_dec(x_20);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
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
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
return x_18;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_18, 0);
lean_inc(x_29);
lean_dec(x_18);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
}
else
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_13, 0);
lean_inc(x_31);
lean_dec(x_13);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
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
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
else
{
lean_object* x_35; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_35 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc(x_4);
lean_inc_ref(x_3);
x_37 = l_Lean_Meta_Grind_mkEqFalseProof(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
x_39 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4;
lean_inc_ref(x_2);
x_40 = l_Lean_mkApp4(x_39, x_2, x_3, x_36, x_38);
x_41 = l_Lean_Meta_Grind_pushEqFalse___redArg(x_2, x_40, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec(x_4);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_36);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_42 = lean_ctor_get(x_37, 0);
lean_inc(x_42);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 x_43 = x_37;
} else {
 lean_dec_ref(x_37);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 1, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_42);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
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
x_45 = lean_ctor_get(x_35, 0);
lean_inc(x_45);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_46 = x_35;
} else {
 lean_dec_ref(x_35);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 1, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_45);
return x_47;
}
}
}
}
else
{
uint8_t x_48; 
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
x_48 = !lean_is_exclusive(x_13);
if (x_48 == 0)
{
return x_13;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_13, 0);
lean_inc(x_49);
lean_dec(x_13);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
block_73:
{
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
x_54 = lean_unbox(x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
lean_inc_ref(x_3);
x_55 = l_Lean_Meta_Grind_isEqFalse___redArg(x_3, x_4, x_6, x_10, x_11);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_unbox(x_56);
lean_dec(x_56);
if (x_57 == 0)
{
x_13 = x_55;
goto block_51;
}
else
{
lean_object* x_58; 
lean_dec_ref(x_55);
lean_inc_ref(x_1);
x_58 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_4, x_6, x_10, x_11);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_unbox(x_59);
lean_dec(x_59);
if (x_60 == 0)
{
x_13 = x_58;
goto block_51;
}
else
{
lean_object* x_61; 
lean_dec_ref(x_58);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_2);
x_61 = l_Lean_Meta_isProp(x_2, x_8, x_9, x_10, x_11);
x_13 = x_61;
goto block_51;
}
}
else
{
x_13 = x_58;
goto block_51;
}
}
}
else
{
x_13 = x_55;
goto block_51;
}
}
else
{
lean_object* x_62; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc(x_4);
lean_inc_ref(x_3);
x_62 = l_Lean_Meta_Grind_mkEqTrueProof(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec_ref(x_62);
x_64 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__7;
x_65 = l_Lean_mkApp3(x_64, x_2, x_3, x_63);
x_66 = l_Lean_Meta_Grind_pushEqTrue___redArg(x_1, x_65, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec(x_4);
return x_66;
}
else
{
uint8_t x_67; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_67 = !lean_is_exclusive(x_62);
if (x_67 == 0)
{
return x_62;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_62, 0);
lean_inc(x_68);
lean_dec(x_62);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
return x_69;
}
}
}
}
else
{
uint8_t x_70; 
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
x_70 = !lean_is_exclusive(x_52);
if (x_70 == 0)
{
return x_52;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_52, 0);
lean_inc(x_71);
lean_dec(x_52);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
}
}
block_93:
{
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec_ref(x_75);
x_77 = lean_unbox(x_76);
lean_dec(x_76);
if (x_77 == 0)
{
lean_object* x_78; 
lean_inc_ref(x_3);
x_78 = l_Lean_Meta_Grind_isEqTrue___redArg(x_3, x_4, x_6, x_10, x_11);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_unbox(x_79);
lean_dec(x_79);
if (x_80 == 0)
{
x_52 = x_78;
goto block_73;
}
else
{
lean_object* x_81; 
lean_dec_ref(x_78);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_2);
x_81 = l_Lean_Meta_isProp(x_2, x_8, x_9, x_10, x_11);
x_52 = x_81;
goto block_73;
}
}
else
{
x_52 = x_78;
goto block_73;
}
}
else
{
lean_object* x_82; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_4);
lean_inc_ref(x_2);
x_82 = l_Lean_Meta_Grind_mkEqTrueProof(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec_ref(x_82);
x_84 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__10;
lean_inc_ref(x_3);
x_85 = l_Lean_mkApp3(x_84, x_2, x_3, x_83);
x_86 = l_Lean_Meta_Grind_pushEqCore___redArg(x_1, x_3, x_85, x_74, x_4, x_8, x_9, x_10, x_11);
lean_dec(x_4);
return x_86;
}
else
{
uint8_t x_87; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_87 = !lean_is_exclusive(x_82);
if (x_87 == 0)
{
return x_82;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_82, 0);
lean_inc(x_88);
lean_dec(x_82);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
return x_89;
}
}
}
}
else
{
uint8_t x_90; 
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
x_90 = !lean_is_exclusive(x_75);
if (x_90 == 0)
{
return x_75;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_75, 0);
lean_inc(x_91);
lean_dec(x_75);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
return x_92;
}
}
}
block_115:
{
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; uint8_t x_96; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
lean_dec_ref(x_94);
x_96 = lean_unbox(x_95);
if (x_96 == 0)
{
lean_object* x_97; 
lean_inc_ref(x_2);
x_97 = l_Lean_Meta_Grind_isEqTrue___redArg(x_2, x_4, x_6, x_10, x_11);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; uint8_t x_99; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_unbox(x_98);
lean_dec(x_98);
if (x_99 == 0)
{
uint8_t x_100; 
x_100 = lean_unbox(x_95);
lean_dec(x_95);
x_74 = x_100;
x_75 = x_97;
goto block_93;
}
else
{
lean_object* x_101; uint8_t x_102; 
lean_dec_ref(x_97);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_3);
x_101 = l_Lean_Meta_isProp(x_3, x_8, x_9, x_10, x_11);
x_102 = lean_unbox(x_95);
lean_dec(x_95);
x_74 = x_102;
x_75 = x_101;
goto block_93;
}
}
else
{
uint8_t x_103; 
x_103 = lean_unbox(x_95);
lean_dec(x_95);
x_74 = x_103;
x_75 = x_97;
goto block_93;
}
}
else
{
lean_object* x_104; 
lean_dec(x_95);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_6);
lean_inc(x_4);
lean_inc_ref(x_2);
x_104 = l_Lean_Meta_Grind_mkEqFalseProof(x_2, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
lean_dec_ref(x_104);
x_106 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__13;
x_107 = l_Lean_mkApp3(x_106, x_2, x_3, x_105);
x_108 = l_Lean_Meta_Grind_pushEqTrue___redArg(x_1, x_107, x_4, x_6, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec(x_4);
return x_108;
}
else
{
uint8_t x_109; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_109 = !lean_is_exclusive(x_104);
if (x_109 == 0)
{
return x_104;
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_104, 0);
lean_inc(x_110);
lean_dec(x_104);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_110);
return x_111;
}
}
}
}
else
{
uint8_t x_112; 
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
x_112 = !lean_is_exclusive(x_94);
if (x_112 == 0)
{
return x_94;
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_94, 0);
lean_inc(x_113);
lean_dec(x_94);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_113);
return x_114;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 13);
x_6 = l_Lean_checkTraceOption(x_5, x_4, x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(x_1, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec_ref(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec_ref(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc(x_12);
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(x_1, x_2, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropUp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_1, 2);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_35 = l_Lean_Meta_Grind_propagateForallPropUp___closed__6;
x_122 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(x_35, x_8);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
lean_dec_ref(x_122);
x_124 = lean_unbox(x_123);
lean_dec(x_123);
if (x_124 == 0)
{
x_80 = x_2;
x_81 = x_3;
x_82 = x_4;
x_83 = x_5;
x_84 = x_6;
x_85 = x_7;
x_86 = x_8;
x_87 = x_9;
x_88 = lean_box(0);
goto block_121;
}
else
{
lean_object* x_125; 
x_125 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; 
lean_dec_ref(x_125);
lean_inc_ref(x_1);
x_126 = l_Lean_MessageData_ofExpr(x_1);
x_127 = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(x_35, x_126, x_6, x_7, x_8, x_9);
lean_dec_ref(x_127);
x_80 = x_2;
x_81 = x_3;
x_82 = x_4;
x_83 = x_5;
x_84 = x_6;
x_85 = x_7;
x_86 = x_8;
x_87 = x_9;
x_88 = lean_box(0);
goto block_121;
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
return x_125;
}
}
block_34:
{
lean_object* x_26; 
lean_inc(x_24);
lean_inc_ref(x_23);
lean_inc(x_22);
lean_inc_ref(x_21);
x_26 = l_Lean_Meta_Simp_Result_getProof(x_19, x_21, x_22, x_23, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = l_Lean_Meta_Grind_propagateForallPropUp___closed__2;
lean_inc_ref(x_17);
lean_inc_ref(x_12);
x_29 = l_Lean_mkApp5(x_28, x_12, x_15, x_17, x_16, x_27);
x_30 = l_Lean_Meta_Grind_pushEqCore___redArg(x_1, x_17, x_29, x_18, x_20, x_21, x_22, x_23, x_24);
lean_dec(x_20);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_21);
lean_dec(x_20);
lean_dec_ref(x_17);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_1);
x_31 = !lean_is_exclusive(x_26);
if (x_31 == 0)
{
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
block_79:
{
lean_object* x_46; 
lean_inc(x_44);
lean_inc_ref(x_43);
lean_inc(x_42);
lean_inc_ref(x_41);
lean_inc(x_40);
lean_inc_ref(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc_ref(x_12);
x_46 = l_Lean_Meta_Grind_mkEqTrueProof(x_12, x_37, x_38, x_39, x_40, x_41, x_42, x_43, x_44);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec_ref(x_46);
lean_inc(x_47);
lean_inc_ref(x_12);
x_48 = l_Lean_Meta_mkOfEqTrueCore(x_12, x_47);
x_49 = lean_expr_instantiate1(x_13, x_48);
lean_dec_ref(x_48);
lean_inc(x_44);
lean_inc_ref(x_43);
lean_inc(x_42);
lean_inc_ref(x_41);
lean_inc(x_40);
lean_inc_ref(x_39);
lean_inc(x_38);
lean_inc(x_37);
x_50 = l_Lean_Meta_Grind_preprocess(x_49, x_37, x_38, x_39, x_40, x_41, x_42, x_43, x_44);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec_ref(x_50);
x_52 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_37);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
x_54 = lean_ctor_get(x_51, 0);
lean_inc_ref(x_54);
x_55 = lean_box(0);
lean_inc(x_44);
lean_inc_ref(x_43);
lean_inc(x_42);
lean_inc_ref(x_41);
lean_inc(x_40);
lean_inc_ref(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc_ref(x_54);
x_56 = lean_grind_internalize(x_54, x_53, x_55, x_37, x_38, x_39, x_40, x_41, x_42, x_43, x_44);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
lean_dec_ref(x_56);
x_57 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(x_35, x_43);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec_ref(x_57);
lean_inc_ref(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
x_59 = l_Lean_mkLambda(x_11, x_14, x_12, x_13);
x_60 = lean_unbox(x_58);
lean_dec(x_58);
if (x_60 == 0)
{
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_38);
x_15 = x_59;
x_16 = x_47;
x_17 = x_54;
x_18 = x_36;
x_19 = x_51;
x_20 = x_37;
x_21 = x_41;
x_22 = x_42;
x_23 = x_43;
x_24 = x_44;
x_25 = lean_box(0);
goto block_34;
}
else
{
lean_object* x_61; 
x_61 = l_Lean_Meta_Grind_updateLastTag(x_37, x_38, x_39, x_40, x_41, x_42, x_43, x_44);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_38);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec_ref(x_61);
x_62 = l_Lean_Meta_Grind_propagateForallPropUp___closed__8;
lean_inc_ref(x_54);
x_63 = l_Lean_MessageData_ofExpr(x_54);
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_Meta_Grind_propagateForallPropUp___closed__10;
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
lean_inc_ref(x_1);
x_67 = l_Lean_indentExpr(x_1);
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(x_35, x_68, x_41, x_42, x_43, x_44);
lean_dec_ref(x_69);
x_15 = x_59;
x_16 = x_47;
x_17 = x_54;
x_18 = x_36;
x_19 = x_51;
x_20 = x_37;
x_21 = x_41;
x_22 = x_42;
x_23 = x_43;
x_24 = x_44;
x_25 = lean_box(0);
goto block_34;
}
else
{
lean_dec_ref(x_59);
lean_dec_ref(x_54);
lean_dec(x_51);
lean_dec(x_47);
lean_dec(x_44);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_37);
lean_dec_ref(x_1);
return x_61;
}
}
}
else
{
lean_dec_ref(x_54);
lean_dec(x_51);
lean_dec(x_47);
lean_dec(x_44);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec_ref(x_1);
return x_56;
}
}
else
{
uint8_t x_70; 
lean_dec(x_51);
lean_dec(x_47);
lean_dec(x_44);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec_ref(x_1);
x_70 = !lean_is_exclusive(x_52);
if (x_70 == 0)
{
return x_52;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_52, 0);
lean_inc(x_71);
lean_dec(x_52);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_47);
lean_dec(x_44);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec_ref(x_1);
x_73 = !lean_is_exclusive(x_50);
if (x_73 == 0)
{
return x_50;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_50, 0);
lean_inc(x_74);
lean_dec(x_50);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_44);
lean_dec_ref(x_43);
lean_dec(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec_ref(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec_ref(x_1);
x_76 = !lean_is_exclusive(x_46);
if (x_76 == 0)
{
return x_46;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_46, 0);
lean_inc(x_77);
lean_dec(x_46);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
return x_78;
}
}
}
block_121:
{
uint8_t x_89; 
x_89 = l_Lean_Expr_hasLooseBVars(x_13);
if (x_89 == 0)
{
lean_object* x_90; 
lean_inc_ref(x_13);
lean_inc_ref(x_12);
x_90 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp(x_1, x_12, x_13, x_80, x_81, x_82, x_83, x_84, x_85, x_86, x_87);
return x_90;
}
else
{
lean_object* x_91; 
lean_inc_ref(x_12);
x_91 = l_Lean_Meta_Grind_isEqTrue___redArg(x_12, x_80, x_82, x_86, x_87);
if (lean_obj_tag(x_91) == 0)
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; uint8_t x_94; 
x_93 = lean_ctor_get(x_91, 0);
x_94 = lean_unbox(x_93);
lean_dec(x_93);
if (x_94 == 0)
{
lean_object* x_95; 
lean_dec(x_87);
lean_dec_ref(x_86);
lean_dec(x_85);
lean_dec_ref(x_84);
lean_dec(x_83);
lean_dec_ref(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec_ref(x_1);
x_95 = lean_box(0);
lean_ctor_set(x_91, 0, x_95);
return x_91;
}
else
{
lean_object* x_96; lean_object* x_97; uint8_t x_98; uint8_t x_99; 
lean_free_object(x_91);
x_96 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(x_35, x_86);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
lean_dec_ref(x_96);
x_98 = 0;
x_99 = lean_unbox(x_97);
lean_dec(x_97);
if (x_99 == 0)
{
x_36 = x_98;
x_37 = x_80;
x_38 = x_81;
x_39 = x_82;
x_40 = x_83;
x_41 = x_84;
x_42 = x_85;
x_43 = x_86;
x_44 = x_87;
x_45 = lean_box(0);
goto block_79;
}
else
{
lean_object* x_100; 
x_100 = l_Lean_Meta_Grind_updateLastTag(x_80, x_81, x_82, x_83, x_84, x_85, x_86, x_87);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec_ref(x_100);
x_101 = l_Lean_Meta_Grind_propagateForallPropUp___closed__12;
lean_inc_ref(x_1);
x_102 = l_Lean_MessageData_ofExpr(x_1);
x_103 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(x_35, x_103, x_84, x_85, x_86, x_87);
lean_dec_ref(x_104);
x_36 = x_98;
x_37 = x_80;
x_38 = x_81;
x_39 = x_82;
x_40 = x_83;
x_41 = x_84;
x_42 = x_85;
x_43 = x_86;
x_44 = x_87;
x_45 = lean_box(0);
goto block_79;
}
else
{
lean_dec(x_87);
lean_dec_ref(x_86);
lean_dec(x_85);
lean_dec_ref(x_84);
lean_dec(x_83);
lean_dec_ref(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec_ref(x_1);
return x_100;
}
}
}
}
else
{
lean_object* x_105; uint8_t x_106; 
x_105 = lean_ctor_get(x_91, 0);
lean_inc(x_105);
lean_dec(x_91);
x_106 = lean_unbox(x_105);
lean_dec(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_87);
lean_dec_ref(x_86);
lean_dec(x_85);
lean_dec_ref(x_84);
lean_dec(x_83);
lean_dec_ref(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec_ref(x_1);
x_107 = lean_box(0);
x_108 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_108, 0, x_107);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; uint8_t x_112; 
x_109 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(x_35, x_86);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
lean_dec_ref(x_109);
x_111 = 0;
x_112 = lean_unbox(x_110);
lean_dec(x_110);
if (x_112 == 0)
{
x_36 = x_111;
x_37 = x_80;
x_38 = x_81;
x_39 = x_82;
x_40 = x_83;
x_41 = x_84;
x_42 = x_85;
x_43 = x_86;
x_44 = x_87;
x_45 = lean_box(0);
goto block_79;
}
else
{
lean_object* x_113; 
x_113 = l_Lean_Meta_Grind_updateLastTag(x_80, x_81, x_82, x_83, x_84, x_85, x_86, x_87);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec_ref(x_113);
x_114 = l_Lean_Meta_Grind_propagateForallPropUp___closed__12;
lean_inc_ref(x_1);
x_115 = l_Lean_MessageData_ofExpr(x_1);
x_116 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(x_35, x_116, x_84, x_85, x_86, x_87);
lean_dec_ref(x_117);
x_36 = x_111;
x_37 = x_80;
x_38 = x_81;
x_39 = x_82;
x_40 = x_83;
x_41 = x_84;
x_42 = x_85;
x_43 = x_86;
x_44 = x_87;
x_45 = lean_box(0);
goto block_79;
}
else
{
lean_dec(x_87);
lean_dec_ref(x_86);
lean_dec(x_85);
lean_dec_ref(x_84);
lean_dec(x_83);
lean_dec_ref(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec_ref(x_1);
return x_113;
}
}
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_87);
lean_dec_ref(x_86);
lean_dec(x_85);
lean_dec_ref(x_84);
lean_dec(x_83);
lean_dec_ref(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec_ref(x_1);
x_118 = !lean_is_exclusive(x_91);
if (x_118 == 0)
{
return x_91;
}
else
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_91, 0);
lean_inc(x_119);
lean_dec(x_91);
x_120 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_120, 0, x_119);
return x_120;
}
}
}
}
}
else
{
lean_object* x_128; lean_object* x_129; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_128 = lean_box(0);
x_129 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_129, 0, x_128);
return x_129;
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropUp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_propagateForallPropUp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
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
lean_dec(x_14);
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
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_expr_eqv(x_5, x_7);
if (x_9 == 0)
{
return x_9;
}
else
{
x_1 = x_6;
x_2 = x_8;
goto _start;
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
lean_dec_ref(x_6);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_getAnchorRefs___redArg(x_3);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_10, 0);
if (lean_obj_tag(x_12) == 1)
{
lean_object* x_13; lean_object* x_14; 
lean_free_object(x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_14 = lean_infer_type(x_1, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = l_Lean_Meta_Grind_getAnchor(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_array_get_size(x_13);
x_21 = lean_nat_dec_lt(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_13);
x_22 = lean_box(x_21);
lean_ctor_set(x_16, 0, x_22);
return x_16;
}
else
{
if (x_21 == 0)
{
lean_object* x_23; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_13);
x_23 = lean_box(x_21);
lean_ctor_set(x_16, 0, x_23);
return x_16;
}
else
{
size_t x_24; size_t x_25; uint64_t x_26; uint8_t x_27; lean_object* x_28; 
x_24 = 0;
x_25 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_26 = lean_unbox_uint64(x_18);
lean_dec(x_18);
x_27 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof_spec__0(x_26, x_13, x_24, x_25);
lean_dec(x_13);
x_28 = lean_box(x_27);
lean_ctor_set(x_16, 0, x_28);
return x_16;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_16, 0);
lean_inc(x_29);
lean_dec(x_16);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_array_get_size(x_13);
x_32 = lean_nat_dec_lt(x_30, x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_13);
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
else
{
if (x_32 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_13);
x_35 = lean_box(x_32);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
else
{
size_t x_37; size_t x_38; uint64_t x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; 
x_37 = 0;
x_38 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_39 = lean_unbox_uint64(x_29);
lean_dec(x_29);
x_40 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof_spec__0(x_39, x_13, x_37, x_38);
lean_dec(x_13);
x_41 = lean_box(x_40);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_13);
x_43 = !lean_is_exclusive(x_16);
if (x_43 == 0)
{
return x_16;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_16, 0);
lean_inc(x_44);
lean_dec(x_16);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_46 = !lean_is_exclusive(x_14);
if (x_46 == 0)
{
return x_14;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_14, 0);
lean_inc(x_47);
lean_dec(x_14);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; lean_object* x_50; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_49 = 1;
x_50 = lean_box(x_49);
lean_ctor_set(x_10, 0, x_50);
return x_10;
}
}
else
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_10, 0);
lean_inc(x_51);
lean_dec(x_10);
if (lean_obj_tag(x_51) == 1)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_53 = lean_infer_type(x_1, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec_ref(x_53);
x_55 = l_Lean_Meta_Grind_getAnchor(x_54, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 x_57 = x_55;
} else {
 lean_dec_ref(x_55);
 x_57 = lean_box(0);
}
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_array_get_size(x_52);
x_60 = lean_nat_dec_lt(x_58, x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_59);
lean_dec(x_56);
lean_dec(x_52);
x_61 = lean_box(x_60);
if (lean_is_scalar(x_57)) {
 x_62 = lean_alloc_ctor(0, 1, 0);
} else {
 x_62 = x_57;
}
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
else
{
if (x_60 == 0)
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_59);
lean_dec(x_56);
lean_dec(x_52);
x_63 = lean_box(x_60);
if (lean_is_scalar(x_57)) {
 x_64 = lean_alloc_ctor(0, 1, 0);
} else {
 x_64 = x_57;
}
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
else
{
size_t x_65; size_t x_66; uint64_t x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; 
x_65 = 0;
x_66 = lean_usize_of_nat(x_59);
lean_dec(x_59);
x_67 = lean_unbox_uint64(x_56);
lean_dec(x_56);
x_68 = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof_spec__0(x_67, x_52, x_65, x_66);
lean_dec(x_52);
x_69 = lean_box(x_68);
if (lean_is_scalar(x_57)) {
 x_70 = lean_alloc_ctor(0, 1, 0);
} else {
 x_70 = x_57;
}
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_52);
x_71 = lean_ctor_get(x_55, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 x_72 = x_55;
} else {
 lean_dec_ref(x_55);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 1, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_71);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_52);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_74 = lean_ctor_get(x_53, 0);
lean_inc(x_74);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 x_75 = x_53;
} else {
 lean_dec_ref(x_53);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_74);
return x_76;
}
}
else
{
uint8_t x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_51);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_77 = 1;
x_78 = lean_box(x_77);
x_79 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_79, 0, x_78);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_80 = !lean_is_exclusive(x_10);
if (x_80 == 0)
{
return x_10;
}
else
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_10, 0);
lean_inc(x_81);
lean_dec(x_10);
x_82 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_82, 0, x_81);
return x_82;
}
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_5);
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
x_16 = lean_box(0);
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
x_25 = l_Lean_Meta_Grind_activateTheorem(x_23, x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec_ref(x_25);
x_26 = lean_ctor_get(x_23, 3);
lean_inc(x_26);
lean_dec_ref(x_23);
x_27 = lean_array_push(x_5, x_26);
x_15 = x_27;
x_16 = lean_box(0);
goto block_20;
}
else
{
uint8_t x_28; 
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
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_104; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_104 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_212; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
lean_dec_ref(x_104);
lean_inc(x_105);
x_212 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isEqTrueHyp_x3f(x_105);
if (lean_obj_tag(x_212) == 1)
{
uint8_t x_213; 
x_213 = !lean_is_exclusive(x_212);
if (x_213 == 0)
{
x_106 = x_212;
x_107 = x_2;
x_108 = x_3;
x_109 = x_4;
x_110 = x_5;
x_111 = x_6;
x_112 = x_7;
x_113 = x_8;
x_114 = x_9;
x_115 = lean_box(0);
goto block_211;
}
else
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_ctor_get(x_212, 0);
lean_inc(x_214);
lean_dec(x_212);
x_215 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_215, 0, x_214);
x_106 = x_215;
x_107 = x_2;
x_108 = x_3;
x_109 = x_4;
x_110 = x_5;
x_111 = x_6;
x_112 = x_7;
x_113 = x_8;
x_114 = x_9;
x_115 = lean_box(0);
goto block_211;
}
}
else
{
lean_object* x_216; uint8_t x_217; 
lean_dec(x_212);
x_216 = lean_st_ref_take(x_2);
x_217 = !lean_is_exclusive(x_216);
if (x_217 == 0)
{
lean_object* x_218; uint8_t x_219; 
x_218 = lean_ctor_get(x_216, 12);
x_219 = !lean_is_exclusive(x_218);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_220 = lean_ctor_get(x_218, 7);
x_221 = lean_unsigned_to_nat(1u);
x_222 = lean_nat_add(x_220, x_221);
lean_ctor_set(x_218, 7, x_222);
x_223 = lean_st_ref_set(x_2, x_216);
x_224 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__3;
x_225 = lean_name_append_index_after(x_224, x_220);
x_226 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_226, 0, x_225);
x_106 = x_226;
x_107 = x_2;
x_108 = x_3;
x_109 = x_4;
x_110 = x_5;
x_111 = x_6;
x_112 = x_7;
x_113 = x_8;
x_114 = x_9;
x_115 = lean_box(0);
goto block_211;
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_227 = lean_ctor_get(x_218, 0);
x_228 = lean_ctor_get(x_218, 1);
x_229 = lean_ctor_get(x_218, 2);
x_230 = lean_ctor_get(x_218, 3);
x_231 = lean_ctor_get(x_218, 4);
x_232 = lean_ctor_get(x_218, 5);
x_233 = lean_ctor_get(x_218, 6);
x_234 = lean_ctor_get(x_218, 7);
x_235 = lean_ctor_get(x_218, 8);
lean_inc(x_235);
lean_inc(x_234);
lean_inc(x_233);
lean_inc(x_232);
lean_inc(x_231);
lean_inc(x_230);
lean_inc(x_229);
lean_inc(x_228);
lean_inc(x_227);
lean_dec(x_218);
x_236 = lean_unsigned_to_nat(1u);
x_237 = lean_nat_add(x_234, x_236);
x_238 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_238, 0, x_227);
lean_ctor_set(x_238, 1, x_228);
lean_ctor_set(x_238, 2, x_229);
lean_ctor_set(x_238, 3, x_230);
lean_ctor_set(x_238, 4, x_231);
lean_ctor_set(x_238, 5, x_232);
lean_ctor_set(x_238, 6, x_233);
lean_ctor_set(x_238, 7, x_237);
lean_ctor_set(x_238, 8, x_235);
lean_ctor_set(x_216, 12, x_238);
x_239 = lean_st_ref_set(x_2, x_216);
x_240 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__3;
x_241 = lean_name_append_index_after(x_240, x_234);
x_242 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_242, 0, x_241);
x_106 = x_242;
x_107 = x_2;
x_108 = x_3;
x_109 = x_4;
x_110 = x_5;
x_111 = x_6;
x_112 = x_7;
x_113 = x_8;
x_114 = x_9;
x_115 = lean_box(0);
goto block_211;
}
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_243 = lean_ctor_get(x_216, 12);
x_244 = lean_ctor_get(x_216, 0);
x_245 = lean_ctor_get(x_216, 1);
x_246 = lean_ctor_get(x_216, 2);
x_247 = lean_ctor_get(x_216, 3);
x_248 = lean_ctor_get(x_216, 4);
x_249 = lean_ctor_get(x_216, 5);
x_250 = lean_ctor_get(x_216, 6);
x_251 = lean_ctor_get(x_216, 7);
x_252 = lean_ctor_get_uint8(x_216, sizeof(void*)*17);
x_253 = lean_ctor_get(x_216, 8);
x_254 = lean_ctor_get(x_216, 9);
x_255 = lean_ctor_get(x_216, 10);
x_256 = lean_ctor_get(x_216, 11);
x_257 = lean_ctor_get(x_216, 13);
x_258 = lean_ctor_get(x_216, 14);
x_259 = lean_ctor_get(x_216, 15);
x_260 = lean_ctor_get(x_216, 16);
lean_inc(x_260);
lean_inc(x_259);
lean_inc(x_258);
lean_inc(x_257);
lean_inc(x_243);
lean_inc(x_256);
lean_inc(x_255);
lean_inc(x_254);
lean_inc(x_253);
lean_inc(x_251);
lean_inc(x_250);
lean_inc(x_249);
lean_inc(x_248);
lean_inc(x_247);
lean_inc(x_246);
lean_inc(x_245);
lean_inc(x_244);
lean_dec(x_216);
x_261 = lean_ctor_get(x_243, 0);
lean_inc_ref(x_261);
x_262 = lean_ctor_get(x_243, 1);
lean_inc(x_262);
x_263 = lean_ctor_get(x_243, 2);
lean_inc_ref(x_263);
x_264 = lean_ctor_get(x_243, 3);
lean_inc_ref(x_264);
x_265 = lean_ctor_get(x_243, 4);
lean_inc(x_265);
x_266 = lean_ctor_get(x_243, 5);
lean_inc(x_266);
x_267 = lean_ctor_get(x_243, 6);
lean_inc_ref(x_267);
x_268 = lean_ctor_get(x_243, 7);
lean_inc(x_268);
x_269 = lean_ctor_get(x_243, 8);
lean_inc_ref(x_269);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 lean_ctor_release(x_243, 2);
 lean_ctor_release(x_243, 3);
 lean_ctor_release(x_243, 4);
 lean_ctor_release(x_243, 5);
 lean_ctor_release(x_243, 6);
 lean_ctor_release(x_243, 7);
 lean_ctor_release(x_243, 8);
 x_270 = x_243;
} else {
 lean_dec_ref(x_243);
 x_270 = lean_box(0);
}
x_271 = lean_unsigned_to_nat(1u);
x_272 = lean_nat_add(x_268, x_271);
if (lean_is_scalar(x_270)) {
 x_273 = lean_alloc_ctor(0, 9, 0);
} else {
 x_273 = x_270;
}
lean_ctor_set(x_273, 0, x_261);
lean_ctor_set(x_273, 1, x_262);
lean_ctor_set(x_273, 2, x_263);
lean_ctor_set(x_273, 3, x_264);
lean_ctor_set(x_273, 4, x_265);
lean_ctor_set(x_273, 5, x_266);
lean_ctor_set(x_273, 6, x_267);
lean_ctor_set(x_273, 7, x_272);
lean_ctor_set(x_273, 8, x_269);
x_274 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_274, 0, x_244);
lean_ctor_set(x_274, 1, x_245);
lean_ctor_set(x_274, 2, x_246);
lean_ctor_set(x_274, 3, x_247);
lean_ctor_set(x_274, 4, x_248);
lean_ctor_set(x_274, 5, x_249);
lean_ctor_set(x_274, 6, x_250);
lean_ctor_set(x_274, 7, x_251);
lean_ctor_set(x_274, 8, x_253);
lean_ctor_set(x_274, 9, x_254);
lean_ctor_set(x_274, 10, x_255);
lean_ctor_set(x_274, 11, x_256);
lean_ctor_set(x_274, 12, x_273);
lean_ctor_set(x_274, 13, x_257);
lean_ctor_set(x_274, 14, x_258);
lean_ctor_set(x_274, 15, x_259);
lean_ctor_set(x_274, 16, x_260);
lean_ctor_set_uint8(x_274, sizeof(void*)*17, x_252);
x_275 = lean_st_ref_set(x_2, x_274);
x_276 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__3;
x_277 = lean_name_append_index_after(x_276, x_268);
x_278 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_278, 0, x_277);
x_106 = x_278;
x_107 = x_2;
x_108 = x_3;
x_109 = x_4;
x_110 = x_5;
x_111 = x_6;
x_112 = x_7;
x_113 = x_8;
x_114 = x_9;
x_115 = lean_box(0);
goto block_211;
}
}
block_211:
{
lean_object* x_116; lean_object* x_117; 
lean_inc_ref(x_1);
x_116 = l_Lean_Meta_mkOfEqTrueCore(x_1, x_105);
lean_inc(x_114);
lean_inc_ref(x_113);
lean_inc(x_112);
lean_inc_ref(x_111);
lean_inc_ref(x_116);
x_117 = l_Lean_Meta_Grind_checkAnchorRefsEMatchTheoremProof(x_116, x_108, x_109, x_110, x_111, x_112, x_113, x_114);
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
lean_dec_ref(x_116);
lean_dec(x_114);
lean_dec_ref(x_113);
lean_dec(x_112);
lean_dec_ref(x_111);
lean_dec(x_110);
lean_dec_ref(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec_ref(x_1);
x_121 = lean_box(0);
lean_ctor_set(x_117, 0, x_121);
return x_117;
}
else
{
lean_object* x_122; lean_object* x_123; 
lean_free_object(x_117);
x_122 = lean_st_ref_get(x_107);
x_123 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_107);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
lean_dec_ref(x_123);
x_125 = l_Lean_Meta_Grind_getSymbolPriorities___redArg(x_109);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; lean_object* x_130; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec_ref(x_125);
x_127 = lean_unsigned_to_nat(1000u);
x_128 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___closed__0;
x_129 = 0;
lean_inc(x_114);
lean_inc_ref(x_113);
lean_inc(x_112);
lean_inc_ref(x_111);
lean_inc(x_126);
lean_inc_ref(x_116);
lean_inc_ref(x_106);
x_130 = l_Lean_Meta_Grind_mkEMatchTheoremUsingSingletonPatterns(x_106, x_128, x_116, x_127, x_126, x_129, x_111, x_112, x_113, x_114);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; size_t x_132; size_t x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
lean_dec_ref(x_130);
x_132 = lean_array_size(x_131);
x_133 = 0;
lean_inc(x_114);
lean_inc_ref(x_113);
lean_inc(x_112);
lean_inc_ref(x_111);
lean_inc(x_110);
lean_inc_ref(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_124);
x_134 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0(x_124, x_131, x_132, x_133, x_128, x_107, x_108, x_109, x_110, x_111, x_112, x_113, x_114);
lean_dec(x_131);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
lean_dec_ref(x_134);
x_136 = lean_box(6);
lean_inc(x_114);
lean_inc_ref(x_113);
lean_inc(x_112);
lean_inc_ref(x_111);
lean_inc(x_126);
lean_inc_ref(x_116);
lean_inc_ref(x_106);
x_137 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(x_106, x_116, x_136, x_126, x_111, x_112, x_113, x_114);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_122, 12);
lean_inc_ref(x_138);
lean_dec_ref(x_122);
x_139 = lean_ctor_get(x_138, 3);
lean_inc_ref(x_139);
lean_dec_ref(x_138);
x_140 = lean_ctor_get(x_137, 0);
lean_inc(x_140);
lean_dec_ref(x_137);
if (lean_obj_tag(x_140) == 1)
{
lean_object* x_141; lean_object* x_142; uint8_t x_143; 
x_141 = lean_ctor_get(x_139, 2);
lean_inc(x_141);
lean_dec_ref(x_139);
x_142 = lean_ctor_get(x_140, 0);
lean_inc(x_142);
lean_dec_ref(x_140);
x_143 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(x_135, x_142);
if (x_143 == 0)
{
lean_dec(x_142);
x_78 = x_141;
x_79 = x_126;
x_80 = x_129;
x_81 = x_116;
x_82 = x_106;
x_83 = x_124;
x_84 = x_135;
x_85 = x_107;
x_86 = x_108;
x_87 = x_109;
x_88 = x_110;
x_89 = x_111;
x_90 = x_112;
x_91 = x_113;
x_92 = x_114;
x_93 = lean_box(0);
goto block_103;
}
else
{
lean_object* x_144; 
lean_inc(x_114);
lean_inc_ref(x_113);
lean_inc(x_112);
lean_inc_ref(x_111);
lean_inc(x_110);
lean_inc_ref(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_124);
lean_inc(x_142);
x_144 = l_Lean_Meta_Grind_activateTheorem(x_142, x_124, x_107, x_108, x_109, x_110, x_111, x_112, x_113, x_114);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; 
lean_dec_ref(x_144);
x_145 = lean_ctor_get(x_142, 3);
lean_inc(x_145);
lean_dec(x_142);
x_146 = lean_array_push(x_135, x_145);
x_78 = x_141;
x_79 = x_126;
x_80 = x_129;
x_81 = x_116;
x_82 = x_106;
x_83 = x_124;
x_84 = x_146;
x_85 = x_107;
x_86 = x_108;
x_87 = x_109;
x_88 = x_110;
x_89 = x_111;
x_90 = x_112;
x_91 = x_113;
x_92 = x_114;
x_93 = lean_box(0);
goto block_103;
}
else
{
lean_dec(x_142);
lean_dec(x_141);
lean_dec(x_135);
lean_dec(x_126);
lean_dec(x_124);
lean_dec_ref(x_116);
lean_dec(x_114);
lean_dec_ref(x_113);
lean_dec(x_112);
lean_dec_ref(x_111);
lean_dec(x_110);
lean_dec_ref(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec_ref(x_1);
return x_144;
}
}
}
else
{
lean_object* x_147; 
lean_dec(x_140);
x_147 = lean_ctor_get(x_139, 2);
lean_inc(x_147);
lean_dec_ref(x_139);
x_78 = x_147;
x_79 = x_126;
x_80 = x_129;
x_81 = x_116;
x_82 = x_106;
x_83 = x_124;
x_84 = x_135;
x_85 = x_107;
x_86 = x_108;
x_87 = x_109;
x_88 = x_110;
x_89 = x_111;
x_90 = x_112;
x_91 = x_113;
x_92 = x_114;
x_93 = lean_box(0);
goto block_103;
}
}
else
{
uint8_t x_148; 
lean_dec(x_135);
lean_dec(x_126);
lean_dec(x_124);
lean_dec_ref(x_122);
lean_dec_ref(x_116);
lean_dec(x_114);
lean_dec_ref(x_113);
lean_dec(x_112);
lean_dec_ref(x_111);
lean_dec(x_110);
lean_dec_ref(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec_ref(x_1);
x_148 = !lean_is_exclusive(x_137);
if (x_148 == 0)
{
return x_137;
}
else
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_137, 0);
lean_inc(x_149);
lean_dec(x_137);
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_149);
return x_150;
}
}
}
else
{
uint8_t x_151; 
lean_dec(x_126);
lean_dec(x_124);
lean_dec_ref(x_122);
lean_dec_ref(x_116);
lean_dec(x_114);
lean_dec_ref(x_113);
lean_dec(x_112);
lean_dec_ref(x_111);
lean_dec(x_110);
lean_dec_ref(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec_ref(x_1);
x_151 = !lean_is_exclusive(x_134);
if (x_151 == 0)
{
return x_134;
}
else
{
lean_object* x_152; lean_object* x_153; 
x_152 = lean_ctor_get(x_134, 0);
lean_inc(x_152);
lean_dec(x_134);
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_152);
return x_153;
}
}
}
else
{
uint8_t x_154; 
lean_dec(x_126);
lean_dec(x_124);
lean_dec_ref(x_122);
lean_dec_ref(x_116);
lean_dec(x_114);
lean_dec_ref(x_113);
lean_dec(x_112);
lean_dec_ref(x_111);
lean_dec(x_110);
lean_dec_ref(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec_ref(x_1);
x_154 = !lean_is_exclusive(x_130);
if (x_154 == 0)
{
return x_130;
}
else
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_130, 0);
lean_inc(x_155);
lean_dec(x_130);
x_156 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_156, 0, x_155);
return x_156;
}
}
}
else
{
uint8_t x_157; 
lean_dec(x_124);
lean_dec_ref(x_122);
lean_dec_ref(x_116);
lean_dec(x_114);
lean_dec_ref(x_113);
lean_dec(x_112);
lean_dec_ref(x_111);
lean_dec(x_110);
lean_dec_ref(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec_ref(x_1);
x_157 = !lean_is_exclusive(x_125);
if (x_157 == 0)
{
return x_125;
}
else
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_ctor_get(x_125, 0);
lean_inc(x_158);
lean_dec(x_125);
x_159 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_159, 0, x_158);
return x_159;
}
}
}
else
{
uint8_t x_160; 
lean_dec_ref(x_122);
lean_dec_ref(x_116);
lean_dec(x_114);
lean_dec_ref(x_113);
lean_dec(x_112);
lean_dec_ref(x_111);
lean_dec(x_110);
lean_dec_ref(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec_ref(x_1);
x_160 = !lean_is_exclusive(x_123);
if (x_160 == 0)
{
return x_123;
}
else
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_123, 0);
lean_inc(x_161);
lean_dec(x_123);
x_162 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_162, 0, x_161);
return x_162;
}
}
}
}
else
{
lean_object* x_163; uint8_t x_164; 
x_163 = lean_ctor_get(x_117, 0);
lean_inc(x_163);
lean_dec(x_117);
x_164 = lean_unbox(x_163);
lean_dec(x_163);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; 
lean_dec_ref(x_116);
lean_dec(x_114);
lean_dec_ref(x_113);
lean_dec(x_112);
lean_dec_ref(x_111);
lean_dec(x_110);
lean_dec_ref(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec_ref(x_1);
x_165 = lean_box(0);
x_166 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_166, 0, x_165);
return x_166;
}
else
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_st_ref_get(x_107);
x_168 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_107);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
lean_dec_ref(x_168);
x_170 = l_Lean_Meta_Grind_getSymbolPriorities___redArg(x_109);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; lean_object* x_175; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
lean_dec_ref(x_170);
x_172 = lean_unsigned_to_nat(1000u);
x_173 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f___closed__0;
x_174 = 0;
lean_inc(x_114);
lean_inc_ref(x_113);
lean_inc(x_112);
lean_inc_ref(x_111);
lean_inc(x_171);
lean_inc_ref(x_116);
lean_inc_ref(x_106);
x_175 = l_Lean_Meta_Grind_mkEMatchTheoremUsingSingletonPatterns(x_106, x_173, x_116, x_172, x_171, x_174, x_111, x_112, x_113, x_114);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; size_t x_177; size_t x_178; lean_object* x_179; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
lean_dec_ref(x_175);
x_177 = lean_array_size(x_176);
x_178 = 0;
lean_inc(x_114);
lean_inc_ref(x_113);
lean_inc(x_112);
lean_inc_ref(x_111);
lean_inc(x_110);
lean_inc_ref(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_169);
x_179 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0(x_169, x_176, x_177, x_178, x_173, x_107, x_108, x_109, x_110, x_111, x_112, x_113, x_114);
lean_dec(x_176);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
lean_dec_ref(x_179);
x_181 = lean_box(6);
lean_inc(x_114);
lean_inc_ref(x_113);
lean_inc(x_112);
lean_inc_ref(x_111);
lean_inc(x_171);
lean_inc_ref(x_116);
lean_inc_ref(x_106);
x_182 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(x_106, x_116, x_181, x_171, x_111, x_112, x_113, x_114);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_167, 12);
lean_inc_ref(x_183);
lean_dec_ref(x_167);
x_184 = lean_ctor_get(x_183, 3);
lean_inc_ref(x_184);
lean_dec_ref(x_183);
x_185 = lean_ctor_get(x_182, 0);
lean_inc(x_185);
lean_dec_ref(x_182);
if (lean_obj_tag(x_185) == 1)
{
lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_186 = lean_ctor_get(x_184, 2);
lean_inc(x_186);
lean_dec_ref(x_184);
x_187 = lean_ctor_get(x_185, 0);
lean_inc(x_187);
lean_dec_ref(x_185);
x_188 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(x_180, x_187);
if (x_188 == 0)
{
lean_dec(x_187);
x_78 = x_186;
x_79 = x_171;
x_80 = x_174;
x_81 = x_116;
x_82 = x_106;
x_83 = x_169;
x_84 = x_180;
x_85 = x_107;
x_86 = x_108;
x_87 = x_109;
x_88 = x_110;
x_89 = x_111;
x_90 = x_112;
x_91 = x_113;
x_92 = x_114;
x_93 = lean_box(0);
goto block_103;
}
else
{
lean_object* x_189; 
lean_inc(x_114);
lean_inc_ref(x_113);
lean_inc(x_112);
lean_inc_ref(x_111);
lean_inc(x_110);
lean_inc_ref(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_inc(x_169);
lean_inc(x_187);
x_189 = l_Lean_Meta_Grind_activateTheorem(x_187, x_169, x_107, x_108, x_109, x_110, x_111, x_112, x_113, x_114);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; 
lean_dec_ref(x_189);
x_190 = lean_ctor_get(x_187, 3);
lean_inc(x_190);
lean_dec(x_187);
x_191 = lean_array_push(x_180, x_190);
x_78 = x_186;
x_79 = x_171;
x_80 = x_174;
x_81 = x_116;
x_82 = x_106;
x_83 = x_169;
x_84 = x_191;
x_85 = x_107;
x_86 = x_108;
x_87 = x_109;
x_88 = x_110;
x_89 = x_111;
x_90 = x_112;
x_91 = x_113;
x_92 = x_114;
x_93 = lean_box(0);
goto block_103;
}
else
{
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_180);
lean_dec(x_171);
lean_dec(x_169);
lean_dec_ref(x_116);
lean_dec(x_114);
lean_dec_ref(x_113);
lean_dec(x_112);
lean_dec_ref(x_111);
lean_dec(x_110);
lean_dec_ref(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec_ref(x_1);
return x_189;
}
}
}
else
{
lean_object* x_192; 
lean_dec(x_185);
x_192 = lean_ctor_get(x_184, 2);
lean_inc(x_192);
lean_dec_ref(x_184);
x_78 = x_192;
x_79 = x_171;
x_80 = x_174;
x_81 = x_116;
x_82 = x_106;
x_83 = x_169;
x_84 = x_180;
x_85 = x_107;
x_86 = x_108;
x_87 = x_109;
x_88 = x_110;
x_89 = x_111;
x_90 = x_112;
x_91 = x_113;
x_92 = x_114;
x_93 = lean_box(0);
goto block_103;
}
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_180);
lean_dec(x_171);
lean_dec(x_169);
lean_dec_ref(x_167);
lean_dec_ref(x_116);
lean_dec(x_114);
lean_dec_ref(x_113);
lean_dec(x_112);
lean_dec_ref(x_111);
lean_dec(x_110);
lean_dec_ref(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec_ref(x_1);
x_193 = lean_ctor_get(x_182, 0);
lean_inc(x_193);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 x_194 = x_182;
} else {
 lean_dec_ref(x_182);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_194)) {
 x_195 = lean_alloc_ctor(1, 1, 0);
} else {
 x_195 = x_194;
}
lean_ctor_set(x_195, 0, x_193);
return x_195;
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_171);
lean_dec(x_169);
lean_dec_ref(x_167);
lean_dec_ref(x_116);
lean_dec(x_114);
lean_dec_ref(x_113);
lean_dec(x_112);
lean_dec_ref(x_111);
lean_dec(x_110);
lean_dec_ref(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec_ref(x_1);
x_196 = lean_ctor_get(x_179, 0);
lean_inc(x_196);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 x_197 = x_179;
} else {
 lean_dec_ref(x_179);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(1, 1, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_196);
return x_198;
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_171);
lean_dec(x_169);
lean_dec_ref(x_167);
lean_dec_ref(x_116);
lean_dec(x_114);
lean_dec_ref(x_113);
lean_dec(x_112);
lean_dec_ref(x_111);
lean_dec(x_110);
lean_dec_ref(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec_ref(x_1);
x_199 = lean_ctor_get(x_175, 0);
lean_inc(x_199);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 x_200 = x_175;
} else {
 lean_dec_ref(x_175);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_200)) {
 x_201 = lean_alloc_ctor(1, 1, 0);
} else {
 x_201 = x_200;
}
lean_ctor_set(x_201, 0, x_199);
return x_201;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_169);
lean_dec_ref(x_167);
lean_dec_ref(x_116);
lean_dec(x_114);
lean_dec_ref(x_113);
lean_dec(x_112);
lean_dec_ref(x_111);
lean_dec(x_110);
lean_dec_ref(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec_ref(x_1);
x_202 = lean_ctor_get(x_170, 0);
lean_inc(x_202);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 x_203 = x_170;
} else {
 lean_dec_ref(x_170);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(1, 1, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_202);
return x_204;
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
lean_dec_ref(x_167);
lean_dec_ref(x_116);
lean_dec(x_114);
lean_dec_ref(x_113);
lean_dec(x_112);
lean_dec_ref(x_111);
lean_dec(x_110);
lean_dec_ref(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec_ref(x_1);
x_205 = lean_ctor_get(x_168, 0);
lean_inc(x_205);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 x_206 = x_168;
} else {
 lean_dec_ref(x_168);
 x_206 = lean_box(0);
}
if (lean_is_scalar(x_206)) {
 x_207 = lean_alloc_ctor(1, 1, 0);
} else {
 x_207 = x_206;
}
lean_ctor_set(x_207, 0, x_205);
return x_207;
}
}
}
}
else
{
uint8_t x_208; 
lean_dec_ref(x_116);
lean_dec(x_114);
lean_dec_ref(x_113);
lean_dec(x_112);
lean_dec_ref(x_111);
lean_dec(x_110);
lean_dec_ref(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec_ref(x_1);
x_208 = !lean_is_exclusive(x_117);
if (x_208 == 0)
{
return x_117;
}
else
{
lean_object* x_209; lean_object* x_210; 
x_209 = lean_ctor_get(x_117, 0);
lean_inc(x_209);
lean_dec(x_117);
x_210 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_210, 0, x_209);
return x_210;
}
}
}
}
else
{
uint8_t x_279; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_279 = !lean_is_exclusive(x_104);
if (x_279 == 0)
{
return x_104;
}
else
{
lean_object* x_280; lean_object* x_281; 
x_280 = lean_ctor_get(x_104, 0);
lean_inc(x_280);
lean_dec(x_104);
x_281 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_281, 0, x_280);
return x_281;
}
}
block_48:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_st_ref_get(x_12);
lean_dec(x_12);
x_22 = lean_ctor_get(x_21, 12);
lean_inc_ref(x_22);
lean_dec_ref(x_21);
x_23 = lean_ctor_get(x_22, 3);
lean_inc_ref(x_23);
lean_dec_ref(x_22);
x_24 = lean_ctor_get(x_23, 2);
lean_inc(x_24);
lean_dec_ref(x_23);
x_25 = lean_nat_dec_eq(x_24, x_11);
lean_dec(x_11);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_1);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
else
{
lean_object* x_28; 
x_28 = l_Lean_Meta_Grind_getConfig___redArg(x_14);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get_uint8(x_30, sizeof(void*)*10 + 13);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_1);
x_32 = lean_box(0);
lean_ctor_set(x_28, 0, x_32);
return x_28;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_free_object(x_28);
x_33 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1;
x_34 = l_Lean_indentExpr(x_1);
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_Meta_Grind_reportIssue(x_35, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
return x_36;
}
}
else
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_28, 0);
lean_inc(x_37);
lean_dec(x_28);
x_38 = lean_ctor_get_uint8(x_37, sizeof(void*)*10 + 13);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_1);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___closed__1;
x_42 = l_Lean_indentExpr(x_1);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Meta_Grind_reportIssue(x_43, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_1);
x_45 = !lean_is_exclusive(x_28);
if (x_45 == 0)
{
return x_28;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_28, 0);
lean_inc(x_46);
lean_dec(x_28);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
}
block_77:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_64 = lean_st_ref_get(x_55);
x_65 = lean_ctor_get(x_64, 12);
lean_inc_ref(x_65);
lean_dec_ref(x_64);
x_66 = lean_ctor_get(x_65, 3);
lean_inc_ref(x_66);
lean_dec_ref(x_65);
x_67 = lean_ctor_get(x_66, 2);
lean_inc(x_67);
lean_dec_ref(x_66);
x_68 = lean_nat_dec_eq(x_67, x_49);
lean_dec(x_67);
if (x_68 == 0)
{
lean_dec(x_54);
lean_dec_ref(x_52);
lean_dec_ref(x_51);
lean_dec_ref(x_50);
x_11 = x_49;
x_12 = x_55;
x_13 = x_56;
x_14 = x_57;
x_15 = x_58;
x_16 = x_59;
x_17 = x_60;
x_18 = x_61;
x_19 = x_62;
x_20 = lean_box(0);
goto block_48;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_alloc_ctor(8, 0, 1);
lean_ctor_set_uint8(x_69, 0, x_53);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
x_70 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(x_52, x_51, x_69, x_50, x_59, x_60, x_61, x_62);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec_ref(x_70);
if (lean_obj_tag(x_71) == 1)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec_ref(x_71);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_56);
lean_inc(x_55);
x_73 = l_Lean_Meta_Grind_activateTheorem(x_72, x_54, x_55, x_56, x_57, x_58, x_59, x_60, x_61, x_62);
if (lean_obj_tag(x_73) == 0)
{
lean_dec_ref(x_73);
x_11 = x_49;
x_12 = x_55;
x_13 = x_56;
x_14 = x_57;
x_15 = x_58;
x_16 = x_59;
x_17 = x_60;
x_18 = x_61;
x_19 = x_62;
x_20 = lean_box(0);
goto block_48;
}
else
{
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_49);
lean_dec_ref(x_1);
return x_73;
}
}
else
{
lean_dec(x_71);
lean_dec(x_54);
x_11 = x_49;
x_12 = x_55;
x_13 = x_56;
x_14 = x_57;
x_15 = x_58;
x_16 = x_59;
x_17 = x_60;
x_18 = x_61;
x_19 = x_62;
x_20 = lean_box(0);
goto block_48;
}
}
else
{
uint8_t x_74; 
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_49);
lean_dec_ref(x_1);
x_74 = !lean_is_exclusive(x_70);
if (x_74 == 0)
{
return x_70;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_70, 0);
lean_inc(x_75);
lean_dec(x_70);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
}
}
}
block_103:
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_box(7);
lean_inc(x_92);
lean_inc_ref(x_91);
lean_inc(x_90);
lean_inc_ref(x_89);
lean_inc_ref(x_79);
lean_inc_ref(x_81);
lean_inc_ref(x_82);
x_95 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_mkEMatchTheoremWithKind_x27_x3f(x_82, x_81, x_94, x_79, x_89, x_90, x_91, x_92);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
lean_dec_ref(x_95);
if (lean_obj_tag(x_96) == 1)
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
lean_dec_ref(x_96);
x_98 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isNewPat(x_84, x_97);
lean_dec_ref(x_84);
if (x_98 == 0)
{
lean_dec(x_97);
x_49 = x_78;
x_50 = x_79;
x_51 = x_81;
x_52 = x_82;
x_53 = x_80;
x_54 = x_83;
x_55 = x_85;
x_56 = x_86;
x_57 = x_87;
x_58 = x_88;
x_59 = x_89;
x_60 = x_90;
x_61 = x_91;
x_62 = x_92;
x_63 = lean_box(0);
goto block_77;
}
else
{
lean_object* x_99; 
lean_inc(x_92);
lean_inc_ref(x_91);
lean_inc(x_90);
lean_inc_ref(x_89);
lean_inc(x_88);
lean_inc_ref(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_83);
x_99 = l_Lean_Meta_Grind_activateTheorem(x_97, x_83, x_85, x_86, x_87, x_88, x_89, x_90, x_91, x_92);
if (lean_obj_tag(x_99) == 0)
{
lean_dec_ref(x_99);
x_49 = x_78;
x_50 = x_79;
x_51 = x_81;
x_52 = x_82;
x_53 = x_80;
x_54 = x_83;
x_55 = x_85;
x_56 = x_86;
x_57 = x_87;
x_58 = x_88;
x_59 = x_89;
x_60 = x_90;
x_61 = x_91;
x_62 = x_92;
x_63 = lean_box(0);
goto block_77;
}
else
{
lean_dec(x_92);
lean_dec_ref(x_91);
lean_dec(x_90);
lean_dec_ref(x_89);
lean_dec(x_88);
lean_dec_ref(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_83);
lean_dec_ref(x_82);
lean_dec_ref(x_81);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec_ref(x_1);
return x_99;
}
}
}
else
{
lean_dec(x_96);
lean_dec_ref(x_84);
x_49 = x_78;
x_50 = x_79;
x_51 = x_81;
x_52 = x_82;
x_53 = x_80;
x_54 = x_83;
x_55 = x_85;
x_56 = x_86;
x_57 = x_87;
x_58 = x_88;
x_59 = x_89;
x_60 = x_90;
x_61 = x_91;
x_62 = x_92;
x_63 = lean_box(0);
goto block_77;
}
}
else
{
uint8_t x_100; 
lean_dec(x_92);
lean_dec_ref(x_91);
lean_dec(x_90);
lean_dec_ref(x_89);
lean_dec(x_88);
lean_dec_ref(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec_ref(x_84);
lean_dec(x_83);
lean_dec_ref(x_82);
lean_dec_ref(x_81);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec_ref(x_1);
x_100 = !lean_is_exclusive(x_95);
if (x_100 == 0)
{
return x_95;
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_95, 0);
lean_inc(x_101);
lean_dec(x_95);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
return x_102;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
size_t x_15; size_t x_16; lean_object* x_17; 
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_17 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems_spec__0(x_1, x_2, x_15, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropDown(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_107; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_1, 2);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_inc_ref(x_1);
x_107 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_4, x_8, x_9);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; uint8_t x_109; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
lean_dec_ref(x_107);
x_109 = lean_unbox(x_108);
lean_dec(x_108);
if (x_109 == 0)
{
lean_object* x_110; 
lean_inc_ref(x_1);
x_110 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_4, x_8, x_9);
if (lean_obj_tag(x_110) == 0)
{
uint8_t x_111; 
x_111 = !lean_is_exclusive(x_110);
if (x_111 == 0)
{
lean_object* x_112; uint8_t x_113; 
x_112 = lean_ctor_get(x_110, 0);
x_113 = lean_unbox(x_112);
lean_dec(x_112);
if (x_113 == 0)
{
lean_object* x_114; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_114 = lean_box(0);
lean_ctor_set(x_110, 0, x_114);
return x_110;
}
else
{
lean_object* x_115; 
lean_free_object(x_110);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_1);
x_115 = l_Lean_Meta_Grind_eqResolution(x_1, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
lean_dec_ref(x_115);
if (lean_obj_tag(x_116) == 1)
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 x_118 = x_116;
} else {
 lean_dec_ref(x_116);
 x_118 = lean_box(0);
}
x_119 = !lean_is_exclusive(x_117);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_120 = lean_ctor_get(x_117, 0);
x_121 = lean_ctor_get(x_117, 1);
x_146 = l_Lean_Meta_Grind_propagateForallPropDown___closed__1;
x_147 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(x_146, x_8);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
lean_dec_ref(x_147);
x_149 = lean_unbox(x_148);
lean_dec(x_148);
if (x_149 == 0)
{
lean_free_object(x_117);
x_122 = x_2;
x_123 = x_3;
x_124 = x_4;
x_125 = x_5;
x_126 = x_6;
x_127 = x_7;
x_128 = x_8;
x_129 = x_9;
x_130 = lean_box(0);
goto block_145;
}
else
{
lean_object* x_150; 
x_150 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec_ref(x_150);
lean_inc_ref(x_1);
x_151 = l_Lean_MessageData_ofExpr(x_1);
x_152 = l_Lean_Meta_Grind_propagateForallPropDown___closed__3;
lean_ctor_set_tag(x_117, 7);
lean_ctor_set(x_117, 1, x_152);
lean_ctor_set(x_117, 0, x_151);
lean_inc(x_120);
x_153 = l_Lean_MessageData_ofExpr(x_120);
x_154 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_154, 0, x_117);
lean_ctor_set(x_154, 1, x_153);
x_155 = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(x_146, x_154, x_6, x_7, x_8, x_9);
lean_dec_ref(x_155);
x_122 = x_2;
x_123 = x_3;
x_124 = x_4;
x_125 = x_5;
x_126 = x_6;
x_127 = x_7;
x_128 = x_8;
x_129 = x_9;
x_130 = lean_box(0);
goto block_145;
}
else
{
lean_free_object(x_117);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_118);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_150;
}
}
block_145:
{
lean_object* x_131; 
lean_inc(x_129);
lean_inc_ref(x_128);
lean_inc(x_127);
lean_inc_ref(x_126);
lean_inc(x_125);
lean_inc_ref(x_124);
lean_inc(x_123);
lean_inc(x_122);
lean_inc_ref(x_1);
x_131 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_122, x_123, x_124, x_125, x_126, x_127, x_128, x_129);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
lean_dec_ref(x_131);
x_133 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_122);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
lean_dec_ref(x_133);
lean_inc_ref(x_1);
x_135 = l_Lean_Meta_mkOfEqTrueCore(x_1, x_132);
x_136 = l_Lean_Expr_app___override(x_121, x_135);
lean_inc_ref(x_1);
if (lean_is_scalar(x_118)) {
 x_137 = lean_alloc_ctor(4, 1, 0);
} else {
 x_137 = x_118;
 lean_ctor_set_tag(x_137, 4);
}
lean_ctor_set(x_137, 0, x_1);
lean_inc(x_129);
lean_inc_ref(x_128);
lean_inc(x_127);
lean_inc_ref(x_126);
x_138 = l_Lean_Meta_Grind_addNewRawFact(x_136, x_120, x_134, x_137, x_122, x_123, x_124, x_125, x_126, x_127, x_128, x_129);
if (lean_obj_tag(x_138) == 0)
{
lean_dec_ref(x_138);
x_62 = x_122;
x_63 = x_123;
x_64 = x_124;
x_65 = x_125;
x_66 = x_126;
x_67 = x_127;
x_68 = x_128;
x_69 = x_129;
x_70 = lean_box(0);
goto block_106;
}
else
{
lean_dec(x_129);
lean_dec_ref(x_128);
lean_dec(x_127);
lean_dec_ref(x_126);
lean_dec(x_125);
lean_dec_ref(x_124);
lean_dec(x_123);
lean_dec(x_122);
lean_dec_ref(x_1);
return x_138;
}
}
else
{
uint8_t x_139; 
lean_dec(x_132);
lean_dec(x_129);
lean_dec_ref(x_128);
lean_dec(x_127);
lean_dec_ref(x_126);
lean_dec(x_125);
lean_dec_ref(x_124);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_118);
lean_dec_ref(x_1);
x_139 = !lean_is_exclusive(x_133);
if (x_139 == 0)
{
return x_133;
}
else
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_133, 0);
lean_inc(x_140);
lean_dec(x_133);
x_141 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_141, 0, x_140);
return x_141;
}
}
}
else
{
uint8_t x_142; 
lean_dec(x_129);
lean_dec_ref(x_128);
lean_dec(x_127);
lean_dec_ref(x_126);
lean_dec(x_125);
lean_dec_ref(x_124);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_118);
lean_dec_ref(x_1);
x_142 = !lean_is_exclusive(x_131);
if (x_142 == 0)
{
return x_131;
}
else
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_131, 0);
lean_inc(x_143);
lean_dec(x_131);
x_144 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_144, 0, x_143);
return x_144;
}
}
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
x_156 = lean_ctor_get(x_117, 0);
x_157 = lean_ctor_get(x_117, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_117);
x_182 = l_Lean_Meta_Grind_propagateForallPropDown___closed__1;
x_183 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(x_182, x_8);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
lean_dec_ref(x_183);
x_185 = lean_unbox(x_184);
lean_dec(x_184);
if (x_185 == 0)
{
x_158 = x_2;
x_159 = x_3;
x_160 = x_4;
x_161 = x_5;
x_162 = x_6;
x_163 = x_7;
x_164 = x_8;
x_165 = x_9;
x_166 = lean_box(0);
goto block_181;
}
else
{
lean_object* x_186; 
x_186 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec_ref(x_186);
lean_inc_ref(x_1);
x_187 = l_Lean_MessageData_ofExpr(x_1);
x_188 = l_Lean_Meta_Grind_propagateForallPropDown___closed__3;
x_189 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
lean_inc(x_156);
x_190 = l_Lean_MessageData_ofExpr(x_156);
x_191 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
x_192 = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(x_182, x_191, x_6, x_7, x_8, x_9);
lean_dec_ref(x_192);
x_158 = x_2;
x_159 = x_3;
x_160 = x_4;
x_161 = x_5;
x_162 = x_6;
x_163 = x_7;
x_164 = x_8;
x_165 = x_9;
x_166 = lean_box(0);
goto block_181;
}
else
{
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_118);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_186;
}
}
block_181:
{
lean_object* x_167; 
lean_inc(x_165);
lean_inc_ref(x_164);
lean_inc(x_163);
lean_inc_ref(x_162);
lean_inc(x_161);
lean_inc_ref(x_160);
lean_inc(x_159);
lean_inc(x_158);
lean_inc_ref(x_1);
x_167 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_158, x_159, x_160, x_161, x_162, x_163, x_164, x_165);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
lean_dec_ref(x_167);
x_169 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_158);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
lean_dec_ref(x_169);
lean_inc_ref(x_1);
x_171 = l_Lean_Meta_mkOfEqTrueCore(x_1, x_168);
x_172 = l_Lean_Expr_app___override(x_157, x_171);
lean_inc_ref(x_1);
if (lean_is_scalar(x_118)) {
 x_173 = lean_alloc_ctor(4, 1, 0);
} else {
 x_173 = x_118;
 lean_ctor_set_tag(x_173, 4);
}
lean_ctor_set(x_173, 0, x_1);
lean_inc(x_165);
lean_inc_ref(x_164);
lean_inc(x_163);
lean_inc_ref(x_162);
x_174 = l_Lean_Meta_Grind_addNewRawFact(x_172, x_156, x_170, x_173, x_158, x_159, x_160, x_161, x_162, x_163, x_164, x_165);
if (lean_obj_tag(x_174) == 0)
{
lean_dec_ref(x_174);
x_62 = x_158;
x_63 = x_159;
x_64 = x_160;
x_65 = x_161;
x_66 = x_162;
x_67 = x_163;
x_68 = x_164;
x_69 = x_165;
x_70 = lean_box(0);
goto block_106;
}
else
{
lean_dec(x_165);
lean_dec_ref(x_164);
lean_dec(x_163);
lean_dec_ref(x_162);
lean_dec(x_161);
lean_dec_ref(x_160);
lean_dec(x_159);
lean_dec(x_158);
lean_dec_ref(x_1);
return x_174;
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_168);
lean_dec(x_165);
lean_dec_ref(x_164);
lean_dec(x_163);
lean_dec_ref(x_162);
lean_dec(x_161);
lean_dec_ref(x_160);
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_118);
lean_dec_ref(x_1);
x_175 = lean_ctor_get(x_169, 0);
lean_inc(x_175);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 x_176 = x_169;
} else {
 lean_dec_ref(x_169);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(1, 1, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_175);
return x_177;
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_165);
lean_dec_ref(x_164);
lean_dec(x_163);
lean_dec_ref(x_162);
lean_dec(x_161);
lean_dec_ref(x_160);
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_118);
lean_dec_ref(x_1);
x_178 = lean_ctor_get(x_167, 0);
lean_inc(x_178);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 x_179 = x_167;
} else {
 lean_dec_ref(x_167);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(1, 1, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_178);
return x_180;
}
}
}
}
else
{
lean_dec(x_116);
x_62 = x_2;
x_63 = x_3;
x_64 = x_4;
x_65 = x_5;
x_66 = x_6;
x_67 = x_7;
x_68 = x_8;
x_69 = x_9;
x_70 = lean_box(0);
goto block_106;
}
}
else
{
uint8_t x_193; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_193 = !lean_is_exclusive(x_115);
if (x_193 == 0)
{
return x_115;
}
else
{
lean_object* x_194; lean_object* x_195; 
x_194 = lean_ctor_get(x_115, 0);
lean_inc(x_194);
lean_dec(x_115);
x_195 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_195, 0, x_194);
return x_195;
}
}
}
}
else
{
lean_object* x_196; uint8_t x_197; 
x_196 = lean_ctor_get(x_110, 0);
lean_inc(x_196);
lean_dec(x_110);
x_197 = lean_unbox(x_196);
lean_dec(x_196);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_198 = lean_box(0);
x_199 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_199, 0, x_198);
return x_199;
}
else
{
lean_object* x_200; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_1);
x_200 = l_Lean_Meta_Grind_eqResolution(x_1, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
lean_dec_ref(x_200);
if (lean_obj_tag(x_201) == 1)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 x_203 = x_201;
} else {
 lean_dec_ref(x_201);
 x_203 = lean_box(0);
}
x_204 = lean_ctor_get(x_202, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_202, 1);
lean_inc(x_205);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_206 = x_202;
} else {
 lean_dec_ref(x_202);
 x_206 = lean_box(0);
}
x_231 = l_Lean_Meta_Grind_propagateForallPropDown___closed__1;
x_232 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_propagateForallPropUp_spec__0___redArg(x_231, x_8);
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
lean_dec_ref(x_232);
x_234 = lean_unbox(x_233);
lean_dec(x_233);
if (x_234 == 0)
{
lean_dec(x_206);
x_207 = x_2;
x_208 = x_3;
x_209 = x_4;
x_210 = x_5;
x_211 = x_6;
x_212 = x_7;
x_213 = x_8;
x_214 = x_9;
x_215 = lean_box(0);
goto block_230;
}
else
{
lean_object* x_235; 
x_235 = l_Lean_Meta_Grind_updateLastTag(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec_ref(x_235);
lean_inc_ref(x_1);
x_236 = l_Lean_MessageData_ofExpr(x_1);
x_237 = l_Lean_Meta_Grind_propagateForallPropDown___closed__3;
if (lean_is_scalar(x_206)) {
 x_238 = lean_alloc_ctor(7, 2, 0);
} else {
 x_238 = x_206;
 lean_ctor_set_tag(x_238, 7);
}
lean_ctor_set(x_238, 0, x_236);
lean_ctor_set(x_238, 1, x_237);
lean_inc(x_204);
x_239 = l_Lean_MessageData_ofExpr(x_204);
x_240 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_239);
x_241 = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateForallPropUp_spec__1___redArg(x_231, x_240, x_6, x_7, x_8, x_9);
lean_dec_ref(x_241);
x_207 = x_2;
x_208 = x_3;
x_209 = x_4;
x_210 = x_5;
x_211 = x_6;
x_212 = x_7;
x_213 = x_8;
x_214 = x_9;
x_215 = lean_box(0);
goto block_230;
}
else
{
lean_dec(x_206);
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_235;
}
}
block_230:
{
lean_object* x_216; 
lean_inc(x_214);
lean_inc_ref(x_213);
lean_inc(x_212);
lean_inc_ref(x_211);
lean_inc(x_210);
lean_inc_ref(x_209);
lean_inc(x_208);
lean_inc(x_207);
lean_inc_ref(x_1);
x_216 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_207, x_208, x_209, x_210, x_211, x_212, x_213, x_214);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; 
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
lean_dec_ref(x_216);
x_218 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_207);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
lean_dec_ref(x_218);
lean_inc_ref(x_1);
x_220 = l_Lean_Meta_mkOfEqTrueCore(x_1, x_217);
x_221 = l_Lean_Expr_app___override(x_205, x_220);
lean_inc_ref(x_1);
if (lean_is_scalar(x_203)) {
 x_222 = lean_alloc_ctor(4, 1, 0);
} else {
 x_222 = x_203;
 lean_ctor_set_tag(x_222, 4);
}
lean_ctor_set(x_222, 0, x_1);
lean_inc(x_214);
lean_inc_ref(x_213);
lean_inc(x_212);
lean_inc_ref(x_211);
x_223 = l_Lean_Meta_Grind_addNewRawFact(x_221, x_204, x_219, x_222, x_207, x_208, x_209, x_210, x_211, x_212, x_213, x_214);
if (lean_obj_tag(x_223) == 0)
{
lean_dec_ref(x_223);
x_62 = x_207;
x_63 = x_208;
x_64 = x_209;
x_65 = x_210;
x_66 = x_211;
x_67 = x_212;
x_68 = x_213;
x_69 = x_214;
x_70 = lean_box(0);
goto block_106;
}
else
{
lean_dec(x_214);
lean_dec_ref(x_213);
lean_dec(x_212);
lean_dec_ref(x_211);
lean_dec(x_210);
lean_dec_ref(x_209);
lean_dec(x_208);
lean_dec(x_207);
lean_dec_ref(x_1);
return x_223;
}
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec(x_217);
lean_dec(x_214);
lean_dec_ref(x_213);
lean_dec(x_212);
lean_dec_ref(x_211);
lean_dec(x_210);
lean_dec_ref(x_209);
lean_dec(x_208);
lean_dec(x_207);
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec_ref(x_1);
x_224 = lean_ctor_get(x_218, 0);
lean_inc(x_224);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 x_225 = x_218;
} else {
 lean_dec_ref(x_218);
 x_225 = lean_box(0);
}
if (lean_is_scalar(x_225)) {
 x_226 = lean_alloc_ctor(1, 1, 0);
} else {
 x_226 = x_225;
}
lean_ctor_set(x_226, 0, x_224);
return x_226;
}
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec(x_214);
lean_dec_ref(x_213);
lean_dec(x_212);
lean_dec_ref(x_211);
lean_dec(x_210);
lean_dec_ref(x_209);
lean_dec(x_208);
lean_dec(x_207);
lean_dec(x_205);
lean_dec(x_204);
lean_dec(x_203);
lean_dec_ref(x_1);
x_227 = lean_ctor_get(x_216, 0);
lean_inc(x_227);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 x_228 = x_216;
} else {
 lean_dec_ref(x_216);
 x_228 = lean_box(0);
}
if (lean_is_scalar(x_228)) {
 x_229 = lean_alloc_ctor(1, 1, 0);
} else {
 x_229 = x_228;
}
lean_ctor_set(x_229, 0, x_227);
return x_229;
}
}
}
else
{
lean_dec(x_201);
x_62 = x_2;
x_63 = x_3;
x_64 = x_4;
x_65 = x_5;
x_66 = x_6;
x_67 = x_7;
x_68 = x_8;
x_69 = x_9;
x_70 = lean_box(0);
goto block_106;
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_242 = lean_ctor_get(x_200, 0);
lean_inc(x_242);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 x_243 = x_200;
} else {
 lean_dec_ref(x_200);
 x_243 = lean_box(0);
}
if (lean_is_scalar(x_243)) {
 x_244 = lean_alloc_ctor(1, 1, 0);
} else {
 x_244 = x_243;
}
lean_ctor_set(x_244, 0, x_242);
return x_244;
}
}
}
}
else
{
uint8_t x_245; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_245 = !lean_is_exclusive(x_110);
if (x_245 == 0)
{
return x_110;
}
else
{
lean_object* x_246; lean_object* x_247; 
x_246 = lean_ctor_get(x_110, 0);
lean_inc(x_246);
lean_dec(x_110);
x_247 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_247, 0, x_246);
return x_247;
}
}
}
else
{
lean_object* x_248; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_12);
x_248 = l_Lean_Meta_isProp(x_12, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; uint8_t x_279; 
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
lean_dec_ref(x_248);
x_279 = l_Lean_Expr_hasLooseBVars(x_13);
if (x_279 == 0)
{
uint8_t x_280; 
x_280 = lean_unbox(x_249);
lean_dec(x_249);
if (x_280 == 0)
{
goto block_278;
}
else
{
if (x_279 == 0)
{
lean_object* x_281; 
lean_inc_ref(x_13);
lean_inc_ref(x_12);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_4);
lean_inc(x_2);
x_281 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
lean_dec_ref(x_281);
x_283 = l_Lean_Meta_Grind_propagateForallPropDown___closed__10;
lean_inc(x_282);
lean_inc_ref(x_13);
lean_inc_ref(x_12);
x_284 = l_Lean_mkApp3(x_283, x_12, x_13, x_282);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_12);
x_285 = l_Lean_Meta_Grind_pushEqTrue___redArg(x_12, x_284, x_2, x_4, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec_ref(x_285);
x_286 = l_Lean_Meta_Grind_propagateForallPropDown___closed__13;
lean_inc_ref(x_13);
x_287 = l_Lean_mkApp3(x_286, x_12, x_13, x_282);
x_288 = l_Lean_Meta_Grind_pushEqFalse___redArg(x_13, x_287, x_2, x_4, x_6, x_7, x_8, x_9);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_288;
}
else
{
lean_dec(x_282);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_285;
}
}
else
{
uint8_t x_289; 
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_4);
lean_dec(x_2);
x_289 = !lean_is_exclusive(x_281);
if (x_289 == 0)
{
return x_281;
}
else
{
lean_object* x_290; lean_object* x_291; 
x_290 = lean_ctor_get(x_281, 0);
lean_inc(x_290);
lean_dec(x_281);
x_291 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_291, 0, x_290);
return x_291;
}
}
}
else
{
goto block_278;
}
}
}
else
{
lean_dec(x_249);
goto block_278;
}
block_278:
{
lean_object* x_250; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_12);
x_250 = l_Lean_Meta_getLevel(x_12, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_250) == 0)
{
lean_object* x_251; lean_object* x_252; 
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
lean_dec_ref(x_250);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_252 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; 
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
lean_dec_ref(x_252);
x_254 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
lean_dec_ref(x_254);
x_256 = l_Lean_Meta_Grind_propagateForallPropDown___closed__5;
x_257 = lean_box(0);
x_258 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_258, 0, x_251);
lean_ctor_set(x_258, 1, x_257);
lean_inc_ref(x_258);
x_259 = l_Lean_mkConst(x_256, x_258);
lean_inc_ref(x_13);
x_260 = l_Lean_mkNot(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
x_261 = l_Lean_mkLambda(x_11, x_14, x_12, x_260);
lean_inc_ref(x_12);
x_262 = l_Lean_mkAppB(x_259, x_12, x_261);
x_263 = l_Lean_Meta_Grind_propagateForallPropDown___closed__7;
x_264 = l_Lean_mkConst(x_263, x_258);
lean_inc_ref(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
x_265 = l_Lean_mkLambda(x_11, x_14, x_12, x_13);
lean_inc_ref(x_12);
x_266 = l_Lean_mkApp3(x_264, x_12, x_265, x_253);
x_267 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_267, 0, x_1);
x_268 = l_Lean_Meta_Grind_addNewRawFact(x_266, x_262, x_255, x_267, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_268;
}
else
{
uint8_t x_269; 
lean_dec(x_253);
lean_dec(x_251);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_269 = !lean_is_exclusive(x_254);
if (x_269 == 0)
{
return x_254;
}
else
{
lean_object* x_270; lean_object* x_271; 
x_270 = lean_ctor_get(x_254, 0);
lean_inc(x_270);
lean_dec(x_254);
x_271 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_271, 0, x_270);
return x_271;
}
}
}
else
{
uint8_t x_272; 
lean_dec(x_251);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_272 = !lean_is_exclusive(x_252);
if (x_272 == 0)
{
return x_252;
}
else
{
lean_object* x_273; lean_object* x_274; 
x_273 = lean_ctor_get(x_252, 0);
lean_inc(x_273);
lean_dec(x_252);
x_274 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_274, 0, x_273);
return x_274;
}
}
}
else
{
uint8_t x_275; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_275 = !lean_is_exclusive(x_250);
if (x_275 == 0)
{
return x_250;
}
else
{
lean_object* x_276; lean_object* x_277; 
x_276 = lean_ctor_get(x_250, 0);
lean_inc(x_276);
lean_dec(x_250);
x_277 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_277, 0, x_276);
return x_277;
}
}
}
}
else
{
uint8_t x_292; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_292 = !lean_is_exclusive(x_248);
if (x_292 == 0)
{
return x_248;
}
else
{
lean_object* x_293; lean_object* x_294; 
x_293 = lean_ctor_get(x_248, 0);
lean_inc(x_293);
lean_dec(x_248);
x_294 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_294, 0, x_293);
return x_294;
}
}
}
}
else
{
uint8_t x_295; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_295 = !lean_is_exclusive(x_107);
if (x_295 == 0)
{
return x_107;
}
else
{
lean_object* x_296; lean_object* x_297; 
x_296 = lean_ctor_get(x_107, 0);
lean_inc(x_296);
lean_dec(x_107);
x_297 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_297, 0, x_296);
return x_297;
}
}
block_61:
{
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_1);
x_27 = lean_box(0);
lean_ctor_set(x_23, 0, x_27);
return x_23;
}
else
{
lean_object* x_28; 
lean_free_object(x_23);
lean_inc(x_21);
lean_inc_ref(x_18);
lean_inc(x_20);
lean_inc_ref(x_22);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_19);
lean_inc(x_17);
x_28 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_17, x_19, x_15, x_16, x_22, x_20, x_18, x_21);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
lean_inc(x_21);
lean_inc_ref(x_18);
lean_inc(x_20);
lean_inc_ref(x_22);
lean_inc_ref(x_15);
lean_inc(x_17);
lean_inc_ref(x_13);
x_30 = l_Lean_Meta_Grind_mkEqFalseProof(x_13, x_17, x_19, x_15, x_16, x_22, x_20, x_18, x_21);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
x_32 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4;
lean_inc_ref(x_12);
x_33 = l_Lean_mkApp4(x_32, x_12, x_13, x_29, x_31);
x_34 = l_Lean_Meta_Grind_pushEqFalse___redArg(x_12, x_33, x_17, x_15, x_22, x_20, x_18, x_21);
lean_dec_ref(x_15);
lean_dec(x_17);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_29);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
lean_dec(x_30);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
x_38 = !lean_is_exclusive(x_28);
if (x_38 == 0)
{
return x_28;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_28, 0);
lean_inc(x_39);
lean_dec(x_28);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
}
else
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_23, 0);
lean_inc(x_41);
lean_dec(x_23);
x_42 = lean_unbox(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_1);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
else
{
lean_object* x_45; 
lean_inc(x_21);
lean_inc_ref(x_18);
lean_inc(x_20);
lean_inc_ref(x_22);
lean_inc(x_16);
lean_inc_ref(x_15);
lean_inc(x_19);
lean_inc(x_17);
x_45 = l_Lean_Meta_Grind_mkEqTrueProof(x_1, x_17, x_19, x_15, x_16, x_22, x_20, x_18, x_21);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
lean_inc(x_21);
lean_inc_ref(x_18);
lean_inc(x_20);
lean_inc_ref(x_22);
lean_inc_ref(x_15);
lean_inc(x_17);
lean_inc_ref(x_13);
x_47 = l_Lean_Meta_Grind_mkEqFalseProof(x_13, x_17, x_19, x_15, x_16, x_22, x_20, x_18, x_21);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
x_49 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_propagateForallPropUp_propagateImpliesUp___closed__4;
lean_inc_ref(x_12);
x_50 = l_Lean_mkApp4(x_49, x_12, x_13, x_46, x_48);
x_51 = l_Lean_Meta_Grind_pushEqFalse___redArg(x_12, x_50, x_17, x_15, x_22, x_20, x_18, x_21);
lean_dec_ref(x_15);
lean_dec(x_17);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_46);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
x_52 = lean_ctor_get(x_47, 0);
lean_inc(x_52);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 x_53 = x_47;
} else {
 lean_dec_ref(x_47);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 1, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_52);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
x_55 = lean_ctor_get(x_45, 0);
lean_inc(x_55);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 x_56 = x_45;
} else {
 lean_dec_ref(x_45);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 1, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_55);
return x_57;
}
}
}
}
else
{
uint8_t x_58; 
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_1);
x_58 = !lean_is_exclusive(x_23);
if (x_58 == 0)
{
return x_23;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_23, 0);
lean_inc(x_59);
lean_dec(x_23);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
}
}
block_106:
{
uint8_t x_71; 
x_71 = l_Lean_Expr_hasLooseBVars(x_13);
if (x_71 == 0)
{
lean_object* x_72; 
lean_inc_ref(x_13);
lean_inc_ref(x_12);
x_72 = l_Lean_Meta_Grind_alreadyInternalized___redArg(x_13, x_62);
if (lean_obj_tag(x_72) == 0)
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_ctor_get(x_72, 0);
x_75 = lean_unbox(x_74);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; 
lean_dec(x_69);
lean_dec_ref(x_68);
lean_dec(x_67);
lean_dec_ref(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_1);
x_76 = lean_box(0);
lean_ctor_set(x_72, 0, x_76);
return x_72;
}
else
{
lean_object* x_77; 
lean_free_object(x_72);
lean_inc_ref(x_13);
x_77 = l_Lean_Meta_Grind_isEqFalse___redArg(x_13, x_62, x_64, x_68, x_69);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_unbox(x_78);
lean_dec(x_78);
if (x_79 == 0)
{
x_15 = x_64;
x_16 = x_65;
x_17 = x_62;
x_18 = x_68;
x_19 = x_63;
x_20 = x_67;
x_21 = x_69;
x_22 = x_66;
x_23 = x_77;
goto block_61;
}
else
{
lean_object* x_80; 
lean_dec_ref(x_77);
lean_inc(x_69);
lean_inc_ref(x_68);
lean_inc(x_67);
lean_inc_ref(x_66);
lean_inc_ref(x_12);
x_80 = l_Lean_Meta_isProp(x_12, x_66, x_67, x_68, x_69);
x_15 = x_64;
x_16 = x_65;
x_17 = x_62;
x_18 = x_68;
x_19 = x_63;
x_20 = x_67;
x_21 = x_69;
x_22 = x_66;
x_23 = x_80;
goto block_61;
}
}
else
{
x_15 = x_64;
x_16 = x_65;
x_17 = x_62;
x_18 = x_68;
x_19 = x_63;
x_20 = x_67;
x_21 = x_69;
x_22 = x_66;
x_23 = x_77;
goto block_61;
}
}
}
else
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_ctor_get(x_72, 0);
lean_inc(x_81);
lean_dec(x_72);
x_82 = lean_unbox(x_81);
lean_dec(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
lean_dec(x_69);
lean_dec_ref(x_68);
lean_dec(x_67);
lean_dec_ref(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_1);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
else
{
lean_object* x_85; 
lean_inc_ref(x_13);
x_85 = l_Lean_Meta_Grind_isEqFalse___redArg(x_13, x_62, x_64, x_68, x_69);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_unbox(x_86);
lean_dec(x_86);
if (x_87 == 0)
{
x_15 = x_64;
x_16 = x_65;
x_17 = x_62;
x_18 = x_68;
x_19 = x_63;
x_20 = x_67;
x_21 = x_69;
x_22 = x_66;
x_23 = x_85;
goto block_61;
}
else
{
lean_object* x_88; 
lean_dec_ref(x_85);
lean_inc(x_69);
lean_inc_ref(x_68);
lean_inc(x_67);
lean_inc_ref(x_66);
lean_inc_ref(x_12);
x_88 = l_Lean_Meta_isProp(x_12, x_66, x_67, x_68, x_69);
x_15 = x_64;
x_16 = x_65;
x_17 = x_62;
x_18 = x_68;
x_19 = x_63;
x_20 = x_67;
x_21 = x_69;
x_22 = x_66;
x_23 = x_88;
goto block_61;
}
}
else
{
x_15 = x_64;
x_16 = x_65;
x_17 = x_62;
x_18 = x_68;
x_19 = x_63;
x_20 = x_67;
x_21 = x_69;
x_22 = x_66;
x_23 = x_85;
goto block_61;
}
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_69);
lean_dec_ref(x_68);
lean_dec(x_67);
lean_dec_ref(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_1);
x_89 = !lean_is_exclusive(x_72);
if (x_89 == 0)
{
return x_72;
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_72, 0);
lean_inc(x_90);
lean_dec(x_72);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
}
}
else
{
lean_object* x_92; 
lean_inc(x_69);
lean_inc_ref(x_68);
lean_inc(x_67);
lean_inc_ref(x_66);
lean_inc_ref(x_12);
x_92 = l_Lean_Meta_isProp(x_12, x_66, x_67, x_68, x_69);
if (lean_obj_tag(x_92) == 0)
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_ctor_get(x_92, 0);
x_95 = lean_unbox(x_94);
lean_dec(x_94);
if (x_95 == 0)
{
lean_object* x_96; 
lean_free_object(x_92);
x_96 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems(x_1, x_62, x_63, x_64, x_65, x_66, x_67, x_68, x_69);
return x_96;
}
else
{
lean_object* x_97; 
lean_dec(x_69);
lean_dec_ref(x_68);
lean_dec(x_67);
lean_dec_ref(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec_ref(x_1);
x_97 = lean_box(0);
lean_ctor_set(x_92, 0, x_97);
return x_92;
}
}
else
{
lean_object* x_98; uint8_t x_99; 
x_98 = lean_ctor_get(x_92, 0);
lean_inc(x_98);
lean_dec(x_92);
x_99 = lean_unbox(x_98);
lean_dec(x_98);
if (x_99 == 0)
{
lean_object* x_100; 
x_100 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_addLocalEMatchTheorems(x_1, x_62, x_63, x_64, x_65, x_66, x_67, x_68, x_69);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_69);
lean_dec_ref(x_68);
lean_dec(x_67);
lean_dec_ref(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec_ref(x_1);
x_101 = lean_box(0);
x_102 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_102, 0, x_101);
return x_102;
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_69);
lean_dec_ref(x_68);
lean_dec(x_67);
lean_dec_ref(x_66);
lean_dec(x_65);
lean_dec_ref(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec_ref(x_1);
x_103 = !lean_is_exclusive(x_92);
if (x_103 == 0)
{
return x_92;
}
else
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_92, 0);
lean_inc(x_104);
lean_dec(x_92);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_104);
return x_105;
}
}
}
}
}
else
{
lean_object* x_298; lean_object* x_299; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_298 = lean_box(0);
x_299 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_299, 0, x_298);
return x_299;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateForallPropDown___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_propagateForallPropDown(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateExistsDown(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_15; 
lean_inc_ref(x_1);
x_15 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_4, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_19 = lean_box(0);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
else
{
lean_object* x_20; uint8_t x_21; 
lean_free_object(x_15);
lean_inc_ref(x_1);
x_20 = l_Lean_Expr_cleanupAnnotations(x_1);
x_21 = l_Lean_Expr_isApp(x_20);
if (x_21 == 0)
{
lean_dec_ref(x_20);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_22; uint8_t x_23; 
lean_inc_ref(x_20);
x_22 = l_Lean_Expr_appFnCleanup___redArg(x_20);
x_23 = l_Lean_Expr_isApp(x_22);
if (x_23 == 0)
{
lean_dec_ref(x_22);
lean_dec_ref(x_20);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_inc_ref(x_22);
x_24 = l_Lean_Expr_appFnCleanup___redArg(x_22);
x_25 = l_Lean_Meta_Grind_propagateForallPropDown___closed__5;
x_26 = l_Lean_Expr_isConstOf(x_24, x_25);
if (x_26 == 0)
{
lean_dec_ref(x_24);
lean_dec_ref(x_22);
lean_dec_ref(x_20);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_27; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_27 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
x_29 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec_ref(x_29);
x_31 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_31);
lean_dec_ref(x_20);
x_32 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_32);
lean_dec_ref(x_22);
x_33 = l_Lean_Expr_constLevels_x21(x_24);
lean_dec_ref(x_24);
x_34 = l_Lean_Meta_Grind_propagateExistsDown___closed__2;
x_35 = l_Lean_Meta_Grind_propagateExistsDown___closed__3;
lean_inc_ref(x_31);
x_36 = l_Lean_Expr_app___override(x_31, x_35);
x_37 = l_Lean_Expr_headBeta(x_36);
x_38 = l_Lean_Expr_app___override(x_34, x_37);
x_39 = l_Lean_Meta_Grind_propagateExistsDown___closed__5;
x_40 = 0;
lean_inc_ref(x_32);
x_41 = l_Lean_mkForall(x_39, x_40, x_32, x_38);
x_42 = l_Lean_Meta_Grind_propagateExistsDown___closed__7;
x_43 = l_Lean_mkConst(x_42, x_33);
lean_inc_ref(x_1);
x_44 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_28);
x_45 = l_Lean_mkApp3(x_43, x_32, x_31, x_44);
x_46 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_46, 0, x_1);
x_47 = l_Lean_Meta_Grind_addNewRawFact(x_45, x_41, x_30, x_46, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_47;
}
else
{
uint8_t x_48; 
lean_dec(x_28);
lean_dec_ref(x_24);
lean_dec_ref(x_22);
lean_dec_ref(x_20);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_48 = !lean_is_exclusive(x_29);
if (x_48 == 0)
{
return x_29;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_29, 0);
lean_inc(x_49);
lean_dec(x_29);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec_ref(x_24);
lean_dec_ref(x_22);
lean_dec_ref(x_20);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_51 = !lean_is_exclusive(x_27);
if (x_51 == 0)
{
return x_27;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_27, 0);
lean_inc(x_52);
lean_dec(x_27);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
}
}
}
}
}
else
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_15, 0);
lean_inc(x_54);
lean_dec(x_15);
x_55 = lean_unbox(x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
else
{
lean_object* x_58; uint8_t x_59; 
lean_inc_ref(x_1);
x_58 = l_Lean_Expr_cleanupAnnotations(x_1);
x_59 = l_Lean_Expr_isApp(x_58);
if (x_59 == 0)
{
lean_dec_ref(x_58);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_60; uint8_t x_61; 
lean_inc_ref(x_58);
x_60 = l_Lean_Expr_appFnCleanup___redArg(x_58);
x_61 = l_Lean_Expr_isApp(x_60);
if (x_61 == 0)
{
lean_dec_ref(x_60);
lean_dec_ref(x_58);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
lean_inc_ref(x_60);
x_62 = l_Lean_Expr_appFnCleanup___redArg(x_60);
x_63 = l_Lean_Meta_Grind_propagateForallPropDown___closed__5;
x_64 = l_Lean_Expr_isConstOf(x_62, x_63);
if (x_64 == 0)
{
lean_dec_ref(x_62);
lean_dec_ref(x_60);
lean_dec_ref(x_58);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_65; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_65 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec_ref(x_65);
x_67 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec_ref(x_67);
x_69 = lean_ctor_get(x_58, 1);
lean_inc_ref(x_69);
lean_dec_ref(x_58);
x_70 = lean_ctor_get(x_60, 1);
lean_inc_ref(x_70);
lean_dec_ref(x_60);
x_71 = l_Lean_Expr_constLevels_x21(x_62);
lean_dec_ref(x_62);
x_72 = l_Lean_Meta_Grind_propagateExistsDown___closed__2;
x_73 = l_Lean_Meta_Grind_propagateExistsDown___closed__3;
lean_inc_ref(x_69);
x_74 = l_Lean_Expr_app___override(x_69, x_73);
x_75 = l_Lean_Expr_headBeta(x_74);
x_76 = l_Lean_Expr_app___override(x_72, x_75);
x_77 = l_Lean_Meta_Grind_propagateExistsDown___closed__5;
x_78 = 0;
lean_inc_ref(x_70);
x_79 = l_Lean_mkForall(x_77, x_78, x_70, x_76);
x_80 = l_Lean_Meta_Grind_propagateExistsDown___closed__7;
x_81 = l_Lean_mkConst(x_80, x_71);
lean_inc_ref(x_1);
x_82 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_66);
x_83 = l_Lean_mkApp3(x_81, x_70, x_69, x_82);
x_84 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_84, 0, x_1);
x_85 = l_Lean_Meta_Grind_addNewRawFact(x_83, x_79, x_68, x_84, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_66);
lean_dec_ref(x_62);
lean_dec_ref(x_60);
lean_dec_ref(x_58);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_86 = lean_ctor_get(x_67, 0);
lean_inc(x_86);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 x_87 = x_67;
} else {
 lean_dec_ref(x_67);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 1, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_86);
return x_88;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec_ref(x_62);
lean_dec_ref(x_60);
lean_dec_ref(x_58);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_89 = lean_ctor_get(x_65, 0);
lean_inc(x_89);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 x_90 = x_65;
} else {
 lean_dec_ref(x_65);
 x_90 = lean_box(0);
}
if (lean_is_scalar(x_90)) {
 x_91 = lean_alloc_ctor(1, 1, 0);
} else {
 x_91 = x_90;
}
lean_ctor_set(x_91, 0, x_89);
return x_91;
}
}
}
}
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_92 = !lean_is_exclusive(x_15);
if (x_92 == 0)
{
return x_15;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_15, 0);
lean_inc(x_93);
lean_dec(x_15);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
return x_94;
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateExistsDown___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_propagateExistsDown(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateExistsDown___regBuiltin_Lean_Meta_Grind_propagateExistsDown_declare__1_00___x40_Lean_Meta_Tactic_Grind_ForallProp_115310127____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_Grind_propagateForallPropDown___closed__5;
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_propagateExistsDown___boxed), 10, 0);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_5, x_2, x_3, x_4, x_6, x_7, x_8, x_9, lean_box(0));
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
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
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; uint8_t x_426; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_15);
x_16 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_16);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec_ref(x_1);
x_426 = l_Lean_Expr_hasLooseBVars(x_16);
if (x_426 == 0)
{
lean_object* x_427; 
lean_inc_ref(x_15);
x_427 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_15, x_6);
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_428; uint8_t x_429; lean_object* x_430; lean_object* x_453; lean_object* x_454; uint8_t x_455; 
x_428 = lean_ctor_get(x_427, 0);
lean_inc(x_428);
lean_dec_ref(x_427);
x_429 = 1;
x_453 = l_Lean_Expr_cleanupAnnotations(x_428);
x_454 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__3;
x_455 = l_Lean_Expr_isConstOf(x_453, x_454);
if (x_455 == 0)
{
lean_object* x_456; uint8_t x_457; 
x_456 = l_Lean_Meta_Grind_simpForall___closed__12;
x_457 = l_Lean_Expr_isConstOf(x_453, x_456);
lean_dec_ref(x_453);
if (x_457 == 0)
{
if (lean_obj_tag(x_15) == 7)
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; uint8_t x_461; uint8_t x_462; lean_object* x_463; uint8_t x_503; 
x_458 = lean_ctor_get(x_15, 0);
x_459 = lean_ctor_get(x_15, 1);
x_460 = lean_ctor_get(x_15, 2);
x_461 = lean_ctor_get_uint8(x_15, sizeof(void*)*3 + 8);
x_503 = l_Lean_Expr_hasLooseBVars(x_460);
if (x_503 == 0)
{
x_462 = x_503;
x_463 = lean_box(0);
goto block_502;
}
else
{
lean_object* x_504; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_15);
x_504 = l_Lean_Meta_isProp(x_15, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_504) == 0)
{
lean_object* x_505; uint8_t x_506; 
x_505 = lean_ctor_get(x_504, 0);
lean_inc(x_505);
lean_dec_ref(x_504);
x_506 = lean_unbox(x_505);
lean_dec(x_505);
x_462 = x_506;
x_463 = lean_box(0);
goto block_502;
}
else
{
uint8_t x_507; 
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
x_507 = !lean_is_exclusive(x_504);
if (x_507 == 0)
{
return x_504;
}
else
{
lean_object* x_508; lean_object* x_509; 
x_508 = lean_ctor_get(x_504, 0);
lean_inc(x_508);
lean_dec(x_504);
x_509 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_509, 0, x_508);
return x_509;
}
}
}
block_502:
{
if (x_462 == 0)
{
x_413 = x_2;
x_414 = x_3;
x_415 = x_4;
x_416 = x_5;
x_417 = x_6;
x_418 = x_7;
x_419 = x_8;
x_420 = lean_box(0);
goto block_425;
}
else
{
lean_object* x_464; 
lean_inc_ref(x_460);
lean_inc_ref(x_459);
lean_inc(x_458);
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_inc_ref(x_459);
x_464 = l_Lean_Meta_getLevel(x_459, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_464) == 0)
{
uint8_t x_465; 
x_465 = !lean_is_exclusive(x_464);
if (x_465 == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_466 = lean_ctor_get(x_464, 0);
lean_inc_ref(x_460);
lean_inc_ref(x_459);
lean_inc(x_458);
x_467 = l_Lean_mkLambda(x_458, x_461, x_459, x_460);
x_468 = l_Lean_Meta_Grind_propagateForallPropDown___closed__5;
x_469 = lean_box(0);
x_470 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_470, 0, x_466);
lean_ctor_set(x_470, 1, x_469);
lean_inc_ref(x_470);
x_471 = l_Lean_mkConst(x_468, x_470);
x_472 = l_Lean_mkNot(x_460);
lean_inc_ref(x_459);
x_473 = l_Lean_mkLambda(x_458, x_461, x_459, x_472);
lean_inc_ref(x_459);
x_474 = l_Lean_mkAppB(x_471, x_459, x_473);
lean_inc_ref(x_16);
x_475 = l_Lean_mkOr(x_474, x_16);
x_476 = l_Lean_Meta_Grind_simpForall___closed__18;
x_477 = l_Lean_mkConst(x_476, x_470);
x_478 = l_Lean_mkApp3(x_477, x_459, x_467, x_16);
x_479 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_479, 0, x_478);
x_480 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_480, 0, x_475);
lean_ctor_set(x_480, 1, x_479);
lean_ctor_set_uint8(x_480, sizeof(void*)*2, x_429);
x_481 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_481, 0, x_480);
lean_ctor_set(x_464, 0, x_481);
return x_464;
}
else
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; 
x_482 = lean_ctor_get(x_464, 0);
lean_inc(x_482);
lean_dec(x_464);
lean_inc_ref(x_460);
lean_inc_ref(x_459);
lean_inc(x_458);
x_483 = l_Lean_mkLambda(x_458, x_461, x_459, x_460);
x_484 = l_Lean_Meta_Grind_propagateForallPropDown___closed__5;
x_485 = lean_box(0);
x_486 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_486, 0, x_482);
lean_ctor_set(x_486, 1, x_485);
lean_inc_ref(x_486);
x_487 = l_Lean_mkConst(x_484, x_486);
x_488 = l_Lean_mkNot(x_460);
lean_inc_ref(x_459);
x_489 = l_Lean_mkLambda(x_458, x_461, x_459, x_488);
lean_inc_ref(x_459);
x_490 = l_Lean_mkAppB(x_487, x_459, x_489);
lean_inc_ref(x_16);
x_491 = l_Lean_mkOr(x_490, x_16);
x_492 = l_Lean_Meta_Grind_simpForall___closed__18;
x_493 = l_Lean_mkConst(x_492, x_486);
x_494 = l_Lean_mkApp3(x_493, x_459, x_483, x_16);
x_495 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_495, 0, x_494);
x_496 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_496, 0, x_491);
lean_ctor_set(x_496, 1, x_495);
lean_ctor_set_uint8(x_496, sizeof(void*)*2, x_429);
x_497 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_497, 0, x_496);
x_498 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_498, 0, x_497);
return x_498;
}
}
else
{
uint8_t x_499; 
lean_dec_ref(x_460);
lean_dec_ref(x_459);
lean_dec(x_458);
lean_dec_ref(x_16);
x_499 = !lean_is_exclusive(x_464);
if (x_499 == 0)
{
return x_464;
}
else
{
lean_object* x_500; lean_object* x_501; 
x_500 = lean_ctor_get(x_464, 0);
lean_inc(x_500);
lean_dec(x_464);
x_501 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_501, 0, x_500);
return x_501;
}
}
}
}
}
else
{
lean_object* x_510; 
lean_inc_ref(x_16);
x_510 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_16, x_6);
if (lean_obj_tag(x_510) == 0)
{
lean_object* x_511; lean_object* x_512; uint8_t x_513; 
x_511 = lean_ctor_get(x_510, 0);
lean_inc(x_511);
lean_dec_ref(x_510);
x_512 = l_Lean_Expr_cleanupAnnotations(x_511);
x_513 = l_Lean_Expr_isConstOf(x_512, x_454);
if (x_513 == 0)
{
uint8_t x_514; 
x_514 = l_Lean_Expr_isConstOf(x_512, x_456);
lean_dec_ref(x_512);
if (x_514 == 0)
{
lean_object* x_515; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_15);
x_515 = l_Lean_Meta_isProp(x_15, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_515) == 0)
{
lean_object* x_516; uint8_t x_517; 
x_516 = lean_ctor_get(x_515, 0);
lean_inc(x_516);
x_517 = lean_unbox(x_516);
lean_dec(x_516);
if (x_517 == 0)
{
x_430 = x_515;
goto block_452;
}
else
{
lean_object* x_518; 
lean_dec_ref(x_515);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_16);
lean_inc_ref(x_15);
x_518 = l_Lean_Meta_isExprDefEq(x_15, x_16, x_5, x_6, x_7, x_8);
x_430 = x_518;
goto block_452;
}
}
else
{
x_430 = x_515;
goto block_452;
}
}
else
{
lean_object* x_519; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_15);
x_519 = l_Lean_Meta_isProp(x_15, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_519) == 0)
{
uint8_t x_520; 
x_520 = !lean_is_exclusive(x_519);
if (x_520 == 0)
{
lean_object* x_521; uint8_t x_522; 
x_521 = lean_ctor_get(x_519, 0);
x_522 = lean_unbox(x_521);
lean_dec(x_521);
if (x_522 == 0)
{
lean_free_object(x_519);
x_413 = x_2;
x_414 = x_3;
x_415 = x_4;
x_416 = x_5;
x_417 = x_6;
x_418 = x_7;
x_419 = x_8;
x_420 = lean_box(0);
goto block_425;
}
else
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; 
lean_dec_ref(x_16);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_523 = l_Lean_Meta_Grind_simpForall___closed__13;
x_524 = l_Lean_Meta_Grind_simpForall___closed__21;
x_525 = l_Lean_Expr_app___override(x_524, x_15);
x_526 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_526, 0, x_525);
x_527 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_527, 0, x_523);
lean_ctor_set(x_527, 1, x_526);
lean_ctor_set_uint8(x_527, sizeof(void*)*2, x_429);
x_528 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_528, 0, x_527);
lean_ctor_set(x_519, 0, x_528);
return x_519;
}
}
else
{
lean_object* x_529; uint8_t x_530; 
x_529 = lean_ctor_get(x_519, 0);
lean_inc(x_529);
lean_dec(x_519);
x_530 = lean_unbox(x_529);
lean_dec(x_529);
if (x_530 == 0)
{
x_413 = x_2;
x_414 = x_3;
x_415 = x_4;
x_416 = x_5;
x_417 = x_6;
x_418 = x_7;
x_419 = x_8;
x_420 = lean_box(0);
goto block_425;
}
else
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; 
lean_dec_ref(x_16);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_531 = l_Lean_Meta_Grind_simpForall___closed__13;
x_532 = l_Lean_Meta_Grind_simpForall___closed__21;
x_533 = l_Lean_Expr_app___override(x_532, x_15);
x_534 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_534, 0, x_533);
x_535 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_535, 0, x_531);
lean_ctor_set(x_535, 1, x_534);
lean_ctor_set_uint8(x_535, sizeof(void*)*2, x_429);
x_536 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_536, 0, x_535);
x_537 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_537, 0, x_536);
return x_537;
}
}
}
else
{
uint8_t x_538; 
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
x_538 = !lean_is_exclusive(x_519);
if (x_538 == 0)
{
return x_519;
}
else
{
lean_object* x_539; lean_object* x_540; 
x_539 = lean_ctor_get(x_519, 0);
lean_inc(x_539);
lean_dec(x_519);
x_540 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_540, 0, x_539);
return x_540;
}
}
}
}
else
{
lean_object* x_541; 
lean_dec_ref(x_512);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_15);
x_541 = l_Lean_Meta_isProp(x_15, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_541) == 0)
{
uint8_t x_542; 
x_542 = !lean_is_exclusive(x_541);
if (x_542 == 0)
{
lean_object* x_543; uint8_t x_544; 
x_543 = lean_ctor_get(x_541, 0);
x_544 = lean_unbox(x_543);
lean_dec(x_543);
if (x_544 == 0)
{
lean_free_object(x_541);
x_413 = x_2;
x_414 = x_3;
x_415 = x_4;
x_416 = x_5;
x_417 = x_6;
x_418 = x_7;
x_419 = x_8;
x_420 = lean_box(0);
goto block_425;
}
else
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; 
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
x_545 = l_Lean_mkNot(x_15);
x_546 = l_Lean_Meta_Grind_simpForall___closed__24;
x_547 = l_Lean_Expr_app___override(x_546, x_15);
x_548 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_548, 0, x_547);
x_549 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_549, 0, x_545);
lean_ctor_set(x_549, 1, x_548);
lean_ctor_set_uint8(x_549, sizeof(void*)*2, x_429);
x_550 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_550, 0, x_549);
lean_ctor_set(x_541, 0, x_550);
return x_541;
}
}
else
{
lean_object* x_551; uint8_t x_552; 
x_551 = lean_ctor_get(x_541, 0);
lean_inc(x_551);
lean_dec(x_541);
x_552 = lean_unbox(x_551);
lean_dec(x_551);
if (x_552 == 0)
{
x_413 = x_2;
x_414 = x_3;
x_415 = x_4;
x_416 = x_5;
x_417 = x_6;
x_418 = x_7;
x_419 = x_8;
x_420 = lean_box(0);
goto block_425;
}
else
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; 
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
x_553 = l_Lean_mkNot(x_15);
x_554 = l_Lean_Meta_Grind_simpForall___closed__24;
x_555 = l_Lean_Expr_app___override(x_554, x_15);
x_556 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_556, 0, x_555);
x_557 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_557, 0, x_553);
lean_ctor_set(x_557, 1, x_556);
lean_ctor_set_uint8(x_557, sizeof(void*)*2, x_429);
x_558 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_558, 0, x_557);
x_559 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_559, 0, x_558);
return x_559;
}
}
}
else
{
uint8_t x_560; 
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
x_560 = !lean_is_exclusive(x_541);
if (x_560 == 0)
{
return x_541;
}
else
{
lean_object* x_561; lean_object* x_562; 
x_561 = lean_ctor_get(x_541, 0);
lean_inc(x_561);
lean_dec(x_541);
x_562 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_562, 0, x_561);
return x_562;
}
}
}
}
else
{
uint8_t x_563; 
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
x_563 = !lean_is_exclusive(x_510);
if (x_563 == 0)
{
return x_510;
}
else
{
lean_object* x_564; lean_object* x_565; 
x_564 = lean_ctor_get(x_510, 0);
lean_inc(x_564);
lean_dec(x_510);
x_565 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_565, 0, x_564);
return x_565;
}
}
}
}
else
{
lean_object* x_566; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_16);
x_566 = l_Lean_Meta_isProp(x_16, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_566) == 0)
{
uint8_t x_567; 
x_567 = !lean_is_exclusive(x_566);
if (x_567 == 0)
{
lean_object* x_568; uint8_t x_569; 
x_568 = lean_ctor_get(x_566, 0);
x_569 = lean_unbox(x_568);
lean_dec(x_568);
if (x_569 == 0)
{
lean_free_object(x_566);
x_413 = x_2;
x_414 = x_3;
x_415 = x_4;
x_416 = x_5;
x_417 = x_6;
x_418 = x_7;
x_419 = x_8;
x_420 = lean_box(0);
goto block_425;
}
else
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; 
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_570 = l_Lean_Meta_Grind_simpForall___closed__27;
lean_inc_ref(x_16);
x_571 = l_Lean_Expr_app___override(x_570, x_16);
x_572 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_572, 0, x_571);
x_573 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_573, 0, x_16);
lean_ctor_set(x_573, 1, x_572);
lean_ctor_set_uint8(x_573, sizeof(void*)*2, x_429);
x_574 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_574, 0, x_573);
lean_ctor_set(x_566, 0, x_574);
return x_566;
}
}
else
{
lean_object* x_575; uint8_t x_576; 
x_575 = lean_ctor_get(x_566, 0);
lean_inc(x_575);
lean_dec(x_566);
x_576 = lean_unbox(x_575);
lean_dec(x_575);
if (x_576 == 0)
{
x_413 = x_2;
x_414 = x_3;
x_415 = x_4;
x_416 = x_5;
x_417 = x_6;
x_418 = x_7;
x_419 = x_8;
x_420 = lean_box(0);
goto block_425;
}
else
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; 
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_577 = l_Lean_Meta_Grind_simpForall___closed__27;
lean_inc_ref(x_16);
x_578 = l_Lean_Expr_app___override(x_577, x_16);
x_579 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_579, 0, x_578);
x_580 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_580, 0, x_16);
lean_ctor_set(x_580, 1, x_579);
lean_ctor_set_uint8(x_580, sizeof(void*)*2, x_429);
x_581 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_581, 0, x_580);
x_582 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_582, 0, x_581);
return x_582;
}
}
}
else
{
uint8_t x_583; 
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
x_583 = !lean_is_exclusive(x_566);
if (x_583 == 0)
{
return x_566;
}
else
{
lean_object* x_584; lean_object* x_585; 
x_584 = lean_ctor_get(x_566, 0);
lean_inc(x_584);
lean_dec(x_566);
x_585 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_585, 0, x_584);
return x_585;
}
}
}
}
else
{
lean_object* x_586; 
lean_dec_ref(x_453);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_16);
x_586 = l_Lean_Meta_isProp(x_16, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_586) == 0)
{
uint8_t x_587; 
x_587 = !lean_is_exclusive(x_586);
if (x_587 == 0)
{
lean_object* x_588; uint8_t x_589; 
x_588 = lean_ctor_get(x_586, 0);
x_589 = lean_unbox(x_588);
lean_dec(x_588);
if (x_589 == 0)
{
lean_free_object(x_586);
x_413 = x_2;
x_414 = x_3;
x_415 = x_4;
x_416 = x_5;
x_417 = x_6;
x_418 = x_7;
x_419 = x_8;
x_420 = lean_box(0);
goto block_425;
}
else
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; 
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_590 = l_Lean_Meta_Grind_simpForall___closed__13;
x_591 = l_Lean_Meta_Grind_simpForall___closed__30;
x_592 = l_Lean_Expr_app___override(x_591, x_16);
x_593 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_593, 0, x_592);
x_594 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_594, 0, x_590);
lean_ctor_set(x_594, 1, x_593);
lean_ctor_set_uint8(x_594, sizeof(void*)*2, x_429);
x_595 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_595, 0, x_594);
lean_ctor_set(x_586, 0, x_595);
return x_586;
}
}
else
{
lean_object* x_596; uint8_t x_597; 
x_596 = lean_ctor_get(x_586, 0);
lean_inc(x_596);
lean_dec(x_586);
x_597 = lean_unbox(x_596);
lean_dec(x_596);
if (x_597 == 0)
{
x_413 = x_2;
x_414 = x_3;
x_415 = x_4;
x_416 = x_5;
x_417 = x_6;
x_418 = x_7;
x_419 = x_8;
x_420 = lean_box(0);
goto block_425;
}
else
{
lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; 
lean_dec_ref(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_598 = l_Lean_Meta_Grind_simpForall___closed__13;
x_599 = l_Lean_Meta_Grind_simpForall___closed__30;
x_600 = l_Lean_Expr_app___override(x_599, x_16);
x_601 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_601, 0, x_600);
x_602 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_602, 0, x_598);
lean_ctor_set(x_602, 1, x_601);
lean_ctor_set_uint8(x_602, sizeof(void*)*2, x_429);
x_603 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_603, 0, x_602);
x_604 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_604, 0, x_603);
return x_604;
}
}
}
else
{
uint8_t x_605; 
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
x_605 = !lean_is_exclusive(x_586);
if (x_605 == 0)
{
return x_586;
}
else
{
lean_object* x_606; lean_object* x_607; 
x_606 = lean_ctor_get(x_586, 0);
lean_inc(x_606);
lean_dec(x_586);
x_607 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_607, 0, x_606);
return x_607;
}
}
}
block_452:
{
if (lean_obj_tag(x_430) == 0)
{
uint8_t x_431; 
x_431 = !lean_is_exclusive(x_430);
if (x_431 == 0)
{
lean_object* x_432; uint8_t x_433; 
x_432 = lean_ctor_get(x_430, 0);
x_433 = lean_unbox(x_432);
lean_dec(x_432);
if (x_433 == 0)
{
lean_free_object(x_430);
x_413 = x_2;
x_414 = x_3;
x_415 = x_4;
x_416 = x_5;
x_417 = x_6;
x_418 = x_7;
x_419 = x_8;
x_420 = lean_box(0);
goto block_425;
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
lean_dec_ref(x_16);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_434 = l_Lean_Meta_Grind_simpForall___closed__13;
x_435 = l_Lean_Meta_Grind_simpForall___closed__16;
x_436 = l_Lean_Expr_app___override(x_435, x_15);
x_437 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_437, 0, x_436);
x_438 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_438, 0, x_434);
lean_ctor_set(x_438, 1, x_437);
lean_ctor_set_uint8(x_438, sizeof(void*)*2, x_429);
x_439 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_439, 0, x_438);
lean_ctor_set(x_430, 0, x_439);
return x_430;
}
}
else
{
lean_object* x_440; uint8_t x_441; 
x_440 = lean_ctor_get(x_430, 0);
lean_inc(x_440);
lean_dec(x_430);
x_441 = lean_unbox(x_440);
lean_dec(x_440);
if (x_441 == 0)
{
x_413 = x_2;
x_414 = x_3;
x_415 = x_4;
x_416 = x_5;
x_417 = x_6;
x_418 = x_7;
x_419 = x_8;
x_420 = lean_box(0);
goto block_425;
}
else
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
lean_dec_ref(x_16);
lean_dec(x_14);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_442 = l_Lean_Meta_Grind_simpForall___closed__13;
x_443 = l_Lean_Meta_Grind_simpForall___closed__16;
x_444 = l_Lean_Expr_app___override(x_443, x_15);
x_445 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_445, 0, x_444);
x_446 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_446, 0, x_442);
lean_ctor_set(x_446, 1, x_445);
lean_ctor_set_uint8(x_446, sizeof(void*)*2, x_429);
x_447 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_447, 0, x_446);
x_448 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_448, 0, x_447);
return x_448;
}
}
}
else
{
uint8_t x_449; 
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
x_449 = !lean_is_exclusive(x_430);
if (x_449 == 0)
{
return x_430;
}
else
{
lean_object* x_450; lean_object* x_451; 
x_450 = lean_ctor_get(x_430, 0);
lean_inc(x_450);
lean_dec(x_430);
x_451 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_451, 0, x_450);
return x_451;
}
}
}
}
else
{
uint8_t x_608; 
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
x_608 = !lean_is_exclusive(x_427);
if (x_608 == 0)
{
return x_427;
}
else
{
lean_object* x_609; lean_object* x_610; 
x_609 = lean_ctor_get(x_427, 0);
lean_inc(x_609);
lean_dec(x_427);
x_610 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_610, 0, x_609);
return x_610;
}
}
}
else
{
lean_object* x_611; 
lean_inc_ref(x_15);
x_611 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_15, x_6);
if (lean_obj_tag(x_611) == 0)
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; uint8_t x_615; 
x_612 = lean_ctor_get(x_611, 0);
lean_inc(x_612);
lean_dec_ref(x_611);
x_613 = l_Lean_Expr_cleanupAnnotations(x_612);
x_614 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f___closed__3;
x_615 = l_Lean_Expr_isConstOf(x_613, x_614);
if (x_615 == 0)
{
lean_object* x_616; uint8_t x_617; 
x_616 = l_Lean_Meta_Grind_simpForall___closed__12;
x_617 = l_Lean_Expr_isConstOf(x_613, x_616);
lean_dec_ref(x_613);
if (x_617 == 0)
{
x_413 = x_2;
x_414 = x_3;
x_415 = x_4;
x_416 = x_5;
x_417 = x_6;
x_418 = x_7;
x_419 = x_8;
x_420 = lean_box(0);
goto block_425;
}
else
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; 
x_618 = l_Lean_Meta_Grind_simpForall___closed__33;
x_619 = lean_expr_instantiate1(x_16, x_618);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_619);
x_620 = l_Lean_Meta_isProp(x_619, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_620) == 0)
{
uint8_t x_621; 
x_621 = !lean_is_exclusive(x_620);
if (x_621 == 0)
{
lean_object* x_622; uint8_t x_623; 
x_622 = lean_ctor_get(x_620, 0);
x_623 = lean_unbox(x_622);
lean_dec(x_622);
if (x_623 == 0)
{
lean_free_object(x_620);
lean_dec_ref(x_619);
x_413 = x_2;
x_414 = x_3;
x_415 = x_4;
x_416 = x_5;
x_417 = x_6;
x_418 = x_7;
x_419 = x_8;
x_420 = lean_box(0);
goto block_425;
}
else
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_624 = l_Lean_mkLambda(x_14, x_17, x_15, x_16);
x_625 = l_Lean_Meta_Grind_simpForall___closed__36;
x_626 = l_Lean_Expr_app___override(x_625, x_624);
x_627 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_627, 0, x_626);
x_628 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_628, 0, x_619);
lean_ctor_set(x_628, 1, x_627);
lean_ctor_set_uint8(x_628, sizeof(void*)*2, x_426);
x_629 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_629, 0, x_628);
lean_ctor_set(x_620, 0, x_629);
return x_620;
}
}
else
{
lean_object* x_630; uint8_t x_631; 
x_630 = lean_ctor_get(x_620, 0);
lean_inc(x_630);
lean_dec(x_620);
x_631 = lean_unbox(x_630);
lean_dec(x_630);
if (x_631 == 0)
{
lean_dec_ref(x_619);
x_413 = x_2;
x_414 = x_3;
x_415 = x_4;
x_416 = x_5;
x_417 = x_6;
x_418 = x_7;
x_419 = x_8;
x_420 = lean_box(0);
goto block_425;
}
else
{
lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_632 = l_Lean_mkLambda(x_14, x_17, x_15, x_16);
x_633 = l_Lean_Meta_Grind_simpForall___closed__36;
x_634 = l_Lean_Expr_app___override(x_633, x_632);
x_635 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_635, 0, x_634);
x_636 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_636, 0, x_619);
lean_ctor_set(x_636, 1, x_635);
lean_ctor_set_uint8(x_636, sizeof(void*)*2, x_426);
x_637 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_637, 0, x_636);
x_638 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_638, 0, x_637);
return x_638;
}
}
}
else
{
uint8_t x_639; 
lean_dec_ref(x_619);
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
x_639 = !lean_is_exclusive(x_620);
if (x_639 == 0)
{
return x_620;
}
else
{
lean_object* x_640; lean_object* x_641; 
x_640 = lean_ctor_get(x_620, 0);
lean_inc(x_640);
lean_dec(x_620);
x_641 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_641, 0, x_640);
return x_641;
}
}
}
}
else
{
lean_object* x_642; lean_object* x_643; 
lean_dec_ref(x_613);
lean_inc_ref(x_16);
lean_inc_ref(x_15);
lean_inc(x_14);
x_642 = l_Lean_mkLambda(x_14, x_17, x_15, x_16);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc_ref(x_642);
x_643 = lean_infer_type(x_642, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_643) == 0)
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; 
x_644 = lean_ctor_get(x_643, 0);
lean_inc(x_644);
lean_dec_ref(x_643);
x_645 = l_Lean_Meta_Grind_simpForall___closed__38;
lean_inc_ref(x_15);
lean_inc(x_14);
x_646 = l_Lean_mkForall(x_14, x_17, x_15, x_645);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_647 = l_Lean_Meta_isExprDefEq(x_644, x_646, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_647) == 0)
{
uint8_t x_648; 
x_648 = !lean_is_exclusive(x_647);
if (x_648 == 0)
{
lean_object* x_649; uint8_t x_650; 
x_649 = lean_ctor_get(x_647, 0);
x_650 = lean_unbox(x_649);
lean_dec(x_649);
if (x_650 == 0)
{
lean_free_object(x_647);
lean_dec_ref(x_642);
x_413 = x_2;
x_414 = x_3;
x_415 = x_4;
x_416 = x_5;
x_417 = x_6;
x_418 = x_7;
x_419 = x_8;
x_420 = lean_box(0);
goto block_425;
}
else
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; 
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
x_651 = l_Lean_Meta_Grind_simpForall___closed__13;
x_652 = l_Lean_Meta_Grind_simpForall___closed__41;
x_653 = l_Lean_Expr_app___override(x_652, x_642);
x_654 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_654, 0, x_653);
x_655 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_655, 0, x_651);
lean_ctor_set(x_655, 1, x_654);
lean_ctor_set_uint8(x_655, sizeof(void*)*2, x_426);
x_656 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_656, 0, x_655);
lean_ctor_set(x_647, 0, x_656);
return x_647;
}
}
else
{
lean_object* x_657; uint8_t x_658; 
x_657 = lean_ctor_get(x_647, 0);
lean_inc(x_657);
lean_dec(x_647);
x_658 = lean_unbox(x_657);
lean_dec(x_657);
if (x_658 == 0)
{
lean_dec_ref(x_642);
x_413 = x_2;
x_414 = x_3;
x_415 = x_4;
x_416 = x_5;
x_417 = x_6;
x_418 = x_7;
x_419 = x_8;
x_420 = lean_box(0);
goto block_425;
}
else
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; 
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
x_659 = l_Lean_Meta_Grind_simpForall___closed__13;
x_660 = l_Lean_Meta_Grind_simpForall___closed__41;
x_661 = l_Lean_Expr_app___override(x_660, x_642);
x_662 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_662, 0, x_661);
x_663 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_663, 0, x_659);
lean_ctor_set(x_663, 1, x_662);
lean_ctor_set_uint8(x_663, sizeof(void*)*2, x_426);
x_664 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_664, 0, x_663);
x_665 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_665, 0, x_664);
return x_665;
}
}
}
else
{
uint8_t x_666; 
lean_dec_ref(x_642);
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
x_666 = !lean_is_exclusive(x_647);
if (x_666 == 0)
{
return x_647;
}
else
{
lean_object* x_667; lean_object* x_668; 
x_667 = lean_ctor_get(x_647, 0);
lean_inc(x_667);
lean_dec(x_647);
x_668 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_668, 0, x_667);
return x_668;
}
}
}
else
{
uint8_t x_669; 
lean_dec_ref(x_642);
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
x_669 = !lean_is_exclusive(x_643);
if (x_669 == 0)
{
return x_643;
}
else
{
lean_object* x_670; lean_object* x_671; 
x_670 = lean_ctor_get(x_643, 0);
lean_inc(x_670);
lean_dec(x_643);
x_671 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_671, 0, x_670);
return x_671;
}
}
}
}
else
{
uint8_t x_672; 
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
x_672 = !lean_is_exclusive(x_611);
if (x_672 == 0)
{
return x_611;
}
else
{
lean_object* x_673; lean_object* x_674; 
x_673 = lean_ctor_get(x_611, 0);
lean_inc(x_673);
lean_dec(x_611);
x_674 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_674, 0, x_673);
return x_674;
}
}
}
block_412:
{
if (x_26 == 0)
{
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
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
lean_dec_ref(x_22);
lean_dec(x_19);
lean_dec(x_18);
x_32 = l_Lean_Meta_Grind_simpForall___closed__4;
x_33 = lean_name_eq(x_29, x_32);
lean_dec(x_29);
if (x_33 == 0)
{
lean_dec_ref(x_27);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
x_10 = lean_box(0);
goto block_13;
}
else
{
lean_object* x_34; 
lean_inc_ref(x_15);
x_34 = l_Lean_Meta_getLevel(x_15, x_23, x_24, x_20, x_21);
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
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_52 = lean_ctor_get(x_34, 0);
lean_inc(x_52);
lean_dec(x_34);
x_53 = l_Lean_Expr_appArg_x21(x_27);
lean_dec_ref(x_27);
x_54 = l_Lean_Expr_appArg_x21(x_16);
lean_dec_ref(x_16);
lean_inc_ref(x_53);
lean_inc_ref(x_15);
lean_inc(x_14);
x_55 = l_Lean_mkLambda(x_14, x_17, x_15, x_53);
lean_inc_ref(x_54);
lean_inc_ref(x_15);
lean_inc(x_14);
x_56 = l_Lean_mkLambda(x_14, x_17, x_15, x_54);
lean_inc_ref(x_15);
lean_inc(x_14);
x_57 = l_Lean_mkForall(x_14, x_17, x_15, x_53);
lean_inc_ref(x_15);
x_58 = l_Lean_mkForall(x_14, x_17, x_15, x_54);
x_59 = l_Lean_mkAnd(x_57, x_58);
x_60 = l_Lean_Meta_Grind_simpForall___closed__6;
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_52);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_mkConst(x_60, x_62);
x_64 = l_Lean_mkApp3(x_63, x_15, x_55, x_56);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_66, 0, x_59);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set_uint8(x_66, sizeof(void*)*2, x_26);
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
else
{
uint8_t x_69; 
lean_dec_ref(x_27);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
x_69 = !lean_is_exclusive(x_34);
if (x_69 == 0)
{
return x_34;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_34, 0);
lean_inc(x_70);
lean_dec(x_34);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
return x_71;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_29);
x_72 = l_Lean_Expr_appArg_x21(x_27);
lean_dec_ref(x_27);
x_73 = l_Lean_Expr_appArg_x21(x_16);
lean_dec_ref(x_16);
x_74 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f(x_72);
if (lean_obj_tag(x_74) == 1)
{
uint8_t x_75; 
lean_dec_ref(x_72);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_74, 0);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_ctor_get(x_76, 1);
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_76, 0);
x_81 = lean_ctor_get(x_78, 0);
x_82 = lean_ctor_get(x_78, 1);
lean_inc(x_21);
lean_inc_ref(x_20);
lean_inc(x_24);
lean_inc_ref(x_23);
lean_inc_ref(x_15);
x_83 = l_Lean_Meta_getLevel(x_15, x_23, x_24, x_20, x_21);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
lean_inc(x_81);
x_85 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpForall___lam__0___boxed), 10, 1);
lean_closure_set(x_85, 0, x_81);
lean_inc_ref(x_15);
lean_inc(x_14);
x_86 = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(x_14, x_15, x_85, x_18, x_22, x_19, x_23, x_24, x_20, x_21);
if (lean_obj_tag(x_86) == 0)
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_88 = lean_ctor_get(x_86, 0);
lean_inc_ref(x_73);
lean_inc_ref(x_15);
lean_inc(x_14);
x_89 = l_Lean_mkLambda(x_14, x_17, x_15, x_73);
x_90 = 0;
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
x_91 = l_Lean_mkLambda(x_80, x_90, x_81, x_82);
lean_inc_ref(x_15);
lean_inc(x_14);
x_92 = l_Lean_mkLambda(x_14, x_17, x_15, x_91);
lean_inc(x_81);
lean_inc_ref(x_15);
lean_inc(x_14);
x_93 = l_Lean_mkLambda(x_14, x_17, x_15, x_81);
x_94 = lean_unsigned_to_nat(0u);
x_95 = lean_unsigned_to_nat(1u);
x_96 = lean_expr_lift_loose_bvars(x_73, x_94, x_95);
lean_dec_ref(x_73);
x_97 = l_Lean_mkOr(x_82, x_96);
x_98 = l_Lean_mkForall(x_80, x_90, x_81, x_97);
lean_inc_ref(x_15);
x_99 = l_Lean_mkForall(x_14, x_17, x_15, x_98);
x_100 = l_Lean_Meta_Grind_simpForall___closed__8;
x_101 = lean_box(0);
lean_ctor_set_tag(x_78, 1);
lean_ctor_set(x_78, 1, x_101);
lean_ctor_set(x_78, 0, x_88);
lean_ctor_set_tag(x_76, 1);
lean_ctor_set(x_76, 0, x_84);
x_102 = l_Lean_mkConst(x_100, x_76);
x_103 = l_Lean_mkApp4(x_102, x_15, x_93, x_89, x_92);
lean_ctor_set(x_74, 0, x_103);
x_104 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_104, 0, x_99);
lean_ctor_set(x_104, 1, x_74);
lean_ctor_set_uint8(x_104, sizeof(void*)*2, x_26);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_86, 0, x_105);
return x_86;
}
else
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_106 = lean_ctor_get(x_86, 0);
lean_inc(x_106);
lean_dec(x_86);
lean_inc_ref(x_73);
lean_inc_ref(x_15);
lean_inc(x_14);
x_107 = l_Lean_mkLambda(x_14, x_17, x_15, x_73);
x_108 = 0;
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
x_109 = l_Lean_mkLambda(x_80, x_108, x_81, x_82);
lean_inc_ref(x_15);
lean_inc(x_14);
x_110 = l_Lean_mkLambda(x_14, x_17, x_15, x_109);
lean_inc(x_81);
lean_inc_ref(x_15);
lean_inc(x_14);
x_111 = l_Lean_mkLambda(x_14, x_17, x_15, x_81);
x_112 = lean_unsigned_to_nat(0u);
x_113 = lean_unsigned_to_nat(1u);
x_114 = lean_expr_lift_loose_bvars(x_73, x_112, x_113);
lean_dec_ref(x_73);
x_115 = l_Lean_mkOr(x_82, x_114);
x_116 = l_Lean_mkForall(x_80, x_108, x_81, x_115);
lean_inc_ref(x_15);
x_117 = l_Lean_mkForall(x_14, x_17, x_15, x_116);
x_118 = l_Lean_Meta_Grind_simpForall___closed__8;
x_119 = lean_box(0);
lean_ctor_set_tag(x_78, 1);
lean_ctor_set(x_78, 1, x_119);
lean_ctor_set(x_78, 0, x_106);
lean_ctor_set_tag(x_76, 1);
lean_ctor_set(x_76, 0, x_84);
x_120 = l_Lean_mkConst(x_118, x_76);
x_121 = l_Lean_mkApp4(x_120, x_15, x_111, x_107, x_110);
lean_ctor_set(x_74, 0, x_121);
x_122 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_122, 0, x_117);
lean_ctor_set(x_122, 1, x_74);
lean_ctor_set_uint8(x_122, sizeof(void*)*2, x_26);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_122);
x_124 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_124, 0, x_123);
return x_124;
}
}
else
{
uint8_t x_125; 
lean_dec(x_84);
lean_free_object(x_78);
lean_dec(x_82);
lean_dec(x_81);
lean_free_object(x_76);
lean_dec(x_80);
lean_free_object(x_74);
lean_dec_ref(x_73);
lean_dec_ref(x_15);
lean_dec(x_14);
x_125 = !lean_is_exclusive(x_86);
if (x_125 == 0)
{
return x_86;
}
else
{
lean_object* x_126; lean_object* x_127; 
x_126 = lean_ctor_get(x_86, 0);
lean_inc(x_126);
lean_dec(x_86);
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_126);
return x_127;
}
}
}
else
{
uint8_t x_128; 
lean_free_object(x_78);
lean_dec(x_82);
lean_dec(x_81);
lean_free_object(x_76);
lean_dec(x_80);
lean_free_object(x_74);
lean_dec_ref(x_73);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec_ref(x_15);
lean_dec(x_14);
x_128 = !lean_is_exclusive(x_83);
if (x_128 == 0)
{
return x_83;
}
else
{
lean_object* x_129; lean_object* x_130; 
x_129 = lean_ctor_get(x_83, 0);
lean_inc(x_129);
lean_dec(x_83);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_129);
return x_130;
}
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_76, 0);
x_132 = lean_ctor_get(x_78, 0);
x_133 = lean_ctor_get(x_78, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_78);
lean_inc(x_21);
lean_inc_ref(x_20);
lean_inc(x_24);
lean_inc_ref(x_23);
lean_inc_ref(x_15);
x_134 = l_Lean_Meta_getLevel(x_15, x_23, x_24, x_20, x_21);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
lean_dec_ref(x_134);
lean_inc(x_132);
x_136 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpForall___lam__0___boxed), 10, 1);
lean_closure_set(x_136, 0, x_132);
lean_inc_ref(x_15);
lean_inc(x_14);
x_137 = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(x_14, x_15, x_136, x_18, x_22, x_19, x_23, x_24, x_20, x_21);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 x_139 = x_137;
} else {
 lean_dec_ref(x_137);
 x_139 = lean_box(0);
}
lean_inc_ref(x_73);
lean_inc_ref(x_15);
lean_inc(x_14);
x_140 = l_Lean_mkLambda(x_14, x_17, x_15, x_73);
x_141 = 0;
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
x_142 = l_Lean_mkLambda(x_131, x_141, x_132, x_133);
lean_inc_ref(x_15);
lean_inc(x_14);
x_143 = l_Lean_mkLambda(x_14, x_17, x_15, x_142);
lean_inc(x_132);
lean_inc_ref(x_15);
lean_inc(x_14);
x_144 = l_Lean_mkLambda(x_14, x_17, x_15, x_132);
x_145 = lean_unsigned_to_nat(0u);
x_146 = lean_unsigned_to_nat(1u);
x_147 = lean_expr_lift_loose_bvars(x_73, x_145, x_146);
lean_dec_ref(x_73);
x_148 = l_Lean_mkOr(x_133, x_147);
x_149 = l_Lean_mkForall(x_131, x_141, x_132, x_148);
lean_inc_ref(x_15);
x_150 = l_Lean_mkForall(x_14, x_17, x_15, x_149);
x_151 = l_Lean_Meta_Grind_simpForall___closed__8;
x_152 = lean_box(0);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_138);
lean_ctor_set(x_153, 1, x_152);
lean_ctor_set_tag(x_76, 1);
lean_ctor_set(x_76, 1, x_153);
lean_ctor_set(x_76, 0, x_135);
x_154 = l_Lean_mkConst(x_151, x_76);
x_155 = l_Lean_mkApp4(x_154, x_15, x_144, x_140, x_143);
lean_ctor_set(x_74, 0, x_155);
x_156 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_156, 0, x_150);
lean_ctor_set(x_156, 1, x_74);
lean_ctor_set_uint8(x_156, sizeof(void*)*2, x_26);
x_157 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_157, 0, x_156);
if (lean_is_scalar(x_139)) {
 x_158 = lean_alloc_ctor(0, 1, 0);
} else {
 x_158 = x_139;
}
lean_ctor_set(x_158, 0, x_157);
return x_158;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_135);
lean_dec(x_133);
lean_dec(x_132);
lean_free_object(x_76);
lean_dec(x_131);
lean_free_object(x_74);
lean_dec_ref(x_73);
lean_dec_ref(x_15);
lean_dec(x_14);
x_159 = lean_ctor_get(x_137, 0);
lean_inc(x_159);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 x_160 = x_137;
} else {
 lean_dec_ref(x_137);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 1, 0);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_159);
return x_161;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_133);
lean_dec(x_132);
lean_free_object(x_76);
lean_dec(x_131);
lean_free_object(x_74);
lean_dec_ref(x_73);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec_ref(x_15);
lean_dec(x_14);
x_162 = lean_ctor_get(x_134, 0);
lean_inc(x_162);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 x_163 = x_134;
} else {
 lean_dec_ref(x_134);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 1, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_162);
return x_164;
}
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_165 = lean_ctor_get(x_76, 1);
x_166 = lean_ctor_get(x_76, 0);
lean_inc(x_165);
lean_inc(x_166);
lean_dec(x_76);
x_167 = lean_ctor_get(x_165, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_165, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_169 = x_165;
} else {
 lean_dec_ref(x_165);
 x_169 = lean_box(0);
}
lean_inc(x_21);
lean_inc_ref(x_20);
lean_inc(x_24);
lean_inc_ref(x_23);
lean_inc_ref(x_15);
x_170 = l_Lean_Meta_getLevel(x_15, x_23, x_24, x_20, x_21);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
lean_dec_ref(x_170);
lean_inc(x_167);
x_172 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpForall___lam__0___boxed), 10, 1);
lean_closure_set(x_172, 0, x_167);
lean_inc_ref(x_15);
lean_inc(x_14);
x_173 = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(x_14, x_15, x_172, x_18, x_22, x_19, x_23, x_24, x_20, x_21);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 x_175 = x_173;
} else {
 lean_dec_ref(x_173);
 x_175 = lean_box(0);
}
lean_inc_ref(x_73);
lean_inc_ref(x_15);
lean_inc(x_14);
x_176 = l_Lean_mkLambda(x_14, x_17, x_15, x_73);
x_177 = 0;
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_166);
x_178 = l_Lean_mkLambda(x_166, x_177, x_167, x_168);
lean_inc_ref(x_15);
lean_inc(x_14);
x_179 = l_Lean_mkLambda(x_14, x_17, x_15, x_178);
lean_inc(x_167);
lean_inc_ref(x_15);
lean_inc(x_14);
x_180 = l_Lean_mkLambda(x_14, x_17, x_15, x_167);
x_181 = lean_unsigned_to_nat(0u);
x_182 = lean_unsigned_to_nat(1u);
x_183 = lean_expr_lift_loose_bvars(x_73, x_181, x_182);
lean_dec_ref(x_73);
x_184 = l_Lean_mkOr(x_168, x_183);
x_185 = l_Lean_mkForall(x_166, x_177, x_167, x_184);
lean_inc_ref(x_15);
x_186 = l_Lean_mkForall(x_14, x_17, x_15, x_185);
x_187 = l_Lean_Meta_Grind_simpForall___closed__8;
x_188 = lean_box(0);
if (lean_is_scalar(x_169)) {
 x_189 = lean_alloc_ctor(1, 2, 0);
} else {
 x_189 = x_169;
 lean_ctor_set_tag(x_189, 1);
}
lean_ctor_set(x_189, 0, x_174);
lean_ctor_set(x_189, 1, x_188);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_171);
lean_ctor_set(x_190, 1, x_189);
x_191 = l_Lean_mkConst(x_187, x_190);
x_192 = l_Lean_mkApp4(x_191, x_15, x_180, x_176, x_179);
lean_ctor_set(x_74, 0, x_192);
x_193 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_193, 0, x_186);
lean_ctor_set(x_193, 1, x_74);
lean_ctor_set_uint8(x_193, sizeof(void*)*2, x_26);
x_194 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_194, 0, x_193);
if (lean_is_scalar(x_175)) {
 x_195 = lean_alloc_ctor(0, 1, 0);
} else {
 x_195 = x_175;
}
lean_ctor_set(x_195, 0, x_194);
return x_195;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_171);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_166);
lean_free_object(x_74);
lean_dec_ref(x_73);
lean_dec_ref(x_15);
lean_dec(x_14);
x_196 = lean_ctor_get(x_173, 0);
lean_inc(x_196);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 x_197 = x_173;
} else {
 lean_dec_ref(x_173);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(1, 1, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_196);
return x_198;
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_166);
lean_free_object(x_74);
lean_dec_ref(x_73);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec_ref(x_15);
lean_dec(x_14);
x_199 = lean_ctor_get(x_170, 0);
lean_inc(x_199);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 x_200 = x_170;
} else {
 lean_dec_ref(x_170);
 x_200 = lean_box(0);
}
if (lean_is_scalar(x_200)) {
 x_201 = lean_alloc_ctor(1, 1, 0);
} else {
 x_201 = x_200;
}
lean_ctor_set(x_201, 0, x_199);
return x_201;
}
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_202 = lean_ctor_get(x_74, 0);
lean_inc(x_202);
lean_dec(x_74);
x_203 = lean_ctor_get(x_202, 1);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 0);
lean_inc(x_204);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_205 = x_202;
} else {
 lean_dec_ref(x_202);
 x_205 = lean_box(0);
}
x_206 = lean_ctor_get(x_203, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_203, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_208 = x_203;
} else {
 lean_dec_ref(x_203);
 x_208 = lean_box(0);
}
lean_inc(x_21);
lean_inc_ref(x_20);
lean_inc(x_24);
lean_inc_ref(x_23);
lean_inc_ref(x_15);
x_209 = l_Lean_Meta_getLevel(x_15, x_23, x_24, x_20, x_21);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
lean_dec_ref(x_209);
lean_inc(x_206);
x_211 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpForall___lam__0___boxed), 10, 1);
lean_closure_set(x_211, 0, x_206);
lean_inc_ref(x_15);
lean_inc(x_14);
x_212 = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(x_14, x_15, x_211, x_18, x_22, x_19, x_23, x_24, x_20, x_21);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 x_214 = x_212;
} else {
 lean_dec_ref(x_212);
 x_214 = lean_box(0);
}
lean_inc_ref(x_73);
lean_inc_ref(x_15);
lean_inc(x_14);
x_215 = l_Lean_mkLambda(x_14, x_17, x_15, x_73);
x_216 = 0;
lean_inc(x_207);
lean_inc(x_206);
lean_inc(x_204);
x_217 = l_Lean_mkLambda(x_204, x_216, x_206, x_207);
lean_inc_ref(x_15);
lean_inc(x_14);
x_218 = l_Lean_mkLambda(x_14, x_17, x_15, x_217);
lean_inc(x_206);
lean_inc_ref(x_15);
lean_inc(x_14);
x_219 = l_Lean_mkLambda(x_14, x_17, x_15, x_206);
x_220 = lean_unsigned_to_nat(0u);
x_221 = lean_unsigned_to_nat(1u);
x_222 = lean_expr_lift_loose_bvars(x_73, x_220, x_221);
lean_dec_ref(x_73);
x_223 = l_Lean_mkOr(x_207, x_222);
x_224 = l_Lean_mkForall(x_204, x_216, x_206, x_223);
lean_inc_ref(x_15);
x_225 = l_Lean_mkForall(x_14, x_17, x_15, x_224);
x_226 = l_Lean_Meta_Grind_simpForall___closed__8;
x_227 = lean_box(0);
if (lean_is_scalar(x_208)) {
 x_228 = lean_alloc_ctor(1, 2, 0);
} else {
 x_228 = x_208;
 lean_ctor_set_tag(x_228, 1);
}
lean_ctor_set(x_228, 0, x_213);
lean_ctor_set(x_228, 1, x_227);
if (lean_is_scalar(x_205)) {
 x_229 = lean_alloc_ctor(1, 2, 0);
} else {
 x_229 = x_205;
 lean_ctor_set_tag(x_229, 1);
}
lean_ctor_set(x_229, 0, x_210);
lean_ctor_set(x_229, 1, x_228);
x_230 = l_Lean_mkConst(x_226, x_229);
x_231 = l_Lean_mkApp4(x_230, x_15, x_219, x_215, x_218);
x_232 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_232, 0, x_231);
x_233 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_233, 0, x_225);
lean_ctor_set(x_233, 1, x_232);
lean_ctor_set_uint8(x_233, sizeof(void*)*2, x_26);
x_234 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_234, 0, x_233);
if (lean_is_scalar(x_214)) {
 x_235 = lean_alloc_ctor(0, 1, 0);
} else {
 x_235 = x_214;
}
lean_ctor_set(x_235, 0, x_234);
return x_235;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
lean_dec(x_210);
lean_dec(x_208);
lean_dec(x_207);
lean_dec(x_206);
lean_dec(x_205);
lean_dec(x_204);
lean_dec_ref(x_73);
lean_dec_ref(x_15);
lean_dec(x_14);
x_236 = lean_ctor_get(x_212, 0);
lean_inc(x_236);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 x_237 = x_212;
} else {
 lean_dec_ref(x_212);
 x_237 = lean_box(0);
}
if (lean_is_scalar(x_237)) {
 x_238 = lean_alloc_ctor(1, 1, 0);
} else {
 x_238 = x_237;
}
lean_ctor_set(x_238, 0, x_236);
return x_238;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_208);
lean_dec(x_207);
lean_dec(x_206);
lean_dec(x_205);
lean_dec(x_204);
lean_dec_ref(x_73);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec_ref(x_15);
lean_dec(x_14);
x_239 = lean_ctor_get(x_209, 0);
lean_inc(x_239);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 x_240 = x_209;
} else {
 lean_dec_ref(x_209);
 x_240 = lean_box(0);
}
if (lean_is_scalar(x_240)) {
 x_241 = lean_alloc_ctor(1, 1, 0);
} else {
 x_241 = x_240;
}
lean_ctor_set(x_241, 0, x_239);
return x_241;
}
}
}
else
{
lean_object* x_242; 
lean_dec(x_74);
x_242 = l___private_Lean_Meta_Tactic_Grind_ForallProp_0__Lean_Meta_Grind_isForallOrNot_x3f(x_73);
lean_dec_ref(x_73);
if (lean_obj_tag(x_242) == 1)
{
uint8_t x_243; 
x_243 = !lean_is_exclusive(x_242);
if (x_243 == 0)
{
lean_object* x_244; uint8_t x_245; 
x_244 = lean_ctor_get(x_242, 0);
x_245 = !lean_is_exclusive(x_244);
if (x_245 == 0)
{
lean_object* x_246; uint8_t x_247; 
x_246 = lean_ctor_get(x_244, 1);
x_247 = !lean_is_exclusive(x_246);
if (x_247 == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_248 = lean_ctor_get(x_244, 0);
x_249 = lean_ctor_get(x_246, 0);
x_250 = lean_ctor_get(x_246, 1);
lean_inc(x_21);
lean_inc_ref(x_20);
lean_inc(x_24);
lean_inc_ref(x_23);
lean_inc_ref(x_15);
x_251 = l_Lean_Meta_getLevel(x_15, x_23, x_24, x_20, x_21);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
lean_dec_ref(x_251);
lean_inc(x_249);
x_253 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpForall___lam__0___boxed), 10, 1);
lean_closure_set(x_253, 0, x_249);
lean_inc_ref(x_15);
lean_inc(x_14);
x_254 = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(x_14, x_15, x_253, x_18, x_22, x_19, x_23, x_24, x_20, x_21);
if (lean_obj_tag(x_254) == 0)
{
uint8_t x_255; 
x_255 = !lean_is_exclusive(x_254);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; uint8_t x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_256 = lean_ctor_get(x_254, 0);
lean_inc_ref(x_72);
lean_inc_ref(x_15);
lean_inc(x_14);
x_257 = l_Lean_mkLambda(x_14, x_17, x_15, x_72);
x_258 = 0;
lean_inc(x_250);
lean_inc(x_249);
lean_inc(x_248);
x_259 = l_Lean_mkLambda(x_248, x_258, x_249, x_250);
lean_inc_ref(x_15);
lean_inc(x_14);
x_260 = l_Lean_mkLambda(x_14, x_17, x_15, x_259);
lean_inc(x_249);
lean_inc_ref(x_15);
lean_inc(x_14);
x_261 = l_Lean_mkLambda(x_14, x_17, x_15, x_249);
x_262 = lean_unsigned_to_nat(0u);
x_263 = lean_unsigned_to_nat(1u);
x_264 = lean_expr_lift_loose_bvars(x_72, x_262, x_263);
lean_dec_ref(x_72);
x_265 = l_Lean_mkOr(x_264, x_250);
x_266 = l_Lean_mkForall(x_248, x_258, x_249, x_265);
lean_inc_ref(x_15);
x_267 = l_Lean_mkForall(x_14, x_17, x_15, x_266);
x_268 = l_Lean_Meta_Grind_simpForall___closed__10;
x_269 = lean_box(0);
lean_ctor_set_tag(x_246, 1);
lean_ctor_set(x_246, 1, x_269);
lean_ctor_set(x_246, 0, x_256);
lean_ctor_set_tag(x_244, 1);
lean_ctor_set(x_244, 0, x_252);
x_270 = l_Lean_mkConst(x_268, x_244);
x_271 = l_Lean_mkApp4(x_270, x_15, x_261, x_257, x_260);
lean_ctor_set(x_242, 0, x_271);
x_272 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_272, 0, x_267);
lean_ctor_set(x_272, 1, x_242);
lean_ctor_set_uint8(x_272, sizeof(void*)*2, x_26);
x_273 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_254, 0, x_273);
return x_254;
}
else
{
lean_object* x_274; lean_object* x_275; uint8_t x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_274 = lean_ctor_get(x_254, 0);
lean_inc(x_274);
lean_dec(x_254);
lean_inc_ref(x_72);
lean_inc_ref(x_15);
lean_inc(x_14);
x_275 = l_Lean_mkLambda(x_14, x_17, x_15, x_72);
x_276 = 0;
lean_inc(x_250);
lean_inc(x_249);
lean_inc(x_248);
x_277 = l_Lean_mkLambda(x_248, x_276, x_249, x_250);
lean_inc_ref(x_15);
lean_inc(x_14);
x_278 = l_Lean_mkLambda(x_14, x_17, x_15, x_277);
lean_inc(x_249);
lean_inc_ref(x_15);
lean_inc(x_14);
x_279 = l_Lean_mkLambda(x_14, x_17, x_15, x_249);
x_280 = lean_unsigned_to_nat(0u);
x_281 = lean_unsigned_to_nat(1u);
x_282 = lean_expr_lift_loose_bvars(x_72, x_280, x_281);
lean_dec_ref(x_72);
x_283 = l_Lean_mkOr(x_282, x_250);
x_284 = l_Lean_mkForall(x_248, x_276, x_249, x_283);
lean_inc_ref(x_15);
x_285 = l_Lean_mkForall(x_14, x_17, x_15, x_284);
x_286 = l_Lean_Meta_Grind_simpForall___closed__10;
x_287 = lean_box(0);
lean_ctor_set_tag(x_246, 1);
lean_ctor_set(x_246, 1, x_287);
lean_ctor_set(x_246, 0, x_274);
lean_ctor_set_tag(x_244, 1);
lean_ctor_set(x_244, 0, x_252);
x_288 = l_Lean_mkConst(x_286, x_244);
x_289 = l_Lean_mkApp4(x_288, x_15, x_279, x_275, x_278);
lean_ctor_set(x_242, 0, x_289);
x_290 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_290, 0, x_285);
lean_ctor_set(x_290, 1, x_242);
lean_ctor_set_uint8(x_290, sizeof(void*)*2, x_26);
x_291 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_291, 0, x_290);
x_292 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_292, 0, x_291);
return x_292;
}
}
else
{
uint8_t x_293; 
lean_dec(x_252);
lean_free_object(x_246);
lean_dec(x_250);
lean_dec(x_249);
lean_free_object(x_244);
lean_dec(x_248);
lean_free_object(x_242);
lean_dec_ref(x_72);
lean_dec_ref(x_15);
lean_dec(x_14);
x_293 = !lean_is_exclusive(x_254);
if (x_293 == 0)
{
return x_254;
}
else
{
lean_object* x_294; lean_object* x_295; 
x_294 = lean_ctor_get(x_254, 0);
lean_inc(x_294);
lean_dec(x_254);
x_295 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_295, 0, x_294);
return x_295;
}
}
}
else
{
uint8_t x_296; 
lean_free_object(x_246);
lean_dec(x_250);
lean_dec(x_249);
lean_free_object(x_244);
lean_dec(x_248);
lean_free_object(x_242);
lean_dec_ref(x_72);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec_ref(x_15);
lean_dec(x_14);
x_296 = !lean_is_exclusive(x_251);
if (x_296 == 0)
{
return x_251;
}
else
{
lean_object* x_297; lean_object* x_298; 
x_297 = lean_ctor_get(x_251, 0);
lean_inc(x_297);
lean_dec(x_251);
x_298 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_298, 0, x_297);
return x_298;
}
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_299 = lean_ctor_get(x_244, 0);
x_300 = lean_ctor_get(x_246, 0);
x_301 = lean_ctor_get(x_246, 1);
lean_inc(x_301);
lean_inc(x_300);
lean_dec(x_246);
lean_inc(x_21);
lean_inc_ref(x_20);
lean_inc(x_24);
lean_inc_ref(x_23);
lean_inc_ref(x_15);
x_302 = l_Lean_Meta_getLevel(x_15, x_23, x_24, x_20, x_21);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
lean_dec_ref(x_302);
lean_inc(x_300);
x_304 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpForall___lam__0___boxed), 10, 1);
lean_closure_set(x_304, 0, x_300);
lean_inc_ref(x_15);
lean_inc(x_14);
x_305 = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(x_14, x_15, x_304, x_18, x_22, x_19, x_23, x_24, x_20, x_21);
if (lean_obj_tag(x_305) == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_306 = lean_ctor_get(x_305, 0);
lean_inc(x_306);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 x_307 = x_305;
} else {
 lean_dec_ref(x_305);
 x_307 = lean_box(0);
}
lean_inc_ref(x_72);
lean_inc_ref(x_15);
lean_inc(x_14);
x_308 = l_Lean_mkLambda(x_14, x_17, x_15, x_72);
x_309 = 0;
lean_inc(x_301);
lean_inc(x_300);
lean_inc(x_299);
x_310 = l_Lean_mkLambda(x_299, x_309, x_300, x_301);
lean_inc_ref(x_15);
lean_inc(x_14);
x_311 = l_Lean_mkLambda(x_14, x_17, x_15, x_310);
lean_inc(x_300);
lean_inc_ref(x_15);
lean_inc(x_14);
x_312 = l_Lean_mkLambda(x_14, x_17, x_15, x_300);
x_313 = lean_unsigned_to_nat(0u);
x_314 = lean_unsigned_to_nat(1u);
x_315 = lean_expr_lift_loose_bvars(x_72, x_313, x_314);
lean_dec_ref(x_72);
x_316 = l_Lean_mkOr(x_315, x_301);
x_317 = l_Lean_mkForall(x_299, x_309, x_300, x_316);
lean_inc_ref(x_15);
x_318 = l_Lean_mkForall(x_14, x_17, x_15, x_317);
x_319 = l_Lean_Meta_Grind_simpForall___closed__10;
x_320 = lean_box(0);
x_321 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_321, 0, x_306);
lean_ctor_set(x_321, 1, x_320);
lean_ctor_set_tag(x_244, 1);
lean_ctor_set(x_244, 1, x_321);
lean_ctor_set(x_244, 0, x_303);
x_322 = l_Lean_mkConst(x_319, x_244);
x_323 = l_Lean_mkApp4(x_322, x_15, x_312, x_308, x_311);
lean_ctor_set(x_242, 0, x_323);
x_324 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_324, 0, x_318);
lean_ctor_set(x_324, 1, x_242);
lean_ctor_set_uint8(x_324, sizeof(void*)*2, x_26);
x_325 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_325, 0, x_324);
if (lean_is_scalar(x_307)) {
 x_326 = lean_alloc_ctor(0, 1, 0);
} else {
 x_326 = x_307;
}
lean_ctor_set(x_326, 0, x_325);
return x_326;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; 
lean_dec(x_303);
lean_dec(x_301);
lean_dec(x_300);
lean_free_object(x_244);
lean_dec(x_299);
lean_free_object(x_242);
lean_dec_ref(x_72);
lean_dec_ref(x_15);
lean_dec(x_14);
x_327 = lean_ctor_get(x_305, 0);
lean_inc(x_327);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 x_328 = x_305;
} else {
 lean_dec_ref(x_305);
 x_328 = lean_box(0);
}
if (lean_is_scalar(x_328)) {
 x_329 = lean_alloc_ctor(1, 1, 0);
} else {
 x_329 = x_328;
}
lean_ctor_set(x_329, 0, x_327);
return x_329;
}
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; 
lean_dec(x_301);
lean_dec(x_300);
lean_free_object(x_244);
lean_dec(x_299);
lean_free_object(x_242);
lean_dec_ref(x_72);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec_ref(x_15);
lean_dec(x_14);
x_330 = lean_ctor_get(x_302, 0);
lean_inc(x_330);
if (lean_is_exclusive(x_302)) {
 lean_ctor_release(x_302, 0);
 x_331 = x_302;
} else {
 lean_dec_ref(x_302);
 x_331 = lean_box(0);
}
if (lean_is_scalar(x_331)) {
 x_332 = lean_alloc_ctor(1, 1, 0);
} else {
 x_332 = x_331;
}
lean_ctor_set(x_332, 0, x_330);
return x_332;
}
}
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_333 = lean_ctor_get(x_244, 1);
x_334 = lean_ctor_get(x_244, 0);
lean_inc(x_333);
lean_inc(x_334);
lean_dec(x_244);
x_335 = lean_ctor_get(x_333, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_333, 1);
lean_inc(x_336);
if (lean_is_exclusive(x_333)) {
 lean_ctor_release(x_333, 0);
 lean_ctor_release(x_333, 1);
 x_337 = x_333;
} else {
 lean_dec_ref(x_333);
 x_337 = lean_box(0);
}
lean_inc(x_21);
lean_inc_ref(x_20);
lean_inc(x_24);
lean_inc_ref(x_23);
lean_inc_ref(x_15);
x_338 = l_Lean_Meta_getLevel(x_15, x_23, x_24, x_20, x_21);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
lean_dec_ref(x_338);
lean_inc(x_335);
x_340 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpForall___lam__0___boxed), 10, 1);
lean_closure_set(x_340, 0, x_335);
lean_inc_ref(x_15);
lean_inc(x_14);
x_341 = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(x_14, x_15, x_340, x_18, x_22, x_19, x_23, x_24, x_20, x_21);
if (lean_obj_tag(x_341) == 0)
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; uint8_t x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 x_343 = x_341;
} else {
 lean_dec_ref(x_341);
 x_343 = lean_box(0);
}
lean_inc_ref(x_72);
lean_inc_ref(x_15);
lean_inc(x_14);
x_344 = l_Lean_mkLambda(x_14, x_17, x_15, x_72);
x_345 = 0;
lean_inc(x_336);
lean_inc(x_335);
lean_inc(x_334);
x_346 = l_Lean_mkLambda(x_334, x_345, x_335, x_336);
lean_inc_ref(x_15);
lean_inc(x_14);
x_347 = l_Lean_mkLambda(x_14, x_17, x_15, x_346);
lean_inc(x_335);
lean_inc_ref(x_15);
lean_inc(x_14);
x_348 = l_Lean_mkLambda(x_14, x_17, x_15, x_335);
x_349 = lean_unsigned_to_nat(0u);
x_350 = lean_unsigned_to_nat(1u);
x_351 = lean_expr_lift_loose_bvars(x_72, x_349, x_350);
lean_dec_ref(x_72);
x_352 = l_Lean_mkOr(x_351, x_336);
x_353 = l_Lean_mkForall(x_334, x_345, x_335, x_352);
lean_inc_ref(x_15);
x_354 = l_Lean_mkForall(x_14, x_17, x_15, x_353);
x_355 = l_Lean_Meta_Grind_simpForall___closed__10;
x_356 = lean_box(0);
if (lean_is_scalar(x_337)) {
 x_357 = lean_alloc_ctor(1, 2, 0);
} else {
 x_357 = x_337;
 lean_ctor_set_tag(x_357, 1);
}
lean_ctor_set(x_357, 0, x_342);
lean_ctor_set(x_357, 1, x_356);
x_358 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_358, 0, x_339);
lean_ctor_set(x_358, 1, x_357);
x_359 = l_Lean_mkConst(x_355, x_358);
x_360 = l_Lean_mkApp4(x_359, x_15, x_348, x_344, x_347);
lean_ctor_set(x_242, 0, x_360);
x_361 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_361, 0, x_354);
lean_ctor_set(x_361, 1, x_242);
lean_ctor_set_uint8(x_361, sizeof(void*)*2, x_26);
x_362 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_362, 0, x_361);
if (lean_is_scalar(x_343)) {
 x_363 = lean_alloc_ctor(0, 1, 0);
} else {
 x_363 = x_343;
}
lean_ctor_set(x_363, 0, x_362);
return x_363;
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; 
lean_dec(x_339);
lean_dec(x_337);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_334);
lean_free_object(x_242);
lean_dec_ref(x_72);
lean_dec_ref(x_15);
lean_dec(x_14);
x_364 = lean_ctor_get(x_341, 0);
lean_inc(x_364);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 x_365 = x_341;
} else {
 lean_dec_ref(x_341);
 x_365 = lean_box(0);
}
if (lean_is_scalar(x_365)) {
 x_366 = lean_alloc_ctor(1, 1, 0);
} else {
 x_366 = x_365;
}
lean_ctor_set(x_366, 0, x_364);
return x_366;
}
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; 
lean_dec(x_337);
lean_dec(x_336);
lean_dec(x_335);
lean_dec(x_334);
lean_free_object(x_242);
lean_dec_ref(x_72);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec_ref(x_15);
lean_dec(x_14);
x_367 = lean_ctor_get(x_338, 0);
lean_inc(x_367);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 x_368 = x_338;
} else {
 lean_dec_ref(x_338);
 x_368 = lean_box(0);
}
if (lean_is_scalar(x_368)) {
 x_369 = lean_alloc_ctor(1, 1, 0);
} else {
 x_369 = x_368;
}
lean_ctor_set(x_369, 0, x_367);
return x_369;
}
}
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_370 = lean_ctor_get(x_242, 0);
lean_inc(x_370);
lean_dec(x_242);
x_371 = lean_ctor_get(x_370, 1);
lean_inc(x_371);
x_372 = lean_ctor_get(x_370, 0);
lean_inc(x_372);
if (lean_is_exclusive(x_370)) {
 lean_ctor_release(x_370, 0);
 lean_ctor_release(x_370, 1);
 x_373 = x_370;
} else {
 lean_dec_ref(x_370);
 x_373 = lean_box(0);
}
x_374 = lean_ctor_get(x_371, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_371, 1);
lean_inc(x_375);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 x_376 = x_371;
} else {
 lean_dec_ref(x_371);
 x_376 = lean_box(0);
}
lean_inc(x_21);
lean_inc_ref(x_20);
lean_inc(x_24);
lean_inc_ref(x_23);
lean_inc_ref(x_15);
x_377 = l_Lean_Meta_getLevel(x_15, x_23, x_24, x_20, x_21);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
lean_dec_ref(x_377);
lean_inc(x_374);
x_379 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_simpForall___lam__0___boxed), 10, 1);
lean_closure_set(x_379, 0, x_374);
lean_inc_ref(x_15);
lean_inc(x_14);
x_380 = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(x_14, x_15, x_379, x_18, x_22, x_19, x_23, x_24, x_20, x_21);
if (lean_obj_tag(x_380) == 0)
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; uint8_t x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 x_382 = x_380;
} else {
 lean_dec_ref(x_380);
 x_382 = lean_box(0);
}
lean_inc_ref(x_72);
lean_inc_ref(x_15);
lean_inc(x_14);
x_383 = l_Lean_mkLambda(x_14, x_17, x_15, x_72);
x_384 = 0;
lean_inc(x_375);
lean_inc(x_374);
lean_inc(x_372);
x_385 = l_Lean_mkLambda(x_372, x_384, x_374, x_375);
lean_inc_ref(x_15);
lean_inc(x_14);
x_386 = l_Lean_mkLambda(x_14, x_17, x_15, x_385);
lean_inc(x_374);
lean_inc_ref(x_15);
lean_inc(x_14);
x_387 = l_Lean_mkLambda(x_14, x_17, x_15, x_374);
x_388 = lean_unsigned_to_nat(0u);
x_389 = lean_unsigned_to_nat(1u);
x_390 = lean_expr_lift_loose_bvars(x_72, x_388, x_389);
lean_dec_ref(x_72);
x_391 = l_Lean_mkOr(x_390, x_375);
x_392 = l_Lean_mkForall(x_372, x_384, x_374, x_391);
lean_inc_ref(x_15);
x_393 = l_Lean_mkForall(x_14, x_17, x_15, x_392);
x_394 = l_Lean_Meta_Grind_simpForall___closed__10;
x_395 = lean_box(0);
if (lean_is_scalar(x_376)) {
 x_396 = lean_alloc_ctor(1, 2, 0);
} else {
 x_396 = x_376;
 lean_ctor_set_tag(x_396, 1);
}
lean_ctor_set(x_396, 0, x_381);
lean_ctor_set(x_396, 1, x_395);
if (lean_is_scalar(x_373)) {
 x_397 = lean_alloc_ctor(1, 2, 0);
} else {
 x_397 = x_373;
 lean_ctor_set_tag(x_397, 1);
}
lean_ctor_set(x_397, 0, x_378);
lean_ctor_set(x_397, 1, x_396);
x_398 = l_Lean_mkConst(x_394, x_397);
x_399 = l_Lean_mkApp4(x_398, x_15, x_387, x_383, x_386);
x_400 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_400, 0, x_399);
x_401 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_401, 0, x_393);
lean_ctor_set(x_401, 1, x_400);
lean_ctor_set_uint8(x_401, sizeof(void*)*2, x_26);
x_402 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_402, 0, x_401);
if (lean_is_scalar(x_382)) {
 x_403 = lean_alloc_ctor(0, 1, 0);
} else {
 x_403 = x_382;
}
lean_ctor_set(x_403, 0, x_402);
return x_403;
}
else
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; 
lean_dec(x_378);
lean_dec(x_376);
lean_dec(x_375);
lean_dec(x_374);
lean_dec(x_373);
lean_dec(x_372);
lean_dec_ref(x_72);
lean_dec_ref(x_15);
lean_dec(x_14);
x_404 = lean_ctor_get(x_380, 0);
lean_inc(x_404);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 x_405 = x_380;
} else {
 lean_dec_ref(x_380);
 x_405 = lean_box(0);
}
if (lean_is_scalar(x_405)) {
 x_406 = lean_alloc_ctor(1, 1, 0);
} else {
 x_406 = x_405;
}
lean_ctor_set(x_406, 0, x_404);
return x_406;
}
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; 
lean_dec(x_376);
lean_dec(x_375);
lean_dec(x_374);
lean_dec(x_373);
lean_dec(x_372);
lean_dec_ref(x_72);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec_ref(x_15);
lean_dec(x_14);
x_407 = lean_ctor_get(x_377, 0);
lean_inc(x_407);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 x_408 = x_377;
} else {
 lean_dec_ref(x_377);
 x_408 = lean_box(0);
}
if (lean_is_scalar(x_408)) {
 x_409 = lean_alloc_ctor(1, 1, 0);
} else {
 x_409 = x_408;
}
lean_ctor_set(x_409, 0, x_407);
return x_409;
}
}
}
else
{
lean_dec(x_242);
lean_dec_ref(x_72);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
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
lean_object* x_410; lean_object* x_411; 
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec(x_24);
lean_dec_ref(x_23);
lean_dec_ref(x_22);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec_ref(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
x_410 = l_Lean_Meta_Grind_simpForall___closed__0;
x_411 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_411, 0, x_410);
return x_411;
}
}
}
block_425:
{
uint8_t x_421; 
x_421 = l_Lean_Expr_isApp(x_16);
if (x_421 == 0)
{
x_18 = x_413;
x_19 = x_415;
x_20 = x_418;
x_21 = x_419;
x_22 = x_414;
x_23 = x_416;
x_24 = x_417;
x_25 = lean_box(0);
x_26 = x_421;
goto block_412;
}
else
{
lean_object* x_422; lean_object* x_423; uint8_t x_424; 
x_422 = l_Lean_Expr_getAppNumArgs(x_16);
x_423 = lean_unsigned_to_nat(2u);
x_424 = lean_nat_dec_eq(x_422, x_423);
lean_dec(x_422);
x_18 = x_413;
x_19 = x_415;
x_20 = x_418;
x_21 = x_419;
x_22 = x_414;
x_23 = x_416;
x_24 = x_417;
x_25 = lean_box(0);
x_26 = x_424;
goto block_412;
}
}
}
else
{
lean_object* x_675; lean_object* x_676; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_675 = l_Lean_Meta_Grind_simpForall___closed__0;
x_676 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_676, 0, x_675);
return x_676;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_simpForall_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpForall___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_simpForall(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
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
x_11 = lean_box(0);
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
x_11 = lean_box(0);
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
x_11 = lean_box(0);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_108; uint8_t x_109; lean_object* x_110; uint8_t x_111; uint8_t x_138; uint8_t x_168; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 2);
lean_inc_ref(x_24);
lean_dec_ref(x_22);
x_25 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_25);
lean_dec_ref(x_17);
x_168 = l_Lean_Expr_isApp(x_24);
if (x_168 == 0)
{
x_138 = x_168;
goto block_167;
}
else
{
lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_169 = l_Lean_Expr_getAppNumArgs(x_24);
x_170 = lean_unsigned_to_nat(2u);
x_171 = lean_nat_dec_eq(x_169, x_170);
lean_dec(x_169);
x_138 = x_171;
goto block_167;
}
block_107:
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
x_7 = lean_box(0);
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
x_32 = l_Lean_Meta_isProp(x_25, x_26, x_27, x_28, x_29);
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
x_36 = l_Lean_Expr_constLevels_x21(x_19);
lean_dec_ref(x_19);
x_37 = l_Lean_Meta_Grind_simpExists___redArg___closed__1;
lean_inc(x_36);
x_38 = l_Lean_mkConst(x_37, x_36);
lean_inc_ref(x_25);
x_39 = l_Lean_Expr_app___override(x_38, x_25);
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
lean_inc_ref(x_24);
x_47 = l_Lean_mkApp3(x_46, x_25, x_44, x_24);
lean_ctor_set(x_42, 0, x_47);
x_48 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_48, 0, x_24);
lean_ctor_set(x_48, 1, x_42);
lean_ctor_set_uint8(x_48, sizeof(void*)*2, x_21);
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
lean_inc_ref(x_24);
x_53 = l_Lean_mkApp3(x_52, x_25, x_50, x_24);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_55, 0, x_24);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*2, x_21);
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
lean_dec_ref(x_24);
x_7 = lean_box(0);
goto block_10;
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
lean_inc_ref(x_24);
x_62 = l_Lean_mkApp3(x_61, x_25, x_58, x_24);
if (lean_is_scalar(x_59)) {
 x_63 = lean_alloc_ctor(1, 1, 0);
} else {
 x_63 = x_59;
}
lean_ctor_set(x_63, 0, x_62);
x_64 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_64, 0, x_24);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set_uint8(x_64, sizeof(void*)*2, x_21);
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
lean_dec_ref(x_24);
x_7 = lean_box(0);
goto block_10;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_36);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
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
lean_dec_ref(x_19);
lean_inc_ref(x_24);
lean_inc_ref(x_25);
x_70 = l_Lean_mkAnd(x_25, x_24);
x_71 = l_Lean_Meta_Grind_simpExists___redArg___closed__6;
x_72 = l_Lean_mkAppB(x_71, x_25, x_24);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_74, 0, x_70);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set_uint8(x_74, sizeof(void*)*2, x_21);
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
x_78 = l_Lean_Expr_constLevels_x21(x_19);
lean_dec_ref(x_19);
x_79 = l_Lean_Meta_Grind_simpExists___redArg___closed__1;
lean_inc(x_78);
x_80 = l_Lean_mkConst(x_79, x_78);
lean_inc_ref(x_25);
x_81 = l_Lean_Expr_app___override(x_80, x_25);
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
lean_inc_ref(x_24);
x_89 = l_Lean_mkApp3(x_88, x_25, x_85, x_24);
if (lean_is_scalar(x_86)) {
 x_90 = lean_alloc_ctor(1, 1, 0);
} else {
 x_90 = x_86;
}
lean_ctor_set(x_90, 0, x_89);
x_91 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_91, 0, x_24);
lean_ctor_set(x_91, 1, x_90);
lean_ctor_set_uint8(x_91, sizeof(void*)*2, x_21);
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
lean_dec_ref(x_24);
x_7 = lean_box(0);
goto block_10;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_78);
lean_dec_ref(x_25);
lean_dec_ref(x_24);
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
lean_dec_ref(x_19);
lean_inc_ref(x_24);
lean_inc_ref(x_25);
x_97 = l_Lean_mkAnd(x_25, x_24);
x_98 = l_Lean_Meta_Grind_simpExists___redArg___closed__6;
x_99 = l_Lean_mkAppB(x_98, x_25, x_24);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
x_101 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_101, 0, x_97);
lean_ctor_set(x_101, 1, x_100);
lean_ctor_set_uint8(x_101, sizeof(void*)*2, x_21);
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
lean_dec_ref(x_24);
lean_dec_ref(x_19);
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
lean_dec_ref(x_24);
lean_dec_ref(x_19);
x_7 = lean_box(0);
goto block_10;
}
}
block_137:
{
if (x_111 == 0)
{
uint8_t x_112; 
x_112 = l_Lean_Expr_hasLooseBVars(x_110);
if (x_112 == 0)
{
if (x_109 == 0)
{
lean_dec_ref(x_110);
lean_dec_ref(x_108);
lean_dec(x_23);
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
lean_dec_ref(x_24);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_113 = 0;
lean_inc_ref(x_25);
x_114 = l_Lean_mkLambda(x_23, x_113, x_25, x_108);
lean_inc_ref(x_114);
lean_inc_ref(x_25);
lean_inc_ref(x_19);
x_115 = l_Lean_mkAppB(x_19, x_25, x_114);
lean_inc_ref(x_110);
x_116 = l_Lean_mkAnd(x_115, x_110);
x_117 = l_Lean_Expr_constLevels_x21(x_19);
lean_dec_ref(x_19);
x_118 = l_Lean_Meta_Grind_simpExists___redArg___closed__8;
x_119 = l_Lean_mkConst(x_118, x_117);
x_120 = l_Lean_mkApp3(x_119, x_25, x_114, x_110);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_120);
x_122 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_122, 0, x_116);
lean_ctor_set(x_122, 1, x_121);
lean_ctor_set_uint8(x_122, sizeof(void*)*2, x_21);
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
lean_dec_ref(x_108);
lean_dec(x_23);
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
lean_dec_ref(x_24);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_125 = 0;
lean_inc_ref(x_25);
x_126 = l_Lean_mkLambda(x_23, x_125, x_25, x_110);
lean_inc_ref(x_126);
lean_inc_ref(x_25);
lean_inc_ref(x_19);
x_127 = l_Lean_mkAppB(x_19, x_25, x_126);
lean_inc_ref(x_108);
x_128 = l_Lean_mkAnd(x_108, x_127);
x_129 = l_Lean_Expr_constLevels_x21(x_19);
lean_dec_ref(x_19);
x_130 = l_Lean_Meta_Grind_simpExists___redArg___closed__10;
x_131 = l_Lean_mkConst(x_130, x_129);
x_132 = l_Lean_mkApp3(x_131, x_25, x_126, x_108);
x_133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_133, 0, x_132);
x_134 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_134, 0, x_128);
lean_ctor_set(x_134, 1, x_133);
lean_ctor_set_uint8(x_134, sizeof(void*)*2, x_21);
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
lean_dec(x_23);
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
x_139 = l_Lean_Expr_appFn_x21(x_24);
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
lean_dec(x_23);
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
x_147 = l_Lean_Expr_appArg_x21(x_24);
x_148 = l_Lean_Expr_hasLooseBVars(x_146);
if (x_148 == 0)
{
x_108 = x_146;
x_109 = x_145;
x_110 = x_147;
x_111 = x_145;
goto block_137;
}
else
{
x_108 = x_146;
x_109 = x_145;
x_110 = x_147;
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
x_150 = l_Lean_Expr_appArg_x21(x_24);
lean_dec_ref(x_24);
x_151 = 0;
lean_inc_ref(x_25);
lean_inc(x_23);
x_152 = l_Lean_mkLambda(x_23, x_151, x_25, x_149);
lean_inc_ref(x_25);
x_153 = l_Lean_mkLambda(x_23, x_151, x_25, x_150);
x_154 = l_Lean_Expr_constLevels_x21(x_19);
lean_inc_ref(x_152);
lean_inc_ref(x_25);
lean_inc_ref(x_19);
x_155 = l_Lean_mkAppB(x_19, x_25, x_152);
lean_inc_ref(x_153);
lean_inc_ref(x_25);
x_156 = l_Lean_mkAppB(x_19, x_25, x_153);
x_157 = l_Lean_mkOr(x_155, x_156);
x_158 = l_Lean_Meta_Grind_simpExists___redArg___closed__12;
x_159 = l_Lean_mkConst(x_158, x_154);
x_160 = l_Lean_mkApp3(x_159, x_25, x_152, x_153);
x_161 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_161, 0, x_160);
x_162 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_162, 0, x_157);
lean_ctor_set(x_162, 1, x_161);
lean_ctor_set_uint8(x_162, sizeof(void*)*2, x_21);
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
lean_dec_ref(x_24);
lean_dec(x_23);
lean_dec_ref(x_19);
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
lean_dec_ref(x_22);
lean_dec_ref(x_19);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_simpExists(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_simpExists___redArg(x_1, x_5, x_6, x_7, x_8);
return x_10;
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
