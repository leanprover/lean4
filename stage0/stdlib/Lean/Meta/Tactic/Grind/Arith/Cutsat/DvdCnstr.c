// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.DvdCnstr
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Types import Init.Data.Int.OfNat import Init.Grind.Propagator import Lean.Meta.Tactic.Grind.Simp import Lean.Meta.Tactic.Grind.PropagatorAttr import Lean.Meta.Tactic.Grind.Arith.Cutsat.Var import Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat import Lean.Meta.Tactic.Grind.Arith.Cutsat.Proof import Lean.Meta.Tactic.Grind.Arith.Cutsat.Norm import Lean.Meta.Tactic.Grind.Arith.Cutsat.CommRing import Lean.Meta.NatInstTesters
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
lean_object* l_Lean_Meta_Grind_Arith_gcdExt(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__5;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9;
static lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_8____boxed(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1;
extern lean_object* l_Lean_maxRecDepthErrorMessage;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__4;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__0;
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Meta_Grind_pushNewFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0;
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__3;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_coeff(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_Meta_Structural_isInstDvdInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_Structural_isInstDvdNat___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_8_();
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2;
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__5;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__1;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__6;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static double l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4;
double lean_float_of_nat(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_mul(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
uint8_t l_Lean_instBEqLBool_beq(uint8_t, uint8_t);
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8;
lean_object* l_Lean_PersistentArray_set___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(lean_object*);
lean_object* l_Int_Linear_Poly_gcdCoeffs(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_updateOccs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1;
lean_object* l_Int_Linear_Expr_norm(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqFalseCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__1;
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Int_Linear_Poly_combine(lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_getConst(lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Int_Linear_Poly_findVarToSubst___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7;
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__2;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_norm(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Int_Linear_Poly_isUnsatDvd(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Int_Linear_Poly_isSorted(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___boxed(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6;
lean_object* l_Lean_Meta_Grind_isEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2;
lean_object* l_Int_Linear_Poly_normCommRing_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_div(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd_spec__0(lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5;
lean_object* lean_int_neg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__0;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_natToInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_eagerReflBoolTrue;
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 1);
x_33 = l_Int_Linear_Poly_isSorted(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_inc_ref(x_32);
x_34 = l_Int_Linear_Poly_norm(x_32);
x_35 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_35, 0, x_1);
lean_inc_ref(x_34);
lean_inc(x_31);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set(x_36, 2, x_35);
x_23 = x_36;
x_24 = x_31;
x_25 = x_34;
goto block_30;
}
else
{
lean_inc_ref(x_32);
x_23 = x_1;
x_24 = x_31;
x_25 = x_32;
goto block_30;
}
block_11:
{
if (x_6 == 0)
{
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_int_ediv(x_4, x_3);
lean_dec(x_4);
x_8 = l_Int_Linear_Poly_div(x_3, x_5);
lean_dec(x_3);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_2);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
return x_10;
}
}
block_22:
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = l_Int_Linear_Poly_getConst(x_15);
x_18 = lean_int_emod(x_17, x_16);
lean_dec(x_17);
x_19 = lean_int_dec_eq(x_18, x_13);
lean_dec(x_13);
lean_dec(x_18);
if (x_19 == 0)
{
x_2 = x_12;
x_3 = x_16;
x_4 = x_14;
x_5 = x_15;
x_6 = x_19;
goto block_11;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0;
x_21 = lean_int_dec_eq(x_16, x_20);
if (x_21 == 0)
{
x_2 = x_12;
x_3 = x_16;
x_4 = x_14;
x_5 = x_15;
x_6 = x_19;
goto block_11;
}
else
{
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec(x_14);
return x_12;
}
}
}
block_30:
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_inc(x_24);
x_26 = l_Int_Linear_Poly_gcdCoeffs(x_25, x_24);
x_27 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1;
x_28 = lean_int_dec_lt(x_24, x_27);
if (x_28 == 0)
{
x_12 = x_23;
x_13 = x_27;
x_14 = x_24;
x_15 = x_25;
x_16 = x_26;
goto block_22;
}
else
{
lean_object* x_29; 
x_29 = lean_int_neg(x_26);
lean_dec(x_26);
x_12 = x_23;
x_13 = x_27;
x_14 = x_24;
x_15 = x_25;
x_16 = x_29;
goto block_22;
}
}
}
}
static lean_object* _init_l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trace", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
x_9 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__1;
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_1, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__0() {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1_spec__1(x_2, x_3, x_4, x_5, x_6);
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
x_17 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__0;
x_18 = 0;
x_19 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__1;
x_20 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set_float(x_20, sizeof(void*)*2, x_17);
lean_ctor_set_float(x_20, sizeof(void*)*2 + 8, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*2 + 16, x_18);
x_21 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__2;
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
x_29 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__0;
x_30 = 0;
x_31 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__1;
x_32 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_float(x_32, sizeof(void*)*2, x_29);
lean_ctor_set_float(x_32, sizeof(void*)*2 + 8, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 16, x_30);
x_33 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__2;
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
x_52 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__0;
x_53 = 0;
x_54 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__1;
x_55 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set_float(x_55, sizeof(void*)*2, x_52);
lean_ctor_set_float(x_55, sizeof(void*)*2 + 8, x_52);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 16, x_53);
x_56 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__2;
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
x_79 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__0;
x_80 = 0;
x_81 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__1;
x_82 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_82, 0, x_1);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set_float(x_82, sizeof(void*)*2, x_79);
lean_ctor_set_float(x_82, sizeof(void*)*2 + 8, x_79);
lean_ctor_set_uint8(x_82, sizeof(void*)*2 + 16, x_80);
x_83 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__2;
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("grind", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("debug", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lia", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("subst", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__3;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1;
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(", ", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_35; 
x_16 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4;
x_17 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_16, x_13);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_19 = x_17;
} else {
 lean_dec_ref(x_17);
 x_19 = lean_box(0);
}
x_20 = lean_ctor_get(x_3, 0);
x_21 = lean_ctor_get(x_5, 0);
x_22 = lean_ctor_get(x_5, 1);
x_23 = lean_int_mul(x_1, x_21);
x_24 = lean_nat_abs(x_23);
lean_dec(x_23);
x_25 = lean_nat_to_int(x_24);
lean_inc_ref(x_22);
x_26 = l_Int_Linear_Poly_mul(x_22, x_1);
x_27 = lean_int_neg(x_4);
lean_inc_ref(x_20);
x_28 = l_Int_Linear_Poly_mul(x_20, x_27);
lean_dec(x_27);
x_29 = l_Int_Linear_Poly_combine(x_26, x_28);
x_35 = lean_unbox(x_18);
lean_dec(x_18);
if (x_35 == 0)
{
x_30 = lean_box(0);
goto block_34;
}
else
{
lean_object* x_36; 
x_36 = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(x_2, x_6, x_13);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
lean_inc_ref(x_3);
x_38 = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(x_3, x_6, x_13);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
lean_inc_ref(x_5);
x_40 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_5, x_6, x_13);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = l_Lean_MessageData_ofExpr(x_37);
x_43 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_39);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_43);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_41);
x_48 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_16, x_47, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_48) == 0)
{
lean_dec_ref(x_48);
x_30 = lean_box(0);
goto block_34;
}
else
{
uint8_t x_49; 
lean_dec_ref(x_29);
lean_dec(x_25);
lean_dec(x_19);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
return x_48;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_39);
lean_dec(x_37);
lean_dec_ref(x_29);
lean_dec(x_25);
lean_dec(x_19);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_40);
if (x_52 == 0)
{
return x_40;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_40, 0);
lean_inc(x_53);
lean_dec(x_40);
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_37);
lean_dec_ref(x_29);
lean_dec(x_25);
lean_dec(x_19);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_38);
if (x_55 == 0)
{
return x_38;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_38, 0);
lean_inc(x_56);
lean_dec(x_38);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec_ref(x_29);
lean_dec(x_25);
lean_dec(x_19);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_58 = !lean_is_exclusive(x_36);
if (x_58 == 0)
{
return x_36;
}
else
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_36, 0);
lean_inc(x_59);
lean_dec(x_36);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
return x_60;
}
}
}
block_34:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_alloc_ctor(8, 3, 0);
lean_ctor_set(x_31, 0, x_2);
lean_ctor_set(x_31, 1, x_3);
lean_ctor_set(x_31, 2, x_5);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_25);
lean_ctor_set(x_32, 1, x_29);
lean_ctor_set(x_32, 2, x_31);
if (lean_is_scalar(x_19)) {
 x_33 = lean_alloc_ctor(0, 1, 0);
} else {
 x_33 = x_19;
}
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_1, x_2, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("runtime", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maxRecDepth", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__1;
x_2 = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4;
x_2 = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2;
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_13 = lean_ctor_get(x_9, 0);
x_14 = lean_ctor_get(x_9, 1);
x_15 = lean_ctor_get(x_9, 2);
x_16 = lean_ctor_get(x_9, 3);
x_17 = lean_ctor_get(x_9, 4);
x_18 = lean_ctor_get(x_9, 5);
x_19 = lean_ctor_get(x_9, 6);
x_20 = lean_ctor_get(x_9, 7);
x_21 = lean_ctor_get(x_9, 8);
x_22 = lean_ctor_get(x_9, 9);
x_23 = lean_ctor_get(x_9, 10);
x_24 = lean_ctor_get(x_9, 11);
x_25 = lean_ctor_get(x_9, 12);
x_26 = lean_ctor_get(x_9, 13);
x_27 = lean_nat_dec_eq(x_16, x_17);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_1, 1);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_16, x_29);
lean_dec(x_16);
lean_ctor_set(x_9, 3, x_30);
lean_inc_ref(x_28);
x_31 = l_Int_Linear_Poly_findVarToSubst___redArg(x_28, x_2, x_9);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_31, 0);
if (lean_obj_tag(x_33) == 1)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_free_object(x_31);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec_ref(x_33);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 0);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_ctor_get(x_36, 0);
x_40 = l_Int_Linear_Poly_coeff(x_39, x_38);
x_41 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(x_40, x_38, x_36, x_37, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_37);
lean_dec(x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
x_1 = x_42;
goto _start;
}
else
{
lean_dec_ref(x_9);
return x_41;
}
}
else
{
lean_dec(x_33);
lean_dec_ref(x_9);
lean_ctor_set(x_31, 0, x_1);
return x_31;
}
}
else
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_31, 0);
lean_inc(x_44);
lean_dec(x_31);
if (lean_obj_tag(x_44) == 1)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_45, 0);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_ctor_get(x_46, 0);
lean_inc(x_49);
lean_dec(x_46);
x_50 = lean_ctor_get(x_47, 0);
x_51 = l_Int_Linear_Poly_coeff(x_50, x_49);
x_52 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(x_51, x_49, x_47, x_48, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_48);
lean_dec(x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
x_1 = x_53;
goto _start;
}
else
{
lean_dec_ref(x_9);
return x_52;
}
}
else
{
lean_object* x_55; 
lean_dec(x_44);
lean_dec_ref(x_9);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_1);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec_ref(x_9);
lean_dec_ref(x_1);
x_56 = !lean_is_exclusive(x_31);
if (x_56 == 0)
{
return x_31;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_31, 0);
lean_inc(x_57);
lean_dec(x_31);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; 
lean_free_object(x_9);
lean_dec_ref(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_16);
lean_dec_ref(x_15);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_1);
x_59 = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(x_18);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; uint8_t x_76; 
x_60 = lean_ctor_get(x_9, 0);
x_61 = lean_ctor_get(x_9, 1);
x_62 = lean_ctor_get(x_9, 2);
x_63 = lean_ctor_get(x_9, 3);
x_64 = lean_ctor_get(x_9, 4);
x_65 = lean_ctor_get(x_9, 5);
x_66 = lean_ctor_get(x_9, 6);
x_67 = lean_ctor_get(x_9, 7);
x_68 = lean_ctor_get(x_9, 8);
x_69 = lean_ctor_get(x_9, 9);
x_70 = lean_ctor_get(x_9, 10);
x_71 = lean_ctor_get(x_9, 11);
x_72 = lean_ctor_get_uint8(x_9, sizeof(void*)*14);
x_73 = lean_ctor_get(x_9, 12);
x_74 = lean_ctor_get_uint8(x_9, sizeof(void*)*14 + 1);
x_75 = lean_ctor_get(x_9, 13);
lean_inc(x_75);
lean_inc(x_73);
lean_inc(x_71);
lean_inc(x_70);
lean_inc(x_69);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_9);
x_76 = lean_nat_dec_eq(x_63, x_64);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_1, 1);
x_78 = lean_unsigned_to_nat(1u);
x_79 = lean_nat_add(x_63, x_78);
lean_dec(x_63);
x_80 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_80, 0, x_60);
lean_ctor_set(x_80, 1, x_61);
lean_ctor_set(x_80, 2, x_62);
lean_ctor_set(x_80, 3, x_79);
lean_ctor_set(x_80, 4, x_64);
lean_ctor_set(x_80, 5, x_65);
lean_ctor_set(x_80, 6, x_66);
lean_ctor_set(x_80, 7, x_67);
lean_ctor_set(x_80, 8, x_68);
lean_ctor_set(x_80, 9, x_69);
lean_ctor_set(x_80, 10, x_70);
lean_ctor_set(x_80, 11, x_71);
lean_ctor_set(x_80, 12, x_73);
lean_ctor_set(x_80, 13, x_75);
lean_ctor_set_uint8(x_80, sizeof(void*)*14, x_72);
lean_ctor_set_uint8(x_80, sizeof(void*)*14 + 1, x_74);
lean_inc_ref(x_77);
x_81 = l_Int_Linear_Poly_findVarToSubst___redArg(x_77, x_2, x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 x_83 = x_81;
} else {
 lean_dec_ref(x_81);
 x_83 = lean_box(0);
}
if (lean_obj_tag(x_82) == 1)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_83);
x_84 = lean_ctor_get(x_82, 0);
lean_inc(x_84);
lean_dec_ref(x_82);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_84, 0);
lean_inc(x_87);
lean_dec(x_84);
x_88 = lean_ctor_get(x_85, 0);
lean_inc(x_88);
lean_dec(x_85);
x_89 = lean_ctor_get(x_86, 0);
x_90 = l_Int_Linear_Poly_coeff(x_89, x_88);
x_91 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(x_90, x_88, x_86, x_87, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_80, x_10);
lean_dec(x_87);
lean_dec(x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
lean_dec_ref(x_91);
x_1 = x_92;
x_9 = x_80;
goto _start;
}
else
{
lean_dec_ref(x_80);
return x_91;
}
}
else
{
lean_object* x_94; 
lean_dec(x_82);
lean_dec_ref(x_80);
if (lean_is_scalar(x_83)) {
 x_94 = lean_alloc_ctor(0, 1, 0);
} else {
 x_94 = x_83;
}
lean_ctor_set(x_94, 0, x_1);
return x_94;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec_ref(x_80);
lean_dec_ref(x_1);
x_95 = lean_ctor_get(x_81, 0);
lean_inc(x_95);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 x_96 = x_81;
} else {
 lean_dec_ref(x_81);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 1, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_95);
return x_97;
}
}
else
{
lean_object* x_98; 
lean_dec_ref(x_75);
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_63);
lean_dec_ref(x_62);
lean_dec_ref(x_61);
lean_dec_ref(x_60);
lean_dec_ref(x_1);
x_98 = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(x_65);
return x_98;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 6);
x_5 = lean_box(0);
x_6 = l_Lean_PersistentArray_set___redArg(x_4, x_1, x_5);
lean_ctor_set(x_2, 6, x_6);
return x_2;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_11 = lean_ctor_get(x_2, 4);
x_12 = lean_ctor_get(x_2, 5);
x_13 = lean_ctor_get(x_2, 6);
x_14 = lean_ctor_get(x_2, 7);
x_15 = lean_ctor_get(x_2, 8);
x_16 = lean_ctor_get(x_2, 9);
x_17 = lean_ctor_get(x_2, 10);
x_18 = lean_ctor_get(x_2, 11);
x_19 = lean_ctor_get(x_2, 12);
x_20 = lean_ctor_get(x_2, 13);
x_21 = lean_ctor_get(x_2, 14);
x_22 = lean_ctor_get_uint8(x_2, sizeof(void*)*23);
x_23 = lean_ctor_get(x_2, 15);
x_24 = lean_ctor_get(x_2, 16);
x_25 = lean_ctor_get(x_2, 17);
x_26 = lean_ctor_get(x_2, 18);
x_27 = lean_ctor_get(x_2, 19);
x_28 = lean_ctor_get(x_2, 20);
x_29 = lean_ctor_get(x_2, 21);
x_30 = lean_ctor_get_uint8(x_2, sizeof(void*)*23 + 1);
x_31 = lean_ctor_get(x_2, 22);
lean_inc(x_31);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_2);
x_32 = lean_box(0);
x_33 = l_Lean_PersistentArray_set___redArg(x_13, x_1, x_32);
x_34 = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(x_34, 0, x_7);
lean_ctor_set(x_34, 1, x_8);
lean_ctor_set(x_34, 2, x_9);
lean_ctor_set(x_34, 3, x_10);
lean_ctor_set(x_34, 4, x_11);
lean_ctor_set(x_34, 5, x_12);
lean_ctor_set(x_34, 6, x_33);
lean_ctor_set(x_34, 7, x_14);
lean_ctor_set(x_34, 8, x_15);
lean_ctor_set(x_34, 9, x_16);
lean_ctor_set(x_34, 10, x_17);
lean_ctor_set(x_34, 11, x_18);
lean_ctor_set(x_34, 12, x_19);
lean_ctor_set(x_34, 13, x_20);
lean_ctor_set(x_34, 14, x_21);
lean_ctor_set(x_34, 15, x_23);
lean_ctor_set(x_34, 16, x_24);
lean_ctor_set(x_34, 17, x_25);
lean_ctor_set(x_34, 18, x_26);
lean_ctor_set(x_34, 19, x_27);
lean_ctor_set(x_34, 20, x_28);
lean_ctor_set(x_34, 21, x_29);
lean_ctor_set(x_34, 22, x_31);
lean_ctor_set_uint8(x_34, sizeof(void*)*23, x_22);
lean_ctor_set_uint8(x_34, sizeof(void*)*23 + 1, x_30);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 6);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_1);
x_7 = l_Lean_PersistentArray_set___redArg(x_5, x_2, x_6);
lean_ctor_set(x_3, 6, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
x_10 = lean_ctor_get(x_3, 2);
x_11 = lean_ctor_get(x_3, 3);
x_12 = lean_ctor_get(x_3, 4);
x_13 = lean_ctor_get(x_3, 5);
x_14 = lean_ctor_get(x_3, 6);
x_15 = lean_ctor_get(x_3, 7);
x_16 = lean_ctor_get(x_3, 8);
x_17 = lean_ctor_get(x_3, 9);
x_18 = lean_ctor_get(x_3, 10);
x_19 = lean_ctor_get(x_3, 11);
x_20 = lean_ctor_get(x_3, 12);
x_21 = lean_ctor_get(x_3, 13);
x_22 = lean_ctor_get(x_3, 14);
x_23 = lean_ctor_get_uint8(x_3, sizeof(void*)*23);
x_24 = lean_ctor_get(x_3, 15);
x_25 = lean_ctor_get(x_3, 16);
x_26 = lean_ctor_get(x_3, 17);
x_27 = lean_ctor_get(x_3, 18);
x_28 = lean_ctor_get(x_3, 19);
x_29 = lean_ctor_get(x_3, 20);
x_30 = lean_ctor_get(x_3, 21);
x_31 = lean_ctor_get_uint8(x_3, sizeof(void*)*23 + 1);
x_32 = lean_ctor_get(x_3, 22);
lean_inc(x_32);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_1);
x_34 = l_Lean_PersistentArray_set___redArg(x_14, x_2, x_33);
x_35 = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_9);
lean_ctor_set(x_35, 2, x_10);
lean_ctor_set(x_35, 3, x_11);
lean_ctor_set(x_35, 4, x_12);
lean_ctor_set(x_35, 5, x_13);
lean_ctor_set(x_35, 6, x_34);
lean_ctor_set(x_35, 7, x_15);
lean_ctor_set(x_35, 8, x_16);
lean_ctor_set(x_35, 9, x_17);
lean_ctor_set(x_35, 10, x_18);
lean_ctor_set(x_35, 11, x_19);
lean_ctor_set(x_35, 12, x_20);
lean_ctor_set(x_35, 13, x_21);
lean_ctor_set(x_35, 14, x_22);
lean_ctor_set(x_35, 15, x_24);
lean_ctor_set(x_35, 16, x_25);
lean_ctor_set(x_35, 17, x_26);
lean_ctor_set(x_35, 18, x_27);
lean_ctor_set(x_35, 19, x_28);
lean_ctor_set(x_35, 20, x_29);
lean_ctor_set(x_35, 21, x_30);
lean_ctor_set(x_35, 22, x_32);
lean_ctor_set_uint8(x_35, sizeof(void*)*23, x_23);
lean_ctor_set_uint8(x_35, sizeof(void*)*23 + 1, x_31);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assert", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("store", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2;
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trivial", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2;
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unsat", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__6;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2;
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_43; uint8_t x_47; 
x_47 = !lean_is_exclusive(x_9);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_48 = lean_ctor_get(x_9, 0);
x_49 = lean_ctor_get(x_9, 1);
x_50 = lean_ctor_get(x_9, 2);
x_51 = lean_ctor_get(x_9, 3);
x_52 = lean_ctor_get(x_9, 4);
x_53 = lean_ctor_get(x_9, 5);
x_54 = lean_ctor_get(x_9, 6);
x_55 = lean_ctor_get(x_9, 7);
x_56 = lean_ctor_get(x_9, 8);
x_57 = lean_ctor_get(x_9, 9);
x_58 = lean_ctor_get(x_9, 10);
x_59 = lean_ctor_get(x_9, 11);
x_60 = lean_ctor_get(x_9, 12);
x_61 = lean_ctor_get(x_9, 13);
x_62 = lean_nat_dec_eq(x_51, x_52);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_nat_add(x_51, x_63);
lean_dec(x_51);
lean_ctor_set(x_9, 3, x_64);
x_65 = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(x_2, x_9);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_65, 0);
x_68 = lean_unbox(x_67);
lean_dec(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_217; lean_object* x_218; 
lean_free_object(x_65);
x_217 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3;
x_218 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_217, x_9);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; uint8_t x_312; 
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
lean_dec_ref(x_218);
x_220 = lean_box(0);
x_312 = lean_unbox(x_219);
lean_dec(x_219);
if (x_312 == 0)
{
x_250 = x_2;
x_251 = x_3;
x_252 = x_4;
x_253 = x_5;
x_254 = x_6;
x_255 = x_7;
x_256 = x_8;
x_257 = x_9;
x_258 = x_10;
x_259 = lean_box(0);
goto block_311;
}
else
{
lean_object* x_313; 
lean_inc_ref(x_1);
x_313 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_9);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; lean_object* x_315; 
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
lean_dec_ref(x_313);
x_315 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_217, x_314, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_315) == 0)
{
lean_dec_ref(x_315);
x_250 = x_2;
x_251 = x_3;
x_252 = x_4;
x_253 = x_5;
x_254 = x_6;
x_255 = x_7;
x_256 = x_8;
x_257 = x_9;
x_258 = x_10;
x_259 = lean_box(0);
goto block_311;
}
else
{
lean_dec_ref(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_315;
}
}
else
{
uint8_t x_316; 
lean_dec_ref(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_316 = !lean_is_exclusive(x_313);
if (x_316 == 0)
{
return x_313;
}
else
{
lean_object* x_317; lean_object* x_318; 
x_317 = lean_ctor_get(x_313, 0);
lean_inc(x_317);
lean_dec(x_313);
x_318 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_318, 0, x_317);
return x_318;
}
}
}
block_249:
{
lean_object* x_239; 
x_239 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_229, x_236);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; 
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
lean_dec_ref(x_239);
x_241 = lean_ctor_get(x_240, 6);
lean_inc_ref(x_241);
lean_dec(x_240);
x_242 = lean_ctor_get(x_241, 2);
x_243 = lean_nat_dec_lt(x_222, x_242);
if (x_243 == 0)
{
lean_object* x_244; 
lean_dec_ref(x_241);
x_244 = l_outOfBounds___redArg(x_220);
x_69 = x_222;
x_70 = x_223;
x_71 = x_229;
x_72 = x_231;
x_73 = x_232;
x_74 = x_234;
x_75 = x_226;
x_76 = x_225;
x_77 = x_227;
x_78 = x_228;
x_79 = x_233;
x_80 = x_230;
x_81 = lean_box(0);
x_82 = x_221;
x_83 = x_224;
x_84 = x_236;
x_85 = x_237;
x_86 = x_235;
x_87 = x_244;
goto block_216;
}
else
{
lean_object* x_245; 
x_245 = l_Lean_PersistentArray_get_x21___redArg(x_220, x_241, x_222);
x_69 = x_222;
x_70 = x_223;
x_71 = x_229;
x_72 = x_231;
x_73 = x_232;
x_74 = x_234;
x_75 = x_226;
x_76 = x_225;
x_77 = x_227;
x_78 = x_228;
x_79 = x_233;
x_80 = x_230;
x_81 = lean_box(0);
x_82 = x_221;
x_83 = x_224;
x_84 = x_236;
x_85 = x_237;
x_86 = x_235;
x_87 = x_245;
goto block_216;
}
}
else
{
uint8_t x_246; 
lean_dec(x_237);
lean_dec_ref(x_236);
lean_dec(x_235);
lean_dec_ref(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec_ref(x_231);
lean_dec(x_230);
lean_dec(x_229);
lean_dec_ref(x_228);
lean_dec_ref(x_227);
lean_dec(x_226);
lean_dec_ref(x_225);
lean_dec(x_224);
lean_dec_ref(x_223);
lean_dec(x_222);
lean_dec_ref(x_221);
x_246 = !lean_is_exclusive(x_239);
if (x_246 == 0)
{
return x_239;
}
else
{
lean_object* x_247; lean_object* x_248; 
x_247 = lean_ctor_get(x_239, 0);
lean_inc(x_247);
lean_dec(x_239);
x_248 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_248, 0, x_247);
return x_248;
}
}
}
block_311:
{
lean_object* x_260; lean_object* x_261; 
x_260 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc_ref(x_257);
x_261 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(x_260, x_250, x_251, x_252, x_253, x_254, x_255, x_256, x_257, x_258);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; 
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
lean_dec_ref(x_261);
x_263 = lean_ctor_get(x_262, 0);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_263);
x_265 = l_Int_Linear_Poly_isUnsatDvd(x_263, x_264);
if (x_265 == 0)
{
uint8_t x_266; 
x_266 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_262);
if (x_266 == 0)
{
if (lean_obj_tag(x_264) == 1)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
lean_inc_ref(x_264);
lean_inc(x_263);
x_267 = lean_ctor_get(x_264, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_264, 1);
lean_inc(x_268);
x_269 = lean_ctor_get(x_264, 2);
lean_inc_ref(x_269);
lean_inc(x_262);
x_270 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_262, x_250, x_257);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; uint8_t x_274; uint8_t x_275; uint8_t x_276; 
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
lean_dec_ref(x_270);
lean_inc(x_268);
x_272 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed), 2, 1);
lean_closure_set(x_272, 0, x_268);
lean_inc(x_268);
lean_inc(x_262);
x_273 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed), 3, 2);
lean_closure_set(x_273, 0, x_262);
lean_closure_set(x_273, 1, x_268);
x_274 = 0;
x_275 = lean_unbox(x_271);
lean_dec(x_271);
x_276 = l_Lean_instBEqLBool_beq(x_275, x_274);
if (x_276 == 0)
{
x_221 = x_269;
x_222 = x_268;
x_223 = x_264;
x_224 = x_263;
x_225 = x_272;
x_226 = x_267;
x_227 = x_273;
x_228 = x_262;
x_229 = x_250;
x_230 = x_251;
x_231 = x_252;
x_232 = x_253;
x_233 = x_254;
x_234 = x_255;
x_235 = x_256;
x_236 = x_257;
x_237 = x_258;
x_238 = lean_box(0);
goto block_249;
}
else
{
lean_object* x_277; 
lean_inc(x_268);
x_277 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_268, x_250);
if (lean_obj_tag(x_277) == 0)
{
lean_dec_ref(x_277);
x_221 = x_269;
x_222 = x_268;
x_223 = x_264;
x_224 = x_263;
x_225 = x_272;
x_226 = x_267;
x_227 = x_273;
x_228 = x_262;
x_229 = x_250;
x_230 = x_251;
x_231 = x_252;
x_232 = x_253;
x_233 = x_254;
x_234 = x_255;
x_235 = x_256;
x_236 = x_257;
x_237 = x_258;
x_238 = lean_box(0);
goto block_249;
}
else
{
lean_dec_ref(x_273);
lean_dec_ref(x_272);
lean_dec_ref(x_269);
lean_dec(x_268);
lean_dec(x_267);
lean_dec_ref(x_264);
lean_dec(x_263);
lean_dec(x_262);
lean_dec(x_258);
lean_dec_ref(x_257);
lean_dec(x_256);
lean_dec_ref(x_255);
lean_dec(x_254);
lean_dec(x_253);
lean_dec_ref(x_252);
lean_dec(x_251);
lean_dec(x_250);
return x_277;
}
}
}
else
{
uint8_t x_278; 
lean_dec_ref(x_269);
lean_dec(x_268);
lean_dec(x_267);
lean_dec_ref(x_264);
lean_dec(x_263);
lean_dec(x_262);
lean_dec(x_258);
lean_dec_ref(x_257);
lean_dec(x_256);
lean_dec_ref(x_255);
lean_dec(x_254);
lean_dec(x_253);
lean_dec_ref(x_252);
lean_dec(x_251);
lean_dec(x_250);
x_278 = !lean_is_exclusive(x_270);
if (x_278 == 0)
{
return x_270;
}
else
{
lean_object* x_279; lean_object* x_280; 
x_279 = lean_ctor_get(x_270, 0);
lean_inc(x_279);
lean_dec(x_270);
x_280 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_280, 0, x_279);
return x_280;
}
}
}
else
{
lean_object* x_281; 
x_281 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_262, x_250, x_251, x_252, x_253, x_254, x_255, x_256, x_257, x_258);
lean_dec(x_258);
lean_dec_ref(x_257);
lean_dec(x_256);
lean_dec_ref(x_255);
lean_dec(x_254);
lean_dec(x_253);
lean_dec_ref(x_252);
lean_dec(x_251);
lean_dec(x_250);
return x_281;
}
}
else
{
lean_object* x_282; lean_object* x_283; 
lean_dec(x_254);
lean_dec(x_253);
lean_dec_ref(x_252);
lean_dec(x_251);
x_282 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5;
x_283 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_282, x_257);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; uint8_t x_285; 
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
lean_dec_ref(x_283);
x_285 = lean_unbox(x_284);
lean_dec(x_284);
if (x_285 == 0)
{
lean_dec(x_262);
lean_dec(x_258);
lean_dec_ref(x_257);
lean_dec(x_256);
lean_dec_ref(x_255);
lean_dec(x_250);
x_43 = lean_box(0);
goto block_46;
}
else
{
lean_object* x_286; 
x_286 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_262, x_250, x_257);
lean_dec(x_250);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; lean_object* x_288; 
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
lean_dec_ref(x_286);
x_288 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_282, x_287, x_255, x_256, x_257, x_258);
lean_dec(x_258);
lean_dec_ref(x_257);
lean_dec(x_256);
lean_dec_ref(x_255);
if (lean_obj_tag(x_288) == 0)
{
lean_dec_ref(x_288);
x_43 = lean_box(0);
goto block_46;
}
else
{
return x_288;
}
}
else
{
uint8_t x_289; 
lean_dec(x_258);
lean_dec_ref(x_257);
lean_dec(x_256);
lean_dec_ref(x_255);
x_289 = !lean_is_exclusive(x_286);
if (x_289 == 0)
{
return x_286;
}
else
{
lean_object* x_290; lean_object* x_291; 
x_290 = lean_ctor_get(x_286, 0);
lean_inc(x_290);
lean_dec(x_286);
x_291 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_291, 0, x_290);
return x_291;
}
}
}
}
else
{
uint8_t x_292; 
lean_dec(x_262);
lean_dec(x_258);
lean_dec_ref(x_257);
lean_dec(x_256);
lean_dec_ref(x_255);
lean_dec(x_250);
x_292 = !lean_is_exclusive(x_283);
if (x_292 == 0)
{
return x_283;
}
else
{
lean_object* x_293; lean_object* x_294; 
x_293 = lean_ctor_get(x_283, 0);
lean_inc(x_293);
lean_dec(x_283);
x_294 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_294, 0, x_293);
return x_294;
}
}
}
}
else
{
lean_object* x_295; lean_object* x_296; 
x_295 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7;
x_296 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_295, x_257);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; uint8_t x_298; 
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
lean_dec_ref(x_296);
x_298 = lean_unbox(x_297);
lean_dec(x_297);
if (x_298 == 0)
{
x_12 = x_262;
x_13 = x_250;
x_14 = x_251;
x_15 = x_252;
x_16 = x_253;
x_17 = x_254;
x_18 = x_255;
x_19 = x_256;
x_20 = x_257;
x_21 = x_258;
x_22 = lean_box(0);
goto block_30;
}
else
{
lean_object* x_299; 
lean_inc(x_262);
x_299 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_262, x_250, x_257);
if (lean_obj_tag(x_299) == 0)
{
lean_object* x_300; lean_object* x_301; 
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
lean_dec_ref(x_299);
x_301 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_295, x_300, x_255, x_256, x_257, x_258);
if (lean_obj_tag(x_301) == 0)
{
lean_dec_ref(x_301);
x_12 = x_262;
x_13 = x_250;
x_14 = x_251;
x_15 = x_252;
x_16 = x_253;
x_17 = x_254;
x_18 = x_255;
x_19 = x_256;
x_20 = x_257;
x_21 = x_258;
x_22 = lean_box(0);
goto block_30;
}
else
{
lean_dec(x_262);
lean_dec(x_258);
lean_dec_ref(x_257);
lean_dec(x_256);
lean_dec_ref(x_255);
lean_dec(x_254);
lean_dec(x_253);
lean_dec_ref(x_252);
lean_dec(x_251);
lean_dec(x_250);
return x_301;
}
}
else
{
uint8_t x_302; 
lean_dec(x_262);
lean_dec(x_258);
lean_dec_ref(x_257);
lean_dec(x_256);
lean_dec_ref(x_255);
lean_dec(x_254);
lean_dec(x_253);
lean_dec_ref(x_252);
lean_dec(x_251);
lean_dec(x_250);
x_302 = !lean_is_exclusive(x_299);
if (x_302 == 0)
{
return x_299;
}
else
{
lean_object* x_303; lean_object* x_304; 
x_303 = lean_ctor_get(x_299, 0);
lean_inc(x_303);
lean_dec(x_299);
x_304 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_304, 0, x_303);
return x_304;
}
}
}
}
else
{
uint8_t x_305; 
lean_dec(x_262);
lean_dec(x_258);
lean_dec_ref(x_257);
lean_dec(x_256);
lean_dec_ref(x_255);
lean_dec(x_254);
lean_dec(x_253);
lean_dec_ref(x_252);
lean_dec(x_251);
lean_dec(x_250);
x_305 = !lean_is_exclusive(x_296);
if (x_305 == 0)
{
return x_296;
}
else
{
lean_object* x_306; lean_object* x_307; 
x_306 = lean_ctor_get(x_296, 0);
lean_inc(x_306);
lean_dec(x_296);
x_307 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_307, 0, x_306);
return x_307;
}
}
}
}
else
{
uint8_t x_308; 
lean_dec(x_258);
lean_dec_ref(x_257);
lean_dec(x_256);
lean_dec_ref(x_255);
lean_dec(x_254);
lean_dec(x_253);
lean_dec_ref(x_252);
lean_dec(x_251);
lean_dec(x_250);
x_308 = !lean_is_exclusive(x_261);
if (x_308 == 0)
{
return x_261;
}
else
{
lean_object* x_309; lean_object* x_310; 
x_309 = lean_ctor_get(x_261, 0);
lean_inc(x_309);
lean_dec(x_261);
x_310 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_310, 0, x_309);
return x_310;
}
}
}
}
else
{
uint8_t x_319; 
lean_dec_ref(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_319 = !lean_is_exclusive(x_218);
if (x_319 == 0)
{
return x_218;
}
else
{
lean_object* x_320; lean_object* x_321; 
x_320 = lean_ctor_get(x_218, 0);
lean_inc(x_320);
lean_dec(x_218);
x_321 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_321, 0, x_320);
return x_321;
}
}
block_216:
{
if (lean_obj_tag(x_87) == 1)
{
lean_object* x_88; lean_object* x_89; 
lean_dec_ref(x_77);
lean_dec_ref(x_70);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
lean_dec_ref(x_87);
x_89 = lean_ctor_get(x_88, 1);
lean_inc_ref(x_89);
if (lean_obj_tag(x_89) == 1)
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_91 = lean_ctor_get(x_88, 0);
x_92 = lean_ctor_get(x_89, 0);
x_93 = lean_ctor_get(x_89, 2);
x_94 = lean_ctor_get(x_89, 1);
lean_dec(x_94);
x_95 = lean_int_mul(x_75, x_91);
x_96 = lean_int_mul(x_92, x_83);
x_97 = l_Lean_Meta_Grind_Arith_gcdExt(x_95, x_96);
lean_dec(x_96);
lean_dec(x_95);
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
lean_object* x_99; uint8_t x_100; 
x_99 = lean_ctor_get(x_97, 1);
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_101 = lean_ctor_get(x_97, 0);
x_102 = lean_ctor_get(x_99, 0);
x_103 = lean_ctor_get(x_99, 1);
x_104 = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
x_105 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_104, x_76, x_71);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec_ref(x_105);
x_106 = lean_int_mul(x_102, x_91);
lean_dec(x_102);
lean_inc_ref(x_82);
x_107 = l_Int_Linear_Poly_mul(x_82, x_106);
lean_dec(x_106);
x_108 = lean_int_mul(x_103, x_83);
lean_dec(x_103);
lean_inc_ref(x_93);
x_109 = l_Int_Linear_Poly_mul(x_93, x_108);
lean_dec(x_108);
x_110 = lean_int_mul(x_83, x_91);
lean_dec(x_83);
x_111 = l_Int_Linear_Poly_combine(x_107, x_109);
lean_inc(x_101);
lean_ctor_set(x_89, 2, x_111);
lean_ctor_set(x_89, 1, x_69);
lean_ctor_set(x_89, 0, x_101);
lean_inc(x_88);
lean_inc_ref(x_78);
lean_ctor_set_tag(x_99, 4);
lean_ctor_set(x_99, 1, x_88);
lean_ctor_set(x_99, 0, x_78);
x_112 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_89);
lean_ctor_set(x_112, 2, x_99);
lean_inc(x_85);
lean_inc_ref(x_84);
lean_inc(x_86);
lean_inc_ref(x_74);
lean_inc(x_79);
lean_inc(x_73);
lean_inc_ref(x_72);
lean_inc(x_80);
lean_inc(x_71);
x_113 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_112, x_71, x_80, x_72, x_73, x_79, x_74, x_86, x_84, x_85);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
lean_dec_ref(x_113);
x_114 = l_Int_Linear_Poly_mul(x_82, x_92);
lean_dec(x_92);
x_115 = lean_int_neg(x_75);
lean_dec(x_75);
x_116 = l_Int_Linear_Poly_mul(x_93, x_115);
lean_dec(x_115);
x_117 = l_Int_Linear_Poly_combine(x_114, x_116);
lean_inc(x_88);
lean_ctor_set_tag(x_97, 5);
lean_ctor_set(x_97, 1, x_88);
lean_ctor_set(x_97, 0, x_78);
x_118 = !lean_is_exclusive(x_88);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_88, 2);
lean_dec(x_119);
x_120 = lean_ctor_get(x_88, 1);
lean_dec(x_120);
x_121 = lean_ctor_get(x_88, 0);
lean_dec(x_121);
lean_ctor_set(x_88, 2, x_97);
lean_ctor_set(x_88, 1, x_117);
lean_ctor_set(x_88, 0, x_101);
x_1 = x_88;
x_2 = x_71;
x_3 = x_80;
x_4 = x_72;
x_5 = x_73;
x_6 = x_79;
x_7 = x_74;
x_8 = x_86;
x_9 = x_84;
x_10 = x_85;
goto _start;
}
else
{
lean_object* x_123; 
lean_dec(x_88);
x_123 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_123, 0, x_101);
lean_ctor_set(x_123, 1, x_117);
lean_ctor_set(x_123, 2, x_97);
x_1 = x_123;
x_2 = x_71;
x_3 = x_80;
x_4 = x_72;
x_5 = x_73;
x_6 = x_79;
x_7 = x_74;
x_8 = x_86;
x_9 = x_84;
x_10 = x_85;
goto _start;
}
}
else
{
lean_free_object(x_97);
lean_dec(x_101);
lean_dec_ref(x_93);
lean_dec(x_92);
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_85);
lean_dec_ref(x_84);
lean_dec_ref(x_82);
lean_dec(x_80);
lean_dec(x_79);
lean_dec_ref(x_78);
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec_ref(x_72);
lean_dec(x_71);
return x_113;
}
}
else
{
lean_free_object(x_99);
lean_dec(x_103);
lean_dec(x_102);
lean_free_object(x_97);
lean_dec(x_101);
lean_free_object(x_89);
lean_dec_ref(x_93);
lean_dec(x_92);
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_85);
lean_dec_ref(x_84);
lean_dec(x_83);
lean_dec_ref(x_82);
lean_dec(x_80);
lean_dec(x_79);
lean_dec_ref(x_78);
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec_ref(x_72);
lean_dec(x_71);
lean_dec(x_69);
return x_105;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_125 = lean_ctor_get(x_97, 0);
x_126 = lean_ctor_get(x_99, 0);
x_127 = lean_ctor_get(x_99, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_99);
x_128 = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
x_129 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_128, x_76, x_71);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec_ref(x_129);
x_130 = lean_int_mul(x_126, x_91);
lean_dec(x_126);
lean_inc_ref(x_82);
x_131 = l_Int_Linear_Poly_mul(x_82, x_130);
lean_dec(x_130);
x_132 = lean_int_mul(x_127, x_83);
lean_dec(x_127);
lean_inc_ref(x_93);
x_133 = l_Int_Linear_Poly_mul(x_93, x_132);
lean_dec(x_132);
x_134 = lean_int_mul(x_83, x_91);
lean_dec(x_83);
x_135 = l_Int_Linear_Poly_combine(x_131, x_133);
lean_inc(x_125);
lean_ctor_set(x_89, 2, x_135);
lean_ctor_set(x_89, 1, x_69);
lean_ctor_set(x_89, 0, x_125);
lean_inc(x_88);
lean_inc_ref(x_78);
x_136 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_136, 0, x_78);
lean_ctor_set(x_136, 1, x_88);
x_137 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_89);
lean_ctor_set(x_137, 2, x_136);
lean_inc(x_85);
lean_inc_ref(x_84);
lean_inc(x_86);
lean_inc_ref(x_74);
lean_inc(x_79);
lean_inc(x_73);
lean_inc_ref(x_72);
lean_inc(x_80);
lean_inc(x_71);
x_138 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_137, x_71, x_80, x_72, x_73, x_79, x_74, x_86, x_84, x_85);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec_ref(x_138);
x_139 = l_Int_Linear_Poly_mul(x_82, x_92);
lean_dec(x_92);
x_140 = lean_int_neg(x_75);
lean_dec(x_75);
x_141 = l_Int_Linear_Poly_mul(x_93, x_140);
lean_dec(x_140);
x_142 = l_Int_Linear_Poly_combine(x_139, x_141);
lean_inc(x_88);
lean_ctor_set_tag(x_97, 5);
lean_ctor_set(x_97, 1, x_88);
lean_ctor_set(x_97, 0, x_78);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 lean_ctor_release(x_88, 2);
 x_143 = x_88;
} else {
 lean_dec_ref(x_88);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(0, 3, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_125);
lean_ctor_set(x_144, 1, x_142);
lean_ctor_set(x_144, 2, x_97);
x_1 = x_144;
x_2 = x_71;
x_3 = x_80;
x_4 = x_72;
x_5 = x_73;
x_6 = x_79;
x_7 = x_74;
x_8 = x_86;
x_9 = x_84;
x_10 = x_85;
goto _start;
}
else
{
lean_free_object(x_97);
lean_dec(x_125);
lean_dec_ref(x_93);
lean_dec(x_92);
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_85);
lean_dec_ref(x_84);
lean_dec_ref(x_82);
lean_dec(x_80);
lean_dec(x_79);
lean_dec_ref(x_78);
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec_ref(x_72);
lean_dec(x_71);
return x_138;
}
}
else
{
lean_dec(x_127);
lean_dec(x_126);
lean_free_object(x_97);
lean_dec(x_125);
lean_free_object(x_89);
lean_dec_ref(x_93);
lean_dec(x_92);
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_85);
lean_dec_ref(x_84);
lean_dec(x_83);
lean_dec_ref(x_82);
lean_dec(x_80);
lean_dec(x_79);
lean_dec_ref(x_78);
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec_ref(x_72);
lean_dec(x_71);
lean_dec(x_69);
return x_129;
}
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_146 = lean_ctor_get(x_97, 1);
x_147 = lean_ctor_get(x_97, 0);
lean_inc(x_146);
lean_inc(x_147);
lean_dec(x_97);
x_148 = lean_ctor_get(x_146, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_146, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_150 = x_146;
} else {
 lean_dec_ref(x_146);
 x_150 = lean_box(0);
}
x_151 = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
x_152 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_151, x_76, x_71);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec_ref(x_152);
x_153 = lean_int_mul(x_148, x_91);
lean_dec(x_148);
lean_inc_ref(x_82);
x_154 = l_Int_Linear_Poly_mul(x_82, x_153);
lean_dec(x_153);
x_155 = lean_int_mul(x_149, x_83);
lean_dec(x_149);
lean_inc_ref(x_93);
x_156 = l_Int_Linear_Poly_mul(x_93, x_155);
lean_dec(x_155);
x_157 = lean_int_mul(x_83, x_91);
lean_dec(x_83);
x_158 = l_Int_Linear_Poly_combine(x_154, x_156);
lean_inc(x_147);
lean_ctor_set(x_89, 2, x_158);
lean_ctor_set(x_89, 1, x_69);
lean_ctor_set(x_89, 0, x_147);
lean_inc(x_88);
lean_inc_ref(x_78);
if (lean_is_scalar(x_150)) {
 x_159 = lean_alloc_ctor(4, 2, 0);
} else {
 x_159 = x_150;
 lean_ctor_set_tag(x_159, 4);
}
lean_ctor_set(x_159, 0, x_78);
lean_ctor_set(x_159, 1, x_88);
x_160 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_89);
lean_ctor_set(x_160, 2, x_159);
lean_inc(x_85);
lean_inc_ref(x_84);
lean_inc(x_86);
lean_inc_ref(x_74);
lean_inc(x_79);
lean_inc(x_73);
lean_inc_ref(x_72);
lean_inc(x_80);
lean_inc(x_71);
x_161 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_160, x_71, x_80, x_72, x_73, x_79, x_74, x_86, x_84, x_85);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec_ref(x_161);
x_162 = l_Int_Linear_Poly_mul(x_82, x_92);
lean_dec(x_92);
x_163 = lean_int_neg(x_75);
lean_dec(x_75);
x_164 = l_Int_Linear_Poly_mul(x_93, x_163);
lean_dec(x_163);
x_165 = l_Int_Linear_Poly_combine(x_162, x_164);
lean_inc(x_88);
x_166 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_166, 0, x_78);
lean_ctor_set(x_166, 1, x_88);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 lean_ctor_release(x_88, 2);
 x_167 = x_88;
} else {
 lean_dec_ref(x_88);
 x_167 = lean_box(0);
}
if (lean_is_scalar(x_167)) {
 x_168 = lean_alloc_ctor(0, 3, 0);
} else {
 x_168 = x_167;
}
lean_ctor_set(x_168, 0, x_147);
lean_ctor_set(x_168, 1, x_165);
lean_ctor_set(x_168, 2, x_166);
x_1 = x_168;
x_2 = x_71;
x_3 = x_80;
x_4 = x_72;
x_5 = x_73;
x_6 = x_79;
x_7 = x_74;
x_8 = x_86;
x_9 = x_84;
x_10 = x_85;
goto _start;
}
else
{
lean_dec(x_147);
lean_dec_ref(x_93);
lean_dec(x_92);
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_85);
lean_dec_ref(x_84);
lean_dec_ref(x_82);
lean_dec(x_80);
lean_dec(x_79);
lean_dec_ref(x_78);
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec_ref(x_72);
lean_dec(x_71);
return x_161;
}
}
else
{
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_free_object(x_89);
lean_dec_ref(x_93);
lean_dec(x_92);
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_85);
lean_dec_ref(x_84);
lean_dec(x_83);
lean_dec_ref(x_82);
lean_dec(x_80);
lean_dec(x_79);
lean_dec_ref(x_78);
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec_ref(x_72);
lean_dec(x_71);
lean_dec(x_69);
return x_152;
}
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_170 = lean_ctor_get(x_88, 0);
x_171 = lean_ctor_get(x_89, 0);
x_172 = lean_ctor_get(x_89, 2);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_89);
x_173 = lean_int_mul(x_75, x_170);
x_174 = lean_int_mul(x_171, x_83);
x_175 = l_Lean_Meta_Grind_Arith_gcdExt(x_173, x_174);
lean_dec(x_174);
lean_dec(x_173);
x_176 = lean_ctor_get(x_175, 1);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 0);
lean_inc(x_177);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_178 = x_175;
} else {
 lean_dec_ref(x_175);
 x_178 = lean_box(0);
}
x_179 = lean_ctor_get(x_176, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_176, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_181 = x_176;
} else {
 lean_dec_ref(x_176);
 x_181 = lean_box(0);
}
x_182 = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
x_183 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_182, x_76, x_71);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec_ref(x_183);
x_184 = lean_int_mul(x_179, x_170);
lean_dec(x_179);
lean_inc_ref(x_82);
x_185 = l_Int_Linear_Poly_mul(x_82, x_184);
lean_dec(x_184);
x_186 = lean_int_mul(x_180, x_83);
lean_dec(x_180);
lean_inc_ref(x_172);
x_187 = l_Int_Linear_Poly_mul(x_172, x_186);
lean_dec(x_186);
x_188 = lean_int_mul(x_83, x_170);
lean_dec(x_83);
x_189 = l_Int_Linear_Poly_combine(x_185, x_187);
lean_inc(x_177);
x_190 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_190, 0, x_177);
lean_ctor_set(x_190, 1, x_69);
lean_ctor_set(x_190, 2, x_189);
lean_inc(x_88);
lean_inc_ref(x_78);
if (lean_is_scalar(x_181)) {
 x_191 = lean_alloc_ctor(4, 2, 0);
} else {
 x_191 = x_181;
 lean_ctor_set_tag(x_191, 4);
}
lean_ctor_set(x_191, 0, x_78);
lean_ctor_set(x_191, 1, x_88);
x_192 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_192, 0, x_188);
lean_ctor_set(x_192, 1, x_190);
lean_ctor_set(x_192, 2, x_191);
lean_inc(x_85);
lean_inc_ref(x_84);
lean_inc(x_86);
lean_inc_ref(x_74);
lean_inc(x_79);
lean_inc(x_73);
lean_inc_ref(x_72);
lean_inc(x_80);
lean_inc(x_71);
x_193 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_192, x_71, x_80, x_72, x_73, x_79, x_74, x_86, x_84, x_85);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec_ref(x_193);
x_194 = l_Int_Linear_Poly_mul(x_82, x_171);
lean_dec(x_171);
x_195 = lean_int_neg(x_75);
lean_dec(x_75);
x_196 = l_Int_Linear_Poly_mul(x_172, x_195);
lean_dec(x_195);
x_197 = l_Int_Linear_Poly_combine(x_194, x_196);
lean_inc(x_88);
if (lean_is_scalar(x_178)) {
 x_198 = lean_alloc_ctor(5, 2, 0);
} else {
 x_198 = x_178;
 lean_ctor_set_tag(x_198, 5);
}
lean_ctor_set(x_198, 0, x_78);
lean_ctor_set(x_198, 1, x_88);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 lean_ctor_release(x_88, 2);
 x_199 = x_88;
} else {
 lean_dec_ref(x_88);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(0, 3, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_177);
lean_ctor_set(x_200, 1, x_197);
lean_ctor_set(x_200, 2, x_198);
x_1 = x_200;
x_2 = x_71;
x_3 = x_80;
x_4 = x_72;
x_5 = x_73;
x_6 = x_79;
x_7 = x_74;
x_8 = x_86;
x_9 = x_84;
x_10 = x_85;
goto _start;
}
else
{
lean_dec(x_178);
lean_dec(x_177);
lean_dec_ref(x_172);
lean_dec(x_171);
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_85);
lean_dec_ref(x_84);
lean_dec_ref(x_82);
lean_dec(x_80);
lean_dec(x_79);
lean_dec_ref(x_78);
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec_ref(x_72);
lean_dec(x_71);
return x_193;
}
}
else
{
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_179);
lean_dec(x_178);
lean_dec(x_177);
lean_dec_ref(x_172);
lean_dec(x_171);
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_85);
lean_dec_ref(x_84);
lean_dec(x_83);
lean_dec_ref(x_82);
lean_dec(x_80);
lean_dec(x_79);
lean_dec_ref(x_78);
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec_ref(x_72);
lean_dec(x_71);
lean_dec(x_69);
return x_183;
}
}
}
else
{
lean_object* x_202; 
lean_dec_ref(x_89);
lean_dec(x_83);
lean_dec_ref(x_82);
lean_dec_ref(x_78);
lean_dec_ref(x_76);
lean_dec(x_75);
lean_dec(x_69);
x_202 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_88, x_71, x_80, x_72, x_73, x_79, x_74, x_86, x_84, x_85);
lean_dec(x_85);
lean_dec_ref(x_84);
lean_dec(x_86);
lean_dec_ref(x_74);
lean_dec(x_79);
lean_dec(x_73);
lean_dec_ref(x_72);
lean_dec(x_80);
lean_dec(x_71);
return x_202;
}
}
else
{
lean_object* x_203; lean_object* x_204; 
lean_dec(x_87);
lean_dec(x_83);
lean_dec_ref(x_82);
lean_dec(x_80);
lean_dec(x_79);
lean_dec_ref(x_76);
lean_dec(x_75);
lean_dec(x_73);
lean_dec_ref(x_72);
lean_dec(x_69);
x_203 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2;
x_204 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_203, x_84);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; uint8_t x_206; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
lean_dec_ref(x_204);
x_206 = lean_unbox(x_205);
lean_dec(x_205);
if (x_206 == 0)
{
lean_dec_ref(x_78);
x_31 = x_70;
x_32 = x_77;
x_33 = x_71;
x_34 = x_74;
x_35 = x_86;
x_36 = x_84;
x_37 = x_85;
x_38 = lean_box(0);
goto block_42;
}
else
{
lean_object* x_207; 
x_207 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_78, x_71, x_84);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
lean_dec_ref(x_207);
x_209 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_203, x_208, x_74, x_86, x_84, x_85);
if (lean_obj_tag(x_209) == 0)
{
lean_dec_ref(x_209);
x_31 = x_70;
x_32 = x_77;
x_33 = x_71;
x_34 = x_74;
x_35 = x_86;
x_36 = x_84;
x_37 = x_85;
x_38 = lean_box(0);
goto block_42;
}
else
{
lean_dec(x_86);
lean_dec(x_85);
lean_dec_ref(x_84);
lean_dec_ref(x_77);
lean_dec_ref(x_74);
lean_dec(x_71);
lean_dec_ref(x_70);
return x_209;
}
}
else
{
uint8_t x_210; 
lean_dec(x_86);
lean_dec(x_85);
lean_dec_ref(x_84);
lean_dec_ref(x_77);
lean_dec_ref(x_74);
lean_dec(x_71);
lean_dec_ref(x_70);
x_210 = !lean_is_exclusive(x_207);
if (x_210 == 0)
{
return x_207;
}
else
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_ctor_get(x_207, 0);
lean_inc(x_211);
lean_dec(x_207);
x_212 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_212, 0, x_211);
return x_212;
}
}
}
}
else
{
uint8_t x_213; 
lean_dec(x_86);
lean_dec(x_85);
lean_dec_ref(x_84);
lean_dec_ref(x_78);
lean_dec_ref(x_77);
lean_dec_ref(x_74);
lean_dec(x_71);
lean_dec_ref(x_70);
x_213 = !lean_is_exclusive(x_204);
if (x_213 == 0)
{
return x_204;
}
else
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_ctor_get(x_204, 0);
lean_inc(x_214);
lean_dec(x_204);
x_215 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_215, 0, x_214);
return x_215;
}
}
}
}
}
else
{
lean_object* x_322; 
lean_dec_ref(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_322 = lean_box(0);
lean_ctor_set(x_65, 0, x_322);
return x_65;
}
}
else
{
lean_object* x_323; uint8_t x_324; 
x_323 = lean_ctor_get(x_65, 0);
lean_inc(x_323);
lean_dec(x_65);
x_324 = lean_unbox(x_323);
lean_dec(x_323);
if (x_324 == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_394; lean_object* x_395; 
x_394 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3;
x_395 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_394, x_9);
if (lean_obj_tag(x_395) == 0)
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; uint8_t x_489; 
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
lean_dec_ref(x_395);
x_397 = lean_box(0);
x_489 = lean_unbox(x_396);
lean_dec(x_396);
if (x_489 == 0)
{
x_427 = x_2;
x_428 = x_3;
x_429 = x_4;
x_430 = x_5;
x_431 = x_6;
x_432 = x_7;
x_433 = x_8;
x_434 = x_9;
x_435 = x_10;
x_436 = lean_box(0);
goto block_488;
}
else
{
lean_object* x_490; 
lean_inc_ref(x_1);
x_490 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_9);
if (lean_obj_tag(x_490) == 0)
{
lean_object* x_491; lean_object* x_492; 
x_491 = lean_ctor_get(x_490, 0);
lean_inc(x_491);
lean_dec_ref(x_490);
x_492 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_394, x_491, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_492) == 0)
{
lean_dec_ref(x_492);
x_427 = x_2;
x_428 = x_3;
x_429 = x_4;
x_430 = x_5;
x_431 = x_6;
x_432 = x_7;
x_433 = x_8;
x_434 = x_9;
x_435 = x_10;
x_436 = lean_box(0);
goto block_488;
}
else
{
lean_dec_ref(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_492;
}
}
else
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; 
lean_dec_ref(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_493 = lean_ctor_get(x_490, 0);
lean_inc(x_493);
if (lean_is_exclusive(x_490)) {
 lean_ctor_release(x_490, 0);
 x_494 = x_490;
} else {
 lean_dec_ref(x_490);
 x_494 = lean_box(0);
}
if (lean_is_scalar(x_494)) {
 x_495 = lean_alloc_ctor(1, 1, 0);
} else {
 x_495 = x_494;
}
lean_ctor_set(x_495, 0, x_493);
return x_495;
}
}
block_426:
{
lean_object* x_416; 
x_416 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_406, x_413);
if (lean_obj_tag(x_416) == 0)
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; uint8_t x_420; 
x_417 = lean_ctor_get(x_416, 0);
lean_inc(x_417);
lean_dec_ref(x_416);
x_418 = lean_ctor_get(x_417, 6);
lean_inc_ref(x_418);
lean_dec(x_417);
x_419 = lean_ctor_get(x_418, 2);
x_420 = lean_nat_dec_lt(x_399, x_419);
if (x_420 == 0)
{
lean_object* x_421; 
lean_dec_ref(x_418);
x_421 = l_outOfBounds___redArg(x_397);
x_325 = x_399;
x_326 = x_400;
x_327 = x_406;
x_328 = x_408;
x_329 = x_409;
x_330 = x_411;
x_331 = x_403;
x_332 = x_402;
x_333 = x_404;
x_334 = x_405;
x_335 = x_410;
x_336 = x_407;
x_337 = lean_box(0);
x_338 = x_398;
x_339 = x_401;
x_340 = x_413;
x_341 = x_414;
x_342 = x_412;
x_343 = x_421;
goto block_393;
}
else
{
lean_object* x_422; 
x_422 = l_Lean_PersistentArray_get_x21___redArg(x_397, x_418, x_399);
x_325 = x_399;
x_326 = x_400;
x_327 = x_406;
x_328 = x_408;
x_329 = x_409;
x_330 = x_411;
x_331 = x_403;
x_332 = x_402;
x_333 = x_404;
x_334 = x_405;
x_335 = x_410;
x_336 = x_407;
x_337 = lean_box(0);
x_338 = x_398;
x_339 = x_401;
x_340 = x_413;
x_341 = x_414;
x_342 = x_412;
x_343 = x_422;
goto block_393;
}
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; 
lean_dec(x_414);
lean_dec_ref(x_413);
lean_dec(x_412);
lean_dec_ref(x_411);
lean_dec(x_410);
lean_dec(x_409);
lean_dec_ref(x_408);
lean_dec(x_407);
lean_dec(x_406);
lean_dec_ref(x_405);
lean_dec_ref(x_404);
lean_dec(x_403);
lean_dec_ref(x_402);
lean_dec(x_401);
lean_dec_ref(x_400);
lean_dec(x_399);
lean_dec_ref(x_398);
x_423 = lean_ctor_get(x_416, 0);
lean_inc(x_423);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 x_424 = x_416;
} else {
 lean_dec_ref(x_416);
 x_424 = lean_box(0);
}
if (lean_is_scalar(x_424)) {
 x_425 = lean_alloc_ctor(1, 1, 0);
} else {
 x_425 = x_424;
}
lean_ctor_set(x_425, 0, x_423);
return x_425;
}
}
block_488:
{
lean_object* x_437; lean_object* x_438; 
x_437 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc_ref(x_434);
x_438 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(x_437, x_427, x_428, x_429, x_430, x_431, x_432, x_433, x_434, x_435);
if (lean_obj_tag(x_438) == 0)
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; uint8_t x_442; 
x_439 = lean_ctor_get(x_438, 0);
lean_inc(x_439);
lean_dec_ref(x_438);
x_440 = lean_ctor_get(x_439, 0);
x_441 = lean_ctor_get(x_439, 1);
lean_inc(x_440);
x_442 = l_Int_Linear_Poly_isUnsatDvd(x_440, x_441);
if (x_442 == 0)
{
uint8_t x_443; 
x_443 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_439);
if (x_443 == 0)
{
if (lean_obj_tag(x_441) == 1)
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; 
lean_inc_ref(x_441);
lean_inc(x_440);
x_444 = lean_ctor_get(x_441, 0);
lean_inc(x_444);
x_445 = lean_ctor_get(x_441, 1);
lean_inc(x_445);
x_446 = lean_ctor_get(x_441, 2);
lean_inc_ref(x_446);
lean_inc(x_439);
x_447 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_439, x_427, x_434);
if (lean_obj_tag(x_447) == 0)
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; uint8_t x_451; uint8_t x_452; uint8_t x_453; 
x_448 = lean_ctor_get(x_447, 0);
lean_inc(x_448);
lean_dec_ref(x_447);
lean_inc(x_445);
x_449 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed), 2, 1);
lean_closure_set(x_449, 0, x_445);
lean_inc(x_445);
lean_inc(x_439);
x_450 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed), 3, 2);
lean_closure_set(x_450, 0, x_439);
lean_closure_set(x_450, 1, x_445);
x_451 = 0;
x_452 = lean_unbox(x_448);
lean_dec(x_448);
x_453 = l_Lean_instBEqLBool_beq(x_452, x_451);
if (x_453 == 0)
{
x_398 = x_446;
x_399 = x_445;
x_400 = x_441;
x_401 = x_440;
x_402 = x_449;
x_403 = x_444;
x_404 = x_450;
x_405 = x_439;
x_406 = x_427;
x_407 = x_428;
x_408 = x_429;
x_409 = x_430;
x_410 = x_431;
x_411 = x_432;
x_412 = x_433;
x_413 = x_434;
x_414 = x_435;
x_415 = lean_box(0);
goto block_426;
}
else
{
lean_object* x_454; 
lean_inc(x_445);
x_454 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_445, x_427);
if (lean_obj_tag(x_454) == 0)
{
lean_dec_ref(x_454);
x_398 = x_446;
x_399 = x_445;
x_400 = x_441;
x_401 = x_440;
x_402 = x_449;
x_403 = x_444;
x_404 = x_450;
x_405 = x_439;
x_406 = x_427;
x_407 = x_428;
x_408 = x_429;
x_409 = x_430;
x_410 = x_431;
x_411 = x_432;
x_412 = x_433;
x_413 = x_434;
x_414 = x_435;
x_415 = lean_box(0);
goto block_426;
}
else
{
lean_dec_ref(x_450);
lean_dec_ref(x_449);
lean_dec_ref(x_446);
lean_dec(x_445);
lean_dec(x_444);
lean_dec_ref(x_441);
lean_dec(x_440);
lean_dec(x_439);
lean_dec(x_435);
lean_dec_ref(x_434);
lean_dec(x_433);
lean_dec_ref(x_432);
lean_dec(x_431);
lean_dec(x_430);
lean_dec_ref(x_429);
lean_dec(x_428);
lean_dec(x_427);
return x_454;
}
}
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; 
lean_dec_ref(x_446);
lean_dec(x_445);
lean_dec(x_444);
lean_dec_ref(x_441);
lean_dec(x_440);
lean_dec(x_439);
lean_dec(x_435);
lean_dec_ref(x_434);
lean_dec(x_433);
lean_dec_ref(x_432);
lean_dec(x_431);
lean_dec(x_430);
lean_dec_ref(x_429);
lean_dec(x_428);
lean_dec(x_427);
x_455 = lean_ctor_get(x_447, 0);
lean_inc(x_455);
if (lean_is_exclusive(x_447)) {
 lean_ctor_release(x_447, 0);
 x_456 = x_447;
} else {
 lean_dec_ref(x_447);
 x_456 = lean_box(0);
}
if (lean_is_scalar(x_456)) {
 x_457 = lean_alloc_ctor(1, 1, 0);
} else {
 x_457 = x_456;
}
lean_ctor_set(x_457, 0, x_455);
return x_457;
}
}
else
{
lean_object* x_458; 
x_458 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_439, x_427, x_428, x_429, x_430, x_431, x_432, x_433, x_434, x_435);
lean_dec(x_435);
lean_dec_ref(x_434);
lean_dec(x_433);
lean_dec_ref(x_432);
lean_dec(x_431);
lean_dec(x_430);
lean_dec_ref(x_429);
lean_dec(x_428);
lean_dec(x_427);
return x_458;
}
}
else
{
lean_object* x_459; lean_object* x_460; 
lean_dec(x_431);
lean_dec(x_430);
lean_dec_ref(x_429);
lean_dec(x_428);
x_459 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5;
x_460 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_459, x_434);
if (lean_obj_tag(x_460) == 0)
{
lean_object* x_461; uint8_t x_462; 
x_461 = lean_ctor_get(x_460, 0);
lean_inc(x_461);
lean_dec_ref(x_460);
x_462 = lean_unbox(x_461);
lean_dec(x_461);
if (x_462 == 0)
{
lean_dec(x_439);
lean_dec(x_435);
lean_dec_ref(x_434);
lean_dec(x_433);
lean_dec_ref(x_432);
lean_dec(x_427);
x_43 = lean_box(0);
goto block_46;
}
else
{
lean_object* x_463; 
x_463 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_439, x_427, x_434);
lean_dec(x_427);
if (lean_obj_tag(x_463) == 0)
{
lean_object* x_464; lean_object* x_465; 
x_464 = lean_ctor_get(x_463, 0);
lean_inc(x_464);
lean_dec_ref(x_463);
x_465 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_459, x_464, x_432, x_433, x_434, x_435);
lean_dec(x_435);
lean_dec_ref(x_434);
lean_dec(x_433);
lean_dec_ref(x_432);
if (lean_obj_tag(x_465) == 0)
{
lean_dec_ref(x_465);
x_43 = lean_box(0);
goto block_46;
}
else
{
return x_465;
}
}
else
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; 
lean_dec(x_435);
lean_dec_ref(x_434);
lean_dec(x_433);
lean_dec_ref(x_432);
x_466 = lean_ctor_get(x_463, 0);
lean_inc(x_466);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 x_467 = x_463;
} else {
 lean_dec_ref(x_463);
 x_467 = lean_box(0);
}
if (lean_is_scalar(x_467)) {
 x_468 = lean_alloc_ctor(1, 1, 0);
} else {
 x_468 = x_467;
}
lean_ctor_set(x_468, 0, x_466);
return x_468;
}
}
}
else
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; 
lean_dec(x_439);
lean_dec(x_435);
lean_dec_ref(x_434);
lean_dec(x_433);
lean_dec_ref(x_432);
lean_dec(x_427);
x_469 = lean_ctor_get(x_460, 0);
lean_inc(x_469);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 x_470 = x_460;
} else {
 lean_dec_ref(x_460);
 x_470 = lean_box(0);
}
if (lean_is_scalar(x_470)) {
 x_471 = lean_alloc_ctor(1, 1, 0);
} else {
 x_471 = x_470;
}
lean_ctor_set(x_471, 0, x_469);
return x_471;
}
}
}
else
{
lean_object* x_472; lean_object* x_473; 
x_472 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7;
x_473 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_472, x_434);
if (lean_obj_tag(x_473) == 0)
{
lean_object* x_474; uint8_t x_475; 
x_474 = lean_ctor_get(x_473, 0);
lean_inc(x_474);
lean_dec_ref(x_473);
x_475 = lean_unbox(x_474);
lean_dec(x_474);
if (x_475 == 0)
{
x_12 = x_439;
x_13 = x_427;
x_14 = x_428;
x_15 = x_429;
x_16 = x_430;
x_17 = x_431;
x_18 = x_432;
x_19 = x_433;
x_20 = x_434;
x_21 = x_435;
x_22 = lean_box(0);
goto block_30;
}
else
{
lean_object* x_476; 
lean_inc(x_439);
x_476 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_439, x_427, x_434);
if (lean_obj_tag(x_476) == 0)
{
lean_object* x_477; lean_object* x_478; 
x_477 = lean_ctor_get(x_476, 0);
lean_inc(x_477);
lean_dec_ref(x_476);
x_478 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_472, x_477, x_432, x_433, x_434, x_435);
if (lean_obj_tag(x_478) == 0)
{
lean_dec_ref(x_478);
x_12 = x_439;
x_13 = x_427;
x_14 = x_428;
x_15 = x_429;
x_16 = x_430;
x_17 = x_431;
x_18 = x_432;
x_19 = x_433;
x_20 = x_434;
x_21 = x_435;
x_22 = lean_box(0);
goto block_30;
}
else
{
lean_dec(x_439);
lean_dec(x_435);
lean_dec_ref(x_434);
lean_dec(x_433);
lean_dec_ref(x_432);
lean_dec(x_431);
lean_dec(x_430);
lean_dec_ref(x_429);
lean_dec(x_428);
lean_dec(x_427);
return x_478;
}
}
else
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; 
lean_dec(x_439);
lean_dec(x_435);
lean_dec_ref(x_434);
lean_dec(x_433);
lean_dec_ref(x_432);
lean_dec(x_431);
lean_dec(x_430);
lean_dec_ref(x_429);
lean_dec(x_428);
lean_dec(x_427);
x_479 = lean_ctor_get(x_476, 0);
lean_inc(x_479);
if (lean_is_exclusive(x_476)) {
 lean_ctor_release(x_476, 0);
 x_480 = x_476;
} else {
 lean_dec_ref(x_476);
 x_480 = lean_box(0);
}
if (lean_is_scalar(x_480)) {
 x_481 = lean_alloc_ctor(1, 1, 0);
} else {
 x_481 = x_480;
}
lean_ctor_set(x_481, 0, x_479);
return x_481;
}
}
}
else
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; 
lean_dec(x_439);
lean_dec(x_435);
lean_dec_ref(x_434);
lean_dec(x_433);
lean_dec_ref(x_432);
lean_dec(x_431);
lean_dec(x_430);
lean_dec_ref(x_429);
lean_dec(x_428);
lean_dec(x_427);
x_482 = lean_ctor_get(x_473, 0);
lean_inc(x_482);
if (lean_is_exclusive(x_473)) {
 lean_ctor_release(x_473, 0);
 x_483 = x_473;
} else {
 lean_dec_ref(x_473);
 x_483 = lean_box(0);
}
if (lean_is_scalar(x_483)) {
 x_484 = lean_alloc_ctor(1, 1, 0);
} else {
 x_484 = x_483;
}
lean_ctor_set(x_484, 0, x_482);
return x_484;
}
}
}
else
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; 
lean_dec(x_435);
lean_dec_ref(x_434);
lean_dec(x_433);
lean_dec_ref(x_432);
lean_dec(x_431);
lean_dec(x_430);
lean_dec_ref(x_429);
lean_dec(x_428);
lean_dec(x_427);
x_485 = lean_ctor_get(x_438, 0);
lean_inc(x_485);
if (lean_is_exclusive(x_438)) {
 lean_ctor_release(x_438, 0);
 x_486 = x_438;
} else {
 lean_dec_ref(x_438);
 x_486 = lean_box(0);
}
if (lean_is_scalar(x_486)) {
 x_487 = lean_alloc_ctor(1, 1, 0);
} else {
 x_487 = x_486;
}
lean_ctor_set(x_487, 0, x_485);
return x_487;
}
}
}
else
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; 
lean_dec_ref(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_496 = lean_ctor_get(x_395, 0);
lean_inc(x_496);
if (lean_is_exclusive(x_395)) {
 lean_ctor_release(x_395, 0);
 x_497 = x_395;
} else {
 lean_dec_ref(x_395);
 x_497 = lean_box(0);
}
if (lean_is_scalar(x_497)) {
 x_498 = lean_alloc_ctor(1, 1, 0);
} else {
 x_498 = x_497;
}
lean_ctor_set(x_498, 0, x_496);
return x_498;
}
block_393:
{
if (lean_obj_tag(x_343) == 1)
{
lean_object* x_344; lean_object* x_345; 
lean_dec_ref(x_333);
lean_dec_ref(x_326);
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
lean_dec_ref(x_343);
x_345 = lean_ctor_get(x_344, 1);
lean_inc_ref(x_345);
if (lean_obj_tag(x_345) == 1)
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_346 = lean_ctor_get(x_344, 0);
x_347 = lean_ctor_get(x_345, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_345, 2);
lean_inc_ref(x_348);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 lean_ctor_release(x_345, 2);
 x_349 = x_345;
} else {
 lean_dec_ref(x_345);
 x_349 = lean_box(0);
}
x_350 = lean_int_mul(x_331, x_346);
x_351 = lean_int_mul(x_347, x_339);
x_352 = l_Lean_Meta_Grind_Arith_gcdExt(x_350, x_351);
lean_dec(x_351);
lean_dec(x_350);
x_353 = lean_ctor_get(x_352, 1);
lean_inc(x_353);
x_354 = lean_ctor_get(x_352, 0);
lean_inc(x_354);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 x_355 = x_352;
} else {
 lean_dec_ref(x_352);
 x_355 = lean_box(0);
}
x_356 = lean_ctor_get(x_353, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_353, 1);
lean_inc(x_357);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 x_358 = x_353;
} else {
 lean_dec_ref(x_353);
 x_358 = lean_box(0);
}
x_359 = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
x_360 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_359, x_332, x_327);
if (lean_obj_tag(x_360) == 0)
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
lean_dec_ref(x_360);
x_361 = lean_int_mul(x_356, x_346);
lean_dec(x_356);
lean_inc_ref(x_338);
x_362 = l_Int_Linear_Poly_mul(x_338, x_361);
lean_dec(x_361);
x_363 = lean_int_mul(x_357, x_339);
lean_dec(x_357);
lean_inc_ref(x_348);
x_364 = l_Int_Linear_Poly_mul(x_348, x_363);
lean_dec(x_363);
x_365 = lean_int_mul(x_339, x_346);
lean_dec(x_339);
x_366 = l_Int_Linear_Poly_combine(x_362, x_364);
lean_inc(x_354);
if (lean_is_scalar(x_349)) {
 x_367 = lean_alloc_ctor(1, 3, 0);
} else {
 x_367 = x_349;
}
lean_ctor_set(x_367, 0, x_354);
lean_ctor_set(x_367, 1, x_325);
lean_ctor_set(x_367, 2, x_366);
lean_inc(x_344);
lean_inc_ref(x_334);
if (lean_is_scalar(x_358)) {
 x_368 = lean_alloc_ctor(4, 2, 0);
} else {
 x_368 = x_358;
 lean_ctor_set_tag(x_368, 4);
}
lean_ctor_set(x_368, 0, x_334);
lean_ctor_set(x_368, 1, x_344);
x_369 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_369, 0, x_365);
lean_ctor_set(x_369, 1, x_367);
lean_ctor_set(x_369, 2, x_368);
lean_inc(x_341);
lean_inc_ref(x_340);
lean_inc(x_342);
lean_inc_ref(x_330);
lean_inc(x_335);
lean_inc(x_329);
lean_inc_ref(x_328);
lean_inc(x_336);
lean_inc(x_327);
x_370 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_369, x_327, x_336, x_328, x_329, x_335, x_330, x_342, x_340, x_341);
if (lean_obj_tag(x_370) == 0)
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
lean_dec_ref(x_370);
x_371 = l_Int_Linear_Poly_mul(x_338, x_347);
lean_dec(x_347);
x_372 = lean_int_neg(x_331);
lean_dec(x_331);
x_373 = l_Int_Linear_Poly_mul(x_348, x_372);
lean_dec(x_372);
x_374 = l_Int_Linear_Poly_combine(x_371, x_373);
lean_inc(x_344);
if (lean_is_scalar(x_355)) {
 x_375 = lean_alloc_ctor(5, 2, 0);
} else {
 x_375 = x_355;
 lean_ctor_set_tag(x_375, 5);
}
lean_ctor_set(x_375, 0, x_334);
lean_ctor_set(x_375, 1, x_344);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 lean_ctor_release(x_344, 1);
 lean_ctor_release(x_344, 2);
 x_376 = x_344;
} else {
 lean_dec_ref(x_344);
 x_376 = lean_box(0);
}
if (lean_is_scalar(x_376)) {
 x_377 = lean_alloc_ctor(0, 3, 0);
} else {
 x_377 = x_376;
}
lean_ctor_set(x_377, 0, x_354);
lean_ctor_set(x_377, 1, x_374);
lean_ctor_set(x_377, 2, x_375);
x_1 = x_377;
x_2 = x_327;
x_3 = x_336;
x_4 = x_328;
x_5 = x_329;
x_6 = x_335;
x_7 = x_330;
x_8 = x_342;
x_9 = x_340;
x_10 = x_341;
goto _start;
}
else
{
lean_dec(x_355);
lean_dec(x_354);
lean_dec_ref(x_348);
lean_dec(x_347);
lean_dec(x_344);
lean_dec(x_342);
lean_dec(x_341);
lean_dec_ref(x_340);
lean_dec_ref(x_338);
lean_dec(x_336);
lean_dec(x_335);
lean_dec_ref(x_334);
lean_dec(x_331);
lean_dec_ref(x_330);
lean_dec(x_329);
lean_dec_ref(x_328);
lean_dec(x_327);
return x_370;
}
}
else
{
lean_dec(x_358);
lean_dec(x_357);
lean_dec(x_356);
lean_dec(x_355);
lean_dec(x_354);
lean_dec(x_349);
lean_dec_ref(x_348);
lean_dec(x_347);
lean_dec(x_344);
lean_dec(x_342);
lean_dec(x_341);
lean_dec_ref(x_340);
lean_dec(x_339);
lean_dec_ref(x_338);
lean_dec(x_336);
lean_dec(x_335);
lean_dec_ref(x_334);
lean_dec(x_331);
lean_dec_ref(x_330);
lean_dec(x_329);
lean_dec_ref(x_328);
lean_dec(x_327);
lean_dec(x_325);
return x_360;
}
}
else
{
lean_object* x_379; 
lean_dec_ref(x_345);
lean_dec(x_339);
lean_dec_ref(x_338);
lean_dec_ref(x_334);
lean_dec_ref(x_332);
lean_dec(x_331);
lean_dec(x_325);
x_379 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_344, x_327, x_336, x_328, x_329, x_335, x_330, x_342, x_340, x_341);
lean_dec(x_341);
lean_dec_ref(x_340);
lean_dec(x_342);
lean_dec_ref(x_330);
lean_dec(x_335);
lean_dec(x_329);
lean_dec_ref(x_328);
lean_dec(x_336);
lean_dec(x_327);
return x_379;
}
}
else
{
lean_object* x_380; lean_object* x_381; 
lean_dec(x_343);
lean_dec(x_339);
lean_dec_ref(x_338);
lean_dec(x_336);
lean_dec(x_335);
lean_dec_ref(x_332);
lean_dec(x_331);
lean_dec(x_329);
lean_dec_ref(x_328);
lean_dec(x_325);
x_380 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2;
x_381 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_380, x_340);
if (lean_obj_tag(x_381) == 0)
{
lean_object* x_382; uint8_t x_383; 
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
lean_dec_ref(x_381);
x_383 = lean_unbox(x_382);
lean_dec(x_382);
if (x_383 == 0)
{
lean_dec_ref(x_334);
x_31 = x_326;
x_32 = x_333;
x_33 = x_327;
x_34 = x_330;
x_35 = x_342;
x_36 = x_340;
x_37 = x_341;
x_38 = lean_box(0);
goto block_42;
}
else
{
lean_object* x_384; 
x_384 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_334, x_327, x_340);
if (lean_obj_tag(x_384) == 0)
{
lean_object* x_385; lean_object* x_386; 
x_385 = lean_ctor_get(x_384, 0);
lean_inc(x_385);
lean_dec_ref(x_384);
x_386 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_380, x_385, x_330, x_342, x_340, x_341);
if (lean_obj_tag(x_386) == 0)
{
lean_dec_ref(x_386);
x_31 = x_326;
x_32 = x_333;
x_33 = x_327;
x_34 = x_330;
x_35 = x_342;
x_36 = x_340;
x_37 = x_341;
x_38 = lean_box(0);
goto block_42;
}
else
{
lean_dec(x_342);
lean_dec(x_341);
lean_dec_ref(x_340);
lean_dec_ref(x_333);
lean_dec_ref(x_330);
lean_dec(x_327);
lean_dec_ref(x_326);
return x_386;
}
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; 
lean_dec(x_342);
lean_dec(x_341);
lean_dec_ref(x_340);
lean_dec_ref(x_333);
lean_dec_ref(x_330);
lean_dec(x_327);
lean_dec_ref(x_326);
x_387 = lean_ctor_get(x_384, 0);
lean_inc(x_387);
if (lean_is_exclusive(x_384)) {
 lean_ctor_release(x_384, 0);
 x_388 = x_384;
} else {
 lean_dec_ref(x_384);
 x_388 = lean_box(0);
}
if (lean_is_scalar(x_388)) {
 x_389 = lean_alloc_ctor(1, 1, 0);
} else {
 x_389 = x_388;
}
lean_ctor_set(x_389, 0, x_387);
return x_389;
}
}
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; 
lean_dec(x_342);
lean_dec(x_341);
lean_dec_ref(x_340);
lean_dec_ref(x_334);
lean_dec_ref(x_333);
lean_dec_ref(x_330);
lean_dec(x_327);
lean_dec_ref(x_326);
x_390 = lean_ctor_get(x_381, 0);
lean_inc(x_390);
if (lean_is_exclusive(x_381)) {
 lean_ctor_release(x_381, 0);
 x_391 = x_381;
} else {
 lean_dec_ref(x_381);
 x_391 = lean_box(0);
}
if (lean_is_scalar(x_391)) {
 x_392 = lean_alloc_ctor(1, 1, 0);
} else {
 x_392 = x_391;
}
lean_ctor_set(x_392, 0, x_390);
return x_392;
}
}
}
}
else
{
lean_object* x_499; lean_object* x_500; 
lean_dec_ref(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_499 = lean_box(0);
x_500 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_500, 0, x_499);
return x_500;
}
}
}
else
{
uint8_t x_501; 
lean_dec_ref(x_9);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_501 = !lean_is_exclusive(x_65);
if (x_501 == 0)
{
return x_65;
}
else
{
lean_object* x_502; lean_object* x_503; 
x_502 = lean_ctor_get(x_65, 0);
lean_inc(x_502);
lean_dec(x_65);
x_503 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_503, 0, x_502);
return x_503;
}
}
}
else
{
lean_object* x_504; 
lean_free_object(x_9);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_52);
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec_ref(x_49);
lean_dec_ref(x_48);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_504 = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(x_53);
return x_504;
}
}
else
{
lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; uint8_t x_517; lean_object* x_518; uint8_t x_519; lean_object* x_520; uint8_t x_521; 
x_505 = lean_ctor_get(x_9, 0);
x_506 = lean_ctor_get(x_9, 1);
x_507 = lean_ctor_get(x_9, 2);
x_508 = lean_ctor_get(x_9, 3);
x_509 = lean_ctor_get(x_9, 4);
x_510 = lean_ctor_get(x_9, 5);
x_511 = lean_ctor_get(x_9, 6);
x_512 = lean_ctor_get(x_9, 7);
x_513 = lean_ctor_get(x_9, 8);
x_514 = lean_ctor_get(x_9, 9);
x_515 = lean_ctor_get(x_9, 10);
x_516 = lean_ctor_get(x_9, 11);
x_517 = lean_ctor_get_uint8(x_9, sizeof(void*)*14);
x_518 = lean_ctor_get(x_9, 12);
x_519 = lean_ctor_get_uint8(x_9, sizeof(void*)*14 + 1);
x_520 = lean_ctor_get(x_9, 13);
lean_inc(x_520);
lean_inc(x_518);
lean_inc(x_516);
lean_inc(x_515);
lean_inc(x_514);
lean_inc(x_513);
lean_inc(x_512);
lean_inc(x_511);
lean_inc(x_510);
lean_inc(x_509);
lean_inc(x_508);
lean_inc(x_507);
lean_inc(x_506);
lean_inc(x_505);
lean_dec(x_9);
x_521 = lean_nat_dec_eq(x_508, x_509);
if (x_521 == 0)
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; 
x_522 = lean_unsigned_to_nat(1u);
x_523 = lean_nat_add(x_508, x_522);
lean_dec(x_508);
x_524 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_524, 0, x_505);
lean_ctor_set(x_524, 1, x_506);
lean_ctor_set(x_524, 2, x_507);
lean_ctor_set(x_524, 3, x_523);
lean_ctor_set(x_524, 4, x_509);
lean_ctor_set(x_524, 5, x_510);
lean_ctor_set(x_524, 6, x_511);
lean_ctor_set(x_524, 7, x_512);
lean_ctor_set(x_524, 8, x_513);
lean_ctor_set(x_524, 9, x_514);
lean_ctor_set(x_524, 10, x_515);
lean_ctor_set(x_524, 11, x_516);
lean_ctor_set(x_524, 12, x_518);
lean_ctor_set(x_524, 13, x_520);
lean_ctor_set_uint8(x_524, sizeof(void*)*14, x_517);
lean_ctor_set_uint8(x_524, sizeof(void*)*14 + 1, x_519);
x_525 = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(x_2, x_524);
if (lean_obj_tag(x_525) == 0)
{
lean_object* x_526; lean_object* x_527; uint8_t x_528; 
x_526 = lean_ctor_get(x_525, 0);
lean_inc(x_526);
if (lean_is_exclusive(x_525)) {
 lean_ctor_release(x_525, 0);
 x_527 = x_525;
} else {
 lean_dec_ref(x_525);
 x_527 = lean_box(0);
}
x_528 = lean_unbox(x_526);
lean_dec(x_526);
if (x_528 == 0)
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_598; lean_object* x_599; 
lean_dec(x_527);
x_598 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3;
x_599 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_598, x_524);
if (lean_obj_tag(x_599) == 0)
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; uint8_t x_693; 
x_600 = lean_ctor_get(x_599, 0);
lean_inc(x_600);
lean_dec_ref(x_599);
x_601 = lean_box(0);
x_693 = lean_unbox(x_600);
lean_dec(x_600);
if (x_693 == 0)
{
x_631 = x_2;
x_632 = x_3;
x_633 = x_4;
x_634 = x_5;
x_635 = x_6;
x_636 = x_7;
x_637 = x_8;
x_638 = x_524;
x_639 = x_10;
x_640 = lean_box(0);
goto block_692;
}
else
{
lean_object* x_694; 
lean_inc_ref(x_1);
x_694 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_524);
if (lean_obj_tag(x_694) == 0)
{
lean_object* x_695; lean_object* x_696; 
x_695 = lean_ctor_get(x_694, 0);
lean_inc(x_695);
lean_dec_ref(x_694);
x_696 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_598, x_695, x_7, x_8, x_524, x_10);
if (lean_obj_tag(x_696) == 0)
{
lean_dec_ref(x_696);
x_631 = x_2;
x_632 = x_3;
x_633 = x_4;
x_634 = x_5;
x_635 = x_6;
x_636 = x_7;
x_637 = x_8;
x_638 = x_524;
x_639 = x_10;
x_640 = lean_box(0);
goto block_692;
}
else
{
lean_dec_ref(x_524);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_696;
}
}
else
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; 
lean_dec_ref(x_524);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_697 = lean_ctor_get(x_694, 0);
lean_inc(x_697);
if (lean_is_exclusive(x_694)) {
 lean_ctor_release(x_694, 0);
 x_698 = x_694;
} else {
 lean_dec_ref(x_694);
 x_698 = lean_box(0);
}
if (lean_is_scalar(x_698)) {
 x_699 = lean_alloc_ctor(1, 1, 0);
} else {
 x_699 = x_698;
}
lean_ctor_set(x_699, 0, x_697);
return x_699;
}
}
block_630:
{
lean_object* x_620; 
x_620 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_610, x_617);
if (lean_obj_tag(x_620) == 0)
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; uint8_t x_624; 
x_621 = lean_ctor_get(x_620, 0);
lean_inc(x_621);
lean_dec_ref(x_620);
x_622 = lean_ctor_get(x_621, 6);
lean_inc_ref(x_622);
lean_dec(x_621);
x_623 = lean_ctor_get(x_622, 2);
x_624 = lean_nat_dec_lt(x_603, x_623);
if (x_624 == 0)
{
lean_object* x_625; 
lean_dec_ref(x_622);
x_625 = l_outOfBounds___redArg(x_601);
x_529 = x_603;
x_530 = x_604;
x_531 = x_610;
x_532 = x_612;
x_533 = x_613;
x_534 = x_615;
x_535 = x_607;
x_536 = x_606;
x_537 = x_608;
x_538 = x_609;
x_539 = x_614;
x_540 = x_611;
x_541 = lean_box(0);
x_542 = x_602;
x_543 = x_605;
x_544 = x_617;
x_545 = x_618;
x_546 = x_616;
x_547 = x_625;
goto block_597;
}
else
{
lean_object* x_626; 
x_626 = l_Lean_PersistentArray_get_x21___redArg(x_601, x_622, x_603);
x_529 = x_603;
x_530 = x_604;
x_531 = x_610;
x_532 = x_612;
x_533 = x_613;
x_534 = x_615;
x_535 = x_607;
x_536 = x_606;
x_537 = x_608;
x_538 = x_609;
x_539 = x_614;
x_540 = x_611;
x_541 = lean_box(0);
x_542 = x_602;
x_543 = x_605;
x_544 = x_617;
x_545 = x_618;
x_546 = x_616;
x_547 = x_626;
goto block_597;
}
}
else
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; 
lean_dec(x_618);
lean_dec_ref(x_617);
lean_dec(x_616);
lean_dec_ref(x_615);
lean_dec(x_614);
lean_dec(x_613);
lean_dec_ref(x_612);
lean_dec(x_611);
lean_dec(x_610);
lean_dec_ref(x_609);
lean_dec_ref(x_608);
lean_dec(x_607);
lean_dec_ref(x_606);
lean_dec(x_605);
lean_dec_ref(x_604);
lean_dec(x_603);
lean_dec_ref(x_602);
x_627 = lean_ctor_get(x_620, 0);
lean_inc(x_627);
if (lean_is_exclusive(x_620)) {
 lean_ctor_release(x_620, 0);
 x_628 = x_620;
} else {
 lean_dec_ref(x_620);
 x_628 = lean_box(0);
}
if (lean_is_scalar(x_628)) {
 x_629 = lean_alloc_ctor(1, 1, 0);
} else {
 x_629 = x_628;
}
lean_ctor_set(x_629, 0, x_627);
return x_629;
}
}
block_692:
{
lean_object* x_641; lean_object* x_642; 
x_641 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc_ref(x_638);
x_642 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(x_641, x_631, x_632, x_633, x_634, x_635, x_636, x_637, x_638, x_639);
if (lean_obj_tag(x_642) == 0)
{
lean_object* x_643; lean_object* x_644; lean_object* x_645; uint8_t x_646; 
x_643 = lean_ctor_get(x_642, 0);
lean_inc(x_643);
lean_dec_ref(x_642);
x_644 = lean_ctor_get(x_643, 0);
x_645 = lean_ctor_get(x_643, 1);
lean_inc(x_644);
x_646 = l_Int_Linear_Poly_isUnsatDvd(x_644, x_645);
if (x_646 == 0)
{
uint8_t x_647; 
x_647 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_643);
if (x_647 == 0)
{
if (lean_obj_tag(x_645) == 1)
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; 
lean_inc_ref(x_645);
lean_inc(x_644);
x_648 = lean_ctor_get(x_645, 0);
lean_inc(x_648);
x_649 = lean_ctor_get(x_645, 1);
lean_inc(x_649);
x_650 = lean_ctor_get(x_645, 2);
lean_inc_ref(x_650);
lean_inc(x_643);
x_651 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_643, x_631, x_638);
if (lean_obj_tag(x_651) == 0)
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; uint8_t x_655; uint8_t x_656; uint8_t x_657; 
x_652 = lean_ctor_get(x_651, 0);
lean_inc(x_652);
lean_dec_ref(x_651);
lean_inc(x_649);
x_653 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed), 2, 1);
lean_closure_set(x_653, 0, x_649);
lean_inc(x_649);
lean_inc(x_643);
x_654 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed), 3, 2);
lean_closure_set(x_654, 0, x_643);
lean_closure_set(x_654, 1, x_649);
x_655 = 0;
x_656 = lean_unbox(x_652);
lean_dec(x_652);
x_657 = l_Lean_instBEqLBool_beq(x_656, x_655);
if (x_657 == 0)
{
x_602 = x_650;
x_603 = x_649;
x_604 = x_645;
x_605 = x_644;
x_606 = x_653;
x_607 = x_648;
x_608 = x_654;
x_609 = x_643;
x_610 = x_631;
x_611 = x_632;
x_612 = x_633;
x_613 = x_634;
x_614 = x_635;
x_615 = x_636;
x_616 = x_637;
x_617 = x_638;
x_618 = x_639;
x_619 = lean_box(0);
goto block_630;
}
else
{
lean_object* x_658; 
lean_inc(x_649);
x_658 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_649, x_631);
if (lean_obj_tag(x_658) == 0)
{
lean_dec_ref(x_658);
x_602 = x_650;
x_603 = x_649;
x_604 = x_645;
x_605 = x_644;
x_606 = x_653;
x_607 = x_648;
x_608 = x_654;
x_609 = x_643;
x_610 = x_631;
x_611 = x_632;
x_612 = x_633;
x_613 = x_634;
x_614 = x_635;
x_615 = x_636;
x_616 = x_637;
x_617 = x_638;
x_618 = x_639;
x_619 = lean_box(0);
goto block_630;
}
else
{
lean_dec_ref(x_654);
lean_dec_ref(x_653);
lean_dec_ref(x_650);
lean_dec(x_649);
lean_dec(x_648);
lean_dec_ref(x_645);
lean_dec(x_644);
lean_dec(x_643);
lean_dec(x_639);
lean_dec_ref(x_638);
lean_dec(x_637);
lean_dec_ref(x_636);
lean_dec(x_635);
lean_dec(x_634);
lean_dec_ref(x_633);
lean_dec(x_632);
lean_dec(x_631);
return x_658;
}
}
}
else
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; 
lean_dec_ref(x_650);
lean_dec(x_649);
lean_dec(x_648);
lean_dec_ref(x_645);
lean_dec(x_644);
lean_dec(x_643);
lean_dec(x_639);
lean_dec_ref(x_638);
lean_dec(x_637);
lean_dec_ref(x_636);
lean_dec(x_635);
lean_dec(x_634);
lean_dec_ref(x_633);
lean_dec(x_632);
lean_dec(x_631);
x_659 = lean_ctor_get(x_651, 0);
lean_inc(x_659);
if (lean_is_exclusive(x_651)) {
 lean_ctor_release(x_651, 0);
 x_660 = x_651;
} else {
 lean_dec_ref(x_651);
 x_660 = lean_box(0);
}
if (lean_is_scalar(x_660)) {
 x_661 = lean_alloc_ctor(1, 1, 0);
} else {
 x_661 = x_660;
}
lean_ctor_set(x_661, 0, x_659);
return x_661;
}
}
else
{
lean_object* x_662; 
x_662 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_643, x_631, x_632, x_633, x_634, x_635, x_636, x_637, x_638, x_639);
lean_dec(x_639);
lean_dec_ref(x_638);
lean_dec(x_637);
lean_dec_ref(x_636);
lean_dec(x_635);
lean_dec(x_634);
lean_dec_ref(x_633);
lean_dec(x_632);
lean_dec(x_631);
return x_662;
}
}
else
{
lean_object* x_663; lean_object* x_664; 
lean_dec(x_635);
lean_dec(x_634);
lean_dec_ref(x_633);
lean_dec(x_632);
x_663 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5;
x_664 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_663, x_638);
if (lean_obj_tag(x_664) == 0)
{
lean_object* x_665; uint8_t x_666; 
x_665 = lean_ctor_get(x_664, 0);
lean_inc(x_665);
lean_dec_ref(x_664);
x_666 = lean_unbox(x_665);
lean_dec(x_665);
if (x_666 == 0)
{
lean_dec(x_643);
lean_dec(x_639);
lean_dec_ref(x_638);
lean_dec(x_637);
lean_dec_ref(x_636);
lean_dec(x_631);
x_43 = lean_box(0);
goto block_46;
}
else
{
lean_object* x_667; 
x_667 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_643, x_631, x_638);
lean_dec(x_631);
if (lean_obj_tag(x_667) == 0)
{
lean_object* x_668; lean_object* x_669; 
x_668 = lean_ctor_get(x_667, 0);
lean_inc(x_668);
lean_dec_ref(x_667);
x_669 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_663, x_668, x_636, x_637, x_638, x_639);
lean_dec(x_639);
lean_dec_ref(x_638);
lean_dec(x_637);
lean_dec_ref(x_636);
if (lean_obj_tag(x_669) == 0)
{
lean_dec_ref(x_669);
x_43 = lean_box(0);
goto block_46;
}
else
{
return x_669;
}
}
else
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; 
lean_dec(x_639);
lean_dec_ref(x_638);
lean_dec(x_637);
lean_dec_ref(x_636);
x_670 = lean_ctor_get(x_667, 0);
lean_inc(x_670);
if (lean_is_exclusive(x_667)) {
 lean_ctor_release(x_667, 0);
 x_671 = x_667;
} else {
 lean_dec_ref(x_667);
 x_671 = lean_box(0);
}
if (lean_is_scalar(x_671)) {
 x_672 = lean_alloc_ctor(1, 1, 0);
} else {
 x_672 = x_671;
}
lean_ctor_set(x_672, 0, x_670);
return x_672;
}
}
}
else
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; 
lean_dec(x_643);
lean_dec(x_639);
lean_dec_ref(x_638);
lean_dec(x_637);
lean_dec_ref(x_636);
lean_dec(x_631);
x_673 = lean_ctor_get(x_664, 0);
lean_inc(x_673);
if (lean_is_exclusive(x_664)) {
 lean_ctor_release(x_664, 0);
 x_674 = x_664;
} else {
 lean_dec_ref(x_664);
 x_674 = lean_box(0);
}
if (lean_is_scalar(x_674)) {
 x_675 = lean_alloc_ctor(1, 1, 0);
} else {
 x_675 = x_674;
}
lean_ctor_set(x_675, 0, x_673);
return x_675;
}
}
}
else
{
lean_object* x_676; lean_object* x_677; 
x_676 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7;
x_677 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_676, x_638);
if (lean_obj_tag(x_677) == 0)
{
lean_object* x_678; uint8_t x_679; 
x_678 = lean_ctor_get(x_677, 0);
lean_inc(x_678);
lean_dec_ref(x_677);
x_679 = lean_unbox(x_678);
lean_dec(x_678);
if (x_679 == 0)
{
x_12 = x_643;
x_13 = x_631;
x_14 = x_632;
x_15 = x_633;
x_16 = x_634;
x_17 = x_635;
x_18 = x_636;
x_19 = x_637;
x_20 = x_638;
x_21 = x_639;
x_22 = lean_box(0);
goto block_30;
}
else
{
lean_object* x_680; 
lean_inc(x_643);
x_680 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_643, x_631, x_638);
if (lean_obj_tag(x_680) == 0)
{
lean_object* x_681; lean_object* x_682; 
x_681 = lean_ctor_get(x_680, 0);
lean_inc(x_681);
lean_dec_ref(x_680);
x_682 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_676, x_681, x_636, x_637, x_638, x_639);
if (lean_obj_tag(x_682) == 0)
{
lean_dec_ref(x_682);
x_12 = x_643;
x_13 = x_631;
x_14 = x_632;
x_15 = x_633;
x_16 = x_634;
x_17 = x_635;
x_18 = x_636;
x_19 = x_637;
x_20 = x_638;
x_21 = x_639;
x_22 = lean_box(0);
goto block_30;
}
else
{
lean_dec(x_643);
lean_dec(x_639);
lean_dec_ref(x_638);
lean_dec(x_637);
lean_dec_ref(x_636);
lean_dec(x_635);
lean_dec(x_634);
lean_dec_ref(x_633);
lean_dec(x_632);
lean_dec(x_631);
return x_682;
}
}
else
{
lean_object* x_683; lean_object* x_684; lean_object* x_685; 
lean_dec(x_643);
lean_dec(x_639);
lean_dec_ref(x_638);
lean_dec(x_637);
lean_dec_ref(x_636);
lean_dec(x_635);
lean_dec(x_634);
lean_dec_ref(x_633);
lean_dec(x_632);
lean_dec(x_631);
x_683 = lean_ctor_get(x_680, 0);
lean_inc(x_683);
if (lean_is_exclusive(x_680)) {
 lean_ctor_release(x_680, 0);
 x_684 = x_680;
} else {
 lean_dec_ref(x_680);
 x_684 = lean_box(0);
}
if (lean_is_scalar(x_684)) {
 x_685 = lean_alloc_ctor(1, 1, 0);
} else {
 x_685 = x_684;
}
lean_ctor_set(x_685, 0, x_683);
return x_685;
}
}
}
else
{
lean_object* x_686; lean_object* x_687; lean_object* x_688; 
lean_dec(x_643);
lean_dec(x_639);
lean_dec_ref(x_638);
lean_dec(x_637);
lean_dec_ref(x_636);
lean_dec(x_635);
lean_dec(x_634);
lean_dec_ref(x_633);
lean_dec(x_632);
lean_dec(x_631);
x_686 = lean_ctor_get(x_677, 0);
lean_inc(x_686);
if (lean_is_exclusive(x_677)) {
 lean_ctor_release(x_677, 0);
 x_687 = x_677;
} else {
 lean_dec_ref(x_677);
 x_687 = lean_box(0);
}
if (lean_is_scalar(x_687)) {
 x_688 = lean_alloc_ctor(1, 1, 0);
} else {
 x_688 = x_687;
}
lean_ctor_set(x_688, 0, x_686);
return x_688;
}
}
}
else
{
lean_object* x_689; lean_object* x_690; lean_object* x_691; 
lean_dec(x_639);
lean_dec_ref(x_638);
lean_dec(x_637);
lean_dec_ref(x_636);
lean_dec(x_635);
lean_dec(x_634);
lean_dec_ref(x_633);
lean_dec(x_632);
lean_dec(x_631);
x_689 = lean_ctor_get(x_642, 0);
lean_inc(x_689);
if (lean_is_exclusive(x_642)) {
 lean_ctor_release(x_642, 0);
 x_690 = x_642;
} else {
 lean_dec_ref(x_642);
 x_690 = lean_box(0);
}
if (lean_is_scalar(x_690)) {
 x_691 = lean_alloc_ctor(1, 1, 0);
} else {
 x_691 = x_690;
}
lean_ctor_set(x_691, 0, x_689);
return x_691;
}
}
}
else
{
lean_object* x_700; lean_object* x_701; lean_object* x_702; 
lean_dec_ref(x_524);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_700 = lean_ctor_get(x_599, 0);
lean_inc(x_700);
if (lean_is_exclusive(x_599)) {
 lean_ctor_release(x_599, 0);
 x_701 = x_599;
} else {
 lean_dec_ref(x_599);
 x_701 = lean_box(0);
}
if (lean_is_scalar(x_701)) {
 x_702 = lean_alloc_ctor(1, 1, 0);
} else {
 x_702 = x_701;
}
lean_ctor_set(x_702, 0, x_700);
return x_702;
}
block_597:
{
if (lean_obj_tag(x_547) == 1)
{
lean_object* x_548; lean_object* x_549; 
lean_dec_ref(x_537);
lean_dec_ref(x_530);
x_548 = lean_ctor_get(x_547, 0);
lean_inc(x_548);
lean_dec_ref(x_547);
x_549 = lean_ctor_get(x_548, 1);
lean_inc_ref(x_549);
if (lean_obj_tag(x_549) == 1)
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; 
x_550 = lean_ctor_get(x_548, 0);
x_551 = lean_ctor_get(x_549, 0);
lean_inc(x_551);
x_552 = lean_ctor_get(x_549, 2);
lean_inc_ref(x_552);
if (lean_is_exclusive(x_549)) {
 lean_ctor_release(x_549, 0);
 lean_ctor_release(x_549, 1);
 lean_ctor_release(x_549, 2);
 x_553 = x_549;
} else {
 lean_dec_ref(x_549);
 x_553 = lean_box(0);
}
x_554 = lean_int_mul(x_535, x_550);
x_555 = lean_int_mul(x_551, x_543);
x_556 = l_Lean_Meta_Grind_Arith_gcdExt(x_554, x_555);
lean_dec(x_555);
lean_dec(x_554);
x_557 = lean_ctor_get(x_556, 1);
lean_inc(x_557);
x_558 = lean_ctor_get(x_556, 0);
lean_inc(x_558);
if (lean_is_exclusive(x_556)) {
 lean_ctor_release(x_556, 0);
 lean_ctor_release(x_556, 1);
 x_559 = x_556;
} else {
 lean_dec_ref(x_556);
 x_559 = lean_box(0);
}
x_560 = lean_ctor_get(x_557, 0);
lean_inc(x_560);
x_561 = lean_ctor_get(x_557, 1);
lean_inc(x_561);
if (lean_is_exclusive(x_557)) {
 lean_ctor_release(x_557, 0);
 lean_ctor_release(x_557, 1);
 x_562 = x_557;
} else {
 lean_dec_ref(x_557);
 x_562 = lean_box(0);
}
x_563 = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
x_564 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_563, x_536, x_531);
if (lean_obj_tag(x_564) == 0)
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; 
lean_dec_ref(x_564);
x_565 = lean_int_mul(x_560, x_550);
lean_dec(x_560);
lean_inc_ref(x_542);
x_566 = l_Int_Linear_Poly_mul(x_542, x_565);
lean_dec(x_565);
x_567 = lean_int_mul(x_561, x_543);
lean_dec(x_561);
lean_inc_ref(x_552);
x_568 = l_Int_Linear_Poly_mul(x_552, x_567);
lean_dec(x_567);
x_569 = lean_int_mul(x_543, x_550);
lean_dec(x_543);
x_570 = l_Int_Linear_Poly_combine(x_566, x_568);
lean_inc(x_558);
if (lean_is_scalar(x_553)) {
 x_571 = lean_alloc_ctor(1, 3, 0);
} else {
 x_571 = x_553;
}
lean_ctor_set(x_571, 0, x_558);
lean_ctor_set(x_571, 1, x_529);
lean_ctor_set(x_571, 2, x_570);
lean_inc(x_548);
lean_inc_ref(x_538);
if (lean_is_scalar(x_562)) {
 x_572 = lean_alloc_ctor(4, 2, 0);
} else {
 x_572 = x_562;
 lean_ctor_set_tag(x_572, 4);
}
lean_ctor_set(x_572, 0, x_538);
lean_ctor_set(x_572, 1, x_548);
x_573 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_573, 0, x_569);
lean_ctor_set(x_573, 1, x_571);
lean_ctor_set(x_573, 2, x_572);
lean_inc(x_545);
lean_inc_ref(x_544);
lean_inc(x_546);
lean_inc_ref(x_534);
lean_inc(x_539);
lean_inc(x_533);
lean_inc_ref(x_532);
lean_inc(x_540);
lean_inc(x_531);
x_574 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_573, x_531, x_540, x_532, x_533, x_539, x_534, x_546, x_544, x_545);
if (lean_obj_tag(x_574) == 0)
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; 
lean_dec_ref(x_574);
x_575 = l_Int_Linear_Poly_mul(x_542, x_551);
lean_dec(x_551);
x_576 = lean_int_neg(x_535);
lean_dec(x_535);
x_577 = l_Int_Linear_Poly_mul(x_552, x_576);
lean_dec(x_576);
x_578 = l_Int_Linear_Poly_combine(x_575, x_577);
lean_inc(x_548);
if (lean_is_scalar(x_559)) {
 x_579 = lean_alloc_ctor(5, 2, 0);
} else {
 x_579 = x_559;
 lean_ctor_set_tag(x_579, 5);
}
lean_ctor_set(x_579, 0, x_538);
lean_ctor_set(x_579, 1, x_548);
if (lean_is_exclusive(x_548)) {
 lean_ctor_release(x_548, 0);
 lean_ctor_release(x_548, 1);
 lean_ctor_release(x_548, 2);
 x_580 = x_548;
} else {
 lean_dec_ref(x_548);
 x_580 = lean_box(0);
}
if (lean_is_scalar(x_580)) {
 x_581 = lean_alloc_ctor(0, 3, 0);
} else {
 x_581 = x_580;
}
lean_ctor_set(x_581, 0, x_558);
lean_ctor_set(x_581, 1, x_578);
lean_ctor_set(x_581, 2, x_579);
x_1 = x_581;
x_2 = x_531;
x_3 = x_540;
x_4 = x_532;
x_5 = x_533;
x_6 = x_539;
x_7 = x_534;
x_8 = x_546;
x_9 = x_544;
x_10 = x_545;
goto _start;
}
else
{
lean_dec(x_559);
lean_dec(x_558);
lean_dec_ref(x_552);
lean_dec(x_551);
lean_dec(x_548);
lean_dec(x_546);
lean_dec(x_545);
lean_dec_ref(x_544);
lean_dec_ref(x_542);
lean_dec(x_540);
lean_dec(x_539);
lean_dec_ref(x_538);
lean_dec(x_535);
lean_dec_ref(x_534);
lean_dec(x_533);
lean_dec_ref(x_532);
lean_dec(x_531);
return x_574;
}
}
else
{
lean_dec(x_562);
lean_dec(x_561);
lean_dec(x_560);
lean_dec(x_559);
lean_dec(x_558);
lean_dec(x_553);
lean_dec_ref(x_552);
lean_dec(x_551);
lean_dec(x_548);
lean_dec(x_546);
lean_dec(x_545);
lean_dec_ref(x_544);
lean_dec(x_543);
lean_dec_ref(x_542);
lean_dec(x_540);
lean_dec(x_539);
lean_dec_ref(x_538);
lean_dec(x_535);
lean_dec_ref(x_534);
lean_dec(x_533);
lean_dec_ref(x_532);
lean_dec(x_531);
lean_dec(x_529);
return x_564;
}
}
else
{
lean_object* x_583; 
lean_dec_ref(x_549);
lean_dec(x_543);
lean_dec_ref(x_542);
lean_dec_ref(x_538);
lean_dec_ref(x_536);
lean_dec(x_535);
lean_dec(x_529);
x_583 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_548, x_531, x_540, x_532, x_533, x_539, x_534, x_546, x_544, x_545);
lean_dec(x_545);
lean_dec_ref(x_544);
lean_dec(x_546);
lean_dec_ref(x_534);
lean_dec(x_539);
lean_dec(x_533);
lean_dec_ref(x_532);
lean_dec(x_540);
lean_dec(x_531);
return x_583;
}
}
else
{
lean_object* x_584; lean_object* x_585; 
lean_dec(x_547);
lean_dec(x_543);
lean_dec_ref(x_542);
lean_dec(x_540);
lean_dec(x_539);
lean_dec_ref(x_536);
lean_dec(x_535);
lean_dec(x_533);
lean_dec_ref(x_532);
lean_dec(x_529);
x_584 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2;
x_585 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_584, x_544);
if (lean_obj_tag(x_585) == 0)
{
lean_object* x_586; uint8_t x_587; 
x_586 = lean_ctor_get(x_585, 0);
lean_inc(x_586);
lean_dec_ref(x_585);
x_587 = lean_unbox(x_586);
lean_dec(x_586);
if (x_587 == 0)
{
lean_dec_ref(x_538);
x_31 = x_530;
x_32 = x_537;
x_33 = x_531;
x_34 = x_534;
x_35 = x_546;
x_36 = x_544;
x_37 = x_545;
x_38 = lean_box(0);
goto block_42;
}
else
{
lean_object* x_588; 
x_588 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_538, x_531, x_544);
if (lean_obj_tag(x_588) == 0)
{
lean_object* x_589; lean_object* x_590; 
x_589 = lean_ctor_get(x_588, 0);
lean_inc(x_589);
lean_dec_ref(x_588);
x_590 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_584, x_589, x_534, x_546, x_544, x_545);
if (lean_obj_tag(x_590) == 0)
{
lean_dec_ref(x_590);
x_31 = x_530;
x_32 = x_537;
x_33 = x_531;
x_34 = x_534;
x_35 = x_546;
x_36 = x_544;
x_37 = x_545;
x_38 = lean_box(0);
goto block_42;
}
else
{
lean_dec(x_546);
lean_dec(x_545);
lean_dec_ref(x_544);
lean_dec_ref(x_537);
lean_dec_ref(x_534);
lean_dec(x_531);
lean_dec_ref(x_530);
return x_590;
}
}
else
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; 
lean_dec(x_546);
lean_dec(x_545);
lean_dec_ref(x_544);
lean_dec_ref(x_537);
lean_dec_ref(x_534);
lean_dec(x_531);
lean_dec_ref(x_530);
x_591 = lean_ctor_get(x_588, 0);
lean_inc(x_591);
if (lean_is_exclusive(x_588)) {
 lean_ctor_release(x_588, 0);
 x_592 = x_588;
} else {
 lean_dec_ref(x_588);
 x_592 = lean_box(0);
}
if (lean_is_scalar(x_592)) {
 x_593 = lean_alloc_ctor(1, 1, 0);
} else {
 x_593 = x_592;
}
lean_ctor_set(x_593, 0, x_591);
return x_593;
}
}
}
else
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; 
lean_dec(x_546);
lean_dec(x_545);
lean_dec_ref(x_544);
lean_dec_ref(x_538);
lean_dec_ref(x_537);
lean_dec_ref(x_534);
lean_dec(x_531);
lean_dec_ref(x_530);
x_594 = lean_ctor_get(x_585, 0);
lean_inc(x_594);
if (lean_is_exclusive(x_585)) {
 lean_ctor_release(x_585, 0);
 x_595 = x_585;
} else {
 lean_dec_ref(x_585);
 x_595 = lean_box(0);
}
if (lean_is_scalar(x_595)) {
 x_596 = lean_alloc_ctor(1, 1, 0);
} else {
 x_596 = x_595;
}
lean_ctor_set(x_596, 0, x_594);
return x_596;
}
}
}
}
else
{
lean_object* x_703; lean_object* x_704; 
lean_dec_ref(x_524);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_703 = lean_box(0);
if (lean_is_scalar(x_527)) {
 x_704 = lean_alloc_ctor(0, 1, 0);
} else {
 x_704 = x_527;
}
lean_ctor_set(x_704, 0, x_703);
return x_704;
}
}
else
{
lean_object* x_705; lean_object* x_706; lean_object* x_707; 
lean_dec_ref(x_524);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_705 = lean_ctor_get(x_525, 0);
lean_inc(x_705);
if (lean_is_exclusive(x_525)) {
 lean_ctor_release(x_525, 0);
 x_706 = x_525;
} else {
 lean_dec_ref(x_525);
 x_706 = lean_box(0);
}
if (lean_is_scalar(x_706)) {
 x_707 = lean_alloc_ctor(1, 1, 0);
} else {
 x_707 = x_706;
}
lean_ctor_set(x_707, 0, x_705);
return x_707;
}
}
else
{
lean_object* x_708; 
lean_dec_ref(x_520);
lean_dec(x_518);
lean_dec(x_516);
lean_dec(x_515);
lean_dec(x_514);
lean_dec(x_513);
lean_dec(x_512);
lean_dec(x_511);
lean_dec(x_509);
lean_dec(x_508);
lean_dec_ref(x_507);
lean_dec_ref(x_506);
lean_dec_ref(x_505);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_708 = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(x_510);
return x_708;
}
}
block_30:
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_12);
x_24 = l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(x_23, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_ctor_set(x_24, 0, x_27);
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_24);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
else
{
return x_24;
}
}
block_42:
{
lean_object* x_39; 
x_39 = l_Int_Linear_Poly_updateOccs___redArg(x_31, x_33, x_34, x_35, x_36, x_37);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec(x_35);
lean_dec_ref(x_34);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec_ref(x_39);
x_40 = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
x_41 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_40, x_32, x_33);
lean_dec(x_33);
return x_41;
}
else
{
lean_dec(x_33);
lean_dec_ref(x_32);
return x_39;
}
}
block_46:
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_13);
x_14 = l_Int_Linear_Poly_normCommRing_x3f(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_inc(x_12);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(12, 3, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_18);
lean_ctor_set(x_21, 2, x_19);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_22, 2, x_21);
x_23 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_15);
x_24 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_24;
}
}
else
{
uint8_t x_25; 
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
x_25 = !lean_is_exclusive(x_14);
if (x_25 == 0)
{
return x_14;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_14, 0);
lean_inc(x_26);
lean_dec(x_14);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Dvd", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dvd", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Int", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Linear", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("of_not_dvd", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__5;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("non-linear divisibility constraint found", 40, 40);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_16; 
lean_inc_ref(x_1);
x_16 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_22; uint8_t x_23; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_18 = x_16;
} else {
 lean_dec_ref(x_16);
 x_18 = lean_box(0);
}
x_22 = l_Lean_Expr_cleanupAnnotations(x_17);
x_23 = l_Lean_Expr_isApp(x_22);
if (x_23 == 0)
{
lean_dec_ref(x_22);
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
goto block_21;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_22, 1);
lean_inc_ref(x_24);
x_25 = l_Lean_Expr_appFnCleanup___redArg(x_22);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec_ref(x_25);
lean_dec_ref(x_24);
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
goto block_21;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_27);
x_28 = l_Lean_Expr_appFnCleanup___redArg(x_25);
x_29 = l_Lean_Expr_isApp(x_28);
if (x_29 == 0)
{
lean_dec_ref(x_28);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
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
goto block_21;
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_28, 1);
lean_inc_ref(x_30);
x_31 = l_Lean_Expr_appFnCleanup___redArg(x_28);
x_32 = l_Lean_Expr_isApp(x_31);
if (x_32 == 0)
{
lean_dec_ref(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
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
goto block_21;
}
else
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = l_Lean_Expr_appFnCleanup___redArg(x_31);
x_34 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2;
x_35 = l_Lean_Expr_isConstOf(x_33, x_34);
lean_dec_ref(x_33);
if (x_35 == 0)
{
lean_dec_ref(x_30);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
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
goto block_21;
}
else
{
lean_object* x_36; 
lean_dec(x_18);
x_36 = l_Lean_Meta_Structural_isInstDvdInt___redArg(x_30, x_8);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec_ref(x_27);
lean_dec_ref(x_24);
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
x_40 = lean_box(0);
lean_ctor_set(x_36, 0, x_40);
return x_36;
}
else
{
lean_object* x_41; 
lean_free_object(x_36);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_27);
x_41 = l_Lean_Meta_getIntValue_x3f(x_27, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
if (lean_obj_tag(x_42) == 1)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_inc_ref(x_1);
x_45 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_4, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = lean_unbox(x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
lean_free_object(x_42);
lean_dec(x_44);
lean_inc_ref(x_1);
x_48 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_4, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_unbox(x_50);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
lean_dec_ref(x_27);
lean_dec_ref(x_24);
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
x_52 = lean_box(0);
lean_ctor_set(x_48, 0, x_52);
return x_48;
}
else
{
lean_object* x_53; 
lean_free_object(x_48);
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
x_53 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec_ref(x_53);
x_55 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7;
x_56 = l_Lean_eagerReflBoolTrue;
x_57 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_54);
x_58 = l_Lean_mkApp4(x_55, x_27, x_24, x_56, x_57);
x_59 = lean_unsigned_to_nat(0u);
x_60 = l_Lean_Meta_Grind_pushNewFact(x_58, x_59, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_60;
}
else
{
uint8_t x_61; 
lean_dec_ref(x_27);
lean_dec_ref(x_24);
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
x_61 = !lean_is_exclusive(x_53);
if (x_61 == 0)
{
return x_53;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_53, 0);
lean_inc(x_62);
lean_dec(x_53);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
}
}
}
else
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_48, 0);
lean_inc(x_64);
lean_dec(x_48);
x_65 = lean_unbox(x_64);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
lean_dec_ref(x_27);
lean_dec_ref(x_24);
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
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
return x_67;
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
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec_ref(x_68);
x_70 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7;
x_71 = l_Lean_eagerReflBoolTrue;
x_72 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_69);
x_73 = l_Lean_mkApp4(x_70, x_27, x_24, x_71, x_72);
x_74 = lean_unsigned_to_nat(0u);
x_75 = l_Lean_Meta_Grind_pushNewFact(x_73, x_74, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec_ref(x_27);
lean_dec_ref(x_24);
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
x_76 = lean_ctor_get(x_68, 0);
lean_inc(x_76);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 x_77 = x_68;
} else {
 lean_dec_ref(x_68);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 1, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_76);
return x_78;
}
}
}
}
else
{
uint8_t x_79; 
lean_dec_ref(x_27);
lean_dec_ref(x_24);
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
x_79 = !lean_is_exclusive(x_48);
if (x_79 == 0)
{
return x_48;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_48, 0);
lean_inc(x_80);
lean_dec(x_48);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_80);
return x_81;
}
}
}
else
{
lean_object* x_82; 
lean_dec_ref(x_27);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_82 = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec_ref(x_82);
lean_ctor_set_tag(x_42, 0);
lean_ctor_set(x_42, 0, x_1);
x_84 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_84, 0, x_44);
lean_ctor_set(x_84, 1, x_83);
lean_ctor_set(x_84, 2, x_42);
x_85 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(x_84, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_85;
}
else
{
uint8_t x_86; 
lean_free_object(x_42);
lean_dec(x_44);
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
x_86 = !lean_is_exclusive(x_82);
if (x_86 == 0)
{
return x_82;
}
else
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_82, 0);
lean_inc(x_87);
lean_dec(x_82);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
return x_88;
}
}
}
}
else
{
uint8_t x_89; 
lean_free_object(x_42);
lean_dec(x_44);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
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
x_89 = !lean_is_exclusive(x_45);
if (x_89 == 0)
{
return x_45;
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_45, 0);
lean_inc(x_90);
lean_dec(x_45);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_42, 0);
lean_inc(x_92);
lean_dec(x_42);
lean_inc_ref(x_1);
x_93 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_4, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
lean_dec_ref(x_93);
x_95 = lean_unbox(x_94);
lean_dec(x_94);
if (x_95 == 0)
{
lean_object* x_96; 
lean_dec(x_92);
lean_inc_ref(x_1);
x_96 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_4, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 x_98 = x_96;
} else {
 lean_dec_ref(x_96);
 x_98 = lean_box(0);
}
x_99 = lean_unbox(x_97);
lean_dec(x_97);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; 
lean_dec_ref(x_27);
lean_dec_ref(x_24);
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
x_100 = lean_box(0);
if (lean_is_scalar(x_98)) {
 x_101 = lean_alloc_ctor(0, 1, 0);
} else {
 x_101 = x_98;
}
lean_ctor_set(x_101, 0, x_100);
return x_101;
}
else
{
lean_object* x_102; 
lean_dec(x_98);
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
x_102 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
lean_dec_ref(x_102);
x_104 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7;
x_105 = l_Lean_eagerReflBoolTrue;
x_106 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_103);
x_107 = l_Lean_mkApp4(x_104, x_27, x_24, x_105, x_106);
x_108 = lean_unsigned_to_nat(0u);
x_109 = l_Lean_Meta_Grind_pushNewFact(x_107, x_108, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec_ref(x_27);
lean_dec_ref(x_24);
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
x_110 = lean_ctor_get(x_102, 0);
lean_inc(x_110);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 x_111 = x_102;
} else {
 lean_dec_ref(x_102);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 1, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_110);
return x_112;
}
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec_ref(x_27);
lean_dec_ref(x_24);
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
x_113 = lean_ctor_get(x_96, 0);
lean_inc(x_113);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 x_114 = x_96;
} else {
 lean_dec_ref(x_96);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 1, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_113);
return x_115;
}
}
else
{
lean_object* x_116; 
lean_dec_ref(x_27);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_116 = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
lean_dec_ref(x_116);
x_118 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_118, 0, x_1);
x_119 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_119, 0, x_92);
lean_ctor_set(x_119, 1, x_117);
lean_ctor_set(x_119, 2, x_118);
x_120 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(x_119, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_92);
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
x_121 = lean_ctor_get(x_116, 0);
lean_inc(x_121);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 x_122 = x_116;
} else {
 lean_dec_ref(x_116);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 1, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_121);
return x_123;
}
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_92);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
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
x_124 = lean_ctor_get(x_93, 0);
lean_inc(x_124);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 x_125 = x_93;
} else {
 lean_dec_ref(x_93);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(1, 1, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_124);
return x_126;
}
}
}
else
{
lean_object* x_127; 
lean_dec(x_42);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec(x_2);
x_127 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; uint8_t x_129; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
lean_dec_ref(x_127);
x_129 = lean_ctor_get_uint8(x_128, sizeof(void*)*10 + 14);
lean_dec(x_128);
if (x_129 == 0)
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_12 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_130 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9;
x_131 = l_Lean_indentExpr(x_1);
x_132 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
x_133 = l_Lean_Meta_Grind_reportIssue(x_132, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_133) == 0)
{
lean_dec_ref(x_133);
x_12 = lean_box(0);
goto block_15;
}
else
{
return x_133;
}
}
}
else
{
uint8_t x_134; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_134 = !lean_is_exclusive(x_127);
if (x_134 == 0)
{
return x_127;
}
else
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_127, 0);
lean_inc(x_135);
lean_dec(x_127);
x_136 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_136, 0, x_135);
return x_136;
}
}
}
}
else
{
uint8_t x_137; 
lean_dec_ref(x_27);
lean_dec_ref(x_24);
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
x_137 = !lean_is_exclusive(x_41);
if (x_137 == 0)
{
return x_41;
}
else
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_41, 0);
lean_inc(x_138);
lean_dec(x_41);
x_139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_139, 0, x_138);
return x_139;
}
}
}
}
else
{
lean_object* x_140; uint8_t x_141; 
x_140 = lean_ctor_get(x_36, 0);
lean_inc(x_140);
lean_dec(x_36);
x_141 = lean_unbox(x_140);
lean_dec(x_140);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; 
lean_dec_ref(x_27);
lean_dec_ref(x_24);
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
x_142 = lean_box(0);
x_143 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_143, 0, x_142);
return x_143;
}
else
{
lean_object* x_144; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_27);
x_144 = l_Lean_Meta_getIntValue_x3f(x_27, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
lean_dec_ref(x_144);
if (lean_obj_tag(x_145) == 1)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 x_147 = x_145;
} else {
 lean_dec_ref(x_145);
 x_147 = lean_box(0);
}
lean_inc_ref(x_1);
x_148 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_4, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; uint8_t x_150; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
lean_dec_ref(x_148);
x_150 = lean_unbox(x_149);
lean_dec(x_149);
if (x_150 == 0)
{
lean_object* x_151; 
lean_dec(x_147);
lean_dec(x_146);
lean_inc_ref(x_1);
x_151 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_4, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 x_153 = x_151;
} else {
 lean_dec_ref(x_151);
 x_153 = lean_box(0);
}
x_154 = lean_unbox(x_152);
lean_dec(x_152);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; 
lean_dec_ref(x_27);
lean_dec_ref(x_24);
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
x_155 = lean_box(0);
if (lean_is_scalar(x_153)) {
 x_156 = lean_alloc_ctor(0, 1, 0);
} else {
 x_156 = x_153;
}
lean_ctor_set(x_156, 0, x_155);
return x_156;
}
else
{
lean_object* x_157; 
lean_dec(x_153);
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
x_157 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
lean_dec_ref(x_157);
x_159 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7;
x_160 = l_Lean_eagerReflBoolTrue;
x_161 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_158);
x_162 = l_Lean_mkApp4(x_159, x_27, x_24, x_160, x_161);
x_163 = lean_unsigned_to_nat(0u);
x_164 = l_Lean_Meta_Grind_pushNewFact(x_162, x_163, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_164;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_dec_ref(x_27);
lean_dec_ref(x_24);
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
x_165 = lean_ctor_get(x_157, 0);
lean_inc(x_165);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 x_166 = x_157;
} else {
 lean_dec_ref(x_157);
 x_166 = lean_box(0);
}
if (lean_is_scalar(x_166)) {
 x_167 = lean_alloc_ctor(1, 1, 0);
} else {
 x_167 = x_166;
}
lean_ctor_set(x_167, 0, x_165);
return x_167;
}
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec_ref(x_27);
lean_dec_ref(x_24);
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
x_168 = lean_ctor_get(x_151, 0);
lean_inc(x_168);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 x_169 = x_151;
} else {
 lean_dec_ref(x_151);
 x_169 = lean_box(0);
}
if (lean_is_scalar(x_169)) {
 x_170 = lean_alloc_ctor(1, 1, 0);
} else {
 x_170 = x_169;
}
lean_ctor_set(x_170, 0, x_168);
return x_170;
}
}
else
{
lean_object* x_171; 
lean_dec_ref(x_27);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_171 = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
lean_dec_ref(x_171);
if (lean_is_scalar(x_147)) {
 x_173 = lean_alloc_ctor(0, 1, 0);
} else {
 x_173 = x_147;
 lean_ctor_set_tag(x_173, 0);
}
lean_ctor_set(x_173, 0, x_1);
x_174 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_174, 0, x_146);
lean_ctor_set(x_174, 1, x_172);
lean_ctor_set(x_174, 2, x_173);
x_175 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(x_174, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_175;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_147);
lean_dec(x_146);
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
x_176 = lean_ctor_get(x_171, 0);
lean_inc(x_176);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 x_177 = x_171;
} else {
 lean_dec_ref(x_171);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(1, 1, 0);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_176);
return x_178;
}
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_147);
lean_dec(x_146);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
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
x_179 = lean_ctor_get(x_148, 0);
lean_inc(x_179);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 x_180 = x_148;
} else {
 lean_dec_ref(x_148);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(1, 1, 0);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_179);
return x_181;
}
}
else
{
lean_object* x_182; 
lean_dec(x_145);
lean_dec_ref(x_27);
lean_dec_ref(x_24);
lean_dec(x_2);
x_182 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
if (lean_obj_tag(x_182) == 0)
{
lean_object* x_183; uint8_t x_184; 
x_183 = lean_ctor_get(x_182, 0);
lean_inc(x_183);
lean_dec_ref(x_182);
x_184 = lean_ctor_get_uint8(x_183, sizeof(void*)*10 + 14);
lean_dec(x_183);
if (x_184 == 0)
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_12 = lean_box(0);
goto block_15;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_185 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9;
x_186 = l_Lean_indentExpr(x_1);
x_187 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
x_188 = l_Lean_Meta_Grind_reportIssue(x_187, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_188) == 0)
{
lean_dec_ref(x_188);
x_12 = lean_box(0);
goto block_15;
}
else
{
return x_188;
}
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_189 = lean_ctor_get(x_182, 0);
lean_inc(x_189);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 x_190 = x_182;
} else {
 lean_dec_ref(x_182);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 1, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_189);
return x_191;
}
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec_ref(x_27);
lean_dec_ref(x_24);
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
x_192 = lean_ctor_get(x_144, 0);
lean_inc(x_192);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 x_193 = x_144;
} else {
 lean_dec_ref(x_144);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(1, 1, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_192);
return x_194;
}
}
}
}
else
{
uint8_t x_195; 
lean_dec_ref(x_27);
lean_dec_ref(x_24);
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
x_195 = !lean_is_exclusive(x_36);
if (x_195 == 0)
{
return x_36;
}
else
{
lean_object* x_196; lean_object* x_197; 
x_196 = lean_ctor_get(x_36, 0);
lean_inc(x_196);
lean_dec(x_36);
x_197 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_197, 0, x_196);
return x_197;
}
}
}
}
}
}
}
block_21:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
if (lean_is_scalar(x_18)) {
 x_20 = lean_alloc_ctor(0, 1, 0);
} else {
 x_20 = x_18;
}
lean_ctor_set(x_20, 0, x_19);
return x_20;
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
x_198 = !lean_is_exclusive(x_16);
if (x_198 == 0)
{
return x_16;
}
else
{
lean_object* x_199; lean_object* x_200; 
x_199 = lean_ctor_get(x_16, 0);
lean_inc(x_199);
lean_dec(x_16);
x_200 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_200, 0, x_199);
return x_200;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Nat", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("emod_pos_of_not_dvd", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ToInt", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("of_dvd", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__5;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__4;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_16; lean_object* x_20; uint8_t x_21; 
lean_inc_ref(x_1);
x_20 = l_Lean_Expr_cleanupAnnotations(x_1);
x_21 = l_Lean_Expr_isApp(x_20);
if (x_21 == 0)
{
lean_dec_ref(x_20);
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
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_22);
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_20);
x_24 = l_Lean_Expr_isApp(x_23);
if (x_24 == 0)
{
lean_dec_ref(x_23);
lean_dec_ref(x_22);
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
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_23, 1);
lean_inc_ref(x_25);
x_26 = l_Lean_Expr_appFnCleanup___redArg(x_23);
x_27 = l_Lean_Expr_isApp(x_26);
if (x_27 == 0)
{
lean_dec_ref(x_26);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
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
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_ctor_get(x_26, 1);
lean_inc_ref(x_28);
x_29 = l_Lean_Expr_appFnCleanup___redArg(x_26);
x_30 = l_Lean_Expr_isApp(x_29);
if (x_30 == 0)
{
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
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
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = l_Lean_Expr_appFnCleanup___redArg(x_29);
x_32 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2;
x_33 = l_Lean_Expr_isConstOf(x_31, x_32);
lean_dec_ref(x_31);
if (x_33 == 0)
{
lean_dec_ref(x_28);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
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
lean_object* x_34; 
x_34 = l_Lean_Meta_Structural_isInstDvdNat___redArg(x_28, x_8);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_unbox(x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_dec_ref(x_25);
lean_dec_ref(x_22);
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
x_38 = lean_box(0);
lean_ctor_set(x_34, 0, x_38);
return x_34;
}
else
{
lean_object* x_39; 
lean_free_object(x_34);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_39 = l_Lean_Meta_getNatValue_x3f(x_25, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
if (lean_obj_tag(x_40) == 1)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
lean_inc_ref(x_1);
x_42 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_4, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec_ref(x_42);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_41);
lean_inc_ref(x_1);
x_45 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_4, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_unbox(x_47);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec_ref(x_25);
lean_dec_ref(x_22);
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
x_49 = lean_box(0);
lean_ctor_set(x_45, 0, x_49);
return x_45;
}
else
{
lean_object* x_50; 
lean_free_object(x_45);
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
x_50 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec_ref(x_50);
x_52 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3;
x_53 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_51);
x_54 = l_Lean_mkApp3(x_52, x_25, x_22, x_53);
x_55 = lean_unsigned_to_nat(0u);
x_56 = l_Lean_Meta_Grind_pushNewFact(x_54, x_55, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_56;
}
else
{
uint8_t x_57; 
lean_dec_ref(x_25);
lean_dec_ref(x_22);
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
x_57 = !lean_is_exclusive(x_50);
if (x_57 == 0)
{
return x_50;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_50, 0);
lean_inc(x_58);
lean_dec(x_50);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
}
}
}
}
else
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_ctor_get(x_45, 0);
lean_inc(x_60);
lean_dec(x_45);
x_61 = lean_unbox(x_60);
lean_dec(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec_ref(x_25);
lean_dec_ref(x_22);
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
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_62);
return x_63;
}
else
{
lean_object* x_64; 
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
x_64 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
lean_dec_ref(x_64);
x_66 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3;
x_67 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_65);
x_68 = l_Lean_mkApp3(x_66, x_25, x_22, x_67);
x_69 = lean_unsigned_to_nat(0u);
x_70 = l_Lean_Meta_Grind_pushNewFact(x_68, x_69, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec_ref(x_25);
lean_dec_ref(x_22);
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
x_71 = lean_ctor_get(x_64, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 x_72 = x_64;
} else {
 lean_dec_ref(x_64);
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
}
}
else
{
uint8_t x_74; 
lean_dec_ref(x_25);
lean_dec_ref(x_22);
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
x_74 = !lean_is_exclusive(x_45);
if (x_74 == 0)
{
return x_45;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_45, 0);
lean_inc(x_75);
lean_dec(x_45);
x_76 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
}
}
else
{
lean_object* x_77; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_25);
x_77 = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec_ref(x_77);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_22);
x_81 = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec_ref(x_81);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
lean_dec_ref(x_85);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_83);
x_87 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_83, x_86, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
lean_dec_ref(x_87);
x_89 = l_Int_Linear_Expr_norm(x_88);
x_90 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7;
x_91 = l_Lean_mkApp6(x_90, x_25, x_22, x_79, x_83, x_80, x_84);
lean_inc(x_41);
x_92 = lean_nat_to_int(x_41);
x_93 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_93, 0, x_1);
lean_ctor_set(x_93, 1, x_91);
lean_ctor_set(x_93, 2, x_41);
lean_ctor_set(x_93, 3, x_88);
x_94 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_89);
lean_ctor_set(x_94, 2, x_93);
x_95 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(x_94, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_95;
}
else
{
uint8_t x_96; 
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_41);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
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
x_96 = !lean_is_exclusive(x_87);
if (x_96 == 0)
{
return x_87;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_87, 0);
lean_inc(x_97);
lean_dec(x_87);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
return x_98;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_41);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
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
x_99 = !lean_is_exclusive(x_85);
if (x_99 == 0)
{
return x_85;
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_85, 0);
lean_inc(x_100);
lean_dec(x_85);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
return x_101;
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_80);
lean_dec(x_79);
lean_dec(x_41);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
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
x_102 = !lean_is_exclusive(x_81);
if (x_102 == 0)
{
return x_81;
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_81, 0);
lean_inc(x_103);
lean_dec(x_81);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_103);
return x_104;
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_41);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
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
x_105 = !lean_is_exclusive(x_77);
if (x_105 == 0)
{
return x_77;
}
else
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_77, 0);
lean_inc(x_106);
lean_dec(x_77);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_106);
return x_107;
}
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_41);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
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
x_108 = !lean_is_exclusive(x_42);
if (x_108 == 0)
{
return x_42;
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_42, 0);
lean_inc(x_109);
lean_dec(x_42);
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_109);
return x_110;
}
}
}
else
{
lean_object* x_111; 
lean_dec(x_40);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec(x_2);
x_111 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; uint8_t x_113; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
lean_dec_ref(x_111);
x_113 = lean_ctor_get_uint8(x_112, sizeof(void*)*10 + 14);
lean_dec(x_112);
if (x_113 == 0)
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_16 = lean_box(0);
goto block_19;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9;
x_115 = l_Lean_indentExpr(x_1);
x_116 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = l_Lean_Meta_Grind_reportIssue(x_116, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_117) == 0)
{
lean_dec_ref(x_117);
x_16 = lean_box(0);
goto block_19;
}
else
{
return x_117;
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_118 = !lean_is_exclusive(x_111);
if (x_118 == 0)
{
return x_111;
}
else
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_111, 0);
lean_inc(x_119);
lean_dec(x_111);
x_120 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_120, 0, x_119);
return x_120;
}
}
}
}
else
{
uint8_t x_121; 
lean_dec_ref(x_25);
lean_dec_ref(x_22);
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
x_121 = !lean_is_exclusive(x_39);
if (x_121 == 0)
{
return x_39;
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_39, 0);
lean_inc(x_122);
lean_dec(x_39);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_122);
return x_123;
}
}
}
}
else
{
lean_object* x_124; uint8_t x_125; 
x_124 = lean_ctor_get(x_34, 0);
lean_inc(x_124);
lean_dec(x_34);
x_125 = lean_unbox(x_124);
lean_dec(x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; 
lean_dec_ref(x_25);
lean_dec_ref(x_22);
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
x_126 = lean_box(0);
x_127 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_127, 0, x_126);
return x_127;
}
else
{
lean_object* x_128; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
x_128 = l_Lean_Meta_getNatValue_x3f(x_25, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
lean_dec_ref(x_128);
if (lean_obj_tag(x_129) == 1)
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
lean_dec_ref(x_129);
lean_inc_ref(x_1);
x_131 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_4, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; uint8_t x_133; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
lean_dec_ref(x_131);
x_133 = lean_unbox(x_132);
lean_dec(x_132);
if (x_133 == 0)
{
lean_object* x_134; 
lean_dec(x_130);
lean_inc_ref(x_1);
x_134 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_4, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 x_136 = x_134;
} else {
 lean_dec_ref(x_134);
 x_136 = lean_box(0);
}
x_137 = lean_unbox(x_135);
lean_dec(x_135);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; 
lean_dec_ref(x_25);
lean_dec_ref(x_22);
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
x_138 = lean_box(0);
if (lean_is_scalar(x_136)) {
 x_139 = lean_alloc_ctor(0, 1, 0);
} else {
 x_139 = x_136;
}
lean_ctor_set(x_139, 0, x_138);
return x_139;
}
else
{
lean_object* x_140; 
lean_dec(x_136);
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
x_140 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
lean_dec_ref(x_140);
x_142 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3;
x_143 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_141);
x_144 = l_Lean_mkApp3(x_142, x_25, x_22, x_143);
x_145 = lean_unsigned_to_nat(0u);
x_146 = l_Lean_Meta_Grind_pushNewFact(x_144, x_145, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_146;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec_ref(x_25);
lean_dec_ref(x_22);
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
x_147 = lean_ctor_get(x_140, 0);
lean_inc(x_147);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 x_148 = x_140;
} else {
 lean_dec_ref(x_140);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 1, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_147);
return x_149;
}
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec_ref(x_25);
lean_dec_ref(x_22);
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
x_150 = lean_ctor_get(x_134, 0);
lean_inc(x_150);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 x_151 = x_134;
} else {
 lean_dec_ref(x_134);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(1, 1, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_150);
return x_152;
}
}
else
{
lean_object* x_153; 
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_25);
x_153 = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
lean_dec_ref(x_153);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_22);
x_157 = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
lean_dec_ref(x_157);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
lean_dec_ref(x_161);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_159);
x_163 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_159, x_162, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
lean_dec_ref(x_163);
x_165 = l_Int_Linear_Expr_norm(x_164);
x_166 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7;
x_167 = l_Lean_mkApp6(x_166, x_25, x_22, x_155, x_159, x_156, x_160);
lean_inc(x_130);
x_168 = lean_nat_to_int(x_130);
x_169 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_169, 0, x_1);
lean_ctor_set(x_169, 1, x_167);
lean_ctor_set(x_169, 2, x_130);
lean_ctor_set(x_169, 3, x_164);
x_170 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_165);
lean_ctor_set(x_170, 2, x_169);
x_171 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(x_170, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_171;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_130);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
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
x_172 = lean_ctor_get(x_163, 0);
lean_inc(x_172);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 x_173 = x_163;
} else {
 lean_dec_ref(x_163);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(1, 1, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_172);
return x_174;
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_130);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
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
x_175 = lean_ctor_get(x_161, 0);
lean_inc(x_175);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 x_176 = x_161;
} else {
 lean_dec_ref(x_161);
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
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_130);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
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
x_178 = lean_ctor_get(x_157, 0);
lean_inc(x_178);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 x_179 = x_157;
} else {
 lean_dec_ref(x_157);
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
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_130);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
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
x_181 = lean_ctor_get(x_153, 0);
lean_inc(x_181);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 x_182 = x_153;
} else {
 lean_dec_ref(x_153);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_182)) {
 x_183 = lean_alloc_ctor(1, 1, 0);
} else {
 x_183 = x_182;
}
lean_ctor_set(x_183, 0, x_181);
return x_183;
}
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_130);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
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
x_184 = lean_ctor_get(x_131, 0);
lean_inc(x_184);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 x_185 = x_131;
} else {
 lean_dec_ref(x_131);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(1, 1, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_184);
return x_186;
}
}
else
{
lean_object* x_187; 
lean_dec(x_129);
lean_dec_ref(x_25);
lean_dec_ref(x_22);
lean_dec(x_2);
x_187 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; uint8_t x_189; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
lean_dec_ref(x_187);
x_189 = lean_ctor_get_uint8(x_188, sizeof(void*)*10 + 14);
lean_dec(x_188);
if (x_189 == 0)
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_16 = lean_box(0);
goto block_19;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_190 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9;
x_191 = l_Lean_indentExpr(x_1);
x_192 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
x_193 = l_Lean_Meta_Grind_reportIssue(x_192, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_193) == 0)
{
lean_dec_ref(x_193);
x_16 = lean_box(0);
goto block_19;
}
else
{
return x_193;
}
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_194 = lean_ctor_get(x_187, 0);
lean_inc(x_194);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 x_195 = x_187;
} else {
 lean_dec_ref(x_187);
 x_195 = lean_box(0);
}
if (lean_is_scalar(x_195)) {
 x_196 = lean_alloc_ctor(1, 1, 0);
} else {
 x_196 = x_195;
}
lean_ctor_set(x_196, 0, x_194);
return x_196;
}
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec_ref(x_25);
lean_dec_ref(x_22);
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
x_197 = lean_ctor_get(x_128, 0);
lean_inc(x_197);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 x_198 = x_128;
} else {
 lean_dec_ref(x_128);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(1, 1, 0);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_197);
return x_199;
}
}
}
}
else
{
uint8_t x_200; 
lean_dec_ref(x_25);
lean_dec_ref(x_22);
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
x_200 = !lean_is_exclusive(x_34);
if (x_200 == 0)
{
return x_34;
}
else
{
lean_object* x_201; lean_object* x_202; 
x_201 = lean_ctor_get(x_34, 0);
lean_inc(x_201);
lean_dec(x_34);
x_202 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_202, 0, x_201);
return x_202;
}
}
}
}
}
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
block_19:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get_uint8(x_14, sizeof(void*)*10 + 22);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
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
x_16 = lean_box(0);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; 
lean_free_object(x_12);
lean_inc_ref(x_1);
x_17 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_8);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_23; uint8_t x_24; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_19 = x_17;
} else {
 lean_dec_ref(x_17);
 x_19 = lean_box(0);
}
x_23 = l_Lean_Expr_cleanupAnnotations(x_18);
x_24 = l_Lean_Expr_isApp(x_23);
if (x_24 == 0)
{
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
goto block_22;
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = l_Lean_Expr_appFnCleanup___redArg(x_23);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec_ref(x_25);
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
goto block_22;
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = l_Lean_Expr_appFnCleanup___redArg(x_25);
x_28 = l_Lean_Expr_isApp(x_27);
if (x_28 == 0)
{
lean_dec_ref(x_27);
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
goto block_22;
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = l_Lean_Expr_appFnCleanup___redArg(x_27);
x_30 = l_Lean_Expr_isApp(x_29);
if (x_30 == 0)
{
lean_dec_ref(x_29);
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
goto block_22;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_29, 1);
lean_inc_ref(x_31);
x_32 = l_Lean_Expr_appFnCleanup___redArg(x_29);
x_33 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2;
x_34 = l_Lean_Expr_isConstOf(x_32, x_33);
lean_dec_ref(x_32);
if (x_34 == 0)
{
lean_dec_ref(x_31);
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
goto block_22;
}
else
{
lean_object* x_35; uint8_t x_36; 
lean_dec(x_19);
x_35 = l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0;
x_36 = l_Lean_Expr_isConstOf(x_31, x_35);
lean_dec_ref(x_31);
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_37;
}
else
{
lean_object* x_38; 
x_38 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_38;
}
}
}
}
}
}
block_22:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_box(0);
if (lean_is_scalar(x_19)) {
 x_21 = lean_alloc_ctor(0, 1, 0);
} else {
 x_21 = x_19;
}
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
else
{
uint8_t x_39; 
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
x_39 = !lean_is_exclusive(x_17);
if (x_39 == 0)
{
return x_17;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_17, 0);
lean_inc(x_40);
lean_dec(x_17);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
}
else
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_12, 0);
lean_inc(x_42);
lean_dec(x_12);
x_43 = lean_ctor_get_uint8(x_42, sizeof(void*)*10 + 22);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
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
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
else
{
lean_object* x_46; 
lean_inc_ref(x_1);
x_46 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_8);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_52; uint8_t x_53; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 x_48 = x_46;
} else {
 lean_dec_ref(x_46);
 x_48 = lean_box(0);
}
x_52 = l_Lean_Expr_cleanupAnnotations(x_47);
x_53 = l_Lean_Expr_isApp(x_52);
if (x_53 == 0)
{
lean_dec_ref(x_52);
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
goto block_51;
}
else
{
lean_object* x_54; uint8_t x_55; 
x_54 = l_Lean_Expr_appFnCleanup___redArg(x_52);
x_55 = l_Lean_Expr_isApp(x_54);
if (x_55 == 0)
{
lean_dec_ref(x_54);
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
goto block_51;
}
else
{
lean_object* x_56; uint8_t x_57; 
x_56 = l_Lean_Expr_appFnCleanup___redArg(x_54);
x_57 = l_Lean_Expr_isApp(x_56);
if (x_57 == 0)
{
lean_dec_ref(x_56);
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
goto block_51;
}
else
{
lean_object* x_58; uint8_t x_59; 
x_58 = l_Lean_Expr_appFnCleanup___redArg(x_56);
x_59 = l_Lean_Expr_isApp(x_58);
if (x_59 == 0)
{
lean_dec_ref(x_58);
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
goto block_51;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_58, 1);
lean_inc_ref(x_60);
x_61 = l_Lean_Expr_appFnCleanup___redArg(x_58);
x_62 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2;
x_63 = l_Lean_Expr_isConstOf(x_61, x_62);
lean_dec_ref(x_61);
if (x_63 == 0)
{
lean_dec_ref(x_60);
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
goto block_51;
}
else
{
lean_object* x_64; uint8_t x_65; 
lean_dec(x_48);
x_64 = l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0;
x_65 = l_Lean_Expr_isConstOf(x_60, x_64);
lean_dec_ref(x_60);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_66;
}
else
{
lean_object* x_67; 
x_67 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_67;
}
}
}
}
}
}
block_51:
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_box(0);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 1, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
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
x_68 = lean_ctor_get(x_46, 0);
lean_inc(x_68);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 x_69 = x_46;
} else {
 lean_dec_ref(x_46);
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
else
{
uint8_t x_71; 
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
x_71 = !lean_is_exclusive(x_12);
if (x_71 == 0)
{
return x_12;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_12, 0);
lean_inc(x_72);
lean_dec(x_12);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
return x_73;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2;
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed), 11, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_8____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_8_();
return x_2;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin);
lean_object* initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* initialize_Init_Grind_Propagator(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Proof(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(uint8_t builtin);
lean_object* initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_OfNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Propagator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Proof(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_NatInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1);
l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0 = _init_l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0);
l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__1 = _init_l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__1();
lean_mark_persistent(l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__1);
l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__0 = _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__0();
l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__1 = _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__1();
lean_mark_persistent(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__1);
l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__2 = _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__2();
lean_mark_persistent(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__3 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__3);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6);
l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__0 = _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__0);
l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__1 = _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__1();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__1);
l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2 = _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2);
l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3 = _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3);
l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4 = _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4);
l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5 = _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__6 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__6);
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7);
l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__0 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__0);
l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3);
l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4);
l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__5 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__5);
l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6);
l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7);
l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8);
l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9);
l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0);
l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__1 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__1);
l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2);
l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3);
l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__4 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__4();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__4);
l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__5 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__5();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__5);
l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6);
l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7);
l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0);
if (builtin) {res = l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
