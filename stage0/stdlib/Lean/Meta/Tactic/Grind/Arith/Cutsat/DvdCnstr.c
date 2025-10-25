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
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1;
extern lean_object* l_Lean_maxRecDepthErrorMessage;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__4;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__0;
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Meta_Grind_pushNewFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0;
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__3;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_coeff(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static double l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__0;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4;
double lean_float_of_nat(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstDvdInt___redArg(lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1830001947____hygCtx___hyg_8____boxed(lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
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
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__8;
lean_object* l_Lean_Meta_Grind_isEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_updateOccs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__6;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1;
lean_object* l_Int_Linear_Expr_norm(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkOfEqFalseCore(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1830001947____hygCtx___hyg_8_();
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
lean_object* l_Lean_Meta_Grind_mkEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__2;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_norm(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Int_Linear_Poly_isUnsatDvd(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Int_Linear_Poly_isSorted(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___boxed(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6;
lean_object* l_Lean_Meta_Grind_isEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2;
lean_object* l_Int_Linear_Poly_normCommRing_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_div(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstDvdNat___redArg(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd_spec__0(lean_object*);
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5;
lean_object* lean_int_neg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__0;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_natToInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_int_ediv(x_5, x_2);
lean_dec(x_5);
x_8 = l_Int_Linear_Poly_div(x_2, x_4);
lean_dec(x_2);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_3);
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
x_17 = l_Int_Linear_Poly_getConst(x_14);
x_18 = lean_int_emod(x_17, x_16);
lean_dec(x_17);
x_19 = lean_int_dec_eq(x_18, x_15);
lean_dec(x_15);
lean_dec(x_18);
if (x_19 == 0)
{
x_2 = x_16;
x_3 = x_12;
x_4 = x_14;
x_5 = x_13;
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
x_2 = x_16;
x_3 = x_12;
x_4 = x_14;
x_5 = x_13;
x_6 = x_19;
goto block_11;
}
else
{
lean_dec(x_16);
lean_dec_ref(x_14);
lean_dec(x_13);
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
x_13 = x_24;
x_14 = x_25;
x_15 = x_27;
x_16 = x_26;
goto block_22;
}
else
{
lean_object* x_29; 
x_29 = lean_int_neg(x_26);
lean_dec(x_26);
x_12 = x_23;
x_13 = x_24;
x_14 = x_25;
x_15 = x_27;
x_16 = x_29;
goto block_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_1, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_1, x_2, x_7, x_8, x_9, x_10);
return x_12;
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
x_1 = lean_mk_string_unchecked("cutsat", 6, 6);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_34; 
x_15 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4;
x_16 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_15, x_12);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 x_18 = x_16;
} else {
 lean_dec_ref(x_16);
 x_18 = lean_box(0);
}
x_19 = lean_ctor_get(x_3, 0);
x_20 = lean_ctor_get(x_5, 0);
x_21 = lean_ctor_get(x_5, 1);
x_22 = lean_int_mul(x_1, x_20);
x_23 = lean_nat_abs(x_22);
lean_dec(x_22);
x_24 = lean_nat_to_int(x_23);
lean_inc_ref(x_21);
x_25 = l_Int_Linear_Poly_mul(x_21, x_1);
x_26 = lean_int_neg(x_4);
lean_inc_ref(x_19);
x_27 = l_Int_Linear_Poly_mul(x_19, x_26);
lean_dec(x_26);
x_28 = l_Int_Linear_Poly_combine(x_25, x_27);
x_34 = lean_unbox(x_17);
lean_dec(x_17);
if (x_34 == 0)
{
x_29 = lean_box(0);
goto block_33;
}
else
{
lean_object* x_35; 
x_35 = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(x_2, x_6, x_12);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec_ref(x_35);
lean_inc_ref(x_3);
x_37 = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(x_3, x_6, x_12);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
lean_inc_ref(x_5);
x_39 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_5, x_6, x_12);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = l_Lean_MessageData_ofExpr(x_36);
x_42 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_38);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_42);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_40);
x_47 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_15, x_46, x_10, x_11, x_12, x_13);
lean_dec_ref(x_47);
x_29 = lean_box(0);
goto block_33;
}
else
{
uint8_t x_48; 
lean_dec(x_38);
lean_dec(x_36);
lean_dec_ref(x_28);
lean_dec(x_24);
lean_dec(x_18);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_39);
if (x_48 == 0)
{
return x_39;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_39, 0);
lean_inc(x_49);
lean_dec(x_39);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_36);
lean_dec_ref(x_28);
lean_dec(x_24);
lean_dec(x_18);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_37);
if (x_51 == 0)
{
return x_37;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_37, 0);
lean_inc(x_52);
lean_dec(x_37);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec_ref(x_28);
lean_dec(x_24);
lean_dec(x_18);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_35);
if (x_54 == 0)
{
return x_35;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_35, 0);
lean_inc(x_55);
lean_dec(x_35);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
block_33:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_alloc_ctor(8, 3, 0);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_3);
lean_ctor_set(x_30, 2, x_5);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_28);
lean_ctor_set(x_31, 2, x_30);
if (lean_is_scalar(x_18)) {
 x_32 = lean_alloc_ctor(0, 1, 0);
} else {
 x_32 = x_18;
}
lean_ctor_set(x_32, 0, x_31);
return x_32;
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_15;
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
lean_object* x_1; 
x_1 = l_Lean_maxRecDepthErrorMessage;
return x_1;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5;
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
x_3 = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__6;
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
x_14 = lean_ctor_get(x_8, 2);
x_15 = lean_ctor_get(x_8, 3);
x_16 = lean_ctor_get(x_8, 4);
x_17 = lean_ctor_get(x_8, 5);
x_18 = lean_ctor_get(x_8, 6);
x_19 = lean_ctor_get(x_8, 7);
x_20 = lean_ctor_get(x_8, 8);
x_21 = lean_ctor_get(x_8, 9);
x_22 = lean_ctor_get(x_8, 10);
x_23 = lean_ctor_get(x_8, 11);
x_24 = lean_ctor_get(x_8, 12);
x_25 = lean_ctor_get(x_8, 13);
x_26 = lean_nat_dec_eq(x_15, x_16);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_1, 1);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_15, x_28);
lean_dec(x_15);
lean_ctor_set(x_8, 3, x_29);
lean_inc_ref(x_27);
x_30 = l_Int_Linear_Poly_findVarToSubst___redArg(x_27, x_2, x_8);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_30, 0);
if (lean_obj_tag(x_32) == 0)
{
lean_dec_ref(x_8);
lean_ctor_set(x_30, 0, x_1);
return x_30;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_free_object(x_30);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_ctor_get(x_34, 0);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_ctor_get(x_35, 0);
x_39 = l_Int_Linear_Poly_coeff(x_38, x_37);
x_40 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(x_39, x_37, x_35, x_36, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_36);
lean_dec(x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_1 = x_41;
goto _start;
}
else
{
lean_dec_ref(x_8);
return x_40;
}
}
}
else
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_30, 0);
lean_inc(x_43);
lean_dec(x_30);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
lean_dec_ref(x_8);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_1);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec_ref(x_43);
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
x_52 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(x_51, x_49, x_47, x_48, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_dec_ref(x_8);
return x_52;
}
}
}
}
else
{
uint8_t x_55; 
lean_dec_ref(x_8);
lean_dec_ref(x_1);
x_55 = !lean_is_exclusive(x_30);
if (x_55 == 0)
{
return x_30;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_30, 0);
lean_inc(x_56);
lean_dec(x_30);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; 
lean_free_object(x_8);
lean_dec_ref(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec_ref(x_12);
lean_dec_ref(x_1);
x_58 = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(x_17);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; uint8_t x_75; 
x_59 = lean_ctor_get(x_8, 0);
x_60 = lean_ctor_get(x_8, 1);
x_61 = lean_ctor_get(x_8, 2);
x_62 = lean_ctor_get(x_8, 3);
x_63 = lean_ctor_get(x_8, 4);
x_64 = lean_ctor_get(x_8, 5);
x_65 = lean_ctor_get(x_8, 6);
x_66 = lean_ctor_get(x_8, 7);
x_67 = lean_ctor_get(x_8, 8);
x_68 = lean_ctor_get(x_8, 9);
x_69 = lean_ctor_get(x_8, 10);
x_70 = lean_ctor_get(x_8, 11);
x_71 = lean_ctor_get_uint8(x_8, sizeof(void*)*14);
x_72 = lean_ctor_get(x_8, 12);
x_73 = lean_ctor_get_uint8(x_8, sizeof(void*)*14 + 1);
x_74 = lean_ctor_get(x_8, 13);
lean_inc(x_74);
lean_inc(x_72);
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
lean_inc(x_59);
lean_dec(x_8);
x_75 = lean_nat_dec_eq(x_62, x_63);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_ctor_get(x_1, 1);
x_77 = lean_unsigned_to_nat(1u);
x_78 = lean_nat_add(x_62, x_77);
lean_dec(x_62);
x_79 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_79, 0, x_59);
lean_ctor_set(x_79, 1, x_60);
lean_ctor_set(x_79, 2, x_61);
lean_ctor_set(x_79, 3, x_78);
lean_ctor_set(x_79, 4, x_63);
lean_ctor_set(x_79, 5, x_64);
lean_ctor_set(x_79, 6, x_65);
lean_ctor_set(x_79, 7, x_66);
lean_ctor_set(x_79, 8, x_67);
lean_ctor_set(x_79, 9, x_68);
lean_ctor_set(x_79, 10, x_69);
lean_ctor_set(x_79, 11, x_70);
lean_ctor_set(x_79, 12, x_72);
lean_ctor_set(x_79, 13, x_74);
lean_ctor_set_uint8(x_79, sizeof(void*)*14, x_71);
lean_ctor_set_uint8(x_79, sizeof(void*)*14 + 1, x_73);
lean_inc_ref(x_76);
x_80 = l_Int_Linear_Poly_findVarToSubst___redArg(x_76, x_2, x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 x_82 = x_80;
} else {
 lean_dec_ref(x_80);
 x_82 = lean_box(0);
}
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_83; 
lean_dec_ref(x_79);
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(0, 1, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_1);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_82);
x_84 = lean_ctor_get(x_81, 0);
lean_inc(x_84);
lean_dec_ref(x_81);
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
x_91 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(x_90, x_88, x_86, x_87, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_79, x_9);
lean_dec(x_87);
lean_dec(x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
lean_dec_ref(x_91);
x_1 = x_92;
x_8 = x_79;
goto _start;
}
else
{
lean_dec_ref(x_79);
return x_91;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec_ref(x_79);
lean_dec_ref(x_1);
x_94 = lean_ctor_get(x_80, 0);
lean_inc(x_94);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 x_95 = x_80;
} else {
 lean_dec_ref(x_80);
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
lean_object* x_97; 
lean_dec_ref(x_74);
lean_dec(x_72);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec_ref(x_60);
lean_dec_ref(x_59);
lean_dec_ref(x_1);
x_97 = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(x_64);
return x_97;
}
}
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
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(lean_object* x_1, lean_object* x_2) {
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
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("assert", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("store", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2;
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("trivial", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2;
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unsat", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2;
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_41; uint8_t x_45; 
x_45 = !lean_is_exclusive(x_8);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_46 = lean_ctor_get(x_8, 0);
x_47 = lean_ctor_get(x_8, 1);
x_48 = lean_ctor_get(x_8, 2);
x_49 = lean_ctor_get(x_8, 3);
x_50 = lean_ctor_get(x_8, 4);
x_51 = lean_ctor_get(x_8, 5);
x_52 = lean_ctor_get(x_8, 6);
x_53 = lean_ctor_get(x_8, 7);
x_54 = lean_ctor_get(x_8, 8);
x_55 = lean_ctor_get(x_8, 9);
x_56 = lean_ctor_get(x_8, 10);
x_57 = lean_ctor_get(x_8, 11);
x_58 = lean_ctor_get(x_8, 12);
x_59 = lean_ctor_get(x_8, 13);
x_60 = lean_nat_dec_eq(x_49, x_50);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_add(x_49, x_61);
lean_dec(x_49);
lean_ctor_set(x_8, 3, x_62);
x_63 = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(x_2, x_8);
if (lean_obj_tag(x_63) == 0)
{
uint8_t x_64; 
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; uint8_t x_66; 
x_65 = lean_ctor_get(x_63, 0);
x_66 = lean_unbox(x_65);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_298; 
lean_free_object(x_63);
x_211 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4;
x_212 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_211, x_8);
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
lean_dec_ref(x_212);
x_214 = lean_box(0);
x_298 = lean_unbox(x_213);
lean_dec(x_213);
if (x_298 == 0)
{
x_243 = x_2;
x_244 = x_3;
x_245 = x_4;
x_246 = x_5;
x_247 = x_6;
x_248 = x_7;
x_249 = x_8;
x_250 = x_9;
x_251 = lean_box(0);
goto block_297;
}
else
{
lean_object* x_299; 
lean_inc_ref(x_1);
x_299 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_8);
if (lean_obj_tag(x_299) == 0)
{
lean_object* x_300; lean_object* x_301; 
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
lean_dec_ref(x_299);
x_301 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_211, x_300, x_6, x_7, x_8, x_9);
lean_dec_ref(x_301);
x_243 = x_2;
x_244 = x_3;
x_245 = x_4;
x_246 = x_5;
x_247 = x_6;
x_248 = x_7;
x_249 = x_8;
x_250 = x_9;
x_251 = lean_box(0);
goto block_297;
}
else
{
uint8_t x_302; 
lean_dec_ref(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
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
block_210:
{
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
lean_dec(x_81);
lean_dec_ref(x_80);
lean_dec(x_78);
lean_dec(x_75);
lean_dec(x_73);
lean_dec_ref(x_72);
lean_dec(x_71);
lean_dec_ref(x_70);
x_85 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3;
x_86 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_85, x_74);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec_ref(x_86);
x_88 = lean_unbox(x_87);
lean_dec(x_87);
if (x_88 == 0)
{
lean_dec_ref(x_79);
x_29 = x_67;
x_30 = x_83;
x_31 = x_82;
x_32 = x_76;
x_33 = x_68;
x_34 = x_74;
x_35 = x_69;
x_36 = lean_box(0);
goto block_40;
}
else
{
lean_object* x_89; 
x_89 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_79, x_82, x_74);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
lean_dec_ref(x_89);
x_91 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_85, x_90, x_76, x_68, x_74, x_69);
lean_dec_ref(x_91);
x_29 = x_67;
x_30 = x_83;
x_31 = x_82;
x_32 = x_76;
x_33 = x_68;
x_34 = x_74;
x_35 = x_69;
x_36 = lean_box(0);
goto block_40;
}
else
{
uint8_t x_92; 
lean_dec_ref(x_83);
lean_dec(x_82);
lean_dec_ref(x_76);
lean_dec_ref(x_74);
lean_dec(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
x_92 = !lean_is_exclusive(x_89);
if (x_92 == 0)
{
return x_89;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_89, 0);
lean_inc(x_93);
lean_dec(x_89);
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_93);
return x_94;
}
}
}
}
else
{
lean_object* x_95; lean_object* x_96; 
lean_dec_ref(x_83);
lean_dec_ref(x_67);
x_95 = lean_ctor_get(x_84, 0);
lean_inc(x_95);
lean_dec_ref(x_84);
x_96 = lean_ctor_get(x_95, 1);
lean_inc_ref(x_96);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; 
lean_dec_ref(x_96);
lean_dec(x_81);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec(x_73);
lean_dec_ref(x_72);
lean_dec_ref(x_70);
x_97 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_95, x_82, x_75, x_80, x_71, x_76, x_68, x_74, x_69);
lean_dec(x_69);
lean_dec_ref(x_74);
lean_dec(x_68);
lean_dec_ref(x_76);
lean_dec(x_71);
lean_dec_ref(x_80);
lean_dec(x_75);
lean_dec(x_82);
return x_97;
}
else
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_96);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_99 = lean_ctor_get(x_95, 0);
x_100 = lean_ctor_get(x_96, 0);
x_101 = lean_ctor_get(x_96, 2);
x_102 = lean_ctor_get(x_96, 1);
lean_dec(x_102);
x_103 = lean_int_mul(x_78, x_99);
x_104 = lean_int_mul(x_100, x_73);
x_105 = l_Lean_Meta_Grind_Arith_gcdExt(x_103, x_104);
lean_dec(x_104);
lean_dec(x_103);
x_106 = !lean_is_exclusive(x_105);
if (x_106 == 0)
{
lean_object* x_107; uint8_t x_108; 
x_107 = lean_ctor_get(x_105, 1);
x_108 = !lean_is_exclusive(x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_109 = lean_ctor_get(x_105, 0);
x_110 = lean_ctor_get(x_107, 0);
x_111 = lean_ctor_get(x_107, 1);
x_112 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0;
x_113 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_112, x_70, x_82);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec_ref(x_113);
x_114 = lean_int_mul(x_110, x_99);
lean_dec(x_110);
lean_inc_ref(x_72);
x_115 = l_Int_Linear_Poly_mul(x_72, x_114);
lean_dec(x_114);
x_116 = lean_int_mul(x_111, x_73);
lean_dec(x_111);
lean_inc_ref(x_101);
x_117 = l_Int_Linear_Poly_mul(x_101, x_116);
lean_dec(x_116);
x_118 = lean_int_mul(x_73, x_99);
lean_dec(x_73);
x_119 = l_Int_Linear_Poly_combine(x_115, x_117);
lean_inc(x_109);
lean_ctor_set(x_96, 2, x_119);
lean_ctor_set(x_96, 1, x_81);
lean_ctor_set(x_96, 0, x_109);
lean_inc(x_95);
lean_inc_ref(x_79);
lean_ctor_set_tag(x_107, 4);
lean_ctor_set(x_107, 1, x_95);
lean_ctor_set(x_107, 0, x_79);
x_120 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_96);
lean_ctor_set(x_120, 2, x_107);
lean_inc(x_69);
lean_inc_ref(x_74);
lean_inc(x_68);
lean_inc_ref(x_76);
lean_inc(x_71);
lean_inc_ref(x_80);
lean_inc(x_75);
lean_inc(x_82);
x_121 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_120, x_82, x_75, x_80, x_71, x_76, x_68, x_74, x_69);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
lean_dec_ref(x_121);
x_122 = l_Int_Linear_Poly_mul(x_72, x_100);
lean_dec(x_100);
x_123 = lean_int_neg(x_78);
lean_dec(x_78);
x_124 = l_Int_Linear_Poly_mul(x_101, x_123);
lean_dec(x_123);
x_125 = l_Int_Linear_Poly_combine(x_122, x_124);
lean_inc(x_95);
lean_ctor_set_tag(x_105, 5);
lean_ctor_set(x_105, 1, x_95);
lean_ctor_set(x_105, 0, x_79);
x_126 = !lean_is_exclusive(x_95);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_95, 2);
lean_dec(x_127);
x_128 = lean_ctor_get(x_95, 1);
lean_dec(x_128);
x_129 = lean_ctor_get(x_95, 0);
lean_dec(x_129);
lean_ctor_set(x_95, 2, x_105);
lean_ctor_set(x_95, 1, x_125);
lean_ctor_set(x_95, 0, x_109);
x_1 = x_95;
x_2 = x_82;
x_3 = x_75;
x_4 = x_80;
x_5 = x_71;
x_6 = x_76;
x_7 = x_68;
x_8 = x_74;
x_9 = x_69;
goto _start;
}
else
{
lean_object* x_131; 
lean_dec(x_95);
x_131 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_131, 0, x_109);
lean_ctor_set(x_131, 1, x_125);
lean_ctor_set(x_131, 2, x_105);
x_1 = x_131;
x_2 = x_82;
x_3 = x_75;
x_4 = x_80;
x_5 = x_71;
x_6 = x_76;
x_7 = x_68;
x_8 = x_74;
x_9 = x_69;
goto _start;
}
}
else
{
lean_free_object(x_105);
lean_dec(x_109);
lean_dec_ref(x_101);
lean_dec(x_100);
lean_dec(x_95);
lean_dec(x_82);
lean_dec_ref(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec_ref(x_76);
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec_ref(x_72);
lean_dec(x_71);
lean_dec(x_69);
lean_dec(x_68);
return x_121;
}
}
else
{
lean_free_object(x_107);
lean_dec(x_111);
lean_dec(x_110);
lean_free_object(x_105);
lean_dec(x_109);
lean_free_object(x_96);
lean_dec_ref(x_101);
lean_dec(x_100);
lean_dec(x_95);
lean_dec(x_82);
lean_dec(x_81);
lean_dec_ref(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec_ref(x_76);
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec_ref(x_72);
lean_dec(x_71);
lean_dec(x_69);
lean_dec(x_68);
return x_113;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_133 = lean_ctor_get(x_105, 0);
x_134 = lean_ctor_get(x_107, 0);
x_135 = lean_ctor_get(x_107, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_107);
x_136 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0;
x_137 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_136, x_70, x_82);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec_ref(x_137);
x_138 = lean_int_mul(x_134, x_99);
lean_dec(x_134);
lean_inc_ref(x_72);
x_139 = l_Int_Linear_Poly_mul(x_72, x_138);
lean_dec(x_138);
x_140 = lean_int_mul(x_135, x_73);
lean_dec(x_135);
lean_inc_ref(x_101);
x_141 = l_Int_Linear_Poly_mul(x_101, x_140);
lean_dec(x_140);
x_142 = lean_int_mul(x_73, x_99);
lean_dec(x_73);
x_143 = l_Int_Linear_Poly_combine(x_139, x_141);
lean_inc(x_133);
lean_ctor_set(x_96, 2, x_143);
lean_ctor_set(x_96, 1, x_81);
lean_ctor_set(x_96, 0, x_133);
lean_inc(x_95);
lean_inc_ref(x_79);
x_144 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_144, 0, x_79);
lean_ctor_set(x_144, 1, x_95);
x_145 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_96);
lean_ctor_set(x_145, 2, x_144);
lean_inc(x_69);
lean_inc_ref(x_74);
lean_inc(x_68);
lean_inc_ref(x_76);
lean_inc(x_71);
lean_inc_ref(x_80);
lean_inc(x_75);
lean_inc(x_82);
x_146 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_145, x_82, x_75, x_80, x_71, x_76, x_68, x_74, x_69);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec_ref(x_146);
x_147 = l_Int_Linear_Poly_mul(x_72, x_100);
lean_dec(x_100);
x_148 = lean_int_neg(x_78);
lean_dec(x_78);
x_149 = l_Int_Linear_Poly_mul(x_101, x_148);
lean_dec(x_148);
x_150 = l_Int_Linear_Poly_combine(x_147, x_149);
lean_inc(x_95);
lean_ctor_set_tag(x_105, 5);
lean_ctor_set(x_105, 1, x_95);
lean_ctor_set(x_105, 0, x_79);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 lean_ctor_release(x_95, 2);
 x_151 = x_95;
} else {
 lean_dec_ref(x_95);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(0, 3, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_133);
lean_ctor_set(x_152, 1, x_150);
lean_ctor_set(x_152, 2, x_105);
x_1 = x_152;
x_2 = x_82;
x_3 = x_75;
x_4 = x_80;
x_5 = x_71;
x_6 = x_76;
x_7 = x_68;
x_8 = x_74;
x_9 = x_69;
goto _start;
}
else
{
lean_free_object(x_105);
lean_dec(x_133);
lean_dec_ref(x_101);
lean_dec(x_100);
lean_dec(x_95);
lean_dec(x_82);
lean_dec_ref(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec_ref(x_76);
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec_ref(x_72);
lean_dec(x_71);
lean_dec(x_69);
lean_dec(x_68);
return x_146;
}
}
else
{
lean_dec(x_135);
lean_dec(x_134);
lean_free_object(x_105);
lean_dec(x_133);
lean_free_object(x_96);
lean_dec_ref(x_101);
lean_dec(x_100);
lean_dec(x_95);
lean_dec(x_82);
lean_dec(x_81);
lean_dec_ref(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec_ref(x_76);
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec_ref(x_72);
lean_dec(x_71);
lean_dec(x_69);
lean_dec(x_68);
return x_137;
}
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_154 = lean_ctor_get(x_105, 1);
x_155 = lean_ctor_get(x_105, 0);
lean_inc(x_154);
lean_inc(x_155);
lean_dec(x_105);
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
x_159 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0;
x_160 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_159, x_70, x_82);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec_ref(x_160);
x_161 = lean_int_mul(x_156, x_99);
lean_dec(x_156);
lean_inc_ref(x_72);
x_162 = l_Int_Linear_Poly_mul(x_72, x_161);
lean_dec(x_161);
x_163 = lean_int_mul(x_157, x_73);
lean_dec(x_157);
lean_inc_ref(x_101);
x_164 = l_Int_Linear_Poly_mul(x_101, x_163);
lean_dec(x_163);
x_165 = lean_int_mul(x_73, x_99);
lean_dec(x_73);
x_166 = l_Int_Linear_Poly_combine(x_162, x_164);
lean_inc(x_155);
lean_ctor_set(x_96, 2, x_166);
lean_ctor_set(x_96, 1, x_81);
lean_ctor_set(x_96, 0, x_155);
lean_inc(x_95);
lean_inc_ref(x_79);
if (lean_is_scalar(x_158)) {
 x_167 = lean_alloc_ctor(4, 2, 0);
} else {
 x_167 = x_158;
 lean_ctor_set_tag(x_167, 4);
}
lean_ctor_set(x_167, 0, x_79);
lean_ctor_set(x_167, 1, x_95);
x_168 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_96);
lean_ctor_set(x_168, 2, x_167);
lean_inc(x_69);
lean_inc_ref(x_74);
lean_inc(x_68);
lean_inc_ref(x_76);
lean_inc(x_71);
lean_inc_ref(x_80);
lean_inc(x_75);
lean_inc(x_82);
x_169 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_168, x_82, x_75, x_80, x_71, x_76, x_68, x_74, x_69);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec_ref(x_169);
x_170 = l_Int_Linear_Poly_mul(x_72, x_100);
lean_dec(x_100);
x_171 = lean_int_neg(x_78);
lean_dec(x_78);
x_172 = l_Int_Linear_Poly_mul(x_101, x_171);
lean_dec(x_171);
x_173 = l_Int_Linear_Poly_combine(x_170, x_172);
lean_inc(x_95);
x_174 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_174, 0, x_79);
lean_ctor_set(x_174, 1, x_95);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 lean_ctor_release(x_95, 2);
 x_175 = x_95;
} else {
 lean_dec_ref(x_95);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(0, 3, 0);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_155);
lean_ctor_set(x_176, 1, x_173);
lean_ctor_set(x_176, 2, x_174);
x_1 = x_176;
x_2 = x_82;
x_3 = x_75;
x_4 = x_80;
x_5 = x_71;
x_6 = x_76;
x_7 = x_68;
x_8 = x_74;
x_9 = x_69;
goto _start;
}
else
{
lean_dec(x_155);
lean_dec_ref(x_101);
lean_dec(x_100);
lean_dec(x_95);
lean_dec(x_82);
lean_dec_ref(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec_ref(x_76);
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec_ref(x_72);
lean_dec(x_71);
lean_dec(x_69);
lean_dec(x_68);
return x_169;
}
}
else
{
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_free_object(x_96);
lean_dec_ref(x_101);
lean_dec(x_100);
lean_dec(x_95);
lean_dec(x_82);
lean_dec(x_81);
lean_dec_ref(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec_ref(x_76);
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec_ref(x_72);
lean_dec(x_71);
lean_dec(x_69);
lean_dec(x_68);
return x_160;
}
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_178 = lean_ctor_get(x_95, 0);
x_179 = lean_ctor_get(x_96, 0);
x_180 = lean_ctor_get(x_96, 2);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_96);
x_181 = lean_int_mul(x_78, x_178);
x_182 = lean_int_mul(x_179, x_73);
x_183 = l_Lean_Meta_Grind_Arith_gcdExt(x_181, x_182);
lean_dec(x_182);
lean_dec(x_181);
x_184 = lean_ctor_get(x_183, 1);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 0);
lean_inc(x_185);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_186 = x_183;
} else {
 lean_dec_ref(x_183);
 x_186 = lean_box(0);
}
x_187 = lean_ctor_get(x_184, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_184, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_189 = x_184;
} else {
 lean_dec_ref(x_184);
 x_189 = lean_box(0);
}
x_190 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0;
x_191 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_190, x_70, x_82);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec_ref(x_191);
x_192 = lean_int_mul(x_187, x_178);
lean_dec(x_187);
lean_inc_ref(x_72);
x_193 = l_Int_Linear_Poly_mul(x_72, x_192);
lean_dec(x_192);
x_194 = lean_int_mul(x_188, x_73);
lean_dec(x_188);
lean_inc_ref(x_180);
x_195 = l_Int_Linear_Poly_mul(x_180, x_194);
lean_dec(x_194);
x_196 = lean_int_mul(x_73, x_178);
lean_dec(x_73);
x_197 = l_Int_Linear_Poly_combine(x_193, x_195);
lean_inc(x_185);
x_198 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_198, 0, x_185);
lean_ctor_set(x_198, 1, x_81);
lean_ctor_set(x_198, 2, x_197);
lean_inc(x_95);
lean_inc_ref(x_79);
if (lean_is_scalar(x_189)) {
 x_199 = lean_alloc_ctor(4, 2, 0);
} else {
 x_199 = x_189;
 lean_ctor_set_tag(x_199, 4);
}
lean_ctor_set(x_199, 0, x_79);
lean_ctor_set(x_199, 1, x_95);
x_200 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_200, 0, x_196);
lean_ctor_set(x_200, 1, x_198);
lean_ctor_set(x_200, 2, x_199);
lean_inc(x_69);
lean_inc_ref(x_74);
lean_inc(x_68);
lean_inc_ref(x_76);
lean_inc(x_71);
lean_inc_ref(x_80);
lean_inc(x_75);
lean_inc(x_82);
x_201 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_200, x_82, x_75, x_80, x_71, x_76, x_68, x_74, x_69);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec_ref(x_201);
x_202 = l_Int_Linear_Poly_mul(x_72, x_179);
lean_dec(x_179);
x_203 = lean_int_neg(x_78);
lean_dec(x_78);
x_204 = l_Int_Linear_Poly_mul(x_180, x_203);
lean_dec(x_203);
x_205 = l_Int_Linear_Poly_combine(x_202, x_204);
lean_inc(x_95);
if (lean_is_scalar(x_186)) {
 x_206 = lean_alloc_ctor(5, 2, 0);
} else {
 x_206 = x_186;
 lean_ctor_set_tag(x_206, 5);
}
lean_ctor_set(x_206, 0, x_79);
lean_ctor_set(x_206, 1, x_95);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 lean_ctor_release(x_95, 2);
 x_207 = x_95;
} else {
 lean_dec_ref(x_95);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(0, 3, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_185);
lean_ctor_set(x_208, 1, x_205);
lean_ctor_set(x_208, 2, x_206);
x_1 = x_208;
x_2 = x_82;
x_3 = x_75;
x_4 = x_80;
x_5 = x_71;
x_6 = x_76;
x_7 = x_68;
x_8 = x_74;
x_9 = x_69;
goto _start;
}
else
{
lean_dec(x_186);
lean_dec(x_185);
lean_dec_ref(x_180);
lean_dec(x_179);
lean_dec(x_95);
lean_dec(x_82);
lean_dec_ref(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec_ref(x_76);
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec_ref(x_72);
lean_dec(x_71);
lean_dec(x_69);
lean_dec(x_68);
return x_201;
}
}
else
{
lean_dec(x_189);
lean_dec(x_188);
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_185);
lean_dec_ref(x_180);
lean_dec(x_179);
lean_dec(x_95);
lean_dec(x_82);
lean_dec(x_81);
lean_dec_ref(x_80);
lean_dec_ref(x_79);
lean_dec(x_78);
lean_dec_ref(x_76);
lean_dec(x_75);
lean_dec_ref(x_74);
lean_dec(x_73);
lean_dec_ref(x_72);
lean_dec(x_71);
lean_dec(x_69);
lean_dec(x_68);
return x_191;
}
}
}
}
}
block_242:
{
lean_object* x_232; 
x_232 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_223, x_229);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_236; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
lean_dec_ref(x_232);
x_234 = lean_ctor_get(x_233, 6);
lean_inc_ref(x_234);
lean_dec(x_233);
x_235 = lean_ctor_get(x_234, 2);
x_236 = lean_nat_dec_lt(x_221, x_235);
if (x_236 == 0)
{
lean_object* x_237; 
lean_dec_ref(x_234);
x_237 = l_outOfBounds___redArg(x_214);
x_67 = x_215;
x_68 = x_228;
x_69 = x_230;
x_70 = x_216;
x_71 = x_226;
x_72 = x_219;
x_73 = x_220;
x_74 = x_229;
x_75 = x_224;
x_76 = x_227;
x_77 = lean_box(0);
x_78 = x_217;
x_79 = x_218;
x_80 = x_225;
x_81 = x_221;
x_82 = x_223;
x_83 = x_222;
x_84 = x_237;
goto block_210;
}
else
{
lean_object* x_238; 
x_238 = l_Lean_PersistentArray_get_x21___redArg(x_214, x_234, x_221);
x_67 = x_215;
x_68 = x_228;
x_69 = x_230;
x_70 = x_216;
x_71 = x_226;
x_72 = x_219;
x_73 = x_220;
x_74 = x_229;
x_75 = x_224;
x_76 = x_227;
x_77 = lean_box(0);
x_78 = x_217;
x_79 = x_218;
x_80 = x_225;
x_81 = x_221;
x_82 = x_223;
x_83 = x_222;
x_84 = x_238;
goto block_210;
}
}
else
{
uint8_t x_239; 
lean_dec(x_230);
lean_dec_ref(x_229);
lean_dec(x_228);
lean_dec_ref(x_227);
lean_dec(x_226);
lean_dec_ref(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec_ref(x_222);
lean_dec(x_221);
lean_dec(x_220);
lean_dec_ref(x_219);
lean_dec_ref(x_218);
lean_dec(x_217);
lean_dec_ref(x_216);
lean_dec_ref(x_215);
x_239 = !lean_is_exclusive(x_232);
if (x_239 == 0)
{
return x_232;
}
else
{
lean_object* x_240; lean_object* x_241; 
x_240 = lean_ctor_get(x_232, 0);
lean_inc(x_240);
lean_dec(x_232);
x_241 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_241, 0, x_240);
return x_241;
}
}
}
block_297:
{
lean_object* x_252; lean_object* x_253; 
x_252 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc_ref(x_249);
x_253 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(x_252, x_243, x_244, x_245, x_246, x_247, x_248, x_249, x_250);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
lean_dec_ref(x_253);
x_255 = lean_ctor_get(x_254, 0);
x_256 = lean_ctor_get(x_254, 1);
lean_inc(x_255);
x_257 = l_Int_Linear_Poly_isUnsatDvd(x_255, x_256);
if (x_257 == 0)
{
uint8_t x_258; 
x_258 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_254);
if (x_258 == 0)
{
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_259; 
x_259 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_254, x_243, x_244, x_245, x_246, x_247, x_248, x_249, x_250);
lean_dec(x_250);
lean_dec_ref(x_249);
lean_dec(x_248);
lean_dec_ref(x_247);
lean_dec(x_246);
lean_dec_ref(x_245);
lean_dec(x_244);
lean_dec(x_243);
return x_259;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
lean_inc_ref(x_256);
lean_inc(x_255);
x_260 = lean_ctor_get(x_256, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_256, 1);
lean_inc(x_261);
x_262 = lean_ctor_get(x_256, 2);
lean_inc_ref(x_262);
lean_inc(x_254);
x_263 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_254, x_243, x_249);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; uint8_t x_268; uint8_t x_269; 
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
lean_dec_ref(x_263);
lean_inc(x_261);
lean_inc(x_254);
x_265 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed), 3, 2);
lean_closure_set(x_265, 0, x_254);
lean_closure_set(x_265, 1, x_261);
lean_inc(x_261);
x_266 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed), 2, 1);
lean_closure_set(x_266, 0, x_261);
x_267 = 0;
x_268 = lean_unbox(x_264);
lean_dec(x_264);
x_269 = l_Lean_instBEqLBool_beq(x_268, x_267);
if (x_269 == 0)
{
x_215 = x_265;
x_216 = x_266;
x_217 = x_260;
x_218 = x_254;
x_219 = x_262;
x_220 = x_255;
x_221 = x_261;
x_222 = x_256;
x_223 = x_243;
x_224 = x_244;
x_225 = x_245;
x_226 = x_246;
x_227 = x_247;
x_228 = x_248;
x_229 = x_249;
x_230 = x_250;
x_231 = lean_box(0);
goto block_242;
}
else
{
lean_object* x_270; 
lean_inc(x_261);
x_270 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_261, x_243);
if (lean_obj_tag(x_270) == 0)
{
lean_dec_ref(x_270);
x_215 = x_265;
x_216 = x_266;
x_217 = x_260;
x_218 = x_254;
x_219 = x_262;
x_220 = x_255;
x_221 = x_261;
x_222 = x_256;
x_223 = x_243;
x_224 = x_244;
x_225 = x_245;
x_226 = x_246;
x_227 = x_247;
x_228 = x_248;
x_229 = x_249;
x_230 = x_250;
x_231 = lean_box(0);
goto block_242;
}
else
{
lean_dec_ref(x_266);
lean_dec_ref(x_265);
lean_dec_ref(x_262);
lean_dec(x_261);
lean_dec(x_260);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_250);
lean_dec_ref(x_249);
lean_dec(x_248);
lean_dec_ref(x_247);
lean_dec(x_246);
lean_dec_ref(x_245);
lean_dec(x_244);
lean_dec(x_243);
return x_270;
}
}
}
else
{
uint8_t x_271; 
lean_dec_ref(x_262);
lean_dec(x_261);
lean_dec(x_260);
lean_dec_ref(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_250);
lean_dec_ref(x_249);
lean_dec(x_248);
lean_dec_ref(x_247);
lean_dec(x_246);
lean_dec_ref(x_245);
lean_dec(x_244);
lean_dec(x_243);
x_271 = !lean_is_exclusive(x_263);
if (x_271 == 0)
{
return x_263;
}
else
{
lean_object* x_272; lean_object* x_273; 
x_272 = lean_ctor_get(x_263, 0);
lean_inc(x_272);
lean_dec(x_263);
x_273 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_273, 0, x_272);
return x_273;
}
}
}
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; 
lean_dec(x_246);
lean_dec_ref(x_245);
lean_dec(x_244);
x_274 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__6;
x_275 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_274, x_249);
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
lean_dec_ref(x_275);
x_277 = lean_unbox(x_276);
lean_dec(x_276);
if (x_277 == 0)
{
lean_dec(x_254);
lean_dec(x_250);
lean_dec_ref(x_249);
lean_dec(x_248);
lean_dec_ref(x_247);
lean_dec(x_243);
x_41 = lean_box(0);
goto block_44;
}
else
{
lean_object* x_278; 
x_278 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_254, x_243, x_249);
lean_dec(x_243);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; lean_object* x_280; 
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
lean_dec_ref(x_278);
x_280 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_274, x_279, x_247, x_248, x_249, x_250);
lean_dec(x_250);
lean_dec_ref(x_249);
lean_dec(x_248);
lean_dec_ref(x_247);
lean_dec_ref(x_280);
x_41 = lean_box(0);
goto block_44;
}
else
{
uint8_t x_281; 
lean_dec(x_250);
lean_dec_ref(x_249);
lean_dec(x_248);
lean_dec_ref(x_247);
x_281 = !lean_is_exclusive(x_278);
if (x_281 == 0)
{
return x_278;
}
else
{
lean_object* x_282; lean_object* x_283; 
x_282 = lean_ctor_get(x_278, 0);
lean_inc(x_282);
lean_dec(x_278);
x_283 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_283, 0, x_282);
return x_283;
}
}
}
}
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; 
x_284 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__8;
x_285 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_284, x_249);
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
lean_dec_ref(x_285);
x_287 = lean_unbox(x_286);
lean_dec(x_286);
if (x_287 == 0)
{
x_11 = x_254;
x_12 = x_243;
x_13 = x_244;
x_14 = x_245;
x_15 = x_246;
x_16 = x_247;
x_17 = x_248;
x_18 = x_249;
x_19 = x_250;
x_20 = lean_box(0);
goto block_28;
}
else
{
lean_object* x_288; 
lean_inc(x_254);
x_288 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_254, x_243, x_249);
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; lean_object* x_290; 
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
lean_dec_ref(x_288);
x_290 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_284, x_289, x_247, x_248, x_249, x_250);
lean_dec_ref(x_290);
x_11 = x_254;
x_12 = x_243;
x_13 = x_244;
x_14 = x_245;
x_15 = x_246;
x_16 = x_247;
x_17 = x_248;
x_18 = x_249;
x_19 = x_250;
x_20 = lean_box(0);
goto block_28;
}
else
{
uint8_t x_291; 
lean_dec(x_254);
lean_dec(x_250);
lean_dec_ref(x_249);
lean_dec(x_248);
lean_dec_ref(x_247);
lean_dec(x_246);
lean_dec_ref(x_245);
lean_dec(x_244);
lean_dec(x_243);
x_291 = !lean_is_exclusive(x_288);
if (x_291 == 0)
{
return x_288;
}
else
{
lean_object* x_292; lean_object* x_293; 
x_292 = lean_ctor_get(x_288, 0);
lean_inc(x_292);
lean_dec(x_288);
x_293 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_293, 0, x_292);
return x_293;
}
}
}
}
}
else
{
uint8_t x_294; 
lean_dec(x_250);
lean_dec_ref(x_249);
lean_dec(x_248);
lean_dec_ref(x_247);
lean_dec(x_246);
lean_dec_ref(x_245);
lean_dec(x_244);
lean_dec(x_243);
x_294 = !lean_is_exclusive(x_253);
if (x_294 == 0)
{
return x_253;
}
else
{
lean_object* x_295; lean_object* x_296; 
x_295 = lean_ctor_get(x_253, 0);
lean_inc(x_295);
lean_dec(x_253);
x_296 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_296, 0, x_295);
return x_296;
}
}
}
}
else
{
lean_object* x_305; 
lean_dec_ref(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_305 = lean_box(0);
lean_ctor_set(x_63, 0, x_305);
return x_63;
}
}
else
{
lean_object* x_306; uint8_t x_307; 
x_306 = lean_ctor_get(x_63, 0);
lean_inc(x_306);
lean_dec(x_63);
x_307 = lean_unbox(x_306);
lean_dec(x_306);
if (x_307 == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; uint8_t x_460; 
x_373 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4;
x_374 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_373, x_8);
x_375 = lean_ctor_get(x_374, 0);
lean_inc(x_375);
lean_dec_ref(x_374);
x_376 = lean_box(0);
x_460 = lean_unbox(x_375);
lean_dec(x_375);
if (x_460 == 0)
{
x_405 = x_2;
x_406 = x_3;
x_407 = x_4;
x_408 = x_5;
x_409 = x_6;
x_410 = x_7;
x_411 = x_8;
x_412 = x_9;
x_413 = lean_box(0);
goto block_459;
}
else
{
lean_object* x_461; 
lean_inc_ref(x_1);
x_461 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_8);
if (lean_obj_tag(x_461) == 0)
{
lean_object* x_462; lean_object* x_463; 
x_462 = lean_ctor_get(x_461, 0);
lean_inc(x_462);
lean_dec_ref(x_461);
x_463 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_373, x_462, x_6, x_7, x_8, x_9);
lean_dec_ref(x_463);
x_405 = x_2;
x_406 = x_3;
x_407 = x_4;
x_408 = x_5;
x_409 = x_6;
x_410 = x_7;
x_411 = x_8;
x_412 = x_9;
x_413 = lean_box(0);
goto block_459;
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; 
lean_dec_ref(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_464 = lean_ctor_get(x_461, 0);
lean_inc(x_464);
if (lean_is_exclusive(x_461)) {
 lean_ctor_release(x_461, 0);
 x_465 = x_461;
} else {
 lean_dec_ref(x_461);
 x_465 = lean_box(0);
}
if (lean_is_scalar(x_465)) {
 x_466 = lean_alloc_ctor(1, 1, 0);
} else {
 x_466 = x_465;
}
lean_ctor_set(x_466, 0, x_464);
return x_466;
}
}
block_372:
{
if (lean_obj_tag(x_325) == 0)
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; uint8_t x_329; 
lean_dec(x_322);
lean_dec_ref(x_321);
lean_dec(x_319);
lean_dec(x_316);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec_ref(x_311);
x_326 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3;
x_327 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_326, x_315);
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
lean_dec_ref(x_327);
x_329 = lean_unbox(x_328);
lean_dec(x_328);
if (x_329 == 0)
{
lean_dec_ref(x_320);
x_29 = x_308;
x_30 = x_324;
x_31 = x_323;
x_32 = x_317;
x_33 = x_309;
x_34 = x_315;
x_35 = x_310;
x_36 = lean_box(0);
goto block_40;
}
else
{
lean_object* x_330; 
x_330 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_320, x_323, x_315);
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_331; lean_object* x_332; 
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
lean_dec_ref(x_330);
x_332 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_326, x_331, x_317, x_309, x_315, x_310);
lean_dec_ref(x_332);
x_29 = x_308;
x_30 = x_324;
x_31 = x_323;
x_32 = x_317;
x_33 = x_309;
x_34 = x_315;
x_35 = x_310;
x_36 = lean_box(0);
goto block_40;
}
else
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; 
lean_dec_ref(x_324);
lean_dec(x_323);
lean_dec_ref(x_317);
lean_dec_ref(x_315);
lean_dec(x_310);
lean_dec(x_309);
lean_dec_ref(x_308);
x_333 = lean_ctor_get(x_330, 0);
lean_inc(x_333);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 x_334 = x_330;
} else {
 lean_dec_ref(x_330);
 x_334 = lean_box(0);
}
if (lean_is_scalar(x_334)) {
 x_335 = lean_alloc_ctor(1, 1, 0);
} else {
 x_335 = x_334;
}
lean_ctor_set(x_335, 0, x_333);
return x_335;
}
}
}
else
{
lean_object* x_336; lean_object* x_337; 
lean_dec_ref(x_324);
lean_dec_ref(x_308);
x_336 = lean_ctor_get(x_325, 0);
lean_inc(x_336);
lean_dec_ref(x_325);
x_337 = lean_ctor_get(x_336, 1);
lean_inc_ref(x_337);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; 
lean_dec_ref(x_337);
lean_dec(x_322);
lean_dec_ref(x_320);
lean_dec(x_319);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec_ref(x_311);
x_338 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_336, x_323, x_316, x_321, x_312, x_317, x_309, x_315, x_310);
lean_dec(x_310);
lean_dec_ref(x_315);
lean_dec(x_309);
lean_dec_ref(x_317);
lean_dec(x_312);
lean_dec_ref(x_321);
lean_dec(x_316);
lean_dec(x_323);
return x_338;
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_339 = lean_ctor_get(x_336, 0);
x_340 = lean_ctor_get(x_337, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_337, 2);
lean_inc_ref(x_341);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 lean_ctor_release(x_337, 2);
 x_342 = x_337;
} else {
 lean_dec_ref(x_337);
 x_342 = lean_box(0);
}
x_343 = lean_int_mul(x_319, x_339);
x_344 = lean_int_mul(x_340, x_314);
x_345 = l_Lean_Meta_Grind_Arith_gcdExt(x_343, x_344);
lean_dec(x_344);
lean_dec(x_343);
x_346 = lean_ctor_get(x_345, 1);
lean_inc(x_346);
x_347 = lean_ctor_get(x_345, 0);
lean_inc(x_347);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 x_348 = x_345;
} else {
 lean_dec_ref(x_345);
 x_348 = lean_box(0);
}
x_349 = lean_ctor_get(x_346, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_346, 1);
lean_inc(x_350);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 lean_ctor_release(x_346, 1);
 x_351 = x_346;
} else {
 lean_dec_ref(x_346);
 x_351 = lean_box(0);
}
x_352 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0;
x_353 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_352, x_311, x_323);
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
lean_dec_ref(x_353);
x_354 = lean_int_mul(x_349, x_339);
lean_dec(x_349);
lean_inc_ref(x_313);
x_355 = l_Int_Linear_Poly_mul(x_313, x_354);
lean_dec(x_354);
x_356 = lean_int_mul(x_350, x_314);
lean_dec(x_350);
lean_inc_ref(x_341);
x_357 = l_Int_Linear_Poly_mul(x_341, x_356);
lean_dec(x_356);
x_358 = lean_int_mul(x_314, x_339);
lean_dec(x_314);
x_359 = l_Int_Linear_Poly_combine(x_355, x_357);
lean_inc(x_347);
if (lean_is_scalar(x_342)) {
 x_360 = lean_alloc_ctor(1, 3, 0);
} else {
 x_360 = x_342;
}
lean_ctor_set(x_360, 0, x_347);
lean_ctor_set(x_360, 1, x_322);
lean_ctor_set(x_360, 2, x_359);
lean_inc(x_336);
lean_inc_ref(x_320);
if (lean_is_scalar(x_351)) {
 x_361 = lean_alloc_ctor(4, 2, 0);
} else {
 x_361 = x_351;
 lean_ctor_set_tag(x_361, 4);
}
lean_ctor_set(x_361, 0, x_320);
lean_ctor_set(x_361, 1, x_336);
x_362 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_362, 0, x_358);
lean_ctor_set(x_362, 1, x_360);
lean_ctor_set(x_362, 2, x_361);
lean_inc(x_310);
lean_inc_ref(x_315);
lean_inc(x_309);
lean_inc_ref(x_317);
lean_inc(x_312);
lean_inc_ref(x_321);
lean_inc(x_316);
lean_inc(x_323);
x_363 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_362, x_323, x_316, x_321, x_312, x_317, x_309, x_315, x_310);
if (lean_obj_tag(x_363) == 0)
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
lean_dec_ref(x_363);
x_364 = l_Int_Linear_Poly_mul(x_313, x_340);
lean_dec(x_340);
x_365 = lean_int_neg(x_319);
lean_dec(x_319);
x_366 = l_Int_Linear_Poly_mul(x_341, x_365);
lean_dec(x_365);
x_367 = l_Int_Linear_Poly_combine(x_364, x_366);
lean_inc(x_336);
if (lean_is_scalar(x_348)) {
 x_368 = lean_alloc_ctor(5, 2, 0);
} else {
 x_368 = x_348;
 lean_ctor_set_tag(x_368, 5);
}
lean_ctor_set(x_368, 0, x_320);
lean_ctor_set(x_368, 1, x_336);
if (lean_is_exclusive(x_336)) {
 lean_ctor_release(x_336, 0);
 lean_ctor_release(x_336, 1);
 lean_ctor_release(x_336, 2);
 x_369 = x_336;
} else {
 lean_dec_ref(x_336);
 x_369 = lean_box(0);
}
if (lean_is_scalar(x_369)) {
 x_370 = lean_alloc_ctor(0, 3, 0);
} else {
 x_370 = x_369;
}
lean_ctor_set(x_370, 0, x_347);
lean_ctor_set(x_370, 1, x_367);
lean_ctor_set(x_370, 2, x_368);
x_1 = x_370;
x_2 = x_323;
x_3 = x_316;
x_4 = x_321;
x_5 = x_312;
x_6 = x_317;
x_7 = x_309;
x_8 = x_315;
x_9 = x_310;
goto _start;
}
else
{
lean_dec(x_348);
lean_dec(x_347);
lean_dec_ref(x_341);
lean_dec(x_340);
lean_dec(x_336);
lean_dec(x_323);
lean_dec_ref(x_321);
lean_dec_ref(x_320);
lean_dec(x_319);
lean_dec_ref(x_317);
lean_dec(x_316);
lean_dec_ref(x_315);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec(x_310);
lean_dec(x_309);
return x_363;
}
}
else
{
lean_dec(x_351);
lean_dec(x_350);
lean_dec(x_349);
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_342);
lean_dec_ref(x_341);
lean_dec(x_340);
lean_dec(x_336);
lean_dec(x_323);
lean_dec(x_322);
lean_dec_ref(x_321);
lean_dec_ref(x_320);
lean_dec(x_319);
lean_dec_ref(x_317);
lean_dec(x_316);
lean_dec_ref(x_315);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec(x_310);
lean_dec(x_309);
return x_353;
}
}
}
}
block_404:
{
lean_object* x_394; 
x_394 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_385, x_391);
if (lean_obj_tag(x_394) == 0)
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; uint8_t x_398; 
x_395 = lean_ctor_get(x_394, 0);
lean_inc(x_395);
lean_dec_ref(x_394);
x_396 = lean_ctor_get(x_395, 6);
lean_inc_ref(x_396);
lean_dec(x_395);
x_397 = lean_ctor_get(x_396, 2);
x_398 = lean_nat_dec_lt(x_383, x_397);
if (x_398 == 0)
{
lean_object* x_399; 
lean_dec_ref(x_396);
x_399 = l_outOfBounds___redArg(x_376);
x_308 = x_377;
x_309 = x_390;
x_310 = x_392;
x_311 = x_378;
x_312 = x_388;
x_313 = x_381;
x_314 = x_382;
x_315 = x_391;
x_316 = x_386;
x_317 = x_389;
x_318 = lean_box(0);
x_319 = x_379;
x_320 = x_380;
x_321 = x_387;
x_322 = x_383;
x_323 = x_385;
x_324 = x_384;
x_325 = x_399;
goto block_372;
}
else
{
lean_object* x_400; 
x_400 = l_Lean_PersistentArray_get_x21___redArg(x_376, x_396, x_383);
x_308 = x_377;
x_309 = x_390;
x_310 = x_392;
x_311 = x_378;
x_312 = x_388;
x_313 = x_381;
x_314 = x_382;
x_315 = x_391;
x_316 = x_386;
x_317 = x_389;
x_318 = lean_box(0);
x_319 = x_379;
x_320 = x_380;
x_321 = x_387;
x_322 = x_383;
x_323 = x_385;
x_324 = x_384;
x_325 = x_400;
goto block_372;
}
}
else
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; 
lean_dec(x_392);
lean_dec_ref(x_391);
lean_dec(x_390);
lean_dec_ref(x_389);
lean_dec(x_388);
lean_dec_ref(x_387);
lean_dec(x_386);
lean_dec(x_385);
lean_dec_ref(x_384);
lean_dec(x_383);
lean_dec(x_382);
lean_dec_ref(x_381);
lean_dec_ref(x_380);
lean_dec(x_379);
lean_dec_ref(x_378);
lean_dec_ref(x_377);
x_401 = lean_ctor_get(x_394, 0);
lean_inc(x_401);
if (lean_is_exclusive(x_394)) {
 lean_ctor_release(x_394, 0);
 x_402 = x_394;
} else {
 lean_dec_ref(x_394);
 x_402 = lean_box(0);
}
if (lean_is_scalar(x_402)) {
 x_403 = lean_alloc_ctor(1, 1, 0);
} else {
 x_403 = x_402;
}
lean_ctor_set(x_403, 0, x_401);
return x_403;
}
}
block_459:
{
lean_object* x_414; lean_object* x_415; 
x_414 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc_ref(x_411);
x_415 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(x_414, x_405, x_406, x_407, x_408, x_409, x_410, x_411, x_412);
if (lean_obj_tag(x_415) == 0)
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; uint8_t x_419; 
x_416 = lean_ctor_get(x_415, 0);
lean_inc(x_416);
lean_dec_ref(x_415);
x_417 = lean_ctor_get(x_416, 0);
x_418 = lean_ctor_get(x_416, 1);
lean_inc(x_417);
x_419 = l_Int_Linear_Poly_isUnsatDvd(x_417, x_418);
if (x_419 == 0)
{
uint8_t x_420; 
x_420 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_416);
if (x_420 == 0)
{
if (lean_obj_tag(x_418) == 0)
{
lean_object* x_421; 
x_421 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_416, x_405, x_406, x_407, x_408, x_409, x_410, x_411, x_412);
lean_dec(x_412);
lean_dec_ref(x_411);
lean_dec(x_410);
lean_dec_ref(x_409);
lean_dec(x_408);
lean_dec_ref(x_407);
lean_dec(x_406);
lean_dec(x_405);
return x_421;
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
lean_inc_ref(x_418);
lean_inc(x_417);
x_422 = lean_ctor_get(x_418, 0);
lean_inc(x_422);
x_423 = lean_ctor_get(x_418, 1);
lean_inc(x_423);
x_424 = lean_ctor_get(x_418, 2);
lean_inc_ref(x_424);
lean_inc(x_416);
x_425 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_416, x_405, x_411);
if (lean_obj_tag(x_425) == 0)
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; uint8_t x_429; uint8_t x_430; uint8_t x_431; 
x_426 = lean_ctor_get(x_425, 0);
lean_inc(x_426);
lean_dec_ref(x_425);
lean_inc(x_423);
lean_inc(x_416);
x_427 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed), 3, 2);
lean_closure_set(x_427, 0, x_416);
lean_closure_set(x_427, 1, x_423);
lean_inc(x_423);
x_428 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed), 2, 1);
lean_closure_set(x_428, 0, x_423);
x_429 = 0;
x_430 = lean_unbox(x_426);
lean_dec(x_426);
x_431 = l_Lean_instBEqLBool_beq(x_430, x_429);
if (x_431 == 0)
{
x_377 = x_427;
x_378 = x_428;
x_379 = x_422;
x_380 = x_416;
x_381 = x_424;
x_382 = x_417;
x_383 = x_423;
x_384 = x_418;
x_385 = x_405;
x_386 = x_406;
x_387 = x_407;
x_388 = x_408;
x_389 = x_409;
x_390 = x_410;
x_391 = x_411;
x_392 = x_412;
x_393 = lean_box(0);
goto block_404;
}
else
{
lean_object* x_432; 
lean_inc(x_423);
x_432 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_423, x_405);
if (lean_obj_tag(x_432) == 0)
{
lean_dec_ref(x_432);
x_377 = x_427;
x_378 = x_428;
x_379 = x_422;
x_380 = x_416;
x_381 = x_424;
x_382 = x_417;
x_383 = x_423;
x_384 = x_418;
x_385 = x_405;
x_386 = x_406;
x_387 = x_407;
x_388 = x_408;
x_389 = x_409;
x_390 = x_410;
x_391 = x_411;
x_392 = x_412;
x_393 = lean_box(0);
goto block_404;
}
else
{
lean_dec_ref(x_428);
lean_dec_ref(x_427);
lean_dec_ref(x_424);
lean_dec(x_423);
lean_dec(x_422);
lean_dec_ref(x_418);
lean_dec(x_417);
lean_dec(x_416);
lean_dec(x_412);
lean_dec_ref(x_411);
lean_dec(x_410);
lean_dec_ref(x_409);
lean_dec(x_408);
lean_dec_ref(x_407);
lean_dec(x_406);
lean_dec(x_405);
return x_432;
}
}
}
else
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; 
lean_dec_ref(x_424);
lean_dec(x_423);
lean_dec(x_422);
lean_dec_ref(x_418);
lean_dec(x_417);
lean_dec(x_416);
lean_dec(x_412);
lean_dec_ref(x_411);
lean_dec(x_410);
lean_dec_ref(x_409);
lean_dec(x_408);
lean_dec_ref(x_407);
lean_dec(x_406);
lean_dec(x_405);
x_433 = lean_ctor_get(x_425, 0);
lean_inc(x_433);
if (lean_is_exclusive(x_425)) {
 lean_ctor_release(x_425, 0);
 x_434 = x_425;
} else {
 lean_dec_ref(x_425);
 x_434 = lean_box(0);
}
if (lean_is_scalar(x_434)) {
 x_435 = lean_alloc_ctor(1, 1, 0);
} else {
 x_435 = x_434;
}
lean_ctor_set(x_435, 0, x_433);
return x_435;
}
}
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; uint8_t x_439; 
lean_dec(x_408);
lean_dec_ref(x_407);
lean_dec(x_406);
x_436 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__6;
x_437 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_436, x_411);
x_438 = lean_ctor_get(x_437, 0);
lean_inc(x_438);
lean_dec_ref(x_437);
x_439 = lean_unbox(x_438);
lean_dec(x_438);
if (x_439 == 0)
{
lean_dec(x_416);
lean_dec(x_412);
lean_dec_ref(x_411);
lean_dec(x_410);
lean_dec_ref(x_409);
lean_dec(x_405);
x_41 = lean_box(0);
goto block_44;
}
else
{
lean_object* x_440; 
x_440 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_416, x_405, x_411);
lean_dec(x_405);
if (lean_obj_tag(x_440) == 0)
{
lean_object* x_441; lean_object* x_442; 
x_441 = lean_ctor_get(x_440, 0);
lean_inc(x_441);
lean_dec_ref(x_440);
x_442 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_436, x_441, x_409, x_410, x_411, x_412);
lean_dec(x_412);
lean_dec_ref(x_411);
lean_dec(x_410);
lean_dec_ref(x_409);
lean_dec_ref(x_442);
x_41 = lean_box(0);
goto block_44;
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; 
lean_dec(x_412);
lean_dec_ref(x_411);
lean_dec(x_410);
lean_dec_ref(x_409);
x_443 = lean_ctor_get(x_440, 0);
lean_inc(x_443);
if (lean_is_exclusive(x_440)) {
 lean_ctor_release(x_440, 0);
 x_444 = x_440;
} else {
 lean_dec_ref(x_440);
 x_444 = lean_box(0);
}
if (lean_is_scalar(x_444)) {
 x_445 = lean_alloc_ctor(1, 1, 0);
} else {
 x_445 = x_444;
}
lean_ctor_set(x_445, 0, x_443);
return x_445;
}
}
}
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; uint8_t x_449; 
x_446 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__8;
x_447 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_446, x_411);
x_448 = lean_ctor_get(x_447, 0);
lean_inc(x_448);
lean_dec_ref(x_447);
x_449 = lean_unbox(x_448);
lean_dec(x_448);
if (x_449 == 0)
{
x_11 = x_416;
x_12 = x_405;
x_13 = x_406;
x_14 = x_407;
x_15 = x_408;
x_16 = x_409;
x_17 = x_410;
x_18 = x_411;
x_19 = x_412;
x_20 = lean_box(0);
goto block_28;
}
else
{
lean_object* x_450; 
lean_inc(x_416);
x_450 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_416, x_405, x_411);
if (lean_obj_tag(x_450) == 0)
{
lean_object* x_451; lean_object* x_452; 
x_451 = lean_ctor_get(x_450, 0);
lean_inc(x_451);
lean_dec_ref(x_450);
x_452 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_446, x_451, x_409, x_410, x_411, x_412);
lean_dec_ref(x_452);
x_11 = x_416;
x_12 = x_405;
x_13 = x_406;
x_14 = x_407;
x_15 = x_408;
x_16 = x_409;
x_17 = x_410;
x_18 = x_411;
x_19 = x_412;
x_20 = lean_box(0);
goto block_28;
}
else
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; 
lean_dec(x_416);
lean_dec(x_412);
lean_dec_ref(x_411);
lean_dec(x_410);
lean_dec_ref(x_409);
lean_dec(x_408);
lean_dec_ref(x_407);
lean_dec(x_406);
lean_dec(x_405);
x_453 = lean_ctor_get(x_450, 0);
lean_inc(x_453);
if (lean_is_exclusive(x_450)) {
 lean_ctor_release(x_450, 0);
 x_454 = x_450;
} else {
 lean_dec_ref(x_450);
 x_454 = lean_box(0);
}
if (lean_is_scalar(x_454)) {
 x_455 = lean_alloc_ctor(1, 1, 0);
} else {
 x_455 = x_454;
}
lean_ctor_set(x_455, 0, x_453);
return x_455;
}
}
}
}
else
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; 
lean_dec(x_412);
lean_dec_ref(x_411);
lean_dec(x_410);
lean_dec_ref(x_409);
lean_dec(x_408);
lean_dec_ref(x_407);
lean_dec(x_406);
lean_dec(x_405);
x_456 = lean_ctor_get(x_415, 0);
lean_inc(x_456);
if (lean_is_exclusive(x_415)) {
 lean_ctor_release(x_415, 0);
 x_457 = x_415;
} else {
 lean_dec_ref(x_415);
 x_457 = lean_box(0);
}
if (lean_is_scalar(x_457)) {
 x_458 = lean_alloc_ctor(1, 1, 0);
} else {
 x_458 = x_457;
}
lean_ctor_set(x_458, 0, x_456);
return x_458;
}
}
}
else
{
lean_object* x_467; lean_object* x_468; 
lean_dec_ref(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_467 = lean_box(0);
x_468 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_468, 0, x_467);
return x_468;
}
}
}
else
{
uint8_t x_469; 
lean_dec_ref(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_469 = !lean_is_exclusive(x_63);
if (x_469 == 0)
{
return x_63;
}
else
{
lean_object* x_470; lean_object* x_471; 
x_470 = lean_ctor_get(x_63, 0);
lean_inc(x_470);
lean_dec(x_63);
x_471 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_471, 0, x_470);
return x_471;
}
}
}
else
{
lean_object* x_472; 
lean_free_object(x_8);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec_ref(x_47);
lean_dec_ref(x_46);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_472 = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(x_51);
return x_472;
}
}
else
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; uint8_t x_485; lean_object* x_486; uint8_t x_487; lean_object* x_488; uint8_t x_489; 
x_473 = lean_ctor_get(x_8, 0);
x_474 = lean_ctor_get(x_8, 1);
x_475 = lean_ctor_get(x_8, 2);
x_476 = lean_ctor_get(x_8, 3);
x_477 = lean_ctor_get(x_8, 4);
x_478 = lean_ctor_get(x_8, 5);
x_479 = lean_ctor_get(x_8, 6);
x_480 = lean_ctor_get(x_8, 7);
x_481 = lean_ctor_get(x_8, 8);
x_482 = lean_ctor_get(x_8, 9);
x_483 = lean_ctor_get(x_8, 10);
x_484 = lean_ctor_get(x_8, 11);
x_485 = lean_ctor_get_uint8(x_8, sizeof(void*)*14);
x_486 = lean_ctor_get(x_8, 12);
x_487 = lean_ctor_get_uint8(x_8, sizeof(void*)*14 + 1);
x_488 = lean_ctor_get(x_8, 13);
lean_inc(x_488);
lean_inc(x_486);
lean_inc(x_484);
lean_inc(x_483);
lean_inc(x_482);
lean_inc(x_481);
lean_inc(x_480);
lean_inc(x_479);
lean_inc(x_478);
lean_inc(x_477);
lean_inc(x_476);
lean_inc(x_475);
lean_inc(x_474);
lean_inc(x_473);
lean_dec(x_8);
x_489 = lean_nat_dec_eq(x_476, x_477);
if (x_489 == 0)
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; 
x_490 = lean_unsigned_to_nat(1u);
x_491 = lean_nat_add(x_476, x_490);
lean_dec(x_476);
x_492 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_492, 0, x_473);
lean_ctor_set(x_492, 1, x_474);
lean_ctor_set(x_492, 2, x_475);
lean_ctor_set(x_492, 3, x_491);
lean_ctor_set(x_492, 4, x_477);
lean_ctor_set(x_492, 5, x_478);
lean_ctor_set(x_492, 6, x_479);
lean_ctor_set(x_492, 7, x_480);
lean_ctor_set(x_492, 8, x_481);
lean_ctor_set(x_492, 9, x_482);
lean_ctor_set(x_492, 10, x_483);
lean_ctor_set(x_492, 11, x_484);
lean_ctor_set(x_492, 12, x_486);
lean_ctor_set(x_492, 13, x_488);
lean_ctor_set_uint8(x_492, sizeof(void*)*14, x_485);
lean_ctor_set_uint8(x_492, sizeof(void*)*14 + 1, x_487);
x_493 = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(x_2, x_492);
if (lean_obj_tag(x_493) == 0)
{
lean_object* x_494; lean_object* x_495; uint8_t x_496; 
x_494 = lean_ctor_get(x_493, 0);
lean_inc(x_494);
if (lean_is_exclusive(x_493)) {
 lean_ctor_release(x_493, 0);
 x_495 = x_493;
} else {
 lean_dec_ref(x_493);
 x_495 = lean_box(0);
}
x_496 = lean_unbox(x_494);
lean_dec(x_494);
if (x_496 == 0)
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; uint8_t x_649; 
lean_dec(x_495);
x_562 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4;
x_563 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_562, x_492);
x_564 = lean_ctor_get(x_563, 0);
lean_inc(x_564);
lean_dec_ref(x_563);
x_565 = lean_box(0);
x_649 = lean_unbox(x_564);
lean_dec(x_564);
if (x_649 == 0)
{
x_594 = x_2;
x_595 = x_3;
x_596 = x_4;
x_597 = x_5;
x_598 = x_6;
x_599 = x_7;
x_600 = x_492;
x_601 = x_9;
x_602 = lean_box(0);
goto block_648;
}
else
{
lean_object* x_650; 
lean_inc_ref(x_1);
x_650 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_492);
if (lean_obj_tag(x_650) == 0)
{
lean_object* x_651; lean_object* x_652; 
x_651 = lean_ctor_get(x_650, 0);
lean_inc(x_651);
lean_dec_ref(x_650);
x_652 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_562, x_651, x_6, x_7, x_492, x_9);
lean_dec_ref(x_652);
x_594 = x_2;
x_595 = x_3;
x_596 = x_4;
x_597 = x_5;
x_598 = x_6;
x_599 = x_7;
x_600 = x_492;
x_601 = x_9;
x_602 = lean_box(0);
goto block_648;
}
else
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; 
lean_dec_ref(x_492);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_653 = lean_ctor_get(x_650, 0);
lean_inc(x_653);
if (lean_is_exclusive(x_650)) {
 lean_ctor_release(x_650, 0);
 x_654 = x_650;
} else {
 lean_dec_ref(x_650);
 x_654 = lean_box(0);
}
if (lean_is_scalar(x_654)) {
 x_655 = lean_alloc_ctor(1, 1, 0);
} else {
 x_655 = x_654;
}
lean_ctor_set(x_655, 0, x_653);
return x_655;
}
}
block_561:
{
if (lean_obj_tag(x_514) == 0)
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; uint8_t x_518; 
lean_dec(x_511);
lean_dec_ref(x_510);
lean_dec(x_508);
lean_dec(x_505);
lean_dec(x_503);
lean_dec_ref(x_502);
lean_dec(x_501);
lean_dec_ref(x_500);
x_515 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3;
x_516 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_515, x_504);
x_517 = lean_ctor_get(x_516, 0);
lean_inc(x_517);
lean_dec_ref(x_516);
x_518 = lean_unbox(x_517);
lean_dec(x_517);
if (x_518 == 0)
{
lean_dec_ref(x_509);
x_29 = x_497;
x_30 = x_513;
x_31 = x_512;
x_32 = x_506;
x_33 = x_498;
x_34 = x_504;
x_35 = x_499;
x_36 = lean_box(0);
goto block_40;
}
else
{
lean_object* x_519; 
x_519 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_509, x_512, x_504);
if (lean_obj_tag(x_519) == 0)
{
lean_object* x_520; lean_object* x_521; 
x_520 = lean_ctor_get(x_519, 0);
lean_inc(x_520);
lean_dec_ref(x_519);
x_521 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_515, x_520, x_506, x_498, x_504, x_499);
lean_dec_ref(x_521);
x_29 = x_497;
x_30 = x_513;
x_31 = x_512;
x_32 = x_506;
x_33 = x_498;
x_34 = x_504;
x_35 = x_499;
x_36 = lean_box(0);
goto block_40;
}
else
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; 
lean_dec_ref(x_513);
lean_dec(x_512);
lean_dec_ref(x_506);
lean_dec_ref(x_504);
lean_dec(x_499);
lean_dec(x_498);
lean_dec_ref(x_497);
x_522 = lean_ctor_get(x_519, 0);
lean_inc(x_522);
if (lean_is_exclusive(x_519)) {
 lean_ctor_release(x_519, 0);
 x_523 = x_519;
} else {
 lean_dec_ref(x_519);
 x_523 = lean_box(0);
}
if (lean_is_scalar(x_523)) {
 x_524 = lean_alloc_ctor(1, 1, 0);
} else {
 x_524 = x_523;
}
lean_ctor_set(x_524, 0, x_522);
return x_524;
}
}
}
else
{
lean_object* x_525; lean_object* x_526; 
lean_dec_ref(x_513);
lean_dec_ref(x_497);
x_525 = lean_ctor_get(x_514, 0);
lean_inc(x_525);
lean_dec_ref(x_514);
x_526 = lean_ctor_get(x_525, 1);
lean_inc_ref(x_526);
if (lean_obj_tag(x_526) == 0)
{
lean_object* x_527; 
lean_dec_ref(x_526);
lean_dec(x_511);
lean_dec_ref(x_509);
lean_dec(x_508);
lean_dec(x_503);
lean_dec_ref(x_502);
lean_dec_ref(x_500);
x_527 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_525, x_512, x_505, x_510, x_501, x_506, x_498, x_504, x_499);
lean_dec(x_499);
lean_dec_ref(x_504);
lean_dec(x_498);
lean_dec_ref(x_506);
lean_dec(x_501);
lean_dec_ref(x_510);
lean_dec(x_505);
lean_dec(x_512);
return x_527;
}
else
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; 
x_528 = lean_ctor_get(x_525, 0);
x_529 = lean_ctor_get(x_526, 0);
lean_inc(x_529);
x_530 = lean_ctor_get(x_526, 2);
lean_inc_ref(x_530);
if (lean_is_exclusive(x_526)) {
 lean_ctor_release(x_526, 0);
 lean_ctor_release(x_526, 1);
 lean_ctor_release(x_526, 2);
 x_531 = x_526;
} else {
 lean_dec_ref(x_526);
 x_531 = lean_box(0);
}
x_532 = lean_int_mul(x_508, x_528);
x_533 = lean_int_mul(x_529, x_503);
x_534 = l_Lean_Meta_Grind_Arith_gcdExt(x_532, x_533);
lean_dec(x_533);
lean_dec(x_532);
x_535 = lean_ctor_get(x_534, 1);
lean_inc(x_535);
x_536 = lean_ctor_get(x_534, 0);
lean_inc(x_536);
if (lean_is_exclusive(x_534)) {
 lean_ctor_release(x_534, 0);
 lean_ctor_release(x_534, 1);
 x_537 = x_534;
} else {
 lean_dec_ref(x_534);
 x_537 = lean_box(0);
}
x_538 = lean_ctor_get(x_535, 0);
lean_inc(x_538);
x_539 = lean_ctor_get(x_535, 1);
lean_inc(x_539);
if (lean_is_exclusive(x_535)) {
 lean_ctor_release(x_535, 0);
 lean_ctor_release(x_535, 1);
 x_540 = x_535;
} else {
 lean_dec_ref(x_535);
 x_540 = lean_box(0);
}
x_541 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0;
x_542 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_541, x_500, x_512);
if (lean_obj_tag(x_542) == 0)
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; 
lean_dec_ref(x_542);
x_543 = lean_int_mul(x_538, x_528);
lean_dec(x_538);
lean_inc_ref(x_502);
x_544 = l_Int_Linear_Poly_mul(x_502, x_543);
lean_dec(x_543);
x_545 = lean_int_mul(x_539, x_503);
lean_dec(x_539);
lean_inc_ref(x_530);
x_546 = l_Int_Linear_Poly_mul(x_530, x_545);
lean_dec(x_545);
x_547 = lean_int_mul(x_503, x_528);
lean_dec(x_503);
x_548 = l_Int_Linear_Poly_combine(x_544, x_546);
lean_inc(x_536);
if (lean_is_scalar(x_531)) {
 x_549 = lean_alloc_ctor(1, 3, 0);
} else {
 x_549 = x_531;
}
lean_ctor_set(x_549, 0, x_536);
lean_ctor_set(x_549, 1, x_511);
lean_ctor_set(x_549, 2, x_548);
lean_inc(x_525);
lean_inc_ref(x_509);
if (lean_is_scalar(x_540)) {
 x_550 = lean_alloc_ctor(4, 2, 0);
} else {
 x_550 = x_540;
 lean_ctor_set_tag(x_550, 4);
}
lean_ctor_set(x_550, 0, x_509);
lean_ctor_set(x_550, 1, x_525);
x_551 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_551, 0, x_547);
lean_ctor_set(x_551, 1, x_549);
lean_ctor_set(x_551, 2, x_550);
lean_inc(x_499);
lean_inc_ref(x_504);
lean_inc(x_498);
lean_inc_ref(x_506);
lean_inc(x_501);
lean_inc_ref(x_510);
lean_inc(x_505);
lean_inc(x_512);
x_552 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_551, x_512, x_505, x_510, x_501, x_506, x_498, x_504, x_499);
if (lean_obj_tag(x_552) == 0)
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; 
lean_dec_ref(x_552);
x_553 = l_Int_Linear_Poly_mul(x_502, x_529);
lean_dec(x_529);
x_554 = lean_int_neg(x_508);
lean_dec(x_508);
x_555 = l_Int_Linear_Poly_mul(x_530, x_554);
lean_dec(x_554);
x_556 = l_Int_Linear_Poly_combine(x_553, x_555);
lean_inc(x_525);
if (lean_is_scalar(x_537)) {
 x_557 = lean_alloc_ctor(5, 2, 0);
} else {
 x_557 = x_537;
 lean_ctor_set_tag(x_557, 5);
}
lean_ctor_set(x_557, 0, x_509);
lean_ctor_set(x_557, 1, x_525);
if (lean_is_exclusive(x_525)) {
 lean_ctor_release(x_525, 0);
 lean_ctor_release(x_525, 1);
 lean_ctor_release(x_525, 2);
 x_558 = x_525;
} else {
 lean_dec_ref(x_525);
 x_558 = lean_box(0);
}
if (lean_is_scalar(x_558)) {
 x_559 = lean_alloc_ctor(0, 3, 0);
} else {
 x_559 = x_558;
}
lean_ctor_set(x_559, 0, x_536);
lean_ctor_set(x_559, 1, x_556);
lean_ctor_set(x_559, 2, x_557);
x_1 = x_559;
x_2 = x_512;
x_3 = x_505;
x_4 = x_510;
x_5 = x_501;
x_6 = x_506;
x_7 = x_498;
x_8 = x_504;
x_9 = x_499;
goto _start;
}
else
{
lean_dec(x_537);
lean_dec(x_536);
lean_dec_ref(x_530);
lean_dec(x_529);
lean_dec(x_525);
lean_dec(x_512);
lean_dec_ref(x_510);
lean_dec_ref(x_509);
lean_dec(x_508);
lean_dec_ref(x_506);
lean_dec(x_505);
lean_dec_ref(x_504);
lean_dec_ref(x_502);
lean_dec(x_501);
lean_dec(x_499);
lean_dec(x_498);
return x_552;
}
}
else
{
lean_dec(x_540);
lean_dec(x_539);
lean_dec(x_538);
lean_dec(x_537);
lean_dec(x_536);
lean_dec(x_531);
lean_dec_ref(x_530);
lean_dec(x_529);
lean_dec(x_525);
lean_dec(x_512);
lean_dec(x_511);
lean_dec_ref(x_510);
lean_dec_ref(x_509);
lean_dec(x_508);
lean_dec_ref(x_506);
lean_dec(x_505);
lean_dec_ref(x_504);
lean_dec(x_503);
lean_dec_ref(x_502);
lean_dec(x_501);
lean_dec(x_499);
lean_dec(x_498);
return x_542;
}
}
}
}
block_593:
{
lean_object* x_583; 
x_583 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_574, x_580);
if (lean_obj_tag(x_583) == 0)
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; uint8_t x_587; 
x_584 = lean_ctor_get(x_583, 0);
lean_inc(x_584);
lean_dec_ref(x_583);
x_585 = lean_ctor_get(x_584, 6);
lean_inc_ref(x_585);
lean_dec(x_584);
x_586 = lean_ctor_get(x_585, 2);
x_587 = lean_nat_dec_lt(x_572, x_586);
if (x_587 == 0)
{
lean_object* x_588; 
lean_dec_ref(x_585);
x_588 = l_outOfBounds___redArg(x_565);
x_497 = x_566;
x_498 = x_579;
x_499 = x_581;
x_500 = x_567;
x_501 = x_577;
x_502 = x_570;
x_503 = x_571;
x_504 = x_580;
x_505 = x_575;
x_506 = x_578;
x_507 = lean_box(0);
x_508 = x_568;
x_509 = x_569;
x_510 = x_576;
x_511 = x_572;
x_512 = x_574;
x_513 = x_573;
x_514 = x_588;
goto block_561;
}
else
{
lean_object* x_589; 
x_589 = l_Lean_PersistentArray_get_x21___redArg(x_565, x_585, x_572);
x_497 = x_566;
x_498 = x_579;
x_499 = x_581;
x_500 = x_567;
x_501 = x_577;
x_502 = x_570;
x_503 = x_571;
x_504 = x_580;
x_505 = x_575;
x_506 = x_578;
x_507 = lean_box(0);
x_508 = x_568;
x_509 = x_569;
x_510 = x_576;
x_511 = x_572;
x_512 = x_574;
x_513 = x_573;
x_514 = x_589;
goto block_561;
}
}
else
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; 
lean_dec(x_581);
lean_dec_ref(x_580);
lean_dec(x_579);
lean_dec_ref(x_578);
lean_dec(x_577);
lean_dec_ref(x_576);
lean_dec(x_575);
lean_dec(x_574);
lean_dec_ref(x_573);
lean_dec(x_572);
lean_dec(x_571);
lean_dec_ref(x_570);
lean_dec_ref(x_569);
lean_dec(x_568);
lean_dec_ref(x_567);
lean_dec_ref(x_566);
x_590 = lean_ctor_get(x_583, 0);
lean_inc(x_590);
if (lean_is_exclusive(x_583)) {
 lean_ctor_release(x_583, 0);
 x_591 = x_583;
} else {
 lean_dec_ref(x_583);
 x_591 = lean_box(0);
}
if (lean_is_scalar(x_591)) {
 x_592 = lean_alloc_ctor(1, 1, 0);
} else {
 x_592 = x_591;
}
lean_ctor_set(x_592, 0, x_590);
return x_592;
}
}
block_648:
{
lean_object* x_603; lean_object* x_604; 
x_603 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc_ref(x_600);
x_604 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(x_603, x_594, x_595, x_596, x_597, x_598, x_599, x_600, x_601);
if (lean_obj_tag(x_604) == 0)
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; uint8_t x_608; 
x_605 = lean_ctor_get(x_604, 0);
lean_inc(x_605);
lean_dec_ref(x_604);
x_606 = lean_ctor_get(x_605, 0);
x_607 = lean_ctor_get(x_605, 1);
lean_inc(x_606);
x_608 = l_Int_Linear_Poly_isUnsatDvd(x_606, x_607);
if (x_608 == 0)
{
uint8_t x_609; 
x_609 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_605);
if (x_609 == 0)
{
if (lean_obj_tag(x_607) == 0)
{
lean_object* x_610; 
x_610 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_605, x_594, x_595, x_596, x_597, x_598, x_599, x_600, x_601);
lean_dec(x_601);
lean_dec_ref(x_600);
lean_dec(x_599);
lean_dec_ref(x_598);
lean_dec(x_597);
lean_dec_ref(x_596);
lean_dec(x_595);
lean_dec(x_594);
return x_610;
}
else
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; 
lean_inc_ref(x_607);
lean_inc(x_606);
x_611 = lean_ctor_get(x_607, 0);
lean_inc(x_611);
x_612 = lean_ctor_get(x_607, 1);
lean_inc(x_612);
x_613 = lean_ctor_get(x_607, 2);
lean_inc_ref(x_613);
lean_inc(x_605);
x_614 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_605, x_594, x_600);
if (lean_obj_tag(x_614) == 0)
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; uint8_t x_618; uint8_t x_619; uint8_t x_620; 
x_615 = lean_ctor_get(x_614, 0);
lean_inc(x_615);
lean_dec_ref(x_614);
lean_inc(x_612);
lean_inc(x_605);
x_616 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed), 3, 2);
lean_closure_set(x_616, 0, x_605);
lean_closure_set(x_616, 1, x_612);
lean_inc(x_612);
x_617 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed), 2, 1);
lean_closure_set(x_617, 0, x_612);
x_618 = 0;
x_619 = lean_unbox(x_615);
lean_dec(x_615);
x_620 = l_Lean_instBEqLBool_beq(x_619, x_618);
if (x_620 == 0)
{
x_566 = x_616;
x_567 = x_617;
x_568 = x_611;
x_569 = x_605;
x_570 = x_613;
x_571 = x_606;
x_572 = x_612;
x_573 = x_607;
x_574 = x_594;
x_575 = x_595;
x_576 = x_596;
x_577 = x_597;
x_578 = x_598;
x_579 = x_599;
x_580 = x_600;
x_581 = x_601;
x_582 = lean_box(0);
goto block_593;
}
else
{
lean_object* x_621; 
lean_inc(x_612);
x_621 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_612, x_594);
if (lean_obj_tag(x_621) == 0)
{
lean_dec_ref(x_621);
x_566 = x_616;
x_567 = x_617;
x_568 = x_611;
x_569 = x_605;
x_570 = x_613;
x_571 = x_606;
x_572 = x_612;
x_573 = x_607;
x_574 = x_594;
x_575 = x_595;
x_576 = x_596;
x_577 = x_597;
x_578 = x_598;
x_579 = x_599;
x_580 = x_600;
x_581 = x_601;
x_582 = lean_box(0);
goto block_593;
}
else
{
lean_dec_ref(x_617);
lean_dec_ref(x_616);
lean_dec_ref(x_613);
lean_dec(x_612);
lean_dec(x_611);
lean_dec_ref(x_607);
lean_dec(x_606);
lean_dec(x_605);
lean_dec(x_601);
lean_dec_ref(x_600);
lean_dec(x_599);
lean_dec_ref(x_598);
lean_dec(x_597);
lean_dec_ref(x_596);
lean_dec(x_595);
lean_dec(x_594);
return x_621;
}
}
}
else
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; 
lean_dec_ref(x_613);
lean_dec(x_612);
lean_dec(x_611);
lean_dec_ref(x_607);
lean_dec(x_606);
lean_dec(x_605);
lean_dec(x_601);
lean_dec_ref(x_600);
lean_dec(x_599);
lean_dec_ref(x_598);
lean_dec(x_597);
lean_dec_ref(x_596);
lean_dec(x_595);
lean_dec(x_594);
x_622 = lean_ctor_get(x_614, 0);
lean_inc(x_622);
if (lean_is_exclusive(x_614)) {
 lean_ctor_release(x_614, 0);
 x_623 = x_614;
} else {
 lean_dec_ref(x_614);
 x_623 = lean_box(0);
}
if (lean_is_scalar(x_623)) {
 x_624 = lean_alloc_ctor(1, 1, 0);
} else {
 x_624 = x_623;
}
lean_ctor_set(x_624, 0, x_622);
return x_624;
}
}
}
else
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; uint8_t x_628; 
lean_dec(x_597);
lean_dec_ref(x_596);
lean_dec(x_595);
x_625 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__6;
x_626 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_625, x_600);
x_627 = lean_ctor_get(x_626, 0);
lean_inc(x_627);
lean_dec_ref(x_626);
x_628 = lean_unbox(x_627);
lean_dec(x_627);
if (x_628 == 0)
{
lean_dec(x_605);
lean_dec(x_601);
lean_dec_ref(x_600);
lean_dec(x_599);
lean_dec_ref(x_598);
lean_dec(x_594);
x_41 = lean_box(0);
goto block_44;
}
else
{
lean_object* x_629; 
x_629 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_605, x_594, x_600);
lean_dec(x_594);
if (lean_obj_tag(x_629) == 0)
{
lean_object* x_630; lean_object* x_631; 
x_630 = lean_ctor_get(x_629, 0);
lean_inc(x_630);
lean_dec_ref(x_629);
x_631 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_625, x_630, x_598, x_599, x_600, x_601);
lean_dec(x_601);
lean_dec_ref(x_600);
lean_dec(x_599);
lean_dec_ref(x_598);
lean_dec_ref(x_631);
x_41 = lean_box(0);
goto block_44;
}
else
{
lean_object* x_632; lean_object* x_633; lean_object* x_634; 
lean_dec(x_601);
lean_dec_ref(x_600);
lean_dec(x_599);
lean_dec_ref(x_598);
x_632 = lean_ctor_get(x_629, 0);
lean_inc(x_632);
if (lean_is_exclusive(x_629)) {
 lean_ctor_release(x_629, 0);
 x_633 = x_629;
} else {
 lean_dec_ref(x_629);
 x_633 = lean_box(0);
}
if (lean_is_scalar(x_633)) {
 x_634 = lean_alloc_ctor(1, 1, 0);
} else {
 x_634 = x_633;
}
lean_ctor_set(x_634, 0, x_632);
return x_634;
}
}
}
}
else
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; uint8_t x_638; 
x_635 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__8;
x_636 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_635, x_600);
x_637 = lean_ctor_get(x_636, 0);
lean_inc(x_637);
lean_dec_ref(x_636);
x_638 = lean_unbox(x_637);
lean_dec(x_637);
if (x_638 == 0)
{
x_11 = x_605;
x_12 = x_594;
x_13 = x_595;
x_14 = x_596;
x_15 = x_597;
x_16 = x_598;
x_17 = x_599;
x_18 = x_600;
x_19 = x_601;
x_20 = lean_box(0);
goto block_28;
}
else
{
lean_object* x_639; 
lean_inc(x_605);
x_639 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_605, x_594, x_600);
if (lean_obj_tag(x_639) == 0)
{
lean_object* x_640; lean_object* x_641; 
x_640 = lean_ctor_get(x_639, 0);
lean_inc(x_640);
lean_dec_ref(x_639);
x_641 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_635, x_640, x_598, x_599, x_600, x_601);
lean_dec_ref(x_641);
x_11 = x_605;
x_12 = x_594;
x_13 = x_595;
x_14 = x_596;
x_15 = x_597;
x_16 = x_598;
x_17 = x_599;
x_18 = x_600;
x_19 = x_601;
x_20 = lean_box(0);
goto block_28;
}
else
{
lean_object* x_642; lean_object* x_643; lean_object* x_644; 
lean_dec(x_605);
lean_dec(x_601);
lean_dec_ref(x_600);
lean_dec(x_599);
lean_dec_ref(x_598);
lean_dec(x_597);
lean_dec_ref(x_596);
lean_dec(x_595);
lean_dec(x_594);
x_642 = lean_ctor_get(x_639, 0);
lean_inc(x_642);
if (lean_is_exclusive(x_639)) {
 lean_ctor_release(x_639, 0);
 x_643 = x_639;
} else {
 lean_dec_ref(x_639);
 x_643 = lean_box(0);
}
if (lean_is_scalar(x_643)) {
 x_644 = lean_alloc_ctor(1, 1, 0);
} else {
 x_644 = x_643;
}
lean_ctor_set(x_644, 0, x_642);
return x_644;
}
}
}
}
else
{
lean_object* x_645; lean_object* x_646; lean_object* x_647; 
lean_dec(x_601);
lean_dec_ref(x_600);
lean_dec(x_599);
lean_dec_ref(x_598);
lean_dec(x_597);
lean_dec_ref(x_596);
lean_dec(x_595);
lean_dec(x_594);
x_645 = lean_ctor_get(x_604, 0);
lean_inc(x_645);
if (lean_is_exclusive(x_604)) {
 lean_ctor_release(x_604, 0);
 x_646 = x_604;
} else {
 lean_dec_ref(x_604);
 x_646 = lean_box(0);
}
if (lean_is_scalar(x_646)) {
 x_647 = lean_alloc_ctor(1, 1, 0);
} else {
 x_647 = x_646;
}
lean_ctor_set(x_647, 0, x_645);
return x_647;
}
}
}
else
{
lean_object* x_656; lean_object* x_657; 
lean_dec_ref(x_492);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_656 = lean_box(0);
if (lean_is_scalar(x_495)) {
 x_657 = lean_alloc_ctor(0, 1, 0);
} else {
 x_657 = x_495;
}
lean_ctor_set(x_657, 0, x_656);
return x_657;
}
}
else
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; 
lean_dec_ref(x_492);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_658 = lean_ctor_get(x_493, 0);
lean_inc(x_658);
if (lean_is_exclusive(x_493)) {
 lean_ctor_release(x_493, 0);
 x_659 = x_493;
} else {
 lean_dec_ref(x_493);
 x_659 = lean_box(0);
}
if (lean_is_scalar(x_659)) {
 x_660 = lean_alloc_ctor(1, 1, 0);
} else {
 x_660 = x_659;
}
lean_ctor_set(x_660, 0, x_658);
return x_660;
}
}
else
{
lean_object* x_661; 
lean_dec_ref(x_488);
lean_dec(x_486);
lean_dec(x_484);
lean_dec(x_483);
lean_dec(x_482);
lean_dec(x_481);
lean_dec(x_480);
lean_dec(x_479);
lean_dec(x_477);
lean_dec(x_476);
lean_dec(x_475);
lean_dec_ref(x_474);
lean_dec_ref(x_473);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_661 = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(x_478);
return x_661;
}
}
block_28:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_11);
x_22 = l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(x_21, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
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
lean_object* x_26; lean_object* x_27; 
lean_dec(x_22);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
else
{
return x_22;
}
}
block_40:
{
lean_object* x_37; 
x_37 = l_Int_Linear_Poly_updateOccs___redArg(x_30, x_31, x_32, x_33, x_34, x_35);
lean_dec(x_35);
lean_dec_ref(x_34);
lean_dec(x_33);
lean_dec_ref(x_32);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec_ref(x_37);
x_38 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0;
x_39 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_38, x_29, x_31);
lean_dec(x_31);
return x_39;
}
else
{
lean_dec(x_31);
lean_dec_ref(x_29);
return x_37;
}
}
block_44:
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_42);
return x_43;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_12);
x_13 = l_Int_Linear_Poly_normCommRing_x3f(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_inc(x_11);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec_ref(x_14);
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
lean_ctor_set(x_22, 0, x_11);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_22, 2, x_21);
x_23 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_22, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_24 = !lean_is_exclusive(x_13);
if (x_24 == 0)
{
return x_13;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_13, 0);
lean_inc(x_25);
lean_dec(x_13);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
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
x_1 = lean_mk_string_unchecked("non-linear divisibility constraint found", 40, 40);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Int", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Linear", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("of_not_dvd", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7;
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6;
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__5;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_eagerReflBoolTrue;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_15; 
lean_inc_ref(x_1);
x_15 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_7);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_21; uint8_t x_22; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_17 = x_15;
} else {
 lean_dec_ref(x_15);
 x_17 = lean_box(0);
}
x_21 = l_Lean_Expr_cleanupAnnotations(x_16);
x_22 = l_Lean_Expr_isApp(x_21);
if (x_22 == 0)
{
lean_dec_ref(x_21);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_20;
}
else
{
lean_object* x_23; uint8_t x_24; 
lean_inc_ref(x_21);
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_21);
x_24 = l_Lean_Expr_isApp(x_23);
if (x_24 == 0)
{
lean_dec_ref(x_23);
lean_dec_ref(x_21);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_20;
}
else
{
lean_object* x_25; uint8_t x_26; 
lean_inc_ref(x_23);
x_25 = l_Lean_Expr_appFnCleanup___redArg(x_23);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec_ref(x_25);
lean_dec_ref(x_23);
lean_dec_ref(x_21);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_20;
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
lean_dec_ref(x_23);
lean_dec_ref(x_21);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_20;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = l_Lean_Expr_appFnCleanup___redArg(x_27);
x_30 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2;
x_31 = l_Lean_Expr_isConstOf(x_29, x_30);
lean_dec_ref(x_29);
if (x_31 == 0)
{
lean_dec_ref(x_25);
lean_dec_ref(x_23);
lean_dec_ref(x_21);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_20;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_17);
x_32 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_32);
lean_dec_ref(x_25);
x_33 = l_Lean_Meta_isInstDvdInt___redArg(x_32, x_7);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec_ref(x_23);
lean_dec_ref(x_21);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_37 = lean_box(0);
lean_ctor_set(x_33, 0, x_37);
return x_33;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_free_object(x_33);
x_38 = lean_ctor_get(x_23, 1);
lean_inc_ref(x_38);
lean_dec_ref(x_23);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_38);
x_39 = l_Lean_Meta_getIntValue_x3f(x_38, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
lean_dec_ref(x_38);
lean_dec_ref(x_21);
lean_dec(x_2);
x_41 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
x_43 = lean_ctor_get_uint8(x_42, sizeof(void*)*8 + 13);
lean_dec(x_42);
if (x_43 == 0)
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4;
x_45 = l_Lean_indentExpr(x_1);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_Meta_Grind_reportIssue(x_46, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_47) == 0)
{
lean_dec_ref(x_47);
x_11 = lean_box(0);
goto block_14;
}
else
{
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_48 = !lean_is_exclusive(x_41);
if (x_48 == 0)
{
return x_41;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_41, 0);
lean_inc(x_49);
lean_dec(x_41);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_40);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_1);
x_53 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_4, x_8, x_9);
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
lean_object* x_56; lean_object* x_57; 
lean_free_object(x_40);
lean_dec(x_52);
x_56 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_56);
lean_dec_ref(x_21);
lean_inc_ref(x_1);
x_57 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_4, x_8, x_9);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_unbox(x_59);
lean_dec(x_59);
if (x_60 == 0)
{
lean_object* x_61; 
lean_dec_ref(x_56);
lean_dec_ref(x_38);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_61 = lean_box(0);
lean_ctor_set(x_57, 0, x_61);
return x_57;
}
else
{
lean_object* x_62; 
lean_free_object(x_57);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_62 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec_ref(x_62);
x_64 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9;
x_65 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10;
x_66 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_63);
x_67 = l_Lean_mkApp4(x_64, x_38, x_56, x_65, x_66);
x_68 = lean_unsigned_to_nat(0u);
x_69 = l_Lean_Meta_Grind_pushNewFact(x_67, x_68, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_69;
}
else
{
uint8_t x_70; 
lean_dec_ref(x_56);
lean_dec_ref(x_38);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_70 = !lean_is_exclusive(x_62);
if (x_70 == 0)
{
return x_62;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_62, 0);
lean_inc(x_71);
lean_dec(x_62);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
}
}
}
else
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_ctor_get(x_57, 0);
lean_inc(x_73);
lean_dec(x_57);
x_74 = lean_unbox(x_73);
lean_dec(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
lean_dec_ref(x_56);
lean_dec_ref(x_38);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_76, 0, x_75);
return x_76;
}
else
{
lean_object* x_77; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_77 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec_ref(x_77);
x_79 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9;
x_80 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10;
x_81 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_78);
x_82 = l_Lean_mkApp4(x_79, x_38, x_56, x_80, x_81);
x_83 = lean_unsigned_to_nat(0u);
x_84 = l_Lean_Meta_Grind_pushNewFact(x_82, x_83, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_84;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec_ref(x_56);
lean_dec_ref(x_38);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_85 = lean_ctor_get(x_77, 0);
lean_inc(x_85);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 x_86 = x_77;
} else {
 lean_dec_ref(x_77);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(1, 1, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_85);
return x_87;
}
}
}
}
else
{
uint8_t x_88; 
lean_dec_ref(x_56);
lean_dec_ref(x_38);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_88 = !lean_is_exclusive(x_57);
if (x_88 == 0)
{
return x_57;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_57, 0);
lean_inc(x_89);
lean_dec(x_57);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_89);
return x_90;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; 
lean_dec_ref(x_38);
x_91 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_91);
lean_dec_ref(x_21);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_92 = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(x_91, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
lean_dec_ref(x_92);
lean_ctor_set_tag(x_40, 0);
lean_ctor_set(x_40, 0, x_1);
x_94 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_94, 0, x_52);
lean_ctor_set(x_94, 1, x_93);
lean_ctor_set(x_94, 2, x_40);
x_95 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(x_94, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_95;
}
else
{
uint8_t x_96; 
lean_free_object(x_40);
lean_dec(x_52);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_96 = !lean_is_exclusive(x_92);
if (x_96 == 0)
{
return x_92;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_92, 0);
lean_inc(x_97);
lean_dec(x_92);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
return x_98;
}
}
}
}
else
{
uint8_t x_99; 
lean_free_object(x_40);
lean_dec(x_52);
lean_dec_ref(x_38);
lean_dec_ref(x_21);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_99 = !lean_is_exclusive(x_53);
if (x_99 == 0)
{
return x_53;
}
else
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_53, 0);
lean_inc(x_100);
lean_dec(x_53);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
return x_101;
}
}
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_40, 0);
lean_inc(x_102);
lean_dec(x_40);
lean_inc_ref(x_1);
x_103 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_4, x_8, x_9);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; uint8_t x_105; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
lean_dec_ref(x_103);
x_105 = lean_unbox(x_104);
lean_dec(x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_102);
x_106 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_106);
lean_dec_ref(x_21);
lean_inc_ref(x_1);
x_107 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_4, x_8, x_9);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 x_109 = x_107;
} else {
 lean_dec_ref(x_107);
 x_109 = lean_box(0);
}
x_110 = lean_unbox(x_108);
lean_dec(x_108);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; 
lean_dec_ref(x_106);
lean_dec_ref(x_38);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_111 = lean_box(0);
if (lean_is_scalar(x_109)) {
 x_112 = lean_alloc_ctor(0, 1, 0);
} else {
 x_112 = x_109;
}
lean_ctor_set(x_112, 0, x_111);
return x_112;
}
else
{
lean_object* x_113; 
lean_dec(x_109);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_113 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
lean_dec_ref(x_113);
x_115 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9;
x_116 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10;
x_117 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_114);
x_118 = l_Lean_mkApp4(x_115, x_38, x_106, x_116, x_117);
x_119 = lean_unsigned_to_nat(0u);
x_120 = l_Lean_Meta_Grind_pushNewFact(x_118, x_119, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec_ref(x_106);
lean_dec_ref(x_38);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_121 = lean_ctor_get(x_113, 0);
lean_inc(x_121);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 x_122 = x_113;
} else {
 lean_dec_ref(x_113);
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
lean_dec_ref(x_106);
lean_dec_ref(x_38);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_124 = lean_ctor_get(x_107, 0);
lean_inc(x_124);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 x_125 = x_107;
} else {
 lean_dec_ref(x_107);
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
else
{
lean_object* x_127; lean_object* x_128; 
lean_dec_ref(x_38);
x_127 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_127);
lean_dec_ref(x_21);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_128 = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(x_127, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
lean_dec_ref(x_128);
x_130 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_130, 0, x_1);
x_131 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_131, 0, x_102);
lean_ctor_set(x_131, 1, x_129);
lean_ctor_set(x_131, 2, x_130);
x_132 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(x_131, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_102);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_133 = lean_ctor_get(x_128, 0);
lean_inc(x_133);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 x_134 = x_128;
} else {
 lean_dec_ref(x_128);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(1, 1, 0);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_133);
return x_135;
}
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_102);
lean_dec_ref(x_38);
lean_dec_ref(x_21);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_136 = lean_ctor_get(x_103, 0);
lean_inc(x_136);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 x_137 = x_103;
} else {
 lean_dec_ref(x_103);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 1, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_136);
return x_138;
}
}
}
}
else
{
uint8_t x_139; 
lean_dec_ref(x_38);
lean_dec_ref(x_21);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_139 = !lean_is_exclusive(x_39);
if (x_139 == 0)
{
return x_39;
}
else
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_39, 0);
lean_inc(x_140);
lean_dec(x_39);
x_141 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_141, 0, x_140);
return x_141;
}
}
}
}
else
{
lean_object* x_142; uint8_t x_143; 
x_142 = lean_ctor_get(x_33, 0);
lean_inc(x_142);
lean_dec(x_33);
x_143 = lean_unbox(x_142);
lean_dec(x_142);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; 
lean_dec_ref(x_23);
lean_dec_ref(x_21);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_144 = lean_box(0);
x_145 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_145, 0, x_144);
return x_145;
}
else
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_23, 1);
lean_inc_ref(x_146);
lean_dec_ref(x_23);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_146);
x_147 = l_Lean_Meta_getIntValue_x3f(x_146, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
lean_dec_ref(x_147);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; 
lean_dec_ref(x_146);
lean_dec_ref(x_21);
lean_dec(x_2);
x_149 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; uint8_t x_151; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
lean_dec_ref(x_149);
x_151 = lean_ctor_get_uint8(x_150, sizeof(void*)*8 + 13);
lean_dec(x_150);
if (x_151 == 0)
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_11 = lean_box(0);
goto block_14;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_152 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4;
x_153 = l_Lean_indentExpr(x_1);
x_154 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
x_155 = l_Lean_Meta_Grind_reportIssue(x_154, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_155) == 0)
{
lean_dec_ref(x_155);
x_11 = lean_box(0);
goto block_14;
}
else
{
return x_155;
}
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_156 = lean_ctor_get(x_149, 0);
lean_inc(x_156);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 x_157 = x_149;
} else {
 lean_dec_ref(x_149);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 1, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_156);
return x_158;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_148, 0);
lean_inc(x_159);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 x_160 = x_148;
} else {
 lean_dec_ref(x_148);
 x_160 = lean_box(0);
}
lean_inc_ref(x_1);
x_161 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_4, x_8, x_9);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; uint8_t x_163; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
lean_dec_ref(x_161);
x_163 = lean_unbox(x_162);
lean_dec(x_162);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; 
lean_dec(x_160);
lean_dec(x_159);
x_164 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_164);
lean_dec_ref(x_21);
lean_inc_ref(x_1);
x_165 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_4, x_8, x_9);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 x_167 = x_165;
} else {
 lean_dec_ref(x_165);
 x_167 = lean_box(0);
}
x_168 = lean_unbox(x_166);
lean_dec(x_166);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; 
lean_dec_ref(x_164);
lean_dec_ref(x_146);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_169 = lean_box(0);
if (lean_is_scalar(x_167)) {
 x_170 = lean_alloc_ctor(0, 1, 0);
} else {
 x_170 = x_167;
}
lean_ctor_set(x_170, 0, x_169);
return x_170;
}
else
{
lean_object* x_171; 
lean_dec(x_167);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_171 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
lean_dec_ref(x_171);
x_173 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9;
x_174 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10;
x_175 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_172);
x_176 = l_Lean_mkApp4(x_173, x_146, x_164, x_174, x_175);
x_177 = lean_unsigned_to_nat(0u);
x_178 = l_Lean_Meta_Grind_pushNewFact(x_176, x_177, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_178;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec_ref(x_164);
lean_dec_ref(x_146);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_179 = lean_ctor_get(x_171, 0);
lean_inc(x_179);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 x_180 = x_171;
} else {
 lean_dec_ref(x_171);
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
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec_ref(x_164);
lean_dec_ref(x_146);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_182 = lean_ctor_get(x_165, 0);
lean_inc(x_182);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 x_183 = x_165;
} else {
 lean_dec_ref(x_165);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(1, 1, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_182);
return x_184;
}
}
else
{
lean_object* x_185; lean_object* x_186; 
lean_dec_ref(x_146);
x_185 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_185);
lean_dec_ref(x_21);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_186 = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(x_185, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
lean_dec_ref(x_186);
if (lean_is_scalar(x_160)) {
 x_188 = lean_alloc_ctor(0, 1, 0);
} else {
 x_188 = x_160;
 lean_ctor_set_tag(x_188, 0);
}
lean_ctor_set(x_188, 0, x_1);
x_189 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_189, 0, x_159);
lean_ctor_set(x_189, 1, x_187);
lean_ctor_set(x_189, 2, x_188);
x_190 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(x_189, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_190;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_191 = lean_ctor_get(x_186, 0);
lean_inc(x_191);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 x_192 = x_186;
} else {
 lean_dec_ref(x_186);
 x_192 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(1, 1, 0);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_191);
return x_193;
}
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_160);
lean_dec(x_159);
lean_dec_ref(x_146);
lean_dec_ref(x_21);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_194 = lean_ctor_get(x_161, 0);
lean_inc(x_194);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 x_195 = x_161;
} else {
 lean_dec_ref(x_161);
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
lean_dec_ref(x_146);
lean_dec_ref(x_21);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_197 = lean_ctor_get(x_147, 0);
lean_inc(x_197);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 x_198 = x_147;
} else {
 lean_dec_ref(x_147);
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
lean_dec_ref(x_23);
lean_dec_ref(x_21);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_200 = !lean_is_exclusive(x_33);
if (x_200 == 0)
{
return x_33;
}
else
{
lean_object* x_201; lean_object* x_202; 
x_201 = lean_ctor_get(x_33, 0);
lean_inc(x_201);
lean_dec(x_33);
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
block_20:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(0);
if (lean_is_scalar(x_17)) {
 x_19 = lean_alloc_ctor(0, 1, 0);
} else {
 x_19 = x_17;
}
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
else
{
uint8_t x_203; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_203 = !lean_is_exclusive(x_15);
if (x_203 == 0)
{
return x_15;
}
else
{
lean_object* x_204; lean_object* x_205; 
x_204 = lean_ctor_get(x_15, 0);
lean_inc(x_204);
lean_dec(x_15);
x_205 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_205, 0, x_204);
return x_205;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_15; lean_object* x_19; uint8_t x_20; 
lean_inc_ref(x_1);
x_19 = l_Lean_Expr_cleanupAnnotations(x_1);
x_20 = l_Lean_Expr_isApp(x_19);
if (x_20 == 0)
{
lean_dec_ref(x_19);
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
lean_object* x_21; uint8_t x_22; 
lean_inc_ref(x_19);
x_21 = l_Lean_Expr_appFnCleanup___redArg(x_19);
x_22 = l_Lean_Expr_isApp(x_21);
if (x_22 == 0)
{
lean_dec_ref(x_21);
lean_dec_ref(x_19);
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
lean_object* x_23; uint8_t x_24; 
lean_inc_ref(x_21);
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_21);
x_24 = l_Lean_Expr_isApp(x_23);
if (x_24 == 0)
{
lean_dec_ref(x_23);
lean_dec_ref(x_21);
lean_dec_ref(x_19);
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
lean_object* x_25; uint8_t x_26; 
lean_inc_ref(x_23);
x_25 = l_Lean_Expr_appFnCleanup___redArg(x_23);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec_ref(x_25);
lean_dec_ref(x_23);
lean_dec_ref(x_21);
lean_dec_ref(x_19);
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
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = l_Lean_Expr_appFnCleanup___redArg(x_25);
x_28 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2;
x_29 = l_Lean_Expr_isConstOf(x_27, x_28);
lean_dec_ref(x_27);
if (x_29 == 0)
{
lean_dec_ref(x_23);
lean_dec_ref(x_21);
lean_dec_ref(x_19);
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
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_23, 1);
lean_inc_ref(x_30);
lean_dec_ref(x_23);
x_31 = l_Lean_Meta_isInstDvdNat___redArg(x_30, x_7);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec_ref(x_21);
lean_dec_ref(x_19);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_35 = lean_box(0);
lean_ctor_set(x_31, 0, x_35);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_free_object(x_31);
x_36 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_36);
lean_dec_ref(x_21);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_37 = l_Lean_Meta_getNatValue_x3f(x_36, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; 
lean_dec_ref(x_36);
lean_dec_ref(x_19);
lean_dec(x_2);
x_39 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; uint8_t x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = lean_ctor_get_uint8(x_40, sizeof(void*)*8 + 13);
lean_dec(x_40);
if (x_41 == 0)
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_15 = lean_box(0);
goto block_18;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4;
x_43 = l_Lean_indentExpr(x_1);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_Meta_Grind_reportIssue(x_44, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_45) == 0)
{
lean_dec_ref(x_45);
x_15 = lean_box(0);
goto block_18;
}
else
{
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_46 = !lean_is_exclusive(x_39);
if (x_46 == 0)
{
return x_39;
}
else
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_ctor_get(x_39, 0);
lean_inc(x_47);
lean_dec(x_39);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_38, 0);
lean_inc(x_49);
lean_dec_ref(x_38);
lean_inc_ref(x_1);
x_50 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_4, x_8, x_9);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec_ref(x_50);
x_52 = lean_unbox(x_51);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_49);
x_53 = lean_ctor_get(x_19, 1);
lean_inc_ref(x_53);
lean_dec_ref(x_19);
lean_inc_ref(x_1);
x_54 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_4, x_8, x_9);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = lean_unbox(x_56);
lean_dec(x_56);
if (x_57 == 0)
{
lean_object* x_58; 
lean_dec_ref(x_53);
lean_dec_ref(x_36);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_58 = lean_box(0);
lean_ctor_set(x_54, 0, x_58);
return x_54;
}
else
{
lean_object* x_59; 
lean_free_object(x_54);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_59 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec_ref(x_59);
x_61 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3;
x_62 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_60);
x_63 = l_Lean_mkApp3(x_61, x_36, x_53, x_62);
x_64 = lean_unsigned_to_nat(0u);
x_65 = l_Lean_Meta_Grind_pushNewFact(x_63, x_64, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_65;
}
else
{
uint8_t x_66; 
lean_dec_ref(x_53);
lean_dec_ref(x_36);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_66 = !lean_is_exclusive(x_59);
if (x_66 == 0)
{
return x_59;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_59, 0);
lean_inc(x_67);
lean_dec(x_59);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
}
}
else
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_ctor_get(x_54, 0);
lean_inc(x_69);
lean_dec(x_54);
x_70 = lean_unbox(x_69);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec_ref(x_53);
lean_dec_ref(x_36);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
else
{
lean_object* x_73; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_73 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec_ref(x_73);
x_75 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3;
x_76 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_74);
x_77 = l_Lean_mkApp3(x_75, x_36, x_53, x_76);
x_78 = lean_unsigned_to_nat(0u);
x_79 = l_Lean_Meta_Grind_pushNewFact(x_77, x_78, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec_ref(x_53);
lean_dec_ref(x_36);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_80 = lean_ctor_get(x_73, 0);
lean_inc(x_80);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 x_81 = x_73;
} else {
 lean_dec_ref(x_73);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 1, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_80);
return x_82;
}
}
}
}
else
{
uint8_t x_83; 
lean_dec_ref(x_53);
lean_dec_ref(x_36);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_83 = !lean_is_exclusive(x_54);
if (x_83 == 0)
{
return x_54;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_54, 0);
lean_inc(x_84);
lean_dec(x_54);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_19, 1);
lean_inc_ref(x_86);
lean_dec_ref(x_19);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_36);
x_87 = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(x_36, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
lean_dec_ref(x_87);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_86);
x_91 = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(x_86, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
lean_dec_ref(x_91);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
lean_dec_ref(x_95);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_93);
x_97 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_93, x_96, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
lean_dec_ref(x_97);
x_99 = l_Int_Linear_Expr_norm(x_98);
x_100 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7;
x_101 = l_Lean_mkApp6(x_100, x_36, x_86, x_89, x_93, x_90, x_94);
lean_inc(x_49);
x_102 = lean_nat_to_int(x_49);
x_103 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_103, 0, x_1);
lean_ctor_set(x_103, 1, x_101);
lean_ctor_set(x_103, 2, x_49);
lean_ctor_set(x_103, 3, x_98);
x_104 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_99);
lean_ctor_set(x_104, 2, x_103);
x_105 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(x_104, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_105;
}
else
{
uint8_t x_106; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_90);
lean_dec(x_89);
lean_dec_ref(x_86);
lean_dec(x_49);
lean_dec_ref(x_36);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_106 = !lean_is_exclusive(x_97);
if (x_106 == 0)
{
return x_97;
}
else
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_97, 0);
lean_inc(x_107);
lean_dec(x_97);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
return x_108;
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_90);
lean_dec(x_89);
lean_dec_ref(x_86);
lean_dec(x_49);
lean_dec_ref(x_36);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_109 = !lean_is_exclusive(x_95);
if (x_109 == 0)
{
return x_95;
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_95, 0);
lean_inc(x_110);
lean_dec(x_95);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_110);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_90);
lean_dec(x_89);
lean_dec_ref(x_86);
lean_dec(x_49);
lean_dec_ref(x_36);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_112 = !lean_is_exclusive(x_91);
if (x_112 == 0)
{
return x_91;
}
else
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_ctor_get(x_91, 0);
lean_inc(x_113);
lean_dec(x_91);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_113);
return x_114;
}
}
}
else
{
uint8_t x_115; 
lean_dec_ref(x_86);
lean_dec(x_49);
lean_dec_ref(x_36);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_115 = !lean_is_exclusive(x_87);
if (x_115 == 0)
{
return x_87;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_87, 0);
lean_inc(x_116);
lean_dec(x_87);
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_116);
return x_117;
}
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_49);
lean_dec_ref(x_36);
lean_dec_ref(x_19);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_118 = !lean_is_exclusive(x_50);
if (x_118 == 0)
{
return x_50;
}
else
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_50, 0);
lean_inc(x_119);
lean_dec(x_50);
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
lean_dec_ref(x_36);
lean_dec_ref(x_19);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_121 = !lean_is_exclusive(x_37);
if (x_121 == 0)
{
return x_37;
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_37, 0);
lean_inc(x_122);
lean_dec(x_37);
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
x_124 = lean_ctor_get(x_31, 0);
lean_inc(x_124);
lean_dec(x_31);
x_125 = lean_unbox(x_124);
lean_dec(x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; 
lean_dec_ref(x_21);
lean_dec_ref(x_19);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
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
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_128);
lean_dec_ref(x_21);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_129 = l_Lean_Meta_getNatValue_x3f(x_128, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
lean_dec_ref(x_129);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; 
lean_dec_ref(x_128);
lean_dec_ref(x_19);
lean_dec(x_2);
x_131 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; uint8_t x_133; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
lean_dec_ref(x_131);
x_133 = lean_ctor_get_uint8(x_132, sizeof(void*)*8 + 13);
lean_dec(x_132);
if (x_133 == 0)
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_15 = lean_box(0);
goto block_18;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_134 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4;
x_135 = l_Lean_indentExpr(x_1);
x_136 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
x_137 = l_Lean_Meta_Grind_reportIssue(x_136, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_137) == 0)
{
lean_dec_ref(x_137);
x_15 = lean_box(0);
goto block_18;
}
else
{
return x_137;
}
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_138 = lean_ctor_get(x_131, 0);
lean_inc(x_138);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 x_139 = x_131;
} else {
 lean_dec_ref(x_131);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(1, 1, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_138);
return x_140;
}
}
else
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_130, 0);
lean_inc(x_141);
lean_dec_ref(x_130);
lean_inc_ref(x_1);
x_142 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_4, x_8, x_9);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; uint8_t x_144; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
lean_dec_ref(x_142);
x_144 = lean_unbox(x_143);
lean_dec(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; 
lean_dec(x_141);
x_145 = lean_ctor_get(x_19, 1);
lean_inc_ref(x_145);
lean_dec_ref(x_19);
lean_inc_ref(x_1);
x_146 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_4, x_8, x_9);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 x_148 = x_146;
} else {
 lean_dec_ref(x_146);
 x_148 = lean_box(0);
}
x_149 = lean_unbox(x_147);
lean_dec(x_147);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; 
lean_dec_ref(x_145);
lean_dec_ref(x_128);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_150 = lean_box(0);
if (lean_is_scalar(x_148)) {
 x_151 = lean_alloc_ctor(0, 1, 0);
} else {
 x_151 = x_148;
}
lean_ctor_set(x_151, 0, x_150);
return x_151;
}
else
{
lean_object* x_152; 
lean_dec(x_148);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_152 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
lean_dec_ref(x_152);
x_154 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3;
x_155 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_153);
x_156 = l_Lean_mkApp3(x_154, x_128, x_145, x_155);
x_157 = lean_unsigned_to_nat(0u);
x_158 = l_Lean_Meta_Grind_pushNewFact(x_156, x_157, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_158;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec_ref(x_145);
lean_dec_ref(x_128);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_159 = lean_ctor_get(x_152, 0);
lean_inc(x_159);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 x_160 = x_152;
} else {
 lean_dec_ref(x_152);
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
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec_ref(x_145);
lean_dec_ref(x_128);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_162 = lean_ctor_get(x_146, 0);
lean_inc(x_162);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 x_163 = x_146;
} else {
 lean_dec_ref(x_146);
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
else
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_19, 1);
lean_inc_ref(x_165);
lean_dec_ref(x_19);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_128);
x_166 = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(x_128, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
lean_dec_ref(x_166);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_165);
x_170 = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(x_165, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
lean_dec_ref(x_170);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
x_174 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
lean_dec_ref(x_174);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_172);
x_176 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_172, x_175, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
lean_dec_ref(x_176);
x_178 = l_Int_Linear_Expr_norm(x_177);
x_179 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7;
x_180 = l_Lean_mkApp6(x_179, x_128, x_165, x_168, x_172, x_169, x_173);
lean_inc(x_141);
x_181 = lean_nat_to_int(x_141);
x_182 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_182, 0, x_1);
lean_ctor_set(x_182, 1, x_180);
lean_ctor_set(x_182, 2, x_141);
lean_ctor_set(x_182, 3, x_177);
x_183 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_178);
lean_ctor_set(x_183, 2, x_182);
x_184 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(x_183, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_184;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_169);
lean_dec(x_168);
lean_dec_ref(x_165);
lean_dec(x_141);
lean_dec_ref(x_128);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_185 = lean_ctor_get(x_176, 0);
lean_inc(x_185);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 x_186 = x_176;
} else {
 lean_dec_ref(x_176);
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
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_169);
lean_dec(x_168);
lean_dec_ref(x_165);
lean_dec(x_141);
lean_dec_ref(x_128);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_188 = lean_ctor_get(x_174, 0);
lean_inc(x_188);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 x_189 = x_174;
} else {
 lean_dec_ref(x_174);
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
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_169);
lean_dec(x_168);
lean_dec_ref(x_165);
lean_dec(x_141);
lean_dec_ref(x_128);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_191 = lean_ctor_get(x_170, 0);
lean_inc(x_191);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 x_192 = x_170;
} else {
 lean_dec_ref(x_170);
 x_192 = lean_box(0);
}
if (lean_is_scalar(x_192)) {
 x_193 = lean_alloc_ctor(1, 1, 0);
} else {
 x_193 = x_192;
}
lean_ctor_set(x_193, 0, x_191);
return x_193;
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec_ref(x_165);
lean_dec(x_141);
lean_dec_ref(x_128);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_194 = lean_ctor_get(x_166, 0);
lean_inc(x_194);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 x_195 = x_166;
} else {
 lean_dec_ref(x_166);
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
lean_dec(x_141);
lean_dec_ref(x_128);
lean_dec_ref(x_19);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_197 = lean_ctor_get(x_142, 0);
lean_inc(x_197);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 x_198 = x_142;
} else {
 lean_dec_ref(x_142);
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
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec_ref(x_128);
lean_dec_ref(x_19);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_200 = lean_ctor_get(x_129, 0);
lean_inc(x_200);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 x_201 = x_129;
} else {
 lean_dec_ref(x_129);
 x_201 = lean_box(0);
}
if (lean_is_scalar(x_201)) {
 x_202 = lean_alloc_ctor(1, 1, 0);
} else {
 x_202 = x_201;
}
lean_ctor_set(x_202, 0, x_200);
return x_202;
}
}
}
}
else
{
uint8_t x_203; 
lean_dec_ref(x_21);
lean_dec_ref(x_19);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_203 = !lean_is_exclusive(x_31);
if (x_203 == 0)
{
return x_31;
}
else
{
lean_object* x_204; lean_object* x_205; 
x_204 = lean_ctor_get(x_31, 0);
lean_inc(x_204);
lean_dec(x_31);
x_205 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_205, 0, x_204);
return x_205;
}
}
}
}
}
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
block_18:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*8 + 21);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_15 = lean_box(0);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; 
lean_free_object(x_11);
lean_inc_ref(x_1);
x_16 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_7);
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
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_21;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_Lean_Expr_appFnCleanup___redArg(x_22);
x_25 = l_Lean_Expr_isApp(x_24);
if (x_25 == 0)
{
lean_dec_ref(x_24);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_21;
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = l_Lean_Expr_appFnCleanup___redArg(x_24);
x_27 = l_Lean_Expr_isApp(x_26);
if (x_27 == 0)
{
lean_dec_ref(x_26);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_21;
}
else
{
lean_object* x_28; uint8_t x_29; 
x_28 = l_Lean_Expr_appFnCleanup___redArg(x_26);
x_29 = l_Lean_Expr_isApp(x_28);
if (x_29 == 0)
{
lean_dec_ref(x_28);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
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
lean_inc_ref(x_28);
x_30 = l_Lean_Expr_appFnCleanup___redArg(x_28);
x_31 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2;
x_32 = l_Lean_Expr_isConstOf(x_30, x_31);
lean_dec_ref(x_30);
if (x_32 == 0)
{
lean_dec_ref(x_28);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
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
lean_dec(x_18);
x_33 = lean_ctor_get(x_28, 1);
lean_inc_ref(x_33);
lean_dec_ref(x_28);
x_34 = l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0;
x_35 = l_Lean_Expr_isConstOf(x_33, x_34);
lean_dec_ref(x_33);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_36;
}
else
{
lean_object* x_37; 
x_37 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_37;
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
uint8_t x_38; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_38 = !lean_is_exclusive(x_16);
if (x_38 == 0)
{
return x_16;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_16, 0);
lean_inc(x_39);
lean_dec(x_16);
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
x_41 = lean_ctor_get(x_11, 0);
lean_inc(x_41);
lean_dec(x_11);
x_42 = lean_ctor_get_uint8(x_41, sizeof(void*)*8 + 21);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
else
{
lean_object* x_45; 
lean_inc_ref(x_1);
x_45 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_7);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_51; uint8_t x_52; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
x_51 = l_Lean_Expr_cleanupAnnotations(x_46);
x_52 = l_Lean_Expr_isApp(x_51);
if (x_52 == 0)
{
lean_dec_ref(x_51);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_50;
}
else
{
lean_object* x_53; uint8_t x_54; 
x_53 = l_Lean_Expr_appFnCleanup___redArg(x_51);
x_54 = l_Lean_Expr_isApp(x_53);
if (x_54 == 0)
{
lean_dec_ref(x_53);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_50;
}
else
{
lean_object* x_55; uint8_t x_56; 
x_55 = l_Lean_Expr_appFnCleanup___redArg(x_53);
x_56 = l_Lean_Expr_isApp(x_55);
if (x_56 == 0)
{
lean_dec_ref(x_55);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_50;
}
else
{
lean_object* x_57; uint8_t x_58; 
x_57 = l_Lean_Expr_appFnCleanup___redArg(x_55);
x_58 = l_Lean_Expr_isApp(x_57);
if (x_58 == 0)
{
lean_dec_ref(x_57);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_50;
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
lean_inc_ref(x_57);
x_59 = l_Lean_Expr_appFnCleanup___redArg(x_57);
x_60 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2;
x_61 = l_Lean_Expr_isConstOf(x_59, x_60);
lean_dec_ref(x_59);
if (x_61 == 0)
{
lean_dec_ref(x_57);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
goto block_50;
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
lean_dec(x_47);
x_62 = lean_ctor_get(x_57, 1);
lean_inc_ref(x_62);
lean_dec_ref(x_57);
x_63 = l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0;
x_64 = l_Lean_Expr_isConstOf(x_62, x_63);
lean_dec_ref(x_62);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_65;
}
else
{
lean_object* x_66; 
x_66 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_66;
}
}
}
}
}
}
block_50:
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_box(0);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 1, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_67 = lean_ctor_get(x_45, 0);
lean_inc(x_67);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 x_68 = x_45;
} else {
 lean_dec_ref(x_45);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 1, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_67);
return x_69;
}
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_70 = !lean_is_exclusive(x_11);
if (x_70 == 0)
{
return x_11;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_11, 0);
lean_inc(x_71);
lean_dec(x_11);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1830001947____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2;
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed), 10, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1830001947____hygCtx___hyg_8____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1830001947____hygCtx___hyg_8_();
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
l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__6 = _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__6();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__6);
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
l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__8 = _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__8();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__8);
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
l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10 = _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10);
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
if (builtin) {res = l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1830001947____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
