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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_8____boxed(lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_8_();
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstDvdInt___redArg(lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_mul(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Grind_isEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6;
lean_object* l_Lean_Meta_Grind_isEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_int_ediv(x_3, x_2);
lean_dec(x_3);
x_8 = l_Int_Linear_Poly_div(x_2, x_4);
lean_dec(x_2);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_5);
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
x_19 = lean_int_dec_eq(x_18, x_12);
lean_dec(x_12);
lean_dec(x_18);
if (x_19 == 0)
{
x_2 = x_16;
x_3 = x_13;
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
x_2 = x_16;
x_3 = x_13;
x_4 = x_14;
x_5 = x_15;
x_6 = x_19;
goto block_11;
}
else
{
lean_dec(x_16);
lean_dec_ref(x_14);
lean_dec(x_13);
return x_15;
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
x_12 = x_27;
x_13 = x_24;
x_14 = x_25;
x_15 = x_23;
x_16 = x_26;
goto block_22;
}
else
{
lean_object* x_29; 
x_29 = lean_int_neg(x_26);
lean_dec(x_26);
x_12 = x_27;
x_13 = x_24;
x_14 = x_25;
x_15 = x_23;
x_16 = x_29;
goto block_22;
}
}
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
if (lean_obj_tag(x_47) == 0)
{
lean_dec_ref(x_47);
x_29 = lean_box(0);
goto block_33;
}
else
{
uint8_t x_48; 
lean_dec_ref(x_28);
lean_dec(x_24);
lean_dec(x_18);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
return x_47;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_38);
lean_dec(x_36);
lean_dec_ref(x_28);
lean_dec(x_24);
lean_dec(x_18);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_51 = !lean_is_exclusive(x_39);
if (x_51 == 0)
{
return x_39;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_39, 0);
lean_inc(x_52);
lean_dec(x_39);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_36);
lean_dec_ref(x_28);
lean_dec(x_24);
lean_dec(x_18);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_37);
if (x_54 == 0)
{
return x_37;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_37, 0);
lean_inc(x_55);
lean_dec(x_37);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec_ref(x_28);
lean_dec(x_24);
lean_dec(x_18);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_57 = !lean_is_exclusive(x_35);
if (x_57 == 0)
{
return x_35;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_35, 0);
lean_inc(x_58);
lean_dec(x_35);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_58);
return x_59;
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
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
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("maxRecDepth", 11, 11);
return x_1;
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
if (lean_obj_tag(x_32) == 1)
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
else
{
lean_dec(x_32);
lean_dec_ref(x_8);
lean_ctor_set(x_30, 0, x_1);
return x_30;
}
}
else
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_30, 0);
lean_inc(x_43);
lean_dec(x_30);
if (lean_obj_tag(x_43) == 1)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_44, 0);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_ctor_get(x_45, 0);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_ctor_get(x_46, 0);
x_50 = l_Int_Linear_Poly_coeff(x_49, x_48);
x_51 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(x_50, x_48, x_46, x_47, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_47);
lean_dec(x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
x_1 = x_52;
goto _start;
}
else
{
lean_dec_ref(x_8);
return x_51;
}
}
else
{
lean_object* x_54; 
lean_dec(x_43);
lean_dec_ref(x_8);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_1);
return x_54;
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
if (lean_obj_tag(x_81) == 1)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_82);
x_83 = lean_ctor_get(x_81, 0);
lean_inc(x_83);
lean_dec_ref(x_81);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_83, 0);
lean_inc(x_86);
lean_dec(x_83);
x_87 = lean_ctor_get(x_84, 0);
lean_inc(x_87);
lean_dec(x_84);
x_88 = lean_ctor_get(x_85, 0);
x_89 = l_Int_Linear_Poly_coeff(x_88, x_87);
x_90 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(x_89, x_87, x_85, x_86, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_79, x_9);
lean_dec(x_86);
lean_dec(x_89);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
lean_dec_ref(x_90);
x_1 = x_91;
x_8 = x_79;
goto _start;
}
else
{
lean_dec_ref(x_79);
return x_90;
}
}
else
{
lean_object* x_93; 
lean_dec(x_81);
lean_dec_ref(x_79);
if (lean_is_scalar(x_82)) {
 x_93 = lean_alloc_ctor(0, 1, 0);
} else {
 x_93 = x_82;
}
lean_ctor_set(x_93, 0, x_1);
return x_93;
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
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(x_1);
return x_3;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(x_1, x_2);
lean_dec(x_1);
return x_3;
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
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_214; lean_object* x_215; 
lean_free_object(x_63);
x_214 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4;
x_215 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_214, x_8);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; uint8_t x_307; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
lean_dec_ref(x_215);
x_217 = lean_box(0);
x_307 = lean_unbox(x_216);
lean_dec(x_216);
if (x_307 == 0)
{
x_246 = x_2;
x_247 = x_3;
x_248 = x_4;
x_249 = x_5;
x_250 = x_6;
x_251 = x_7;
x_252 = x_8;
x_253 = x_9;
x_254 = lean_box(0);
goto block_306;
}
else
{
lean_object* x_308; 
lean_inc_ref(x_1);
x_308 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_8);
if (lean_obj_tag(x_308) == 0)
{
lean_object* x_309; lean_object* x_310; 
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
lean_dec_ref(x_308);
x_310 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_214, x_309, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_310) == 0)
{
lean_dec_ref(x_310);
x_246 = x_2;
x_247 = x_3;
x_248 = x_4;
x_249 = x_5;
x_250 = x_6;
x_251 = x_7;
x_252 = x_8;
x_253 = x_9;
x_254 = lean_box(0);
goto block_306;
}
else
{
lean_dec_ref(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_310;
}
}
else
{
uint8_t x_311; 
lean_dec_ref(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_311 = !lean_is_exclusive(x_308);
if (x_311 == 0)
{
return x_308;
}
else
{
lean_object* x_312; lean_object* x_313; 
x_312 = lean_ctor_get(x_308, 0);
lean_inc(x_312);
lean_dec(x_308);
x_313 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_313, 0, x_312);
return x_313;
}
}
}
block_245:
{
lean_object* x_235; 
x_235 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_226, x_232);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; 
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
lean_dec_ref(x_235);
x_237 = lean_ctor_get(x_236, 6);
lean_inc_ref(x_237);
lean_dec(x_236);
x_238 = lean_ctor_get(x_237, 2);
x_239 = lean_nat_dec_lt(x_220, x_238);
if (x_239 == 0)
{
lean_object* x_240; 
lean_dec_ref(x_237);
x_240 = l_outOfBounds___redArg(x_217);
x_67 = x_231;
x_68 = x_229;
x_69 = x_220;
x_70 = x_219;
x_71 = x_228;
x_72 = x_221;
x_73 = x_223;
x_74 = x_225;
x_75 = x_218;
x_76 = x_227;
x_77 = x_233;
x_78 = x_222;
x_79 = x_224;
x_80 = x_226;
x_81 = lean_box(0);
x_82 = x_232;
x_83 = x_230;
x_84 = x_240;
goto block_213;
}
else
{
lean_object* x_241; 
x_241 = l_Lean_PersistentArray_get_x21___redArg(x_217, x_237, x_220);
x_67 = x_231;
x_68 = x_229;
x_69 = x_220;
x_70 = x_219;
x_71 = x_228;
x_72 = x_221;
x_73 = x_223;
x_74 = x_225;
x_75 = x_218;
x_76 = x_227;
x_77 = x_233;
x_78 = x_222;
x_79 = x_224;
x_80 = x_226;
x_81 = lean_box(0);
x_82 = x_232;
x_83 = x_230;
x_84 = x_241;
goto block_213;
}
}
else
{
uint8_t x_242; 
lean_dec(x_233);
lean_dec_ref(x_232);
lean_dec(x_231);
lean_dec_ref(x_230);
lean_dec(x_229);
lean_dec_ref(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec_ref(x_225);
lean_dec_ref(x_224);
lean_dec_ref(x_223);
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_220);
lean_dec_ref(x_219);
lean_dec_ref(x_218);
x_242 = !lean_is_exclusive(x_235);
if (x_242 == 0)
{
return x_235;
}
else
{
lean_object* x_243; lean_object* x_244; 
x_243 = lean_ctor_get(x_235, 0);
lean_inc(x_243);
lean_dec(x_235);
x_244 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_244, 0, x_243);
return x_244;
}
}
}
block_306:
{
lean_object* x_255; lean_object* x_256; 
x_255 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc_ref(x_252);
x_256 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(x_255, x_246, x_247, x_248, x_249, x_250, x_251, x_252, x_253);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; uint8_t x_260; 
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
lean_dec_ref(x_256);
x_258 = lean_ctor_get(x_257, 0);
x_259 = lean_ctor_get(x_257, 1);
lean_inc(x_258);
x_260 = l_Int_Linear_Poly_isUnsatDvd(x_258, x_259);
if (x_260 == 0)
{
uint8_t x_261; 
x_261 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_257);
if (x_261 == 0)
{
if (lean_obj_tag(x_259) == 1)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
lean_inc_ref(x_259);
lean_inc(x_258);
x_262 = lean_ctor_get(x_259, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_259, 1);
lean_inc(x_263);
x_264 = lean_ctor_get(x_259, 2);
lean_inc_ref(x_264);
lean_inc(x_257);
x_265 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_257, x_246, x_252);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; uint8_t x_269; uint8_t x_270; uint8_t x_271; 
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
lean_dec_ref(x_265);
lean_inc(x_263);
x_267 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed), 2, 1);
lean_closure_set(x_267, 0, x_263);
lean_inc(x_263);
lean_inc(x_257);
x_268 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed), 3, 2);
lean_closure_set(x_268, 0, x_257);
lean_closure_set(x_268, 1, x_263);
x_269 = 0;
x_270 = lean_unbox(x_266);
lean_dec(x_266);
x_271 = l_Lean_instBEqLBool_beq(x_270, x_269);
if (x_271 == 0)
{
x_218 = x_264;
x_219 = x_257;
x_220 = x_263;
x_221 = x_258;
x_222 = x_262;
x_223 = x_268;
x_224 = x_259;
x_225 = x_267;
x_226 = x_246;
x_227 = x_247;
x_228 = x_248;
x_229 = x_249;
x_230 = x_250;
x_231 = x_251;
x_232 = x_252;
x_233 = x_253;
x_234 = lean_box(0);
goto block_245;
}
else
{
lean_object* x_272; 
lean_inc(x_263);
x_272 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_263, x_246);
if (lean_obj_tag(x_272) == 0)
{
lean_dec_ref(x_272);
x_218 = x_264;
x_219 = x_257;
x_220 = x_263;
x_221 = x_258;
x_222 = x_262;
x_223 = x_268;
x_224 = x_259;
x_225 = x_267;
x_226 = x_246;
x_227 = x_247;
x_228 = x_248;
x_229 = x_249;
x_230 = x_250;
x_231 = x_251;
x_232 = x_252;
x_233 = x_253;
x_234 = lean_box(0);
goto block_245;
}
else
{
lean_dec_ref(x_268);
lean_dec_ref(x_267);
lean_dec_ref(x_264);
lean_dec(x_263);
lean_dec(x_262);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_253);
lean_dec_ref(x_252);
lean_dec(x_251);
lean_dec_ref(x_250);
lean_dec(x_249);
lean_dec_ref(x_248);
lean_dec(x_247);
lean_dec(x_246);
return x_272;
}
}
}
else
{
uint8_t x_273; 
lean_dec_ref(x_264);
lean_dec(x_263);
lean_dec(x_262);
lean_dec_ref(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_253);
lean_dec_ref(x_252);
lean_dec(x_251);
lean_dec_ref(x_250);
lean_dec(x_249);
lean_dec_ref(x_248);
lean_dec(x_247);
lean_dec(x_246);
x_273 = !lean_is_exclusive(x_265);
if (x_273 == 0)
{
return x_265;
}
else
{
lean_object* x_274; lean_object* x_275; 
x_274 = lean_ctor_get(x_265, 0);
lean_inc(x_274);
lean_dec(x_265);
x_275 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_275, 0, x_274);
return x_275;
}
}
}
else
{
lean_object* x_276; 
x_276 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_257, x_246, x_247, x_248, x_249, x_250, x_251, x_252, x_253);
lean_dec(x_253);
lean_dec_ref(x_252);
lean_dec(x_251);
lean_dec_ref(x_250);
lean_dec(x_249);
lean_dec_ref(x_248);
lean_dec(x_247);
lean_dec(x_246);
return x_276;
}
}
else
{
lean_object* x_277; lean_object* x_278; 
lean_dec(x_249);
lean_dec_ref(x_248);
lean_dec(x_247);
x_277 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__6;
x_278 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_277, x_252);
if (lean_obj_tag(x_278) == 0)
{
lean_object* x_279; uint8_t x_280; 
x_279 = lean_ctor_get(x_278, 0);
lean_inc(x_279);
lean_dec_ref(x_278);
x_280 = lean_unbox(x_279);
lean_dec(x_279);
if (x_280 == 0)
{
lean_dec(x_257);
lean_dec(x_253);
lean_dec_ref(x_252);
lean_dec(x_251);
lean_dec_ref(x_250);
lean_dec(x_246);
x_41 = lean_box(0);
goto block_44;
}
else
{
lean_object* x_281; 
x_281 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_257, x_246, x_252);
lean_dec(x_246);
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_282; lean_object* x_283; 
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
lean_dec_ref(x_281);
x_283 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_277, x_282, x_250, x_251, x_252, x_253);
lean_dec(x_253);
lean_dec_ref(x_252);
lean_dec(x_251);
lean_dec_ref(x_250);
if (lean_obj_tag(x_283) == 0)
{
lean_dec_ref(x_283);
x_41 = lean_box(0);
goto block_44;
}
else
{
return x_283;
}
}
else
{
uint8_t x_284; 
lean_dec(x_253);
lean_dec_ref(x_252);
lean_dec(x_251);
lean_dec_ref(x_250);
x_284 = !lean_is_exclusive(x_281);
if (x_284 == 0)
{
return x_281;
}
else
{
lean_object* x_285; lean_object* x_286; 
x_285 = lean_ctor_get(x_281, 0);
lean_inc(x_285);
lean_dec(x_281);
x_286 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_286, 0, x_285);
return x_286;
}
}
}
}
else
{
uint8_t x_287; 
lean_dec(x_257);
lean_dec(x_253);
lean_dec_ref(x_252);
lean_dec(x_251);
lean_dec_ref(x_250);
lean_dec(x_246);
x_287 = !lean_is_exclusive(x_278);
if (x_287 == 0)
{
return x_278;
}
else
{
lean_object* x_288; lean_object* x_289; 
x_288 = lean_ctor_get(x_278, 0);
lean_inc(x_288);
lean_dec(x_278);
x_289 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_289, 0, x_288);
return x_289;
}
}
}
}
else
{
lean_object* x_290; lean_object* x_291; 
x_290 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__8;
x_291 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_290, x_252);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; uint8_t x_293; 
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
lean_dec_ref(x_291);
x_293 = lean_unbox(x_292);
lean_dec(x_292);
if (x_293 == 0)
{
x_11 = x_257;
x_12 = x_246;
x_13 = x_247;
x_14 = x_248;
x_15 = x_249;
x_16 = x_250;
x_17 = x_251;
x_18 = x_252;
x_19 = x_253;
x_20 = lean_box(0);
goto block_28;
}
else
{
lean_object* x_294; 
lean_inc(x_257);
x_294 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_257, x_246, x_252);
if (lean_obj_tag(x_294) == 0)
{
lean_object* x_295; lean_object* x_296; 
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
lean_dec_ref(x_294);
x_296 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_290, x_295, x_250, x_251, x_252, x_253);
if (lean_obj_tag(x_296) == 0)
{
lean_dec_ref(x_296);
x_11 = x_257;
x_12 = x_246;
x_13 = x_247;
x_14 = x_248;
x_15 = x_249;
x_16 = x_250;
x_17 = x_251;
x_18 = x_252;
x_19 = x_253;
x_20 = lean_box(0);
goto block_28;
}
else
{
lean_dec(x_257);
lean_dec(x_253);
lean_dec_ref(x_252);
lean_dec(x_251);
lean_dec_ref(x_250);
lean_dec(x_249);
lean_dec_ref(x_248);
lean_dec(x_247);
lean_dec(x_246);
return x_296;
}
}
else
{
uint8_t x_297; 
lean_dec(x_257);
lean_dec(x_253);
lean_dec_ref(x_252);
lean_dec(x_251);
lean_dec_ref(x_250);
lean_dec(x_249);
lean_dec_ref(x_248);
lean_dec(x_247);
lean_dec(x_246);
x_297 = !lean_is_exclusive(x_294);
if (x_297 == 0)
{
return x_294;
}
else
{
lean_object* x_298; lean_object* x_299; 
x_298 = lean_ctor_get(x_294, 0);
lean_inc(x_298);
lean_dec(x_294);
x_299 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_299, 0, x_298);
return x_299;
}
}
}
}
else
{
uint8_t x_300; 
lean_dec(x_257);
lean_dec(x_253);
lean_dec_ref(x_252);
lean_dec(x_251);
lean_dec_ref(x_250);
lean_dec(x_249);
lean_dec_ref(x_248);
lean_dec(x_247);
lean_dec(x_246);
x_300 = !lean_is_exclusive(x_291);
if (x_300 == 0)
{
return x_291;
}
else
{
lean_object* x_301; lean_object* x_302; 
x_301 = lean_ctor_get(x_291, 0);
lean_inc(x_301);
lean_dec(x_291);
x_302 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_302, 0, x_301);
return x_302;
}
}
}
}
else
{
uint8_t x_303; 
lean_dec(x_253);
lean_dec_ref(x_252);
lean_dec(x_251);
lean_dec_ref(x_250);
lean_dec(x_249);
lean_dec_ref(x_248);
lean_dec(x_247);
lean_dec(x_246);
x_303 = !lean_is_exclusive(x_256);
if (x_303 == 0)
{
return x_256;
}
else
{
lean_object* x_304; lean_object* x_305; 
x_304 = lean_ctor_get(x_256, 0);
lean_inc(x_304);
lean_dec(x_256);
x_305 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_305, 0, x_304);
return x_305;
}
}
}
}
else
{
uint8_t x_314; 
lean_dec_ref(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_314 = !lean_is_exclusive(x_215);
if (x_314 == 0)
{
return x_215;
}
else
{
lean_object* x_315; lean_object* x_316; 
x_315 = lean_ctor_get(x_215, 0);
lean_inc(x_315);
lean_dec(x_215);
x_316 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_316, 0, x_315);
return x_316;
}
}
block_213:
{
if (lean_obj_tag(x_84) == 1)
{
lean_object* x_85; lean_object* x_86; 
lean_dec_ref(x_79);
lean_dec_ref(x_73);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
lean_dec_ref(x_84);
x_86 = lean_ctor_get(x_85, 1);
lean_inc_ref(x_86);
if (lean_obj_tag(x_86) == 1)
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_88 = lean_ctor_get(x_85, 0);
x_89 = lean_ctor_get(x_86, 0);
x_90 = lean_ctor_get(x_86, 2);
x_91 = lean_ctor_get(x_86, 1);
lean_dec(x_91);
x_92 = lean_int_mul(x_78, x_88);
x_93 = lean_int_mul(x_89, x_72);
x_94 = l_Lean_Meta_Grind_Arith_gcdExt(x_92, x_93);
lean_dec(x_93);
lean_dec(x_92);
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; uint8_t x_97; 
x_96 = lean_ctor_get(x_94, 1);
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = lean_ctor_get(x_94, 0);
x_99 = lean_ctor_get(x_96, 0);
x_100 = lean_ctor_get(x_96, 1);
x_101 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0;
x_102 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_101, x_74, x_80);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec_ref(x_102);
x_103 = lean_int_mul(x_99, x_88);
lean_dec(x_99);
lean_inc_ref(x_75);
x_104 = l_Int_Linear_Poly_mul(x_75, x_103);
lean_dec(x_103);
x_105 = lean_int_mul(x_100, x_72);
lean_dec(x_100);
lean_inc_ref(x_90);
x_106 = l_Int_Linear_Poly_mul(x_90, x_105);
lean_dec(x_105);
x_107 = lean_int_mul(x_72, x_88);
lean_dec(x_72);
x_108 = l_Int_Linear_Poly_combine(x_104, x_106);
lean_inc(x_98);
lean_ctor_set(x_86, 2, x_108);
lean_ctor_set(x_86, 1, x_69);
lean_ctor_set(x_86, 0, x_98);
lean_inc(x_85);
lean_inc_ref(x_70);
lean_ctor_set_tag(x_96, 4);
lean_ctor_set(x_96, 1, x_85);
lean_ctor_set(x_96, 0, x_70);
x_109 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_86);
lean_ctor_set(x_109, 2, x_96);
lean_inc(x_77);
lean_inc_ref(x_82);
lean_inc(x_67);
lean_inc_ref(x_83);
lean_inc(x_68);
lean_inc_ref(x_71);
lean_inc(x_76);
lean_inc(x_80);
x_110 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_109, x_80, x_76, x_71, x_68, x_83, x_67, x_82, x_77);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
lean_dec_ref(x_110);
x_111 = l_Int_Linear_Poly_mul(x_75, x_89);
lean_dec(x_89);
x_112 = lean_int_neg(x_78);
lean_dec(x_78);
x_113 = l_Int_Linear_Poly_mul(x_90, x_112);
lean_dec(x_112);
x_114 = l_Int_Linear_Poly_combine(x_111, x_113);
lean_inc(x_85);
lean_ctor_set_tag(x_94, 5);
lean_ctor_set(x_94, 1, x_85);
lean_ctor_set(x_94, 0, x_70);
x_115 = !lean_is_exclusive(x_85);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_85, 2);
lean_dec(x_116);
x_117 = lean_ctor_get(x_85, 1);
lean_dec(x_117);
x_118 = lean_ctor_get(x_85, 0);
lean_dec(x_118);
lean_ctor_set(x_85, 2, x_94);
lean_ctor_set(x_85, 1, x_114);
lean_ctor_set(x_85, 0, x_98);
x_1 = x_85;
x_2 = x_80;
x_3 = x_76;
x_4 = x_71;
x_5 = x_68;
x_6 = x_83;
x_7 = x_67;
x_8 = x_82;
x_9 = x_77;
goto _start;
}
else
{
lean_object* x_120; 
lean_dec(x_85);
x_120 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_120, 0, x_98);
lean_ctor_set(x_120, 1, x_114);
lean_ctor_set(x_120, 2, x_94);
x_1 = x_120;
x_2 = x_80;
x_3 = x_76;
x_4 = x_71;
x_5 = x_68;
x_6 = x_83;
x_7 = x_67;
x_8 = x_82;
x_9 = x_77;
goto _start;
}
}
else
{
lean_free_object(x_94);
lean_dec(x_98);
lean_dec_ref(x_90);
lean_dec(x_89);
lean_dec(x_85);
lean_dec_ref(x_83);
lean_dec_ref(x_82);
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec_ref(x_75);
lean_dec_ref(x_71);
lean_dec_ref(x_70);
lean_dec(x_68);
lean_dec(x_67);
return x_110;
}
}
else
{
lean_free_object(x_96);
lean_dec(x_100);
lean_dec(x_99);
lean_free_object(x_94);
lean_dec(x_98);
lean_free_object(x_86);
lean_dec_ref(x_90);
lean_dec(x_89);
lean_dec(x_85);
lean_dec_ref(x_83);
lean_dec_ref(x_82);
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec_ref(x_75);
lean_dec(x_72);
lean_dec_ref(x_71);
lean_dec_ref(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
return x_102;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_122 = lean_ctor_get(x_94, 0);
x_123 = lean_ctor_get(x_96, 0);
x_124 = lean_ctor_get(x_96, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_96);
x_125 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0;
x_126 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_125, x_74, x_80);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec_ref(x_126);
x_127 = lean_int_mul(x_123, x_88);
lean_dec(x_123);
lean_inc_ref(x_75);
x_128 = l_Int_Linear_Poly_mul(x_75, x_127);
lean_dec(x_127);
x_129 = lean_int_mul(x_124, x_72);
lean_dec(x_124);
lean_inc_ref(x_90);
x_130 = l_Int_Linear_Poly_mul(x_90, x_129);
lean_dec(x_129);
x_131 = lean_int_mul(x_72, x_88);
lean_dec(x_72);
x_132 = l_Int_Linear_Poly_combine(x_128, x_130);
lean_inc(x_122);
lean_ctor_set(x_86, 2, x_132);
lean_ctor_set(x_86, 1, x_69);
lean_ctor_set(x_86, 0, x_122);
lean_inc(x_85);
lean_inc_ref(x_70);
x_133 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_133, 0, x_70);
lean_ctor_set(x_133, 1, x_85);
x_134 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_86);
lean_ctor_set(x_134, 2, x_133);
lean_inc(x_77);
lean_inc_ref(x_82);
lean_inc(x_67);
lean_inc_ref(x_83);
lean_inc(x_68);
lean_inc_ref(x_71);
lean_inc(x_76);
lean_inc(x_80);
x_135 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_134, x_80, x_76, x_71, x_68, x_83, x_67, x_82, x_77);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec_ref(x_135);
x_136 = l_Int_Linear_Poly_mul(x_75, x_89);
lean_dec(x_89);
x_137 = lean_int_neg(x_78);
lean_dec(x_78);
x_138 = l_Int_Linear_Poly_mul(x_90, x_137);
lean_dec(x_137);
x_139 = l_Int_Linear_Poly_combine(x_136, x_138);
lean_inc(x_85);
lean_ctor_set_tag(x_94, 5);
lean_ctor_set(x_94, 1, x_85);
lean_ctor_set(x_94, 0, x_70);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 lean_ctor_release(x_85, 2);
 x_140 = x_85;
} else {
 lean_dec_ref(x_85);
 x_140 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(0, 3, 0);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_122);
lean_ctor_set(x_141, 1, x_139);
lean_ctor_set(x_141, 2, x_94);
x_1 = x_141;
x_2 = x_80;
x_3 = x_76;
x_4 = x_71;
x_5 = x_68;
x_6 = x_83;
x_7 = x_67;
x_8 = x_82;
x_9 = x_77;
goto _start;
}
else
{
lean_free_object(x_94);
lean_dec(x_122);
lean_dec_ref(x_90);
lean_dec(x_89);
lean_dec(x_85);
lean_dec_ref(x_83);
lean_dec_ref(x_82);
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec_ref(x_75);
lean_dec_ref(x_71);
lean_dec_ref(x_70);
lean_dec(x_68);
lean_dec(x_67);
return x_135;
}
}
else
{
lean_dec(x_124);
lean_dec(x_123);
lean_free_object(x_94);
lean_dec(x_122);
lean_free_object(x_86);
lean_dec_ref(x_90);
lean_dec(x_89);
lean_dec(x_85);
lean_dec_ref(x_83);
lean_dec_ref(x_82);
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec_ref(x_75);
lean_dec(x_72);
lean_dec_ref(x_71);
lean_dec_ref(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
return x_126;
}
}
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_143 = lean_ctor_get(x_94, 1);
x_144 = lean_ctor_get(x_94, 0);
lean_inc(x_143);
lean_inc(x_144);
lean_dec(x_94);
x_145 = lean_ctor_get(x_143, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_143, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_147 = x_143;
} else {
 lean_dec_ref(x_143);
 x_147 = lean_box(0);
}
x_148 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0;
x_149 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_148, x_74, x_80);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec_ref(x_149);
x_150 = lean_int_mul(x_145, x_88);
lean_dec(x_145);
lean_inc_ref(x_75);
x_151 = l_Int_Linear_Poly_mul(x_75, x_150);
lean_dec(x_150);
x_152 = lean_int_mul(x_146, x_72);
lean_dec(x_146);
lean_inc_ref(x_90);
x_153 = l_Int_Linear_Poly_mul(x_90, x_152);
lean_dec(x_152);
x_154 = lean_int_mul(x_72, x_88);
lean_dec(x_72);
x_155 = l_Int_Linear_Poly_combine(x_151, x_153);
lean_inc(x_144);
lean_ctor_set(x_86, 2, x_155);
lean_ctor_set(x_86, 1, x_69);
lean_ctor_set(x_86, 0, x_144);
lean_inc(x_85);
lean_inc_ref(x_70);
if (lean_is_scalar(x_147)) {
 x_156 = lean_alloc_ctor(4, 2, 0);
} else {
 x_156 = x_147;
 lean_ctor_set_tag(x_156, 4);
}
lean_ctor_set(x_156, 0, x_70);
lean_ctor_set(x_156, 1, x_85);
x_157 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set(x_157, 1, x_86);
lean_ctor_set(x_157, 2, x_156);
lean_inc(x_77);
lean_inc_ref(x_82);
lean_inc(x_67);
lean_inc_ref(x_83);
lean_inc(x_68);
lean_inc_ref(x_71);
lean_inc(x_76);
lean_inc(x_80);
x_158 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_157, x_80, x_76, x_71, x_68, x_83, x_67, x_82, x_77);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec_ref(x_158);
x_159 = l_Int_Linear_Poly_mul(x_75, x_89);
lean_dec(x_89);
x_160 = lean_int_neg(x_78);
lean_dec(x_78);
x_161 = l_Int_Linear_Poly_mul(x_90, x_160);
lean_dec(x_160);
x_162 = l_Int_Linear_Poly_combine(x_159, x_161);
lean_inc(x_85);
x_163 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_163, 0, x_70);
lean_ctor_set(x_163, 1, x_85);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 lean_ctor_release(x_85, 2);
 x_164 = x_85;
} else {
 lean_dec_ref(x_85);
 x_164 = lean_box(0);
}
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(0, 3, 0);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_144);
lean_ctor_set(x_165, 1, x_162);
lean_ctor_set(x_165, 2, x_163);
x_1 = x_165;
x_2 = x_80;
x_3 = x_76;
x_4 = x_71;
x_5 = x_68;
x_6 = x_83;
x_7 = x_67;
x_8 = x_82;
x_9 = x_77;
goto _start;
}
else
{
lean_dec(x_144);
lean_dec_ref(x_90);
lean_dec(x_89);
lean_dec(x_85);
lean_dec_ref(x_83);
lean_dec_ref(x_82);
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec_ref(x_75);
lean_dec_ref(x_71);
lean_dec_ref(x_70);
lean_dec(x_68);
lean_dec(x_67);
return x_158;
}
}
else
{
lean_dec(x_147);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_144);
lean_free_object(x_86);
lean_dec_ref(x_90);
lean_dec(x_89);
lean_dec(x_85);
lean_dec_ref(x_83);
lean_dec_ref(x_82);
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec_ref(x_75);
lean_dec(x_72);
lean_dec_ref(x_71);
lean_dec_ref(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
return x_149;
}
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_167 = lean_ctor_get(x_85, 0);
x_168 = lean_ctor_get(x_86, 0);
x_169 = lean_ctor_get(x_86, 2);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_86);
x_170 = lean_int_mul(x_78, x_167);
x_171 = lean_int_mul(x_168, x_72);
x_172 = l_Lean_Meta_Grind_Arith_gcdExt(x_170, x_171);
lean_dec(x_171);
lean_dec(x_170);
x_173 = lean_ctor_get(x_172, 1);
lean_inc(x_173);
x_174 = lean_ctor_get(x_172, 0);
lean_inc(x_174);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_175 = x_172;
} else {
 lean_dec_ref(x_172);
 x_175 = lean_box(0);
}
x_176 = lean_ctor_get(x_173, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_173, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 lean_ctor_release(x_173, 1);
 x_178 = x_173;
} else {
 lean_dec_ref(x_173);
 x_178 = lean_box(0);
}
x_179 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0;
x_180 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_179, x_74, x_80);
if (lean_obj_tag(x_180) == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec_ref(x_180);
x_181 = lean_int_mul(x_176, x_167);
lean_dec(x_176);
lean_inc_ref(x_75);
x_182 = l_Int_Linear_Poly_mul(x_75, x_181);
lean_dec(x_181);
x_183 = lean_int_mul(x_177, x_72);
lean_dec(x_177);
lean_inc_ref(x_169);
x_184 = l_Int_Linear_Poly_mul(x_169, x_183);
lean_dec(x_183);
x_185 = lean_int_mul(x_72, x_167);
lean_dec(x_72);
x_186 = l_Int_Linear_Poly_combine(x_182, x_184);
lean_inc(x_174);
x_187 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_187, 0, x_174);
lean_ctor_set(x_187, 1, x_69);
lean_ctor_set(x_187, 2, x_186);
lean_inc(x_85);
lean_inc_ref(x_70);
if (lean_is_scalar(x_178)) {
 x_188 = lean_alloc_ctor(4, 2, 0);
} else {
 x_188 = x_178;
 lean_ctor_set_tag(x_188, 4);
}
lean_ctor_set(x_188, 0, x_70);
lean_ctor_set(x_188, 1, x_85);
x_189 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_189, 0, x_185);
lean_ctor_set(x_189, 1, x_187);
lean_ctor_set(x_189, 2, x_188);
lean_inc(x_77);
lean_inc_ref(x_82);
lean_inc(x_67);
lean_inc_ref(x_83);
lean_inc(x_68);
lean_inc_ref(x_71);
lean_inc(x_76);
lean_inc(x_80);
x_190 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_189, x_80, x_76, x_71, x_68, x_83, x_67, x_82, x_77);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
lean_dec_ref(x_190);
x_191 = l_Int_Linear_Poly_mul(x_75, x_168);
lean_dec(x_168);
x_192 = lean_int_neg(x_78);
lean_dec(x_78);
x_193 = l_Int_Linear_Poly_mul(x_169, x_192);
lean_dec(x_192);
x_194 = l_Int_Linear_Poly_combine(x_191, x_193);
lean_inc(x_85);
if (lean_is_scalar(x_175)) {
 x_195 = lean_alloc_ctor(5, 2, 0);
} else {
 x_195 = x_175;
 lean_ctor_set_tag(x_195, 5);
}
lean_ctor_set(x_195, 0, x_70);
lean_ctor_set(x_195, 1, x_85);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 lean_ctor_release(x_85, 2);
 x_196 = x_85;
} else {
 lean_dec_ref(x_85);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(0, 3, 0);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_174);
lean_ctor_set(x_197, 1, x_194);
lean_ctor_set(x_197, 2, x_195);
x_1 = x_197;
x_2 = x_80;
x_3 = x_76;
x_4 = x_71;
x_5 = x_68;
x_6 = x_83;
x_7 = x_67;
x_8 = x_82;
x_9 = x_77;
goto _start;
}
else
{
lean_dec(x_175);
lean_dec(x_174);
lean_dec_ref(x_169);
lean_dec(x_168);
lean_dec(x_85);
lean_dec_ref(x_83);
lean_dec_ref(x_82);
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec_ref(x_75);
lean_dec_ref(x_71);
lean_dec_ref(x_70);
lean_dec(x_68);
lean_dec(x_67);
return x_190;
}
}
else
{
lean_dec(x_178);
lean_dec(x_177);
lean_dec(x_176);
lean_dec(x_175);
lean_dec(x_174);
lean_dec_ref(x_169);
lean_dec(x_168);
lean_dec(x_85);
lean_dec_ref(x_83);
lean_dec_ref(x_82);
lean_dec(x_80);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec_ref(x_75);
lean_dec(x_72);
lean_dec_ref(x_71);
lean_dec_ref(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
return x_180;
}
}
}
else
{
lean_object* x_199; 
lean_dec_ref(x_86);
lean_dec(x_78);
lean_dec_ref(x_75);
lean_dec_ref(x_74);
lean_dec(x_72);
lean_dec_ref(x_70);
lean_dec(x_69);
x_199 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_85, x_80, x_76, x_71, x_68, x_83, x_67, x_82, x_77);
lean_dec(x_77);
lean_dec_ref(x_82);
lean_dec(x_67);
lean_dec_ref(x_83);
lean_dec(x_68);
lean_dec_ref(x_71);
lean_dec(x_76);
lean_dec(x_80);
return x_199;
}
}
else
{
lean_object* x_200; lean_object* x_201; 
lean_dec(x_84);
lean_dec(x_78);
lean_dec(x_76);
lean_dec_ref(x_75);
lean_dec_ref(x_74);
lean_dec(x_72);
lean_dec_ref(x_71);
lean_dec(x_69);
lean_dec(x_68);
x_200 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3;
x_201 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_200, x_82);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; uint8_t x_203; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
lean_dec_ref(x_201);
x_203 = lean_unbox(x_202);
lean_dec(x_202);
if (x_203 == 0)
{
lean_dec_ref(x_70);
x_29 = x_73;
x_30 = x_79;
x_31 = x_80;
x_32 = x_83;
x_33 = x_67;
x_34 = x_82;
x_35 = x_77;
x_36 = lean_box(0);
goto block_40;
}
else
{
lean_object* x_204; 
x_204 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_70, x_80, x_82);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
lean_dec_ref(x_204);
x_206 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_200, x_205, x_83, x_67, x_82, x_77);
if (lean_obj_tag(x_206) == 0)
{
lean_dec_ref(x_206);
x_29 = x_73;
x_30 = x_79;
x_31 = x_80;
x_32 = x_83;
x_33 = x_67;
x_34 = x_82;
x_35 = x_77;
x_36 = lean_box(0);
goto block_40;
}
else
{
lean_dec_ref(x_83);
lean_dec_ref(x_82);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec(x_77);
lean_dec_ref(x_73);
lean_dec(x_67);
return x_206;
}
}
else
{
uint8_t x_207; 
lean_dec_ref(x_83);
lean_dec_ref(x_82);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec(x_77);
lean_dec_ref(x_73);
lean_dec(x_67);
x_207 = !lean_is_exclusive(x_204);
if (x_207 == 0)
{
return x_204;
}
else
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_ctor_get(x_204, 0);
lean_inc(x_208);
lean_dec(x_204);
x_209 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_209, 0, x_208);
return x_209;
}
}
}
}
else
{
uint8_t x_210; 
lean_dec_ref(x_83);
lean_dec_ref(x_82);
lean_dec(x_80);
lean_dec_ref(x_79);
lean_dec(x_77);
lean_dec_ref(x_73);
lean_dec_ref(x_70);
lean_dec(x_67);
x_210 = !lean_is_exclusive(x_201);
if (x_210 == 0)
{
return x_201;
}
else
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_ctor_get(x_201, 0);
lean_inc(x_211);
lean_dec(x_201);
x_212 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_212, 0, x_211);
return x_212;
}
}
}
}
}
else
{
lean_object* x_317; 
lean_dec_ref(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_317 = lean_box(0);
lean_ctor_set(x_63, 0, x_317);
return x_63;
}
}
else
{
lean_object* x_318; uint8_t x_319; 
x_318 = lean_ctor_get(x_63, 0);
lean_inc(x_318);
lean_dec(x_63);
x_319 = lean_unbox(x_318);
lean_dec(x_318);
if (x_319 == 0)
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_388; lean_object* x_389; 
x_388 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4;
x_389 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_388, x_8);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; uint8_t x_481; 
x_390 = lean_ctor_get(x_389, 0);
lean_inc(x_390);
lean_dec_ref(x_389);
x_391 = lean_box(0);
x_481 = lean_unbox(x_390);
lean_dec(x_390);
if (x_481 == 0)
{
x_420 = x_2;
x_421 = x_3;
x_422 = x_4;
x_423 = x_5;
x_424 = x_6;
x_425 = x_7;
x_426 = x_8;
x_427 = x_9;
x_428 = lean_box(0);
goto block_480;
}
else
{
lean_object* x_482; 
lean_inc_ref(x_1);
x_482 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_8);
if (lean_obj_tag(x_482) == 0)
{
lean_object* x_483; lean_object* x_484; 
x_483 = lean_ctor_get(x_482, 0);
lean_inc(x_483);
lean_dec_ref(x_482);
x_484 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_388, x_483, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_484) == 0)
{
lean_dec_ref(x_484);
x_420 = x_2;
x_421 = x_3;
x_422 = x_4;
x_423 = x_5;
x_424 = x_6;
x_425 = x_7;
x_426 = x_8;
x_427 = x_9;
x_428 = lean_box(0);
goto block_480;
}
else
{
lean_dec_ref(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_484;
}
}
else
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; 
lean_dec_ref(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_485 = lean_ctor_get(x_482, 0);
lean_inc(x_485);
if (lean_is_exclusive(x_482)) {
 lean_ctor_release(x_482, 0);
 x_486 = x_482;
} else {
 lean_dec_ref(x_482);
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
block_419:
{
lean_object* x_409; 
x_409 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_400, x_406);
if (lean_obj_tag(x_409) == 0)
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; uint8_t x_413; 
x_410 = lean_ctor_get(x_409, 0);
lean_inc(x_410);
lean_dec_ref(x_409);
x_411 = lean_ctor_get(x_410, 6);
lean_inc_ref(x_411);
lean_dec(x_410);
x_412 = lean_ctor_get(x_411, 2);
x_413 = lean_nat_dec_lt(x_394, x_412);
if (x_413 == 0)
{
lean_object* x_414; 
lean_dec_ref(x_411);
x_414 = l_outOfBounds___redArg(x_391);
x_320 = x_405;
x_321 = x_403;
x_322 = x_394;
x_323 = x_393;
x_324 = x_402;
x_325 = x_395;
x_326 = x_397;
x_327 = x_399;
x_328 = x_392;
x_329 = x_401;
x_330 = x_407;
x_331 = x_396;
x_332 = x_398;
x_333 = x_400;
x_334 = lean_box(0);
x_335 = x_406;
x_336 = x_404;
x_337 = x_414;
goto block_387;
}
else
{
lean_object* x_415; 
x_415 = l_Lean_PersistentArray_get_x21___redArg(x_391, x_411, x_394);
x_320 = x_405;
x_321 = x_403;
x_322 = x_394;
x_323 = x_393;
x_324 = x_402;
x_325 = x_395;
x_326 = x_397;
x_327 = x_399;
x_328 = x_392;
x_329 = x_401;
x_330 = x_407;
x_331 = x_396;
x_332 = x_398;
x_333 = x_400;
x_334 = lean_box(0);
x_335 = x_406;
x_336 = x_404;
x_337 = x_415;
goto block_387;
}
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; 
lean_dec(x_407);
lean_dec_ref(x_406);
lean_dec(x_405);
lean_dec_ref(x_404);
lean_dec(x_403);
lean_dec_ref(x_402);
lean_dec(x_401);
lean_dec(x_400);
lean_dec_ref(x_399);
lean_dec_ref(x_398);
lean_dec_ref(x_397);
lean_dec(x_396);
lean_dec(x_395);
lean_dec(x_394);
lean_dec_ref(x_393);
lean_dec_ref(x_392);
x_416 = lean_ctor_get(x_409, 0);
lean_inc(x_416);
if (lean_is_exclusive(x_409)) {
 lean_ctor_release(x_409, 0);
 x_417 = x_409;
} else {
 lean_dec_ref(x_409);
 x_417 = lean_box(0);
}
if (lean_is_scalar(x_417)) {
 x_418 = lean_alloc_ctor(1, 1, 0);
} else {
 x_418 = x_417;
}
lean_ctor_set(x_418, 0, x_416);
return x_418;
}
}
block_480:
{
lean_object* x_429; lean_object* x_430; 
x_429 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc_ref(x_426);
x_430 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(x_429, x_420, x_421, x_422, x_423, x_424, x_425, x_426, x_427);
if (lean_obj_tag(x_430) == 0)
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; uint8_t x_434; 
x_431 = lean_ctor_get(x_430, 0);
lean_inc(x_431);
lean_dec_ref(x_430);
x_432 = lean_ctor_get(x_431, 0);
x_433 = lean_ctor_get(x_431, 1);
lean_inc(x_432);
x_434 = l_Int_Linear_Poly_isUnsatDvd(x_432, x_433);
if (x_434 == 0)
{
uint8_t x_435; 
x_435 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_431);
if (x_435 == 0)
{
if (lean_obj_tag(x_433) == 1)
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
lean_inc_ref(x_433);
lean_inc(x_432);
x_436 = lean_ctor_get(x_433, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_433, 1);
lean_inc(x_437);
x_438 = lean_ctor_get(x_433, 2);
lean_inc_ref(x_438);
lean_inc(x_431);
x_439 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_431, x_420, x_426);
if (lean_obj_tag(x_439) == 0)
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; uint8_t x_443; uint8_t x_444; uint8_t x_445; 
x_440 = lean_ctor_get(x_439, 0);
lean_inc(x_440);
lean_dec_ref(x_439);
lean_inc(x_437);
x_441 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed), 2, 1);
lean_closure_set(x_441, 0, x_437);
lean_inc(x_437);
lean_inc(x_431);
x_442 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed), 3, 2);
lean_closure_set(x_442, 0, x_431);
lean_closure_set(x_442, 1, x_437);
x_443 = 0;
x_444 = lean_unbox(x_440);
lean_dec(x_440);
x_445 = l_Lean_instBEqLBool_beq(x_444, x_443);
if (x_445 == 0)
{
x_392 = x_438;
x_393 = x_431;
x_394 = x_437;
x_395 = x_432;
x_396 = x_436;
x_397 = x_442;
x_398 = x_433;
x_399 = x_441;
x_400 = x_420;
x_401 = x_421;
x_402 = x_422;
x_403 = x_423;
x_404 = x_424;
x_405 = x_425;
x_406 = x_426;
x_407 = x_427;
x_408 = lean_box(0);
goto block_419;
}
else
{
lean_object* x_446; 
lean_inc(x_437);
x_446 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_437, x_420);
if (lean_obj_tag(x_446) == 0)
{
lean_dec_ref(x_446);
x_392 = x_438;
x_393 = x_431;
x_394 = x_437;
x_395 = x_432;
x_396 = x_436;
x_397 = x_442;
x_398 = x_433;
x_399 = x_441;
x_400 = x_420;
x_401 = x_421;
x_402 = x_422;
x_403 = x_423;
x_404 = x_424;
x_405 = x_425;
x_406 = x_426;
x_407 = x_427;
x_408 = lean_box(0);
goto block_419;
}
else
{
lean_dec_ref(x_442);
lean_dec_ref(x_441);
lean_dec_ref(x_438);
lean_dec(x_437);
lean_dec(x_436);
lean_dec_ref(x_433);
lean_dec(x_432);
lean_dec(x_431);
lean_dec(x_427);
lean_dec_ref(x_426);
lean_dec(x_425);
lean_dec_ref(x_424);
lean_dec(x_423);
lean_dec_ref(x_422);
lean_dec(x_421);
lean_dec(x_420);
return x_446;
}
}
}
else
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; 
lean_dec_ref(x_438);
lean_dec(x_437);
lean_dec(x_436);
lean_dec_ref(x_433);
lean_dec(x_432);
lean_dec(x_431);
lean_dec(x_427);
lean_dec_ref(x_426);
lean_dec(x_425);
lean_dec_ref(x_424);
lean_dec(x_423);
lean_dec_ref(x_422);
lean_dec(x_421);
lean_dec(x_420);
x_447 = lean_ctor_get(x_439, 0);
lean_inc(x_447);
if (lean_is_exclusive(x_439)) {
 lean_ctor_release(x_439, 0);
 x_448 = x_439;
} else {
 lean_dec_ref(x_439);
 x_448 = lean_box(0);
}
if (lean_is_scalar(x_448)) {
 x_449 = lean_alloc_ctor(1, 1, 0);
} else {
 x_449 = x_448;
}
lean_ctor_set(x_449, 0, x_447);
return x_449;
}
}
else
{
lean_object* x_450; 
x_450 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_431, x_420, x_421, x_422, x_423, x_424, x_425, x_426, x_427);
lean_dec(x_427);
lean_dec_ref(x_426);
lean_dec(x_425);
lean_dec_ref(x_424);
lean_dec(x_423);
lean_dec_ref(x_422);
lean_dec(x_421);
lean_dec(x_420);
return x_450;
}
}
else
{
lean_object* x_451; lean_object* x_452; 
lean_dec(x_423);
lean_dec_ref(x_422);
lean_dec(x_421);
x_451 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__6;
x_452 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_451, x_426);
if (lean_obj_tag(x_452) == 0)
{
lean_object* x_453; uint8_t x_454; 
x_453 = lean_ctor_get(x_452, 0);
lean_inc(x_453);
lean_dec_ref(x_452);
x_454 = lean_unbox(x_453);
lean_dec(x_453);
if (x_454 == 0)
{
lean_dec(x_431);
lean_dec(x_427);
lean_dec_ref(x_426);
lean_dec(x_425);
lean_dec_ref(x_424);
lean_dec(x_420);
x_41 = lean_box(0);
goto block_44;
}
else
{
lean_object* x_455; 
x_455 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_431, x_420, x_426);
lean_dec(x_420);
if (lean_obj_tag(x_455) == 0)
{
lean_object* x_456; lean_object* x_457; 
x_456 = lean_ctor_get(x_455, 0);
lean_inc(x_456);
lean_dec_ref(x_455);
x_457 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_451, x_456, x_424, x_425, x_426, x_427);
lean_dec(x_427);
lean_dec_ref(x_426);
lean_dec(x_425);
lean_dec_ref(x_424);
if (lean_obj_tag(x_457) == 0)
{
lean_dec_ref(x_457);
x_41 = lean_box(0);
goto block_44;
}
else
{
return x_457;
}
}
else
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; 
lean_dec(x_427);
lean_dec_ref(x_426);
lean_dec(x_425);
lean_dec_ref(x_424);
x_458 = lean_ctor_get(x_455, 0);
lean_inc(x_458);
if (lean_is_exclusive(x_455)) {
 lean_ctor_release(x_455, 0);
 x_459 = x_455;
} else {
 lean_dec_ref(x_455);
 x_459 = lean_box(0);
}
if (lean_is_scalar(x_459)) {
 x_460 = lean_alloc_ctor(1, 1, 0);
} else {
 x_460 = x_459;
}
lean_ctor_set(x_460, 0, x_458);
return x_460;
}
}
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; 
lean_dec(x_431);
lean_dec(x_427);
lean_dec_ref(x_426);
lean_dec(x_425);
lean_dec_ref(x_424);
lean_dec(x_420);
x_461 = lean_ctor_get(x_452, 0);
lean_inc(x_461);
if (lean_is_exclusive(x_452)) {
 lean_ctor_release(x_452, 0);
 x_462 = x_452;
} else {
 lean_dec_ref(x_452);
 x_462 = lean_box(0);
}
if (lean_is_scalar(x_462)) {
 x_463 = lean_alloc_ctor(1, 1, 0);
} else {
 x_463 = x_462;
}
lean_ctor_set(x_463, 0, x_461);
return x_463;
}
}
}
else
{
lean_object* x_464; lean_object* x_465; 
x_464 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__8;
x_465 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_464, x_426);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; uint8_t x_467; 
x_466 = lean_ctor_get(x_465, 0);
lean_inc(x_466);
lean_dec_ref(x_465);
x_467 = lean_unbox(x_466);
lean_dec(x_466);
if (x_467 == 0)
{
x_11 = x_431;
x_12 = x_420;
x_13 = x_421;
x_14 = x_422;
x_15 = x_423;
x_16 = x_424;
x_17 = x_425;
x_18 = x_426;
x_19 = x_427;
x_20 = lean_box(0);
goto block_28;
}
else
{
lean_object* x_468; 
lean_inc(x_431);
x_468 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_431, x_420, x_426);
if (lean_obj_tag(x_468) == 0)
{
lean_object* x_469; lean_object* x_470; 
x_469 = lean_ctor_get(x_468, 0);
lean_inc(x_469);
lean_dec_ref(x_468);
x_470 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_464, x_469, x_424, x_425, x_426, x_427);
if (lean_obj_tag(x_470) == 0)
{
lean_dec_ref(x_470);
x_11 = x_431;
x_12 = x_420;
x_13 = x_421;
x_14 = x_422;
x_15 = x_423;
x_16 = x_424;
x_17 = x_425;
x_18 = x_426;
x_19 = x_427;
x_20 = lean_box(0);
goto block_28;
}
else
{
lean_dec(x_431);
lean_dec(x_427);
lean_dec_ref(x_426);
lean_dec(x_425);
lean_dec_ref(x_424);
lean_dec(x_423);
lean_dec_ref(x_422);
lean_dec(x_421);
lean_dec(x_420);
return x_470;
}
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; 
lean_dec(x_431);
lean_dec(x_427);
lean_dec_ref(x_426);
lean_dec(x_425);
lean_dec_ref(x_424);
lean_dec(x_423);
lean_dec_ref(x_422);
lean_dec(x_421);
lean_dec(x_420);
x_471 = lean_ctor_get(x_468, 0);
lean_inc(x_471);
if (lean_is_exclusive(x_468)) {
 lean_ctor_release(x_468, 0);
 x_472 = x_468;
} else {
 lean_dec_ref(x_468);
 x_472 = lean_box(0);
}
if (lean_is_scalar(x_472)) {
 x_473 = lean_alloc_ctor(1, 1, 0);
} else {
 x_473 = x_472;
}
lean_ctor_set(x_473, 0, x_471);
return x_473;
}
}
}
else
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; 
lean_dec(x_431);
lean_dec(x_427);
lean_dec_ref(x_426);
lean_dec(x_425);
lean_dec_ref(x_424);
lean_dec(x_423);
lean_dec_ref(x_422);
lean_dec(x_421);
lean_dec(x_420);
x_474 = lean_ctor_get(x_465, 0);
lean_inc(x_474);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 x_475 = x_465;
} else {
 lean_dec_ref(x_465);
 x_475 = lean_box(0);
}
if (lean_is_scalar(x_475)) {
 x_476 = lean_alloc_ctor(1, 1, 0);
} else {
 x_476 = x_475;
}
lean_ctor_set(x_476, 0, x_474);
return x_476;
}
}
}
else
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; 
lean_dec(x_427);
lean_dec_ref(x_426);
lean_dec(x_425);
lean_dec_ref(x_424);
lean_dec(x_423);
lean_dec_ref(x_422);
lean_dec(x_421);
lean_dec(x_420);
x_477 = lean_ctor_get(x_430, 0);
lean_inc(x_477);
if (lean_is_exclusive(x_430)) {
 lean_ctor_release(x_430, 0);
 x_478 = x_430;
} else {
 lean_dec_ref(x_430);
 x_478 = lean_box(0);
}
if (lean_is_scalar(x_478)) {
 x_479 = lean_alloc_ctor(1, 1, 0);
} else {
 x_479 = x_478;
}
lean_ctor_set(x_479, 0, x_477);
return x_479;
}
}
}
else
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; 
lean_dec_ref(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_488 = lean_ctor_get(x_389, 0);
lean_inc(x_488);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 x_489 = x_389;
} else {
 lean_dec_ref(x_389);
 x_489 = lean_box(0);
}
if (lean_is_scalar(x_489)) {
 x_490 = lean_alloc_ctor(1, 1, 0);
} else {
 x_490 = x_489;
}
lean_ctor_set(x_490, 0, x_488);
return x_490;
}
block_387:
{
if (lean_obj_tag(x_337) == 1)
{
lean_object* x_338; lean_object* x_339; 
lean_dec_ref(x_332);
lean_dec_ref(x_326);
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
lean_dec_ref(x_337);
x_339 = lean_ctor_get(x_338, 1);
lean_inc_ref(x_339);
if (lean_obj_tag(x_339) == 1)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_340 = lean_ctor_get(x_338, 0);
x_341 = lean_ctor_get(x_339, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_339, 2);
lean_inc_ref(x_342);
if (lean_is_exclusive(x_339)) {
 lean_ctor_release(x_339, 0);
 lean_ctor_release(x_339, 1);
 lean_ctor_release(x_339, 2);
 x_343 = x_339;
} else {
 lean_dec_ref(x_339);
 x_343 = lean_box(0);
}
x_344 = lean_int_mul(x_331, x_340);
x_345 = lean_int_mul(x_341, x_325);
x_346 = l_Lean_Meta_Grind_Arith_gcdExt(x_344, x_345);
lean_dec(x_345);
lean_dec(x_344);
x_347 = lean_ctor_get(x_346, 1);
lean_inc(x_347);
x_348 = lean_ctor_get(x_346, 0);
lean_inc(x_348);
if (lean_is_exclusive(x_346)) {
 lean_ctor_release(x_346, 0);
 lean_ctor_release(x_346, 1);
 x_349 = x_346;
} else {
 lean_dec_ref(x_346);
 x_349 = lean_box(0);
}
x_350 = lean_ctor_get(x_347, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_347, 1);
lean_inc(x_351);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 x_352 = x_347;
} else {
 lean_dec_ref(x_347);
 x_352 = lean_box(0);
}
x_353 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0;
x_354 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_353, x_327, x_333);
if (lean_obj_tag(x_354) == 0)
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
lean_dec_ref(x_354);
x_355 = lean_int_mul(x_350, x_340);
lean_dec(x_350);
lean_inc_ref(x_328);
x_356 = l_Int_Linear_Poly_mul(x_328, x_355);
lean_dec(x_355);
x_357 = lean_int_mul(x_351, x_325);
lean_dec(x_351);
lean_inc_ref(x_342);
x_358 = l_Int_Linear_Poly_mul(x_342, x_357);
lean_dec(x_357);
x_359 = lean_int_mul(x_325, x_340);
lean_dec(x_325);
x_360 = l_Int_Linear_Poly_combine(x_356, x_358);
lean_inc(x_348);
if (lean_is_scalar(x_343)) {
 x_361 = lean_alloc_ctor(1, 3, 0);
} else {
 x_361 = x_343;
}
lean_ctor_set(x_361, 0, x_348);
lean_ctor_set(x_361, 1, x_322);
lean_ctor_set(x_361, 2, x_360);
lean_inc(x_338);
lean_inc_ref(x_323);
if (lean_is_scalar(x_352)) {
 x_362 = lean_alloc_ctor(4, 2, 0);
} else {
 x_362 = x_352;
 lean_ctor_set_tag(x_362, 4);
}
lean_ctor_set(x_362, 0, x_323);
lean_ctor_set(x_362, 1, x_338);
x_363 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_363, 0, x_359);
lean_ctor_set(x_363, 1, x_361);
lean_ctor_set(x_363, 2, x_362);
lean_inc(x_330);
lean_inc_ref(x_335);
lean_inc(x_320);
lean_inc_ref(x_336);
lean_inc(x_321);
lean_inc_ref(x_324);
lean_inc(x_329);
lean_inc(x_333);
x_364 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_363, x_333, x_329, x_324, x_321, x_336, x_320, x_335, x_330);
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
lean_dec_ref(x_364);
x_365 = l_Int_Linear_Poly_mul(x_328, x_341);
lean_dec(x_341);
x_366 = lean_int_neg(x_331);
lean_dec(x_331);
x_367 = l_Int_Linear_Poly_mul(x_342, x_366);
lean_dec(x_366);
x_368 = l_Int_Linear_Poly_combine(x_365, x_367);
lean_inc(x_338);
if (lean_is_scalar(x_349)) {
 x_369 = lean_alloc_ctor(5, 2, 0);
} else {
 x_369 = x_349;
 lean_ctor_set_tag(x_369, 5);
}
lean_ctor_set(x_369, 0, x_323);
lean_ctor_set(x_369, 1, x_338);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 lean_ctor_release(x_338, 1);
 lean_ctor_release(x_338, 2);
 x_370 = x_338;
} else {
 lean_dec_ref(x_338);
 x_370 = lean_box(0);
}
if (lean_is_scalar(x_370)) {
 x_371 = lean_alloc_ctor(0, 3, 0);
} else {
 x_371 = x_370;
}
lean_ctor_set(x_371, 0, x_348);
lean_ctor_set(x_371, 1, x_368);
lean_ctor_set(x_371, 2, x_369);
x_1 = x_371;
x_2 = x_333;
x_3 = x_329;
x_4 = x_324;
x_5 = x_321;
x_6 = x_336;
x_7 = x_320;
x_8 = x_335;
x_9 = x_330;
goto _start;
}
else
{
lean_dec(x_349);
lean_dec(x_348);
lean_dec_ref(x_342);
lean_dec(x_341);
lean_dec(x_338);
lean_dec_ref(x_336);
lean_dec_ref(x_335);
lean_dec(x_333);
lean_dec(x_331);
lean_dec(x_330);
lean_dec(x_329);
lean_dec_ref(x_328);
lean_dec_ref(x_324);
lean_dec_ref(x_323);
lean_dec(x_321);
lean_dec(x_320);
return x_364;
}
}
else
{
lean_dec(x_352);
lean_dec(x_351);
lean_dec(x_350);
lean_dec(x_349);
lean_dec(x_348);
lean_dec(x_343);
lean_dec_ref(x_342);
lean_dec(x_341);
lean_dec(x_338);
lean_dec_ref(x_336);
lean_dec_ref(x_335);
lean_dec(x_333);
lean_dec(x_331);
lean_dec(x_330);
lean_dec(x_329);
lean_dec_ref(x_328);
lean_dec(x_325);
lean_dec_ref(x_324);
lean_dec_ref(x_323);
lean_dec(x_322);
lean_dec(x_321);
lean_dec(x_320);
return x_354;
}
}
else
{
lean_object* x_373; 
lean_dec_ref(x_339);
lean_dec(x_331);
lean_dec_ref(x_328);
lean_dec_ref(x_327);
lean_dec(x_325);
lean_dec_ref(x_323);
lean_dec(x_322);
x_373 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_338, x_333, x_329, x_324, x_321, x_336, x_320, x_335, x_330);
lean_dec(x_330);
lean_dec_ref(x_335);
lean_dec(x_320);
lean_dec_ref(x_336);
lean_dec(x_321);
lean_dec_ref(x_324);
lean_dec(x_329);
lean_dec(x_333);
return x_373;
}
}
else
{
lean_object* x_374; lean_object* x_375; 
lean_dec(x_337);
lean_dec(x_331);
lean_dec(x_329);
lean_dec_ref(x_328);
lean_dec_ref(x_327);
lean_dec(x_325);
lean_dec_ref(x_324);
lean_dec(x_322);
lean_dec(x_321);
x_374 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3;
x_375 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_374, x_335);
if (lean_obj_tag(x_375) == 0)
{
lean_object* x_376; uint8_t x_377; 
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
lean_dec_ref(x_375);
x_377 = lean_unbox(x_376);
lean_dec(x_376);
if (x_377 == 0)
{
lean_dec_ref(x_323);
x_29 = x_326;
x_30 = x_332;
x_31 = x_333;
x_32 = x_336;
x_33 = x_320;
x_34 = x_335;
x_35 = x_330;
x_36 = lean_box(0);
goto block_40;
}
else
{
lean_object* x_378; 
x_378 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_323, x_333, x_335);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; lean_object* x_380; 
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
lean_dec_ref(x_378);
x_380 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_374, x_379, x_336, x_320, x_335, x_330);
if (lean_obj_tag(x_380) == 0)
{
lean_dec_ref(x_380);
x_29 = x_326;
x_30 = x_332;
x_31 = x_333;
x_32 = x_336;
x_33 = x_320;
x_34 = x_335;
x_35 = x_330;
x_36 = lean_box(0);
goto block_40;
}
else
{
lean_dec_ref(x_336);
lean_dec_ref(x_335);
lean_dec(x_333);
lean_dec_ref(x_332);
lean_dec(x_330);
lean_dec_ref(x_326);
lean_dec(x_320);
return x_380;
}
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; 
lean_dec_ref(x_336);
lean_dec_ref(x_335);
lean_dec(x_333);
lean_dec_ref(x_332);
lean_dec(x_330);
lean_dec_ref(x_326);
lean_dec(x_320);
x_381 = lean_ctor_get(x_378, 0);
lean_inc(x_381);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 x_382 = x_378;
} else {
 lean_dec_ref(x_378);
 x_382 = lean_box(0);
}
if (lean_is_scalar(x_382)) {
 x_383 = lean_alloc_ctor(1, 1, 0);
} else {
 x_383 = x_382;
}
lean_ctor_set(x_383, 0, x_381);
return x_383;
}
}
}
else
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; 
lean_dec_ref(x_336);
lean_dec_ref(x_335);
lean_dec(x_333);
lean_dec_ref(x_332);
lean_dec(x_330);
lean_dec_ref(x_326);
lean_dec_ref(x_323);
lean_dec(x_320);
x_384 = lean_ctor_get(x_375, 0);
lean_inc(x_384);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 x_385 = x_375;
} else {
 lean_dec_ref(x_375);
 x_385 = lean_box(0);
}
if (lean_is_scalar(x_385)) {
 x_386 = lean_alloc_ctor(1, 1, 0);
} else {
 x_386 = x_385;
}
lean_ctor_set(x_386, 0, x_384);
return x_386;
}
}
}
}
else
{
lean_object* x_491; lean_object* x_492; 
lean_dec_ref(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_491 = lean_box(0);
x_492 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_492, 0, x_491);
return x_492;
}
}
}
else
{
uint8_t x_493; 
lean_dec_ref(x_8);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_493 = !lean_is_exclusive(x_63);
if (x_493 == 0)
{
return x_63;
}
else
{
lean_object* x_494; lean_object* x_495; 
x_494 = lean_ctor_get(x_63, 0);
lean_inc(x_494);
lean_dec(x_63);
x_495 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_495, 0, x_494);
return x_495;
}
}
}
else
{
lean_object* x_496; 
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
x_496 = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(x_51);
return x_496;
}
}
else
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; uint8_t x_509; lean_object* x_510; uint8_t x_511; lean_object* x_512; uint8_t x_513; 
x_497 = lean_ctor_get(x_8, 0);
x_498 = lean_ctor_get(x_8, 1);
x_499 = lean_ctor_get(x_8, 2);
x_500 = lean_ctor_get(x_8, 3);
x_501 = lean_ctor_get(x_8, 4);
x_502 = lean_ctor_get(x_8, 5);
x_503 = lean_ctor_get(x_8, 6);
x_504 = lean_ctor_get(x_8, 7);
x_505 = lean_ctor_get(x_8, 8);
x_506 = lean_ctor_get(x_8, 9);
x_507 = lean_ctor_get(x_8, 10);
x_508 = lean_ctor_get(x_8, 11);
x_509 = lean_ctor_get_uint8(x_8, sizeof(void*)*14);
x_510 = lean_ctor_get(x_8, 12);
x_511 = lean_ctor_get_uint8(x_8, sizeof(void*)*14 + 1);
x_512 = lean_ctor_get(x_8, 13);
lean_inc(x_512);
lean_inc(x_510);
lean_inc(x_508);
lean_inc(x_507);
lean_inc(x_506);
lean_inc(x_505);
lean_inc(x_504);
lean_inc(x_503);
lean_inc(x_502);
lean_inc(x_501);
lean_inc(x_500);
lean_inc(x_499);
lean_inc(x_498);
lean_inc(x_497);
lean_dec(x_8);
x_513 = lean_nat_dec_eq(x_500, x_501);
if (x_513 == 0)
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; 
x_514 = lean_unsigned_to_nat(1u);
x_515 = lean_nat_add(x_500, x_514);
lean_dec(x_500);
x_516 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_516, 0, x_497);
lean_ctor_set(x_516, 1, x_498);
lean_ctor_set(x_516, 2, x_499);
lean_ctor_set(x_516, 3, x_515);
lean_ctor_set(x_516, 4, x_501);
lean_ctor_set(x_516, 5, x_502);
lean_ctor_set(x_516, 6, x_503);
lean_ctor_set(x_516, 7, x_504);
lean_ctor_set(x_516, 8, x_505);
lean_ctor_set(x_516, 9, x_506);
lean_ctor_set(x_516, 10, x_507);
lean_ctor_set(x_516, 11, x_508);
lean_ctor_set(x_516, 12, x_510);
lean_ctor_set(x_516, 13, x_512);
lean_ctor_set_uint8(x_516, sizeof(void*)*14, x_509);
lean_ctor_set_uint8(x_516, sizeof(void*)*14 + 1, x_511);
x_517 = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(x_2, x_516);
if (lean_obj_tag(x_517) == 0)
{
lean_object* x_518; lean_object* x_519; uint8_t x_520; 
x_518 = lean_ctor_get(x_517, 0);
lean_inc(x_518);
if (lean_is_exclusive(x_517)) {
 lean_ctor_release(x_517, 0);
 x_519 = x_517;
} else {
 lean_dec_ref(x_517);
 x_519 = lean_box(0);
}
x_520 = lean_unbox(x_518);
lean_dec(x_518);
if (x_520 == 0)
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_589; lean_object* x_590; 
lean_dec(x_519);
x_589 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4;
x_590 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_589, x_516);
if (lean_obj_tag(x_590) == 0)
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; uint8_t x_682; 
x_591 = lean_ctor_get(x_590, 0);
lean_inc(x_591);
lean_dec_ref(x_590);
x_592 = lean_box(0);
x_682 = lean_unbox(x_591);
lean_dec(x_591);
if (x_682 == 0)
{
x_621 = x_2;
x_622 = x_3;
x_623 = x_4;
x_624 = x_5;
x_625 = x_6;
x_626 = x_7;
x_627 = x_516;
x_628 = x_9;
x_629 = lean_box(0);
goto block_681;
}
else
{
lean_object* x_683; 
lean_inc_ref(x_1);
x_683 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_516);
if (lean_obj_tag(x_683) == 0)
{
lean_object* x_684; lean_object* x_685; 
x_684 = lean_ctor_get(x_683, 0);
lean_inc(x_684);
lean_dec_ref(x_683);
x_685 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_589, x_684, x_6, x_7, x_516, x_9);
if (lean_obj_tag(x_685) == 0)
{
lean_dec_ref(x_685);
x_621 = x_2;
x_622 = x_3;
x_623 = x_4;
x_624 = x_5;
x_625 = x_6;
x_626 = x_7;
x_627 = x_516;
x_628 = x_9;
x_629 = lean_box(0);
goto block_681;
}
else
{
lean_dec_ref(x_516);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_685;
}
}
else
{
lean_object* x_686; lean_object* x_687; lean_object* x_688; 
lean_dec_ref(x_516);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_686 = lean_ctor_get(x_683, 0);
lean_inc(x_686);
if (lean_is_exclusive(x_683)) {
 lean_ctor_release(x_683, 0);
 x_687 = x_683;
} else {
 lean_dec_ref(x_683);
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
block_620:
{
lean_object* x_610; 
x_610 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(x_601, x_607);
if (lean_obj_tag(x_610) == 0)
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; uint8_t x_614; 
x_611 = lean_ctor_get(x_610, 0);
lean_inc(x_611);
lean_dec_ref(x_610);
x_612 = lean_ctor_get(x_611, 6);
lean_inc_ref(x_612);
lean_dec(x_611);
x_613 = lean_ctor_get(x_612, 2);
x_614 = lean_nat_dec_lt(x_595, x_613);
if (x_614 == 0)
{
lean_object* x_615; 
lean_dec_ref(x_612);
x_615 = l_outOfBounds___redArg(x_592);
x_521 = x_606;
x_522 = x_604;
x_523 = x_595;
x_524 = x_594;
x_525 = x_603;
x_526 = x_596;
x_527 = x_598;
x_528 = x_600;
x_529 = x_593;
x_530 = x_602;
x_531 = x_608;
x_532 = x_597;
x_533 = x_599;
x_534 = x_601;
x_535 = lean_box(0);
x_536 = x_607;
x_537 = x_605;
x_538 = x_615;
goto block_588;
}
else
{
lean_object* x_616; 
x_616 = l_Lean_PersistentArray_get_x21___redArg(x_592, x_612, x_595);
x_521 = x_606;
x_522 = x_604;
x_523 = x_595;
x_524 = x_594;
x_525 = x_603;
x_526 = x_596;
x_527 = x_598;
x_528 = x_600;
x_529 = x_593;
x_530 = x_602;
x_531 = x_608;
x_532 = x_597;
x_533 = x_599;
x_534 = x_601;
x_535 = lean_box(0);
x_536 = x_607;
x_537 = x_605;
x_538 = x_616;
goto block_588;
}
}
else
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; 
lean_dec(x_608);
lean_dec_ref(x_607);
lean_dec(x_606);
lean_dec_ref(x_605);
lean_dec(x_604);
lean_dec_ref(x_603);
lean_dec(x_602);
lean_dec(x_601);
lean_dec_ref(x_600);
lean_dec_ref(x_599);
lean_dec_ref(x_598);
lean_dec(x_597);
lean_dec(x_596);
lean_dec(x_595);
lean_dec_ref(x_594);
lean_dec_ref(x_593);
x_617 = lean_ctor_get(x_610, 0);
lean_inc(x_617);
if (lean_is_exclusive(x_610)) {
 lean_ctor_release(x_610, 0);
 x_618 = x_610;
} else {
 lean_dec_ref(x_610);
 x_618 = lean_box(0);
}
if (lean_is_scalar(x_618)) {
 x_619 = lean_alloc_ctor(1, 1, 0);
} else {
 x_619 = x_618;
}
lean_ctor_set(x_619, 0, x_617);
return x_619;
}
}
block_681:
{
lean_object* x_630; lean_object* x_631; 
x_630 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc_ref(x_627);
x_631 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(x_630, x_621, x_622, x_623, x_624, x_625, x_626, x_627, x_628);
if (lean_obj_tag(x_631) == 0)
{
lean_object* x_632; lean_object* x_633; lean_object* x_634; uint8_t x_635; 
x_632 = lean_ctor_get(x_631, 0);
lean_inc(x_632);
lean_dec_ref(x_631);
x_633 = lean_ctor_get(x_632, 0);
x_634 = lean_ctor_get(x_632, 1);
lean_inc(x_633);
x_635 = l_Int_Linear_Poly_isUnsatDvd(x_633, x_634);
if (x_635 == 0)
{
uint8_t x_636; 
x_636 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_632);
if (x_636 == 0)
{
if (lean_obj_tag(x_634) == 1)
{
lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; 
lean_inc_ref(x_634);
lean_inc(x_633);
x_637 = lean_ctor_get(x_634, 0);
lean_inc(x_637);
x_638 = lean_ctor_get(x_634, 1);
lean_inc(x_638);
x_639 = lean_ctor_get(x_634, 2);
lean_inc_ref(x_639);
lean_inc(x_632);
x_640 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_632, x_621, x_627);
if (lean_obj_tag(x_640) == 0)
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; uint8_t x_644; uint8_t x_645; uint8_t x_646; 
x_641 = lean_ctor_get(x_640, 0);
lean_inc(x_641);
lean_dec_ref(x_640);
lean_inc(x_638);
x_642 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed), 2, 1);
lean_closure_set(x_642, 0, x_638);
lean_inc(x_638);
lean_inc(x_632);
x_643 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed), 3, 2);
lean_closure_set(x_643, 0, x_632);
lean_closure_set(x_643, 1, x_638);
x_644 = 0;
x_645 = lean_unbox(x_641);
lean_dec(x_641);
x_646 = l_Lean_instBEqLBool_beq(x_645, x_644);
if (x_646 == 0)
{
x_593 = x_639;
x_594 = x_632;
x_595 = x_638;
x_596 = x_633;
x_597 = x_637;
x_598 = x_643;
x_599 = x_634;
x_600 = x_642;
x_601 = x_621;
x_602 = x_622;
x_603 = x_623;
x_604 = x_624;
x_605 = x_625;
x_606 = x_626;
x_607 = x_627;
x_608 = x_628;
x_609 = lean_box(0);
goto block_620;
}
else
{
lean_object* x_647; 
lean_inc(x_638);
x_647 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_638, x_621);
if (lean_obj_tag(x_647) == 0)
{
lean_dec_ref(x_647);
x_593 = x_639;
x_594 = x_632;
x_595 = x_638;
x_596 = x_633;
x_597 = x_637;
x_598 = x_643;
x_599 = x_634;
x_600 = x_642;
x_601 = x_621;
x_602 = x_622;
x_603 = x_623;
x_604 = x_624;
x_605 = x_625;
x_606 = x_626;
x_607 = x_627;
x_608 = x_628;
x_609 = lean_box(0);
goto block_620;
}
else
{
lean_dec_ref(x_643);
lean_dec_ref(x_642);
lean_dec_ref(x_639);
lean_dec(x_638);
lean_dec(x_637);
lean_dec_ref(x_634);
lean_dec(x_633);
lean_dec(x_632);
lean_dec(x_628);
lean_dec_ref(x_627);
lean_dec(x_626);
lean_dec_ref(x_625);
lean_dec(x_624);
lean_dec_ref(x_623);
lean_dec(x_622);
lean_dec(x_621);
return x_647;
}
}
}
else
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; 
lean_dec_ref(x_639);
lean_dec(x_638);
lean_dec(x_637);
lean_dec_ref(x_634);
lean_dec(x_633);
lean_dec(x_632);
lean_dec(x_628);
lean_dec_ref(x_627);
lean_dec(x_626);
lean_dec_ref(x_625);
lean_dec(x_624);
lean_dec_ref(x_623);
lean_dec(x_622);
lean_dec(x_621);
x_648 = lean_ctor_get(x_640, 0);
lean_inc(x_648);
if (lean_is_exclusive(x_640)) {
 lean_ctor_release(x_640, 0);
 x_649 = x_640;
} else {
 lean_dec_ref(x_640);
 x_649 = lean_box(0);
}
if (lean_is_scalar(x_649)) {
 x_650 = lean_alloc_ctor(1, 1, 0);
} else {
 x_650 = x_649;
}
lean_ctor_set(x_650, 0, x_648);
return x_650;
}
}
else
{
lean_object* x_651; 
x_651 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_632, x_621, x_622, x_623, x_624, x_625, x_626, x_627, x_628);
lean_dec(x_628);
lean_dec_ref(x_627);
lean_dec(x_626);
lean_dec_ref(x_625);
lean_dec(x_624);
lean_dec_ref(x_623);
lean_dec(x_622);
lean_dec(x_621);
return x_651;
}
}
else
{
lean_object* x_652; lean_object* x_653; 
lean_dec(x_624);
lean_dec_ref(x_623);
lean_dec(x_622);
x_652 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__6;
x_653 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_652, x_627);
if (lean_obj_tag(x_653) == 0)
{
lean_object* x_654; uint8_t x_655; 
x_654 = lean_ctor_get(x_653, 0);
lean_inc(x_654);
lean_dec_ref(x_653);
x_655 = lean_unbox(x_654);
lean_dec(x_654);
if (x_655 == 0)
{
lean_dec(x_632);
lean_dec(x_628);
lean_dec_ref(x_627);
lean_dec(x_626);
lean_dec_ref(x_625);
lean_dec(x_621);
x_41 = lean_box(0);
goto block_44;
}
else
{
lean_object* x_656; 
x_656 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_632, x_621, x_627);
lean_dec(x_621);
if (lean_obj_tag(x_656) == 0)
{
lean_object* x_657; lean_object* x_658; 
x_657 = lean_ctor_get(x_656, 0);
lean_inc(x_657);
lean_dec_ref(x_656);
x_658 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_652, x_657, x_625, x_626, x_627, x_628);
lean_dec(x_628);
lean_dec_ref(x_627);
lean_dec(x_626);
lean_dec_ref(x_625);
if (lean_obj_tag(x_658) == 0)
{
lean_dec_ref(x_658);
x_41 = lean_box(0);
goto block_44;
}
else
{
return x_658;
}
}
else
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; 
lean_dec(x_628);
lean_dec_ref(x_627);
lean_dec(x_626);
lean_dec_ref(x_625);
x_659 = lean_ctor_get(x_656, 0);
lean_inc(x_659);
if (lean_is_exclusive(x_656)) {
 lean_ctor_release(x_656, 0);
 x_660 = x_656;
} else {
 lean_dec_ref(x_656);
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
}
else
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; 
lean_dec(x_632);
lean_dec(x_628);
lean_dec_ref(x_627);
lean_dec(x_626);
lean_dec_ref(x_625);
lean_dec(x_621);
x_662 = lean_ctor_get(x_653, 0);
lean_inc(x_662);
if (lean_is_exclusive(x_653)) {
 lean_ctor_release(x_653, 0);
 x_663 = x_653;
} else {
 lean_dec_ref(x_653);
 x_663 = lean_box(0);
}
if (lean_is_scalar(x_663)) {
 x_664 = lean_alloc_ctor(1, 1, 0);
} else {
 x_664 = x_663;
}
lean_ctor_set(x_664, 0, x_662);
return x_664;
}
}
}
else
{
lean_object* x_665; lean_object* x_666; 
x_665 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__8;
x_666 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_665, x_627);
if (lean_obj_tag(x_666) == 0)
{
lean_object* x_667; uint8_t x_668; 
x_667 = lean_ctor_get(x_666, 0);
lean_inc(x_667);
lean_dec_ref(x_666);
x_668 = lean_unbox(x_667);
lean_dec(x_667);
if (x_668 == 0)
{
x_11 = x_632;
x_12 = x_621;
x_13 = x_622;
x_14 = x_623;
x_15 = x_624;
x_16 = x_625;
x_17 = x_626;
x_18 = x_627;
x_19 = x_628;
x_20 = lean_box(0);
goto block_28;
}
else
{
lean_object* x_669; 
lean_inc(x_632);
x_669 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_632, x_621, x_627);
if (lean_obj_tag(x_669) == 0)
{
lean_object* x_670; lean_object* x_671; 
x_670 = lean_ctor_get(x_669, 0);
lean_inc(x_670);
lean_dec_ref(x_669);
x_671 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_665, x_670, x_625, x_626, x_627, x_628);
if (lean_obj_tag(x_671) == 0)
{
lean_dec_ref(x_671);
x_11 = x_632;
x_12 = x_621;
x_13 = x_622;
x_14 = x_623;
x_15 = x_624;
x_16 = x_625;
x_17 = x_626;
x_18 = x_627;
x_19 = x_628;
x_20 = lean_box(0);
goto block_28;
}
else
{
lean_dec(x_632);
lean_dec(x_628);
lean_dec_ref(x_627);
lean_dec(x_626);
lean_dec_ref(x_625);
lean_dec(x_624);
lean_dec_ref(x_623);
lean_dec(x_622);
lean_dec(x_621);
return x_671;
}
}
else
{
lean_object* x_672; lean_object* x_673; lean_object* x_674; 
lean_dec(x_632);
lean_dec(x_628);
lean_dec_ref(x_627);
lean_dec(x_626);
lean_dec_ref(x_625);
lean_dec(x_624);
lean_dec_ref(x_623);
lean_dec(x_622);
lean_dec(x_621);
x_672 = lean_ctor_get(x_669, 0);
lean_inc(x_672);
if (lean_is_exclusive(x_669)) {
 lean_ctor_release(x_669, 0);
 x_673 = x_669;
} else {
 lean_dec_ref(x_669);
 x_673 = lean_box(0);
}
if (lean_is_scalar(x_673)) {
 x_674 = lean_alloc_ctor(1, 1, 0);
} else {
 x_674 = x_673;
}
lean_ctor_set(x_674, 0, x_672);
return x_674;
}
}
}
else
{
lean_object* x_675; lean_object* x_676; lean_object* x_677; 
lean_dec(x_632);
lean_dec(x_628);
lean_dec_ref(x_627);
lean_dec(x_626);
lean_dec_ref(x_625);
lean_dec(x_624);
lean_dec_ref(x_623);
lean_dec(x_622);
lean_dec(x_621);
x_675 = lean_ctor_get(x_666, 0);
lean_inc(x_675);
if (lean_is_exclusive(x_666)) {
 lean_ctor_release(x_666, 0);
 x_676 = x_666;
} else {
 lean_dec_ref(x_666);
 x_676 = lean_box(0);
}
if (lean_is_scalar(x_676)) {
 x_677 = lean_alloc_ctor(1, 1, 0);
} else {
 x_677 = x_676;
}
lean_ctor_set(x_677, 0, x_675);
return x_677;
}
}
}
else
{
lean_object* x_678; lean_object* x_679; lean_object* x_680; 
lean_dec(x_628);
lean_dec_ref(x_627);
lean_dec(x_626);
lean_dec_ref(x_625);
lean_dec(x_624);
lean_dec_ref(x_623);
lean_dec(x_622);
lean_dec(x_621);
x_678 = lean_ctor_get(x_631, 0);
lean_inc(x_678);
if (lean_is_exclusive(x_631)) {
 lean_ctor_release(x_631, 0);
 x_679 = x_631;
} else {
 lean_dec_ref(x_631);
 x_679 = lean_box(0);
}
if (lean_is_scalar(x_679)) {
 x_680 = lean_alloc_ctor(1, 1, 0);
} else {
 x_680 = x_679;
}
lean_ctor_set(x_680, 0, x_678);
return x_680;
}
}
}
else
{
lean_object* x_689; lean_object* x_690; lean_object* x_691; 
lean_dec_ref(x_516);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_689 = lean_ctor_get(x_590, 0);
lean_inc(x_689);
if (lean_is_exclusive(x_590)) {
 lean_ctor_release(x_590, 0);
 x_690 = x_590;
} else {
 lean_dec_ref(x_590);
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
block_588:
{
if (lean_obj_tag(x_538) == 1)
{
lean_object* x_539; lean_object* x_540; 
lean_dec_ref(x_533);
lean_dec_ref(x_527);
x_539 = lean_ctor_get(x_538, 0);
lean_inc(x_539);
lean_dec_ref(x_538);
x_540 = lean_ctor_get(x_539, 1);
lean_inc_ref(x_540);
if (lean_obj_tag(x_540) == 1)
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; 
x_541 = lean_ctor_get(x_539, 0);
x_542 = lean_ctor_get(x_540, 0);
lean_inc(x_542);
x_543 = lean_ctor_get(x_540, 2);
lean_inc_ref(x_543);
if (lean_is_exclusive(x_540)) {
 lean_ctor_release(x_540, 0);
 lean_ctor_release(x_540, 1);
 lean_ctor_release(x_540, 2);
 x_544 = x_540;
} else {
 lean_dec_ref(x_540);
 x_544 = lean_box(0);
}
x_545 = lean_int_mul(x_532, x_541);
x_546 = lean_int_mul(x_542, x_526);
x_547 = l_Lean_Meta_Grind_Arith_gcdExt(x_545, x_546);
lean_dec(x_546);
lean_dec(x_545);
x_548 = lean_ctor_get(x_547, 1);
lean_inc(x_548);
x_549 = lean_ctor_get(x_547, 0);
lean_inc(x_549);
if (lean_is_exclusive(x_547)) {
 lean_ctor_release(x_547, 0);
 lean_ctor_release(x_547, 1);
 x_550 = x_547;
} else {
 lean_dec_ref(x_547);
 x_550 = lean_box(0);
}
x_551 = lean_ctor_get(x_548, 0);
lean_inc(x_551);
x_552 = lean_ctor_get(x_548, 1);
lean_inc(x_552);
if (lean_is_exclusive(x_548)) {
 lean_ctor_release(x_548, 0);
 lean_ctor_release(x_548, 1);
 x_553 = x_548;
} else {
 lean_dec_ref(x_548);
 x_553 = lean_box(0);
}
x_554 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0;
x_555 = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(x_554, x_528, x_534);
if (lean_obj_tag(x_555) == 0)
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; 
lean_dec_ref(x_555);
x_556 = lean_int_mul(x_551, x_541);
lean_dec(x_551);
lean_inc_ref(x_529);
x_557 = l_Int_Linear_Poly_mul(x_529, x_556);
lean_dec(x_556);
x_558 = lean_int_mul(x_552, x_526);
lean_dec(x_552);
lean_inc_ref(x_543);
x_559 = l_Int_Linear_Poly_mul(x_543, x_558);
lean_dec(x_558);
x_560 = lean_int_mul(x_526, x_541);
lean_dec(x_526);
x_561 = l_Int_Linear_Poly_combine(x_557, x_559);
lean_inc(x_549);
if (lean_is_scalar(x_544)) {
 x_562 = lean_alloc_ctor(1, 3, 0);
} else {
 x_562 = x_544;
}
lean_ctor_set(x_562, 0, x_549);
lean_ctor_set(x_562, 1, x_523);
lean_ctor_set(x_562, 2, x_561);
lean_inc(x_539);
lean_inc_ref(x_524);
if (lean_is_scalar(x_553)) {
 x_563 = lean_alloc_ctor(4, 2, 0);
} else {
 x_563 = x_553;
 lean_ctor_set_tag(x_563, 4);
}
lean_ctor_set(x_563, 0, x_524);
lean_ctor_set(x_563, 1, x_539);
x_564 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_564, 0, x_560);
lean_ctor_set(x_564, 1, x_562);
lean_ctor_set(x_564, 2, x_563);
lean_inc(x_531);
lean_inc_ref(x_536);
lean_inc(x_521);
lean_inc_ref(x_537);
lean_inc(x_522);
lean_inc_ref(x_525);
lean_inc(x_530);
lean_inc(x_534);
x_565 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_564, x_534, x_530, x_525, x_522, x_537, x_521, x_536, x_531);
if (lean_obj_tag(x_565) == 0)
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; 
lean_dec_ref(x_565);
x_566 = l_Int_Linear_Poly_mul(x_529, x_542);
lean_dec(x_542);
x_567 = lean_int_neg(x_532);
lean_dec(x_532);
x_568 = l_Int_Linear_Poly_mul(x_543, x_567);
lean_dec(x_567);
x_569 = l_Int_Linear_Poly_combine(x_566, x_568);
lean_inc(x_539);
if (lean_is_scalar(x_550)) {
 x_570 = lean_alloc_ctor(5, 2, 0);
} else {
 x_570 = x_550;
 lean_ctor_set_tag(x_570, 5);
}
lean_ctor_set(x_570, 0, x_524);
lean_ctor_set(x_570, 1, x_539);
if (lean_is_exclusive(x_539)) {
 lean_ctor_release(x_539, 0);
 lean_ctor_release(x_539, 1);
 lean_ctor_release(x_539, 2);
 x_571 = x_539;
} else {
 lean_dec_ref(x_539);
 x_571 = lean_box(0);
}
if (lean_is_scalar(x_571)) {
 x_572 = lean_alloc_ctor(0, 3, 0);
} else {
 x_572 = x_571;
}
lean_ctor_set(x_572, 0, x_549);
lean_ctor_set(x_572, 1, x_569);
lean_ctor_set(x_572, 2, x_570);
x_1 = x_572;
x_2 = x_534;
x_3 = x_530;
x_4 = x_525;
x_5 = x_522;
x_6 = x_537;
x_7 = x_521;
x_8 = x_536;
x_9 = x_531;
goto _start;
}
else
{
lean_dec(x_550);
lean_dec(x_549);
lean_dec_ref(x_543);
lean_dec(x_542);
lean_dec(x_539);
lean_dec_ref(x_537);
lean_dec_ref(x_536);
lean_dec(x_534);
lean_dec(x_532);
lean_dec(x_531);
lean_dec(x_530);
lean_dec_ref(x_529);
lean_dec_ref(x_525);
lean_dec_ref(x_524);
lean_dec(x_522);
lean_dec(x_521);
return x_565;
}
}
else
{
lean_dec(x_553);
lean_dec(x_552);
lean_dec(x_551);
lean_dec(x_550);
lean_dec(x_549);
lean_dec(x_544);
lean_dec_ref(x_543);
lean_dec(x_542);
lean_dec(x_539);
lean_dec_ref(x_537);
lean_dec_ref(x_536);
lean_dec(x_534);
lean_dec(x_532);
lean_dec(x_531);
lean_dec(x_530);
lean_dec_ref(x_529);
lean_dec(x_526);
lean_dec_ref(x_525);
lean_dec_ref(x_524);
lean_dec(x_523);
lean_dec(x_522);
lean_dec(x_521);
return x_555;
}
}
else
{
lean_object* x_574; 
lean_dec_ref(x_540);
lean_dec(x_532);
lean_dec_ref(x_529);
lean_dec_ref(x_528);
lean_dec(x_526);
lean_dec_ref(x_524);
lean_dec(x_523);
x_574 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(x_539, x_534, x_530, x_525, x_522, x_537, x_521, x_536, x_531);
lean_dec(x_531);
lean_dec_ref(x_536);
lean_dec(x_521);
lean_dec_ref(x_537);
lean_dec(x_522);
lean_dec_ref(x_525);
lean_dec(x_530);
lean_dec(x_534);
return x_574;
}
}
else
{
lean_object* x_575; lean_object* x_576; 
lean_dec(x_538);
lean_dec(x_532);
lean_dec(x_530);
lean_dec_ref(x_529);
lean_dec_ref(x_528);
lean_dec(x_526);
lean_dec_ref(x_525);
lean_dec(x_523);
lean_dec(x_522);
x_575 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3;
x_576 = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(x_575, x_536);
if (lean_obj_tag(x_576) == 0)
{
lean_object* x_577; uint8_t x_578; 
x_577 = lean_ctor_get(x_576, 0);
lean_inc(x_577);
lean_dec_ref(x_576);
x_578 = lean_unbox(x_577);
lean_dec(x_577);
if (x_578 == 0)
{
lean_dec_ref(x_524);
x_29 = x_527;
x_30 = x_533;
x_31 = x_534;
x_32 = x_537;
x_33 = x_521;
x_34 = x_536;
x_35 = x_531;
x_36 = lean_box(0);
goto block_40;
}
else
{
lean_object* x_579; 
x_579 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_524, x_534, x_536);
if (lean_obj_tag(x_579) == 0)
{
lean_object* x_580; lean_object* x_581; 
x_580 = lean_ctor_get(x_579, 0);
lean_inc(x_580);
lean_dec_ref(x_579);
x_581 = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(x_575, x_580, x_537, x_521, x_536, x_531);
if (lean_obj_tag(x_581) == 0)
{
lean_dec_ref(x_581);
x_29 = x_527;
x_30 = x_533;
x_31 = x_534;
x_32 = x_537;
x_33 = x_521;
x_34 = x_536;
x_35 = x_531;
x_36 = lean_box(0);
goto block_40;
}
else
{
lean_dec_ref(x_537);
lean_dec_ref(x_536);
lean_dec(x_534);
lean_dec_ref(x_533);
lean_dec(x_531);
lean_dec_ref(x_527);
lean_dec(x_521);
return x_581;
}
}
else
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; 
lean_dec_ref(x_537);
lean_dec_ref(x_536);
lean_dec(x_534);
lean_dec_ref(x_533);
lean_dec(x_531);
lean_dec_ref(x_527);
lean_dec(x_521);
x_582 = lean_ctor_get(x_579, 0);
lean_inc(x_582);
if (lean_is_exclusive(x_579)) {
 lean_ctor_release(x_579, 0);
 x_583 = x_579;
} else {
 lean_dec_ref(x_579);
 x_583 = lean_box(0);
}
if (lean_is_scalar(x_583)) {
 x_584 = lean_alloc_ctor(1, 1, 0);
} else {
 x_584 = x_583;
}
lean_ctor_set(x_584, 0, x_582);
return x_584;
}
}
}
else
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; 
lean_dec_ref(x_537);
lean_dec_ref(x_536);
lean_dec(x_534);
lean_dec_ref(x_533);
lean_dec(x_531);
lean_dec_ref(x_527);
lean_dec_ref(x_524);
lean_dec(x_521);
x_585 = lean_ctor_get(x_576, 0);
lean_inc(x_585);
if (lean_is_exclusive(x_576)) {
 lean_ctor_release(x_576, 0);
 x_586 = x_576;
} else {
 lean_dec_ref(x_576);
 x_586 = lean_box(0);
}
if (lean_is_scalar(x_586)) {
 x_587 = lean_alloc_ctor(1, 1, 0);
} else {
 x_587 = x_586;
}
lean_ctor_set(x_587, 0, x_585);
return x_587;
}
}
}
}
else
{
lean_object* x_692; lean_object* x_693; 
lean_dec_ref(x_516);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_692 = lean_box(0);
if (lean_is_scalar(x_519)) {
 x_693 = lean_alloc_ctor(0, 1, 0);
} else {
 x_693 = x_519;
}
lean_ctor_set(x_693, 0, x_692);
return x_693;
}
}
else
{
lean_object* x_694; lean_object* x_695; lean_object* x_696; 
lean_dec_ref(x_516);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_694 = lean_ctor_get(x_517, 0);
lean_inc(x_694);
if (lean_is_exclusive(x_517)) {
 lean_ctor_release(x_517, 0);
 x_695 = x_517;
} else {
 lean_dec_ref(x_517);
 x_695 = lean_box(0);
}
if (lean_is_scalar(x_695)) {
 x_696 = lean_alloc_ctor(1, 1, 0);
} else {
 x_696 = x_695;
}
lean_ctor_set(x_696, 0, x_694);
return x_696;
}
}
else
{
lean_object* x_697; 
lean_dec_ref(x_512);
lean_dec(x_510);
lean_dec(x_508);
lean_dec(x_507);
lean_dec(x_506);
lean_dec(x_505);
lean_dec(x_504);
lean_dec(x_503);
lean_dec(x_501);
lean_dec(x_500);
lean_dec(x_499);
lean_dec_ref(x_498);
lean_dec_ref(x_497);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_697 = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(x_502);
return x_697;
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
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_inc(x_11);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(12, 3, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set(x_20, 2, x_18);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_20);
x_22 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_22;
}
else
{
lean_object* x_23; 
lean_dec(x_14);
x_23 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
x_1 = l_Lean_eagerReflBoolTrue;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("non-linear divisibility constraint found", 40, 40);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
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
if (lean_obj_tag(x_40) == 1)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_1);
x_43 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_4, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = lean_unbox(x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_free_object(x_40);
lean_dec(x_42);
x_46 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_46);
lean_dec_ref(x_21);
lean_inc_ref(x_1);
x_47 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_4, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_unbox(x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec_ref(x_46);
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
x_51 = lean_box(0);
lean_ctor_set(x_47, 0, x_51);
return x_47;
}
else
{
lean_object* x_52; 
lean_free_object(x_47);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_52 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
x_54 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7;
x_55 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8;
x_56 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_53);
x_57 = l_Lean_mkApp4(x_54, x_38, x_46, x_55, x_56);
x_58 = lean_unsigned_to_nat(0u);
x_59 = l_Lean_Meta_Grind_pushNewFact(x_57, x_58, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_59;
}
else
{
uint8_t x_60; 
lean_dec_ref(x_46);
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
x_60 = !lean_is_exclusive(x_52);
if (x_60 == 0)
{
return x_52;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_52, 0);
lean_inc(x_61);
lean_dec(x_52);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
}
}
}
else
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_47, 0);
lean_inc(x_63);
lean_dec(x_47);
x_64 = lean_unbox(x_63);
lean_dec(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec_ref(x_46);
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
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
else
{
lean_object* x_67; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_67 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec_ref(x_67);
x_69 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7;
x_70 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8;
x_71 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_68);
x_72 = l_Lean_mkApp4(x_69, x_38, x_46, x_70, x_71);
x_73 = lean_unsigned_to_nat(0u);
x_74 = l_Lean_Meta_Grind_pushNewFact(x_72, x_73, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec_ref(x_46);
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
x_75 = lean_ctor_get(x_67, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 x_76 = x_67;
} else {
 lean_dec_ref(x_67);
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
}
}
else
{
uint8_t x_78; 
lean_dec_ref(x_46);
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
x_78 = !lean_is_exclusive(x_47);
if (x_78 == 0)
{
return x_47;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_47, 0);
lean_inc(x_79);
lean_dec(x_47);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; 
lean_dec_ref(x_38);
x_81 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_81);
lean_dec_ref(x_21);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_82 = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(x_81, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
lean_dec_ref(x_82);
lean_ctor_set_tag(x_40, 0);
lean_ctor_set(x_40, 0, x_1);
x_84 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_84, 0, x_42);
lean_ctor_set(x_84, 1, x_83);
lean_ctor_set(x_84, 2, x_40);
x_85 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(x_84, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_85;
}
else
{
uint8_t x_86; 
lean_free_object(x_40);
lean_dec(x_42);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
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
lean_free_object(x_40);
lean_dec(x_42);
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
x_89 = !lean_is_exclusive(x_43);
if (x_89 == 0)
{
return x_43;
}
else
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_43, 0);
lean_inc(x_90);
lean_dec(x_43);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
}
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_40, 0);
lean_inc(x_92);
lean_dec(x_40);
lean_inc_ref(x_1);
x_93 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_4, x_6, x_7, x_8, x_9);
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
lean_object* x_96; lean_object* x_97; 
lean_dec(x_92);
x_96 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_96);
lean_dec_ref(x_21);
lean_inc_ref(x_1);
x_97 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_4, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 x_99 = x_97;
} else {
 lean_dec_ref(x_97);
 x_99 = lean_box(0);
}
x_100 = lean_unbox(x_98);
lean_dec(x_98);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
lean_dec_ref(x_96);
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
x_101 = lean_box(0);
if (lean_is_scalar(x_99)) {
 x_102 = lean_alloc_ctor(0, 1, 0);
} else {
 x_102 = x_99;
}
lean_ctor_set(x_102, 0, x_101);
return x_102;
}
else
{
lean_object* x_103; 
lean_dec(x_99);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_103 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
lean_dec_ref(x_103);
x_105 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7;
x_106 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8;
x_107 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_104);
x_108 = l_Lean_mkApp4(x_105, x_38, x_96, x_106, x_107);
x_109 = lean_unsigned_to_nat(0u);
x_110 = l_Lean_Meta_Grind_pushNewFact(x_108, x_109, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec_ref(x_96);
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
x_111 = lean_ctor_get(x_103, 0);
lean_inc(x_111);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 x_112 = x_103;
} else {
 lean_dec_ref(x_103);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 1, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_111);
return x_113;
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec_ref(x_96);
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
x_114 = lean_ctor_get(x_97, 0);
lean_inc(x_114);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 x_115 = x_97;
} else {
 lean_dec_ref(x_97);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 1, 0);
} else {
 x_116 = x_115;
}
lean_ctor_set(x_116, 0, x_114);
return x_116;
}
}
else
{
lean_object* x_117; lean_object* x_118; 
lean_dec_ref(x_38);
x_117 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_117);
lean_dec_ref(x_21);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_118 = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(x_117, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
lean_dec_ref(x_118);
x_120 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_120, 0, x_1);
x_121 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_121, 0, x_92);
lean_ctor_set(x_121, 1, x_119);
lean_ctor_set(x_121, 2, x_120);
x_122 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(x_121, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_92);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_123 = lean_ctor_get(x_118, 0);
lean_inc(x_123);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 x_124 = x_118;
} else {
 lean_dec_ref(x_118);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(1, 1, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_123);
return x_125;
}
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_92);
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
x_126 = lean_ctor_get(x_93, 0);
lean_inc(x_126);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 x_127 = x_93;
} else {
 lean_dec_ref(x_93);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(1, 1, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_126);
return x_128;
}
}
}
else
{
lean_object* x_129; 
lean_dec(x_40);
lean_dec_ref(x_38);
lean_dec_ref(x_21);
lean_dec(x_2);
x_129 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; uint8_t x_131; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
lean_dec_ref(x_129);
x_131 = lean_ctor_get_uint8(x_130, sizeof(void*)*10 + 13);
lean_dec(x_130);
if (x_131 == 0)
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
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_132 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10;
x_133 = l_Lean_indentExpr(x_1);
x_134 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
x_135 = l_Lean_Meta_Grind_reportIssue(x_134, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_135) == 0)
{
lean_dec_ref(x_135);
x_11 = lean_box(0);
goto block_14;
}
else
{
return x_135;
}
}
}
else
{
uint8_t x_136; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_136 = !lean_is_exclusive(x_129);
if (x_136 == 0)
{
return x_129;
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_ctor_get(x_129, 0);
lean_inc(x_137);
lean_dec(x_129);
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_137);
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
if (lean_obj_tag(x_148) == 1)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 x_150 = x_148;
} else {
 lean_dec_ref(x_148);
 x_150 = lean_box(0);
}
lean_inc_ref(x_1);
x_151 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_4, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; uint8_t x_153; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
lean_dec_ref(x_151);
x_153 = lean_unbox(x_152);
lean_dec(x_152);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_150);
lean_dec(x_149);
x_154 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_154);
lean_dec_ref(x_21);
lean_inc_ref(x_1);
x_155 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_4, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 x_157 = x_155;
} else {
 lean_dec_ref(x_155);
 x_157 = lean_box(0);
}
x_158 = lean_unbox(x_156);
lean_dec(x_156);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; 
lean_dec_ref(x_154);
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
x_159 = lean_box(0);
if (lean_is_scalar(x_157)) {
 x_160 = lean_alloc_ctor(0, 1, 0);
} else {
 x_160 = x_157;
}
lean_ctor_set(x_160, 0, x_159);
return x_160;
}
else
{
lean_object* x_161; 
lean_dec(x_157);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_161 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
lean_dec_ref(x_161);
x_163 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7;
x_164 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8;
x_165 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_162);
x_166 = l_Lean_mkApp4(x_163, x_146, x_154, x_164, x_165);
x_167 = lean_unsigned_to_nat(0u);
x_168 = l_Lean_Meta_Grind_pushNewFact(x_166, x_167, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_168;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec_ref(x_154);
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
x_169 = lean_ctor_get(x_161, 0);
lean_inc(x_169);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 x_170 = x_161;
} else {
 lean_dec_ref(x_161);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 1, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_169);
return x_171;
}
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec_ref(x_154);
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
x_172 = lean_ctor_get(x_155, 0);
lean_inc(x_172);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 x_173 = x_155;
} else {
 lean_dec_ref(x_155);
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
lean_object* x_175; lean_object* x_176; 
lean_dec_ref(x_146);
x_175 = lean_ctor_get(x_21, 1);
lean_inc_ref(x_175);
lean_dec_ref(x_21);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_176 = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(x_175, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
lean_dec_ref(x_176);
if (lean_is_scalar(x_150)) {
 x_178 = lean_alloc_ctor(0, 1, 0);
} else {
 x_178 = x_150;
 lean_ctor_set_tag(x_178, 0);
}
lean_ctor_set(x_178, 0, x_1);
x_179 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_179, 0, x_149);
lean_ctor_set(x_179, 1, x_177);
lean_ctor_set(x_179, 2, x_178);
x_180 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(x_179, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_180;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_181 = lean_ctor_get(x_176, 0);
lean_inc(x_181);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 x_182 = x_176;
} else {
 lean_dec_ref(x_176);
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
lean_dec(x_150);
lean_dec(x_149);
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
x_184 = lean_ctor_get(x_151, 0);
lean_inc(x_184);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 x_185 = x_151;
} else {
 lean_dec_ref(x_151);
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
lean_dec(x_148);
lean_dec_ref(x_146);
lean_dec_ref(x_21);
lean_dec(x_2);
x_187 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; uint8_t x_189; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
lean_dec_ref(x_187);
x_189 = lean_ctor_get_uint8(x_188, sizeof(void*)*10 + 13);
lean_dec(x_188);
if (x_189 == 0)
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
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_190 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10;
x_191 = l_Lean_indentExpr(x_1);
x_192 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
x_193 = l_Lean_Meta_Grind_reportIssue(x_192, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_193) == 0)
{
lean_dec_ref(x_193);
x_11 = lean_box(0);
goto block_14;
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
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
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
if (lean_obj_tag(x_38) == 1)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
lean_inc_ref(x_1);
x_40 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_4, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec_ref(x_40);
x_42 = lean_unbox(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_39);
x_43 = lean_ctor_get(x_19, 1);
lean_inc_ref(x_43);
lean_dec_ref(x_19);
lean_inc_ref(x_1);
x_44 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_4, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_unbox(x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; 
lean_dec_ref(x_43);
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
x_48 = lean_box(0);
lean_ctor_set(x_44, 0, x_48);
return x_44;
}
else
{
lean_object* x_49; 
lean_free_object(x_44);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_49 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec_ref(x_49);
x_51 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3;
x_52 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_50);
x_53 = l_Lean_mkApp3(x_51, x_36, x_43, x_52);
x_54 = lean_unsigned_to_nat(0u);
x_55 = l_Lean_Meta_Grind_pushNewFact(x_53, x_54, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_55;
}
else
{
uint8_t x_56; 
lean_dec_ref(x_43);
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
x_56 = !lean_is_exclusive(x_49);
if (x_56 == 0)
{
return x_49;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_49, 0);
lean_inc(x_57);
lean_dec(x_49);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
}
}
}
else
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_44, 0);
lean_inc(x_59);
lean_dec(x_44);
x_60 = lean_unbox(x_59);
lean_dec(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
lean_dec_ref(x_43);
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
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_61);
return x_62;
}
else
{
lean_object* x_63; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_63 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec_ref(x_63);
x_65 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3;
x_66 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_64);
x_67 = l_Lean_mkApp3(x_65, x_36, x_43, x_66);
x_68 = lean_unsigned_to_nat(0u);
x_69 = l_Lean_Meta_Grind_pushNewFact(x_67, x_68, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec_ref(x_43);
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
x_70 = lean_ctor_get(x_63, 0);
lean_inc(x_70);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 x_71 = x_63;
} else {
 lean_dec_ref(x_63);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 1, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_70);
return x_72;
}
}
}
}
else
{
uint8_t x_73; 
lean_dec_ref(x_43);
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
x_73 = !lean_is_exclusive(x_44);
if (x_73 == 0)
{
return x_44;
}
else
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_44, 0);
lean_inc(x_74);
lean_dec(x_44);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_74);
return x_75;
}
}
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_19, 1);
lean_inc_ref(x_76);
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
x_77 = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(x_36, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_76);
x_81 = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(x_76, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_83);
x_87 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_83, x_86, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
lean_dec_ref(x_87);
x_89 = l_Int_Linear_Expr_norm(x_88);
x_90 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7;
x_91 = l_Lean_mkApp6(x_90, x_36, x_76, x_79, x_83, x_80, x_84);
lean_inc(x_39);
x_92 = lean_nat_to_int(x_39);
x_93 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_93, 0, x_1);
lean_ctor_set(x_93, 1, x_91);
lean_ctor_set(x_93, 2, x_39);
lean_ctor_set(x_93, 3, x_88);
x_94 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_89);
lean_ctor_set(x_94, 2, x_93);
x_95 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(x_94, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_95;
}
else
{
uint8_t x_96; 
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_80);
lean_dec(x_79);
lean_dec_ref(x_76);
lean_dec(x_39);
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
lean_dec_ref(x_76);
lean_dec(x_39);
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
lean_dec_ref(x_76);
lean_dec(x_39);
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
lean_dec_ref(x_76);
lean_dec(x_39);
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
lean_dec(x_39);
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
x_108 = !lean_is_exclusive(x_40);
if (x_108 == 0)
{
return x_40;
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_40, 0);
lean_inc(x_109);
lean_dec(x_40);
x_110 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_110, 0, x_109);
return x_110;
}
}
}
else
{
lean_object* x_111; 
lean_dec(x_38);
lean_dec_ref(x_36);
lean_dec_ref(x_19);
lean_dec(x_2);
x_111 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; uint8_t x_113; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
lean_dec_ref(x_111);
x_113 = lean_ctor_get_uint8(x_112, sizeof(void*)*10 + 13);
lean_dec(x_112);
if (x_113 == 0)
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
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10;
x_115 = l_Lean_indentExpr(x_1);
x_116 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = l_Lean_Meta_Grind_reportIssue(x_116, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_117) == 0)
{
lean_dec_ref(x_117);
x_15 = lean_box(0);
goto block_18;
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
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
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
if (lean_obj_tag(x_130) == 1)
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
lean_dec_ref(x_130);
lean_inc_ref(x_1);
x_132 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_4, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; uint8_t x_134; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
lean_dec_ref(x_132);
x_134 = lean_unbox(x_133);
lean_dec(x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_131);
x_135 = lean_ctor_get(x_19, 1);
lean_inc_ref(x_135);
lean_dec_ref(x_19);
lean_inc_ref(x_1);
x_136 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_4, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 x_138 = x_136;
} else {
 lean_dec_ref(x_136);
 x_138 = lean_box(0);
}
x_139 = lean_unbox(x_137);
lean_dec(x_137);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; 
lean_dec_ref(x_135);
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
x_140 = lean_box(0);
if (lean_is_scalar(x_138)) {
 x_141 = lean_alloc_ctor(0, 1, 0);
} else {
 x_141 = x_138;
}
lean_ctor_set(x_141, 0, x_140);
return x_141;
}
else
{
lean_object* x_142; 
lean_dec(x_138);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_142 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
lean_dec_ref(x_142);
x_144 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3;
x_145 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_143);
x_146 = l_Lean_mkApp3(x_144, x_128, x_135, x_145);
x_147 = lean_unsigned_to_nat(0u);
x_148 = l_Lean_Meta_Grind_pushNewFact(x_146, x_147, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_148;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec_ref(x_135);
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
x_149 = lean_ctor_get(x_142, 0);
lean_inc(x_149);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 x_150 = x_142;
} else {
 lean_dec_ref(x_142);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 1, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_149);
return x_151;
}
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec_ref(x_135);
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
x_152 = lean_ctor_get(x_136, 0);
lean_inc(x_152);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 x_153 = x_136;
} else {
 lean_dec_ref(x_136);
 x_153 = lean_box(0);
}
if (lean_is_scalar(x_153)) {
 x_154 = lean_alloc_ctor(1, 1, 0);
} else {
 x_154 = x_153;
}
lean_ctor_set(x_154, 0, x_152);
return x_154;
}
}
else
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_19, 1);
lean_inc_ref(x_155);
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
x_156 = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(x_128, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
lean_dec_ref(x_156);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_155);
x_160 = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(x_155, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
lean_dec_ref(x_160);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_164 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
lean_dec_ref(x_164);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_162);
x_166 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_162, x_165, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
lean_dec_ref(x_166);
x_168 = l_Int_Linear_Expr_norm(x_167);
x_169 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7;
x_170 = l_Lean_mkApp6(x_169, x_128, x_155, x_158, x_162, x_159, x_163);
lean_inc(x_131);
x_171 = lean_nat_to_int(x_131);
x_172 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_172, 0, x_1);
lean_ctor_set(x_172, 1, x_170);
lean_ctor_set(x_172, 2, x_131);
lean_ctor_set(x_172, 3, x_167);
x_173 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_168);
lean_ctor_set(x_173, 2, x_172);
x_174 = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(x_173, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_174;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_159);
lean_dec(x_158);
lean_dec_ref(x_155);
lean_dec(x_131);
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
x_175 = lean_ctor_get(x_166, 0);
lean_inc(x_175);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 x_176 = x_166;
} else {
 lean_dec_ref(x_166);
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
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_159);
lean_dec(x_158);
lean_dec_ref(x_155);
lean_dec(x_131);
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
x_178 = lean_ctor_get(x_164, 0);
lean_inc(x_178);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 x_179 = x_164;
} else {
 lean_dec_ref(x_164);
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
lean_dec(x_159);
lean_dec(x_158);
lean_dec_ref(x_155);
lean_dec(x_131);
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
x_181 = lean_ctor_get(x_160, 0);
lean_inc(x_181);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 x_182 = x_160;
} else {
 lean_dec_ref(x_160);
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
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec_ref(x_155);
lean_dec(x_131);
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
x_184 = lean_ctor_get(x_156, 0);
lean_inc(x_184);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 x_185 = x_156;
} else {
 lean_dec_ref(x_156);
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
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_131);
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
x_187 = lean_ctor_get(x_132, 0);
lean_inc(x_187);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 x_188 = x_132;
} else {
 lean_dec_ref(x_132);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(1, 1, 0);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_187);
return x_189;
}
}
else
{
lean_object* x_190; 
lean_dec(x_130);
lean_dec_ref(x_128);
lean_dec_ref(x_19);
lean_dec(x_2);
x_190 = l_Lean_Meta_Grind_getConfig___redArg(x_4);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; uint8_t x_192; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
lean_dec_ref(x_190);
x_192 = lean_ctor_get_uint8(x_191, sizeof(void*)*10 + 13);
lean_dec(x_191);
if (x_192 == 0)
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
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_193 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10;
x_194 = l_Lean_indentExpr(x_1);
x_195 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
x_196 = l_Lean_Meta_Grind_reportIssue(x_195, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_196) == 0)
{
lean_dec_ref(x_196);
x_15 = lean_box(0);
goto block_18;
}
else
{
return x_196;
}
}
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_197 = lean_ctor_get(x_190, 0);
lean_inc(x_197);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 x_198 = x_190;
} else {
 lean_dec_ref(x_190);
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
x_14 = lean_ctor_get_uint8(x_13, sizeof(void*)*10 + 21);
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
x_42 = lean_ctor_get_uint8(x_41, sizeof(void*)*10 + 21);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2;
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed), 10, 0);
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
l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3 = _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3);
l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4 = _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4);
l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5 = _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5);
l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__1 = _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__1();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__1);
l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__0 = _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__0();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__0);
l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2 = _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2();
lean_mark_persistent(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2);
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
if (builtin) {res = l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
