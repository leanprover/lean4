// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.DvdCnstr
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Types import Init.Data.Int.OfNat import Init.Grind.Propagator import Lean.Meta.Tactic.Grind.Simp import Lean.Meta.Tactic.Grind.Arith.Cutsat.Var import Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat import Lean.Meta.Tactic.Grind.Arith.Cutsat.Proof import Lean.Meta.Tactic.Grind.Arith.Cutsat.Norm import Lean.Meta.Tactic.Grind.Arith.Cutsat.CommRing import Lean.Meta.NatInstTesters public import Lean.Meta.Tactic.Grind.PropagatorAttr import Init.Data.Nat.Dvd
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_Structural_isInstDvdInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_eagerReflBoolTrue;
lean_object* l_Lean_Meta_mkOfEqFalseCore(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushNewFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_normCommRing_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_updateOccs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_gcdExt(lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_mul(lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_combine(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_div(lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_getConst(lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Int_Linear_Poly_gcdCoeffs(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
uint8_t l_Int_Linear_Poly_isSorted(lean_object*);
lean_object* l_Int_Linear_Poly_norm(lean_object*);
lean_object* l_Int_Linear_Poly_findVarToSubst___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_coeff(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t l_Int_Linear_Poly_isUnsatDvd(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_set___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqLBool_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstDvdNat___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_natToInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Expr_norm(lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lia"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "subst"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2_value),LEAN_SCALAR_PTR_LITERAL(87, 130, 109, 65, 232, 6, 169, 172)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__3_value),LEAN_SCALAR_PTR_LITERAL(77, 149, 0, 200, 120, 117, 225, 20)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "assert"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "store"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2_value),LEAN_SCALAR_PTR_LITERAL(24, 23, 180, 58, 194, 72, 175, 153)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 137, 50, 202, 239, 114, 140, 141)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1_value),LEAN_SCALAR_PTR_LITERAL(236, 213, 16, 64, 1, 14, 244, 141)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "trivial"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2_value),LEAN_SCALAR_PTR_LITERAL(24, 23, 180, 58, 194, 72, 175, 153)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 137, 50, 202, 239, 114, 140, 141)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3_value),LEAN_SCALAR_PTR_LITERAL(177, 38, 232, 206, 222, 75, 121, 224)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "unsat"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2_value),LEAN_SCALAR_PTR_LITERAL(24, 23, 180, 58, 194, 72, 175, 153)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 137, 50, 202, 239, 114, 140, 141)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__6_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 174, 99, 3, 215, 140, 75)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2_value),LEAN_SCALAR_PTR_LITERAL(24, 23, 180, 58, 194, 72, 175, 153)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 137, 50, 202, 239, 114, 140, 141)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Dvd"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "dvd"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(255, 71, 229, 107, 63, 192, 93, 62)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(233, 16, 181, 127, 123, 63, 3, 18)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linear"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "of_not_dvd"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 107, 233, 98, 67, 69, 81)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__5_value),LEAN_SCALAR_PTR_LITERAL(57, 234, 237, 24, 129, 31, 246, 138)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "non-linear divisibility constraint found"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd_spec__0(lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "emod_pos_of_not_dvd"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__1_value),LEAN_SCALAR_PTR_LITERAL(38, 146, 134, 59, 191, 125, 100, 172)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ToInt"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "of_dvd"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__4_value),LEAN_SCALAR_PTR_LITERAL(4, 173, 245, 176, 99, 227, 18, 222)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__5_value),LEAN_SCALAR_PTR_LITERAL(223, 103, 37, 221, 182, 135, 125, 134)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_8____boxed(lean_object*);
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(1u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_unsigned_to_nat(0u);
v___x_4_ = lean_nat_to_int(v___x_3_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(lean_object* v_c_5_){
_start:
{
lean_object* v___y_7_; lean_object* v___y_8_; lean_object* v___y_9_; lean_object* v___y_10_; uint8_t v___y_11_; lean_object* v___y_17_; lean_object* v___y_18_; lean_object* v___y_19_; lean_object* v___y_20_; lean_object* v___y_21_; lean_object* v___y_28_; lean_object* v_d_29_; lean_object* v_p_30_; lean_object* v_d_35_; lean_object* v_p_36_; uint8_t v___x_37_; 
v_d_35_ = lean_ctor_get(v_c_5_, 0);
lean_inc(v_d_35_);
v_p_36_ = lean_ctor_get(v_c_5_, 1);
v___x_37_ = l_Int_Linear_Poly_isSorted(v_p_36_);
if (v___x_37_ == 0)
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
lean_inc_ref(v_p_36_);
v___x_38_ = l_Int_Linear_Poly_norm(v_p_36_);
v___x_39_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_39_, 0, v_c_5_);
lean_inc_ref(v___x_38_);
lean_inc(v_d_35_);
v___x_40_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_40_, 0, v_d_35_);
lean_ctor_set(v___x_40_, 1, v___x_38_);
lean_ctor_set(v___x_40_, 2, v___x_39_);
v___y_28_ = v___x_40_;
v_d_29_ = v_d_35_;
v_p_30_ = v___x_38_;
goto v___jp_27_;
}
else
{
lean_inc_ref(v_p_36_);
v___y_28_ = v_c_5_;
v_d_29_ = v_d_35_;
v_p_30_ = v_p_36_;
goto v___jp_27_;
}
v___jp_6_:
{
if (v___y_11_ == 0)
{
lean_dec(v___y_10_);
lean_dec_ref(v___y_9_);
lean_dec(v___y_7_);
return v___y_8_;
}
else
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_12_ = lean_int_ediv(v___y_7_, v___y_10_);
lean_dec(v___y_7_);
v___x_13_ = l_Int_Linear_Poly_div(v___y_10_, v___y_9_);
lean_dec(v___y_10_);
v___x_14_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_14_, 0, v___y_8_);
v___x_15_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_15_, 0, v___x_12_);
lean_ctor_set(v___x_15_, 1, v___x_13_);
lean_ctor_set(v___x_15_, 2, v___x_14_);
return v___x_15_;
}
}
v___jp_16_:
{
lean_object* v___x_22_; lean_object* v___x_23_; uint8_t v___x_24_; 
v___x_22_ = l_Int_Linear_Poly_getConst(v___y_20_);
v___x_23_ = lean_int_emod(v___x_22_, v___y_21_);
lean_dec(v___x_22_);
v___x_24_ = lean_int_dec_eq(v___x_23_, v___y_18_);
lean_dec(v___y_18_);
lean_dec(v___x_23_);
if (v___x_24_ == 0)
{
v___y_7_ = v___y_17_;
v___y_8_ = v___y_19_;
v___y_9_ = v___y_20_;
v___y_10_ = v___y_21_;
v___y_11_ = v___x_24_;
goto v___jp_6_;
}
else
{
lean_object* v___x_25_; uint8_t v___x_26_; 
v___x_25_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0);
v___x_26_ = lean_int_dec_eq(v___y_21_, v___x_25_);
if (v___x_26_ == 0)
{
v___y_7_ = v___y_17_;
v___y_8_ = v___y_19_;
v___y_9_ = v___y_20_;
v___y_10_ = v___y_21_;
v___y_11_ = v___x_24_;
goto v___jp_6_;
}
else
{
lean_dec(v___y_21_);
lean_dec_ref(v___y_20_);
lean_dec(v___y_17_);
return v___y_19_;
}
}
}
v___jp_27_:
{
lean_object* v_g_31_; lean_object* v___x_32_; uint8_t v___x_33_; 
lean_inc(v_d_29_);
v_g_31_ = l_Int_Linear_Poly_gcdCoeffs(v_p_30_, v_d_29_);
v___x_32_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1);
v___x_33_ = lean_int_dec_lt(v_d_29_, v___x_32_);
if (v___x_33_ == 0)
{
v___y_17_ = v_d_29_;
v___y_18_ = v___x_32_;
v___y_19_ = v___y_28_;
v___y_20_ = v_p_30_;
v___y_21_ = v_g_31_;
goto v___jp_16_;
}
else
{
lean_object* v___x_34_; 
v___x_34_ = lean_int_neg(v_g_31_);
lean_dec(v_g_31_);
v___y_17_ = v_d_29_;
v___y_18_ = v___x_32_;
v___y_19_ = v___y_28_;
v___y_20_ = v_p_30_;
v___y_21_ = v___x_34_;
goto v___jp_16_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(lean_object* v_cls_44_, lean_object* v___y_45_){
_start:
{
lean_object* v_options_47_; uint8_t v_hasTrace_48_; 
v_options_47_ = lean_ctor_get(v___y_45_, 2);
v_hasTrace_48_ = lean_ctor_get_uint8(v_options_47_, sizeof(void*)*1);
if (v_hasTrace_48_ == 0)
{
lean_object* v___x_49_; lean_object* v___x_50_; 
lean_dec(v_cls_44_);
v___x_49_ = lean_box(v_hasTrace_48_);
v___x_50_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
return v___x_50_;
}
else
{
lean_object* v_inheritedTraceOptions_51_; lean_object* v___x_52_; lean_object* v___x_53_; uint8_t v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v_inheritedTraceOptions_51_ = lean_ctor_get(v___y_45_, 13);
v___x_52_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__1));
v___x_53_ = l_Lean_Name_append(v___x_52_, v_cls_44_);
v___x_54_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_51_, v_options_47_, v___x_53_);
lean_dec(v___x_53_);
v___x_55_ = lean_box(v___x_54_);
v___x_56_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
return v___x_56_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___boxed(lean_object* v_cls_57_, lean_object* v___y_58_, lean_object* v___y_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v_cls_57_, v___y_58_);
lean_dec_ref(v___y_58_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0(lean_object* v_cls_61_, lean_object* v___y_62_, lean_object* v___y_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v_cls_61_, v___y_70_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___boxed(lean_object* v_cls_74_, lean_object* v___y_75_, lean_object* v___y_76_, lean_object* v___y_77_, lean_object* v___y_78_, lean_object* v___y_79_, lean_object* v___y_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0(v_cls_74_, v___y_75_, v___y_76_, v___y_77_, v___y_78_, v___y_79_, v___y_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
lean_dec(v___y_80_);
lean_dec_ref(v___y_79_);
lean_dec(v___y_78_);
lean_dec_ref(v___y_77_);
lean_dec(v___y_76_);
lean_dec(v___y_75_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1_spec__1(lean_object* v_msgData_87_, lean_object* v___y_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
lean_object* v___x_93_; lean_object* v_env_94_; lean_object* v___x_95_; lean_object* v_mctx_96_; lean_object* v_lctx_97_; lean_object* v_options_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_93_ = lean_st_ref_get(v___y_91_);
v_env_94_ = lean_ctor_get(v___x_93_, 0);
lean_inc_ref(v_env_94_);
lean_dec(v___x_93_);
v___x_95_ = lean_st_ref_get(v___y_89_);
v_mctx_96_ = lean_ctor_get(v___x_95_, 0);
lean_inc_ref(v_mctx_96_);
lean_dec(v___x_95_);
v_lctx_97_ = lean_ctor_get(v___y_88_, 2);
v_options_98_ = lean_ctor_get(v___y_90_, 2);
lean_inc_ref(v_options_98_);
lean_inc_ref(v_lctx_97_);
v___x_99_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_99_, 0, v_env_94_);
lean_ctor_set(v___x_99_, 1, v_mctx_96_);
lean_ctor_set(v___x_99_, 2, v_lctx_97_);
lean_ctor_set(v___x_99_, 3, v_options_98_);
v___x_100_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
lean_ctor_set(v___x_100_, 1, v_msgData_87_);
v___x_101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1_spec__1___boxed(lean_object* v_msgData_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1_spec__1(v_msgData_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_);
lean_dec(v___y_106_);
lean_dec_ref(v___y_105_);
lean_dec(v___y_104_);
lean_dec_ref(v___y_103_);
return v_res_108_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_109_; double v___x_110_; 
v___x_109_ = lean_unsigned_to_nat(0u);
v___x_110_ = lean_float_of_nat(v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(lean_object* v_cls_114_, lean_object* v_msg_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_){
_start:
{
lean_object* v_ref_121_; lean_object* v___x_122_; lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_167_; 
v_ref_121_ = lean_ctor_get(v___y_118_, 5);
v___x_122_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1_spec__1(v_msg_115_, v___y_116_, v___y_117_, v___y_118_, v___y_119_);
v_a_123_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_167_ == 0)
{
v___x_125_ = v___x_122_;
v_isShared_126_ = v_isSharedCheck_167_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v___x_122_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_167_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
lean_object* v___x_127_; lean_object* v_traceState_128_; lean_object* v_env_129_; lean_object* v_nextMacroScope_130_; lean_object* v_ngen_131_; lean_object* v_auxDeclNGen_132_; lean_object* v_cache_133_; lean_object* v_messages_134_; lean_object* v_infoState_135_; lean_object* v_snapshotTasks_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_166_; 
v___x_127_ = lean_st_ref_take(v___y_119_);
v_traceState_128_ = lean_ctor_get(v___x_127_, 4);
v_env_129_ = lean_ctor_get(v___x_127_, 0);
v_nextMacroScope_130_ = lean_ctor_get(v___x_127_, 1);
v_ngen_131_ = lean_ctor_get(v___x_127_, 2);
v_auxDeclNGen_132_ = lean_ctor_get(v___x_127_, 3);
v_cache_133_ = lean_ctor_get(v___x_127_, 5);
v_messages_134_ = lean_ctor_get(v___x_127_, 6);
v_infoState_135_ = lean_ctor_get(v___x_127_, 7);
v_snapshotTasks_136_ = lean_ctor_get(v___x_127_, 8);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_127_);
if (v_isSharedCheck_166_ == 0)
{
v___x_138_ = v___x_127_;
v_isShared_139_ = v_isSharedCheck_166_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_snapshotTasks_136_);
lean_inc(v_infoState_135_);
lean_inc(v_messages_134_);
lean_inc(v_cache_133_);
lean_inc(v_traceState_128_);
lean_inc(v_auxDeclNGen_132_);
lean_inc(v_ngen_131_);
lean_inc(v_nextMacroScope_130_);
lean_inc(v_env_129_);
lean_dec(v___x_127_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_166_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
uint64_t v_tid_140_; lean_object* v_traces_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_165_; 
v_tid_140_ = lean_ctor_get_uint64(v_traceState_128_, sizeof(void*)*1);
v_traces_141_ = lean_ctor_get(v_traceState_128_, 0);
v_isSharedCheck_165_ = !lean_is_exclusive(v_traceState_128_);
if (v_isSharedCheck_165_ == 0)
{
v___x_143_ = v_traceState_128_;
v_isShared_144_ = v_isSharedCheck_165_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_traces_141_);
lean_dec(v_traceState_128_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_165_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_145_; double v___x_146_; uint8_t v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_155_; 
v___x_145_ = lean_box(0);
v___x_146_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__0);
v___x_147_ = 0;
v___x_148_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__1));
v___x_149_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_149_, 0, v_cls_114_);
lean_ctor_set(v___x_149_, 1, v___x_145_);
lean_ctor_set(v___x_149_, 2, v___x_148_);
lean_ctor_set_float(v___x_149_, sizeof(void*)*3, v___x_146_);
lean_ctor_set_float(v___x_149_, sizeof(void*)*3 + 8, v___x_146_);
lean_ctor_set_uint8(v___x_149_, sizeof(void*)*3 + 16, v___x_147_);
v___x_150_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___closed__2));
v___x_151_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_151_, 0, v___x_149_);
lean_ctor_set(v___x_151_, 1, v_a_123_);
lean_ctor_set(v___x_151_, 2, v___x_150_);
lean_inc(v_ref_121_);
v___x_152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_152_, 0, v_ref_121_);
lean_ctor_set(v___x_152_, 1, v___x_151_);
v___x_153_ = l_Lean_PersistentArray_push___redArg(v_traces_141_, v___x_152_);
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 0, v___x_153_);
v___x_155_ = v___x_143_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v___x_153_);
lean_ctor_set_uint64(v_reuseFailAlloc_164_, sizeof(void*)*1, v_tid_140_);
v___x_155_ = v_reuseFailAlloc_164_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
lean_object* v___x_157_; 
if (v_isShared_139_ == 0)
{
lean_ctor_set(v___x_138_, 4, v___x_155_);
v___x_157_ = v___x_138_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v_env_129_);
lean_ctor_set(v_reuseFailAlloc_163_, 1, v_nextMacroScope_130_);
lean_ctor_set(v_reuseFailAlloc_163_, 2, v_ngen_131_);
lean_ctor_set(v_reuseFailAlloc_163_, 3, v_auxDeclNGen_132_);
lean_ctor_set(v_reuseFailAlloc_163_, 4, v___x_155_);
lean_ctor_set(v_reuseFailAlloc_163_, 5, v_cache_133_);
lean_ctor_set(v_reuseFailAlloc_163_, 6, v_messages_134_);
lean_ctor_set(v_reuseFailAlloc_163_, 7, v_infoState_135_);
lean_ctor_set(v_reuseFailAlloc_163_, 8, v_snapshotTasks_136_);
v___x_157_ = v_reuseFailAlloc_163_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_161_; 
v___x_158_ = lean_st_ref_set(v___y_119_, v___x_157_);
v___x_159_ = lean_box(0);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 0, v___x_159_);
v___x_161_ = v___x_125_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v___x_159_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg___boxed(lean_object* v_cls_168_, lean_object* v_msg_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_, lean_object* v___y_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(v_cls_168_, v_msg_169_, v___y_170_, v___y_171_, v___y_172_, v___y_173_);
lean_dec(v___y_173_);
lean_dec_ref(v___y_172_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
return v_res_175_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_186_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5));
v___x_187_ = l_Lean_stringToMessageData(v___x_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(lean_object* v_a_188_, lean_object* v_x_189_, lean_object* v_c_u2081_190_, lean_object* v_b_191_, lean_object* v_c_u2082_192_, lean_object* v_a_193_, lean_object* v_a_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_, lean_object* v_a_201_, lean_object* v_a_202_){
_start:
{
lean_object* v_cls_204_; lean_object* v___x_205_; lean_object* v_a_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_272_; 
v_cls_204_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4));
v___x_205_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v_cls_204_, v_a_201_);
v_a_206_ = lean_ctor_get(v___x_205_, 0);
v_isSharedCheck_272_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_272_ == 0)
{
v___x_208_ = v___x_205_;
v_isShared_209_ = v_isSharedCheck_272_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_a_206_);
lean_dec(v___x_205_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_272_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v_p_210_; lean_object* v_d_211_; lean_object* v_p_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v_d_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v_p_219_; uint8_t v___x_226_; 
v_p_210_ = lean_ctor_get(v_c_u2081_190_, 0);
v_d_211_ = lean_ctor_get(v_c_u2082_192_, 0);
v_p_212_ = lean_ctor_get(v_c_u2082_192_, 1);
v___x_213_ = lean_int_mul(v_a_188_, v_d_211_);
v___x_214_ = lean_nat_abs(v___x_213_);
lean_dec(v___x_213_);
v_d_215_ = lean_nat_to_int(v___x_214_);
lean_inc_ref(v_p_212_);
v___x_216_ = l_Int_Linear_Poly_mul(v_p_212_, v_a_188_);
v___x_217_ = lean_int_neg(v_b_191_);
lean_inc_ref(v_p_210_);
v___x_218_ = l_Int_Linear_Poly_mul(v_p_210_, v___x_217_);
lean_dec(v___x_217_);
v_p_219_ = l_Int_Linear_Poly_combine(v___x_216_, v___x_218_);
v___x_226_ = lean_unbox(v_a_206_);
lean_dec(v_a_206_);
if (v___x_226_ == 0)
{
goto v___jp_220_;
}
else
{
lean_object* v___x_227_; 
v___x_227_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_x_189_, v_a_193_, v_a_201_);
if (lean_obj_tag(v___x_227_) == 0)
{
lean_object* v_a_228_; lean_object* v___x_229_; 
v_a_228_ = lean_ctor_get(v___x_227_, 0);
lean_inc(v_a_228_);
lean_dec_ref(v___x_227_);
lean_inc_ref(v_c_u2081_190_);
v___x_229_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_u2081_190_, v_a_193_, v_a_201_);
if (lean_obj_tag(v___x_229_) == 0)
{
lean_object* v_a_230_; lean_object* v___x_231_; 
v_a_230_ = lean_ctor_get(v___x_229_, 0);
lean_inc(v_a_230_);
lean_dec_ref(v___x_229_);
lean_inc_ref(v_c_u2082_192_);
v___x_231_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_u2082_192_, v_a_193_, v_a_201_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v_a_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v_a_232_ = lean_ctor_get(v___x_231_, 0);
lean_inc(v_a_232_);
lean_dec_ref(v___x_231_);
v___x_233_ = l_Lean_MessageData_ofExpr(v_a_228_);
v___x_234_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6);
v___x_235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_235_, 0, v___x_233_);
lean_ctor_set(v___x_235_, 1, v___x_234_);
v___x_236_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_235_);
lean_ctor_set(v___x_236_, 1, v_a_230_);
v___x_237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_236_);
lean_ctor_set(v___x_237_, 1, v___x_234_);
v___x_238_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_237_);
lean_ctor_set(v___x_238_, 1, v_a_232_);
v___x_239_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(v_cls_204_, v___x_238_, v_a_199_, v_a_200_, v_a_201_, v_a_202_);
if (lean_obj_tag(v___x_239_) == 0)
{
lean_dec_ref(v___x_239_);
goto v___jp_220_;
}
else
{
lean_object* v_a_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_247_; 
lean_dec_ref(v_p_219_);
lean_dec(v_d_215_);
lean_del_object(v___x_208_);
lean_dec_ref(v_c_u2082_192_);
lean_dec_ref(v_c_u2081_190_);
lean_dec(v_x_189_);
v_a_240_ = lean_ctor_get(v___x_239_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v___x_239_);
if (v_isSharedCheck_247_ == 0)
{
v___x_242_ = v___x_239_;
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_a_240_);
lean_dec(v___x_239_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_245_; 
if (v_isShared_243_ == 0)
{
v___x_245_ = v___x_242_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_a_240_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
}
else
{
lean_object* v_a_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_255_; 
lean_dec(v_a_230_);
lean_dec(v_a_228_);
lean_dec_ref(v_p_219_);
lean_dec(v_d_215_);
lean_del_object(v___x_208_);
lean_dec_ref(v_c_u2082_192_);
lean_dec_ref(v_c_u2081_190_);
lean_dec(v_x_189_);
v_a_248_ = lean_ctor_get(v___x_231_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_255_ == 0)
{
v___x_250_ = v___x_231_;
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_a_248_);
lean_dec(v___x_231_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_253_; 
if (v_isShared_251_ == 0)
{
v___x_253_ = v___x_250_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v_a_248_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
}
}
else
{
lean_object* v_a_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_263_; 
lean_dec(v_a_228_);
lean_dec_ref(v_p_219_);
lean_dec(v_d_215_);
lean_del_object(v___x_208_);
lean_dec_ref(v_c_u2082_192_);
lean_dec_ref(v_c_u2081_190_);
lean_dec(v_x_189_);
v_a_256_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_263_ == 0)
{
v___x_258_ = v___x_229_;
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_a_256_);
lean_dec(v___x_229_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_263_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_261_; 
if (v_isShared_259_ == 0)
{
v___x_261_ = v___x_258_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v_a_256_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
}
else
{
lean_object* v_a_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_271_; 
lean_dec_ref(v_p_219_);
lean_dec(v_d_215_);
lean_del_object(v___x_208_);
lean_dec_ref(v_c_u2082_192_);
lean_dec_ref(v_c_u2081_190_);
lean_dec(v_x_189_);
v_a_264_ = lean_ctor_get(v___x_227_, 0);
v_isSharedCheck_271_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_271_ == 0)
{
v___x_266_ = v___x_227_;
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_dec(v___x_227_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_269_; 
if (v_isShared_267_ == 0)
{
v___x_269_ = v___x_266_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_a_264_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
}
v___jp_220_:
{
lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_224_; 
v___x_221_ = lean_alloc_ctor(8, 3, 0);
lean_ctor_set(v___x_221_, 0, v_x_189_);
lean_ctor_set(v___x_221_, 1, v_c_u2081_190_);
lean_ctor_set(v___x_221_, 2, v_c_u2082_192_);
v___x_222_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_222_, 0, v_d_215_);
lean_ctor_set(v___x_222_, 1, v_p_219_);
lean_ctor_set(v___x_222_, 2, v___x_221_);
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 0, v___x_222_);
v___x_224_ = v___x_208_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_222_);
v___x_224_ = v_reuseFailAlloc_225_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
return v___x_224_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___boxed(lean_object* v_a_273_, lean_object* v_x_274_, lean_object* v_c_u2081_275_, lean_object* v_b_276_, lean_object* v_c_u2082_277_, lean_object* v_a_278_, lean_object* v_a_279_, lean_object* v_a_280_, lean_object* v_a_281_, lean_object* v_a_282_, lean_object* v_a_283_, lean_object* v_a_284_, lean_object* v_a_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(v_a_273_, v_x_274_, v_c_u2081_275_, v_b_276_, v_c_u2082_277_, v_a_278_, v_a_279_, v_a_280_, v_a_281_, v_a_282_, v_a_283_, v_a_284_, v_a_285_, v_a_286_, v_a_287_);
lean_dec(v_a_287_);
lean_dec_ref(v_a_286_);
lean_dec(v_a_285_);
lean_dec_ref(v_a_284_);
lean_dec(v_a_283_);
lean_dec_ref(v_a_282_);
lean_dec(v_a_281_);
lean_dec_ref(v_a_280_);
lean_dec(v_a_279_);
lean_dec(v_a_278_);
lean_dec(v_b_276_);
lean_dec(v_a_273_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1(lean_object* v_cls_290_, lean_object* v_msg_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(v_cls_290_, v_msg_291_, v___y_298_, v___y_299_, v___y_300_, v___y_301_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___boxed(lean_object* v_cls_304_, lean_object* v_msg_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1(v_cls_304_, v_msg_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
lean_dec(v___y_311_);
lean_dec_ref(v___y_310_);
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
lean_dec(v___y_307_);
lean_dec(v___y_306_);
return v_res_317_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = l_Lean_maxRecDepthErrorMessage;
v___x_324_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_324_, 0, v___x_323_);
return v___x_324_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3);
v___x_326_ = l_Lean_MessageData_ofFormat(v___x_325_);
return v___x_326_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v___x_327_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4);
v___x_328_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2));
v___x_329_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
lean_ctor_set(v___x_329_, 1, v___x_327_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(lean_object* v_ref_330_){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_332_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5);
v___x_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_333_, 0, v_ref_330_);
lean_ctor_set(v___x_333_, 1, v___x_332_);
v___x_334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___boxed(lean_object* v_ref_335_, lean_object* v___y_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_335_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0(lean_object* v_00_u03b1_338_, lean_object* v_ref_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_339_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___boxed(lean_object* v_00_u03b1_352_, lean_object* v_ref_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0(v_00_u03b1_352_, v_ref_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec(v___y_361_);
lean_dec_ref(v___y_360_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
lean_dec(v___y_355_);
lean_dec(v___y_354_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(lean_object* v_c_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_){
_start:
{
lean_object* v_fileName_378_; lean_object* v_fileMap_379_; lean_object* v_options_380_; lean_object* v_currRecDepth_381_; lean_object* v_maxRecDepth_382_; lean_object* v_ref_383_; lean_object* v_currNamespace_384_; lean_object* v_openDecls_385_; lean_object* v_initHeartbeats_386_; lean_object* v_maxHeartbeats_387_; lean_object* v_quotContext_388_; lean_object* v_currMacroScope_389_; uint8_t v_diag_390_; lean_object* v_cancelTk_x3f_391_; uint8_t v_suppressElabErrors_392_; lean_object* v_inheritedTraceOptions_393_; uint8_t v___x_394_; 
v_fileName_378_ = lean_ctor_get(v_a_375_, 0);
lean_inc_ref(v_fileName_378_);
v_fileMap_379_ = lean_ctor_get(v_a_375_, 1);
lean_inc_ref(v_fileMap_379_);
v_options_380_ = lean_ctor_get(v_a_375_, 2);
lean_inc_ref(v_options_380_);
v_currRecDepth_381_ = lean_ctor_get(v_a_375_, 3);
lean_inc(v_currRecDepth_381_);
v_maxRecDepth_382_ = lean_ctor_get(v_a_375_, 4);
lean_inc(v_maxRecDepth_382_);
v_ref_383_ = lean_ctor_get(v_a_375_, 5);
lean_inc(v_ref_383_);
v_currNamespace_384_ = lean_ctor_get(v_a_375_, 6);
lean_inc(v_currNamespace_384_);
v_openDecls_385_ = lean_ctor_get(v_a_375_, 7);
lean_inc(v_openDecls_385_);
v_initHeartbeats_386_ = lean_ctor_get(v_a_375_, 8);
lean_inc(v_initHeartbeats_386_);
v_maxHeartbeats_387_ = lean_ctor_get(v_a_375_, 9);
lean_inc(v_maxHeartbeats_387_);
v_quotContext_388_ = lean_ctor_get(v_a_375_, 10);
lean_inc(v_quotContext_388_);
v_currMacroScope_389_ = lean_ctor_get(v_a_375_, 11);
lean_inc(v_currMacroScope_389_);
v_diag_390_ = lean_ctor_get_uint8(v_a_375_, sizeof(void*)*14);
v_cancelTk_x3f_391_ = lean_ctor_get(v_a_375_, 12);
lean_inc(v_cancelTk_x3f_391_);
v_suppressElabErrors_392_ = lean_ctor_get_uint8(v_a_375_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_393_ = lean_ctor_get(v_a_375_, 13);
lean_inc_ref(v_inheritedTraceOptions_393_);
lean_dec_ref(v_a_375_);
v___x_394_ = lean_nat_dec_eq(v_currRecDepth_381_, v_maxRecDepth_382_);
if (v___x_394_ == 0)
{
lean_object* v_p_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v_p_395_ = lean_ctor_get(v_c_366_, 1);
v___x_396_ = lean_unsigned_to_nat(1u);
v___x_397_ = lean_nat_add(v_currRecDepth_381_, v___x_396_);
lean_dec(v_currRecDepth_381_);
v___x_398_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_398_, 0, v_fileName_378_);
lean_ctor_set(v___x_398_, 1, v_fileMap_379_);
lean_ctor_set(v___x_398_, 2, v_options_380_);
lean_ctor_set(v___x_398_, 3, v___x_397_);
lean_ctor_set(v___x_398_, 4, v_maxRecDepth_382_);
lean_ctor_set(v___x_398_, 5, v_ref_383_);
lean_ctor_set(v___x_398_, 6, v_currNamespace_384_);
lean_ctor_set(v___x_398_, 7, v_openDecls_385_);
lean_ctor_set(v___x_398_, 8, v_initHeartbeats_386_);
lean_ctor_set(v___x_398_, 9, v_maxHeartbeats_387_);
lean_ctor_set(v___x_398_, 10, v_quotContext_388_);
lean_ctor_set(v___x_398_, 11, v_currMacroScope_389_);
lean_ctor_set(v___x_398_, 12, v_cancelTk_x3f_391_);
lean_ctor_set(v___x_398_, 13, v_inheritedTraceOptions_393_);
lean_ctor_set_uint8(v___x_398_, sizeof(void*)*14, v_diag_390_);
lean_ctor_set_uint8(v___x_398_, sizeof(void*)*14 + 1, v_suppressElabErrors_392_);
lean_inc_ref(v_p_395_);
v___x_399_ = l_Int_Linear_Poly_findVarToSubst___redArg(v_p_395_, v_a_367_, v___x_398_);
if (lean_obj_tag(v___x_399_) == 0)
{
lean_object* v_a_400_; lean_object* v___x_402_; uint8_t v_isShared_403_; uint8_t v_isSharedCheck_417_; 
v_a_400_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_417_ == 0)
{
v___x_402_ = v___x_399_;
v_isShared_403_ = v_isSharedCheck_417_;
goto v_resetjp_401_;
}
else
{
lean_inc(v_a_400_);
lean_dec(v___x_399_);
v___x_402_ = lean_box(0);
v_isShared_403_ = v_isSharedCheck_417_;
goto v_resetjp_401_;
}
v_resetjp_401_:
{
if (lean_obj_tag(v_a_400_) == 1)
{
lean_object* v_val_404_; lean_object* v_snd_405_; lean_object* v_snd_406_; lean_object* v_fst_407_; lean_object* v_fst_408_; lean_object* v_p_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
lean_del_object(v___x_402_);
v_val_404_ = lean_ctor_get(v_a_400_, 0);
lean_inc(v_val_404_);
lean_dec_ref(v_a_400_);
v_snd_405_ = lean_ctor_get(v_val_404_, 1);
lean_inc(v_snd_405_);
v_snd_406_ = lean_ctor_get(v_snd_405_, 1);
lean_inc(v_snd_406_);
v_fst_407_ = lean_ctor_get(v_val_404_, 0);
lean_inc(v_fst_407_);
lean_dec(v_val_404_);
v_fst_408_ = lean_ctor_get(v_snd_405_, 0);
lean_inc(v_fst_408_);
lean_dec(v_snd_405_);
v_p_409_ = lean_ctor_get(v_snd_406_, 0);
v___x_410_ = l_Int_Linear_Poly_coeff(v_p_409_, v_fst_408_);
v___x_411_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(v___x_410_, v_fst_408_, v_snd_406_, v_fst_407_, v_c_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_, v___x_398_, v_a_376_);
lean_dec(v_fst_407_);
lean_dec(v___x_410_);
if (lean_obj_tag(v___x_411_) == 0)
{
lean_object* v_a_412_; 
v_a_412_ = lean_ctor_get(v___x_411_, 0);
lean_inc(v_a_412_);
lean_dec_ref(v___x_411_);
v_c_366_ = v_a_412_;
v_a_375_ = v___x_398_;
goto _start;
}
else
{
lean_dec_ref(v___x_398_);
return v___x_411_;
}
}
else
{
lean_object* v___x_415_; 
lean_dec(v_a_400_);
lean_dec_ref(v___x_398_);
if (v_isShared_403_ == 0)
{
lean_ctor_set(v___x_402_, 0, v_c_366_);
v___x_415_ = v___x_402_;
goto v_reusejp_414_;
}
else
{
lean_object* v_reuseFailAlloc_416_; 
v_reuseFailAlloc_416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_416_, 0, v_c_366_);
v___x_415_ = v_reuseFailAlloc_416_;
goto v_reusejp_414_;
}
v_reusejp_414_:
{
return v___x_415_;
}
}
}
}
else
{
lean_object* v_a_418_; lean_object* v___x_420_; uint8_t v_isShared_421_; uint8_t v_isSharedCheck_425_; 
lean_dec_ref(v___x_398_);
lean_dec_ref(v_c_366_);
v_a_418_ = lean_ctor_get(v___x_399_, 0);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_425_ == 0)
{
v___x_420_ = v___x_399_;
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
else
{
lean_inc(v_a_418_);
lean_dec(v___x_399_);
v___x_420_ = lean_box(0);
v_isShared_421_ = v_isSharedCheck_425_;
goto v_resetjp_419_;
}
v_resetjp_419_:
{
lean_object* v___x_423_; 
if (v_isShared_421_ == 0)
{
v___x_423_ = v___x_420_;
goto v_reusejp_422_;
}
else
{
lean_object* v_reuseFailAlloc_424_; 
v_reuseFailAlloc_424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_424_, 0, v_a_418_);
v___x_423_ = v_reuseFailAlloc_424_;
goto v_reusejp_422_;
}
v_reusejp_422_:
{
return v___x_423_;
}
}
}
}
else
{
lean_object* v___x_426_; 
lean_dec_ref(v_inheritedTraceOptions_393_);
lean_dec(v_cancelTk_x3f_391_);
lean_dec(v_currMacroScope_389_);
lean_dec(v_quotContext_388_);
lean_dec(v_maxHeartbeats_387_);
lean_dec(v_initHeartbeats_386_);
lean_dec(v_openDecls_385_);
lean_dec(v_currNamespace_384_);
lean_dec(v_maxRecDepth_382_);
lean_dec(v_currRecDepth_381_);
lean_dec_ref(v_options_380_);
lean_dec_ref(v_fileMap_379_);
lean_dec_ref(v_fileName_378_);
lean_dec_ref(v_c_366_);
v___x_426_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_383_);
return v___x_426_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___boxed(lean_object* v_c_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(v_c_427_, v_a_428_, v_a_429_, v_a_430_, v_a_431_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_);
lean_dec(v_a_437_);
lean_dec(v_a_435_);
lean_dec_ref(v_a_434_);
lean_dec(v_a_433_);
lean_dec_ref(v_a_432_);
lean_dec(v_a_431_);
lean_dec_ref(v_a_430_);
lean_dec(v_a_429_);
lean_dec(v_a_428_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(lean_object* v_v_440_, lean_object* v_s_441_){
_start:
{
lean_object* v_vars_442_; lean_object* v_varMap_443_; lean_object* v_vars_x27_444_; lean_object* v_varMap_x27_445_; lean_object* v_natToIntMap_446_; lean_object* v_natDef_447_; lean_object* v_dvds_448_; lean_object* v_lowers_449_; lean_object* v_uppers_450_; lean_object* v_diseqs_451_; lean_object* v_elimEqs_452_; lean_object* v_elimStack_453_; lean_object* v_occurs_454_; lean_object* v_assignment_455_; lean_object* v_nextCnstrId_456_; uint8_t v_caseSplits_457_; lean_object* v_conflict_x3f_458_; lean_object* v_diseqSplits_459_; lean_object* v_divMod_460_; lean_object* v_toIntIds_461_; lean_object* v_toIntInfos_462_; lean_object* v_toIntTermMap_463_; lean_object* v_toIntVarMap_464_; uint8_t v_usedCommRing_465_; lean_object* v_nonlinearOccs_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_475_; 
v_vars_442_ = lean_ctor_get(v_s_441_, 0);
v_varMap_443_ = lean_ctor_get(v_s_441_, 1);
v_vars_x27_444_ = lean_ctor_get(v_s_441_, 2);
v_varMap_x27_445_ = lean_ctor_get(v_s_441_, 3);
v_natToIntMap_446_ = lean_ctor_get(v_s_441_, 4);
v_natDef_447_ = lean_ctor_get(v_s_441_, 5);
v_dvds_448_ = lean_ctor_get(v_s_441_, 6);
v_lowers_449_ = lean_ctor_get(v_s_441_, 7);
v_uppers_450_ = lean_ctor_get(v_s_441_, 8);
v_diseqs_451_ = lean_ctor_get(v_s_441_, 9);
v_elimEqs_452_ = lean_ctor_get(v_s_441_, 10);
v_elimStack_453_ = lean_ctor_get(v_s_441_, 11);
v_occurs_454_ = lean_ctor_get(v_s_441_, 12);
v_assignment_455_ = lean_ctor_get(v_s_441_, 13);
v_nextCnstrId_456_ = lean_ctor_get(v_s_441_, 14);
v_caseSplits_457_ = lean_ctor_get_uint8(v_s_441_, sizeof(void*)*23);
v_conflict_x3f_458_ = lean_ctor_get(v_s_441_, 15);
v_diseqSplits_459_ = lean_ctor_get(v_s_441_, 16);
v_divMod_460_ = lean_ctor_get(v_s_441_, 17);
v_toIntIds_461_ = lean_ctor_get(v_s_441_, 18);
v_toIntInfos_462_ = lean_ctor_get(v_s_441_, 19);
v_toIntTermMap_463_ = lean_ctor_get(v_s_441_, 20);
v_toIntVarMap_464_ = lean_ctor_get(v_s_441_, 21);
v_usedCommRing_465_ = lean_ctor_get_uint8(v_s_441_, sizeof(void*)*23 + 1);
v_nonlinearOccs_466_ = lean_ctor_get(v_s_441_, 22);
v_isSharedCheck_475_ = !lean_is_exclusive(v_s_441_);
if (v_isSharedCheck_475_ == 0)
{
v___x_468_ = v_s_441_;
v_isShared_469_ = v_isSharedCheck_475_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_nonlinearOccs_466_);
lean_inc(v_toIntVarMap_464_);
lean_inc(v_toIntTermMap_463_);
lean_inc(v_toIntInfos_462_);
lean_inc(v_toIntIds_461_);
lean_inc(v_divMod_460_);
lean_inc(v_diseqSplits_459_);
lean_inc(v_conflict_x3f_458_);
lean_inc(v_nextCnstrId_456_);
lean_inc(v_assignment_455_);
lean_inc(v_occurs_454_);
lean_inc(v_elimStack_453_);
lean_inc(v_elimEqs_452_);
lean_inc(v_diseqs_451_);
lean_inc(v_uppers_450_);
lean_inc(v_lowers_449_);
lean_inc(v_dvds_448_);
lean_inc(v_natDef_447_);
lean_inc(v_natToIntMap_446_);
lean_inc(v_varMap_x27_445_);
lean_inc(v_vars_x27_444_);
lean_inc(v_varMap_443_);
lean_inc(v_vars_442_);
lean_dec(v_s_441_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_475_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_473_; 
v___x_470_ = lean_box(0);
v___x_471_ = l_Lean_PersistentArray_set___redArg(v_dvds_448_, v_v_440_, v___x_470_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 6, v___x_471_);
v___x_473_ = v___x_468_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v_vars_442_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v_varMap_443_);
lean_ctor_set(v_reuseFailAlloc_474_, 2, v_vars_x27_444_);
lean_ctor_set(v_reuseFailAlloc_474_, 3, v_varMap_x27_445_);
lean_ctor_set(v_reuseFailAlloc_474_, 4, v_natToIntMap_446_);
lean_ctor_set(v_reuseFailAlloc_474_, 5, v_natDef_447_);
lean_ctor_set(v_reuseFailAlloc_474_, 6, v___x_471_);
lean_ctor_set(v_reuseFailAlloc_474_, 7, v_lowers_449_);
lean_ctor_set(v_reuseFailAlloc_474_, 8, v_uppers_450_);
lean_ctor_set(v_reuseFailAlloc_474_, 9, v_diseqs_451_);
lean_ctor_set(v_reuseFailAlloc_474_, 10, v_elimEqs_452_);
lean_ctor_set(v_reuseFailAlloc_474_, 11, v_elimStack_453_);
lean_ctor_set(v_reuseFailAlloc_474_, 12, v_occurs_454_);
lean_ctor_set(v_reuseFailAlloc_474_, 13, v_assignment_455_);
lean_ctor_set(v_reuseFailAlloc_474_, 14, v_nextCnstrId_456_);
lean_ctor_set(v_reuseFailAlloc_474_, 15, v_conflict_x3f_458_);
lean_ctor_set(v_reuseFailAlloc_474_, 16, v_diseqSplits_459_);
lean_ctor_set(v_reuseFailAlloc_474_, 17, v_divMod_460_);
lean_ctor_set(v_reuseFailAlloc_474_, 18, v_toIntIds_461_);
lean_ctor_set(v_reuseFailAlloc_474_, 19, v_toIntInfos_462_);
lean_ctor_set(v_reuseFailAlloc_474_, 20, v_toIntTermMap_463_);
lean_ctor_set(v_reuseFailAlloc_474_, 21, v_toIntVarMap_464_);
lean_ctor_set(v_reuseFailAlloc_474_, 22, v_nonlinearOccs_466_);
lean_ctor_set_uint8(v_reuseFailAlloc_474_, sizeof(void*)*23, v_caseSplits_457_);
lean_ctor_set_uint8(v_reuseFailAlloc_474_, sizeof(void*)*23 + 1, v_usedCommRing_465_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed(lean_object* v_v_476_, lean_object* v_s_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(v_v_476_, v_s_477_);
lean_dec(v_v_476_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(lean_object* v_a_479_, lean_object* v_v_480_, lean_object* v_s_481_){
_start:
{
lean_object* v_vars_482_; lean_object* v_varMap_483_; lean_object* v_vars_x27_484_; lean_object* v_varMap_x27_485_; lean_object* v_natToIntMap_486_; lean_object* v_natDef_487_; lean_object* v_dvds_488_; lean_object* v_lowers_489_; lean_object* v_uppers_490_; lean_object* v_diseqs_491_; lean_object* v_elimEqs_492_; lean_object* v_elimStack_493_; lean_object* v_occurs_494_; lean_object* v_assignment_495_; lean_object* v_nextCnstrId_496_; uint8_t v_caseSplits_497_; lean_object* v_conflict_x3f_498_; lean_object* v_diseqSplits_499_; lean_object* v_divMod_500_; lean_object* v_toIntIds_501_; lean_object* v_toIntInfos_502_; lean_object* v_toIntTermMap_503_; lean_object* v_toIntVarMap_504_; uint8_t v_usedCommRing_505_; lean_object* v_nonlinearOccs_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_515_; 
v_vars_482_ = lean_ctor_get(v_s_481_, 0);
v_varMap_483_ = lean_ctor_get(v_s_481_, 1);
v_vars_x27_484_ = lean_ctor_get(v_s_481_, 2);
v_varMap_x27_485_ = lean_ctor_get(v_s_481_, 3);
v_natToIntMap_486_ = lean_ctor_get(v_s_481_, 4);
v_natDef_487_ = lean_ctor_get(v_s_481_, 5);
v_dvds_488_ = lean_ctor_get(v_s_481_, 6);
v_lowers_489_ = lean_ctor_get(v_s_481_, 7);
v_uppers_490_ = lean_ctor_get(v_s_481_, 8);
v_diseqs_491_ = lean_ctor_get(v_s_481_, 9);
v_elimEqs_492_ = lean_ctor_get(v_s_481_, 10);
v_elimStack_493_ = lean_ctor_get(v_s_481_, 11);
v_occurs_494_ = lean_ctor_get(v_s_481_, 12);
v_assignment_495_ = lean_ctor_get(v_s_481_, 13);
v_nextCnstrId_496_ = lean_ctor_get(v_s_481_, 14);
v_caseSplits_497_ = lean_ctor_get_uint8(v_s_481_, sizeof(void*)*23);
v_conflict_x3f_498_ = lean_ctor_get(v_s_481_, 15);
v_diseqSplits_499_ = lean_ctor_get(v_s_481_, 16);
v_divMod_500_ = lean_ctor_get(v_s_481_, 17);
v_toIntIds_501_ = lean_ctor_get(v_s_481_, 18);
v_toIntInfos_502_ = lean_ctor_get(v_s_481_, 19);
v_toIntTermMap_503_ = lean_ctor_get(v_s_481_, 20);
v_toIntVarMap_504_ = lean_ctor_get(v_s_481_, 21);
v_usedCommRing_505_ = lean_ctor_get_uint8(v_s_481_, sizeof(void*)*23 + 1);
v_nonlinearOccs_506_ = lean_ctor_get(v_s_481_, 22);
v_isSharedCheck_515_ = !lean_is_exclusive(v_s_481_);
if (v_isSharedCheck_515_ == 0)
{
v___x_508_ = v_s_481_;
v_isShared_509_ = v_isSharedCheck_515_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_nonlinearOccs_506_);
lean_inc(v_toIntVarMap_504_);
lean_inc(v_toIntTermMap_503_);
lean_inc(v_toIntInfos_502_);
lean_inc(v_toIntIds_501_);
lean_inc(v_divMod_500_);
lean_inc(v_diseqSplits_499_);
lean_inc(v_conflict_x3f_498_);
lean_inc(v_nextCnstrId_496_);
lean_inc(v_assignment_495_);
lean_inc(v_occurs_494_);
lean_inc(v_elimStack_493_);
lean_inc(v_elimEqs_492_);
lean_inc(v_diseqs_491_);
lean_inc(v_uppers_490_);
lean_inc(v_lowers_489_);
lean_inc(v_dvds_488_);
lean_inc(v_natDef_487_);
lean_inc(v_natToIntMap_486_);
lean_inc(v_varMap_x27_485_);
lean_inc(v_vars_x27_484_);
lean_inc(v_varMap_483_);
lean_inc(v_vars_482_);
lean_dec(v_s_481_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_515_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_513_; 
v___x_510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_510_, 0, v_a_479_);
v___x_511_ = l_Lean_PersistentArray_set___redArg(v_dvds_488_, v_v_480_, v___x_510_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 6, v___x_511_);
v___x_513_ = v___x_508_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_vars_482_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v_varMap_483_);
lean_ctor_set(v_reuseFailAlloc_514_, 2, v_vars_x27_484_);
lean_ctor_set(v_reuseFailAlloc_514_, 3, v_varMap_x27_485_);
lean_ctor_set(v_reuseFailAlloc_514_, 4, v_natToIntMap_486_);
lean_ctor_set(v_reuseFailAlloc_514_, 5, v_natDef_487_);
lean_ctor_set(v_reuseFailAlloc_514_, 6, v___x_511_);
lean_ctor_set(v_reuseFailAlloc_514_, 7, v_lowers_489_);
lean_ctor_set(v_reuseFailAlloc_514_, 8, v_uppers_490_);
lean_ctor_set(v_reuseFailAlloc_514_, 9, v_diseqs_491_);
lean_ctor_set(v_reuseFailAlloc_514_, 10, v_elimEqs_492_);
lean_ctor_set(v_reuseFailAlloc_514_, 11, v_elimStack_493_);
lean_ctor_set(v_reuseFailAlloc_514_, 12, v_occurs_494_);
lean_ctor_set(v_reuseFailAlloc_514_, 13, v_assignment_495_);
lean_ctor_set(v_reuseFailAlloc_514_, 14, v_nextCnstrId_496_);
lean_ctor_set(v_reuseFailAlloc_514_, 15, v_conflict_x3f_498_);
lean_ctor_set(v_reuseFailAlloc_514_, 16, v_diseqSplits_499_);
lean_ctor_set(v_reuseFailAlloc_514_, 17, v_divMod_500_);
lean_ctor_set(v_reuseFailAlloc_514_, 18, v_toIntIds_501_);
lean_ctor_set(v_reuseFailAlloc_514_, 19, v_toIntInfos_502_);
lean_ctor_set(v_reuseFailAlloc_514_, 20, v_toIntTermMap_503_);
lean_ctor_set(v_reuseFailAlloc_514_, 21, v_toIntVarMap_504_);
lean_ctor_set(v_reuseFailAlloc_514_, 22, v_nonlinearOccs_506_);
lean_ctor_set_uint8(v_reuseFailAlloc_514_, sizeof(void*)*23, v_caseSplits_497_);
lean_ctor_set_uint8(v_reuseFailAlloc_514_, sizeof(void*)*23 + 1, v_usedCommRing_505_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
return v___x_513_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed(lean_object* v_a_516_, lean_object* v_v_517_, lean_object* v_s_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(v_a_516_, v_v_517_, v_s_518_);
lean_dec(v_v_517_);
return v_res_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(lean_object* v_c_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_, lean_object* v_a_549_, lean_object* v_a_550_, lean_object* v_a_551_, lean_object* v_a_552_, lean_object* v_a_553_){
_start:
{
lean_object* v___y_559_; lean_object* v___y_560_; lean_object* v___y_561_; lean_object* v___y_562_; lean_object* v___y_563_; lean_object* v___y_564_; lean_object* v___y_565_; lean_object* v___y_570_; lean_object* v___y_571_; lean_object* v___y_572_; lean_object* v___y_573_; lean_object* v___y_574_; lean_object* v___y_575_; lean_object* v___y_576_; lean_object* v___y_577_; lean_object* v___y_578_; lean_object* v___y_579_; lean_object* v___y_580_; lean_object* v_fileName_592_; lean_object* v_fileMap_593_; lean_object* v_options_594_; lean_object* v_currRecDepth_595_; lean_object* v_maxRecDepth_596_; lean_object* v_ref_597_; lean_object* v_currNamespace_598_; lean_object* v_openDecls_599_; lean_object* v_initHeartbeats_600_; lean_object* v_maxHeartbeats_601_; lean_object* v_quotContext_602_; lean_object* v_currMacroScope_603_; uint8_t v_diag_604_; lean_object* v_cancelTk_x3f_605_; uint8_t v_suppressElabErrors_606_; lean_object* v_inheritedTraceOptions_607_; uint8_t v___x_608_; 
v_fileName_592_ = lean_ctor_get(v_a_552_, 0);
lean_inc_ref(v_fileName_592_);
v_fileMap_593_ = lean_ctor_get(v_a_552_, 1);
lean_inc_ref(v_fileMap_593_);
v_options_594_ = lean_ctor_get(v_a_552_, 2);
lean_inc_ref(v_options_594_);
v_currRecDepth_595_ = lean_ctor_get(v_a_552_, 3);
lean_inc(v_currRecDepth_595_);
v_maxRecDepth_596_ = lean_ctor_get(v_a_552_, 4);
lean_inc(v_maxRecDepth_596_);
v_ref_597_ = lean_ctor_get(v_a_552_, 5);
lean_inc(v_ref_597_);
v_currNamespace_598_ = lean_ctor_get(v_a_552_, 6);
lean_inc(v_currNamespace_598_);
v_openDecls_599_ = lean_ctor_get(v_a_552_, 7);
lean_inc(v_openDecls_599_);
v_initHeartbeats_600_ = lean_ctor_get(v_a_552_, 8);
lean_inc(v_initHeartbeats_600_);
v_maxHeartbeats_601_ = lean_ctor_get(v_a_552_, 9);
lean_inc(v_maxHeartbeats_601_);
v_quotContext_602_ = lean_ctor_get(v_a_552_, 10);
lean_inc(v_quotContext_602_);
v_currMacroScope_603_ = lean_ctor_get(v_a_552_, 11);
lean_inc(v_currMacroScope_603_);
v_diag_604_ = lean_ctor_get_uint8(v_a_552_, sizeof(void*)*14);
v_cancelTk_x3f_605_ = lean_ctor_get(v_a_552_, 12);
lean_inc(v_cancelTk_x3f_605_);
v_suppressElabErrors_606_ = lean_ctor_get_uint8(v_a_552_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_607_ = lean_ctor_get(v_a_552_, 13);
lean_inc_ref(v_inheritedTraceOptions_607_);
lean_dec_ref(v_a_552_);
v___x_608_ = lean_nat_dec_eq(v_currRecDepth_595_, v_maxRecDepth_596_);
if (v___x_608_ == 0)
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_609_ = lean_unsigned_to_nat(1u);
v___x_610_ = lean_nat_add(v_currRecDepth_595_, v___x_609_);
lean_dec(v_currRecDepth_595_);
v___x_611_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_611_, 0, v_fileName_592_);
lean_ctor_set(v___x_611_, 1, v_fileMap_593_);
lean_ctor_set(v___x_611_, 2, v_options_594_);
lean_ctor_set(v___x_611_, 3, v___x_610_);
lean_ctor_set(v___x_611_, 4, v_maxRecDepth_596_);
lean_ctor_set(v___x_611_, 5, v_ref_597_);
lean_ctor_set(v___x_611_, 6, v_currNamespace_598_);
lean_ctor_set(v___x_611_, 7, v_openDecls_599_);
lean_ctor_set(v___x_611_, 8, v_initHeartbeats_600_);
lean_ctor_set(v___x_611_, 9, v_maxHeartbeats_601_);
lean_ctor_set(v___x_611_, 10, v_quotContext_602_);
lean_ctor_set(v___x_611_, 11, v_currMacroScope_603_);
lean_ctor_set(v___x_611_, 12, v_cancelTk_x3f_605_);
lean_ctor_set(v___x_611_, 13, v_inheritedTraceOptions_607_);
lean_ctor_set_uint8(v___x_611_, sizeof(void*)*14, v_diag_604_);
lean_ctor_set_uint8(v___x_611_, sizeof(void*)*14 + 1, v_suppressElabErrors_606_);
v___x_612_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_544_, v___x_611_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v_a_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_875_; 
v_a_613_ = lean_ctor_get(v___x_612_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_875_ == 0)
{
v___x_615_ = v___x_612_;
v_isShared_616_ = v_isSharedCheck_875_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_a_613_);
lean_dec(v___x_612_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_875_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
uint8_t v___x_617_; 
v___x_617_ = lean_unbox(v_a_613_);
lean_dec(v_a_613_);
if (v___x_617_ == 0)
{
lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_722_; lean_object* v___y_723_; lean_object* v___y_724_; lean_object* v___y_725_; lean_object* v___y_726_; lean_object* v___y_727_; lean_object* v___y_728_; lean_object* v___y_729_; lean_object* v___y_730_; lean_object* v___y_731_; lean_object* v___y_732_; lean_object* v___y_733_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___x_848_; lean_object* v___x_849_; 
lean_del_object(v___x_615_);
v___x_848_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__7));
v___x_849_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_848_, v___x_611_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v_a_850_; uint8_t v___x_851_; 
v_a_850_ = lean_ctor_get(v___x_849_, 0);
lean_inc(v_a_850_);
lean_dec_ref(v___x_849_);
v___x_851_ = lean_unbox(v_a_850_);
lean_dec(v_a_850_);
if (v___x_851_ == 0)
{
v___y_757_ = v_a_544_;
v___y_758_ = v_a_545_;
v___y_759_ = v_a_546_;
v___y_760_ = v_a_547_;
v___y_761_ = v_a_548_;
v___y_762_ = v_a_549_;
v___y_763_ = v_a_550_;
v___y_764_ = v_a_551_;
v___y_765_ = v___x_611_;
v___y_766_ = v_a_553_;
goto v___jp_756_;
}
else
{
lean_object* v___x_852_; 
lean_inc_ref(v_c_543_);
v___x_852_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_543_, v_a_544_, v___x_611_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; lean_object* v___x_854_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_a_853_);
lean_dec_ref(v___x_852_);
v___x_854_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(v___x_848_, v_a_853_, v_a_550_, v_a_551_, v___x_611_, v_a_553_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_dec_ref(v___x_854_);
v___y_757_ = v_a_544_;
v___y_758_ = v_a_545_;
v___y_759_ = v_a_546_;
v___y_760_ = v_a_547_;
v___y_761_ = v_a_548_;
v___y_762_ = v_a_549_;
v___y_763_ = v_a_550_;
v___y_764_ = v_a_551_;
v___y_765_ = v___x_611_;
v___y_766_ = v_a_553_;
goto v___jp_756_;
}
else
{
lean_dec_ref(v___x_611_);
lean_dec_ref(v_c_543_);
return v___x_854_;
}
}
else
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_862_; 
lean_dec_ref(v___x_611_);
lean_dec_ref(v_c_543_);
v_a_855_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_862_ == 0)
{
v___x_857_ = v___x_852_;
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_852_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_860_; 
if (v_isShared_858_ == 0)
{
v___x_860_ = v___x_857_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_a_855_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
}
else
{
lean_object* v_a_863_; lean_object* v___x_865_; uint8_t v_isShared_866_; uint8_t v_isSharedCheck_870_; 
lean_dec_ref(v___x_611_);
lean_dec_ref(v_c_543_);
v_a_863_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_870_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_870_ == 0)
{
v___x_865_ = v___x_849_;
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
else
{
lean_inc(v_a_863_);
lean_dec(v___x_849_);
v___x_865_ = lean_box(0);
v_isShared_866_ = v_isSharedCheck_870_;
goto v_resetjp_864_;
}
v_resetjp_864_:
{
lean_object* v___x_868_; 
if (v_isShared_866_ == 0)
{
v___x_868_ = v___x_865_;
goto v_reusejp_867_;
}
else
{
lean_object* v_reuseFailAlloc_869_; 
v_reuseFailAlloc_869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_869_, 0, v_a_863_);
v___x_868_ = v_reuseFailAlloc_869_;
goto v_reusejp_867_;
}
v_reusejp_867_:
{
return v___x_868_;
}
}
}
v___jp_618_:
{
if (lean_obj_tag(v___y_637_) == 1)
{
lean_object* v_val_638_; lean_object* v_p_639_; 
lean_dec_ref(v___y_633_);
lean_dec_ref(v___y_619_);
v_val_638_ = lean_ctor_get(v___y_637_, 0);
lean_inc(v_val_638_);
lean_dec_ref(v___y_637_);
v_p_639_ = lean_ctor_get(v_val_638_, 1);
lean_inc_ref(v_p_639_);
if (lean_obj_tag(v_p_639_) == 1)
{
lean_object* v_d_640_; lean_object* v_k_641_; lean_object* v_p_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_695_; 
v_d_640_ = lean_ctor_get(v_val_638_, 0);
v_k_641_ = lean_ctor_get(v_p_639_, 0);
v_p_642_ = lean_ctor_get(v_p_639_, 2);
v_isSharedCheck_695_ = !lean_is_exclusive(v_p_639_);
if (v_isSharedCheck_695_ == 0)
{
lean_object* v_unused_696_; 
v_unused_696_ = lean_ctor_get(v_p_639_, 1);
lean_dec(v_unused_696_);
v___x_644_ = v_p_639_;
v_isShared_645_ = v_isSharedCheck_695_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_p_642_);
lean_inc(v_k_641_);
lean_dec(v_p_639_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_695_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v_snd_649_; lean_object* v_fst_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_694_; 
v___x_646_ = lean_int_mul(v___y_627_, v_d_640_);
v___x_647_ = lean_int_mul(v_k_641_, v___y_622_);
v___x_648_ = l_Lean_Meta_Grind_Arith_gcdExt(v___x_646_, v___x_647_);
lean_dec(v___x_647_);
lean_dec(v___x_646_);
v_snd_649_ = lean_ctor_get(v___x_648_, 1);
v_fst_650_ = lean_ctor_get(v___x_648_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_648_);
if (v_isSharedCheck_694_ == 0)
{
v___x_652_ = v___x_648_;
v_isShared_653_ = v_isSharedCheck_694_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_snd_649_);
lean_inc(v_fst_650_);
lean_dec(v___x_648_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_694_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v_fst_654_; lean_object* v_snd_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_693_; 
v_fst_654_ = lean_ctor_get(v_snd_649_, 0);
v_snd_655_ = lean_ctor_get(v_snd_649_, 1);
v_isSharedCheck_693_ = !lean_is_exclusive(v_snd_649_);
if (v_isSharedCheck_693_ == 0)
{
v___x_657_ = v_snd_649_;
v_isShared_658_ = v_isSharedCheck_693_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_snd_655_);
lean_inc(v_fst_654_);
lean_dec(v_snd_649_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_693_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_659_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_660_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_659_, v___y_628_, v___y_630_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_668_; 
lean_dec_ref(v___x_660_);
v___x_661_ = lean_int_mul(v_fst_654_, v_d_640_);
lean_dec(v_fst_654_);
lean_inc_ref(v___y_620_);
v___x_662_ = l_Int_Linear_Poly_mul(v___y_620_, v___x_661_);
lean_dec(v___x_661_);
v___x_663_ = lean_int_mul(v_snd_655_, v___y_622_);
lean_dec(v_snd_655_);
lean_inc_ref(v_p_642_);
v___x_664_ = l_Int_Linear_Poly_mul(v_p_642_, v___x_663_);
lean_dec(v___x_663_);
v___x_665_ = lean_int_mul(v___y_622_, v_d_640_);
lean_dec(v___y_622_);
v___x_666_ = l_Int_Linear_Poly_combine(v___x_662_, v___x_664_);
lean_inc(v_fst_650_);
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 2, v___x_666_);
lean_ctor_set(v___x_644_, 1, v___y_623_);
lean_ctor_set(v___x_644_, 0, v_fst_650_);
v___x_668_ = v___x_644_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v_fst_650_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v___y_623_);
lean_ctor_set(v_reuseFailAlloc_692_, 2, v___x_666_);
v___x_668_ = v_reuseFailAlloc_692_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
lean_object* v___x_670_; 
lean_inc(v_val_638_);
lean_inc_ref(v___y_631_);
if (v_isShared_658_ == 0)
{
lean_ctor_set_tag(v___x_657_, 4);
lean_ctor_set(v___x_657_, 1, v_val_638_);
lean_ctor_set(v___x_657_, 0, v___y_631_);
v___x_670_ = v___x_657_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v___y_631_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v_val_638_);
v___x_670_ = v_reuseFailAlloc_691_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_671_, 0, v___x_665_);
lean_ctor_set(v___x_671_, 1, v___x_668_);
lean_ctor_set(v___x_671_, 2, v___x_670_);
lean_inc_ref(v___y_621_);
v___x_672_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v___x_671_, v___y_630_, v___y_626_, v___y_629_, v___y_632_, v___y_636_, v___y_634_, v___y_635_, v___y_625_, v___y_621_, v___y_624_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_678_; 
lean_dec_ref(v___x_672_);
v___x_673_ = l_Int_Linear_Poly_mul(v___y_620_, v_k_641_);
lean_dec(v_k_641_);
v___x_674_ = lean_int_neg(v___y_627_);
lean_dec(v___y_627_);
v___x_675_ = l_Int_Linear_Poly_mul(v_p_642_, v___x_674_);
lean_dec(v___x_674_);
v___x_676_ = l_Int_Linear_Poly_combine(v___x_673_, v___x_675_);
lean_inc(v_val_638_);
if (v_isShared_653_ == 0)
{
lean_ctor_set_tag(v___x_652_, 5);
lean_ctor_set(v___x_652_, 1, v_val_638_);
lean_ctor_set(v___x_652_, 0, v___y_631_);
v___x_678_ = v___x_652_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v___y_631_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v_val_638_);
v___x_678_ = v_reuseFailAlloc_690_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_686_; 
v_isSharedCheck_686_ = !lean_is_exclusive(v_val_638_);
if (v_isSharedCheck_686_ == 0)
{
lean_object* v_unused_687_; lean_object* v_unused_688_; lean_object* v_unused_689_; 
v_unused_687_ = lean_ctor_get(v_val_638_, 2);
lean_dec(v_unused_687_);
v_unused_688_ = lean_ctor_get(v_val_638_, 1);
lean_dec(v_unused_688_);
v_unused_689_ = lean_ctor_get(v_val_638_, 0);
lean_dec(v_unused_689_);
v___x_680_ = v_val_638_;
v_isShared_681_ = v_isSharedCheck_686_;
goto v_resetjp_679_;
}
else
{
lean_dec(v_val_638_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_686_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v___x_683_; 
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 2, v___x_678_);
lean_ctor_set(v___x_680_, 1, v___x_676_);
lean_ctor_set(v___x_680_, 0, v_fst_650_);
v___x_683_ = v___x_680_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_685_; 
v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_685_, 0, v_fst_650_);
lean_ctor_set(v_reuseFailAlloc_685_, 1, v___x_676_);
lean_ctor_set(v_reuseFailAlloc_685_, 2, v___x_678_);
v___x_683_ = v_reuseFailAlloc_685_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
v_c_543_ = v___x_683_;
v_a_544_ = v___y_630_;
v_a_545_ = v___y_626_;
v_a_546_ = v___y_629_;
v_a_547_ = v___y_632_;
v_a_548_ = v___y_636_;
v_a_549_ = v___y_634_;
v_a_550_ = v___y_635_;
v_a_551_ = v___y_625_;
v_a_552_ = v___y_621_;
v_a_553_ = v___y_624_;
goto _start;
}
}
}
}
else
{
lean_del_object(v___x_652_);
lean_dec(v_fst_650_);
lean_dec_ref(v_p_642_);
lean_dec(v_k_641_);
lean_dec(v_val_638_);
lean_dec_ref(v___y_631_);
lean_dec(v___y_627_);
lean_dec_ref(v___y_621_);
lean_dec_ref(v___y_620_);
return v___x_672_;
}
}
}
}
else
{
lean_del_object(v___x_657_);
lean_dec(v_snd_655_);
lean_dec(v_fst_654_);
lean_del_object(v___x_652_);
lean_dec(v_fst_650_);
lean_del_object(v___x_644_);
lean_dec_ref(v_p_642_);
lean_dec(v_k_641_);
lean_dec(v_val_638_);
lean_dec_ref(v___y_631_);
lean_dec(v___y_627_);
lean_dec(v___y_623_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec_ref(v___y_620_);
return v___x_660_;
}
}
}
}
}
else
{
lean_object* v___x_697_; 
lean_dec_ref(v_p_639_);
lean_dec_ref(v___y_631_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
lean_dec(v___y_623_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_620_);
v___x_697_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_val_638_, v___y_630_, v___y_626_, v___y_629_, v___y_632_, v___y_636_, v___y_634_, v___y_635_, v___y_625_, v___y_621_, v___y_624_);
lean_dec_ref(v___y_621_);
return v___x_697_;
}
}
else
{
lean_object* v___x_698_; lean_object* v___x_699_; 
lean_dec(v___y_637_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
lean_dec(v___y_623_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_620_);
v___x_698_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2));
v___x_699_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_698_, v___y_621_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; uint8_t v___x_701_; 
v_a_700_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_a_700_);
lean_dec_ref(v___x_699_);
v___x_701_ = lean_unbox(v_a_700_);
lean_dec(v_a_700_);
if (v___x_701_ == 0)
{
lean_dec_ref(v___y_631_);
v___y_559_ = v___y_619_;
v___y_560_ = v___y_633_;
v___y_561_ = v___y_630_;
v___y_562_ = v___y_635_;
v___y_563_ = v___y_625_;
v___y_564_ = v___y_621_;
v___y_565_ = v___y_624_;
goto v___jp_558_;
}
else
{
lean_object* v___x_702_; 
v___x_702_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v___y_631_, v___y_630_, v___y_621_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_object* v_a_703_; lean_object* v___x_704_; 
v_a_703_ = lean_ctor_get(v___x_702_, 0);
lean_inc(v_a_703_);
lean_dec_ref(v___x_702_);
v___x_704_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(v___x_698_, v_a_703_, v___y_635_, v___y_625_, v___y_621_, v___y_624_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_dec_ref(v___x_704_);
v___y_559_ = v___y_619_;
v___y_560_ = v___y_633_;
v___y_561_ = v___y_630_;
v___y_562_ = v___y_635_;
v___y_563_ = v___y_625_;
v___y_564_ = v___y_621_;
v___y_565_ = v___y_624_;
goto v___jp_558_;
}
else
{
lean_dec_ref(v___y_633_);
lean_dec_ref(v___y_621_);
lean_dec_ref(v___y_619_);
return v___x_704_;
}
}
else
{
lean_object* v_a_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_712_; 
lean_dec_ref(v___y_633_);
lean_dec_ref(v___y_621_);
lean_dec_ref(v___y_619_);
v_a_705_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_712_ == 0)
{
v___x_707_ = v___x_702_;
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_a_705_);
lean_dec(v___x_702_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_710_; 
if (v_isShared_708_ == 0)
{
v___x_710_ = v___x_707_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_a_705_);
v___x_710_ = v_reuseFailAlloc_711_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
return v___x_710_;
}
}
}
}
}
else
{
lean_object* v_a_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_720_; 
lean_dec_ref(v___y_633_);
lean_dec_ref(v___y_631_);
lean_dec_ref(v___y_621_);
lean_dec_ref(v___y_619_);
v_a_713_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_720_ == 0)
{
v___x_715_ = v___x_699_;
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_a_713_);
lean_dec(v___x_699_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_718_; 
if (v_isShared_716_ == 0)
{
v___x_718_ = v___x_715_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_a_713_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
}
}
v___jp_721_:
{
lean_object* v___x_740_; 
v___x_740_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v___y_730_, v___y_738_);
if (lean_obj_tag(v___x_740_) == 0)
{
lean_object* v_a_741_; lean_object* v_dvds_742_; lean_object* v_size_743_; lean_object* v___x_744_; uint8_t v___x_745_; 
v_a_741_ = lean_ctor_get(v___x_740_, 0);
lean_inc(v_a_741_);
lean_dec_ref(v___x_740_);
v_dvds_742_ = lean_ctor_get(v_a_741_, 6);
lean_inc_ref(v_dvds_742_);
lean_dec(v_a_741_);
v_size_743_ = lean_ctor_get(v_dvds_742_, 2);
v___x_744_ = lean_box(0);
v___x_745_ = lean_nat_dec_lt(v___y_725_, v_size_743_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; 
lean_dec_ref(v_dvds_742_);
v___x_746_ = l_outOfBounds___redArg(v___x_744_);
v___y_619_ = v___y_722_;
v___y_620_ = v___y_724_;
v___y_621_ = v___y_738_;
v___y_622_ = v___y_726_;
v___y_623_ = v___y_725_;
v___y_624_ = v___y_739_;
v___y_625_ = v___y_737_;
v___y_626_ = v___y_731_;
v___y_627_ = v___y_729_;
v___y_628_ = v___y_728_;
v___y_629_ = v___y_732_;
v___y_630_ = v___y_730_;
v___y_631_ = v___y_723_;
v___y_632_ = v___y_733_;
v___y_633_ = v___y_727_;
v___y_634_ = v___y_735_;
v___y_635_ = v___y_736_;
v___y_636_ = v___y_734_;
v___y_637_ = v___x_746_;
goto v___jp_618_;
}
else
{
lean_object* v___x_747_; 
v___x_747_ = l_Lean_PersistentArray_get_x21___redArg(v___x_744_, v_dvds_742_, v___y_725_);
v___y_619_ = v___y_722_;
v___y_620_ = v___y_724_;
v___y_621_ = v___y_738_;
v___y_622_ = v___y_726_;
v___y_623_ = v___y_725_;
v___y_624_ = v___y_739_;
v___y_625_ = v___y_737_;
v___y_626_ = v___y_731_;
v___y_627_ = v___y_729_;
v___y_628_ = v___y_728_;
v___y_629_ = v___y_732_;
v___y_630_ = v___y_730_;
v___y_631_ = v___y_723_;
v___y_632_ = v___y_733_;
v___y_633_ = v___y_727_;
v___y_634_ = v___y_735_;
v___y_635_ = v___y_736_;
v___y_636_ = v___y_734_;
v___y_637_ = v___x_747_;
goto v___jp_618_;
}
}
else
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_755_; 
lean_dec_ref(v___y_738_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec(v___y_726_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec_ref(v___y_722_);
v_a_748_ = lean_ctor_get(v___x_740_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_740_);
if (v_isSharedCheck_755_ == 0)
{
v___x_750_ = v___x_740_;
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_740_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_755_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_753_; 
if (v_isShared_751_ == 0)
{
v___x_753_ = v___x_750_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_a_748_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
v___jp_756_:
{
lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_767_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(v_c_543_);
lean_inc_ref(v___y_765_);
v___x_768_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(v___x_767_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v_a_769_; lean_object* v_d_770_; lean_object* v_p_771_; uint8_t v___x_772_; 
v_a_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_a_769_);
lean_dec_ref(v___x_768_);
v_d_770_ = lean_ctor_get(v_a_769_, 0);
v_p_771_ = lean_ctor_get(v_a_769_, 1);
lean_inc(v_d_770_);
v___x_772_ = l_Int_Linear_Poly_isUnsatDvd(v_d_770_, v_p_771_);
if (v___x_772_ == 0)
{
uint8_t v___x_773_; 
v___x_773_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(v_a_769_);
if (v___x_773_ == 0)
{
if (lean_obj_tag(v_p_771_) == 1)
{
lean_object* v_k_774_; lean_object* v_v_775_; lean_object* v_p_776_; lean_object* v___x_777_; 
lean_inc_ref(v_p_771_);
lean_inc(v_d_770_);
v_k_774_ = lean_ctor_get(v_p_771_, 0);
lean_inc(v_k_774_);
v_v_775_ = lean_ctor_get(v_p_771_, 1);
lean_inc(v_v_775_);
v_p_776_ = lean_ctor_get(v_p_771_, 2);
lean_inc_ref(v_p_776_);
lean_inc(v_a_769_);
v___x_777_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(v_a_769_, v___y_757_, v___y_765_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v_a_778_; lean_object* v___f_779_; lean_object* v___f_780_; uint8_t v___x_781_; uint8_t v___x_782_; uint8_t v___x_783_; 
v_a_778_ = lean_ctor_get(v___x_777_, 0);
lean_inc(v_a_778_);
lean_dec_ref(v___x_777_);
lean_inc(v_v_775_);
v___f_779_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed), 2, 1);
lean_closure_set(v___f_779_, 0, v_v_775_);
lean_inc(v_v_775_);
lean_inc(v_a_769_);
v___f_780_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed), 3, 2);
lean_closure_set(v___f_780_, 0, v_a_769_);
lean_closure_set(v___f_780_, 1, v_v_775_);
v___x_781_ = 0;
v___x_782_ = lean_unbox(v_a_778_);
lean_dec(v_a_778_);
v___x_783_ = l_Lean_instBEqLBool_beq(v___x_782_, v___x_781_);
if (v___x_783_ == 0)
{
v___y_722_ = v_p_771_;
v___y_723_ = v_a_769_;
v___y_724_ = v_p_776_;
v___y_725_ = v_v_775_;
v___y_726_ = v_d_770_;
v___y_727_ = v___f_780_;
v___y_728_ = v___f_779_;
v___y_729_ = v_k_774_;
v___y_730_ = v___y_757_;
v___y_731_ = v___y_758_;
v___y_732_ = v___y_759_;
v___y_733_ = v___y_760_;
v___y_734_ = v___y_761_;
v___y_735_ = v___y_762_;
v___y_736_ = v___y_763_;
v___y_737_ = v___y_764_;
v___y_738_ = v___y_765_;
v___y_739_ = v___y_766_;
goto v___jp_721_;
}
else
{
lean_object* v___x_784_; 
lean_inc(v_v_775_);
v___x_784_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v_v_775_, v___y_757_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_dec_ref(v___x_784_);
v___y_722_ = v_p_771_;
v___y_723_ = v_a_769_;
v___y_724_ = v_p_776_;
v___y_725_ = v_v_775_;
v___y_726_ = v_d_770_;
v___y_727_ = v___f_780_;
v___y_728_ = v___f_779_;
v___y_729_ = v_k_774_;
v___y_730_ = v___y_757_;
v___y_731_ = v___y_758_;
v___y_732_ = v___y_759_;
v___y_733_ = v___y_760_;
v___y_734_ = v___y_761_;
v___y_735_ = v___y_762_;
v___y_736_ = v___y_763_;
v___y_737_ = v___y_764_;
v___y_738_ = v___y_765_;
v___y_739_ = v___y_766_;
goto v___jp_721_;
}
else
{
lean_dec_ref(v___f_780_);
lean_dec_ref(v___f_779_);
lean_dec_ref(v_p_776_);
lean_dec(v_v_775_);
lean_dec(v_k_774_);
lean_dec_ref(v_p_771_);
lean_dec(v_d_770_);
lean_dec(v_a_769_);
lean_dec_ref(v___y_765_);
return v___x_784_;
}
}
}
else
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_792_; 
lean_dec_ref(v_p_776_);
lean_dec(v_v_775_);
lean_dec_ref(v_p_771_);
lean_dec(v_k_774_);
lean_dec(v_d_770_);
lean_dec(v_a_769_);
lean_dec_ref(v___y_765_);
v_a_785_ = lean_ctor_get(v___x_777_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_777_);
if (v_isSharedCheck_792_ == 0)
{
v___x_787_ = v___x_777_;
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_777_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_792_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
lean_object* v___x_790_; 
if (v_isShared_788_ == 0)
{
v___x_790_ = v___x_787_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_a_785_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
}
else
{
lean_object* v___x_793_; 
v___x_793_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_a_769_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
lean_dec_ref(v___y_765_);
return v___x_793_;
}
}
else
{
lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_794_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4));
v___x_795_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_794_, v___y_765_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v_a_796_; uint8_t v___x_797_; 
v_a_796_ = lean_ctor_get(v___x_795_, 0);
lean_inc(v_a_796_);
lean_dec_ref(v___x_795_);
v___x_797_ = lean_unbox(v_a_796_);
lean_dec(v_a_796_);
if (v___x_797_ == 0)
{
lean_dec(v_a_769_);
lean_dec_ref(v___y_765_);
goto v___jp_555_;
}
else
{
lean_object* v___x_798_; 
v___x_798_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_a_769_, v___y_757_, v___y_765_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v_a_799_; lean_object* v___x_800_; 
v_a_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_a_799_);
lean_dec_ref(v___x_798_);
v___x_800_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(v___x_794_, v_a_799_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
lean_dec_ref(v___y_765_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_dec_ref(v___x_800_);
goto v___jp_555_;
}
else
{
return v___x_800_;
}
}
else
{
lean_object* v_a_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_808_; 
lean_dec_ref(v___y_765_);
v_a_801_ = lean_ctor_get(v___x_798_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_798_);
if (v_isSharedCheck_808_ == 0)
{
v___x_803_ = v___x_798_;
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_a_801_);
lean_dec(v___x_798_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_806_; 
if (v_isShared_804_ == 0)
{
v___x_806_ = v___x_803_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_a_801_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
}
}
else
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
lean_dec(v_a_769_);
lean_dec_ref(v___y_765_);
v_a_809_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_816_ == 0)
{
v___x_811_ = v___x_795_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_795_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_809_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
}
else
{
lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_817_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__6));
v___x_818_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_817_, v___y_765_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; uint8_t v___x_820_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_a_819_);
lean_dec_ref(v___x_818_);
v___x_820_ = lean_unbox(v_a_819_);
lean_dec(v_a_819_);
if (v___x_820_ == 0)
{
v___y_570_ = v_a_769_;
v___y_571_ = v___y_757_;
v___y_572_ = v___y_758_;
v___y_573_ = v___y_759_;
v___y_574_ = v___y_760_;
v___y_575_ = v___y_761_;
v___y_576_ = v___y_762_;
v___y_577_ = v___y_763_;
v___y_578_ = v___y_764_;
v___y_579_ = v___y_765_;
v___y_580_ = v___y_766_;
goto v___jp_569_;
}
else
{
lean_object* v___x_821_; 
lean_inc(v_a_769_);
v___x_821_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_a_769_, v___y_757_, v___y_765_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v_a_822_; lean_object* v___x_823_; 
v_a_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_a_822_);
lean_dec_ref(v___x_821_);
v___x_823_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__1___redArg(v___x_817_, v_a_822_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_dec_ref(v___x_823_);
v___y_570_ = v_a_769_;
v___y_571_ = v___y_757_;
v___y_572_ = v___y_758_;
v___y_573_ = v___y_759_;
v___y_574_ = v___y_760_;
v___y_575_ = v___y_761_;
v___y_576_ = v___y_762_;
v___y_577_ = v___y_763_;
v___y_578_ = v___y_764_;
v___y_579_ = v___y_765_;
v___y_580_ = v___y_766_;
goto v___jp_569_;
}
else
{
lean_dec(v_a_769_);
lean_dec_ref(v___y_765_);
return v___x_823_;
}
}
else
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_831_; 
lean_dec(v_a_769_);
lean_dec_ref(v___y_765_);
v_a_824_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_831_ == 0)
{
v___x_826_ = v___x_821_;
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_821_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_831_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_829_; 
if (v_isShared_827_ == 0)
{
v___x_829_ = v___x_826_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v_a_824_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
}
}
else
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
lean_dec(v_a_769_);
lean_dec_ref(v___y_765_);
v_a_832_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_839_ == 0)
{
v___x_834_ = v___x_818_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_818_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_a_832_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
}
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
lean_dec_ref(v___y_765_);
v_a_840_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_768_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_768_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_840_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
}
else
{
lean_object* v___x_871_; lean_object* v___x_873_; 
lean_dec_ref(v___x_611_);
lean_dec_ref(v_c_543_);
v___x_871_ = lean_box(0);
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 0, v___x_871_);
v___x_873_ = v___x_615_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v___x_871_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
lean_dec_ref(v___x_611_);
lean_dec_ref(v_c_543_);
v_a_876_ = lean_ctor_get(v___x_612_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_612_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_612_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
else
{
lean_object* v___x_884_; 
lean_dec_ref(v_inheritedTraceOptions_607_);
lean_dec(v_cancelTk_x3f_605_);
lean_dec(v_currMacroScope_603_);
lean_dec(v_quotContext_602_);
lean_dec(v_maxHeartbeats_601_);
lean_dec(v_initHeartbeats_600_);
lean_dec(v_openDecls_599_);
lean_dec(v_currNamespace_598_);
lean_dec(v_maxRecDepth_596_);
lean_dec(v_currRecDepth_595_);
lean_dec_ref(v_options_594_);
lean_dec_ref(v_fileMap_593_);
lean_dec_ref(v_fileName_592_);
lean_dec_ref(v_c_543_);
v___x_884_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_597_);
return v___x_884_;
}
v___jp_555_:
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = lean_box(0);
v___x_557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_557_, 0, v___x_556_);
return v___x_557_;
}
v___jp_558_:
{
lean_object* v___x_566_; 
v___x_566_ = l_Int_Linear_Poly_updateOccs___redArg(v___y_559_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
lean_dec_ref(v___y_564_);
if (lean_obj_tag(v___x_566_) == 0)
{
lean_object* v___x_567_; lean_object* v___x_568_; 
lean_dec_ref(v___x_566_);
v___x_567_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_568_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_567_, v___y_560_, v___y_561_);
return v___x_568_;
}
else
{
lean_dec_ref(v___y_560_);
return v___x_566_;
}
}
v___jp_569_:
{
lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_581_, 0, v___y_570_);
v___x_582_ = l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(v___x_581_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_);
lean_dec_ref(v___y_579_);
if (lean_obj_tag(v___x_582_) == 0)
{
lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_590_; 
v_isSharedCheck_590_ = !lean_is_exclusive(v___x_582_);
if (v_isSharedCheck_590_ == 0)
{
lean_object* v_unused_591_; 
v_unused_591_ = lean_ctor_get(v___x_582_, 0);
lean_dec(v_unused_591_);
v___x_584_ = v___x_582_;
v_isShared_585_ = v_isSharedCheck_590_;
goto v_resetjp_583_;
}
else
{
lean_dec(v___x_582_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_590_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_586_; lean_object* v___x_588_; 
v___x_586_ = lean_box(0);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 0, v___x_586_);
v___x_588_ = v___x_584_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_586_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
else
{
return v___x_582_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___boxed(lean_object* v_c_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v_c_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_);
lean_dec(v_a_895_);
lean_dec(v_a_893_);
lean_dec_ref(v_a_892_);
lean_dec(v_a_891_);
lean_dec_ref(v_a_890_);
lean_dec(v_a_889_);
lean_dec_ref(v_a_888_);
lean_dec(v_a_887_);
lean_dec(v_a_886_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(lean_object* v_c_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_){
_start:
{
lean_object* v_d_910_; lean_object* v_p_911_; lean_object* v___x_912_; 
v_d_910_ = lean_ctor_get(v_c_898_, 0);
v_p_911_ = lean_ctor_get(v_c_898_, 1);
lean_inc_ref(v_p_911_);
v___x_912_ = l_Int_Linear_Poly_normCommRing_x3f(v_p_911_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_a_913_; 
v_a_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_a_913_);
lean_dec_ref(v___x_912_);
if (lean_obj_tag(v_a_913_) == 1)
{
lean_object* v_val_914_; lean_object* v_snd_915_; lean_object* v_fst_916_; lean_object* v_fst_917_; lean_object* v_snd_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
lean_inc(v_d_910_);
v_val_914_ = lean_ctor_get(v_a_913_, 0);
lean_inc(v_val_914_);
lean_dec_ref(v_a_913_);
v_snd_915_ = lean_ctor_get(v_val_914_, 1);
lean_inc(v_snd_915_);
v_fst_916_ = lean_ctor_get(v_val_914_, 0);
lean_inc(v_fst_916_);
lean_dec(v_val_914_);
v_fst_917_ = lean_ctor_get(v_snd_915_, 0);
lean_inc(v_fst_917_);
v_snd_918_ = lean_ctor_get(v_snd_915_, 1);
lean_inc(v_snd_918_);
lean_dec(v_snd_915_);
v___x_919_ = lean_alloc_ctor(12, 3, 0);
lean_ctor_set(v___x_919_, 0, v_c_898_);
lean_ctor_set(v___x_919_, 1, v_fst_916_);
lean_ctor_set(v___x_919_, 2, v_fst_917_);
v___x_920_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_920_, 0, v_d_910_);
lean_ctor_set(v___x_920_, 1, v_snd_918_);
lean_ctor_set(v___x_920_, 2, v___x_919_);
lean_inc_ref(v_a_907_);
v___x_921_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v___x_920_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
return v___x_921_;
}
else
{
lean_object* v___x_922_; 
lean_dec(v_a_913_);
lean_inc_ref(v_a_907_);
v___x_922_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v_c_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
return v___x_922_;
}
}
else
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_930_; 
lean_dec_ref(v_c_898_);
v_a_923_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_930_ == 0)
{
v___x_925_ = v___x_912_;
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_912_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
v___x_928_ = v___x_925_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_923_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore___boxed(lean_object* v_c_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_){
_start:
{
lean_object* v_res_943_; 
v_res_943_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v_c_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_, v_a_937_, v_a_938_, v_a_939_, v_a_940_, v_a_941_);
lean_dec(v_a_941_);
lean_dec_ref(v_a_940_);
lean_dec(v_a_939_);
lean_dec_ref(v_a_938_);
lean_dec(v_a_937_);
lean_dec_ref(v_a_936_);
lean_dec(v_a_935_);
lean_dec_ref(v_a_934_);
lean_dec(v_a_933_);
lean_dec(v_a_932_);
return v_res_943_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7(void){
_start:
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_956_ = lean_box(0);
v___x_957_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6));
v___x_958_ = l_Lean_mkConst(v___x_957_, v___x_956_);
return v___x_958_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9(void){
_start:
{
lean_object* v___x_960_; lean_object* v___x_961_; 
v___x_960_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8));
v___x_961_ = l_Lean_stringToMessageData(v___x_960_);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(lean_object* v_e_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_){
_start:
{
lean_object* v___x_977_; 
lean_inc_ref(v_e_962_);
v___x_977_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_962_, v_a_970_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_1111_; 
v_a_978_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_980_ = v___x_977_;
v_isShared_981_ = v_isSharedCheck_1111_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_977_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_1111_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_987_; uint8_t v___x_988_; 
v___x_987_ = l_Lean_Expr_cleanupAnnotations(v_a_978_);
v___x_988_ = l_Lean_Expr_isApp(v___x_987_);
if (v___x_988_ == 0)
{
lean_dec_ref(v___x_987_);
lean_dec_ref(v_e_962_);
goto v___jp_982_;
}
else
{
lean_object* v_arg_989_; lean_object* v___x_990_; uint8_t v___x_991_; 
v_arg_989_ = lean_ctor_get(v___x_987_, 1);
lean_inc_ref(v_arg_989_);
v___x_990_ = l_Lean_Expr_appFnCleanup___redArg(v___x_987_);
v___x_991_ = l_Lean_Expr_isApp(v___x_990_);
if (v___x_991_ == 0)
{
lean_dec_ref(v___x_990_);
lean_dec_ref(v_arg_989_);
lean_dec_ref(v_e_962_);
goto v___jp_982_;
}
else
{
lean_object* v_arg_992_; lean_object* v___x_993_; uint8_t v___x_994_; 
v_arg_992_ = lean_ctor_get(v___x_990_, 1);
lean_inc_ref(v_arg_992_);
v___x_993_ = l_Lean_Expr_appFnCleanup___redArg(v___x_990_);
v___x_994_ = l_Lean_Expr_isApp(v___x_993_);
if (v___x_994_ == 0)
{
lean_dec_ref(v___x_993_);
lean_dec_ref(v_arg_992_);
lean_dec_ref(v_arg_989_);
lean_dec_ref(v_e_962_);
goto v___jp_982_;
}
else
{
lean_object* v_arg_995_; lean_object* v___x_996_; uint8_t v___x_997_; 
v_arg_995_ = lean_ctor_get(v___x_993_, 1);
lean_inc_ref(v_arg_995_);
v___x_996_ = l_Lean_Expr_appFnCleanup___redArg(v___x_993_);
v___x_997_ = l_Lean_Expr_isApp(v___x_996_);
if (v___x_997_ == 0)
{
lean_dec_ref(v___x_996_);
lean_dec_ref(v_arg_995_);
lean_dec_ref(v_arg_992_);
lean_dec_ref(v_arg_989_);
lean_dec_ref(v_e_962_);
goto v___jp_982_;
}
else
{
lean_object* v___x_998_; lean_object* v___x_999_; uint8_t v___x_1000_; 
v___x_998_ = l_Lean_Expr_appFnCleanup___redArg(v___x_996_);
v___x_999_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1000_ = l_Lean_Expr_isConstOf(v___x_998_, v___x_999_);
lean_dec_ref(v___x_998_);
if (v___x_1000_ == 0)
{
lean_dec_ref(v_arg_995_);
lean_dec_ref(v_arg_992_);
lean_dec_ref(v_arg_989_);
lean_dec_ref(v_e_962_);
goto v___jp_982_;
}
else
{
lean_object* v___x_1001_; 
lean_del_object(v___x_980_);
v___x_1001_ = l_Lean_Meta_Structural_isInstDvdInt___redArg(v_arg_995_, v_a_970_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1102_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1004_ = v___x_1001_;
v_isShared_1005_ = v_isSharedCheck_1102_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_1001_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1102_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
uint8_t v___x_1006_; 
v___x_1006_ = lean_unbox(v_a_1002_);
lean_dec(v_a_1002_);
if (v___x_1006_ == 0)
{
lean_object* v___x_1007_; lean_object* v___x_1009_; 
lean_dec_ref(v_arg_992_);
lean_dec_ref(v_arg_989_);
lean_dec_ref(v_e_962_);
v___x_1007_ = lean_box(0);
if (v_isShared_1005_ == 0)
{
lean_ctor_set(v___x_1004_, 0, v___x_1007_);
v___x_1009_ = v___x_1004_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1007_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
else
{
lean_object* v___x_1011_; 
lean_del_object(v___x_1004_);
lean_inc_ref(v_arg_992_);
v___x_1011_ = l_Lean_Meta_getIntValue_x3f(v_arg_992_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_a_1012_; 
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_a_1012_);
lean_dec_ref(v___x_1011_);
if (lean_obj_tag(v_a_1012_) == 1)
{
lean_object* v_val_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1078_; 
v_val_1013_ = lean_ctor_get(v_a_1012_, 0);
v_isSharedCheck_1078_ = !lean_is_exclusive(v_a_1012_);
if (v_isSharedCheck_1078_ == 0)
{
v___x_1015_ = v_a_1012_;
v_isShared_1016_ = v_isSharedCheck_1078_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_val_1013_);
lean_dec(v_a_1012_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1078_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1017_; 
lean_inc_ref(v_e_962_);
v___x_1017_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_962_, v_a_963_, v_a_967_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_object* v_a_1018_; uint8_t v___x_1019_; 
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
lean_inc(v_a_1018_);
lean_dec_ref(v___x_1017_);
v___x_1019_ = lean_unbox(v_a_1018_);
lean_dec(v_a_1018_);
if (v___x_1019_ == 0)
{
lean_object* v___x_1020_; 
lean_del_object(v___x_1015_);
lean_dec(v_val_1013_);
lean_inc_ref(v_e_962_);
v___x_1020_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_962_, v_a_963_, v_a_967_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
if (lean_obj_tag(v___x_1020_) == 0)
{
lean_object* v_a_1021_; lean_object* v___x_1023_; uint8_t v_isShared_1024_; uint8_t v_isSharedCheck_1046_; 
v_a_1021_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1046_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1046_ == 0)
{
v___x_1023_ = v___x_1020_;
v_isShared_1024_ = v_isSharedCheck_1046_;
goto v_resetjp_1022_;
}
else
{
lean_inc(v_a_1021_);
lean_dec(v___x_1020_);
v___x_1023_ = lean_box(0);
v_isShared_1024_ = v_isSharedCheck_1046_;
goto v_resetjp_1022_;
}
v_resetjp_1022_:
{
uint8_t v___x_1025_; 
v___x_1025_ = lean_unbox(v_a_1021_);
lean_dec(v_a_1021_);
if (v___x_1025_ == 0)
{
lean_object* v___x_1026_; lean_object* v___x_1028_; 
lean_dec_ref(v_arg_992_);
lean_dec_ref(v_arg_989_);
lean_dec_ref(v_e_962_);
v___x_1026_ = lean_box(0);
if (v_isShared_1024_ == 0)
{
lean_ctor_set(v___x_1023_, 0, v___x_1026_);
v___x_1028_ = v___x_1023_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v___x_1026_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
else
{
lean_object* v___x_1030_; 
lean_del_object(v___x_1023_);
lean_inc_ref(v_e_962_);
v___x_1030_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
if (lean_obj_tag(v___x_1030_) == 0)
{
lean_object* v_a_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v_a_1031_ = lean_ctor_get(v___x_1030_, 0);
lean_inc(v_a_1031_);
lean_dec_ref(v___x_1030_);
v___x_1032_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7);
v___x_1033_ = l_Lean_eagerReflBoolTrue;
v___x_1034_ = l_Lean_Meta_mkOfEqFalseCore(v_e_962_, v_a_1031_);
v___x_1035_ = l_Lean_mkApp4(v___x_1032_, v_arg_992_, v_arg_989_, v___x_1033_, v___x_1034_);
v___x_1036_ = lean_unsigned_to_nat(0u);
v___x_1037_ = l_Lean_Meta_Grind_pushNewFact(v___x_1035_, v___x_1036_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
return v___x_1037_;
}
else
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1045_; 
lean_dec_ref(v_arg_992_);
lean_dec_ref(v_arg_989_);
lean_dec_ref(v_e_962_);
v_a_1038_ = lean_ctor_get(v___x_1030_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1030_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1040_ = v___x_1030_;
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1030_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v___x_1043_; 
if (v_isShared_1041_ == 0)
{
v___x_1043_ = v___x_1040_;
goto v_reusejp_1042_;
}
else
{
lean_object* v_reuseFailAlloc_1044_; 
v_reuseFailAlloc_1044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1044_, 0, v_a_1038_);
v___x_1043_ = v_reuseFailAlloc_1044_;
goto v_reusejp_1042_;
}
v_reusejp_1042_:
{
return v___x_1043_;
}
}
}
}
}
}
else
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
lean_dec_ref(v_arg_992_);
lean_dec_ref(v_arg_989_);
lean_dec_ref(v_e_962_);
v_a_1047_ = lean_ctor_get(v___x_1020_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1020_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1049_ = v___x_1020_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1020_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1047_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
else
{
lean_object* v___x_1055_; 
lean_dec_ref(v_arg_992_);
v___x_1055_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(v_arg_989_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
if (lean_obj_tag(v___x_1055_) == 0)
{
lean_object* v_a_1056_; lean_object* v___x_1058_; 
v_a_1056_ = lean_ctor_get(v___x_1055_, 0);
lean_inc(v_a_1056_);
lean_dec_ref(v___x_1055_);
if (v_isShared_1016_ == 0)
{
lean_ctor_set_tag(v___x_1015_, 0);
lean_ctor_set(v___x_1015_, 0, v_e_962_);
v___x_1058_ = v___x_1015_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_e_962_);
v___x_1058_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1059_, 0, v_val_1013_);
lean_ctor_set(v___x_1059_, 1, v_a_1056_);
lean_ctor_set(v___x_1059_, 2, v___x_1058_);
v___x_1060_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v___x_1059_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
return v___x_1060_;
}
}
else
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1069_; 
lean_del_object(v___x_1015_);
lean_dec(v_val_1013_);
lean_dec_ref(v_e_962_);
v_a_1062_ = lean_ctor_get(v___x_1055_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1055_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1064_ = v___x_1055_;
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1055_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
if (v_isShared_1065_ == 0)
{
v___x_1067_ = v___x_1064_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_a_1062_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
}
else
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1077_; 
lean_del_object(v___x_1015_);
lean_dec(v_val_1013_);
lean_dec_ref(v_arg_992_);
lean_dec_ref(v_arg_989_);
lean_dec_ref(v_e_962_);
v_a_1070_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1072_ = v___x_1017_;
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1017_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1075_; 
if (v_isShared_1073_ == 0)
{
v___x_1075_ = v___x_1072_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_a_1070_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
}
}
else
{
lean_object* v___x_1079_; 
lean_dec(v_a_1012_);
lean_dec_ref(v_arg_992_);
lean_dec_ref(v_arg_989_);
v___x_1079_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_965_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; uint8_t v_verbose_1081_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc(v_a_1080_);
lean_dec_ref(v___x_1079_);
v_verbose_1081_ = lean_ctor_get_uint8(v_a_1080_, sizeof(void*)*11 + 15);
lean_dec(v_a_1080_);
if (v_verbose_1081_ == 0)
{
lean_dec_ref(v_e_962_);
goto v___jp_974_;
}
else
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1082_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9);
v___x_1083_ = l_Lean_indentExpr(v_e_962_);
v___x_1084_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1082_);
lean_ctor_set(v___x_1084_, 1, v___x_1083_);
v___x_1085_ = l_Lean_Meta_Grind_reportIssue(v___x_1084_, v_a_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_, v_a_969_, v_a_970_, v_a_971_, v_a_972_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_dec_ref(v___x_1085_);
goto v___jp_974_;
}
else
{
return v___x_1085_;
}
}
}
else
{
lean_object* v_a_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1093_; 
lean_dec_ref(v_e_962_);
v_a_1086_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1093_ == 0)
{
v___x_1088_ = v___x_1079_;
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_a_1086_);
lean_dec(v___x_1079_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1091_; 
if (v_isShared_1089_ == 0)
{
v___x_1091_ = v___x_1088_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_a_1086_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
}
}
else
{
lean_object* v_a_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1101_; 
lean_dec_ref(v_arg_992_);
lean_dec_ref(v_arg_989_);
lean_dec_ref(v_e_962_);
v_a_1094_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1096_ = v___x_1011_;
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_a_1094_);
lean_dec(v___x_1011_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1099_; 
if (v_isShared_1097_ == 0)
{
v___x_1099_ = v___x_1096_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_a_1094_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
}
}
}
else
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1110_; 
lean_dec_ref(v_arg_992_);
lean_dec_ref(v_arg_989_);
lean_dec_ref(v_e_962_);
v_a_1103_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1105_ = v___x_1001_;
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1001_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
if (v_isShared_1106_ == 0)
{
v___x_1108_ = v___x_1105_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_a_1103_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
}
}
}
}
v___jp_982_:
{
lean_object* v___x_983_; lean_object* v___x_985_; 
v___x_983_ = lean_box(0);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 0, v___x_983_);
v___x_985_ = v___x_980_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v___x_983_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
}
else
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1119_; 
lean_dec_ref(v_e_962_);
v_a_1112_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1114_ = v___x_977_;
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_977_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1117_; 
if (v_isShared_1115_ == 0)
{
v___x_1117_ = v___x_1114_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_a_1112_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
v___jp_974_:
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = lean_box(0);
v___x_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_976_, 0, v___x_975_);
return v___x_976_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___boxed(lean_object* v_e_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_, lean_object* v_a_1124_, lean_object* v_a_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_, lean_object* v_a_1128_, lean_object* v_a_1129_, lean_object* v_a_1130_, lean_object* v_a_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(v_e_1120_, v_a_1121_, v_a_1122_, v_a_1123_, v_a_1124_, v_a_1125_, v_a_1126_, v_a_1127_, v_a_1128_, v_a_1129_, v_a_1130_);
lean_dec(v_a_1130_);
lean_dec_ref(v_a_1129_);
lean_dec(v_a_1128_);
lean_dec_ref(v_a_1127_);
lean_dec(v_a_1126_);
lean_dec_ref(v_a_1125_);
lean_dec(v_a_1124_);
lean_dec_ref(v_a_1123_);
lean_dec(v_a_1122_);
lean_dec(v_a_1121_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd_spec__0(lean_object* v_a_1133_){
_start:
{
lean_object* v___x_1134_; 
v___x_1134_ = lean_nat_to_int(v_a_1133_);
return v___x_1134_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3(void){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1140_ = lean_box(0);
v___x_1141_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2));
v___x_1142_ = l_Lean_mkConst(v___x_1141_, v___x_1140_);
return v___x_1142_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7(void){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1149_ = lean_box(0);
v___x_1150_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6));
v___x_1151_ = l_Lean_mkConst(v___x_1150_, v___x_1149_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(lean_object* v_e_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_, lean_object* v_a_1158_, lean_object* v_a_1159_, lean_object* v_a_1160_, lean_object* v_a_1161_, lean_object* v_a_1162_){
_start:
{
lean_object* v___x_1170_; uint8_t v___x_1171_; 
lean_inc_ref(v_e_1152_);
v___x_1170_ = l_Lean_Expr_cleanupAnnotations(v_e_1152_);
v___x_1171_ = l_Lean_Expr_isApp(v___x_1170_);
if (v___x_1171_ == 0)
{
lean_dec_ref(v___x_1170_);
lean_dec_ref(v_e_1152_);
goto v___jp_1164_;
}
else
{
lean_object* v_arg_1172_; lean_object* v___x_1173_; uint8_t v___x_1174_; 
v_arg_1172_ = lean_ctor_get(v___x_1170_, 1);
lean_inc_ref(v_arg_1172_);
v___x_1173_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1170_);
v___x_1174_ = l_Lean_Expr_isApp(v___x_1173_);
if (v___x_1174_ == 0)
{
lean_dec_ref(v___x_1173_);
lean_dec_ref(v_arg_1172_);
lean_dec_ref(v_e_1152_);
goto v___jp_1164_;
}
else
{
lean_object* v_arg_1175_; lean_object* v___x_1176_; uint8_t v___x_1177_; 
v_arg_1175_ = lean_ctor_get(v___x_1173_, 1);
lean_inc_ref(v_arg_1175_);
v___x_1176_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1173_);
v___x_1177_ = l_Lean_Expr_isApp(v___x_1176_);
if (v___x_1177_ == 0)
{
lean_dec_ref(v___x_1176_);
lean_dec_ref(v_arg_1175_);
lean_dec_ref(v_arg_1172_);
lean_dec_ref(v_e_1152_);
goto v___jp_1164_;
}
else
{
lean_object* v_arg_1178_; lean_object* v___x_1179_; uint8_t v___x_1180_; 
v_arg_1178_ = lean_ctor_get(v___x_1176_, 1);
lean_inc_ref(v_arg_1178_);
v___x_1179_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1176_);
v___x_1180_ = l_Lean_Expr_isApp(v___x_1179_);
if (v___x_1180_ == 0)
{
lean_dec_ref(v___x_1179_);
lean_dec_ref(v_arg_1178_);
lean_dec_ref(v_arg_1175_);
lean_dec_ref(v_arg_1172_);
lean_dec_ref(v_e_1152_);
goto v___jp_1164_;
}
else
{
lean_object* v___x_1181_; lean_object* v___x_1182_; uint8_t v___x_1183_; 
v___x_1181_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1179_);
v___x_1182_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1183_ = l_Lean_Expr_isConstOf(v___x_1181_, v___x_1182_);
lean_dec_ref(v___x_1181_);
if (v___x_1183_ == 0)
{
lean_dec_ref(v_arg_1178_);
lean_dec_ref(v_arg_1175_);
lean_dec_ref(v_arg_1172_);
lean_dec_ref(v_e_1152_);
goto v___jp_1164_;
}
else
{
lean_object* v___x_1184_; 
v___x_1184_ = l_Lean_Meta_Structural_isInstDvdNat___redArg(v_arg_1178_, v_a_1160_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_object* v_a_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1316_; 
v_a_1185_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1187_ = v___x_1184_;
v_isShared_1188_ = v_isSharedCheck_1316_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_a_1185_);
lean_dec(v___x_1184_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1316_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
uint8_t v___x_1189_; 
v___x_1189_ = lean_unbox(v_a_1185_);
lean_dec(v_a_1185_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1190_; lean_object* v___x_1192_; 
lean_dec_ref(v_arg_1175_);
lean_dec_ref(v_arg_1172_);
lean_dec_ref(v_e_1152_);
v___x_1190_ = lean_box(0);
if (v_isShared_1188_ == 0)
{
lean_ctor_set(v___x_1187_, 0, v___x_1190_);
v___x_1192_ = v___x_1187_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v___x_1190_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
else
{
lean_object* v___x_1194_; 
lean_del_object(v___x_1187_);
v___x_1194_ = l_Lean_Meta_getNatValue_x3f(v_arg_1175_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1195_; 
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_a_1195_);
lean_dec_ref(v___x_1194_);
if (lean_obj_tag(v_a_1195_) == 1)
{
lean_object* v_val_1196_; lean_object* v___x_1197_; 
v_val_1196_ = lean_ctor_get(v_a_1195_, 0);
lean_inc(v_val_1196_);
lean_dec_ref(v_a_1195_);
lean_inc_ref(v_e_1152_);
v___x_1197_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_1152_, v_a_1153_, v_a_1157_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_);
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_object* v_a_1198_; uint8_t v___x_1199_; 
v_a_1198_ = lean_ctor_get(v___x_1197_, 0);
lean_inc(v_a_1198_);
lean_dec_ref(v___x_1197_);
v___x_1199_ = lean_unbox(v_a_1198_);
lean_dec(v_a_1198_);
if (v___x_1199_ == 0)
{
lean_object* v___x_1200_; 
lean_dec(v_val_1196_);
lean_inc_ref(v_e_1152_);
v___x_1200_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_1152_, v_a_1153_, v_a_1157_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_);
if (lean_obj_tag(v___x_1200_) == 0)
{
lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1225_; 
v_a_1201_ = lean_ctor_get(v___x_1200_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1203_ = v___x_1200_;
v_isShared_1204_ = v_isSharedCheck_1225_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v___x_1200_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1225_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
uint8_t v___x_1205_; 
v___x_1205_ = lean_unbox(v_a_1201_);
lean_dec(v_a_1201_);
if (v___x_1205_ == 0)
{
lean_object* v___x_1206_; lean_object* v___x_1208_; 
lean_dec_ref(v_arg_1175_);
lean_dec_ref(v_arg_1172_);
lean_dec_ref(v_e_1152_);
v___x_1206_ = lean_box(0);
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 0, v___x_1206_);
v___x_1208_ = v___x_1203_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v___x_1206_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
else
{
lean_object* v___x_1210_; 
lean_del_object(v___x_1203_);
lean_inc_ref(v_e_1152_);
v___x_1210_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v_a_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
lean_inc(v_a_1211_);
lean_dec_ref(v___x_1210_);
v___x_1212_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3);
v___x_1213_ = l_Lean_Meta_mkOfEqFalseCore(v_e_1152_, v_a_1211_);
v___x_1214_ = l_Lean_mkApp3(v___x_1212_, v_arg_1175_, v_arg_1172_, v___x_1213_);
v___x_1215_ = lean_unsigned_to_nat(0u);
v___x_1216_ = l_Lean_Meta_Grind_pushNewFact(v___x_1214_, v___x_1215_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_);
return v___x_1216_;
}
else
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1224_; 
lean_dec_ref(v_arg_1175_);
lean_dec_ref(v_arg_1172_);
lean_dec_ref(v_e_1152_);
v_a_1217_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1219_ = v___x_1210_;
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v___x_1210_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1222_; 
if (v_isShared_1220_ == 0)
{
v___x_1222_ = v___x_1219_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_a_1217_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
}
}
else
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
lean_dec_ref(v_arg_1175_);
lean_dec_ref(v_arg_1172_);
lean_dec_ref(v_e_1152_);
v_a_1226_ = lean_ctor_get(v___x_1200_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1228_ = v___x_1200_;
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1200_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1226_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
else
{
lean_object* v___x_1234_; 
lean_inc_ref(v_arg_1175_);
v___x_1234_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_1175_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_);
if (lean_obj_tag(v___x_1234_) == 0)
{
lean_object* v_a_1235_; lean_object* v_fst_1236_; lean_object* v_snd_1237_; lean_object* v___x_1238_; 
v_a_1235_ = lean_ctor_get(v___x_1234_, 0);
lean_inc(v_a_1235_);
lean_dec_ref(v___x_1234_);
v_fst_1236_ = lean_ctor_get(v_a_1235_, 0);
lean_inc(v_fst_1236_);
v_snd_1237_ = lean_ctor_get(v_a_1235_, 1);
lean_inc(v_snd_1237_);
lean_dec(v_a_1235_);
lean_inc_ref(v_arg_1172_);
v___x_1238_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_1172_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; lean_object* v_fst_1240_; lean_object* v_snd_1241_; lean_object* v___x_1242_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_a_1239_);
lean_dec_ref(v___x_1238_);
v_fst_1240_ = lean_ctor_get(v_a_1239_, 0);
lean_inc(v_fst_1240_);
v_snd_1241_ = lean_ctor_get(v_a_1239_, 1);
lean_inc(v_snd_1241_);
lean_dec(v_a_1239_);
v___x_1242_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1152_, v_a_1153_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v_a_1243_; lean_object* v___x_1244_; 
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
lean_inc(v_a_1243_);
lean_dec_ref(v___x_1242_);
lean_inc(v_fst_1240_);
v___x_1244_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_1240_, v_a_1243_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v_a_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_a_1245_);
lean_dec_ref(v___x_1244_);
v___x_1246_ = l_Int_Linear_Expr_norm(v_a_1245_);
v___x_1247_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7);
v___x_1248_ = l_Lean_mkApp6(v___x_1247_, v_arg_1175_, v_arg_1172_, v_fst_1236_, v_fst_1240_, v_snd_1237_, v_snd_1241_);
lean_inc(v_val_1196_);
v___x_1249_ = lean_nat_to_int(v_val_1196_);
v___x_1250_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1250_, 0, v_e_1152_);
lean_ctor_set(v___x_1250_, 1, v___x_1248_);
lean_ctor_set(v___x_1250_, 2, v_val_1196_);
lean_ctor_set(v___x_1250_, 3, v_a_1245_);
v___x_1251_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1251_, 0, v___x_1249_);
lean_ctor_set(v___x_1251_, 1, v___x_1246_);
lean_ctor_set(v___x_1251_, 2, v___x_1250_);
v___x_1252_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v___x_1251_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_);
return v___x_1252_;
}
else
{
lean_object* v_a_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1260_; 
lean_dec(v_snd_1241_);
lean_dec(v_fst_1240_);
lean_dec(v_snd_1237_);
lean_dec(v_fst_1236_);
lean_dec(v_val_1196_);
lean_dec_ref(v_arg_1175_);
lean_dec_ref(v_arg_1172_);
lean_dec_ref(v_e_1152_);
v_a_1253_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1255_ = v___x_1244_;
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_a_1253_);
lean_dec(v___x_1244_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1258_; 
if (v_isShared_1256_ == 0)
{
v___x_1258_ = v___x_1255_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_a_1253_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
else
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1268_; 
lean_dec(v_snd_1241_);
lean_dec(v_fst_1240_);
lean_dec(v_snd_1237_);
lean_dec(v_fst_1236_);
lean_dec(v_val_1196_);
lean_dec_ref(v_arg_1175_);
lean_dec_ref(v_arg_1172_);
lean_dec_ref(v_e_1152_);
v_a_1261_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1263_ = v___x_1242_;
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1242_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1264_ == 0)
{
v___x_1266_ = v___x_1263_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_a_1261_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
}
else
{
lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1276_; 
lean_dec(v_snd_1237_);
lean_dec(v_fst_1236_);
lean_dec(v_val_1196_);
lean_dec_ref(v_arg_1175_);
lean_dec_ref(v_arg_1172_);
lean_dec_ref(v_e_1152_);
v_a_1269_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1271_ = v___x_1238_;
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1238_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1274_; 
if (v_isShared_1272_ == 0)
{
v___x_1274_ = v___x_1271_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_a_1269_);
v___x_1274_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
return v___x_1274_;
}
}
}
}
else
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1284_; 
lean_dec(v_val_1196_);
lean_dec_ref(v_arg_1175_);
lean_dec_ref(v_arg_1172_);
lean_dec_ref(v_e_1152_);
v_a_1277_ = lean_ctor_get(v___x_1234_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1279_ = v___x_1234_;
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v___x_1234_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1282_; 
if (v_isShared_1280_ == 0)
{
v___x_1282_ = v___x_1279_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v_a_1277_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
}
}
else
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
lean_dec(v_val_1196_);
lean_dec_ref(v_arg_1175_);
lean_dec_ref(v_arg_1172_);
lean_dec_ref(v_e_1152_);
v_a_1285_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1197_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1197_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1285_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
else
{
lean_object* v___x_1293_; 
lean_dec(v_a_1195_);
lean_dec_ref(v_arg_1175_);
lean_dec_ref(v_arg_1172_);
v___x_1293_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1155_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v_a_1294_; uint8_t v_verbose_1295_; 
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_a_1294_);
lean_dec_ref(v___x_1293_);
v_verbose_1295_ = lean_ctor_get_uint8(v_a_1294_, sizeof(void*)*11 + 15);
lean_dec(v_a_1294_);
if (v_verbose_1295_ == 0)
{
lean_dec_ref(v_e_1152_);
goto v___jp_1167_;
}
else
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1296_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9);
v___x_1297_ = l_Lean_indentExpr(v_e_1152_);
v___x_1298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1298_, 0, v___x_1296_);
lean_ctor_set(v___x_1298_, 1, v___x_1297_);
v___x_1299_ = l_Lean_Meta_Grind_reportIssue(v___x_1298_, v_a_1154_, v_a_1155_, v_a_1156_, v_a_1157_, v_a_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_);
if (lean_obj_tag(v___x_1299_) == 0)
{
lean_dec_ref(v___x_1299_);
goto v___jp_1167_;
}
else
{
return v___x_1299_;
}
}
}
else
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1307_; 
lean_dec_ref(v_e_1152_);
v_a_1300_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1302_ = v___x_1293_;
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_dec(v___x_1293_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_a_1300_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
}
else
{
lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1315_; 
lean_dec_ref(v_arg_1175_);
lean_dec_ref(v_arg_1172_);
lean_dec_ref(v_e_1152_);
v_a_1308_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1310_ = v___x_1194_;
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v___x_1194_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1313_; 
if (v_isShared_1311_ == 0)
{
v___x_1313_ = v___x_1310_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_a_1308_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
}
}
}
}
else
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1324_; 
lean_dec_ref(v_arg_1175_);
lean_dec_ref(v_arg_1172_);
lean_dec_ref(v_e_1152_);
v_a_1317_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1319_ = v___x_1184_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1184_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_a_1317_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
}
}
}
}
v___jp_1164_:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1165_ = lean_box(0);
v___x_1166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1166_, 0, v___x_1165_);
return v___x_1166_;
}
v___jp_1167_:
{
lean_object* v___x_1168_; lean_object* v___x_1169_; 
v___x_1168_ = lean_box(0);
v___x_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1168_);
return v___x_1169_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___boxed(lean_object* v_e_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(v_e_1325_, v_a_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_);
lean_dec(v_a_1335_);
lean_dec_ref(v_a_1334_);
lean_dec(v_a_1333_);
lean_dec_ref(v_a_1332_);
lean_dec(v_a_1331_);
lean_dec_ref(v_a_1330_);
lean_dec(v_a_1329_);
lean_dec_ref(v_a_1328_);
lean_dec(v_a_1327_);
lean_dec(v_a_1326_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(lean_object* v_e_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_){
_start:
{
lean_object* v___x_1352_; 
v___x_1352_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1343_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1397_; 
v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1397_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1397_ == 0)
{
v___x_1355_ = v___x_1352_;
v_isShared_1356_ = v_isSharedCheck_1397_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1352_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1397_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
uint8_t v_lia_1357_; 
v_lia_1357_ = lean_ctor_get_uint8(v_a_1353_, sizeof(void*)*11 + 23);
lean_dec(v_a_1353_);
if (v_lia_1357_ == 0)
{
lean_object* v___x_1358_; lean_object* v___x_1360_; 
lean_dec_ref(v_e_1340_);
v___x_1358_ = lean_box(0);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 0, v___x_1358_);
v___x_1360_ = v___x_1355_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v___x_1358_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
else
{
lean_object* v___x_1362_; 
lean_del_object(v___x_1355_);
lean_inc_ref(v_e_1340_);
v___x_1362_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1340_, v_a_1348_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1388_; 
v_a_1363_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1365_ = v___x_1362_;
v_isShared_1366_ = v_isSharedCheck_1388_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1362_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1388_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1372_; uint8_t v___x_1373_; 
v___x_1372_ = l_Lean_Expr_cleanupAnnotations(v_a_1363_);
v___x_1373_ = l_Lean_Expr_isApp(v___x_1372_);
if (v___x_1373_ == 0)
{
lean_dec_ref(v___x_1372_);
lean_dec_ref(v_e_1340_);
goto v___jp_1367_;
}
else
{
lean_object* v___x_1374_; uint8_t v___x_1375_; 
v___x_1374_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1372_);
v___x_1375_ = l_Lean_Expr_isApp(v___x_1374_);
if (v___x_1375_ == 0)
{
lean_dec_ref(v___x_1374_);
lean_dec_ref(v_e_1340_);
goto v___jp_1367_;
}
else
{
lean_object* v___x_1376_; uint8_t v___x_1377_; 
v___x_1376_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1374_);
v___x_1377_ = l_Lean_Expr_isApp(v___x_1376_);
if (v___x_1377_ == 0)
{
lean_dec_ref(v___x_1376_);
lean_dec_ref(v_e_1340_);
goto v___jp_1367_;
}
else
{
lean_object* v___x_1378_; uint8_t v___x_1379_; 
v___x_1378_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1376_);
v___x_1379_ = l_Lean_Expr_isApp(v___x_1378_);
if (v___x_1379_ == 0)
{
lean_dec_ref(v___x_1378_);
lean_dec_ref(v_e_1340_);
goto v___jp_1367_;
}
else
{
lean_object* v_arg_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; uint8_t v___x_1383_; 
v_arg_1380_ = lean_ctor_get(v___x_1378_, 1);
lean_inc_ref(v_arg_1380_);
v___x_1381_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1378_);
v___x_1382_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1383_ = l_Lean_Expr_isConstOf(v___x_1381_, v___x_1382_);
lean_dec_ref(v___x_1381_);
if (v___x_1383_ == 0)
{
lean_dec_ref(v_arg_1380_);
lean_dec_ref(v_e_1340_);
goto v___jp_1367_;
}
else
{
lean_object* v___x_1384_; uint8_t v___x_1385_; 
lean_del_object(v___x_1365_);
v___x_1384_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0));
v___x_1385_ = l_Lean_Expr_isConstOf(v_arg_1380_, v___x_1384_);
lean_dec_ref(v_arg_1380_);
if (v___x_1385_ == 0)
{
lean_object* v___x_1386_; 
v___x_1386_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(v_e_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_);
return v___x_1386_;
}
else
{
lean_object* v___x_1387_; 
v___x_1387_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(v_e_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_);
return v___x_1387_;
}
}
}
}
}
}
v___jp_1367_:
{
lean_object* v___x_1368_; lean_object* v___x_1370_; 
v___x_1368_ = lean_box(0);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 0, v___x_1368_);
v___x_1370_ = v___x_1365_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v___x_1368_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
else
{
lean_object* v_a_1389_; lean_object* v___x_1391_; uint8_t v_isShared_1392_; uint8_t v_isSharedCheck_1396_; 
lean_dec_ref(v_e_1340_);
v_a_1389_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1396_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1391_ = v___x_1362_;
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
else
{
lean_inc(v_a_1389_);
lean_dec(v___x_1362_);
v___x_1391_ = lean_box(0);
v_isShared_1392_ = v_isSharedCheck_1396_;
goto v_resetjp_1390_;
}
v_resetjp_1390_:
{
lean_object* v___x_1394_; 
if (v_isShared_1392_ == 0)
{
v___x_1394_ = v___x_1391_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1395_; 
v_reuseFailAlloc_1395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1395_, 0, v_a_1389_);
v___x_1394_ = v_reuseFailAlloc_1395_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
return v___x_1394_;
}
}
}
}
}
}
else
{
lean_object* v_a_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1405_; 
lean_dec_ref(v_e_1340_);
v_a_1398_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1405_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1405_ == 0)
{
v___x_1400_ = v___x_1352_;
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_a_1398_);
lean_dec(v___x_1352_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1405_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1403_; 
if (v_isShared_1401_ == 0)
{
v___x_1403_ = v___x_1400_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v_a_1398_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed(lean_object* v_e_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_, lean_object* v_a_1411_, lean_object* v_a_1412_, lean_object* v_a_1413_, lean_object* v_a_1414_, lean_object* v_a_1415_, lean_object* v_a_1416_, lean_object* v_a_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(v_e_1406_, v_a_1407_, v_a_1408_, v_a_1409_, v_a_1410_, v_a_1411_, v_a_1412_, v_a_1413_, v_a_1414_, v_a_1415_, v_a_1416_);
lean_dec(v_a_1416_);
lean_dec_ref(v_a_1415_);
lean_dec(v_a_1414_);
lean_dec_ref(v_a_1413_);
lean_dec(v_a_1412_);
lean_dec_ref(v_a_1411_);
lean_dec(v_a_1410_);
lean_dec_ref(v_a_1409_);
lean_dec(v_a_1408_);
lean_dec(v_a_1407_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1420_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1421_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed), 12, 0);
v___x_1422_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_1420_, v___x_1421_);
return v___x_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_8____boxed(lean_object* v_a_1423_){
_start:
{
lean_object* v_res_1424_; 
v_res_1424_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_8_();
return v_res_1424_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Propagator(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Proof(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Dvd(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_OfNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Propagator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Simp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Proof(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_NatInstTesters(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Dvd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin);
lean_object* initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* initialize_Init_Grind_Propagator(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Proof(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(uint8_t builtin);
lean_object* initialize_Lean_Meta_NatInstTesters(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Dvd(uint8_t builtin);
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
res = initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Dvd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(builtin);
}
#ifdef __cplusplus
}
#endif
