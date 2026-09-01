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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_eagerReflBoolTrue;
lean_object* l_Lean_Meta_mkOfEqFalseCore(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_pushNewFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_normCommRing_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_updateOccs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_gcdExt(lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_mul(lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_combine(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_getConst(lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_div(lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_gcdCoeffs(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
uint8_t l_Int_Internal_Linear_Poly_isSorted(lean_object*);
lean_object* l_Int_Internal_Linear_Poly_norm(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_findVarToSubst___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_coeff(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t l_Int_Internal_Linear_Poly_isUnsatDvd(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_set___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqLBool_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(lean_object*, lean_object*);
lean_object* lean_grind_cutsat_assert_eq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstDvdNat___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_natToInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Expr_norm(lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__5_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "store"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "trivial"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "unsat"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "assert"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2_value),LEAN_SCALAR_PTR_LITERAL(24, 23, 180, 58, 194, 72, 175, 153)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3_value),LEAN_SCALAR_PTR_LITERAL(198, 137, 50, 202, 239, 114, 140, 141)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5;
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
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linear"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "of_not_dvd"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__3_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__4_value),LEAN_SCALAR_PTR_LITERAL(80, 75, 231, 118, 66, 61, 134, 150)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__5_value),LEAN_SCALAR_PTR_LITERAL(57, 190, 3, 113, 15, 121, 86, 21)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__6_value),LEAN_SCALAR_PTR_LITERAL(4, 93, 162, 5, 159, 42, 23, 43)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "non-linear divisibility constraint found"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_9_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_9____boxed(lean_object*);
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
lean_object* v___y_7_; lean_object* v___y_8_; lean_object* v___y_9_; lean_object* v___y_10_; lean_object* v___y_11_; lean_object* v___y_22_; lean_object* v_d_23_; lean_object* v_p_24_; lean_object* v_d_29_; lean_object* v_p_30_; uint8_t v___x_31_; 
v_d_29_ = lean_ctor_get(v_c_5_, 0);
lean_inc(v_d_29_);
v_p_30_ = lean_ctor_get(v_c_5_, 1);
v___x_31_ = l_Int_Internal_Linear_Poly_isSorted(v_p_30_);
if (v___x_31_ == 0)
{
lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
lean_inc_ref(v_p_30_);
v___x_32_ = l_Int_Internal_Linear_Poly_norm(v_p_30_);
v___x_33_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_33_, 0, v_c_5_);
lean_inc_ref(v___x_32_);
lean_inc(v_d_29_);
v___x_34_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_34_, 0, v_d_29_);
lean_ctor_set(v___x_34_, 1, v___x_32_);
lean_ctor_set(v___x_34_, 2, v___x_33_);
v___y_22_ = v___x_34_;
v_d_23_ = v_d_29_;
v_p_24_ = v___x_32_;
goto v___jp_21_;
}
else
{
lean_inc_ref(v_p_30_);
v___y_22_ = v_c_5_;
v_d_23_ = v_d_29_;
v_p_24_ = v_p_30_;
goto v___jp_21_;
}
v___jp_6_:
{
lean_object* v___x_12_; lean_object* v___x_13_; uint8_t v___x_14_; 
v___x_12_ = l_Int_Internal_Linear_Poly_getConst(v___y_9_);
v___x_13_ = lean_int_emod(v___x_12_, v___y_11_);
lean_dec(v___x_12_);
v___x_14_ = lean_int_dec_eq(v___x_13_, v___y_10_);
lean_dec(v___x_13_);
if (v___x_14_ == 0)
{
lean_dec(v___y_11_);
lean_dec_ref(v___y_9_);
lean_dec(v___y_8_);
return v___y_7_;
}
else
{
lean_object* v___x_15_; uint8_t v___x_16_; 
v___x_15_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0);
v___x_16_ = lean_int_dec_eq(v___y_11_, v___x_15_);
if (v___x_16_ == 0)
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; lean_object* v___x_20_; 
v___x_17_ = lean_int_ediv(v___y_8_, v___y_11_);
lean_dec(v___y_8_);
v___x_18_ = l_Int_Internal_Linear_Poly_div(v___y_11_, v___y_9_);
lean_dec(v___y_11_);
v___x_19_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_19_, 0, v___y_7_);
v___x_20_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_20_, 0, v___x_17_);
lean_ctor_set(v___x_20_, 1, v___x_18_);
lean_ctor_set(v___x_20_, 2, v___x_19_);
return v___x_20_;
}
else
{
lean_dec(v___y_11_);
lean_dec_ref(v___y_9_);
lean_dec(v___y_8_);
return v___y_7_;
}
}
}
v___jp_21_:
{
lean_object* v_g_25_; lean_object* v___x_26_; uint8_t v___x_27_; 
lean_inc(v_d_23_);
v_g_25_ = l_Int_Internal_Linear_Poly_gcdCoeffs(v_p_24_, v_d_23_);
v___x_26_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1);
v___x_27_ = lean_int_dec_lt(v_d_23_, v___x_26_);
if (v___x_27_ == 0)
{
v___y_7_ = v___y_22_;
v___y_8_ = v_d_23_;
v___y_9_ = v_p_24_;
v___y_10_ = v___x_26_;
v___y_11_ = v_g_25_;
goto v___jp_6_;
}
else
{
lean_object* v___x_28_; 
v___x_28_ = lean_int_neg(v_g_25_);
lean_dec(v_g_25_);
v___y_7_ = v___y_22_;
v___y_8_ = v_d_23_;
v___y_9_ = v_p_24_;
v___y_10_ = v___x_26_;
v___y_11_ = v___x_28_;
goto v___jp_6_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0_spec__0(lean_object* v_msgData_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_){
_start:
{
lean_object* v___x_41_; lean_object* v_env_42_; lean_object* v___x_43_; lean_object* v_mctx_44_; lean_object* v_lctx_45_; lean_object* v_options_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_41_ = lean_st_ref_get(v___y_39_);
v_env_42_ = lean_ctor_get(v___x_41_, 0);
lean_inc_ref(v_env_42_);
lean_dec(v___x_41_);
v___x_43_ = lean_st_ref_get(v___y_37_);
v_mctx_44_ = lean_ctor_get(v___x_43_, 0);
lean_inc_ref(v_mctx_44_);
lean_dec(v___x_43_);
v_lctx_45_ = lean_ctor_get(v___y_36_, 2);
v_options_46_ = lean_ctor_get(v___y_38_, 1);
lean_inc_ref(v_options_46_);
lean_inc_ref(v_lctx_45_);
v___x_47_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_47_, 0, v_env_42_);
lean_ctor_set(v___x_47_, 1, v_mctx_44_);
lean_ctor_set(v___x_47_, 2, v_lctx_45_);
lean_ctor_set(v___x_47_, 3, v_options_46_);
v___x_48_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
lean_ctor_set(v___x_48_, 1, v_msgData_35_);
v___x_49_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_49_, 0, v___x_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0_spec__0___boxed(lean_object* v_msgData_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v_res_56_; 
v_res_56_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0_spec__0(v_msgData_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
lean_dec(v___y_54_);
lean_dec_ref(v___y_53_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
return v_res_56_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_57_; double v___x_58_; 
v___x_57_ = lean_unsigned_to_nat(0u);
v___x_58_ = lean_float_of_nat(v___x_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(lean_object* v_cls_62_, lean_object* v_msg_63_, lean_object* v___y_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_){
_start:
{
lean_object* v_ref_69_; lean_object* v___x_70_; lean_object* v_a_71_; lean_object* v___x_73_; uint8_t v_isShared_74_; uint8_t v_isSharedCheck_115_; 
v_ref_69_ = lean_ctor_get(v___y_66_, 4);
v___x_70_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0_spec__0(v_msg_63_, v___y_64_, v___y_65_, v___y_66_, v___y_67_);
v_a_71_ = lean_ctor_get(v___x_70_, 0);
v_isSharedCheck_115_ = !lean_is_exclusive(v___x_70_);
if (v_isSharedCheck_115_ == 0)
{
v___x_73_ = v___x_70_;
v_isShared_74_ = v_isSharedCheck_115_;
goto v_resetjp_72_;
}
else
{
lean_inc(v_a_71_);
lean_dec(v___x_70_);
v___x_73_ = lean_box(0);
v_isShared_74_ = v_isSharedCheck_115_;
goto v_resetjp_72_;
}
v_resetjp_72_:
{
lean_object* v___x_75_; lean_object* v_traceState_76_; lean_object* v_env_77_; lean_object* v_nextMacroScope_78_; lean_object* v_ngen_79_; lean_object* v_auxDeclNGen_80_; lean_object* v_cache_81_; lean_object* v_messages_82_; lean_object* v_infoState_83_; lean_object* v_snapshotTasks_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_114_; 
v___x_75_ = lean_st_ref_take(v___y_67_);
v_traceState_76_ = lean_ctor_get(v___x_75_, 4);
v_env_77_ = lean_ctor_get(v___x_75_, 0);
v_nextMacroScope_78_ = lean_ctor_get(v___x_75_, 1);
v_ngen_79_ = lean_ctor_get(v___x_75_, 2);
v_auxDeclNGen_80_ = lean_ctor_get(v___x_75_, 3);
v_cache_81_ = lean_ctor_get(v___x_75_, 5);
v_messages_82_ = lean_ctor_get(v___x_75_, 6);
v_infoState_83_ = lean_ctor_get(v___x_75_, 7);
v_snapshotTasks_84_ = lean_ctor_get(v___x_75_, 8);
v_isSharedCheck_114_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_114_ == 0)
{
v___x_86_ = v___x_75_;
v_isShared_87_ = v_isSharedCheck_114_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_snapshotTasks_84_);
lean_inc(v_infoState_83_);
lean_inc(v_messages_82_);
lean_inc(v_cache_81_);
lean_inc(v_traceState_76_);
lean_inc(v_auxDeclNGen_80_);
lean_inc(v_ngen_79_);
lean_inc(v_nextMacroScope_78_);
lean_inc(v_env_77_);
lean_dec(v___x_75_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_114_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
uint64_t v_tid_88_; lean_object* v_traces_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_113_; 
v_tid_88_ = lean_ctor_get_uint64(v_traceState_76_, sizeof(void*)*1);
v_traces_89_ = lean_ctor_get(v_traceState_76_, 0);
v_isSharedCheck_113_ = !lean_is_exclusive(v_traceState_76_);
if (v_isSharedCheck_113_ == 0)
{
v___x_91_ = v_traceState_76_;
v_isShared_92_ = v_isSharedCheck_113_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_traces_89_);
lean_dec(v_traceState_76_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_113_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_93_; double v___x_94_; uint8_t v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_103_; 
v___x_93_ = lean_box(0);
v___x_94_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0);
v___x_95_ = 0;
v___x_96_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__1));
v___x_97_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_97_, 0, v_cls_62_);
lean_ctor_set(v___x_97_, 1, v___x_93_);
lean_ctor_set(v___x_97_, 2, v___x_96_);
lean_ctor_set_float(v___x_97_, sizeof(void*)*3, v___x_94_);
lean_ctor_set_float(v___x_97_, sizeof(void*)*3 + 8, v___x_94_);
lean_ctor_set_uint8(v___x_97_, sizeof(void*)*3 + 16, v___x_95_);
v___x_98_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__2));
v___x_99_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_99_, 0, v___x_97_);
lean_ctor_set(v___x_99_, 1, v_a_71_);
lean_ctor_set(v___x_99_, 2, v___x_98_);
lean_inc(v_ref_69_);
v___x_100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_100_, 0, v_ref_69_);
lean_ctor_set(v___x_100_, 1, v___x_99_);
v___x_101_ = l_Lean_PersistentArray_push___redArg(v_traces_89_, v___x_100_);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 0, v___x_101_);
v___x_103_ = v___x_91_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v___x_101_);
lean_ctor_set_uint64(v_reuseFailAlloc_112_, sizeof(void*)*1, v_tid_88_);
v___x_103_ = v_reuseFailAlloc_112_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
lean_object* v___x_105_; 
if (v_isShared_87_ == 0)
{
lean_ctor_set(v___x_86_, 4, v___x_103_);
v___x_105_ = v___x_86_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v_env_77_);
lean_ctor_set(v_reuseFailAlloc_111_, 1, v_nextMacroScope_78_);
lean_ctor_set(v_reuseFailAlloc_111_, 2, v_ngen_79_);
lean_ctor_set(v_reuseFailAlloc_111_, 3, v_auxDeclNGen_80_);
lean_ctor_set(v_reuseFailAlloc_111_, 4, v___x_103_);
lean_ctor_set(v_reuseFailAlloc_111_, 5, v_cache_81_);
lean_ctor_set(v_reuseFailAlloc_111_, 6, v_messages_82_);
lean_ctor_set(v_reuseFailAlloc_111_, 7, v_infoState_83_);
lean_ctor_set(v_reuseFailAlloc_111_, 8, v_snapshotTasks_84_);
v___x_105_ = v_reuseFailAlloc_111_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_109_; 
v___x_106_ = lean_st_ref_put(v___y_67_, v___x_105_);
v___x_107_ = lean_box(0);
if (v_isShared_74_ == 0)
{
lean_ctor_set(v___x_73_, 0, v___x_107_);
v___x_109_ = v___x_73_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v___x_107_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___boxed(lean_object* v_cls_116_, lean_object* v_msg_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v_cls_116_, v_msg_117_, v___y_118_, v___y_119_, v___y_120_, v___y_121_);
lean_dec(v___y_121_);
lean_dec_ref(v___y_120_);
lean_dec(v___y_119_);
lean_dec_ref(v___y_118_);
return v_res_123_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7(void){
_start:
{
lean_object* v_cls_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v_cls_136_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4));
v___x_137_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
v___x_138_ = l_Lean_Name_append(v___x_137_, v_cls_136_);
return v___x_138_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9(void){
_start:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__8));
v___x_141_ = l_Lean_stringToMessageData(v___x_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(lean_object* v_a_142_, lean_object* v_x_143_, lean_object* v_c_u2081_144_, lean_object* v_b_145_, lean_object* v_c_u2082_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_){
_start:
{
lean_object* v_options_158_; lean_object* v_p_159_; lean_object* v_d_160_; lean_object* v_p_161_; lean_object* v_toCold_162_; uint8_t v_hasTrace_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v_d_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v_p_170_; 
v_options_158_ = lean_ctor_get(v_a_155_, 1);
v_p_159_ = lean_ctor_get(v_c_u2081_144_, 0);
v_d_160_ = lean_ctor_get(v_c_u2082_146_, 0);
v_p_161_ = lean_ctor_get(v_c_u2082_146_, 1);
v_toCold_162_ = lean_ctor_get(v_a_155_, 0);
v_hasTrace_163_ = lean_ctor_get_uint8(v_options_158_, sizeof(void*)*1);
v___x_164_ = lean_int_mul(v_a_142_, v_d_160_);
v___x_165_ = lean_nat_abs(v___x_164_);
lean_dec(v___x_164_);
v_d_166_ = lean_nat_to_int(v___x_165_);
lean_inc_ref(v_p_161_);
v___x_167_ = l_Int_Internal_Linear_Poly_mul(v_p_161_, v_a_142_);
v___x_168_ = lean_int_neg(v_b_145_);
lean_inc_ref(v_p_159_);
v___x_169_ = l_Int_Internal_Linear_Poly_mul(v_p_159_, v___x_168_);
lean_dec(v___x_168_);
v_p_170_ = l_Int_Internal_Linear_Poly_combine(v___x_167_, v___x_169_);
if (v_hasTrace_163_ == 0)
{
goto v___jp_171_;
}
else
{
lean_object* v_inheritedTraceOptions_175_; lean_object* v_cls_176_; lean_object* v___x_177_; uint8_t v___x_178_; 
v_inheritedTraceOptions_175_ = lean_ctor_get(v_toCold_162_, 4);
v_cls_176_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4));
v___x_177_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7);
v___x_178_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_175_, v_options_158_, v___x_177_);
if (v___x_178_ == 0)
{
goto v___jp_171_;
}
else
{
lean_object* v___x_179_; 
v___x_179_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_x_143_, v_a_147_, v_a_155_);
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v_a_180_; lean_object* v___x_181_; 
v_a_180_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_a_180_);
lean_dec_ref_known(v___x_179_, 1);
lean_inc_ref(v_c_u2081_144_);
v___x_181_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_u2081_144_, v_a_147_, v_a_155_);
if (lean_obj_tag(v___x_181_) == 0)
{
lean_object* v_a_182_; lean_object* v___x_183_; 
v_a_182_ = lean_ctor_get(v___x_181_, 0);
lean_inc(v_a_182_);
lean_dec_ref_known(v___x_181_, 1);
lean_inc_ref(v_c_u2082_146_);
v___x_183_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_u2082_146_, v_a_147_, v_a_155_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v_a_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v_a_184_ = lean_ctor_get(v___x_183_, 0);
lean_inc(v_a_184_);
lean_dec_ref_known(v___x_183_, 1);
v___x_185_ = l_Lean_MessageData_ofExpr(v_a_180_);
v___x_186_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9);
v___x_187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_185_);
lean_ctor_set(v___x_187_, 1, v___x_186_);
v___x_188_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
lean_ctor_set(v___x_188_, 1, v_a_182_);
v___x_189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
lean_ctor_set(v___x_189_, 1, v___x_186_);
v___x_190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
lean_ctor_set(v___x_190_, 1, v_a_184_);
v___x_191_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v_cls_176_, v___x_190_, v_a_153_, v_a_154_, v_a_155_, v_a_156_);
if (lean_obj_tag(v___x_191_) == 0)
{
lean_dec_ref_known(v___x_191_, 1);
goto v___jp_171_;
}
else
{
lean_object* v_a_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_199_; 
lean_dec_ref(v_p_170_);
lean_dec(v_d_166_);
lean_dec_ref(v_c_u2082_146_);
lean_dec_ref(v_c_u2081_144_);
lean_dec(v_x_143_);
v_a_192_ = lean_ctor_get(v___x_191_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_191_);
if (v_isSharedCheck_199_ == 0)
{
v___x_194_ = v___x_191_;
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_a_192_);
lean_dec(v___x_191_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_197_; 
if (v_isShared_195_ == 0)
{
v___x_197_ = v___x_194_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_a_192_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
else
{
lean_object* v_a_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_207_; 
lean_dec(v_a_182_);
lean_dec(v_a_180_);
lean_dec_ref(v_p_170_);
lean_dec(v_d_166_);
lean_dec_ref(v_c_u2082_146_);
lean_dec_ref(v_c_u2081_144_);
lean_dec(v_x_143_);
v_a_200_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_207_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_207_ == 0)
{
v___x_202_ = v___x_183_;
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_a_200_);
lean_dec(v___x_183_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_207_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_205_; 
if (v_isShared_203_ == 0)
{
v___x_205_ = v___x_202_;
goto v_reusejp_204_;
}
else
{
lean_object* v_reuseFailAlloc_206_; 
v_reuseFailAlloc_206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_206_, 0, v_a_200_);
v___x_205_ = v_reuseFailAlloc_206_;
goto v_reusejp_204_;
}
v_reusejp_204_:
{
return v___x_205_;
}
}
}
}
else
{
lean_object* v_a_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_215_; 
lean_dec(v_a_180_);
lean_dec_ref(v_p_170_);
lean_dec(v_d_166_);
lean_dec_ref(v_c_u2082_146_);
lean_dec_ref(v_c_u2081_144_);
lean_dec(v_x_143_);
v_a_208_ = lean_ctor_get(v___x_181_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_215_ == 0)
{
v___x_210_ = v___x_181_;
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_a_208_);
lean_dec(v___x_181_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_215_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_213_; 
if (v_isShared_211_ == 0)
{
v___x_213_ = v___x_210_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_a_208_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
}
else
{
lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_223_; 
lean_dec_ref(v_p_170_);
lean_dec(v_d_166_);
lean_dec_ref(v_c_u2082_146_);
lean_dec_ref(v_c_u2081_144_);
lean_dec(v_x_143_);
v_a_216_ = lean_ctor_get(v___x_179_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_223_ == 0)
{
v___x_218_ = v___x_179_;
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_dec(v___x_179_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_221_; 
if (v_isShared_219_ == 0)
{
v___x_221_ = v___x_218_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_a_216_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
}
}
v___jp_171_:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_172_ = lean_alloc_ctor(8, 3, 0);
lean_ctor_set(v___x_172_, 0, v_x_143_);
lean_ctor_set(v___x_172_, 1, v_c_u2081_144_);
lean_ctor_set(v___x_172_, 2, v_c_u2082_146_);
v___x_173_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_173_, 0, v_d_166_);
lean_ctor_set(v___x_173_, 1, v_p_170_);
lean_ctor_set(v___x_173_, 2, v___x_172_);
v___x_174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_174_, 0, v___x_173_);
return v___x_174_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___boxed(lean_object* v_a_224_, lean_object* v_x_225_, lean_object* v_c_u2081_226_, lean_object* v_b_227_, lean_object* v_c_u2082_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(v_a_224_, v_x_225_, v_c_u2081_226_, v_b_227_, v_c_u2082_228_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_);
lean_dec(v_a_238_);
lean_dec_ref(v_a_237_);
lean_dec(v_a_236_);
lean_dec_ref(v_a_235_);
lean_dec(v_a_234_);
lean_dec_ref(v_a_233_);
lean_dec(v_a_232_);
lean_dec_ref(v_a_231_);
lean_dec(v_a_230_);
lean_dec(v_a_229_);
lean_dec(v_b_227_);
lean_dec(v_a_224_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0(lean_object* v_cls_241_, lean_object* v_msg_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v_cls_241_, v_msg_242_, v___y_249_, v___y_250_, v___y_251_, v___y_252_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___boxed(lean_object* v_cls_255_, lean_object* v_msg_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0(v_cls_255_, v_msg_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
lean_dec(v___y_260_);
lean_dec_ref(v___y_259_);
lean_dec(v___y_258_);
lean_dec(v___y_257_);
return v_res_268_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = l_Lean_maxRecDepthErrorMessage;
v___x_275_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_275_, 0, v___x_274_);
return v___x_275_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3);
v___x_277_ = l_Lean_MessageData_ofFormat(v___x_276_);
return v___x_277_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_278_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4);
v___x_279_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2));
v___x_280_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
lean_ctor_set(v___x_280_, 1, v___x_278_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(lean_object* v_ref_281_){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_283_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5);
v___x_284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_284_, 0, v_ref_281_);
lean_ctor_set(v___x_284_, 1, v___x_283_);
v___x_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___boxed(lean_object* v_ref_286_, lean_object* v___y_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_286_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0(lean_object* v_00_u03b1_289_, lean_object* v_ref_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_290_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___boxed(lean_object* v_00_u03b1_303_, lean_object* v_ref_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0(v_00_u03b1_303_, v_ref_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_);
lean_dec(v___y_314_);
lean_dec_ref(v___y_313_);
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
lean_dec(v___y_310_);
lean_dec_ref(v___y_309_);
lean_dec(v___y_308_);
lean_dec_ref(v___y_307_);
lean_dec(v___y_306_);
lean_dec(v___y_305_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(lean_object* v_c_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v_p_329_; lean_object* v_toCold_330_; lean_object* v_options_331_; lean_object* v_currRecDepth_332_; lean_object* v_maxRecDepth_333_; lean_object* v_ref_334_; lean_object* v_currNamespace_335_; lean_object* v_openDecls_336_; lean_object* v_initHeartbeats_337_; lean_object* v_maxHeartbeats_338_; lean_object* v_currMacroScope_339_; uint8_t v_diag_340_; uint8_t v_suppressElabErrors_341_; lean_object* v___x_373_; uint8_t v___x_374_; 
v_p_329_ = lean_ctor_get(v_c_317_, 1);
v_toCold_330_ = lean_ctor_get(v_a_326_, 0);
lean_inc_ref(v_toCold_330_);
v_options_331_ = lean_ctor_get(v_a_326_, 1);
lean_inc_ref(v_options_331_);
v_currRecDepth_332_ = lean_ctor_get(v_a_326_, 2);
lean_inc(v_currRecDepth_332_);
v_maxRecDepth_333_ = lean_ctor_get(v_a_326_, 3);
lean_inc(v_maxRecDepth_333_);
v_ref_334_ = lean_ctor_get(v_a_326_, 4);
lean_inc(v_ref_334_);
v_currNamespace_335_ = lean_ctor_get(v_a_326_, 5);
lean_inc(v_currNamespace_335_);
v_openDecls_336_ = lean_ctor_get(v_a_326_, 6);
lean_inc(v_openDecls_336_);
v_initHeartbeats_337_ = lean_ctor_get(v_a_326_, 7);
lean_inc(v_initHeartbeats_337_);
v_maxHeartbeats_338_ = lean_ctor_get(v_a_326_, 8);
lean_inc(v_maxHeartbeats_338_);
v_currMacroScope_339_ = lean_ctor_get(v_a_326_, 9);
lean_inc(v_currMacroScope_339_);
v_diag_340_ = lean_ctor_get_uint8(v_a_326_, sizeof(void*)*10);
v_suppressElabErrors_341_ = lean_ctor_get_uint8(v_a_326_, sizeof(void*)*10 + 1);
lean_dec_ref(v_a_326_);
v___x_373_ = lean_unsigned_to_nat(0u);
v___x_374_ = lean_nat_dec_eq(v_maxRecDepth_333_, v___x_373_);
if (v___x_374_ == 0)
{
uint8_t v___x_375_; 
v___x_375_ = lean_nat_dec_eq(v_currRecDepth_332_, v_maxRecDepth_333_);
if (v___x_375_ == 0)
{
goto v___jp_342_;
}
else
{
lean_object* v___x_376_; 
lean_dec(v_currMacroScope_339_);
lean_dec(v_maxHeartbeats_338_);
lean_dec(v_initHeartbeats_337_);
lean_dec(v_openDecls_336_);
lean_dec(v_currNamespace_335_);
lean_dec(v_maxRecDepth_333_);
lean_dec(v_currRecDepth_332_);
lean_dec_ref(v_options_331_);
lean_dec_ref(v_toCold_330_);
lean_dec_ref(v_c_317_);
v___x_376_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_334_);
return v___x_376_;
}
}
else
{
goto v___jp_342_;
}
v___jp_342_:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_343_ = lean_unsigned_to_nat(1u);
v___x_344_ = lean_nat_add(v_currRecDepth_332_, v___x_343_);
lean_dec(v_currRecDepth_332_);
v___x_345_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_345_, 0, v_toCold_330_);
lean_ctor_set(v___x_345_, 1, v_options_331_);
lean_ctor_set(v___x_345_, 2, v___x_344_);
lean_ctor_set(v___x_345_, 3, v_maxRecDepth_333_);
lean_ctor_set(v___x_345_, 4, v_ref_334_);
lean_ctor_set(v___x_345_, 5, v_currNamespace_335_);
lean_ctor_set(v___x_345_, 6, v_openDecls_336_);
lean_ctor_set(v___x_345_, 7, v_initHeartbeats_337_);
lean_ctor_set(v___x_345_, 8, v_maxHeartbeats_338_);
lean_ctor_set(v___x_345_, 9, v_currMacroScope_339_);
lean_ctor_set_uint8(v___x_345_, sizeof(void*)*10, v_diag_340_);
lean_ctor_set_uint8(v___x_345_, sizeof(void*)*10 + 1, v_suppressElabErrors_341_);
lean_inc_ref(v_p_329_);
v___x_346_ = l_Int_Internal_Linear_Poly_findVarToSubst___redArg(v_p_329_, v_a_318_, v___x_345_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v_a_347_; lean_object* v___x_349_; uint8_t v_isShared_350_; uint8_t v_isSharedCheck_364_; 
v_a_347_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_364_ == 0)
{
v___x_349_ = v___x_346_;
v_isShared_350_ = v_isSharedCheck_364_;
goto v_resetjp_348_;
}
else
{
lean_inc(v_a_347_);
lean_dec(v___x_346_);
v___x_349_ = lean_box(0);
v_isShared_350_ = v_isSharedCheck_364_;
goto v_resetjp_348_;
}
v_resetjp_348_:
{
if (lean_obj_tag(v_a_347_) == 1)
{
lean_object* v_val_351_; lean_object* v_snd_352_; lean_object* v_snd_353_; lean_object* v_fst_354_; lean_object* v_fst_355_; lean_object* v_p_356_; lean_object* v___x_357_; lean_object* v___x_358_; 
lean_del_object(v___x_349_);
v_val_351_ = lean_ctor_get(v_a_347_, 0);
lean_inc(v_val_351_);
lean_dec_ref_known(v_a_347_, 1);
v_snd_352_ = lean_ctor_get(v_val_351_, 1);
lean_inc(v_snd_352_);
v_snd_353_ = lean_ctor_get(v_snd_352_, 1);
lean_inc(v_snd_353_);
v_fst_354_ = lean_ctor_get(v_val_351_, 0);
lean_inc(v_fst_354_);
lean_dec(v_val_351_);
v_fst_355_ = lean_ctor_get(v_snd_352_, 0);
lean_inc(v_fst_355_);
lean_dec(v_snd_352_);
v_p_356_ = lean_ctor_get(v_snd_353_, 0);
v___x_357_ = l_Int_Internal_Linear_Poly_coeff(v_p_356_, v_fst_355_);
v___x_358_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(v___x_357_, v_fst_355_, v_snd_353_, v_fst_354_, v_c_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v___x_345_, v_a_327_);
lean_dec(v_fst_354_);
lean_dec(v___x_357_);
if (lean_obj_tag(v___x_358_) == 0)
{
lean_object* v_a_359_; 
v_a_359_ = lean_ctor_get(v___x_358_, 0);
lean_inc(v_a_359_);
lean_dec_ref_known(v___x_358_, 1);
v_c_317_ = v_a_359_;
v_a_326_ = v___x_345_;
goto _start;
}
else
{
lean_dec_ref_known(v___x_345_, 10);
return v___x_358_;
}
}
else
{
lean_object* v___x_362_; 
lean_dec(v_a_347_);
lean_dec_ref_known(v___x_345_, 10);
if (v_isShared_350_ == 0)
{
lean_ctor_set(v___x_349_, 0, v_c_317_);
v___x_362_ = v___x_349_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_c_317_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
}
else
{
lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_372_; 
lean_dec_ref_known(v___x_345_, 10);
lean_dec_ref(v_c_317_);
v_a_365_ = lean_ctor_get(v___x_346_, 0);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_346_);
if (v_isSharedCheck_372_ == 0)
{
v___x_367_ = v___x_346_;
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_dec(v___x_346_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_370_; 
if (v_isShared_368_ == 0)
{
v___x_370_ = v___x_367_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_a_365_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___boxed(lean_object* v_c_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(v_c_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_);
lean_dec(v_a_387_);
lean_dec(v_a_385_);
lean_dec_ref(v_a_384_);
lean_dec(v_a_383_);
lean_dec_ref(v_a_382_);
lean_dec(v_a_381_);
lean_dec_ref(v_a_380_);
lean_dec(v_a_379_);
lean_dec(v_a_378_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(lean_object* v_a_390_, lean_object* v_v_391_, lean_object* v_s_392_){
_start:
{
lean_object* v_vars_393_; lean_object* v_varMap_394_; lean_object* v_vars_x27_395_; lean_object* v_varMap_x27_396_; lean_object* v_natToIntMap_397_; lean_object* v_natDef_398_; lean_object* v_dvds_399_; lean_object* v_lowers_400_; lean_object* v_uppers_401_; lean_object* v_diseqs_402_; lean_object* v_elimEqs_403_; lean_object* v_elimStack_404_; lean_object* v_occurs_405_; lean_object* v_assignment_406_; lean_object* v_nextCnstrId_407_; uint8_t v_caseSplits_408_; lean_object* v_steps_409_; lean_object* v_conflict_x3f_410_; lean_object* v_diseqSplits_411_; lean_object* v_divMod_412_; uint8_t v_usedCommRing_413_; lean_object* v_nonlinearOccs_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_423_; 
v_vars_393_ = lean_ctor_get(v_s_392_, 0);
v_varMap_394_ = lean_ctor_get(v_s_392_, 1);
v_vars_x27_395_ = lean_ctor_get(v_s_392_, 2);
v_varMap_x27_396_ = lean_ctor_get(v_s_392_, 3);
v_natToIntMap_397_ = lean_ctor_get(v_s_392_, 4);
v_natDef_398_ = lean_ctor_get(v_s_392_, 5);
v_dvds_399_ = lean_ctor_get(v_s_392_, 6);
v_lowers_400_ = lean_ctor_get(v_s_392_, 7);
v_uppers_401_ = lean_ctor_get(v_s_392_, 8);
v_diseqs_402_ = lean_ctor_get(v_s_392_, 9);
v_elimEqs_403_ = lean_ctor_get(v_s_392_, 10);
v_elimStack_404_ = lean_ctor_get(v_s_392_, 11);
v_occurs_405_ = lean_ctor_get(v_s_392_, 12);
v_assignment_406_ = lean_ctor_get(v_s_392_, 13);
v_nextCnstrId_407_ = lean_ctor_get(v_s_392_, 14);
v_caseSplits_408_ = lean_ctor_get_uint8(v_s_392_, sizeof(void*)*20);
v_steps_409_ = lean_ctor_get(v_s_392_, 15);
v_conflict_x3f_410_ = lean_ctor_get(v_s_392_, 16);
v_diseqSplits_411_ = lean_ctor_get(v_s_392_, 17);
v_divMod_412_ = lean_ctor_get(v_s_392_, 18);
v_usedCommRing_413_ = lean_ctor_get_uint8(v_s_392_, sizeof(void*)*20 + 1);
v_nonlinearOccs_414_ = lean_ctor_get(v_s_392_, 19);
v_isSharedCheck_423_ = !lean_is_exclusive(v_s_392_);
if (v_isSharedCheck_423_ == 0)
{
v___x_416_ = v_s_392_;
v_isShared_417_ = v_isSharedCheck_423_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_nonlinearOccs_414_);
lean_inc(v_divMod_412_);
lean_inc(v_diseqSplits_411_);
lean_inc(v_conflict_x3f_410_);
lean_inc(v_steps_409_);
lean_inc(v_nextCnstrId_407_);
lean_inc(v_assignment_406_);
lean_inc(v_occurs_405_);
lean_inc(v_elimStack_404_);
lean_inc(v_elimEqs_403_);
lean_inc(v_diseqs_402_);
lean_inc(v_uppers_401_);
lean_inc(v_lowers_400_);
lean_inc(v_dvds_399_);
lean_inc(v_natDef_398_);
lean_inc(v_natToIntMap_397_);
lean_inc(v_varMap_x27_396_);
lean_inc(v_vars_x27_395_);
lean_inc(v_varMap_394_);
lean_inc(v_vars_393_);
lean_dec(v_s_392_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_423_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_421_; 
v___x_418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_418_, 0, v_a_390_);
v___x_419_ = l_Lean_PersistentArray_set___redArg(v_dvds_399_, v_v_391_, v___x_418_);
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 6, v___x_419_);
v___x_421_ = v___x_416_;
goto v_reusejp_420_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 20, 2);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v_vars_393_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v_varMap_394_);
lean_ctor_set(v_reuseFailAlloc_422_, 2, v_vars_x27_395_);
lean_ctor_set(v_reuseFailAlloc_422_, 3, v_varMap_x27_396_);
lean_ctor_set(v_reuseFailAlloc_422_, 4, v_natToIntMap_397_);
lean_ctor_set(v_reuseFailAlloc_422_, 5, v_natDef_398_);
lean_ctor_set(v_reuseFailAlloc_422_, 6, v___x_419_);
lean_ctor_set(v_reuseFailAlloc_422_, 7, v_lowers_400_);
lean_ctor_set(v_reuseFailAlloc_422_, 8, v_uppers_401_);
lean_ctor_set(v_reuseFailAlloc_422_, 9, v_diseqs_402_);
lean_ctor_set(v_reuseFailAlloc_422_, 10, v_elimEqs_403_);
lean_ctor_set(v_reuseFailAlloc_422_, 11, v_elimStack_404_);
lean_ctor_set(v_reuseFailAlloc_422_, 12, v_occurs_405_);
lean_ctor_set(v_reuseFailAlloc_422_, 13, v_assignment_406_);
lean_ctor_set(v_reuseFailAlloc_422_, 14, v_nextCnstrId_407_);
lean_ctor_set(v_reuseFailAlloc_422_, 15, v_steps_409_);
lean_ctor_set(v_reuseFailAlloc_422_, 16, v_conflict_x3f_410_);
lean_ctor_set(v_reuseFailAlloc_422_, 17, v_diseqSplits_411_);
lean_ctor_set(v_reuseFailAlloc_422_, 18, v_divMod_412_);
lean_ctor_set(v_reuseFailAlloc_422_, 19, v_nonlinearOccs_414_);
lean_ctor_set_uint8(v_reuseFailAlloc_422_, sizeof(void*)*20, v_caseSplits_408_);
lean_ctor_set_uint8(v_reuseFailAlloc_422_, sizeof(void*)*20 + 1, v_usedCommRing_413_);
v___x_421_ = v_reuseFailAlloc_422_;
goto v_reusejp_420_;
}
v_reusejp_420_:
{
return v___x_421_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed(lean_object* v_a_424_, lean_object* v_v_425_, lean_object* v_s_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(v_a_424_, v_v_425_, v_s_426_);
lean_dec(v_v_425_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(lean_object* v_v_428_, lean_object* v_s_429_){
_start:
{
lean_object* v_vars_430_; lean_object* v_varMap_431_; lean_object* v_vars_x27_432_; lean_object* v_varMap_x27_433_; lean_object* v_natToIntMap_434_; lean_object* v_natDef_435_; lean_object* v_dvds_436_; lean_object* v_lowers_437_; lean_object* v_uppers_438_; lean_object* v_diseqs_439_; lean_object* v_elimEqs_440_; lean_object* v_elimStack_441_; lean_object* v_occurs_442_; lean_object* v_assignment_443_; lean_object* v_nextCnstrId_444_; uint8_t v_caseSplits_445_; lean_object* v_steps_446_; lean_object* v_conflict_x3f_447_; lean_object* v_diseqSplits_448_; lean_object* v_divMod_449_; uint8_t v_usedCommRing_450_; lean_object* v_nonlinearOccs_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_460_; 
v_vars_430_ = lean_ctor_get(v_s_429_, 0);
v_varMap_431_ = lean_ctor_get(v_s_429_, 1);
v_vars_x27_432_ = lean_ctor_get(v_s_429_, 2);
v_varMap_x27_433_ = lean_ctor_get(v_s_429_, 3);
v_natToIntMap_434_ = lean_ctor_get(v_s_429_, 4);
v_natDef_435_ = lean_ctor_get(v_s_429_, 5);
v_dvds_436_ = lean_ctor_get(v_s_429_, 6);
v_lowers_437_ = lean_ctor_get(v_s_429_, 7);
v_uppers_438_ = lean_ctor_get(v_s_429_, 8);
v_diseqs_439_ = lean_ctor_get(v_s_429_, 9);
v_elimEqs_440_ = lean_ctor_get(v_s_429_, 10);
v_elimStack_441_ = lean_ctor_get(v_s_429_, 11);
v_occurs_442_ = lean_ctor_get(v_s_429_, 12);
v_assignment_443_ = lean_ctor_get(v_s_429_, 13);
v_nextCnstrId_444_ = lean_ctor_get(v_s_429_, 14);
v_caseSplits_445_ = lean_ctor_get_uint8(v_s_429_, sizeof(void*)*20);
v_steps_446_ = lean_ctor_get(v_s_429_, 15);
v_conflict_x3f_447_ = lean_ctor_get(v_s_429_, 16);
v_diseqSplits_448_ = lean_ctor_get(v_s_429_, 17);
v_divMod_449_ = lean_ctor_get(v_s_429_, 18);
v_usedCommRing_450_ = lean_ctor_get_uint8(v_s_429_, sizeof(void*)*20 + 1);
v_nonlinearOccs_451_ = lean_ctor_get(v_s_429_, 19);
v_isSharedCheck_460_ = !lean_is_exclusive(v_s_429_);
if (v_isSharedCheck_460_ == 0)
{
v___x_453_ = v_s_429_;
v_isShared_454_ = v_isSharedCheck_460_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_nonlinearOccs_451_);
lean_inc(v_divMod_449_);
lean_inc(v_diseqSplits_448_);
lean_inc(v_conflict_x3f_447_);
lean_inc(v_steps_446_);
lean_inc(v_nextCnstrId_444_);
lean_inc(v_assignment_443_);
lean_inc(v_occurs_442_);
lean_inc(v_elimStack_441_);
lean_inc(v_elimEqs_440_);
lean_inc(v_diseqs_439_);
lean_inc(v_uppers_438_);
lean_inc(v_lowers_437_);
lean_inc(v_dvds_436_);
lean_inc(v_natDef_435_);
lean_inc(v_natToIntMap_434_);
lean_inc(v_varMap_x27_433_);
lean_inc(v_vars_x27_432_);
lean_inc(v_varMap_431_);
lean_inc(v_vars_430_);
lean_dec(v_s_429_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_460_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_458_; 
v___x_455_ = lean_box(0);
v___x_456_ = l_Lean_PersistentArray_set___redArg(v_dvds_436_, v_v_428_, v___x_455_);
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 6, v___x_456_);
v___x_458_ = v___x_453_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 20, 2);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_vars_430_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v_varMap_431_);
lean_ctor_set(v_reuseFailAlloc_459_, 2, v_vars_x27_432_);
lean_ctor_set(v_reuseFailAlloc_459_, 3, v_varMap_x27_433_);
lean_ctor_set(v_reuseFailAlloc_459_, 4, v_natToIntMap_434_);
lean_ctor_set(v_reuseFailAlloc_459_, 5, v_natDef_435_);
lean_ctor_set(v_reuseFailAlloc_459_, 6, v___x_456_);
lean_ctor_set(v_reuseFailAlloc_459_, 7, v_lowers_437_);
lean_ctor_set(v_reuseFailAlloc_459_, 8, v_uppers_438_);
lean_ctor_set(v_reuseFailAlloc_459_, 9, v_diseqs_439_);
lean_ctor_set(v_reuseFailAlloc_459_, 10, v_elimEqs_440_);
lean_ctor_set(v_reuseFailAlloc_459_, 11, v_elimStack_441_);
lean_ctor_set(v_reuseFailAlloc_459_, 12, v_occurs_442_);
lean_ctor_set(v_reuseFailAlloc_459_, 13, v_assignment_443_);
lean_ctor_set(v_reuseFailAlloc_459_, 14, v_nextCnstrId_444_);
lean_ctor_set(v_reuseFailAlloc_459_, 15, v_steps_446_);
lean_ctor_set(v_reuseFailAlloc_459_, 16, v_conflict_x3f_447_);
lean_ctor_set(v_reuseFailAlloc_459_, 17, v_diseqSplits_448_);
lean_ctor_set(v_reuseFailAlloc_459_, 18, v_divMod_449_);
lean_ctor_set(v_reuseFailAlloc_459_, 19, v_nonlinearOccs_451_);
lean_ctor_set_uint8(v_reuseFailAlloc_459_, sizeof(void*)*20, v_caseSplits_445_);
lean_ctor_set_uint8(v_reuseFailAlloc_459_, sizeof(void*)*20 + 1, v_usedCommRing_450_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
return v___x_458_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed(lean_object* v_v_461_, lean_object* v_s_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(v_v_461_, v_s_462_);
lean_dec(v_v_461_);
return v_res_463_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5(void){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_472_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4));
v___x_473_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
v___x_474_ = l_Lean_Name_append(v___x_473_, v___x_472_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(lean_object* v_c_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_){
_start:
{
lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v___y_493_; lean_object* v___y_494_; lean_object* v___y_495_; lean_object* v___y_496_; lean_object* v___y_497_; lean_object* v___y_502_; lean_object* v___y_503_; lean_object* v___y_504_; lean_object* v___y_505_; lean_object* v___y_506_; lean_object* v___y_507_; lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___y_611_; lean_object* v___y_612_; lean_object* v___y_613_; lean_object* v___y_614_; lean_object* v___y_615_; lean_object* v_toCold_627_; lean_object* v_options_628_; lean_object* v_currRecDepth_629_; lean_object* v_maxRecDepth_630_; lean_object* v_ref_631_; lean_object* v_currNamespace_632_; lean_object* v_openDecls_633_; lean_object* v_initHeartbeats_634_; lean_object* v_maxHeartbeats_635_; lean_object* v_currMacroScope_636_; uint8_t v_diag_637_; uint8_t v_suppressElabErrors_638_; lean_object* v___x_639_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___x_822_; uint8_t v___x_823_; 
v_toCold_627_ = lean_ctor_get(v_a_484_, 0);
lean_inc_ref(v_toCold_627_);
v_options_628_ = lean_ctor_get(v_a_484_, 1);
lean_inc_ref(v_options_628_);
v_currRecDepth_629_ = lean_ctor_get(v_a_484_, 2);
lean_inc(v_currRecDepth_629_);
v_maxRecDepth_630_ = lean_ctor_get(v_a_484_, 3);
lean_inc(v_maxRecDepth_630_);
v_ref_631_ = lean_ctor_get(v_a_484_, 4);
lean_inc(v_ref_631_);
v_currNamespace_632_ = lean_ctor_get(v_a_484_, 5);
lean_inc(v_currNamespace_632_);
v_openDecls_633_ = lean_ctor_get(v_a_484_, 6);
lean_inc(v_openDecls_633_);
v_initHeartbeats_634_ = lean_ctor_get(v_a_484_, 7);
lean_inc(v_initHeartbeats_634_);
v_maxHeartbeats_635_ = lean_ctor_get(v_a_484_, 8);
lean_inc(v_maxHeartbeats_635_);
v_currMacroScope_636_ = lean_ctor_get(v_a_484_, 9);
lean_inc(v_currMacroScope_636_);
v_diag_637_ = lean_ctor_get_uint8(v_a_484_, sizeof(void*)*10);
v_suppressElabErrors_638_ = lean_ctor_get_uint8(v_a_484_, sizeof(void*)*10 + 1);
lean_dec_ref(v_a_484_);
v___x_639_ = lean_box(0);
v___x_822_ = lean_unsigned_to_nat(0u);
v___x_823_ = lean_nat_dec_eq(v_maxRecDepth_630_, v___x_822_);
if (v___x_823_ == 0)
{
uint8_t v___x_824_; 
v___x_824_ = lean_nat_dec_eq(v_currRecDepth_629_, v_maxRecDepth_630_);
if (v___x_824_ == 0)
{
goto v___jp_780_;
}
else
{
lean_object* v___x_825_; 
lean_dec(v_currMacroScope_636_);
lean_dec(v_maxHeartbeats_635_);
lean_dec(v_initHeartbeats_634_);
lean_dec(v_openDecls_633_);
lean_dec(v_currNamespace_632_);
lean_dec(v_maxRecDepth_630_);
lean_dec(v_currRecDepth_629_);
lean_dec_ref(v_options_628_);
lean_dec_ref(v_toCold_627_);
lean_dec_ref(v_c_475_);
v___x_825_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_631_);
return v___x_825_;
}
}
else
{
goto v___jp_780_;
}
v___jp_487_:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = lean_box(0);
v___x_489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
return v___x_489_;
}
v___jp_490_:
{
lean_object* v___x_498_; 
v___x_498_ = l_Int_Internal_Linear_Poly_updateOccs___redArg(v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_);
lean_dec_ref(v___y_496_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v___x_499_; lean_object* v___x_500_; 
lean_dec_ref_known(v___x_498_, 1);
v___x_499_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_500_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_499_, v___y_491_, v___y_493_);
return v___x_500_;
}
else
{
lean_dec_ref(v___y_491_);
return v___x_498_;
}
}
v___jp_501_:
{
if (lean_obj_tag(v___y_523_) == 1)
{
lean_object* v_val_524_; lean_object* v_p_525_; 
lean_dec_ref(v___y_522_);
lean_dec_ref(v___y_507_);
v_val_524_ = lean_ctor_get(v___y_523_, 0);
lean_inc(v_val_524_);
lean_dec_ref_known(v___y_523_, 1);
v_p_525_ = lean_ctor_get(v_val_524_, 1);
lean_inc_ref(v_p_525_);
if (lean_obj_tag(v_p_525_) == 1)
{
lean_object* v_d_526_; lean_object* v_k_527_; lean_object* v_p_528_; lean_object* v___x_530_; uint8_t v_isShared_531_; uint8_t v_isSharedCheck_581_; 
v_d_526_ = lean_ctor_get(v_val_524_, 0);
v_k_527_ = lean_ctor_get(v_p_525_, 0);
v_p_528_ = lean_ctor_get(v_p_525_, 2);
v_isSharedCheck_581_ = !lean_is_exclusive(v_p_525_);
if (v_isSharedCheck_581_ == 0)
{
lean_object* v_unused_582_; 
v_unused_582_ = lean_ctor_get(v_p_525_, 1);
lean_dec(v_unused_582_);
v___x_530_ = v_p_525_;
v_isShared_531_ = v_isSharedCheck_581_;
goto v_resetjp_529_;
}
else
{
lean_inc(v_p_528_);
lean_inc(v_k_527_);
lean_dec(v_p_525_);
v___x_530_ = lean_box(0);
v_isShared_531_ = v_isSharedCheck_581_;
goto v_resetjp_529_;
}
v_resetjp_529_:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v_snd_535_; lean_object* v_fst_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_580_; 
v___x_532_ = lean_int_mul(v___y_512_, v_d_526_);
v___x_533_ = lean_int_mul(v_k_527_, v___y_520_);
v___x_534_ = l_Lean_Meta_Grind_Arith_gcdExt(v___x_532_, v___x_533_);
lean_dec(v___x_533_);
lean_dec(v___x_532_);
v_snd_535_ = lean_ctor_get(v___x_534_, 1);
v_fst_536_ = lean_ctor_get(v___x_534_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v___x_534_);
if (v_isSharedCheck_580_ == 0)
{
v___x_538_ = v___x_534_;
v_isShared_539_ = v_isSharedCheck_580_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_snd_535_);
lean_inc(v_fst_536_);
lean_dec(v___x_534_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_580_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v_fst_540_; lean_object* v_snd_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_579_; 
v_fst_540_ = lean_ctor_get(v_snd_535_, 0);
v_snd_541_ = lean_ctor_get(v_snd_535_, 1);
v_isSharedCheck_579_ = !lean_is_exclusive(v_snd_535_);
if (v_isSharedCheck_579_ == 0)
{
v___x_543_ = v_snd_535_;
v_isShared_544_ = v_isSharedCheck_579_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_snd_541_);
lean_inc(v_fst_540_);
lean_dec(v_snd_535_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_579_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_546_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_545_, v___y_518_, v___y_503_);
if (lean_obj_tag(v___x_546_) == 0)
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_554_; 
lean_dec_ref_known(v___x_546_, 1);
v___x_547_ = lean_int_mul(v_fst_540_, v_d_526_);
lean_dec(v_fst_540_);
lean_inc_ref(v___y_521_);
v___x_548_ = l_Int_Internal_Linear_Poly_mul(v___y_521_, v___x_547_);
lean_dec(v___x_547_);
v___x_549_ = lean_int_mul(v_snd_541_, v___y_520_);
lean_dec(v_snd_541_);
lean_inc_ref(v_p_528_);
v___x_550_ = l_Int_Internal_Linear_Poly_mul(v_p_528_, v___x_549_);
lean_dec(v___x_549_);
v___x_551_ = lean_int_mul(v___y_520_, v_d_526_);
lean_dec(v___y_520_);
v___x_552_ = l_Int_Internal_Linear_Poly_combine(v___x_548_, v___x_550_);
lean_inc(v_fst_536_);
if (v_isShared_531_ == 0)
{
lean_ctor_set(v___x_530_, 2, v___x_552_);
lean_ctor_set(v___x_530_, 1, v___y_504_);
lean_ctor_set(v___x_530_, 0, v_fst_536_);
v___x_554_ = v___x_530_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v_fst_536_);
lean_ctor_set(v_reuseFailAlloc_578_, 1, v___y_504_);
lean_ctor_set(v_reuseFailAlloc_578_, 2, v___x_552_);
v___x_554_ = v_reuseFailAlloc_578_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
lean_object* v___x_556_; 
lean_inc(v_val_524_);
lean_inc_ref(v___y_513_);
if (v_isShared_544_ == 0)
{
lean_ctor_set_tag(v___x_543_, 4);
lean_ctor_set(v___x_543_, 1, v_val_524_);
lean_ctor_set(v___x_543_, 0, v___y_513_);
v___x_556_ = v___x_543_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___y_513_);
lean_ctor_set(v_reuseFailAlloc_577_, 1, v_val_524_);
v___x_556_ = v_reuseFailAlloc_577_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_557_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_557_, 0, v___x_551_);
lean_ctor_set(v___x_557_, 1, v___x_554_);
lean_ctor_set(v___x_557_, 2, v___x_556_);
lean_inc_ref(v___y_517_);
v___x_558_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v___x_557_, v___y_503_, v___y_510_, v___y_519_, v___y_508_, v___y_506_, v___y_509_, v___y_511_, v___y_515_, v___y_517_, v___y_516_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_564_; 
lean_dec_ref_known(v___x_558_, 1);
v___x_559_ = l_Int_Internal_Linear_Poly_mul(v___y_521_, v_k_527_);
lean_dec(v_k_527_);
v___x_560_ = lean_int_neg(v___y_512_);
lean_dec(v___y_512_);
v___x_561_ = l_Int_Internal_Linear_Poly_mul(v_p_528_, v___x_560_);
lean_dec(v___x_560_);
v___x_562_ = l_Int_Internal_Linear_Poly_combine(v___x_559_, v___x_561_);
lean_inc(v_val_524_);
if (v_isShared_539_ == 0)
{
lean_ctor_set_tag(v___x_538_, 5);
lean_ctor_set(v___x_538_, 1, v_val_524_);
lean_ctor_set(v___x_538_, 0, v___y_513_);
v___x_564_ = v___x_538_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___y_513_);
lean_ctor_set(v_reuseFailAlloc_576_, 1, v_val_524_);
v___x_564_ = v_reuseFailAlloc_576_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_572_; 
v_isSharedCheck_572_ = !lean_is_exclusive(v_val_524_);
if (v_isSharedCheck_572_ == 0)
{
lean_object* v_unused_573_; lean_object* v_unused_574_; lean_object* v_unused_575_; 
v_unused_573_ = lean_ctor_get(v_val_524_, 2);
lean_dec(v_unused_573_);
v_unused_574_ = lean_ctor_get(v_val_524_, 1);
lean_dec(v_unused_574_);
v_unused_575_ = lean_ctor_get(v_val_524_, 0);
lean_dec(v_unused_575_);
v___x_566_ = v_val_524_;
v_isShared_567_ = v_isSharedCheck_572_;
goto v_resetjp_565_;
}
else
{
lean_dec(v_val_524_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_572_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_569_; 
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 2, v___x_564_);
lean_ctor_set(v___x_566_, 1, v___x_562_);
lean_ctor_set(v___x_566_, 0, v_fst_536_);
v___x_569_ = v___x_566_;
goto v_reusejp_568_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_fst_536_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v___x_562_);
lean_ctor_set(v_reuseFailAlloc_571_, 2, v___x_564_);
v___x_569_ = v_reuseFailAlloc_571_;
goto v_reusejp_568_;
}
v_reusejp_568_:
{
v_c_475_ = v___x_569_;
v_a_476_ = v___y_503_;
v_a_477_ = v___y_510_;
v_a_478_ = v___y_519_;
v_a_479_ = v___y_508_;
v_a_480_ = v___y_506_;
v_a_481_ = v___y_509_;
v_a_482_ = v___y_511_;
v_a_483_ = v___y_515_;
v_a_484_ = v___y_517_;
v_a_485_ = v___y_516_;
goto _start;
}
}
}
}
else
{
lean_del_object(v___x_538_);
lean_dec(v_fst_536_);
lean_dec_ref(v_p_528_);
lean_dec(v_k_527_);
lean_dec(v_val_524_);
lean_dec_ref(v___y_521_);
lean_dec_ref(v___y_517_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
return v___x_558_;
}
}
}
}
else
{
lean_del_object(v___x_543_);
lean_dec(v_snd_541_);
lean_dec(v_fst_540_);
lean_del_object(v___x_538_);
lean_dec(v_fst_536_);
lean_del_object(v___x_530_);
lean_dec_ref(v_p_528_);
lean_dec(v_k_527_);
lean_dec(v_val_524_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_517_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec(v___y_504_);
return v___x_546_;
}
}
}
}
}
else
{
lean_object* v___x_583_; 
lean_dec_ref(v_p_525_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_518_);
lean_dec_ref(v___y_513_);
lean_dec(v___y_512_);
lean_dec(v___y_504_);
v___x_583_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_val_524_, v___y_503_, v___y_510_, v___y_519_, v___y_508_, v___y_506_, v___y_509_, v___y_511_, v___y_515_, v___y_517_, v___y_516_);
lean_dec_ref(v___y_517_);
return v___x_583_;
}
}
else
{
lean_object* v_options_584_; uint8_t v_hasTrace_585_; 
lean_dec(v___y_523_);
lean_dec_ref(v___y_521_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_518_);
lean_dec(v___y_512_);
lean_dec(v___y_504_);
v_options_584_ = lean_ctor_get(v___y_517_, 1);
v_hasTrace_585_ = lean_ctor_get_uint8(v_options_584_, sizeof(void*)*1);
if (v_hasTrace_585_ == 0)
{
lean_dec_ref(v___y_513_);
v___y_491_ = v___y_507_;
v___y_492_ = v___y_522_;
v___y_493_ = v___y_503_;
v___y_494_ = v___y_511_;
v___y_495_ = v___y_515_;
v___y_496_ = v___y_517_;
v___y_497_ = v___y_516_;
goto v___jp_490_;
}
else
{
lean_object* v_toCold_586_; lean_object* v_inheritedTraceOptions_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; uint8_t v___x_592_; 
v_toCold_586_ = lean_ctor_get(v___y_517_, 0);
v_inheritedTraceOptions_587_ = lean_ctor_get(v_toCold_586_, 4);
v___x_588_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0));
lean_inc_ref(v___y_505_);
lean_inc_ref(v___y_502_);
lean_inc_ref(v___y_514_);
v___x_589_ = l_Lean_Name_mkStr4(v___y_514_, v___y_502_, v___y_505_, v___x_588_);
v___x_590_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
lean_inc(v___x_589_);
v___x_591_ = l_Lean_Name_append(v___x_590_, v___x_589_);
v___x_592_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_587_, v_options_584_, v___x_591_);
lean_dec(v___x_591_);
if (v___x_592_ == 0)
{
lean_dec(v___x_589_);
lean_dec_ref(v___y_513_);
v___y_491_ = v___y_507_;
v___y_492_ = v___y_522_;
v___y_493_ = v___y_503_;
v___y_494_ = v___y_511_;
v___y_495_ = v___y_515_;
v___y_496_ = v___y_517_;
v___y_497_ = v___y_516_;
goto v___jp_490_;
}
else
{
lean_object* v___x_593_; 
v___x_593_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v___y_513_, v___y_503_, v___y_517_);
if (lean_obj_tag(v___x_593_) == 0)
{
lean_object* v_a_594_; lean_object* v___x_595_; 
v_a_594_ = lean_ctor_get(v___x_593_, 0);
lean_inc(v_a_594_);
lean_dec_ref_known(v___x_593_, 1);
v___x_595_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_589_, v_a_594_, v___y_511_, v___y_515_, v___y_517_, v___y_516_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_dec_ref_known(v___x_595_, 1);
v___y_491_ = v___y_507_;
v___y_492_ = v___y_522_;
v___y_493_ = v___y_503_;
v___y_494_ = v___y_511_;
v___y_495_ = v___y_515_;
v___y_496_ = v___y_517_;
v___y_497_ = v___y_516_;
goto v___jp_490_;
}
else
{
lean_dec_ref(v___y_522_);
lean_dec_ref(v___y_517_);
lean_dec_ref(v___y_507_);
return v___x_595_;
}
}
else
{
lean_object* v_a_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_603_; 
lean_dec(v___x_589_);
lean_dec_ref(v___y_522_);
lean_dec_ref(v___y_517_);
lean_dec_ref(v___y_507_);
v_a_596_ = lean_ctor_get(v___x_593_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v___x_593_);
if (v_isSharedCheck_603_ == 0)
{
v___x_598_ = v___x_593_;
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_a_596_);
lean_dec(v___x_593_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_603_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_601_; 
if (v_isShared_599_ == 0)
{
v___x_601_ = v___x_598_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v_a_596_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
}
}
}
v___jp_604_:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_616_, 0, v___y_605_);
v___x_617_ = l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(v___x_616_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_);
lean_dec_ref(v___y_614_);
if (lean_obj_tag(v___x_617_) == 0)
{
lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_625_; 
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_617_);
if (v_isSharedCheck_625_ == 0)
{
lean_object* v_unused_626_; 
v_unused_626_ = lean_ctor_get(v___x_617_, 0);
lean_dec(v_unused_626_);
v___x_619_ = v___x_617_;
v_isShared_620_ = v_isSharedCheck_625_;
goto v_resetjp_618_;
}
else
{
lean_dec(v___x_617_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_625_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_621_; lean_object* v___x_623_; 
v___x_621_ = lean_box(0);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 0, v___x_621_);
v___x_623_ = v___x_619_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v___x_621_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
else
{
return v___x_617_;
}
}
v___jp_640_:
{
lean_object* v___x_662_; 
v___x_662_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v___y_652_, v___y_660_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_object* v_a_663_; lean_object* v_dvds_664_; lean_object* v_size_665_; uint8_t v___x_666_; 
v_a_663_ = lean_ctor_get(v___x_662_, 0);
lean_inc(v_a_663_);
lean_dec_ref_known(v___x_662_, 1);
v_dvds_664_ = lean_ctor_get(v_a_663_, 6);
lean_inc_ref(v_dvds_664_);
lean_dec(v_a_663_);
v_size_665_ = lean_ctor_get(v_dvds_664_, 2);
v___x_666_ = lean_nat_dec_lt(v___y_642_, v_size_665_);
if (v___x_666_ == 0)
{
lean_object* v___x_667_; 
lean_dec_ref(v_dvds_664_);
v___x_667_ = l_outOfBounds___redArg(v___x_639_);
v___y_502_ = v___y_641_;
v___y_503_ = v___y_652_;
v___y_504_ = v___y_642_;
v___y_505_ = v___y_643_;
v___y_506_ = v___y_656_;
v___y_507_ = v___y_644_;
v___y_508_ = v___y_655_;
v___y_509_ = v___y_657_;
v___y_510_ = v___y_653_;
v___y_511_ = v___y_658_;
v___y_512_ = v___y_648_;
v___y_513_ = v___y_649_;
v___y_514_ = v___y_650_;
v___y_515_ = v___y_659_;
v___y_516_ = v___y_661_;
v___y_517_ = v___y_660_;
v___y_518_ = v___y_645_;
v___y_519_ = v___y_654_;
v___y_520_ = v___y_646_;
v___y_521_ = v___y_647_;
v___y_522_ = v___y_651_;
v___y_523_ = v___x_667_;
goto v___jp_501_;
}
else
{
lean_object* v___x_668_; 
v___x_668_ = l_Lean_PersistentArray_get_x21___redArg(v___x_639_, v_dvds_664_, v___y_642_);
lean_dec_ref(v_dvds_664_);
v___y_502_ = v___y_641_;
v___y_503_ = v___y_652_;
v___y_504_ = v___y_642_;
v___y_505_ = v___y_643_;
v___y_506_ = v___y_656_;
v___y_507_ = v___y_644_;
v___y_508_ = v___y_655_;
v___y_509_ = v___y_657_;
v___y_510_ = v___y_653_;
v___y_511_ = v___y_658_;
v___y_512_ = v___y_648_;
v___y_513_ = v___y_649_;
v___y_514_ = v___y_650_;
v___y_515_ = v___y_659_;
v___y_516_ = v___y_661_;
v___y_517_ = v___y_660_;
v___y_518_ = v___y_645_;
v___y_519_ = v___y_654_;
v___y_520_ = v___y_646_;
v___y_521_ = v___y_647_;
v___y_522_ = v___y_651_;
v___y_523_ = v___x_668_;
goto v___jp_501_;
}
}
else
{
lean_object* v_a_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_676_; 
lean_dec_ref(v___y_660_);
lean_dec_ref(v___y_651_);
lean_dec_ref(v___y_649_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
lean_dec(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec(v___y_642_);
v_a_669_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_676_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_676_ == 0)
{
v___x_671_ = v___x_662_;
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_a_669_);
lean_dec(v___x_662_);
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_676_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_674_; 
if (v_isShared_672_ == 0)
{
v___x_674_ = v___x_671_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_a_669_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
}
v___jp_677_:
{
lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_691_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(v_c_475_);
lean_inc_ref(v___y_689_);
v___x_692_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(v___x_691_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
if (lean_obj_tag(v___x_692_) == 0)
{
lean_object* v_a_693_; lean_object* v_d_694_; lean_object* v_p_695_; uint8_t v___x_696_; 
v_a_693_ = lean_ctor_get(v___x_692_, 0);
lean_inc(v_a_693_);
lean_dec_ref_known(v___x_692_, 1);
v_d_694_ = lean_ctor_get(v_a_693_, 0);
v_p_695_ = lean_ctor_get(v_a_693_, 1);
lean_inc(v_d_694_);
v___x_696_ = l_Int_Internal_Linear_Poly_isUnsatDvd(v_d_694_, v_p_695_);
if (v___x_696_ == 0)
{
uint8_t v___x_697_; 
v___x_697_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(v_a_693_);
if (v___x_697_ == 0)
{
lean_object* v___x_698_; uint8_t v___x_699_; 
v___x_698_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1);
v___x_699_ = lean_int_dec_eq(v_d_694_, v___x_698_);
if (v___x_699_ == 0)
{
if (lean_obj_tag(v_p_695_) == 1)
{
lean_object* v_k_700_; lean_object* v_v_701_; lean_object* v_p_702_; lean_object* v___x_703_; 
lean_inc_ref(v_p_695_);
lean_inc(v_d_694_);
v_k_700_ = lean_ctor_get(v_p_695_, 0);
lean_inc(v_k_700_);
v_v_701_ = lean_ctor_get(v_p_695_, 1);
lean_inc(v_v_701_);
v_p_702_ = lean_ctor_get(v_p_695_, 2);
lean_inc_ref(v_p_702_);
lean_inc(v_a_693_);
v___x_703_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(v_a_693_, v___y_681_, v___y_689_);
if (lean_obj_tag(v___x_703_) == 0)
{
lean_object* v_a_704_; lean_object* v___f_705_; lean_object* v___f_706_; uint8_t v___x_707_; uint8_t v___x_708_; uint8_t v___x_709_; 
v_a_704_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_a_704_);
lean_dec_ref_known(v___x_703_, 1);
lean_inc_n(v_v_701_, 2);
lean_inc(v_a_693_);
v___f_705_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed), 3, 2);
lean_closure_set(v___f_705_, 0, v_a_693_);
lean_closure_set(v___f_705_, 1, v_v_701_);
v___f_706_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed), 2, 1);
lean_closure_set(v___f_706_, 0, v_v_701_);
v___x_707_ = 0;
v___x_708_ = lean_unbox(v_a_704_);
lean_dec(v_a_704_);
v___x_709_ = l_Lean_instBEqLBool_beq(v___x_708_, v___x_707_);
if (v___x_709_ == 0)
{
v___y_641_ = v___y_678_;
v___y_642_ = v_v_701_;
v___y_643_ = v___y_679_;
v___y_644_ = v___f_705_;
v___y_645_ = v___f_706_;
v___y_646_ = v_d_694_;
v___y_647_ = v_p_702_;
v___y_648_ = v_k_700_;
v___y_649_ = v_a_693_;
v___y_650_ = v___y_680_;
v___y_651_ = v_p_695_;
v___y_652_ = v___y_681_;
v___y_653_ = v___y_682_;
v___y_654_ = v___y_683_;
v___y_655_ = v___y_684_;
v___y_656_ = v___y_685_;
v___y_657_ = v___y_686_;
v___y_658_ = v___y_687_;
v___y_659_ = v___y_688_;
v___y_660_ = v___y_689_;
v___y_661_ = v___y_690_;
goto v___jp_640_;
}
else
{
lean_object* v___x_710_; 
lean_inc(v_v_701_);
v___x_710_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v_v_701_, v___y_681_);
if (lean_obj_tag(v___x_710_) == 0)
{
lean_dec_ref_known(v___x_710_, 1);
v___y_641_ = v___y_678_;
v___y_642_ = v_v_701_;
v___y_643_ = v___y_679_;
v___y_644_ = v___f_705_;
v___y_645_ = v___f_706_;
v___y_646_ = v_d_694_;
v___y_647_ = v_p_702_;
v___y_648_ = v_k_700_;
v___y_649_ = v_a_693_;
v___y_650_ = v___y_680_;
v___y_651_ = v_p_695_;
v___y_652_ = v___y_681_;
v___y_653_ = v___y_682_;
v___y_654_ = v___y_683_;
v___y_655_ = v___y_684_;
v___y_656_ = v___y_685_;
v___y_657_ = v___y_686_;
v___y_658_ = v___y_687_;
v___y_659_ = v___y_688_;
v___y_660_ = v___y_689_;
v___y_661_ = v___y_690_;
goto v___jp_640_;
}
else
{
lean_dec_ref(v___f_706_);
lean_dec_ref(v___f_705_);
lean_dec_ref(v_p_702_);
lean_dec(v_v_701_);
lean_dec_ref_known(v_p_695_, 3);
lean_dec(v_k_700_);
lean_dec(v_d_694_);
lean_dec(v_a_693_);
lean_dec_ref(v___y_689_);
return v___x_710_;
}
}
}
else
{
lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_718_; 
lean_dec_ref(v_p_702_);
lean_dec(v_v_701_);
lean_dec(v_k_700_);
lean_dec_ref_known(v_p_695_, 3);
lean_dec(v_d_694_);
lean_dec(v_a_693_);
lean_dec_ref(v___y_689_);
v_a_711_ = lean_ctor_get(v___x_703_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_718_ == 0)
{
v___x_713_ = v___x_703_;
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___x_703_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_716_; 
if (v_isShared_714_ == 0)
{
v___x_716_ = v___x_713_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_a_711_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
}
else
{
lean_object* v___x_719_; 
v___x_719_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_a_693_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
lean_dec_ref(v___y_689_);
return v___x_719_;
}
}
else
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; 
lean_inc_ref(v_p_695_);
v___x_720_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_720_, 0, v_a_693_);
v___x_721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_721_, 0, v_p_695_);
lean_ctor_set(v___x_721_, 1, v___x_720_);
lean_inc(v___y_690_);
lean_inc(v___y_688_);
lean_inc_ref(v___y_687_);
lean_inc(v___y_686_);
lean_inc_ref(v___y_685_);
lean_inc(v___y_684_);
lean_inc_ref(v___y_683_);
lean_inc(v___y_682_);
lean_inc(v___y_681_);
v___x_722_ = lean_grind_cutsat_assert_eq(v___x_721_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
if (lean_obj_tag(v___x_722_) == 0)
{
lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_730_; 
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_730_ == 0)
{
lean_object* v_unused_731_; 
v_unused_731_ = lean_ctor_get(v___x_722_, 0);
lean_dec(v_unused_731_);
v___x_724_ = v___x_722_;
v_isShared_725_ = v_isSharedCheck_730_;
goto v_resetjp_723_;
}
else
{
lean_dec(v___x_722_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_730_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_726_; lean_object* v___x_728_; 
v___x_726_ = lean_box(0);
if (v_isShared_725_ == 0)
{
lean_ctor_set(v___x_724_, 0, v___x_726_);
v___x_728_ = v___x_724_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_726_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
else
{
return v___x_722_;
}
}
}
else
{
lean_object* v_options_732_; uint8_t v_hasTrace_733_; 
v_options_732_ = lean_ctor_get(v___y_689_, 1);
v_hasTrace_733_ = lean_ctor_get_uint8(v_options_732_, sizeof(void*)*1);
if (v_hasTrace_733_ == 0)
{
lean_dec(v_a_693_);
lean_dec_ref(v___y_689_);
goto v___jp_487_;
}
else
{
lean_object* v_toCold_734_; lean_object* v_inheritedTraceOptions_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; uint8_t v___x_740_; 
v_toCold_734_ = lean_ctor_get(v___y_689_, 0);
v_inheritedTraceOptions_735_ = lean_ctor_get(v_toCold_734_, 4);
v___x_736_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1));
lean_inc_ref(v___y_679_);
lean_inc_ref(v___y_678_);
lean_inc_ref(v___y_680_);
v___x_737_ = l_Lean_Name_mkStr4(v___y_680_, v___y_678_, v___y_679_, v___x_736_);
v___x_738_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
lean_inc(v___x_737_);
v___x_739_ = l_Lean_Name_append(v___x_738_, v___x_737_);
v___x_740_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_735_, v_options_732_, v___x_739_);
lean_dec(v___x_739_);
if (v___x_740_ == 0)
{
lean_dec(v___x_737_);
lean_dec(v_a_693_);
lean_dec_ref(v___y_689_);
goto v___jp_487_;
}
else
{
lean_object* v___x_741_; 
v___x_741_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_a_693_, v___y_681_, v___y_689_);
if (lean_obj_tag(v___x_741_) == 0)
{
lean_object* v_a_742_; lean_object* v___x_743_; 
v_a_742_ = lean_ctor_get(v___x_741_, 0);
lean_inc(v_a_742_);
lean_dec_ref_known(v___x_741_, 1);
v___x_743_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_737_, v_a_742_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
lean_dec_ref(v___y_689_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_dec_ref_known(v___x_743_, 1);
goto v___jp_487_;
}
else
{
return v___x_743_;
}
}
else
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
lean_dec(v___x_737_);
lean_dec_ref(v___y_689_);
v_a_744_ = lean_ctor_get(v___x_741_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___x_741_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_741_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_744_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
}
}
}
else
{
lean_object* v_options_752_; uint8_t v_hasTrace_753_; 
v_options_752_ = lean_ctor_get(v___y_689_, 1);
v_hasTrace_753_ = lean_ctor_get_uint8(v_options_752_, sizeof(void*)*1);
if (v_hasTrace_753_ == 0)
{
v___y_605_ = v_a_693_;
v___y_606_ = v___y_681_;
v___y_607_ = v___y_682_;
v___y_608_ = v___y_683_;
v___y_609_ = v___y_684_;
v___y_610_ = v___y_685_;
v___y_611_ = v___y_686_;
v___y_612_ = v___y_687_;
v___y_613_ = v___y_688_;
v___y_614_ = v___y_689_;
v___y_615_ = v___y_690_;
goto v___jp_604_;
}
else
{
lean_object* v_toCold_754_; lean_object* v_inheritedTraceOptions_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; uint8_t v___x_760_; 
v_toCold_754_ = lean_ctor_get(v___y_689_, 0);
v_inheritedTraceOptions_755_ = lean_ctor_get(v_toCold_754_, 4);
v___x_756_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2));
lean_inc_ref(v___y_679_);
lean_inc_ref(v___y_678_);
lean_inc_ref(v___y_680_);
v___x_757_ = l_Lean_Name_mkStr4(v___y_680_, v___y_678_, v___y_679_, v___x_756_);
v___x_758_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
lean_inc(v___x_757_);
v___x_759_ = l_Lean_Name_append(v___x_758_, v___x_757_);
v___x_760_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_755_, v_options_752_, v___x_759_);
lean_dec(v___x_759_);
if (v___x_760_ == 0)
{
lean_dec(v___x_757_);
v___y_605_ = v_a_693_;
v___y_606_ = v___y_681_;
v___y_607_ = v___y_682_;
v___y_608_ = v___y_683_;
v___y_609_ = v___y_684_;
v___y_610_ = v___y_685_;
v___y_611_ = v___y_686_;
v___y_612_ = v___y_687_;
v___y_613_ = v___y_688_;
v___y_614_ = v___y_689_;
v___y_615_ = v___y_690_;
goto v___jp_604_;
}
else
{
lean_object* v___x_761_; 
lean_inc(v_a_693_);
v___x_761_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_a_693_, v___y_681_, v___y_689_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_a_762_; lean_object* v___x_763_; 
v_a_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_a_762_);
lean_dec_ref_known(v___x_761_, 1);
v___x_763_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_757_, v_a_762_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_dec_ref_known(v___x_763_, 1);
v___y_605_ = v_a_693_;
v___y_606_ = v___y_681_;
v___y_607_ = v___y_682_;
v___y_608_ = v___y_683_;
v___y_609_ = v___y_684_;
v___y_610_ = v___y_685_;
v___y_611_ = v___y_686_;
v___y_612_ = v___y_687_;
v___y_613_ = v___y_688_;
v___y_614_ = v___y_689_;
v___y_615_ = v___y_690_;
goto v___jp_604_;
}
else
{
lean_dec(v_a_693_);
lean_dec_ref(v___y_689_);
return v___x_763_;
}
}
else
{
lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_771_; 
lean_dec(v___x_757_);
lean_dec(v_a_693_);
lean_dec_ref(v___y_689_);
v_a_764_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_771_ == 0)
{
v___x_766_ = v___x_761_;
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v___x_761_);
v___x_766_ = lean_box(0);
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
v_resetjp_765_:
{
lean_object* v___x_769_; 
if (v_isShared_767_ == 0)
{
v___x_769_ = v___x_766_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_770_; 
v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_770_, 0, v_a_764_);
v___x_769_ = v_reuseFailAlloc_770_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
return v___x_769_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_772_; lean_object* v___x_774_; uint8_t v_isShared_775_; uint8_t v_isSharedCheck_779_; 
lean_dec_ref(v___y_689_);
v_a_772_ = lean_ctor_get(v___x_692_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_692_);
if (v_isSharedCheck_779_ == 0)
{
v___x_774_ = v___x_692_;
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
else
{
lean_inc(v_a_772_);
lean_dec(v___x_692_);
v___x_774_ = lean_box(0);
v_isShared_775_ = v_isSharedCheck_779_;
goto v_resetjp_773_;
}
v_resetjp_773_:
{
lean_object* v___x_777_; 
if (v_isShared_775_ == 0)
{
v___x_777_ = v___x_774_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_a_772_);
v___x_777_ = v_reuseFailAlloc_778_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
return v___x_777_;
}
}
}
}
v___jp_780_:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_781_ = lean_unsigned_to_nat(1u);
v___x_782_ = lean_nat_add(v_currRecDepth_629_, v___x_781_);
lean_dec(v_currRecDepth_629_);
lean_inc_ref(v_options_628_);
lean_inc_ref(v_toCold_627_);
v___x_783_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_783_, 0, v_toCold_627_);
lean_ctor_set(v___x_783_, 1, v_options_628_);
lean_ctor_set(v___x_783_, 2, v___x_782_);
lean_ctor_set(v___x_783_, 3, v_maxRecDepth_630_);
lean_ctor_set(v___x_783_, 4, v_ref_631_);
lean_ctor_set(v___x_783_, 5, v_currNamespace_632_);
lean_ctor_set(v___x_783_, 6, v_openDecls_633_);
lean_ctor_set(v___x_783_, 7, v_initHeartbeats_634_);
lean_ctor_set(v___x_783_, 8, v_maxHeartbeats_635_);
lean_ctor_set(v___x_783_, 9, v_currMacroScope_636_);
lean_ctor_set_uint8(v___x_783_, sizeof(void*)*10, v_diag_637_);
lean_ctor_set_uint8(v___x_783_, sizeof(void*)*10 + 1, v_suppressElabErrors_638_);
v___x_784_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_476_, v___x_783_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_a_785_; lean_object* v___x_787_; uint8_t v_isShared_788_; uint8_t v_isSharedCheck_813_; 
v_a_785_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_813_ == 0)
{
v___x_787_ = v___x_784_;
v_isShared_788_ = v_isSharedCheck_813_;
goto v_resetjp_786_;
}
else
{
lean_inc(v_a_785_);
lean_dec(v___x_784_);
v___x_787_ = lean_box(0);
v_isShared_788_ = v_isSharedCheck_813_;
goto v_resetjp_786_;
}
v_resetjp_786_:
{
uint8_t v___x_789_; 
v___x_789_ = lean_unbox(v_a_785_);
lean_dec(v_a_785_);
if (v___x_789_ == 0)
{
uint8_t v_hasTrace_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; 
lean_del_object(v___x_787_);
v_hasTrace_790_ = lean_ctor_get_uint8(v_options_628_, sizeof(void*)*1);
v___x_791_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0));
v___x_792_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2));
v___x_793_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3));
if (v_hasTrace_790_ == 0)
{
lean_dec_ref(v_options_628_);
lean_dec_ref(v_toCold_627_);
v___y_678_ = v___x_792_;
v___y_679_ = v___x_793_;
v___y_680_ = v___x_791_;
v___y_681_ = v_a_476_;
v___y_682_ = v_a_477_;
v___y_683_ = v_a_478_;
v___y_684_ = v_a_479_;
v___y_685_ = v_a_480_;
v___y_686_ = v_a_481_;
v___y_687_ = v_a_482_;
v___y_688_ = v_a_483_;
v___y_689_ = v___x_783_;
v___y_690_ = v_a_485_;
goto v___jp_677_;
}
else
{
lean_object* v_inheritedTraceOptions_794_; lean_object* v___x_795_; lean_object* v___x_796_; uint8_t v___x_797_; 
v_inheritedTraceOptions_794_ = lean_ctor_get(v_toCold_627_, 4);
lean_inc_ref(v_inheritedTraceOptions_794_);
lean_dec_ref(v_toCold_627_);
v___x_795_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4));
v___x_796_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5);
v___x_797_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_794_, v_options_628_, v___x_796_);
lean_dec_ref(v_options_628_);
lean_dec_ref(v_inheritedTraceOptions_794_);
if (v___x_797_ == 0)
{
v___y_678_ = v___x_792_;
v___y_679_ = v___x_793_;
v___y_680_ = v___x_791_;
v___y_681_ = v_a_476_;
v___y_682_ = v_a_477_;
v___y_683_ = v_a_478_;
v___y_684_ = v_a_479_;
v___y_685_ = v_a_480_;
v___y_686_ = v_a_481_;
v___y_687_ = v_a_482_;
v___y_688_ = v_a_483_;
v___y_689_ = v___x_783_;
v___y_690_ = v_a_485_;
goto v___jp_677_;
}
else
{
lean_object* v___x_798_; 
lean_inc_ref(v_c_475_);
v___x_798_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_475_, v_a_476_, v___x_783_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v_a_799_; lean_object* v___x_800_; 
v_a_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_a_799_);
lean_dec_ref_known(v___x_798_, 1);
v___x_800_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_795_, v_a_799_, v_a_482_, v_a_483_, v___x_783_, v_a_485_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_dec_ref_known(v___x_800_, 1);
v___y_678_ = v___x_792_;
v___y_679_ = v___x_793_;
v___y_680_ = v___x_791_;
v___y_681_ = v_a_476_;
v___y_682_ = v_a_477_;
v___y_683_ = v_a_478_;
v___y_684_ = v_a_479_;
v___y_685_ = v_a_480_;
v___y_686_ = v_a_481_;
v___y_687_ = v_a_482_;
v___y_688_ = v_a_483_;
v___y_689_ = v___x_783_;
v___y_690_ = v_a_485_;
goto v___jp_677_;
}
else
{
lean_dec_ref_known(v___x_783_, 10);
lean_dec_ref(v_c_475_);
return v___x_800_;
}
}
else
{
lean_object* v_a_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_808_; 
lean_dec_ref_known(v___x_783_, 10);
lean_dec_ref(v_c_475_);
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
}
else
{
lean_object* v___x_809_; lean_object* v___x_811_; 
lean_dec_ref_known(v___x_783_, 10);
lean_dec_ref(v_options_628_);
lean_dec_ref(v_toCold_627_);
lean_dec_ref(v_c_475_);
v___x_809_ = lean_box(0);
if (v_isShared_788_ == 0)
{
lean_ctor_set(v___x_787_, 0, v___x_809_);
v___x_811_ = v___x_787_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v___x_809_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
else
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_821_; 
lean_dec_ref_known(v___x_783_, 10);
lean_dec_ref(v_options_628_);
lean_dec_ref(v_toCold_627_);
lean_dec_ref(v_c_475_);
v_a_814_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_821_ == 0)
{
v___x_816_ = v___x_784_;
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_784_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_819_; 
if (v_isShared_817_ == 0)
{
v___x_819_ = v___x_816_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_a_814_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___boxed(lean_object* v_c_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v_c_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_);
lean_dec(v_a_836_);
lean_dec(v_a_834_);
lean_dec_ref(v_a_833_);
lean_dec(v_a_832_);
lean_dec_ref(v_a_831_);
lean_dec(v_a_830_);
lean_dec_ref(v_a_829_);
lean_dec(v_a_828_);
lean_dec(v_a_827_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(lean_object* v_c_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_){
_start:
{
lean_object* v_d_851_; lean_object* v_p_852_; lean_object* v___x_853_; 
v_d_851_ = lean_ctor_get(v_c_839_, 0);
v_p_852_ = lean_ctor_get(v_c_839_, 1);
lean_inc_ref(v_p_852_);
v___x_853_ = l_Int_Internal_Linear_Poly_normCommRing_x3f(v_p_852_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
if (lean_obj_tag(v___x_853_) == 0)
{
lean_object* v_a_854_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
lean_inc(v_a_854_);
lean_dec_ref_known(v___x_853_, 1);
if (lean_obj_tag(v_a_854_) == 1)
{
lean_object* v_val_855_; lean_object* v_snd_856_; lean_object* v_fst_857_; lean_object* v_fst_858_; lean_object* v_snd_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
lean_inc(v_d_851_);
v_val_855_ = lean_ctor_get(v_a_854_, 0);
lean_inc(v_val_855_);
lean_dec_ref_known(v_a_854_, 1);
v_snd_856_ = lean_ctor_get(v_val_855_, 1);
lean_inc(v_snd_856_);
v_fst_857_ = lean_ctor_get(v_val_855_, 0);
lean_inc(v_fst_857_);
lean_dec(v_val_855_);
v_fst_858_ = lean_ctor_get(v_snd_856_, 0);
lean_inc(v_fst_858_);
v_snd_859_ = lean_ctor_get(v_snd_856_, 1);
lean_inc(v_snd_859_);
lean_dec(v_snd_856_);
v___x_860_ = lean_alloc_ctor(12, 3, 0);
lean_ctor_set(v___x_860_, 0, v_c_839_);
lean_ctor_set(v___x_860_, 1, v_fst_857_);
lean_ctor_set(v___x_860_, 2, v_fst_858_);
v___x_861_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_861_, 0, v_d_851_);
lean_ctor_set(v___x_861_, 1, v_snd_859_);
lean_ctor_set(v___x_861_, 2, v___x_860_);
lean_inc_ref(v_a_848_);
v___x_862_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v___x_861_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
return v___x_862_;
}
else
{
lean_object* v___x_863_; 
lean_dec(v_a_854_);
lean_inc_ref(v_a_848_);
v___x_863_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v_c_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
return v___x_863_;
}
}
else
{
lean_object* v_a_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_871_; 
lean_dec_ref(v_c_839_);
v_a_864_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_871_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_871_ == 0)
{
v___x_866_ = v___x_853_;
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_a_864_);
lean_dec(v___x_853_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_871_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
if (v_isShared_867_ == 0)
{
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_870_; 
v_reuseFailAlloc_870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_870_, 0, v_a_864_);
v___x_869_ = v_reuseFailAlloc_870_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
return v___x_869_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore___boxed(lean_object* v_c_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v_c_872_, v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_);
lean_dec(v_a_882_);
lean_dec_ref(v_a_881_);
lean_dec(v_a_880_);
lean_dec_ref(v_a_879_);
lean_dec(v_a_878_);
lean_dec_ref(v_a_877_);
lean_dec(v_a_876_);
lean_dec_ref(v_a_875_);
lean_dec(v_a_874_);
lean_dec(v_a_873_);
return v_res_884_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8(void){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; 
v___x_899_ = lean_box(0);
v___x_900_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7));
v___x_901_ = l_Lean_mkConst(v___x_900_, v___x_899_);
return v___x_901_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10(void){
_start:
{
lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_903_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9));
v___x_904_ = l_Lean_stringToMessageData(v___x_903_);
return v___x_904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(lean_object* v_e_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_){
_start:
{
lean_object* v___x_920_; 
lean_inc_ref(v_e_905_);
v___x_920_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_905_, v_a_913_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_1054_; 
v_a_921_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_923_ = v___x_920_;
v_isShared_924_ = v_isSharedCheck_1054_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_920_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_1054_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_930_; uint8_t v___x_931_; 
v___x_930_ = l_Lean_Expr_cleanupAnnotations(v_a_921_);
v___x_931_ = l_Lean_Expr_isApp(v___x_930_);
if (v___x_931_ == 0)
{
lean_dec_ref(v___x_930_);
lean_dec_ref(v_e_905_);
goto v___jp_925_;
}
else
{
lean_object* v_arg_932_; lean_object* v___x_933_; uint8_t v___x_934_; 
v_arg_932_ = lean_ctor_get(v___x_930_, 1);
lean_inc_ref(v_arg_932_);
v___x_933_ = l_Lean_Expr_appFnCleanup___redArg(v___x_930_);
v___x_934_ = l_Lean_Expr_isApp(v___x_933_);
if (v___x_934_ == 0)
{
lean_dec_ref(v___x_933_);
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_e_905_);
goto v___jp_925_;
}
else
{
lean_object* v_arg_935_; lean_object* v___x_936_; uint8_t v___x_937_; 
v_arg_935_ = lean_ctor_get(v___x_933_, 1);
lean_inc_ref(v_arg_935_);
v___x_936_ = l_Lean_Expr_appFnCleanup___redArg(v___x_933_);
v___x_937_ = l_Lean_Expr_isApp(v___x_936_);
if (v___x_937_ == 0)
{
lean_dec_ref(v___x_936_);
lean_dec_ref(v_arg_935_);
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_e_905_);
goto v___jp_925_;
}
else
{
lean_object* v_arg_938_; lean_object* v___x_939_; uint8_t v___x_940_; 
v_arg_938_ = lean_ctor_get(v___x_936_, 1);
lean_inc_ref(v_arg_938_);
v___x_939_ = l_Lean_Expr_appFnCleanup___redArg(v___x_936_);
v___x_940_ = l_Lean_Expr_isApp(v___x_939_);
if (v___x_940_ == 0)
{
lean_dec_ref(v___x_939_);
lean_dec_ref(v_arg_938_);
lean_dec_ref(v_arg_935_);
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_e_905_);
goto v___jp_925_;
}
else
{
lean_object* v___x_941_; lean_object* v___x_942_; uint8_t v___x_943_; 
v___x_941_ = l_Lean_Expr_appFnCleanup___redArg(v___x_939_);
v___x_942_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_943_ = l_Lean_Expr_isConstOf(v___x_941_, v___x_942_);
lean_dec_ref(v___x_941_);
if (v___x_943_ == 0)
{
lean_dec_ref(v_arg_938_);
lean_dec_ref(v_arg_935_);
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_e_905_);
goto v___jp_925_;
}
else
{
lean_object* v___x_944_; 
lean_del_object(v___x_923_);
v___x_944_ = l_Lean_Meta_Structural_isInstDvdInt___redArg(v_arg_938_, v_a_913_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_1045_; 
v_a_945_ = lean_ctor_get(v___x_944_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_947_ = v___x_944_;
v_isShared_948_ = v_isSharedCheck_1045_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_dec(v___x_944_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_1045_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
uint8_t v___x_949_; 
v___x_949_ = lean_unbox(v_a_945_);
lean_dec(v_a_945_);
if (v___x_949_ == 0)
{
lean_object* v___x_950_; lean_object* v___x_952_; 
lean_dec_ref(v_arg_935_);
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_e_905_);
v___x_950_ = lean_box(0);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 0, v___x_950_);
v___x_952_ = v___x_947_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v___x_950_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
else
{
lean_object* v___x_954_; 
lean_del_object(v___x_947_);
lean_inc_ref(v_arg_935_);
v___x_954_ = l_Lean_Meta_getIntValue_x3f(v_arg_935_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
if (lean_obj_tag(v___x_954_) == 0)
{
lean_object* v_a_955_; 
v_a_955_ = lean_ctor_get(v___x_954_, 0);
lean_inc(v_a_955_);
lean_dec_ref_known(v___x_954_, 1);
if (lean_obj_tag(v_a_955_) == 1)
{
lean_object* v_val_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_1021_; 
v_val_956_ = lean_ctor_get(v_a_955_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v_a_955_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_958_ = v_a_955_;
v_isShared_959_ = v_isSharedCheck_1021_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_val_956_);
lean_dec(v_a_955_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_1021_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
lean_object* v___x_960_; 
lean_inc_ref(v_e_905_);
v___x_960_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_905_, v_a_906_, v_a_910_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; uint8_t v___x_962_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_a_961_);
lean_dec_ref_known(v___x_960_, 1);
v___x_962_ = lean_unbox(v_a_961_);
lean_dec(v_a_961_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; 
lean_del_object(v___x_958_);
lean_dec(v_val_956_);
lean_inc_ref(v_e_905_);
v___x_963_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_905_, v_a_906_, v_a_910_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v_a_964_; lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_989_; 
v_a_964_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_989_ == 0)
{
v___x_966_ = v___x_963_;
v_isShared_967_ = v_isSharedCheck_989_;
goto v_resetjp_965_;
}
else
{
lean_inc(v_a_964_);
lean_dec(v___x_963_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_989_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
uint8_t v___x_968_; 
v___x_968_ = lean_unbox(v_a_964_);
lean_dec(v_a_964_);
if (v___x_968_ == 0)
{
lean_object* v___x_969_; lean_object* v___x_971_; 
lean_dec_ref(v_arg_935_);
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_e_905_);
v___x_969_ = lean_box(0);
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 0, v___x_969_);
v___x_971_ = v___x_966_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_969_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
else
{
lean_object* v___x_973_; 
lean_del_object(v___x_966_);
lean_inc_ref(v_e_905_);
v___x_973_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_905_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
lean_inc(v_a_974_);
lean_dec_ref_known(v___x_973_, 1);
v___x_975_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8);
v___x_976_ = l_Lean_eagerReflBoolTrue;
v___x_977_ = l_Lean_Meta_mkOfEqFalseCore(v_e_905_, v_a_974_);
v___x_978_ = l_Lean_mkApp4(v___x_975_, v_arg_935_, v_arg_932_, v___x_976_, v___x_977_);
v___x_979_ = lean_unsigned_to_nat(0u);
v___x_980_ = l_Lean_Meta_Grind_pushNewFact(v___x_978_, v___x_979_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
return v___x_980_;
}
else
{
lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_988_; 
lean_dec_ref(v_arg_935_);
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_e_905_);
v_a_981_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_988_ == 0)
{
v___x_983_ = v___x_973_;
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v___x_973_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_986_; 
if (v_isShared_984_ == 0)
{
v___x_986_ = v___x_983_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_a_981_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
}
}
else
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_997_; 
lean_dec_ref(v_arg_935_);
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_e_905_);
v_a_990_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_997_ == 0)
{
v___x_992_ = v___x_963_;
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_963_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_995_; 
if (v_isShared_993_ == 0)
{
v___x_995_ = v___x_992_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v_a_990_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
}
else
{
lean_object* v___x_998_; 
lean_dec_ref(v_arg_935_);
v___x_998_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(v_arg_932_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v___x_1001_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_a_999_);
lean_dec_ref_known(v___x_998_, 1);
if (v_isShared_959_ == 0)
{
lean_ctor_set_tag(v___x_958_, 0);
lean_ctor_set(v___x_958_, 0, v_e_905_);
v___x_1001_ = v___x_958_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_e_905_);
v___x_1001_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_1002_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1002_, 0, v_val_956_);
lean_ctor_set(v___x_1002_, 1, v_a_999_);
lean_ctor_set(v___x_1002_, 2, v___x_1001_);
v___x_1003_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v___x_1002_, v_a_906_, v_a_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
return v___x_1003_;
}
}
else
{
lean_object* v_a_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1012_; 
lean_del_object(v___x_958_);
lean_dec(v_val_956_);
lean_dec_ref(v_e_905_);
v_a_1005_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_1007_ = v___x_998_;
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_dec(v___x_998_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1012_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
lean_object* v___x_1010_; 
if (v_isShared_1008_ == 0)
{
v___x_1010_ = v___x_1007_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_a_1005_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
}
}
else
{
lean_object* v_a_1013_; lean_object* v___x_1015_; uint8_t v_isShared_1016_; uint8_t v_isSharedCheck_1020_; 
lean_del_object(v___x_958_);
lean_dec(v_val_956_);
lean_dec_ref(v_arg_935_);
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_e_905_);
v_a_1013_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_1020_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_1020_ == 0)
{
v___x_1015_ = v___x_960_;
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
else
{
lean_inc(v_a_1013_);
lean_dec(v___x_960_);
v___x_1015_ = lean_box(0);
v_isShared_1016_ = v_isSharedCheck_1020_;
goto v_resetjp_1014_;
}
v_resetjp_1014_:
{
lean_object* v___x_1018_; 
if (v_isShared_1016_ == 0)
{
v___x_1018_ = v___x_1015_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1019_; 
v_reuseFailAlloc_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_a_1013_);
v___x_1018_ = v_reuseFailAlloc_1019_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
return v___x_1018_;
}
}
}
}
}
else
{
lean_object* v___x_1022_; 
lean_dec(v_a_955_);
lean_dec_ref(v_arg_935_);
lean_dec_ref(v_arg_932_);
v___x_1022_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_910_);
if (lean_obj_tag(v___x_1022_) == 0)
{
lean_object* v_a_1023_; uint8_t v_verbose_1024_; 
v_a_1023_ = lean_ctor_get(v___x_1022_, 0);
lean_inc(v_a_1023_);
lean_dec_ref_known(v___x_1022_, 1);
v_verbose_1024_ = lean_ctor_get_uint8(v_a_1023_, 0);
lean_dec(v_a_1023_);
if (v_verbose_1024_ == 0)
{
lean_dec_ref(v_e_905_);
goto v___jp_917_;
}
else
{
lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1025_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10);
v___x_1026_ = l_Lean_indentExpr(v_e_905_);
v___x_1027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1025_);
lean_ctor_set(v___x_1027_, 1, v___x_1026_);
v___x_1028_ = l_Lean_Meta_Sym_reportIssue(v___x_1027_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_dec_ref_known(v___x_1028_, 1);
goto v___jp_917_;
}
else
{
return v___x_1028_;
}
}
}
else
{
lean_object* v_a_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1036_; 
lean_dec_ref(v_e_905_);
v_a_1029_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1036_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1036_ == 0)
{
v___x_1031_ = v___x_1022_;
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_a_1029_);
lean_dec(v___x_1022_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1036_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1034_; 
if (v_isShared_1032_ == 0)
{
v___x_1034_ = v___x_1031_;
goto v_reusejp_1033_;
}
else
{
lean_object* v_reuseFailAlloc_1035_; 
v_reuseFailAlloc_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_a_1029_);
v___x_1034_ = v_reuseFailAlloc_1035_;
goto v_reusejp_1033_;
}
v_reusejp_1033_:
{
return v___x_1034_;
}
}
}
}
}
else
{
lean_object* v_a_1037_; lean_object* v___x_1039_; uint8_t v_isShared_1040_; uint8_t v_isSharedCheck_1044_; 
lean_dec_ref(v_arg_935_);
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_e_905_);
v_a_1037_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_1039_ = v___x_954_;
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
else
{
lean_inc(v_a_1037_);
lean_dec(v___x_954_);
v___x_1039_ = lean_box(0);
v_isShared_1040_ = v_isSharedCheck_1044_;
goto v_resetjp_1038_;
}
v_resetjp_1038_:
{
lean_object* v___x_1042_; 
if (v_isShared_1040_ == 0)
{
v___x_1042_ = v___x_1039_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v_a_1037_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
}
}
}
else
{
lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1053_; 
lean_dec_ref(v_arg_935_);
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_e_905_);
v_a_1046_ = lean_ctor_get(v___x_944_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1048_ = v___x_944_;
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v___x_944_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1051_; 
if (v_isShared_1049_ == 0)
{
v___x_1051_ = v___x_1048_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v_a_1046_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
}
}
}
}
}
v___jp_925_:
{
lean_object* v___x_926_; lean_object* v___x_928_; 
v___x_926_ = lean_box(0);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 0, v___x_926_);
v___x_928_ = v___x_923_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_926_);
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
else
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
lean_dec_ref(v_e_905_);
v_a_1055_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1057_ = v___x_920_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_920_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v___x_1060_; 
if (v_isShared_1058_ == 0)
{
v___x_1060_ = v___x_1057_;
goto v_reusejp_1059_;
}
else
{
lean_object* v_reuseFailAlloc_1061_; 
v_reuseFailAlloc_1061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1061_, 0, v_a_1055_);
v___x_1060_ = v_reuseFailAlloc_1061_;
goto v_reusejp_1059_;
}
v_reusejp_1059_:
{
return v___x_1060_;
}
}
}
v___jp_917_:
{
lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_918_ = lean_box(0);
v___x_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_919_, 0, v___x_918_);
return v___x_919_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___boxed(lean_object* v_e_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_){
_start:
{
lean_object* v_res_1075_; 
v_res_1075_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(v_e_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_);
lean_dec(v_a_1073_);
lean_dec_ref(v_a_1072_);
lean_dec(v_a_1071_);
lean_dec_ref(v_a_1070_);
lean_dec(v_a_1069_);
lean_dec_ref(v_a_1068_);
lean_dec(v_a_1067_);
lean_dec_ref(v_a_1066_);
lean_dec(v_a_1065_);
lean_dec(v_a_1064_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd_spec__0(lean_object* v_a_1076_){
_start:
{
lean_object* v___x_1077_; 
v___x_1077_ = lean_nat_to_int(v_a_1076_);
return v___x_1077_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3(void){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1083_ = lean_box(0);
v___x_1084_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2));
v___x_1085_ = l_Lean_mkConst(v___x_1084_, v___x_1083_);
return v___x_1085_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7(void){
_start:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1092_ = lean_box(0);
v___x_1093_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6));
v___x_1094_ = l_Lean_mkConst(v___x_1093_, v___x_1092_);
return v___x_1094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(lean_object* v_e_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_){
_start:
{
lean_object* v___x_1113_; uint8_t v___x_1114_; 
lean_inc_ref(v_e_1095_);
v___x_1113_ = l_Lean_Expr_cleanupAnnotations(v_e_1095_);
v___x_1114_ = l_Lean_Expr_isApp(v___x_1113_);
if (v___x_1114_ == 0)
{
lean_dec_ref(v___x_1113_);
lean_dec_ref(v_e_1095_);
goto v___jp_1107_;
}
else
{
lean_object* v_arg_1115_; lean_object* v___x_1116_; uint8_t v___x_1117_; 
v_arg_1115_ = lean_ctor_get(v___x_1113_, 1);
lean_inc_ref(v_arg_1115_);
v___x_1116_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1113_);
v___x_1117_ = l_Lean_Expr_isApp(v___x_1116_);
if (v___x_1117_ == 0)
{
lean_dec_ref(v___x_1116_);
lean_dec_ref(v_arg_1115_);
lean_dec_ref(v_e_1095_);
goto v___jp_1107_;
}
else
{
lean_object* v_arg_1118_; lean_object* v___x_1119_; uint8_t v___x_1120_; 
v_arg_1118_ = lean_ctor_get(v___x_1116_, 1);
lean_inc_ref(v_arg_1118_);
v___x_1119_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1116_);
v___x_1120_ = l_Lean_Expr_isApp(v___x_1119_);
if (v___x_1120_ == 0)
{
lean_dec_ref(v___x_1119_);
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_arg_1115_);
lean_dec_ref(v_e_1095_);
goto v___jp_1107_;
}
else
{
lean_object* v_arg_1121_; lean_object* v___x_1122_; uint8_t v___x_1123_; 
v_arg_1121_ = lean_ctor_get(v___x_1119_, 1);
lean_inc_ref(v_arg_1121_);
v___x_1122_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1119_);
v___x_1123_ = l_Lean_Expr_isApp(v___x_1122_);
if (v___x_1123_ == 0)
{
lean_dec_ref(v___x_1122_);
lean_dec_ref(v_arg_1121_);
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_arg_1115_);
lean_dec_ref(v_e_1095_);
goto v___jp_1107_;
}
else
{
lean_object* v___x_1124_; lean_object* v___x_1125_; uint8_t v___x_1126_; 
v___x_1124_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1122_);
v___x_1125_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1126_ = l_Lean_Expr_isConstOf(v___x_1124_, v___x_1125_);
lean_dec_ref(v___x_1124_);
if (v___x_1126_ == 0)
{
lean_dec_ref(v_arg_1121_);
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_arg_1115_);
lean_dec_ref(v_e_1095_);
goto v___jp_1107_;
}
else
{
lean_object* v___x_1127_; 
v___x_1127_ = l_Lean_Meta_Structural_isInstDvdNat___redArg(v_arg_1121_, v_a_1103_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1259_; 
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1130_ = v___x_1127_;
v_isShared_1131_ = v_isSharedCheck_1259_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1127_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1259_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
uint8_t v___x_1132_; 
v___x_1132_ = lean_unbox(v_a_1128_);
lean_dec(v_a_1128_);
if (v___x_1132_ == 0)
{
lean_object* v___x_1133_; lean_object* v___x_1135_; 
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_arg_1115_);
lean_dec_ref(v_e_1095_);
v___x_1133_ = lean_box(0);
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 0, v___x_1133_);
v___x_1135_ = v___x_1130_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___x_1133_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
else
{
lean_object* v___x_1137_; 
lean_del_object(v___x_1130_);
v___x_1137_ = l_Lean_Meta_getNatValue_x3f(v_arg_1118_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v_a_1138_; 
v_a_1138_ = lean_ctor_get(v___x_1137_, 0);
lean_inc(v_a_1138_);
lean_dec_ref_known(v___x_1137_, 1);
if (lean_obj_tag(v_a_1138_) == 1)
{
lean_object* v_val_1139_; lean_object* v___x_1140_; 
v_val_1139_ = lean_ctor_get(v_a_1138_, 0);
lean_inc(v_val_1139_);
lean_dec_ref_known(v_a_1138_, 1);
lean_inc_ref(v_e_1095_);
v___x_1140_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_1095_, v_a_1096_, v_a_1100_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v_a_1141_; uint8_t v___x_1142_; 
v_a_1141_ = lean_ctor_get(v___x_1140_, 0);
lean_inc(v_a_1141_);
lean_dec_ref_known(v___x_1140_, 1);
v___x_1142_ = lean_unbox(v_a_1141_);
lean_dec(v_a_1141_);
if (v___x_1142_ == 0)
{
lean_object* v___x_1143_; 
lean_dec(v_val_1139_);
lean_inc_ref(v_e_1095_);
v___x_1143_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_1095_, v_a_1096_, v_a_1100_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1168_; 
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1146_ = v___x_1143_;
v_isShared_1147_ = v_isSharedCheck_1168_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_1143_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1168_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
uint8_t v___x_1148_; 
v___x_1148_ = lean_unbox(v_a_1144_);
lean_dec(v_a_1144_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; lean_object* v___x_1151_; 
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_arg_1115_);
lean_dec_ref(v_e_1095_);
v___x_1149_ = lean_box(0);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 0, v___x_1149_);
v___x_1151_ = v___x_1146_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1149_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
else
{
lean_object* v___x_1153_; 
lean_del_object(v___x_1146_);
lean_inc_ref(v_e_1095_);
v___x_1153_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
if (lean_obj_tag(v___x_1153_) == 0)
{
lean_object* v_a_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; 
v_a_1154_ = lean_ctor_get(v___x_1153_, 0);
lean_inc(v_a_1154_);
lean_dec_ref_known(v___x_1153_, 1);
v___x_1155_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3);
v___x_1156_ = l_Lean_Meta_mkOfEqFalseCore(v_e_1095_, v_a_1154_);
v___x_1157_ = l_Lean_mkApp3(v___x_1155_, v_arg_1118_, v_arg_1115_, v___x_1156_);
v___x_1158_ = lean_unsigned_to_nat(0u);
v___x_1159_ = l_Lean_Meta_Grind_pushNewFact(v___x_1157_, v___x_1158_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
return v___x_1159_;
}
else
{
lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1167_; 
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_arg_1115_);
lean_dec_ref(v_e_1095_);
v_a_1160_ = lean_ctor_get(v___x_1153_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1153_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1162_ = v___x_1153_;
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v___x_1153_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1165_; 
if (v_isShared_1163_ == 0)
{
v___x_1165_ = v___x_1162_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1160_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
}
}
else
{
lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1176_; 
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_arg_1115_);
lean_dec_ref(v_e_1095_);
v_a_1169_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1171_ = v___x_1143_;
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1143_);
v___x_1171_ = lean_box(0);
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
v_resetjp_1170_:
{
lean_object* v___x_1174_; 
if (v_isShared_1172_ == 0)
{
v___x_1174_ = v___x_1171_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1175_; 
v_reuseFailAlloc_1175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1175_, 0, v_a_1169_);
v___x_1174_ = v_reuseFailAlloc_1175_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
return v___x_1174_;
}
}
}
}
else
{
lean_object* v___x_1177_; 
lean_inc_ref(v_arg_1118_);
v___x_1177_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_1118_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1178_; lean_object* v_fst_1179_; lean_object* v_snd_1180_; lean_object* v___x_1181_; 
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
lean_inc(v_a_1178_);
lean_dec_ref_known(v___x_1177_, 1);
v_fst_1179_ = lean_ctor_get(v_a_1178_, 0);
lean_inc(v_fst_1179_);
v_snd_1180_ = lean_ctor_get(v_a_1178_, 1);
lean_inc(v_snd_1180_);
lean_dec(v_a_1178_);
lean_inc_ref(v_arg_1115_);
v___x_1181_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_1115_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
if (lean_obj_tag(v___x_1181_) == 0)
{
lean_object* v_a_1182_; lean_object* v_fst_1183_; lean_object* v_snd_1184_; lean_object* v___x_1185_; 
v_a_1182_ = lean_ctor_get(v___x_1181_, 0);
lean_inc(v_a_1182_);
lean_dec_ref_known(v___x_1181_, 1);
v_fst_1183_ = lean_ctor_get(v_a_1182_, 0);
lean_inc(v_fst_1183_);
v_snd_1184_ = lean_ctor_get(v_a_1182_, 1);
lean_inc(v_snd_1184_);
lean_dec(v_a_1182_);
v___x_1185_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1095_, v_a_1096_);
if (lean_obj_tag(v___x_1185_) == 0)
{
lean_object* v_a_1186_; lean_object* v___x_1187_; 
v_a_1186_ = lean_ctor_get(v___x_1185_, 0);
lean_inc(v_a_1186_);
lean_dec_ref_known(v___x_1185_, 1);
lean_inc(v_fst_1183_);
v___x_1187_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_1183_, v_a_1186_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_object* v_a_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
v_a_1188_ = lean_ctor_get(v___x_1187_, 0);
lean_inc(v_a_1188_);
lean_dec_ref_known(v___x_1187_, 1);
v___x_1189_ = l_Int_Internal_Linear_Expr_norm(v_a_1188_);
v___x_1190_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7);
v___x_1191_ = l_Lean_mkApp6(v___x_1190_, v_arg_1118_, v_arg_1115_, v_fst_1179_, v_fst_1183_, v_snd_1180_, v_snd_1184_);
lean_inc(v_val_1139_);
v___x_1192_ = lean_nat_to_int(v_val_1139_);
v___x_1193_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1193_, 0, v_e_1095_);
lean_ctor_set(v___x_1193_, 1, v___x_1191_);
lean_ctor_set(v___x_1193_, 2, v_val_1139_);
lean_ctor_set(v___x_1193_, 3, v_a_1188_);
v___x_1194_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1192_);
lean_ctor_set(v___x_1194_, 1, v___x_1189_);
lean_ctor_set(v___x_1194_, 2, v___x_1193_);
v___x_1195_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v___x_1194_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
return v___x_1195_;
}
else
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
lean_dec(v_snd_1184_);
lean_dec(v_fst_1183_);
lean_dec(v_snd_1180_);
lean_dec(v_fst_1179_);
lean_dec(v_val_1139_);
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_arg_1115_);
lean_dec_ref(v_e_1095_);
v_a_1196_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1198_ = v___x_1187_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1187_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1201_; 
if (v_isShared_1199_ == 0)
{
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_a_1196_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
else
{
lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1211_; 
lean_dec(v_snd_1184_);
lean_dec(v_fst_1183_);
lean_dec(v_snd_1180_);
lean_dec(v_fst_1179_);
lean_dec(v_val_1139_);
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_arg_1115_);
lean_dec_ref(v_e_1095_);
v_a_1204_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1206_ = v___x_1185_;
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v___x_1185_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1209_; 
if (v_isShared_1207_ == 0)
{
v___x_1209_ = v___x_1206_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_a_1204_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
}
else
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1219_; 
lean_dec(v_snd_1180_);
lean_dec(v_fst_1179_);
lean_dec(v_val_1139_);
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_arg_1115_);
lean_dec_ref(v_e_1095_);
v_a_1212_ = lean_ctor_get(v___x_1181_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1181_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1214_ = v___x_1181_;
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1181_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v___x_1217_; 
if (v_isShared_1215_ == 0)
{
v___x_1217_ = v___x_1214_;
goto v_reusejp_1216_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v_a_1212_);
v___x_1217_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1216_;
}
v_reusejp_1216_:
{
return v___x_1217_;
}
}
}
}
else
{
lean_object* v_a_1220_; lean_object* v___x_1222_; uint8_t v_isShared_1223_; uint8_t v_isSharedCheck_1227_; 
lean_dec(v_val_1139_);
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_arg_1115_);
lean_dec_ref(v_e_1095_);
v_a_1220_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1227_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1227_ == 0)
{
v___x_1222_ = v___x_1177_;
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
else
{
lean_inc(v_a_1220_);
lean_dec(v___x_1177_);
v___x_1222_ = lean_box(0);
v_isShared_1223_ = v_isSharedCheck_1227_;
goto v_resetjp_1221_;
}
v_resetjp_1221_:
{
lean_object* v___x_1225_; 
if (v_isShared_1223_ == 0)
{
v___x_1225_ = v___x_1222_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1226_; 
v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1220_);
v___x_1225_ = v_reuseFailAlloc_1226_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
return v___x_1225_;
}
}
}
}
}
else
{
lean_object* v_a_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1235_; 
lean_dec(v_val_1139_);
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_arg_1115_);
lean_dec_ref(v_e_1095_);
v_a_1228_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1230_ = v___x_1140_;
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_a_1228_);
lean_dec(v___x_1140_);
v___x_1230_ = lean_box(0);
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
v_resetjp_1229_:
{
lean_object* v___x_1233_; 
if (v_isShared_1231_ == 0)
{
v___x_1233_ = v___x_1230_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1234_; 
v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_a_1228_);
v___x_1233_ = v_reuseFailAlloc_1234_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
return v___x_1233_;
}
}
}
}
else
{
lean_object* v___x_1236_; 
lean_dec(v_a_1138_);
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_arg_1115_);
v___x_1236_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1100_);
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v_a_1237_; uint8_t v_verbose_1238_; 
v_a_1237_ = lean_ctor_get(v___x_1236_, 0);
lean_inc(v_a_1237_);
lean_dec_ref_known(v___x_1236_, 1);
v_verbose_1238_ = lean_ctor_get_uint8(v_a_1237_, 0);
lean_dec(v_a_1237_);
if (v_verbose_1238_ == 0)
{
lean_dec_ref(v_e_1095_);
goto v___jp_1110_;
}
else
{
lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1239_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10);
v___x_1240_ = l_Lean_indentExpr(v_e_1095_);
v___x_1241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1239_);
lean_ctor_set(v___x_1241_, 1, v___x_1240_);
v___x_1242_ = l_Lean_Meta_Sym_reportIssue(v___x_1241_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_dec_ref_known(v___x_1242_, 1);
goto v___jp_1110_;
}
else
{
return v___x_1242_;
}
}
}
else
{
lean_object* v_a_1243_; lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1250_; 
lean_dec_ref(v_e_1095_);
v_a_1243_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1250_ == 0)
{
v___x_1245_ = v___x_1236_;
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
else
{
lean_inc(v_a_1243_);
lean_dec(v___x_1236_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1248_; 
if (v_isShared_1246_ == 0)
{
v___x_1248_ = v___x_1245_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_a_1243_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
}
}
else
{
lean_object* v_a_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1258_; 
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_arg_1115_);
lean_dec_ref(v_e_1095_);
v_a_1251_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1253_ = v___x_1137_;
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_a_1251_);
lean_dec(v___x_1137_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1256_; 
if (v_isShared_1254_ == 0)
{
v___x_1256_ = v___x_1253_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_a_1251_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
}
}
}
else
{
lean_object* v_a_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1267_; 
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_arg_1115_);
lean_dec_ref(v_e_1095_);
v_a_1260_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1262_ = v___x_1127_;
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_a_1260_);
lean_dec(v___x_1127_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1265_; 
if (v_isShared_1263_ == 0)
{
v___x_1265_ = v___x_1262_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_a_1260_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
}
}
}
}
}
}
v___jp_1107_:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = lean_box(0);
v___x_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1108_);
return v___x_1109_;
}
v___jp_1110_:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = lean_box(0);
v___x_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1111_);
return v___x_1112_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___boxed(lean_object* v_e_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_){
_start:
{
lean_object* v_res_1280_; 
v_res_1280_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(v_e_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_);
lean_dec(v_a_1278_);
lean_dec_ref(v_a_1277_);
lean_dec(v_a_1276_);
lean_dec_ref(v_a_1275_);
lean_dec(v_a_1274_);
lean_dec_ref(v_a_1273_);
lean_dec(v_a_1272_);
lean_dec_ref(v_a_1271_);
lean_dec(v_a_1270_);
lean_dec(v_a_1269_);
return v_res_1280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(lean_object* v_e_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_){
_start:
{
lean_object* v___x_1295_; 
v___x_1295_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1286_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1340_; 
v_a_1296_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1298_ = v___x_1295_;
v_isShared_1299_ = v_isSharedCheck_1340_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1295_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1340_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
uint8_t v_lia_1300_; 
v_lia_1300_ = lean_ctor_get_uint8(v_a_1296_, sizeof(void*)*14 + 23);
lean_dec(v_a_1296_);
if (v_lia_1300_ == 0)
{
lean_object* v___x_1301_; lean_object* v___x_1303_; 
lean_dec_ref(v_e_1283_);
v___x_1301_ = lean_box(0);
if (v_isShared_1299_ == 0)
{
lean_ctor_set(v___x_1298_, 0, v___x_1301_);
v___x_1303_ = v___x_1298_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v___x_1301_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
else
{
lean_object* v___x_1305_; 
lean_del_object(v___x_1298_);
lean_inc_ref(v_e_1283_);
v___x_1305_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1283_, v_a_1291_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1331_; 
v_a_1306_ = lean_ctor_get(v___x_1305_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1308_ = v___x_1305_;
v_isShared_1309_ = v_isSharedCheck_1331_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1305_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1331_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1315_; uint8_t v___x_1316_; 
v___x_1315_ = l_Lean_Expr_cleanupAnnotations(v_a_1306_);
v___x_1316_ = l_Lean_Expr_isApp(v___x_1315_);
if (v___x_1316_ == 0)
{
lean_dec_ref(v___x_1315_);
lean_dec_ref(v_e_1283_);
goto v___jp_1310_;
}
else
{
lean_object* v___x_1317_; uint8_t v___x_1318_; 
v___x_1317_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1315_);
v___x_1318_ = l_Lean_Expr_isApp(v___x_1317_);
if (v___x_1318_ == 0)
{
lean_dec_ref(v___x_1317_);
lean_dec_ref(v_e_1283_);
goto v___jp_1310_;
}
else
{
lean_object* v___x_1319_; uint8_t v___x_1320_; 
v___x_1319_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1317_);
v___x_1320_ = l_Lean_Expr_isApp(v___x_1319_);
if (v___x_1320_ == 0)
{
lean_dec_ref(v___x_1319_);
lean_dec_ref(v_e_1283_);
goto v___jp_1310_;
}
else
{
lean_object* v___x_1321_; uint8_t v___x_1322_; 
v___x_1321_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1319_);
v___x_1322_ = l_Lean_Expr_isApp(v___x_1321_);
if (v___x_1322_ == 0)
{
lean_dec_ref(v___x_1321_);
lean_dec_ref(v_e_1283_);
goto v___jp_1310_;
}
else
{
lean_object* v_arg_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; uint8_t v___x_1326_; 
v_arg_1323_ = lean_ctor_get(v___x_1321_, 1);
lean_inc_ref(v_arg_1323_);
v___x_1324_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1321_);
v___x_1325_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1326_ = l_Lean_Expr_isConstOf(v___x_1324_, v___x_1325_);
lean_dec_ref(v___x_1324_);
if (v___x_1326_ == 0)
{
lean_dec_ref(v_arg_1323_);
lean_dec_ref(v_e_1283_);
goto v___jp_1310_;
}
else
{
lean_object* v___x_1327_; uint8_t v___x_1328_; 
lean_del_object(v___x_1308_);
v___x_1327_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0));
v___x_1328_ = l_Lean_Expr_isConstOf(v_arg_1323_, v___x_1327_);
lean_dec_ref(v_arg_1323_);
if (v___x_1328_ == 0)
{
lean_object* v___x_1329_; 
v___x_1329_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(v_e_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_);
return v___x_1329_;
}
else
{
lean_object* v___x_1330_; 
v___x_1330_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(v_e_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_);
return v___x_1330_;
}
}
}
}
}
}
v___jp_1310_:
{
lean_object* v___x_1311_; lean_object* v___x_1313_; 
v___x_1311_ = lean_box(0);
if (v_isShared_1309_ == 0)
{
lean_ctor_set(v___x_1308_, 0, v___x_1311_);
v___x_1313_ = v___x_1308_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v___x_1311_);
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
else
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1339_; 
lean_dec_ref(v_e_1283_);
v_a_1332_ = lean_ctor_get(v___x_1305_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1334_ = v___x_1305_;
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1305_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1337_; 
if (v_isShared_1335_ == 0)
{
v___x_1337_ = v___x_1334_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_a_1332_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
}
}
}
else
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1348_; 
lean_dec_ref(v_e_1283_);
v_a_1341_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1343_ = v___x_1295_;
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1295_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1346_; 
if (v_isShared_1344_ == 0)
{
v___x_1346_ = v___x_1343_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1341_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed(lean_object* v_e_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(v_e_1349_, v_a_1350_, v_a_1351_, v_a_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_);
lean_dec(v_a_1359_);
lean_dec_ref(v_a_1358_);
lean_dec(v_a_1357_);
lean_dec_ref(v_a_1356_);
lean_dec(v_a_1355_);
lean_dec_ref(v_a_1354_);
lean_dec(v_a_1353_);
lean_dec_ref(v_a_1352_);
lean_dec(v_a_1351_);
lean_dec(v_a_1350_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1363_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1364_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed), 12, 0);
v___x_1365_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_1363_, v___x_1364_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_9____boxed(lean_object* v_a_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_9_();
return v_res_1367_;
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
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_9_();
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
