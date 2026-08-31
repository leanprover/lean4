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
v_options_46_ = lean_ctor_get(v___y_38_, 2);
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
v_ref_69_ = lean_ctor_get(v___y_66_, 5);
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
lean_object* v_options_158_; lean_object* v_p_159_; lean_object* v_d_160_; lean_object* v_p_161_; lean_object* v_inheritedTraceOptions_162_; uint8_t v_hasTrace_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v_d_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v_p_170_; 
v_options_158_ = lean_ctor_get(v_a_155_, 2);
v_p_159_ = lean_ctor_get(v_c_u2081_144_, 0);
v_d_160_ = lean_ctor_get(v_c_u2082_146_, 0);
v_p_161_ = lean_ctor_get(v_c_u2082_146_, 1);
v_inheritedTraceOptions_162_ = lean_ctor_get(v_a_155_, 13);
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
lean_object* v_cls_175_; lean_object* v___x_176_; uint8_t v___x_177_; 
v_cls_175_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4));
v___x_176_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7);
v___x_177_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_162_, v_options_158_, v___x_176_);
if (v___x_177_ == 0)
{
goto v___jp_171_;
}
else
{
lean_object* v___x_178_; 
v___x_178_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_x_143_, v_a_147_, v_a_155_);
if (lean_obj_tag(v___x_178_) == 0)
{
lean_object* v_a_179_; lean_object* v___x_180_; 
v_a_179_ = lean_ctor_get(v___x_178_, 0);
lean_inc(v_a_179_);
lean_dec_ref_known(v___x_178_, 1);
lean_inc_ref(v_c_u2081_144_);
v___x_180_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_u2081_144_, v_a_147_, v_a_155_);
if (lean_obj_tag(v___x_180_) == 0)
{
lean_object* v_a_181_; lean_object* v___x_182_; 
v_a_181_ = lean_ctor_get(v___x_180_, 0);
lean_inc(v_a_181_);
lean_dec_ref_known(v___x_180_, 1);
lean_inc_ref(v_c_u2082_146_);
v___x_182_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_u2082_146_, v_a_147_, v_a_155_);
if (lean_obj_tag(v___x_182_) == 0)
{
lean_object* v_a_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v_a_183_ = lean_ctor_get(v___x_182_, 0);
lean_inc(v_a_183_);
lean_dec_ref_known(v___x_182_, 1);
v___x_184_ = l_Lean_MessageData_ofExpr(v_a_179_);
v___x_185_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9);
v___x_186_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_184_);
lean_ctor_set(v___x_186_, 1, v___x_185_);
v___x_187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_187_, 0, v___x_186_);
lean_ctor_set(v___x_187_, 1, v_a_181_);
v___x_188_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
lean_ctor_set(v___x_188_, 1, v___x_185_);
v___x_189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
lean_ctor_set(v___x_189_, 1, v_a_183_);
v___x_190_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v_cls_175_, v___x_189_, v_a_153_, v_a_154_, v_a_155_, v_a_156_);
if (lean_obj_tag(v___x_190_) == 0)
{
lean_dec_ref_known(v___x_190_, 1);
goto v___jp_171_;
}
else
{
lean_object* v_a_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_198_; 
lean_dec_ref(v_p_170_);
lean_dec(v_d_166_);
lean_dec_ref(v_c_u2082_146_);
lean_dec_ref(v_c_u2081_144_);
lean_dec(v_x_143_);
v_a_191_ = lean_ctor_get(v___x_190_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_190_);
if (v_isSharedCheck_198_ == 0)
{
v___x_193_ = v___x_190_;
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_a_191_);
lean_dec(v___x_190_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_196_; 
if (v_isShared_194_ == 0)
{
v___x_196_ = v___x_193_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_a_191_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
}
else
{
lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_206_; 
lean_dec(v_a_181_);
lean_dec(v_a_179_);
lean_dec_ref(v_p_170_);
lean_dec(v_d_166_);
lean_dec_ref(v_c_u2082_146_);
lean_dec_ref(v_c_u2081_144_);
lean_dec(v_x_143_);
v_a_199_ = lean_ctor_get(v___x_182_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_206_ == 0)
{
v___x_201_ = v___x_182_;
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_182_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_204_; 
if (v_isShared_202_ == 0)
{
v___x_204_ = v___x_201_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_a_199_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
else
{
lean_object* v_a_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_214_; 
lean_dec(v_a_179_);
lean_dec_ref(v_p_170_);
lean_dec(v_d_166_);
lean_dec_ref(v_c_u2082_146_);
lean_dec_ref(v_c_u2081_144_);
lean_dec(v_x_143_);
v_a_207_ = lean_ctor_get(v___x_180_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_214_ == 0)
{
v___x_209_ = v___x_180_;
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_a_207_);
lean_dec(v___x_180_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_214_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_212_; 
if (v_isShared_210_ == 0)
{
v___x_212_ = v___x_209_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_a_207_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
}
else
{
lean_object* v_a_215_; lean_object* v___x_217_; uint8_t v_isShared_218_; uint8_t v_isSharedCheck_222_; 
lean_dec_ref(v_p_170_);
lean_dec(v_d_166_);
lean_dec_ref(v_c_u2082_146_);
lean_dec_ref(v_c_u2081_144_);
lean_dec(v_x_143_);
v_a_215_ = lean_ctor_get(v___x_178_, 0);
v_isSharedCheck_222_ = !lean_is_exclusive(v___x_178_);
if (v_isSharedCheck_222_ == 0)
{
v___x_217_ = v___x_178_;
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
else
{
lean_inc(v_a_215_);
lean_dec(v___x_178_);
v___x_217_ = lean_box(0);
v_isShared_218_ = v_isSharedCheck_222_;
goto v_resetjp_216_;
}
v_resetjp_216_:
{
lean_object* v___x_220_; 
if (v_isShared_218_ == 0)
{
v___x_220_ = v___x_217_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_221_; 
v_reuseFailAlloc_221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_221_, 0, v_a_215_);
v___x_220_ = v_reuseFailAlloc_221_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
return v___x_220_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___boxed(lean_object* v_a_223_, lean_object* v_x_224_, lean_object* v_c_u2081_225_, lean_object* v_b_226_, lean_object* v_c_u2082_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(v_a_223_, v_x_224_, v_c_u2081_225_, v_b_226_, v_c_u2082_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_);
lean_dec(v_a_237_);
lean_dec_ref(v_a_236_);
lean_dec(v_a_235_);
lean_dec_ref(v_a_234_);
lean_dec(v_a_233_);
lean_dec_ref(v_a_232_);
lean_dec(v_a_231_);
lean_dec_ref(v_a_230_);
lean_dec(v_a_229_);
lean_dec(v_a_228_);
lean_dec(v_b_226_);
lean_dec(v_a_223_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0(lean_object* v_cls_240_, lean_object* v_msg_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_){
_start:
{
lean_object* v___x_253_; 
v___x_253_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v_cls_240_, v_msg_241_, v___y_248_, v___y_249_, v___y_250_, v___y_251_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___boxed(lean_object* v_cls_254_, lean_object* v_msg_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0(v_cls_254_, v_msg_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
lean_dec(v___y_261_);
lean_dec_ref(v___y_260_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec(v___y_256_);
return v_res_267_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = l_Lean_maxRecDepthErrorMessage;
v___x_274_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_274_, 0, v___x_273_);
return v___x_274_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3);
v___x_276_ = l_Lean_MessageData_ofFormat(v___x_275_);
return v___x_276_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_277_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4);
v___x_278_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2));
v___x_279_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_279_, 0, v___x_278_);
lean_ctor_set(v___x_279_, 1, v___x_277_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(lean_object* v_ref_280_){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_282_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5);
v___x_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_283_, 0, v_ref_280_);
lean_ctor_set(v___x_283_, 1, v___x_282_);
v___x_284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___boxed(lean_object* v_ref_285_, lean_object* v___y_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_285_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0(lean_object* v_00_u03b1_288_, lean_object* v_ref_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_289_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___boxed(lean_object* v_00_u03b1_302_, lean_object* v_ref_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0(v_00_u03b1_302_, v_ref_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
lean_dec(v___y_311_);
lean_dec_ref(v___y_310_);
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
lean_dec(v___y_305_);
lean_dec(v___y_304_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(lean_object* v_c_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_){
_start:
{
lean_object* v_p_328_; lean_object* v_fileName_329_; lean_object* v_fileMap_330_; lean_object* v_options_331_; lean_object* v_currRecDepth_332_; lean_object* v_maxRecDepth_333_; lean_object* v_ref_334_; lean_object* v_currNamespace_335_; lean_object* v_openDecls_336_; lean_object* v_initHeartbeats_337_; lean_object* v_maxHeartbeats_338_; lean_object* v_quotContext_339_; lean_object* v_currMacroScope_340_; uint8_t v_diag_341_; lean_object* v_cancelTk_x3f_342_; uint8_t v_suppressElabErrors_343_; lean_object* v_inheritedTraceOptions_344_; lean_object* v___x_376_; uint8_t v___x_377_; 
v_p_328_ = lean_ctor_get(v_c_316_, 1);
v_fileName_329_ = lean_ctor_get(v_a_325_, 0);
lean_inc_ref(v_fileName_329_);
v_fileMap_330_ = lean_ctor_get(v_a_325_, 1);
lean_inc_ref(v_fileMap_330_);
v_options_331_ = lean_ctor_get(v_a_325_, 2);
lean_inc_ref(v_options_331_);
v_currRecDepth_332_ = lean_ctor_get(v_a_325_, 3);
lean_inc(v_currRecDepth_332_);
v_maxRecDepth_333_ = lean_ctor_get(v_a_325_, 4);
lean_inc(v_maxRecDepth_333_);
v_ref_334_ = lean_ctor_get(v_a_325_, 5);
lean_inc(v_ref_334_);
v_currNamespace_335_ = lean_ctor_get(v_a_325_, 6);
lean_inc(v_currNamespace_335_);
v_openDecls_336_ = lean_ctor_get(v_a_325_, 7);
lean_inc(v_openDecls_336_);
v_initHeartbeats_337_ = lean_ctor_get(v_a_325_, 8);
lean_inc(v_initHeartbeats_337_);
v_maxHeartbeats_338_ = lean_ctor_get(v_a_325_, 9);
lean_inc(v_maxHeartbeats_338_);
v_quotContext_339_ = lean_ctor_get(v_a_325_, 10);
lean_inc(v_quotContext_339_);
v_currMacroScope_340_ = lean_ctor_get(v_a_325_, 11);
lean_inc(v_currMacroScope_340_);
v_diag_341_ = lean_ctor_get_uint8(v_a_325_, sizeof(void*)*14);
v_cancelTk_x3f_342_ = lean_ctor_get(v_a_325_, 12);
lean_inc(v_cancelTk_x3f_342_);
v_suppressElabErrors_343_ = lean_ctor_get_uint8(v_a_325_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_344_ = lean_ctor_get(v_a_325_, 13);
lean_inc_ref(v_inheritedTraceOptions_344_);
lean_dec_ref(v_a_325_);
v___x_376_ = lean_unsigned_to_nat(0u);
v___x_377_ = lean_nat_dec_eq(v_maxRecDepth_333_, v___x_376_);
if (v___x_377_ == 0)
{
uint8_t v___x_378_; 
v___x_378_ = lean_nat_dec_eq(v_currRecDepth_332_, v_maxRecDepth_333_);
if (v___x_378_ == 0)
{
goto v___jp_345_;
}
else
{
lean_object* v___x_379_; 
lean_dec_ref(v_inheritedTraceOptions_344_);
lean_dec(v_cancelTk_x3f_342_);
lean_dec(v_currMacroScope_340_);
lean_dec(v_quotContext_339_);
lean_dec(v_maxHeartbeats_338_);
lean_dec(v_initHeartbeats_337_);
lean_dec(v_openDecls_336_);
lean_dec(v_currNamespace_335_);
lean_dec(v_maxRecDepth_333_);
lean_dec(v_currRecDepth_332_);
lean_dec_ref(v_options_331_);
lean_dec_ref(v_fileMap_330_);
lean_dec_ref(v_fileName_329_);
lean_dec_ref(v_c_316_);
v___x_379_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_334_);
return v___x_379_;
}
}
else
{
goto v___jp_345_;
}
v___jp_345_:
{
lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_346_ = lean_unsigned_to_nat(1u);
v___x_347_ = lean_nat_add(v_currRecDepth_332_, v___x_346_);
lean_dec(v_currRecDepth_332_);
v___x_348_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_348_, 0, v_fileName_329_);
lean_ctor_set(v___x_348_, 1, v_fileMap_330_);
lean_ctor_set(v___x_348_, 2, v_options_331_);
lean_ctor_set(v___x_348_, 3, v___x_347_);
lean_ctor_set(v___x_348_, 4, v_maxRecDepth_333_);
lean_ctor_set(v___x_348_, 5, v_ref_334_);
lean_ctor_set(v___x_348_, 6, v_currNamespace_335_);
lean_ctor_set(v___x_348_, 7, v_openDecls_336_);
lean_ctor_set(v___x_348_, 8, v_initHeartbeats_337_);
lean_ctor_set(v___x_348_, 9, v_maxHeartbeats_338_);
lean_ctor_set(v___x_348_, 10, v_quotContext_339_);
lean_ctor_set(v___x_348_, 11, v_currMacroScope_340_);
lean_ctor_set(v___x_348_, 12, v_cancelTk_x3f_342_);
lean_ctor_set(v___x_348_, 13, v_inheritedTraceOptions_344_);
lean_ctor_set_uint8(v___x_348_, sizeof(void*)*14, v_diag_341_);
lean_ctor_set_uint8(v___x_348_, sizeof(void*)*14 + 1, v_suppressElabErrors_343_);
lean_inc_ref(v_p_328_);
v___x_349_ = l_Int_Internal_Linear_Poly_findVarToSubst___redArg(v_p_328_, v_a_317_, v___x_348_);
if (lean_obj_tag(v___x_349_) == 0)
{
lean_object* v_a_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_367_; 
v_a_350_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_367_ == 0)
{
v___x_352_ = v___x_349_;
v_isShared_353_ = v_isSharedCheck_367_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_a_350_);
lean_dec(v___x_349_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_367_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
if (lean_obj_tag(v_a_350_) == 1)
{
lean_object* v_val_354_; lean_object* v_snd_355_; lean_object* v_snd_356_; lean_object* v_fst_357_; lean_object* v_fst_358_; lean_object* v_p_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
lean_del_object(v___x_352_);
v_val_354_ = lean_ctor_get(v_a_350_, 0);
lean_inc(v_val_354_);
lean_dec_ref_known(v_a_350_, 1);
v_snd_355_ = lean_ctor_get(v_val_354_, 1);
lean_inc(v_snd_355_);
v_snd_356_ = lean_ctor_get(v_snd_355_, 1);
lean_inc(v_snd_356_);
v_fst_357_ = lean_ctor_get(v_val_354_, 0);
lean_inc(v_fst_357_);
lean_dec(v_val_354_);
v_fst_358_ = lean_ctor_get(v_snd_355_, 0);
lean_inc(v_fst_358_);
lean_dec(v_snd_355_);
v_p_359_ = lean_ctor_get(v_snd_356_, 0);
v___x_360_ = l_Int_Internal_Linear_Poly_coeff(v_p_359_, v_fst_358_);
v___x_361_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(v___x_360_, v_fst_358_, v_snd_356_, v_fst_357_, v_c_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v___x_348_, v_a_326_);
lean_dec(v_fst_357_);
lean_dec(v___x_360_);
if (lean_obj_tag(v___x_361_) == 0)
{
lean_object* v_a_362_; 
v_a_362_ = lean_ctor_get(v___x_361_, 0);
lean_inc(v_a_362_);
lean_dec_ref_known(v___x_361_, 1);
v_c_316_ = v_a_362_;
v_a_325_ = v___x_348_;
goto _start;
}
else
{
lean_dec_ref_known(v___x_348_, 14);
return v___x_361_;
}
}
else
{
lean_object* v___x_365_; 
lean_dec(v_a_350_);
lean_dec_ref_known(v___x_348_, 14);
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 0, v_c_316_);
v___x_365_ = v___x_352_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_c_316_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
return v___x_365_;
}
}
}
}
else
{
lean_object* v_a_368_; lean_object* v___x_370_; uint8_t v_isShared_371_; uint8_t v_isSharedCheck_375_; 
lean_dec_ref_known(v___x_348_, 14);
lean_dec_ref(v_c_316_);
v_a_368_ = lean_ctor_get(v___x_349_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_349_);
if (v_isSharedCheck_375_ == 0)
{
v___x_370_ = v___x_349_;
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
else
{
lean_inc(v_a_368_);
lean_dec(v___x_349_);
v___x_370_ = lean_box(0);
v_isShared_371_ = v_isSharedCheck_375_;
goto v_resetjp_369_;
}
v_resetjp_369_:
{
lean_object* v___x_373_; 
if (v_isShared_371_ == 0)
{
v___x_373_ = v___x_370_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_a_368_);
v___x_373_ = v_reuseFailAlloc_374_;
goto v_reusejp_372_;
}
v_reusejp_372_:
{
return v___x_373_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___boxed(lean_object* v_c_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(v_c_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_);
lean_dec(v_a_390_);
lean_dec(v_a_388_);
lean_dec_ref(v_a_387_);
lean_dec(v_a_386_);
lean_dec_ref(v_a_385_);
lean_dec(v_a_384_);
lean_dec_ref(v_a_383_);
lean_dec(v_a_382_);
lean_dec(v_a_381_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(lean_object* v_a_393_, lean_object* v_v_394_, lean_object* v_s_395_){
_start:
{
lean_object* v_vars_396_; lean_object* v_varMap_397_; lean_object* v_vars_x27_398_; lean_object* v_varMap_x27_399_; lean_object* v_natToIntMap_400_; lean_object* v_natDef_401_; lean_object* v_dvds_402_; lean_object* v_lowers_403_; lean_object* v_uppers_404_; lean_object* v_diseqs_405_; lean_object* v_elimEqs_406_; lean_object* v_elimStack_407_; lean_object* v_occurs_408_; lean_object* v_assignment_409_; lean_object* v_nextCnstrId_410_; uint8_t v_caseSplits_411_; lean_object* v_steps_412_; lean_object* v_conflict_x3f_413_; lean_object* v_diseqSplits_414_; lean_object* v_divMod_415_; uint8_t v_usedCommRing_416_; lean_object* v_nonlinearOccs_417_; lean_object* v___x_419_; uint8_t v_isShared_420_; uint8_t v_isSharedCheck_426_; 
v_vars_396_ = lean_ctor_get(v_s_395_, 0);
v_varMap_397_ = lean_ctor_get(v_s_395_, 1);
v_vars_x27_398_ = lean_ctor_get(v_s_395_, 2);
v_varMap_x27_399_ = lean_ctor_get(v_s_395_, 3);
v_natToIntMap_400_ = lean_ctor_get(v_s_395_, 4);
v_natDef_401_ = lean_ctor_get(v_s_395_, 5);
v_dvds_402_ = lean_ctor_get(v_s_395_, 6);
v_lowers_403_ = lean_ctor_get(v_s_395_, 7);
v_uppers_404_ = lean_ctor_get(v_s_395_, 8);
v_diseqs_405_ = lean_ctor_get(v_s_395_, 9);
v_elimEqs_406_ = lean_ctor_get(v_s_395_, 10);
v_elimStack_407_ = lean_ctor_get(v_s_395_, 11);
v_occurs_408_ = lean_ctor_get(v_s_395_, 12);
v_assignment_409_ = lean_ctor_get(v_s_395_, 13);
v_nextCnstrId_410_ = lean_ctor_get(v_s_395_, 14);
v_caseSplits_411_ = lean_ctor_get_uint8(v_s_395_, sizeof(void*)*20);
v_steps_412_ = lean_ctor_get(v_s_395_, 15);
v_conflict_x3f_413_ = lean_ctor_get(v_s_395_, 16);
v_diseqSplits_414_ = lean_ctor_get(v_s_395_, 17);
v_divMod_415_ = lean_ctor_get(v_s_395_, 18);
v_usedCommRing_416_ = lean_ctor_get_uint8(v_s_395_, sizeof(void*)*20 + 1);
v_nonlinearOccs_417_ = lean_ctor_get(v_s_395_, 19);
v_isSharedCheck_426_ = !lean_is_exclusive(v_s_395_);
if (v_isSharedCheck_426_ == 0)
{
v___x_419_ = v_s_395_;
v_isShared_420_ = v_isSharedCheck_426_;
goto v_resetjp_418_;
}
else
{
lean_inc(v_nonlinearOccs_417_);
lean_inc(v_divMod_415_);
lean_inc(v_diseqSplits_414_);
lean_inc(v_conflict_x3f_413_);
lean_inc(v_steps_412_);
lean_inc(v_nextCnstrId_410_);
lean_inc(v_assignment_409_);
lean_inc(v_occurs_408_);
lean_inc(v_elimStack_407_);
lean_inc(v_elimEqs_406_);
lean_inc(v_diseqs_405_);
lean_inc(v_uppers_404_);
lean_inc(v_lowers_403_);
lean_inc(v_dvds_402_);
lean_inc(v_natDef_401_);
lean_inc(v_natToIntMap_400_);
lean_inc(v_varMap_x27_399_);
lean_inc(v_vars_x27_398_);
lean_inc(v_varMap_397_);
lean_inc(v_vars_396_);
lean_dec(v_s_395_);
v___x_419_ = lean_box(0);
v_isShared_420_ = v_isSharedCheck_426_;
goto v_resetjp_418_;
}
v_resetjp_418_:
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_424_; 
v___x_421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_421_, 0, v_a_393_);
v___x_422_ = l_Lean_PersistentArray_set___redArg(v_dvds_402_, v_v_394_, v___x_421_);
if (v_isShared_420_ == 0)
{
lean_ctor_set(v___x_419_, 6, v___x_422_);
v___x_424_ = v___x_419_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_425_; 
v_reuseFailAlloc_425_ = lean_alloc_ctor(0, 20, 2);
lean_ctor_set(v_reuseFailAlloc_425_, 0, v_vars_396_);
lean_ctor_set(v_reuseFailAlloc_425_, 1, v_varMap_397_);
lean_ctor_set(v_reuseFailAlloc_425_, 2, v_vars_x27_398_);
lean_ctor_set(v_reuseFailAlloc_425_, 3, v_varMap_x27_399_);
lean_ctor_set(v_reuseFailAlloc_425_, 4, v_natToIntMap_400_);
lean_ctor_set(v_reuseFailAlloc_425_, 5, v_natDef_401_);
lean_ctor_set(v_reuseFailAlloc_425_, 6, v___x_422_);
lean_ctor_set(v_reuseFailAlloc_425_, 7, v_lowers_403_);
lean_ctor_set(v_reuseFailAlloc_425_, 8, v_uppers_404_);
lean_ctor_set(v_reuseFailAlloc_425_, 9, v_diseqs_405_);
lean_ctor_set(v_reuseFailAlloc_425_, 10, v_elimEqs_406_);
lean_ctor_set(v_reuseFailAlloc_425_, 11, v_elimStack_407_);
lean_ctor_set(v_reuseFailAlloc_425_, 12, v_occurs_408_);
lean_ctor_set(v_reuseFailAlloc_425_, 13, v_assignment_409_);
lean_ctor_set(v_reuseFailAlloc_425_, 14, v_nextCnstrId_410_);
lean_ctor_set(v_reuseFailAlloc_425_, 15, v_steps_412_);
lean_ctor_set(v_reuseFailAlloc_425_, 16, v_conflict_x3f_413_);
lean_ctor_set(v_reuseFailAlloc_425_, 17, v_diseqSplits_414_);
lean_ctor_set(v_reuseFailAlloc_425_, 18, v_divMod_415_);
lean_ctor_set(v_reuseFailAlloc_425_, 19, v_nonlinearOccs_417_);
lean_ctor_set_uint8(v_reuseFailAlloc_425_, sizeof(void*)*20, v_caseSplits_411_);
lean_ctor_set_uint8(v_reuseFailAlloc_425_, sizeof(void*)*20 + 1, v_usedCommRing_416_);
v___x_424_ = v_reuseFailAlloc_425_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
return v___x_424_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed(lean_object* v_a_427_, lean_object* v_v_428_, lean_object* v_s_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(v_a_427_, v_v_428_, v_s_429_);
lean_dec(v_v_428_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(lean_object* v_v_431_, lean_object* v_s_432_){
_start:
{
lean_object* v_vars_433_; lean_object* v_varMap_434_; lean_object* v_vars_x27_435_; lean_object* v_varMap_x27_436_; lean_object* v_natToIntMap_437_; lean_object* v_natDef_438_; lean_object* v_dvds_439_; lean_object* v_lowers_440_; lean_object* v_uppers_441_; lean_object* v_diseqs_442_; lean_object* v_elimEqs_443_; lean_object* v_elimStack_444_; lean_object* v_occurs_445_; lean_object* v_assignment_446_; lean_object* v_nextCnstrId_447_; uint8_t v_caseSplits_448_; lean_object* v_steps_449_; lean_object* v_conflict_x3f_450_; lean_object* v_diseqSplits_451_; lean_object* v_divMod_452_; uint8_t v_usedCommRing_453_; lean_object* v_nonlinearOccs_454_; lean_object* v___x_456_; uint8_t v_isShared_457_; uint8_t v_isSharedCheck_463_; 
v_vars_433_ = lean_ctor_get(v_s_432_, 0);
v_varMap_434_ = lean_ctor_get(v_s_432_, 1);
v_vars_x27_435_ = lean_ctor_get(v_s_432_, 2);
v_varMap_x27_436_ = lean_ctor_get(v_s_432_, 3);
v_natToIntMap_437_ = lean_ctor_get(v_s_432_, 4);
v_natDef_438_ = lean_ctor_get(v_s_432_, 5);
v_dvds_439_ = lean_ctor_get(v_s_432_, 6);
v_lowers_440_ = lean_ctor_get(v_s_432_, 7);
v_uppers_441_ = lean_ctor_get(v_s_432_, 8);
v_diseqs_442_ = lean_ctor_get(v_s_432_, 9);
v_elimEqs_443_ = lean_ctor_get(v_s_432_, 10);
v_elimStack_444_ = lean_ctor_get(v_s_432_, 11);
v_occurs_445_ = lean_ctor_get(v_s_432_, 12);
v_assignment_446_ = lean_ctor_get(v_s_432_, 13);
v_nextCnstrId_447_ = lean_ctor_get(v_s_432_, 14);
v_caseSplits_448_ = lean_ctor_get_uint8(v_s_432_, sizeof(void*)*20);
v_steps_449_ = lean_ctor_get(v_s_432_, 15);
v_conflict_x3f_450_ = lean_ctor_get(v_s_432_, 16);
v_diseqSplits_451_ = lean_ctor_get(v_s_432_, 17);
v_divMod_452_ = lean_ctor_get(v_s_432_, 18);
v_usedCommRing_453_ = lean_ctor_get_uint8(v_s_432_, sizeof(void*)*20 + 1);
v_nonlinearOccs_454_ = lean_ctor_get(v_s_432_, 19);
v_isSharedCheck_463_ = !lean_is_exclusive(v_s_432_);
if (v_isSharedCheck_463_ == 0)
{
v___x_456_ = v_s_432_;
v_isShared_457_ = v_isSharedCheck_463_;
goto v_resetjp_455_;
}
else
{
lean_inc(v_nonlinearOccs_454_);
lean_inc(v_divMod_452_);
lean_inc(v_diseqSplits_451_);
lean_inc(v_conflict_x3f_450_);
lean_inc(v_steps_449_);
lean_inc(v_nextCnstrId_447_);
lean_inc(v_assignment_446_);
lean_inc(v_occurs_445_);
lean_inc(v_elimStack_444_);
lean_inc(v_elimEqs_443_);
lean_inc(v_diseqs_442_);
lean_inc(v_uppers_441_);
lean_inc(v_lowers_440_);
lean_inc(v_dvds_439_);
lean_inc(v_natDef_438_);
lean_inc(v_natToIntMap_437_);
lean_inc(v_varMap_x27_436_);
lean_inc(v_vars_x27_435_);
lean_inc(v_varMap_434_);
lean_inc(v_vars_433_);
lean_dec(v_s_432_);
v___x_456_ = lean_box(0);
v_isShared_457_ = v_isSharedCheck_463_;
goto v_resetjp_455_;
}
v_resetjp_455_:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_461_; 
v___x_458_ = lean_box(0);
v___x_459_ = l_Lean_PersistentArray_set___redArg(v_dvds_439_, v_v_431_, v___x_458_);
if (v_isShared_457_ == 0)
{
lean_ctor_set(v___x_456_, 6, v___x_459_);
v___x_461_ = v___x_456_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 20, 2);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_vars_433_);
lean_ctor_set(v_reuseFailAlloc_462_, 1, v_varMap_434_);
lean_ctor_set(v_reuseFailAlloc_462_, 2, v_vars_x27_435_);
lean_ctor_set(v_reuseFailAlloc_462_, 3, v_varMap_x27_436_);
lean_ctor_set(v_reuseFailAlloc_462_, 4, v_natToIntMap_437_);
lean_ctor_set(v_reuseFailAlloc_462_, 5, v_natDef_438_);
lean_ctor_set(v_reuseFailAlloc_462_, 6, v___x_459_);
lean_ctor_set(v_reuseFailAlloc_462_, 7, v_lowers_440_);
lean_ctor_set(v_reuseFailAlloc_462_, 8, v_uppers_441_);
lean_ctor_set(v_reuseFailAlloc_462_, 9, v_diseqs_442_);
lean_ctor_set(v_reuseFailAlloc_462_, 10, v_elimEqs_443_);
lean_ctor_set(v_reuseFailAlloc_462_, 11, v_elimStack_444_);
lean_ctor_set(v_reuseFailAlloc_462_, 12, v_occurs_445_);
lean_ctor_set(v_reuseFailAlloc_462_, 13, v_assignment_446_);
lean_ctor_set(v_reuseFailAlloc_462_, 14, v_nextCnstrId_447_);
lean_ctor_set(v_reuseFailAlloc_462_, 15, v_steps_449_);
lean_ctor_set(v_reuseFailAlloc_462_, 16, v_conflict_x3f_450_);
lean_ctor_set(v_reuseFailAlloc_462_, 17, v_diseqSplits_451_);
lean_ctor_set(v_reuseFailAlloc_462_, 18, v_divMod_452_);
lean_ctor_set(v_reuseFailAlloc_462_, 19, v_nonlinearOccs_454_);
lean_ctor_set_uint8(v_reuseFailAlloc_462_, sizeof(void*)*20, v_caseSplits_448_);
lean_ctor_set_uint8(v_reuseFailAlloc_462_, sizeof(void*)*20 + 1, v_usedCommRing_453_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed(lean_object* v_v_464_, lean_object* v_s_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(v_v_464_, v_s_465_);
lean_dec(v_v_464_);
return v_res_466_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5(void){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_475_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4));
v___x_476_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
v___x_477_ = l_Lean_Name_append(v___x_476_, v___x_475_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(lean_object* v_c_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_){
_start:
{
lean_object* v___y_494_; lean_object* v___y_495_; lean_object* v___y_496_; lean_object* v___y_497_; lean_object* v___y_498_; lean_object* v___y_499_; lean_object* v___y_500_; lean_object* v___y_505_; lean_object* v___y_506_; lean_object* v___y_507_; lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___y_611_; lean_object* v___y_612_; lean_object* v___y_613_; lean_object* v___y_614_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___y_617_; lean_object* v_fileName_629_; lean_object* v_fileMap_630_; lean_object* v_options_631_; lean_object* v_currRecDepth_632_; lean_object* v_maxRecDepth_633_; lean_object* v_ref_634_; lean_object* v_currNamespace_635_; lean_object* v_openDecls_636_; lean_object* v_initHeartbeats_637_; lean_object* v_maxHeartbeats_638_; lean_object* v_quotContext_639_; lean_object* v_currMacroScope_640_; uint8_t v_diag_641_; lean_object* v_cancelTk_x3f_642_; uint8_t v_suppressElabErrors_643_; lean_object* v_inheritedTraceOptions_644_; lean_object* v___x_645_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___x_825_; uint8_t v___x_826_; 
v_fileName_629_ = lean_ctor_get(v_a_487_, 0);
lean_inc_ref(v_fileName_629_);
v_fileMap_630_ = lean_ctor_get(v_a_487_, 1);
lean_inc_ref(v_fileMap_630_);
v_options_631_ = lean_ctor_get(v_a_487_, 2);
lean_inc_ref(v_options_631_);
v_currRecDepth_632_ = lean_ctor_get(v_a_487_, 3);
lean_inc(v_currRecDepth_632_);
v_maxRecDepth_633_ = lean_ctor_get(v_a_487_, 4);
lean_inc(v_maxRecDepth_633_);
v_ref_634_ = lean_ctor_get(v_a_487_, 5);
lean_inc(v_ref_634_);
v_currNamespace_635_ = lean_ctor_get(v_a_487_, 6);
lean_inc(v_currNamespace_635_);
v_openDecls_636_ = lean_ctor_get(v_a_487_, 7);
lean_inc(v_openDecls_636_);
v_initHeartbeats_637_ = lean_ctor_get(v_a_487_, 8);
lean_inc(v_initHeartbeats_637_);
v_maxHeartbeats_638_ = lean_ctor_get(v_a_487_, 9);
lean_inc(v_maxHeartbeats_638_);
v_quotContext_639_ = lean_ctor_get(v_a_487_, 10);
lean_inc(v_quotContext_639_);
v_currMacroScope_640_ = lean_ctor_get(v_a_487_, 11);
lean_inc(v_currMacroScope_640_);
v_diag_641_ = lean_ctor_get_uint8(v_a_487_, sizeof(void*)*14);
v_cancelTk_x3f_642_ = lean_ctor_get(v_a_487_, 12);
lean_inc(v_cancelTk_x3f_642_);
v_suppressElabErrors_643_ = lean_ctor_get_uint8(v_a_487_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_644_ = lean_ctor_get(v_a_487_, 13);
lean_inc_ref(v_inheritedTraceOptions_644_);
lean_dec_ref(v_a_487_);
v___x_645_ = lean_box(0);
v___x_825_ = lean_unsigned_to_nat(0u);
v___x_826_ = lean_nat_dec_eq(v_maxRecDepth_633_, v___x_825_);
if (v___x_826_ == 0)
{
uint8_t v___x_827_; 
v___x_827_ = lean_nat_dec_eq(v_currRecDepth_632_, v_maxRecDepth_633_);
if (v___x_827_ == 0)
{
goto v___jp_784_;
}
else
{
lean_object* v___x_828_; 
lean_dec_ref(v_inheritedTraceOptions_644_);
lean_dec(v_cancelTk_x3f_642_);
lean_dec(v_currMacroScope_640_);
lean_dec(v_quotContext_639_);
lean_dec(v_maxHeartbeats_638_);
lean_dec(v_initHeartbeats_637_);
lean_dec(v_openDecls_636_);
lean_dec(v_currNamespace_635_);
lean_dec(v_maxRecDepth_633_);
lean_dec(v_currRecDepth_632_);
lean_dec_ref(v_options_631_);
lean_dec_ref(v_fileMap_630_);
lean_dec_ref(v_fileName_629_);
lean_dec_ref(v_c_478_);
v___x_828_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_634_);
return v___x_828_;
}
}
else
{
goto v___jp_784_;
}
v___jp_490_:
{
lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_491_ = lean_box(0);
v___x_492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_492_, 0, v___x_491_);
return v___x_492_;
}
v___jp_493_:
{
lean_object* v___x_501_; 
v___x_501_ = l_Int_Internal_Linear_Poly_updateOccs___redArg(v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_);
lean_dec_ref(v___y_499_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v___x_502_; lean_object* v___x_503_; 
lean_dec_ref_known(v___x_501_, 1);
v___x_502_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_503_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_502_, v___y_494_, v___y_496_);
return v___x_503_;
}
else
{
lean_dec_ref(v___y_494_);
return v___x_501_;
}
}
v___jp_504_:
{
if (lean_obj_tag(v___y_526_) == 1)
{
lean_object* v_val_527_; lean_object* v_p_528_; 
lean_dec_ref(v___y_519_);
lean_dec_ref(v___y_511_);
v_val_527_ = lean_ctor_get(v___y_526_, 0);
lean_inc(v_val_527_);
lean_dec_ref_known(v___y_526_, 1);
v_p_528_ = lean_ctor_get(v_val_527_, 1);
lean_inc_ref(v_p_528_);
if (lean_obj_tag(v_p_528_) == 1)
{
lean_object* v_d_529_; lean_object* v_k_530_; lean_object* v_p_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_584_; 
v_d_529_ = lean_ctor_get(v_val_527_, 0);
v_k_530_ = lean_ctor_get(v_p_528_, 0);
v_p_531_ = lean_ctor_get(v_p_528_, 2);
v_isSharedCheck_584_ = !lean_is_exclusive(v_p_528_);
if (v_isSharedCheck_584_ == 0)
{
lean_object* v_unused_585_; 
v_unused_585_ = lean_ctor_get(v_p_528_, 1);
lean_dec(v_unused_585_);
v___x_533_ = v_p_528_;
v_isShared_534_ = v_isSharedCheck_584_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_p_531_);
lean_inc(v_k_530_);
lean_dec(v_p_528_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_584_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v_snd_538_; lean_object* v_fst_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_583_; 
v___x_535_ = lean_int_mul(v___y_508_, v_d_529_);
v___x_536_ = lean_int_mul(v_k_530_, v___y_507_);
v___x_537_ = l_Lean_Meta_Grind_Arith_gcdExt(v___x_535_, v___x_536_);
lean_dec(v___x_536_);
lean_dec(v___x_535_);
v_snd_538_ = lean_ctor_get(v___x_537_, 1);
v_fst_539_ = lean_ctor_get(v___x_537_, 0);
v_isSharedCheck_583_ = !lean_is_exclusive(v___x_537_);
if (v_isSharedCheck_583_ == 0)
{
v___x_541_ = v___x_537_;
v_isShared_542_ = v_isSharedCheck_583_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_snd_538_);
lean_inc(v_fst_539_);
lean_dec(v___x_537_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_583_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v_fst_543_; lean_object* v_snd_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_582_; 
v_fst_543_ = lean_ctor_get(v_snd_538_, 0);
v_snd_544_ = lean_ctor_get(v_snd_538_, 1);
v_isSharedCheck_582_ = !lean_is_exclusive(v_snd_538_);
if (v_isSharedCheck_582_ == 0)
{
v___x_546_ = v_snd_538_;
v_isShared_547_ = v_isSharedCheck_582_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_snd_544_);
lean_inc(v_fst_543_);
lean_dec(v_snd_538_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_582_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_548_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_549_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_548_, v___y_512_, v___y_516_);
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_557_; 
lean_dec_ref_known(v___x_549_, 1);
v___x_550_ = lean_int_mul(v_fst_543_, v_d_529_);
lean_dec(v_fst_543_);
lean_inc_ref(v___y_523_);
v___x_551_ = l_Int_Internal_Linear_Poly_mul(v___y_523_, v___x_550_);
lean_dec(v___x_550_);
v___x_552_ = lean_int_mul(v_snd_544_, v___y_507_);
lean_dec(v_snd_544_);
lean_inc_ref(v_p_531_);
v___x_553_ = l_Int_Internal_Linear_Poly_mul(v_p_531_, v___x_552_);
lean_dec(v___x_552_);
v___x_554_ = lean_int_mul(v___y_507_, v_d_529_);
lean_dec(v___y_507_);
v___x_555_ = l_Int_Internal_Linear_Poly_combine(v___x_551_, v___x_553_);
lean_inc(v_fst_539_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 2, v___x_555_);
lean_ctor_set(v___x_533_, 1, v___y_510_);
lean_ctor_set(v___x_533_, 0, v_fst_539_);
v___x_557_ = v___x_533_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v_fst_539_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v___y_510_);
lean_ctor_set(v_reuseFailAlloc_581_, 2, v___x_555_);
v___x_557_ = v_reuseFailAlloc_581_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
lean_object* v___x_559_; 
lean_inc(v_val_527_);
lean_inc_ref(v___y_524_);
if (v_isShared_547_ == 0)
{
lean_ctor_set_tag(v___x_546_, 4);
lean_ctor_set(v___x_546_, 1, v_val_527_);
lean_ctor_set(v___x_546_, 0, v___y_524_);
v___x_559_ = v___x_546_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v___y_524_);
lean_ctor_set(v_reuseFailAlloc_580_, 1, v_val_527_);
v___x_559_ = v_reuseFailAlloc_580_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_560_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_560_, 0, v___x_554_);
lean_ctor_set(v___x_560_, 1, v___x_557_);
lean_ctor_set(v___x_560_, 2, v___x_559_);
lean_inc_ref(v___y_517_);
v___x_561_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v___x_560_, v___y_516_, v___y_506_, v___y_513_, v___y_525_, v___y_515_, v___y_514_, v___y_518_, v___y_522_, v___y_517_, v___y_509_);
if (lean_obj_tag(v___x_561_) == 0)
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_567_; 
lean_dec_ref_known(v___x_561_, 1);
v___x_562_ = l_Int_Internal_Linear_Poly_mul(v___y_523_, v_k_530_);
lean_dec(v_k_530_);
v___x_563_ = lean_int_neg(v___y_508_);
lean_dec(v___y_508_);
v___x_564_ = l_Int_Internal_Linear_Poly_mul(v_p_531_, v___x_563_);
lean_dec(v___x_563_);
v___x_565_ = l_Int_Internal_Linear_Poly_combine(v___x_562_, v___x_564_);
lean_inc(v_val_527_);
if (v_isShared_542_ == 0)
{
lean_ctor_set_tag(v___x_541_, 5);
lean_ctor_set(v___x_541_, 1, v_val_527_);
lean_ctor_set(v___x_541_, 0, v___y_524_);
v___x_567_ = v___x_541_;
goto v_reusejp_566_;
}
else
{
lean_object* v_reuseFailAlloc_579_; 
v_reuseFailAlloc_579_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_579_, 0, v___y_524_);
lean_ctor_set(v_reuseFailAlloc_579_, 1, v_val_527_);
v___x_567_ = v_reuseFailAlloc_579_;
goto v_reusejp_566_;
}
v_reusejp_566_:
{
lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_575_; 
v_isSharedCheck_575_ = !lean_is_exclusive(v_val_527_);
if (v_isSharedCheck_575_ == 0)
{
lean_object* v_unused_576_; lean_object* v_unused_577_; lean_object* v_unused_578_; 
v_unused_576_ = lean_ctor_get(v_val_527_, 2);
lean_dec(v_unused_576_);
v_unused_577_ = lean_ctor_get(v_val_527_, 1);
lean_dec(v_unused_577_);
v_unused_578_ = lean_ctor_get(v_val_527_, 0);
lean_dec(v_unused_578_);
v___x_569_ = v_val_527_;
v_isShared_570_ = v_isSharedCheck_575_;
goto v_resetjp_568_;
}
else
{
lean_dec(v_val_527_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_575_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_572_; 
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 2, v___x_567_);
lean_ctor_set(v___x_569_, 1, v___x_565_);
lean_ctor_set(v___x_569_, 0, v_fst_539_);
v___x_572_ = v___x_569_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_fst_539_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v___x_565_);
lean_ctor_set(v_reuseFailAlloc_574_, 2, v___x_567_);
v___x_572_ = v_reuseFailAlloc_574_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
v_c_478_ = v___x_572_;
v_a_479_ = v___y_516_;
v_a_480_ = v___y_506_;
v_a_481_ = v___y_513_;
v_a_482_ = v___y_525_;
v_a_483_ = v___y_515_;
v_a_484_ = v___y_514_;
v_a_485_ = v___y_518_;
v_a_486_ = v___y_522_;
v_a_487_ = v___y_517_;
v_a_488_ = v___y_509_;
goto _start;
}
}
}
}
else
{
lean_del_object(v___x_541_);
lean_dec(v_fst_539_);
lean_dec_ref(v_p_531_);
lean_dec(v_k_530_);
lean_dec(v_val_527_);
lean_dec_ref(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec_ref(v___y_517_);
lean_dec(v___y_508_);
return v___x_561_;
}
}
}
}
else
{
lean_del_object(v___x_546_);
lean_dec(v_snd_544_);
lean_dec(v_fst_543_);
lean_del_object(v___x_541_);
lean_dec(v_fst_539_);
lean_del_object(v___x_533_);
lean_dec_ref(v_p_531_);
lean_dec(v_k_530_);
lean_dec(v_val_527_);
lean_dec_ref(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec_ref(v___y_517_);
lean_dec(v___y_510_);
lean_dec(v___y_508_);
lean_dec(v___y_507_);
return v___x_549_;
}
}
}
}
}
else
{
lean_object* v___x_586_; 
lean_dec_ref(v_p_528_);
lean_dec_ref(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec_ref(v___y_512_);
lean_dec(v___y_510_);
lean_dec(v___y_508_);
lean_dec(v___y_507_);
v___x_586_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_val_527_, v___y_516_, v___y_506_, v___y_513_, v___y_525_, v___y_515_, v___y_514_, v___y_518_, v___y_522_, v___y_517_, v___y_509_);
lean_dec_ref(v___y_517_);
return v___x_586_;
}
}
else
{
lean_object* v_options_587_; uint8_t v_hasTrace_588_; 
lean_dec(v___y_526_);
lean_dec_ref(v___y_523_);
lean_dec_ref(v___y_512_);
lean_dec(v___y_510_);
lean_dec(v___y_508_);
lean_dec(v___y_507_);
v_options_587_ = lean_ctor_get(v___y_517_, 2);
v_hasTrace_588_ = lean_ctor_get_uint8(v_options_587_, sizeof(void*)*1);
if (v_hasTrace_588_ == 0)
{
lean_dec_ref(v___y_524_);
v___y_494_ = v___y_519_;
v___y_495_ = v___y_511_;
v___y_496_ = v___y_516_;
v___y_497_ = v___y_518_;
v___y_498_ = v___y_522_;
v___y_499_ = v___y_517_;
v___y_500_ = v___y_509_;
goto v___jp_493_;
}
else
{
lean_object* v_inheritedTraceOptions_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; uint8_t v___x_594_; 
v_inheritedTraceOptions_589_ = lean_ctor_get(v___y_517_, 13);
v___x_590_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0));
lean_inc_ref(v___y_520_);
lean_inc_ref(v___y_505_);
lean_inc_ref(v___y_521_);
v___x_591_ = l_Lean_Name_mkStr4(v___y_521_, v___y_505_, v___y_520_, v___x_590_);
v___x_592_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
lean_inc(v___x_591_);
v___x_593_ = l_Lean_Name_append(v___x_592_, v___x_591_);
v___x_594_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_589_, v_options_587_, v___x_593_);
lean_dec(v___x_593_);
if (v___x_594_ == 0)
{
lean_dec(v___x_591_);
lean_dec_ref(v___y_524_);
v___y_494_ = v___y_519_;
v___y_495_ = v___y_511_;
v___y_496_ = v___y_516_;
v___y_497_ = v___y_518_;
v___y_498_ = v___y_522_;
v___y_499_ = v___y_517_;
v___y_500_ = v___y_509_;
goto v___jp_493_;
}
else
{
lean_object* v___x_595_; 
v___x_595_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v___y_524_, v___y_516_, v___y_517_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v_a_596_; lean_object* v___x_597_; 
v_a_596_ = lean_ctor_get(v___x_595_, 0);
lean_inc(v_a_596_);
lean_dec_ref_known(v___x_595_, 1);
v___x_597_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_591_, v_a_596_, v___y_518_, v___y_522_, v___y_517_, v___y_509_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_dec_ref_known(v___x_597_, 1);
v___y_494_ = v___y_519_;
v___y_495_ = v___y_511_;
v___y_496_ = v___y_516_;
v___y_497_ = v___y_518_;
v___y_498_ = v___y_522_;
v___y_499_ = v___y_517_;
v___y_500_ = v___y_509_;
goto v___jp_493_;
}
else
{
lean_dec_ref(v___y_519_);
lean_dec_ref(v___y_517_);
lean_dec_ref(v___y_511_);
return v___x_597_;
}
}
else
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
lean_dec(v___x_591_);
lean_dec_ref(v___y_519_);
lean_dec_ref(v___y_517_);
lean_dec_ref(v___y_511_);
v_a_598_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_605_ == 0)
{
v___x_600_ = v___x_595_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_595_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_601_ == 0)
{
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_598_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
}
}
}
v___jp_606_:
{
lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_618_, 0, v___y_607_);
v___x_619_ = l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(v___x_618_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_);
lean_dec_ref(v___y_616_);
if (lean_obj_tag(v___x_619_) == 0)
{
lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_627_; 
v_isSharedCheck_627_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_627_ == 0)
{
lean_object* v_unused_628_; 
v_unused_628_ = lean_ctor_get(v___x_619_, 0);
lean_dec(v_unused_628_);
v___x_621_ = v___x_619_;
v_isShared_622_ = v_isSharedCheck_627_;
goto v_resetjp_620_;
}
else
{
lean_dec(v___x_619_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_627_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_623_; lean_object* v___x_625_; 
v___x_623_ = lean_box(0);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v___x_623_);
v___x_625_ = v___x_621_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v___x_623_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
}
else
{
return v___x_619_;
}
}
v___jp_646_:
{
lean_object* v___x_668_; 
v___x_668_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v___y_658_, v___y_666_);
if (lean_obj_tag(v___x_668_) == 0)
{
lean_object* v_a_669_; lean_object* v_dvds_670_; lean_object* v_size_671_; uint8_t v___x_672_; 
v_a_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_a_669_);
lean_dec_ref_known(v___x_668_, 1);
v_dvds_670_ = lean_ctor_get(v_a_669_, 6);
lean_inc_ref(v_dvds_670_);
lean_dec(v_a_669_);
v_size_671_ = lean_ctor_get(v_dvds_670_, 2);
v___x_672_ = lean_nat_dec_lt(v___y_653_, v_size_671_);
if (v___x_672_ == 0)
{
lean_object* v___x_673_; 
lean_dec_ref(v_dvds_670_);
v___x_673_ = l_outOfBounds___redArg(v___x_645_);
v___y_505_ = v___y_647_;
v___y_506_ = v___y_659_;
v___y_507_ = v___y_648_;
v___y_508_ = v___y_649_;
v___y_509_ = v___y_667_;
v___y_510_ = v___y_653_;
v___y_511_ = v___y_654_;
v___y_512_ = v___y_657_;
v___y_513_ = v___y_660_;
v___y_514_ = v___y_663_;
v___y_515_ = v___y_662_;
v___y_516_ = v___y_658_;
v___y_517_ = v___y_666_;
v___y_518_ = v___y_664_;
v___y_519_ = v___y_650_;
v___y_520_ = v___y_651_;
v___y_521_ = v___y_652_;
v___y_522_ = v___y_665_;
v___y_523_ = v___y_656_;
v___y_524_ = v___y_655_;
v___y_525_ = v___y_661_;
v___y_526_ = v___x_673_;
goto v___jp_504_;
}
else
{
lean_object* v___x_674_; 
v___x_674_ = l_Lean_PersistentArray_get_x21___redArg(v___x_645_, v_dvds_670_, v___y_653_);
lean_dec_ref(v_dvds_670_);
v___y_505_ = v___y_647_;
v___y_506_ = v___y_659_;
v___y_507_ = v___y_648_;
v___y_508_ = v___y_649_;
v___y_509_ = v___y_667_;
v___y_510_ = v___y_653_;
v___y_511_ = v___y_654_;
v___y_512_ = v___y_657_;
v___y_513_ = v___y_660_;
v___y_514_ = v___y_663_;
v___y_515_ = v___y_662_;
v___y_516_ = v___y_658_;
v___y_517_ = v___y_666_;
v___y_518_ = v___y_664_;
v___y_519_ = v___y_650_;
v___y_520_ = v___y_651_;
v___y_521_ = v___y_652_;
v___y_522_ = v___y_665_;
v___y_523_ = v___y_656_;
v___y_524_ = v___y_655_;
v___y_525_ = v___y_661_;
v___y_526_ = v___x_674_;
goto v___jp_504_;
}
}
else
{
lean_object* v_a_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_682_; 
lean_dec_ref(v___y_666_);
lean_dec_ref(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec_ref(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_650_);
lean_dec(v___y_649_);
lean_dec(v___y_648_);
v_a_675_ = lean_ctor_get(v___x_668_, 0);
v_isSharedCheck_682_ = !lean_is_exclusive(v___x_668_);
if (v_isSharedCheck_682_ == 0)
{
v___x_677_ = v___x_668_;
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_a_675_);
lean_dec(v___x_668_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_682_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v___x_680_; 
if (v_isShared_678_ == 0)
{
v___x_680_ = v___x_677_;
goto v_reusejp_679_;
}
else
{
lean_object* v_reuseFailAlloc_681_; 
v_reuseFailAlloc_681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_681_, 0, v_a_675_);
v___x_680_ = v_reuseFailAlloc_681_;
goto v_reusejp_679_;
}
v_reusejp_679_:
{
return v___x_680_;
}
}
}
}
v___jp_683_:
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(v_c_478_);
lean_inc_ref(v___y_695_);
v___x_698_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(v___x_697_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v_a_699_; lean_object* v_d_700_; lean_object* v_p_701_; uint8_t v___x_702_; 
v_a_699_ = lean_ctor_get(v___x_698_, 0);
lean_inc(v_a_699_);
lean_dec_ref_known(v___x_698_, 1);
v_d_700_ = lean_ctor_get(v_a_699_, 0);
v_p_701_ = lean_ctor_get(v_a_699_, 1);
lean_inc(v_d_700_);
v___x_702_ = l_Int_Internal_Linear_Poly_isUnsatDvd(v_d_700_, v_p_701_);
if (v___x_702_ == 0)
{
uint8_t v___x_703_; 
v___x_703_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(v_a_699_);
if (v___x_703_ == 0)
{
lean_object* v___x_704_; uint8_t v___x_705_; 
v___x_704_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1);
v___x_705_ = lean_int_dec_eq(v_d_700_, v___x_704_);
if (v___x_705_ == 0)
{
if (lean_obj_tag(v_p_701_) == 1)
{
lean_object* v_k_706_; lean_object* v_v_707_; lean_object* v_p_708_; lean_object* v___x_709_; 
lean_inc_ref(v_p_701_);
lean_inc(v_d_700_);
v_k_706_ = lean_ctor_get(v_p_701_, 0);
lean_inc(v_k_706_);
v_v_707_ = lean_ctor_get(v_p_701_, 1);
lean_inc(v_v_707_);
v_p_708_ = lean_ctor_get(v_p_701_, 2);
lean_inc_ref(v_p_708_);
lean_inc(v_a_699_);
v___x_709_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(v_a_699_, v___y_687_, v___y_695_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; lean_object* v___f_711_; lean_object* v___f_712_; uint8_t v___x_713_; uint8_t v___x_714_; uint8_t v___x_715_; 
v_a_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_a_710_);
lean_dec_ref_known(v___x_709_, 1);
lean_inc_n(v_v_707_, 2);
lean_inc(v_a_699_);
v___f_711_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed), 3, 2);
lean_closure_set(v___f_711_, 0, v_a_699_);
lean_closure_set(v___f_711_, 1, v_v_707_);
v___f_712_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed), 2, 1);
lean_closure_set(v___f_712_, 0, v_v_707_);
v___x_713_ = 0;
v___x_714_ = lean_unbox(v_a_710_);
lean_dec(v_a_710_);
v___x_715_ = l_Lean_instBEqLBool_beq(v___x_714_, v___x_713_);
if (v___x_715_ == 0)
{
v___y_647_ = v___y_684_;
v___y_648_ = v_d_700_;
v___y_649_ = v_k_706_;
v___y_650_ = v___f_711_;
v___y_651_ = v___y_685_;
v___y_652_ = v___y_686_;
v___y_653_ = v_v_707_;
v___y_654_ = v_p_701_;
v___y_655_ = v_a_699_;
v___y_656_ = v_p_708_;
v___y_657_ = v___f_712_;
v___y_658_ = v___y_687_;
v___y_659_ = v___y_688_;
v___y_660_ = v___y_689_;
v___y_661_ = v___y_690_;
v___y_662_ = v___y_691_;
v___y_663_ = v___y_692_;
v___y_664_ = v___y_693_;
v___y_665_ = v___y_694_;
v___y_666_ = v___y_695_;
v___y_667_ = v___y_696_;
goto v___jp_646_;
}
else
{
lean_object* v___x_716_; 
lean_inc(v_v_707_);
v___x_716_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v_v_707_, v___y_687_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_dec_ref_known(v___x_716_, 1);
v___y_647_ = v___y_684_;
v___y_648_ = v_d_700_;
v___y_649_ = v_k_706_;
v___y_650_ = v___f_711_;
v___y_651_ = v___y_685_;
v___y_652_ = v___y_686_;
v___y_653_ = v_v_707_;
v___y_654_ = v_p_701_;
v___y_655_ = v_a_699_;
v___y_656_ = v_p_708_;
v___y_657_ = v___f_712_;
v___y_658_ = v___y_687_;
v___y_659_ = v___y_688_;
v___y_660_ = v___y_689_;
v___y_661_ = v___y_690_;
v___y_662_ = v___y_691_;
v___y_663_ = v___y_692_;
v___y_664_ = v___y_693_;
v___y_665_ = v___y_694_;
v___y_666_ = v___y_695_;
v___y_667_ = v___y_696_;
goto v___jp_646_;
}
else
{
lean_dec_ref(v___f_712_);
lean_dec_ref(v___f_711_);
lean_dec_ref(v_p_708_);
lean_dec(v_v_707_);
lean_dec_ref_known(v_p_701_, 3);
lean_dec(v_k_706_);
lean_dec(v_d_700_);
lean_dec(v_a_699_);
lean_dec_ref(v___y_695_);
return v___x_716_;
}
}
}
else
{
lean_object* v_a_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_724_; 
lean_dec_ref(v_p_708_);
lean_dec(v_v_707_);
lean_dec(v_k_706_);
lean_dec_ref_known(v_p_701_, 3);
lean_dec(v_d_700_);
lean_dec(v_a_699_);
lean_dec_ref(v___y_695_);
v_a_717_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_724_ == 0)
{
v___x_719_ = v___x_709_;
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_a_717_);
lean_dec(v___x_709_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_724_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v___x_722_; 
if (v_isShared_720_ == 0)
{
v___x_722_ = v___x_719_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_a_717_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
}
else
{
lean_object* v___x_725_; 
v___x_725_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_a_699_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
lean_dec_ref(v___y_695_);
return v___x_725_;
}
}
else
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; 
lean_inc_ref(v_p_701_);
v___x_726_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_726_, 0, v_a_699_);
v___x_727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_727_, 0, v_p_701_);
lean_ctor_set(v___x_727_, 1, v___x_726_);
lean_inc(v___y_696_);
lean_inc(v___y_694_);
lean_inc_ref(v___y_693_);
lean_inc(v___y_692_);
lean_inc_ref(v___y_691_);
lean_inc(v___y_690_);
lean_inc_ref(v___y_689_);
lean_inc(v___y_688_);
lean_inc(v___y_687_);
v___x_728_ = lean_grind_cutsat_assert_eq(v___x_727_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
if (lean_obj_tag(v___x_728_) == 0)
{
lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_736_; 
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_736_ == 0)
{
lean_object* v_unused_737_; 
v_unused_737_ = lean_ctor_get(v___x_728_, 0);
lean_dec(v_unused_737_);
v___x_730_ = v___x_728_;
v_isShared_731_ = v_isSharedCheck_736_;
goto v_resetjp_729_;
}
else
{
lean_dec(v___x_728_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_736_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_732_; lean_object* v___x_734_; 
v___x_732_ = lean_box(0);
if (v_isShared_731_ == 0)
{
lean_ctor_set(v___x_730_, 0, v___x_732_);
v___x_734_ = v___x_730_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v___x_732_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
}
}
}
else
{
return v___x_728_;
}
}
}
else
{
lean_object* v_options_738_; uint8_t v_hasTrace_739_; 
v_options_738_ = lean_ctor_get(v___y_695_, 2);
v_hasTrace_739_ = lean_ctor_get_uint8(v_options_738_, sizeof(void*)*1);
if (v_hasTrace_739_ == 0)
{
lean_dec(v_a_699_);
lean_dec_ref(v___y_695_);
goto v___jp_490_;
}
else
{
lean_object* v_inheritedTraceOptions_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; uint8_t v___x_745_; 
v_inheritedTraceOptions_740_ = lean_ctor_get(v___y_695_, 13);
v___x_741_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1));
lean_inc_ref(v___y_685_);
lean_inc_ref(v___y_684_);
lean_inc_ref(v___y_686_);
v___x_742_ = l_Lean_Name_mkStr4(v___y_686_, v___y_684_, v___y_685_, v___x_741_);
v___x_743_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
lean_inc(v___x_742_);
v___x_744_ = l_Lean_Name_append(v___x_743_, v___x_742_);
v___x_745_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_740_, v_options_738_, v___x_744_);
lean_dec(v___x_744_);
if (v___x_745_ == 0)
{
lean_dec(v___x_742_);
lean_dec(v_a_699_);
lean_dec_ref(v___y_695_);
goto v___jp_490_;
}
else
{
lean_object* v___x_746_; 
v___x_746_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_a_699_, v___y_687_, v___y_695_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; lean_object* v___x_748_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
lean_inc(v_a_747_);
lean_dec_ref_known(v___x_746_, 1);
v___x_748_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_742_, v_a_747_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
lean_dec_ref(v___y_695_);
if (lean_obj_tag(v___x_748_) == 0)
{
lean_dec_ref_known(v___x_748_, 1);
goto v___jp_490_;
}
else
{
return v___x_748_;
}
}
else
{
lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_756_; 
lean_dec(v___x_742_);
lean_dec_ref(v___y_695_);
v_a_749_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_756_ == 0)
{
v___x_751_ = v___x_746_;
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_746_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_754_; 
if (v_isShared_752_ == 0)
{
v___x_754_ = v___x_751_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_a_749_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
}
}
}
}
else
{
lean_object* v_options_757_; uint8_t v_hasTrace_758_; 
v_options_757_ = lean_ctor_get(v___y_695_, 2);
v_hasTrace_758_ = lean_ctor_get_uint8(v_options_757_, sizeof(void*)*1);
if (v_hasTrace_758_ == 0)
{
v___y_607_ = v_a_699_;
v___y_608_ = v___y_687_;
v___y_609_ = v___y_688_;
v___y_610_ = v___y_689_;
v___y_611_ = v___y_690_;
v___y_612_ = v___y_691_;
v___y_613_ = v___y_692_;
v___y_614_ = v___y_693_;
v___y_615_ = v___y_694_;
v___y_616_ = v___y_695_;
v___y_617_ = v___y_696_;
goto v___jp_606_;
}
else
{
lean_object* v_inheritedTraceOptions_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; uint8_t v___x_764_; 
v_inheritedTraceOptions_759_ = lean_ctor_get(v___y_695_, 13);
v___x_760_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2));
lean_inc_ref(v___y_685_);
lean_inc_ref(v___y_684_);
lean_inc_ref(v___y_686_);
v___x_761_ = l_Lean_Name_mkStr4(v___y_686_, v___y_684_, v___y_685_, v___x_760_);
v___x_762_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
lean_inc(v___x_761_);
v___x_763_ = l_Lean_Name_append(v___x_762_, v___x_761_);
v___x_764_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_759_, v_options_757_, v___x_763_);
lean_dec(v___x_763_);
if (v___x_764_ == 0)
{
lean_dec(v___x_761_);
v___y_607_ = v_a_699_;
v___y_608_ = v___y_687_;
v___y_609_ = v___y_688_;
v___y_610_ = v___y_689_;
v___y_611_ = v___y_690_;
v___y_612_ = v___y_691_;
v___y_613_ = v___y_692_;
v___y_614_ = v___y_693_;
v___y_615_ = v___y_694_;
v___y_616_ = v___y_695_;
v___y_617_ = v___y_696_;
goto v___jp_606_;
}
else
{
lean_object* v___x_765_; 
lean_inc(v_a_699_);
v___x_765_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_a_699_, v___y_687_, v___y_695_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; lean_object* v___x_767_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_a_766_);
lean_dec_ref_known(v___x_765_, 1);
v___x_767_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_761_, v_a_766_, v___y_693_, v___y_694_, v___y_695_, v___y_696_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_dec_ref_known(v___x_767_, 1);
v___y_607_ = v_a_699_;
v___y_608_ = v___y_687_;
v___y_609_ = v___y_688_;
v___y_610_ = v___y_689_;
v___y_611_ = v___y_690_;
v___y_612_ = v___y_691_;
v___y_613_ = v___y_692_;
v___y_614_ = v___y_693_;
v___y_615_ = v___y_694_;
v___y_616_ = v___y_695_;
v___y_617_ = v___y_696_;
goto v___jp_606_;
}
else
{
lean_dec(v_a_699_);
lean_dec_ref(v___y_695_);
return v___x_767_;
}
}
else
{
lean_object* v_a_768_; lean_object* v___x_770_; uint8_t v_isShared_771_; uint8_t v_isSharedCheck_775_; 
lean_dec(v___x_761_);
lean_dec(v_a_699_);
lean_dec_ref(v___y_695_);
v_a_768_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_775_ == 0)
{
v___x_770_ = v___x_765_;
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
else
{
lean_inc(v_a_768_);
lean_dec(v___x_765_);
v___x_770_ = lean_box(0);
v_isShared_771_ = v_isSharedCheck_775_;
goto v_resetjp_769_;
}
v_resetjp_769_:
{
lean_object* v___x_773_; 
if (v_isShared_771_ == 0)
{
v___x_773_ = v___x_770_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_a_768_);
v___x_773_ = v_reuseFailAlloc_774_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
return v___x_773_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
lean_dec_ref(v___y_695_);
v_a_776_ = lean_ctor_get(v___x_698_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_698_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_698_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_698_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_776_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
v___jp_784_:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_785_ = lean_unsigned_to_nat(1u);
v___x_786_ = lean_nat_add(v_currRecDepth_632_, v___x_785_);
lean_dec(v_currRecDepth_632_);
lean_inc_ref(v_inheritedTraceOptions_644_);
lean_inc_ref(v_options_631_);
v___x_787_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_787_, 0, v_fileName_629_);
lean_ctor_set(v___x_787_, 1, v_fileMap_630_);
lean_ctor_set(v___x_787_, 2, v_options_631_);
lean_ctor_set(v___x_787_, 3, v___x_786_);
lean_ctor_set(v___x_787_, 4, v_maxRecDepth_633_);
lean_ctor_set(v___x_787_, 5, v_ref_634_);
lean_ctor_set(v___x_787_, 6, v_currNamespace_635_);
lean_ctor_set(v___x_787_, 7, v_openDecls_636_);
lean_ctor_set(v___x_787_, 8, v_initHeartbeats_637_);
lean_ctor_set(v___x_787_, 9, v_maxHeartbeats_638_);
lean_ctor_set(v___x_787_, 10, v_quotContext_639_);
lean_ctor_set(v___x_787_, 11, v_currMacroScope_640_);
lean_ctor_set(v___x_787_, 12, v_cancelTk_x3f_642_);
lean_ctor_set(v___x_787_, 13, v_inheritedTraceOptions_644_);
lean_ctor_set_uint8(v___x_787_, sizeof(void*)*14, v_diag_641_);
lean_ctor_set_uint8(v___x_787_, sizeof(void*)*14 + 1, v_suppressElabErrors_643_);
v___x_788_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_479_, v___x_787_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_816_; 
v_a_789_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_816_ == 0)
{
v___x_791_ = v___x_788_;
v_isShared_792_ = v_isSharedCheck_816_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___x_788_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_816_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
uint8_t v___x_793_; 
v___x_793_ = lean_unbox(v_a_789_);
lean_dec(v_a_789_);
if (v___x_793_ == 0)
{
uint8_t v_hasTrace_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; 
lean_del_object(v___x_791_);
v_hasTrace_794_ = lean_ctor_get_uint8(v_options_631_, sizeof(void*)*1);
v___x_795_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0));
v___x_796_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2));
v___x_797_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3));
if (v_hasTrace_794_ == 0)
{
lean_dec_ref(v_inheritedTraceOptions_644_);
lean_dec_ref(v_options_631_);
v___y_684_ = v___x_796_;
v___y_685_ = v___x_797_;
v___y_686_ = v___x_795_;
v___y_687_ = v_a_479_;
v___y_688_ = v_a_480_;
v___y_689_ = v_a_481_;
v___y_690_ = v_a_482_;
v___y_691_ = v_a_483_;
v___y_692_ = v_a_484_;
v___y_693_ = v_a_485_;
v___y_694_ = v_a_486_;
v___y_695_ = v___x_787_;
v___y_696_ = v_a_488_;
goto v___jp_683_;
}
else
{
lean_object* v___x_798_; lean_object* v___x_799_; uint8_t v___x_800_; 
v___x_798_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4));
v___x_799_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5);
v___x_800_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_644_, v_options_631_, v___x_799_);
lean_dec_ref(v_options_631_);
lean_dec_ref(v_inheritedTraceOptions_644_);
if (v___x_800_ == 0)
{
v___y_684_ = v___x_796_;
v___y_685_ = v___x_797_;
v___y_686_ = v___x_795_;
v___y_687_ = v_a_479_;
v___y_688_ = v_a_480_;
v___y_689_ = v_a_481_;
v___y_690_ = v_a_482_;
v___y_691_ = v_a_483_;
v___y_692_ = v_a_484_;
v___y_693_ = v_a_485_;
v___y_694_ = v_a_486_;
v___y_695_ = v___x_787_;
v___y_696_ = v_a_488_;
goto v___jp_683_;
}
else
{
lean_object* v___x_801_; 
lean_inc_ref(v_c_478_);
v___x_801_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_478_, v_a_479_, v___x_787_);
if (lean_obj_tag(v___x_801_) == 0)
{
lean_object* v_a_802_; lean_object* v___x_803_; 
v_a_802_ = lean_ctor_get(v___x_801_, 0);
lean_inc(v_a_802_);
lean_dec_ref_known(v___x_801_, 1);
v___x_803_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_798_, v_a_802_, v_a_485_, v_a_486_, v___x_787_, v_a_488_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_dec_ref_known(v___x_803_, 1);
v___y_684_ = v___x_796_;
v___y_685_ = v___x_797_;
v___y_686_ = v___x_795_;
v___y_687_ = v_a_479_;
v___y_688_ = v_a_480_;
v___y_689_ = v_a_481_;
v___y_690_ = v_a_482_;
v___y_691_ = v_a_483_;
v___y_692_ = v_a_484_;
v___y_693_ = v_a_485_;
v___y_694_ = v_a_486_;
v___y_695_ = v___x_787_;
v___y_696_ = v_a_488_;
goto v___jp_683_;
}
else
{
lean_dec_ref_known(v___x_787_, 14);
lean_dec_ref(v_c_478_);
return v___x_803_;
}
}
else
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_811_; 
lean_dec_ref_known(v___x_787_, 14);
lean_dec_ref(v_c_478_);
v_a_804_ = lean_ctor_get(v___x_801_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_801_);
if (v_isSharedCheck_811_ == 0)
{
v___x_806_ = v___x_801_;
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_801_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_809_; 
if (v_isShared_807_ == 0)
{
v___x_809_ = v___x_806_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_a_804_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
}
}
}
else
{
lean_object* v___x_812_; lean_object* v___x_814_; 
lean_dec_ref_known(v___x_787_, 14);
lean_dec_ref(v_inheritedTraceOptions_644_);
lean_dec_ref(v_options_631_);
lean_dec_ref(v_c_478_);
v___x_812_ = lean_box(0);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 0, v___x_812_);
v___x_814_ = v___x_791_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v___x_812_);
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
else
{
lean_object* v_a_817_; lean_object* v___x_819_; uint8_t v_isShared_820_; uint8_t v_isSharedCheck_824_; 
lean_dec_ref_known(v___x_787_, 14);
lean_dec_ref(v_inheritedTraceOptions_644_);
lean_dec_ref(v_options_631_);
lean_dec_ref(v_c_478_);
v_a_817_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_824_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_824_ == 0)
{
v___x_819_ = v___x_788_;
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
else
{
lean_inc(v_a_817_);
lean_dec(v___x_788_);
v___x_819_ = lean_box(0);
v_isShared_820_ = v_isSharedCheck_824_;
goto v_resetjp_818_;
}
v_resetjp_818_:
{
lean_object* v___x_822_; 
if (v_isShared_820_ == 0)
{
v___x_822_ = v___x_819_;
goto v_reusejp_821_;
}
else
{
lean_object* v_reuseFailAlloc_823_; 
v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_823_, 0, v_a_817_);
v___x_822_ = v_reuseFailAlloc_823_;
goto v_reusejp_821_;
}
v_reusejp_821_:
{
return v___x_822_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___boxed(lean_object* v_c_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v_c_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_);
lean_dec(v_a_839_);
lean_dec(v_a_837_);
lean_dec_ref(v_a_836_);
lean_dec(v_a_835_);
lean_dec_ref(v_a_834_);
lean_dec(v_a_833_);
lean_dec_ref(v_a_832_);
lean_dec(v_a_831_);
lean_dec(v_a_830_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(lean_object* v_c_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_){
_start:
{
lean_object* v_d_854_; lean_object* v_p_855_; lean_object* v___x_856_; 
v_d_854_ = lean_ctor_get(v_c_842_, 0);
v_p_855_ = lean_ctor_get(v_c_842_, 1);
lean_inc_ref(v_p_855_);
v___x_856_ = l_Int_Internal_Linear_Poly_normCommRing_x3f(v_p_855_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v_a_857_; 
v_a_857_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_a_857_);
lean_dec_ref_known(v___x_856_, 1);
if (lean_obj_tag(v_a_857_) == 1)
{
lean_object* v_val_858_; lean_object* v_snd_859_; lean_object* v_fst_860_; lean_object* v_fst_861_; lean_object* v_snd_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
lean_inc(v_d_854_);
v_val_858_ = lean_ctor_get(v_a_857_, 0);
lean_inc(v_val_858_);
lean_dec_ref_known(v_a_857_, 1);
v_snd_859_ = lean_ctor_get(v_val_858_, 1);
lean_inc(v_snd_859_);
v_fst_860_ = lean_ctor_get(v_val_858_, 0);
lean_inc(v_fst_860_);
lean_dec(v_val_858_);
v_fst_861_ = lean_ctor_get(v_snd_859_, 0);
lean_inc(v_fst_861_);
v_snd_862_ = lean_ctor_get(v_snd_859_, 1);
lean_inc(v_snd_862_);
lean_dec(v_snd_859_);
v___x_863_ = lean_alloc_ctor(12, 3, 0);
lean_ctor_set(v___x_863_, 0, v_c_842_);
lean_ctor_set(v___x_863_, 1, v_fst_860_);
lean_ctor_set(v___x_863_, 2, v_fst_861_);
v___x_864_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_864_, 0, v_d_854_);
lean_ctor_set(v___x_864_, 1, v_snd_862_);
lean_ctor_set(v___x_864_, 2, v___x_863_);
lean_inc_ref(v_a_851_);
v___x_865_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v___x_864_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_);
return v___x_865_;
}
else
{
lean_object* v___x_866_; 
lean_dec(v_a_857_);
lean_inc_ref(v_a_851_);
v___x_866_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v_c_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_);
return v___x_866_;
}
}
else
{
lean_object* v_a_867_; lean_object* v___x_869_; uint8_t v_isShared_870_; uint8_t v_isSharedCheck_874_; 
lean_dec_ref(v_c_842_);
v_a_867_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_874_ == 0)
{
v___x_869_ = v___x_856_;
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
else
{
lean_inc(v_a_867_);
lean_dec(v___x_856_);
v___x_869_ = lean_box(0);
v_isShared_870_ = v_isSharedCheck_874_;
goto v_resetjp_868_;
}
v_resetjp_868_:
{
lean_object* v___x_872_; 
if (v_isShared_870_ == 0)
{
v___x_872_ = v___x_869_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_a_867_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore___boxed(lean_object* v_c_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v_c_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_);
lean_dec(v_a_885_);
lean_dec_ref(v_a_884_);
lean_dec(v_a_883_);
lean_dec_ref(v_a_882_);
lean_dec(v_a_881_);
lean_dec_ref(v_a_880_);
lean_dec(v_a_879_);
lean_dec_ref(v_a_878_);
lean_dec(v_a_877_);
lean_dec(v_a_876_);
return v_res_887_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; 
v___x_902_ = lean_box(0);
v___x_903_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7));
v___x_904_ = l_Lean_mkConst(v___x_903_, v___x_902_);
return v___x_904_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10(void){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_906_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9));
v___x_907_ = l_Lean_stringToMessageData(v___x_906_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(lean_object* v_e_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_){
_start:
{
lean_object* v___x_923_; 
lean_inc_ref(v_e_908_);
v___x_923_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_908_, v_a_916_);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_1057_; 
v_a_924_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_926_ = v___x_923_;
v_isShared_927_ = v_isSharedCheck_1057_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_923_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_1057_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_933_; uint8_t v___x_934_; 
v___x_933_ = l_Lean_Expr_cleanupAnnotations(v_a_924_);
v___x_934_ = l_Lean_Expr_isApp(v___x_933_);
if (v___x_934_ == 0)
{
lean_dec_ref(v___x_933_);
lean_dec_ref(v_e_908_);
goto v___jp_928_;
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
lean_dec_ref(v_e_908_);
goto v___jp_928_;
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
lean_dec_ref(v_e_908_);
goto v___jp_928_;
}
else
{
lean_object* v_arg_941_; lean_object* v___x_942_; uint8_t v___x_943_; 
v_arg_941_ = lean_ctor_get(v___x_939_, 1);
lean_inc_ref(v_arg_941_);
v___x_942_ = l_Lean_Expr_appFnCleanup___redArg(v___x_939_);
v___x_943_ = l_Lean_Expr_isApp(v___x_942_);
if (v___x_943_ == 0)
{
lean_dec_ref(v___x_942_);
lean_dec_ref(v_arg_941_);
lean_dec_ref(v_arg_938_);
lean_dec_ref(v_arg_935_);
lean_dec_ref(v_e_908_);
goto v___jp_928_;
}
else
{
lean_object* v___x_944_; lean_object* v___x_945_; uint8_t v___x_946_; 
v___x_944_ = l_Lean_Expr_appFnCleanup___redArg(v___x_942_);
v___x_945_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_946_ = l_Lean_Expr_isConstOf(v___x_944_, v___x_945_);
lean_dec_ref(v___x_944_);
if (v___x_946_ == 0)
{
lean_dec_ref(v_arg_941_);
lean_dec_ref(v_arg_938_);
lean_dec_ref(v_arg_935_);
lean_dec_ref(v_e_908_);
goto v___jp_928_;
}
else
{
lean_object* v___x_947_; 
lean_del_object(v___x_926_);
v___x_947_ = l_Lean_Meta_Structural_isInstDvdInt___redArg(v_arg_941_, v_a_916_);
if (lean_obj_tag(v___x_947_) == 0)
{
lean_object* v_a_948_; lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_1048_; 
v_a_948_ = lean_ctor_get(v___x_947_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_947_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_950_ = v___x_947_;
v_isShared_951_ = v_isSharedCheck_1048_;
goto v_resetjp_949_;
}
else
{
lean_inc(v_a_948_);
lean_dec(v___x_947_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_1048_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
uint8_t v___x_952_; 
v___x_952_ = lean_unbox(v_a_948_);
lean_dec(v_a_948_);
if (v___x_952_ == 0)
{
lean_object* v___x_953_; lean_object* v___x_955_; 
lean_dec_ref(v_arg_938_);
lean_dec_ref(v_arg_935_);
lean_dec_ref(v_e_908_);
v___x_953_ = lean_box(0);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 0, v___x_953_);
v___x_955_ = v___x_950_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v___x_953_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
return v___x_955_;
}
}
else
{
lean_object* v___x_957_; 
lean_del_object(v___x_950_);
lean_inc_ref(v_arg_938_);
v___x_957_ = l_Lean_Meta_getIntValue_x3f(v_arg_938_, v_a_915_, v_a_916_, v_a_917_, v_a_918_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v_a_958_; 
v_a_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_a_958_);
lean_dec_ref_known(v___x_957_, 1);
if (lean_obj_tag(v_a_958_) == 1)
{
lean_object* v_val_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_1024_; 
v_val_959_ = lean_ctor_get(v_a_958_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v_a_958_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_961_ = v_a_958_;
v_isShared_962_ = v_isSharedCheck_1024_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_val_959_);
lean_dec(v_a_958_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_1024_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_963_; 
lean_inc_ref(v_e_908_);
v___x_963_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_908_, v_a_909_, v_a_913_, v_a_915_, v_a_916_, v_a_917_, v_a_918_);
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v_a_964_; uint8_t v___x_965_; 
v_a_964_ = lean_ctor_get(v___x_963_, 0);
lean_inc(v_a_964_);
lean_dec_ref_known(v___x_963_, 1);
v___x_965_ = lean_unbox(v_a_964_);
lean_dec(v_a_964_);
if (v___x_965_ == 0)
{
lean_object* v___x_966_; 
lean_del_object(v___x_961_);
lean_dec(v_val_959_);
lean_inc_ref(v_e_908_);
v___x_966_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_908_, v_a_909_, v_a_913_, v_a_915_, v_a_916_, v_a_917_, v_a_918_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_992_; 
v_a_967_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_992_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_992_ == 0)
{
v___x_969_ = v___x_966_;
v_isShared_970_ = v_isSharedCheck_992_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_966_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_992_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
uint8_t v___x_971_; 
v___x_971_ = lean_unbox(v_a_967_);
lean_dec(v_a_967_);
if (v___x_971_ == 0)
{
lean_object* v___x_972_; lean_object* v___x_974_; 
lean_dec_ref(v_arg_938_);
lean_dec_ref(v_arg_935_);
lean_dec_ref(v_e_908_);
v___x_972_ = lean_box(0);
if (v_isShared_970_ == 0)
{
lean_ctor_set(v___x_969_, 0, v___x_972_);
v___x_974_ = v___x_969_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v___x_972_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
else
{
lean_object* v___x_976_; 
lean_del_object(v___x_969_);
lean_inc_ref(v_e_908_);
v___x_976_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_);
if (lean_obj_tag(v___x_976_) == 0)
{
lean_object* v_a_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; 
v_a_977_ = lean_ctor_get(v___x_976_, 0);
lean_inc(v_a_977_);
lean_dec_ref_known(v___x_976_, 1);
v___x_978_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8);
v___x_979_ = l_Lean_eagerReflBoolTrue;
v___x_980_ = l_Lean_Meta_mkOfEqFalseCore(v_e_908_, v_a_977_);
v___x_981_ = l_Lean_mkApp4(v___x_978_, v_arg_938_, v_arg_935_, v___x_979_, v___x_980_);
v___x_982_ = lean_unsigned_to_nat(0u);
v___x_983_ = l_Lean_Meta_Grind_pushNewFact(v___x_981_, v___x_982_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_);
return v___x_983_;
}
else
{
lean_object* v_a_984_; lean_object* v___x_986_; uint8_t v_isShared_987_; uint8_t v_isSharedCheck_991_; 
lean_dec_ref(v_arg_938_);
lean_dec_ref(v_arg_935_);
lean_dec_ref(v_e_908_);
v_a_984_ = lean_ctor_get(v___x_976_, 0);
v_isSharedCheck_991_ = !lean_is_exclusive(v___x_976_);
if (v_isSharedCheck_991_ == 0)
{
v___x_986_ = v___x_976_;
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
else
{
lean_inc(v_a_984_);
lean_dec(v___x_976_);
v___x_986_ = lean_box(0);
v_isShared_987_ = v_isSharedCheck_991_;
goto v_resetjp_985_;
}
v_resetjp_985_:
{
lean_object* v___x_989_; 
if (v_isShared_987_ == 0)
{
v___x_989_ = v___x_986_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_a_984_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
}
}
}
}
else
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
lean_dec_ref(v_arg_938_);
lean_dec_ref(v_arg_935_);
lean_dec_ref(v_e_908_);
v_a_993_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_995_ = v___x_966_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_966_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_998_; 
if (v_isShared_996_ == 0)
{
v___x_998_ = v___x_995_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_a_993_);
v___x_998_ = v_reuseFailAlloc_999_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
return v___x_998_;
}
}
}
}
else
{
lean_object* v___x_1001_; 
lean_dec_ref(v_arg_938_);
v___x_1001_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(v_arg_935_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; lean_object* v___x_1004_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
lean_inc(v_a_1002_);
lean_dec_ref_known(v___x_1001_, 1);
if (v_isShared_962_ == 0)
{
lean_ctor_set_tag(v___x_961_, 0);
lean_ctor_set(v___x_961_, 0, v_e_908_);
v___x_1004_ = v___x_961_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_e_908_);
v___x_1004_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1005_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1005_, 0, v_val_959_);
lean_ctor_set(v___x_1005_, 1, v_a_1002_);
lean_ctor_set(v___x_1005_, 2, v___x_1004_);
v___x_1006_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v___x_1005_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_);
return v___x_1006_;
}
}
else
{
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1015_; 
lean_del_object(v___x_961_);
lean_dec(v_val_959_);
lean_dec_ref(v_e_908_);
v_a_1008_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1010_ = v___x_1001_;
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_dec(v___x_1001_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1013_; 
if (v_isShared_1011_ == 0)
{
v___x_1013_ = v___x_1010_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_a_1008_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
}
}
else
{
lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1023_; 
lean_del_object(v___x_961_);
lean_dec(v_val_959_);
lean_dec_ref(v_arg_938_);
lean_dec_ref(v_arg_935_);
lean_dec_ref(v_e_908_);
v_a_1016_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1018_ = v___x_963_;
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_963_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1021_; 
if (v_isShared_1019_ == 0)
{
v___x_1021_ = v___x_1018_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_a_1016_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
}
}
else
{
lean_object* v___x_1025_; 
lean_dec(v_a_958_);
lean_dec_ref(v_arg_938_);
lean_dec_ref(v_arg_935_);
v___x_1025_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_913_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; uint8_t v_verbose_1027_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_a_1026_);
lean_dec_ref_known(v___x_1025_, 1);
v_verbose_1027_ = lean_ctor_get_uint8(v_a_1026_, 0);
lean_dec(v_a_1026_);
if (v_verbose_1027_ == 0)
{
lean_dec_ref(v_e_908_);
goto v___jp_920_;
}
else
{
lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1028_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10);
v___x_1029_ = l_Lean_indentExpr(v_e_908_);
v___x_1030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1028_);
lean_ctor_set(v___x_1030_, 1, v___x_1029_);
v___x_1031_ = l_Lean_Meta_Sym_reportIssue(v___x_1030_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_dec_ref_known(v___x_1031_, 1);
goto v___jp_920_;
}
else
{
return v___x_1031_;
}
}
}
else
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
lean_dec_ref(v_e_908_);
v_a_1032_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_1025_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_1025_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1037_; 
if (v_isShared_1035_ == 0)
{
v___x_1037_ = v___x_1034_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v_a_1032_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
}
}
else
{
lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1047_; 
lean_dec_ref(v_arg_938_);
lean_dec_ref(v_arg_935_);
lean_dec_ref(v_e_908_);
v_a_1040_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1042_ = v___x_957_;
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_957_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1045_; 
if (v_isShared_1043_ == 0)
{
v___x_1045_ = v___x_1042_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_a_1040_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
}
}
}
else
{
lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1056_; 
lean_dec_ref(v_arg_938_);
lean_dec_ref(v_arg_935_);
lean_dec_ref(v_e_908_);
v_a_1049_ = lean_ctor_get(v___x_947_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_947_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1051_ = v___x_947_;
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_dec(v___x_947_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1054_; 
if (v_isShared_1052_ == 0)
{
v___x_1054_ = v___x_1051_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_a_1049_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
}
}
}
}
}
v___jp_928_:
{
lean_object* v___x_929_; lean_object* v___x_931_; 
v___x_929_ = lean_box(0);
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 0, v___x_929_);
v___x_931_ = v___x_926_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_929_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
else
{
lean_object* v_a_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1065_; 
lean_dec_ref(v_e_908_);
v_a_1058_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_1065_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_1065_ == 0)
{
v___x_1060_ = v___x_923_;
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_a_1058_);
lean_dec(v___x_923_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1065_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1063_; 
if (v_isShared_1061_ == 0)
{
v___x_1063_ = v___x_1060_;
goto v_reusejp_1062_;
}
else
{
lean_object* v_reuseFailAlloc_1064_; 
v_reuseFailAlloc_1064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1064_, 0, v_a_1058_);
v___x_1063_ = v_reuseFailAlloc_1064_;
goto v_reusejp_1062_;
}
v_reusejp_1062_:
{
return v___x_1063_;
}
}
}
v___jp_920_:
{
lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_921_ = lean_box(0);
v___x_922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_922_, 0, v___x_921_);
return v___x_922_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___boxed(lean_object* v_e_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(v_e_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_);
lean_dec(v_a_1076_);
lean_dec_ref(v_a_1075_);
lean_dec(v_a_1074_);
lean_dec_ref(v_a_1073_);
lean_dec(v_a_1072_);
lean_dec_ref(v_a_1071_);
lean_dec(v_a_1070_);
lean_dec_ref(v_a_1069_);
lean_dec(v_a_1068_);
lean_dec(v_a_1067_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd_spec__0(lean_object* v_a_1079_){
_start:
{
lean_object* v___x_1080_; 
v___x_1080_ = lean_nat_to_int(v_a_1079_);
return v___x_1080_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3(void){
_start:
{
lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; 
v___x_1086_ = lean_box(0);
v___x_1087_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2));
v___x_1088_ = l_Lean_mkConst(v___x_1087_, v___x_1086_);
return v___x_1088_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7(void){
_start:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1095_ = lean_box(0);
v___x_1096_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6));
v___x_1097_ = l_Lean_mkConst(v___x_1096_, v___x_1095_);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(lean_object* v_e_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_){
_start:
{
lean_object* v___x_1116_; uint8_t v___x_1117_; 
lean_inc_ref(v_e_1098_);
v___x_1116_ = l_Lean_Expr_cleanupAnnotations(v_e_1098_);
v___x_1117_ = l_Lean_Expr_isApp(v___x_1116_);
if (v___x_1117_ == 0)
{
lean_dec_ref(v___x_1116_);
lean_dec_ref(v_e_1098_);
goto v___jp_1110_;
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
lean_dec_ref(v_e_1098_);
goto v___jp_1110_;
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
lean_dec_ref(v_e_1098_);
goto v___jp_1110_;
}
else
{
lean_object* v_arg_1124_; lean_object* v___x_1125_; uint8_t v___x_1126_; 
v_arg_1124_ = lean_ctor_get(v___x_1122_, 1);
lean_inc_ref(v_arg_1124_);
v___x_1125_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1122_);
v___x_1126_ = l_Lean_Expr_isApp(v___x_1125_);
if (v___x_1126_ == 0)
{
lean_dec_ref(v___x_1125_);
lean_dec_ref(v_arg_1124_);
lean_dec_ref(v_arg_1121_);
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_e_1098_);
goto v___jp_1110_;
}
else
{
lean_object* v___x_1127_; lean_object* v___x_1128_; uint8_t v___x_1129_; 
v___x_1127_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1125_);
v___x_1128_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1129_ = l_Lean_Expr_isConstOf(v___x_1127_, v___x_1128_);
lean_dec_ref(v___x_1127_);
if (v___x_1129_ == 0)
{
lean_dec_ref(v_arg_1124_);
lean_dec_ref(v_arg_1121_);
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_e_1098_);
goto v___jp_1110_;
}
else
{
lean_object* v___x_1130_; 
v___x_1130_ = l_Lean_Meta_Structural_isInstDvdNat___redArg(v_arg_1124_, v_a_1106_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1262_; 
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1133_ = v___x_1130_;
v_isShared_1134_ = v_isSharedCheck_1262_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1130_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1262_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
uint8_t v___x_1135_; 
v___x_1135_ = lean_unbox(v_a_1131_);
lean_dec(v_a_1131_);
if (v___x_1135_ == 0)
{
lean_object* v___x_1136_; lean_object* v___x_1138_; 
lean_dec_ref(v_arg_1121_);
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_e_1098_);
v___x_1136_ = lean_box(0);
if (v_isShared_1134_ == 0)
{
lean_ctor_set(v___x_1133_, 0, v___x_1136_);
v___x_1138_ = v___x_1133_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v___x_1136_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
else
{
lean_object* v___x_1140_; 
lean_del_object(v___x_1133_);
v___x_1140_ = l_Lean_Meta_getNatValue_x3f(v_arg_1121_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v_a_1141_; 
v_a_1141_ = lean_ctor_get(v___x_1140_, 0);
lean_inc(v_a_1141_);
lean_dec_ref_known(v___x_1140_, 1);
if (lean_obj_tag(v_a_1141_) == 1)
{
lean_object* v_val_1142_; lean_object* v___x_1143_; 
v_val_1142_ = lean_ctor_get(v_a_1141_, 0);
lean_inc(v_val_1142_);
lean_dec_ref_known(v_a_1141_, 1);
lean_inc_ref(v_e_1098_);
v___x_1143_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_1098_, v_a_1099_, v_a_1103_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_a_1144_; uint8_t v___x_1145_; 
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
lean_inc(v_a_1144_);
lean_dec_ref_known(v___x_1143_, 1);
v___x_1145_ = lean_unbox(v_a_1144_);
lean_dec(v_a_1144_);
if (v___x_1145_ == 0)
{
lean_object* v___x_1146_; 
lean_dec(v_val_1142_);
lean_inc_ref(v_e_1098_);
v___x_1146_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_1098_, v_a_1099_, v_a_1103_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1171_; 
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1149_ = v___x_1146_;
v_isShared_1150_ = v_isSharedCheck_1171_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1146_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1171_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
uint8_t v___x_1151_; 
v___x_1151_ = lean_unbox(v_a_1147_);
lean_dec(v_a_1147_);
if (v___x_1151_ == 0)
{
lean_object* v___x_1152_; lean_object* v___x_1154_; 
lean_dec_ref(v_arg_1121_);
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_e_1098_);
v___x_1152_ = lean_box(0);
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 0, v___x_1152_);
v___x_1154_ = v___x_1149_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v___x_1152_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
else
{
lean_object* v___x_1156_; 
lean_del_object(v___x_1149_);
lean_inc_ref(v_e_1098_);
v___x_1156_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_);
if (lean_obj_tag(v___x_1156_) == 0)
{
lean_object* v_a_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v_a_1157_ = lean_ctor_get(v___x_1156_, 0);
lean_inc(v_a_1157_);
lean_dec_ref_known(v___x_1156_, 1);
v___x_1158_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3);
v___x_1159_ = l_Lean_Meta_mkOfEqFalseCore(v_e_1098_, v_a_1157_);
v___x_1160_ = l_Lean_mkApp3(v___x_1158_, v_arg_1121_, v_arg_1118_, v___x_1159_);
v___x_1161_ = lean_unsigned_to_nat(0u);
v___x_1162_ = l_Lean_Meta_Grind_pushNewFact(v___x_1160_, v___x_1161_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_);
return v___x_1162_;
}
else
{
lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1170_; 
lean_dec_ref(v_arg_1121_);
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_e_1098_);
v_a_1163_ = lean_ctor_get(v___x_1156_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1156_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1165_ = v___x_1156_;
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___x_1156_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1168_; 
if (v_isShared_1166_ == 0)
{
v___x_1168_ = v___x_1165_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_a_1163_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
}
}
else
{
lean_object* v_a_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1179_; 
lean_dec_ref(v_arg_1121_);
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_e_1098_);
v_a_1172_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1179_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1179_ == 0)
{
v___x_1174_ = v___x_1146_;
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_a_1172_);
lean_dec(v___x_1146_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1179_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___x_1177_; 
if (v_isShared_1175_ == 0)
{
v___x_1177_ = v___x_1174_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1178_; 
v_reuseFailAlloc_1178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1178_, 0, v_a_1172_);
v___x_1177_ = v_reuseFailAlloc_1178_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
return v___x_1177_;
}
}
}
}
else
{
lean_object* v___x_1180_; 
lean_inc_ref(v_arg_1121_);
v___x_1180_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_1121_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_);
if (lean_obj_tag(v___x_1180_) == 0)
{
lean_object* v_a_1181_; lean_object* v_fst_1182_; lean_object* v_snd_1183_; lean_object* v___x_1184_; 
v_a_1181_ = lean_ctor_get(v___x_1180_, 0);
lean_inc(v_a_1181_);
lean_dec_ref_known(v___x_1180_, 1);
v_fst_1182_ = lean_ctor_get(v_a_1181_, 0);
lean_inc(v_fst_1182_);
v_snd_1183_ = lean_ctor_get(v_a_1181_, 1);
lean_inc(v_snd_1183_);
lean_dec(v_a_1181_);
lean_inc_ref(v_arg_1118_);
v___x_1184_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_1118_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_object* v_a_1185_; lean_object* v_fst_1186_; lean_object* v_snd_1187_; lean_object* v___x_1188_; 
v_a_1185_ = lean_ctor_get(v___x_1184_, 0);
lean_inc(v_a_1185_);
lean_dec_ref_known(v___x_1184_, 1);
v_fst_1186_ = lean_ctor_get(v_a_1185_, 0);
lean_inc(v_fst_1186_);
v_snd_1187_ = lean_ctor_get(v_a_1185_, 1);
lean_inc(v_snd_1187_);
lean_dec(v_a_1185_);
v___x_1188_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1098_, v_a_1099_);
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_object* v_a_1189_; lean_object* v___x_1190_; 
v_a_1189_ = lean_ctor_get(v___x_1188_, 0);
lean_inc(v_a_1189_);
lean_dec_ref_known(v___x_1188_, 1);
lean_inc(v_fst_1186_);
v___x_1190_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_1186_, v_a_1189_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_);
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_object* v_a_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v_a_1191_ = lean_ctor_get(v___x_1190_, 0);
lean_inc(v_a_1191_);
lean_dec_ref_known(v___x_1190_, 1);
v___x_1192_ = l_Int_Internal_Linear_Expr_norm(v_a_1191_);
v___x_1193_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7);
v___x_1194_ = l_Lean_mkApp6(v___x_1193_, v_arg_1121_, v_arg_1118_, v_fst_1182_, v_fst_1186_, v_snd_1183_, v_snd_1187_);
lean_inc(v_val_1142_);
v___x_1195_ = lean_nat_to_int(v_val_1142_);
v___x_1196_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1196_, 0, v_e_1098_);
lean_ctor_set(v___x_1196_, 1, v___x_1194_);
lean_ctor_set(v___x_1196_, 2, v_val_1142_);
lean_ctor_set(v___x_1196_, 3, v_a_1191_);
v___x_1197_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1195_);
lean_ctor_set(v___x_1197_, 1, v___x_1192_);
lean_ctor_set(v___x_1197_, 2, v___x_1196_);
v___x_1198_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v___x_1197_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_);
return v___x_1198_;
}
else
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1206_; 
lean_dec(v_snd_1187_);
lean_dec(v_fst_1186_);
lean_dec(v_snd_1183_);
lean_dec(v_fst_1182_);
lean_dec(v_val_1142_);
lean_dec_ref(v_arg_1121_);
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_e_1098_);
v_a_1199_ = lean_ctor_get(v___x_1190_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1201_ = v___x_1190_;
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1190_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v___x_1204_; 
if (v_isShared_1202_ == 0)
{
v___x_1204_ = v___x_1201_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_a_1199_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
}
}
else
{
lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1214_; 
lean_dec(v_snd_1187_);
lean_dec(v_fst_1186_);
lean_dec(v_snd_1183_);
lean_dec(v_fst_1182_);
lean_dec(v_val_1142_);
lean_dec_ref(v_arg_1121_);
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_e_1098_);
v_a_1207_ = lean_ctor_get(v___x_1188_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1209_ = v___x_1188_;
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_dec(v___x_1188_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1212_; 
if (v_isShared_1210_ == 0)
{
v___x_1212_ = v___x_1209_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_a_1207_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
}
else
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1222_; 
lean_dec(v_snd_1183_);
lean_dec(v_fst_1182_);
lean_dec(v_val_1142_);
lean_dec_ref(v_arg_1121_);
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_e_1098_);
v_a_1215_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1217_ = v___x_1184_;
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1184_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1218_ == 0)
{
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_a_1215_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
}
else
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1230_; 
lean_dec(v_val_1142_);
lean_dec_ref(v_arg_1121_);
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_e_1098_);
v_a_1223_ = lean_ctor_get(v___x_1180_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1180_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1225_ = v___x_1180_;
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1180_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1228_; 
if (v_isShared_1226_ == 0)
{
v___x_1228_ = v___x_1225_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_a_1223_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
}
else
{
lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1238_; 
lean_dec(v_val_1142_);
lean_dec_ref(v_arg_1121_);
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_e_1098_);
v_a_1231_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1233_ = v___x_1143_;
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v___x_1143_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1236_; 
if (v_isShared_1234_ == 0)
{
v___x_1236_ = v___x_1233_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_a_1231_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
}
else
{
lean_object* v___x_1239_; 
lean_dec(v_a_1141_);
lean_dec_ref(v_arg_1121_);
lean_dec_ref(v_arg_1118_);
v___x_1239_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1103_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v_a_1240_; uint8_t v_verbose_1241_; 
v_a_1240_ = lean_ctor_get(v___x_1239_, 0);
lean_inc(v_a_1240_);
lean_dec_ref_known(v___x_1239_, 1);
v_verbose_1241_ = lean_ctor_get_uint8(v_a_1240_, 0);
lean_dec(v_a_1240_);
if (v_verbose_1241_ == 0)
{
lean_dec_ref(v_e_1098_);
goto v___jp_1113_;
}
else
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1242_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10);
v___x_1243_ = l_Lean_indentExpr(v_e_1098_);
v___x_1244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1242_);
lean_ctor_set(v___x_1244_, 1, v___x_1243_);
v___x_1245_ = l_Lean_Meta_Sym_reportIssue(v___x_1244_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_dec_ref_known(v___x_1245_, 1);
goto v___jp_1113_;
}
else
{
return v___x_1245_;
}
}
}
else
{
lean_object* v_a_1246_; lean_object* v___x_1248_; uint8_t v_isShared_1249_; uint8_t v_isSharedCheck_1253_; 
lean_dec_ref(v_e_1098_);
v_a_1246_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1248_ = v___x_1239_;
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
else
{
lean_inc(v_a_1246_);
lean_dec(v___x_1239_);
v___x_1248_ = lean_box(0);
v_isShared_1249_ = v_isSharedCheck_1253_;
goto v_resetjp_1247_;
}
v_resetjp_1247_:
{
lean_object* v___x_1251_; 
if (v_isShared_1249_ == 0)
{
v___x_1251_ = v___x_1248_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v_a_1246_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
}
}
else
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1261_; 
lean_dec_ref(v_arg_1121_);
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_e_1098_);
v_a_1254_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1256_ = v___x_1140_;
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1140_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
if (v_isShared_1257_ == 0)
{
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_a_1254_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
}
}
else
{
lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1270_; 
lean_dec_ref(v_arg_1121_);
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_e_1098_);
v_a_1263_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1265_ = v___x_1130_;
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_dec(v___x_1130_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1268_; 
if (v_isShared_1266_ == 0)
{
v___x_1268_ = v___x_1265_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_a_1263_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
}
}
}
}
}
v___jp_1110_:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; 
v___x_1111_ = lean_box(0);
v___x_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1111_);
return v___x_1112_;
}
v___jp_1113_:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1114_ = lean_box(0);
v___x_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1114_);
return v___x_1115_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___boxed(lean_object* v_e_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(v_e_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_);
lean_dec(v_a_1281_);
lean_dec_ref(v_a_1280_);
lean_dec(v_a_1279_);
lean_dec_ref(v_a_1278_);
lean_dec(v_a_1277_);
lean_dec_ref(v_a_1276_);
lean_dec(v_a_1275_);
lean_dec_ref(v_a_1274_);
lean_dec(v_a_1273_);
lean_dec(v_a_1272_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(lean_object* v_e_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_){
_start:
{
lean_object* v___x_1298_; 
v___x_1298_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1289_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1343_; 
v_a_1299_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1301_ = v___x_1298_;
v_isShared_1302_ = v_isSharedCheck_1343_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v___x_1298_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1343_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
uint8_t v_lia_1303_; 
v_lia_1303_ = lean_ctor_get_uint8(v_a_1299_, sizeof(void*)*14 + 23);
lean_dec(v_a_1299_);
if (v_lia_1303_ == 0)
{
lean_object* v___x_1304_; lean_object* v___x_1306_; 
lean_dec_ref(v_e_1286_);
v___x_1304_ = lean_box(0);
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 0, v___x_1304_);
v___x_1306_ = v___x_1301_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v___x_1304_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
else
{
lean_object* v___x_1308_; 
lean_del_object(v___x_1301_);
lean_inc_ref(v_e_1286_);
v___x_1308_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1286_, v_a_1294_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1334_; 
v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1311_ = v___x_1308_;
v_isShared_1312_ = v_isSharedCheck_1334_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1308_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1334_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1318_; uint8_t v___x_1319_; 
v___x_1318_ = l_Lean_Expr_cleanupAnnotations(v_a_1309_);
v___x_1319_ = l_Lean_Expr_isApp(v___x_1318_);
if (v___x_1319_ == 0)
{
lean_dec_ref(v___x_1318_);
lean_dec_ref(v_e_1286_);
goto v___jp_1313_;
}
else
{
lean_object* v___x_1320_; uint8_t v___x_1321_; 
v___x_1320_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1318_);
v___x_1321_ = l_Lean_Expr_isApp(v___x_1320_);
if (v___x_1321_ == 0)
{
lean_dec_ref(v___x_1320_);
lean_dec_ref(v_e_1286_);
goto v___jp_1313_;
}
else
{
lean_object* v___x_1322_; uint8_t v___x_1323_; 
v___x_1322_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1320_);
v___x_1323_ = l_Lean_Expr_isApp(v___x_1322_);
if (v___x_1323_ == 0)
{
lean_dec_ref(v___x_1322_);
lean_dec_ref(v_e_1286_);
goto v___jp_1313_;
}
else
{
lean_object* v___x_1324_; uint8_t v___x_1325_; 
v___x_1324_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1322_);
v___x_1325_ = l_Lean_Expr_isApp(v___x_1324_);
if (v___x_1325_ == 0)
{
lean_dec_ref(v___x_1324_);
lean_dec_ref(v_e_1286_);
goto v___jp_1313_;
}
else
{
lean_object* v_arg_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; uint8_t v___x_1329_; 
v_arg_1326_ = lean_ctor_get(v___x_1324_, 1);
lean_inc_ref(v_arg_1326_);
v___x_1327_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1324_);
v___x_1328_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1329_ = l_Lean_Expr_isConstOf(v___x_1327_, v___x_1328_);
lean_dec_ref(v___x_1327_);
if (v___x_1329_ == 0)
{
lean_dec_ref(v_arg_1326_);
lean_dec_ref(v_e_1286_);
goto v___jp_1313_;
}
else
{
lean_object* v___x_1330_; uint8_t v___x_1331_; 
lean_del_object(v___x_1311_);
v___x_1330_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0));
v___x_1331_ = l_Lean_Expr_isConstOf(v_arg_1326_, v___x_1330_);
lean_dec_ref(v_arg_1326_);
if (v___x_1331_ == 0)
{
lean_object* v___x_1332_; 
v___x_1332_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(v_e_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_);
return v___x_1332_;
}
else
{
lean_object* v___x_1333_; 
v___x_1333_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(v_e_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_);
return v___x_1333_;
}
}
}
}
}
}
v___jp_1313_:
{
lean_object* v___x_1314_; lean_object* v___x_1316_; 
v___x_1314_ = lean_box(0);
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 0, v___x_1314_);
v___x_1316_ = v___x_1311_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v___x_1314_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
}
else
{
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1342_; 
lean_dec_ref(v_e_1286_);
v_a_1335_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1337_ = v___x_1308_;
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1308_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1340_; 
if (v_isShared_1338_ == 0)
{
v___x_1340_ = v___x_1337_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_a_1335_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
}
}
}
else
{
lean_object* v_a_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1351_; 
lean_dec_ref(v_e_1286_);
v_a_1344_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1346_ = v___x_1298_;
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_a_1344_);
lean_dec(v___x_1298_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1349_; 
if (v_isShared_1347_ == 0)
{
v___x_1349_ = v___x_1346_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1344_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed(lean_object* v_e_1352_, lean_object* v_a_1353_, lean_object* v_a_1354_, lean_object* v_a_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(v_e_1352_, v_a_1353_, v_a_1354_, v_a_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_);
lean_dec(v_a_1362_);
lean_dec_ref(v_a_1361_);
lean_dec(v_a_1360_);
lean_dec_ref(v_a_1359_);
lean_dec(v_a_1358_);
lean_dec_ref(v_a_1357_);
lean_dec(v_a_1356_);
lean_dec_ref(v_a_1355_);
lean_dec(v_a_1354_);
lean_dec(v_a_1353_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; 
v___x_1366_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1367_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed), 12, 0);
v___x_1368_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_1366_, v___x_1367_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_9____boxed(lean_object* v_a_1369_){
_start:
{
lean_object* v_res_1370_; 
v_res_1370_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_9_();
return v_res_1370_;
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
