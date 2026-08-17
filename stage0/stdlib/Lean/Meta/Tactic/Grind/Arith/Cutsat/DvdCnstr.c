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
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_div(lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_getConst(lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
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
lean_object* v___y_7_; lean_object* v___y_8_; lean_object* v___y_9_; lean_object* v___y_10_; uint8_t v___y_11_; lean_object* v___y_17_; lean_object* v___y_18_; lean_object* v___y_19_; lean_object* v___y_20_; lean_object* v___y_21_; lean_object* v___y_28_; lean_object* v_d_29_; lean_object* v_p_30_; lean_object* v_d_35_; lean_object* v_p_36_; uint8_t v___x_37_; 
v_d_35_ = lean_ctor_get(v_c_5_, 0);
lean_inc(v_d_35_);
v_p_36_ = lean_ctor_get(v_c_5_, 1);
v___x_37_ = l_Int_Internal_Linear_Poly_isSorted(v_p_36_);
if (v___x_37_ == 0)
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
lean_inc_ref(v_p_36_);
v___x_38_ = l_Int_Internal_Linear_Poly_norm(v_p_36_);
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
lean_dec_ref(v___y_10_);
lean_dec(v___y_8_);
lean_dec(v___y_7_);
return v___y_9_;
}
else
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_12_ = lean_int_ediv(v___y_8_, v___y_7_);
lean_dec(v___y_8_);
v___x_13_ = l_Int_Internal_Linear_Poly_div(v___y_7_, v___y_10_);
lean_dec(v___y_7_);
v___x_14_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_14_, 0, v___y_9_);
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
v___x_22_ = l_Int_Internal_Linear_Poly_getConst(v___y_20_);
v___x_23_ = lean_int_emod(v___x_22_, v___y_21_);
lean_dec(v___x_22_);
v___x_24_ = lean_int_dec_eq(v___x_23_, v___y_19_);
lean_dec(v___x_23_);
if (v___x_24_ == 0)
{
v___y_7_ = v___y_21_;
v___y_8_ = v___y_17_;
v___y_9_ = v___y_18_;
v___y_10_ = v___y_20_;
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
v___y_7_ = v___y_21_;
v___y_8_ = v___y_17_;
v___y_9_ = v___y_18_;
v___y_10_ = v___y_20_;
v___y_11_ = v___x_24_;
goto v___jp_6_;
}
else
{
lean_dec(v___y_21_);
lean_dec_ref(v___y_20_);
lean_dec(v___y_17_);
return v___y_18_;
}
}
}
v___jp_27_:
{
lean_object* v_g_31_; lean_object* v___x_32_; uint8_t v___x_33_; 
lean_inc(v_d_29_);
v_g_31_ = l_Int_Internal_Linear_Poly_gcdCoeffs(v_p_30_, v_d_29_);
v___x_32_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1);
v___x_33_ = lean_int_dec_lt(v_d_29_, v___x_32_);
if (v___x_33_ == 0)
{
v___y_17_ = v_d_29_;
v___y_18_ = v___y_28_;
v___y_19_ = v___x_32_;
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
v___y_18_ = v___y_28_;
v___y_19_ = v___x_32_;
v___y_20_ = v_p_30_;
v___y_21_ = v___x_34_;
goto v___jp_16_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0_spec__0(lean_object* v_msgData_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_){
_start:
{
lean_object* v___x_47_; lean_object* v_env_48_; lean_object* v___x_49_; lean_object* v_mctx_50_; lean_object* v_lctx_51_; lean_object* v_options_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_47_ = lean_st_ref_get(v___y_45_);
v_env_48_ = lean_ctor_get(v___x_47_, 0);
lean_inc_ref(v_env_48_);
lean_dec(v___x_47_);
v___x_49_ = lean_st_ref_get(v___y_43_);
v_mctx_50_ = lean_ctor_get(v___x_49_, 0);
lean_inc_ref(v_mctx_50_);
lean_dec(v___x_49_);
v_lctx_51_ = lean_ctor_get(v___y_42_, 2);
v_options_52_ = lean_ctor_get(v___y_44_, 2);
lean_inc_ref(v_options_52_);
lean_inc_ref(v_lctx_51_);
v___x_53_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_53_, 0, v_env_48_);
lean_ctor_set(v___x_53_, 1, v_mctx_50_);
lean_ctor_set(v___x_53_, 2, v_lctx_51_);
lean_ctor_set(v___x_53_, 3, v_options_52_);
v___x_54_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
lean_ctor_set(v___x_54_, 1, v_msgData_41_);
v___x_55_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0_spec__0___boxed(lean_object* v_msgData_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0_spec__0(v_msgData_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_);
lean_dec(v___y_60_);
lean_dec_ref(v___y_59_);
lean_dec(v___y_58_);
lean_dec_ref(v___y_57_);
return v_res_62_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_63_; double v___x_64_; 
v___x_63_ = lean_unsigned_to_nat(0u);
v___x_64_ = lean_float_of_nat(v___x_63_);
return v___x_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(lean_object* v_cls_68_, lean_object* v_msg_69_, lean_object* v___y_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_){
_start:
{
lean_object* v_ref_75_; lean_object* v___x_76_; lean_object* v_a_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_121_; 
v_ref_75_ = lean_ctor_get(v___y_72_, 5);
v___x_76_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0_spec__0(v_msg_69_, v___y_70_, v___y_71_, v___y_72_, v___y_73_);
v_a_77_ = lean_ctor_get(v___x_76_, 0);
v_isSharedCheck_121_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_121_ == 0)
{
v___x_79_ = v___x_76_;
v_isShared_80_ = v_isSharedCheck_121_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_a_77_);
lean_dec(v___x_76_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_121_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_81_; lean_object* v_traceState_82_; lean_object* v_env_83_; lean_object* v_nextMacroScope_84_; lean_object* v_ngen_85_; lean_object* v_auxDeclNGen_86_; lean_object* v_cache_87_; lean_object* v_messages_88_; lean_object* v_infoState_89_; lean_object* v_snapshotTasks_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_120_; 
v___x_81_ = lean_st_ref_take(v___y_73_);
v_traceState_82_ = lean_ctor_get(v___x_81_, 4);
v_env_83_ = lean_ctor_get(v___x_81_, 0);
v_nextMacroScope_84_ = lean_ctor_get(v___x_81_, 1);
v_ngen_85_ = lean_ctor_get(v___x_81_, 2);
v_auxDeclNGen_86_ = lean_ctor_get(v___x_81_, 3);
v_cache_87_ = lean_ctor_get(v___x_81_, 5);
v_messages_88_ = lean_ctor_get(v___x_81_, 6);
v_infoState_89_ = lean_ctor_get(v___x_81_, 7);
v_snapshotTasks_90_ = lean_ctor_get(v___x_81_, 8);
v_isSharedCheck_120_ = !lean_is_exclusive(v___x_81_);
if (v_isSharedCheck_120_ == 0)
{
v___x_92_ = v___x_81_;
v_isShared_93_ = v_isSharedCheck_120_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_snapshotTasks_90_);
lean_inc(v_infoState_89_);
lean_inc(v_messages_88_);
lean_inc(v_cache_87_);
lean_inc(v_traceState_82_);
lean_inc(v_auxDeclNGen_86_);
lean_inc(v_ngen_85_);
lean_inc(v_nextMacroScope_84_);
lean_inc(v_env_83_);
lean_dec(v___x_81_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_120_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
uint64_t v_tid_94_; lean_object* v_traces_95_; lean_object* v___x_97_; uint8_t v_isShared_98_; uint8_t v_isSharedCheck_119_; 
v_tid_94_ = lean_ctor_get_uint64(v_traceState_82_, sizeof(void*)*1);
v_traces_95_ = lean_ctor_get(v_traceState_82_, 0);
v_isSharedCheck_119_ = !lean_is_exclusive(v_traceState_82_);
if (v_isSharedCheck_119_ == 0)
{
v___x_97_ = v_traceState_82_;
v_isShared_98_ = v_isSharedCheck_119_;
goto v_resetjp_96_;
}
else
{
lean_inc(v_traces_95_);
lean_dec(v_traceState_82_);
v___x_97_ = lean_box(0);
v_isShared_98_ = v_isSharedCheck_119_;
goto v_resetjp_96_;
}
v_resetjp_96_:
{
lean_object* v___x_99_; double v___x_100_; uint8_t v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_109_; 
v___x_99_ = lean_box(0);
v___x_100_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0);
v___x_101_ = 0;
v___x_102_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__1));
v___x_103_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_103_, 0, v_cls_68_);
lean_ctor_set(v___x_103_, 1, v___x_99_);
lean_ctor_set(v___x_103_, 2, v___x_102_);
lean_ctor_set_float(v___x_103_, sizeof(void*)*3, v___x_100_);
lean_ctor_set_float(v___x_103_, sizeof(void*)*3 + 8, v___x_100_);
lean_ctor_set_uint8(v___x_103_, sizeof(void*)*3 + 16, v___x_101_);
v___x_104_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__2));
v___x_105_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_105_, 0, v___x_103_);
lean_ctor_set(v___x_105_, 1, v_a_77_);
lean_ctor_set(v___x_105_, 2, v___x_104_);
lean_inc(v_ref_75_);
v___x_106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_106_, 0, v_ref_75_);
lean_ctor_set(v___x_106_, 1, v___x_105_);
v___x_107_ = l_Lean_PersistentArray_push___redArg(v_traces_95_, v___x_106_);
if (v_isShared_98_ == 0)
{
lean_ctor_set(v___x_97_, 0, v___x_107_);
v___x_109_ = v___x_97_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v___x_107_);
lean_ctor_set_uint64(v_reuseFailAlloc_118_, sizeof(void*)*1, v_tid_94_);
v___x_109_ = v_reuseFailAlloc_118_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v___x_111_; 
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 4, v___x_109_);
v___x_111_ = v___x_92_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v_env_83_);
lean_ctor_set(v_reuseFailAlloc_117_, 1, v_nextMacroScope_84_);
lean_ctor_set(v_reuseFailAlloc_117_, 2, v_ngen_85_);
lean_ctor_set(v_reuseFailAlloc_117_, 3, v_auxDeclNGen_86_);
lean_ctor_set(v_reuseFailAlloc_117_, 4, v___x_109_);
lean_ctor_set(v_reuseFailAlloc_117_, 5, v_cache_87_);
lean_ctor_set(v_reuseFailAlloc_117_, 6, v_messages_88_);
lean_ctor_set(v_reuseFailAlloc_117_, 7, v_infoState_89_);
lean_ctor_set(v_reuseFailAlloc_117_, 8, v_snapshotTasks_90_);
v___x_111_ = v_reuseFailAlloc_117_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_115_; 
v___x_112_ = lean_st_ref_put(v___y_73_, v___x_111_);
v___x_113_ = lean_box(0);
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 0, v___x_113_);
v___x_115_ = v___x_79_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v___x_113_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___boxed(lean_object* v_cls_122_, lean_object* v_msg_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v_cls_122_, v_msg_123_, v___y_124_, v___y_125_, v___y_126_, v___y_127_);
lean_dec(v___y_127_);
lean_dec_ref(v___y_126_);
lean_dec(v___y_125_);
lean_dec_ref(v___y_124_);
return v_res_129_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7(void){
_start:
{
lean_object* v_cls_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v_cls_142_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4));
v___x_143_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
v___x_144_ = l_Lean_Name_append(v___x_143_, v_cls_142_);
return v___x_144_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9(void){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_146_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__8));
v___x_147_ = l_Lean_stringToMessageData(v___x_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(lean_object* v_a_148_, lean_object* v_x_149_, lean_object* v_c_u2081_150_, lean_object* v_b_151_, lean_object* v_c_u2082_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_){
_start:
{
lean_object* v_options_164_; lean_object* v_p_165_; lean_object* v_d_166_; lean_object* v_p_167_; lean_object* v_inheritedTraceOptions_168_; uint8_t v_hasTrace_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v_d_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v_p_176_; 
v_options_164_ = lean_ctor_get(v_a_161_, 2);
v_p_165_ = lean_ctor_get(v_c_u2081_150_, 0);
v_d_166_ = lean_ctor_get(v_c_u2082_152_, 0);
v_p_167_ = lean_ctor_get(v_c_u2082_152_, 1);
v_inheritedTraceOptions_168_ = lean_ctor_get(v_a_161_, 13);
v_hasTrace_169_ = lean_ctor_get_uint8(v_options_164_, sizeof(void*)*1);
v___x_170_ = lean_int_mul(v_a_148_, v_d_166_);
v___x_171_ = lean_nat_abs(v___x_170_);
lean_dec(v___x_170_);
v_d_172_ = lean_nat_to_int(v___x_171_);
lean_inc_ref(v_p_167_);
v___x_173_ = l_Int_Internal_Linear_Poly_mul(v_p_167_, v_a_148_);
v___x_174_ = lean_int_neg(v_b_151_);
lean_inc_ref(v_p_165_);
v___x_175_ = l_Int_Internal_Linear_Poly_mul(v_p_165_, v___x_174_);
lean_dec(v___x_174_);
v_p_176_ = l_Int_Internal_Linear_Poly_combine(v___x_173_, v___x_175_);
if (v_hasTrace_169_ == 0)
{
goto v___jp_177_;
}
else
{
lean_object* v_cls_181_; lean_object* v___x_182_; uint8_t v___x_183_; 
v_cls_181_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4));
v___x_182_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7);
v___x_183_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_168_, v_options_164_, v___x_182_);
if (v___x_183_ == 0)
{
goto v___jp_177_;
}
else
{
lean_object* v___x_184_; 
v___x_184_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_x_149_, v_a_153_, v_a_161_);
if (lean_obj_tag(v___x_184_) == 0)
{
lean_object* v_a_185_; lean_object* v___x_186_; 
v_a_185_ = lean_ctor_get(v___x_184_, 0);
lean_inc(v_a_185_);
lean_dec_ref_known(v___x_184_, 1);
lean_inc_ref(v_c_u2081_150_);
v___x_186_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_u2081_150_, v_a_153_, v_a_161_);
if (lean_obj_tag(v___x_186_) == 0)
{
lean_object* v_a_187_; lean_object* v___x_188_; 
v_a_187_ = lean_ctor_get(v___x_186_, 0);
lean_inc(v_a_187_);
lean_dec_ref_known(v___x_186_, 1);
lean_inc_ref(v_c_u2082_152_);
v___x_188_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_u2082_152_, v_a_153_, v_a_161_);
if (lean_obj_tag(v___x_188_) == 0)
{
lean_object* v_a_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v_a_189_ = lean_ctor_get(v___x_188_, 0);
lean_inc(v_a_189_);
lean_dec_ref_known(v___x_188_, 1);
v___x_190_ = l_Lean_MessageData_ofExpr(v_a_185_);
v___x_191_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9);
v___x_192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_190_);
lean_ctor_set(v___x_192_, 1, v___x_191_);
v___x_193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_193_, 0, v___x_192_);
lean_ctor_set(v___x_193_, 1, v_a_187_);
v___x_194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
lean_ctor_set(v___x_194_, 1, v___x_191_);
v___x_195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set(v___x_195_, 1, v_a_189_);
v___x_196_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v_cls_181_, v___x_195_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
if (lean_obj_tag(v___x_196_) == 0)
{
lean_dec_ref_known(v___x_196_, 1);
goto v___jp_177_;
}
else
{
lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_204_; 
lean_dec_ref(v_p_176_);
lean_dec(v_d_172_);
lean_dec_ref(v_c_u2082_152_);
lean_dec_ref(v_c_u2081_150_);
lean_dec(v_x_149_);
v_a_197_ = lean_ctor_get(v___x_196_, 0);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_196_);
if (v_isSharedCheck_204_ == 0)
{
v___x_199_ = v___x_196_;
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_dec(v___x_196_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_202_; 
if (v_isShared_200_ == 0)
{
v___x_202_ = v___x_199_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_a_197_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
else
{
lean_object* v_a_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_212_; 
lean_dec(v_a_187_);
lean_dec(v_a_185_);
lean_dec_ref(v_p_176_);
lean_dec(v_d_172_);
lean_dec_ref(v_c_u2082_152_);
lean_dec_ref(v_c_u2081_150_);
lean_dec(v_x_149_);
v_a_205_ = lean_ctor_get(v___x_188_, 0);
v_isSharedCheck_212_ = !lean_is_exclusive(v___x_188_);
if (v_isSharedCheck_212_ == 0)
{
v___x_207_ = v___x_188_;
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_a_205_);
lean_dec(v___x_188_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_212_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_210_; 
if (v_isShared_208_ == 0)
{
v___x_210_ = v___x_207_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v_a_205_);
v___x_210_ = v_reuseFailAlloc_211_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
return v___x_210_;
}
}
}
}
else
{
lean_object* v_a_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_220_; 
lean_dec(v_a_185_);
lean_dec_ref(v_p_176_);
lean_dec(v_d_172_);
lean_dec_ref(v_c_u2082_152_);
lean_dec_ref(v_c_u2081_150_);
lean_dec(v_x_149_);
v_a_213_ = lean_ctor_get(v___x_186_, 0);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_186_);
if (v_isSharedCheck_220_ == 0)
{
v___x_215_ = v___x_186_;
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_a_213_);
lean_dec(v___x_186_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_220_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___x_218_; 
if (v_isShared_216_ == 0)
{
v___x_218_ = v___x_215_;
goto v_reusejp_217_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_a_213_);
v___x_218_ = v_reuseFailAlloc_219_;
goto v_reusejp_217_;
}
v_reusejp_217_:
{
return v___x_218_;
}
}
}
}
else
{
lean_object* v_a_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_228_; 
lean_dec_ref(v_p_176_);
lean_dec(v_d_172_);
lean_dec_ref(v_c_u2082_152_);
lean_dec_ref(v_c_u2081_150_);
lean_dec(v_x_149_);
v_a_221_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_228_ == 0)
{
v___x_223_ = v___x_184_;
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_a_221_);
lean_dec(v___x_184_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_228_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_226_; 
if (v_isShared_224_ == 0)
{
v___x_226_ = v___x_223_;
goto v_reusejp_225_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_a_221_);
v___x_226_ = v_reuseFailAlloc_227_;
goto v_reusejp_225_;
}
v_reusejp_225_:
{
return v___x_226_;
}
}
}
}
}
v___jp_177_:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_178_ = lean_alloc_ctor(8, 3, 0);
lean_ctor_set(v___x_178_, 0, v_x_149_);
lean_ctor_set(v___x_178_, 1, v_c_u2081_150_);
lean_ctor_set(v___x_178_, 2, v_c_u2082_152_);
v___x_179_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_179_, 0, v_d_172_);
lean_ctor_set(v___x_179_, 1, v_p_176_);
lean_ctor_set(v___x_179_, 2, v___x_178_);
v___x_180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
return v___x_180_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___boxed(lean_object* v_a_229_, lean_object* v_x_230_, lean_object* v_c_u2081_231_, lean_object* v_b_232_, lean_object* v_c_u2082_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(v_a_229_, v_x_230_, v_c_u2081_231_, v_b_232_, v_c_u2082_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_);
lean_dec(v_a_243_);
lean_dec_ref(v_a_242_);
lean_dec(v_a_241_);
lean_dec_ref(v_a_240_);
lean_dec(v_a_239_);
lean_dec_ref(v_a_238_);
lean_dec(v_a_237_);
lean_dec_ref(v_a_236_);
lean_dec(v_a_235_);
lean_dec(v_a_234_);
lean_dec(v_b_232_);
lean_dec(v_a_229_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0(lean_object* v_cls_246_, lean_object* v_msg_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_){
_start:
{
lean_object* v___x_259_; 
v___x_259_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v_cls_246_, v_msg_247_, v___y_254_, v___y_255_, v___y_256_, v___y_257_);
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___boxed(lean_object* v_cls_260_, lean_object* v_msg_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0(v_cls_260_, v_msg_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_);
lean_dec(v___y_271_);
lean_dec_ref(v___y_270_);
lean_dec(v___y_269_);
lean_dec_ref(v___y_268_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec(v___y_263_);
lean_dec(v___y_262_);
return v_res_273_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = l_Lean_maxRecDepthErrorMessage;
v___x_280_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_280_, 0, v___x_279_);
return v___x_280_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3);
v___x_282_ = l_Lean_MessageData_ofFormat(v___x_281_);
return v___x_282_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_283_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4);
v___x_284_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2));
v___x_285_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_285_, 0, v___x_284_);
lean_ctor_set(v___x_285_, 1, v___x_283_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(lean_object* v_ref_286_){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_288_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5);
v___x_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_289_, 0, v_ref_286_);
lean_ctor_set(v___x_289_, 1, v___x_288_);
v___x_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_290_, 0, v___x_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___boxed(lean_object* v_ref_291_, lean_object* v___y_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_291_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0(lean_object* v_00_u03b1_294_, lean_object* v_ref_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_295_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___boxed(lean_object* v_00_u03b1_308_, lean_object* v_ref_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_){
_start:
{
lean_object* v_res_321_; 
v_res_321_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0(v_00_u03b1_308_, v_ref_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
lean_dec(v___y_317_);
lean_dec_ref(v___y_316_);
lean_dec(v___y_315_);
lean_dec_ref(v___y_314_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
lean_dec(v___y_311_);
lean_dec(v___y_310_);
return v_res_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(lean_object* v_c_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_){
_start:
{
lean_object* v_p_334_; lean_object* v_fileName_335_; lean_object* v_fileMap_336_; lean_object* v_options_337_; lean_object* v_currRecDepth_338_; lean_object* v_maxRecDepth_339_; lean_object* v_ref_340_; lean_object* v_currNamespace_341_; lean_object* v_openDecls_342_; lean_object* v_initHeartbeats_343_; lean_object* v_maxHeartbeats_344_; lean_object* v_quotContext_345_; lean_object* v_currMacroScope_346_; uint8_t v_diag_347_; lean_object* v_cancelTk_x3f_348_; uint8_t v_suppressElabErrors_349_; lean_object* v_inheritedTraceOptions_350_; lean_object* v___x_382_; uint8_t v___x_383_; 
v_p_334_ = lean_ctor_get(v_c_322_, 1);
v_fileName_335_ = lean_ctor_get(v_a_331_, 0);
lean_inc_ref(v_fileName_335_);
v_fileMap_336_ = lean_ctor_get(v_a_331_, 1);
lean_inc_ref(v_fileMap_336_);
v_options_337_ = lean_ctor_get(v_a_331_, 2);
lean_inc_ref(v_options_337_);
v_currRecDepth_338_ = lean_ctor_get(v_a_331_, 3);
lean_inc(v_currRecDepth_338_);
v_maxRecDepth_339_ = lean_ctor_get(v_a_331_, 4);
lean_inc(v_maxRecDepth_339_);
v_ref_340_ = lean_ctor_get(v_a_331_, 5);
lean_inc(v_ref_340_);
v_currNamespace_341_ = lean_ctor_get(v_a_331_, 6);
lean_inc(v_currNamespace_341_);
v_openDecls_342_ = lean_ctor_get(v_a_331_, 7);
lean_inc(v_openDecls_342_);
v_initHeartbeats_343_ = lean_ctor_get(v_a_331_, 8);
lean_inc(v_initHeartbeats_343_);
v_maxHeartbeats_344_ = lean_ctor_get(v_a_331_, 9);
lean_inc(v_maxHeartbeats_344_);
v_quotContext_345_ = lean_ctor_get(v_a_331_, 10);
lean_inc(v_quotContext_345_);
v_currMacroScope_346_ = lean_ctor_get(v_a_331_, 11);
lean_inc(v_currMacroScope_346_);
v_diag_347_ = lean_ctor_get_uint8(v_a_331_, sizeof(void*)*14);
v_cancelTk_x3f_348_ = lean_ctor_get(v_a_331_, 12);
lean_inc(v_cancelTk_x3f_348_);
v_suppressElabErrors_349_ = lean_ctor_get_uint8(v_a_331_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_350_ = lean_ctor_get(v_a_331_, 13);
lean_inc_ref(v_inheritedTraceOptions_350_);
lean_dec_ref(v_a_331_);
v___x_382_ = lean_unsigned_to_nat(0u);
v___x_383_ = lean_nat_dec_eq(v_maxRecDepth_339_, v___x_382_);
if (v___x_383_ == 0)
{
uint8_t v___x_384_; 
v___x_384_ = lean_nat_dec_eq(v_currRecDepth_338_, v_maxRecDepth_339_);
if (v___x_384_ == 0)
{
goto v___jp_351_;
}
else
{
lean_object* v___x_385_; 
lean_dec_ref(v_inheritedTraceOptions_350_);
lean_dec(v_cancelTk_x3f_348_);
lean_dec(v_currMacroScope_346_);
lean_dec(v_quotContext_345_);
lean_dec(v_maxHeartbeats_344_);
lean_dec(v_initHeartbeats_343_);
lean_dec(v_openDecls_342_);
lean_dec(v_currNamespace_341_);
lean_dec(v_maxRecDepth_339_);
lean_dec(v_currRecDepth_338_);
lean_dec_ref(v_options_337_);
lean_dec_ref(v_fileMap_336_);
lean_dec_ref(v_fileName_335_);
lean_dec_ref(v_c_322_);
v___x_385_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_340_);
return v___x_385_;
}
}
else
{
goto v___jp_351_;
}
v___jp_351_:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_352_ = lean_unsigned_to_nat(1u);
v___x_353_ = lean_nat_add(v_currRecDepth_338_, v___x_352_);
lean_dec(v_currRecDepth_338_);
v___x_354_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_354_, 0, v_fileName_335_);
lean_ctor_set(v___x_354_, 1, v_fileMap_336_);
lean_ctor_set(v___x_354_, 2, v_options_337_);
lean_ctor_set(v___x_354_, 3, v___x_353_);
lean_ctor_set(v___x_354_, 4, v_maxRecDepth_339_);
lean_ctor_set(v___x_354_, 5, v_ref_340_);
lean_ctor_set(v___x_354_, 6, v_currNamespace_341_);
lean_ctor_set(v___x_354_, 7, v_openDecls_342_);
lean_ctor_set(v___x_354_, 8, v_initHeartbeats_343_);
lean_ctor_set(v___x_354_, 9, v_maxHeartbeats_344_);
lean_ctor_set(v___x_354_, 10, v_quotContext_345_);
lean_ctor_set(v___x_354_, 11, v_currMacroScope_346_);
lean_ctor_set(v___x_354_, 12, v_cancelTk_x3f_348_);
lean_ctor_set(v___x_354_, 13, v_inheritedTraceOptions_350_);
lean_ctor_set_uint8(v___x_354_, sizeof(void*)*14, v_diag_347_);
lean_ctor_set_uint8(v___x_354_, sizeof(void*)*14 + 1, v_suppressElabErrors_349_);
lean_inc_ref(v_p_334_);
v___x_355_ = l_Int_Internal_Linear_Poly_findVarToSubst___redArg(v_p_334_, v_a_323_, v___x_354_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_373_; 
v_a_356_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_373_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_373_ == 0)
{
v___x_358_ = v___x_355_;
v_isShared_359_ = v_isSharedCheck_373_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_355_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_373_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
if (lean_obj_tag(v_a_356_) == 1)
{
lean_object* v_val_360_; lean_object* v_snd_361_; lean_object* v_snd_362_; lean_object* v_fst_363_; lean_object* v_fst_364_; lean_object* v_p_365_; lean_object* v___x_366_; lean_object* v___x_367_; 
lean_del_object(v___x_358_);
v_val_360_ = lean_ctor_get(v_a_356_, 0);
lean_inc(v_val_360_);
lean_dec_ref_known(v_a_356_, 1);
v_snd_361_ = lean_ctor_get(v_val_360_, 1);
lean_inc(v_snd_361_);
v_snd_362_ = lean_ctor_get(v_snd_361_, 1);
lean_inc(v_snd_362_);
v_fst_363_ = lean_ctor_get(v_val_360_, 0);
lean_inc(v_fst_363_);
lean_dec(v_val_360_);
v_fst_364_ = lean_ctor_get(v_snd_361_, 0);
lean_inc(v_fst_364_);
lean_dec(v_snd_361_);
v_p_365_ = lean_ctor_get(v_snd_362_, 0);
v___x_366_ = l_Int_Internal_Linear_Poly_coeff(v_p_365_, v_fst_364_);
v___x_367_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(v___x_366_, v_fst_364_, v_snd_362_, v_fst_363_, v_c_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v___x_354_, v_a_332_);
lean_dec(v_fst_363_);
lean_dec(v___x_366_);
if (lean_obj_tag(v___x_367_) == 0)
{
lean_object* v_a_368_; 
v_a_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_a_368_);
lean_dec_ref_known(v___x_367_, 1);
v_c_322_ = v_a_368_;
v_a_331_ = v___x_354_;
goto _start;
}
else
{
lean_dec_ref_known(v___x_354_, 14);
return v___x_367_;
}
}
else
{
lean_object* v___x_371_; 
lean_dec(v_a_356_);
lean_dec_ref_known(v___x_354_, 14);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 0, v_c_322_);
v___x_371_ = v___x_358_;
goto v_reusejp_370_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_c_322_);
v___x_371_ = v_reuseFailAlloc_372_;
goto v_reusejp_370_;
}
v_reusejp_370_:
{
return v___x_371_;
}
}
}
}
else
{
lean_object* v_a_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_381_; 
lean_dec_ref_known(v___x_354_, 14);
lean_dec_ref(v_c_322_);
v_a_374_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_381_ == 0)
{
v___x_376_ = v___x_355_;
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_a_374_);
lean_dec(v___x_355_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_381_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_a_374_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___boxed(lean_object* v_c_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(v_c_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_);
lean_dec(v_a_396_);
lean_dec(v_a_394_);
lean_dec_ref(v_a_393_);
lean_dec(v_a_392_);
lean_dec_ref(v_a_391_);
lean_dec(v_a_390_);
lean_dec_ref(v_a_389_);
lean_dec(v_a_388_);
lean_dec(v_a_387_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(lean_object* v_a_399_, lean_object* v_v_400_, lean_object* v_s_401_){
_start:
{
lean_object* v_vars_402_; lean_object* v_varMap_403_; lean_object* v_vars_x27_404_; lean_object* v_varMap_x27_405_; lean_object* v_natToIntMap_406_; lean_object* v_natDef_407_; lean_object* v_dvds_408_; lean_object* v_lowers_409_; lean_object* v_uppers_410_; lean_object* v_diseqs_411_; lean_object* v_elimEqs_412_; lean_object* v_elimStack_413_; lean_object* v_occurs_414_; lean_object* v_assignment_415_; lean_object* v_nextCnstrId_416_; uint8_t v_caseSplits_417_; lean_object* v_steps_418_; lean_object* v_conflict_x3f_419_; lean_object* v_diseqSplits_420_; lean_object* v_divMod_421_; uint8_t v_usedCommRing_422_; lean_object* v_nonlinearOccs_423_; lean_object* v___x_425_; uint8_t v_isShared_426_; uint8_t v_isSharedCheck_432_; 
v_vars_402_ = lean_ctor_get(v_s_401_, 0);
v_varMap_403_ = lean_ctor_get(v_s_401_, 1);
v_vars_x27_404_ = lean_ctor_get(v_s_401_, 2);
v_varMap_x27_405_ = lean_ctor_get(v_s_401_, 3);
v_natToIntMap_406_ = lean_ctor_get(v_s_401_, 4);
v_natDef_407_ = lean_ctor_get(v_s_401_, 5);
v_dvds_408_ = lean_ctor_get(v_s_401_, 6);
v_lowers_409_ = lean_ctor_get(v_s_401_, 7);
v_uppers_410_ = lean_ctor_get(v_s_401_, 8);
v_diseqs_411_ = lean_ctor_get(v_s_401_, 9);
v_elimEqs_412_ = lean_ctor_get(v_s_401_, 10);
v_elimStack_413_ = lean_ctor_get(v_s_401_, 11);
v_occurs_414_ = lean_ctor_get(v_s_401_, 12);
v_assignment_415_ = lean_ctor_get(v_s_401_, 13);
v_nextCnstrId_416_ = lean_ctor_get(v_s_401_, 14);
v_caseSplits_417_ = lean_ctor_get_uint8(v_s_401_, sizeof(void*)*20);
v_steps_418_ = lean_ctor_get(v_s_401_, 15);
v_conflict_x3f_419_ = lean_ctor_get(v_s_401_, 16);
v_diseqSplits_420_ = lean_ctor_get(v_s_401_, 17);
v_divMod_421_ = lean_ctor_get(v_s_401_, 18);
v_usedCommRing_422_ = lean_ctor_get_uint8(v_s_401_, sizeof(void*)*20 + 1);
v_nonlinearOccs_423_ = lean_ctor_get(v_s_401_, 19);
v_isSharedCheck_432_ = !lean_is_exclusive(v_s_401_);
if (v_isSharedCheck_432_ == 0)
{
v___x_425_ = v_s_401_;
v_isShared_426_ = v_isSharedCheck_432_;
goto v_resetjp_424_;
}
else
{
lean_inc(v_nonlinearOccs_423_);
lean_inc(v_divMod_421_);
lean_inc(v_diseqSplits_420_);
lean_inc(v_conflict_x3f_419_);
lean_inc(v_steps_418_);
lean_inc(v_nextCnstrId_416_);
lean_inc(v_assignment_415_);
lean_inc(v_occurs_414_);
lean_inc(v_elimStack_413_);
lean_inc(v_elimEqs_412_);
lean_inc(v_diseqs_411_);
lean_inc(v_uppers_410_);
lean_inc(v_lowers_409_);
lean_inc(v_dvds_408_);
lean_inc(v_natDef_407_);
lean_inc(v_natToIntMap_406_);
lean_inc(v_varMap_x27_405_);
lean_inc(v_vars_x27_404_);
lean_inc(v_varMap_403_);
lean_inc(v_vars_402_);
lean_dec(v_s_401_);
v___x_425_ = lean_box(0);
v_isShared_426_ = v_isSharedCheck_432_;
goto v_resetjp_424_;
}
v_resetjp_424_:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_430_; 
v___x_427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_427_, 0, v_a_399_);
v___x_428_ = l_Lean_PersistentArray_set___redArg(v_dvds_408_, v_v_400_, v___x_427_);
if (v_isShared_426_ == 0)
{
lean_ctor_set(v___x_425_, 6, v___x_428_);
v___x_430_ = v___x_425_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 20, 2);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_vars_402_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v_varMap_403_);
lean_ctor_set(v_reuseFailAlloc_431_, 2, v_vars_x27_404_);
lean_ctor_set(v_reuseFailAlloc_431_, 3, v_varMap_x27_405_);
lean_ctor_set(v_reuseFailAlloc_431_, 4, v_natToIntMap_406_);
lean_ctor_set(v_reuseFailAlloc_431_, 5, v_natDef_407_);
lean_ctor_set(v_reuseFailAlloc_431_, 6, v___x_428_);
lean_ctor_set(v_reuseFailAlloc_431_, 7, v_lowers_409_);
lean_ctor_set(v_reuseFailAlloc_431_, 8, v_uppers_410_);
lean_ctor_set(v_reuseFailAlloc_431_, 9, v_diseqs_411_);
lean_ctor_set(v_reuseFailAlloc_431_, 10, v_elimEqs_412_);
lean_ctor_set(v_reuseFailAlloc_431_, 11, v_elimStack_413_);
lean_ctor_set(v_reuseFailAlloc_431_, 12, v_occurs_414_);
lean_ctor_set(v_reuseFailAlloc_431_, 13, v_assignment_415_);
lean_ctor_set(v_reuseFailAlloc_431_, 14, v_nextCnstrId_416_);
lean_ctor_set(v_reuseFailAlloc_431_, 15, v_steps_418_);
lean_ctor_set(v_reuseFailAlloc_431_, 16, v_conflict_x3f_419_);
lean_ctor_set(v_reuseFailAlloc_431_, 17, v_diseqSplits_420_);
lean_ctor_set(v_reuseFailAlloc_431_, 18, v_divMod_421_);
lean_ctor_set(v_reuseFailAlloc_431_, 19, v_nonlinearOccs_423_);
lean_ctor_set_uint8(v_reuseFailAlloc_431_, sizeof(void*)*20, v_caseSplits_417_);
lean_ctor_set_uint8(v_reuseFailAlloc_431_, sizeof(void*)*20 + 1, v_usedCommRing_422_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed(lean_object* v_a_433_, lean_object* v_v_434_, lean_object* v_s_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(v_a_433_, v_v_434_, v_s_435_);
lean_dec(v_v_434_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(lean_object* v_v_437_, lean_object* v_s_438_){
_start:
{
lean_object* v_vars_439_; lean_object* v_varMap_440_; lean_object* v_vars_x27_441_; lean_object* v_varMap_x27_442_; lean_object* v_natToIntMap_443_; lean_object* v_natDef_444_; lean_object* v_dvds_445_; lean_object* v_lowers_446_; lean_object* v_uppers_447_; lean_object* v_diseqs_448_; lean_object* v_elimEqs_449_; lean_object* v_elimStack_450_; lean_object* v_occurs_451_; lean_object* v_assignment_452_; lean_object* v_nextCnstrId_453_; uint8_t v_caseSplits_454_; lean_object* v_steps_455_; lean_object* v_conflict_x3f_456_; lean_object* v_diseqSplits_457_; lean_object* v_divMod_458_; uint8_t v_usedCommRing_459_; lean_object* v_nonlinearOccs_460_; lean_object* v___x_462_; uint8_t v_isShared_463_; uint8_t v_isSharedCheck_469_; 
v_vars_439_ = lean_ctor_get(v_s_438_, 0);
v_varMap_440_ = lean_ctor_get(v_s_438_, 1);
v_vars_x27_441_ = lean_ctor_get(v_s_438_, 2);
v_varMap_x27_442_ = lean_ctor_get(v_s_438_, 3);
v_natToIntMap_443_ = lean_ctor_get(v_s_438_, 4);
v_natDef_444_ = lean_ctor_get(v_s_438_, 5);
v_dvds_445_ = lean_ctor_get(v_s_438_, 6);
v_lowers_446_ = lean_ctor_get(v_s_438_, 7);
v_uppers_447_ = lean_ctor_get(v_s_438_, 8);
v_diseqs_448_ = lean_ctor_get(v_s_438_, 9);
v_elimEqs_449_ = lean_ctor_get(v_s_438_, 10);
v_elimStack_450_ = lean_ctor_get(v_s_438_, 11);
v_occurs_451_ = lean_ctor_get(v_s_438_, 12);
v_assignment_452_ = lean_ctor_get(v_s_438_, 13);
v_nextCnstrId_453_ = lean_ctor_get(v_s_438_, 14);
v_caseSplits_454_ = lean_ctor_get_uint8(v_s_438_, sizeof(void*)*20);
v_steps_455_ = lean_ctor_get(v_s_438_, 15);
v_conflict_x3f_456_ = lean_ctor_get(v_s_438_, 16);
v_diseqSplits_457_ = lean_ctor_get(v_s_438_, 17);
v_divMod_458_ = lean_ctor_get(v_s_438_, 18);
v_usedCommRing_459_ = lean_ctor_get_uint8(v_s_438_, sizeof(void*)*20 + 1);
v_nonlinearOccs_460_ = lean_ctor_get(v_s_438_, 19);
v_isSharedCheck_469_ = !lean_is_exclusive(v_s_438_);
if (v_isSharedCheck_469_ == 0)
{
v___x_462_ = v_s_438_;
v_isShared_463_ = v_isSharedCheck_469_;
goto v_resetjp_461_;
}
else
{
lean_inc(v_nonlinearOccs_460_);
lean_inc(v_divMod_458_);
lean_inc(v_diseqSplits_457_);
lean_inc(v_conflict_x3f_456_);
lean_inc(v_steps_455_);
lean_inc(v_nextCnstrId_453_);
lean_inc(v_assignment_452_);
lean_inc(v_occurs_451_);
lean_inc(v_elimStack_450_);
lean_inc(v_elimEqs_449_);
lean_inc(v_diseqs_448_);
lean_inc(v_uppers_447_);
lean_inc(v_lowers_446_);
lean_inc(v_dvds_445_);
lean_inc(v_natDef_444_);
lean_inc(v_natToIntMap_443_);
lean_inc(v_varMap_x27_442_);
lean_inc(v_vars_x27_441_);
lean_inc(v_varMap_440_);
lean_inc(v_vars_439_);
lean_dec(v_s_438_);
v___x_462_ = lean_box(0);
v_isShared_463_ = v_isSharedCheck_469_;
goto v_resetjp_461_;
}
v_resetjp_461_:
{
lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_467_; 
v___x_464_ = lean_box(0);
v___x_465_ = l_Lean_PersistentArray_set___redArg(v_dvds_445_, v_v_437_, v___x_464_);
if (v_isShared_463_ == 0)
{
lean_ctor_set(v___x_462_, 6, v___x_465_);
v___x_467_ = v___x_462_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 20, 2);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_vars_439_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v_varMap_440_);
lean_ctor_set(v_reuseFailAlloc_468_, 2, v_vars_x27_441_);
lean_ctor_set(v_reuseFailAlloc_468_, 3, v_varMap_x27_442_);
lean_ctor_set(v_reuseFailAlloc_468_, 4, v_natToIntMap_443_);
lean_ctor_set(v_reuseFailAlloc_468_, 5, v_natDef_444_);
lean_ctor_set(v_reuseFailAlloc_468_, 6, v___x_465_);
lean_ctor_set(v_reuseFailAlloc_468_, 7, v_lowers_446_);
lean_ctor_set(v_reuseFailAlloc_468_, 8, v_uppers_447_);
lean_ctor_set(v_reuseFailAlloc_468_, 9, v_diseqs_448_);
lean_ctor_set(v_reuseFailAlloc_468_, 10, v_elimEqs_449_);
lean_ctor_set(v_reuseFailAlloc_468_, 11, v_elimStack_450_);
lean_ctor_set(v_reuseFailAlloc_468_, 12, v_occurs_451_);
lean_ctor_set(v_reuseFailAlloc_468_, 13, v_assignment_452_);
lean_ctor_set(v_reuseFailAlloc_468_, 14, v_nextCnstrId_453_);
lean_ctor_set(v_reuseFailAlloc_468_, 15, v_steps_455_);
lean_ctor_set(v_reuseFailAlloc_468_, 16, v_conflict_x3f_456_);
lean_ctor_set(v_reuseFailAlloc_468_, 17, v_diseqSplits_457_);
lean_ctor_set(v_reuseFailAlloc_468_, 18, v_divMod_458_);
lean_ctor_set(v_reuseFailAlloc_468_, 19, v_nonlinearOccs_460_);
lean_ctor_set_uint8(v_reuseFailAlloc_468_, sizeof(void*)*20, v_caseSplits_454_);
lean_ctor_set_uint8(v_reuseFailAlloc_468_, sizeof(void*)*20 + 1, v_usedCommRing_459_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
return v___x_467_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed(lean_object* v_v_470_, lean_object* v_s_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(v_v_470_, v_s_471_);
lean_dec(v_v_470_);
return v_res_472_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_481_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4));
v___x_482_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
v___x_483_ = l_Lean_Name_append(v___x_482_, v___x_481_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(lean_object* v_c_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_, lean_object* v_a_490_, lean_object* v_a_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_){
_start:
{
lean_object* v___y_500_; lean_object* v___y_501_; lean_object* v___y_502_; lean_object* v___y_503_; lean_object* v___y_504_; lean_object* v___y_505_; lean_object* v___y_506_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___y_527_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___y_613_; lean_object* v___y_614_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___y_617_; lean_object* v___y_618_; lean_object* v___y_619_; lean_object* v___y_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v_fileName_774_; lean_object* v_fileMap_775_; lean_object* v_options_776_; lean_object* v_currRecDepth_777_; lean_object* v_maxRecDepth_778_; lean_object* v_ref_779_; lean_object* v_currNamespace_780_; lean_object* v_openDecls_781_; lean_object* v_initHeartbeats_782_; lean_object* v_maxHeartbeats_783_; lean_object* v_quotContext_784_; lean_object* v_currMacroScope_785_; uint8_t v_diag_786_; lean_object* v_cancelTk_x3f_787_; uint8_t v_suppressElabErrors_788_; lean_object* v_inheritedTraceOptions_789_; lean_object* v___x_831_; uint8_t v___x_832_; 
v_fileName_774_ = lean_ctor_get(v_a_493_, 0);
lean_inc_ref(v_fileName_774_);
v_fileMap_775_ = lean_ctor_get(v_a_493_, 1);
lean_inc_ref(v_fileMap_775_);
v_options_776_ = lean_ctor_get(v_a_493_, 2);
lean_inc_ref(v_options_776_);
v_currRecDepth_777_ = lean_ctor_get(v_a_493_, 3);
lean_inc(v_currRecDepth_777_);
v_maxRecDepth_778_ = lean_ctor_get(v_a_493_, 4);
lean_inc(v_maxRecDepth_778_);
v_ref_779_ = lean_ctor_get(v_a_493_, 5);
lean_inc(v_ref_779_);
v_currNamespace_780_ = lean_ctor_get(v_a_493_, 6);
lean_inc(v_currNamespace_780_);
v_openDecls_781_ = lean_ctor_get(v_a_493_, 7);
lean_inc(v_openDecls_781_);
v_initHeartbeats_782_ = lean_ctor_get(v_a_493_, 8);
lean_inc(v_initHeartbeats_782_);
v_maxHeartbeats_783_ = lean_ctor_get(v_a_493_, 9);
lean_inc(v_maxHeartbeats_783_);
v_quotContext_784_ = lean_ctor_get(v_a_493_, 10);
lean_inc(v_quotContext_784_);
v_currMacroScope_785_ = lean_ctor_get(v_a_493_, 11);
lean_inc(v_currMacroScope_785_);
v_diag_786_ = lean_ctor_get_uint8(v_a_493_, sizeof(void*)*14);
v_cancelTk_x3f_787_ = lean_ctor_get(v_a_493_, 12);
lean_inc(v_cancelTk_x3f_787_);
v_suppressElabErrors_788_ = lean_ctor_get_uint8(v_a_493_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_789_ = lean_ctor_get(v_a_493_, 13);
lean_inc_ref(v_inheritedTraceOptions_789_);
lean_dec_ref(v_a_493_);
v___x_831_ = lean_unsigned_to_nat(0u);
v___x_832_ = lean_nat_dec_eq(v_maxRecDepth_778_, v___x_831_);
if (v___x_832_ == 0)
{
uint8_t v___x_833_; 
v___x_833_ = lean_nat_dec_eq(v_currRecDepth_777_, v_maxRecDepth_778_);
if (v___x_833_ == 0)
{
goto v___jp_790_;
}
else
{
lean_object* v___x_834_; 
lean_dec_ref(v_inheritedTraceOptions_789_);
lean_dec(v_cancelTk_x3f_787_);
lean_dec(v_currMacroScope_785_);
lean_dec(v_quotContext_784_);
lean_dec(v_maxHeartbeats_783_);
lean_dec(v_initHeartbeats_782_);
lean_dec(v_openDecls_781_);
lean_dec(v_currNamespace_780_);
lean_dec(v_maxRecDepth_778_);
lean_dec(v_currRecDepth_777_);
lean_dec_ref(v_options_776_);
lean_dec_ref(v_fileMap_775_);
lean_dec_ref(v_fileName_774_);
lean_dec_ref(v_c_484_);
v___x_834_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_779_);
return v___x_834_;
}
}
else
{
goto v___jp_790_;
}
v___jp_496_:
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = lean_box(0);
v___x_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_498_, 0, v___x_497_);
return v___x_498_;
}
v___jp_499_:
{
lean_object* v___x_507_; 
v___x_507_ = l_Int_Internal_Linear_Poly_updateOccs___redArg(v___y_500_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_);
lean_dec_ref(v___y_505_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v___x_508_; lean_object* v___x_509_; 
lean_dec_ref_known(v___x_507_, 1);
v___x_508_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_509_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_508_, v___y_501_, v___y_502_);
return v___x_509_;
}
else
{
lean_dec_ref(v___y_501_);
return v___x_507_;
}
}
v___jp_510_:
{
if (lean_obj_tag(v___y_532_) == 1)
{
lean_object* v_val_533_; lean_object* v_p_534_; 
lean_dec_ref(v___y_517_);
lean_dec_ref(v___y_515_);
v_val_533_ = lean_ctor_get(v___y_532_, 0);
lean_inc(v_val_533_);
lean_dec_ref_known(v___y_532_, 1);
v_p_534_ = lean_ctor_get(v_val_533_, 1);
lean_inc_ref(v_p_534_);
if (lean_obj_tag(v_p_534_) == 1)
{
lean_object* v_d_535_; lean_object* v_k_536_; lean_object* v_p_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_590_; 
v_d_535_ = lean_ctor_get(v_val_533_, 0);
v_k_536_ = lean_ctor_get(v_p_534_, 0);
v_p_537_ = lean_ctor_get(v_p_534_, 2);
v_isSharedCheck_590_ = !lean_is_exclusive(v_p_534_);
if (v_isSharedCheck_590_ == 0)
{
lean_object* v_unused_591_; 
v_unused_591_ = lean_ctor_get(v_p_534_, 1);
lean_dec(v_unused_591_);
v___x_539_ = v_p_534_;
v_isShared_540_ = v_isSharedCheck_590_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_p_537_);
lean_inc(v_k_536_);
lean_dec(v_p_534_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_590_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v_snd_544_; lean_object* v_fst_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_589_; 
v___x_541_ = lean_int_mul(v___y_524_, v_d_535_);
v___x_542_ = lean_int_mul(v_k_536_, v___y_526_);
v___x_543_ = l_Lean_Meta_Grind_Arith_gcdExt(v___x_541_, v___x_542_);
lean_dec(v___x_542_);
lean_dec(v___x_541_);
v_snd_544_ = lean_ctor_get(v___x_543_, 1);
v_fst_545_ = lean_ctor_get(v___x_543_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_543_);
if (v_isSharedCheck_589_ == 0)
{
v___x_547_ = v___x_543_;
v_isShared_548_ = v_isSharedCheck_589_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_snd_544_);
lean_inc(v_fst_545_);
lean_dec(v___x_543_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_589_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v_fst_549_; lean_object* v_snd_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_588_; 
v_fst_549_ = lean_ctor_get(v_snd_544_, 0);
v_snd_550_ = lean_ctor_get(v_snd_544_, 1);
v_isSharedCheck_588_ = !lean_is_exclusive(v_snd_544_);
if (v_isSharedCheck_588_ == 0)
{
v___x_552_ = v_snd_544_;
v_isShared_553_ = v_isSharedCheck_588_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_snd_550_);
lean_inc(v_fst_549_);
lean_dec(v_snd_544_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_588_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_554_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_555_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_554_, v___y_525_, v___y_519_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_563_; 
lean_dec_ref_known(v___x_555_, 1);
v___x_556_ = lean_int_mul(v_fst_549_, v_d_535_);
lean_dec(v_fst_549_);
lean_inc_ref(v___y_516_);
v___x_557_ = l_Int_Internal_Linear_Poly_mul(v___y_516_, v___x_556_);
lean_dec(v___x_556_);
v___x_558_ = lean_int_mul(v_snd_550_, v___y_526_);
lean_dec(v_snd_550_);
lean_inc_ref(v_p_537_);
v___x_559_ = l_Int_Internal_Linear_Poly_mul(v_p_537_, v___x_558_);
lean_dec(v___x_558_);
v___x_560_ = lean_int_mul(v___y_526_, v_d_535_);
lean_dec(v___y_526_);
v___x_561_ = l_Int_Internal_Linear_Poly_combine(v___x_557_, v___x_559_);
lean_inc(v_fst_545_);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 2, v___x_561_);
lean_ctor_set(v___x_539_, 1, v___y_512_);
lean_ctor_set(v___x_539_, 0, v_fst_545_);
v___x_563_ = v___x_539_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_fst_545_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v___y_512_);
lean_ctor_set(v_reuseFailAlloc_587_, 2, v___x_561_);
v___x_563_ = v_reuseFailAlloc_587_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
lean_object* v___x_565_; 
lean_inc(v_val_533_);
lean_inc_ref(v___y_523_);
if (v_isShared_553_ == 0)
{
lean_ctor_set_tag(v___x_552_, 4);
lean_ctor_set(v___x_552_, 1, v_val_533_);
lean_ctor_set(v___x_552_, 0, v___y_523_);
v___x_565_ = v___x_552_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___y_523_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v_val_533_);
v___x_565_ = v_reuseFailAlloc_586_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_566_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_566_, 0, v___x_560_);
lean_ctor_set(v___x_566_, 1, v___x_563_);
lean_ctor_set(v___x_566_, 2, v___x_565_);
lean_inc_ref(v___y_531_);
v___x_567_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v___x_566_, v___y_519_, v___y_528_, v___y_522_, v___y_518_, v___y_527_, v___y_514_, v___y_513_, v___y_530_, v___y_531_, v___y_529_);
if (lean_obj_tag(v___x_567_) == 0)
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_573_; 
lean_dec_ref_known(v___x_567_, 1);
v___x_568_ = l_Int_Internal_Linear_Poly_mul(v___y_516_, v_k_536_);
lean_dec(v_k_536_);
v___x_569_ = lean_int_neg(v___y_524_);
lean_dec(v___y_524_);
v___x_570_ = l_Int_Internal_Linear_Poly_mul(v_p_537_, v___x_569_);
lean_dec(v___x_569_);
v___x_571_ = l_Int_Internal_Linear_Poly_combine(v___x_568_, v___x_570_);
lean_inc(v_val_533_);
if (v_isShared_548_ == 0)
{
lean_ctor_set_tag(v___x_547_, 5);
lean_ctor_set(v___x_547_, 1, v_val_533_);
lean_ctor_set(v___x_547_, 0, v___y_523_);
v___x_573_ = v___x_547_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v___y_523_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v_val_533_);
v___x_573_ = v_reuseFailAlloc_585_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_581_; 
v_isSharedCheck_581_ = !lean_is_exclusive(v_val_533_);
if (v_isSharedCheck_581_ == 0)
{
lean_object* v_unused_582_; lean_object* v_unused_583_; lean_object* v_unused_584_; 
v_unused_582_ = lean_ctor_get(v_val_533_, 2);
lean_dec(v_unused_582_);
v_unused_583_ = lean_ctor_get(v_val_533_, 1);
lean_dec(v_unused_583_);
v_unused_584_ = lean_ctor_get(v_val_533_, 0);
lean_dec(v_unused_584_);
v___x_575_ = v_val_533_;
v_isShared_576_ = v_isSharedCheck_581_;
goto v_resetjp_574_;
}
else
{
lean_dec(v_val_533_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_581_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_578_; 
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 2, v___x_573_);
lean_ctor_set(v___x_575_, 1, v___x_571_);
lean_ctor_set(v___x_575_, 0, v_fst_545_);
v___x_578_ = v___x_575_;
goto v_reusejp_577_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_fst_545_);
lean_ctor_set(v_reuseFailAlloc_580_, 1, v___x_571_);
lean_ctor_set(v_reuseFailAlloc_580_, 2, v___x_573_);
v___x_578_ = v_reuseFailAlloc_580_;
goto v_reusejp_577_;
}
v_reusejp_577_:
{
v_c_484_ = v___x_578_;
v_a_485_ = v___y_519_;
v_a_486_ = v___y_528_;
v_a_487_ = v___y_522_;
v_a_488_ = v___y_518_;
v_a_489_ = v___y_527_;
v_a_490_ = v___y_514_;
v_a_491_ = v___y_513_;
v_a_492_ = v___y_530_;
v_a_493_ = v___y_531_;
v_a_494_ = v___y_529_;
goto _start;
}
}
}
}
else
{
lean_del_object(v___x_547_);
lean_dec(v_fst_545_);
lean_dec_ref(v_p_537_);
lean_dec(v_k_536_);
lean_dec(v_val_533_);
lean_dec_ref(v___y_531_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec_ref(v___y_516_);
return v___x_567_;
}
}
}
}
else
{
lean_del_object(v___x_552_);
lean_dec(v_snd_550_);
lean_dec(v_fst_549_);
lean_del_object(v___x_547_);
lean_dec(v_fst_545_);
lean_del_object(v___x_539_);
lean_dec_ref(v_p_537_);
lean_dec(v_k_536_);
lean_dec(v_val_533_);
lean_dec_ref(v___y_531_);
lean_dec(v___y_526_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_512_);
return v___x_555_;
}
}
}
}
}
else
{
lean_object* v___x_592_; 
lean_dec_ref(v_p_534_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_512_);
v___x_592_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_val_533_, v___y_519_, v___y_528_, v___y_522_, v___y_518_, v___y_527_, v___y_514_, v___y_513_, v___y_530_, v___y_531_, v___y_529_);
lean_dec_ref(v___y_531_);
return v___x_592_;
}
}
else
{
lean_object* v_options_593_; uint8_t v_hasTrace_594_; 
lean_dec(v___y_532_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_525_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_512_);
v_options_593_ = lean_ctor_get(v___y_531_, 2);
v_hasTrace_594_ = lean_ctor_get_uint8(v_options_593_, sizeof(void*)*1);
if (v_hasTrace_594_ == 0)
{
lean_dec_ref(v___y_523_);
v___y_500_ = v___y_515_;
v___y_501_ = v___y_517_;
v___y_502_ = v___y_519_;
v___y_503_ = v___y_513_;
v___y_504_ = v___y_530_;
v___y_505_ = v___y_531_;
v___y_506_ = v___y_529_;
goto v___jp_499_;
}
else
{
lean_object* v_inheritedTraceOptions_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; uint8_t v___x_600_; 
v_inheritedTraceOptions_595_ = lean_ctor_get(v___y_531_, 13);
v___x_596_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0));
lean_inc_ref(v___y_520_);
lean_inc_ref(v___y_521_);
lean_inc_ref(v___y_511_);
v___x_597_ = l_Lean_Name_mkStr4(v___y_511_, v___y_521_, v___y_520_, v___x_596_);
v___x_598_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
lean_inc(v___x_597_);
v___x_599_ = l_Lean_Name_append(v___x_598_, v___x_597_);
v___x_600_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_595_, v_options_593_, v___x_599_);
lean_dec(v___x_599_);
if (v___x_600_ == 0)
{
lean_dec(v___x_597_);
lean_dec_ref(v___y_523_);
v___y_500_ = v___y_515_;
v___y_501_ = v___y_517_;
v___y_502_ = v___y_519_;
v___y_503_ = v___y_513_;
v___y_504_ = v___y_530_;
v___y_505_ = v___y_531_;
v___y_506_ = v___y_529_;
goto v___jp_499_;
}
else
{
lean_object* v___x_601_; 
v___x_601_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v___y_523_, v___y_519_, v___y_531_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v_a_602_; lean_object* v___x_603_; 
v_a_602_ = lean_ctor_get(v___x_601_, 0);
lean_inc(v_a_602_);
lean_dec_ref_known(v___x_601_, 1);
v___x_603_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_597_, v_a_602_, v___y_513_, v___y_530_, v___y_531_, v___y_529_);
if (lean_obj_tag(v___x_603_) == 0)
{
lean_dec_ref_known(v___x_603_, 1);
v___y_500_ = v___y_515_;
v___y_501_ = v___y_517_;
v___y_502_ = v___y_519_;
v___y_503_ = v___y_513_;
v___y_504_ = v___y_530_;
v___y_505_ = v___y_531_;
v___y_506_ = v___y_529_;
goto v___jp_499_;
}
else
{
lean_dec_ref(v___y_531_);
lean_dec_ref(v___y_517_);
lean_dec_ref(v___y_515_);
return v___x_603_;
}
}
else
{
lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_611_; 
lean_dec(v___x_597_);
lean_dec_ref(v___y_531_);
lean_dec_ref(v___y_517_);
lean_dec_ref(v___y_515_);
v_a_604_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_611_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_611_ == 0)
{
v___x_606_ = v___x_601_;
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_dec(v___x_601_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_611_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_609_; 
if (v_isShared_607_ == 0)
{
v___x_609_ = v___x_606_;
goto v_reusejp_608_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_a_604_);
v___x_609_ = v_reuseFailAlloc_610_;
goto v_reusejp_608_;
}
v_reusejp_608_:
{
return v___x_609_;
}
}
}
}
}
}
}
v___jp_612_:
{
lean_object* v___x_634_; 
v___x_634_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v___y_624_, v___y_632_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v_a_635_; lean_object* v_dvds_636_; lean_object* v_size_637_; lean_object* v___x_638_; uint8_t v___x_639_; 
v_a_635_ = lean_ctor_get(v___x_634_, 0);
lean_inc(v_a_635_);
lean_dec_ref_known(v___x_634_, 1);
v_dvds_636_ = lean_ctor_get(v_a_635_, 6);
lean_inc_ref(v_dvds_636_);
lean_dec(v_a_635_);
v_size_637_ = lean_ctor_get(v_dvds_636_, 2);
v___x_638_ = lean_box(0);
v___x_639_ = lean_nat_dec_lt(v___y_614_, v_size_637_);
if (v___x_639_ == 0)
{
lean_object* v___x_640_; 
lean_dec_ref(v_dvds_636_);
v___x_640_ = l_outOfBounds___redArg(v___x_638_);
v___y_511_ = v___y_613_;
v___y_512_ = v___y_614_;
v___y_513_ = v___y_630_;
v___y_514_ = v___y_629_;
v___y_515_ = v___y_618_;
v___y_516_ = v___y_619_;
v___y_517_ = v___y_621_;
v___y_518_ = v___y_627_;
v___y_519_ = v___y_624_;
v___y_520_ = v___y_622_;
v___y_521_ = v___y_623_;
v___y_522_ = v___y_626_;
v___y_523_ = v___y_615_;
v___y_524_ = v___y_616_;
v___y_525_ = v___y_617_;
v___y_526_ = v___y_620_;
v___y_527_ = v___y_628_;
v___y_528_ = v___y_625_;
v___y_529_ = v___y_633_;
v___y_530_ = v___y_631_;
v___y_531_ = v___y_632_;
v___y_532_ = v___x_640_;
goto v___jp_510_;
}
else
{
lean_object* v___x_641_; 
v___x_641_ = l_Lean_PersistentArray_get_x21___redArg(v___x_638_, v_dvds_636_, v___y_614_);
lean_dec_ref(v_dvds_636_);
v___y_511_ = v___y_613_;
v___y_512_ = v___y_614_;
v___y_513_ = v___y_630_;
v___y_514_ = v___y_629_;
v___y_515_ = v___y_618_;
v___y_516_ = v___y_619_;
v___y_517_ = v___y_621_;
v___y_518_ = v___y_627_;
v___y_519_ = v___y_624_;
v___y_520_ = v___y_622_;
v___y_521_ = v___y_623_;
v___y_522_ = v___y_626_;
v___y_523_ = v___y_615_;
v___y_524_ = v___y_616_;
v___y_525_ = v___y_617_;
v___y_526_ = v___y_620_;
v___y_527_ = v___y_628_;
v___y_528_ = v___y_625_;
v___y_529_ = v___y_633_;
v___y_530_ = v___y_631_;
v___y_531_ = v___y_632_;
v___y_532_ = v___x_641_;
goto v___jp_510_;
}
}
else
{
lean_object* v_a_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_649_; 
lean_dec_ref(v___y_632_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
v_a_642_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_649_ == 0)
{
v___x_644_ = v___x_634_;
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_a_642_);
lean_dec(v___x_634_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_649_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_647_; 
if (v_isShared_645_ == 0)
{
v___x_647_ = v___x_644_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_648_; 
v_reuseFailAlloc_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_648_, 0, v_a_642_);
v___x_647_ = v_reuseFailAlloc_648_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
return v___x_647_;
}
}
}
}
v___jp_650_:
{
lean_object* v___x_662_; lean_object* v___x_663_; 
v___x_662_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_662_, 0, v___y_651_);
v___x_663_ = l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(v___x_662_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
lean_dec_ref(v___y_660_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_671_; 
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_671_ == 0)
{
lean_object* v_unused_672_; 
v_unused_672_ = lean_ctor_get(v___x_663_, 0);
lean_dec(v_unused_672_);
v___x_665_ = v___x_663_;
v_isShared_666_ = v_isSharedCheck_671_;
goto v_resetjp_664_;
}
else
{
lean_dec(v___x_663_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_671_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_667_; lean_object* v___x_669_; 
v___x_667_ = lean_box(0);
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 0, v___x_667_);
v___x_669_ = v___x_665_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_667_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
else
{
return v___x_663_;
}
}
v___jp_673_:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(v_c_484_);
lean_inc_ref(v___y_685_);
v___x_688_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(v___x_687_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_688_) == 0)
{
lean_object* v_a_689_; lean_object* v_d_690_; lean_object* v_p_691_; uint8_t v___x_692_; 
v_a_689_ = lean_ctor_get(v___x_688_, 0);
lean_inc(v_a_689_);
lean_dec_ref_known(v___x_688_, 1);
v_d_690_ = lean_ctor_get(v_a_689_, 0);
v_p_691_ = lean_ctor_get(v_a_689_, 1);
lean_inc(v_d_690_);
v___x_692_ = l_Int_Internal_Linear_Poly_isUnsatDvd(v_d_690_, v_p_691_);
if (v___x_692_ == 0)
{
uint8_t v___x_693_; 
v___x_693_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(v_a_689_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; uint8_t v___x_695_; 
v___x_694_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1);
v___x_695_ = lean_int_dec_eq(v_d_690_, v___x_694_);
if (v___x_695_ == 0)
{
if (lean_obj_tag(v_p_691_) == 1)
{
lean_object* v_k_696_; lean_object* v_v_697_; lean_object* v_p_698_; lean_object* v___x_699_; 
lean_inc_ref(v_p_691_);
lean_inc(v_d_690_);
v_k_696_ = lean_ctor_get(v_p_691_, 0);
lean_inc(v_k_696_);
v_v_697_ = lean_ctor_get(v_p_691_, 1);
lean_inc(v_v_697_);
v_p_698_ = lean_ctor_get(v_p_691_, 2);
lean_inc_ref(v_p_698_);
lean_inc(v_a_689_);
v___x_699_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(v_a_689_, v___y_677_, v___y_685_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; lean_object* v___f_701_; lean_object* v___f_702_; uint8_t v___x_703_; uint8_t v___x_704_; uint8_t v___x_705_; 
v_a_700_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_a_700_);
lean_dec_ref_known(v___x_699_, 1);
lean_inc_n(v_v_697_, 2);
lean_inc(v_a_689_);
v___f_701_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed), 3, 2);
lean_closure_set(v___f_701_, 0, v_a_689_);
lean_closure_set(v___f_701_, 1, v_v_697_);
v___f_702_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed), 2, 1);
lean_closure_set(v___f_702_, 0, v_v_697_);
v___x_703_ = 0;
v___x_704_ = lean_unbox(v_a_700_);
lean_dec(v_a_700_);
v___x_705_ = l_Lean_instBEqLBool_beq(v___x_704_, v___x_703_);
if (v___x_705_ == 0)
{
v___y_613_ = v___y_674_;
v___y_614_ = v_v_697_;
v___y_615_ = v_a_689_;
v___y_616_ = v_k_696_;
v___y_617_ = v___f_702_;
v___y_618_ = v_p_691_;
v___y_619_ = v_p_698_;
v___y_620_ = v_d_690_;
v___y_621_ = v___f_701_;
v___y_622_ = v___y_675_;
v___y_623_ = v___y_676_;
v___y_624_ = v___y_677_;
v___y_625_ = v___y_678_;
v___y_626_ = v___y_679_;
v___y_627_ = v___y_680_;
v___y_628_ = v___y_681_;
v___y_629_ = v___y_682_;
v___y_630_ = v___y_683_;
v___y_631_ = v___y_684_;
v___y_632_ = v___y_685_;
v___y_633_ = v___y_686_;
goto v___jp_612_;
}
else
{
lean_object* v___x_706_; 
lean_inc(v_v_697_);
v___x_706_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v_v_697_, v___y_677_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_dec_ref_known(v___x_706_, 1);
v___y_613_ = v___y_674_;
v___y_614_ = v_v_697_;
v___y_615_ = v_a_689_;
v___y_616_ = v_k_696_;
v___y_617_ = v___f_702_;
v___y_618_ = v_p_691_;
v___y_619_ = v_p_698_;
v___y_620_ = v_d_690_;
v___y_621_ = v___f_701_;
v___y_622_ = v___y_675_;
v___y_623_ = v___y_676_;
v___y_624_ = v___y_677_;
v___y_625_ = v___y_678_;
v___y_626_ = v___y_679_;
v___y_627_ = v___y_680_;
v___y_628_ = v___y_681_;
v___y_629_ = v___y_682_;
v___y_630_ = v___y_683_;
v___y_631_ = v___y_684_;
v___y_632_ = v___y_685_;
v___y_633_ = v___y_686_;
goto v___jp_612_;
}
else
{
lean_dec_ref(v___f_702_);
lean_dec_ref(v___f_701_);
lean_dec_ref(v_p_698_);
lean_dec(v_v_697_);
lean_dec_ref_known(v_p_691_, 3);
lean_dec(v_k_696_);
lean_dec(v_d_690_);
lean_dec(v_a_689_);
lean_dec_ref(v___y_685_);
return v___x_706_;
}
}
}
else
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
lean_dec_ref(v_p_698_);
lean_dec(v_v_697_);
lean_dec_ref_known(v_p_691_, 3);
lean_dec(v_k_696_);
lean_dec(v_d_690_);
lean_dec(v_a_689_);
lean_dec_ref(v___y_685_);
v_a_707_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___x_699_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_699_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_a_707_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
else
{
lean_object* v___x_715_; 
v___x_715_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_a_689_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
lean_dec_ref(v___y_685_);
return v___x_715_;
}
}
else
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; 
lean_inc_ref(v_p_691_);
v___x_716_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_716_, 0, v_a_689_);
v___x_717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_717_, 0, v_p_691_);
lean_ctor_set(v___x_717_, 1, v___x_716_);
lean_inc(v___y_686_);
lean_inc(v___y_684_);
lean_inc_ref(v___y_683_);
lean_inc(v___y_682_);
lean_inc_ref(v___y_681_);
lean_inc(v___y_680_);
lean_inc_ref(v___y_679_);
lean_inc(v___y_678_);
lean_inc(v___y_677_);
v___x_718_ = lean_grind_cutsat_assert_eq(v___x_717_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_718_) == 0)
{
lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_726_; 
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_718_);
if (v_isSharedCheck_726_ == 0)
{
lean_object* v_unused_727_; 
v_unused_727_ = lean_ctor_get(v___x_718_, 0);
lean_dec(v_unused_727_);
v___x_720_ = v___x_718_;
v_isShared_721_ = v_isSharedCheck_726_;
goto v_resetjp_719_;
}
else
{
lean_dec(v___x_718_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_726_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_722_; lean_object* v___x_724_; 
v___x_722_ = lean_box(0);
if (v_isShared_721_ == 0)
{
lean_ctor_set(v___x_720_, 0, v___x_722_);
v___x_724_ = v___x_720_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_722_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
else
{
return v___x_718_;
}
}
}
else
{
lean_object* v_options_728_; uint8_t v_hasTrace_729_; 
v_options_728_ = lean_ctor_get(v___y_685_, 2);
v_hasTrace_729_ = lean_ctor_get_uint8(v_options_728_, sizeof(void*)*1);
if (v_hasTrace_729_ == 0)
{
lean_dec(v_a_689_);
lean_dec_ref(v___y_685_);
goto v___jp_496_;
}
else
{
lean_object* v_inheritedTraceOptions_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; uint8_t v___x_735_; 
v_inheritedTraceOptions_730_ = lean_ctor_get(v___y_685_, 13);
v___x_731_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1));
lean_inc_ref(v___y_675_);
lean_inc_ref(v___y_676_);
lean_inc_ref(v___y_674_);
v___x_732_ = l_Lean_Name_mkStr4(v___y_674_, v___y_676_, v___y_675_, v___x_731_);
v___x_733_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
lean_inc(v___x_732_);
v___x_734_ = l_Lean_Name_append(v___x_733_, v___x_732_);
v___x_735_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_730_, v_options_728_, v___x_734_);
lean_dec(v___x_734_);
if (v___x_735_ == 0)
{
lean_dec(v___x_732_);
lean_dec(v_a_689_);
lean_dec_ref(v___y_685_);
goto v___jp_496_;
}
else
{
lean_object* v___x_736_; 
v___x_736_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_a_689_, v___y_677_, v___y_685_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v_a_737_; lean_object* v___x_738_; 
v_a_737_ = lean_ctor_get(v___x_736_, 0);
lean_inc(v_a_737_);
lean_dec_ref_known(v___x_736_, 1);
v___x_738_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_732_, v_a_737_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
lean_dec_ref(v___y_685_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_dec_ref_known(v___x_738_, 1);
goto v___jp_496_;
}
else
{
return v___x_738_;
}
}
else
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_746_; 
lean_dec(v___x_732_);
lean_dec_ref(v___y_685_);
v_a_739_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_746_ == 0)
{
v___x_741_ = v___x_736_;
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_736_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_744_; 
if (v_isShared_742_ == 0)
{
v___x_744_ = v___x_741_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_a_739_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
}
}
}
else
{
lean_object* v_options_747_; uint8_t v_hasTrace_748_; 
v_options_747_ = lean_ctor_get(v___y_685_, 2);
v_hasTrace_748_ = lean_ctor_get_uint8(v_options_747_, sizeof(void*)*1);
if (v_hasTrace_748_ == 0)
{
v___y_651_ = v_a_689_;
v___y_652_ = v___y_677_;
v___y_653_ = v___y_678_;
v___y_654_ = v___y_679_;
v___y_655_ = v___y_680_;
v___y_656_ = v___y_681_;
v___y_657_ = v___y_682_;
v___y_658_ = v___y_683_;
v___y_659_ = v___y_684_;
v___y_660_ = v___y_685_;
v___y_661_ = v___y_686_;
goto v___jp_650_;
}
else
{
lean_object* v_inheritedTraceOptions_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; uint8_t v___x_754_; 
v_inheritedTraceOptions_749_ = lean_ctor_get(v___y_685_, 13);
v___x_750_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2));
lean_inc_ref(v___y_675_);
lean_inc_ref(v___y_676_);
lean_inc_ref(v___y_674_);
v___x_751_ = l_Lean_Name_mkStr4(v___y_674_, v___y_676_, v___y_675_, v___x_750_);
v___x_752_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
lean_inc(v___x_751_);
v___x_753_ = l_Lean_Name_append(v___x_752_, v___x_751_);
v___x_754_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_749_, v_options_747_, v___x_753_);
lean_dec(v___x_753_);
if (v___x_754_ == 0)
{
lean_dec(v___x_751_);
v___y_651_ = v_a_689_;
v___y_652_ = v___y_677_;
v___y_653_ = v___y_678_;
v___y_654_ = v___y_679_;
v___y_655_ = v___y_680_;
v___y_656_ = v___y_681_;
v___y_657_ = v___y_682_;
v___y_658_ = v___y_683_;
v___y_659_ = v___y_684_;
v___y_660_ = v___y_685_;
v___y_661_ = v___y_686_;
goto v___jp_650_;
}
else
{
lean_object* v___x_755_; 
lean_inc(v_a_689_);
v___x_755_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_a_689_, v___y_677_, v___y_685_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v_a_756_; lean_object* v___x_757_; 
v_a_756_ = lean_ctor_get(v___x_755_, 0);
lean_inc(v_a_756_);
lean_dec_ref_known(v___x_755_, 1);
v___x_757_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_751_, v_a_756_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_dec_ref_known(v___x_757_, 1);
v___y_651_ = v_a_689_;
v___y_652_ = v___y_677_;
v___y_653_ = v___y_678_;
v___y_654_ = v___y_679_;
v___y_655_ = v___y_680_;
v___y_656_ = v___y_681_;
v___y_657_ = v___y_682_;
v___y_658_ = v___y_683_;
v___y_659_ = v___y_684_;
v___y_660_ = v___y_685_;
v___y_661_ = v___y_686_;
goto v___jp_650_;
}
else
{
lean_dec(v_a_689_);
lean_dec_ref(v___y_685_);
return v___x_757_;
}
}
else
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
lean_dec(v___x_751_);
lean_dec(v_a_689_);
lean_dec_ref(v___y_685_);
v_a_758_ = lean_ctor_get(v___x_755_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_755_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_755_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_755_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_758_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
lean_dec_ref(v___y_685_);
v_a_766_ = lean_ctor_get(v___x_688_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_688_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_688_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_688_);
v___x_768_ = lean_box(0);
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
v_resetjp_767_:
{
lean_object* v___x_771_; 
if (v_isShared_769_ == 0)
{
v___x_771_ = v___x_768_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_a_766_);
v___x_771_ = v_reuseFailAlloc_772_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
return v___x_771_;
}
}
}
}
v___jp_790_:
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_791_ = lean_unsigned_to_nat(1u);
v___x_792_ = lean_nat_add(v_currRecDepth_777_, v___x_791_);
lean_dec(v_currRecDepth_777_);
lean_inc_ref(v_inheritedTraceOptions_789_);
lean_inc_ref(v_options_776_);
v___x_793_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_793_, 0, v_fileName_774_);
lean_ctor_set(v___x_793_, 1, v_fileMap_775_);
lean_ctor_set(v___x_793_, 2, v_options_776_);
lean_ctor_set(v___x_793_, 3, v___x_792_);
lean_ctor_set(v___x_793_, 4, v_maxRecDepth_778_);
lean_ctor_set(v___x_793_, 5, v_ref_779_);
lean_ctor_set(v___x_793_, 6, v_currNamespace_780_);
lean_ctor_set(v___x_793_, 7, v_openDecls_781_);
lean_ctor_set(v___x_793_, 8, v_initHeartbeats_782_);
lean_ctor_set(v___x_793_, 9, v_maxHeartbeats_783_);
lean_ctor_set(v___x_793_, 10, v_quotContext_784_);
lean_ctor_set(v___x_793_, 11, v_currMacroScope_785_);
lean_ctor_set(v___x_793_, 12, v_cancelTk_x3f_787_);
lean_ctor_set(v___x_793_, 13, v_inheritedTraceOptions_789_);
lean_ctor_set_uint8(v___x_793_, sizeof(void*)*14, v_diag_786_);
lean_ctor_set_uint8(v___x_793_, sizeof(void*)*14 + 1, v_suppressElabErrors_788_);
v___x_794_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_485_, v___x_793_);
if (lean_obj_tag(v___x_794_) == 0)
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_822_; 
v_a_795_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_822_ == 0)
{
v___x_797_ = v___x_794_;
v_isShared_798_ = v_isSharedCheck_822_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_794_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_822_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
uint8_t v___x_799_; 
v___x_799_ = lean_unbox(v_a_795_);
lean_dec(v_a_795_);
if (v___x_799_ == 0)
{
uint8_t v_hasTrace_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; 
lean_del_object(v___x_797_);
v_hasTrace_800_ = lean_ctor_get_uint8(v_options_776_, sizeof(void*)*1);
v___x_801_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0));
v___x_802_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2));
v___x_803_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3));
if (v_hasTrace_800_ == 0)
{
lean_dec_ref(v_inheritedTraceOptions_789_);
lean_dec_ref(v_options_776_);
v___y_674_ = v___x_801_;
v___y_675_ = v___x_803_;
v___y_676_ = v___x_802_;
v___y_677_ = v_a_485_;
v___y_678_ = v_a_486_;
v___y_679_ = v_a_487_;
v___y_680_ = v_a_488_;
v___y_681_ = v_a_489_;
v___y_682_ = v_a_490_;
v___y_683_ = v_a_491_;
v___y_684_ = v_a_492_;
v___y_685_ = v___x_793_;
v___y_686_ = v_a_494_;
goto v___jp_673_;
}
else
{
lean_object* v___x_804_; lean_object* v___x_805_; uint8_t v___x_806_; 
v___x_804_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4));
v___x_805_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5);
v___x_806_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_789_, v_options_776_, v___x_805_);
lean_dec_ref(v_options_776_);
lean_dec_ref(v_inheritedTraceOptions_789_);
if (v___x_806_ == 0)
{
v___y_674_ = v___x_801_;
v___y_675_ = v___x_803_;
v___y_676_ = v___x_802_;
v___y_677_ = v_a_485_;
v___y_678_ = v_a_486_;
v___y_679_ = v_a_487_;
v___y_680_ = v_a_488_;
v___y_681_ = v_a_489_;
v___y_682_ = v_a_490_;
v___y_683_ = v_a_491_;
v___y_684_ = v_a_492_;
v___y_685_ = v___x_793_;
v___y_686_ = v_a_494_;
goto v___jp_673_;
}
else
{
lean_object* v___x_807_; 
lean_inc_ref(v_c_484_);
v___x_807_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_484_, v_a_485_, v___x_793_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v_a_808_; lean_object* v___x_809_; 
v_a_808_ = lean_ctor_get(v___x_807_, 0);
lean_inc(v_a_808_);
lean_dec_ref_known(v___x_807_, 1);
v___x_809_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_804_, v_a_808_, v_a_491_, v_a_492_, v___x_793_, v_a_494_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_dec_ref_known(v___x_809_, 1);
v___y_674_ = v___x_801_;
v___y_675_ = v___x_803_;
v___y_676_ = v___x_802_;
v___y_677_ = v_a_485_;
v___y_678_ = v_a_486_;
v___y_679_ = v_a_487_;
v___y_680_ = v_a_488_;
v___y_681_ = v_a_489_;
v___y_682_ = v_a_490_;
v___y_683_ = v_a_491_;
v___y_684_ = v_a_492_;
v___y_685_ = v___x_793_;
v___y_686_ = v_a_494_;
goto v___jp_673_;
}
else
{
lean_dec_ref_known(v___x_793_, 14);
lean_dec_ref(v_c_484_);
return v___x_809_;
}
}
else
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
lean_dec_ref_known(v___x_793_, 14);
lean_dec_ref(v_c_484_);
v_a_810_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_807_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_807_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
}
}
else
{
lean_object* v___x_818_; lean_object* v___x_820_; 
lean_dec_ref_known(v___x_793_, 14);
lean_dec_ref(v_inheritedTraceOptions_789_);
lean_dec_ref(v_options_776_);
lean_dec_ref(v_c_484_);
v___x_818_ = lean_box(0);
if (v_isShared_798_ == 0)
{
lean_ctor_set(v___x_797_, 0, v___x_818_);
v___x_820_ = v___x_797_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_818_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
else
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_830_; 
lean_dec_ref_known(v___x_793_, 14);
lean_dec_ref(v_inheritedTraceOptions_789_);
lean_dec_ref(v_options_776_);
lean_dec_ref(v_c_484_);
v_a_823_ = lean_ctor_get(v___x_794_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_830_ == 0)
{
v___x_825_ = v___x_794_;
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_794_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_830_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v___x_828_; 
if (v_isShared_826_ == 0)
{
v___x_828_ = v___x_825_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v_a_823_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___boxed(lean_object* v_c_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v_c_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_);
lean_dec(v_a_845_);
lean_dec(v_a_843_);
lean_dec_ref(v_a_842_);
lean_dec(v_a_841_);
lean_dec_ref(v_a_840_);
lean_dec(v_a_839_);
lean_dec_ref(v_a_838_);
lean_dec(v_a_837_);
lean_dec(v_a_836_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(lean_object* v_c_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_){
_start:
{
lean_object* v_d_860_; lean_object* v_p_861_; lean_object* v___x_862_; 
v_d_860_ = lean_ctor_get(v_c_848_, 0);
v_p_861_ = lean_ctor_get(v_c_848_, 1);
lean_inc_ref(v_p_861_);
v___x_862_ = l_Int_Internal_Linear_Poly_normCommRing_x3f(v_p_861_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_a_863_);
lean_dec_ref_known(v___x_862_, 1);
if (lean_obj_tag(v_a_863_) == 1)
{
lean_object* v_val_864_; lean_object* v_snd_865_; lean_object* v_fst_866_; lean_object* v_fst_867_; lean_object* v_snd_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; 
lean_inc(v_d_860_);
v_val_864_ = lean_ctor_get(v_a_863_, 0);
lean_inc(v_val_864_);
lean_dec_ref_known(v_a_863_, 1);
v_snd_865_ = lean_ctor_get(v_val_864_, 1);
lean_inc(v_snd_865_);
v_fst_866_ = lean_ctor_get(v_val_864_, 0);
lean_inc(v_fst_866_);
lean_dec(v_val_864_);
v_fst_867_ = lean_ctor_get(v_snd_865_, 0);
lean_inc(v_fst_867_);
v_snd_868_ = lean_ctor_get(v_snd_865_, 1);
lean_inc(v_snd_868_);
lean_dec(v_snd_865_);
v___x_869_ = lean_alloc_ctor(12, 3, 0);
lean_ctor_set(v___x_869_, 0, v_c_848_);
lean_ctor_set(v___x_869_, 1, v_fst_866_);
lean_ctor_set(v___x_869_, 2, v_fst_867_);
v___x_870_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_870_, 0, v_d_860_);
lean_ctor_set(v___x_870_, 1, v_snd_868_);
lean_ctor_set(v___x_870_, 2, v___x_869_);
lean_inc_ref(v_a_857_);
v___x_871_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v___x_870_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_);
return v___x_871_;
}
else
{
lean_object* v___x_872_; 
lean_dec(v_a_863_);
lean_inc_ref(v_a_857_);
v___x_872_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v_c_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_);
return v___x_872_;
}
}
else
{
lean_object* v_a_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_880_; 
lean_dec_ref(v_c_848_);
v_a_873_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_880_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_880_ == 0)
{
v___x_875_ = v___x_862_;
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_a_873_);
lean_dec(v___x_862_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_880_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___x_878_; 
if (v_isShared_876_ == 0)
{
v___x_878_ = v___x_875_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_879_; 
v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_873_);
v___x_878_ = v_reuseFailAlloc_879_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
return v___x_878_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore___boxed(lean_object* v_c_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v_c_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_);
lean_dec(v_a_891_);
lean_dec_ref(v_a_890_);
lean_dec(v_a_889_);
lean_dec_ref(v_a_888_);
lean_dec(v_a_887_);
lean_dec_ref(v_a_886_);
lean_dec(v_a_885_);
lean_dec_ref(v_a_884_);
lean_dec(v_a_883_);
lean_dec(v_a_882_);
return v_res_893_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8(void){
_start:
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_908_ = lean_box(0);
v___x_909_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7));
v___x_910_ = l_Lean_mkConst(v___x_909_, v___x_908_);
return v___x_910_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10(void){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9));
v___x_913_ = l_Lean_stringToMessageData(v___x_912_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(lean_object* v_e_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_){
_start:
{
lean_object* v___x_929_; 
lean_inc_ref(v_e_914_);
v___x_929_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_914_, v_a_922_);
if (lean_obj_tag(v___x_929_) == 0)
{
lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_1063_; 
v_a_930_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_932_ = v___x_929_;
v_isShared_933_ = v_isSharedCheck_1063_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___x_929_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_1063_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_939_; uint8_t v___x_940_; 
v___x_939_ = l_Lean_Expr_cleanupAnnotations(v_a_930_);
v___x_940_ = l_Lean_Expr_isApp(v___x_939_);
if (v___x_940_ == 0)
{
lean_dec_ref(v___x_939_);
lean_dec_ref(v_e_914_);
goto v___jp_934_;
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
lean_dec_ref(v_e_914_);
goto v___jp_934_;
}
else
{
lean_object* v_arg_944_; lean_object* v___x_945_; uint8_t v___x_946_; 
v_arg_944_ = lean_ctor_get(v___x_942_, 1);
lean_inc_ref(v_arg_944_);
v___x_945_ = l_Lean_Expr_appFnCleanup___redArg(v___x_942_);
v___x_946_ = l_Lean_Expr_isApp(v___x_945_);
if (v___x_946_ == 0)
{
lean_dec_ref(v___x_945_);
lean_dec_ref(v_arg_944_);
lean_dec_ref(v_arg_941_);
lean_dec_ref(v_e_914_);
goto v___jp_934_;
}
else
{
lean_object* v_arg_947_; lean_object* v___x_948_; uint8_t v___x_949_; 
v_arg_947_ = lean_ctor_get(v___x_945_, 1);
lean_inc_ref(v_arg_947_);
v___x_948_ = l_Lean_Expr_appFnCleanup___redArg(v___x_945_);
v___x_949_ = l_Lean_Expr_isApp(v___x_948_);
if (v___x_949_ == 0)
{
lean_dec_ref(v___x_948_);
lean_dec_ref(v_arg_947_);
lean_dec_ref(v_arg_944_);
lean_dec_ref(v_arg_941_);
lean_dec_ref(v_e_914_);
goto v___jp_934_;
}
else
{
lean_object* v___x_950_; lean_object* v___x_951_; uint8_t v___x_952_; 
v___x_950_ = l_Lean_Expr_appFnCleanup___redArg(v___x_948_);
v___x_951_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_952_ = l_Lean_Expr_isConstOf(v___x_950_, v___x_951_);
lean_dec_ref(v___x_950_);
if (v___x_952_ == 0)
{
lean_dec_ref(v_arg_947_);
lean_dec_ref(v_arg_944_);
lean_dec_ref(v_arg_941_);
lean_dec_ref(v_e_914_);
goto v___jp_934_;
}
else
{
lean_object* v___x_953_; 
lean_del_object(v___x_932_);
v___x_953_ = l_Lean_Meta_Structural_isInstDvdInt___redArg(v_arg_947_, v_a_922_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_1054_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_956_ = v___x_953_;
v_isShared_957_ = v_isSharedCheck_1054_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_953_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_1054_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
uint8_t v___x_958_; 
v___x_958_ = lean_unbox(v_a_954_);
lean_dec(v_a_954_);
if (v___x_958_ == 0)
{
lean_object* v___x_959_; lean_object* v___x_961_; 
lean_dec_ref(v_arg_944_);
lean_dec_ref(v_arg_941_);
lean_dec_ref(v_e_914_);
v___x_959_ = lean_box(0);
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 0, v___x_959_);
v___x_961_ = v___x_956_;
goto v_reusejp_960_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v___x_959_);
v___x_961_ = v_reuseFailAlloc_962_;
goto v_reusejp_960_;
}
v_reusejp_960_:
{
return v___x_961_;
}
}
else
{
lean_object* v___x_963_; 
lean_del_object(v___x_956_);
lean_inc_ref(v_arg_944_);
v___x_963_ = l_Lean_Meta_getIntValue_x3f(v_arg_944_, v_a_921_, v_a_922_, v_a_923_, v_a_924_);
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v_a_964_; 
v_a_964_ = lean_ctor_get(v___x_963_, 0);
lean_inc(v_a_964_);
lean_dec_ref_known(v___x_963_, 1);
if (lean_obj_tag(v_a_964_) == 1)
{
lean_object* v_val_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_1030_; 
v_val_965_ = lean_ctor_get(v_a_964_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v_a_964_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_967_ = v_a_964_;
v_isShared_968_ = v_isSharedCheck_1030_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_val_965_);
lean_dec(v_a_964_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_1030_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_969_; 
lean_inc_ref(v_e_914_);
v___x_969_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_914_, v_a_915_, v_a_919_, v_a_921_, v_a_922_, v_a_923_, v_a_924_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; uint8_t v___x_971_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
lean_inc(v_a_970_);
lean_dec_ref_known(v___x_969_, 1);
v___x_971_ = lean_unbox(v_a_970_);
lean_dec(v_a_970_);
if (v___x_971_ == 0)
{
lean_object* v___x_972_; 
lean_del_object(v___x_967_);
lean_dec(v_val_965_);
lean_inc_ref(v_e_914_);
v___x_972_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_914_, v_a_915_, v_a_919_, v_a_921_, v_a_922_, v_a_923_, v_a_924_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_998_; 
v_a_973_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_998_ == 0)
{
v___x_975_ = v___x_972_;
v_isShared_976_ = v_isSharedCheck_998_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_972_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_998_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
uint8_t v___x_977_; 
v___x_977_ = lean_unbox(v_a_973_);
lean_dec(v_a_973_);
if (v___x_977_ == 0)
{
lean_object* v___x_978_; lean_object* v___x_980_; 
lean_dec_ref(v_arg_944_);
lean_dec_ref(v_arg_941_);
lean_dec_ref(v_e_914_);
v___x_978_ = lean_box(0);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v___x_978_);
v___x_980_ = v___x_975_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v___x_978_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
else
{
lean_object* v___x_982_; 
lean_del_object(v___x_975_);
lean_inc_ref(v_e_914_);
v___x_982_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_a_983_);
lean_dec_ref_known(v___x_982_, 1);
v___x_984_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8);
v___x_985_ = l_Lean_eagerReflBoolTrue;
v___x_986_ = l_Lean_Meta_mkOfEqFalseCore(v_e_914_, v_a_983_);
v___x_987_ = l_Lean_mkApp4(v___x_984_, v_arg_944_, v_arg_941_, v___x_985_, v___x_986_);
v___x_988_ = lean_unsigned_to_nat(0u);
v___x_989_ = l_Lean_Meta_Grind_pushNewFact(v___x_987_, v___x_988_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_);
return v___x_989_;
}
else
{
lean_object* v_a_990_; lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_997_; 
lean_dec_ref(v_arg_944_);
lean_dec_ref(v_arg_941_);
lean_dec_ref(v_e_914_);
v_a_990_ = lean_ctor_get(v___x_982_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v___x_982_);
if (v_isSharedCheck_997_ == 0)
{
v___x_992_ = v___x_982_;
v_isShared_993_ = v_isSharedCheck_997_;
goto v_resetjp_991_;
}
else
{
lean_inc(v_a_990_);
lean_dec(v___x_982_);
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
}
}
else
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1006_; 
lean_dec_ref(v_arg_944_);
lean_dec_ref(v_arg_941_);
lean_dec_ref(v_e_914_);
v_a_999_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_1001_ = v___x_972_;
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_972_);
v___x_1001_ = lean_box(0);
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
v_resetjp_1000_:
{
lean_object* v___x_1004_; 
if (v_isShared_1002_ == 0)
{
v___x_1004_ = v___x_1001_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_a_999_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
}
}
else
{
lean_object* v___x_1007_; 
lean_dec_ref(v_arg_944_);
v___x_1007_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(v_arg_941_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v_a_1008_; lean_object* v___x_1010_; 
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
lean_inc(v_a_1008_);
lean_dec_ref_known(v___x_1007_, 1);
if (v_isShared_968_ == 0)
{
lean_ctor_set_tag(v___x_967_, 0);
lean_ctor_set(v___x_967_, 0, v_e_914_);
v___x_1010_ = v___x_967_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_e_914_);
v___x_1010_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; 
v___x_1011_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1011_, 0, v_val_965_);
lean_ctor_set(v___x_1011_, 1, v_a_1008_);
lean_ctor_set(v___x_1011_, 2, v___x_1010_);
v___x_1012_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v___x_1011_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_);
return v___x_1012_;
}
}
else
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1021_; 
lean_del_object(v___x_967_);
lean_dec(v_val_965_);
lean_dec_ref(v_e_914_);
v_a_1014_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1016_ = v___x_1007_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_1007_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_a_1014_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
}
else
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
lean_del_object(v___x_967_);
lean_dec(v_val_965_);
lean_dec_ref(v_arg_944_);
lean_dec_ref(v_arg_941_);
lean_dec_ref(v_e_914_);
v_a_1022_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_969_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_969_);
v___x_1024_ = lean_box(0);
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
v_resetjp_1023_:
{
lean_object* v___x_1027_; 
if (v_isShared_1025_ == 0)
{
v___x_1027_ = v___x_1024_;
goto v_reusejp_1026_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_a_1022_);
v___x_1027_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1026_;
}
v_reusejp_1026_:
{
return v___x_1027_;
}
}
}
}
}
else
{
lean_object* v___x_1031_; 
lean_dec(v_a_964_);
lean_dec_ref(v_arg_944_);
lean_dec_ref(v_arg_941_);
v___x_1031_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_919_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v_a_1032_; uint8_t v_verbose_1033_; 
v_a_1032_ = lean_ctor_get(v___x_1031_, 0);
lean_inc(v_a_1032_);
lean_dec_ref_known(v___x_1031_, 1);
v_verbose_1033_ = lean_ctor_get_uint8(v_a_1032_, 0);
lean_dec(v_a_1032_);
if (v_verbose_1033_ == 0)
{
lean_dec_ref(v_e_914_);
goto v___jp_926_;
}
else
{
lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1034_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10);
v___x_1035_ = l_Lean_indentExpr(v_e_914_);
v___x_1036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1036_, 0, v___x_1034_);
lean_ctor_set(v___x_1036_, 1, v___x_1035_);
v___x_1037_ = l_Lean_Meta_Sym_reportIssue(v___x_1036_, v_a_919_, v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_);
if (lean_obj_tag(v___x_1037_) == 0)
{
lean_dec_ref_known(v___x_1037_, 1);
goto v___jp_926_;
}
else
{
return v___x_1037_;
}
}
}
else
{
lean_object* v_a_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1045_; 
lean_dec_ref(v_e_914_);
v_a_1038_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1045_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1045_ == 0)
{
v___x_1040_ = v___x_1031_;
v_isShared_1041_ = v_isSharedCheck_1045_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_a_1038_);
lean_dec(v___x_1031_);
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
else
{
lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1053_; 
lean_dec_ref(v_arg_944_);
lean_dec_ref(v_arg_941_);
lean_dec_ref(v_e_914_);
v_a_1046_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1048_ = v___x_963_;
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v___x_963_);
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
else
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
lean_dec_ref(v_arg_944_);
lean_dec_ref(v_arg_941_);
lean_dec_ref(v_e_914_);
v_a_1055_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1057_ = v___x_953_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_953_);
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
}
}
}
}
}
v___jp_934_:
{
lean_object* v___x_935_; lean_object* v___x_937_; 
v___x_935_ = lean_box(0);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 0, v___x_935_);
v___x_937_ = v___x_932_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v___x_935_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
else
{
lean_object* v_a_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1071_; 
lean_dec_ref(v_e_914_);
v_a_1064_ = lean_ctor_get(v___x_929_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_929_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_1066_ = v___x_929_;
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_a_1064_);
lean_dec(v___x_929_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1071_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1069_; 
if (v_isShared_1067_ == 0)
{
v___x_1069_ = v___x_1066_;
goto v_reusejp_1068_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v_a_1064_);
v___x_1069_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1068_;
}
v_reusejp_1068_:
{
return v___x_1069_;
}
}
}
v___jp_926_:
{
lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_927_ = lean_box(0);
v___x_928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_928_, 0, v___x_927_);
return v___x_928_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___boxed(lean_object* v_e_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(v_e_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_, v_a_1080_, v_a_1081_, v_a_1082_);
lean_dec(v_a_1082_);
lean_dec_ref(v_a_1081_);
lean_dec(v_a_1080_);
lean_dec_ref(v_a_1079_);
lean_dec(v_a_1078_);
lean_dec_ref(v_a_1077_);
lean_dec(v_a_1076_);
lean_dec_ref(v_a_1075_);
lean_dec(v_a_1074_);
lean_dec(v_a_1073_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd_spec__0(lean_object* v_a_1085_){
_start:
{
lean_object* v___x_1086_; 
v___x_1086_ = lean_nat_to_int(v_a_1085_);
return v___x_1086_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3(void){
_start:
{
lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1092_ = lean_box(0);
v___x_1093_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2));
v___x_1094_ = l_Lean_mkConst(v___x_1093_, v___x_1092_);
return v___x_1094_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7(void){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1101_ = lean_box(0);
v___x_1102_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6));
v___x_1103_ = l_Lean_mkConst(v___x_1102_, v___x_1101_);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(lean_object* v_e_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_, lean_object* v_a_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_){
_start:
{
lean_object* v___x_1122_; uint8_t v___x_1123_; 
lean_inc_ref(v_e_1104_);
v___x_1122_ = l_Lean_Expr_cleanupAnnotations(v_e_1104_);
v___x_1123_ = l_Lean_Expr_isApp(v___x_1122_);
if (v___x_1123_ == 0)
{
lean_dec_ref(v___x_1122_);
lean_dec_ref(v_e_1104_);
goto v___jp_1116_;
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
lean_dec_ref(v_e_1104_);
goto v___jp_1116_;
}
else
{
lean_object* v_arg_1127_; lean_object* v___x_1128_; uint8_t v___x_1129_; 
v_arg_1127_ = lean_ctor_get(v___x_1125_, 1);
lean_inc_ref(v_arg_1127_);
v___x_1128_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1125_);
v___x_1129_ = l_Lean_Expr_isApp(v___x_1128_);
if (v___x_1129_ == 0)
{
lean_dec_ref(v___x_1128_);
lean_dec_ref(v_arg_1127_);
lean_dec_ref(v_arg_1124_);
lean_dec_ref(v_e_1104_);
goto v___jp_1116_;
}
else
{
lean_object* v_arg_1130_; lean_object* v___x_1131_; uint8_t v___x_1132_; 
v_arg_1130_ = lean_ctor_get(v___x_1128_, 1);
lean_inc_ref(v_arg_1130_);
v___x_1131_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1128_);
v___x_1132_ = l_Lean_Expr_isApp(v___x_1131_);
if (v___x_1132_ == 0)
{
lean_dec_ref(v___x_1131_);
lean_dec_ref(v_arg_1130_);
lean_dec_ref(v_arg_1127_);
lean_dec_ref(v_arg_1124_);
lean_dec_ref(v_e_1104_);
goto v___jp_1116_;
}
else
{
lean_object* v___x_1133_; lean_object* v___x_1134_; uint8_t v___x_1135_; 
v___x_1133_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1131_);
v___x_1134_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1135_ = l_Lean_Expr_isConstOf(v___x_1133_, v___x_1134_);
lean_dec_ref(v___x_1133_);
if (v___x_1135_ == 0)
{
lean_dec_ref(v_arg_1130_);
lean_dec_ref(v_arg_1127_);
lean_dec_ref(v_arg_1124_);
lean_dec_ref(v_e_1104_);
goto v___jp_1116_;
}
else
{
lean_object* v___x_1136_; 
v___x_1136_ = l_Lean_Meta_Structural_isInstDvdNat___redArg(v_arg_1130_, v_a_1112_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1268_; 
v_a_1137_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1139_ = v___x_1136_;
v_isShared_1140_ = v_isSharedCheck_1268_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1136_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1268_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
uint8_t v___x_1141_; 
v___x_1141_ = lean_unbox(v_a_1137_);
lean_dec(v_a_1137_);
if (v___x_1141_ == 0)
{
lean_object* v___x_1142_; lean_object* v___x_1144_; 
lean_dec_ref(v_arg_1127_);
lean_dec_ref(v_arg_1124_);
lean_dec_ref(v_e_1104_);
v___x_1142_ = lean_box(0);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 0, v___x_1142_);
v___x_1144_ = v___x_1139_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v___x_1142_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
else
{
lean_object* v___x_1146_; 
lean_del_object(v___x_1139_);
v___x_1146_ = l_Lean_Meta_getNatValue_x3f(v_arg_1127_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v_a_1147_; 
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
lean_inc(v_a_1147_);
lean_dec_ref_known(v___x_1146_, 1);
if (lean_obj_tag(v_a_1147_) == 1)
{
lean_object* v_val_1148_; lean_object* v___x_1149_; 
v_val_1148_ = lean_ctor_get(v_a_1147_, 0);
lean_inc(v_val_1148_);
lean_dec_ref_known(v_a_1147_, 1);
lean_inc_ref(v_e_1104_);
v___x_1149_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_1104_, v_a_1105_, v_a_1109_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v_a_1150_; uint8_t v___x_1151_; 
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
lean_inc(v_a_1150_);
lean_dec_ref_known(v___x_1149_, 1);
v___x_1151_ = lean_unbox(v_a_1150_);
lean_dec(v_a_1150_);
if (v___x_1151_ == 0)
{
lean_object* v___x_1152_; 
lean_dec(v_val_1148_);
lean_inc_ref(v_e_1104_);
v___x_1152_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_1104_, v_a_1105_, v_a_1109_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_);
if (lean_obj_tag(v___x_1152_) == 0)
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1177_; 
v_a_1153_ = lean_ctor_get(v___x_1152_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1155_ = v___x_1152_;
v_isShared_1156_ = v_isSharedCheck_1177_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1152_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1177_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
uint8_t v___x_1157_; 
v___x_1157_ = lean_unbox(v_a_1153_);
lean_dec(v_a_1153_);
if (v___x_1157_ == 0)
{
lean_object* v___x_1158_; lean_object* v___x_1160_; 
lean_dec_ref(v_arg_1127_);
lean_dec_ref(v_arg_1124_);
lean_dec_ref(v_e_1104_);
v___x_1158_ = lean_box(0);
if (v_isShared_1156_ == 0)
{
lean_ctor_set(v___x_1155_, 0, v___x_1158_);
v___x_1160_ = v___x_1155_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1158_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
else
{
lean_object* v___x_1162_; 
lean_del_object(v___x_1155_);
lean_inc_ref(v_e_1104_);
v___x_1162_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc(v_a_1163_);
lean_dec_ref_known(v___x_1162_, 1);
v___x_1164_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3);
v___x_1165_ = l_Lean_Meta_mkOfEqFalseCore(v_e_1104_, v_a_1163_);
v___x_1166_ = l_Lean_mkApp3(v___x_1164_, v_arg_1127_, v_arg_1124_, v___x_1165_);
v___x_1167_ = lean_unsigned_to_nat(0u);
v___x_1168_ = l_Lean_Meta_Grind_pushNewFact(v___x_1166_, v___x_1167_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_);
return v___x_1168_;
}
else
{
lean_object* v_a_1169_; lean_object* v___x_1171_; uint8_t v_isShared_1172_; uint8_t v_isSharedCheck_1176_; 
lean_dec_ref(v_arg_1127_);
lean_dec_ref(v_arg_1124_);
lean_dec_ref(v_e_1104_);
v_a_1169_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1176_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1171_ = v___x_1162_;
v_isShared_1172_ = v_isSharedCheck_1176_;
goto v_resetjp_1170_;
}
else
{
lean_inc(v_a_1169_);
lean_dec(v___x_1162_);
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
}
}
else
{
lean_object* v_a_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1185_; 
lean_dec_ref(v_arg_1127_);
lean_dec_ref(v_arg_1124_);
lean_dec_ref(v_e_1104_);
v_a_1178_ = lean_ctor_get(v___x_1152_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1180_ = v___x_1152_;
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_a_1178_);
lean_dec(v___x_1152_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1185_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v___x_1183_; 
if (v_isShared_1181_ == 0)
{
v___x_1183_ = v___x_1180_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_a_1178_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
else
{
lean_object* v___x_1186_; 
lean_inc_ref(v_arg_1127_);
v___x_1186_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_1127_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_);
if (lean_obj_tag(v___x_1186_) == 0)
{
lean_object* v_a_1187_; lean_object* v_fst_1188_; lean_object* v_snd_1189_; lean_object* v___x_1190_; 
v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
lean_inc(v_a_1187_);
lean_dec_ref_known(v___x_1186_, 1);
v_fst_1188_ = lean_ctor_get(v_a_1187_, 0);
lean_inc(v_fst_1188_);
v_snd_1189_ = lean_ctor_get(v_a_1187_, 1);
lean_inc(v_snd_1189_);
lean_dec(v_a_1187_);
lean_inc_ref(v_arg_1124_);
v___x_1190_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_1124_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_);
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_object* v_a_1191_; lean_object* v_fst_1192_; lean_object* v_snd_1193_; lean_object* v___x_1194_; 
v_a_1191_ = lean_ctor_get(v___x_1190_, 0);
lean_inc(v_a_1191_);
lean_dec_ref_known(v___x_1190_, 1);
v_fst_1192_ = lean_ctor_get(v_a_1191_, 0);
lean_inc(v_fst_1192_);
v_snd_1193_ = lean_ctor_get(v_a_1191_, 1);
lean_inc(v_snd_1193_);
lean_dec(v_a_1191_);
v___x_1194_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1104_, v_a_1105_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1195_; lean_object* v___x_1196_; 
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_a_1195_);
lean_dec_ref_known(v___x_1194_, 1);
lean_inc(v_fst_1192_);
v___x_1196_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_1192_, v_a_1195_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_object* v_a_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v_a_1197_ = lean_ctor_get(v___x_1196_, 0);
lean_inc(v_a_1197_);
lean_dec_ref_known(v___x_1196_, 1);
v___x_1198_ = l_Int_Internal_Linear_Expr_norm(v_a_1197_);
v___x_1199_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7);
v___x_1200_ = l_Lean_mkApp6(v___x_1199_, v_arg_1127_, v_arg_1124_, v_fst_1188_, v_fst_1192_, v_snd_1189_, v_snd_1193_);
lean_inc(v_val_1148_);
v___x_1201_ = lean_nat_to_int(v_val_1148_);
v___x_1202_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1202_, 0, v_e_1104_);
lean_ctor_set(v___x_1202_, 1, v___x_1200_);
lean_ctor_set(v___x_1202_, 2, v_val_1148_);
lean_ctor_set(v___x_1202_, 3, v_a_1197_);
v___x_1203_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1201_);
lean_ctor_set(v___x_1203_, 1, v___x_1198_);
lean_ctor_set(v___x_1203_, 2, v___x_1202_);
v___x_1204_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v___x_1203_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_);
return v___x_1204_;
}
else
{
lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1212_; 
lean_dec(v_snd_1193_);
lean_dec(v_fst_1192_);
lean_dec(v_snd_1189_);
lean_dec(v_fst_1188_);
lean_dec(v_val_1148_);
lean_dec_ref(v_arg_1127_);
lean_dec_ref(v_arg_1124_);
lean_dec_ref(v_e_1104_);
v_a_1205_ = lean_ctor_get(v___x_1196_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1207_ = v___x_1196_;
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_a_1205_);
lean_dec(v___x_1196_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1210_; 
if (v_isShared_1208_ == 0)
{
v___x_1210_ = v___x_1207_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_a_1205_);
v___x_1210_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
return v___x_1210_;
}
}
}
}
else
{
lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1220_; 
lean_dec(v_snd_1193_);
lean_dec(v_fst_1192_);
lean_dec(v_snd_1189_);
lean_dec(v_fst_1188_);
lean_dec(v_val_1148_);
lean_dec_ref(v_arg_1127_);
lean_dec_ref(v_arg_1124_);
lean_dec_ref(v_e_1104_);
v_a_1213_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1215_ = v___x_1194_;
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v___x_1194_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1218_; 
if (v_isShared_1216_ == 0)
{
v___x_1218_ = v___x_1215_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_a_1213_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
}
else
{
lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1228_; 
lean_dec(v_snd_1189_);
lean_dec(v_fst_1188_);
lean_dec(v_val_1148_);
lean_dec_ref(v_arg_1127_);
lean_dec_ref(v_arg_1124_);
lean_dec_ref(v_e_1104_);
v_a_1221_ = lean_ctor_get(v___x_1190_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1190_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1223_ = v___x_1190_;
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1190_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___x_1226_; 
if (v_isShared_1224_ == 0)
{
v___x_1226_ = v___x_1223_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_a_1221_);
v___x_1226_ = v_reuseFailAlloc_1227_;
goto v_reusejp_1225_;
}
v_reusejp_1225_:
{
return v___x_1226_;
}
}
}
}
else
{
lean_object* v_a_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1236_; 
lean_dec(v_val_1148_);
lean_dec_ref(v_arg_1127_);
lean_dec_ref(v_arg_1124_);
lean_dec_ref(v_e_1104_);
v_a_1229_ = lean_ctor_get(v___x_1186_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1186_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1231_ = v___x_1186_;
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1186_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v___x_1234_; 
if (v_isShared_1232_ == 0)
{
v___x_1234_ = v___x_1231_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1235_; 
v_reuseFailAlloc_1235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1235_, 0, v_a_1229_);
v___x_1234_ = v_reuseFailAlloc_1235_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
return v___x_1234_;
}
}
}
}
}
else
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1244_; 
lean_dec(v_val_1148_);
lean_dec_ref(v_arg_1127_);
lean_dec_ref(v_arg_1124_);
lean_dec_ref(v_e_1104_);
v_a_1237_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1239_ = v___x_1149_;
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v___x_1149_);
v___x_1239_ = lean_box(0);
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
v_resetjp_1238_:
{
lean_object* v___x_1242_; 
if (v_isShared_1240_ == 0)
{
v___x_1242_ = v___x_1239_;
goto v_reusejp_1241_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_a_1237_);
v___x_1242_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1241_;
}
v_reusejp_1241_:
{
return v___x_1242_;
}
}
}
}
else
{
lean_object* v___x_1245_; 
lean_dec(v_a_1147_);
lean_dec_ref(v_arg_1127_);
lean_dec_ref(v_arg_1124_);
v___x_1245_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1109_);
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v_a_1246_; uint8_t v_verbose_1247_; 
v_a_1246_ = lean_ctor_get(v___x_1245_, 0);
lean_inc(v_a_1246_);
lean_dec_ref_known(v___x_1245_, 1);
v_verbose_1247_ = lean_ctor_get_uint8(v_a_1246_, 0);
lean_dec(v_a_1246_);
if (v_verbose_1247_ == 0)
{
lean_dec_ref(v_e_1104_);
goto v___jp_1119_;
}
else
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; 
v___x_1248_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10);
v___x_1249_ = l_Lean_indentExpr(v_e_1104_);
v___x_1250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1250_, 0, v___x_1248_);
lean_ctor_set(v___x_1250_, 1, v___x_1249_);
v___x_1251_ = l_Lean_Meta_Sym_reportIssue(v___x_1250_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_dec_ref_known(v___x_1251_, 1);
goto v___jp_1119_;
}
else
{
return v___x_1251_;
}
}
}
else
{
lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1259_; 
lean_dec_ref(v_e_1104_);
v_a_1252_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1254_ = v___x_1245_;
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_dec(v___x_1245_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1257_; 
if (v_isShared_1255_ == 0)
{
v___x_1257_ = v___x_1254_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_a_1252_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
}
}
else
{
lean_object* v_a_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1267_; 
lean_dec_ref(v_arg_1127_);
lean_dec_ref(v_arg_1124_);
lean_dec_ref(v_e_1104_);
v_a_1260_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1262_ = v___x_1146_;
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_a_1260_);
lean_dec(v___x_1146_);
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
else
{
lean_object* v_a_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1276_; 
lean_dec_ref(v_arg_1127_);
lean_dec_ref(v_arg_1124_);
lean_dec_ref(v_e_1104_);
v_a_1269_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1271_ = v___x_1136_;
v_isShared_1272_ = v_isSharedCheck_1276_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_a_1269_);
lean_dec(v___x_1136_);
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
}
}
}
}
v___jp_1116_:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = lean_box(0);
v___x_1118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1117_);
return v___x_1118_;
}
v___jp_1119_:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1120_ = lean_box(0);
v___x_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1121_, 0, v___x_1120_);
return v___x_1121_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___boxed(lean_object* v_e_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(v_e_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_);
lean_dec(v_a_1287_);
lean_dec_ref(v_a_1286_);
lean_dec(v_a_1285_);
lean_dec_ref(v_a_1284_);
lean_dec(v_a_1283_);
lean_dec_ref(v_a_1282_);
lean_dec(v_a_1281_);
lean_dec_ref(v_a_1280_);
lean_dec(v_a_1279_);
lean_dec(v_a_1278_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(lean_object* v_e_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_){
_start:
{
lean_object* v___x_1304_; 
v___x_1304_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1295_);
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_object* v_a_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1349_; 
v_a_1305_ = lean_ctor_get(v___x_1304_, 0);
v_isSharedCheck_1349_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1349_ == 0)
{
v___x_1307_ = v___x_1304_;
v_isShared_1308_ = v_isSharedCheck_1349_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_a_1305_);
lean_dec(v___x_1304_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1349_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
uint8_t v_lia_1309_; 
v_lia_1309_ = lean_ctor_get_uint8(v_a_1305_, sizeof(void*)*14 + 23);
lean_dec(v_a_1305_);
if (v_lia_1309_ == 0)
{
lean_object* v___x_1310_; lean_object* v___x_1312_; 
lean_dec_ref(v_e_1292_);
v___x_1310_ = lean_box(0);
if (v_isShared_1308_ == 0)
{
lean_ctor_set(v___x_1307_, 0, v___x_1310_);
v___x_1312_ = v___x_1307_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v___x_1310_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
else
{
lean_object* v___x_1314_; 
lean_del_object(v___x_1307_);
lean_inc_ref(v_e_1292_);
v___x_1314_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1292_, v_a_1300_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1340_; 
v_a_1315_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1317_ = v___x_1314_;
v_isShared_1318_ = v_isSharedCheck_1340_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_dec(v___x_1314_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1340_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1324_; uint8_t v___x_1325_; 
v___x_1324_ = l_Lean_Expr_cleanupAnnotations(v_a_1315_);
v___x_1325_ = l_Lean_Expr_isApp(v___x_1324_);
if (v___x_1325_ == 0)
{
lean_dec_ref(v___x_1324_);
lean_dec_ref(v_e_1292_);
goto v___jp_1319_;
}
else
{
lean_object* v___x_1326_; uint8_t v___x_1327_; 
v___x_1326_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1324_);
v___x_1327_ = l_Lean_Expr_isApp(v___x_1326_);
if (v___x_1327_ == 0)
{
lean_dec_ref(v___x_1326_);
lean_dec_ref(v_e_1292_);
goto v___jp_1319_;
}
else
{
lean_object* v___x_1328_; uint8_t v___x_1329_; 
v___x_1328_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1326_);
v___x_1329_ = l_Lean_Expr_isApp(v___x_1328_);
if (v___x_1329_ == 0)
{
lean_dec_ref(v___x_1328_);
lean_dec_ref(v_e_1292_);
goto v___jp_1319_;
}
else
{
lean_object* v___x_1330_; uint8_t v___x_1331_; 
v___x_1330_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1328_);
v___x_1331_ = l_Lean_Expr_isApp(v___x_1330_);
if (v___x_1331_ == 0)
{
lean_dec_ref(v___x_1330_);
lean_dec_ref(v_e_1292_);
goto v___jp_1319_;
}
else
{
lean_object* v_arg_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; uint8_t v___x_1335_; 
v_arg_1332_ = lean_ctor_get(v___x_1330_, 1);
lean_inc_ref(v_arg_1332_);
v___x_1333_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1330_);
v___x_1334_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1335_ = l_Lean_Expr_isConstOf(v___x_1333_, v___x_1334_);
lean_dec_ref(v___x_1333_);
if (v___x_1335_ == 0)
{
lean_dec_ref(v_arg_1332_);
lean_dec_ref(v_e_1292_);
goto v___jp_1319_;
}
else
{
lean_object* v___x_1336_; uint8_t v___x_1337_; 
lean_del_object(v___x_1317_);
v___x_1336_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0));
v___x_1337_ = l_Lean_Expr_isConstOf(v_arg_1332_, v___x_1336_);
lean_dec_ref(v_arg_1332_);
if (v___x_1337_ == 0)
{
lean_object* v___x_1338_; 
v___x_1338_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(v_e_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_);
return v___x_1338_;
}
else
{
lean_object* v___x_1339_; 
v___x_1339_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(v_e_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_, v_a_1301_, v_a_1302_);
return v___x_1339_;
}
}
}
}
}
}
v___jp_1319_:
{
lean_object* v___x_1320_; lean_object* v___x_1322_; 
v___x_1320_ = lean_box(0);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 0, v___x_1320_);
v___x_1322_ = v___x_1317_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1320_);
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
else
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1348_; 
lean_dec_ref(v_e_1292_);
v_a_1341_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1343_ = v___x_1314_;
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1314_);
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
}
else
{
lean_object* v_a_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1357_; 
lean_dec_ref(v_e_1292_);
v_a_1350_ = lean_ctor_get(v___x_1304_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1352_ = v___x_1304_;
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_a_1350_);
lean_dec(v___x_1304_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1357_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1355_; 
if (v_isShared_1353_ == 0)
{
v___x_1355_ = v___x_1352_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_a_1350_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed(lean_object* v_e_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_){
_start:
{
lean_object* v_res_1370_; 
v_res_1370_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(v_e_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_, v_a_1366_, v_a_1367_, v_a_1368_);
lean_dec(v_a_1368_);
lean_dec_ref(v_a_1367_);
lean_dec(v_a_1366_);
lean_dec_ref(v_a_1365_);
lean_dec(v_a_1364_);
lean_dec_ref(v_a_1363_);
lean_dec(v_a_1362_);
lean_dec_ref(v_a_1361_);
lean_dec(v_a_1360_);
lean_dec(v_a_1359_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; 
v___x_1372_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1373_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed), 12, 0);
v___x_1374_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_1372_, v___x_1373_);
return v___x_1374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_9____boxed(lean_object* v_a_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_9_();
return v_res_1376_;
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
