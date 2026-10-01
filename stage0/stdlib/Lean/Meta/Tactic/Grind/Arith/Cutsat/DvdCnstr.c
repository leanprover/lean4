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
lean_object* l_Lean_PersistentArray_set___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqLBool_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(lean_object*, lean_object*);
lean_object* lean_grind_cutsat_assert_eq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
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
lean_object* v___x_41_; lean_object* v_env_42_; lean_object* v___x_43_; lean_object* v_toCold_44_; lean_object* v_mctx_45_; lean_object* v_lctx_46_; lean_object* v_options_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_41_ = lean_st_ref_get(v___y_39_);
v_env_42_ = lean_ctor_get(v___x_41_, 0);
lean_inc_ref(v_env_42_);
lean_dec(v___x_41_);
v___x_43_ = lean_st_ref_get(v___y_37_);
v_toCold_44_ = lean_ctor_get(v___y_38_, 0);
v_mctx_45_ = lean_ctor_get(v___x_43_, 0);
lean_inc_ref(v_mctx_45_);
lean_dec(v___x_43_);
v_lctx_46_ = lean_ctor_get(v___y_36_, 2);
v_options_47_ = lean_ctor_get(v_toCold_44_, 2);
lean_inc_ref(v_options_47_);
lean_inc_ref(v_lctx_46_);
v___x_48_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_48_, 0, v_env_42_);
lean_ctor_set(v___x_48_, 1, v_mctx_45_);
lean_ctor_set(v___x_48_, 2, v_lctx_46_);
lean_ctor_set(v___x_48_, 3, v_options_47_);
v___x_49_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_49_, 0, v___x_48_);
lean_ctor_set(v___x_49_, 1, v_msgData_35_);
v___x_50_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_50_, 0, v___x_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0_spec__0___boxed(lean_object* v_msgData_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0_spec__0(v_msgData_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
return v_res_57_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_58_; double v___x_59_; 
v___x_58_ = lean_unsigned_to_nat(0u);
v___x_59_ = lean_float_of_nat(v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(lean_object* v_cls_63_, lean_object* v_msg_64_, lean_object* v___y_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_){
_start:
{
lean_object* v_ref_70_; lean_object* v___x_71_; lean_object* v_a_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_117_; 
v_ref_70_ = lean_ctor_get(v___y_67_, 2);
v___x_71_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0_spec__0(v_msg_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_);
v_a_72_ = lean_ctor_get(v___x_71_, 0);
v_isSharedCheck_117_ = !lean_is_exclusive(v___x_71_);
if (v_isSharedCheck_117_ == 0)
{
v___x_74_ = v___x_71_;
v_isShared_75_ = v_isSharedCheck_117_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_a_72_);
lean_dec(v___x_71_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_117_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
lean_object* v___x_76_; lean_object* v_traceState_77_; lean_object* v_env_78_; lean_object* v_nextMacroScope_79_; lean_object* v_ngen_80_; lean_object* v_auxDeclNGen_81_; lean_object* v_cache_82_; lean_object* v_recordedDeps_83_; lean_object* v_messages_84_; lean_object* v_infoState_85_; lean_object* v_snapshotTasks_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_116_; 
v___x_76_ = lean_st_ref_take(v___y_68_);
v_traceState_77_ = lean_ctor_get(v___x_76_, 4);
v_env_78_ = lean_ctor_get(v___x_76_, 0);
v_nextMacroScope_79_ = lean_ctor_get(v___x_76_, 1);
v_ngen_80_ = lean_ctor_get(v___x_76_, 2);
v_auxDeclNGen_81_ = lean_ctor_get(v___x_76_, 3);
v_cache_82_ = lean_ctor_get(v___x_76_, 5);
v_recordedDeps_83_ = lean_ctor_get(v___x_76_, 6);
v_messages_84_ = lean_ctor_get(v___x_76_, 7);
v_infoState_85_ = lean_ctor_get(v___x_76_, 8);
v_snapshotTasks_86_ = lean_ctor_get(v___x_76_, 9);
v_isSharedCheck_116_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_116_ == 0)
{
v___x_88_ = v___x_76_;
v_isShared_89_ = v_isSharedCheck_116_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_snapshotTasks_86_);
lean_inc(v_infoState_85_);
lean_inc(v_messages_84_);
lean_inc(v_recordedDeps_83_);
lean_inc(v_cache_82_);
lean_inc(v_traceState_77_);
lean_inc(v_auxDeclNGen_81_);
lean_inc(v_ngen_80_);
lean_inc(v_nextMacroScope_79_);
lean_inc(v_env_78_);
lean_dec(v___x_76_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_116_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
uint64_t v_tid_90_; lean_object* v_traces_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_115_; 
v_tid_90_ = lean_ctor_get_uint64(v_traceState_77_, sizeof(void*)*1);
v_traces_91_ = lean_ctor_get(v_traceState_77_, 0);
v_isSharedCheck_115_ = !lean_is_exclusive(v_traceState_77_);
if (v_isSharedCheck_115_ == 0)
{
v___x_93_ = v_traceState_77_;
v_isShared_94_ = v_isSharedCheck_115_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_traces_91_);
lean_dec(v_traceState_77_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_115_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___x_95_; lean_object* v___x_96_; double v___x_97_; uint8_t v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_106_; 
v___x_95_ = lean_box(0);
v___x_96_ = lean_box(0);
v___x_97_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0);
v___x_98_ = 0;
v___x_99_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__1));
v___x_100_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_100_, 0, v_cls_63_);
lean_ctor_set(v___x_100_, 1, v___x_96_);
lean_ctor_set(v___x_100_, 2, v___x_99_);
lean_ctor_set_float(v___x_100_, sizeof(void*)*3, v___x_97_);
lean_ctor_set_float(v___x_100_, sizeof(void*)*3 + 8, v___x_97_);
lean_ctor_set_uint8(v___x_100_, sizeof(void*)*3 + 16, v___x_98_);
v___x_101_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__2));
v___x_102_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_102_, 0, v___x_100_);
lean_ctor_set(v___x_102_, 1, v_a_72_);
lean_ctor_set(v___x_102_, 2, v___x_101_);
lean_inc(v_ref_70_);
v___x_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_103_, 0, v_ref_70_);
lean_ctor_set(v___x_103_, 1, v___x_102_);
v___x_104_ = l_Lean_PersistentArray_push___redArg(v_traces_91_, v___x_103_);
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 0, v___x_104_);
v___x_106_ = v___x_93_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v___x_104_);
lean_ctor_set_uint64(v_reuseFailAlloc_114_, sizeof(void*)*1, v_tid_90_);
v___x_106_ = v_reuseFailAlloc_114_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
lean_object* v___x_108_; 
if (v_isShared_89_ == 0)
{
lean_ctor_set(v___x_88_, 4, v___x_106_);
v___x_108_ = v___x_88_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v_env_78_);
lean_ctor_set(v_reuseFailAlloc_113_, 1, v_nextMacroScope_79_);
lean_ctor_set(v_reuseFailAlloc_113_, 2, v_ngen_80_);
lean_ctor_set(v_reuseFailAlloc_113_, 3, v_auxDeclNGen_81_);
lean_ctor_set(v_reuseFailAlloc_113_, 4, v___x_106_);
lean_ctor_set(v_reuseFailAlloc_113_, 5, v_cache_82_);
lean_ctor_set(v_reuseFailAlloc_113_, 6, v_recordedDeps_83_);
lean_ctor_set(v_reuseFailAlloc_113_, 7, v_messages_84_);
lean_ctor_set(v_reuseFailAlloc_113_, 8, v_infoState_85_);
lean_ctor_set(v_reuseFailAlloc_113_, 9, v_snapshotTasks_86_);
v___x_108_ = v_reuseFailAlloc_113_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
lean_object* v___x_109_; lean_object* v___x_111_; 
v___x_109_ = lean_st_ref_put(v___y_68_, v___x_108_);
if (v_isShared_75_ == 0)
{
lean_ctor_set(v___x_74_, 0, v___x_95_);
v___x_111_ = v___x_74_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v___x_95_);
v___x_111_ = v_reuseFailAlloc_112_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
return v___x_111_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___boxed(lean_object* v_cls_118_, lean_object* v_msg_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v_cls_118_, v_msg_119_, v___y_120_, v___y_121_, v___y_122_, v___y_123_);
lean_dec(v___y_123_);
lean_dec_ref(v___y_122_);
lean_dec(v___y_121_);
lean_dec_ref(v___y_120_);
return v_res_125_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7(void){
_start:
{
lean_object* v_cls_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v_cls_138_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4));
v___x_139_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
v___x_140_ = l_Lean_Name_append(v___x_139_, v_cls_138_);
return v___x_140_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__8));
v___x_143_ = l_Lean_stringToMessageData(v___x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(lean_object* v_a_144_, lean_object* v_x_145_, lean_object* v_c_u2081_146_, lean_object* v_b_147_, lean_object* v_c_u2082_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_){
_start:
{
lean_object* v_toCold_160_; lean_object* v_options_161_; lean_object* v_p_162_; lean_object* v_d_163_; lean_object* v_p_164_; lean_object* v_inheritedTraceOptions_165_; uint8_t v_hasTrace_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v_d_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v_p_173_; 
v_toCold_160_ = lean_ctor_get(v_a_157_, 0);
v_options_161_ = lean_ctor_get(v_toCold_160_, 2);
v_p_162_ = lean_ctor_get(v_c_u2081_146_, 0);
v_d_163_ = lean_ctor_get(v_c_u2082_148_, 0);
v_p_164_ = lean_ctor_get(v_c_u2082_148_, 1);
v_inheritedTraceOptions_165_ = lean_ctor_get(v_toCold_160_, 11);
v_hasTrace_166_ = lean_ctor_get_uint8(v_options_161_, sizeof(void*)*1);
v___x_167_ = lean_int_mul(v_a_144_, v_d_163_);
v___x_168_ = lean_nat_abs(v___x_167_);
lean_dec(v___x_167_);
v_d_169_ = lean_nat_to_int(v___x_168_);
lean_inc_ref(v_p_164_);
v___x_170_ = l_Int_Internal_Linear_Poly_mul(v_p_164_, v_a_144_);
v___x_171_ = lean_int_neg(v_b_147_);
lean_inc_ref(v_p_162_);
v___x_172_ = l_Int_Internal_Linear_Poly_mul(v_p_162_, v___x_171_);
lean_dec(v___x_171_);
v_p_173_ = l_Int_Internal_Linear_Poly_combine(v___x_170_, v___x_172_);
if (v_hasTrace_166_ == 0)
{
goto v___jp_174_;
}
else
{
lean_object* v_cls_178_; lean_object* v___x_179_; uint8_t v___x_180_; 
v_cls_178_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4));
v___x_179_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7);
v___x_180_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_165_, v_options_161_, v___x_179_);
if (v___x_180_ == 0)
{
goto v___jp_174_;
}
else
{
lean_object* v___x_181_; 
v___x_181_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_x_145_, v_a_149_, v_a_157_);
if (lean_obj_tag(v___x_181_) == 0)
{
lean_object* v_a_182_; lean_object* v___x_183_; 
v_a_182_ = lean_ctor_get(v___x_181_, 0);
lean_inc(v_a_182_);
lean_dec_ref_known(v___x_181_, 1);
lean_inc_ref(v_c_u2081_146_);
v___x_183_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_u2081_146_, v_a_149_, v_a_157_);
if (lean_obj_tag(v___x_183_) == 0)
{
lean_object* v_a_184_; lean_object* v___x_185_; 
v_a_184_ = lean_ctor_get(v___x_183_, 0);
lean_inc(v_a_184_);
lean_dec_ref_known(v___x_183_, 1);
lean_inc_ref(v_c_u2082_148_);
v___x_185_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_u2082_148_, v_a_149_, v_a_157_);
if (lean_obj_tag(v___x_185_) == 0)
{
lean_object* v_a_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; 
v_a_186_ = lean_ctor_get(v___x_185_, 0);
lean_inc(v_a_186_);
lean_dec_ref_known(v___x_185_, 1);
v___x_187_ = l_Lean_MessageData_ofExpr(v_a_182_);
v___x_188_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9);
v___x_189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_187_);
lean_ctor_set(v___x_189_, 1, v___x_188_);
v___x_190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
lean_ctor_set(v___x_190_, 1, v_a_184_);
v___x_191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
lean_ctor_set(v___x_191_, 1, v___x_188_);
v___x_192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v_a_186_);
v___x_193_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v_cls_178_, v___x_192_, v_a_155_, v_a_156_, v_a_157_, v_a_158_);
if (lean_obj_tag(v___x_193_) == 0)
{
lean_dec_ref_known(v___x_193_, 1);
goto v___jp_174_;
}
else
{
lean_object* v_a_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_201_; 
lean_dec_ref(v_p_173_);
lean_dec(v_d_169_);
lean_dec_ref(v_c_u2082_148_);
lean_dec_ref(v_c_u2081_146_);
lean_dec(v_x_145_);
v_a_194_ = lean_ctor_get(v___x_193_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_201_ == 0)
{
v___x_196_ = v___x_193_;
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_a_194_);
lean_dec(v___x_193_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_199_; 
if (v_isShared_197_ == 0)
{
v___x_199_ = v___x_196_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_a_194_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
}
else
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_209_; 
lean_dec(v_a_184_);
lean_dec(v_a_182_);
lean_dec_ref(v_p_173_);
lean_dec(v_d_169_);
lean_dec_ref(v_c_u2082_148_);
lean_dec_ref(v_c_u2081_146_);
lean_dec(v_x_145_);
v_a_202_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_209_ == 0)
{
v___x_204_ = v___x_185_;
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_185_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; 
if (v_isShared_205_ == 0)
{
v___x_207_ = v___x_204_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_a_202_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
}
else
{
lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_217_; 
lean_dec(v_a_182_);
lean_dec_ref(v_p_173_);
lean_dec(v_d_169_);
lean_dec_ref(v_c_u2082_148_);
lean_dec_ref(v_c_u2081_146_);
lean_dec(v_x_145_);
v_a_210_ = lean_ctor_get(v___x_183_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_183_);
if (v_isSharedCheck_217_ == 0)
{
v___x_212_ = v___x_183_;
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v___x_183_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_215_; 
if (v_isShared_213_ == 0)
{
v___x_215_ = v___x_212_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_a_210_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
}
else
{
lean_object* v_a_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_225_; 
lean_dec_ref(v_p_173_);
lean_dec(v_d_169_);
lean_dec_ref(v_c_u2082_148_);
lean_dec_ref(v_c_u2081_146_);
lean_dec(v_x_145_);
v_a_218_ = lean_ctor_get(v___x_181_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_225_ == 0)
{
v___x_220_ = v___x_181_;
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_a_218_);
lean_dec(v___x_181_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_223_; 
if (v_isShared_221_ == 0)
{
v___x_223_ = v___x_220_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_a_218_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
}
}
v___jp_174_:
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_175_ = lean_alloc_ctor(8, 3, 0);
lean_ctor_set(v___x_175_, 0, v_x_145_);
lean_ctor_set(v___x_175_, 1, v_c_u2081_146_);
lean_ctor_set(v___x_175_, 2, v_c_u2082_148_);
v___x_176_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_176_, 0, v_d_169_);
lean_ctor_set(v___x_176_, 1, v_p_173_);
lean_ctor_set(v___x_176_, 2, v___x_175_);
v___x_177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
return v___x_177_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___boxed(lean_object* v_a_226_, lean_object* v_x_227_, lean_object* v_c_u2081_228_, lean_object* v_b_229_, lean_object* v_c_u2082_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_){
_start:
{
lean_object* v_res_242_; 
v_res_242_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(v_a_226_, v_x_227_, v_c_u2081_228_, v_b_229_, v_c_u2082_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_);
lean_dec(v_a_240_);
lean_dec_ref(v_a_239_);
lean_dec(v_a_238_);
lean_dec_ref(v_a_237_);
lean_dec(v_a_236_);
lean_dec_ref(v_a_235_);
lean_dec(v_a_234_);
lean_dec_ref(v_a_233_);
lean_dec(v_a_232_);
lean_dec(v_a_231_);
lean_dec(v_b_229_);
lean_dec(v_a_226_);
return v_res_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0(lean_object* v_cls_243_, lean_object* v_msg_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v_cls_243_, v_msg_244_, v___y_251_, v___y_252_, v___y_253_, v___y_254_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___boxed(lean_object* v_cls_257_, lean_object* v_msg_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0(v_cls_257_, v_msg_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
lean_dec(v___y_260_);
lean_dec(v___y_259_);
return v_res_270_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = l_Lean_maxRecDepthErrorMessage;
v___x_277_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
return v___x_277_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_278_; lean_object* v___x_279_; 
v___x_278_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3);
v___x_279_ = l_Lean_MessageData_ofFormat(v___x_278_);
return v___x_279_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_280_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4);
v___x_281_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2));
v___x_282_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
lean_ctor_set(v___x_282_, 1, v___x_280_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(lean_object* v_ref_283_){
_start:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_285_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5);
v___x_286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_286_, 0, v_ref_283_);
lean_ctor_set(v___x_286_, 1, v___x_285_);
v___x_287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___boxed(lean_object* v_ref_288_, lean_object* v___y_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_288_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0(lean_object* v_00_u03b1_291_, lean_object* v_ref_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_292_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___boxed(lean_object* v_00_u03b1_305_, lean_object* v_ref_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0(v_00_u03b1_305_, v_ref_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
lean_dec(v___y_314_);
lean_dec_ref(v___y_313_);
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
lean_dec(v___y_310_);
lean_dec_ref(v___y_309_);
lean_dec(v___y_308_);
lean_dec(v___y_307_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(lean_object* v_c_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_){
_start:
{
lean_object* v_p_331_; lean_object* v_toCold_332_; lean_object* v_currRecDepth_333_; lean_object* v_ref_334_; uint16_t v_optionFlags_335_; uint8_t v_suppressElabErrors_336_; uint8_t v_isRecordingDeps_337_; lean_object* v_maxRecDepth_369_; lean_object* v___x_370_; uint8_t v___x_371_; 
v_p_331_ = lean_ctor_get(v_c_319_, 1);
v_toCold_332_ = lean_ctor_get(v_a_328_, 0);
lean_inc_ref(v_toCold_332_);
v_currRecDepth_333_ = lean_ctor_get(v_a_328_, 1);
lean_inc(v_currRecDepth_333_);
v_ref_334_ = lean_ctor_get(v_a_328_, 2);
lean_inc(v_ref_334_);
v_optionFlags_335_ = lean_ctor_get_uint16(v_a_328_, sizeof(void*)*3);
v_suppressElabErrors_336_ = lean_ctor_get_uint8(v_a_328_, sizeof(void*)*3 + 2);
v_isRecordingDeps_337_ = lean_ctor_get_uint8(v_a_328_, sizeof(void*)*3 + 3);
lean_dec_ref(v_a_328_);
v_maxRecDepth_369_ = lean_ctor_get(v_toCold_332_, 3);
v___x_370_ = lean_unsigned_to_nat(0u);
v___x_371_ = lean_nat_dec_eq(v_maxRecDepth_369_, v___x_370_);
if (v___x_371_ == 0)
{
uint8_t v___x_372_; 
v___x_372_ = lean_nat_dec_eq(v_currRecDepth_333_, v_maxRecDepth_369_);
if (v___x_372_ == 0)
{
goto v___jp_338_;
}
else
{
lean_object* v___x_373_; 
lean_dec(v_currRecDepth_333_);
lean_dec_ref(v_toCold_332_);
lean_dec_ref(v_c_319_);
v___x_373_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_334_);
return v___x_373_;
}
}
else
{
goto v___jp_338_;
}
v___jp_338_:
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_339_ = lean_unsigned_to_nat(1u);
v___x_340_ = lean_nat_add(v_currRecDepth_333_, v___x_339_);
lean_dec(v_currRecDepth_333_);
v___x_341_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_341_, 0, v_toCold_332_);
lean_ctor_set(v___x_341_, 1, v___x_340_);
lean_ctor_set(v___x_341_, 2, v_ref_334_);
lean_ctor_set_uint16(v___x_341_, sizeof(void*)*3, v_optionFlags_335_);
lean_ctor_set_uint8(v___x_341_, sizeof(void*)*3 + 2, v_suppressElabErrors_336_);
lean_ctor_set_uint8(v___x_341_, sizeof(void*)*3 + 3, v_isRecordingDeps_337_);
lean_inc_ref(v_p_331_);
v___x_342_ = l_Int_Internal_Linear_Poly_findVarToSubst___redArg(v_p_331_, v_a_320_, v___x_341_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_a_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_360_; 
v_a_343_ = lean_ctor_get(v___x_342_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_360_ == 0)
{
v___x_345_ = v___x_342_;
v_isShared_346_ = v_isSharedCheck_360_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_a_343_);
lean_dec(v___x_342_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_360_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
if (lean_obj_tag(v_a_343_) == 1)
{
lean_object* v_val_347_; lean_object* v_snd_348_; lean_object* v_snd_349_; lean_object* v_fst_350_; lean_object* v_fst_351_; lean_object* v_p_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
lean_del_object(v___x_345_);
v_val_347_ = lean_ctor_get(v_a_343_, 0);
lean_inc(v_val_347_);
lean_dec_ref_known(v_a_343_, 1);
v_snd_348_ = lean_ctor_get(v_val_347_, 1);
lean_inc(v_snd_348_);
v_snd_349_ = lean_ctor_get(v_snd_348_, 1);
lean_inc(v_snd_349_);
v_fst_350_ = lean_ctor_get(v_val_347_, 0);
lean_inc(v_fst_350_);
lean_dec(v_val_347_);
v_fst_351_ = lean_ctor_get(v_snd_348_, 0);
lean_inc(v_fst_351_);
lean_dec(v_snd_348_);
v_p_352_ = lean_ctor_get(v_snd_349_, 0);
v___x_353_ = l_Int_Internal_Linear_Poly_coeff(v_p_352_, v_fst_351_);
v___x_354_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(v___x_353_, v_fst_351_, v_snd_349_, v_fst_350_, v_c_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v___x_341_, v_a_329_);
lean_dec(v_fst_350_);
lean_dec(v___x_353_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v_a_355_; 
v_a_355_ = lean_ctor_get(v___x_354_, 0);
lean_inc(v_a_355_);
lean_dec_ref_known(v___x_354_, 1);
v_c_319_ = v_a_355_;
v_a_328_ = v___x_341_;
goto _start;
}
else
{
lean_dec_ref_known(v___x_341_, 3);
return v___x_354_;
}
}
else
{
lean_object* v___x_358_; 
lean_dec(v_a_343_);
lean_dec_ref_known(v___x_341_, 3);
if (v_isShared_346_ == 0)
{
lean_ctor_set(v___x_345_, 0, v_c_319_);
v___x_358_ = v___x_345_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_c_319_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
}
else
{
lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_368_; 
lean_dec_ref_known(v___x_341_, 3);
lean_dec_ref(v_c_319_);
v_a_361_ = lean_ctor_get(v___x_342_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_368_ == 0)
{
v___x_363_ = v___x_342_;
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v___x_342_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_366_; 
if (v_isShared_364_ == 0)
{
v___x_366_ = v___x_363_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_a_361_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___boxed(lean_object* v_c_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(v_c_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_);
lean_dec(v_a_384_);
lean_dec(v_a_382_);
lean_dec_ref(v_a_381_);
lean_dec(v_a_380_);
lean_dec_ref(v_a_379_);
lean_dec(v_a_378_);
lean_dec_ref(v_a_377_);
lean_dec(v_a_376_);
lean_dec(v_a_375_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(lean_object* v_a_387_, lean_object* v_v_388_, lean_object* v_s_389_){
_start:
{
lean_object* v_vars_390_; lean_object* v_varMap_391_; lean_object* v_varsHistory_392_; lean_object* v_natToIntMap_393_; lean_object* v_natDef_394_; lean_object* v_dvds_395_; lean_object* v_lowers_396_; lean_object* v_uppers_397_; lean_object* v_diseqs_398_; lean_object* v_elimEqs_399_; lean_object* v_elimStack_400_; lean_object* v_occurs_401_; lean_object* v_assignment_402_; lean_object* v_nextCnstrId_403_; uint8_t v_caseSplits_404_; lean_object* v_steps_405_; lean_object* v_conflict_x3f_406_; lean_object* v_diseqSplits_407_; lean_object* v_divMod_408_; uint8_t v_usedCommRing_409_; lean_object* v_nonlinearOccs_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_419_; 
v_vars_390_ = lean_ctor_get(v_s_389_, 0);
v_varMap_391_ = lean_ctor_get(v_s_389_, 1);
v_varsHistory_392_ = lean_ctor_get(v_s_389_, 2);
v_natToIntMap_393_ = lean_ctor_get(v_s_389_, 3);
v_natDef_394_ = lean_ctor_get(v_s_389_, 4);
v_dvds_395_ = lean_ctor_get(v_s_389_, 5);
v_lowers_396_ = lean_ctor_get(v_s_389_, 6);
v_uppers_397_ = lean_ctor_get(v_s_389_, 7);
v_diseqs_398_ = lean_ctor_get(v_s_389_, 8);
v_elimEqs_399_ = lean_ctor_get(v_s_389_, 9);
v_elimStack_400_ = lean_ctor_get(v_s_389_, 10);
v_occurs_401_ = lean_ctor_get(v_s_389_, 11);
v_assignment_402_ = lean_ctor_get(v_s_389_, 12);
v_nextCnstrId_403_ = lean_ctor_get(v_s_389_, 13);
v_caseSplits_404_ = lean_ctor_get_uint8(v_s_389_, sizeof(void*)*19);
v_steps_405_ = lean_ctor_get(v_s_389_, 14);
v_conflict_x3f_406_ = lean_ctor_get(v_s_389_, 15);
v_diseqSplits_407_ = lean_ctor_get(v_s_389_, 16);
v_divMod_408_ = lean_ctor_get(v_s_389_, 17);
v_usedCommRing_409_ = lean_ctor_get_uint8(v_s_389_, sizeof(void*)*19 + 1);
v_nonlinearOccs_410_ = lean_ctor_get(v_s_389_, 18);
v_isSharedCheck_419_ = !lean_is_exclusive(v_s_389_);
if (v_isSharedCheck_419_ == 0)
{
v___x_412_ = v_s_389_;
v_isShared_413_ = v_isSharedCheck_419_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_nonlinearOccs_410_);
lean_inc(v_divMod_408_);
lean_inc(v_diseqSplits_407_);
lean_inc(v_conflict_x3f_406_);
lean_inc(v_steps_405_);
lean_inc(v_nextCnstrId_403_);
lean_inc(v_assignment_402_);
lean_inc(v_occurs_401_);
lean_inc(v_elimStack_400_);
lean_inc(v_elimEqs_399_);
lean_inc(v_diseqs_398_);
lean_inc(v_uppers_397_);
lean_inc(v_lowers_396_);
lean_inc(v_dvds_395_);
lean_inc(v_natDef_394_);
lean_inc(v_natToIntMap_393_);
lean_inc(v_varsHistory_392_);
lean_inc(v_varMap_391_);
lean_inc(v_vars_390_);
lean_dec(v_s_389_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_419_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_417_; 
v___x_414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_414_, 0, v_a_387_);
v___x_415_ = l_Lean_PersistentArray_set___redArg(v_dvds_395_, v_v_388_, v___x_414_);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 5, v___x_415_);
v___x_417_ = v___x_412_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_418_; 
v_reuseFailAlloc_418_ = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(v_reuseFailAlloc_418_, 0, v_vars_390_);
lean_ctor_set(v_reuseFailAlloc_418_, 1, v_varMap_391_);
lean_ctor_set(v_reuseFailAlloc_418_, 2, v_varsHistory_392_);
lean_ctor_set(v_reuseFailAlloc_418_, 3, v_natToIntMap_393_);
lean_ctor_set(v_reuseFailAlloc_418_, 4, v_natDef_394_);
lean_ctor_set(v_reuseFailAlloc_418_, 5, v___x_415_);
lean_ctor_set(v_reuseFailAlloc_418_, 6, v_lowers_396_);
lean_ctor_set(v_reuseFailAlloc_418_, 7, v_uppers_397_);
lean_ctor_set(v_reuseFailAlloc_418_, 8, v_diseqs_398_);
lean_ctor_set(v_reuseFailAlloc_418_, 9, v_elimEqs_399_);
lean_ctor_set(v_reuseFailAlloc_418_, 10, v_elimStack_400_);
lean_ctor_set(v_reuseFailAlloc_418_, 11, v_occurs_401_);
lean_ctor_set(v_reuseFailAlloc_418_, 12, v_assignment_402_);
lean_ctor_set(v_reuseFailAlloc_418_, 13, v_nextCnstrId_403_);
lean_ctor_set(v_reuseFailAlloc_418_, 14, v_steps_405_);
lean_ctor_set(v_reuseFailAlloc_418_, 15, v_conflict_x3f_406_);
lean_ctor_set(v_reuseFailAlloc_418_, 16, v_diseqSplits_407_);
lean_ctor_set(v_reuseFailAlloc_418_, 17, v_divMod_408_);
lean_ctor_set(v_reuseFailAlloc_418_, 18, v_nonlinearOccs_410_);
lean_ctor_set_uint8(v_reuseFailAlloc_418_, sizeof(void*)*19, v_caseSplits_404_);
lean_ctor_set_uint8(v_reuseFailAlloc_418_, sizeof(void*)*19 + 1, v_usedCommRing_409_);
v___x_417_ = v_reuseFailAlloc_418_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
return v___x_417_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed(lean_object* v_a_420_, lean_object* v_v_421_, lean_object* v_s_422_){
_start:
{
lean_object* v_res_423_; 
v_res_423_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(v_a_420_, v_v_421_, v_s_422_);
lean_dec(v_v_421_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(lean_object* v_v_424_, lean_object* v_s_425_){
_start:
{
lean_object* v_vars_426_; lean_object* v_varMap_427_; lean_object* v_varsHistory_428_; lean_object* v_natToIntMap_429_; lean_object* v_natDef_430_; lean_object* v_dvds_431_; lean_object* v_lowers_432_; lean_object* v_uppers_433_; lean_object* v_diseqs_434_; lean_object* v_elimEqs_435_; lean_object* v_elimStack_436_; lean_object* v_occurs_437_; lean_object* v_assignment_438_; lean_object* v_nextCnstrId_439_; uint8_t v_caseSplits_440_; lean_object* v_steps_441_; lean_object* v_conflict_x3f_442_; lean_object* v_diseqSplits_443_; lean_object* v_divMod_444_; uint8_t v_usedCommRing_445_; lean_object* v_nonlinearOccs_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_455_; 
v_vars_426_ = lean_ctor_get(v_s_425_, 0);
v_varMap_427_ = lean_ctor_get(v_s_425_, 1);
v_varsHistory_428_ = lean_ctor_get(v_s_425_, 2);
v_natToIntMap_429_ = lean_ctor_get(v_s_425_, 3);
v_natDef_430_ = lean_ctor_get(v_s_425_, 4);
v_dvds_431_ = lean_ctor_get(v_s_425_, 5);
v_lowers_432_ = lean_ctor_get(v_s_425_, 6);
v_uppers_433_ = lean_ctor_get(v_s_425_, 7);
v_diseqs_434_ = lean_ctor_get(v_s_425_, 8);
v_elimEqs_435_ = lean_ctor_get(v_s_425_, 9);
v_elimStack_436_ = lean_ctor_get(v_s_425_, 10);
v_occurs_437_ = lean_ctor_get(v_s_425_, 11);
v_assignment_438_ = lean_ctor_get(v_s_425_, 12);
v_nextCnstrId_439_ = lean_ctor_get(v_s_425_, 13);
v_caseSplits_440_ = lean_ctor_get_uint8(v_s_425_, sizeof(void*)*19);
v_steps_441_ = lean_ctor_get(v_s_425_, 14);
v_conflict_x3f_442_ = lean_ctor_get(v_s_425_, 15);
v_diseqSplits_443_ = lean_ctor_get(v_s_425_, 16);
v_divMod_444_ = lean_ctor_get(v_s_425_, 17);
v_usedCommRing_445_ = lean_ctor_get_uint8(v_s_425_, sizeof(void*)*19 + 1);
v_nonlinearOccs_446_ = lean_ctor_get(v_s_425_, 18);
v_isSharedCheck_455_ = !lean_is_exclusive(v_s_425_);
if (v_isSharedCheck_455_ == 0)
{
v___x_448_ = v_s_425_;
v_isShared_449_ = v_isSharedCheck_455_;
goto v_resetjp_447_;
}
else
{
lean_inc(v_nonlinearOccs_446_);
lean_inc(v_divMod_444_);
lean_inc(v_diseqSplits_443_);
lean_inc(v_conflict_x3f_442_);
lean_inc(v_steps_441_);
lean_inc(v_nextCnstrId_439_);
lean_inc(v_assignment_438_);
lean_inc(v_occurs_437_);
lean_inc(v_elimStack_436_);
lean_inc(v_elimEqs_435_);
lean_inc(v_diseqs_434_);
lean_inc(v_uppers_433_);
lean_inc(v_lowers_432_);
lean_inc(v_dvds_431_);
lean_inc(v_natDef_430_);
lean_inc(v_natToIntMap_429_);
lean_inc(v_varsHistory_428_);
lean_inc(v_varMap_427_);
lean_inc(v_vars_426_);
lean_dec(v_s_425_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_455_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_453_; 
v___x_450_ = lean_box(0);
v___x_451_ = l_Lean_PersistentArray_set___redArg(v_dvds_431_, v_v_424_, v___x_450_);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 5, v___x_451_);
v___x_453_ = v___x_448_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_vars_426_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v_varMap_427_);
lean_ctor_set(v_reuseFailAlloc_454_, 2, v_varsHistory_428_);
lean_ctor_set(v_reuseFailAlloc_454_, 3, v_natToIntMap_429_);
lean_ctor_set(v_reuseFailAlloc_454_, 4, v_natDef_430_);
lean_ctor_set(v_reuseFailAlloc_454_, 5, v___x_451_);
lean_ctor_set(v_reuseFailAlloc_454_, 6, v_lowers_432_);
lean_ctor_set(v_reuseFailAlloc_454_, 7, v_uppers_433_);
lean_ctor_set(v_reuseFailAlloc_454_, 8, v_diseqs_434_);
lean_ctor_set(v_reuseFailAlloc_454_, 9, v_elimEqs_435_);
lean_ctor_set(v_reuseFailAlloc_454_, 10, v_elimStack_436_);
lean_ctor_set(v_reuseFailAlloc_454_, 11, v_occurs_437_);
lean_ctor_set(v_reuseFailAlloc_454_, 12, v_assignment_438_);
lean_ctor_set(v_reuseFailAlloc_454_, 13, v_nextCnstrId_439_);
lean_ctor_set(v_reuseFailAlloc_454_, 14, v_steps_441_);
lean_ctor_set(v_reuseFailAlloc_454_, 15, v_conflict_x3f_442_);
lean_ctor_set(v_reuseFailAlloc_454_, 16, v_diseqSplits_443_);
lean_ctor_set(v_reuseFailAlloc_454_, 17, v_divMod_444_);
lean_ctor_set(v_reuseFailAlloc_454_, 18, v_nonlinearOccs_446_);
lean_ctor_set_uint8(v_reuseFailAlloc_454_, sizeof(void*)*19, v_caseSplits_440_);
lean_ctor_set_uint8(v_reuseFailAlloc_454_, sizeof(void*)*19 + 1, v_usedCommRing_445_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed(lean_object* v_v_456_, lean_object* v_s_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(v_v_456_, v_s_457_);
lean_dec(v_v_456_);
return v_res_458_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5(void){
_start:
{
lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_467_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4));
v___x_468_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
v___x_469_ = l_Lean_Name_append(v___x_468_, v___x_467_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(lean_object* v_c_470_, lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_){
_start:
{
lean_object* v___y_486_; lean_object* v___y_487_; lean_object* v___y_488_; lean_object* v___y_489_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v___y_497_; lean_object* v___y_498_; lean_object* v___y_499_; lean_object* v___y_500_; lean_object* v___y_501_; lean_object* v___y_502_; lean_object* v___y_503_; lean_object* v___y_504_; lean_object* v___y_505_; lean_object* v___y_506_; lean_object* v___y_507_; lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_600_; lean_object* v___y_601_; lean_object* v___y_602_; lean_object* v___y_603_; lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v_toCold_622_; lean_object* v_currRecDepth_623_; lean_object* v_ref_624_; uint16_t v_optionFlags_625_; uint8_t v_suppressElabErrors_626_; uint8_t v_isRecordingDeps_627_; lean_object* v_options_628_; lean_object* v_maxRecDepth_629_; lean_object* v_inheritedTraceOptions_630_; lean_object* v___x_631_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_670_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___x_813_; uint8_t v___x_814_; 
v_toCold_622_ = lean_ctor_get(v_a_479_, 0);
lean_inc_ref(v_toCold_622_);
v_currRecDepth_623_ = lean_ctor_get(v_a_479_, 1);
lean_inc(v_currRecDepth_623_);
v_ref_624_ = lean_ctor_get(v_a_479_, 2);
lean_inc(v_ref_624_);
v_optionFlags_625_ = lean_ctor_get_uint16(v_a_479_, sizeof(void*)*3);
v_suppressElabErrors_626_ = lean_ctor_get_uint8(v_a_479_, sizeof(void*)*3 + 2);
v_isRecordingDeps_627_ = lean_ctor_get_uint8(v_a_479_, sizeof(void*)*3 + 3);
lean_dec_ref(v_a_479_);
v_options_628_ = lean_ctor_get(v_toCold_622_, 2);
lean_inc_ref(v_options_628_);
v_maxRecDepth_629_ = lean_ctor_get(v_toCold_622_, 3);
v_inheritedTraceOptions_630_ = lean_ctor_get(v_toCold_622_, 11);
lean_inc_ref(v_inheritedTraceOptions_630_);
v___x_631_ = lean_box(0);
v___x_813_ = lean_unsigned_to_nat(0u);
v___x_814_ = lean_nat_dec_eq(v_maxRecDepth_629_, v___x_813_);
if (v___x_814_ == 0)
{
uint8_t v___x_815_; 
v___x_815_ = lean_nat_dec_eq(v_currRecDepth_623_, v_maxRecDepth_629_);
if (v___x_815_ == 0)
{
goto v___jp_772_;
}
else
{
lean_object* v___x_816_; 
lean_dec_ref(v_inheritedTraceOptions_630_);
lean_dec_ref(v_options_628_);
lean_dec(v_currRecDepth_623_);
lean_dec_ref(v_toCold_622_);
lean_dec_ref(v_c_470_);
v___x_816_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_624_);
return v___x_816_;
}
}
else
{
goto v___jp_772_;
}
v___jp_482_:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = lean_box(0);
v___x_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_484_, 0, v___x_483_);
return v___x_484_;
}
v___jp_485_:
{
lean_object* v___x_493_; 
v___x_493_ = l_Int_Internal_Linear_Poly_updateOccs___redArg(v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
lean_dec_ref(v___y_491_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v___x_494_; lean_object* v___x_495_; 
lean_dec_ref_known(v___x_493_, 1);
v___x_494_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_495_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_494_, v___y_486_, v___y_488_);
return v___x_495_;
}
else
{
lean_dec_ref(v___y_486_);
return v___x_493_;
}
}
v___jp_496_:
{
if (lean_obj_tag(v___y_518_) == 1)
{
lean_object* v_val_519_; lean_object* v_p_520_; 
lean_dec_ref(v___y_510_);
lean_dec_ref(v___y_504_);
v_val_519_ = lean_ctor_get(v___y_518_, 0);
lean_inc(v_val_519_);
lean_dec_ref_known(v___y_518_, 1);
v_p_520_ = lean_ctor_get(v_val_519_, 1);
lean_inc_ref(v_p_520_);
if (lean_obj_tag(v_p_520_) == 1)
{
lean_object* v_d_521_; lean_object* v_k_522_; lean_object* v_p_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_576_; 
v_d_521_ = lean_ctor_get(v_val_519_, 0);
v_k_522_ = lean_ctor_get(v_p_520_, 0);
v_p_523_ = lean_ctor_get(v_p_520_, 2);
v_isSharedCheck_576_ = !lean_is_exclusive(v_p_520_);
if (v_isSharedCheck_576_ == 0)
{
lean_object* v_unused_577_; 
v_unused_577_ = lean_ctor_get(v_p_520_, 1);
lean_dec(v_unused_577_);
v___x_525_ = v_p_520_;
v_isShared_526_ = v_isSharedCheck_576_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_p_523_);
lean_inc(v_k_522_);
lean_dec(v_p_520_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_576_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v_snd_530_; lean_object* v_fst_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_575_; 
v___x_527_ = lean_int_mul(v___y_501_, v_d_521_);
v___x_528_ = lean_int_mul(v_k_522_, v___y_514_);
v___x_529_ = l_Lean_Meta_Grind_Arith_gcdExt(v___x_527_, v___x_528_);
lean_dec(v___x_528_);
lean_dec(v___x_527_);
v_snd_530_ = lean_ctor_get(v___x_529_, 1);
v_fst_531_ = lean_ctor_get(v___x_529_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_529_);
if (v_isSharedCheck_575_ == 0)
{
v___x_533_ = v___x_529_;
v_isShared_534_ = v_isSharedCheck_575_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_snd_530_);
lean_inc(v_fst_531_);
lean_dec(v___x_529_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_575_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v_fst_535_; lean_object* v_snd_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_574_; 
v_fst_535_ = lean_ctor_get(v_snd_530_, 0);
v_snd_536_ = lean_ctor_get(v_snd_530_, 1);
v_isSharedCheck_574_ = !lean_is_exclusive(v_snd_530_);
if (v_isSharedCheck_574_ == 0)
{
v___x_538_ = v_snd_530_;
v_isShared_539_ = v_isSharedCheck_574_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_snd_536_);
lean_inc(v_fst_535_);
lean_dec(v_snd_530_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_574_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_547_; 
v___x_540_ = lean_int_mul(v_fst_535_, v_d_521_);
lean_dec(v_fst_535_);
lean_inc_ref(v___y_497_);
v___x_541_ = l_Int_Internal_Linear_Poly_mul(v___y_497_, v___x_540_);
lean_dec(v___x_540_);
v___x_542_ = lean_int_mul(v_snd_536_, v___y_514_);
lean_dec(v_snd_536_);
lean_inc_ref(v_p_523_);
v___x_543_ = l_Int_Internal_Linear_Poly_mul(v_p_523_, v___x_542_);
lean_dec(v___x_542_);
v___x_544_ = lean_int_mul(v___y_514_, v_d_521_);
lean_dec(v___y_514_);
v___x_545_ = l_Int_Internal_Linear_Poly_combine(v___x_541_, v___x_543_);
lean_inc(v_fst_531_);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 2, v___x_545_);
lean_ctor_set(v___x_525_, 1, v___y_512_);
lean_ctor_set(v___x_525_, 0, v_fst_531_);
v___x_547_ = v___x_525_;
goto v_reusejp_546_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_fst_531_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v___y_512_);
lean_ctor_set(v_reuseFailAlloc_573_, 2, v___x_545_);
v___x_547_ = v_reuseFailAlloc_573_;
goto v_reusejp_546_;
}
v_reusejp_546_:
{
lean_object* v___x_549_; 
lean_inc(v_val_519_);
lean_inc_ref(v___y_515_);
if (v_isShared_539_ == 0)
{
lean_ctor_set_tag(v___x_538_, 4);
lean_ctor_set(v___x_538_, 1, v_val_519_);
lean_ctor_set(v___x_538_, 0, v___y_515_);
v___x_549_ = v___x_538_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___y_515_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_val_519_);
v___x_549_ = v_reuseFailAlloc_572_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_550_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_550_, 0, v___x_544_);
lean_ctor_set(v___x_550_, 1, v___x_547_);
lean_ctor_set(v___x_550_, 2, v___x_549_);
v___x_551_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_552_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_551_, v___y_498_, v___y_516_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v___x_553_; 
lean_dec_ref_known(v___x_552_, 1);
lean_inc_ref(v___y_506_);
v___x_553_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v___x_550_, v___y_516_, v___y_517_, v___y_508_, v___y_513_, v___y_502_, v___y_509_, v___y_503_, v___y_500_, v___y_506_, v___y_507_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_559_; 
lean_dec_ref_known(v___x_553_, 1);
v___x_554_ = l_Int_Internal_Linear_Poly_mul(v___y_497_, v_k_522_);
lean_dec(v_k_522_);
v___x_555_ = lean_int_neg(v___y_501_);
lean_dec(v___y_501_);
v___x_556_ = l_Int_Internal_Linear_Poly_mul(v_p_523_, v___x_555_);
lean_dec(v___x_555_);
v___x_557_ = l_Int_Internal_Linear_Poly_combine(v___x_554_, v___x_556_);
lean_inc(v_val_519_);
if (v_isShared_534_ == 0)
{
lean_ctor_set_tag(v___x_533_, 5);
lean_ctor_set(v___x_533_, 1, v_val_519_);
lean_ctor_set(v___x_533_, 0, v___y_515_);
v___x_559_ = v___x_533_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___y_515_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_val_519_);
v___x_559_ = v_reuseFailAlloc_571_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_567_; 
v_isSharedCheck_567_ = !lean_is_exclusive(v_val_519_);
if (v_isSharedCheck_567_ == 0)
{
lean_object* v_unused_568_; lean_object* v_unused_569_; lean_object* v_unused_570_; 
v_unused_568_ = lean_ctor_get(v_val_519_, 2);
lean_dec(v_unused_568_);
v_unused_569_ = lean_ctor_get(v_val_519_, 1);
lean_dec(v_unused_569_);
v_unused_570_ = lean_ctor_get(v_val_519_, 0);
lean_dec(v_unused_570_);
v___x_561_ = v_val_519_;
v_isShared_562_ = v_isSharedCheck_567_;
goto v_resetjp_560_;
}
else
{
lean_dec(v_val_519_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_567_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_564_; 
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 2, v___x_559_);
lean_ctor_set(v___x_561_, 1, v___x_557_);
lean_ctor_set(v___x_561_, 0, v_fst_531_);
v___x_564_ = v___x_561_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v_fst_531_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v___x_557_);
lean_ctor_set(v_reuseFailAlloc_566_, 2, v___x_559_);
v___x_564_ = v_reuseFailAlloc_566_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
v_c_470_ = v___x_564_;
v_a_471_ = v___y_516_;
v_a_472_ = v___y_517_;
v_a_473_ = v___y_508_;
v_a_474_ = v___y_513_;
v_a_475_ = v___y_502_;
v_a_476_ = v___y_509_;
v_a_477_ = v___y_503_;
v_a_478_ = v___y_500_;
v_a_479_ = v___y_506_;
v_a_480_ = v___y_507_;
goto _start;
}
}
}
}
else
{
lean_del_object(v___x_533_);
lean_dec(v_fst_531_);
lean_dec_ref(v_p_523_);
lean_dec(v_k_522_);
lean_dec(v_val_519_);
lean_dec_ref(v___y_515_);
lean_dec_ref(v___y_506_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_497_);
return v___x_553_;
}
}
else
{
lean_dec_ref_known(v___x_550_, 3);
lean_del_object(v___x_533_);
lean_dec(v_fst_531_);
lean_dec_ref(v_p_523_);
lean_dec(v_k_522_);
lean_dec(v_val_519_);
lean_dec_ref(v___y_515_);
lean_dec_ref(v___y_506_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_497_);
return v___x_552_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_578_; 
lean_dec_ref(v_p_520_);
lean_dec_ref(v___y_515_);
lean_dec(v___y_514_);
lean_dec(v___y_512_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_498_);
lean_dec_ref(v___y_497_);
v___x_578_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_val_519_, v___y_516_, v___y_517_, v___y_508_, v___y_513_, v___y_502_, v___y_509_, v___y_503_, v___y_500_, v___y_506_, v___y_507_);
lean_dec_ref(v___y_506_);
return v___x_578_;
}
}
else
{
lean_object* v_toCold_579_; lean_object* v_options_580_; uint8_t v_hasTrace_581_; 
lean_dec(v___y_518_);
lean_dec(v___y_514_);
lean_dec(v___y_512_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_498_);
lean_dec_ref(v___y_497_);
v_toCold_579_ = lean_ctor_get(v___y_506_, 0);
v_options_580_ = lean_ctor_get(v_toCold_579_, 2);
v_hasTrace_581_ = lean_ctor_get_uint8(v_options_580_, sizeof(void*)*1);
if (v_hasTrace_581_ == 0)
{
lean_dec_ref(v___y_515_);
v___y_486_ = v___y_510_;
v___y_487_ = v___y_504_;
v___y_488_ = v___y_516_;
v___y_489_ = v___y_503_;
v___y_490_ = v___y_500_;
v___y_491_ = v___y_506_;
v___y_492_ = v___y_507_;
goto v___jp_485_;
}
else
{
lean_object* v_inheritedTraceOptions_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; uint8_t v___x_587_; 
v_inheritedTraceOptions_582_ = lean_ctor_get(v_toCold_579_, 11);
v___x_583_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0));
lean_inc_ref(v___y_499_);
lean_inc_ref(v___y_505_);
lean_inc_ref(v___y_511_);
v___x_584_ = l_Lean_Name_mkStr4(v___y_511_, v___y_505_, v___y_499_, v___x_583_);
v___x_585_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
lean_inc(v___x_584_);
v___x_586_ = l_Lean_Name_append(v___x_585_, v___x_584_);
v___x_587_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_582_, v_options_580_, v___x_586_);
lean_dec(v___x_586_);
if (v___x_587_ == 0)
{
lean_dec(v___x_584_);
lean_dec_ref(v___y_515_);
v___y_486_ = v___y_510_;
v___y_487_ = v___y_504_;
v___y_488_ = v___y_516_;
v___y_489_ = v___y_503_;
v___y_490_ = v___y_500_;
v___y_491_ = v___y_506_;
v___y_492_ = v___y_507_;
goto v___jp_485_;
}
else
{
lean_object* v___x_588_; 
v___x_588_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v___y_515_, v___y_516_, v___y_506_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v_a_589_; lean_object* v___x_590_; 
v_a_589_ = lean_ctor_get(v___x_588_, 0);
lean_inc(v_a_589_);
lean_dec_ref_known(v___x_588_, 1);
v___x_590_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_584_, v_a_589_, v___y_503_, v___y_500_, v___y_506_, v___y_507_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_dec_ref_known(v___x_590_, 1);
v___y_486_ = v___y_510_;
v___y_487_ = v___y_504_;
v___y_488_ = v___y_516_;
v___y_489_ = v___y_503_;
v___y_490_ = v___y_500_;
v___y_491_ = v___y_506_;
v___y_492_ = v___y_507_;
goto v___jp_485_;
}
else
{
lean_dec_ref(v___y_510_);
lean_dec_ref(v___y_506_);
lean_dec_ref(v___y_504_);
return v___x_590_;
}
}
else
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_598_; 
lean_dec(v___x_584_);
lean_dec_ref(v___y_510_);
lean_dec_ref(v___y_506_);
lean_dec_ref(v___y_504_);
v_a_591_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_598_ == 0)
{
v___x_593_ = v___x_588_;
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_a_591_);
lean_dec(v___x_588_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_598_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_596_; 
if (v_isShared_594_ == 0)
{
v___x_596_ = v___x_593_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_a_591_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
}
}
}
}
v___jp_599_:
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_611_, 0, v___y_600_);
v___x_612_ = l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(v___x_611_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_);
lean_dec_ref(v___y_609_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_620_; 
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_612_);
if (v_isSharedCheck_620_ == 0)
{
lean_object* v_unused_621_; 
v_unused_621_ = lean_ctor_get(v___x_612_, 0);
lean_dec(v_unused_621_);
v___x_614_ = v___x_612_;
v_isShared_615_ = v_isSharedCheck_620_;
goto v_resetjp_613_;
}
else
{
lean_dec(v___x_612_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_620_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_616_; lean_object* v___x_618_; 
v___x_616_ = lean_box(0);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 0, v___x_616_);
v___x_618_ = v___x_614_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v___x_616_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
else
{
return v___x_612_;
}
}
v___jp_632_:
{
lean_object* v___x_654_; 
v___x_654_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v___y_644_, v___y_652_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v_a_655_; lean_object* v_dvds_656_; lean_object* v_size_657_; uint8_t v___x_658_; 
v_a_655_ = lean_ctor_get(v___x_654_, 0);
lean_inc(v_a_655_);
lean_dec_ref_known(v___x_654_, 1);
v_dvds_656_ = lean_ctor_get(v_a_655_, 5);
lean_inc_ref(v_dvds_656_);
lean_dec(v_a_655_);
v_size_657_ = lean_ctor_get(v_dvds_656_, 2);
v___x_658_ = lean_nat_dec_lt(v___y_636_, v_size_657_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; 
lean_dec_ref(v_dvds_656_);
v___x_659_ = l_outOfBounds___redArg(v___x_631_);
v___y_497_ = v___y_634_;
v___y_498_ = v___y_633_;
v___y_499_ = v___y_635_;
v___y_500_ = v___y_651_;
v___y_501_ = v___y_639_;
v___y_502_ = v___y_648_;
v___y_503_ = v___y_650_;
v___y_504_ = v___y_642_;
v___y_505_ = v___y_643_;
v___y_506_ = v___y_652_;
v___y_507_ = v___y_653_;
v___y_508_ = v___y_646_;
v___y_509_ = v___y_649_;
v___y_510_ = v___y_638_;
v___y_511_ = v___y_637_;
v___y_512_ = v___y_636_;
v___y_513_ = v___y_647_;
v___y_514_ = v___y_640_;
v___y_515_ = v___y_641_;
v___y_516_ = v___y_644_;
v___y_517_ = v___y_645_;
v___y_518_ = v___x_659_;
goto v___jp_496_;
}
else
{
lean_object* v___x_660_; 
v___x_660_ = l_Lean_PersistentArray_get_x21___redArg(v___x_631_, v_dvds_656_, v___y_636_);
lean_dec_ref(v_dvds_656_);
v___y_497_ = v___y_634_;
v___y_498_ = v___y_633_;
v___y_499_ = v___y_635_;
v___y_500_ = v___y_651_;
v___y_501_ = v___y_639_;
v___y_502_ = v___y_648_;
v___y_503_ = v___y_650_;
v___y_504_ = v___y_642_;
v___y_505_ = v___y_643_;
v___y_506_ = v___y_652_;
v___y_507_ = v___y_653_;
v___y_508_ = v___y_646_;
v___y_509_ = v___y_649_;
v___y_510_ = v___y_638_;
v___y_511_ = v___y_637_;
v___y_512_ = v___y_636_;
v___y_513_ = v___y_647_;
v___y_514_ = v___y_640_;
v___y_515_ = v___y_641_;
v___y_516_ = v___y_644_;
v___y_517_ = v___y_645_;
v___y_518_ = v___x_660_;
goto v___jp_496_;
}
}
else
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_668_; 
lean_dec_ref(v___y_652_);
lean_dec_ref(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_634_);
lean_dec_ref(v___y_633_);
v_a_661_ = lean_ctor_get(v___x_654_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_668_ == 0)
{
v___x_663_ = v___x_654_;
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_654_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_666_; 
if (v_isShared_664_ == 0)
{
v___x_666_ = v___x_663_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_a_661_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
v___jp_669_:
{
lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_683_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(v_c_470_);
lean_inc_ref(v___y_681_);
v___x_684_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(v___x_683_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v_a_685_; lean_object* v_d_686_; lean_object* v_p_687_; uint8_t v___x_688_; 
v_a_685_ = lean_ctor_get(v___x_684_, 0);
lean_inc(v_a_685_);
lean_dec_ref_known(v___x_684_, 1);
v_d_686_ = lean_ctor_get(v_a_685_, 0);
v_p_687_ = lean_ctor_get(v_a_685_, 1);
lean_inc(v_d_686_);
v___x_688_ = l_Int_Internal_Linear_Poly_isUnsatDvd(v_d_686_, v_p_687_);
if (v___x_688_ == 0)
{
uint8_t v___x_689_; 
v___x_689_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(v_a_685_);
if (v___x_689_ == 0)
{
lean_object* v___x_690_; uint8_t v___x_691_; 
v___x_690_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1);
v___x_691_ = lean_int_dec_eq(v_d_686_, v___x_690_);
if (v___x_691_ == 0)
{
if (lean_obj_tag(v_p_687_) == 1)
{
lean_object* v_k_692_; lean_object* v_v_693_; lean_object* v_p_694_; lean_object* v___f_695_; lean_object* v___f_696_; lean_object* v___x_697_; 
lean_inc_ref(v_p_687_);
lean_inc(v_d_686_);
v_k_692_ = lean_ctor_get(v_p_687_, 0);
lean_inc(v_k_692_);
v_v_693_ = lean_ctor_get(v_p_687_, 1);
lean_inc_n(v_v_693_, 3);
v_p_694_ = lean_ctor_get(v_p_687_, 2);
lean_inc_ref(v_p_694_);
lean_inc_n(v_a_685_, 2);
v___f_695_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed), 3, 2);
lean_closure_set(v___f_695_, 0, v_a_685_);
lean_closure_set(v___f_695_, 1, v_v_693_);
v___f_696_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed), 2, 1);
lean_closure_set(v___f_696_, 0, v_v_693_);
v___x_697_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(v_a_685_, v___y_673_, v___y_681_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v_a_698_; uint8_t v___x_699_; uint8_t v___x_700_; uint8_t v___x_701_; 
v_a_698_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_a_698_);
lean_dec_ref_known(v___x_697_, 1);
v___x_699_ = 0;
v___x_700_ = lean_unbox(v_a_698_);
lean_dec(v_a_698_);
v___x_701_ = l_Lean_instBEqLBool_beq(v___x_700_, v___x_699_);
if (v___x_701_ == 0)
{
v___y_633_ = v___f_696_;
v___y_634_ = v_p_694_;
v___y_635_ = v___y_670_;
v___y_636_ = v_v_693_;
v___y_637_ = v___y_671_;
v___y_638_ = v___f_695_;
v___y_639_ = v_k_692_;
v___y_640_ = v_d_686_;
v___y_641_ = v_a_685_;
v___y_642_ = v_p_687_;
v___y_643_ = v___y_672_;
v___y_644_ = v___y_673_;
v___y_645_ = v___y_674_;
v___y_646_ = v___y_675_;
v___y_647_ = v___y_676_;
v___y_648_ = v___y_677_;
v___y_649_ = v___y_678_;
v___y_650_ = v___y_679_;
v___y_651_ = v___y_680_;
v___y_652_ = v___y_681_;
v___y_653_ = v___y_682_;
goto v___jp_632_;
}
else
{
lean_object* v___x_702_; 
lean_inc(v_v_693_);
v___x_702_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v_v_693_, v___y_673_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_dec_ref_known(v___x_702_, 1);
v___y_633_ = v___f_696_;
v___y_634_ = v_p_694_;
v___y_635_ = v___y_670_;
v___y_636_ = v_v_693_;
v___y_637_ = v___y_671_;
v___y_638_ = v___f_695_;
v___y_639_ = v_k_692_;
v___y_640_ = v_d_686_;
v___y_641_ = v_a_685_;
v___y_642_ = v_p_687_;
v___y_643_ = v___y_672_;
v___y_644_ = v___y_673_;
v___y_645_ = v___y_674_;
v___y_646_ = v___y_675_;
v___y_647_ = v___y_676_;
v___y_648_ = v___y_677_;
v___y_649_ = v___y_678_;
v___y_650_ = v___y_679_;
v___y_651_ = v___y_680_;
v___y_652_ = v___y_681_;
v___y_653_ = v___y_682_;
goto v___jp_632_;
}
else
{
lean_dec_ref(v___f_696_);
lean_dec_ref(v___f_695_);
lean_dec_ref(v_p_694_);
lean_dec(v_v_693_);
lean_dec_ref_known(v_p_687_, 3);
lean_dec(v_k_692_);
lean_dec(v_d_686_);
lean_dec(v_a_685_);
lean_dec_ref(v___y_681_);
return v___x_702_;
}
}
}
else
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_710_; 
lean_dec_ref(v___f_696_);
lean_dec_ref(v___f_695_);
lean_dec_ref(v_p_694_);
lean_dec(v_v_693_);
lean_dec_ref_known(v_p_687_, 3);
lean_dec(v_k_692_);
lean_dec(v_d_686_);
lean_dec(v_a_685_);
lean_dec_ref(v___y_681_);
v_a_703_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_710_ == 0)
{
v___x_705_ = v___x_697_;
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_697_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_708_; 
if (v_isShared_706_ == 0)
{
v___x_708_ = v___x_705_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_a_703_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
else
{
lean_object* v___x_711_; 
v___x_711_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_a_685_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
lean_dec_ref(v___y_681_);
return v___x_711_;
}
}
else
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
lean_inc_ref(v_p_687_);
v___x_712_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_712_, 0, v_a_685_);
v___x_713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_713_, 0, v_p_687_);
lean_ctor_set(v___x_713_, 1, v___x_712_);
lean_inc(v___y_682_);
lean_inc(v___y_680_);
lean_inc_ref(v___y_679_);
lean_inc(v___y_678_);
lean_inc_ref(v___y_677_);
lean_inc(v___y_676_);
lean_inc_ref(v___y_675_);
lean_inc(v___y_674_);
lean_inc(v___y_673_);
v___x_714_ = lean_grind_cutsat_assert_eq(v___x_713_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_722_; 
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_714_);
if (v_isSharedCheck_722_ == 0)
{
lean_object* v_unused_723_; 
v_unused_723_ = lean_ctor_get(v___x_714_, 0);
lean_dec(v_unused_723_);
v___x_716_ = v___x_714_;
v_isShared_717_ = v_isSharedCheck_722_;
goto v_resetjp_715_;
}
else
{
lean_dec(v___x_714_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_722_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_718_; lean_object* v___x_720_; 
v___x_718_ = lean_box(0);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 0, v___x_718_);
v___x_720_ = v___x_716_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_718_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
else
{
return v___x_714_;
}
}
}
else
{
lean_object* v_toCold_724_; lean_object* v_options_725_; uint8_t v_hasTrace_726_; 
v_toCold_724_ = lean_ctor_get(v___y_681_, 0);
v_options_725_ = lean_ctor_get(v_toCold_724_, 2);
v_hasTrace_726_ = lean_ctor_get_uint8(v_options_725_, sizeof(void*)*1);
if (v_hasTrace_726_ == 0)
{
lean_dec(v_a_685_);
lean_dec_ref(v___y_681_);
goto v___jp_482_;
}
else
{
lean_object* v_inheritedTraceOptions_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; uint8_t v___x_732_; 
v_inheritedTraceOptions_727_ = lean_ctor_get(v_toCold_724_, 11);
v___x_728_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1));
lean_inc_ref(v___y_670_);
lean_inc_ref(v___y_672_);
lean_inc_ref(v___y_671_);
v___x_729_ = l_Lean_Name_mkStr4(v___y_671_, v___y_672_, v___y_670_, v___x_728_);
v___x_730_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
lean_inc(v___x_729_);
v___x_731_ = l_Lean_Name_append(v___x_730_, v___x_729_);
v___x_732_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_727_, v_options_725_, v___x_731_);
lean_dec(v___x_731_);
if (v___x_732_ == 0)
{
lean_dec(v___x_729_);
lean_dec(v_a_685_);
lean_dec_ref(v___y_681_);
goto v___jp_482_;
}
else
{
lean_object* v___x_733_; 
v___x_733_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_a_685_, v___y_673_, v___y_681_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_object* v_a_734_; lean_object* v___x_735_; 
v_a_734_ = lean_ctor_get(v___x_733_, 0);
lean_inc(v_a_734_);
lean_dec_ref_known(v___x_733_, 1);
v___x_735_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_729_, v_a_734_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
lean_dec_ref(v___y_681_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_dec_ref_known(v___x_735_, 1);
goto v___jp_482_;
}
else
{
return v___x_735_;
}
}
else
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
lean_dec(v___x_729_);
lean_dec_ref(v___y_681_);
v_a_736_ = lean_ctor_get(v___x_733_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v___x_733_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_733_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_736_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
}
}
}
else
{
lean_object* v_toCold_744_; lean_object* v_options_745_; uint8_t v_hasTrace_746_; 
v_toCold_744_ = lean_ctor_get(v___y_681_, 0);
v_options_745_ = lean_ctor_get(v_toCold_744_, 2);
v_hasTrace_746_ = lean_ctor_get_uint8(v_options_745_, sizeof(void*)*1);
if (v_hasTrace_746_ == 0)
{
v___y_600_ = v_a_685_;
v___y_601_ = v___y_673_;
v___y_602_ = v___y_674_;
v___y_603_ = v___y_675_;
v___y_604_ = v___y_676_;
v___y_605_ = v___y_677_;
v___y_606_ = v___y_678_;
v___y_607_ = v___y_679_;
v___y_608_ = v___y_680_;
v___y_609_ = v___y_681_;
v___y_610_ = v___y_682_;
goto v___jp_599_;
}
else
{
lean_object* v_inheritedTraceOptions_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; uint8_t v___x_752_; 
v_inheritedTraceOptions_747_ = lean_ctor_get(v_toCold_744_, 11);
v___x_748_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2));
lean_inc_ref(v___y_670_);
lean_inc_ref(v___y_672_);
lean_inc_ref(v___y_671_);
v___x_749_ = l_Lean_Name_mkStr4(v___y_671_, v___y_672_, v___y_670_, v___x_748_);
v___x_750_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
lean_inc(v___x_749_);
v___x_751_ = l_Lean_Name_append(v___x_750_, v___x_749_);
v___x_752_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_747_, v_options_745_, v___x_751_);
lean_dec(v___x_751_);
if (v___x_752_ == 0)
{
lean_dec(v___x_749_);
v___y_600_ = v_a_685_;
v___y_601_ = v___y_673_;
v___y_602_ = v___y_674_;
v___y_603_ = v___y_675_;
v___y_604_ = v___y_676_;
v___y_605_ = v___y_677_;
v___y_606_ = v___y_678_;
v___y_607_ = v___y_679_;
v___y_608_ = v___y_680_;
v___y_609_ = v___y_681_;
v___y_610_ = v___y_682_;
goto v___jp_599_;
}
else
{
lean_object* v___x_753_; 
lean_inc(v_a_685_);
v___x_753_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_a_685_, v___y_673_, v___y_681_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_object* v_a_754_; lean_object* v___x_755_; 
v_a_754_ = lean_ctor_get(v___x_753_, 0);
lean_inc(v_a_754_);
lean_dec_ref_known(v___x_753_, 1);
v___x_755_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_749_, v_a_754_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_dec_ref_known(v___x_755_, 1);
v___y_600_ = v_a_685_;
v___y_601_ = v___y_673_;
v___y_602_ = v___y_674_;
v___y_603_ = v___y_675_;
v___y_604_ = v___y_676_;
v___y_605_ = v___y_677_;
v___y_606_ = v___y_678_;
v___y_607_ = v___y_679_;
v___y_608_ = v___y_680_;
v___y_609_ = v___y_681_;
v___y_610_ = v___y_682_;
goto v___jp_599_;
}
else
{
lean_dec(v_a_685_);
lean_dec_ref(v___y_681_);
return v___x_755_;
}
}
else
{
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
lean_dec(v___x_749_);
lean_dec(v_a_685_);
lean_dec_ref(v___y_681_);
v_a_756_ = lean_ctor_get(v___x_753_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_753_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___x_753_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_753_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_759_ == 0)
{
v___x_761_ = v___x_758_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_756_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_764_; lean_object* v___x_766_; uint8_t v_isShared_767_; uint8_t v_isSharedCheck_771_; 
lean_dec_ref(v___y_681_);
v_a_764_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_771_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_771_ == 0)
{
v___x_766_ = v___x_684_;
v_isShared_767_ = v_isSharedCheck_771_;
goto v_resetjp_765_;
}
else
{
lean_inc(v_a_764_);
lean_dec(v___x_684_);
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
v___jp_772_:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_773_ = lean_unsigned_to_nat(1u);
v___x_774_ = lean_nat_add(v_currRecDepth_623_, v___x_773_);
lean_dec(v_currRecDepth_623_);
v___x_775_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_775_, 0, v_toCold_622_);
lean_ctor_set(v___x_775_, 1, v___x_774_);
lean_ctor_set(v___x_775_, 2, v_ref_624_);
lean_ctor_set_uint16(v___x_775_, sizeof(void*)*3, v_optionFlags_625_);
lean_ctor_set_uint8(v___x_775_, sizeof(void*)*3 + 2, v_suppressElabErrors_626_);
lean_ctor_set_uint8(v___x_775_, sizeof(void*)*3 + 3, v_isRecordingDeps_627_);
v___x_776_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_471_, v___x_775_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v_a_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_804_; 
v_a_777_ = lean_ctor_get(v___x_776_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_804_ == 0)
{
v___x_779_ = v___x_776_;
v_isShared_780_ = v_isSharedCheck_804_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_a_777_);
lean_dec(v___x_776_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_804_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
uint8_t v___x_781_; 
v___x_781_ = lean_unbox(v_a_777_);
lean_dec(v_a_777_);
if (v___x_781_ == 0)
{
uint8_t v_hasTrace_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
lean_del_object(v___x_779_);
v_hasTrace_782_ = lean_ctor_get_uint8(v_options_628_, sizeof(void*)*1);
v___x_783_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0));
v___x_784_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2));
v___x_785_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3));
if (v_hasTrace_782_ == 0)
{
lean_dec_ref(v_inheritedTraceOptions_630_);
lean_dec_ref(v_options_628_);
v___y_670_ = v___x_785_;
v___y_671_ = v___x_783_;
v___y_672_ = v___x_784_;
v___y_673_ = v_a_471_;
v___y_674_ = v_a_472_;
v___y_675_ = v_a_473_;
v___y_676_ = v_a_474_;
v___y_677_ = v_a_475_;
v___y_678_ = v_a_476_;
v___y_679_ = v_a_477_;
v___y_680_ = v_a_478_;
v___y_681_ = v___x_775_;
v___y_682_ = v_a_480_;
goto v___jp_669_;
}
else
{
lean_object* v___x_786_; lean_object* v___x_787_; uint8_t v___x_788_; 
v___x_786_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4));
v___x_787_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5);
v___x_788_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_630_, v_options_628_, v___x_787_);
lean_dec_ref(v_options_628_);
lean_dec_ref(v_inheritedTraceOptions_630_);
if (v___x_788_ == 0)
{
v___y_670_ = v___x_785_;
v___y_671_ = v___x_783_;
v___y_672_ = v___x_784_;
v___y_673_ = v_a_471_;
v___y_674_ = v_a_472_;
v___y_675_ = v_a_473_;
v___y_676_ = v_a_474_;
v___y_677_ = v_a_475_;
v___y_678_ = v_a_476_;
v___y_679_ = v_a_477_;
v___y_680_ = v_a_478_;
v___y_681_ = v___x_775_;
v___y_682_ = v_a_480_;
goto v___jp_669_;
}
else
{
lean_object* v___x_789_; 
lean_inc_ref(v_c_470_);
v___x_789_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_470_, v_a_471_, v___x_775_);
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v_a_790_; lean_object* v___x_791_; 
v_a_790_ = lean_ctor_get(v___x_789_, 0);
lean_inc(v_a_790_);
lean_dec_ref_known(v___x_789_, 1);
v___x_791_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_786_, v_a_790_, v_a_477_, v_a_478_, v___x_775_, v_a_480_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_dec_ref_known(v___x_791_, 1);
v___y_670_ = v___x_785_;
v___y_671_ = v___x_783_;
v___y_672_ = v___x_784_;
v___y_673_ = v_a_471_;
v___y_674_ = v_a_472_;
v___y_675_ = v_a_473_;
v___y_676_ = v_a_474_;
v___y_677_ = v_a_475_;
v___y_678_ = v_a_476_;
v___y_679_ = v_a_477_;
v___y_680_ = v_a_478_;
v___y_681_ = v___x_775_;
v___y_682_ = v_a_480_;
goto v___jp_669_;
}
else
{
lean_dec_ref_known(v___x_775_, 3);
lean_dec_ref(v_c_470_);
return v___x_791_;
}
}
else
{
lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_799_; 
lean_dec_ref_known(v___x_775_, 3);
lean_dec_ref(v_c_470_);
v_a_792_ = lean_ctor_get(v___x_789_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_799_ == 0)
{
v___x_794_ = v___x_789_;
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_dec(v___x_789_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_797_; 
if (v_isShared_795_ == 0)
{
v___x_797_ = v___x_794_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_a_792_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
}
}
}
else
{
lean_object* v___x_800_; lean_object* v___x_802_; 
lean_dec_ref_known(v___x_775_, 3);
lean_dec_ref(v_inheritedTraceOptions_630_);
lean_dec_ref(v_options_628_);
lean_dec_ref(v_c_470_);
v___x_800_ = lean_box(0);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 0, v___x_800_);
v___x_802_ = v___x_779_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v___x_800_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
else
{
lean_object* v_a_805_; lean_object* v___x_807_; uint8_t v_isShared_808_; uint8_t v_isSharedCheck_812_; 
lean_dec_ref_known(v___x_775_, 3);
lean_dec_ref(v_inheritedTraceOptions_630_);
lean_dec_ref(v_options_628_);
lean_dec_ref(v_c_470_);
v_a_805_ = lean_ctor_get(v___x_776_, 0);
v_isSharedCheck_812_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_812_ == 0)
{
v___x_807_ = v___x_776_;
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
else
{
lean_inc(v_a_805_);
lean_dec(v___x_776_);
v___x_807_ = lean_box(0);
v_isShared_808_ = v_isSharedCheck_812_;
goto v_resetjp_806_;
}
v_resetjp_806_:
{
lean_object* v___x_810_; 
if (v_isShared_808_ == 0)
{
v___x_810_ = v___x_807_;
goto v_reusejp_809_;
}
else
{
lean_object* v_reuseFailAlloc_811_; 
v_reuseFailAlloc_811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_811_, 0, v_a_805_);
v___x_810_ = v_reuseFailAlloc_811_;
goto v_reusejp_809_;
}
v_reusejp_809_:
{
return v___x_810_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___boxed(lean_object* v_c_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v_c_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_);
lean_dec(v_a_827_);
lean_dec(v_a_825_);
lean_dec_ref(v_a_824_);
lean_dec(v_a_823_);
lean_dec_ref(v_a_822_);
lean_dec(v_a_821_);
lean_dec_ref(v_a_820_);
lean_dec(v_a_819_);
lean_dec(v_a_818_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(lean_object* v_c_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_){
_start:
{
lean_object* v_d_842_; lean_object* v_p_843_; lean_object* v___x_844_; 
v_d_842_ = lean_ctor_get(v_c_830_, 0);
v_p_843_ = lean_ctor_get(v_c_830_, 1);
lean_inc_ref(v_p_843_);
v___x_844_ = l_Int_Internal_Linear_Poly_normCommRing_x3f(v_p_843_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_a_845_; 
v_a_845_ = lean_ctor_get(v___x_844_, 0);
lean_inc(v_a_845_);
lean_dec_ref_known(v___x_844_, 1);
if (lean_obj_tag(v_a_845_) == 1)
{
lean_object* v_val_846_; lean_object* v_snd_847_; lean_object* v_fst_848_; lean_object* v_fst_849_; lean_object* v_snd_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
lean_inc(v_d_842_);
v_val_846_ = lean_ctor_get(v_a_845_, 0);
lean_inc(v_val_846_);
lean_dec_ref_known(v_a_845_, 1);
v_snd_847_ = lean_ctor_get(v_val_846_, 1);
lean_inc(v_snd_847_);
v_fst_848_ = lean_ctor_get(v_val_846_, 0);
lean_inc(v_fst_848_);
lean_dec(v_val_846_);
v_fst_849_ = lean_ctor_get(v_snd_847_, 0);
lean_inc(v_fst_849_);
v_snd_850_ = lean_ctor_get(v_snd_847_, 1);
lean_inc(v_snd_850_);
lean_dec(v_snd_847_);
v___x_851_ = lean_alloc_ctor(12, 3, 0);
lean_ctor_set(v___x_851_, 0, v_c_830_);
lean_ctor_set(v___x_851_, 1, v_fst_848_);
lean_ctor_set(v___x_851_, 2, v_fst_849_);
v___x_852_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_852_, 0, v_d_842_);
lean_ctor_set(v___x_852_, 1, v_snd_850_);
lean_ctor_set(v___x_852_, 2, v___x_851_);
lean_inc_ref(v_a_839_);
v___x_853_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v___x_852_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_);
return v___x_853_;
}
else
{
lean_object* v___x_854_; 
lean_dec(v_a_845_);
lean_inc_ref(v_a_839_);
v___x_854_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v_c_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_);
return v___x_854_;
}
}
else
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_862_; 
lean_dec_ref(v_c_830_);
v_a_855_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_862_ == 0)
{
v___x_857_ = v___x_844_;
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_844_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore___boxed(lean_object* v_c_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v_c_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_);
lean_dec(v_a_873_);
lean_dec_ref(v_a_872_);
lean_dec(v_a_871_);
lean_dec_ref(v_a_870_);
lean_dec(v_a_869_);
lean_dec_ref(v_a_868_);
lean_dec(v_a_867_);
lean_dec_ref(v_a_866_);
lean_dec(v_a_865_);
lean_dec(v_a_864_);
return v_res_875_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8(void){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v___x_890_ = lean_box(0);
v___x_891_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7));
v___x_892_ = l_Lean_mkConst(v___x_891_, v___x_890_);
return v___x_892_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10(void){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_894_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9));
v___x_895_ = l_Lean_stringToMessageData(v___x_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(lean_object* v_e_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_){
_start:
{
lean_object* v___x_914_; 
lean_inc_ref(v_e_896_);
v___x_914_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_896_, v_a_904_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; lean_object* v___x_916_; uint8_t v___x_917_; 
v_a_915_ = lean_ctor_get(v___x_914_, 0);
lean_inc(v_a_915_);
lean_dec_ref_known(v___x_914_, 1);
v___x_916_ = l_Lean_Expr_cleanupAnnotations(v_a_915_);
v___x_917_ = l_Lean_Expr_isApp(v___x_916_);
if (v___x_917_ == 0)
{
lean_dec_ref(v___x_916_);
lean_dec_ref(v_e_896_);
goto v___jp_908_;
}
else
{
lean_object* v_arg_918_; lean_object* v___x_919_; uint8_t v___x_920_; 
v_arg_918_ = lean_ctor_get(v___x_916_, 1);
lean_inc_ref(v_arg_918_);
v___x_919_ = l_Lean_Expr_appFnCleanup___redArg(v___x_916_);
v___x_920_ = l_Lean_Expr_isApp(v___x_919_);
if (v___x_920_ == 0)
{
lean_dec_ref(v___x_919_);
lean_dec_ref(v_arg_918_);
lean_dec_ref(v_e_896_);
goto v___jp_908_;
}
else
{
lean_object* v_arg_921_; lean_object* v___x_922_; uint8_t v___x_923_; 
v_arg_921_ = lean_ctor_get(v___x_919_, 1);
lean_inc_ref(v_arg_921_);
v___x_922_ = l_Lean_Expr_appFnCleanup___redArg(v___x_919_);
v___x_923_ = l_Lean_Expr_isApp(v___x_922_);
if (v___x_923_ == 0)
{
lean_dec_ref(v___x_922_);
lean_dec_ref(v_arg_921_);
lean_dec_ref(v_arg_918_);
lean_dec_ref(v_e_896_);
goto v___jp_908_;
}
else
{
lean_object* v_arg_924_; lean_object* v___x_925_; uint8_t v___x_926_; 
v_arg_924_ = lean_ctor_get(v___x_922_, 1);
lean_inc_ref(v_arg_924_);
v___x_925_ = l_Lean_Expr_appFnCleanup___redArg(v___x_922_);
v___x_926_ = l_Lean_Expr_isApp(v___x_925_);
if (v___x_926_ == 0)
{
lean_dec_ref(v___x_925_);
lean_dec_ref(v_arg_924_);
lean_dec_ref(v_arg_921_);
lean_dec_ref(v_arg_918_);
lean_dec_ref(v_e_896_);
goto v___jp_908_;
}
else
{
lean_object* v___x_927_; lean_object* v___x_928_; uint8_t v___x_929_; 
v___x_927_ = l_Lean_Expr_appFnCleanup___redArg(v___x_925_);
v___x_928_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_929_ = l_Lean_Expr_isConstOf(v___x_927_, v___x_928_);
lean_dec_ref(v___x_927_);
if (v___x_929_ == 0)
{
lean_dec_ref(v_arg_924_);
lean_dec_ref(v_arg_921_);
lean_dec_ref(v_arg_918_);
lean_dec_ref(v_e_896_);
goto v___jp_908_;
}
else
{
lean_object* v___x_930_; 
v___x_930_ = l_Lean_Meta_Structural_isInstDvdInt___redArg(v_arg_924_, v_a_904_);
if (lean_obj_tag(v___x_930_) == 0)
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_1031_; 
v_a_931_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_933_ = v___x_930_;
v_isShared_934_ = v_isSharedCheck_1031_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_930_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_1031_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
uint8_t v___x_935_; 
v___x_935_ = lean_unbox(v_a_931_);
lean_dec(v_a_931_);
if (v___x_935_ == 0)
{
lean_object* v___x_936_; lean_object* v___x_938_; 
lean_dec_ref(v_arg_921_);
lean_dec_ref(v_arg_918_);
lean_dec_ref(v_e_896_);
v___x_936_ = lean_box(0);
if (v_isShared_934_ == 0)
{
lean_ctor_set(v___x_933_, 0, v___x_936_);
v___x_938_ = v___x_933_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_936_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
else
{
lean_object* v___x_940_; 
lean_del_object(v___x_933_);
lean_inc_ref(v_arg_921_);
v___x_940_ = l_Lean_Meta_getIntValue_x3f(v_arg_921_, v_a_903_, v_a_904_, v_a_905_, v_a_906_);
if (lean_obj_tag(v___x_940_) == 0)
{
lean_object* v_a_941_; 
v_a_941_ = lean_ctor_get(v___x_940_, 0);
lean_inc(v_a_941_);
lean_dec_ref_known(v___x_940_, 1);
if (lean_obj_tag(v_a_941_) == 1)
{
lean_object* v_val_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_1007_; 
v_val_942_ = lean_ctor_get(v_a_941_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v_a_941_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_944_ = v_a_941_;
v_isShared_945_ = v_isSharedCheck_1007_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_val_942_);
lean_dec(v_a_941_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_1007_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
lean_object* v___x_946_; 
lean_inc_ref(v_e_896_);
v___x_946_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_896_, v_a_897_, v_a_901_, v_a_903_, v_a_904_, v_a_905_, v_a_906_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v_a_947_; uint8_t v___x_948_; 
v_a_947_ = lean_ctor_get(v___x_946_, 0);
lean_inc(v_a_947_);
lean_dec_ref_known(v___x_946_, 1);
v___x_948_ = lean_unbox(v_a_947_);
lean_dec(v_a_947_);
if (v___x_948_ == 0)
{
lean_object* v___x_949_; 
lean_del_object(v___x_944_);
lean_dec(v_val_942_);
lean_inc_ref(v_e_896_);
v___x_949_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_896_, v_a_897_, v_a_901_, v_a_903_, v_a_904_, v_a_905_, v_a_906_);
if (lean_obj_tag(v___x_949_) == 0)
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_975_; 
v_a_950_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_975_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_975_ == 0)
{
v___x_952_ = v___x_949_;
v_isShared_953_ = v_isSharedCheck_975_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_949_);
v___x_952_ = lean_box(0);
v_isShared_953_ = v_isSharedCheck_975_;
goto v_resetjp_951_;
}
v_resetjp_951_:
{
uint8_t v___x_954_; 
v___x_954_ = lean_unbox(v_a_950_);
lean_dec(v_a_950_);
if (v___x_954_ == 0)
{
lean_object* v___x_955_; lean_object* v___x_957_; 
lean_dec_ref(v_arg_921_);
lean_dec_ref(v_arg_918_);
lean_dec_ref(v_e_896_);
v___x_955_ = lean_box(0);
if (v_isShared_953_ == 0)
{
lean_ctor_set(v___x_952_, 0, v___x_955_);
v___x_957_ = v___x_952_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v___x_955_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
else
{
lean_object* v___x_959_; 
lean_del_object(v___x_952_);
lean_inc_ref(v_e_896_);
v___x_959_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v_a_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; 
v_a_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc(v_a_960_);
lean_dec_ref_known(v___x_959_, 1);
v___x_961_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8);
v___x_962_ = l_Lean_eagerReflBoolTrue;
v___x_963_ = l_Lean_Meta_mkOfEqFalseCore(v_e_896_, v_a_960_);
v___x_964_ = l_Lean_mkApp4(v___x_961_, v_arg_921_, v_arg_918_, v___x_962_, v___x_963_);
v___x_965_ = lean_unsigned_to_nat(0u);
v___x_966_ = l_Lean_Meta_Grind_pushNewFact(v___x_964_, v___x_965_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_);
return v___x_966_;
}
else
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
lean_dec_ref(v_arg_921_);
lean_dec_ref(v_arg_918_);
lean_dec_ref(v_e_896_);
v_a_967_ = lean_ctor_get(v___x_959_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_959_);
if (v_isSharedCheck_974_ == 0)
{
v___x_969_ = v___x_959_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_959_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_967_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
}
}
else
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_983_; 
lean_dec_ref(v_arg_921_);
lean_dec_ref(v_arg_918_);
lean_dec_ref(v_e_896_);
v_a_976_ = lean_ctor_get(v___x_949_, 0);
v_isSharedCheck_983_ = !lean_is_exclusive(v___x_949_);
if (v_isSharedCheck_983_ == 0)
{
v___x_978_ = v___x_949_;
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_949_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_983_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_981_; 
if (v_isShared_979_ == 0)
{
v___x_981_ = v___x_978_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_a_976_);
v___x_981_ = v_reuseFailAlloc_982_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
return v___x_981_;
}
}
}
}
else
{
lean_object* v___x_984_; 
lean_dec_ref(v_arg_921_);
v___x_984_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(v_arg_918_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_);
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v_a_985_; lean_object* v___x_987_; 
v_a_985_ = lean_ctor_get(v___x_984_, 0);
lean_inc(v_a_985_);
lean_dec_ref_known(v___x_984_, 1);
if (v_isShared_945_ == 0)
{
lean_ctor_set_tag(v___x_944_, 0);
lean_ctor_set(v___x_944_, 0, v_e_896_);
v___x_987_ = v___x_944_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_e_896_);
v___x_987_ = v_reuseFailAlloc_990_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_988_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_988_, 0, v_val_942_);
lean_ctor_set(v___x_988_, 1, v_a_985_);
lean_ctor_set(v___x_988_, 2, v___x_987_);
v___x_989_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v___x_988_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_);
return v___x_989_;
}
}
else
{
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
lean_del_object(v___x_944_);
lean_dec(v_val_942_);
lean_dec_ref(v_e_896_);
v_a_991_ = lean_ctor_get(v___x_984_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_984_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_984_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_984_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
}
else
{
lean_object* v_a_999_; lean_object* v___x_1001_; uint8_t v_isShared_1002_; uint8_t v_isSharedCheck_1006_; 
lean_del_object(v___x_944_);
lean_dec(v_val_942_);
lean_dec_ref(v_arg_921_);
lean_dec_ref(v_arg_918_);
lean_dec_ref(v_e_896_);
v_a_999_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_1001_ = v___x_946_;
v_isShared_1002_ = v_isSharedCheck_1006_;
goto v_resetjp_1000_;
}
else
{
lean_inc(v_a_999_);
lean_dec(v___x_946_);
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
}
else
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
lean_dec(v_a_941_);
lean_dec_ref(v_arg_921_);
lean_dec_ref(v_arg_918_);
v___x_1008_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10);
v___x_1009_ = l_Lean_indentExpr(v_e_896_);
v___x_1010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1008_);
lean_ctor_set(v___x_1010_, 1, v___x_1009_);
v___x_1011_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_901_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v_a_1012_; uint8_t v_verbose_1013_; 
v_a_1012_ = lean_ctor_get(v___x_1011_, 0);
lean_inc(v_a_1012_);
lean_dec_ref_known(v___x_1011_, 1);
v_verbose_1013_ = lean_ctor_get_uint8(v_a_1012_, 0);
lean_dec(v_a_1012_);
if (v_verbose_1013_ == 0)
{
lean_dec_ref_known(v___x_1010_, 2);
goto v___jp_911_;
}
else
{
lean_object* v___x_1014_; 
v___x_1014_ = l_Lean_Meta_Sym_reportIssue(v___x_1010_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_dec_ref_known(v___x_1014_, 1);
goto v___jp_911_;
}
else
{
return v___x_1014_;
}
}
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
lean_dec_ref_known(v___x_1010_, 2);
v_a_1015_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_1011_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_1011_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1015_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
lean_dec_ref(v_arg_921_);
lean_dec_ref(v_arg_918_);
lean_dec_ref(v_e_896_);
v_a_1023_ = lean_ctor_get(v___x_940_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_940_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_940_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_940_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
}
}
else
{
lean_object* v_a_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1039_; 
lean_dec_ref(v_arg_921_);
lean_dec_ref(v_arg_918_);
lean_dec_ref(v_e_896_);
v_a_1032_ = lean_ctor_get(v___x_930_, 0);
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_930_);
if (v_isSharedCheck_1039_ == 0)
{
v___x_1034_ = v___x_930_;
v_isShared_1035_ = v_isSharedCheck_1039_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_a_1032_);
lean_dec(v___x_930_);
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
}
}
}
}
else
{
lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1047_; 
lean_dec_ref(v_e_896_);
v_a_1040_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1042_ = v___x_914_;
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_914_);
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
v___jp_908_:
{
lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_909_ = lean_box(0);
v___x_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_910_, 0, v___x_909_);
return v___x_910_;
}
v___jp_911_:
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = lean_box(0);
v___x_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_913_, 0, v___x_912_);
return v___x_913_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___boxed(lean_object* v_e_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(v_e_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_);
lean_dec(v_a_1058_);
lean_dec_ref(v_a_1057_);
lean_dec(v_a_1056_);
lean_dec_ref(v_a_1055_);
lean_dec(v_a_1054_);
lean_dec_ref(v_a_1053_);
lean_dec(v_a_1052_);
lean_dec_ref(v_a_1051_);
lean_dec(v_a_1050_);
lean_dec(v_a_1049_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd_spec__0(lean_object* v_a_1061_){
_start:
{
lean_object* v___x_1062_; 
v___x_1062_ = lean_nat_to_int(v_a_1061_);
return v___x_1062_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3(void){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1068_ = lean_box(0);
v___x_1069_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2));
v___x_1070_ = l_Lean_mkConst(v___x_1069_, v___x_1068_);
return v___x_1070_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7(void){
_start:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1077_ = lean_box(0);
v___x_1078_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6));
v___x_1079_ = l_Lean_mkConst(v___x_1078_, v___x_1077_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(lean_object* v_e_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_){
_start:
{
lean_object* v___x_1098_; uint8_t v___x_1099_; 
lean_inc_ref(v_e_1080_);
v___x_1098_ = l_Lean_Expr_cleanupAnnotations(v_e_1080_);
v___x_1099_ = l_Lean_Expr_isApp(v___x_1098_);
if (v___x_1099_ == 0)
{
lean_dec_ref(v___x_1098_);
lean_dec_ref(v_e_1080_);
goto v___jp_1092_;
}
else
{
lean_object* v_arg_1100_; lean_object* v___x_1101_; uint8_t v___x_1102_; 
v_arg_1100_ = lean_ctor_get(v___x_1098_, 1);
lean_inc_ref(v_arg_1100_);
v___x_1101_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1098_);
v___x_1102_ = l_Lean_Expr_isApp(v___x_1101_);
if (v___x_1102_ == 0)
{
lean_dec_ref(v___x_1101_);
lean_dec_ref(v_arg_1100_);
lean_dec_ref(v_e_1080_);
goto v___jp_1092_;
}
else
{
lean_object* v_arg_1103_; lean_object* v___x_1104_; uint8_t v___x_1105_; 
v_arg_1103_ = lean_ctor_get(v___x_1101_, 1);
lean_inc_ref(v_arg_1103_);
v___x_1104_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1101_);
v___x_1105_ = l_Lean_Expr_isApp(v___x_1104_);
if (v___x_1105_ == 0)
{
lean_dec_ref(v___x_1104_);
lean_dec_ref(v_arg_1103_);
lean_dec_ref(v_arg_1100_);
lean_dec_ref(v_e_1080_);
goto v___jp_1092_;
}
else
{
lean_object* v_arg_1106_; lean_object* v___x_1107_; uint8_t v___x_1108_; 
v_arg_1106_ = lean_ctor_get(v___x_1104_, 1);
lean_inc_ref(v_arg_1106_);
v___x_1107_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1104_);
v___x_1108_ = l_Lean_Expr_isApp(v___x_1107_);
if (v___x_1108_ == 0)
{
lean_dec_ref(v___x_1107_);
lean_dec_ref(v_arg_1106_);
lean_dec_ref(v_arg_1103_);
lean_dec_ref(v_arg_1100_);
lean_dec_ref(v_e_1080_);
goto v___jp_1092_;
}
else
{
lean_object* v___x_1109_; lean_object* v___x_1110_; uint8_t v___x_1111_; 
v___x_1109_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1107_);
v___x_1110_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1111_ = l_Lean_Expr_isConstOf(v___x_1109_, v___x_1110_);
lean_dec_ref(v___x_1109_);
if (v___x_1111_ == 0)
{
lean_dec_ref(v_arg_1106_);
lean_dec_ref(v_arg_1103_);
lean_dec_ref(v_arg_1100_);
lean_dec_ref(v_e_1080_);
goto v___jp_1092_;
}
else
{
lean_object* v___x_1112_; 
v___x_1112_ = l_Lean_Meta_Structural_isInstDvdNat___redArg(v_arg_1106_, v_a_1088_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1244_; 
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1115_ = v___x_1112_;
v_isShared_1116_ = v_isSharedCheck_1244_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1112_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1244_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
uint8_t v___x_1117_; 
v___x_1117_ = lean_unbox(v_a_1113_);
lean_dec(v_a_1113_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; lean_object* v___x_1120_; 
lean_dec_ref(v_arg_1103_);
lean_dec_ref(v_arg_1100_);
lean_dec_ref(v_e_1080_);
v___x_1118_ = lean_box(0);
if (v_isShared_1116_ == 0)
{
lean_ctor_set(v___x_1115_, 0, v___x_1118_);
v___x_1120_ = v___x_1115_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___x_1118_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
else
{
lean_object* v___x_1122_; 
lean_del_object(v___x_1115_);
v___x_1122_ = l_Lean_Meta_getNatValue_x3f(v_arg_1103_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_object* v_a_1123_; 
v_a_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc(v_a_1123_);
lean_dec_ref_known(v___x_1122_, 1);
if (lean_obj_tag(v_a_1123_) == 1)
{
lean_object* v_val_1124_; lean_object* v___x_1125_; 
v_val_1124_ = lean_ctor_get(v_a_1123_, 0);
lean_inc(v_val_1124_);
lean_dec_ref_known(v_a_1123_, 1);
lean_inc_ref(v_e_1080_);
v___x_1125_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_1080_, v_a_1081_, v_a_1085_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_object* v_a_1126_; uint8_t v___x_1127_; 
v_a_1126_ = lean_ctor_get(v___x_1125_, 0);
lean_inc(v_a_1126_);
lean_dec_ref_known(v___x_1125_, 1);
v___x_1127_ = lean_unbox(v_a_1126_);
lean_dec(v_a_1126_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; 
lean_dec(v_val_1124_);
lean_inc_ref(v_e_1080_);
v___x_1128_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_1080_, v_a_1081_, v_a_1085_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1153_; 
v_a_1129_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1131_ = v___x_1128_;
v_isShared_1132_ = v_isSharedCheck_1153_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v___x_1128_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1153_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
uint8_t v___x_1133_; 
v___x_1133_ = lean_unbox(v_a_1129_);
lean_dec(v_a_1129_);
if (v___x_1133_ == 0)
{
lean_object* v___x_1134_; lean_object* v___x_1136_; 
lean_dec_ref(v_arg_1103_);
lean_dec_ref(v_arg_1100_);
lean_dec_ref(v_e_1080_);
v___x_1134_ = lean_box(0);
if (v_isShared_1132_ == 0)
{
lean_ctor_set(v___x_1131_, 0, v___x_1134_);
v___x_1136_ = v___x_1131_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1134_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
else
{
lean_object* v___x_1138_; 
lean_del_object(v___x_1131_);
lean_inc_ref(v_e_1080_);
v___x_1138_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_);
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_object* v_a_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v_a_1139_ = lean_ctor_get(v___x_1138_, 0);
lean_inc(v_a_1139_);
lean_dec_ref_known(v___x_1138_, 1);
v___x_1140_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3);
v___x_1141_ = l_Lean_Meta_mkOfEqFalseCore(v_e_1080_, v_a_1139_);
v___x_1142_ = l_Lean_mkApp3(v___x_1140_, v_arg_1103_, v_arg_1100_, v___x_1141_);
v___x_1143_ = lean_unsigned_to_nat(0u);
v___x_1144_ = l_Lean_Meta_Grind_pushNewFact(v___x_1142_, v___x_1143_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_);
return v___x_1144_;
}
else
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1152_; 
lean_dec_ref(v_arg_1103_);
lean_dec_ref(v_arg_1100_);
lean_dec_ref(v_e_1080_);
v_a_1145_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1147_ = v___x_1138_;
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1138_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1150_; 
if (v_isShared_1148_ == 0)
{
v___x_1150_ = v___x_1147_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_a_1145_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
}
}
else
{
lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1161_; 
lean_dec_ref(v_arg_1103_);
lean_dec_ref(v_arg_1100_);
lean_dec_ref(v_e_1080_);
v_a_1154_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1156_ = v___x_1128_;
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___x_1128_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1159_; 
if (v_isShared_1157_ == 0)
{
v___x_1159_ = v___x_1156_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_a_1154_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
else
{
lean_object* v___x_1162_; 
lean_inc_ref(v_arg_1103_);
v___x_1162_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_1103_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_);
if (lean_obj_tag(v___x_1162_) == 0)
{
lean_object* v_a_1163_; lean_object* v_fst_1164_; lean_object* v_snd_1165_; lean_object* v___x_1166_; 
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
lean_inc(v_a_1163_);
lean_dec_ref_known(v___x_1162_, 1);
v_fst_1164_ = lean_ctor_get(v_a_1163_, 0);
lean_inc(v_fst_1164_);
v_snd_1165_ = lean_ctor_get(v_a_1163_, 1);
lean_inc(v_snd_1165_);
lean_dec(v_a_1163_);
lean_inc_ref(v_arg_1100_);
v___x_1166_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_1100_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_);
if (lean_obj_tag(v___x_1166_) == 0)
{
lean_object* v_a_1167_; lean_object* v_fst_1168_; lean_object* v_snd_1169_; lean_object* v___x_1170_; 
v_a_1167_ = lean_ctor_get(v___x_1166_, 0);
lean_inc(v_a_1167_);
lean_dec_ref_known(v___x_1166_, 1);
v_fst_1168_ = lean_ctor_get(v_a_1167_, 0);
lean_inc(v_fst_1168_);
v_snd_1169_ = lean_ctor_get(v_a_1167_, 1);
lean_inc(v_snd_1169_);
lean_dec(v_a_1167_);
v___x_1170_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1080_, v_a_1081_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v_a_1171_; lean_object* v___x_1172_; 
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
lean_inc(v_a_1171_);
lean_dec_ref_known(v___x_1170_, 1);
lean_inc(v_fst_1168_);
v___x_1172_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_1168_, v_a_1171_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_a_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_a_1173_);
lean_dec_ref_known(v___x_1172_, 1);
v___x_1174_ = l_Int_Internal_Linear_Expr_norm(v_a_1173_);
v___x_1175_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7);
v___x_1176_ = l_Lean_mkApp6(v___x_1175_, v_arg_1103_, v_arg_1100_, v_fst_1164_, v_fst_1168_, v_snd_1165_, v_snd_1169_);
lean_inc(v_val_1124_);
v___x_1177_ = lean_nat_to_int(v_val_1124_);
v___x_1178_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1178_, 0, v_e_1080_);
lean_ctor_set(v___x_1178_, 1, v___x_1176_);
lean_ctor_set(v___x_1178_, 2, v_val_1124_);
lean_ctor_set(v___x_1178_, 3, v_a_1173_);
v___x_1179_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1177_);
lean_ctor_set(v___x_1179_, 1, v___x_1174_);
lean_ctor_set(v___x_1179_, 2, v___x_1178_);
v___x_1180_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v___x_1179_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_);
return v___x_1180_;
}
else
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1188_; 
lean_dec(v_snd_1169_);
lean_dec(v_fst_1168_);
lean_dec(v_snd_1165_);
lean_dec(v_fst_1164_);
lean_dec(v_val_1124_);
lean_dec_ref(v_arg_1103_);
lean_dec_ref(v_arg_1100_);
lean_dec_ref(v_e_1080_);
v_a_1181_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1183_ = v___x_1172_;
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___x_1172_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1186_; 
if (v_isShared_1184_ == 0)
{
v___x_1186_ = v___x_1183_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_a_1181_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
else
{
lean_object* v_a_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1196_; 
lean_dec(v_snd_1169_);
lean_dec(v_fst_1168_);
lean_dec(v_snd_1165_);
lean_dec(v_fst_1164_);
lean_dec(v_val_1124_);
lean_dec_ref(v_arg_1103_);
lean_dec_ref(v_arg_1100_);
lean_dec_ref(v_e_1080_);
v_a_1189_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1191_ = v___x_1170_;
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_a_1189_);
lean_dec(v___x_1170_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1196_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v___x_1194_; 
if (v_isShared_1192_ == 0)
{
v___x_1194_ = v___x_1191_;
goto v_reusejp_1193_;
}
else
{
lean_object* v_reuseFailAlloc_1195_; 
v_reuseFailAlloc_1195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1195_, 0, v_a_1189_);
v___x_1194_ = v_reuseFailAlloc_1195_;
goto v_reusejp_1193_;
}
v_reusejp_1193_:
{
return v___x_1194_;
}
}
}
}
else
{
lean_object* v_a_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1204_; 
lean_dec(v_snd_1165_);
lean_dec(v_fst_1164_);
lean_dec(v_val_1124_);
lean_dec_ref(v_arg_1103_);
lean_dec_ref(v_arg_1100_);
lean_dec_ref(v_e_1080_);
v_a_1197_ = lean_ctor_get(v___x_1166_, 0);
v_isSharedCheck_1204_ = !lean_is_exclusive(v___x_1166_);
if (v_isSharedCheck_1204_ == 0)
{
v___x_1199_ = v___x_1166_;
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_a_1197_);
lean_dec(v___x_1166_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1204_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___x_1202_; 
if (v_isShared_1200_ == 0)
{
v___x_1202_ = v___x_1199_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_a_1197_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
else
{
lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1212_; 
lean_dec(v_val_1124_);
lean_dec_ref(v_arg_1103_);
lean_dec_ref(v_arg_1100_);
lean_dec_ref(v_e_1080_);
v_a_1205_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1207_ = v___x_1162_;
v_isShared_1208_ = v_isSharedCheck_1212_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_a_1205_);
lean_dec(v___x_1162_);
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
}
else
{
lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1220_; 
lean_dec(v_val_1124_);
lean_dec_ref(v_arg_1103_);
lean_dec_ref(v_arg_1100_);
lean_dec_ref(v_e_1080_);
v_a_1213_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1215_ = v___x_1125_;
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v___x_1125_);
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
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
lean_dec(v_a_1123_);
lean_dec_ref(v_arg_1103_);
lean_dec_ref(v_arg_1100_);
v___x_1221_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10);
v___x_1222_ = l_Lean_indentExpr(v_e_1080_);
v___x_1223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1223_, 0, v___x_1221_);
lean_ctor_set(v___x_1223_, 1, v___x_1222_);
v___x_1224_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1085_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v_a_1225_; uint8_t v_verbose_1226_; 
v_a_1225_ = lean_ctor_get(v___x_1224_, 0);
lean_inc(v_a_1225_);
lean_dec_ref_known(v___x_1224_, 1);
v_verbose_1226_ = lean_ctor_get_uint8(v_a_1225_, 0);
lean_dec(v_a_1225_);
if (v_verbose_1226_ == 0)
{
lean_dec_ref_known(v___x_1223_, 2);
goto v___jp_1095_;
}
else
{
lean_object* v___x_1227_; 
v___x_1227_ = l_Lean_Meta_Sym_reportIssue(v___x_1223_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_dec_ref_known(v___x_1227_, 1);
goto v___jp_1095_;
}
else
{
return v___x_1227_;
}
}
}
else
{
lean_object* v_a_1228_; lean_object* v___x_1230_; uint8_t v_isShared_1231_; uint8_t v_isSharedCheck_1235_; 
lean_dec_ref_known(v___x_1223_, 2);
v_a_1228_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1235_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1235_ == 0)
{
v___x_1230_ = v___x_1224_;
v_isShared_1231_ = v_isSharedCheck_1235_;
goto v_resetjp_1229_;
}
else
{
lean_inc(v_a_1228_);
lean_dec(v___x_1224_);
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
}
else
{
lean_object* v_a_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1243_; 
lean_dec_ref(v_arg_1103_);
lean_dec_ref(v_arg_1100_);
lean_dec_ref(v_e_1080_);
v_a_1236_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1238_ = v___x_1122_;
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_a_1236_);
lean_dec(v___x_1122_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1243_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v___x_1241_; 
if (v_isShared_1239_ == 0)
{
v___x_1241_ = v___x_1238_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v_a_1236_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
}
}
}
}
else
{
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
lean_dec_ref(v_arg_1103_);
lean_dec_ref(v_arg_1100_);
lean_dec_ref(v_e_1080_);
v_a_1245_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1247_ = v___x_1112_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1112_);
v___x_1247_ = lean_box(0);
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
v_resetjp_1246_:
{
lean_object* v___x_1250_; 
if (v_isShared_1248_ == 0)
{
v___x_1250_ = v___x_1247_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v_a_1245_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
}
}
}
}
}
v___jp_1092_:
{
lean_object* v___x_1093_; lean_object* v___x_1094_; 
v___x_1093_ = lean_box(0);
v___x_1094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1093_);
return v___x_1094_;
}
v___jp_1095_:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; 
v___x_1096_ = lean_box(0);
v___x_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1096_);
return v___x_1097_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___boxed(lean_object* v_e_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(v_e_1253_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_);
lean_dec(v_a_1263_);
lean_dec_ref(v_a_1262_);
lean_dec(v_a_1261_);
lean_dec_ref(v_a_1260_);
lean_dec(v_a_1259_);
lean_dec_ref(v_a_1258_);
lean_dec(v_a_1257_);
lean_dec_ref(v_a_1256_);
lean_dec(v_a_1255_);
lean_dec(v_a_1254_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(lean_object* v_e_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_){
_start:
{
lean_object* v___x_1283_; 
v___x_1283_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1271_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1319_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1286_ = v___x_1283_;
v_isShared_1287_ = v_isSharedCheck_1319_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1283_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1319_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
uint8_t v_lia_1288_; 
v_lia_1288_ = lean_ctor_get_uint8(v_a_1284_, sizeof(void*)*14 + 23);
lean_dec(v_a_1284_);
if (v_lia_1288_ == 0)
{
lean_object* v___x_1289_; lean_object* v___x_1291_; 
lean_dec_ref(v_e_1268_);
v___x_1289_ = lean_box(0);
if (v_isShared_1287_ == 0)
{
lean_ctor_set(v___x_1286_, 0, v___x_1289_);
v___x_1291_ = v___x_1286_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1289_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
else
{
lean_object* v___x_1293_; 
lean_del_object(v___x_1286_);
lean_inc_ref(v_e_1268_);
v___x_1293_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1268_, v_a_1276_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v_a_1294_; lean_object* v___x_1295_; uint8_t v___x_1296_; 
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_a_1294_);
lean_dec_ref_known(v___x_1293_, 1);
v___x_1295_ = l_Lean_Expr_cleanupAnnotations(v_a_1294_);
v___x_1296_ = l_Lean_Expr_isApp(v___x_1295_);
if (v___x_1296_ == 0)
{
lean_dec_ref(v___x_1295_);
lean_dec_ref(v_e_1268_);
goto v___jp_1280_;
}
else
{
lean_object* v___x_1297_; uint8_t v___x_1298_; 
v___x_1297_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1295_);
v___x_1298_ = l_Lean_Expr_isApp(v___x_1297_);
if (v___x_1298_ == 0)
{
lean_dec_ref(v___x_1297_);
lean_dec_ref(v_e_1268_);
goto v___jp_1280_;
}
else
{
lean_object* v___x_1299_; uint8_t v___x_1300_; 
v___x_1299_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1297_);
v___x_1300_ = l_Lean_Expr_isApp(v___x_1299_);
if (v___x_1300_ == 0)
{
lean_dec_ref(v___x_1299_);
lean_dec_ref(v_e_1268_);
goto v___jp_1280_;
}
else
{
lean_object* v___x_1301_; uint8_t v___x_1302_; 
v___x_1301_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1299_);
v___x_1302_ = l_Lean_Expr_isApp(v___x_1301_);
if (v___x_1302_ == 0)
{
lean_dec_ref(v___x_1301_);
lean_dec_ref(v_e_1268_);
goto v___jp_1280_;
}
else
{
lean_object* v_arg_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; uint8_t v___x_1306_; 
v_arg_1303_ = lean_ctor_get(v___x_1301_, 1);
lean_inc_ref(v_arg_1303_);
v___x_1304_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1301_);
v___x_1305_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1306_ = l_Lean_Expr_isConstOf(v___x_1304_, v___x_1305_);
lean_dec_ref(v___x_1304_);
if (v___x_1306_ == 0)
{
lean_dec_ref(v_arg_1303_);
lean_dec_ref(v_e_1268_);
goto v___jp_1280_;
}
else
{
lean_object* v___x_1307_; uint8_t v___x_1308_; 
v___x_1307_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0));
v___x_1308_ = l_Lean_Expr_isConstOf(v_arg_1303_, v___x_1307_);
lean_dec_ref(v_arg_1303_);
if (v___x_1308_ == 0)
{
lean_object* v___x_1309_; 
v___x_1309_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(v_e_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_);
return v___x_1309_;
}
else
{
lean_object* v___x_1310_; 
v___x_1310_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(v_e_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_);
return v___x_1310_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1318_; 
lean_dec_ref(v_e_1268_);
v_a_1311_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1313_ = v___x_1293_;
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1293_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
if (v_isShared_1314_ == 0)
{
v___x_1316_ = v___x_1313_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_a_1311_);
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
}
}
else
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1327_; 
lean_dec_ref(v_e_1268_);
v_a_1320_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1322_ = v___x_1283_;
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1283_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1325_; 
if (v_isShared_1323_ == 0)
{
v___x_1325_ = v___x_1322_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_a_1320_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
v___jp_1280_:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = lean_box(0);
v___x_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1281_);
return v___x_1282_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed(lean_object* v_e_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_){
_start:
{
lean_object* v_res_1340_; 
v_res_1340_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(v_e_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_);
lean_dec(v_a_1338_);
lean_dec_ref(v_a_1337_);
lean_dec(v_a_1336_);
lean_dec_ref(v_a_1335_);
lean_dec(v_a_1334_);
lean_dec_ref(v_a_1333_);
lean_dec(v_a_1332_);
lean_dec_ref(v_a_1331_);
lean_dec(v_a_1330_);
lean_dec(v_a_1329_);
return v_res_1340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; 
v___x_1342_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1343_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed), 12, 0);
v___x_1344_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_1342_, v___x_1343_);
return v___x_1344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_9____boxed(lean_object* v_a_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_9_();
return v_res_1346_;
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
