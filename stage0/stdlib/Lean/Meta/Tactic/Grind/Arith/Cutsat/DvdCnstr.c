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
lean_object* v_vars_390_; lean_object* v_varMap_391_; lean_object* v_vars_x27_392_; lean_object* v_varMap_x27_393_; lean_object* v_natToIntMap_394_; lean_object* v_natDef_395_; lean_object* v_dvds_396_; lean_object* v_lowers_397_; lean_object* v_uppers_398_; lean_object* v_diseqs_399_; lean_object* v_elimEqs_400_; lean_object* v_elimStack_401_; lean_object* v_occurs_402_; lean_object* v_assignment_403_; lean_object* v_nextCnstrId_404_; uint8_t v_caseSplits_405_; lean_object* v_steps_406_; lean_object* v_conflict_x3f_407_; lean_object* v_diseqSplits_408_; lean_object* v_divMod_409_; uint8_t v_usedCommRing_410_; lean_object* v_nonlinearOccs_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_420_; 
v_vars_390_ = lean_ctor_get(v_s_389_, 0);
v_varMap_391_ = lean_ctor_get(v_s_389_, 1);
v_vars_x27_392_ = lean_ctor_get(v_s_389_, 2);
v_varMap_x27_393_ = lean_ctor_get(v_s_389_, 3);
v_natToIntMap_394_ = lean_ctor_get(v_s_389_, 4);
v_natDef_395_ = lean_ctor_get(v_s_389_, 5);
v_dvds_396_ = lean_ctor_get(v_s_389_, 6);
v_lowers_397_ = lean_ctor_get(v_s_389_, 7);
v_uppers_398_ = lean_ctor_get(v_s_389_, 8);
v_diseqs_399_ = lean_ctor_get(v_s_389_, 9);
v_elimEqs_400_ = lean_ctor_get(v_s_389_, 10);
v_elimStack_401_ = lean_ctor_get(v_s_389_, 11);
v_occurs_402_ = lean_ctor_get(v_s_389_, 12);
v_assignment_403_ = lean_ctor_get(v_s_389_, 13);
v_nextCnstrId_404_ = lean_ctor_get(v_s_389_, 14);
v_caseSplits_405_ = lean_ctor_get_uint8(v_s_389_, sizeof(void*)*20);
v_steps_406_ = lean_ctor_get(v_s_389_, 15);
v_conflict_x3f_407_ = lean_ctor_get(v_s_389_, 16);
v_diseqSplits_408_ = lean_ctor_get(v_s_389_, 17);
v_divMod_409_ = lean_ctor_get(v_s_389_, 18);
v_usedCommRing_410_ = lean_ctor_get_uint8(v_s_389_, sizeof(void*)*20 + 1);
v_nonlinearOccs_411_ = lean_ctor_get(v_s_389_, 19);
v_isSharedCheck_420_ = !lean_is_exclusive(v_s_389_);
if (v_isSharedCheck_420_ == 0)
{
v___x_413_ = v_s_389_;
v_isShared_414_ = v_isSharedCheck_420_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_nonlinearOccs_411_);
lean_inc(v_divMod_409_);
lean_inc(v_diseqSplits_408_);
lean_inc(v_conflict_x3f_407_);
lean_inc(v_steps_406_);
lean_inc(v_nextCnstrId_404_);
lean_inc(v_assignment_403_);
lean_inc(v_occurs_402_);
lean_inc(v_elimStack_401_);
lean_inc(v_elimEqs_400_);
lean_inc(v_diseqs_399_);
lean_inc(v_uppers_398_);
lean_inc(v_lowers_397_);
lean_inc(v_dvds_396_);
lean_inc(v_natDef_395_);
lean_inc(v_natToIntMap_394_);
lean_inc(v_varMap_x27_393_);
lean_inc(v_vars_x27_392_);
lean_inc(v_varMap_391_);
lean_inc(v_vars_390_);
lean_dec(v_s_389_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_420_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_418_; 
v___x_415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_415_, 0, v_a_387_);
v___x_416_ = l_Lean_PersistentArray_set___redArg(v_dvds_396_, v_v_388_, v___x_415_);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 6, v___x_416_);
v___x_418_ = v___x_413_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 20, 2);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_vars_390_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v_varMap_391_);
lean_ctor_set(v_reuseFailAlloc_419_, 2, v_vars_x27_392_);
lean_ctor_set(v_reuseFailAlloc_419_, 3, v_varMap_x27_393_);
lean_ctor_set(v_reuseFailAlloc_419_, 4, v_natToIntMap_394_);
lean_ctor_set(v_reuseFailAlloc_419_, 5, v_natDef_395_);
lean_ctor_set(v_reuseFailAlloc_419_, 6, v___x_416_);
lean_ctor_set(v_reuseFailAlloc_419_, 7, v_lowers_397_);
lean_ctor_set(v_reuseFailAlloc_419_, 8, v_uppers_398_);
lean_ctor_set(v_reuseFailAlloc_419_, 9, v_diseqs_399_);
lean_ctor_set(v_reuseFailAlloc_419_, 10, v_elimEqs_400_);
lean_ctor_set(v_reuseFailAlloc_419_, 11, v_elimStack_401_);
lean_ctor_set(v_reuseFailAlloc_419_, 12, v_occurs_402_);
lean_ctor_set(v_reuseFailAlloc_419_, 13, v_assignment_403_);
lean_ctor_set(v_reuseFailAlloc_419_, 14, v_nextCnstrId_404_);
lean_ctor_set(v_reuseFailAlloc_419_, 15, v_steps_406_);
lean_ctor_set(v_reuseFailAlloc_419_, 16, v_conflict_x3f_407_);
lean_ctor_set(v_reuseFailAlloc_419_, 17, v_diseqSplits_408_);
lean_ctor_set(v_reuseFailAlloc_419_, 18, v_divMod_409_);
lean_ctor_set(v_reuseFailAlloc_419_, 19, v_nonlinearOccs_411_);
lean_ctor_set_uint8(v_reuseFailAlloc_419_, sizeof(void*)*20, v_caseSplits_405_);
lean_ctor_set_uint8(v_reuseFailAlloc_419_, sizeof(void*)*20 + 1, v_usedCommRing_410_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed(lean_object* v_a_421_, lean_object* v_v_422_, lean_object* v_s_423_){
_start:
{
lean_object* v_res_424_; 
v_res_424_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(v_a_421_, v_v_422_, v_s_423_);
lean_dec(v_v_422_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(lean_object* v_v_425_, lean_object* v_s_426_){
_start:
{
lean_object* v_vars_427_; lean_object* v_varMap_428_; lean_object* v_vars_x27_429_; lean_object* v_varMap_x27_430_; lean_object* v_natToIntMap_431_; lean_object* v_natDef_432_; lean_object* v_dvds_433_; lean_object* v_lowers_434_; lean_object* v_uppers_435_; lean_object* v_diseqs_436_; lean_object* v_elimEqs_437_; lean_object* v_elimStack_438_; lean_object* v_occurs_439_; lean_object* v_assignment_440_; lean_object* v_nextCnstrId_441_; uint8_t v_caseSplits_442_; lean_object* v_steps_443_; lean_object* v_conflict_x3f_444_; lean_object* v_diseqSplits_445_; lean_object* v_divMod_446_; uint8_t v_usedCommRing_447_; lean_object* v_nonlinearOccs_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_457_; 
v_vars_427_ = lean_ctor_get(v_s_426_, 0);
v_varMap_428_ = lean_ctor_get(v_s_426_, 1);
v_vars_x27_429_ = lean_ctor_get(v_s_426_, 2);
v_varMap_x27_430_ = lean_ctor_get(v_s_426_, 3);
v_natToIntMap_431_ = lean_ctor_get(v_s_426_, 4);
v_natDef_432_ = lean_ctor_get(v_s_426_, 5);
v_dvds_433_ = lean_ctor_get(v_s_426_, 6);
v_lowers_434_ = lean_ctor_get(v_s_426_, 7);
v_uppers_435_ = lean_ctor_get(v_s_426_, 8);
v_diseqs_436_ = lean_ctor_get(v_s_426_, 9);
v_elimEqs_437_ = lean_ctor_get(v_s_426_, 10);
v_elimStack_438_ = lean_ctor_get(v_s_426_, 11);
v_occurs_439_ = lean_ctor_get(v_s_426_, 12);
v_assignment_440_ = lean_ctor_get(v_s_426_, 13);
v_nextCnstrId_441_ = lean_ctor_get(v_s_426_, 14);
v_caseSplits_442_ = lean_ctor_get_uint8(v_s_426_, sizeof(void*)*20);
v_steps_443_ = lean_ctor_get(v_s_426_, 15);
v_conflict_x3f_444_ = lean_ctor_get(v_s_426_, 16);
v_diseqSplits_445_ = lean_ctor_get(v_s_426_, 17);
v_divMod_446_ = lean_ctor_get(v_s_426_, 18);
v_usedCommRing_447_ = lean_ctor_get_uint8(v_s_426_, sizeof(void*)*20 + 1);
v_nonlinearOccs_448_ = lean_ctor_get(v_s_426_, 19);
v_isSharedCheck_457_ = !lean_is_exclusive(v_s_426_);
if (v_isSharedCheck_457_ == 0)
{
v___x_450_ = v_s_426_;
v_isShared_451_ = v_isSharedCheck_457_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_nonlinearOccs_448_);
lean_inc(v_divMod_446_);
lean_inc(v_diseqSplits_445_);
lean_inc(v_conflict_x3f_444_);
lean_inc(v_steps_443_);
lean_inc(v_nextCnstrId_441_);
lean_inc(v_assignment_440_);
lean_inc(v_occurs_439_);
lean_inc(v_elimStack_438_);
lean_inc(v_elimEqs_437_);
lean_inc(v_diseqs_436_);
lean_inc(v_uppers_435_);
lean_inc(v_lowers_434_);
lean_inc(v_dvds_433_);
lean_inc(v_natDef_432_);
lean_inc(v_natToIntMap_431_);
lean_inc(v_varMap_x27_430_);
lean_inc(v_vars_x27_429_);
lean_inc(v_varMap_428_);
lean_inc(v_vars_427_);
lean_dec(v_s_426_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_457_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_455_; 
v___x_452_ = lean_box(0);
v___x_453_ = l_Lean_PersistentArray_set___redArg(v_dvds_433_, v_v_425_, v___x_452_);
if (v_isShared_451_ == 0)
{
lean_ctor_set(v___x_450_, 6, v___x_453_);
v___x_455_ = v___x_450_;
goto v_reusejp_454_;
}
else
{
lean_object* v_reuseFailAlloc_456_; 
v_reuseFailAlloc_456_ = lean_alloc_ctor(0, 20, 2);
lean_ctor_set(v_reuseFailAlloc_456_, 0, v_vars_427_);
lean_ctor_set(v_reuseFailAlloc_456_, 1, v_varMap_428_);
lean_ctor_set(v_reuseFailAlloc_456_, 2, v_vars_x27_429_);
lean_ctor_set(v_reuseFailAlloc_456_, 3, v_varMap_x27_430_);
lean_ctor_set(v_reuseFailAlloc_456_, 4, v_natToIntMap_431_);
lean_ctor_set(v_reuseFailAlloc_456_, 5, v_natDef_432_);
lean_ctor_set(v_reuseFailAlloc_456_, 6, v___x_453_);
lean_ctor_set(v_reuseFailAlloc_456_, 7, v_lowers_434_);
lean_ctor_set(v_reuseFailAlloc_456_, 8, v_uppers_435_);
lean_ctor_set(v_reuseFailAlloc_456_, 9, v_diseqs_436_);
lean_ctor_set(v_reuseFailAlloc_456_, 10, v_elimEqs_437_);
lean_ctor_set(v_reuseFailAlloc_456_, 11, v_elimStack_438_);
lean_ctor_set(v_reuseFailAlloc_456_, 12, v_occurs_439_);
lean_ctor_set(v_reuseFailAlloc_456_, 13, v_assignment_440_);
lean_ctor_set(v_reuseFailAlloc_456_, 14, v_nextCnstrId_441_);
lean_ctor_set(v_reuseFailAlloc_456_, 15, v_steps_443_);
lean_ctor_set(v_reuseFailAlloc_456_, 16, v_conflict_x3f_444_);
lean_ctor_set(v_reuseFailAlloc_456_, 17, v_diseqSplits_445_);
lean_ctor_set(v_reuseFailAlloc_456_, 18, v_divMod_446_);
lean_ctor_set(v_reuseFailAlloc_456_, 19, v_nonlinearOccs_448_);
lean_ctor_set_uint8(v_reuseFailAlloc_456_, sizeof(void*)*20, v_caseSplits_442_);
lean_ctor_set_uint8(v_reuseFailAlloc_456_, sizeof(void*)*20 + 1, v_usedCommRing_447_);
v___x_455_ = v_reuseFailAlloc_456_;
goto v_reusejp_454_;
}
v_reusejp_454_:
{
return v___x_455_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed(lean_object* v_v_458_, lean_object* v_s_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(v_v_458_, v_s_459_);
lean_dec(v_v_458_);
return v_res_460_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5(void){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_469_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4));
v___x_470_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
v___x_471_ = l_Lean_Name_append(v___x_470_, v___x_469_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(lean_object* v_c_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_, lean_object* v_a_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_){
_start:
{
lean_object* v___y_488_; lean_object* v___y_489_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v___y_493_; lean_object* v___y_494_; lean_object* v___y_499_; lean_object* v___y_500_; lean_object* v___y_501_; lean_object* v___y_502_; lean_object* v___y_503_; lean_object* v___y_504_; lean_object* v___y_505_; lean_object* v___y_506_; lean_object* v___y_507_; lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_602_; lean_object* v___y_603_; lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___y_611_; lean_object* v___y_612_; lean_object* v_toCold_624_; lean_object* v_currRecDepth_625_; lean_object* v_ref_626_; uint16_t v_optionFlags_627_; uint8_t v_suppressElabErrors_628_; uint8_t v_isRecordingDeps_629_; lean_object* v_options_630_; lean_object* v_maxRecDepth_631_; lean_object* v_inheritedTraceOptions_632_; lean_object* v___x_633_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___x_815_; uint8_t v___x_816_; 
v_toCold_624_ = lean_ctor_get(v_a_481_, 0);
lean_inc_ref(v_toCold_624_);
v_currRecDepth_625_ = lean_ctor_get(v_a_481_, 1);
lean_inc(v_currRecDepth_625_);
v_ref_626_ = lean_ctor_get(v_a_481_, 2);
lean_inc(v_ref_626_);
v_optionFlags_627_ = lean_ctor_get_uint16(v_a_481_, sizeof(void*)*3);
v_suppressElabErrors_628_ = lean_ctor_get_uint8(v_a_481_, sizeof(void*)*3 + 2);
v_isRecordingDeps_629_ = lean_ctor_get_uint8(v_a_481_, sizeof(void*)*3 + 3);
lean_dec_ref(v_a_481_);
v_options_630_ = lean_ctor_get(v_toCold_624_, 2);
lean_inc_ref(v_options_630_);
v_maxRecDepth_631_ = lean_ctor_get(v_toCold_624_, 3);
v_inheritedTraceOptions_632_ = lean_ctor_get(v_toCold_624_, 11);
lean_inc_ref(v_inheritedTraceOptions_632_);
v___x_633_ = lean_box(0);
v___x_815_ = lean_unsigned_to_nat(0u);
v___x_816_ = lean_nat_dec_eq(v_maxRecDepth_631_, v___x_815_);
if (v___x_816_ == 0)
{
uint8_t v___x_817_; 
v___x_817_ = lean_nat_dec_eq(v_currRecDepth_625_, v_maxRecDepth_631_);
if (v___x_817_ == 0)
{
goto v___jp_774_;
}
else
{
lean_object* v___x_818_; 
lean_dec_ref(v_inheritedTraceOptions_632_);
lean_dec_ref(v_options_630_);
lean_dec(v_currRecDepth_625_);
lean_dec_ref(v_toCold_624_);
lean_dec_ref(v_c_472_);
v___x_818_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_626_);
return v___x_818_;
}
}
else
{
goto v___jp_774_;
}
v___jp_484_:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = lean_box(0);
v___x_486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
return v___x_486_;
}
v___jp_487_:
{
lean_object* v___x_495_; 
v___x_495_ = l_Int_Internal_Linear_Poly_updateOccs___redArg(v___y_488_, v___y_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
lean_dec_ref(v___y_493_);
if (lean_obj_tag(v___x_495_) == 0)
{
lean_object* v___x_496_; lean_object* v___x_497_; 
lean_dec_ref_known(v___x_495_, 1);
v___x_496_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_497_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_496_, v___y_489_, v___y_490_);
return v___x_497_;
}
else
{
lean_dec_ref(v___y_489_);
return v___x_495_;
}
}
v___jp_498_:
{
if (lean_obj_tag(v___y_520_) == 1)
{
lean_object* v_val_521_; lean_object* v_p_522_; 
lean_dec_ref(v___y_507_);
lean_dec_ref(v___y_500_);
v_val_521_ = lean_ctor_get(v___y_520_, 0);
lean_inc(v_val_521_);
lean_dec_ref_known(v___y_520_, 1);
v_p_522_ = lean_ctor_get(v_val_521_, 1);
lean_inc_ref(v_p_522_);
if (lean_obj_tag(v_p_522_) == 1)
{
lean_object* v_d_523_; lean_object* v_k_524_; lean_object* v_p_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_578_; 
v_d_523_ = lean_ctor_get(v_val_521_, 0);
v_k_524_ = lean_ctor_get(v_p_522_, 0);
v_p_525_ = lean_ctor_get(v_p_522_, 2);
v_isSharedCheck_578_ = !lean_is_exclusive(v_p_522_);
if (v_isSharedCheck_578_ == 0)
{
lean_object* v_unused_579_; 
v_unused_579_ = lean_ctor_get(v_p_522_, 1);
lean_dec(v_unused_579_);
v___x_527_ = v_p_522_;
v_isShared_528_ = v_isSharedCheck_578_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_p_525_);
lean_inc(v_k_524_);
lean_dec(v_p_522_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_578_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v_snd_532_; lean_object* v_fst_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_577_; 
v___x_529_ = lean_int_mul(v___y_512_, v_d_523_);
v___x_530_ = lean_int_mul(v_k_524_, v___y_518_);
v___x_531_ = l_Lean_Meta_Grind_Arith_gcdExt(v___x_529_, v___x_530_);
lean_dec(v___x_530_);
lean_dec(v___x_529_);
v_snd_532_ = lean_ctor_get(v___x_531_, 1);
v_fst_533_ = lean_ctor_get(v___x_531_, 0);
v_isSharedCheck_577_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_577_ == 0)
{
v___x_535_ = v___x_531_;
v_isShared_536_ = v_isSharedCheck_577_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_snd_532_);
lean_inc(v_fst_533_);
lean_dec(v___x_531_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_577_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v_fst_537_; lean_object* v_snd_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_576_; 
v_fst_537_ = lean_ctor_get(v_snd_532_, 0);
v_snd_538_ = lean_ctor_get(v_snd_532_, 1);
v_isSharedCheck_576_ = !lean_is_exclusive(v_snd_532_);
if (v_isSharedCheck_576_ == 0)
{
v___x_540_ = v_snd_532_;
v_isShared_541_ = v_isSharedCheck_576_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_snd_538_);
lean_inc(v_fst_537_);
lean_dec(v_snd_532_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_576_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_549_; 
v___x_542_ = lean_int_mul(v_fst_537_, v_d_523_);
lean_dec(v_fst_537_);
lean_inc_ref(v___y_519_);
v___x_543_ = l_Int_Internal_Linear_Poly_mul(v___y_519_, v___x_542_);
lean_dec(v___x_542_);
v___x_544_ = lean_int_mul(v_snd_538_, v___y_518_);
lean_dec(v_snd_538_);
lean_inc_ref(v_p_525_);
v___x_545_ = l_Int_Internal_Linear_Poly_mul(v_p_525_, v___x_544_);
lean_dec(v___x_544_);
v___x_546_ = lean_int_mul(v___y_518_, v_d_523_);
lean_dec(v___y_518_);
v___x_547_ = l_Int_Internal_Linear_Poly_combine(v___x_543_, v___x_545_);
lean_inc(v_fst_533_);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 2, v___x_547_);
lean_ctor_set(v___x_527_, 1, v___y_501_);
lean_ctor_set(v___x_527_, 0, v_fst_533_);
v___x_549_ = v___x_527_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_fst_533_);
lean_ctor_set(v_reuseFailAlloc_575_, 1, v___y_501_);
lean_ctor_set(v_reuseFailAlloc_575_, 2, v___x_547_);
v___x_549_ = v_reuseFailAlloc_575_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
lean_object* v___x_551_; 
lean_inc(v_val_521_);
lean_inc_ref(v___y_502_);
if (v_isShared_541_ == 0)
{
lean_ctor_set_tag(v___x_540_, 4);
lean_ctor_set(v___x_540_, 1, v_val_521_);
lean_ctor_set(v___x_540_, 0, v___y_502_);
v___x_551_ = v___x_540_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___y_502_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v_val_521_);
v___x_551_ = v_reuseFailAlloc_574_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_552_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_552_, 0, v___x_546_);
lean_ctor_set(v___x_552_, 1, v___x_549_);
lean_ctor_set(v___x_552_, 2, v___x_551_);
v___x_553_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_554_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_553_, v___y_514_, v___y_503_);
if (lean_obj_tag(v___x_554_) == 0)
{
lean_object* v___x_555_; 
lean_dec_ref_known(v___x_554_, 1);
lean_inc_ref(v___y_509_);
v___x_555_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v___x_552_, v___y_503_, v___y_499_, v___y_511_, v___y_516_, v___y_515_, v___y_506_, v___y_510_, v___y_505_, v___y_509_, v___y_508_);
if (lean_obj_tag(v___x_555_) == 0)
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_561_; 
lean_dec_ref_known(v___x_555_, 1);
v___x_556_ = l_Int_Internal_Linear_Poly_mul(v___y_519_, v_k_524_);
lean_dec(v_k_524_);
v___x_557_ = lean_int_neg(v___y_512_);
lean_dec(v___y_512_);
v___x_558_ = l_Int_Internal_Linear_Poly_mul(v_p_525_, v___x_557_);
lean_dec(v___x_557_);
v___x_559_ = l_Int_Internal_Linear_Poly_combine(v___x_556_, v___x_558_);
lean_inc(v_val_521_);
if (v_isShared_536_ == 0)
{
lean_ctor_set_tag(v___x_535_, 5);
lean_ctor_set(v___x_535_, 1, v_val_521_);
lean_ctor_set(v___x_535_, 0, v___y_502_);
v___x_561_ = v___x_535_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v___y_502_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v_val_521_);
v___x_561_ = v_reuseFailAlloc_573_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
lean_object* v___x_563_; uint8_t v_isShared_564_; uint8_t v_isSharedCheck_569_; 
v_isSharedCheck_569_ = !lean_is_exclusive(v_val_521_);
if (v_isSharedCheck_569_ == 0)
{
lean_object* v_unused_570_; lean_object* v_unused_571_; lean_object* v_unused_572_; 
v_unused_570_ = lean_ctor_get(v_val_521_, 2);
lean_dec(v_unused_570_);
v_unused_571_ = lean_ctor_get(v_val_521_, 1);
lean_dec(v_unused_571_);
v_unused_572_ = lean_ctor_get(v_val_521_, 0);
lean_dec(v_unused_572_);
v___x_563_ = v_val_521_;
v_isShared_564_ = v_isSharedCheck_569_;
goto v_resetjp_562_;
}
else
{
lean_dec(v_val_521_);
v___x_563_ = lean_box(0);
v_isShared_564_ = v_isSharedCheck_569_;
goto v_resetjp_562_;
}
v_resetjp_562_:
{
lean_object* v___x_566_; 
if (v_isShared_564_ == 0)
{
lean_ctor_set(v___x_563_, 2, v___x_561_);
lean_ctor_set(v___x_563_, 1, v___x_559_);
lean_ctor_set(v___x_563_, 0, v_fst_533_);
v___x_566_ = v___x_563_;
goto v_reusejp_565_;
}
else
{
lean_object* v_reuseFailAlloc_568_; 
v_reuseFailAlloc_568_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_568_, 0, v_fst_533_);
lean_ctor_set(v_reuseFailAlloc_568_, 1, v___x_559_);
lean_ctor_set(v_reuseFailAlloc_568_, 2, v___x_561_);
v___x_566_ = v_reuseFailAlloc_568_;
goto v_reusejp_565_;
}
v_reusejp_565_:
{
v_c_472_ = v___x_566_;
v_a_473_ = v___y_503_;
v_a_474_ = v___y_499_;
v_a_475_ = v___y_511_;
v_a_476_ = v___y_516_;
v_a_477_ = v___y_515_;
v_a_478_ = v___y_506_;
v_a_479_ = v___y_510_;
v_a_480_ = v___y_505_;
v_a_481_ = v___y_509_;
v_a_482_ = v___y_508_;
goto _start;
}
}
}
}
else
{
lean_del_object(v___x_535_);
lean_dec(v_fst_533_);
lean_dec_ref(v_p_525_);
lean_dec(v_k_524_);
lean_dec(v_val_521_);
lean_dec_ref(v___y_519_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_509_);
lean_dec_ref(v___y_502_);
return v___x_555_;
}
}
else
{
lean_dec_ref_known(v___x_552_, 3);
lean_del_object(v___x_535_);
lean_dec(v_fst_533_);
lean_dec_ref(v_p_525_);
lean_dec(v_k_524_);
lean_dec(v_val_521_);
lean_dec_ref(v___y_519_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_509_);
lean_dec_ref(v___y_502_);
return v___x_554_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_580_; 
lean_dec_ref(v_p_522_);
lean_dec_ref(v___y_519_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_514_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_501_);
v___x_580_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_val_521_, v___y_503_, v___y_499_, v___y_511_, v___y_516_, v___y_515_, v___y_506_, v___y_510_, v___y_505_, v___y_509_, v___y_508_);
lean_dec_ref(v___y_509_);
return v___x_580_;
}
}
else
{
lean_object* v_toCold_581_; lean_object* v_options_582_; uint8_t v_hasTrace_583_; 
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_514_);
lean_dec(v___y_512_);
lean_dec(v___y_501_);
v_toCold_581_ = lean_ctor_get(v___y_509_, 0);
v_options_582_ = lean_ctor_get(v_toCold_581_, 2);
v_hasTrace_583_ = lean_ctor_get_uint8(v_options_582_, sizeof(void*)*1);
if (v_hasTrace_583_ == 0)
{
lean_dec_ref(v___y_502_);
v___y_488_ = v___y_500_;
v___y_489_ = v___y_507_;
v___y_490_ = v___y_503_;
v___y_491_ = v___y_510_;
v___y_492_ = v___y_505_;
v___y_493_ = v___y_509_;
v___y_494_ = v___y_508_;
goto v___jp_487_;
}
else
{
lean_object* v_inheritedTraceOptions_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; uint8_t v___x_589_; 
v_inheritedTraceOptions_584_ = lean_ctor_get(v_toCold_581_, 11);
v___x_585_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0));
lean_inc_ref(v___y_504_);
lean_inc_ref(v___y_517_);
lean_inc_ref(v___y_513_);
v___x_586_ = l_Lean_Name_mkStr4(v___y_513_, v___y_517_, v___y_504_, v___x_585_);
v___x_587_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
lean_inc(v___x_586_);
v___x_588_ = l_Lean_Name_append(v___x_587_, v___x_586_);
v___x_589_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_584_, v_options_582_, v___x_588_);
lean_dec(v___x_588_);
if (v___x_589_ == 0)
{
lean_dec(v___x_586_);
lean_dec_ref(v___y_502_);
v___y_488_ = v___y_500_;
v___y_489_ = v___y_507_;
v___y_490_ = v___y_503_;
v___y_491_ = v___y_510_;
v___y_492_ = v___y_505_;
v___y_493_ = v___y_509_;
v___y_494_ = v___y_508_;
goto v___jp_487_;
}
else
{
lean_object* v___x_590_; 
v___x_590_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v___y_502_, v___y_503_, v___y_509_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_object* v_a_591_; lean_object* v___x_592_; 
v_a_591_ = lean_ctor_get(v___x_590_, 0);
lean_inc(v_a_591_);
lean_dec_ref_known(v___x_590_, 1);
v___x_592_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_586_, v_a_591_, v___y_510_, v___y_505_, v___y_509_, v___y_508_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_dec_ref_known(v___x_592_, 1);
v___y_488_ = v___y_500_;
v___y_489_ = v___y_507_;
v___y_490_ = v___y_503_;
v___y_491_ = v___y_510_;
v___y_492_ = v___y_505_;
v___y_493_ = v___y_509_;
v___y_494_ = v___y_508_;
goto v___jp_487_;
}
else
{
lean_dec_ref(v___y_509_);
lean_dec_ref(v___y_507_);
lean_dec_ref(v___y_500_);
return v___x_592_;
}
}
else
{
lean_object* v_a_593_; lean_object* v___x_595_; uint8_t v_isShared_596_; uint8_t v_isSharedCheck_600_; 
lean_dec(v___x_586_);
lean_dec_ref(v___y_509_);
lean_dec_ref(v___y_507_);
lean_dec_ref(v___y_500_);
v_a_593_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_600_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_600_ == 0)
{
v___x_595_ = v___x_590_;
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
else
{
lean_inc(v_a_593_);
lean_dec(v___x_590_);
v___x_595_ = lean_box(0);
v_isShared_596_ = v_isSharedCheck_600_;
goto v_resetjp_594_;
}
v_resetjp_594_:
{
lean_object* v___x_598_; 
if (v_isShared_596_ == 0)
{
v___x_598_ = v___x_595_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_a_593_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
}
}
}
}
}
v___jp_601_:
{
lean_object* v___x_613_; lean_object* v___x_614_; 
v___x_613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_613_, 0, v___y_602_);
v___x_614_ = l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(v___x_613_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_);
lean_dec_ref(v___y_611_);
if (lean_obj_tag(v___x_614_) == 0)
{
lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_622_; 
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_614_);
if (v_isSharedCheck_622_ == 0)
{
lean_object* v_unused_623_; 
v_unused_623_ = lean_ctor_get(v___x_614_, 0);
lean_dec(v_unused_623_);
v___x_616_ = v___x_614_;
v_isShared_617_ = v_isSharedCheck_622_;
goto v_resetjp_615_;
}
else
{
lean_dec(v___x_614_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_622_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_618_; lean_object* v___x_620_; 
v___x_618_ = lean_box(0);
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 0, v___x_618_);
v___x_620_ = v___x_616_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_618_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
else
{
return v___x_614_;
}
}
v___jp_634_:
{
lean_object* v___x_656_; 
v___x_656_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v___y_646_, v___y_654_);
if (lean_obj_tag(v___x_656_) == 0)
{
lean_object* v_a_657_; lean_object* v_dvds_658_; lean_object* v_size_659_; uint8_t v___x_660_; 
v_a_657_ = lean_ctor_get(v___x_656_, 0);
lean_inc(v_a_657_);
lean_dec_ref_known(v___x_656_, 1);
v_dvds_658_ = lean_ctor_get(v_a_657_, 6);
lean_inc_ref(v_dvds_658_);
lean_dec(v_a_657_);
v_size_659_ = lean_ctor_get(v_dvds_658_, 2);
v___x_660_ = lean_nat_dec_lt(v___y_635_, v_size_659_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; 
lean_dec_ref(v_dvds_658_);
v___x_661_ = l_outOfBounds___redArg(v___x_633_);
v___y_499_ = v___y_647_;
v___y_500_ = v___y_636_;
v___y_501_ = v___y_635_;
v___y_502_ = v___y_638_;
v___y_503_ = v___y_646_;
v___y_504_ = v___y_639_;
v___y_505_ = v___y_653_;
v___y_506_ = v___y_651_;
v___y_507_ = v___y_642_;
v___y_508_ = v___y_655_;
v___y_509_ = v___y_654_;
v___y_510_ = v___y_652_;
v___y_511_ = v___y_648_;
v___y_512_ = v___y_637_;
v___y_513_ = v___y_640_;
v___y_514_ = v___y_641_;
v___y_515_ = v___y_650_;
v___y_516_ = v___y_649_;
v___y_517_ = v___y_643_;
v___y_518_ = v___y_645_;
v___y_519_ = v___y_644_;
v___y_520_ = v___x_661_;
goto v___jp_498_;
}
else
{
lean_object* v___x_662_; 
v___x_662_ = l_Lean_PersistentArray_get_x21___redArg(v___x_633_, v_dvds_658_, v___y_635_);
lean_dec_ref(v_dvds_658_);
v___y_499_ = v___y_647_;
v___y_500_ = v___y_636_;
v___y_501_ = v___y_635_;
v___y_502_ = v___y_638_;
v___y_503_ = v___y_646_;
v___y_504_ = v___y_639_;
v___y_505_ = v___y_653_;
v___y_506_ = v___y_651_;
v___y_507_ = v___y_642_;
v___y_508_ = v___y_655_;
v___y_509_ = v___y_654_;
v___y_510_ = v___y_652_;
v___y_511_ = v___y_648_;
v___y_512_ = v___y_637_;
v___y_513_ = v___y_640_;
v___y_514_ = v___y_641_;
v___y_515_ = v___y_650_;
v___y_516_ = v___y_649_;
v___y_517_ = v___y_643_;
v___y_518_ = v___y_645_;
v___y_519_ = v___y_644_;
v___y_520_ = v___x_662_;
goto v___jp_498_;
}
}
else
{
lean_object* v_a_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_670_; 
lean_dec_ref(v___y_654_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec_ref(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec_ref(v___y_638_);
lean_dec(v___y_637_);
lean_dec_ref(v___y_636_);
lean_dec(v___y_635_);
v_a_663_ = lean_ctor_get(v___x_656_, 0);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_656_);
if (v_isSharedCheck_670_ == 0)
{
v___x_665_ = v___x_656_;
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_a_663_);
lean_dec(v___x_656_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_670_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_668_; 
if (v_isShared_666_ == 0)
{
v___x_668_ = v___x_665_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v_a_663_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
}
}
v___jp_671_:
{
lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_685_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(v_c_472_);
lean_inc_ref(v___y_683_);
v___x_686_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(v___x_685_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v_a_687_; lean_object* v_d_688_; lean_object* v_p_689_; uint8_t v___x_690_; 
v_a_687_ = lean_ctor_get(v___x_686_, 0);
lean_inc(v_a_687_);
lean_dec_ref_known(v___x_686_, 1);
v_d_688_ = lean_ctor_get(v_a_687_, 0);
v_p_689_ = lean_ctor_get(v_a_687_, 1);
lean_inc(v_d_688_);
v___x_690_ = l_Int_Internal_Linear_Poly_isUnsatDvd(v_d_688_, v_p_689_);
if (v___x_690_ == 0)
{
uint8_t v___x_691_; 
v___x_691_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(v_a_687_);
if (v___x_691_ == 0)
{
lean_object* v___x_692_; uint8_t v___x_693_; 
v___x_692_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1);
v___x_693_ = lean_int_dec_eq(v_d_688_, v___x_692_);
if (v___x_693_ == 0)
{
if (lean_obj_tag(v_p_689_) == 1)
{
lean_object* v_k_694_; lean_object* v_v_695_; lean_object* v_p_696_; lean_object* v___f_697_; lean_object* v___f_698_; lean_object* v___x_699_; 
lean_inc_ref(v_p_689_);
lean_inc(v_d_688_);
v_k_694_ = lean_ctor_get(v_p_689_, 0);
lean_inc(v_k_694_);
v_v_695_ = lean_ctor_get(v_p_689_, 1);
lean_inc_n(v_v_695_, 3);
v_p_696_ = lean_ctor_get(v_p_689_, 2);
lean_inc_ref(v_p_696_);
lean_inc_n(v_a_687_, 2);
v___f_697_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed), 3, 2);
lean_closure_set(v___f_697_, 0, v_a_687_);
lean_closure_set(v___f_697_, 1, v_v_695_);
v___f_698_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed), 2, 1);
lean_closure_set(v___f_698_, 0, v_v_695_);
v___x_699_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(v_a_687_, v___y_675_, v___y_683_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; uint8_t v___x_701_; uint8_t v___x_702_; uint8_t v___x_703_; 
v_a_700_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_a_700_);
lean_dec_ref_known(v___x_699_, 1);
v___x_701_ = 0;
v___x_702_ = lean_unbox(v_a_700_);
lean_dec(v_a_700_);
v___x_703_ = l_Lean_instBEqLBool_beq(v___x_702_, v___x_701_);
if (v___x_703_ == 0)
{
v___y_635_ = v_v_695_;
v___y_636_ = v_p_689_;
v___y_637_ = v_k_694_;
v___y_638_ = v_a_687_;
v___y_639_ = v___y_672_;
v___y_640_ = v___y_673_;
v___y_641_ = v___f_698_;
v___y_642_ = v___f_697_;
v___y_643_ = v___y_674_;
v___y_644_ = v_p_696_;
v___y_645_ = v_d_688_;
v___y_646_ = v___y_675_;
v___y_647_ = v___y_676_;
v___y_648_ = v___y_677_;
v___y_649_ = v___y_678_;
v___y_650_ = v___y_679_;
v___y_651_ = v___y_680_;
v___y_652_ = v___y_681_;
v___y_653_ = v___y_682_;
v___y_654_ = v___y_683_;
v___y_655_ = v___y_684_;
goto v___jp_634_;
}
else
{
lean_object* v___x_704_; 
lean_inc(v_v_695_);
v___x_704_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v_v_695_, v___y_675_);
if (lean_obj_tag(v___x_704_) == 0)
{
lean_dec_ref_known(v___x_704_, 1);
v___y_635_ = v_v_695_;
v___y_636_ = v_p_689_;
v___y_637_ = v_k_694_;
v___y_638_ = v_a_687_;
v___y_639_ = v___y_672_;
v___y_640_ = v___y_673_;
v___y_641_ = v___f_698_;
v___y_642_ = v___f_697_;
v___y_643_ = v___y_674_;
v___y_644_ = v_p_696_;
v___y_645_ = v_d_688_;
v___y_646_ = v___y_675_;
v___y_647_ = v___y_676_;
v___y_648_ = v___y_677_;
v___y_649_ = v___y_678_;
v___y_650_ = v___y_679_;
v___y_651_ = v___y_680_;
v___y_652_ = v___y_681_;
v___y_653_ = v___y_682_;
v___y_654_ = v___y_683_;
v___y_655_ = v___y_684_;
goto v___jp_634_;
}
else
{
lean_dec_ref(v___f_698_);
lean_dec_ref(v___f_697_);
lean_dec_ref(v_p_696_);
lean_dec(v_v_695_);
lean_dec(v_k_694_);
lean_dec_ref_known(v_p_689_, 3);
lean_dec(v_d_688_);
lean_dec(v_a_687_);
lean_dec_ref(v___y_683_);
return v___x_704_;
}
}
}
else
{
lean_object* v_a_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_712_; 
lean_dec_ref(v___f_698_);
lean_dec_ref(v___f_697_);
lean_dec_ref(v_p_696_);
lean_dec(v_v_695_);
lean_dec(v_k_694_);
lean_dec_ref_known(v_p_689_, 3);
lean_dec(v_d_688_);
lean_dec(v_a_687_);
lean_dec_ref(v___y_683_);
v_a_705_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_712_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_712_ == 0)
{
v___x_707_ = v___x_699_;
v_isShared_708_ = v_isSharedCheck_712_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_a_705_);
lean_dec(v___x_699_);
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
else
{
lean_object* v___x_713_; 
v___x_713_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_a_687_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
lean_dec_ref(v___y_683_);
return v___x_713_;
}
}
else
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; 
lean_inc_ref(v_p_689_);
v___x_714_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_714_, 0, v_a_687_);
v___x_715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_715_, 0, v_p_689_);
lean_ctor_set(v___x_715_, 1, v___x_714_);
lean_inc(v___y_684_);
lean_inc(v___y_682_);
lean_inc_ref(v___y_681_);
lean_inc(v___y_680_);
lean_inc_ref(v___y_679_);
lean_inc(v___y_678_);
lean_inc_ref(v___y_677_);
lean_inc(v___y_676_);
lean_inc(v___y_675_);
v___x_716_ = lean_grind_cutsat_assert_eq(v___x_715_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
if (lean_obj_tag(v___x_716_) == 0)
{
lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_724_; 
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_716_);
if (v_isSharedCheck_724_ == 0)
{
lean_object* v_unused_725_; 
v_unused_725_ = lean_ctor_get(v___x_716_, 0);
lean_dec(v_unused_725_);
v___x_718_ = v___x_716_;
v_isShared_719_ = v_isSharedCheck_724_;
goto v_resetjp_717_;
}
else
{
lean_dec(v___x_716_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_724_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_720_; lean_object* v___x_722_; 
v___x_720_ = lean_box(0);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 0, v___x_720_);
v___x_722_ = v___x_718_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_720_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
else
{
return v___x_716_;
}
}
}
else
{
lean_object* v_toCold_726_; lean_object* v_options_727_; uint8_t v_hasTrace_728_; 
v_toCold_726_ = lean_ctor_get(v___y_683_, 0);
v_options_727_ = lean_ctor_get(v_toCold_726_, 2);
v_hasTrace_728_ = lean_ctor_get_uint8(v_options_727_, sizeof(void*)*1);
if (v_hasTrace_728_ == 0)
{
lean_dec(v_a_687_);
lean_dec_ref(v___y_683_);
goto v___jp_484_;
}
else
{
lean_object* v_inheritedTraceOptions_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; uint8_t v___x_734_; 
v_inheritedTraceOptions_729_ = lean_ctor_get(v_toCold_726_, 11);
v___x_730_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1));
lean_inc_ref(v___y_672_);
lean_inc_ref(v___y_674_);
lean_inc_ref(v___y_673_);
v___x_731_ = l_Lean_Name_mkStr4(v___y_673_, v___y_674_, v___y_672_, v___x_730_);
v___x_732_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
lean_inc(v___x_731_);
v___x_733_ = l_Lean_Name_append(v___x_732_, v___x_731_);
v___x_734_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_729_, v_options_727_, v___x_733_);
lean_dec(v___x_733_);
if (v___x_734_ == 0)
{
lean_dec(v___x_731_);
lean_dec(v_a_687_);
lean_dec_ref(v___y_683_);
goto v___jp_484_;
}
else
{
lean_object* v___x_735_; 
v___x_735_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_a_687_, v___y_675_, v___y_683_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_object* v_a_736_; lean_object* v___x_737_; 
v_a_736_ = lean_ctor_get(v___x_735_, 0);
lean_inc(v_a_736_);
lean_dec_ref_known(v___x_735_, 1);
v___x_737_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_731_, v_a_736_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
lean_dec_ref(v___y_683_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_dec_ref_known(v___x_737_, 1);
goto v___jp_484_;
}
else
{
return v___x_737_;
}
}
else
{
lean_object* v_a_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_745_; 
lean_dec(v___x_731_);
lean_dec_ref(v___y_683_);
v_a_738_ = lean_ctor_get(v___x_735_, 0);
v_isSharedCheck_745_ = !lean_is_exclusive(v___x_735_);
if (v_isSharedCheck_745_ == 0)
{
v___x_740_ = v___x_735_;
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
else
{
lean_inc(v_a_738_);
lean_dec(v___x_735_);
v___x_740_ = lean_box(0);
v_isShared_741_ = v_isSharedCheck_745_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v___x_743_; 
if (v_isShared_741_ == 0)
{
v___x_743_ = v___x_740_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_744_; 
v_reuseFailAlloc_744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_744_, 0, v_a_738_);
v___x_743_ = v_reuseFailAlloc_744_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
return v___x_743_;
}
}
}
}
}
}
}
else
{
lean_object* v_toCold_746_; lean_object* v_options_747_; uint8_t v_hasTrace_748_; 
v_toCold_746_ = lean_ctor_get(v___y_683_, 0);
v_options_747_ = lean_ctor_get(v_toCold_746_, 2);
v_hasTrace_748_ = lean_ctor_get_uint8(v_options_747_, sizeof(void*)*1);
if (v_hasTrace_748_ == 0)
{
v___y_602_ = v_a_687_;
v___y_603_ = v___y_675_;
v___y_604_ = v___y_676_;
v___y_605_ = v___y_677_;
v___y_606_ = v___y_678_;
v___y_607_ = v___y_679_;
v___y_608_ = v___y_680_;
v___y_609_ = v___y_681_;
v___y_610_ = v___y_682_;
v___y_611_ = v___y_683_;
v___y_612_ = v___y_684_;
goto v___jp_601_;
}
else
{
lean_object* v_inheritedTraceOptions_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; uint8_t v___x_754_; 
v_inheritedTraceOptions_749_ = lean_ctor_get(v_toCold_746_, 11);
v___x_750_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2));
lean_inc_ref(v___y_672_);
lean_inc_ref(v___y_674_);
lean_inc_ref(v___y_673_);
v___x_751_ = l_Lean_Name_mkStr4(v___y_673_, v___y_674_, v___y_672_, v___x_750_);
v___x_752_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
lean_inc(v___x_751_);
v___x_753_ = l_Lean_Name_append(v___x_752_, v___x_751_);
v___x_754_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_749_, v_options_747_, v___x_753_);
lean_dec(v___x_753_);
if (v___x_754_ == 0)
{
lean_dec(v___x_751_);
v___y_602_ = v_a_687_;
v___y_603_ = v___y_675_;
v___y_604_ = v___y_676_;
v___y_605_ = v___y_677_;
v___y_606_ = v___y_678_;
v___y_607_ = v___y_679_;
v___y_608_ = v___y_680_;
v___y_609_ = v___y_681_;
v___y_610_ = v___y_682_;
v___y_611_ = v___y_683_;
v___y_612_ = v___y_684_;
goto v___jp_601_;
}
else
{
lean_object* v___x_755_; 
lean_inc(v_a_687_);
v___x_755_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_a_687_, v___y_675_, v___y_683_);
if (lean_obj_tag(v___x_755_) == 0)
{
lean_object* v_a_756_; lean_object* v___x_757_; 
v_a_756_ = lean_ctor_get(v___x_755_, 0);
lean_inc(v_a_756_);
lean_dec_ref_known(v___x_755_, 1);
v___x_757_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_751_, v_a_756_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
if (lean_obj_tag(v___x_757_) == 0)
{
lean_dec_ref_known(v___x_757_, 1);
v___y_602_ = v_a_687_;
v___y_603_ = v___y_675_;
v___y_604_ = v___y_676_;
v___y_605_ = v___y_677_;
v___y_606_ = v___y_678_;
v___y_607_ = v___y_679_;
v___y_608_ = v___y_680_;
v___y_609_ = v___y_681_;
v___y_610_ = v___y_682_;
v___y_611_ = v___y_683_;
v___y_612_ = v___y_684_;
goto v___jp_601_;
}
else
{
lean_dec(v_a_687_);
lean_dec_ref(v___y_683_);
return v___x_757_;
}
}
else
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
lean_dec(v___x_751_);
lean_dec(v_a_687_);
lean_dec_ref(v___y_683_);
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
lean_dec_ref(v___y_683_);
v_a_766_ = lean_ctor_get(v___x_686_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_686_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_686_);
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
v___jp_774_:
{
lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_775_ = lean_unsigned_to_nat(1u);
v___x_776_ = lean_nat_add(v_currRecDepth_625_, v___x_775_);
lean_dec(v_currRecDepth_625_);
v___x_777_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_777_, 0, v_toCold_624_);
lean_ctor_set(v___x_777_, 1, v___x_776_);
lean_ctor_set(v___x_777_, 2, v_ref_626_);
lean_ctor_set_uint16(v___x_777_, sizeof(void*)*3, v_optionFlags_627_);
lean_ctor_set_uint8(v___x_777_, sizeof(void*)*3 + 2, v_suppressElabErrors_628_);
lean_ctor_set_uint8(v___x_777_, sizeof(void*)*3 + 3, v_isRecordingDeps_629_);
v___x_778_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_473_, v___x_777_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_806_; 
v_a_779_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_806_ == 0)
{
v___x_781_ = v___x_778_;
v_isShared_782_ = v_isSharedCheck_806_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_778_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_806_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
uint8_t v___x_783_; 
v___x_783_ = lean_unbox(v_a_779_);
lean_dec(v_a_779_);
if (v___x_783_ == 0)
{
uint8_t v_hasTrace_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; 
lean_del_object(v___x_781_);
v_hasTrace_784_ = lean_ctor_get_uint8(v_options_630_, sizeof(void*)*1);
v___x_785_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0));
v___x_786_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2));
v___x_787_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3));
if (v_hasTrace_784_ == 0)
{
lean_dec_ref(v_inheritedTraceOptions_632_);
lean_dec_ref(v_options_630_);
v___y_672_ = v___x_787_;
v___y_673_ = v___x_785_;
v___y_674_ = v___x_786_;
v___y_675_ = v_a_473_;
v___y_676_ = v_a_474_;
v___y_677_ = v_a_475_;
v___y_678_ = v_a_476_;
v___y_679_ = v_a_477_;
v___y_680_ = v_a_478_;
v___y_681_ = v_a_479_;
v___y_682_ = v_a_480_;
v___y_683_ = v___x_777_;
v___y_684_ = v_a_482_;
goto v___jp_671_;
}
else
{
lean_object* v___x_788_; lean_object* v___x_789_; uint8_t v___x_790_; 
v___x_788_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4));
v___x_789_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5);
v___x_790_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_632_, v_options_630_, v___x_789_);
lean_dec_ref(v_options_630_);
lean_dec_ref(v_inheritedTraceOptions_632_);
if (v___x_790_ == 0)
{
v___y_672_ = v___x_787_;
v___y_673_ = v___x_785_;
v___y_674_ = v___x_786_;
v___y_675_ = v_a_473_;
v___y_676_ = v_a_474_;
v___y_677_ = v_a_475_;
v___y_678_ = v_a_476_;
v___y_679_ = v_a_477_;
v___y_680_ = v_a_478_;
v___y_681_ = v_a_479_;
v___y_682_ = v_a_480_;
v___y_683_ = v___x_777_;
v___y_684_ = v_a_482_;
goto v___jp_671_;
}
else
{
lean_object* v___x_791_; 
lean_inc_ref(v_c_472_);
v___x_791_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_472_, v_a_473_, v___x_777_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_a_792_; lean_object* v___x_793_; 
v_a_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_a_792_);
lean_dec_ref_known(v___x_791_, 1);
v___x_793_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_788_, v_a_792_, v_a_479_, v_a_480_, v___x_777_, v_a_482_);
if (lean_obj_tag(v___x_793_) == 0)
{
lean_dec_ref_known(v___x_793_, 1);
v___y_672_ = v___x_787_;
v___y_673_ = v___x_785_;
v___y_674_ = v___x_786_;
v___y_675_ = v_a_473_;
v___y_676_ = v_a_474_;
v___y_677_ = v_a_475_;
v___y_678_ = v_a_476_;
v___y_679_ = v_a_477_;
v___y_680_ = v_a_478_;
v___y_681_ = v_a_479_;
v___y_682_ = v_a_480_;
v___y_683_ = v___x_777_;
v___y_684_ = v_a_482_;
goto v___jp_671_;
}
else
{
lean_dec_ref_known(v___x_777_, 3);
lean_dec_ref(v_c_472_);
return v___x_793_;
}
}
else
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_801_; 
lean_dec_ref_known(v___x_777_, 3);
lean_dec_ref(v_c_472_);
v_a_794_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_801_ == 0)
{
v___x_796_ = v___x_791_;
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_791_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_a_794_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
}
}
else
{
lean_object* v___x_802_; lean_object* v___x_804_; 
lean_dec_ref_known(v___x_777_, 3);
lean_dec_ref(v_inheritedTraceOptions_632_);
lean_dec_ref(v_options_630_);
lean_dec_ref(v_c_472_);
v___x_802_ = lean_box(0);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 0, v___x_802_);
v___x_804_ = v___x_781_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_802_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
else
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_814_; 
lean_dec_ref_known(v___x_777_, 3);
lean_dec_ref(v_inheritedTraceOptions_632_);
lean_dec_ref(v_options_630_);
lean_dec_ref(v_c_472_);
v_a_807_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_814_ == 0)
{
v___x_809_ = v___x_778_;
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_778_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_812_; 
if (v_isShared_810_ == 0)
{
v___x_812_ = v___x_809_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_a_807_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___boxed(lean_object* v_c_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v_c_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_);
lean_dec(v_a_829_);
lean_dec(v_a_827_);
lean_dec_ref(v_a_826_);
lean_dec(v_a_825_);
lean_dec_ref(v_a_824_);
lean_dec(v_a_823_);
lean_dec_ref(v_a_822_);
lean_dec(v_a_821_);
lean_dec(v_a_820_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(lean_object* v_c_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_){
_start:
{
lean_object* v_d_844_; lean_object* v_p_845_; lean_object* v___x_846_; 
v_d_844_ = lean_ctor_get(v_c_832_, 0);
v_p_845_ = lean_ctor_get(v_c_832_, 1);
lean_inc_ref(v_p_845_);
v___x_846_ = l_Int_Internal_Linear_Poly_normCommRing_x3f(v_p_845_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v_a_847_; 
v_a_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_a_847_);
lean_dec_ref_known(v___x_846_, 1);
if (lean_obj_tag(v_a_847_) == 1)
{
lean_object* v_val_848_; lean_object* v_snd_849_; lean_object* v_fst_850_; lean_object* v_fst_851_; lean_object* v_snd_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
lean_inc(v_d_844_);
v_val_848_ = lean_ctor_get(v_a_847_, 0);
lean_inc(v_val_848_);
lean_dec_ref_known(v_a_847_, 1);
v_snd_849_ = lean_ctor_get(v_val_848_, 1);
lean_inc(v_snd_849_);
v_fst_850_ = lean_ctor_get(v_val_848_, 0);
lean_inc(v_fst_850_);
lean_dec(v_val_848_);
v_fst_851_ = lean_ctor_get(v_snd_849_, 0);
lean_inc(v_fst_851_);
v_snd_852_ = lean_ctor_get(v_snd_849_, 1);
lean_inc(v_snd_852_);
lean_dec(v_snd_849_);
v___x_853_ = lean_alloc_ctor(12, 3, 0);
lean_ctor_set(v___x_853_, 0, v_c_832_);
lean_ctor_set(v___x_853_, 1, v_fst_850_);
lean_ctor_set(v___x_853_, 2, v_fst_851_);
v___x_854_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_854_, 0, v_d_844_);
lean_ctor_set(v___x_854_, 1, v_snd_852_);
lean_ctor_set(v___x_854_, 2, v___x_853_);
lean_inc_ref(v_a_841_);
v___x_855_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v___x_854_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_);
return v___x_855_;
}
else
{
lean_object* v___x_856_; 
lean_dec(v_a_847_);
lean_inc_ref(v_a_841_);
v___x_856_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v_c_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_);
return v___x_856_;
}
}
else
{
lean_object* v_a_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_864_; 
lean_dec_ref(v_c_832_);
v_a_857_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_864_ == 0)
{
v___x_859_ = v___x_846_;
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_a_857_);
lean_dec(v___x_846_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_864_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v___x_862_; 
if (v_isShared_860_ == 0)
{
v___x_862_ = v___x_859_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_863_; 
v_reuseFailAlloc_863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_863_, 0, v_a_857_);
v___x_862_ = v_reuseFailAlloc_863_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
return v___x_862_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore___boxed(lean_object* v_c_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_){
_start:
{
lean_object* v_res_877_; 
v_res_877_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v_c_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_, v_a_873_, v_a_874_, v_a_875_);
lean_dec(v_a_875_);
lean_dec_ref(v_a_874_);
lean_dec(v_a_873_);
lean_dec_ref(v_a_872_);
lean_dec(v_a_871_);
lean_dec_ref(v_a_870_);
lean_dec(v_a_869_);
lean_dec_ref(v_a_868_);
lean_dec(v_a_867_);
lean_dec(v_a_866_);
return v_res_877_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8(void){
_start:
{
lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_892_ = lean_box(0);
v___x_893_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7));
v___x_894_ = l_Lean_mkConst(v___x_893_, v___x_892_);
return v___x_894_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10(void){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_896_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9));
v___x_897_ = l_Lean_stringToMessageData(v___x_896_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(lean_object* v_e_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_, lean_object* v_a_907_, lean_object* v_a_908_){
_start:
{
lean_object* v___x_916_; 
lean_inc_ref(v_e_898_);
v___x_916_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_898_, v_a_906_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v_a_917_; lean_object* v___x_918_; uint8_t v___x_919_; 
v_a_917_ = lean_ctor_get(v___x_916_, 0);
lean_inc(v_a_917_);
lean_dec_ref_known(v___x_916_, 1);
v___x_918_ = l_Lean_Expr_cleanupAnnotations(v_a_917_);
v___x_919_ = l_Lean_Expr_isApp(v___x_918_);
if (v___x_919_ == 0)
{
lean_dec_ref(v___x_918_);
lean_dec_ref(v_e_898_);
goto v___jp_910_;
}
else
{
lean_object* v_arg_920_; lean_object* v___x_921_; uint8_t v___x_922_; 
v_arg_920_ = lean_ctor_get(v___x_918_, 1);
lean_inc_ref(v_arg_920_);
v___x_921_ = l_Lean_Expr_appFnCleanup___redArg(v___x_918_);
v___x_922_ = l_Lean_Expr_isApp(v___x_921_);
if (v___x_922_ == 0)
{
lean_dec_ref(v___x_921_);
lean_dec_ref(v_arg_920_);
lean_dec_ref(v_e_898_);
goto v___jp_910_;
}
else
{
lean_object* v_arg_923_; lean_object* v___x_924_; uint8_t v___x_925_; 
v_arg_923_ = lean_ctor_get(v___x_921_, 1);
lean_inc_ref(v_arg_923_);
v___x_924_ = l_Lean_Expr_appFnCleanup___redArg(v___x_921_);
v___x_925_ = l_Lean_Expr_isApp(v___x_924_);
if (v___x_925_ == 0)
{
lean_dec_ref(v___x_924_);
lean_dec_ref(v_arg_923_);
lean_dec_ref(v_arg_920_);
lean_dec_ref(v_e_898_);
goto v___jp_910_;
}
else
{
lean_object* v_arg_926_; lean_object* v___x_927_; uint8_t v___x_928_; 
v_arg_926_ = lean_ctor_get(v___x_924_, 1);
lean_inc_ref(v_arg_926_);
v___x_927_ = l_Lean_Expr_appFnCleanup___redArg(v___x_924_);
v___x_928_ = l_Lean_Expr_isApp(v___x_927_);
if (v___x_928_ == 0)
{
lean_dec_ref(v___x_927_);
lean_dec_ref(v_arg_926_);
lean_dec_ref(v_arg_923_);
lean_dec_ref(v_arg_920_);
lean_dec_ref(v_e_898_);
goto v___jp_910_;
}
else
{
lean_object* v___x_929_; lean_object* v___x_930_; uint8_t v___x_931_; 
v___x_929_ = l_Lean_Expr_appFnCleanup___redArg(v___x_927_);
v___x_930_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_931_ = l_Lean_Expr_isConstOf(v___x_929_, v___x_930_);
lean_dec_ref(v___x_929_);
if (v___x_931_ == 0)
{
lean_dec_ref(v_arg_926_);
lean_dec_ref(v_arg_923_);
lean_dec_ref(v_arg_920_);
lean_dec_ref(v_e_898_);
goto v___jp_910_;
}
else
{
lean_object* v___x_932_; 
v___x_932_ = l_Lean_Meta_Structural_isInstDvdInt___redArg(v_arg_926_, v_a_906_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_1033_; 
v_a_933_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_935_ = v___x_932_;
v_isShared_936_ = v_isSharedCheck_1033_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v___x_932_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_1033_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
uint8_t v___x_937_; 
v___x_937_ = lean_unbox(v_a_933_);
lean_dec(v_a_933_);
if (v___x_937_ == 0)
{
lean_object* v___x_938_; lean_object* v___x_940_; 
lean_dec_ref(v_arg_923_);
lean_dec_ref(v_arg_920_);
lean_dec_ref(v_e_898_);
v___x_938_ = lean_box(0);
if (v_isShared_936_ == 0)
{
lean_ctor_set(v___x_935_, 0, v___x_938_);
v___x_940_ = v___x_935_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v___x_938_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
else
{
lean_object* v___x_942_; 
lean_del_object(v___x_935_);
lean_inc_ref(v_arg_923_);
v___x_942_ = l_Lean_Meta_getIntValue_x3f(v_arg_923_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v_a_943_; 
v_a_943_ = lean_ctor_get(v___x_942_, 0);
lean_inc(v_a_943_);
lean_dec_ref_known(v___x_942_, 1);
if (lean_obj_tag(v_a_943_) == 1)
{
lean_object* v_val_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_1009_; 
v_val_944_ = lean_ctor_get(v_a_943_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v_a_943_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_946_ = v_a_943_;
v_isShared_947_ = v_isSharedCheck_1009_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_val_944_);
lean_dec(v_a_943_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_1009_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_948_; 
lean_inc_ref(v_e_898_);
v___x_948_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_898_, v_a_899_, v_a_903_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
if (lean_obj_tag(v___x_948_) == 0)
{
lean_object* v_a_949_; uint8_t v___x_950_; 
v_a_949_ = lean_ctor_get(v___x_948_, 0);
lean_inc(v_a_949_);
lean_dec_ref_known(v___x_948_, 1);
v___x_950_ = lean_unbox(v_a_949_);
lean_dec(v_a_949_);
if (v___x_950_ == 0)
{
lean_object* v___x_951_; 
lean_del_object(v___x_946_);
lean_dec(v_val_944_);
lean_inc_ref(v_e_898_);
v___x_951_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_898_, v_a_899_, v_a_903_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v_a_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_977_; 
v_a_952_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_977_ == 0)
{
v___x_954_ = v___x_951_;
v_isShared_955_ = v_isSharedCheck_977_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_a_952_);
lean_dec(v___x_951_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_977_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
uint8_t v___x_956_; 
v___x_956_ = lean_unbox(v_a_952_);
lean_dec(v_a_952_);
if (v___x_956_ == 0)
{
lean_object* v___x_957_; lean_object* v___x_959_; 
lean_dec_ref(v_arg_923_);
lean_dec_ref(v_arg_920_);
lean_dec_ref(v_e_898_);
v___x_957_ = lean_box(0);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 0, v___x_957_);
v___x_959_ = v___x_954_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v___x_957_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
else
{
lean_object* v___x_961_; 
lean_del_object(v___x_954_);
lean_inc_ref(v_e_898_);
v___x_961_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v_a_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
v_a_962_ = lean_ctor_get(v___x_961_, 0);
lean_inc(v_a_962_);
lean_dec_ref_known(v___x_961_, 1);
v___x_963_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8);
v___x_964_ = l_Lean_eagerReflBoolTrue;
v___x_965_ = l_Lean_Meta_mkOfEqFalseCore(v_e_898_, v_a_962_);
v___x_966_ = l_Lean_mkApp4(v___x_963_, v_arg_923_, v_arg_920_, v___x_964_, v___x_965_);
v___x_967_ = lean_unsigned_to_nat(0u);
v___x_968_ = l_Lean_Meta_Grind_pushNewFact(v___x_966_, v___x_967_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
return v___x_968_;
}
else
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_976_; 
lean_dec_ref(v_arg_923_);
lean_dec_ref(v_arg_920_);
lean_dec_ref(v_e_898_);
v_a_969_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_976_ == 0)
{
v___x_971_ = v___x_961_;
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_961_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_974_; 
if (v_isShared_972_ == 0)
{
v___x_974_ = v___x_971_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_a_969_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
}
}
}
else
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_985_; 
lean_dec_ref(v_arg_923_);
lean_dec_ref(v_arg_920_);
lean_dec_ref(v_e_898_);
v_a_978_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_985_ == 0)
{
v___x_980_ = v___x_951_;
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_951_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_983_; 
if (v_isShared_981_ == 0)
{
v___x_983_ = v___x_980_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_a_978_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
}
else
{
lean_object* v___x_986_; 
lean_dec_ref(v_arg_923_);
v___x_986_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(v_arg_920_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
if (lean_obj_tag(v___x_986_) == 0)
{
lean_object* v_a_987_; lean_object* v___x_989_; 
v_a_987_ = lean_ctor_get(v___x_986_, 0);
lean_inc(v_a_987_);
lean_dec_ref_known(v___x_986_, 1);
if (v_isShared_947_ == 0)
{
lean_ctor_set_tag(v___x_946_, 0);
lean_ctor_set(v___x_946_, 0, v_e_898_);
v___x_989_ = v___x_946_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_992_; 
v_reuseFailAlloc_992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_992_, 0, v_e_898_);
v___x_989_ = v_reuseFailAlloc_992_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
lean_object* v___x_990_; lean_object* v___x_991_; 
v___x_990_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_990_, 0, v_val_944_);
lean_ctor_set(v___x_990_, 1, v_a_987_);
lean_ctor_set(v___x_990_, 2, v___x_989_);
v___x_991_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v___x_990_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
return v___x_991_;
}
}
else
{
lean_object* v_a_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1000_; 
lean_del_object(v___x_946_);
lean_dec(v_val_944_);
lean_dec_ref(v_e_898_);
v_a_993_ = lean_ctor_get(v___x_986_, 0);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_986_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_995_ = v___x_986_;
v_isShared_996_ = v_isSharedCheck_1000_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_a_993_);
lean_dec(v___x_986_);
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
}
else
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1008_; 
lean_del_object(v___x_946_);
lean_dec(v_val_944_);
lean_dec_ref(v_arg_923_);
lean_dec_ref(v_arg_920_);
lean_dec_ref(v_e_898_);
v_a_1001_ = lean_ctor_get(v___x_948_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_948_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_1003_ = v___x_948_;
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_948_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1008_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v___x_1006_; 
if (v_isShared_1004_ == 0)
{
v___x_1006_ = v___x_1003_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_a_1001_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
}
else
{
lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
lean_dec(v_a_943_);
lean_dec_ref(v_arg_923_);
lean_dec_ref(v_arg_920_);
v___x_1010_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10);
v___x_1011_ = l_Lean_indentExpr(v_e_898_);
v___x_1012_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1010_);
lean_ctor_set(v___x_1012_, 1, v___x_1011_);
v___x_1013_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_903_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v_a_1014_; uint8_t v_verbose_1015_; 
v_a_1014_ = lean_ctor_get(v___x_1013_, 0);
lean_inc(v_a_1014_);
lean_dec_ref_known(v___x_1013_, 1);
v_verbose_1015_ = lean_ctor_get_uint8(v_a_1014_, 0);
lean_dec(v_a_1014_);
if (v_verbose_1015_ == 0)
{
lean_dec_ref_known(v___x_1012_, 2);
goto v___jp_913_;
}
else
{
lean_object* v___x_1016_; 
v___x_1016_ = l_Lean_Meta_Sym_reportIssue(v___x_1012_, v_a_903_, v_a_904_, v_a_905_, v_a_906_, v_a_907_, v_a_908_);
if (lean_obj_tag(v___x_1016_) == 0)
{
lean_dec_ref_known(v___x_1016_, 1);
goto v___jp_913_;
}
else
{
return v___x_1016_;
}
}
}
else
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
lean_dec_ref_known(v___x_1012_, 2);
v_a_1017_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1019_ = v___x_1013_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_1013_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_a_1017_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
}
else
{
lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1032_; 
lean_dec_ref(v_arg_923_);
lean_dec_ref(v_arg_920_);
lean_dec_ref(v_e_898_);
v_a_1025_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_1032_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_1032_ == 0)
{
v___x_1027_ = v___x_942_;
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_942_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1032_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
lean_object* v___x_1030_; 
if (v_isShared_1028_ == 0)
{
v___x_1030_ = v___x_1027_;
goto v_reusejp_1029_;
}
else
{
lean_object* v_reuseFailAlloc_1031_; 
v_reuseFailAlloc_1031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1031_, 0, v_a_1025_);
v___x_1030_ = v_reuseFailAlloc_1031_;
goto v_reusejp_1029_;
}
v_reusejp_1029_:
{
return v___x_1030_;
}
}
}
}
}
}
else
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1041_; 
lean_dec_ref(v_arg_923_);
lean_dec_ref(v_arg_920_);
lean_dec_ref(v_e_898_);
v_a_1034_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1036_ = v___x_932_;
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_932_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1039_; 
if (v_isShared_1037_ == 0)
{
v___x_1039_ = v___x_1036_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_a_1034_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
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
lean_object* v_a_1042_; lean_object* v___x_1044_; uint8_t v_isShared_1045_; uint8_t v_isSharedCheck_1049_; 
lean_dec_ref(v_e_898_);
v_a_1042_ = lean_ctor_get(v___x_916_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1044_ = v___x_916_;
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
else
{
lean_inc(v_a_1042_);
lean_dec(v___x_916_);
v___x_1044_ = lean_box(0);
v_isShared_1045_ = v_isSharedCheck_1049_;
goto v_resetjp_1043_;
}
v_resetjp_1043_:
{
lean_object* v___x_1047_; 
if (v_isShared_1045_ == 0)
{
v___x_1047_ = v___x_1044_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v_a_1042_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
v___jp_910_:
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = lean_box(0);
v___x_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
return v___x_912_;
}
v___jp_913_:
{
lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_914_ = lean_box(0);
v___x_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
return v___x_915_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___boxed(lean_object* v_e_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(v_e_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_);
lean_dec(v_a_1060_);
lean_dec_ref(v_a_1059_);
lean_dec(v_a_1058_);
lean_dec_ref(v_a_1057_);
lean_dec(v_a_1056_);
lean_dec_ref(v_a_1055_);
lean_dec(v_a_1054_);
lean_dec_ref(v_a_1053_);
lean_dec(v_a_1052_);
lean_dec(v_a_1051_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd_spec__0(lean_object* v_a_1063_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = lean_nat_to_int(v_a_1063_);
return v___x_1064_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3(void){
_start:
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1070_ = lean_box(0);
v___x_1071_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2));
v___x_1072_ = l_Lean_mkConst(v___x_1071_, v___x_1070_);
return v___x_1072_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7(void){
_start:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1079_ = lean_box(0);
v___x_1080_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6));
v___x_1081_ = l_Lean_mkConst(v___x_1080_, v___x_1079_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(lean_object* v_e_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_){
_start:
{
lean_object* v___x_1100_; uint8_t v___x_1101_; 
lean_inc_ref(v_e_1082_);
v___x_1100_ = l_Lean_Expr_cleanupAnnotations(v_e_1082_);
v___x_1101_ = l_Lean_Expr_isApp(v___x_1100_);
if (v___x_1101_ == 0)
{
lean_dec_ref(v___x_1100_);
lean_dec_ref(v_e_1082_);
goto v___jp_1094_;
}
else
{
lean_object* v_arg_1102_; lean_object* v___x_1103_; uint8_t v___x_1104_; 
v_arg_1102_ = lean_ctor_get(v___x_1100_, 1);
lean_inc_ref(v_arg_1102_);
v___x_1103_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1100_);
v___x_1104_ = l_Lean_Expr_isApp(v___x_1103_);
if (v___x_1104_ == 0)
{
lean_dec_ref(v___x_1103_);
lean_dec_ref(v_arg_1102_);
lean_dec_ref(v_e_1082_);
goto v___jp_1094_;
}
else
{
lean_object* v_arg_1105_; lean_object* v___x_1106_; uint8_t v___x_1107_; 
v_arg_1105_ = lean_ctor_get(v___x_1103_, 1);
lean_inc_ref(v_arg_1105_);
v___x_1106_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1103_);
v___x_1107_ = l_Lean_Expr_isApp(v___x_1106_);
if (v___x_1107_ == 0)
{
lean_dec_ref(v___x_1106_);
lean_dec_ref(v_arg_1105_);
lean_dec_ref(v_arg_1102_);
lean_dec_ref(v_e_1082_);
goto v___jp_1094_;
}
else
{
lean_object* v_arg_1108_; lean_object* v___x_1109_; uint8_t v___x_1110_; 
v_arg_1108_ = lean_ctor_get(v___x_1106_, 1);
lean_inc_ref(v_arg_1108_);
v___x_1109_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1106_);
v___x_1110_ = l_Lean_Expr_isApp(v___x_1109_);
if (v___x_1110_ == 0)
{
lean_dec_ref(v___x_1109_);
lean_dec_ref(v_arg_1108_);
lean_dec_ref(v_arg_1105_);
lean_dec_ref(v_arg_1102_);
lean_dec_ref(v_e_1082_);
goto v___jp_1094_;
}
else
{
lean_object* v___x_1111_; lean_object* v___x_1112_; uint8_t v___x_1113_; 
v___x_1111_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1109_);
v___x_1112_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1113_ = l_Lean_Expr_isConstOf(v___x_1111_, v___x_1112_);
lean_dec_ref(v___x_1111_);
if (v___x_1113_ == 0)
{
lean_dec_ref(v_arg_1108_);
lean_dec_ref(v_arg_1105_);
lean_dec_ref(v_arg_1102_);
lean_dec_ref(v_e_1082_);
goto v___jp_1094_;
}
else
{
lean_object* v___x_1114_; 
v___x_1114_ = l_Lean_Meta_Structural_isInstDvdNat___redArg(v_arg_1108_, v_a_1090_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1246_; 
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1117_ = v___x_1114_;
v_isShared_1118_ = v_isSharedCheck_1246_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1114_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1246_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
uint8_t v___x_1119_; 
v___x_1119_ = lean_unbox(v_a_1115_);
lean_dec(v_a_1115_);
if (v___x_1119_ == 0)
{
lean_object* v___x_1120_; lean_object* v___x_1122_; 
lean_dec_ref(v_arg_1105_);
lean_dec_ref(v_arg_1102_);
lean_dec_ref(v_e_1082_);
v___x_1120_ = lean_box(0);
if (v_isShared_1118_ == 0)
{
lean_ctor_set(v___x_1117_, 0, v___x_1120_);
v___x_1122_ = v___x_1117_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1120_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
else
{
lean_object* v___x_1124_; 
lean_del_object(v___x_1117_);
v___x_1124_ = l_Lean_Meta_getNatValue_x3f(v_arg_1105_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v_a_1125_; 
v_a_1125_ = lean_ctor_get(v___x_1124_, 0);
lean_inc(v_a_1125_);
lean_dec_ref_known(v___x_1124_, 1);
if (lean_obj_tag(v_a_1125_) == 1)
{
lean_object* v_val_1126_; lean_object* v___x_1127_; 
v_val_1126_ = lean_ctor_get(v_a_1125_, 0);
lean_inc(v_val_1126_);
lean_dec_ref_known(v_a_1125_, 1);
lean_inc_ref(v_e_1082_);
v___x_1127_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_1082_, v_a_1083_, v_a_1087_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; uint8_t v___x_1129_; 
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_a_1128_);
lean_dec_ref_known(v___x_1127_, 1);
v___x_1129_ = lean_unbox(v_a_1128_);
lean_dec(v_a_1128_);
if (v___x_1129_ == 0)
{
lean_object* v___x_1130_; 
lean_dec(v_val_1126_);
lean_inc_ref(v_e_1082_);
v___x_1130_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_1082_, v_a_1083_, v_a_1087_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1155_; 
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1133_ = v___x_1130_;
v_isShared_1134_ = v_isSharedCheck_1155_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1130_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1155_;
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
lean_dec_ref(v_arg_1105_);
lean_dec_ref(v_arg_1102_);
lean_dec_ref(v_e_1082_);
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
lean_inc_ref(v_e_1082_);
v___x_1140_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v_a_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; 
v_a_1141_ = lean_ctor_get(v___x_1140_, 0);
lean_inc(v_a_1141_);
lean_dec_ref_known(v___x_1140_, 1);
v___x_1142_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3);
v___x_1143_ = l_Lean_Meta_mkOfEqFalseCore(v_e_1082_, v_a_1141_);
v___x_1144_ = l_Lean_mkApp3(v___x_1142_, v_arg_1105_, v_arg_1102_, v___x_1143_);
v___x_1145_ = lean_unsigned_to_nat(0u);
v___x_1146_ = l_Lean_Meta_Grind_pushNewFact(v___x_1144_, v___x_1145_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_);
return v___x_1146_;
}
else
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1154_; 
lean_dec_ref(v_arg_1105_);
lean_dec_ref(v_arg_1102_);
lean_dec_ref(v_e_1082_);
v_a_1147_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1149_ = v___x_1140_;
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1140_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1152_; 
if (v_isShared_1150_ == 0)
{
v___x_1152_ = v___x_1149_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_a_1147_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
}
}
else
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1163_; 
lean_dec_ref(v_arg_1105_);
lean_dec_ref(v_arg_1102_);
lean_dec_ref(v_e_1082_);
v_a_1156_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1158_ = v___x_1130_;
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1130_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1159_ == 0)
{
v___x_1161_ = v___x_1158_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1156_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
else
{
lean_object* v___x_1164_; 
lean_inc_ref(v_arg_1105_);
v___x_1164_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_1105_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_);
if (lean_obj_tag(v___x_1164_) == 0)
{
lean_object* v_a_1165_; lean_object* v_fst_1166_; lean_object* v_snd_1167_; lean_object* v___x_1168_; 
v_a_1165_ = lean_ctor_get(v___x_1164_, 0);
lean_inc(v_a_1165_);
lean_dec_ref_known(v___x_1164_, 1);
v_fst_1166_ = lean_ctor_get(v_a_1165_, 0);
lean_inc(v_fst_1166_);
v_snd_1167_ = lean_ctor_get(v_a_1165_, 1);
lean_inc(v_snd_1167_);
lean_dec(v_a_1165_);
lean_inc_ref(v_arg_1102_);
v___x_1168_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_1102_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_);
if (lean_obj_tag(v___x_1168_) == 0)
{
lean_object* v_a_1169_; lean_object* v_fst_1170_; lean_object* v_snd_1171_; lean_object* v___x_1172_; 
v_a_1169_ = lean_ctor_get(v___x_1168_, 0);
lean_inc(v_a_1169_);
lean_dec_ref_known(v___x_1168_, 1);
v_fst_1170_ = lean_ctor_get(v_a_1169_, 0);
lean_inc(v_fst_1170_);
v_snd_1171_ = lean_ctor_get(v_a_1169_, 1);
lean_inc(v_snd_1171_);
lean_dec(v_a_1169_);
v___x_1172_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1082_, v_a_1083_);
if (lean_obj_tag(v___x_1172_) == 0)
{
lean_object* v_a_1173_; lean_object* v___x_1174_; 
v_a_1173_ = lean_ctor_get(v___x_1172_, 0);
lean_inc(v_a_1173_);
lean_dec_ref_known(v___x_1172_, 1);
lean_inc(v_fst_1170_);
v___x_1174_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_1170_, v_a_1173_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v_a_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_a_1175_);
lean_dec_ref_known(v___x_1174_, 1);
v___x_1176_ = l_Int_Internal_Linear_Expr_norm(v_a_1175_);
v___x_1177_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7);
v___x_1178_ = l_Lean_mkApp6(v___x_1177_, v_arg_1105_, v_arg_1102_, v_fst_1166_, v_fst_1170_, v_snd_1167_, v_snd_1171_);
lean_inc(v_val_1126_);
v___x_1179_ = lean_nat_to_int(v_val_1126_);
v___x_1180_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1180_, 0, v_e_1082_);
lean_ctor_set(v___x_1180_, 1, v___x_1178_);
lean_ctor_set(v___x_1180_, 2, v_val_1126_);
lean_ctor_set(v___x_1180_, 3, v_a_1175_);
v___x_1181_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1181_, 0, v___x_1179_);
lean_ctor_set(v___x_1181_, 1, v___x_1176_);
lean_ctor_set(v___x_1181_, 2, v___x_1180_);
v___x_1182_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v___x_1181_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_);
return v___x_1182_;
}
else
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1190_; 
lean_dec(v_snd_1171_);
lean_dec(v_fst_1170_);
lean_dec(v_snd_1167_);
lean_dec(v_fst_1166_);
lean_dec(v_val_1126_);
lean_dec_ref(v_arg_1105_);
lean_dec_ref(v_arg_1102_);
lean_dec_ref(v_e_1082_);
v_a_1183_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1185_ = v___x_1174_;
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1174_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1186_ == 0)
{
v___x_1188_ = v___x_1185_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_a_1183_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
}
else
{
lean_object* v_a_1191_; lean_object* v___x_1193_; uint8_t v_isShared_1194_; uint8_t v_isSharedCheck_1198_; 
lean_dec(v_snd_1171_);
lean_dec(v_fst_1170_);
lean_dec(v_snd_1167_);
lean_dec(v_fst_1166_);
lean_dec(v_val_1126_);
lean_dec_ref(v_arg_1105_);
lean_dec_ref(v_arg_1102_);
lean_dec_ref(v_e_1082_);
v_a_1191_ = lean_ctor_get(v___x_1172_, 0);
v_isSharedCheck_1198_ = !lean_is_exclusive(v___x_1172_);
if (v_isSharedCheck_1198_ == 0)
{
v___x_1193_ = v___x_1172_;
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
else
{
lean_inc(v_a_1191_);
lean_dec(v___x_1172_);
v___x_1193_ = lean_box(0);
v_isShared_1194_ = v_isSharedCheck_1198_;
goto v_resetjp_1192_;
}
v_resetjp_1192_:
{
lean_object* v___x_1196_; 
if (v_isShared_1194_ == 0)
{
v___x_1196_ = v___x_1193_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_a_1191_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
}
else
{
lean_object* v_a_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1206_; 
lean_dec(v_snd_1167_);
lean_dec(v_fst_1166_);
lean_dec(v_val_1126_);
lean_dec_ref(v_arg_1105_);
lean_dec_ref(v_arg_1102_);
lean_dec_ref(v_e_1082_);
v_a_1199_ = lean_ctor_get(v___x_1168_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1201_ = v___x_1168_;
v_isShared_1202_ = v_isSharedCheck_1206_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_a_1199_);
lean_dec(v___x_1168_);
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
lean_dec(v_val_1126_);
lean_dec_ref(v_arg_1105_);
lean_dec_ref(v_arg_1102_);
lean_dec_ref(v_e_1082_);
v_a_1207_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1209_ = v___x_1164_;
v_isShared_1210_ = v_isSharedCheck_1214_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_dec(v___x_1164_);
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
}
else
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1222_; 
lean_dec(v_val_1126_);
lean_dec_ref(v_arg_1105_);
lean_dec_ref(v_arg_1102_);
lean_dec_ref(v_e_1082_);
v_a_1215_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1217_ = v___x_1127_;
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1127_);
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
lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
lean_dec(v_a_1125_);
lean_dec_ref(v_arg_1105_);
lean_dec_ref(v_arg_1102_);
v___x_1223_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10);
v___x_1224_ = l_Lean_indentExpr(v_e_1082_);
v___x_1225_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1223_);
lean_ctor_set(v___x_1225_, 1, v___x_1224_);
v___x_1226_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1087_);
if (lean_obj_tag(v___x_1226_) == 0)
{
lean_object* v_a_1227_; uint8_t v_verbose_1228_; 
v_a_1227_ = lean_ctor_get(v___x_1226_, 0);
lean_inc(v_a_1227_);
lean_dec_ref_known(v___x_1226_, 1);
v_verbose_1228_ = lean_ctor_get_uint8(v_a_1227_, 0);
lean_dec(v_a_1227_);
if (v_verbose_1228_ == 0)
{
lean_dec_ref_known(v___x_1225_, 2);
goto v___jp_1097_;
}
else
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Lean_Meta_Sym_reportIssue(v___x_1225_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_);
if (lean_obj_tag(v___x_1229_) == 0)
{
lean_dec_ref_known(v___x_1229_, 1);
goto v___jp_1097_;
}
else
{
return v___x_1229_;
}
}
}
else
{
lean_object* v_a_1230_; lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1237_; 
lean_dec_ref_known(v___x_1225_, 2);
v_a_1230_ = lean_ctor_get(v___x_1226_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1232_ = v___x_1226_;
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
else
{
lean_inc(v_a_1230_);
lean_dec(v___x_1226_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1235_; 
if (v_isShared_1233_ == 0)
{
v___x_1235_ = v___x_1232_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_a_1230_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
}
}
}
else
{
lean_object* v_a_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1245_; 
lean_dec_ref(v_arg_1105_);
lean_dec_ref(v_arg_1102_);
lean_dec_ref(v_e_1082_);
v_a_1238_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1245_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1240_ = v___x_1124_;
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_a_1238_);
lean_dec(v___x_1124_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1245_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___x_1243_; 
if (v_isShared_1241_ == 0)
{
v___x_1243_ = v___x_1240_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_a_1238_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
}
}
}
else
{
lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1254_; 
lean_dec_ref(v_arg_1105_);
lean_dec_ref(v_arg_1102_);
lean_dec_ref(v_e_1082_);
v_a_1247_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1249_ = v___x_1114_;
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_dec(v___x_1114_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1252_; 
if (v_isShared_1250_ == 0)
{
v___x_1252_ = v___x_1249_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_a_1247_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
}
}
}
}
}
}
v___jp_1094_:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1095_ = lean_box(0);
v___x_1096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1095_);
return v___x_1096_;
}
v___jp_1097_:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1098_ = lean_box(0);
v___x_1099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1098_);
return v___x_1099_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___boxed(lean_object* v_e_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(v_e_1255_, v_a_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_);
lean_dec(v_a_1265_);
lean_dec_ref(v_a_1264_);
lean_dec(v_a_1263_);
lean_dec_ref(v_a_1262_);
lean_dec(v_a_1261_);
lean_dec_ref(v_a_1260_);
lean_dec(v_a_1259_);
lean_dec_ref(v_a_1258_);
lean_dec(v_a_1257_);
lean_dec(v_a_1256_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(lean_object* v_e_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_){
_start:
{
lean_object* v___x_1285_; 
v___x_1285_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1273_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1321_; 
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1288_ = v___x_1285_;
v_isShared_1289_ = v_isSharedCheck_1321_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1285_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1321_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
uint8_t v_lia_1290_; 
v_lia_1290_ = lean_ctor_get_uint8(v_a_1286_, sizeof(void*)*14 + 23);
lean_dec(v_a_1286_);
if (v_lia_1290_ == 0)
{
lean_object* v___x_1291_; lean_object* v___x_1293_; 
lean_dec_ref(v_e_1270_);
v___x_1291_ = lean_box(0);
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 0, v___x_1291_);
v___x_1293_ = v___x_1288_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v___x_1291_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
else
{
lean_object* v___x_1295_; 
lean_del_object(v___x_1288_);
lean_inc_ref(v_e_1270_);
v___x_1295_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1270_, v_a_1278_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_object* v_a_1296_; lean_object* v___x_1297_; uint8_t v___x_1298_; 
v_a_1296_ = lean_ctor_get(v___x_1295_, 0);
lean_inc(v_a_1296_);
lean_dec_ref_known(v___x_1295_, 1);
v___x_1297_ = l_Lean_Expr_cleanupAnnotations(v_a_1296_);
v___x_1298_ = l_Lean_Expr_isApp(v___x_1297_);
if (v___x_1298_ == 0)
{
lean_dec_ref(v___x_1297_);
lean_dec_ref(v_e_1270_);
goto v___jp_1282_;
}
else
{
lean_object* v___x_1299_; uint8_t v___x_1300_; 
v___x_1299_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1297_);
v___x_1300_ = l_Lean_Expr_isApp(v___x_1299_);
if (v___x_1300_ == 0)
{
lean_dec_ref(v___x_1299_);
lean_dec_ref(v_e_1270_);
goto v___jp_1282_;
}
else
{
lean_object* v___x_1301_; uint8_t v___x_1302_; 
v___x_1301_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1299_);
v___x_1302_ = l_Lean_Expr_isApp(v___x_1301_);
if (v___x_1302_ == 0)
{
lean_dec_ref(v___x_1301_);
lean_dec_ref(v_e_1270_);
goto v___jp_1282_;
}
else
{
lean_object* v___x_1303_; uint8_t v___x_1304_; 
v___x_1303_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1301_);
v___x_1304_ = l_Lean_Expr_isApp(v___x_1303_);
if (v___x_1304_ == 0)
{
lean_dec_ref(v___x_1303_);
lean_dec_ref(v_e_1270_);
goto v___jp_1282_;
}
else
{
lean_object* v_arg_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; uint8_t v___x_1308_; 
v_arg_1305_ = lean_ctor_get(v___x_1303_, 1);
lean_inc_ref(v_arg_1305_);
v___x_1306_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1303_);
v___x_1307_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1308_ = l_Lean_Expr_isConstOf(v___x_1306_, v___x_1307_);
lean_dec_ref(v___x_1306_);
if (v___x_1308_ == 0)
{
lean_dec_ref(v_arg_1305_);
lean_dec_ref(v_e_1270_);
goto v___jp_1282_;
}
else
{
lean_object* v___x_1309_; uint8_t v___x_1310_; 
v___x_1309_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0));
v___x_1310_ = l_Lean_Expr_isConstOf(v_arg_1305_, v___x_1309_);
lean_dec_ref(v_arg_1305_);
if (v___x_1310_ == 0)
{
lean_object* v___x_1311_; 
v___x_1311_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(v_e_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_);
return v___x_1311_;
}
else
{
lean_object* v___x_1312_; 
v___x_1312_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(v_e_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_);
return v___x_1312_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1320_; 
lean_dec_ref(v_e_1270_);
v_a_1313_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1315_ = v___x_1295_;
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v___x_1295_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1318_; 
if (v_isShared_1316_ == 0)
{
v___x_1318_ = v___x_1315_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_a_1313_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
}
}
}
else
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1329_; 
lean_dec_ref(v_e_1270_);
v_a_1322_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1324_ = v___x_1285_;
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v___x_1285_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1327_; 
if (v_isShared_1325_ == 0)
{
v___x_1327_ = v___x_1324_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_a_1322_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
v___jp_1282_:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1283_ = lean_box(0);
v___x_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1283_);
return v___x_1284_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed(lean_object* v_e_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_, lean_object* v_a_1334_, lean_object* v_a_1335_, lean_object* v_a_1336_, lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(v_e_1330_, v_a_1331_, v_a_1332_, v_a_1333_, v_a_1334_, v_a_1335_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_);
lean_dec(v_a_1340_);
lean_dec_ref(v_a_1339_);
lean_dec(v_a_1338_);
lean_dec_ref(v_a_1337_);
lean_dec(v_a_1336_);
lean_dec_ref(v_a_1335_);
lean_dec(v_a_1334_);
lean_dec_ref(v_a_1333_);
lean_dec(v_a_1332_);
lean_dec(v_a_1331_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1344_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1345_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed), 12, 0);
v___x_1346_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_1344_, v___x_1345_);
return v___x_1346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_9____boxed(lean_object* v_a_1347_){
_start:
{
lean_object* v_res_1348_; 
v_res_1348_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_9_();
return v_res_1348_;
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
