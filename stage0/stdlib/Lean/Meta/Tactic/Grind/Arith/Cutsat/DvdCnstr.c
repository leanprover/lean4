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
lean_object* v_ref_70_; lean_object* v___x_71_; lean_object* v_a_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_116_; 
v_ref_70_ = lean_ctor_get(v___y_67_, 2);
v___x_71_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0_spec__0(v_msg_64_, v___y_65_, v___y_66_, v___y_67_, v___y_68_);
v_a_72_ = lean_ctor_get(v___x_71_, 0);
v_isSharedCheck_116_ = !lean_is_exclusive(v___x_71_);
if (v_isSharedCheck_116_ == 0)
{
v___x_74_ = v___x_71_;
v_isShared_75_ = v_isSharedCheck_116_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_a_72_);
lean_dec(v___x_71_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_116_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
lean_object* v___x_76_; lean_object* v_traceState_77_; lean_object* v_env_78_; lean_object* v_nextMacroScope_79_; lean_object* v_ngen_80_; lean_object* v_auxDeclNGen_81_; lean_object* v_cache_82_; lean_object* v_messages_83_; lean_object* v_infoState_84_; lean_object* v_snapshotTasks_85_; lean_object* v___x_87_; uint8_t v_isShared_88_; uint8_t v_isSharedCheck_115_; 
v___x_76_ = lean_st_ref_take(v___y_68_);
v_traceState_77_ = lean_ctor_get(v___x_76_, 4);
v_env_78_ = lean_ctor_get(v___x_76_, 0);
v_nextMacroScope_79_ = lean_ctor_get(v___x_76_, 1);
v_ngen_80_ = lean_ctor_get(v___x_76_, 2);
v_auxDeclNGen_81_ = lean_ctor_get(v___x_76_, 3);
v_cache_82_ = lean_ctor_get(v___x_76_, 5);
v_messages_83_ = lean_ctor_get(v___x_76_, 6);
v_infoState_84_ = lean_ctor_get(v___x_76_, 7);
v_snapshotTasks_85_ = lean_ctor_get(v___x_76_, 8);
v_isSharedCheck_115_ = !lean_is_exclusive(v___x_76_);
if (v_isSharedCheck_115_ == 0)
{
v___x_87_ = v___x_76_;
v_isShared_88_ = v_isSharedCheck_115_;
goto v_resetjp_86_;
}
else
{
lean_inc(v_snapshotTasks_85_);
lean_inc(v_infoState_84_);
lean_inc(v_messages_83_);
lean_inc(v_cache_82_);
lean_inc(v_traceState_77_);
lean_inc(v_auxDeclNGen_81_);
lean_inc(v_ngen_80_);
lean_inc(v_nextMacroScope_79_);
lean_inc(v_env_78_);
lean_dec(v___x_76_);
v___x_87_ = lean_box(0);
v_isShared_88_ = v_isSharedCheck_115_;
goto v_resetjp_86_;
}
v_resetjp_86_:
{
uint64_t v_tid_89_; lean_object* v_traces_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_114_; 
v_tid_89_ = lean_ctor_get_uint64(v_traceState_77_, sizeof(void*)*1);
v_traces_90_ = lean_ctor_get(v_traceState_77_, 0);
v_isSharedCheck_114_ = !lean_is_exclusive(v_traceState_77_);
if (v_isSharedCheck_114_ == 0)
{
v___x_92_ = v_traceState_77_;
v_isShared_93_ = v_isSharedCheck_114_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_traces_90_);
lean_dec(v_traceState_77_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_114_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
lean_object* v___x_94_; double v___x_95_; uint8_t v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_104_; 
v___x_94_ = lean_box(0);
v___x_95_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0);
v___x_96_ = 0;
v___x_97_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__1));
v___x_98_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_98_, 0, v_cls_63_);
lean_ctor_set(v___x_98_, 1, v___x_94_);
lean_ctor_set(v___x_98_, 2, v___x_97_);
lean_ctor_set_float(v___x_98_, sizeof(void*)*3, v___x_95_);
lean_ctor_set_float(v___x_98_, sizeof(void*)*3 + 8, v___x_95_);
lean_ctor_set_uint8(v___x_98_, sizeof(void*)*3 + 16, v___x_96_);
v___x_99_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__2));
v___x_100_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_100_, 0, v___x_98_);
lean_ctor_set(v___x_100_, 1, v_a_72_);
lean_ctor_set(v___x_100_, 2, v___x_99_);
lean_inc(v_ref_70_);
v___x_101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_101_, 0, v_ref_70_);
lean_ctor_set(v___x_101_, 1, v___x_100_);
v___x_102_ = l_Lean_PersistentArray_push___redArg(v_traces_90_, v___x_101_);
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 0, v___x_102_);
v___x_104_ = v___x_92_;
goto v_reusejp_103_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v___x_102_);
lean_ctor_set_uint64(v_reuseFailAlloc_113_, sizeof(void*)*1, v_tid_89_);
v___x_104_ = v_reuseFailAlloc_113_;
goto v_reusejp_103_;
}
v_reusejp_103_:
{
lean_object* v___x_106_; 
if (v_isShared_88_ == 0)
{
lean_ctor_set(v___x_87_, 4, v___x_104_);
v___x_106_ = v___x_87_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v_env_78_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v_nextMacroScope_79_);
lean_ctor_set(v_reuseFailAlloc_112_, 2, v_ngen_80_);
lean_ctor_set(v_reuseFailAlloc_112_, 3, v_auxDeclNGen_81_);
lean_ctor_set(v_reuseFailAlloc_112_, 4, v___x_104_);
lean_ctor_set(v_reuseFailAlloc_112_, 5, v_cache_82_);
lean_ctor_set(v_reuseFailAlloc_112_, 6, v_messages_83_);
lean_ctor_set(v_reuseFailAlloc_112_, 7, v_infoState_84_);
lean_ctor_set(v_reuseFailAlloc_112_, 8, v_snapshotTasks_85_);
v___x_106_ = v_reuseFailAlloc_112_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_110_; 
v___x_107_ = lean_st_ref_put(v___y_68_, v___x_106_);
v___x_108_ = lean_box(0);
if (v_isShared_75_ == 0)
{
lean_ctor_set(v___x_74_, 0, v___x_108_);
v___x_110_ = v___x_74_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v___x_108_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
return v___x_110_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___boxed(lean_object* v_cls_117_, lean_object* v_msg_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v_cls_117_, v_msg_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_);
lean_dec(v___y_122_);
lean_dec_ref(v___y_121_);
lean_dec(v___y_120_);
lean_dec_ref(v___y_119_);
return v_res_124_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7(void){
_start:
{
lean_object* v_cls_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v_cls_137_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4));
v___x_138_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
v___x_139_ = l_Lean_Name_append(v___x_138_, v_cls_137_);
return v___x_139_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9(void){
_start:
{
lean_object* v___x_141_; lean_object* v___x_142_; 
v___x_141_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__8));
v___x_142_ = l_Lean_stringToMessageData(v___x_141_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(lean_object* v_a_143_, lean_object* v_x_144_, lean_object* v_c_u2081_145_, lean_object* v_b_146_, lean_object* v_c_u2082_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_){
_start:
{
lean_object* v_toCold_159_; lean_object* v_options_160_; lean_object* v_p_161_; lean_object* v_d_162_; lean_object* v_p_163_; lean_object* v_inheritedTraceOptions_164_; uint8_t v_hasTrace_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v_d_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v_p_172_; 
v_toCold_159_ = lean_ctor_get(v_a_156_, 0);
v_options_160_ = lean_ctor_get(v_toCold_159_, 2);
v_p_161_ = lean_ctor_get(v_c_u2081_145_, 0);
v_d_162_ = lean_ctor_get(v_c_u2082_147_, 0);
v_p_163_ = lean_ctor_get(v_c_u2082_147_, 1);
v_inheritedTraceOptions_164_ = lean_ctor_get(v_toCold_159_, 11);
v_hasTrace_165_ = lean_ctor_get_uint8(v_options_160_, sizeof(void*)*1);
v___x_166_ = lean_int_mul(v_a_143_, v_d_162_);
v___x_167_ = lean_nat_abs(v___x_166_);
lean_dec(v___x_166_);
v_d_168_ = lean_nat_to_int(v___x_167_);
lean_inc_ref(v_p_163_);
v___x_169_ = l_Int_Internal_Linear_Poly_mul(v_p_163_, v_a_143_);
v___x_170_ = lean_int_neg(v_b_146_);
lean_inc_ref(v_p_161_);
v___x_171_ = l_Int_Internal_Linear_Poly_mul(v_p_161_, v___x_170_);
lean_dec(v___x_170_);
v_p_172_ = l_Int_Internal_Linear_Poly_combine(v___x_169_, v___x_171_);
if (v_hasTrace_165_ == 0)
{
goto v___jp_173_;
}
else
{
lean_object* v_cls_177_; lean_object* v___x_178_; uint8_t v___x_179_; 
v_cls_177_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4));
v___x_178_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7);
v___x_179_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_164_, v_options_160_, v___x_178_);
if (v___x_179_ == 0)
{
goto v___jp_173_;
}
else
{
lean_object* v___x_180_; 
v___x_180_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_x_144_, v_a_148_, v_a_156_);
if (lean_obj_tag(v___x_180_) == 0)
{
lean_object* v_a_181_; lean_object* v___x_182_; 
v_a_181_ = lean_ctor_get(v___x_180_, 0);
lean_inc(v_a_181_);
lean_dec_ref_known(v___x_180_, 1);
lean_inc_ref(v_c_u2081_145_);
v___x_182_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_u2081_145_, v_a_148_, v_a_156_);
if (lean_obj_tag(v___x_182_) == 0)
{
lean_object* v_a_183_; lean_object* v___x_184_; 
v_a_183_ = lean_ctor_get(v___x_182_, 0);
lean_inc(v_a_183_);
lean_dec_ref_known(v___x_182_, 1);
lean_inc_ref(v_c_u2082_147_);
v___x_184_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_u2082_147_, v_a_148_, v_a_156_);
if (lean_obj_tag(v___x_184_) == 0)
{
lean_object* v_a_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v_a_185_ = lean_ctor_get(v___x_184_, 0);
lean_inc(v_a_185_);
lean_dec_ref_known(v___x_184_, 1);
v___x_186_ = l_Lean_MessageData_ofExpr(v_a_181_);
v___x_187_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9);
v___x_188_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_188_, 0, v___x_186_);
lean_ctor_set(v___x_188_, 1, v___x_187_);
v___x_189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_189_, 0, v___x_188_);
lean_ctor_set(v___x_189_, 1, v_a_183_);
v___x_190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_190_, 0, v___x_189_);
lean_ctor_set(v___x_190_, 1, v___x_187_);
v___x_191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_191_, 0, v___x_190_);
lean_ctor_set(v___x_191_, 1, v_a_185_);
v___x_192_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v_cls_177_, v___x_191_, v_a_154_, v_a_155_, v_a_156_, v_a_157_);
if (lean_obj_tag(v___x_192_) == 0)
{
lean_dec_ref_known(v___x_192_, 1);
goto v___jp_173_;
}
else
{
lean_object* v_a_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_200_; 
lean_dec_ref(v_p_172_);
lean_dec(v_d_168_);
lean_dec_ref(v_c_u2082_147_);
lean_dec_ref(v_c_u2081_145_);
lean_dec(v_x_144_);
v_a_193_ = lean_ctor_get(v___x_192_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_192_);
if (v_isSharedCheck_200_ == 0)
{
v___x_195_ = v___x_192_;
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_a_193_);
lean_dec(v___x_192_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_198_; 
if (v_isShared_196_ == 0)
{
v___x_198_ = v___x_195_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_a_193_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
}
else
{
lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_208_; 
lean_dec(v_a_183_);
lean_dec(v_a_181_);
lean_dec_ref(v_p_172_);
lean_dec(v_d_168_);
lean_dec_ref(v_c_u2082_147_);
lean_dec_ref(v_c_u2081_145_);
lean_dec(v_x_144_);
v_a_201_ = lean_ctor_get(v___x_184_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_184_);
if (v_isSharedCheck_208_ == 0)
{
v___x_203_ = v___x_184_;
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_184_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_206_; 
if (v_isShared_204_ == 0)
{
v___x_206_ = v___x_203_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_a_201_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
}
else
{
lean_object* v_a_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_216_; 
lean_dec(v_a_181_);
lean_dec_ref(v_p_172_);
lean_dec(v_d_168_);
lean_dec_ref(v_c_u2082_147_);
lean_dec_ref(v_c_u2081_145_);
lean_dec(v_x_144_);
v_a_209_ = lean_ctor_get(v___x_182_, 0);
v_isSharedCheck_216_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_216_ == 0)
{
v___x_211_ = v___x_182_;
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_a_209_);
lean_dec(v___x_182_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_214_; 
if (v_isShared_212_ == 0)
{
v___x_214_ = v___x_211_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_a_209_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
}
}
else
{
lean_object* v_a_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_224_; 
lean_dec_ref(v_p_172_);
lean_dec(v_d_168_);
lean_dec_ref(v_c_u2082_147_);
lean_dec_ref(v_c_u2081_145_);
lean_dec(v_x_144_);
v_a_217_ = lean_ctor_get(v___x_180_, 0);
v_isSharedCheck_224_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_224_ == 0)
{
v___x_219_ = v___x_180_;
v_isShared_220_ = v_isSharedCheck_224_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_a_217_);
lean_dec(v___x_180_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_224_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_222_; 
if (v_isShared_220_ == 0)
{
v___x_222_ = v___x_219_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v_a_217_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
}
}
}
v___jp_173_:
{
lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_174_ = lean_alloc_ctor(8, 3, 0);
lean_ctor_set(v___x_174_, 0, v_x_144_);
lean_ctor_set(v___x_174_, 1, v_c_u2081_145_);
lean_ctor_set(v___x_174_, 2, v_c_u2082_147_);
v___x_175_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_175_, 0, v_d_168_);
lean_ctor_set(v___x_175_, 1, v_p_172_);
lean_ctor_set(v___x_175_, 2, v___x_174_);
v___x_176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
return v___x_176_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___boxed(lean_object* v_a_225_, lean_object* v_x_226_, lean_object* v_c_u2081_227_, lean_object* v_b_228_, lean_object* v_c_u2082_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_){
_start:
{
lean_object* v_res_241_; 
v_res_241_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(v_a_225_, v_x_226_, v_c_u2081_227_, v_b_228_, v_c_u2082_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_);
lean_dec(v_a_239_);
lean_dec_ref(v_a_238_);
lean_dec(v_a_237_);
lean_dec_ref(v_a_236_);
lean_dec(v_a_235_);
lean_dec_ref(v_a_234_);
lean_dec(v_a_233_);
lean_dec_ref(v_a_232_);
lean_dec(v_a_231_);
lean_dec(v_a_230_);
lean_dec(v_b_228_);
lean_dec(v_a_225_);
return v_res_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0(lean_object* v_cls_242_, lean_object* v_msg_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_){
_start:
{
lean_object* v___x_255_; 
v___x_255_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v_cls_242_, v_msg_243_, v___y_250_, v___y_251_, v___y_252_, v___y_253_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___boxed(lean_object* v_cls_256_, lean_object* v_msg_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0(v_cls_256_, v_msg_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
lean_dec(v___y_261_);
lean_dec_ref(v___y_260_);
lean_dec(v___y_259_);
lean_dec(v___y_258_);
return v_res_269_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; 
v___x_275_ = l_Lean_maxRecDepthErrorMessage;
v___x_276_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_276_, 0, v___x_275_);
return v___x_276_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3);
v___x_278_ = l_Lean_MessageData_ofFormat(v___x_277_);
return v___x_278_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_279_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4);
v___x_280_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2));
v___x_281_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
lean_ctor_set(v___x_281_, 1, v___x_279_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(lean_object* v_ref_282_){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_284_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5);
v___x_285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_285_, 0, v_ref_282_);
lean_ctor_set(v___x_285_, 1, v___x_284_);
v___x_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___boxed(lean_object* v_ref_287_, lean_object* v___y_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_287_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0(lean_object* v_00_u03b1_290_, lean_object* v_ref_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
lean_object* v___x_303_; 
v___x_303_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_291_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___boxed(lean_object* v_00_u03b1_304_, lean_object* v_ref_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0(v_00_u03b1_304_, v_ref_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(lean_object* v_c_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_){
_start:
{
lean_object* v_p_330_; lean_object* v_toCold_331_; lean_object* v_currRecDepth_332_; lean_object* v_ref_333_; uint8_t v_diag_334_; uint8_t v_suppressElabErrors_335_; lean_object* v_maxRecDepth_367_; lean_object* v___x_368_; uint8_t v___x_369_; 
v_p_330_ = lean_ctor_get(v_c_318_, 1);
v_toCold_331_ = lean_ctor_get(v_a_327_, 0);
lean_inc_ref(v_toCold_331_);
v_currRecDepth_332_ = lean_ctor_get(v_a_327_, 1);
lean_inc(v_currRecDepth_332_);
v_ref_333_ = lean_ctor_get(v_a_327_, 2);
lean_inc(v_ref_333_);
v_diag_334_ = lean_ctor_get_uint8(v_a_327_, sizeof(void*)*3);
v_suppressElabErrors_335_ = lean_ctor_get_uint8(v_a_327_, sizeof(void*)*3 + 1);
lean_dec_ref(v_a_327_);
v_maxRecDepth_367_ = lean_ctor_get(v_toCold_331_, 3);
v___x_368_ = lean_unsigned_to_nat(0u);
v___x_369_ = lean_nat_dec_eq(v_maxRecDepth_367_, v___x_368_);
if (v___x_369_ == 0)
{
uint8_t v___x_370_; 
v___x_370_ = lean_nat_dec_eq(v_currRecDepth_332_, v_maxRecDepth_367_);
if (v___x_370_ == 0)
{
goto v___jp_336_;
}
else
{
lean_object* v___x_371_; 
lean_dec(v_currRecDepth_332_);
lean_dec_ref(v_toCold_331_);
lean_dec_ref(v_c_318_);
v___x_371_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_333_);
return v___x_371_;
}
}
else
{
goto v___jp_336_;
}
v___jp_336_:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_337_ = lean_unsigned_to_nat(1u);
v___x_338_ = lean_nat_add(v_currRecDepth_332_, v___x_337_);
lean_dec(v_currRecDepth_332_);
v___x_339_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_339_, 0, v_toCold_331_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
lean_ctor_set(v___x_339_, 2, v_ref_333_);
lean_ctor_set_uint8(v___x_339_, sizeof(void*)*3, v_diag_334_);
lean_ctor_set_uint8(v___x_339_, sizeof(void*)*3 + 1, v_suppressElabErrors_335_);
lean_inc_ref(v_p_330_);
v___x_340_ = l_Int_Internal_Linear_Poly_findVarToSubst___redArg(v_p_330_, v_a_319_, v___x_339_);
if (lean_obj_tag(v___x_340_) == 0)
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_358_; 
v_a_341_ = lean_ctor_get(v___x_340_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_358_ == 0)
{
v___x_343_ = v___x_340_;
v_isShared_344_ = v_isSharedCheck_358_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v___x_340_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_358_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
if (lean_obj_tag(v_a_341_) == 1)
{
lean_object* v_val_345_; lean_object* v_snd_346_; lean_object* v_snd_347_; lean_object* v_fst_348_; lean_object* v_fst_349_; lean_object* v_p_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
lean_del_object(v___x_343_);
v_val_345_ = lean_ctor_get(v_a_341_, 0);
lean_inc(v_val_345_);
lean_dec_ref_known(v_a_341_, 1);
v_snd_346_ = lean_ctor_get(v_val_345_, 1);
lean_inc(v_snd_346_);
v_snd_347_ = lean_ctor_get(v_snd_346_, 1);
lean_inc(v_snd_347_);
v_fst_348_ = lean_ctor_get(v_val_345_, 0);
lean_inc(v_fst_348_);
lean_dec(v_val_345_);
v_fst_349_ = lean_ctor_get(v_snd_346_, 0);
lean_inc(v_fst_349_);
lean_dec(v_snd_346_);
v_p_350_ = lean_ctor_get(v_snd_347_, 0);
v___x_351_ = l_Int_Internal_Linear_Poly_coeff(v_p_350_, v_fst_349_);
v___x_352_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(v___x_351_, v_fst_349_, v_snd_347_, v_fst_348_, v_c_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_, v___x_339_, v_a_328_);
lean_dec(v_fst_348_);
lean_dec(v___x_351_);
if (lean_obj_tag(v___x_352_) == 0)
{
lean_object* v_a_353_; 
v_a_353_ = lean_ctor_get(v___x_352_, 0);
lean_inc(v_a_353_);
lean_dec_ref_known(v___x_352_, 1);
v_c_318_ = v_a_353_;
v_a_327_ = v___x_339_;
goto _start;
}
else
{
lean_dec_ref_known(v___x_339_, 3);
return v___x_352_;
}
}
else
{
lean_object* v___x_356_; 
lean_dec(v_a_341_);
lean_dec_ref_known(v___x_339_, 3);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 0, v_c_318_);
v___x_356_ = v___x_343_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_c_318_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
else
{
lean_object* v_a_359_; lean_object* v___x_361_; uint8_t v_isShared_362_; uint8_t v_isSharedCheck_366_; 
lean_dec_ref_known(v___x_339_, 3);
lean_dec_ref(v_c_318_);
v_a_359_ = lean_ctor_get(v___x_340_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_366_ == 0)
{
v___x_361_ = v___x_340_;
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
else
{
lean_inc(v_a_359_);
lean_dec(v___x_340_);
v___x_361_ = lean_box(0);
v_isShared_362_ = v_isSharedCheck_366_;
goto v_resetjp_360_;
}
v_resetjp_360_:
{
lean_object* v___x_364_; 
if (v_isShared_362_ == 0)
{
v___x_364_ = v___x_361_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v_a_359_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___boxed(lean_object* v_c_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(v_c_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
lean_dec(v_a_382_);
lean_dec(v_a_380_);
lean_dec_ref(v_a_379_);
lean_dec(v_a_378_);
lean_dec_ref(v_a_377_);
lean_dec(v_a_376_);
lean_dec_ref(v_a_375_);
lean_dec(v_a_374_);
lean_dec(v_a_373_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(lean_object* v_a_385_, lean_object* v_v_386_, lean_object* v_s_387_){
_start:
{
lean_object* v_vars_388_; lean_object* v_varMap_389_; lean_object* v_vars_x27_390_; lean_object* v_varMap_x27_391_; lean_object* v_natToIntMap_392_; lean_object* v_natDef_393_; lean_object* v_dvds_394_; lean_object* v_lowers_395_; lean_object* v_uppers_396_; lean_object* v_diseqs_397_; lean_object* v_elimEqs_398_; lean_object* v_elimStack_399_; lean_object* v_occurs_400_; lean_object* v_assignment_401_; lean_object* v_nextCnstrId_402_; uint8_t v_caseSplits_403_; lean_object* v_steps_404_; lean_object* v_conflict_x3f_405_; lean_object* v_diseqSplits_406_; lean_object* v_divMod_407_; uint8_t v_usedCommRing_408_; lean_object* v_nonlinearOccs_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_418_; 
v_vars_388_ = lean_ctor_get(v_s_387_, 0);
v_varMap_389_ = lean_ctor_get(v_s_387_, 1);
v_vars_x27_390_ = lean_ctor_get(v_s_387_, 2);
v_varMap_x27_391_ = lean_ctor_get(v_s_387_, 3);
v_natToIntMap_392_ = lean_ctor_get(v_s_387_, 4);
v_natDef_393_ = lean_ctor_get(v_s_387_, 5);
v_dvds_394_ = lean_ctor_get(v_s_387_, 6);
v_lowers_395_ = lean_ctor_get(v_s_387_, 7);
v_uppers_396_ = lean_ctor_get(v_s_387_, 8);
v_diseqs_397_ = lean_ctor_get(v_s_387_, 9);
v_elimEqs_398_ = lean_ctor_get(v_s_387_, 10);
v_elimStack_399_ = lean_ctor_get(v_s_387_, 11);
v_occurs_400_ = lean_ctor_get(v_s_387_, 12);
v_assignment_401_ = lean_ctor_get(v_s_387_, 13);
v_nextCnstrId_402_ = lean_ctor_get(v_s_387_, 14);
v_caseSplits_403_ = lean_ctor_get_uint8(v_s_387_, sizeof(void*)*20);
v_steps_404_ = lean_ctor_get(v_s_387_, 15);
v_conflict_x3f_405_ = lean_ctor_get(v_s_387_, 16);
v_diseqSplits_406_ = lean_ctor_get(v_s_387_, 17);
v_divMod_407_ = lean_ctor_get(v_s_387_, 18);
v_usedCommRing_408_ = lean_ctor_get_uint8(v_s_387_, sizeof(void*)*20 + 1);
v_nonlinearOccs_409_ = lean_ctor_get(v_s_387_, 19);
v_isSharedCheck_418_ = !lean_is_exclusive(v_s_387_);
if (v_isSharedCheck_418_ == 0)
{
v___x_411_ = v_s_387_;
v_isShared_412_ = v_isSharedCheck_418_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_nonlinearOccs_409_);
lean_inc(v_divMod_407_);
lean_inc(v_diseqSplits_406_);
lean_inc(v_conflict_x3f_405_);
lean_inc(v_steps_404_);
lean_inc(v_nextCnstrId_402_);
lean_inc(v_assignment_401_);
lean_inc(v_occurs_400_);
lean_inc(v_elimStack_399_);
lean_inc(v_elimEqs_398_);
lean_inc(v_diseqs_397_);
lean_inc(v_uppers_396_);
lean_inc(v_lowers_395_);
lean_inc(v_dvds_394_);
lean_inc(v_natDef_393_);
lean_inc(v_natToIntMap_392_);
lean_inc(v_varMap_x27_391_);
lean_inc(v_vars_x27_390_);
lean_inc(v_varMap_389_);
lean_inc(v_vars_388_);
lean_dec(v_s_387_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_418_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_416_; 
v___x_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_413_, 0, v_a_385_);
v___x_414_ = l_Lean_PersistentArray_set___redArg(v_dvds_394_, v_v_386_, v___x_413_);
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 6, v___x_414_);
v___x_416_ = v___x_411_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 20, 2);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_vars_388_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v_varMap_389_);
lean_ctor_set(v_reuseFailAlloc_417_, 2, v_vars_x27_390_);
lean_ctor_set(v_reuseFailAlloc_417_, 3, v_varMap_x27_391_);
lean_ctor_set(v_reuseFailAlloc_417_, 4, v_natToIntMap_392_);
lean_ctor_set(v_reuseFailAlloc_417_, 5, v_natDef_393_);
lean_ctor_set(v_reuseFailAlloc_417_, 6, v___x_414_);
lean_ctor_set(v_reuseFailAlloc_417_, 7, v_lowers_395_);
lean_ctor_set(v_reuseFailAlloc_417_, 8, v_uppers_396_);
lean_ctor_set(v_reuseFailAlloc_417_, 9, v_diseqs_397_);
lean_ctor_set(v_reuseFailAlloc_417_, 10, v_elimEqs_398_);
lean_ctor_set(v_reuseFailAlloc_417_, 11, v_elimStack_399_);
lean_ctor_set(v_reuseFailAlloc_417_, 12, v_occurs_400_);
lean_ctor_set(v_reuseFailAlloc_417_, 13, v_assignment_401_);
lean_ctor_set(v_reuseFailAlloc_417_, 14, v_nextCnstrId_402_);
lean_ctor_set(v_reuseFailAlloc_417_, 15, v_steps_404_);
lean_ctor_set(v_reuseFailAlloc_417_, 16, v_conflict_x3f_405_);
lean_ctor_set(v_reuseFailAlloc_417_, 17, v_diseqSplits_406_);
lean_ctor_set(v_reuseFailAlloc_417_, 18, v_divMod_407_);
lean_ctor_set(v_reuseFailAlloc_417_, 19, v_nonlinearOccs_409_);
lean_ctor_set_uint8(v_reuseFailAlloc_417_, sizeof(void*)*20, v_caseSplits_403_);
lean_ctor_set_uint8(v_reuseFailAlloc_417_, sizeof(void*)*20 + 1, v_usedCommRing_408_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed(lean_object* v_a_419_, lean_object* v_v_420_, lean_object* v_s_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(v_a_419_, v_v_420_, v_s_421_);
lean_dec(v_v_420_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(lean_object* v_v_423_, lean_object* v_s_424_){
_start:
{
lean_object* v_vars_425_; lean_object* v_varMap_426_; lean_object* v_vars_x27_427_; lean_object* v_varMap_x27_428_; lean_object* v_natToIntMap_429_; lean_object* v_natDef_430_; lean_object* v_dvds_431_; lean_object* v_lowers_432_; lean_object* v_uppers_433_; lean_object* v_diseqs_434_; lean_object* v_elimEqs_435_; lean_object* v_elimStack_436_; lean_object* v_occurs_437_; lean_object* v_assignment_438_; lean_object* v_nextCnstrId_439_; uint8_t v_caseSplits_440_; lean_object* v_steps_441_; lean_object* v_conflict_x3f_442_; lean_object* v_diseqSplits_443_; lean_object* v_divMod_444_; uint8_t v_usedCommRing_445_; lean_object* v_nonlinearOccs_446_; lean_object* v___x_448_; uint8_t v_isShared_449_; uint8_t v_isSharedCheck_455_; 
v_vars_425_ = lean_ctor_get(v_s_424_, 0);
v_varMap_426_ = lean_ctor_get(v_s_424_, 1);
v_vars_x27_427_ = lean_ctor_get(v_s_424_, 2);
v_varMap_x27_428_ = lean_ctor_get(v_s_424_, 3);
v_natToIntMap_429_ = lean_ctor_get(v_s_424_, 4);
v_natDef_430_ = lean_ctor_get(v_s_424_, 5);
v_dvds_431_ = lean_ctor_get(v_s_424_, 6);
v_lowers_432_ = lean_ctor_get(v_s_424_, 7);
v_uppers_433_ = lean_ctor_get(v_s_424_, 8);
v_diseqs_434_ = lean_ctor_get(v_s_424_, 9);
v_elimEqs_435_ = lean_ctor_get(v_s_424_, 10);
v_elimStack_436_ = lean_ctor_get(v_s_424_, 11);
v_occurs_437_ = lean_ctor_get(v_s_424_, 12);
v_assignment_438_ = lean_ctor_get(v_s_424_, 13);
v_nextCnstrId_439_ = lean_ctor_get(v_s_424_, 14);
v_caseSplits_440_ = lean_ctor_get_uint8(v_s_424_, sizeof(void*)*20);
v_steps_441_ = lean_ctor_get(v_s_424_, 15);
v_conflict_x3f_442_ = lean_ctor_get(v_s_424_, 16);
v_diseqSplits_443_ = lean_ctor_get(v_s_424_, 17);
v_divMod_444_ = lean_ctor_get(v_s_424_, 18);
v_usedCommRing_445_ = lean_ctor_get_uint8(v_s_424_, sizeof(void*)*20 + 1);
v_nonlinearOccs_446_ = lean_ctor_get(v_s_424_, 19);
v_isSharedCheck_455_ = !lean_is_exclusive(v_s_424_);
if (v_isSharedCheck_455_ == 0)
{
v___x_448_ = v_s_424_;
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
lean_inc(v_varMap_x27_428_);
lean_inc(v_vars_x27_427_);
lean_inc(v_varMap_426_);
lean_inc(v_vars_425_);
lean_dec(v_s_424_);
v___x_448_ = lean_box(0);
v_isShared_449_ = v_isSharedCheck_455_;
goto v_resetjp_447_;
}
v_resetjp_447_:
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_453_; 
v___x_450_ = lean_box(0);
v___x_451_ = l_Lean_PersistentArray_set___redArg(v_dvds_431_, v_v_423_, v___x_450_);
if (v_isShared_449_ == 0)
{
lean_ctor_set(v___x_448_, 6, v___x_451_);
v___x_453_ = v___x_448_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 20, 2);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_vars_425_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v_varMap_426_);
lean_ctor_set(v_reuseFailAlloc_454_, 2, v_vars_x27_427_);
lean_ctor_set(v_reuseFailAlloc_454_, 3, v_varMap_x27_428_);
lean_ctor_set(v_reuseFailAlloc_454_, 4, v_natToIntMap_429_);
lean_ctor_set(v_reuseFailAlloc_454_, 5, v_natDef_430_);
lean_ctor_set(v_reuseFailAlloc_454_, 6, v___x_451_);
lean_ctor_set(v_reuseFailAlloc_454_, 7, v_lowers_432_);
lean_ctor_set(v_reuseFailAlloc_454_, 8, v_uppers_433_);
lean_ctor_set(v_reuseFailAlloc_454_, 9, v_diseqs_434_);
lean_ctor_set(v_reuseFailAlloc_454_, 10, v_elimEqs_435_);
lean_ctor_set(v_reuseFailAlloc_454_, 11, v_elimStack_436_);
lean_ctor_set(v_reuseFailAlloc_454_, 12, v_occurs_437_);
lean_ctor_set(v_reuseFailAlloc_454_, 13, v_assignment_438_);
lean_ctor_set(v_reuseFailAlloc_454_, 14, v_nextCnstrId_439_);
lean_ctor_set(v_reuseFailAlloc_454_, 15, v_steps_441_);
lean_ctor_set(v_reuseFailAlloc_454_, 16, v_conflict_x3f_442_);
lean_ctor_set(v_reuseFailAlloc_454_, 17, v_diseqSplits_443_);
lean_ctor_set(v_reuseFailAlloc_454_, 18, v_divMod_444_);
lean_ctor_set(v_reuseFailAlloc_454_, 19, v_nonlinearOccs_446_);
lean_ctor_set_uint8(v_reuseFailAlloc_454_, sizeof(void*)*20, v_caseSplits_440_);
lean_ctor_set_uint8(v_reuseFailAlloc_454_, sizeof(void*)*20 + 1, v_usedCommRing_445_);
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
lean_object* v___y_486_; lean_object* v___y_487_; lean_object* v___y_488_; lean_object* v___y_489_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v___y_497_; lean_object* v___y_498_; lean_object* v___y_499_; lean_object* v___y_500_; lean_object* v___y_501_; lean_object* v___y_502_; lean_object* v___y_503_; lean_object* v___y_504_; lean_object* v___y_505_; lean_object* v___y_506_; lean_object* v___y_507_; lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_600_; lean_object* v___y_601_; lean_object* v___y_602_; lean_object* v___y_603_; lean_object* v___y_604_; lean_object* v___y_605_; lean_object* v___y_606_; lean_object* v___y_607_; lean_object* v___y_608_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v_toCold_622_; lean_object* v_currRecDepth_623_; lean_object* v_ref_624_; uint8_t v_diag_625_; uint8_t v_suppressElabErrors_626_; lean_object* v_options_627_; lean_object* v_maxRecDepth_628_; lean_object* v_inheritedTraceOptions_629_; lean_object* v___x_630_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_669_; lean_object* v___y_670_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_674_; lean_object* v___y_675_; lean_object* v___y_676_; lean_object* v___y_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___x_812_; uint8_t v___x_813_; 
v_toCold_622_ = lean_ctor_get(v_a_479_, 0);
lean_inc_ref(v_toCold_622_);
v_currRecDepth_623_ = lean_ctor_get(v_a_479_, 1);
lean_inc(v_currRecDepth_623_);
v_ref_624_ = lean_ctor_get(v_a_479_, 2);
lean_inc(v_ref_624_);
v_diag_625_ = lean_ctor_get_uint8(v_a_479_, sizeof(void*)*3);
v_suppressElabErrors_626_ = lean_ctor_get_uint8(v_a_479_, sizeof(void*)*3 + 1);
lean_dec_ref(v_a_479_);
v_options_627_ = lean_ctor_get(v_toCold_622_, 2);
lean_inc_ref(v_options_627_);
v_maxRecDepth_628_ = lean_ctor_get(v_toCold_622_, 3);
v_inheritedTraceOptions_629_ = lean_ctor_get(v_toCold_622_, 11);
lean_inc_ref(v_inheritedTraceOptions_629_);
v___x_630_ = lean_box(0);
v___x_812_ = lean_unsigned_to_nat(0u);
v___x_813_ = lean_nat_dec_eq(v_maxRecDepth_628_, v___x_812_);
if (v___x_813_ == 0)
{
uint8_t v___x_814_; 
v___x_814_ = lean_nat_dec_eq(v_currRecDepth_623_, v_maxRecDepth_628_);
if (v___x_814_ == 0)
{
goto v___jp_771_;
}
else
{
lean_object* v___x_815_; 
lean_dec_ref(v_inheritedTraceOptions_629_);
lean_dec_ref(v_options_627_);
lean_dec(v_currRecDepth_623_);
lean_dec_ref(v_toCold_622_);
lean_dec_ref(v_c_470_);
v___x_815_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_624_);
return v___x_815_;
}
}
else
{
goto v___jp_771_;
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
v___x_493_ = l_Int_Internal_Linear_Poly_updateOccs___redArg(v___y_486_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_);
lean_dec_ref(v___y_491_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v___x_494_; lean_object* v___x_495_; 
lean_dec_ref_known(v___x_493_, 1);
v___x_494_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_495_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_494_, v___y_487_, v___y_488_);
return v___x_495_;
}
else
{
lean_dec_ref(v___y_487_);
return v___x_493_;
}
}
v___jp_496_:
{
if (lean_obj_tag(v___y_518_) == 1)
{
lean_object* v_val_519_; lean_object* v_p_520_; 
lean_dec_ref(v___y_510_);
lean_dec_ref(v___y_501_);
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
v___x_527_ = lean_int_mul(v___y_498_, v_d_521_);
v___x_528_ = lean_int_mul(v_k_522_, v___y_503_);
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
lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_540_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_541_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_540_, v___y_514_, v___y_508_);
if (lean_obj_tag(v___x_541_) == 0)
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_549_; 
lean_dec_ref_known(v___x_541_, 1);
v___x_542_ = lean_int_mul(v_fst_535_, v_d_521_);
lean_dec(v_fst_535_);
lean_inc_ref(v___y_502_);
v___x_543_ = l_Int_Internal_Linear_Poly_mul(v___y_502_, v___x_542_);
lean_dec(v___x_542_);
v___x_544_ = lean_int_mul(v_snd_536_, v___y_503_);
lean_dec(v_snd_536_);
lean_inc_ref(v_p_523_);
v___x_545_ = l_Int_Internal_Linear_Poly_mul(v_p_523_, v___x_544_);
lean_dec(v___x_544_);
v___x_546_ = lean_int_mul(v___y_503_, v_d_521_);
lean_dec(v___y_503_);
v___x_547_ = l_Int_Internal_Linear_Poly_combine(v___x_543_, v___x_545_);
lean_inc(v_fst_531_);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 2, v___x_547_);
lean_ctor_set(v___x_525_, 1, v___y_505_);
lean_ctor_set(v___x_525_, 0, v_fst_531_);
v___x_549_ = v___x_525_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_573_; 
v_reuseFailAlloc_573_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_573_, 0, v_fst_531_);
lean_ctor_set(v_reuseFailAlloc_573_, 1, v___y_505_);
lean_ctor_set(v_reuseFailAlloc_573_, 2, v___x_547_);
v___x_549_ = v_reuseFailAlloc_573_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
lean_object* v___x_551_; 
lean_inc(v_val_519_);
lean_inc_ref(v___y_511_);
if (v_isShared_539_ == 0)
{
lean_ctor_set_tag(v___x_538_, 4);
lean_ctor_set(v___x_538_, 1, v_val_519_);
lean_ctor_set(v___x_538_, 0, v___y_511_);
v___x_551_ = v___x_538_;
goto v_reusejp_550_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v___y_511_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_val_519_);
v___x_551_ = v_reuseFailAlloc_572_;
goto v_reusejp_550_;
}
v_reusejp_550_:
{
lean_object* v___x_552_; lean_object* v___x_553_; 
v___x_552_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_552_, 0, v___x_546_);
lean_ctor_set(v___x_552_, 1, v___x_549_);
lean_ctor_set(v___x_552_, 2, v___x_551_);
lean_inc_ref(v___y_513_);
v___x_553_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v___x_552_, v___y_508_, v___y_507_, v___y_509_, v___y_516_, v___y_506_, v___y_517_, v___y_500_, v___y_515_, v___y_513_, v___y_497_);
if (lean_obj_tag(v___x_553_) == 0)
{
lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_559_; 
lean_dec_ref_known(v___x_553_, 1);
v___x_554_ = l_Int_Internal_Linear_Poly_mul(v___y_502_, v_k_522_);
lean_dec(v_k_522_);
v___x_555_ = lean_int_neg(v___y_498_);
lean_dec(v___y_498_);
v___x_556_ = l_Int_Internal_Linear_Poly_mul(v_p_523_, v___x_555_);
lean_dec(v___x_555_);
v___x_557_ = l_Int_Internal_Linear_Poly_combine(v___x_554_, v___x_556_);
lean_inc(v_val_519_);
if (v_isShared_534_ == 0)
{
lean_ctor_set_tag(v___x_533_, 5);
lean_ctor_set(v___x_533_, 1, v_val_519_);
lean_ctor_set(v___x_533_, 0, v___y_511_);
v___x_559_ = v___x_533_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v___y_511_);
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
v_a_471_ = v___y_508_;
v_a_472_ = v___y_507_;
v_a_473_ = v___y_509_;
v_a_474_ = v___y_516_;
v_a_475_ = v___y_506_;
v_a_476_ = v___y_517_;
v_a_477_ = v___y_500_;
v_a_478_ = v___y_515_;
v_a_479_ = v___y_513_;
v_a_480_ = v___y_497_;
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
lean_dec_ref(v___y_513_);
lean_dec_ref(v___y_511_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_498_);
return v___x_553_;
}
}
}
}
else
{
lean_del_object(v___x_538_);
lean_dec(v_snd_536_);
lean_dec(v_fst_535_);
lean_del_object(v___x_533_);
lean_dec(v_fst_531_);
lean_del_object(v___x_525_);
lean_dec_ref(v_p_523_);
lean_dec(v_k_522_);
lean_dec(v_val_519_);
lean_dec_ref(v___y_513_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_505_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_498_);
return v___x_541_;
}
}
}
}
}
else
{
lean_object* v___x_578_; 
lean_dec_ref(v_p_520_);
lean_dec_ref(v___y_514_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_505_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_498_);
v___x_578_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_val_519_, v___y_508_, v___y_507_, v___y_509_, v___y_516_, v___y_506_, v___y_517_, v___y_500_, v___y_515_, v___y_513_, v___y_497_);
lean_dec_ref(v___y_513_);
return v___x_578_;
}
}
else
{
lean_object* v_toCold_579_; lean_object* v_options_580_; uint8_t v_hasTrace_581_; 
lean_dec(v___y_518_);
lean_dec_ref(v___y_514_);
lean_dec(v___y_505_);
lean_dec(v___y_503_);
lean_dec_ref(v___y_502_);
lean_dec(v___y_498_);
v_toCold_579_ = lean_ctor_get(v___y_513_, 0);
v_options_580_ = lean_ctor_get(v_toCold_579_, 2);
v_hasTrace_581_ = lean_ctor_get_uint8(v_options_580_, sizeof(void*)*1);
if (v_hasTrace_581_ == 0)
{
lean_dec_ref(v___y_511_);
v___y_486_ = v___y_510_;
v___y_487_ = v___y_501_;
v___y_488_ = v___y_508_;
v___y_489_ = v___y_500_;
v___y_490_ = v___y_515_;
v___y_491_ = v___y_513_;
v___y_492_ = v___y_497_;
goto v___jp_485_;
}
else
{
lean_object* v_inheritedTraceOptions_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; uint8_t v___x_587_; 
v_inheritedTraceOptions_582_ = lean_ctor_get(v_toCold_579_, 11);
v___x_583_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0));
lean_inc_ref(v___y_499_);
lean_inc_ref(v___y_504_);
lean_inc_ref(v___y_512_);
v___x_584_ = l_Lean_Name_mkStr4(v___y_512_, v___y_504_, v___y_499_, v___x_583_);
v___x_585_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
lean_inc(v___x_584_);
v___x_586_ = l_Lean_Name_append(v___x_585_, v___x_584_);
v___x_587_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_582_, v_options_580_, v___x_586_);
lean_dec(v___x_586_);
if (v___x_587_ == 0)
{
lean_dec(v___x_584_);
lean_dec_ref(v___y_511_);
v___y_486_ = v___y_510_;
v___y_487_ = v___y_501_;
v___y_488_ = v___y_508_;
v___y_489_ = v___y_500_;
v___y_490_ = v___y_515_;
v___y_491_ = v___y_513_;
v___y_492_ = v___y_497_;
goto v___jp_485_;
}
else
{
lean_object* v___x_588_; 
v___x_588_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v___y_511_, v___y_508_, v___y_513_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v_a_589_; lean_object* v___x_590_; 
v_a_589_ = lean_ctor_get(v___x_588_, 0);
lean_inc(v_a_589_);
lean_dec_ref_known(v___x_588_, 1);
v___x_590_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_584_, v_a_589_, v___y_500_, v___y_515_, v___y_513_, v___y_497_);
if (lean_obj_tag(v___x_590_) == 0)
{
lean_dec_ref_known(v___x_590_, 1);
v___y_486_ = v___y_510_;
v___y_487_ = v___y_501_;
v___y_488_ = v___y_508_;
v___y_489_ = v___y_500_;
v___y_490_ = v___y_515_;
v___y_491_ = v___y_513_;
v___y_492_ = v___y_497_;
goto v___jp_485_;
}
else
{
lean_dec_ref(v___y_513_);
lean_dec_ref(v___y_510_);
lean_dec_ref(v___y_501_);
return v___x_590_;
}
}
else
{
lean_object* v_a_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_598_; 
lean_dec(v___x_584_);
lean_dec_ref(v___y_513_);
lean_dec_ref(v___y_510_);
lean_dec_ref(v___y_501_);
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
v___jp_631_:
{
lean_object* v___x_653_; 
v___x_653_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v___y_643_, v___y_651_);
if (lean_obj_tag(v___x_653_) == 0)
{
lean_object* v_a_654_; lean_object* v_dvds_655_; lean_object* v_size_656_; uint8_t v___x_657_; 
v_a_654_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_a_654_);
lean_dec_ref_known(v___x_653_, 1);
v_dvds_655_ = lean_ctor_get(v_a_654_, 6);
lean_inc_ref(v_dvds_655_);
lean_dec(v_a_654_);
v_size_656_ = lean_ctor_get(v_dvds_655_, 2);
v___x_657_ = lean_nat_dec_lt(v___y_641_, v_size_656_);
if (v___x_657_ == 0)
{
lean_object* v___x_658_; 
lean_dec_ref(v_dvds_655_);
v___x_658_ = l_outOfBounds___redArg(v___x_630_);
v___y_497_ = v___y_652_;
v___y_498_ = v___y_632_;
v___y_499_ = v___y_633_;
v___y_500_ = v___y_649_;
v___y_501_ = v___y_638_;
v___y_502_ = v___y_637_;
v___y_503_ = v___y_639_;
v___y_504_ = v___y_640_;
v___y_505_ = v___y_641_;
v___y_506_ = v___y_647_;
v___y_507_ = v___y_644_;
v___y_508_ = v___y_643_;
v___y_509_ = v___y_645_;
v___y_510_ = v___y_635_;
v___y_511_ = v___y_634_;
v___y_512_ = v___y_636_;
v___y_513_ = v___y_651_;
v___y_514_ = v___y_642_;
v___y_515_ = v___y_650_;
v___y_516_ = v___y_646_;
v___y_517_ = v___y_648_;
v___y_518_ = v___x_658_;
goto v___jp_496_;
}
else
{
lean_object* v___x_659_; 
v___x_659_ = l_Lean_PersistentArray_get_x21___redArg(v___x_630_, v_dvds_655_, v___y_641_);
lean_dec_ref(v_dvds_655_);
v___y_497_ = v___y_652_;
v___y_498_ = v___y_632_;
v___y_499_ = v___y_633_;
v___y_500_ = v___y_649_;
v___y_501_ = v___y_638_;
v___y_502_ = v___y_637_;
v___y_503_ = v___y_639_;
v___y_504_ = v___y_640_;
v___y_505_ = v___y_641_;
v___y_506_ = v___y_647_;
v___y_507_ = v___y_644_;
v___y_508_ = v___y_643_;
v___y_509_ = v___y_645_;
v___y_510_ = v___y_635_;
v___y_511_ = v___y_634_;
v___y_512_ = v___y_636_;
v___y_513_ = v___y_651_;
v___y_514_ = v___y_642_;
v___y_515_ = v___y_650_;
v___y_516_ = v___y_646_;
v___y_517_ = v___y_648_;
v___y_518_ = v___x_659_;
goto v___jp_496_;
}
}
else
{
lean_object* v_a_660_; lean_object* v___x_662_; uint8_t v_isShared_663_; uint8_t v_isSharedCheck_667_; 
lean_dec_ref(v___y_651_);
lean_dec_ref(v___y_642_);
lean_dec(v___y_641_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec_ref(v___y_635_);
lean_dec_ref(v___y_634_);
lean_dec(v___y_632_);
v_a_660_ = lean_ctor_get(v___x_653_, 0);
v_isSharedCheck_667_ = !lean_is_exclusive(v___x_653_);
if (v_isSharedCheck_667_ == 0)
{
v___x_662_ = v___x_653_;
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
else
{
lean_inc(v_a_660_);
lean_dec(v___x_653_);
v___x_662_ = lean_box(0);
v_isShared_663_ = v_isSharedCheck_667_;
goto v_resetjp_661_;
}
v_resetjp_661_:
{
lean_object* v___x_665_; 
if (v_isShared_663_ == 0)
{
v___x_665_ = v___x_662_;
goto v_reusejp_664_;
}
else
{
lean_object* v_reuseFailAlloc_666_; 
v_reuseFailAlloc_666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_666_, 0, v_a_660_);
v___x_665_ = v_reuseFailAlloc_666_;
goto v_reusejp_664_;
}
v_reusejp_664_:
{
return v___x_665_;
}
}
}
}
v___jp_668_:
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(v_c_470_);
lean_inc_ref(v___y_680_);
v___x_683_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(v___x_682_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v_a_684_; lean_object* v_d_685_; lean_object* v_p_686_; uint8_t v___x_687_; 
v_a_684_ = lean_ctor_get(v___x_683_, 0);
lean_inc(v_a_684_);
lean_dec_ref_known(v___x_683_, 1);
v_d_685_ = lean_ctor_get(v_a_684_, 0);
v_p_686_ = lean_ctor_get(v_a_684_, 1);
lean_inc(v_d_685_);
v___x_687_ = l_Int_Internal_Linear_Poly_isUnsatDvd(v_d_685_, v_p_686_);
if (v___x_687_ == 0)
{
uint8_t v___x_688_; 
v___x_688_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(v_a_684_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; uint8_t v___x_690_; 
v___x_689_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1);
v___x_690_ = lean_int_dec_eq(v_d_685_, v___x_689_);
if (v___x_690_ == 0)
{
if (lean_obj_tag(v_p_686_) == 1)
{
lean_object* v_k_691_; lean_object* v_v_692_; lean_object* v_p_693_; lean_object* v___x_694_; 
lean_inc_ref(v_p_686_);
lean_inc(v_d_685_);
v_k_691_ = lean_ctor_get(v_p_686_, 0);
lean_inc(v_k_691_);
v_v_692_ = lean_ctor_get(v_p_686_, 1);
lean_inc(v_v_692_);
v_p_693_ = lean_ctor_get(v_p_686_, 2);
lean_inc_ref(v_p_693_);
lean_inc(v_a_684_);
v___x_694_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(v_a_684_, v___y_672_, v___y_680_);
if (lean_obj_tag(v___x_694_) == 0)
{
lean_object* v_a_695_; lean_object* v___f_696_; lean_object* v___f_697_; uint8_t v___x_698_; uint8_t v___x_699_; uint8_t v___x_700_; 
v_a_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_a_695_);
lean_dec_ref_known(v___x_694_, 1);
lean_inc_n(v_v_692_, 2);
lean_inc(v_a_684_);
v___f_696_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed), 3, 2);
lean_closure_set(v___f_696_, 0, v_a_684_);
lean_closure_set(v___f_696_, 1, v_v_692_);
v___f_697_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed), 2, 1);
lean_closure_set(v___f_697_, 0, v_v_692_);
v___x_698_ = 0;
v___x_699_ = lean_unbox(v_a_695_);
lean_dec(v_a_695_);
v___x_700_ = l_Lean_instBEqLBool_beq(v___x_699_, v___x_698_);
if (v___x_700_ == 0)
{
v___y_632_ = v_k_691_;
v___y_633_ = v___y_669_;
v___y_634_ = v_a_684_;
v___y_635_ = v_p_686_;
v___y_636_ = v___y_670_;
v___y_637_ = v_p_693_;
v___y_638_ = v___f_696_;
v___y_639_ = v_d_685_;
v___y_640_ = v___y_671_;
v___y_641_ = v_v_692_;
v___y_642_ = v___f_697_;
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
goto v___jp_631_;
}
else
{
lean_object* v___x_701_; 
lean_inc(v_v_692_);
v___x_701_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v_v_692_, v___y_672_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_dec_ref_known(v___x_701_, 1);
v___y_632_ = v_k_691_;
v___y_633_ = v___y_669_;
v___y_634_ = v_a_684_;
v___y_635_ = v_p_686_;
v___y_636_ = v___y_670_;
v___y_637_ = v_p_693_;
v___y_638_ = v___f_696_;
v___y_639_ = v_d_685_;
v___y_640_ = v___y_671_;
v___y_641_ = v_v_692_;
v___y_642_ = v___f_697_;
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
goto v___jp_631_;
}
else
{
lean_dec_ref(v___f_697_);
lean_dec_ref(v___f_696_);
lean_dec_ref(v_p_693_);
lean_dec(v_v_692_);
lean_dec_ref_known(v_p_686_, 3);
lean_dec(v_k_691_);
lean_dec(v_d_685_);
lean_dec(v_a_684_);
lean_dec_ref(v___y_680_);
return v___x_701_;
}
}
}
else
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_709_; 
lean_dec_ref(v_p_693_);
lean_dec(v_v_692_);
lean_dec_ref_known(v_p_686_, 3);
lean_dec(v_k_691_);
lean_dec(v_d_685_);
lean_dec(v_a_684_);
lean_dec_ref(v___y_680_);
v_a_702_ = lean_ctor_get(v___x_694_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_694_);
if (v_isSharedCheck_709_ == 0)
{
v___x_704_ = v___x_694_;
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_694_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_707_; 
if (v_isShared_705_ == 0)
{
v___x_707_ = v___x_704_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_a_702_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
else
{
lean_object* v___x_710_; 
v___x_710_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_a_684_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
lean_dec_ref(v___y_680_);
return v___x_710_;
}
}
else
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
lean_inc_ref(v_p_686_);
v___x_711_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_711_, 0, v_a_684_);
v___x_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_712_, 0, v_p_686_);
lean_ctor_set(v___x_712_, 1, v___x_711_);
lean_inc(v___y_681_);
lean_inc(v___y_679_);
lean_inc_ref(v___y_678_);
lean_inc(v___y_677_);
lean_inc_ref(v___y_676_);
lean_inc(v___y_675_);
lean_inc_ref(v___y_674_);
lean_inc(v___y_673_);
lean_inc(v___y_672_);
v___x_713_ = lean_grind_cutsat_assert_eq(v___x_712_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_721_; 
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_721_ == 0)
{
lean_object* v_unused_722_; 
v_unused_722_ = lean_ctor_get(v___x_713_, 0);
lean_dec(v_unused_722_);
v___x_715_ = v___x_713_;
v_isShared_716_ = v_isSharedCheck_721_;
goto v_resetjp_714_;
}
else
{
lean_dec(v___x_713_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_721_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_717_; lean_object* v___x_719_; 
v___x_717_ = lean_box(0);
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 0, v___x_717_);
v___x_719_ = v___x_715_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_717_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
else
{
return v___x_713_;
}
}
}
else
{
lean_object* v_toCold_723_; lean_object* v_options_724_; uint8_t v_hasTrace_725_; 
v_toCold_723_ = lean_ctor_get(v___y_680_, 0);
v_options_724_ = lean_ctor_get(v_toCold_723_, 2);
v_hasTrace_725_ = lean_ctor_get_uint8(v_options_724_, sizeof(void*)*1);
if (v_hasTrace_725_ == 0)
{
lean_dec(v_a_684_);
lean_dec_ref(v___y_680_);
goto v___jp_482_;
}
else
{
lean_object* v_inheritedTraceOptions_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; uint8_t v___x_731_; 
v_inheritedTraceOptions_726_ = lean_ctor_get(v_toCold_723_, 11);
v___x_727_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1));
lean_inc_ref(v___y_669_);
lean_inc_ref(v___y_671_);
lean_inc_ref(v___y_670_);
v___x_728_ = l_Lean_Name_mkStr4(v___y_670_, v___y_671_, v___y_669_, v___x_727_);
v___x_729_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
lean_inc(v___x_728_);
v___x_730_ = l_Lean_Name_append(v___x_729_, v___x_728_);
v___x_731_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_726_, v_options_724_, v___x_730_);
lean_dec(v___x_730_);
if (v___x_731_ == 0)
{
lean_dec(v___x_728_);
lean_dec(v_a_684_);
lean_dec_ref(v___y_680_);
goto v___jp_482_;
}
else
{
lean_object* v___x_732_; 
v___x_732_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_a_684_, v___y_672_, v___y_680_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_object* v_a_733_; lean_object* v___x_734_; 
v_a_733_ = lean_ctor_get(v___x_732_, 0);
lean_inc(v_a_733_);
lean_dec_ref_known(v___x_732_, 1);
v___x_734_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_728_, v_a_733_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
lean_dec_ref(v___y_680_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_dec_ref_known(v___x_734_, 1);
goto v___jp_482_;
}
else
{
return v___x_734_;
}
}
else
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_742_; 
lean_dec(v___x_728_);
lean_dec_ref(v___y_680_);
v_a_735_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_742_ == 0)
{
v___x_737_ = v___x_732_;
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_732_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_740_; 
if (v_isShared_738_ == 0)
{
v___x_740_ = v___x_737_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_a_735_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
}
}
}
else
{
lean_object* v_toCold_743_; lean_object* v_options_744_; uint8_t v_hasTrace_745_; 
v_toCold_743_ = lean_ctor_get(v___y_680_, 0);
v_options_744_ = lean_ctor_get(v_toCold_743_, 2);
v_hasTrace_745_ = lean_ctor_get_uint8(v_options_744_, sizeof(void*)*1);
if (v_hasTrace_745_ == 0)
{
v___y_600_ = v_a_684_;
v___y_601_ = v___y_672_;
v___y_602_ = v___y_673_;
v___y_603_ = v___y_674_;
v___y_604_ = v___y_675_;
v___y_605_ = v___y_676_;
v___y_606_ = v___y_677_;
v___y_607_ = v___y_678_;
v___y_608_ = v___y_679_;
v___y_609_ = v___y_680_;
v___y_610_ = v___y_681_;
goto v___jp_599_;
}
else
{
lean_object* v_inheritedTraceOptions_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; uint8_t v___x_751_; 
v_inheritedTraceOptions_746_ = lean_ctor_get(v_toCold_743_, 11);
v___x_747_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2));
lean_inc_ref(v___y_669_);
lean_inc_ref(v___y_671_);
lean_inc_ref(v___y_670_);
v___x_748_ = l_Lean_Name_mkStr4(v___y_670_, v___y_671_, v___y_669_, v___x_747_);
v___x_749_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
lean_inc(v___x_748_);
v___x_750_ = l_Lean_Name_append(v___x_749_, v___x_748_);
v___x_751_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_746_, v_options_744_, v___x_750_);
lean_dec(v___x_750_);
if (v___x_751_ == 0)
{
lean_dec(v___x_748_);
v___y_600_ = v_a_684_;
v___y_601_ = v___y_672_;
v___y_602_ = v___y_673_;
v___y_603_ = v___y_674_;
v___y_604_ = v___y_675_;
v___y_605_ = v___y_676_;
v___y_606_ = v___y_677_;
v___y_607_ = v___y_678_;
v___y_608_ = v___y_679_;
v___y_609_ = v___y_680_;
v___y_610_ = v___y_681_;
goto v___jp_599_;
}
else
{
lean_object* v___x_752_; 
lean_inc(v_a_684_);
v___x_752_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_a_684_, v___y_672_, v___y_680_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v_a_753_; lean_object* v___x_754_; 
v_a_753_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_a_753_);
lean_dec_ref_known(v___x_752_, 1);
v___x_754_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_748_, v_a_753_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_dec_ref_known(v___x_754_, 1);
v___y_600_ = v_a_684_;
v___y_601_ = v___y_672_;
v___y_602_ = v___y_673_;
v___y_603_ = v___y_674_;
v___y_604_ = v___y_675_;
v___y_605_ = v___y_676_;
v___y_606_ = v___y_677_;
v___y_607_ = v___y_678_;
v___y_608_ = v___y_679_;
v___y_609_ = v___y_680_;
v___y_610_ = v___y_681_;
goto v___jp_599_;
}
else
{
lean_dec(v_a_684_);
lean_dec_ref(v___y_680_);
return v___x_754_;
}
}
else
{
lean_object* v_a_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_762_; 
lean_dec(v___x_748_);
lean_dec(v_a_684_);
lean_dec_ref(v___y_680_);
v_a_755_ = lean_ctor_get(v___x_752_, 0);
v_isSharedCheck_762_ = !lean_is_exclusive(v___x_752_);
if (v_isSharedCheck_762_ == 0)
{
v___x_757_ = v___x_752_;
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_a_755_);
lean_dec(v___x_752_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_762_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v___x_760_; 
if (v_isShared_758_ == 0)
{
v___x_760_ = v___x_757_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_a_755_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_770_; 
lean_dec_ref(v___y_680_);
v_a_763_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_770_ == 0)
{
v___x_765_ = v___x_683_;
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_683_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_768_; 
if (v_isShared_766_ == 0)
{
v___x_768_ = v___x_765_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_a_763_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
v___jp_771_:
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_772_ = lean_unsigned_to_nat(1u);
v___x_773_ = lean_nat_add(v_currRecDepth_623_, v___x_772_);
lean_dec(v_currRecDepth_623_);
v___x_774_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_774_, 0, v_toCold_622_);
lean_ctor_set(v___x_774_, 1, v___x_773_);
lean_ctor_set(v___x_774_, 2, v_ref_624_);
lean_ctor_set_uint8(v___x_774_, sizeof(void*)*3, v_diag_625_);
lean_ctor_set_uint8(v___x_774_, sizeof(void*)*3 + 1, v_suppressElabErrors_626_);
v___x_775_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_471_, v___x_774_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_803_; 
v_a_776_ = lean_ctor_get(v___x_775_, 0);
v_isSharedCheck_803_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_803_ == 0)
{
v___x_778_ = v___x_775_;
v_isShared_779_ = v_isSharedCheck_803_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_775_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_803_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
uint8_t v___x_780_; 
v___x_780_ = lean_unbox(v_a_776_);
lean_dec(v_a_776_);
if (v___x_780_ == 0)
{
uint8_t v_hasTrace_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
lean_del_object(v___x_778_);
v_hasTrace_781_ = lean_ctor_get_uint8(v_options_627_, sizeof(void*)*1);
v___x_782_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0));
v___x_783_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2));
v___x_784_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3));
if (v_hasTrace_781_ == 0)
{
lean_dec_ref(v_inheritedTraceOptions_629_);
lean_dec_ref(v_options_627_);
v___y_669_ = v___x_784_;
v___y_670_ = v___x_782_;
v___y_671_ = v___x_783_;
v___y_672_ = v_a_471_;
v___y_673_ = v_a_472_;
v___y_674_ = v_a_473_;
v___y_675_ = v_a_474_;
v___y_676_ = v_a_475_;
v___y_677_ = v_a_476_;
v___y_678_ = v_a_477_;
v___y_679_ = v_a_478_;
v___y_680_ = v___x_774_;
v___y_681_ = v_a_480_;
goto v___jp_668_;
}
else
{
lean_object* v___x_785_; lean_object* v___x_786_; uint8_t v___x_787_; 
v___x_785_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4));
v___x_786_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5);
v___x_787_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_629_, v_options_627_, v___x_786_);
lean_dec_ref(v_options_627_);
lean_dec_ref(v_inheritedTraceOptions_629_);
if (v___x_787_ == 0)
{
v___y_669_ = v___x_784_;
v___y_670_ = v___x_782_;
v___y_671_ = v___x_783_;
v___y_672_ = v_a_471_;
v___y_673_ = v_a_472_;
v___y_674_ = v_a_473_;
v___y_675_ = v_a_474_;
v___y_676_ = v_a_475_;
v___y_677_ = v_a_476_;
v___y_678_ = v_a_477_;
v___y_679_ = v_a_478_;
v___y_680_ = v___x_774_;
v___y_681_ = v_a_480_;
goto v___jp_668_;
}
else
{
lean_object* v___x_788_; 
lean_inc_ref(v_c_470_);
v___x_788_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_470_, v_a_471_, v___x_774_);
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v_a_789_; lean_object* v___x_790_; 
v_a_789_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_a_789_);
lean_dec_ref_known(v___x_788_, 1);
v___x_790_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_785_, v_a_789_, v_a_477_, v_a_478_, v___x_774_, v_a_480_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_dec_ref_known(v___x_790_, 1);
v___y_669_ = v___x_784_;
v___y_670_ = v___x_782_;
v___y_671_ = v___x_783_;
v___y_672_ = v_a_471_;
v___y_673_ = v_a_472_;
v___y_674_ = v_a_473_;
v___y_675_ = v_a_474_;
v___y_676_ = v_a_475_;
v___y_677_ = v_a_476_;
v___y_678_ = v_a_477_;
v___y_679_ = v_a_478_;
v___y_680_ = v___x_774_;
v___y_681_ = v_a_480_;
goto v___jp_668_;
}
else
{
lean_dec_ref_known(v___x_774_, 3);
lean_dec_ref(v_c_470_);
return v___x_790_;
}
}
else
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
lean_dec_ref_known(v___x_774_, 3);
lean_dec_ref(v_c_470_);
v_a_791_ = lean_ctor_get(v___x_788_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_788_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v___x_788_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_788_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
}
}
else
{
lean_object* v___x_799_; lean_object* v___x_801_; 
lean_dec_ref_known(v___x_774_, 3);
lean_dec_ref(v_inheritedTraceOptions_629_);
lean_dec_ref(v_options_627_);
lean_dec_ref(v_c_470_);
v___x_799_ = lean_box(0);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 0, v___x_799_);
v___x_801_ = v___x_778_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v___x_799_);
v___x_801_ = v_reuseFailAlloc_802_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
return v___x_801_;
}
}
}
}
else
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_811_; 
lean_dec_ref_known(v___x_774_, 3);
lean_dec_ref(v_inheritedTraceOptions_629_);
lean_dec_ref(v_options_627_);
lean_dec_ref(v_c_470_);
v_a_804_ = lean_ctor_get(v___x_775_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_811_ == 0)
{
v___x_806_ = v___x_775_;
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_775_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___boxed(lean_object* v_c_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v_c_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_);
lean_dec(v_a_826_);
lean_dec(v_a_824_);
lean_dec_ref(v_a_823_);
lean_dec(v_a_822_);
lean_dec_ref(v_a_821_);
lean_dec(v_a_820_);
lean_dec_ref(v_a_819_);
lean_dec(v_a_818_);
lean_dec(v_a_817_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(lean_object* v_c_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_){
_start:
{
lean_object* v_d_841_; lean_object* v_p_842_; lean_object* v___x_843_; 
v_d_841_ = lean_ctor_get(v_c_829_, 0);
v_p_842_ = lean_ctor_get(v_c_829_, 1);
lean_inc_ref(v_p_842_);
v___x_843_ = l_Int_Internal_Linear_Poly_normCommRing_x3f(v_p_842_, v_a_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_844_; 
v_a_844_ = lean_ctor_get(v___x_843_, 0);
lean_inc(v_a_844_);
lean_dec_ref_known(v___x_843_, 1);
if (lean_obj_tag(v_a_844_) == 1)
{
lean_object* v_val_845_; lean_object* v_snd_846_; lean_object* v_fst_847_; lean_object* v_fst_848_; lean_object* v_snd_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
lean_inc(v_d_841_);
v_val_845_ = lean_ctor_get(v_a_844_, 0);
lean_inc(v_val_845_);
lean_dec_ref_known(v_a_844_, 1);
v_snd_846_ = lean_ctor_get(v_val_845_, 1);
lean_inc(v_snd_846_);
v_fst_847_ = lean_ctor_get(v_val_845_, 0);
lean_inc(v_fst_847_);
lean_dec(v_val_845_);
v_fst_848_ = lean_ctor_get(v_snd_846_, 0);
lean_inc(v_fst_848_);
v_snd_849_ = lean_ctor_get(v_snd_846_, 1);
lean_inc(v_snd_849_);
lean_dec(v_snd_846_);
v___x_850_ = lean_alloc_ctor(12, 3, 0);
lean_ctor_set(v___x_850_, 0, v_c_829_);
lean_ctor_set(v___x_850_, 1, v_fst_847_);
lean_ctor_set(v___x_850_, 2, v_fst_848_);
v___x_851_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_851_, 0, v_d_841_);
lean_ctor_set(v___x_851_, 1, v_snd_849_);
lean_ctor_set(v___x_851_, 2, v___x_850_);
lean_inc_ref(v_a_838_);
v___x_852_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v___x_851_, v_a_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_);
return v___x_852_;
}
else
{
lean_object* v___x_853_; 
lean_dec(v_a_844_);
lean_inc_ref(v_a_838_);
v___x_853_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v_c_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_);
return v___x_853_;
}
}
else
{
lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_861_; 
lean_dec_ref(v_c_829_);
v_a_854_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_861_ == 0)
{
v___x_856_ = v___x_843_;
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_843_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_859_; 
if (v_isShared_857_ == 0)
{
v___x_859_ = v___x_856_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_a_854_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore___boxed(lean_object* v_c_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_){
_start:
{
lean_object* v_res_874_; 
v_res_874_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v_c_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_);
lean_dec(v_a_872_);
lean_dec_ref(v_a_871_);
lean_dec(v_a_870_);
lean_dec_ref(v_a_869_);
lean_dec(v_a_868_);
lean_dec_ref(v_a_867_);
lean_dec(v_a_866_);
lean_dec_ref(v_a_865_);
lean_dec(v_a_864_);
lean_dec(v_a_863_);
return v_res_874_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8(void){
_start:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_889_ = lean_box(0);
v___x_890_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7));
v___x_891_ = l_Lean_mkConst(v___x_890_, v___x_889_);
return v___x_891_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10(void){
_start:
{
lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_893_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9));
v___x_894_ = l_Lean_stringToMessageData(v___x_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(lean_object* v_e_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_){
_start:
{
lean_object* v___x_910_; 
lean_inc_ref(v_e_895_);
v___x_910_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_895_, v_a_903_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_1044_; 
v_a_911_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_1044_ == 0)
{
v___x_913_ = v___x_910_;
v_isShared_914_ = v_isSharedCheck_1044_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_910_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_1044_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_920_; uint8_t v___x_921_; 
v___x_920_ = l_Lean_Expr_cleanupAnnotations(v_a_911_);
v___x_921_ = l_Lean_Expr_isApp(v___x_920_);
if (v___x_921_ == 0)
{
lean_dec_ref(v___x_920_);
lean_dec_ref(v_e_895_);
goto v___jp_915_;
}
else
{
lean_object* v_arg_922_; lean_object* v___x_923_; uint8_t v___x_924_; 
v_arg_922_ = lean_ctor_get(v___x_920_, 1);
lean_inc_ref(v_arg_922_);
v___x_923_ = l_Lean_Expr_appFnCleanup___redArg(v___x_920_);
v___x_924_ = l_Lean_Expr_isApp(v___x_923_);
if (v___x_924_ == 0)
{
lean_dec_ref(v___x_923_);
lean_dec_ref(v_arg_922_);
lean_dec_ref(v_e_895_);
goto v___jp_915_;
}
else
{
lean_object* v_arg_925_; lean_object* v___x_926_; uint8_t v___x_927_; 
v_arg_925_ = lean_ctor_get(v___x_923_, 1);
lean_inc_ref(v_arg_925_);
v___x_926_ = l_Lean_Expr_appFnCleanup___redArg(v___x_923_);
v___x_927_ = l_Lean_Expr_isApp(v___x_926_);
if (v___x_927_ == 0)
{
lean_dec_ref(v___x_926_);
lean_dec_ref(v_arg_925_);
lean_dec_ref(v_arg_922_);
lean_dec_ref(v_e_895_);
goto v___jp_915_;
}
else
{
lean_object* v_arg_928_; lean_object* v___x_929_; uint8_t v___x_930_; 
v_arg_928_ = lean_ctor_get(v___x_926_, 1);
lean_inc_ref(v_arg_928_);
v___x_929_ = l_Lean_Expr_appFnCleanup___redArg(v___x_926_);
v___x_930_ = l_Lean_Expr_isApp(v___x_929_);
if (v___x_930_ == 0)
{
lean_dec_ref(v___x_929_);
lean_dec_ref(v_arg_928_);
lean_dec_ref(v_arg_925_);
lean_dec_ref(v_arg_922_);
lean_dec_ref(v_e_895_);
goto v___jp_915_;
}
else
{
lean_object* v___x_931_; lean_object* v___x_932_; uint8_t v___x_933_; 
v___x_931_ = l_Lean_Expr_appFnCleanup___redArg(v___x_929_);
v___x_932_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_933_ = l_Lean_Expr_isConstOf(v___x_931_, v___x_932_);
lean_dec_ref(v___x_931_);
if (v___x_933_ == 0)
{
lean_dec_ref(v_arg_928_);
lean_dec_ref(v_arg_925_);
lean_dec_ref(v_arg_922_);
lean_dec_ref(v_e_895_);
goto v___jp_915_;
}
else
{
lean_object* v___x_934_; 
lean_del_object(v___x_913_);
v___x_934_ = l_Lean_Meta_Structural_isInstDvdInt___redArg(v_arg_928_, v_a_903_);
if (lean_obj_tag(v___x_934_) == 0)
{
lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_1035_; 
v_a_935_ = lean_ctor_get(v___x_934_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_937_ = v___x_934_;
v_isShared_938_ = v_isSharedCheck_1035_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v___x_934_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_1035_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
uint8_t v___x_939_; 
v___x_939_ = lean_unbox(v_a_935_);
lean_dec(v_a_935_);
if (v___x_939_ == 0)
{
lean_object* v___x_940_; lean_object* v___x_942_; 
lean_dec_ref(v_arg_925_);
lean_dec_ref(v_arg_922_);
lean_dec_ref(v_e_895_);
v___x_940_ = lean_box(0);
if (v_isShared_938_ == 0)
{
lean_ctor_set(v___x_937_, 0, v___x_940_);
v___x_942_ = v___x_937_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v___x_940_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
else
{
lean_object* v___x_944_; 
lean_del_object(v___x_937_);
lean_inc_ref(v_arg_925_);
v___x_944_ = l_Lean_Meta_getIntValue_x3f(v_arg_925_, v_a_902_, v_a_903_, v_a_904_, v_a_905_);
if (lean_obj_tag(v___x_944_) == 0)
{
lean_object* v_a_945_; 
v_a_945_ = lean_ctor_get(v___x_944_, 0);
lean_inc(v_a_945_);
lean_dec_ref_known(v___x_944_, 1);
if (lean_obj_tag(v_a_945_) == 1)
{
lean_object* v_val_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_1011_; 
v_val_946_ = lean_ctor_get(v_a_945_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v_a_945_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_948_ = v_a_945_;
v_isShared_949_ = v_isSharedCheck_1011_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_val_946_);
lean_dec(v_a_945_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_1011_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_950_; 
lean_inc_ref(v_e_895_);
v___x_950_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_895_, v_a_896_, v_a_900_, v_a_902_, v_a_903_, v_a_904_, v_a_905_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_object* v_a_951_; uint8_t v___x_952_; 
v_a_951_ = lean_ctor_get(v___x_950_, 0);
lean_inc(v_a_951_);
lean_dec_ref_known(v___x_950_, 1);
v___x_952_ = lean_unbox(v_a_951_);
lean_dec(v_a_951_);
if (v___x_952_ == 0)
{
lean_object* v___x_953_; 
lean_del_object(v___x_948_);
lean_dec(v_val_946_);
lean_inc_ref(v_e_895_);
v___x_953_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_895_, v_a_896_, v_a_900_, v_a_902_, v_a_903_, v_a_904_, v_a_905_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_979_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_979_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_979_ == 0)
{
v___x_956_ = v___x_953_;
v_isShared_957_ = v_isSharedCheck_979_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_953_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_979_;
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
lean_dec_ref(v_arg_925_);
lean_dec_ref(v_arg_922_);
lean_dec_ref(v_e_895_);
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
lean_inc_ref(v_e_895_);
v___x_963_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_);
if (lean_obj_tag(v___x_963_) == 0)
{
lean_object* v_a_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; 
v_a_964_ = lean_ctor_get(v___x_963_, 0);
lean_inc(v_a_964_);
lean_dec_ref_known(v___x_963_, 1);
v___x_965_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8);
v___x_966_ = l_Lean_eagerReflBoolTrue;
v___x_967_ = l_Lean_Meta_mkOfEqFalseCore(v_e_895_, v_a_964_);
v___x_968_ = l_Lean_mkApp4(v___x_965_, v_arg_925_, v_arg_922_, v___x_966_, v___x_967_);
v___x_969_ = lean_unsigned_to_nat(0u);
v___x_970_ = l_Lean_Meta_Grind_pushNewFact(v___x_968_, v___x_969_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_);
return v___x_970_;
}
else
{
lean_object* v_a_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_978_; 
lean_dec_ref(v_arg_925_);
lean_dec_ref(v_arg_922_);
lean_dec_ref(v_e_895_);
v_a_971_ = lean_ctor_get(v___x_963_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_963_);
if (v_isSharedCheck_978_ == 0)
{
v___x_973_ = v___x_963_;
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_a_971_);
lean_dec(v___x_963_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_976_; 
if (v_isShared_974_ == 0)
{
v___x_976_ = v___x_973_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_a_971_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
}
}
else
{
lean_object* v_a_980_; lean_object* v___x_982_; uint8_t v_isShared_983_; uint8_t v_isSharedCheck_987_; 
lean_dec_ref(v_arg_925_);
lean_dec_ref(v_arg_922_);
lean_dec_ref(v_e_895_);
v_a_980_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_987_ == 0)
{
v___x_982_ = v___x_953_;
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
else
{
lean_inc(v_a_980_);
lean_dec(v___x_953_);
v___x_982_ = lean_box(0);
v_isShared_983_ = v_isSharedCheck_987_;
goto v_resetjp_981_;
}
v_resetjp_981_:
{
lean_object* v___x_985_; 
if (v_isShared_983_ == 0)
{
v___x_985_ = v___x_982_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v_a_980_);
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
lean_object* v___x_988_; 
lean_dec_ref(v_arg_925_);
v___x_988_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(v_arg_922_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_);
if (lean_obj_tag(v___x_988_) == 0)
{
lean_object* v_a_989_; lean_object* v___x_991_; 
v_a_989_ = lean_ctor_get(v___x_988_, 0);
lean_inc(v_a_989_);
lean_dec_ref_known(v___x_988_, 1);
if (v_isShared_949_ == 0)
{
lean_ctor_set_tag(v___x_948_, 0);
lean_ctor_set(v___x_948_, 0, v_e_895_);
v___x_991_ = v___x_948_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_e_895_);
v___x_991_ = v_reuseFailAlloc_994_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_992_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_992_, 0, v_val_946_);
lean_ctor_set(v___x_992_, 1, v_a_989_);
lean_ctor_set(v___x_992_, 2, v___x_991_);
v___x_993_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v___x_992_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_);
return v___x_993_;
}
}
else
{
lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1002_; 
lean_del_object(v___x_948_);
lean_dec(v_val_946_);
lean_dec_ref(v_e_895_);
v_a_995_ = lean_ctor_get(v___x_988_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_988_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_997_ = v___x_988_;
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_988_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1002_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_1000_; 
if (v_isShared_998_ == 0)
{
v___x_1000_ = v___x_997_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_a_995_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
}
}
}
else
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
lean_del_object(v___x_948_);
lean_dec(v_val_946_);
lean_dec_ref(v_arg_925_);
lean_dec_ref(v_arg_922_);
lean_dec_ref(v_e_895_);
v_a_1003_ = lean_ctor_get(v___x_950_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_950_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_950_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1003_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
}
else
{
lean_object* v___x_1012_; 
lean_dec(v_a_945_);
lean_dec_ref(v_arg_925_);
lean_dec_ref(v_arg_922_);
v___x_1012_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_900_);
if (lean_obj_tag(v___x_1012_) == 0)
{
lean_object* v_a_1013_; uint8_t v_verbose_1014_; 
v_a_1013_ = lean_ctor_get(v___x_1012_, 0);
lean_inc(v_a_1013_);
lean_dec_ref_known(v___x_1012_, 1);
v_verbose_1014_ = lean_ctor_get_uint8(v_a_1013_, 0);
lean_dec(v_a_1013_);
if (v_verbose_1014_ == 0)
{
lean_dec_ref(v_e_895_);
goto v___jp_907_;
}
else
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v___x_1015_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10);
v___x_1016_ = l_Lean_indentExpr(v_e_895_);
v___x_1017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1015_);
lean_ctor_set(v___x_1017_, 1, v___x_1016_);
v___x_1018_ = l_Lean_Meta_Sym_reportIssue(v___x_1017_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_, v_a_905_);
if (lean_obj_tag(v___x_1018_) == 0)
{
lean_dec_ref_known(v___x_1018_, 1);
goto v___jp_907_;
}
else
{
return v___x_1018_;
}
}
}
else
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
lean_dec_ref(v_e_895_);
v_a_1019_ = lean_ctor_get(v___x_1012_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1012_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___x_1012_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_1012_);
v___x_1021_ = lean_box(0);
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
v_resetjp_1020_:
{
lean_object* v___x_1024_; 
if (v_isShared_1022_ == 0)
{
v___x_1024_ = v___x_1021_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1019_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
}
}
else
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1034_; 
lean_dec_ref(v_arg_925_);
lean_dec_ref(v_arg_922_);
lean_dec_ref(v_e_895_);
v_a_1027_ = lean_ctor_get(v___x_944_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_944_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1029_ = v___x_944_;
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_944_);
v___x_1029_ = lean_box(0);
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
v_resetjp_1028_:
{
lean_object* v___x_1032_; 
if (v_isShared_1030_ == 0)
{
v___x_1032_ = v___x_1029_;
goto v_reusejp_1031_;
}
else
{
lean_object* v_reuseFailAlloc_1033_; 
v_reuseFailAlloc_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1033_, 0, v_a_1027_);
v___x_1032_ = v_reuseFailAlloc_1033_;
goto v_reusejp_1031_;
}
v_reusejp_1031_:
{
return v___x_1032_;
}
}
}
}
}
}
else
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1043_; 
lean_dec_ref(v_arg_925_);
lean_dec_ref(v_arg_922_);
lean_dec_ref(v_e_895_);
v_a_1036_ = lean_ctor_get(v___x_934_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1038_ = v___x_934_;
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_934_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1039_ == 0)
{
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_a_1036_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
}
}
}
}
v___jp_915_:
{
lean_object* v___x_916_; lean_object* v___x_918_; 
v___x_916_ = lean_box(0);
if (v_isShared_914_ == 0)
{
lean_ctor_set(v___x_913_, 0, v___x_916_);
v___x_918_ = v___x_913_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v___x_916_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
else
{
lean_object* v_a_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1052_; 
lean_dec_ref(v_e_895_);
v_a_1045_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_1052_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_1052_ == 0)
{
v___x_1047_ = v___x_910_;
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_a_1045_);
lean_dec(v___x_910_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1052_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1050_; 
if (v_isShared_1048_ == 0)
{
v___x_1050_ = v___x_1047_;
goto v_reusejp_1049_;
}
else
{
lean_object* v_reuseFailAlloc_1051_; 
v_reuseFailAlloc_1051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1051_, 0, v_a_1045_);
v___x_1050_ = v_reuseFailAlloc_1051_;
goto v_reusejp_1049_;
}
v_reusejp_1049_:
{
return v___x_1050_;
}
}
}
v___jp_907_:
{
lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_908_ = lean_box(0);
v___x_909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_909_, 0, v___x_908_);
return v___x_909_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___boxed(lean_object* v_e_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(v_e_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_);
lean_dec(v_a_1063_);
lean_dec_ref(v_a_1062_);
lean_dec(v_a_1061_);
lean_dec_ref(v_a_1060_);
lean_dec(v_a_1059_);
lean_dec_ref(v_a_1058_);
lean_dec(v_a_1057_);
lean_dec_ref(v_a_1056_);
lean_dec(v_a_1055_);
lean_dec(v_a_1054_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd_spec__0(lean_object* v_a_1066_){
_start:
{
lean_object* v___x_1067_; 
v___x_1067_ = lean_nat_to_int(v_a_1066_);
return v___x_1067_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3(void){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1073_ = lean_box(0);
v___x_1074_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2));
v___x_1075_ = l_Lean_mkConst(v___x_1074_, v___x_1073_);
return v___x_1075_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7(void){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1082_ = lean_box(0);
v___x_1083_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6));
v___x_1084_ = l_Lean_mkConst(v___x_1083_, v___x_1082_);
return v___x_1084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(lean_object* v_e_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_){
_start:
{
lean_object* v___x_1103_; uint8_t v___x_1104_; 
lean_inc_ref(v_e_1085_);
v___x_1103_ = l_Lean_Expr_cleanupAnnotations(v_e_1085_);
v___x_1104_ = l_Lean_Expr_isApp(v___x_1103_);
if (v___x_1104_ == 0)
{
lean_dec_ref(v___x_1103_);
lean_dec_ref(v_e_1085_);
goto v___jp_1097_;
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
lean_dec_ref(v_e_1085_);
goto v___jp_1097_;
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
lean_dec_ref(v_e_1085_);
goto v___jp_1097_;
}
else
{
lean_object* v_arg_1111_; lean_object* v___x_1112_; uint8_t v___x_1113_; 
v_arg_1111_ = lean_ctor_get(v___x_1109_, 1);
lean_inc_ref(v_arg_1111_);
v___x_1112_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1109_);
v___x_1113_ = l_Lean_Expr_isApp(v___x_1112_);
if (v___x_1113_ == 0)
{
lean_dec_ref(v___x_1112_);
lean_dec_ref(v_arg_1111_);
lean_dec_ref(v_arg_1108_);
lean_dec_ref(v_arg_1105_);
lean_dec_ref(v_e_1085_);
goto v___jp_1097_;
}
else
{
lean_object* v___x_1114_; lean_object* v___x_1115_; uint8_t v___x_1116_; 
v___x_1114_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1112_);
v___x_1115_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1116_ = l_Lean_Expr_isConstOf(v___x_1114_, v___x_1115_);
lean_dec_ref(v___x_1114_);
if (v___x_1116_ == 0)
{
lean_dec_ref(v_arg_1111_);
lean_dec_ref(v_arg_1108_);
lean_dec_ref(v_arg_1105_);
lean_dec_ref(v_e_1085_);
goto v___jp_1097_;
}
else
{
lean_object* v___x_1117_; 
v___x_1117_ = l_Lean_Meta_Structural_isInstDvdNat___redArg(v_arg_1111_, v_a_1093_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1249_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1120_ = v___x_1117_;
v_isShared_1121_ = v_isSharedCheck_1249_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1117_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1249_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
uint8_t v___x_1122_; 
v___x_1122_ = lean_unbox(v_a_1118_);
lean_dec(v_a_1118_);
if (v___x_1122_ == 0)
{
lean_object* v___x_1123_; lean_object* v___x_1125_; 
lean_dec_ref(v_arg_1108_);
lean_dec_ref(v_arg_1105_);
lean_dec_ref(v_e_1085_);
v___x_1123_ = lean_box(0);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 0, v___x_1123_);
v___x_1125_ = v___x_1120_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v___x_1123_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
else
{
lean_object* v___x_1127_; 
lean_del_object(v___x_1120_);
v___x_1127_ = l_Lean_Meta_getNatValue_x3f(v_arg_1108_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
if (lean_obj_tag(v___x_1127_) == 0)
{
lean_object* v_a_1128_; 
v_a_1128_ = lean_ctor_get(v___x_1127_, 0);
lean_inc(v_a_1128_);
lean_dec_ref_known(v___x_1127_, 1);
if (lean_obj_tag(v_a_1128_) == 1)
{
lean_object* v_val_1129_; lean_object* v___x_1130_; 
v_val_1129_ = lean_ctor_get(v_a_1128_, 0);
lean_inc(v_val_1129_);
lean_dec_ref_known(v_a_1128_, 1);
lean_inc_ref(v_e_1085_);
v___x_1130_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_1085_, v_a_1086_, v_a_1090_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v_a_1131_; uint8_t v___x_1132_; 
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
lean_inc(v_a_1131_);
lean_dec_ref_known(v___x_1130_, 1);
v___x_1132_ = lean_unbox(v_a_1131_);
lean_dec(v_a_1131_);
if (v___x_1132_ == 0)
{
lean_object* v___x_1133_; 
lean_dec(v_val_1129_);
lean_inc_ref(v_e_1085_);
v___x_1133_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_1085_, v_a_1086_, v_a_1090_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1158_; 
v_a_1134_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1136_ = v___x_1133_;
v_isShared_1137_ = v_isSharedCheck_1158_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1133_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1158_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
uint8_t v___x_1138_; 
v___x_1138_ = lean_unbox(v_a_1134_);
lean_dec(v_a_1134_);
if (v___x_1138_ == 0)
{
lean_object* v___x_1139_; lean_object* v___x_1141_; 
lean_dec_ref(v_arg_1108_);
lean_dec_ref(v_arg_1105_);
lean_dec_ref(v_e_1085_);
v___x_1139_ = lean_box(0);
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 0, v___x_1139_);
v___x_1141_ = v___x_1136_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1139_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
else
{
lean_object* v___x_1143_; 
lean_del_object(v___x_1136_);
lean_inc_ref(v_e_1085_);
v___x_1143_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_a_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
lean_inc(v_a_1144_);
lean_dec_ref_known(v___x_1143_, 1);
v___x_1145_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3);
v___x_1146_ = l_Lean_Meta_mkOfEqFalseCore(v_e_1085_, v_a_1144_);
v___x_1147_ = l_Lean_mkApp3(v___x_1145_, v_arg_1108_, v_arg_1105_, v___x_1146_);
v___x_1148_ = lean_unsigned_to_nat(0u);
v___x_1149_ = l_Lean_Meta_Grind_pushNewFact(v___x_1147_, v___x_1148_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
return v___x_1149_;
}
else
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1157_; 
lean_dec_ref(v_arg_1108_);
lean_dec_ref(v_arg_1105_);
lean_dec_ref(v_e_1085_);
v_a_1150_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1152_ = v___x_1143_;
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1143_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1157_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v___x_1155_; 
if (v_isShared_1153_ == 0)
{
v___x_1155_ = v___x_1152_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
}
}
else
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
lean_dec_ref(v_arg_1108_);
lean_dec_ref(v_arg_1105_);
lean_dec_ref(v_e_1085_);
v_a_1159_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1161_ = v___x_1133_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1133_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
if (v_isShared_1162_ == 0)
{
v___x_1164_ = v___x_1161_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1159_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
}
else
{
lean_object* v___x_1167_; 
lean_inc_ref(v_arg_1108_);
v___x_1167_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_1108_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
if (lean_obj_tag(v___x_1167_) == 0)
{
lean_object* v_a_1168_; lean_object* v_fst_1169_; lean_object* v_snd_1170_; lean_object* v___x_1171_; 
v_a_1168_ = lean_ctor_get(v___x_1167_, 0);
lean_inc(v_a_1168_);
lean_dec_ref_known(v___x_1167_, 1);
v_fst_1169_ = lean_ctor_get(v_a_1168_, 0);
lean_inc(v_fst_1169_);
v_snd_1170_ = lean_ctor_get(v_a_1168_, 1);
lean_inc(v_snd_1170_);
lean_dec(v_a_1168_);
lean_inc_ref(v_arg_1105_);
v___x_1171_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_1105_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
if (lean_obj_tag(v___x_1171_) == 0)
{
lean_object* v_a_1172_; lean_object* v_fst_1173_; lean_object* v_snd_1174_; lean_object* v___x_1175_; 
v_a_1172_ = lean_ctor_get(v___x_1171_, 0);
lean_inc(v_a_1172_);
lean_dec_ref_known(v___x_1171_, 1);
v_fst_1173_ = lean_ctor_get(v_a_1172_, 0);
lean_inc(v_fst_1173_);
v_snd_1174_ = lean_ctor_get(v_a_1172_, 1);
lean_inc(v_snd_1174_);
lean_dec(v_a_1172_);
v___x_1175_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1085_, v_a_1086_);
if (lean_obj_tag(v___x_1175_) == 0)
{
lean_object* v_a_1176_; lean_object* v___x_1177_; 
v_a_1176_ = lean_ctor_get(v___x_1175_, 0);
lean_inc(v_a_1176_);
lean_dec_ref_known(v___x_1175_, 1);
lean_inc(v_fst_1173_);
v___x_1177_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_1173_, v_a_1176_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
if (lean_obj_tag(v___x_1177_) == 0)
{
lean_object* v_a_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v_a_1178_ = lean_ctor_get(v___x_1177_, 0);
lean_inc(v_a_1178_);
lean_dec_ref_known(v___x_1177_, 1);
v___x_1179_ = l_Int_Internal_Linear_Expr_norm(v_a_1178_);
v___x_1180_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7);
v___x_1181_ = l_Lean_mkApp6(v___x_1180_, v_arg_1108_, v_arg_1105_, v_fst_1169_, v_fst_1173_, v_snd_1170_, v_snd_1174_);
lean_inc(v_val_1129_);
v___x_1182_ = lean_nat_to_int(v_val_1129_);
v___x_1183_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1183_, 0, v_e_1085_);
lean_ctor_set(v___x_1183_, 1, v___x_1181_);
lean_ctor_set(v___x_1183_, 2, v_val_1129_);
lean_ctor_set(v___x_1183_, 3, v_a_1178_);
v___x_1184_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1182_);
lean_ctor_set(v___x_1184_, 1, v___x_1179_);
lean_ctor_set(v___x_1184_, 2, v___x_1183_);
v___x_1185_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v___x_1184_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
return v___x_1185_;
}
else
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1193_; 
lean_dec(v_snd_1174_);
lean_dec(v_fst_1173_);
lean_dec(v_snd_1170_);
lean_dec(v_fst_1169_);
lean_dec(v_val_1129_);
lean_dec_ref(v_arg_1108_);
lean_dec_ref(v_arg_1105_);
lean_dec_ref(v_e_1085_);
v_a_1186_ = lean_ctor_get(v___x_1177_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1177_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1188_ = v___x_1177_;
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1177_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v___x_1191_; 
if (v_isShared_1189_ == 0)
{
v___x_1191_ = v___x_1188_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_a_1186_);
v___x_1191_ = v_reuseFailAlloc_1192_;
goto v_reusejp_1190_;
}
v_reusejp_1190_:
{
return v___x_1191_;
}
}
}
}
else
{
lean_object* v_a_1194_; lean_object* v___x_1196_; uint8_t v_isShared_1197_; uint8_t v_isSharedCheck_1201_; 
lean_dec(v_snd_1174_);
lean_dec(v_fst_1173_);
lean_dec(v_snd_1170_);
lean_dec(v_fst_1169_);
lean_dec(v_val_1129_);
lean_dec_ref(v_arg_1108_);
lean_dec_ref(v_arg_1105_);
lean_dec_ref(v_e_1085_);
v_a_1194_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1196_ = v___x_1175_;
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1175_);
v___x_1196_ = lean_box(0);
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
v_resetjp_1195_:
{
lean_object* v___x_1199_; 
if (v_isShared_1197_ == 0)
{
v___x_1199_ = v___x_1196_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_a_1194_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
}
else
{
lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1209_; 
lean_dec(v_snd_1170_);
lean_dec(v_fst_1169_);
lean_dec(v_val_1129_);
lean_dec_ref(v_arg_1108_);
lean_dec_ref(v_arg_1105_);
lean_dec_ref(v_e_1085_);
v_a_1202_ = lean_ctor_get(v___x_1171_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1171_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1204_ = v___x_1171_;
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v___x_1171_);
v___x_1204_ = lean_box(0);
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
v_resetjp_1203_:
{
lean_object* v___x_1207_; 
if (v_isShared_1205_ == 0)
{
v___x_1207_ = v___x_1204_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_a_1202_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
}
else
{
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1217_; 
lean_dec(v_val_1129_);
lean_dec_ref(v_arg_1108_);
lean_dec_ref(v_arg_1105_);
lean_dec_ref(v_e_1085_);
v_a_1210_ = lean_ctor_get(v___x_1167_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1212_ = v___x_1167_;
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1167_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1215_; 
if (v_isShared_1213_ == 0)
{
v___x_1215_ = v___x_1212_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_a_1210_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
}
else
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1225_; 
lean_dec(v_val_1129_);
lean_dec_ref(v_arg_1108_);
lean_dec_ref(v_arg_1105_);
lean_dec_ref(v_e_1085_);
v_a_1218_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1220_ = v___x_1130_;
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1130_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1223_; 
if (v_isShared_1221_ == 0)
{
v___x_1223_ = v___x_1220_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1218_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
else
{
lean_object* v___x_1226_; 
lean_dec(v_a_1128_);
lean_dec_ref(v_arg_1108_);
lean_dec_ref(v_arg_1105_);
v___x_1226_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1090_);
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
lean_dec_ref(v_e_1085_);
goto v___jp_1100_;
}
else
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1229_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10);
v___x_1230_ = l_Lean_indentExpr(v_e_1085_);
v___x_1231_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1229_);
lean_ctor_set(v___x_1231_, 1, v___x_1230_);
v___x_1232_ = l_Lean_Meta_Sym_reportIssue(v___x_1231_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_);
if (lean_obj_tag(v___x_1232_) == 0)
{
lean_dec_ref_known(v___x_1232_, 1);
goto v___jp_1100_;
}
else
{
return v___x_1232_;
}
}
}
else
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
lean_dec_ref(v_e_1085_);
v_a_1233_ = lean_ctor_get(v___x_1226_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1226_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1235_ = v___x_1226_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1226_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
if (v_isShared_1236_ == 0)
{
v___x_1238_ = v___x_1235_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_a_1233_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
}
}
else
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1248_; 
lean_dec_ref(v_arg_1108_);
lean_dec_ref(v_arg_1105_);
lean_dec_ref(v_e_1085_);
v_a_1241_ = lean_ctor_get(v___x_1127_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1127_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1243_ = v___x_1127_;
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1127_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1246_; 
if (v_isShared_1244_ == 0)
{
v___x_1246_ = v___x_1243_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_a_1241_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
}
}
}
else
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
lean_dec_ref(v_arg_1108_);
lean_dec_ref(v_arg_1105_);
lean_dec_ref(v_e_1085_);
v_a_1250_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1252_ = v___x_1117_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1117_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
if (v_isShared_1253_ == 0)
{
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1250_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
}
}
}
}
}
v___jp_1097_:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1098_ = lean_box(0);
v___x_1099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1098_);
return v___x_1099_;
}
v___jp_1100_:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = lean_box(0);
v___x_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
return v___x_1102_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___boxed(lean_object* v_e_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_){
_start:
{
lean_object* v_res_1270_; 
v_res_1270_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(v_e_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
lean_dec(v_a_1268_);
lean_dec_ref(v_a_1267_);
lean_dec(v_a_1266_);
lean_dec_ref(v_a_1265_);
lean_dec(v_a_1264_);
lean_dec_ref(v_a_1263_);
lean_dec(v_a_1262_);
lean_dec_ref(v_a_1261_);
lean_dec(v_a_1260_);
lean_dec(v_a_1259_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(lean_object* v_e_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_){
_start:
{
lean_object* v___x_1285_; 
v___x_1285_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1276_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1330_; 
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1288_ = v___x_1285_;
v_isShared_1289_ = v_isSharedCheck_1330_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1285_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1330_;
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
lean_dec_ref(v_e_1273_);
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
lean_inc_ref(v_e_1273_);
v___x_1295_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1273_, v_a_1281_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1321_; 
v_a_1296_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1321_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1298_ = v___x_1295_;
v_isShared_1299_ = v_isSharedCheck_1321_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1295_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1321_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1305_; uint8_t v___x_1306_; 
v___x_1305_ = l_Lean_Expr_cleanupAnnotations(v_a_1296_);
v___x_1306_ = l_Lean_Expr_isApp(v___x_1305_);
if (v___x_1306_ == 0)
{
lean_dec_ref(v___x_1305_);
lean_dec_ref(v_e_1273_);
goto v___jp_1300_;
}
else
{
lean_object* v___x_1307_; uint8_t v___x_1308_; 
v___x_1307_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1305_);
v___x_1308_ = l_Lean_Expr_isApp(v___x_1307_);
if (v___x_1308_ == 0)
{
lean_dec_ref(v___x_1307_);
lean_dec_ref(v_e_1273_);
goto v___jp_1300_;
}
else
{
lean_object* v___x_1309_; uint8_t v___x_1310_; 
v___x_1309_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1307_);
v___x_1310_ = l_Lean_Expr_isApp(v___x_1309_);
if (v___x_1310_ == 0)
{
lean_dec_ref(v___x_1309_);
lean_dec_ref(v_e_1273_);
goto v___jp_1300_;
}
else
{
lean_object* v___x_1311_; uint8_t v___x_1312_; 
v___x_1311_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1309_);
v___x_1312_ = l_Lean_Expr_isApp(v___x_1311_);
if (v___x_1312_ == 0)
{
lean_dec_ref(v___x_1311_);
lean_dec_ref(v_e_1273_);
goto v___jp_1300_;
}
else
{
lean_object* v_arg_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; uint8_t v___x_1316_; 
v_arg_1313_ = lean_ctor_get(v___x_1311_, 1);
lean_inc_ref(v_arg_1313_);
v___x_1314_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1311_);
v___x_1315_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1316_ = l_Lean_Expr_isConstOf(v___x_1314_, v___x_1315_);
lean_dec_ref(v___x_1314_);
if (v___x_1316_ == 0)
{
lean_dec_ref(v_arg_1313_);
lean_dec_ref(v_e_1273_);
goto v___jp_1300_;
}
else
{
lean_object* v___x_1317_; uint8_t v___x_1318_; 
lean_del_object(v___x_1298_);
v___x_1317_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0));
v___x_1318_ = l_Lean_Expr_isConstOf(v_arg_1313_, v___x_1317_);
lean_dec_ref(v_arg_1313_);
if (v___x_1318_ == 0)
{
lean_object* v___x_1319_; 
v___x_1319_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(v_e_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_);
return v___x_1319_;
}
else
{
lean_object* v___x_1320_; 
v___x_1320_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(v_e_1273_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_);
return v___x_1320_;
}
}
}
}
}
}
v___jp_1300_:
{
lean_object* v___x_1301_; lean_object* v___x_1303_; 
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
}
}
else
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1329_; 
lean_dec_ref(v_e_1273_);
v_a_1322_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1324_ = v___x_1295_;
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v___x_1295_);
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
}
}
}
else
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1338_; 
lean_dec_ref(v_e_1273_);
v_a_1331_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1333_ = v___x_1285_;
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1285_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1336_; 
if (v_isShared_1334_ == 0)
{
v___x_1336_ = v___x_1333_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_a_1331_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed(lean_object* v_e_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_, lean_object* v_a_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(v_e_1339_, v_a_1340_, v_a_1341_, v_a_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_);
lean_dec(v_a_1349_);
lean_dec_ref(v_a_1348_);
lean_dec(v_a_1347_);
lean_dec_ref(v_a_1346_);
lean_dec(v_a_1345_);
lean_dec_ref(v_a_1344_);
lean_dec(v_a_1343_);
lean_dec_ref(v_a_1342_);
lean_dec(v_a_1341_);
lean_dec(v_a_1340_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; 
v___x_1353_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1354_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed), 12, 0);
v___x_1355_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_1353_, v___x_1354_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_9____boxed(lean_object* v_a_1356_){
_start:
{
lean_object* v_res_1357_; 
v_res_1357_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_9_();
return v_res_1357_;
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
