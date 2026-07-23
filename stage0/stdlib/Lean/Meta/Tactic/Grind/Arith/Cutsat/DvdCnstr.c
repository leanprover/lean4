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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_8____boxed(lean_object*);
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
lean_dec(v___y_10_);
lean_dec_ref(v___y_9_);
lean_dec(v___y_8_);
return v___y_7_;
}
else
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_12_ = lean_int_ediv(v___y_8_, v___y_10_);
lean_dec(v___y_8_);
v___x_13_ = l_Int_Internal_Linear_Poly_div(v___y_10_, v___y_9_);
lean_dec(v___y_10_);
v___x_14_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_14_, 0, v___y_7_);
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
v___x_24_ = lean_int_dec_eq(v___x_23_, v___y_17_);
lean_dec(v___x_23_);
if (v___x_24_ == 0)
{
v___y_7_ = v___y_18_;
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
v___y_7_ = v___y_18_;
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
lean_dec(v___y_19_);
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
v___y_17_ = v___x_32_;
v___y_18_ = v___y_28_;
v___y_19_ = v_d_29_;
v___y_20_ = v_p_30_;
v___y_21_ = v_g_31_;
goto v___jp_16_;
}
else
{
lean_object* v___x_34_; 
v___x_34_ = lean_int_neg(v_g_31_);
lean_dec(v_g_31_);
v___y_17_ = v___x_32_;
v___y_18_ = v___y_28_;
v___y_19_ = v_d_29_;
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
v___x_112_ = lean_st_ref_set(v___y_73_, v___x_111_);
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
lean_object* v_vars_402_; lean_object* v_varMap_403_; lean_object* v_vars_x27_404_; lean_object* v_varMap_x27_405_; lean_object* v_natToIntMap_406_; lean_object* v_natDef_407_; lean_object* v_dvds_408_; lean_object* v_lowers_409_; lean_object* v_uppers_410_; lean_object* v_diseqs_411_; lean_object* v_elimEqs_412_; lean_object* v_elimStack_413_; lean_object* v_occurs_414_; lean_object* v_assignment_415_; lean_object* v_nextCnstrId_416_; uint8_t v_caseSplits_417_; lean_object* v_steps_418_; lean_object* v_conflict_x3f_419_; lean_object* v_diseqSplits_420_; lean_object* v_divMod_421_; lean_object* v_toIntIds_422_; lean_object* v_toIntInfos_423_; lean_object* v_toIntTermMap_424_; lean_object* v_toIntVarMap_425_; uint8_t v_usedCommRing_426_; lean_object* v_nonlinearOccs_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_436_; 
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
v_caseSplits_417_ = lean_ctor_get_uint8(v_s_401_, sizeof(void*)*24);
v_steps_418_ = lean_ctor_get(v_s_401_, 15);
v_conflict_x3f_419_ = lean_ctor_get(v_s_401_, 16);
v_diseqSplits_420_ = lean_ctor_get(v_s_401_, 17);
v_divMod_421_ = lean_ctor_get(v_s_401_, 18);
v_toIntIds_422_ = lean_ctor_get(v_s_401_, 19);
v_toIntInfos_423_ = lean_ctor_get(v_s_401_, 20);
v_toIntTermMap_424_ = lean_ctor_get(v_s_401_, 21);
v_toIntVarMap_425_ = lean_ctor_get(v_s_401_, 22);
v_usedCommRing_426_ = lean_ctor_get_uint8(v_s_401_, sizeof(void*)*24 + 1);
v_nonlinearOccs_427_ = lean_ctor_get(v_s_401_, 23);
v_isSharedCheck_436_ = !lean_is_exclusive(v_s_401_);
if (v_isSharedCheck_436_ == 0)
{
v___x_429_ = v_s_401_;
v_isShared_430_ = v_isSharedCheck_436_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_nonlinearOccs_427_);
lean_inc(v_toIntVarMap_425_);
lean_inc(v_toIntTermMap_424_);
lean_inc(v_toIntInfos_423_);
lean_inc(v_toIntIds_422_);
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
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_436_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_434_; 
v___x_431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_431_, 0, v_a_399_);
v___x_432_ = l_Lean_PersistentArray_set___redArg(v_dvds_408_, v_v_400_, v___x_431_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 6, v___x_432_);
v___x_434_ = v___x_429_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 24, 2);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_vars_402_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v_varMap_403_);
lean_ctor_set(v_reuseFailAlloc_435_, 2, v_vars_x27_404_);
lean_ctor_set(v_reuseFailAlloc_435_, 3, v_varMap_x27_405_);
lean_ctor_set(v_reuseFailAlloc_435_, 4, v_natToIntMap_406_);
lean_ctor_set(v_reuseFailAlloc_435_, 5, v_natDef_407_);
lean_ctor_set(v_reuseFailAlloc_435_, 6, v___x_432_);
lean_ctor_set(v_reuseFailAlloc_435_, 7, v_lowers_409_);
lean_ctor_set(v_reuseFailAlloc_435_, 8, v_uppers_410_);
lean_ctor_set(v_reuseFailAlloc_435_, 9, v_diseqs_411_);
lean_ctor_set(v_reuseFailAlloc_435_, 10, v_elimEqs_412_);
lean_ctor_set(v_reuseFailAlloc_435_, 11, v_elimStack_413_);
lean_ctor_set(v_reuseFailAlloc_435_, 12, v_occurs_414_);
lean_ctor_set(v_reuseFailAlloc_435_, 13, v_assignment_415_);
lean_ctor_set(v_reuseFailAlloc_435_, 14, v_nextCnstrId_416_);
lean_ctor_set(v_reuseFailAlloc_435_, 15, v_steps_418_);
lean_ctor_set(v_reuseFailAlloc_435_, 16, v_conflict_x3f_419_);
lean_ctor_set(v_reuseFailAlloc_435_, 17, v_diseqSplits_420_);
lean_ctor_set(v_reuseFailAlloc_435_, 18, v_divMod_421_);
lean_ctor_set(v_reuseFailAlloc_435_, 19, v_toIntIds_422_);
lean_ctor_set(v_reuseFailAlloc_435_, 20, v_toIntInfos_423_);
lean_ctor_set(v_reuseFailAlloc_435_, 21, v_toIntTermMap_424_);
lean_ctor_set(v_reuseFailAlloc_435_, 22, v_toIntVarMap_425_);
lean_ctor_set(v_reuseFailAlloc_435_, 23, v_nonlinearOccs_427_);
lean_ctor_set_uint8(v_reuseFailAlloc_435_, sizeof(void*)*24, v_caseSplits_417_);
lean_ctor_set_uint8(v_reuseFailAlloc_435_, sizeof(void*)*24 + 1, v_usedCommRing_426_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed(lean_object* v_a_437_, lean_object* v_v_438_, lean_object* v_s_439_){
_start:
{
lean_object* v_res_440_; 
v_res_440_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(v_a_437_, v_v_438_, v_s_439_);
lean_dec(v_v_438_);
return v_res_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(lean_object* v_v_441_, lean_object* v_s_442_){
_start:
{
lean_object* v_vars_443_; lean_object* v_varMap_444_; lean_object* v_vars_x27_445_; lean_object* v_varMap_x27_446_; lean_object* v_natToIntMap_447_; lean_object* v_natDef_448_; lean_object* v_dvds_449_; lean_object* v_lowers_450_; lean_object* v_uppers_451_; lean_object* v_diseqs_452_; lean_object* v_elimEqs_453_; lean_object* v_elimStack_454_; lean_object* v_occurs_455_; lean_object* v_assignment_456_; lean_object* v_nextCnstrId_457_; uint8_t v_caseSplits_458_; lean_object* v_steps_459_; lean_object* v_conflict_x3f_460_; lean_object* v_diseqSplits_461_; lean_object* v_divMod_462_; lean_object* v_toIntIds_463_; lean_object* v_toIntInfos_464_; lean_object* v_toIntTermMap_465_; lean_object* v_toIntVarMap_466_; uint8_t v_usedCommRing_467_; lean_object* v_nonlinearOccs_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_477_; 
v_vars_443_ = lean_ctor_get(v_s_442_, 0);
v_varMap_444_ = lean_ctor_get(v_s_442_, 1);
v_vars_x27_445_ = lean_ctor_get(v_s_442_, 2);
v_varMap_x27_446_ = lean_ctor_get(v_s_442_, 3);
v_natToIntMap_447_ = lean_ctor_get(v_s_442_, 4);
v_natDef_448_ = lean_ctor_get(v_s_442_, 5);
v_dvds_449_ = lean_ctor_get(v_s_442_, 6);
v_lowers_450_ = lean_ctor_get(v_s_442_, 7);
v_uppers_451_ = lean_ctor_get(v_s_442_, 8);
v_diseqs_452_ = lean_ctor_get(v_s_442_, 9);
v_elimEqs_453_ = lean_ctor_get(v_s_442_, 10);
v_elimStack_454_ = lean_ctor_get(v_s_442_, 11);
v_occurs_455_ = lean_ctor_get(v_s_442_, 12);
v_assignment_456_ = lean_ctor_get(v_s_442_, 13);
v_nextCnstrId_457_ = lean_ctor_get(v_s_442_, 14);
v_caseSplits_458_ = lean_ctor_get_uint8(v_s_442_, sizeof(void*)*24);
v_steps_459_ = lean_ctor_get(v_s_442_, 15);
v_conflict_x3f_460_ = lean_ctor_get(v_s_442_, 16);
v_diseqSplits_461_ = lean_ctor_get(v_s_442_, 17);
v_divMod_462_ = lean_ctor_get(v_s_442_, 18);
v_toIntIds_463_ = lean_ctor_get(v_s_442_, 19);
v_toIntInfos_464_ = lean_ctor_get(v_s_442_, 20);
v_toIntTermMap_465_ = lean_ctor_get(v_s_442_, 21);
v_toIntVarMap_466_ = lean_ctor_get(v_s_442_, 22);
v_usedCommRing_467_ = lean_ctor_get_uint8(v_s_442_, sizeof(void*)*24 + 1);
v_nonlinearOccs_468_ = lean_ctor_get(v_s_442_, 23);
v_isSharedCheck_477_ = !lean_is_exclusive(v_s_442_);
if (v_isSharedCheck_477_ == 0)
{
v___x_470_ = v_s_442_;
v_isShared_471_ = v_isSharedCheck_477_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_nonlinearOccs_468_);
lean_inc(v_toIntVarMap_466_);
lean_inc(v_toIntTermMap_465_);
lean_inc(v_toIntInfos_464_);
lean_inc(v_toIntIds_463_);
lean_inc(v_divMod_462_);
lean_inc(v_diseqSplits_461_);
lean_inc(v_conflict_x3f_460_);
lean_inc(v_steps_459_);
lean_inc(v_nextCnstrId_457_);
lean_inc(v_assignment_456_);
lean_inc(v_occurs_455_);
lean_inc(v_elimStack_454_);
lean_inc(v_elimEqs_453_);
lean_inc(v_diseqs_452_);
lean_inc(v_uppers_451_);
lean_inc(v_lowers_450_);
lean_inc(v_dvds_449_);
lean_inc(v_natDef_448_);
lean_inc(v_natToIntMap_447_);
lean_inc(v_varMap_x27_446_);
lean_inc(v_vars_x27_445_);
lean_inc(v_varMap_444_);
lean_inc(v_vars_443_);
lean_dec(v_s_442_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_477_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_475_; 
v___x_472_ = lean_box(0);
v___x_473_ = l_Lean_PersistentArray_set___redArg(v_dvds_449_, v_v_441_, v___x_472_);
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 6, v___x_473_);
v___x_475_ = v___x_470_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 24, 2);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_vars_443_);
lean_ctor_set(v_reuseFailAlloc_476_, 1, v_varMap_444_);
lean_ctor_set(v_reuseFailAlloc_476_, 2, v_vars_x27_445_);
lean_ctor_set(v_reuseFailAlloc_476_, 3, v_varMap_x27_446_);
lean_ctor_set(v_reuseFailAlloc_476_, 4, v_natToIntMap_447_);
lean_ctor_set(v_reuseFailAlloc_476_, 5, v_natDef_448_);
lean_ctor_set(v_reuseFailAlloc_476_, 6, v___x_473_);
lean_ctor_set(v_reuseFailAlloc_476_, 7, v_lowers_450_);
lean_ctor_set(v_reuseFailAlloc_476_, 8, v_uppers_451_);
lean_ctor_set(v_reuseFailAlloc_476_, 9, v_diseqs_452_);
lean_ctor_set(v_reuseFailAlloc_476_, 10, v_elimEqs_453_);
lean_ctor_set(v_reuseFailAlloc_476_, 11, v_elimStack_454_);
lean_ctor_set(v_reuseFailAlloc_476_, 12, v_occurs_455_);
lean_ctor_set(v_reuseFailAlloc_476_, 13, v_assignment_456_);
lean_ctor_set(v_reuseFailAlloc_476_, 14, v_nextCnstrId_457_);
lean_ctor_set(v_reuseFailAlloc_476_, 15, v_steps_459_);
lean_ctor_set(v_reuseFailAlloc_476_, 16, v_conflict_x3f_460_);
lean_ctor_set(v_reuseFailAlloc_476_, 17, v_diseqSplits_461_);
lean_ctor_set(v_reuseFailAlloc_476_, 18, v_divMod_462_);
lean_ctor_set(v_reuseFailAlloc_476_, 19, v_toIntIds_463_);
lean_ctor_set(v_reuseFailAlloc_476_, 20, v_toIntInfos_464_);
lean_ctor_set(v_reuseFailAlloc_476_, 21, v_toIntTermMap_465_);
lean_ctor_set(v_reuseFailAlloc_476_, 22, v_toIntVarMap_466_);
lean_ctor_set(v_reuseFailAlloc_476_, 23, v_nonlinearOccs_468_);
lean_ctor_set_uint8(v_reuseFailAlloc_476_, sizeof(void*)*24, v_caseSplits_458_);
lean_ctor_set_uint8(v_reuseFailAlloc_476_, sizeof(void*)*24 + 1, v_usedCommRing_467_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed(lean_object* v_v_478_, lean_object* v_s_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(v_v_478_, v_s_479_);
lean_dec(v_v_478_);
return v_res_480_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5(void){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_489_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4));
v___x_490_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
v___x_491_ = l_Lean_Name_append(v___x_490_, v___x_489_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(lean_object* v_c_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_){
_start:
{
lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___y_527_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v___y_536_; lean_object* v___y_537_; lean_object* v___y_538_; lean_object* v___y_539_; lean_object* v___y_540_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_669_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v_fileName_782_; lean_object* v_fileMap_783_; lean_object* v_options_784_; lean_object* v_currRecDepth_785_; lean_object* v_maxRecDepth_786_; lean_object* v_ref_787_; lean_object* v_currNamespace_788_; lean_object* v_openDecls_789_; lean_object* v_initHeartbeats_790_; lean_object* v_maxHeartbeats_791_; lean_object* v_quotContext_792_; lean_object* v_currMacroScope_793_; uint8_t v_diag_794_; lean_object* v_cancelTk_x3f_795_; uint8_t v_suppressElabErrors_796_; lean_object* v_inheritedTraceOptions_797_; lean_object* v___x_839_; uint8_t v___x_840_; 
v_fileName_782_ = lean_ctor_get(v_a_501_, 0);
lean_inc_ref(v_fileName_782_);
v_fileMap_783_ = lean_ctor_get(v_a_501_, 1);
lean_inc_ref(v_fileMap_783_);
v_options_784_ = lean_ctor_get(v_a_501_, 2);
lean_inc_ref(v_options_784_);
v_currRecDepth_785_ = lean_ctor_get(v_a_501_, 3);
lean_inc(v_currRecDepth_785_);
v_maxRecDepth_786_ = lean_ctor_get(v_a_501_, 4);
lean_inc(v_maxRecDepth_786_);
v_ref_787_ = lean_ctor_get(v_a_501_, 5);
lean_inc(v_ref_787_);
v_currNamespace_788_ = lean_ctor_get(v_a_501_, 6);
lean_inc(v_currNamespace_788_);
v_openDecls_789_ = lean_ctor_get(v_a_501_, 7);
lean_inc(v_openDecls_789_);
v_initHeartbeats_790_ = lean_ctor_get(v_a_501_, 8);
lean_inc(v_initHeartbeats_790_);
v_maxHeartbeats_791_ = lean_ctor_get(v_a_501_, 9);
lean_inc(v_maxHeartbeats_791_);
v_quotContext_792_ = lean_ctor_get(v_a_501_, 10);
lean_inc(v_quotContext_792_);
v_currMacroScope_793_ = lean_ctor_get(v_a_501_, 11);
lean_inc(v_currMacroScope_793_);
v_diag_794_ = lean_ctor_get_uint8(v_a_501_, sizeof(void*)*14);
v_cancelTk_x3f_795_ = lean_ctor_get(v_a_501_, 12);
lean_inc(v_cancelTk_x3f_795_);
v_suppressElabErrors_796_ = lean_ctor_get_uint8(v_a_501_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_797_ = lean_ctor_get(v_a_501_, 13);
lean_inc_ref(v_inheritedTraceOptions_797_);
lean_dec_ref(v_a_501_);
v___x_839_ = lean_unsigned_to_nat(0u);
v___x_840_ = lean_nat_dec_eq(v_maxRecDepth_786_, v___x_839_);
if (v___x_840_ == 0)
{
uint8_t v___x_841_; 
v___x_841_ = lean_nat_dec_eq(v_currRecDepth_785_, v_maxRecDepth_786_);
if (v___x_841_ == 0)
{
goto v___jp_798_;
}
else
{
lean_object* v___x_842_; 
lean_dec_ref(v_inheritedTraceOptions_797_);
lean_dec(v_cancelTk_x3f_795_);
lean_dec(v_currMacroScope_793_);
lean_dec(v_quotContext_792_);
lean_dec(v_maxHeartbeats_791_);
lean_dec(v_initHeartbeats_790_);
lean_dec(v_openDecls_789_);
lean_dec(v_currNamespace_788_);
lean_dec(v_maxRecDepth_786_);
lean_dec(v_currRecDepth_785_);
lean_dec_ref(v_options_784_);
lean_dec_ref(v_fileMap_783_);
lean_dec_ref(v_fileName_782_);
lean_dec_ref(v_c_492_);
v___x_842_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_787_);
return v___x_842_;
}
}
else
{
goto v___jp_798_;
}
v___jp_504_:
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = lean_box(0);
v___x_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_506_, 0, v___x_505_);
return v___x_506_;
}
v___jp_507_:
{
lean_object* v___x_515_; 
v___x_515_ = l_Int_Internal_Linear_Poly_updateOccs___redArg(v___y_508_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_);
lean_dec_ref(v___y_513_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v___x_516_; lean_object* v___x_517_; 
lean_dec_ref_known(v___x_515_, 1);
v___x_516_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_517_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_516_, v___y_509_, v___y_510_);
return v___x_517_;
}
else
{
lean_dec_ref(v___y_509_);
return v___x_515_;
}
}
v___jp_518_:
{
if (lean_obj_tag(v___y_540_) == 1)
{
lean_object* v_val_541_; lean_object* v_p_542_; 
lean_dec_ref(v___y_538_);
lean_dec_ref(v___y_536_);
v_val_541_ = lean_ctor_get(v___y_540_, 0);
lean_inc(v_val_541_);
lean_dec_ref_known(v___y_540_, 1);
v_p_542_ = lean_ctor_get(v_val_541_, 1);
lean_inc_ref(v_p_542_);
if (lean_obj_tag(v_p_542_) == 1)
{
lean_object* v_d_543_; lean_object* v_k_544_; lean_object* v_p_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_598_; 
v_d_543_ = lean_ctor_get(v_val_541_, 0);
v_k_544_ = lean_ctor_get(v_p_542_, 0);
v_p_545_ = lean_ctor_get(v_p_542_, 2);
v_isSharedCheck_598_ = !lean_is_exclusive(v_p_542_);
if (v_isSharedCheck_598_ == 0)
{
lean_object* v_unused_599_; 
v_unused_599_ = lean_ctor_get(v_p_542_, 1);
lean_dec(v_unused_599_);
v___x_547_ = v_p_542_;
v_isShared_548_ = v_isSharedCheck_598_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_p_545_);
lean_inc(v_k_544_);
lean_dec(v_p_542_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_598_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v_snd_552_; lean_object* v_fst_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_597_; 
v___x_549_ = lean_int_mul(v___y_521_, v_d_543_);
v___x_550_ = lean_int_mul(v_k_544_, v___y_526_);
v___x_551_ = l_Lean_Meta_Grind_Arith_gcdExt(v___x_549_, v___x_550_);
lean_dec(v___x_550_);
lean_dec(v___x_549_);
v_snd_552_ = lean_ctor_get(v___x_551_, 1);
v_fst_553_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_597_ == 0)
{
v___x_555_ = v___x_551_;
v_isShared_556_ = v_isSharedCheck_597_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_snd_552_);
lean_inc(v_fst_553_);
lean_dec(v___x_551_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_597_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v_fst_557_; lean_object* v_snd_558_; lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_596_; 
v_fst_557_ = lean_ctor_get(v_snd_552_, 0);
v_snd_558_ = lean_ctor_get(v_snd_552_, 1);
v_isSharedCheck_596_ = !lean_is_exclusive(v_snd_552_);
if (v_isSharedCheck_596_ == 0)
{
v___x_560_ = v_snd_552_;
v_isShared_561_ = v_isSharedCheck_596_;
goto v_resetjp_559_;
}
else
{
lean_inc(v_snd_558_);
lean_inc(v_fst_557_);
lean_dec(v_snd_552_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_596_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_563_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_562_, v___y_520_, v___y_527_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_571_; 
lean_dec_ref_known(v___x_563_, 1);
v___x_564_ = lean_int_mul(v_fst_557_, v_d_543_);
lean_dec(v_fst_557_);
lean_inc_ref(v___y_535_);
v___x_565_ = l_Int_Internal_Linear_Poly_mul(v___y_535_, v___x_564_);
lean_dec(v___x_564_);
v___x_566_ = lean_int_mul(v_snd_558_, v___y_526_);
lean_dec(v_snd_558_);
lean_inc_ref(v_p_545_);
v___x_567_ = l_Int_Internal_Linear_Poly_mul(v_p_545_, v___x_566_);
lean_dec(v___x_566_);
v___x_568_ = lean_int_mul(v___y_526_, v_d_543_);
lean_dec(v___y_526_);
v___x_569_ = l_Int_Internal_Linear_Poly_combine(v___x_565_, v___x_567_);
lean_inc(v_fst_553_);
if (v_isShared_548_ == 0)
{
lean_ctor_set(v___x_547_, 2, v___x_569_);
lean_ctor_set(v___x_547_, 1, v___y_522_);
lean_ctor_set(v___x_547_, 0, v_fst_553_);
v___x_571_ = v___x_547_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_fst_553_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v___y_522_);
lean_ctor_set(v_reuseFailAlloc_595_, 2, v___x_569_);
v___x_571_ = v_reuseFailAlloc_595_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
lean_object* v___x_573_; 
lean_inc(v_val_541_);
lean_inc_ref(v___y_523_);
if (v_isShared_561_ == 0)
{
lean_ctor_set_tag(v___x_560_, 4);
lean_ctor_set(v___x_560_, 1, v_val_541_);
lean_ctor_set(v___x_560_, 0, v___y_523_);
v___x_573_ = v___x_560_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___y_523_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_val_541_);
v___x_573_ = v_reuseFailAlloc_594_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_574_, 0, v___x_568_);
lean_ctor_set(v___x_574_, 1, v___x_571_);
lean_ctor_set(v___x_574_, 2, v___x_573_);
lean_inc_ref(v___y_530_);
v___x_575_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v___x_574_, v___y_527_, v___y_525_, v___y_533_, v___y_539_, v___y_519_, v___y_537_, v___y_534_, v___y_524_, v___y_530_, v___y_532_);
if (lean_obj_tag(v___x_575_) == 0)
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_581_; 
lean_dec_ref_known(v___x_575_, 1);
v___x_576_ = l_Int_Internal_Linear_Poly_mul(v___y_535_, v_k_544_);
lean_dec(v_k_544_);
v___x_577_ = lean_int_neg(v___y_521_);
lean_dec(v___y_521_);
v___x_578_ = l_Int_Internal_Linear_Poly_mul(v_p_545_, v___x_577_);
lean_dec(v___x_577_);
v___x_579_ = l_Int_Internal_Linear_Poly_combine(v___x_576_, v___x_578_);
lean_inc(v_val_541_);
if (v_isShared_556_ == 0)
{
lean_ctor_set_tag(v___x_555_, 5);
lean_ctor_set(v___x_555_, 1, v_val_541_);
lean_ctor_set(v___x_555_, 0, v___y_523_);
v___x_581_ = v___x_555_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v___y_523_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v_val_541_);
v___x_581_ = v_reuseFailAlloc_593_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_589_; 
v_isSharedCheck_589_ = !lean_is_exclusive(v_val_541_);
if (v_isSharedCheck_589_ == 0)
{
lean_object* v_unused_590_; lean_object* v_unused_591_; lean_object* v_unused_592_; 
v_unused_590_ = lean_ctor_get(v_val_541_, 2);
lean_dec(v_unused_590_);
v_unused_591_ = lean_ctor_get(v_val_541_, 1);
lean_dec(v_unused_591_);
v_unused_592_ = lean_ctor_get(v_val_541_, 0);
lean_dec(v_unused_592_);
v___x_583_ = v_val_541_;
v_isShared_584_ = v_isSharedCheck_589_;
goto v_resetjp_582_;
}
else
{
lean_dec(v_val_541_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_589_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 2, v___x_581_);
lean_ctor_set(v___x_583_, 1, v___x_579_);
lean_ctor_set(v___x_583_, 0, v_fst_553_);
v___x_586_ = v___x_583_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_fst_553_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v___x_579_);
lean_ctor_set(v_reuseFailAlloc_588_, 2, v___x_581_);
v___x_586_ = v_reuseFailAlloc_588_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
v_c_492_ = v___x_586_;
v_a_493_ = v___y_527_;
v_a_494_ = v___y_525_;
v_a_495_ = v___y_533_;
v_a_496_ = v___y_539_;
v_a_497_ = v___y_519_;
v_a_498_ = v___y_537_;
v_a_499_ = v___y_534_;
v_a_500_ = v___y_524_;
v_a_501_ = v___y_530_;
v_a_502_ = v___y_532_;
goto _start;
}
}
}
}
else
{
lean_del_object(v___x_555_);
lean_dec(v_fst_553_);
lean_dec_ref(v_p_545_);
lean_dec(v_k_544_);
lean_dec(v_val_541_);
lean_dec_ref(v___y_535_);
lean_dec_ref(v___y_530_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_521_);
return v___x_575_;
}
}
}
}
else
{
lean_del_object(v___x_560_);
lean_dec(v_snd_558_);
lean_dec(v_fst_557_);
lean_del_object(v___x_555_);
lean_dec(v_fst_553_);
lean_del_object(v___x_547_);
lean_dec_ref(v_p_545_);
lean_dec(v_k_544_);
lean_dec(v_val_541_);
lean_dec_ref(v___y_535_);
lean_dec_ref(v___y_530_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_522_);
lean_dec(v___y_521_);
return v___x_563_;
}
}
}
}
}
else
{
lean_object* v___x_600_; 
lean_dec_ref(v_p_542_);
lean_dec_ref(v___y_535_);
lean_dec(v___y_526_);
lean_dec_ref(v___y_523_);
lean_dec(v___y_522_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
v___x_600_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_val_541_, v___y_527_, v___y_525_, v___y_533_, v___y_539_, v___y_519_, v___y_537_, v___y_534_, v___y_524_, v___y_530_, v___y_532_);
lean_dec_ref(v___y_530_);
return v___x_600_;
}
}
else
{
lean_object* v_options_601_; uint8_t v_hasTrace_602_; 
lean_dec(v___y_540_);
lean_dec_ref(v___y_535_);
lean_dec(v___y_526_);
lean_dec(v___y_522_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
v_options_601_ = lean_ctor_get(v___y_530_, 2);
v_hasTrace_602_ = lean_ctor_get_uint8(v_options_601_, sizeof(void*)*1);
if (v_hasTrace_602_ == 0)
{
lean_dec_ref(v___y_523_);
v___y_508_ = v___y_536_;
v___y_509_ = v___y_538_;
v___y_510_ = v___y_527_;
v___y_511_ = v___y_534_;
v___y_512_ = v___y_524_;
v___y_513_ = v___y_530_;
v___y_514_ = v___y_532_;
goto v___jp_507_;
}
else
{
lean_object* v_inheritedTraceOptions_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; uint8_t v___x_608_; 
v_inheritedTraceOptions_603_ = lean_ctor_get(v___y_530_, 13);
v___x_604_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0));
lean_inc_ref(v___y_528_);
lean_inc_ref(v___y_531_);
lean_inc_ref(v___y_529_);
v___x_605_ = l_Lean_Name_mkStr4(v___y_529_, v___y_531_, v___y_528_, v___x_604_);
v___x_606_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
lean_inc(v___x_605_);
v___x_607_ = l_Lean_Name_append(v___x_606_, v___x_605_);
v___x_608_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_603_, v_options_601_, v___x_607_);
lean_dec(v___x_607_);
if (v___x_608_ == 0)
{
lean_dec(v___x_605_);
lean_dec_ref(v___y_523_);
v___y_508_ = v___y_536_;
v___y_509_ = v___y_538_;
v___y_510_ = v___y_527_;
v___y_511_ = v___y_534_;
v___y_512_ = v___y_524_;
v___y_513_ = v___y_530_;
v___y_514_ = v___y_532_;
goto v___jp_507_;
}
else
{
lean_object* v___x_609_; 
v___x_609_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v___y_523_, v___y_527_, v___y_530_);
if (lean_obj_tag(v___x_609_) == 0)
{
lean_object* v_a_610_; lean_object* v___x_611_; 
v_a_610_ = lean_ctor_get(v___x_609_, 0);
lean_inc(v_a_610_);
lean_dec_ref_known(v___x_609_, 1);
v___x_611_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_605_, v_a_610_, v___y_534_, v___y_524_, v___y_530_, v___y_532_);
if (lean_obj_tag(v___x_611_) == 0)
{
lean_dec_ref_known(v___x_611_, 1);
v___y_508_ = v___y_536_;
v___y_509_ = v___y_538_;
v___y_510_ = v___y_527_;
v___y_511_ = v___y_534_;
v___y_512_ = v___y_524_;
v___y_513_ = v___y_530_;
v___y_514_ = v___y_532_;
goto v___jp_507_;
}
else
{
lean_dec_ref(v___y_538_);
lean_dec_ref(v___y_536_);
lean_dec_ref(v___y_530_);
return v___x_611_;
}
}
else
{
lean_object* v_a_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_619_; 
lean_dec(v___x_605_);
lean_dec_ref(v___y_538_);
lean_dec_ref(v___y_536_);
lean_dec_ref(v___y_530_);
v_a_612_ = lean_ctor_get(v___x_609_, 0);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_619_ == 0)
{
v___x_614_ = v___x_609_;
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_a_612_);
lean_dec(v___x_609_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_619_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_617_; 
if (v_isShared_615_ == 0)
{
v___x_617_ = v___x_614_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_a_612_);
v___x_617_ = v_reuseFailAlloc_618_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
return v___x_617_;
}
}
}
}
}
}
}
v___jp_620_:
{
lean_object* v___x_642_; 
v___x_642_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v___y_632_, v___y_640_);
if (lean_obj_tag(v___x_642_) == 0)
{
lean_object* v_a_643_; lean_object* v_dvds_644_; lean_object* v_size_645_; lean_object* v___x_646_; uint8_t v___x_647_; 
v_a_643_ = lean_ctor_get(v___x_642_, 0);
lean_inc(v_a_643_);
lean_dec_ref_known(v___x_642_, 1);
v_dvds_644_ = lean_ctor_get(v_a_643_, 6);
lean_inc_ref(v_dvds_644_);
lean_dec(v_a_643_);
v_size_645_ = lean_ctor_get(v_dvds_644_, 2);
v___x_646_ = lean_box(0);
v___x_647_ = lean_nat_dec_lt(v___y_625_, v_size_645_);
if (v___x_647_ == 0)
{
lean_object* v___x_648_; 
lean_dec_ref(v_dvds_644_);
v___x_648_ = l_outOfBounds___redArg(v___x_646_);
v___y_519_ = v___y_636_;
v___y_520_ = v___y_622_;
v___y_521_ = v___y_626_;
v___y_522_ = v___y_625_;
v___y_523_ = v___y_624_;
v___y_524_ = v___y_639_;
v___y_525_ = v___y_633_;
v___y_526_ = v___y_627_;
v___y_527_ = v___y_632_;
v___y_528_ = v___y_629_;
v___y_529_ = v___y_630_;
v___y_530_ = v___y_640_;
v___y_531_ = v___y_631_;
v___y_532_ = v___y_641_;
v___y_533_ = v___y_634_;
v___y_534_ = v___y_638_;
v___y_535_ = v___y_621_;
v___y_536_ = v___y_623_;
v___y_537_ = v___y_637_;
v___y_538_ = v___y_628_;
v___y_539_ = v___y_635_;
v___y_540_ = v___x_648_;
goto v___jp_518_;
}
else
{
lean_object* v___x_649_; 
v___x_649_ = l_Lean_PersistentArray_get_x21___redArg(v___x_646_, v_dvds_644_, v___y_625_);
lean_dec_ref(v_dvds_644_);
v___y_519_ = v___y_636_;
v___y_520_ = v___y_622_;
v___y_521_ = v___y_626_;
v___y_522_ = v___y_625_;
v___y_523_ = v___y_624_;
v___y_524_ = v___y_639_;
v___y_525_ = v___y_633_;
v___y_526_ = v___y_627_;
v___y_527_ = v___y_632_;
v___y_528_ = v___y_629_;
v___y_529_ = v___y_630_;
v___y_530_ = v___y_640_;
v___y_531_ = v___y_631_;
v___y_532_ = v___y_641_;
v___y_533_ = v___y_634_;
v___y_534_ = v___y_638_;
v___y_535_ = v___y_621_;
v___y_536_ = v___y_623_;
v___y_537_ = v___y_637_;
v___y_538_ = v___y_628_;
v___y_539_ = v___y_635_;
v___y_540_ = v___x_649_;
goto v___jp_518_;
}
}
else
{
lean_object* v_a_650_; lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_657_; 
lean_dec_ref(v___y_640_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
lean_dec(v___y_626_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec_ref(v___y_622_);
lean_dec_ref(v___y_621_);
v_a_650_ = lean_ctor_get(v___x_642_, 0);
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_642_);
if (v_isSharedCheck_657_ == 0)
{
v___x_652_ = v___x_642_;
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
else
{
lean_inc(v_a_650_);
lean_dec(v___x_642_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_657_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
lean_object* v___x_655_; 
if (v_isShared_653_ == 0)
{
v___x_655_ = v___x_652_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_a_650_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
}
v___jp_658_:
{
lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_670_, 0, v___y_659_);
v___x_671_ = l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(v___x_670_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
lean_dec_ref(v___y_668_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v___x_673_; uint8_t v_isShared_674_; uint8_t v_isSharedCheck_679_; 
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_679_ == 0)
{
lean_object* v_unused_680_; 
v_unused_680_ = lean_ctor_get(v___x_671_, 0);
lean_dec(v_unused_680_);
v___x_673_ = v___x_671_;
v_isShared_674_ = v_isSharedCheck_679_;
goto v_resetjp_672_;
}
else
{
lean_dec(v___x_671_);
v___x_673_ = lean_box(0);
v_isShared_674_ = v_isSharedCheck_679_;
goto v_resetjp_672_;
}
v_resetjp_672_:
{
lean_object* v___x_675_; lean_object* v___x_677_; 
v___x_675_ = lean_box(0);
if (v_isShared_674_ == 0)
{
lean_ctor_set(v___x_673_, 0, v___x_675_);
v___x_677_ = v___x_673_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_675_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
else
{
return v___x_671_;
}
}
v___jp_681_:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(v_c_492_);
lean_inc_ref(v___y_693_);
v___x_696_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(v___x_695_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_);
if (lean_obj_tag(v___x_696_) == 0)
{
lean_object* v_a_697_; lean_object* v_d_698_; lean_object* v_p_699_; uint8_t v___x_700_; 
v_a_697_ = lean_ctor_get(v___x_696_, 0);
lean_inc(v_a_697_);
lean_dec_ref_known(v___x_696_, 1);
v_d_698_ = lean_ctor_get(v_a_697_, 0);
v_p_699_ = lean_ctor_get(v_a_697_, 1);
lean_inc(v_d_698_);
v___x_700_ = l_Int_Internal_Linear_Poly_isUnsatDvd(v_d_698_, v_p_699_);
if (v___x_700_ == 0)
{
uint8_t v___x_701_; 
v___x_701_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(v_a_697_);
if (v___x_701_ == 0)
{
lean_object* v___x_702_; uint8_t v___x_703_; 
v___x_702_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1);
v___x_703_ = lean_int_dec_eq(v_d_698_, v___x_702_);
if (v___x_703_ == 0)
{
if (lean_obj_tag(v_p_699_) == 1)
{
lean_object* v_k_704_; lean_object* v_v_705_; lean_object* v_p_706_; lean_object* v___x_707_; 
lean_inc_ref(v_p_699_);
lean_inc(v_d_698_);
v_k_704_ = lean_ctor_get(v_p_699_, 0);
lean_inc(v_k_704_);
v_v_705_ = lean_ctor_get(v_p_699_, 1);
lean_inc(v_v_705_);
v_p_706_ = lean_ctor_get(v_p_699_, 2);
lean_inc_ref(v_p_706_);
lean_inc(v_a_697_);
v___x_707_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(v_a_697_, v___y_685_, v___y_693_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v_a_708_; lean_object* v___f_709_; lean_object* v___f_710_; uint8_t v___x_711_; uint8_t v___x_712_; uint8_t v___x_713_; 
v_a_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_a_708_);
lean_dec_ref_known(v___x_707_, 1);
lean_inc_n(v_v_705_, 2);
lean_inc(v_a_697_);
v___f_709_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed), 3, 2);
lean_closure_set(v___f_709_, 0, v_a_697_);
lean_closure_set(v___f_709_, 1, v_v_705_);
v___f_710_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed), 2, 1);
lean_closure_set(v___f_710_, 0, v_v_705_);
v___x_711_ = 0;
v___x_712_ = lean_unbox(v_a_708_);
lean_dec(v_a_708_);
v___x_713_ = l_Lean_instBEqLBool_beq(v___x_712_, v___x_711_);
if (v___x_713_ == 0)
{
v___y_621_ = v_p_706_;
v___y_622_ = v___f_710_;
v___y_623_ = v_p_699_;
v___y_624_ = v_a_697_;
v___y_625_ = v_v_705_;
v___y_626_ = v_k_704_;
v___y_627_ = v_d_698_;
v___y_628_ = v___f_709_;
v___y_629_ = v___y_682_;
v___y_630_ = v___y_683_;
v___y_631_ = v___y_684_;
v___y_632_ = v___y_685_;
v___y_633_ = v___y_686_;
v___y_634_ = v___y_687_;
v___y_635_ = v___y_688_;
v___y_636_ = v___y_689_;
v___y_637_ = v___y_690_;
v___y_638_ = v___y_691_;
v___y_639_ = v___y_692_;
v___y_640_ = v___y_693_;
v___y_641_ = v___y_694_;
goto v___jp_620_;
}
else
{
lean_object* v___x_714_; 
lean_inc(v_v_705_);
v___x_714_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v_v_705_, v___y_685_);
if (lean_obj_tag(v___x_714_) == 0)
{
lean_dec_ref_known(v___x_714_, 1);
v___y_621_ = v_p_706_;
v___y_622_ = v___f_710_;
v___y_623_ = v_p_699_;
v___y_624_ = v_a_697_;
v___y_625_ = v_v_705_;
v___y_626_ = v_k_704_;
v___y_627_ = v_d_698_;
v___y_628_ = v___f_709_;
v___y_629_ = v___y_682_;
v___y_630_ = v___y_683_;
v___y_631_ = v___y_684_;
v___y_632_ = v___y_685_;
v___y_633_ = v___y_686_;
v___y_634_ = v___y_687_;
v___y_635_ = v___y_688_;
v___y_636_ = v___y_689_;
v___y_637_ = v___y_690_;
v___y_638_ = v___y_691_;
v___y_639_ = v___y_692_;
v___y_640_ = v___y_693_;
v___y_641_ = v___y_694_;
goto v___jp_620_;
}
else
{
lean_dec_ref(v___f_710_);
lean_dec_ref(v___f_709_);
lean_dec_ref(v_p_706_);
lean_dec(v_v_705_);
lean_dec(v_k_704_);
lean_dec_ref_known(v_p_699_, 3);
lean_dec(v_d_698_);
lean_dec(v_a_697_);
lean_dec_ref(v___y_693_);
return v___x_714_;
}
}
}
else
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_722_; 
lean_dec_ref(v_p_706_);
lean_dec(v_v_705_);
lean_dec(v_k_704_);
lean_dec_ref_known(v_p_699_, 3);
lean_dec(v_d_698_);
lean_dec(v_a_697_);
lean_dec_ref(v___y_693_);
v_a_715_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_722_ == 0)
{
v___x_717_ = v___x_707_;
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_707_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_720_; 
if (v_isShared_718_ == 0)
{
v___x_720_ = v___x_717_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_a_715_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
}
else
{
lean_object* v___x_723_; 
v___x_723_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_a_697_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_);
lean_dec_ref(v___y_693_);
return v___x_723_;
}
}
else
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; 
lean_inc_ref(v_p_699_);
v___x_724_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_724_, 0, v_a_697_);
v___x_725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_725_, 0, v_p_699_);
lean_ctor_set(v___x_725_, 1, v___x_724_);
lean_inc(v___y_694_);
lean_inc(v___y_692_);
lean_inc_ref(v___y_691_);
lean_inc(v___y_690_);
lean_inc_ref(v___y_689_);
lean_inc(v___y_688_);
lean_inc_ref(v___y_687_);
lean_inc(v___y_686_);
lean_inc(v___y_685_);
v___x_726_ = lean_grind_cutsat_assert_eq(v___x_725_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_);
if (lean_obj_tag(v___x_726_) == 0)
{
lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_734_; 
v_isSharedCheck_734_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_734_ == 0)
{
lean_object* v_unused_735_; 
v_unused_735_ = lean_ctor_get(v___x_726_, 0);
lean_dec(v_unused_735_);
v___x_728_ = v___x_726_;
v_isShared_729_ = v_isSharedCheck_734_;
goto v_resetjp_727_;
}
else
{
lean_dec(v___x_726_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_734_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_730_; lean_object* v___x_732_; 
v___x_730_ = lean_box(0);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 0, v___x_730_);
v___x_732_ = v___x_728_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_730_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
else
{
return v___x_726_;
}
}
}
else
{
lean_object* v_options_736_; uint8_t v_hasTrace_737_; 
v_options_736_ = lean_ctor_get(v___y_693_, 2);
v_hasTrace_737_ = lean_ctor_get_uint8(v_options_736_, sizeof(void*)*1);
if (v_hasTrace_737_ == 0)
{
lean_dec(v_a_697_);
lean_dec_ref(v___y_693_);
goto v___jp_504_;
}
else
{
lean_object* v_inheritedTraceOptions_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; uint8_t v___x_743_; 
v_inheritedTraceOptions_738_ = lean_ctor_get(v___y_693_, 13);
v___x_739_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1));
lean_inc_ref(v___y_682_);
lean_inc_ref(v___y_684_);
lean_inc_ref(v___y_683_);
v___x_740_ = l_Lean_Name_mkStr4(v___y_683_, v___y_684_, v___y_682_, v___x_739_);
v___x_741_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
lean_inc(v___x_740_);
v___x_742_ = l_Lean_Name_append(v___x_741_, v___x_740_);
v___x_743_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_738_, v_options_736_, v___x_742_);
lean_dec(v___x_742_);
if (v___x_743_ == 0)
{
lean_dec(v___x_740_);
lean_dec(v_a_697_);
lean_dec_ref(v___y_693_);
goto v___jp_504_;
}
else
{
lean_object* v___x_744_; 
v___x_744_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_a_697_, v___y_685_, v___y_693_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; lean_object* v___x_746_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_a_745_);
lean_dec_ref_known(v___x_744_, 1);
v___x_746_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_740_, v_a_745_, v___y_691_, v___y_692_, v___y_693_, v___y_694_);
lean_dec_ref(v___y_693_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_dec_ref_known(v___x_746_, 1);
goto v___jp_504_;
}
else
{
return v___x_746_;
}
}
else
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
lean_dec(v___x_740_);
lean_dec_ref(v___y_693_);
v_a_747_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_754_ == 0)
{
v___x_749_ = v___x_744_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_744_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_752_; 
if (v_isShared_750_ == 0)
{
v___x_752_ = v___x_749_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_a_747_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
}
}
}
else
{
lean_object* v_options_755_; uint8_t v_hasTrace_756_; 
v_options_755_ = lean_ctor_get(v___y_693_, 2);
v_hasTrace_756_ = lean_ctor_get_uint8(v_options_755_, sizeof(void*)*1);
if (v_hasTrace_756_ == 0)
{
v___y_659_ = v_a_697_;
v___y_660_ = v___y_685_;
v___y_661_ = v___y_686_;
v___y_662_ = v___y_687_;
v___y_663_ = v___y_688_;
v___y_664_ = v___y_689_;
v___y_665_ = v___y_690_;
v___y_666_ = v___y_691_;
v___y_667_ = v___y_692_;
v___y_668_ = v___y_693_;
v___y_669_ = v___y_694_;
goto v___jp_658_;
}
else
{
lean_object* v_inheritedTraceOptions_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; uint8_t v___x_762_; 
v_inheritedTraceOptions_757_ = lean_ctor_get(v___y_693_, 13);
v___x_758_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2));
lean_inc_ref(v___y_682_);
lean_inc_ref(v___y_684_);
lean_inc_ref(v___y_683_);
v___x_759_ = l_Lean_Name_mkStr4(v___y_683_, v___y_684_, v___y_682_, v___x_758_);
v___x_760_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
lean_inc(v___x_759_);
v___x_761_ = l_Lean_Name_append(v___x_760_, v___x_759_);
v___x_762_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_757_, v_options_755_, v___x_761_);
lean_dec(v___x_761_);
if (v___x_762_ == 0)
{
lean_dec(v___x_759_);
v___y_659_ = v_a_697_;
v___y_660_ = v___y_685_;
v___y_661_ = v___y_686_;
v___y_662_ = v___y_687_;
v___y_663_ = v___y_688_;
v___y_664_ = v___y_689_;
v___y_665_ = v___y_690_;
v___y_666_ = v___y_691_;
v___y_667_ = v___y_692_;
v___y_668_ = v___y_693_;
v___y_669_ = v___y_694_;
goto v___jp_658_;
}
else
{
lean_object* v___x_763_; 
lean_inc(v_a_697_);
v___x_763_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_a_697_, v___y_685_, v___y_693_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_a_764_; lean_object* v___x_765_; 
v_a_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_a_764_);
lean_dec_ref_known(v___x_763_, 1);
v___x_765_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_759_, v_a_764_, v___y_691_, v___y_692_, v___y_693_, v___y_694_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_dec_ref_known(v___x_765_, 1);
v___y_659_ = v_a_697_;
v___y_660_ = v___y_685_;
v___y_661_ = v___y_686_;
v___y_662_ = v___y_687_;
v___y_663_ = v___y_688_;
v___y_664_ = v___y_689_;
v___y_665_ = v___y_690_;
v___y_666_ = v___y_691_;
v___y_667_ = v___y_692_;
v___y_668_ = v___y_693_;
v___y_669_ = v___y_694_;
goto v___jp_658_;
}
else
{
lean_dec(v_a_697_);
lean_dec_ref(v___y_693_);
return v___x_765_;
}
}
else
{
lean_object* v_a_766_; lean_object* v___x_768_; uint8_t v_isShared_769_; uint8_t v_isSharedCheck_773_; 
lean_dec(v___x_759_);
lean_dec(v_a_697_);
lean_dec_ref(v___y_693_);
v_a_766_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_773_ == 0)
{
v___x_768_ = v___x_763_;
v_isShared_769_ = v_isSharedCheck_773_;
goto v_resetjp_767_;
}
else
{
lean_inc(v_a_766_);
lean_dec(v___x_763_);
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
}
}
}
else
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_781_; 
lean_dec_ref(v___y_693_);
v_a_774_ = lean_ctor_get(v___x_696_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v___x_696_);
if (v_isSharedCheck_781_ == 0)
{
v___x_776_ = v___x_696_;
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_696_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_781_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v___x_779_; 
if (v_isShared_777_ == 0)
{
v___x_779_ = v___x_776_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v_a_774_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
v___jp_798_:
{
lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_799_ = lean_unsigned_to_nat(1u);
v___x_800_ = lean_nat_add(v_currRecDepth_785_, v___x_799_);
lean_dec(v_currRecDepth_785_);
lean_inc_ref(v_inheritedTraceOptions_797_);
lean_inc_ref(v_options_784_);
v___x_801_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_801_, 0, v_fileName_782_);
lean_ctor_set(v___x_801_, 1, v_fileMap_783_);
lean_ctor_set(v___x_801_, 2, v_options_784_);
lean_ctor_set(v___x_801_, 3, v___x_800_);
lean_ctor_set(v___x_801_, 4, v_maxRecDepth_786_);
lean_ctor_set(v___x_801_, 5, v_ref_787_);
lean_ctor_set(v___x_801_, 6, v_currNamespace_788_);
lean_ctor_set(v___x_801_, 7, v_openDecls_789_);
lean_ctor_set(v___x_801_, 8, v_initHeartbeats_790_);
lean_ctor_set(v___x_801_, 9, v_maxHeartbeats_791_);
lean_ctor_set(v___x_801_, 10, v_quotContext_792_);
lean_ctor_set(v___x_801_, 11, v_currMacroScope_793_);
lean_ctor_set(v___x_801_, 12, v_cancelTk_x3f_795_);
lean_ctor_set(v___x_801_, 13, v_inheritedTraceOptions_797_);
lean_ctor_set_uint8(v___x_801_, sizeof(void*)*14, v_diag_794_);
lean_ctor_set_uint8(v___x_801_, sizeof(void*)*14 + 1, v_suppressElabErrors_796_);
v___x_802_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_493_, v___x_801_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_830_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_830_ == 0)
{
v___x_805_ = v___x_802_;
v_isShared_806_ = v_isSharedCheck_830_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_a_803_);
lean_dec(v___x_802_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_830_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
uint8_t v___x_807_; 
v___x_807_ = lean_unbox(v_a_803_);
lean_dec(v_a_803_);
if (v___x_807_ == 0)
{
uint8_t v_hasTrace_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
lean_del_object(v___x_805_);
v_hasTrace_808_ = lean_ctor_get_uint8(v_options_784_, sizeof(void*)*1);
v___x_809_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0));
v___x_810_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2));
v___x_811_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3));
if (v_hasTrace_808_ == 0)
{
lean_dec_ref(v_inheritedTraceOptions_797_);
lean_dec_ref(v_options_784_);
v___y_682_ = v___x_811_;
v___y_683_ = v___x_809_;
v___y_684_ = v___x_810_;
v___y_685_ = v_a_493_;
v___y_686_ = v_a_494_;
v___y_687_ = v_a_495_;
v___y_688_ = v_a_496_;
v___y_689_ = v_a_497_;
v___y_690_ = v_a_498_;
v___y_691_ = v_a_499_;
v___y_692_ = v_a_500_;
v___y_693_ = v___x_801_;
v___y_694_ = v_a_502_;
goto v___jp_681_;
}
else
{
lean_object* v___x_812_; lean_object* v___x_813_; uint8_t v___x_814_; 
v___x_812_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4));
v___x_813_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5);
v___x_814_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_797_, v_options_784_, v___x_813_);
lean_dec_ref(v_options_784_);
lean_dec_ref(v_inheritedTraceOptions_797_);
if (v___x_814_ == 0)
{
v___y_682_ = v___x_811_;
v___y_683_ = v___x_809_;
v___y_684_ = v___x_810_;
v___y_685_ = v_a_493_;
v___y_686_ = v_a_494_;
v___y_687_ = v_a_495_;
v___y_688_ = v_a_496_;
v___y_689_ = v_a_497_;
v___y_690_ = v_a_498_;
v___y_691_ = v_a_499_;
v___y_692_ = v_a_500_;
v___y_693_ = v___x_801_;
v___y_694_ = v_a_502_;
goto v___jp_681_;
}
else
{
lean_object* v___x_815_; 
lean_inc_ref(v_c_492_);
v___x_815_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_492_, v_a_493_, v___x_801_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_object* v_a_816_; lean_object* v___x_817_; 
v_a_816_ = lean_ctor_get(v___x_815_, 0);
lean_inc(v_a_816_);
lean_dec_ref_known(v___x_815_, 1);
v___x_817_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_812_, v_a_816_, v_a_499_, v_a_500_, v___x_801_, v_a_502_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_dec_ref_known(v___x_817_, 1);
v___y_682_ = v___x_811_;
v___y_683_ = v___x_809_;
v___y_684_ = v___x_810_;
v___y_685_ = v_a_493_;
v___y_686_ = v_a_494_;
v___y_687_ = v_a_495_;
v___y_688_ = v_a_496_;
v___y_689_ = v_a_497_;
v___y_690_ = v_a_498_;
v___y_691_ = v_a_499_;
v___y_692_ = v_a_500_;
v___y_693_ = v___x_801_;
v___y_694_ = v_a_502_;
goto v___jp_681_;
}
else
{
lean_dec_ref_known(v___x_801_, 14);
lean_dec_ref(v_c_492_);
return v___x_817_;
}
}
else
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_825_; 
lean_dec_ref_known(v___x_801_, 14);
lean_dec_ref(v_c_492_);
v_a_818_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_825_ == 0)
{
v___x_820_ = v___x_815_;
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_815_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_823_; 
if (v_isShared_821_ == 0)
{
v___x_823_ = v___x_820_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_a_818_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
}
}
else
{
lean_object* v___x_826_; lean_object* v___x_828_; 
lean_dec_ref_known(v___x_801_, 14);
lean_dec_ref(v_inheritedTraceOptions_797_);
lean_dec_ref(v_options_784_);
lean_dec_ref(v_c_492_);
v___x_826_ = lean_box(0);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 0, v___x_826_);
v___x_828_ = v___x_805_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_826_);
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
else
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
lean_dec_ref_known(v___x_801_, 14);
lean_dec_ref(v_inheritedTraceOptions_797_);
lean_dec_ref(v_options_784_);
lean_dec_ref(v_c_492_);
v_a_831_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_802_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_802_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_a_831_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___boxed(lean_object* v_c_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v_c_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_);
lean_dec(v_a_853_);
lean_dec(v_a_851_);
lean_dec_ref(v_a_850_);
lean_dec(v_a_849_);
lean_dec_ref(v_a_848_);
lean_dec(v_a_847_);
lean_dec_ref(v_a_846_);
lean_dec(v_a_845_);
lean_dec(v_a_844_);
return v_res_855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(lean_object* v_c_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_){
_start:
{
lean_object* v_d_868_; lean_object* v_p_869_; lean_object* v___x_870_; 
v_d_868_ = lean_ctor_get(v_c_856_, 0);
v_p_869_ = lean_ctor_get(v_c_856_, 1);
lean_inc_ref(v_p_869_);
v___x_870_ = l_Int_Internal_Linear_Poly_normCommRing_x3f(v_p_869_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
lean_inc(v_a_871_);
lean_dec_ref_known(v___x_870_, 1);
if (lean_obj_tag(v_a_871_) == 1)
{
lean_object* v_val_872_; lean_object* v_snd_873_; lean_object* v_fst_874_; lean_object* v_fst_875_; lean_object* v_snd_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
lean_inc(v_d_868_);
v_val_872_ = lean_ctor_get(v_a_871_, 0);
lean_inc(v_val_872_);
lean_dec_ref_known(v_a_871_, 1);
v_snd_873_ = lean_ctor_get(v_val_872_, 1);
lean_inc(v_snd_873_);
v_fst_874_ = lean_ctor_get(v_val_872_, 0);
lean_inc(v_fst_874_);
lean_dec(v_val_872_);
v_fst_875_ = lean_ctor_get(v_snd_873_, 0);
lean_inc(v_fst_875_);
v_snd_876_ = lean_ctor_get(v_snd_873_, 1);
lean_inc(v_snd_876_);
lean_dec(v_snd_873_);
v___x_877_ = lean_alloc_ctor(12, 3, 0);
lean_ctor_set(v___x_877_, 0, v_c_856_);
lean_ctor_set(v___x_877_, 1, v_fst_874_);
lean_ctor_set(v___x_877_, 2, v_fst_875_);
v___x_878_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_878_, 0, v_d_868_);
lean_ctor_set(v___x_878_, 1, v_snd_876_);
lean_ctor_set(v___x_878_, 2, v___x_877_);
lean_inc_ref(v_a_865_);
v___x_879_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v___x_878_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_);
return v___x_879_;
}
else
{
lean_object* v___x_880_; 
lean_dec(v_a_871_);
lean_inc_ref(v_a_865_);
v___x_880_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v_c_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_, v_a_863_, v_a_864_, v_a_865_, v_a_866_);
return v___x_880_;
}
}
else
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
lean_dec_ref(v_c_856_);
v_a_881_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_888_ == 0)
{
v___x_883_ = v___x_870_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_870_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_881_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore___boxed(lean_object* v_c_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v_c_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_);
lean_dec(v_a_899_);
lean_dec_ref(v_a_898_);
lean_dec(v_a_897_);
lean_dec_ref(v_a_896_);
lean_dec(v_a_895_);
lean_dec_ref(v_a_894_);
lean_dec(v_a_893_);
lean_dec_ref(v_a_892_);
lean_dec(v_a_891_);
lean_dec(v_a_890_);
return v_res_901_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8(void){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_916_ = lean_box(0);
v___x_917_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7));
v___x_918_ = l_Lean_mkConst(v___x_917_, v___x_916_);
return v___x_918_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10(void){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9));
v___x_921_ = l_Lean_stringToMessageData(v___x_920_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(lean_object* v_e_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_){
_start:
{
lean_object* v___x_937_; 
lean_inc_ref(v_e_922_);
v___x_937_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_922_, v_a_930_);
if (lean_obj_tag(v___x_937_) == 0)
{
lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_1071_; 
v_a_938_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_1071_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_1071_ == 0)
{
v___x_940_ = v___x_937_;
v_isShared_941_ = v_isSharedCheck_1071_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_937_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_1071_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_947_; uint8_t v___x_948_; 
v___x_947_ = l_Lean_Expr_cleanupAnnotations(v_a_938_);
v___x_948_ = l_Lean_Expr_isApp(v___x_947_);
if (v___x_948_ == 0)
{
lean_dec_ref(v___x_947_);
lean_dec_ref(v_e_922_);
goto v___jp_942_;
}
else
{
lean_object* v_arg_949_; lean_object* v___x_950_; uint8_t v___x_951_; 
v_arg_949_ = lean_ctor_get(v___x_947_, 1);
lean_inc_ref(v_arg_949_);
v___x_950_ = l_Lean_Expr_appFnCleanup___redArg(v___x_947_);
v___x_951_ = l_Lean_Expr_isApp(v___x_950_);
if (v___x_951_ == 0)
{
lean_dec_ref(v___x_950_);
lean_dec_ref(v_arg_949_);
lean_dec_ref(v_e_922_);
goto v___jp_942_;
}
else
{
lean_object* v_arg_952_; lean_object* v___x_953_; uint8_t v___x_954_; 
v_arg_952_ = lean_ctor_get(v___x_950_, 1);
lean_inc_ref(v_arg_952_);
v___x_953_ = l_Lean_Expr_appFnCleanup___redArg(v___x_950_);
v___x_954_ = l_Lean_Expr_isApp(v___x_953_);
if (v___x_954_ == 0)
{
lean_dec_ref(v___x_953_);
lean_dec_ref(v_arg_952_);
lean_dec_ref(v_arg_949_);
lean_dec_ref(v_e_922_);
goto v___jp_942_;
}
else
{
lean_object* v_arg_955_; lean_object* v___x_956_; uint8_t v___x_957_; 
v_arg_955_ = lean_ctor_get(v___x_953_, 1);
lean_inc_ref(v_arg_955_);
v___x_956_ = l_Lean_Expr_appFnCleanup___redArg(v___x_953_);
v___x_957_ = l_Lean_Expr_isApp(v___x_956_);
if (v___x_957_ == 0)
{
lean_dec_ref(v___x_956_);
lean_dec_ref(v_arg_955_);
lean_dec_ref(v_arg_952_);
lean_dec_ref(v_arg_949_);
lean_dec_ref(v_e_922_);
goto v___jp_942_;
}
else
{
lean_object* v___x_958_; lean_object* v___x_959_; uint8_t v___x_960_; 
v___x_958_ = l_Lean_Expr_appFnCleanup___redArg(v___x_956_);
v___x_959_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_960_ = l_Lean_Expr_isConstOf(v___x_958_, v___x_959_);
lean_dec_ref(v___x_958_);
if (v___x_960_ == 0)
{
lean_dec_ref(v_arg_955_);
lean_dec_ref(v_arg_952_);
lean_dec_ref(v_arg_949_);
lean_dec_ref(v_e_922_);
goto v___jp_942_;
}
else
{
lean_object* v___x_961_; 
lean_del_object(v___x_940_);
v___x_961_ = l_Lean_Meta_Structural_isInstDvdInt___redArg(v_arg_955_, v_a_930_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_1062_; 
v_a_962_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_964_ = v___x_961_;
v_isShared_965_ = v_isSharedCheck_1062_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_961_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_1062_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
uint8_t v___x_966_; 
v___x_966_ = lean_unbox(v_a_962_);
lean_dec(v_a_962_);
if (v___x_966_ == 0)
{
lean_object* v___x_967_; lean_object* v___x_969_; 
lean_dec_ref(v_arg_952_);
lean_dec_ref(v_arg_949_);
lean_dec_ref(v_e_922_);
v___x_967_ = lean_box(0);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 0, v___x_967_);
v___x_969_ = v___x_964_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_967_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
else
{
lean_object* v___x_971_; 
lean_del_object(v___x_964_);
lean_inc_ref(v_arg_952_);
v___x_971_ = l_Lean_Meta_getIntValue_x3f(v_arg_952_, v_a_929_, v_a_930_, v_a_931_, v_a_932_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v_a_972_; 
v_a_972_ = lean_ctor_get(v___x_971_, 0);
lean_inc(v_a_972_);
lean_dec_ref_known(v___x_971_, 1);
if (lean_obj_tag(v_a_972_) == 1)
{
lean_object* v_val_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_1038_; 
v_val_973_ = lean_ctor_get(v_a_972_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v_a_972_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_975_ = v_a_972_;
v_isShared_976_ = v_isSharedCheck_1038_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_val_973_);
lean_dec(v_a_972_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_1038_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_977_; 
lean_inc_ref(v_e_922_);
v___x_977_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_922_, v_a_923_, v_a_927_, v_a_929_, v_a_930_, v_a_931_, v_a_932_);
if (lean_obj_tag(v___x_977_) == 0)
{
lean_object* v_a_978_; uint8_t v___x_979_; 
v_a_978_ = lean_ctor_get(v___x_977_, 0);
lean_inc(v_a_978_);
lean_dec_ref_known(v___x_977_, 1);
v___x_979_ = lean_unbox(v_a_978_);
lean_dec(v_a_978_);
if (v___x_979_ == 0)
{
lean_object* v___x_980_; 
lean_del_object(v___x_975_);
lean_dec(v_val_973_);
lean_inc_ref(v_e_922_);
v___x_980_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_922_, v_a_923_, v_a_927_, v_a_929_, v_a_930_, v_a_931_, v_a_932_);
if (lean_obj_tag(v___x_980_) == 0)
{
lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_1006_; 
v_a_981_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_1006_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_983_ = v___x_980_;
v_isShared_984_ = v_isSharedCheck_1006_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v___x_980_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_1006_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
uint8_t v___x_985_; 
v___x_985_ = lean_unbox(v_a_981_);
lean_dec(v_a_981_);
if (v___x_985_ == 0)
{
lean_object* v___x_986_; lean_object* v___x_988_; 
lean_dec_ref(v_arg_952_);
lean_dec_ref(v_arg_949_);
lean_dec_ref(v_e_922_);
v___x_986_ = lean_box(0);
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 0, v___x_986_);
v___x_988_ = v___x_983_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v___x_986_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
else
{
lean_object* v___x_990_; 
lean_del_object(v___x_983_);
lean_inc_ref(v_e_922_);
v___x_990_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v_a_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v_a_991_ = lean_ctor_get(v___x_990_, 0);
lean_inc(v_a_991_);
lean_dec_ref_known(v___x_990_, 1);
v___x_992_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8);
v___x_993_ = l_Lean_eagerReflBoolTrue;
v___x_994_ = l_Lean_Meta_mkOfEqFalseCore(v_e_922_, v_a_991_);
v___x_995_ = l_Lean_mkApp4(v___x_992_, v_arg_952_, v_arg_949_, v___x_993_, v___x_994_);
v___x_996_ = lean_unsigned_to_nat(0u);
v___x_997_ = l_Lean_Meta_Grind_pushNewFact(v___x_995_, v___x_996_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_);
return v___x_997_;
}
else
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1005_; 
lean_dec_ref(v_arg_952_);
lean_dec_ref(v_arg_949_);
lean_dec_ref(v_e_922_);
v_a_998_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1005_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1005_ == 0)
{
v___x_1000_ = v___x_990_;
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_990_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1005_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1003_; 
if (v_isShared_1001_ == 0)
{
v___x_1003_ = v___x_1000_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_a_998_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
}
}
}
else
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1014_; 
lean_dec_ref(v_arg_952_);
lean_dec_ref(v_arg_949_);
lean_dec_ref(v_e_922_);
v_a_1007_ = lean_ctor_get(v___x_980_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_980_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1009_ = v___x_980_;
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_980_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_a_1007_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
}
else
{
lean_object* v___x_1015_; 
lean_dec_ref(v_arg_952_);
v___x_1015_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(v_arg_949_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v_a_1016_; lean_object* v___x_1018_; 
v_a_1016_ = lean_ctor_get(v___x_1015_, 0);
lean_inc(v_a_1016_);
lean_dec_ref_known(v___x_1015_, 1);
if (v_isShared_976_ == 0)
{
lean_ctor_set_tag(v___x_975_, 0);
lean_ctor_set(v___x_975_, 0, v_e_922_);
v___x_1018_ = v___x_975_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_e_922_);
v___x_1018_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1019_, 0, v_val_973_);
lean_ctor_set(v___x_1019_, 1, v_a_1016_);
lean_ctor_set(v___x_1019_, 2, v___x_1018_);
v___x_1020_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v___x_1019_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_);
return v___x_1020_;
}
}
else
{
lean_object* v_a_1022_; lean_object* v___x_1024_; uint8_t v_isShared_1025_; uint8_t v_isSharedCheck_1029_; 
lean_del_object(v___x_975_);
lean_dec(v_val_973_);
lean_dec_ref(v_e_922_);
v_a_1022_ = lean_ctor_get(v___x_1015_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1029_ == 0)
{
v___x_1024_ = v___x_1015_;
v_isShared_1025_ = v_isSharedCheck_1029_;
goto v_resetjp_1023_;
}
else
{
lean_inc(v_a_1022_);
lean_dec(v___x_1015_);
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
lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1037_; 
lean_del_object(v___x_975_);
lean_dec(v_val_973_);
lean_dec_ref(v_arg_952_);
lean_dec_ref(v_arg_949_);
lean_dec_ref(v_e_922_);
v_a_1030_ = lean_ctor_get(v___x_977_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v___x_977_);
if (v_isSharedCheck_1037_ == 0)
{
v___x_1032_ = v___x_977_;
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___x_977_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1037_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1035_; 
if (v_isShared_1033_ == 0)
{
v___x_1035_ = v___x_1032_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v_a_1030_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
}
}
else
{
lean_object* v___x_1039_; 
lean_dec(v_a_972_);
lean_dec_ref(v_arg_952_);
lean_dec_ref(v_arg_949_);
v___x_1039_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_927_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v_a_1040_; uint8_t v_verbose_1041_; 
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
lean_inc(v_a_1040_);
lean_dec_ref_known(v___x_1039_, 1);
v_verbose_1041_ = lean_ctor_get_uint8(v_a_1040_, 0);
lean_dec(v_a_1040_);
if (v_verbose_1041_ == 0)
{
lean_dec_ref(v_e_922_);
goto v___jp_934_;
}
else
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1042_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10);
v___x_1043_ = l_Lean_indentExpr(v_e_922_);
v___x_1044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1044_, 0, v___x_1042_);
lean_ctor_set(v___x_1044_, 1, v___x_1043_);
v___x_1045_ = l_Lean_Meta_Sym_reportIssue(v___x_1044_, v_a_927_, v_a_928_, v_a_929_, v_a_930_, v_a_931_, v_a_932_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_dec_ref_known(v___x_1045_, 1);
goto v___jp_934_;
}
else
{
return v___x_1045_;
}
}
}
else
{
lean_object* v_a_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1053_; 
lean_dec_ref(v_e_922_);
v_a_1046_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1053_ == 0)
{
v___x_1048_ = v___x_1039_;
v_isShared_1049_ = v_isSharedCheck_1053_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_a_1046_);
lean_dec(v___x_1039_);
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
else
{
lean_object* v_a_1054_; lean_object* v___x_1056_; uint8_t v_isShared_1057_; uint8_t v_isSharedCheck_1061_; 
lean_dec_ref(v_arg_952_);
lean_dec_ref(v_arg_949_);
lean_dec_ref(v_e_922_);
v_a_1054_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1056_ = v___x_971_;
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
else
{
lean_inc(v_a_1054_);
lean_dec(v___x_971_);
v___x_1056_ = lean_box(0);
v_isShared_1057_ = v_isSharedCheck_1061_;
goto v_resetjp_1055_;
}
v_resetjp_1055_:
{
lean_object* v___x_1059_; 
if (v_isShared_1057_ == 0)
{
v___x_1059_ = v___x_1056_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v_a_1054_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
}
}
else
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1070_; 
lean_dec_ref(v_arg_952_);
lean_dec_ref(v_arg_949_);
lean_dec_ref(v_e_922_);
v_a_1063_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1065_ = v___x_961_;
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_961_);
v___x_1065_ = lean_box(0);
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
v_resetjp_1064_:
{
lean_object* v___x_1068_; 
if (v_isShared_1066_ == 0)
{
v___x_1068_ = v___x_1065_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1069_; 
v_reuseFailAlloc_1069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1069_, 0, v_a_1063_);
v___x_1068_ = v_reuseFailAlloc_1069_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
return v___x_1068_;
}
}
}
}
}
}
}
}
v___jp_942_:
{
lean_object* v___x_943_; lean_object* v___x_945_; 
v___x_943_ = lean_box(0);
if (v_isShared_941_ == 0)
{
lean_ctor_set(v___x_940_, 0, v___x_943_);
v___x_945_ = v___x_940_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_943_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
else
{
lean_object* v_a_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1079_; 
lean_dec_ref(v_e_922_);
v_a_1072_ = lean_ctor_get(v___x_937_, 0);
v_isSharedCheck_1079_ = !lean_is_exclusive(v___x_937_);
if (v_isSharedCheck_1079_ == 0)
{
v___x_1074_ = v___x_937_;
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_a_1072_);
lean_dec(v___x_937_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1079_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1077_; 
if (v_isShared_1075_ == 0)
{
v___x_1077_ = v___x_1074_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_a_1072_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
}
v___jp_934_:
{
lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_935_ = lean_box(0);
v___x_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
return v___x_936_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___boxed(lean_object* v_e_1080_, lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(v_e_1080_, v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_);
lean_dec(v_a_1090_);
lean_dec_ref(v_a_1089_);
lean_dec(v_a_1088_);
lean_dec_ref(v_a_1087_);
lean_dec(v_a_1086_);
lean_dec_ref(v_a_1085_);
lean_dec(v_a_1084_);
lean_dec_ref(v_a_1083_);
lean_dec(v_a_1082_);
lean_dec(v_a_1081_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd_spec__0(lean_object* v_a_1093_){
_start:
{
lean_object* v___x_1094_; 
v___x_1094_ = lean_nat_to_int(v_a_1093_);
return v___x_1094_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3(void){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1100_ = lean_box(0);
v___x_1101_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2));
v___x_1102_ = l_Lean_mkConst(v___x_1101_, v___x_1100_);
return v___x_1102_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7(void){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1109_ = lean_box(0);
v___x_1110_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6));
v___x_1111_ = l_Lean_mkConst(v___x_1110_, v___x_1109_);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(lean_object* v_e_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_){
_start:
{
lean_object* v___x_1130_; uint8_t v___x_1131_; 
lean_inc_ref(v_e_1112_);
v___x_1130_ = l_Lean_Expr_cleanupAnnotations(v_e_1112_);
v___x_1131_ = l_Lean_Expr_isApp(v___x_1130_);
if (v___x_1131_ == 0)
{
lean_dec_ref(v___x_1130_);
lean_dec_ref(v_e_1112_);
goto v___jp_1124_;
}
else
{
lean_object* v_arg_1132_; lean_object* v___x_1133_; uint8_t v___x_1134_; 
v_arg_1132_ = lean_ctor_get(v___x_1130_, 1);
lean_inc_ref(v_arg_1132_);
v___x_1133_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1130_);
v___x_1134_ = l_Lean_Expr_isApp(v___x_1133_);
if (v___x_1134_ == 0)
{
lean_dec_ref(v___x_1133_);
lean_dec_ref(v_arg_1132_);
lean_dec_ref(v_e_1112_);
goto v___jp_1124_;
}
else
{
lean_object* v_arg_1135_; lean_object* v___x_1136_; uint8_t v___x_1137_; 
v_arg_1135_ = lean_ctor_get(v___x_1133_, 1);
lean_inc_ref(v_arg_1135_);
v___x_1136_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1133_);
v___x_1137_ = l_Lean_Expr_isApp(v___x_1136_);
if (v___x_1137_ == 0)
{
lean_dec_ref(v___x_1136_);
lean_dec_ref(v_arg_1135_);
lean_dec_ref(v_arg_1132_);
lean_dec_ref(v_e_1112_);
goto v___jp_1124_;
}
else
{
lean_object* v_arg_1138_; lean_object* v___x_1139_; uint8_t v___x_1140_; 
v_arg_1138_ = lean_ctor_get(v___x_1136_, 1);
lean_inc_ref(v_arg_1138_);
v___x_1139_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1136_);
v___x_1140_ = l_Lean_Expr_isApp(v___x_1139_);
if (v___x_1140_ == 0)
{
lean_dec_ref(v___x_1139_);
lean_dec_ref(v_arg_1138_);
lean_dec_ref(v_arg_1135_);
lean_dec_ref(v_arg_1132_);
lean_dec_ref(v_e_1112_);
goto v___jp_1124_;
}
else
{
lean_object* v___x_1141_; lean_object* v___x_1142_; uint8_t v___x_1143_; 
v___x_1141_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1139_);
v___x_1142_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1143_ = l_Lean_Expr_isConstOf(v___x_1141_, v___x_1142_);
lean_dec_ref(v___x_1141_);
if (v___x_1143_ == 0)
{
lean_dec_ref(v_arg_1138_);
lean_dec_ref(v_arg_1135_);
lean_dec_ref(v_arg_1132_);
lean_dec_ref(v_e_1112_);
goto v___jp_1124_;
}
else
{
lean_object* v___x_1144_; 
v___x_1144_ = l_Lean_Meta_Structural_isInstDvdNat___redArg(v_arg_1138_, v_a_1120_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1276_; 
v_a_1145_ = lean_ctor_get(v___x_1144_, 0);
v_isSharedCheck_1276_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1147_ = v___x_1144_;
v_isShared_1148_ = v_isSharedCheck_1276_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1144_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1276_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
uint8_t v___x_1149_; 
v___x_1149_ = lean_unbox(v_a_1145_);
lean_dec(v_a_1145_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; lean_object* v___x_1152_; 
lean_dec_ref(v_arg_1135_);
lean_dec_ref(v_arg_1132_);
lean_dec_ref(v_e_1112_);
v___x_1150_ = lean_box(0);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 0, v___x_1150_);
v___x_1152_ = v___x_1147_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1150_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
else
{
lean_object* v___x_1154_; 
lean_del_object(v___x_1147_);
v___x_1154_ = l_Lean_Meta_getNatValue_x3f(v_arg_1135_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_object* v_a_1155_; 
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
lean_inc(v_a_1155_);
lean_dec_ref_known(v___x_1154_, 1);
if (lean_obj_tag(v_a_1155_) == 1)
{
lean_object* v_val_1156_; lean_object* v___x_1157_; 
v_val_1156_ = lean_ctor_get(v_a_1155_, 0);
lean_inc(v_val_1156_);
lean_dec_ref_known(v_a_1155_, 1);
lean_inc_ref(v_e_1112_);
v___x_1157_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_1112_, v_a_1113_, v_a_1117_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_object* v_a_1158_; uint8_t v___x_1159_; 
v_a_1158_ = lean_ctor_get(v___x_1157_, 0);
lean_inc(v_a_1158_);
lean_dec_ref_known(v___x_1157_, 1);
v___x_1159_ = lean_unbox(v_a_1158_);
lean_dec(v_a_1158_);
if (v___x_1159_ == 0)
{
lean_object* v___x_1160_; 
lean_dec(v_val_1156_);
lean_inc_ref(v_e_1112_);
v___x_1160_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_1112_, v_a_1113_, v_a_1117_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
if (lean_obj_tag(v___x_1160_) == 0)
{
lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1185_; 
v_a_1161_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1163_ = v___x_1160_;
v_isShared_1164_ = v_isSharedCheck_1185_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_dec(v___x_1160_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1185_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
uint8_t v___x_1165_; 
v___x_1165_ = lean_unbox(v_a_1161_);
lean_dec(v_a_1161_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; lean_object* v___x_1168_; 
lean_dec_ref(v_arg_1135_);
lean_dec_ref(v_arg_1132_);
lean_dec_ref(v_e_1112_);
v___x_1166_ = lean_box(0);
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 0, v___x_1166_);
v___x_1168_ = v___x_1163_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1166_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
else
{
lean_object* v___x_1170_; 
lean_del_object(v___x_1163_);
lean_inc_ref(v_e_1112_);
v___x_1170_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
if (lean_obj_tag(v___x_1170_) == 0)
{
lean_object* v_a_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; 
v_a_1171_ = lean_ctor_get(v___x_1170_, 0);
lean_inc(v_a_1171_);
lean_dec_ref_known(v___x_1170_, 1);
v___x_1172_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3);
v___x_1173_ = l_Lean_Meta_mkOfEqFalseCore(v_e_1112_, v_a_1171_);
v___x_1174_ = l_Lean_mkApp3(v___x_1172_, v_arg_1135_, v_arg_1132_, v___x_1173_);
v___x_1175_ = lean_unsigned_to_nat(0u);
v___x_1176_ = l_Lean_Meta_Grind_pushNewFact(v___x_1174_, v___x_1175_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
return v___x_1176_;
}
else
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1184_; 
lean_dec_ref(v_arg_1135_);
lean_dec_ref(v_arg_1132_);
lean_dec_ref(v_e_1112_);
v_a_1177_ = lean_ctor_get(v___x_1170_, 0);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1170_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1179_ = v___x_1170_;
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v___x_1170_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1184_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1182_; 
if (v_isShared_1180_ == 0)
{
v___x_1182_ = v___x_1179_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_a_1177_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
}
}
}
else
{
lean_object* v_a_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1193_; 
lean_dec_ref(v_arg_1135_);
lean_dec_ref(v_arg_1132_);
lean_dec_ref(v_e_1112_);
v_a_1186_ = lean_ctor_get(v___x_1160_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1160_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1188_ = v___x_1160_;
v_isShared_1189_ = v_isSharedCheck_1193_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_a_1186_);
lean_dec(v___x_1160_);
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
lean_object* v___x_1194_; 
lean_inc_ref(v_arg_1135_);
v___x_1194_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_1135_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
if (lean_obj_tag(v___x_1194_) == 0)
{
lean_object* v_a_1195_; lean_object* v_fst_1196_; lean_object* v_snd_1197_; lean_object* v___x_1198_; 
v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
lean_inc(v_a_1195_);
lean_dec_ref_known(v___x_1194_, 1);
v_fst_1196_ = lean_ctor_get(v_a_1195_, 0);
lean_inc(v_fst_1196_);
v_snd_1197_ = lean_ctor_get(v_a_1195_, 1);
lean_inc(v_snd_1197_);
lean_dec(v_a_1195_);
lean_inc_ref(v_arg_1132_);
v___x_1198_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_1132_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v_a_1199_; lean_object* v_fst_1200_; lean_object* v_snd_1201_; lean_object* v___x_1202_; 
v_a_1199_ = lean_ctor_get(v___x_1198_, 0);
lean_inc(v_a_1199_);
lean_dec_ref_known(v___x_1198_, 1);
v_fst_1200_ = lean_ctor_get(v_a_1199_, 0);
lean_inc(v_fst_1200_);
v_snd_1201_ = lean_ctor_get(v_a_1199_, 1);
lean_inc(v_snd_1201_);
lean_dec(v_a_1199_);
v___x_1202_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1112_, v_a_1113_);
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_object* v_a_1203_; lean_object* v___x_1204_; 
v_a_1203_ = lean_ctor_get(v___x_1202_, 0);
lean_inc(v_a_1203_);
lean_dec_ref_known(v___x_1202_, 1);
lean_inc(v_fst_1200_);
v___x_1204_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_1200_, v_a_1203_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
if (lean_obj_tag(v___x_1204_) == 0)
{
lean_object* v_a_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v_a_1205_ = lean_ctor_get(v___x_1204_, 0);
lean_inc(v_a_1205_);
lean_dec_ref_known(v___x_1204_, 1);
v___x_1206_ = l_Int_Internal_Linear_Expr_norm(v_a_1205_);
v___x_1207_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7);
v___x_1208_ = l_Lean_mkApp6(v___x_1207_, v_arg_1135_, v_arg_1132_, v_fst_1196_, v_fst_1200_, v_snd_1197_, v_snd_1201_);
lean_inc(v_val_1156_);
v___x_1209_ = lean_nat_to_int(v_val_1156_);
v___x_1210_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1210_, 0, v_e_1112_);
lean_ctor_set(v___x_1210_, 1, v___x_1208_);
lean_ctor_set(v___x_1210_, 2, v_val_1156_);
lean_ctor_set(v___x_1210_, 3, v_a_1205_);
v___x_1211_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1211_, 0, v___x_1209_);
lean_ctor_set(v___x_1211_, 1, v___x_1206_);
lean_ctor_set(v___x_1211_, 2, v___x_1210_);
v___x_1212_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v___x_1211_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
return v___x_1212_;
}
else
{
lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1220_; 
lean_dec(v_snd_1201_);
lean_dec(v_fst_1200_);
lean_dec(v_snd_1197_);
lean_dec(v_fst_1196_);
lean_dec(v_val_1156_);
lean_dec_ref(v_arg_1135_);
lean_dec_ref(v_arg_1132_);
lean_dec_ref(v_e_1112_);
v_a_1213_ = lean_ctor_get(v___x_1204_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1204_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1215_ = v___x_1204_;
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v___x_1204_);
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
lean_dec(v_snd_1201_);
lean_dec(v_fst_1200_);
lean_dec(v_snd_1197_);
lean_dec(v_fst_1196_);
lean_dec(v_val_1156_);
lean_dec_ref(v_arg_1135_);
lean_dec_ref(v_arg_1132_);
lean_dec_ref(v_e_1112_);
v_a_1221_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1223_ = v___x_1202_;
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1202_);
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
lean_dec(v_snd_1197_);
lean_dec(v_fst_1196_);
lean_dec(v_val_1156_);
lean_dec_ref(v_arg_1135_);
lean_dec_ref(v_arg_1132_);
lean_dec_ref(v_e_1112_);
v_a_1229_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1231_ = v___x_1198_;
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1198_);
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
else
{
lean_object* v_a_1237_; lean_object* v___x_1239_; uint8_t v_isShared_1240_; uint8_t v_isSharedCheck_1244_; 
lean_dec(v_val_1156_);
lean_dec_ref(v_arg_1135_);
lean_dec_ref(v_arg_1132_);
lean_dec_ref(v_e_1112_);
v_a_1237_ = lean_ctor_get(v___x_1194_, 0);
v_isSharedCheck_1244_ = !lean_is_exclusive(v___x_1194_);
if (v_isSharedCheck_1244_ == 0)
{
v___x_1239_ = v___x_1194_;
v_isShared_1240_ = v_isSharedCheck_1244_;
goto v_resetjp_1238_;
}
else
{
lean_inc(v_a_1237_);
lean_dec(v___x_1194_);
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
}
else
{
lean_object* v_a_1245_; lean_object* v___x_1247_; uint8_t v_isShared_1248_; uint8_t v_isSharedCheck_1252_; 
lean_dec(v_val_1156_);
lean_dec_ref(v_arg_1135_);
lean_dec_ref(v_arg_1132_);
lean_dec_ref(v_e_1112_);
v_a_1245_ = lean_ctor_get(v___x_1157_, 0);
v_isSharedCheck_1252_ = !lean_is_exclusive(v___x_1157_);
if (v_isSharedCheck_1252_ == 0)
{
v___x_1247_ = v___x_1157_;
v_isShared_1248_ = v_isSharedCheck_1252_;
goto v_resetjp_1246_;
}
else
{
lean_inc(v_a_1245_);
lean_dec(v___x_1157_);
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
else
{
lean_object* v___x_1253_; 
lean_dec(v_a_1155_);
lean_dec_ref(v_arg_1135_);
lean_dec_ref(v_arg_1132_);
v___x_1253_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1117_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_a_1254_; uint8_t v_verbose_1255_; 
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_a_1254_);
lean_dec_ref_known(v___x_1253_, 1);
v_verbose_1255_ = lean_ctor_get_uint8(v_a_1254_, 0);
lean_dec(v_a_1254_);
if (v_verbose_1255_ == 0)
{
lean_dec_ref(v_e_1112_);
goto v___jp_1127_;
}
else
{
lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
v___x_1256_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10);
v___x_1257_ = l_Lean_indentExpr(v_e_1112_);
v___x_1258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1256_);
lean_ctor_set(v___x_1258_, 1, v___x_1257_);
v___x_1259_ = l_Lean_Meta_Sym_reportIssue(v___x_1258_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_);
if (lean_obj_tag(v___x_1259_) == 0)
{
lean_dec_ref_known(v___x_1259_, 1);
goto v___jp_1127_;
}
else
{
return v___x_1259_;
}
}
}
else
{
lean_object* v_a_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1267_; 
lean_dec_ref(v_e_1112_);
v_a_1260_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1262_ = v___x_1253_;
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_a_1260_);
lean_dec(v___x_1253_);
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
else
{
lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1275_; 
lean_dec_ref(v_arg_1135_);
lean_dec_ref(v_arg_1132_);
lean_dec_ref(v_e_1112_);
v_a_1268_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1270_ = v___x_1154_;
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_dec(v___x_1154_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1273_; 
if (v_isShared_1271_ == 0)
{
v___x_1273_ = v___x_1270_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_a_1268_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
}
}
}
else
{
lean_object* v_a_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1284_; 
lean_dec_ref(v_arg_1135_);
lean_dec_ref(v_arg_1132_);
lean_dec_ref(v_e_1112_);
v_a_1277_ = lean_ctor_get(v___x_1144_, 0);
v_isSharedCheck_1284_ = !lean_is_exclusive(v___x_1144_);
if (v_isSharedCheck_1284_ == 0)
{
v___x_1279_ = v___x_1144_;
v_isShared_1280_ = v_isSharedCheck_1284_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_a_1277_);
lean_dec(v___x_1144_);
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
}
}
}
v___jp_1124_:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = lean_box(0);
v___x_1126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1125_);
return v___x_1126_;
}
v___jp_1127_:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1128_ = lean_box(0);
v___x_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1128_);
return v___x_1129_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___boxed(lean_object* v_e_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(v_e_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_);
lean_dec(v_a_1295_);
lean_dec_ref(v_a_1294_);
lean_dec(v_a_1293_);
lean_dec_ref(v_a_1292_);
lean_dec(v_a_1291_);
lean_dec_ref(v_a_1290_);
lean_dec(v_a_1289_);
lean_dec_ref(v_a_1288_);
lean_dec(v_a_1287_);
lean_dec(v_a_1286_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(lean_object* v_e_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_, lean_object* v_a_1305_, lean_object* v_a_1306_, lean_object* v_a_1307_, lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_){
_start:
{
lean_object* v___x_1312_; 
v___x_1312_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1303_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1357_; 
v_a_1313_ = lean_ctor_get(v___x_1312_, 0);
v_isSharedCheck_1357_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1315_ = v___x_1312_;
v_isShared_1316_ = v_isSharedCheck_1357_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v___x_1312_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1357_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
uint8_t v_lia_1317_; 
v_lia_1317_ = lean_ctor_get_uint8(v_a_1313_, sizeof(void*)*14 + 23);
lean_dec(v_a_1313_);
if (v_lia_1317_ == 0)
{
lean_object* v___x_1318_; lean_object* v___x_1320_; 
lean_dec_ref(v_e_1300_);
v___x_1318_ = lean_box(0);
if (v_isShared_1316_ == 0)
{
lean_ctor_set(v___x_1315_, 0, v___x_1318_);
v___x_1320_ = v___x_1315_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v___x_1318_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
else
{
lean_object* v___x_1322_; 
lean_del_object(v___x_1315_);
lean_inc_ref(v_e_1300_);
v___x_1322_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1300_, v_a_1308_);
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_object* v_a_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1348_; 
v_a_1323_ = lean_ctor_get(v___x_1322_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1325_ = v___x_1322_;
v_isShared_1326_ = v_isSharedCheck_1348_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_a_1323_);
lean_dec(v___x_1322_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1348_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1332_; uint8_t v___x_1333_; 
v___x_1332_ = l_Lean_Expr_cleanupAnnotations(v_a_1323_);
v___x_1333_ = l_Lean_Expr_isApp(v___x_1332_);
if (v___x_1333_ == 0)
{
lean_dec_ref(v___x_1332_);
lean_dec_ref(v_e_1300_);
goto v___jp_1327_;
}
else
{
lean_object* v___x_1334_; uint8_t v___x_1335_; 
v___x_1334_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1332_);
v___x_1335_ = l_Lean_Expr_isApp(v___x_1334_);
if (v___x_1335_ == 0)
{
lean_dec_ref(v___x_1334_);
lean_dec_ref(v_e_1300_);
goto v___jp_1327_;
}
else
{
lean_object* v___x_1336_; uint8_t v___x_1337_; 
v___x_1336_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1334_);
v___x_1337_ = l_Lean_Expr_isApp(v___x_1336_);
if (v___x_1337_ == 0)
{
lean_dec_ref(v___x_1336_);
lean_dec_ref(v_e_1300_);
goto v___jp_1327_;
}
else
{
lean_object* v___x_1338_; uint8_t v___x_1339_; 
v___x_1338_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1336_);
v___x_1339_ = l_Lean_Expr_isApp(v___x_1338_);
if (v___x_1339_ == 0)
{
lean_dec_ref(v___x_1338_);
lean_dec_ref(v_e_1300_);
goto v___jp_1327_;
}
else
{
lean_object* v_arg_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; uint8_t v___x_1343_; 
v_arg_1340_ = lean_ctor_get(v___x_1338_, 1);
lean_inc_ref(v_arg_1340_);
v___x_1341_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1338_);
v___x_1342_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1343_ = l_Lean_Expr_isConstOf(v___x_1341_, v___x_1342_);
lean_dec_ref(v___x_1341_);
if (v___x_1343_ == 0)
{
lean_dec_ref(v_arg_1340_);
lean_dec_ref(v_e_1300_);
goto v___jp_1327_;
}
else
{
lean_object* v___x_1344_; uint8_t v___x_1345_; 
lean_del_object(v___x_1325_);
v___x_1344_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0));
v___x_1345_ = l_Lean_Expr_isConstOf(v_arg_1340_, v___x_1344_);
lean_dec_ref(v_arg_1340_);
if (v___x_1345_ == 0)
{
lean_object* v___x_1346_; 
v___x_1346_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(v_e_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_);
return v___x_1346_;
}
else
{
lean_object* v___x_1347_; 
v___x_1347_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(v_e_1300_, v_a_1301_, v_a_1302_, v_a_1303_, v_a_1304_, v_a_1305_, v_a_1306_, v_a_1307_, v_a_1308_, v_a_1309_, v_a_1310_);
return v___x_1347_;
}
}
}
}
}
}
v___jp_1327_:
{
lean_object* v___x_1328_; lean_object* v___x_1330_; 
v___x_1328_ = lean_box(0);
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 0, v___x_1328_);
v___x_1330_ = v___x_1325_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1328_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
else
{
lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1356_; 
lean_dec_ref(v_e_1300_);
v_a_1349_ = lean_ctor_get(v___x_1322_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1351_ = v___x_1322_;
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1322_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1356_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
lean_object* v___x_1354_; 
if (v_isShared_1352_ == 0)
{
v___x_1354_ = v___x_1351_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v_a_1349_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
}
}
else
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1365_; 
lean_dec_ref(v_e_1300_);
v_a_1358_ = lean_ctor_get(v___x_1312_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1360_ = v___x_1312_;
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1312_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1363_; 
if (v_isShared_1361_ == 0)
{
v___x_1363_ = v___x_1360_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_a_1358_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed(lean_object* v_e_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_, lean_object* v_a_1374_, lean_object* v_a_1375_, lean_object* v_a_1376_, lean_object* v_a_1377_){
_start:
{
lean_object* v_res_1378_; 
v_res_1378_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(v_e_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_, v_a_1373_, v_a_1374_, v_a_1375_, v_a_1376_);
lean_dec(v_a_1376_);
lean_dec_ref(v_a_1375_);
lean_dec(v_a_1374_);
lean_dec_ref(v_a_1373_);
lean_dec(v_a_1372_);
lean_dec_ref(v_a_1371_);
lean_dec(v_a_1370_);
lean_dec_ref(v_a_1369_);
lean_dec(v_a_1368_);
lean_dec(v_a_1367_);
return v_res_1378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1380_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1381_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed), 12, 0);
v___x_1382_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_1380_, v___x_1381_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_8____boxed(lean_object* v_a_1383_){
_start:
{
lean_object* v_res_1384_; 
v_res_1384_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_8_();
return v_res_1384_;
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
res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_8_();
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
