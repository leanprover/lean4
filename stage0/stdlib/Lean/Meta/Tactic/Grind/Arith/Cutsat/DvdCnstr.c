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
uint8_t lean_bool_not(uint8_t);
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
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Int_Internal_Linear_Poly_isUnsatDvd(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_set___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqLBool_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(lean_object*, lean_object*);
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
lean_object* v___y_7_; lean_object* v___y_8_; lean_object* v___y_9_; lean_object* v___y_10_; uint8_t v___y_11_; lean_object* v___y_17_; lean_object* v___y_18_; lean_object* v___y_19_; lean_object* v___y_20_; lean_object* v___y_21_; lean_object* v___y_29_; lean_object* v_d_30_; lean_object* v_p_31_; lean_object* v_d_36_; lean_object* v_p_37_; uint8_t v___x_38_; 
v_d_36_ = lean_ctor_get(v_c_5_, 0);
lean_inc(v_d_36_);
v_p_37_ = lean_ctor_get(v_c_5_, 1);
v___x_38_ = l_Int_Internal_Linear_Poly_isSorted(v_p_37_);
if (v___x_38_ == 0)
{
lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
lean_inc_ref(v_p_37_);
v___x_39_ = l_Int_Internal_Linear_Poly_norm(v_p_37_);
v___x_40_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_40_, 0, v_c_5_);
lean_inc_ref(v___x_39_);
lean_inc(v_d_36_);
v___x_41_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_41_, 0, v_d_36_);
lean_ctor_set(v___x_41_, 1, v___x_39_);
lean_ctor_set(v___x_41_, 2, v___x_40_);
v___y_29_ = v___x_41_;
v_d_30_ = v_d_36_;
v_p_31_ = v___x_39_;
goto v___jp_28_;
}
else
{
lean_inc_ref(v_p_37_);
v___y_29_ = v_c_5_;
v_d_30_ = v_d_36_;
v_p_31_ = v_p_37_;
goto v___jp_28_;
}
v___jp_6_:
{
if (v___y_11_ == 0)
{
lean_dec(v___y_10_);
lean_dec(v___y_9_);
lean_dec_ref(v___y_8_);
return v___y_7_;
}
else
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___x_12_ = lean_int_ediv(v___y_10_, v___y_9_);
lean_dec(v___y_10_);
v___x_13_ = l_Int_Internal_Linear_Poly_div(v___y_9_, v___y_8_);
lean_dec(v___y_9_);
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
v___x_22_ = l_Int_Internal_Linear_Poly_getConst(v___y_19_);
v___x_23_ = lean_int_emod(v___x_22_, v___y_21_);
lean_dec(v___x_22_);
v___x_24_ = lean_int_dec_eq(v___x_23_, v___y_17_);
lean_dec(v___x_23_);
if (v___x_24_ == 0)
{
v___y_7_ = v___y_18_;
v___y_8_ = v___y_19_;
v___y_9_ = v___y_21_;
v___y_10_ = v___y_20_;
v___y_11_ = v___x_24_;
goto v___jp_6_;
}
else
{
lean_object* v___x_25_; uint8_t v___x_26_; uint8_t v___x_27_; 
v___x_25_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__0);
v___x_26_ = lean_int_dec_eq(v___y_21_, v___x_25_);
v___x_27_ = lean_bool_not(v___x_26_);
v___y_7_ = v___y_18_;
v___y_8_ = v___y_19_;
v___y_9_ = v___y_21_;
v___y_10_ = v___y_20_;
v___y_11_ = v___x_27_;
goto v___jp_6_;
}
}
v___jp_28_:
{
lean_object* v_g_32_; lean_object* v___x_33_; uint8_t v___x_34_; 
lean_inc(v_d_30_);
v_g_32_ = l_Int_Internal_Linear_Poly_gcdCoeffs(v_p_31_, v_d_30_);
v___x_33_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1);
v___x_34_ = lean_int_dec_lt(v_d_30_, v___x_33_);
if (v___x_34_ == 0)
{
v___y_17_ = v___x_33_;
v___y_18_ = v___y_29_;
v___y_19_ = v_p_31_;
v___y_20_ = v_d_30_;
v___y_21_ = v_g_32_;
goto v___jp_16_;
}
else
{
lean_object* v___x_35_; 
v___x_35_ = lean_int_neg(v_g_32_);
lean_dec(v_g_32_);
v___y_17_ = v___x_33_;
v___y_18_ = v___y_29_;
v___y_19_ = v_p_31_;
v___y_20_ = v_d_30_;
v___y_21_ = v___x_35_;
goto v___jp_16_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0_spec__0(lean_object* v_msgData_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_){
_start:
{
lean_object* v___x_48_; lean_object* v_env_49_; lean_object* v___x_50_; lean_object* v_mctx_51_; lean_object* v_lctx_52_; lean_object* v_options_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_48_ = lean_st_ref_get(v___y_46_);
v_env_49_ = lean_ctor_get(v___x_48_, 0);
lean_inc_ref(v_env_49_);
lean_dec(v___x_48_);
v___x_50_ = lean_st_ref_get(v___y_44_);
v_mctx_51_ = lean_ctor_get(v___x_50_, 0);
lean_inc_ref(v_mctx_51_);
lean_dec(v___x_50_);
v_lctx_52_ = lean_ctor_get(v___y_43_, 2);
v_options_53_ = lean_ctor_get(v___y_45_, 2);
lean_inc_ref(v_options_53_);
lean_inc_ref(v_lctx_52_);
v___x_54_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_54_, 0, v_env_49_);
lean_ctor_set(v___x_54_, 1, v_mctx_51_);
lean_ctor_set(v___x_54_, 2, v_lctx_52_);
lean_ctor_set(v___x_54_, 3, v_options_53_);
v___x_55_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_55_, 0, v___x_54_);
lean_ctor_set(v___x_55_, 1, v_msgData_42_);
v___x_56_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_56_, 0, v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0_spec__0___boxed(lean_object* v_msgData_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0_spec__0(v_msgData_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_);
lean_dec(v___y_61_);
lean_dec_ref(v___y_60_);
lean_dec(v___y_59_);
lean_dec_ref(v___y_58_);
return v_res_63_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_64_; double v___x_65_; 
v___x_64_ = lean_unsigned_to_nat(0u);
v___x_65_ = lean_float_of_nat(v___x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(lean_object* v_cls_69_, lean_object* v_msg_70_, lean_object* v___y_71_, lean_object* v___y_72_, lean_object* v___y_73_, lean_object* v___y_74_){
_start:
{
lean_object* v_ref_76_; lean_object* v___x_77_; lean_object* v_a_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_122_; 
v_ref_76_ = lean_ctor_get(v___y_73_, 5);
v___x_77_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0_spec__0(v_msg_70_, v___y_71_, v___y_72_, v___y_73_, v___y_74_);
v_a_78_ = lean_ctor_get(v___x_77_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_77_);
if (v_isSharedCheck_122_ == 0)
{
v___x_80_ = v___x_77_;
v_isShared_81_ = v_isSharedCheck_122_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_a_78_);
lean_dec(v___x_77_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_122_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___x_82_; lean_object* v_traceState_83_; lean_object* v_env_84_; lean_object* v_nextMacroScope_85_; lean_object* v_ngen_86_; lean_object* v_auxDeclNGen_87_; lean_object* v_cache_88_; lean_object* v_messages_89_; lean_object* v_infoState_90_; lean_object* v_snapshotTasks_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_121_; 
v___x_82_ = lean_st_ref_take(v___y_74_);
v_traceState_83_ = lean_ctor_get(v___x_82_, 4);
v_env_84_ = lean_ctor_get(v___x_82_, 0);
v_nextMacroScope_85_ = lean_ctor_get(v___x_82_, 1);
v_ngen_86_ = lean_ctor_get(v___x_82_, 2);
v_auxDeclNGen_87_ = lean_ctor_get(v___x_82_, 3);
v_cache_88_ = lean_ctor_get(v___x_82_, 5);
v_messages_89_ = lean_ctor_get(v___x_82_, 6);
v_infoState_90_ = lean_ctor_get(v___x_82_, 7);
v_snapshotTasks_91_ = lean_ctor_get(v___x_82_, 8);
v_isSharedCheck_121_ = !lean_is_exclusive(v___x_82_);
if (v_isSharedCheck_121_ == 0)
{
v___x_93_ = v___x_82_;
v_isShared_94_ = v_isSharedCheck_121_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_snapshotTasks_91_);
lean_inc(v_infoState_90_);
lean_inc(v_messages_89_);
lean_inc(v_cache_88_);
lean_inc(v_traceState_83_);
lean_inc(v_auxDeclNGen_87_);
lean_inc(v_ngen_86_);
lean_inc(v_nextMacroScope_85_);
lean_inc(v_env_84_);
lean_dec(v___x_82_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_121_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
uint64_t v_tid_95_; lean_object* v_traces_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_120_; 
v_tid_95_ = lean_ctor_get_uint64(v_traceState_83_, sizeof(void*)*1);
v_traces_96_ = lean_ctor_get(v_traceState_83_, 0);
v_isSharedCheck_120_ = !lean_is_exclusive(v_traceState_83_);
if (v_isSharedCheck_120_ == 0)
{
v___x_98_ = v_traceState_83_;
v_isShared_99_ = v_isSharedCheck_120_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_traces_96_);
lean_dec(v_traceState_83_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_120_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_100_; double v___x_101_; uint8_t v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_110_; 
v___x_100_ = lean_box(0);
v___x_101_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0);
v___x_102_ = 0;
v___x_103_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__1));
v___x_104_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_104_, 0, v_cls_69_);
lean_ctor_set(v___x_104_, 1, v___x_100_);
lean_ctor_set(v___x_104_, 2, v___x_103_);
lean_ctor_set_float(v___x_104_, sizeof(void*)*3, v___x_101_);
lean_ctor_set_float(v___x_104_, sizeof(void*)*3 + 8, v___x_101_);
lean_ctor_set_uint8(v___x_104_, sizeof(void*)*3 + 16, v___x_102_);
v___x_105_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__2));
v___x_106_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_106_, 0, v___x_104_);
lean_ctor_set(v___x_106_, 1, v_a_78_);
lean_ctor_set(v___x_106_, 2, v___x_105_);
lean_inc(v_ref_76_);
v___x_107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_107_, 0, v_ref_76_);
lean_ctor_set(v___x_107_, 1, v___x_106_);
v___x_108_ = l_Lean_PersistentArray_push___redArg(v_traces_96_, v___x_107_);
if (v_isShared_99_ == 0)
{
lean_ctor_set(v___x_98_, 0, v___x_108_);
v___x_110_ = v___x_98_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_119_; 
v_reuseFailAlloc_119_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_119_, 0, v___x_108_);
lean_ctor_set_uint64(v_reuseFailAlloc_119_, sizeof(void*)*1, v_tid_95_);
v___x_110_ = v_reuseFailAlloc_119_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
lean_object* v___x_112_; 
if (v_isShared_94_ == 0)
{
lean_ctor_set(v___x_93_, 4, v___x_110_);
v___x_112_ = v___x_93_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v_env_84_);
lean_ctor_set(v_reuseFailAlloc_118_, 1, v_nextMacroScope_85_);
lean_ctor_set(v_reuseFailAlloc_118_, 2, v_ngen_86_);
lean_ctor_set(v_reuseFailAlloc_118_, 3, v_auxDeclNGen_87_);
lean_ctor_set(v_reuseFailAlloc_118_, 4, v___x_110_);
lean_ctor_set(v_reuseFailAlloc_118_, 5, v_cache_88_);
lean_ctor_set(v_reuseFailAlloc_118_, 6, v_messages_89_);
lean_ctor_set(v_reuseFailAlloc_118_, 7, v_infoState_90_);
lean_ctor_set(v_reuseFailAlloc_118_, 8, v_snapshotTasks_91_);
v___x_112_ = v_reuseFailAlloc_118_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_116_; 
v___x_113_ = lean_st_ref_set(v___y_74_, v___x_112_);
v___x_114_ = lean_box(0);
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 0, v___x_114_);
v___x_116_ = v___x_80_;
goto v_reusejp_115_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_114_);
v___x_116_ = v_reuseFailAlloc_117_;
goto v_reusejp_115_;
}
v_reusejp_115_:
{
return v___x_116_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___boxed(lean_object* v_cls_123_, lean_object* v_msg_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v_cls_123_, v_msg_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_);
lean_dec(v___y_128_);
lean_dec_ref(v___y_127_);
lean_dec(v___y_126_);
lean_dec_ref(v___y_125_);
return v_res_130_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7(void){
_start:
{
lean_object* v_cls_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v_cls_143_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4));
v___x_144_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
v___x_145_ = l_Lean_Name_append(v___x_144_, v_cls_143_);
return v___x_145_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__8));
v___x_148_ = l_Lean_stringToMessageData(v___x_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(lean_object* v_a_149_, lean_object* v_x_150_, lean_object* v_c_u2081_151_, lean_object* v_b_152_, lean_object* v_c_u2082_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_){
_start:
{
lean_object* v_options_165_; lean_object* v_p_166_; lean_object* v_d_167_; lean_object* v_p_168_; lean_object* v_inheritedTraceOptions_169_; uint8_t v_hasTrace_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v_d_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v_p_177_; 
v_options_165_ = lean_ctor_get(v_a_162_, 2);
v_p_166_ = lean_ctor_get(v_c_u2081_151_, 0);
v_d_167_ = lean_ctor_get(v_c_u2082_153_, 0);
v_p_168_ = lean_ctor_get(v_c_u2082_153_, 1);
v_inheritedTraceOptions_169_ = lean_ctor_get(v_a_162_, 13);
v_hasTrace_170_ = lean_ctor_get_uint8(v_options_165_, sizeof(void*)*1);
v___x_171_ = lean_int_mul(v_a_149_, v_d_167_);
v___x_172_ = lean_nat_abs(v___x_171_);
lean_dec(v___x_171_);
v_d_173_ = lean_nat_to_int(v___x_172_);
lean_inc_ref(v_p_168_);
v___x_174_ = l_Int_Internal_Linear_Poly_mul(v_p_168_, v_a_149_);
v___x_175_ = lean_int_neg(v_b_152_);
lean_inc_ref(v_p_166_);
v___x_176_ = l_Int_Internal_Linear_Poly_mul(v_p_166_, v___x_175_);
lean_dec(v___x_175_);
v_p_177_ = l_Int_Internal_Linear_Poly_combine(v___x_174_, v___x_176_);
if (v_hasTrace_170_ == 0)
{
goto v___jp_178_;
}
else
{
lean_object* v_cls_182_; lean_object* v___x_183_; uint8_t v___x_184_; 
v_cls_182_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__4));
v___x_183_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__7);
v___x_184_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_169_, v_options_165_, v___x_183_);
if (v___x_184_ == 0)
{
goto v___jp_178_;
}
else
{
lean_object* v___x_185_; 
v___x_185_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_x_150_, v_a_154_, v_a_162_);
if (lean_obj_tag(v___x_185_) == 0)
{
lean_object* v_a_186_; lean_object* v___x_187_; 
v_a_186_ = lean_ctor_get(v___x_185_, 0);
lean_inc(v_a_186_);
lean_dec_ref_known(v___x_185_, 1);
lean_inc_ref(v_c_u2081_151_);
v___x_187_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_u2081_151_, v_a_154_, v_a_162_);
if (lean_obj_tag(v___x_187_) == 0)
{
lean_object* v_a_188_; lean_object* v___x_189_; 
v_a_188_ = lean_ctor_get(v___x_187_, 0);
lean_inc(v_a_188_);
lean_dec_ref_known(v___x_187_, 1);
lean_inc_ref(v_c_u2082_153_);
v___x_189_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_u2082_153_, v_a_154_, v_a_162_);
if (lean_obj_tag(v___x_189_) == 0)
{
lean_object* v_a_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v_a_190_ = lean_ctor_get(v___x_189_, 0);
lean_inc(v_a_190_);
lean_dec_ref_known(v___x_189_, 1);
v___x_191_ = l_Lean_MessageData_ofExpr(v_a_186_);
v___x_192_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__9);
v___x_193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_193_, 0, v___x_191_);
lean_ctor_set(v___x_193_, 1, v___x_192_);
v___x_194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
lean_ctor_set(v___x_194_, 1, v_a_188_);
v___x_195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_195_, 0, v___x_194_);
lean_ctor_set(v___x_195_, 1, v___x_192_);
v___x_196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
lean_ctor_set(v___x_196_, 1, v_a_190_);
v___x_197_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v_cls_182_, v___x_196_, v_a_160_, v_a_161_, v_a_162_, v_a_163_);
if (lean_obj_tag(v___x_197_) == 0)
{
lean_dec_ref_known(v___x_197_, 1);
goto v___jp_178_;
}
else
{
lean_object* v_a_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_205_; 
lean_dec_ref(v_p_177_);
lean_dec(v_d_173_);
lean_dec_ref(v_c_u2082_153_);
lean_dec_ref(v_c_u2081_151_);
lean_dec(v_x_150_);
v_a_198_ = lean_ctor_get(v___x_197_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_197_);
if (v_isSharedCheck_205_ == 0)
{
v___x_200_ = v___x_197_;
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_a_198_);
lean_dec(v___x_197_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_203_; 
if (v_isShared_201_ == 0)
{
v___x_203_ = v___x_200_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_a_198_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
}
else
{
lean_object* v_a_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_213_; 
lean_dec(v_a_188_);
lean_dec(v_a_186_);
lean_dec_ref(v_p_177_);
lean_dec(v_d_173_);
lean_dec_ref(v_c_u2082_153_);
lean_dec_ref(v_c_u2081_151_);
lean_dec(v_x_150_);
v_a_206_ = lean_ctor_get(v___x_189_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v___x_189_);
if (v_isSharedCheck_213_ == 0)
{
v___x_208_ = v___x_189_;
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_a_206_);
lean_dec(v___x_189_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_211_; 
if (v_isShared_209_ == 0)
{
v___x_211_ = v___x_208_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v_a_206_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
}
else
{
lean_object* v_a_214_; lean_object* v___x_216_; uint8_t v_isShared_217_; uint8_t v_isSharedCheck_221_; 
lean_dec(v_a_186_);
lean_dec_ref(v_p_177_);
lean_dec(v_d_173_);
lean_dec_ref(v_c_u2082_153_);
lean_dec_ref(v_c_u2081_151_);
lean_dec(v_x_150_);
v_a_214_ = lean_ctor_get(v___x_187_, 0);
v_isSharedCheck_221_ = !lean_is_exclusive(v___x_187_);
if (v_isSharedCheck_221_ == 0)
{
v___x_216_ = v___x_187_;
v_isShared_217_ = v_isSharedCheck_221_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_a_214_);
lean_dec(v___x_187_);
v___x_216_ = lean_box(0);
v_isShared_217_ = v_isSharedCheck_221_;
goto v_resetjp_215_;
}
v_resetjp_215_:
{
lean_object* v___x_219_; 
if (v_isShared_217_ == 0)
{
v___x_219_ = v___x_216_;
goto v_reusejp_218_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_a_214_);
v___x_219_ = v_reuseFailAlloc_220_;
goto v_reusejp_218_;
}
v_reusejp_218_:
{
return v___x_219_;
}
}
}
}
else
{
lean_object* v_a_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_229_; 
lean_dec_ref(v_p_177_);
lean_dec(v_d_173_);
lean_dec_ref(v_c_u2082_153_);
lean_dec_ref(v_c_u2081_151_);
lean_dec(v_x_150_);
v_a_222_ = lean_ctor_get(v___x_185_, 0);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_185_);
if (v_isSharedCheck_229_ == 0)
{
v___x_224_ = v___x_185_;
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_a_222_);
lean_dec(v___x_185_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_227_; 
if (v_isShared_225_ == 0)
{
v___x_227_ = v___x_224_;
goto v_reusejp_226_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_a_222_);
v___x_227_ = v_reuseFailAlloc_228_;
goto v_reusejp_226_;
}
v_reusejp_226_:
{
return v___x_227_;
}
}
}
}
}
v___jp_178_:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_179_ = lean_alloc_ctor(8, 3, 0);
lean_ctor_set(v___x_179_, 0, v_x_150_);
lean_ctor_set(v___x_179_, 1, v_c_u2081_151_);
lean_ctor_set(v___x_179_, 2, v_c_u2082_153_);
v___x_180_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_180_, 0, v_d_173_);
lean_ctor_set(v___x_180_, 1, v_p_177_);
lean_ctor_set(v___x_180_, 2, v___x_179_);
v___x_181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_181_, 0, v___x_180_);
return v___x_181_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___boxed(lean_object* v_a_230_, lean_object* v_x_231_, lean_object* v_c_u2081_232_, lean_object* v_b_233_, lean_object* v_c_u2082_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(v_a_230_, v_x_231_, v_c_u2081_232_, v_b_233_, v_c_u2082_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
lean_dec(v_a_244_);
lean_dec_ref(v_a_243_);
lean_dec(v_a_242_);
lean_dec_ref(v_a_241_);
lean_dec(v_a_240_);
lean_dec_ref(v_a_239_);
lean_dec(v_a_238_);
lean_dec_ref(v_a_237_);
lean_dec(v_a_236_);
lean_dec(v_a_235_);
lean_dec(v_b_233_);
lean_dec(v_a_230_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0(lean_object* v_cls_247_, lean_object* v_msg_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v_cls_247_, v_msg_248_, v___y_255_, v___y_256_, v___y_257_, v___y_258_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___boxed(lean_object* v_cls_261_, lean_object* v_msg_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0(v_cls_261_, v_msg_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
lean_dec(v___y_270_);
lean_dec_ref(v___y_269_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
lean_dec(v___y_264_);
lean_dec(v___y_263_);
return v_res_274_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = l_Lean_maxRecDepthErrorMessage;
v___x_281_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
return v___x_281_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3);
v___x_283_ = l_Lean_MessageData_ofFormat(v___x_282_);
return v___x_283_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
v___x_284_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4);
v___x_285_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2));
v___x_286_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_286_, 0, v___x_285_);
lean_ctor_set(v___x_286_, 1, v___x_284_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(lean_object* v_ref_287_){
_start:
{
lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; 
v___x_289_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5);
v___x_290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_290_, 0, v_ref_287_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
v___x_291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___boxed(lean_object* v_ref_292_, lean_object* v___y_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_292_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0(lean_object* v_00_u03b1_295_, lean_object* v_ref_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_296_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___boxed(lean_object* v_00_u03b1_309_, lean_object* v_ref_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0(v_00_u03b1_309_, v_ref_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
lean_dec(v___y_316_);
lean_dec_ref(v___y_315_);
lean_dec(v___y_314_);
lean_dec_ref(v___y_313_);
lean_dec(v___y_312_);
lean_dec(v___y_311_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(lean_object* v_c_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_){
_start:
{
lean_object* v_p_335_; lean_object* v_fileName_336_; lean_object* v_fileMap_337_; lean_object* v_options_338_; lean_object* v_currRecDepth_339_; lean_object* v_maxRecDepth_340_; lean_object* v_ref_341_; lean_object* v_currNamespace_342_; lean_object* v_openDecls_343_; lean_object* v_initHeartbeats_344_; lean_object* v_maxHeartbeats_345_; lean_object* v_quotContext_346_; lean_object* v_currMacroScope_347_; uint8_t v_diag_348_; lean_object* v_cancelTk_x3f_349_; uint8_t v_suppressElabErrors_350_; lean_object* v_inheritedTraceOptions_351_; uint8_t v___y_353_; lean_object* v___x_385_; uint8_t v___x_386_; uint8_t v___x_387_; 
v_p_335_ = lean_ctor_get(v_c_323_, 1);
v_fileName_336_ = lean_ctor_get(v_a_332_, 0);
lean_inc_ref(v_fileName_336_);
v_fileMap_337_ = lean_ctor_get(v_a_332_, 1);
lean_inc_ref(v_fileMap_337_);
v_options_338_ = lean_ctor_get(v_a_332_, 2);
lean_inc_ref(v_options_338_);
v_currRecDepth_339_ = lean_ctor_get(v_a_332_, 3);
lean_inc(v_currRecDepth_339_);
v_maxRecDepth_340_ = lean_ctor_get(v_a_332_, 4);
lean_inc(v_maxRecDepth_340_);
v_ref_341_ = lean_ctor_get(v_a_332_, 5);
lean_inc(v_ref_341_);
v_currNamespace_342_ = lean_ctor_get(v_a_332_, 6);
lean_inc(v_currNamespace_342_);
v_openDecls_343_ = lean_ctor_get(v_a_332_, 7);
lean_inc(v_openDecls_343_);
v_initHeartbeats_344_ = lean_ctor_get(v_a_332_, 8);
lean_inc(v_initHeartbeats_344_);
v_maxHeartbeats_345_ = lean_ctor_get(v_a_332_, 9);
lean_inc(v_maxHeartbeats_345_);
v_quotContext_346_ = lean_ctor_get(v_a_332_, 10);
lean_inc(v_quotContext_346_);
v_currMacroScope_347_ = lean_ctor_get(v_a_332_, 11);
lean_inc(v_currMacroScope_347_);
v_diag_348_ = lean_ctor_get_uint8(v_a_332_, sizeof(void*)*14);
v_cancelTk_x3f_349_ = lean_ctor_get(v_a_332_, 12);
lean_inc(v_cancelTk_x3f_349_);
v_suppressElabErrors_350_ = lean_ctor_get_uint8(v_a_332_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_351_ = lean_ctor_get(v_a_332_, 13);
lean_inc_ref(v_inheritedTraceOptions_351_);
lean_dec_ref(v_a_332_);
v___x_385_ = lean_unsigned_to_nat(0u);
v___x_386_ = lean_nat_dec_eq(v_maxRecDepth_340_, v___x_385_);
v___x_387_ = lean_bool_not(v___x_386_);
if (v___x_387_ == 0)
{
v___y_353_ = v___x_387_;
goto v___jp_352_;
}
else
{
uint8_t v___x_388_; 
v___x_388_ = lean_nat_dec_eq(v_currRecDepth_339_, v_maxRecDepth_340_);
v___y_353_ = v___x_388_;
goto v___jp_352_;
}
v___jp_352_:
{
if (v___y_353_ == 0)
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; 
v___x_354_ = lean_unsigned_to_nat(1u);
v___x_355_ = lean_nat_add(v_currRecDepth_339_, v___x_354_);
lean_dec(v_currRecDepth_339_);
v___x_356_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_356_, 0, v_fileName_336_);
lean_ctor_set(v___x_356_, 1, v_fileMap_337_);
lean_ctor_set(v___x_356_, 2, v_options_338_);
lean_ctor_set(v___x_356_, 3, v___x_355_);
lean_ctor_set(v___x_356_, 4, v_maxRecDepth_340_);
lean_ctor_set(v___x_356_, 5, v_ref_341_);
lean_ctor_set(v___x_356_, 6, v_currNamespace_342_);
lean_ctor_set(v___x_356_, 7, v_openDecls_343_);
lean_ctor_set(v___x_356_, 8, v_initHeartbeats_344_);
lean_ctor_set(v___x_356_, 9, v_maxHeartbeats_345_);
lean_ctor_set(v___x_356_, 10, v_quotContext_346_);
lean_ctor_set(v___x_356_, 11, v_currMacroScope_347_);
lean_ctor_set(v___x_356_, 12, v_cancelTk_x3f_349_);
lean_ctor_set(v___x_356_, 13, v_inheritedTraceOptions_351_);
lean_ctor_set_uint8(v___x_356_, sizeof(void*)*14, v_diag_348_);
lean_ctor_set_uint8(v___x_356_, sizeof(void*)*14 + 1, v_suppressElabErrors_350_);
lean_inc_ref(v_p_335_);
v___x_357_ = l_Int_Internal_Linear_Poly_findVarToSubst___redArg(v_p_335_, v_a_324_, v___x_356_);
if (lean_obj_tag(v___x_357_) == 0)
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_375_; 
v_a_358_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_375_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_375_ == 0)
{
v___x_360_ = v___x_357_;
v_isShared_361_ = v_isSharedCheck_375_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_357_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_375_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
if (lean_obj_tag(v_a_358_) == 1)
{
lean_object* v_val_362_; lean_object* v_snd_363_; lean_object* v_snd_364_; lean_object* v_fst_365_; lean_object* v_fst_366_; lean_object* v_p_367_; lean_object* v___x_368_; lean_object* v___x_369_; 
lean_del_object(v___x_360_);
v_val_362_ = lean_ctor_get(v_a_358_, 0);
lean_inc(v_val_362_);
lean_dec_ref_known(v_a_358_, 1);
v_snd_363_ = lean_ctor_get(v_val_362_, 1);
lean_inc(v_snd_363_);
v_snd_364_ = lean_ctor_get(v_snd_363_, 1);
lean_inc(v_snd_364_);
v_fst_365_ = lean_ctor_get(v_val_362_, 0);
lean_inc(v_fst_365_);
lean_dec(v_val_362_);
v_fst_366_ = lean_ctor_get(v_snd_363_, 0);
lean_inc(v_fst_366_);
lean_dec(v_snd_363_);
v_p_367_ = lean_ctor_get(v_snd_364_, 0);
v___x_368_ = l_Int_Internal_Linear_Poly_coeff(v_p_367_, v_fst_366_);
v___x_369_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(v___x_368_, v_fst_366_, v_snd_364_, v_fst_365_, v_c_323_, v_a_324_, v_a_325_, v_a_326_, v_a_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v___x_356_, v_a_333_);
lean_dec(v_fst_365_);
lean_dec(v___x_368_);
if (lean_obj_tag(v___x_369_) == 0)
{
lean_object* v_a_370_; 
v_a_370_ = lean_ctor_get(v___x_369_, 0);
lean_inc(v_a_370_);
lean_dec_ref_known(v___x_369_, 1);
v_c_323_ = v_a_370_;
v_a_332_ = v___x_356_;
goto _start;
}
else
{
lean_dec_ref_known(v___x_356_, 14);
return v___x_369_;
}
}
else
{
lean_object* v___x_373_; 
lean_dec(v_a_358_);
lean_dec_ref_known(v___x_356_, 14);
if (v_isShared_361_ == 0)
{
lean_ctor_set(v___x_360_, 0, v_c_323_);
v___x_373_ = v___x_360_;
goto v_reusejp_372_;
}
else
{
lean_object* v_reuseFailAlloc_374_; 
v_reuseFailAlloc_374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_374_, 0, v_c_323_);
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
else
{
lean_object* v_a_376_; lean_object* v___x_378_; uint8_t v_isShared_379_; uint8_t v_isSharedCheck_383_; 
lean_dec_ref_known(v___x_356_, 14);
lean_dec_ref(v_c_323_);
v_a_376_ = lean_ctor_get(v___x_357_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_357_);
if (v_isSharedCheck_383_ == 0)
{
v___x_378_ = v___x_357_;
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
else
{
lean_inc(v_a_376_);
lean_dec(v___x_357_);
v___x_378_ = lean_box(0);
v_isShared_379_ = v_isSharedCheck_383_;
goto v_resetjp_377_;
}
v_resetjp_377_:
{
lean_object* v___x_381_; 
if (v_isShared_379_ == 0)
{
v___x_381_ = v___x_378_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v_a_376_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
}
else
{
lean_object* v___x_384_; 
lean_dec_ref(v_inheritedTraceOptions_351_);
lean_dec(v_cancelTk_x3f_349_);
lean_dec(v_currMacroScope_347_);
lean_dec(v_quotContext_346_);
lean_dec(v_maxHeartbeats_345_);
lean_dec(v_initHeartbeats_344_);
lean_dec(v_openDecls_343_);
lean_dec(v_currNamespace_342_);
lean_dec(v_maxRecDepth_340_);
lean_dec(v_currRecDepth_339_);
lean_dec_ref(v_options_338_);
lean_dec_ref(v_fileMap_337_);
lean_dec_ref(v_fileName_336_);
lean_dec_ref(v_c_323_);
v___x_384_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_341_);
return v___x_384_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___boxed(lean_object* v_c_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(v_c_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_, v_a_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_);
lean_dec(v_a_399_);
lean_dec(v_a_397_);
lean_dec_ref(v_a_396_);
lean_dec(v_a_395_);
lean_dec_ref(v_a_394_);
lean_dec(v_a_393_);
lean_dec_ref(v_a_392_);
lean_dec(v_a_391_);
lean_dec(v_a_390_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(lean_object* v_a_402_, lean_object* v_v_403_, lean_object* v_s_404_){
_start:
{
lean_object* v_vars_405_; lean_object* v_varMap_406_; lean_object* v_vars_x27_407_; lean_object* v_varMap_x27_408_; lean_object* v_natToIntMap_409_; lean_object* v_natDef_410_; lean_object* v_dvds_411_; lean_object* v_lowers_412_; lean_object* v_uppers_413_; lean_object* v_diseqs_414_; lean_object* v_elimEqs_415_; lean_object* v_elimStack_416_; lean_object* v_occurs_417_; lean_object* v_assignment_418_; lean_object* v_nextCnstrId_419_; uint8_t v_caseSplits_420_; lean_object* v_conflict_x3f_421_; lean_object* v_diseqSplits_422_; lean_object* v_divMod_423_; lean_object* v_toIntIds_424_; lean_object* v_toIntInfos_425_; lean_object* v_toIntTermMap_426_; lean_object* v_toIntVarMap_427_; uint8_t v_usedCommRing_428_; lean_object* v_nonlinearOccs_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_438_; 
v_vars_405_ = lean_ctor_get(v_s_404_, 0);
v_varMap_406_ = lean_ctor_get(v_s_404_, 1);
v_vars_x27_407_ = lean_ctor_get(v_s_404_, 2);
v_varMap_x27_408_ = lean_ctor_get(v_s_404_, 3);
v_natToIntMap_409_ = lean_ctor_get(v_s_404_, 4);
v_natDef_410_ = lean_ctor_get(v_s_404_, 5);
v_dvds_411_ = lean_ctor_get(v_s_404_, 6);
v_lowers_412_ = lean_ctor_get(v_s_404_, 7);
v_uppers_413_ = lean_ctor_get(v_s_404_, 8);
v_diseqs_414_ = lean_ctor_get(v_s_404_, 9);
v_elimEqs_415_ = lean_ctor_get(v_s_404_, 10);
v_elimStack_416_ = lean_ctor_get(v_s_404_, 11);
v_occurs_417_ = lean_ctor_get(v_s_404_, 12);
v_assignment_418_ = lean_ctor_get(v_s_404_, 13);
v_nextCnstrId_419_ = lean_ctor_get(v_s_404_, 14);
v_caseSplits_420_ = lean_ctor_get_uint8(v_s_404_, sizeof(void*)*23);
v_conflict_x3f_421_ = lean_ctor_get(v_s_404_, 15);
v_diseqSplits_422_ = lean_ctor_get(v_s_404_, 16);
v_divMod_423_ = lean_ctor_get(v_s_404_, 17);
v_toIntIds_424_ = lean_ctor_get(v_s_404_, 18);
v_toIntInfos_425_ = lean_ctor_get(v_s_404_, 19);
v_toIntTermMap_426_ = lean_ctor_get(v_s_404_, 20);
v_toIntVarMap_427_ = lean_ctor_get(v_s_404_, 21);
v_usedCommRing_428_ = lean_ctor_get_uint8(v_s_404_, sizeof(void*)*23 + 1);
v_nonlinearOccs_429_ = lean_ctor_get(v_s_404_, 22);
v_isSharedCheck_438_ = !lean_is_exclusive(v_s_404_);
if (v_isSharedCheck_438_ == 0)
{
v___x_431_ = v_s_404_;
v_isShared_432_ = v_isSharedCheck_438_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_nonlinearOccs_429_);
lean_inc(v_toIntVarMap_427_);
lean_inc(v_toIntTermMap_426_);
lean_inc(v_toIntInfos_425_);
lean_inc(v_toIntIds_424_);
lean_inc(v_divMod_423_);
lean_inc(v_diseqSplits_422_);
lean_inc(v_conflict_x3f_421_);
lean_inc(v_nextCnstrId_419_);
lean_inc(v_assignment_418_);
lean_inc(v_occurs_417_);
lean_inc(v_elimStack_416_);
lean_inc(v_elimEqs_415_);
lean_inc(v_diseqs_414_);
lean_inc(v_uppers_413_);
lean_inc(v_lowers_412_);
lean_inc(v_dvds_411_);
lean_inc(v_natDef_410_);
lean_inc(v_natToIntMap_409_);
lean_inc(v_varMap_x27_408_);
lean_inc(v_vars_x27_407_);
lean_inc(v_varMap_406_);
lean_inc(v_vars_405_);
lean_dec(v_s_404_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_438_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_436_; 
v___x_433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_433_, 0, v_a_402_);
v___x_434_ = l_Lean_PersistentArray_set___redArg(v_dvds_411_, v_v_403_, v___x_433_);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 6, v___x_434_);
v___x_436_ = v___x_431_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_437_; 
v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_437_, 0, v_vars_405_);
lean_ctor_set(v_reuseFailAlloc_437_, 1, v_varMap_406_);
lean_ctor_set(v_reuseFailAlloc_437_, 2, v_vars_x27_407_);
lean_ctor_set(v_reuseFailAlloc_437_, 3, v_varMap_x27_408_);
lean_ctor_set(v_reuseFailAlloc_437_, 4, v_natToIntMap_409_);
lean_ctor_set(v_reuseFailAlloc_437_, 5, v_natDef_410_);
lean_ctor_set(v_reuseFailAlloc_437_, 6, v___x_434_);
lean_ctor_set(v_reuseFailAlloc_437_, 7, v_lowers_412_);
lean_ctor_set(v_reuseFailAlloc_437_, 8, v_uppers_413_);
lean_ctor_set(v_reuseFailAlloc_437_, 9, v_diseqs_414_);
lean_ctor_set(v_reuseFailAlloc_437_, 10, v_elimEqs_415_);
lean_ctor_set(v_reuseFailAlloc_437_, 11, v_elimStack_416_);
lean_ctor_set(v_reuseFailAlloc_437_, 12, v_occurs_417_);
lean_ctor_set(v_reuseFailAlloc_437_, 13, v_assignment_418_);
lean_ctor_set(v_reuseFailAlloc_437_, 14, v_nextCnstrId_419_);
lean_ctor_set(v_reuseFailAlloc_437_, 15, v_conflict_x3f_421_);
lean_ctor_set(v_reuseFailAlloc_437_, 16, v_diseqSplits_422_);
lean_ctor_set(v_reuseFailAlloc_437_, 17, v_divMod_423_);
lean_ctor_set(v_reuseFailAlloc_437_, 18, v_toIntIds_424_);
lean_ctor_set(v_reuseFailAlloc_437_, 19, v_toIntInfos_425_);
lean_ctor_set(v_reuseFailAlloc_437_, 20, v_toIntTermMap_426_);
lean_ctor_set(v_reuseFailAlloc_437_, 21, v_toIntVarMap_427_);
lean_ctor_set(v_reuseFailAlloc_437_, 22, v_nonlinearOccs_429_);
lean_ctor_set_uint8(v_reuseFailAlloc_437_, sizeof(void*)*23, v_caseSplits_420_);
lean_ctor_set_uint8(v_reuseFailAlloc_437_, sizeof(void*)*23 + 1, v_usedCommRing_428_);
v___x_436_ = v_reuseFailAlloc_437_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
return v___x_436_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed(lean_object* v_a_439_, lean_object* v_v_440_, lean_object* v_s_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(v_a_439_, v_v_440_, v_s_441_);
lean_dec(v_v_440_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(lean_object* v_v_443_, lean_object* v_s_444_){
_start:
{
lean_object* v_vars_445_; lean_object* v_varMap_446_; lean_object* v_vars_x27_447_; lean_object* v_varMap_x27_448_; lean_object* v_natToIntMap_449_; lean_object* v_natDef_450_; lean_object* v_dvds_451_; lean_object* v_lowers_452_; lean_object* v_uppers_453_; lean_object* v_diseqs_454_; lean_object* v_elimEqs_455_; lean_object* v_elimStack_456_; lean_object* v_occurs_457_; lean_object* v_assignment_458_; lean_object* v_nextCnstrId_459_; uint8_t v_caseSplits_460_; lean_object* v_conflict_x3f_461_; lean_object* v_diseqSplits_462_; lean_object* v_divMod_463_; lean_object* v_toIntIds_464_; lean_object* v_toIntInfos_465_; lean_object* v_toIntTermMap_466_; lean_object* v_toIntVarMap_467_; uint8_t v_usedCommRing_468_; lean_object* v_nonlinearOccs_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_478_; 
v_vars_445_ = lean_ctor_get(v_s_444_, 0);
v_varMap_446_ = lean_ctor_get(v_s_444_, 1);
v_vars_x27_447_ = lean_ctor_get(v_s_444_, 2);
v_varMap_x27_448_ = lean_ctor_get(v_s_444_, 3);
v_natToIntMap_449_ = lean_ctor_get(v_s_444_, 4);
v_natDef_450_ = lean_ctor_get(v_s_444_, 5);
v_dvds_451_ = lean_ctor_get(v_s_444_, 6);
v_lowers_452_ = lean_ctor_get(v_s_444_, 7);
v_uppers_453_ = lean_ctor_get(v_s_444_, 8);
v_diseqs_454_ = lean_ctor_get(v_s_444_, 9);
v_elimEqs_455_ = lean_ctor_get(v_s_444_, 10);
v_elimStack_456_ = lean_ctor_get(v_s_444_, 11);
v_occurs_457_ = lean_ctor_get(v_s_444_, 12);
v_assignment_458_ = lean_ctor_get(v_s_444_, 13);
v_nextCnstrId_459_ = lean_ctor_get(v_s_444_, 14);
v_caseSplits_460_ = lean_ctor_get_uint8(v_s_444_, sizeof(void*)*23);
v_conflict_x3f_461_ = lean_ctor_get(v_s_444_, 15);
v_diseqSplits_462_ = lean_ctor_get(v_s_444_, 16);
v_divMod_463_ = lean_ctor_get(v_s_444_, 17);
v_toIntIds_464_ = lean_ctor_get(v_s_444_, 18);
v_toIntInfos_465_ = lean_ctor_get(v_s_444_, 19);
v_toIntTermMap_466_ = lean_ctor_get(v_s_444_, 20);
v_toIntVarMap_467_ = lean_ctor_get(v_s_444_, 21);
v_usedCommRing_468_ = lean_ctor_get_uint8(v_s_444_, sizeof(void*)*23 + 1);
v_nonlinearOccs_469_ = lean_ctor_get(v_s_444_, 22);
v_isSharedCheck_478_ = !lean_is_exclusive(v_s_444_);
if (v_isSharedCheck_478_ == 0)
{
v___x_471_ = v_s_444_;
v_isShared_472_ = v_isSharedCheck_478_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_nonlinearOccs_469_);
lean_inc(v_toIntVarMap_467_);
lean_inc(v_toIntTermMap_466_);
lean_inc(v_toIntInfos_465_);
lean_inc(v_toIntIds_464_);
lean_inc(v_divMod_463_);
lean_inc(v_diseqSplits_462_);
lean_inc(v_conflict_x3f_461_);
lean_inc(v_nextCnstrId_459_);
lean_inc(v_assignment_458_);
lean_inc(v_occurs_457_);
lean_inc(v_elimStack_456_);
lean_inc(v_elimEqs_455_);
lean_inc(v_diseqs_454_);
lean_inc(v_uppers_453_);
lean_inc(v_lowers_452_);
lean_inc(v_dvds_451_);
lean_inc(v_natDef_450_);
lean_inc(v_natToIntMap_449_);
lean_inc(v_varMap_x27_448_);
lean_inc(v_vars_x27_447_);
lean_inc(v_varMap_446_);
lean_inc(v_vars_445_);
lean_dec(v_s_444_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_478_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_476_; 
v___x_473_ = lean_box(0);
v___x_474_ = l_Lean_PersistentArray_set___redArg(v_dvds_451_, v_v_443_, v___x_473_);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 6, v___x_474_);
v___x_476_ = v___x_471_;
goto v_reusejp_475_;
}
else
{
lean_object* v_reuseFailAlloc_477_; 
v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_477_, 0, v_vars_445_);
lean_ctor_set(v_reuseFailAlloc_477_, 1, v_varMap_446_);
lean_ctor_set(v_reuseFailAlloc_477_, 2, v_vars_x27_447_);
lean_ctor_set(v_reuseFailAlloc_477_, 3, v_varMap_x27_448_);
lean_ctor_set(v_reuseFailAlloc_477_, 4, v_natToIntMap_449_);
lean_ctor_set(v_reuseFailAlloc_477_, 5, v_natDef_450_);
lean_ctor_set(v_reuseFailAlloc_477_, 6, v___x_474_);
lean_ctor_set(v_reuseFailAlloc_477_, 7, v_lowers_452_);
lean_ctor_set(v_reuseFailAlloc_477_, 8, v_uppers_453_);
lean_ctor_set(v_reuseFailAlloc_477_, 9, v_diseqs_454_);
lean_ctor_set(v_reuseFailAlloc_477_, 10, v_elimEqs_455_);
lean_ctor_set(v_reuseFailAlloc_477_, 11, v_elimStack_456_);
lean_ctor_set(v_reuseFailAlloc_477_, 12, v_occurs_457_);
lean_ctor_set(v_reuseFailAlloc_477_, 13, v_assignment_458_);
lean_ctor_set(v_reuseFailAlloc_477_, 14, v_nextCnstrId_459_);
lean_ctor_set(v_reuseFailAlloc_477_, 15, v_conflict_x3f_461_);
lean_ctor_set(v_reuseFailAlloc_477_, 16, v_diseqSplits_462_);
lean_ctor_set(v_reuseFailAlloc_477_, 17, v_divMod_463_);
lean_ctor_set(v_reuseFailAlloc_477_, 18, v_toIntIds_464_);
lean_ctor_set(v_reuseFailAlloc_477_, 19, v_toIntInfos_465_);
lean_ctor_set(v_reuseFailAlloc_477_, 20, v_toIntTermMap_466_);
lean_ctor_set(v_reuseFailAlloc_477_, 21, v_toIntVarMap_467_);
lean_ctor_set(v_reuseFailAlloc_477_, 22, v_nonlinearOccs_469_);
lean_ctor_set_uint8(v_reuseFailAlloc_477_, sizeof(void*)*23, v_caseSplits_460_);
lean_ctor_set_uint8(v_reuseFailAlloc_477_, sizeof(void*)*23 + 1, v_usedCommRing_468_);
v___x_476_ = v_reuseFailAlloc_477_;
goto v_reusejp_475_;
}
v_reusejp_475_:
{
return v___x_476_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed(lean_object* v_v_479_, lean_object* v_s_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(v_v_479_, v_s_480_);
lean_dec(v_v_479_);
return v_res_481_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5(void){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; 
v___x_490_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4));
v___x_491_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
v___x_492_ = l_Lean_Name_append(v___x_491_, v___x_490_);
return v___x_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(lean_object* v_c_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_, lean_object* v_a_499_, lean_object* v_a_500_, lean_object* v_a_501_, lean_object* v_a_502_, lean_object* v_a_503_){
_start:
{
lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___y_527_; lean_object* v___y_528_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v___y_536_; lean_object* v___y_537_; lean_object* v___y_538_; lean_object* v___y_539_; lean_object* v___y_540_; lean_object* v___y_541_; lean_object* v___y_622_; lean_object* v___y_623_; lean_object* v___y_624_; lean_object* v___y_625_; lean_object* v___y_626_; lean_object* v___y_627_; lean_object* v___y_628_; lean_object* v___y_629_; lean_object* v___y_630_; lean_object* v___y_631_; lean_object* v___y_632_; lean_object* v___y_633_; lean_object* v___y_634_; lean_object* v___y_635_; lean_object* v___y_636_; lean_object* v___y_637_; lean_object* v___y_638_; lean_object* v___y_639_; lean_object* v___y_640_; lean_object* v___y_641_; lean_object* v___y_642_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_666_; lean_object* v___y_667_; lean_object* v___y_668_; lean_object* v___y_669_; lean_object* v___y_670_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v_fileName_769_; lean_object* v_fileMap_770_; lean_object* v_options_771_; lean_object* v_currRecDepth_772_; lean_object* v_maxRecDepth_773_; lean_object* v_ref_774_; lean_object* v_currNamespace_775_; lean_object* v_openDecls_776_; lean_object* v_initHeartbeats_777_; lean_object* v_maxHeartbeats_778_; lean_object* v_quotContext_779_; lean_object* v_currMacroScope_780_; uint8_t v_diag_781_; lean_object* v_cancelTk_x3f_782_; uint8_t v_suppressElabErrors_783_; lean_object* v_inheritedTraceOptions_784_; uint8_t v___y_786_; lean_object* v___x_828_; uint8_t v___x_829_; uint8_t v___x_830_; 
v_fileName_769_ = lean_ctor_get(v_a_502_, 0);
lean_inc_ref(v_fileName_769_);
v_fileMap_770_ = lean_ctor_get(v_a_502_, 1);
lean_inc_ref(v_fileMap_770_);
v_options_771_ = lean_ctor_get(v_a_502_, 2);
lean_inc_ref(v_options_771_);
v_currRecDepth_772_ = lean_ctor_get(v_a_502_, 3);
lean_inc(v_currRecDepth_772_);
v_maxRecDepth_773_ = lean_ctor_get(v_a_502_, 4);
lean_inc(v_maxRecDepth_773_);
v_ref_774_ = lean_ctor_get(v_a_502_, 5);
lean_inc(v_ref_774_);
v_currNamespace_775_ = lean_ctor_get(v_a_502_, 6);
lean_inc(v_currNamespace_775_);
v_openDecls_776_ = lean_ctor_get(v_a_502_, 7);
lean_inc(v_openDecls_776_);
v_initHeartbeats_777_ = lean_ctor_get(v_a_502_, 8);
lean_inc(v_initHeartbeats_777_);
v_maxHeartbeats_778_ = lean_ctor_get(v_a_502_, 9);
lean_inc(v_maxHeartbeats_778_);
v_quotContext_779_ = lean_ctor_get(v_a_502_, 10);
lean_inc(v_quotContext_779_);
v_currMacroScope_780_ = lean_ctor_get(v_a_502_, 11);
lean_inc(v_currMacroScope_780_);
v_diag_781_ = lean_ctor_get_uint8(v_a_502_, sizeof(void*)*14);
v_cancelTk_x3f_782_ = lean_ctor_get(v_a_502_, 12);
lean_inc(v_cancelTk_x3f_782_);
v_suppressElabErrors_783_ = lean_ctor_get_uint8(v_a_502_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_784_ = lean_ctor_get(v_a_502_, 13);
lean_inc_ref(v_inheritedTraceOptions_784_);
lean_dec_ref(v_a_502_);
v___x_828_ = lean_unsigned_to_nat(0u);
v___x_829_ = lean_nat_dec_eq(v_maxRecDepth_773_, v___x_828_);
v___x_830_ = lean_bool_not(v___x_829_);
if (v___x_830_ == 0)
{
v___y_786_ = v___x_830_;
goto v___jp_785_;
}
else
{
uint8_t v___x_831_; 
v___x_831_ = lean_nat_dec_eq(v_currRecDepth_772_, v_maxRecDepth_773_);
v___y_786_ = v___x_831_;
goto v___jp_785_;
}
v___jp_505_:
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = lean_box(0);
v___x_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_507_, 0, v___x_506_);
return v___x_507_;
}
v___jp_508_:
{
lean_object* v___x_516_; 
v___x_516_ = l_Int_Internal_Linear_Poly_updateOccs___redArg(v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
lean_dec_ref(v___y_514_);
if (lean_obj_tag(v___x_516_) == 0)
{
lean_object* v___x_517_; lean_object* v___x_518_; 
lean_dec_ref_known(v___x_516_, 1);
v___x_517_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_518_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_517_, v___y_509_, v___y_511_);
return v___x_518_;
}
else
{
lean_dec_ref(v___y_509_);
return v___x_516_;
}
}
v___jp_519_:
{
if (lean_obj_tag(v___y_541_) == 1)
{
lean_object* v_val_542_; lean_object* v_p_543_; 
lean_dec_ref(v___y_529_);
lean_dec_ref(v___y_521_);
v_val_542_ = lean_ctor_get(v___y_541_, 0);
lean_inc(v_val_542_);
lean_dec_ref_known(v___y_541_, 1);
v_p_543_ = lean_ctor_get(v_val_542_, 1);
lean_inc_ref(v_p_543_);
if (lean_obj_tag(v_p_543_) == 1)
{
lean_object* v_d_544_; lean_object* v_k_545_; lean_object* v_p_546_; lean_object* v___x_548_; uint8_t v_isShared_549_; uint8_t v_isSharedCheck_599_; 
v_d_544_ = lean_ctor_get(v_val_542_, 0);
v_k_545_ = lean_ctor_get(v_p_543_, 0);
v_p_546_ = lean_ctor_get(v_p_543_, 2);
v_isSharedCheck_599_ = !lean_is_exclusive(v_p_543_);
if (v_isSharedCheck_599_ == 0)
{
lean_object* v_unused_600_; 
v_unused_600_ = lean_ctor_get(v_p_543_, 1);
lean_dec(v_unused_600_);
v___x_548_ = v_p_543_;
v_isShared_549_ = v_isSharedCheck_599_;
goto v_resetjp_547_;
}
else
{
lean_inc(v_p_546_);
lean_inc(v_k_545_);
lean_dec(v_p_543_);
v___x_548_ = lean_box(0);
v_isShared_549_ = v_isSharedCheck_599_;
goto v_resetjp_547_;
}
v_resetjp_547_:
{
lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v_snd_553_; lean_object* v_fst_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_598_; 
v___x_550_ = lean_int_mul(v___y_537_, v_d_544_);
v___x_551_ = lean_int_mul(v_k_545_, v___y_533_);
v___x_552_ = l_Lean_Meta_Grind_Arith_gcdExt(v___x_550_, v___x_551_);
lean_dec(v___x_551_);
lean_dec(v___x_550_);
v_snd_553_ = lean_ctor_get(v___x_552_, 1);
v_fst_554_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_598_ == 0)
{
v___x_556_ = v___x_552_;
v_isShared_557_ = v_isSharedCheck_598_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_snd_553_);
lean_inc(v_fst_554_);
lean_dec(v___x_552_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_598_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v_fst_558_; lean_object* v_snd_559_; lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_597_; 
v_fst_558_ = lean_ctor_get(v_snd_553_, 0);
v_snd_559_ = lean_ctor_get(v_snd_553_, 1);
v_isSharedCheck_597_ = !lean_is_exclusive(v_snd_553_);
if (v_isSharedCheck_597_ == 0)
{
v___x_561_ = v_snd_553_;
v_isShared_562_ = v_isSharedCheck_597_;
goto v_resetjp_560_;
}
else
{
lean_inc(v_snd_559_);
lean_inc(v_fst_558_);
lean_dec(v_snd_553_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_597_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_563_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_564_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_563_, v___y_526_, v___y_528_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_572_; 
lean_dec_ref_known(v___x_564_, 1);
v___x_565_ = lean_int_mul(v_fst_558_, v_d_544_);
lean_dec(v_fst_558_);
lean_inc_ref(v___y_527_);
v___x_566_ = l_Int_Internal_Linear_Poly_mul(v___y_527_, v___x_565_);
lean_dec(v___x_565_);
v___x_567_ = lean_int_mul(v_snd_559_, v___y_533_);
lean_dec(v_snd_559_);
lean_inc_ref(v_p_546_);
v___x_568_ = l_Int_Internal_Linear_Poly_mul(v_p_546_, v___x_567_);
lean_dec(v___x_567_);
v___x_569_ = lean_int_mul(v___y_533_, v_d_544_);
lean_dec(v___y_533_);
v___x_570_ = l_Int_Internal_Linear_Poly_combine(v___x_566_, v___x_568_);
lean_inc(v_fst_554_);
if (v_isShared_549_ == 0)
{
lean_ctor_set(v___x_548_, 2, v___x_570_);
lean_ctor_set(v___x_548_, 1, v___y_532_);
lean_ctor_set(v___x_548_, 0, v_fst_554_);
v___x_572_ = v___x_548_;
goto v_reusejp_571_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_fst_554_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v___y_532_);
lean_ctor_set(v_reuseFailAlloc_596_, 2, v___x_570_);
v___x_572_ = v_reuseFailAlloc_596_;
goto v_reusejp_571_;
}
v_reusejp_571_:
{
lean_object* v___x_574_; 
lean_inc(v_val_542_);
lean_inc_ref(v___y_538_);
if (v_isShared_562_ == 0)
{
lean_ctor_set_tag(v___x_561_, 4);
lean_ctor_set(v___x_561_, 1, v_val_542_);
lean_ctor_set(v___x_561_, 0, v___y_538_);
v___x_574_ = v___x_561_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___y_538_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v_val_542_);
v___x_574_ = v_reuseFailAlloc_595_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_575_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_575_, 0, v___x_569_);
lean_ctor_set(v___x_575_, 1, v___x_572_);
lean_ctor_set(v___x_575_, 2, v___x_574_);
lean_inc_ref(v___y_520_);
v___x_576_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v___x_575_, v___y_528_, v___y_534_, v___y_522_, v___y_540_, v___y_523_, v___y_525_, v___y_539_, v___y_531_, v___y_520_, v___y_535_);
if (lean_obj_tag(v___x_576_) == 0)
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_582_; 
lean_dec_ref_known(v___x_576_, 1);
v___x_577_ = l_Int_Internal_Linear_Poly_mul(v___y_527_, v_k_545_);
lean_dec(v_k_545_);
v___x_578_ = lean_int_neg(v___y_537_);
lean_dec(v___y_537_);
v___x_579_ = l_Int_Internal_Linear_Poly_mul(v_p_546_, v___x_578_);
lean_dec(v___x_578_);
v___x_580_ = l_Int_Internal_Linear_Poly_combine(v___x_577_, v___x_579_);
lean_inc(v_val_542_);
if (v_isShared_557_ == 0)
{
lean_ctor_set_tag(v___x_556_, 5);
lean_ctor_set(v___x_556_, 1, v_val_542_);
lean_ctor_set(v___x_556_, 0, v___y_538_);
v___x_582_ = v___x_556_;
goto v_reusejp_581_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___y_538_);
lean_ctor_set(v_reuseFailAlloc_594_, 1, v_val_542_);
v___x_582_ = v_reuseFailAlloc_594_;
goto v_reusejp_581_;
}
v_reusejp_581_:
{
lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_590_; 
v_isSharedCheck_590_ = !lean_is_exclusive(v_val_542_);
if (v_isSharedCheck_590_ == 0)
{
lean_object* v_unused_591_; lean_object* v_unused_592_; lean_object* v_unused_593_; 
v_unused_591_ = lean_ctor_get(v_val_542_, 2);
lean_dec(v_unused_591_);
v_unused_592_ = lean_ctor_get(v_val_542_, 1);
lean_dec(v_unused_592_);
v_unused_593_ = lean_ctor_get(v_val_542_, 0);
lean_dec(v_unused_593_);
v___x_584_ = v_val_542_;
v_isShared_585_ = v_isSharedCheck_590_;
goto v_resetjp_583_;
}
else
{
lean_dec(v_val_542_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_590_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_587_; 
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 2, v___x_582_);
lean_ctor_set(v___x_584_, 1, v___x_580_);
lean_ctor_set(v___x_584_, 0, v_fst_554_);
v___x_587_ = v___x_584_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_fst_554_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v___x_580_);
lean_ctor_set(v_reuseFailAlloc_589_, 2, v___x_582_);
v___x_587_ = v_reuseFailAlloc_589_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
v_c_493_ = v___x_587_;
v_a_494_ = v___y_528_;
v_a_495_ = v___y_534_;
v_a_496_ = v___y_522_;
v_a_497_ = v___y_540_;
v_a_498_ = v___y_523_;
v_a_499_ = v___y_525_;
v_a_500_ = v___y_539_;
v_a_501_ = v___y_531_;
v_a_502_ = v___y_520_;
v_a_503_ = v___y_535_;
goto _start;
}
}
}
}
else
{
lean_del_object(v___x_556_);
lean_dec(v_fst_554_);
lean_dec_ref(v_p_546_);
lean_dec(v_k_545_);
lean_dec(v_val_542_);
lean_dec_ref(v___y_538_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_527_);
lean_dec_ref(v___y_520_);
return v___x_576_;
}
}
}
}
else
{
lean_del_object(v___x_561_);
lean_dec(v_snd_559_);
lean_dec(v_fst_558_);
lean_del_object(v___x_556_);
lean_dec(v_fst_554_);
lean_del_object(v___x_548_);
lean_dec_ref(v_p_546_);
lean_dec(v_k_545_);
lean_dec(v_val_542_);
lean_dec_ref(v___y_538_);
lean_dec(v___y_537_);
lean_dec(v___y_533_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_527_);
lean_dec_ref(v___y_520_);
return v___x_564_;
}
}
}
}
}
else
{
lean_object* v___x_601_; 
lean_dec_ref(v_p_543_);
lean_dec_ref(v___y_538_);
lean_dec(v___y_537_);
lean_dec(v___y_533_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_527_);
lean_dec_ref(v___y_526_);
v___x_601_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_val_542_, v___y_528_, v___y_534_, v___y_522_, v___y_540_, v___y_523_, v___y_525_, v___y_539_, v___y_531_, v___y_520_, v___y_535_);
lean_dec_ref(v___y_520_);
return v___x_601_;
}
}
else
{
lean_object* v_options_602_; uint8_t v_hasTrace_603_; 
lean_dec(v___y_541_);
lean_dec(v___y_537_);
lean_dec(v___y_533_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_527_);
lean_dec_ref(v___y_526_);
v_options_602_ = lean_ctor_get(v___y_520_, 2);
v_hasTrace_603_ = lean_ctor_get_uint8(v_options_602_, sizeof(void*)*1);
if (v_hasTrace_603_ == 0)
{
lean_dec_ref(v___y_538_);
v___y_509_ = v___y_529_;
v___y_510_ = v___y_521_;
v___y_511_ = v___y_528_;
v___y_512_ = v___y_539_;
v___y_513_ = v___y_531_;
v___y_514_ = v___y_520_;
v___y_515_ = v___y_535_;
goto v___jp_508_;
}
else
{
lean_object* v_inheritedTraceOptions_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; uint8_t v___x_609_; 
v_inheritedTraceOptions_604_ = lean_ctor_get(v___y_520_, 13);
v___x_605_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0));
lean_inc_ref(v___y_530_);
lean_inc_ref(v___y_524_);
lean_inc_ref(v___y_536_);
v___x_606_ = l_Lean_Name_mkStr4(v___y_536_, v___y_524_, v___y_530_, v___x_605_);
v___x_607_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
lean_inc(v___x_606_);
v___x_608_ = l_Lean_Name_append(v___x_607_, v___x_606_);
v___x_609_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_604_, v_options_602_, v___x_608_);
lean_dec(v___x_608_);
if (v___x_609_ == 0)
{
lean_dec(v___x_606_);
lean_dec_ref(v___y_538_);
v___y_509_ = v___y_529_;
v___y_510_ = v___y_521_;
v___y_511_ = v___y_528_;
v___y_512_ = v___y_539_;
v___y_513_ = v___y_531_;
v___y_514_ = v___y_520_;
v___y_515_ = v___y_535_;
goto v___jp_508_;
}
else
{
lean_object* v___x_610_; 
v___x_610_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v___y_538_, v___y_528_, v___y_520_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v_a_611_; lean_object* v___x_612_; 
v_a_611_ = lean_ctor_get(v___x_610_, 0);
lean_inc(v_a_611_);
lean_dec_ref_known(v___x_610_, 1);
v___x_612_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_606_, v_a_611_, v___y_539_, v___y_531_, v___y_520_, v___y_535_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_dec_ref_known(v___x_612_, 1);
v___y_509_ = v___y_529_;
v___y_510_ = v___y_521_;
v___y_511_ = v___y_528_;
v___y_512_ = v___y_539_;
v___y_513_ = v___y_531_;
v___y_514_ = v___y_520_;
v___y_515_ = v___y_535_;
goto v___jp_508_;
}
else
{
lean_dec_ref(v___y_529_);
lean_dec_ref(v___y_521_);
lean_dec_ref(v___y_520_);
return v___x_612_;
}
}
else
{
lean_object* v_a_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_620_; 
lean_dec(v___x_606_);
lean_dec_ref(v___y_529_);
lean_dec_ref(v___y_521_);
lean_dec_ref(v___y_520_);
v_a_613_ = lean_ctor_get(v___x_610_, 0);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_610_);
if (v_isSharedCheck_620_ == 0)
{
v___x_615_ = v___x_610_;
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_a_613_);
lean_dec(v___x_610_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_620_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_618_; 
if (v_isShared_616_ == 0)
{
v___x_618_ = v___x_615_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_a_613_);
v___x_618_ = v_reuseFailAlloc_619_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
return v___x_618_;
}
}
}
}
}
}
}
v___jp_621_:
{
lean_object* v___x_643_; 
v___x_643_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v___y_633_, v___y_641_);
if (lean_obj_tag(v___x_643_) == 0)
{
lean_object* v_a_644_; lean_object* v_dvds_645_; lean_object* v_size_646_; lean_object* v___x_647_; uint8_t v___x_648_; 
v_a_644_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_a_644_);
lean_dec_ref_known(v___x_643_, 1);
v_dvds_645_ = lean_ctor_get(v_a_644_, 6);
lean_inc_ref(v_dvds_645_);
lean_dec(v_a_644_);
v_size_646_ = lean_ctor_get(v_dvds_645_, 2);
v___x_647_ = lean_box(0);
v___x_648_ = lean_nat_dec_lt(v___y_625_, v_size_646_);
if (v___x_648_ == 0)
{
lean_object* v___x_649_; 
lean_dec_ref(v_dvds_645_);
v___x_649_ = l_outOfBounds___redArg(v___x_647_);
v___y_520_ = v___y_641_;
v___y_521_ = v___y_624_;
v___y_522_ = v___y_635_;
v___y_523_ = v___y_637_;
v___y_524_ = v___y_626_;
v___y_525_ = v___y_638_;
v___y_526_ = v___y_628_;
v___y_527_ = v___y_631_;
v___y_528_ = v___y_633_;
v___y_529_ = v___y_622_;
v___y_530_ = v___y_623_;
v___y_531_ = v___y_640_;
v___y_532_ = v___y_625_;
v___y_533_ = v___y_627_;
v___y_534_ = v___y_634_;
v___y_535_ = v___y_642_;
v___y_536_ = v___y_630_;
v___y_537_ = v___y_629_;
v___y_538_ = v___y_632_;
v___y_539_ = v___y_639_;
v___y_540_ = v___y_636_;
v___y_541_ = v___x_649_;
goto v___jp_519_;
}
else
{
lean_object* v___x_650_; 
v___x_650_ = l_Lean_PersistentArray_get_x21___redArg(v___x_647_, v_dvds_645_, v___y_625_);
lean_dec_ref(v_dvds_645_);
v___y_520_ = v___y_641_;
v___y_521_ = v___y_624_;
v___y_522_ = v___y_635_;
v___y_523_ = v___y_637_;
v___y_524_ = v___y_626_;
v___y_525_ = v___y_638_;
v___y_526_ = v___y_628_;
v___y_527_ = v___y_631_;
v___y_528_ = v___y_633_;
v___y_529_ = v___y_622_;
v___y_530_ = v___y_623_;
v___y_531_ = v___y_640_;
v___y_532_ = v___y_625_;
v___y_533_ = v___y_627_;
v___y_534_ = v___y_634_;
v___y_535_ = v___y_642_;
v___y_536_ = v___y_630_;
v___y_537_ = v___y_629_;
v___y_538_ = v___y_632_;
v___y_539_ = v___y_639_;
v___y_540_ = v___y_636_;
v___y_541_ = v___x_650_;
goto v___jp_519_;
}
}
else
{
lean_object* v_a_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_658_; 
lean_dec_ref(v___y_641_);
lean_dec_ref(v___y_632_);
lean_dec_ref(v___y_631_);
lean_dec(v___y_629_);
lean_dec_ref(v___y_628_);
lean_dec(v___y_627_);
lean_dec(v___y_625_);
lean_dec_ref(v___y_624_);
lean_dec_ref(v___y_622_);
v_a_651_ = lean_ctor_get(v___x_643_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v___x_643_);
if (v_isSharedCheck_658_ == 0)
{
v___x_653_ = v___x_643_;
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_a_651_);
lean_dec(v___x_643_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_658_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_656_; 
if (v_isShared_654_ == 0)
{
v___x_656_ = v___x_653_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v_a_651_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
}
v___jp_659_:
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_671_, 0, v___y_660_);
v___x_672_ = l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(v___x_671_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_);
lean_dec_ref(v___y_669_);
if (lean_obj_tag(v___x_672_) == 0)
{
lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_680_; 
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_672_);
if (v_isSharedCheck_680_ == 0)
{
lean_object* v_unused_681_; 
v_unused_681_ = lean_ctor_get(v___x_672_, 0);
lean_dec(v_unused_681_);
v___x_674_ = v___x_672_;
v_isShared_675_ = v_isSharedCheck_680_;
goto v_resetjp_673_;
}
else
{
lean_dec(v___x_672_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_680_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v___x_676_; lean_object* v___x_678_; 
v___x_676_ = lean_box(0);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 0, v___x_676_);
v___x_678_ = v___x_674_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v___x_676_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
else
{
return v___x_672_;
}
}
v___jp_682_:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(v_c_493_);
lean_inc_ref(v___y_694_);
v___x_697_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(v___x_696_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v_a_698_; lean_object* v_d_699_; lean_object* v_p_700_; uint8_t v___x_701_; 
v_a_698_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_a_698_);
lean_dec_ref_known(v___x_697_, 1);
v_d_699_ = lean_ctor_get(v_a_698_, 0);
v_p_700_ = lean_ctor_get(v_a_698_, 1);
lean_inc(v_d_699_);
v___x_701_ = l_Int_Internal_Linear_Poly_isUnsatDvd(v_d_699_, v_p_700_);
if (v___x_701_ == 0)
{
uint8_t v___x_702_; 
v___x_702_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(v_a_698_);
if (v___x_702_ == 0)
{
if (lean_obj_tag(v_p_700_) == 1)
{
lean_object* v_k_703_; lean_object* v_v_704_; lean_object* v_p_705_; lean_object* v___x_706_; 
lean_inc_ref(v_p_700_);
lean_inc(v_d_699_);
v_k_703_ = lean_ctor_get(v_p_700_, 0);
lean_inc(v_k_703_);
v_v_704_ = lean_ctor_get(v_p_700_, 1);
lean_inc(v_v_704_);
v_p_705_ = lean_ctor_get(v_p_700_, 2);
lean_inc_ref(v_p_705_);
lean_inc(v_a_698_);
v___x_706_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(v_a_698_, v___y_686_, v___y_694_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_707_; lean_object* v___f_708_; lean_object* v___f_709_; uint8_t v___x_710_; uint8_t v___x_711_; uint8_t v___x_712_; 
v_a_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_a_707_);
lean_dec_ref_known(v___x_706_, 1);
lean_inc_n(v_v_704_, 2);
lean_inc(v_a_698_);
v___f_708_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed), 3, 2);
lean_closure_set(v___f_708_, 0, v_a_698_);
lean_closure_set(v___f_708_, 1, v_v_704_);
v___f_709_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed), 2, 1);
lean_closure_set(v___f_709_, 0, v_v_704_);
v___x_710_ = 0;
v___x_711_ = lean_unbox(v_a_707_);
lean_dec(v_a_707_);
v___x_712_ = l_Lean_instBEqLBool_beq(v___x_711_, v___x_710_);
if (v___x_712_ == 0)
{
v___y_622_ = v___f_708_;
v___y_623_ = v___y_683_;
v___y_624_ = v_p_700_;
v___y_625_ = v_v_704_;
v___y_626_ = v___y_684_;
v___y_627_ = v_d_699_;
v___y_628_ = v___f_709_;
v___y_629_ = v_k_703_;
v___y_630_ = v___y_685_;
v___y_631_ = v_p_705_;
v___y_632_ = v_a_698_;
v___y_633_ = v___y_686_;
v___y_634_ = v___y_687_;
v___y_635_ = v___y_688_;
v___y_636_ = v___y_689_;
v___y_637_ = v___y_690_;
v___y_638_ = v___y_691_;
v___y_639_ = v___y_692_;
v___y_640_ = v___y_693_;
v___y_641_ = v___y_694_;
v___y_642_ = v___y_695_;
goto v___jp_621_;
}
else
{
lean_object* v___x_713_; 
lean_inc(v_v_704_);
v___x_713_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v_v_704_, v___y_686_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_dec_ref_known(v___x_713_, 1);
v___y_622_ = v___f_708_;
v___y_623_ = v___y_683_;
v___y_624_ = v_p_700_;
v___y_625_ = v_v_704_;
v___y_626_ = v___y_684_;
v___y_627_ = v_d_699_;
v___y_628_ = v___f_709_;
v___y_629_ = v_k_703_;
v___y_630_ = v___y_685_;
v___y_631_ = v_p_705_;
v___y_632_ = v_a_698_;
v___y_633_ = v___y_686_;
v___y_634_ = v___y_687_;
v___y_635_ = v___y_688_;
v___y_636_ = v___y_689_;
v___y_637_ = v___y_690_;
v___y_638_ = v___y_691_;
v___y_639_ = v___y_692_;
v___y_640_ = v___y_693_;
v___y_641_ = v___y_694_;
v___y_642_ = v___y_695_;
goto v___jp_621_;
}
else
{
lean_dec_ref(v___f_709_);
lean_dec_ref(v___f_708_);
lean_dec_ref(v_p_705_);
lean_dec(v_v_704_);
lean_dec_ref_known(v_p_700_, 3);
lean_dec(v_k_703_);
lean_dec(v_d_699_);
lean_dec(v_a_698_);
lean_dec_ref(v___y_694_);
return v___x_713_;
}
}
}
else
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
lean_dec_ref(v_p_705_);
lean_dec(v_v_704_);
lean_dec_ref_known(v_p_700_, 3);
lean_dec(v_k_703_);
lean_dec(v_d_699_);
lean_dec(v_a_698_);
lean_dec_ref(v___y_694_);
v_a_714_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_721_ == 0)
{
v___x_716_ = v___x_706_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_706_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_a_714_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
}
else
{
lean_object* v___x_722_; 
v___x_722_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_a_698_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
lean_dec_ref(v___y_694_);
return v___x_722_;
}
}
else
{
lean_object* v_options_723_; uint8_t v_hasTrace_724_; 
v_options_723_ = lean_ctor_get(v___y_694_, 2);
v_hasTrace_724_ = lean_ctor_get_uint8(v_options_723_, sizeof(void*)*1);
if (v_hasTrace_724_ == 0)
{
lean_dec(v_a_698_);
lean_dec_ref(v___y_694_);
goto v___jp_505_;
}
else
{
lean_object* v_inheritedTraceOptions_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; uint8_t v___x_730_; 
v_inheritedTraceOptions_725_ = lean_ctor_get(v___y_694_, 13);
v___x_726_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1));
lean_inc_ref(v___y_683_);
lean_inc_ref(v___y_684_);
lean_inc_ref(v___y_685_);
v___x_727_ = l_Lean_Name_mkStr4(v___y_685_, v___y_684_, v___y_683_, v___x_726_);
v___x_728_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
lean_inc(v___x_727_);
v___x_729_ = l_Lean_Name_append(v___x_728_, v___x_727_);
v___x_730_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_725_, v_options_723_, v___x_729_);
lean_dec(v___x_729_);
if (v___x_730_ == 0)
{
lean_dec(v___x_727_);
lean_dec(v_a_698_);
lean_dec_ref(v___y_694_);
goto v___jp_505_;
}
else
{
lean_object* v___x_731_; 
v___x_731_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_a_698_, v___y_686_, v___y_694_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_object* v_a_732_; lean_object* v___x_733_; 
v_a_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc(v_a_732_);
lean_dec_ref_known(v___x_731_, 1);
v___x_733_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_727_, v_a_732_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
lean_dec_ref(v___y_694_);
if (lean_obj_tag(v___x_733_) == 0)
{
lean_dec_ref_known(v___x_733_, 1);
goto v___jp_505_;
}
else
{
return v___x_733_;
}
}
else
{
lean_object* v_a_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_741_; 
lean_dec(v___x_727_);
lean_dec_ref(v___y_694_);
v_a_734_ = lean_ctor_get(v___x_731_, 0);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_731_);
if (v_isSharedCheck_741_ == 0)
{
v___x_736_ = v___x_731_;
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_a_734_);
lean_dec(v___x_731_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_741_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v___x_739_; 
if (v_isShared_737_ == 0)
{
v___x_739_ = v___x_736_;
goto v_reusejp_738_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v_a_734_);
v___x_739_ = v_reuseFailAlloc_740_;
goto v_reusejp_738_;
}
v_reusejp_738_:
{
return v___x_739_;
}
}
}
}
}
}
}
else
{
lean_object* v_options_742_; uint8_t v_hasTrace_743_; 
v_options_742_ = lean_ctor_get(v___y_694_, 2);
v_hasTrace_743_ = lean_ctor_get_uint8(v_options_742_, sizeof(void*)*1);
if (v_hasTrace_743_ == 0)
{
v___y_660_ = v_a_698_;
v___y_661_ = v___y_686_;
v___y_662_ = v___y_687_;
v___y_663_ = v___y_688_;
v___y_664_ = v___y_689_;
v___y_665_ = v___y_690_;
v___y_666_ = v___y_691_;
v___y_667_ = v___y_692_;
v___y_668_ = v___y_693_;
v___y_669_ = v___y_694_;
v___y_670_ = v___y_695_;
goto v___jp_659_;
}
else
{
lean_object* v_inheritedTraceOptions_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; uint8_t v___x_749_; 
v_inheritedTraceOptions_744_ = lean_ctor_get(v___y_694_, 13);
v___x_745_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2));
lean_inc_ref(v___y_683_);
lean_inc_ref(v___y_684_);
lean_inc_ref(v___y_685_);
v___x_746_ = l_Lean_Name_mkStr4(v___y_685_, v___y_684_, v___y_683_, v___x_745_);
v___x_747_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
lean_inc(v___x_746_);
v___x_748_ = l_Lean_Name_append(v___x_747_, v___x_746_);
v___x_749_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_744_, v_options_742_, v___x_748_);
lean_dec(v___x_748_);
if (v___x_749_ == 0)
{
lean_dec(v___x_746_);
v___y_660_ = v_a_698_;
v___y_661_ = v___y_686_;
v___y_662_ = v___y_687_;
v___y_663_ = v___y_688_;
v___y_664_ = v___y_689_;
v___y_665_ = v___y_690_;
v___y_666_ = v___y_691_;
v___y_667_ = v___y_692_;
v___y_668_ = v___y_693_;
v___y_669_ = v___y_694_;
v___y_670_ = v___y_695_;
goto v___jp_659_;
}
else
{
lean_object* v___x_750_; 
lean_inc(v_a_698_);
v___x_750_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_a_698_, v___y_686_, v___y_694_);
if (lean_obj_tag(v___x_750_) == 0)
{
lean_object* v_a_751_; lean_object* v___x_752_; 
v_a_751_ = lean_ctor_get(v___x_750_, 0);
lean_inc(v_a_751_);
lean_dec_ref_known(v___x_750_, 1);
v___x_752_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_746_, v_a_751_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_dec_ref_known(v___x_752_, 1);
v___y_660_ = v_a_698_;
v___y_661_ = v___y_686_;
v___y_662_ = v___y_687_;
v___y_663_ = v___y_688_;
v___y_664_ = v___y_689_;
v___y_665_ = v___y_690_;
v___y_666_ = v___y_691_;
v___y_667_ = v___y_692_;
v___y_668_ = v___y_693_;
v___y_669_ = v___y_694_;
v___y_670_ = v___y_695_;
goto v___jp_659_;
}
else
{
lean_dec(v_a_698_);
lean_dec_ref(v___y_694_);
return v___x_752_;
}
}
else
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_760_; 
lean_dec(v___x_746_);
lean_dec(v_a_698_);
lean_dec_ref(v___y_694_);
v_a_753_ = lean_ctor_get(v___x_750_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_750_);
if (v_isSharedCheck_760_ == 0)
{
v___x_755_ = v___x_750_;
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___x_750_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_756_ == 0)
{
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_a_753_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_768_; 
lean_dec_ref(v___y_694_);
v_a_761_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_768_ == 0)
{
v___x_763_ = v___x_697_;
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_697_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_766_; 
if (v_isShared_764_ == 0)
{
v___x_766_ = v___x_763_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_a_761_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
v___jp_785_:
{
if (v___y_786_ == 0)
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_787_ = lean_unsigned_to_nat(1u);
v___x_788_ = lean_nat_add(v_currRecDepth_772_, v___x_787_);
lean_dec(v_currRecDepth_772_);
lean_inc_ref(v_inheritedTraceOptions_784_);
lean_inc_ref(v_options_771_);
v___x_789_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_789_, 0, v_fileName_769_);
lean_ctor_set(v___x_789_, 1, v_fileMap_770_);
lean_ctor_set(v___x_789_, 2, v_options_771_);
lean_ctor_set(v___x_789_, 3, v___x_788_);
lean_ctor_set(v___x_789_, 4, v_maxRecDepth_773_);
lean_ctor_set(v___x_789_, 5, v_ref_774_);
lean_ctor_set(v___x_789_, 6, v_currNamespace_775_);
lean_ctor_set(v___x_789_, 7, v_openDecls_776_);
lean_ctor_set(v___x_789_, 8, v_initHeartbeats_777_);
lean_ctor_set(v___x_789_, 9, v_maxHeartbeats_778_);
lean_ctor_set(v___x_789_, 10, v_quotContext_779_);
lean_ctor_set(v___x_789_, 11, v_currMacroScope_780_);
lean_ctor_set(v___x_789_, 12, v_cancelTk_x3f_782_);
lean_ctor_set(v___x_789_, 13, v_inheritedTraceOptions_784_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*14, v_diag_781_);
lean_ctor_set_uint8(v___x_789_, sizeof(void*)*14 + 1, v_suppressElabErrors_783_);
v___x_790_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_494_, v___x_789_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_818_; 
v_a_791_ = lean_ctor_get(v___x_790_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_818_ == 0)
{
v___x_793_ = v___x_790_;
v_isShared_794_ = v_isSharedCheck_818_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_790_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_818_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
uint8_t v___x_795_; 
v___x_795_ = lean_unbox(v_a_791_);
lean_dec(v_a_791_);
if (v___x_795_ == 0)
{
uint8_t v_hasTrace_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
lean_del_object(v___x_793_);
v_hasTrace_796_ = lean_ctor_get_uint8(v_options_771_, sizeof(void*)*1);
v___x_797_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0));
v___x_798_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2));
v___x_799_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3));
if (v_hasTrace_796_ == 0)
{
lean_dec_ref(v_inheritedTraceOptions_784_);
lean_dec_ref(v_options_771_);
v___y_683_ = v___x_799_;
v___y_684_ = v___x_798_;
v___y_685_ = v___x_797_;
v___y_686_ = v_a_494_;
v___y_687_ = v_a_495_;
v___y_688_ = v_a_496_;
v___y_689_ = v_a_497_;
v___y_690_ = v_a_498_;
v___y_691_ = v_a_499_;
v___y_692_ = v_a_500_;
v___y_693_ = v_a_501_;
v___y_694_ = v___x_789_;
v___y_695_ = v_a_503_;
goto v___jp_682_;
}
else
{
lean_object* v___x_800_; lean_object* v___x_801_; uint8_t v___x_802_; 
v___x_800_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4));
v___x_801_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5);
v___x_802_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_784_, v_options_771_, v___x_801_);
lean_dec_ref(v_options_771_);
lean_dec_ref(v_inheritedTraceOptions_784_);
if (v___x_802_ == 0)
{
v___y_683_ = v___x_799_;
v___y_684_ = v___x_798_;
v___y_685_ = v___x_797_;
v___y_686_ = v_a_494_;
v___y_687_ = v_a_495_;
v___y_688_ = v_a_496_;
v___y_689_ = v_a_497_;
v___y_690_ = v_a_498_;
v___y_691_ = v_a_499_;
v___y_692_ = v_a_500_;
v___y_693_ = v_a_501_;
v___y_694_ = v___x_789_;
v___y_695_ = v_a_503_;
goto v___jp_682_;
}
else
{
lean_object* v___x_803_; 
lean_inc_ref(v_c_493_);
v___x_803_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_493_, v_a_494_, v___x_789_);
if (lean_obj_tag(v___x_803_) == 0)
{
lean_object* v_a_804_; lean_object* v___x_805_; 
v_a_804_ = lean_ctor_get(v___x_803_, 0);
lean_inc(v_a_804_);
lean_dec_ref_known(v___x_803_, 1);
v___x_805_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_800_, v_a_804_, v_a_500_, v_a_501_, v___x_789_, v_a_503_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_dec_ref_known(v___x_805_, 1);
v___y_683_ = v___x_799_;
v___y_684_ = v___x_798_;
v___y_685_ = v___x_797_;
v___y_686_ = v_a_494_;
v___y_687_ = v_a_495_;
v___y_688_ = v_a_496_;
v___y_689_ = v_a_497_;
v___y_690_ = v_a_498_;
v___y_691_ = v_a_499_;
v___y_692_ = v_a_500_;
v___y_693_ = v_a_501_;
v___y_694_ = v___x_789_;
v___y_695_ = v_a_503_;
goto v___jp_682_;
}
else
{
lean_dec_ref_known(v___x_789_, 14);
lean_dec_ref(v_c_493_);
return v___x_805_;
}
}
else
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_813_; 
lean_dec_ref_known(v___x_789_, 14);
lean_dec_ref(v_c_493_);
v_a_806_ = lean_ctor_get(v___x_803_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_803_);
if (v_isSharedCheck_813_ == 0)
{
v___x_808_ = v___x_803_;
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_803_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_806_);
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
}
}
else
{
lean_object* v___x_814_; lean_object* v___x_816_; 
lean_dec_ref_known(v___x_789_, 14);
lean_dec_ref(v_inheritedTraceOptions_784_);
lean_dec_ref(v_options_771_);
lean_dec_ref(v_c_493_);
v___x_814_ = lean_box(0);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 0, v___x_814_);
v___x_816_ = v___x_793_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_814_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
else
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
lean_dec_ref_known(v___x_789_, 14);
lean_dec_ref(v_inheritedTraceOptions_784_);
lean_dec_ref(v_options_771_);
lean_dec_ref(v_c_493_);
v_a_819_ = lean_ctor_get(v___x_790_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_790_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_790_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_790_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_822_ == 0)
{
v___x_824_ = v___x_821_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_a_819_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
else
{
lean_object* v___x_827_; 
lean_dec_ref(v_inheritedTraceOptions_784_);
lean_dec(v_cancelTk_x3f_782_);
lean_dec(v_currMacroScope_780_);
lean_dec(v_quotContext_779_);
lean_dec(v_maxHeartbeats_778_);
lean_dec(v_initHeartbeats_777_);
lean_dec(v_openDecls_776_);
lean_dec(v_currNamespace_775_);
lean_dec(v_maxRecDepth_773_);
lean_dec(v_currRecDepth_772_);
lean_dec_ref(v_options_771_);
lean_dec_ref(v_fileMap_770_);
lean_dec_ref(v_fileName_769_);
lean_dec_ref(v_c_493_);
v___x_827_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_774_);
return v___x_827_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___boxed(lean_object* v_c_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v_c_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_);
lean_dec(v_a_842_);
lean_dec(v_a_840_);
lean_dec_ref(v_a_839_);
lean_dec(v_a_838_);
lean_dec_ref(v_a_837_);
lean_dec(v_a_836_);
lean_dec_ref(v_a_835_);
lean_dec(v_a_834_);
lean_dec(v_a_833_);
return v_res_844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(lean_object* v_c_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_){
_start:
{
lean_object* v_d_857_; lean_object* v_p_858_; lean_object* v___x_859_; 
v_d_857_ = lean_ctor_get(v_c_845_, 0);
v_p_858_ = lean_ctor_get(v_c_845_, 1);
lean_inc_ref(v_p_858_);
v___x_859_ = l_Int_Internal_Linear_Poly_normCommRing_x3f(v_p_858_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_a_860_);
lean_dec_ref_known(v___x_859_, 1);
if (lean_obj_tag(v_a_860_) == 1)
{
lean_object* v_val_861_; lean_object* v_snd_862_; lean_object* v_fst_863_; lean_object* v_fst_864_; lean_object* v_snd_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; 
lean_inc(v_d_857_);
v_val_861_ = lean_ctor_get(v_a_860_, 0);
lean_inc(v_val_861_);
lean_dec_ref_known(v_a_860_, 1);
v_snd_862_ = lean_ctor_get(v_val_861_, 1);
lean_inc(v_snd_862_);
v_fst_863_ = lean_ctor_get(v_val_861_, 0);
lean_inc(v_fst_863_);
lean_dec(v_val_861_);
v_fst_864_ = lean_ctor_get(v_snd_862_, 0);
lean_inc(v_fst_864_);
v_snd_865_ = lean_ctor_get(v_snd_862_, 1);
lean_inc(v_snd_865_);
lean_dec(v_snd_862_);
v___x_866_ = lean_alloc_ctor(12, 3, 0);
lean_ctor_set(v___x_866_, 0, v_c_845_);
lean_ctor_set(v___x_866_, 1, v_fst_863_);
lean_ctor_set(v___x_866_, 2, v_fst_864_);
v___x_867_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_867_, 0, v_d_857_);
lean_ctor_set(v___x_867_, 1, v_snd_865_);
lean_ctor_set(v___x_867_, 2, v___x_866_);
lean_inc_ref(v_a_854_);
v___x_868_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v___x_867_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_);
return v___x_868_;
}
else
{
lean_object* v___x_869_; 
lean_dec(v_a_860_);
lean_inc_ref(v_a_854_);
v___x_869_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v_c_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_);
return v___x_869_;
}
}
else
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_877_; 
lean_dec_ref(v_c_845_);
v_a_870_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_877_ == 0)
{
v___x_872_ = v___x_859_;
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_859_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_875_; 
if (v_isShared_873_ == 0)
{
v___x_875_ = v___x_872_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_a_870_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore___boxed(lean_object* v_c_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v_c_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_);
lean_dec(v_a_888_);
lean_dec_ref(v_a_887_);
lean_dec(v_a_886_);
lean_dec_ref(v_a_885_);
lean_dec(v_a_884_);
lean_dec_ref(v_a_883_);
lean_dec(v_a_882_);
lean_dec_ref(v_a_881_);
lean_dec(v_a_880_);
lean_dec(v_a_879_);
return v_res_890_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8(void){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_905_ = lean_box(0);
v___x_906_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7));
v___x_907_ = l_Lean_mkConst(v___x_906_, v___x_905_);
return v___x_907_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10(void){
_start:
{
lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_909_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9));
v___x_910_ = l_Lean_stringToMessageData(v___x_909_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(lean_object* v_e_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_){
_start:
{
lean_object* v___x_926_; 
lean_inc_ref(v_e_911_);
v___x_926_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_911_, v_a_919_);
if (lean_obj_tag(v___x_926_) == 0)
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_1060_; 
v_a_927_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_929_ = v___x_926_;
v_isShared_930_ = v_isSharedCheck_1060_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_926_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_1060_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_936_; uint8_t v___x_937_; 
v___x_936_ = l_Lean_Expr_cleanupAnnotations(v_a_927_);
v___x_937_ = l_Lean_Expr_isApp(v___x_936_);
if (v___x_937_ == 0)
{
lean_dec_ref(v___x_936_);
lean_dec_ref(v_e_911_);
goto v___jp_931_;
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
lean_dec_ref(v_e_911_);
goto v___jp_931_;
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
lean_dec_ref(v_e_911_);
goto v___jp_931_;
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
lean_dec_ref(v_arg_938_);
lean_dec_ref(v_e_911_);
goto v___jp_931_;
}
else
{
lean_object* v___x_947_; lean_object* v___x_948_; uint8_t v___x_949_; 
v___x_947_ = l_Lean_Expr_appFnCleanup___redArg(v___x_945_);
v___x_948_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_949_ = l_Lean_Expr_isConstOf(v___x_947_, v___x_948_);
lean_dec_ref(v___x_947_);
if (v___x_949_ == 0)
{
lean_dec_ref(v_arg_944_);
lean_dec_ref(v_arg_941_);
lean_dec_ref(v_arg_938_);
lean_dec_ref(v_e_911_);
goto v___jp_931_;
}
else
{
lean_object* v___x_950_; 
lean_del_object(v___x_929_);
v___x_950_ = l_Lean_Meta_Structural_isInstDvdInt___redArg(v_arg_944_, v_a_919_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_1051_; 
v_a_951_ = lean_ctor_get(v___x_950_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_953_ = v___x_950_;
v_isShared_954_ = v_isSharedCheck_1051_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_a_951_);
lean_dec(v___x_950_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_1051_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
uint8_t v___x_955_; 
v___x_955_ = lean_unbox(v_a_951_);
lean_dec(v_a_951_);
if (v___x_955_ == 0)
{
lean_object* v___x_956_; lean_object* v___x_958_; 
lean_dec_ref(v_arg_941_);
lean_dec_ref(v_arg_938_);
lean_dec_ref(v_e_911_);
v___x_956_ = lean_box(0);
if (v_isShared_954_ == 0)
{
lean_ctor_set(v___x_953_, 0, v___x_956_);
v___x_958_ = v___x_953_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v___x_956_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
else
{
lean_object* v___x_960_; 
lean_del_object(v___x_953_);
lean_inc_ref(v_arg_941_);
v___x_960_ = l_Lean_Meta_getIntValue_x3f(v_arg_941_, v_a_918_, v_a_919_, v_a_920_, v_a_921_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_a_961_);
lean_dec_ref_known(v___x_960_, 1);
if (lean_obj_tag(v_a_961_) == 1)
{
lean_object* v_val_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_1027_; 
v_val_962_ = lean_ctor_get(v_a_961_, 0);
v_isSharedCheck_1027_ = !lean_is_exclusive(v_a_961_);
if (v_isSharedCheck_1027_ == 0)
{
v___x_964_ = v_a_961_;
v_isShared_965_ = v_isSharedCheck_1027_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_val_962_);
lean_dec(v_a_961_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_1027_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_966_; 
lean_inc_ref(v_e_911_);
v___x_966_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_911_, v_a_912_, v_a_916_, v_a_918_, v_a_919_, v_a_920_, v_a_921_);
if (lean_obj_tag(v___x_966_) == 0)
{
lean_object* v_a_967_; uint8_t v___x_968_; 
v_a_967_ = lean_ctor_get(v___x_966_, 0);
lean_inc(v_a_967_);
lean_dec_ref_known(v___x_966_, 1);
v___x_968_ = lean_unbox(v_a_967_);
lean_dec(v_a_967_);
if (v___x_968_ == 0)
{
lean_object* v___x_969_; 
lean_del_object(v___x_964_);
lean_dec(v_val_962_);
lean_inc_ref(v_e_911_);
v___x_969_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_911_, v_a_912_, v_a_916_, v_a_918_, v_a_919_, v_a_920_, v_a_921_);
if (lean_obj_tag(v___x_969_) == 0)
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_995_; 
v_a_970_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_995_ == 0)
{
v___x_972_ = v___x_969_;
v_isShared_973_ = v_isSharedCheck_995_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_969_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_995_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
uint8_t v___x_974_; 
v___x_974_ = lean_unbox(v_a_970_);
lean_dec(v_a_970_);
if (v___x_974_ == 0)
{
lean_object* v___x_975_; lean_object* v___x_977_; 
lean_dec_ref(v_arg_941_);
lean_dec_ref(v_arg_938_);
lean_dec_ref(v_e_911_);
v___x_975_ = lean_box(0);
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 0, v___x_975_);
v___x_977_ = v___x_972_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_978_; 
v_reuseFailAlloc_978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_978_, 0, v___x_975_);
v___x_977_ = v_reuseFailAlloc_978_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
return v___x_977_;
}
}
else
{
lean_object* v___x_979_; 
lean_del_object(v___x_972_);
lean_inc_ref(v_e_911_);
v___x_979_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_);
if (lean_obj_tag(v___x_979_) == 0)
{
lean_object* v_a_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; 
v_a_980_ = lean_ctor_get(v___x_979_, 0);
lean_inc(v_a_980_);
lean_dec_ref_known(v___x_979_, 1);
v___x_981_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8);
v___x_982_ = l_Lean_eagerReflBoolTrue;
v___x_983_ = l_Lean_Meta_mkOfEqFalseCore(v_e_911_, v_a_980_);
v___x_984_ = l_Lean_mkApp4(v___x_981_, v_arg_941_, v_arg_938_, v___x_982_, v___x_983_);
v___x_985_ = lean_unsigned_to_nat(0u);
v___x_986_ = l_Lean_Meta_Grind_pushNewFact(v___x_984_, v___x_985_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_);
return v___x_986_;
}
else
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_994_; 
lean_dec_ref(v_arg_941_);
lean_dec_ref(v_arg_938_);
lean_dec_ref(v_e_911_);
v_a_987_ = lean_ctor_get(v___x_979_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_979_);
if (v_isSharedCheck_994_ == 0)
{
v___x_989_ = v___x_979_;
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_979_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_992_; 
if (v_isShared_990_ == 0)
{
v___x_992_ = v___x_989_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v_a_987_);
v___x_992_ = v_reuseFailAlloc_993_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
return v___x_992_;
}
}
}
}
}
}
else
{
lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1003_; 
lean_dec_ref(v_arg_941_);
lean_dec_ref(v_arg_938_);
lean_dec_ref(v_e_911_);
v_a_996_ = lean_ctor_get(v___x_969_, 0);
v_isSharedCheck_1003_ = !lean_is_exclusive(v___x_969_);
if (v_isSharedCheck_1003_ == 0)
{
v___x_998_ = v___x_969_;
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_dec(v___x_969_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1003_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v___x_1001_; 
if (v_isShared_999_ == 0)
{
v___x_1001_ = v___x_998_;
goto v_reusejp_1000_;
}
else
{
lean_object* v_reuseFailAlloc_1002_; 
v_reuseFailAlloc_1002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_a_996_);
v___x_1001_ = v_reuseFailAlloc_1002_;
goto v_reusejp_1000_;
}
v_reusejp_1000_:
{
return v___x_1001_;
}
}
}
}
else
{
lean_object* v___x_1004_; 
lean_dec_ref(v_arg_941_);
v___x_1004_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(v_arg_938_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_);
if (lean_obj_tag(v___x_1004_) == 0)
{
lean_object* v_a_1005_; lean_object* v___x_1007_; 
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
lean_inc(v_a_1005_);
lean_dec_ref_known(v___x_1004_, 1);
if (v_isShared_965_ == 0)
{
lean_ctor_set_tag(v___x_964_, 0);
lean_ctor_set(v___x_964_, 0, v_e_911_);
v___x_1007_ = v___x_964_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_e_911_);
v___x_1007_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1008_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1008_, 0, v_val_962_);
lean_ctor_set(v___x_1008_, 1, v_a_1005_);
lean_ctor_set(v___x_1008_, 2, v___x_1007_);
v___x_1009_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v___x_1008_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_);
return v___x_1009_;
}
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
lean_del_object(v___x_964_);
lean_dec(v_val_962_);
lean_dec_ref(v_e_911_);
v_a_1011_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_1004_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_1004_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1016_; 
if (v_isShared_1014_ == 0)
{
v___x_1016_ = v___x_1013_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1011_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
}
else
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
lean_del_object(v___x_964_);
lean_dec(v_val_962_);
lean_dec_ref(v_arg_941_);
lean_dec_ref(v_arg_938_);
lean_dec_ref(v_e_911_);
v_a_1019_ = lean_ctor_get(v___x_966_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_966_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___x_966_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_966_);
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
lean_object* v___x_1028_; 
lean_dec(v_a_961_);
lean_dec_ref(v_arg_941_);
lean_dec_ref(v_arg_938_);
v___x_1028_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_916_);
if (lean_obj_tag(v___x_1028_) == 0)
{
lean_object* v_a_1029_; uint8_t v_verbose_1030_; 
v_a_1029_ = lean_ctor_get(v___x_1028_, 0);
lean_inc(v_a_1029_);
lean_dec_ref_known(v___x_1028_, 1);
v_verbose_1030_ = lean_ctor_get_uint8(v_a_1029_, 0);
lean_dec(v_a_1029_);
if (v_verbose_1030_ == 0)
{
lean_dec_ref(v_e_911_);
goto v___jp_923_;
}
else
{
lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1031_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10);
v___x_1032_ = l_Lean_indentExpr(v_e_911_);
v___x_1033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1031_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
v___x_1034_ = l_Lean_Meta_Sym_reportIssue(v___x_1033_, v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_, v_a_921_);
if (lean_obj_tag(v___x_1034_) == 0)
{
lean_dec_ref_known(v___x_1034_, 1);
goto v___jp_923_;
}
else
{
return v___x_1034_;
}
}
}
else
{
lean_object* v_a_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1042_; 
lean_dec_ref(v_e_911_);
v_a_1035_ = lean_ctor_get(v___x_1028_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1028_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1037_ = v___x_1028_;
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_a_1035_);
lean_dec(v___x_1028_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1042_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1040_; 
if (v_isShared_1038_ == 0)
{
v___x_1040_ = v___x_1037_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_a_1035_);
v___x_1040_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
return v___x_1040_;
}
}
}
}
}
else
{
lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1050_; 
lean_dec_ref(v_arg_941_);
lean_dec_ref(v_arg_938_);
lean_dec_ref(v_e_911_);
v_a_1043_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1045_ = v___x_960_;
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___x_960_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1048_; 
if (v_isShared_1046_ == 0)
{
v___x_1048_ = v___x_1045_;
goto v_reusejp_1047_;
}
else
{
lean_object* v_reuseFailAlloc_1049_; 
v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_a_1043_);
v___x_1048_ = v_reuseFailAlloc_1049_;
goto v_reusejp_1047_;
}
v_reusejp_1047_:
{
return v___x_1048_;
}
}
}
}
}
}
else
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
lean_dec_ref(v_arg_941_);
lean_dec_ref(v_arg_938_);
lean_dec_ref(v_e_911_);
v_a_1052_ = lean_ctor_get(v___x_950_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___x_950_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_950_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1052_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
}
}
}
}
v___jp_931_:
{
lean_object* v___x_932_; lean_object* v___x_934_; 
v___x_932_ = lean_box(0);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 0, v___x_932_);
v___x_934_ = v___x_929_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_932_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
else
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1068_; 
lean_dec_ref(v_e_911_);
v_a_1061_ = lean_ctor_get(v___x_926_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_926_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1063_ = v___x_926_;
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_926_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1066_; 
if (v_isShared_1064_ == 0)
{
v___x_1066_ = v___x_1063_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1061_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
v___jp_923_:
{
lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_924_ = lean_box(0);
v___x_925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_925_, 0, v___x_924_);
return v___x_925_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___boxed(lean_object* v_e_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_, lean_object* v_a_1079_, lean_object* v_a_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(v_e_1069_, v_a_1070_, v_a_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_, v_a_1076_, v_a_1077_, v_a_1078_, v_a_1079_);
lean_dec(v_a_1079_);
lean_dec_ref(v_a_1078_);
lean_dec(v_a_1077_);
lean_dec_ref(v_a_1076_);
lean_dec(v_a_1075_);
lean_dec_ref(v_a_1074_);
lean_dec(v_a_1073_);
lean_dec_ref(v_a_1072_);
lean_dec(v_a_1071_);
lean_dec(v_a_1070_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd_spec__0(lean_object* v_a_1082_){
_start:
{
lean_object* v___x_1083_; 
v___x_1083_ = lean_nat_to_int(v_a_1082_);
return v___x_1083_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3(void){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1089_ = lean_box(0);
v___x_1090_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2));
v___x_1091_ = l_Lean_mkConst(v___x_1090_, v___x_1089_);
return v___x_1091_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7(void){
_start:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1098_ = lean_box(0);
v___x_1099_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6));
v___x_1100_ = l_Lean_mkConst(v___x_1099_, v___x_1098_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(lean_object* v_e_1101_, lean_object* v_a_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_, lean_object* v_a_1105_, lean_object* v_a_1106_, lean_object* v_a_1107_, lean_object* v_a_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_, lean_object* v_a_1111_){
_start:
{
lean_object* v___x_1119_; uint8_t v___x_1120_; 
lean_inc_ref(v_e_1101_);
v___x_1119_ = l_Lean_Expr_cleanupAnnotations(v_e_1101_);
v___x_1120_ = l_Lean_Expr_isApp(v___x_1119_);
if (v___x_1120_ == 0)
{
lean_dec_ref(v___x_1119_);
lean_dec_ref(v_e_1101_);
goto v___jp_1113_;
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
lean_dec_ref(v_e_1101_);
goto v___jp_1113_;
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
lean_dec_ref(v_e_1101_);
goto v___jp_1113_;
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
lean_dec_ref(v_arg_1121_);
lean_dec_ref(v_e_1101_);
goto v___jp_1113_;
}
else
{
lean_object* v___x_1130_; lean_object* v___x_1131_; uint8_t v___x_1132_; 
v___x_1130_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1128_);
v___x_1131_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1132_ = l_Lean_Expr_isConstOf(v___x_1130_, v___x_1131_);
lean_dec_ref(v___x_1130_);
if (v___x_1132_ == 0)
{
lean_dec_ref(v_arg_1127_);
lean_dec_ref(v_arg_1124_);
lean_dec_ref(v_arg_1121_);
lean_dec_ref(v_e_1101_);
goto v___jp_1113_;
}
else
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Lean_Meta_Structural_isInstDvdNat___redArg(v_arg_1127_, v_a_1109_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1265_; 
v_a_1134_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1265_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1265_ == 0)
{
v___x_1136_ = v___x_1133_;
v_isShared_1137_ = v_isSharedCheck_1265_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1133_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1265_;
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
lean_dec_ref(v_arg_1124_);
lean_dec_ref(v_arg_1121_);
lean_dec_ref(v_e_1101_);
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
v___x_1143_ = l_Lean_Meta_getNatValue_x3f(v_arg_1124_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_a_1144_; 
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
lean_inc(v_a_1144_);
lean_dec_ref_known(v___x_1143_, 1);
if (lean_obj_tag(v_a_1144_) == 1)
{
lean_object* v_val_1145_; lean_object* v___x_1146_; 
v_val_1145_ = lean_ctor_get(v_a_1144_, 0);
lean_inc(v_val_1145_);
lean_dec_ref_known(v_a_1144_, 1);
lean_inc_ref(v_e_1101_);
v___x_1146_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_1101_, v_a_1102_, v_a_1106_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v_a_1147_; uint8_t v___x_1148_; 
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
lean_inc(v_a_1147_);
lean_dec_ref_known(v___x_1146_, 1);
v___x_1148_ = lean_unbox(v_a_1147_);
lean_dec(v_a_1147_);
if (v___x_1148_ == 0)
{
lean_object* v___x_1149_; 
lean_dec(v_val_1145_);
lean_inc_ref(v_e_1101_);
v___x_1149_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_1101_, v_a_1102_, v_a_1106_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_);
if (lean_obj_tag(v___x_1149_) == 0)
{
lean_object* v_a_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1174_; 
v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1152_ = v___x_1149_;
v_isShared_1153_ = v_isSharedCheck_1174_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_a_1150_);
lean_dec(v___x_1149_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1174_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
uint8_t v___x_1154_; 
v___x_1154_ = lean_unbox(v_a_1150_);
lean_dec(v_a_1150_);
if (v___x_1154_ == 0)
{
lean_object* v___x_1155_; lean_object* v___x_1157_; 
lean_dec_ref(v_arg_1124_);
lean_dec_ref(v_arg_1121_);
lean_dec_ref(v_e_1101_);
v___x_1155_ = lean_box(0);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 0, v___x_1155_);
v___x_1157_ = v___x_1152_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v___x_1155_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
else
{
lean_object* v___x_1159_; 
lean_del_object(v___x_1152_);
lean_inc_ref(v_e_1101_);
v___x_1159_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_);
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_object* v_a_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; 
v_a_1160_ = lean_ctor_get(v___x_1159_, 0);
lean_inc(v_a_1160_);
lean_dec_ref_known(v___x_1159_, 1);
v___x_1161_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3);
v___x_1162_ = l_Lean_Meta_mkOfEqFalseCore(v_e_1101_, v_a_1160_);
v___x_1163_ = l_Lean_mkApp3(v___x_1161_, v_arg_1124_, v_arg_1121_, v___x_1162_);
v___x_1164_ = lean_unsigned_to_nat(0u);
v___x_1165_ = l_Lean_Meta_Grind_pushNewFact(v___x_1163_, v___x_1164_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_);
return v___x_1165_;
}
else
{
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1173_; 
lean_dec_ref(v_arg_1124_);
lean_dec_ref(v_arg_1121_);
lean_dec_ref(v_e_1101_);
v_a_1166_ = lean_ctor_get(v___x_1159_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1168_ = v___x_1159_;
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1159_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v___x_1171_; 
if (v_isShared_1169_ == 0)
{
v___x_1171_ = v___x_1168_;
goto v_reusejp_1170_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_a_1166_);
v___x_1171_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1170_;
}
v_reusejp_1170_:
{
return v___x_1171_;
}
}
}
}
}
}
else
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1182_; 
lean_dec_ref(v_arg_1124_);
lean_dec_ref(v_arg_1121_);
lean_dec_ref(v_e_1101_);
v_a_1175_ = lean_ctor_get(v___x_1149_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1149_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1177_ = v___x_1149_;
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___x_1149_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1180_; 
if (v_isShared_1178_ == 0)
{
v___x_1180_ = v___x_1177_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_a_1175_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
else
{
lean_object* v___x_1183_; 
lean_inc_ref(v_arg_1124_);
v___x_1183_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_1124_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_);
if (lean_obj_tag(v___x_1183_) == 0)
{
lean_object* v_a_1184_; lean_object* v_fst_1185_; lean_object* v_snd_1186_; lean_object* v___x_1187_; 
v_a_1184_ = lean_ctor_get(v___x_1183_, 0);
lean_inc(v_a_1184_);
lean_dec_ref_known(v___x_1183_, 1);
v_fst_1185_ = lean_ctor_get(v_a_1184_, 0);
lean_inc(v_fst_1185_);
v_snd_1186_ = lean_ctor_get(v_a_1184_, 1);
lean_inc(v_snd_1186_);
lean_dec(v_a_1184_);
lean_inc_ref(v_arg_1121_);
v___x_1187_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_1121_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_);
if (lean_obj_tag(v___x_1187_) == 0)
{
lean_object* v_a_1188_; lean_object* v_fst_1189_; lean_object* v_snd_1190_; lean_object* v___x_1191_; 
v_a_1188_ = lean_ctor_get(v___x_1187_, 0);
lean_inc(v_a_1188_);
lean_dec_ref_known(v___x_1187_, 1);
v_fst_1189_ = lean_ctor_get(v_a_1188_, 0);
lean_inc(v_fst_1189_);
v_snd_1190_ = lean_ctor_get(v_a_1188_, 1);
lean_inc(v_snd_1190_);
lean_dec(v_a_1188_);
v___x_1191_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1101_, v_a_1102_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_a_1192_; lean_object* v___x_1193_; 
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
lean_inc(v_a_1192_);
lean_dec_ref_known(v___x_1191_, 1);
lean_inc(v_fst_1189_);
v___x_1193_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_1189_, v_a_1192_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_object* v_a_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v_a_1194_ = lean_ctor_get(v___x_1193_, 0);
lean_inc(v_a_1194_);
lean_dec_ref_known(v___x_1193_, 1);
v___x_1195_ = l_Int_Internal_Linear_Expr_norm(v_a_1194_);
v___x_1196_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7);
v___x_1197_ = l_Lean_mkApp6(v___x_1196_, v_arg_1124_, v_arg_1121_, v_fst_1185_, v_fst_1189_, v_snd_1186_, v_snd_1190_);
lean_inc(v_val_1145_);
v___x_1198_ = lean_nat_to_int(v_val_1145_);
v___x_1199_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1199_, 0, v_e_1101_);
lean_ctor_set(v___x_1199_, 1, v___x_1197_);
lean_ctor_set(v___x_1199_, 2, v_val_1145_);
lean_ctor_set(v___x_1199_, 3, v_a_1194_);
v___x_1200_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1198_);
lean_ctor_set(v___x_1200_, 1, v___x_1195_);
lean_ctor_set(v___x_1200_, 2, v___x_1199_);
v___x_1201_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v___x_1200_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_);
return v___x_1201_;
}
else
{
lean_object* v_a_1202_; lean_object* v___x_1204_; uint8_t v_isShared_1205_; uint8_t v_isSharedCheck_1209_; 
lean_dec(v_snd_1190_);
lean_dec(v_fst_1189_);
lean_dec(v_snd_1186_);
lean_dec(v_fst_1185_);
lean_dec(v_val_1145_);
lean_dec_ref(v_arg_1124_);
lean_dec_ref(v_arg_1121_);
lean_dec_ref(v_e_1101_);
v_a_1202_ = lean_ctor_get(v___x_1193_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1193_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1204_ = v___x_1193_;
v_isShared_1205_ = v_isSharedCheck_1209_;
goto v_resetjp_1203_;
}
else
{
lean_inc(v_a_1202_);
lean_dec(v___x_1193_);
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
lean_dec(v_snd_1190_);
lean_dec(v_fst_1189_);
lean_dec(v_snd_1186_);
lean_dec(v_fst_1185_);
lean_dec(v_val_1145_);
lean_dec_ref(v_arg_1124_);
lean_dec_ref(v_arg_1121_);
lean_dec_ref(v_e_1101_);
v_a_1210_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1212_ = v___x_1191_;
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1191_);
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
else
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1225_; 
lean_dec(v_snd_1186_);
lean_dec(v_fst_1185_);
lean_dec(v_val_1145_);
lean_dec_ref(v_arg_1124_);
lean_dec_ref(v_arg_1121_);
lean_dec_ref(v_e_1101_);
v_a_1218_ = lean_ctor_get(v___x_1187_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1187_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1220_ = v___x_1187_;
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1187_);
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
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
lean_dec(v_val_1145_);
lean_dec_ref(v_arg_1124_);
lean_dec_ref(v_arg_1121_);
lean_dec_ref(v_e_1101_);
v_a_1226_ = lean_ctor_get(v___x_1183_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1183_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1228_ = v___x_1183_;
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1183_);
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
}
else
{
lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1241_; 
lean_dec(v_val_1145_);
lean_dec_ref(v_arg_1124_);
lean_dec_ref(v_arg_1121_);
lean_dec_ref(v_e_1101_);
v_a_1234_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1236_ = v___x_1146_;
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_dec(v___x_1146_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1239_; 
if (v_isShared_1237_ == 0)
{
v___x_1239_ = v___x_1236_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_a_1234_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
}
else
{
lean_object* v___x_1242_; 
lean_dec(v_a_1144_);
lean_dec_ref(v_arg_1124_);
lean_dec_ref(v_arg_1121_);
v___x_1242_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1106_);
if (lean_obj_tag(v___x_1242_) == 0)
{
lean_object* v_a_1243_; uint8_t v_verbose_1244_; 
v_a_1243_ = lean_ctor_get(v___x_1242_, 0);
lean_inc(v_a_1243_);
lean_dec_ref_known(v___x_1242_, 1);
v_verbose_1244_ = lean_ctor_get_uint8(v_a_1243_, 0);
lean_dec(v_a_1243_);
if (v_verbose_1244_ == 0)
{
lean_dec_ref(v_e_1101_);
goto v___jp_1116_;
}
else
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; 
v___x_1245_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10);
v___x_1246_ = l_Lean_indentExpr(v_e_1101_);
v___x_1247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1245_);
lean_ctor_set(v___x_1247_, 1, v___x_1246_);
v___x_1248_ = l_Lean_Meta_Sym_reportIssue(v___x_1247_, v_a_1106_, v_a_1107_, v_a_1108_, v_a_1109_, v_a_1110_, v_a_1111_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_dec_ref_known(v___x_1248_, 1);
goto v___jp_1116_;
}
else
{
return v___x_1248_;
}
}
}
else
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1256_; 
lean_dec_ref(v_e_1101_);
v_a_1249_ = lean_ctor_get(v___x_1242_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1242_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1251_ = v___x_1242_;
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1242_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1254_; 
if (v_isShared_1252_ == 0)
{
v___x_1254_ = v___x_1251_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_a_1249_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
}
}
else
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1264_; 
lean_dec_ref(v_arg_1124_);
lean_dec_ref(v_arg_1121_);
lean_dec_ref(v_e_1101_);
v_a_1257_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1259_ = v___x_1143_;
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1143_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1262_; 
if (v_isShared_1260_ == 0)
{
v___x_1262_ = v___x_1259_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_a_1257_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
}
}
}
else
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_dec_ref(v_arg_1124_);
lean_dec_ref(v_arg_1121_);
lean_dec_ref(v_e_1101_);
v_a_1266_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1133_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1133_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
}
}
}
}
v___jp_1113_:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1114_ = lean_box(0);
v___x_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1115_, 0, v___x_1114_);
return v___x_1115_;
}
v___jp_1116_:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = lean_box(0);
v___x_1118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1117_);
return v___x_1118_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___boxed(lean_object* v_e_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_){
_start:
{
lean_object* v_res_1286_; 
v_res_1286_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(v_e_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_);
lean_dec(v_a_1284_);
lean_dec_ref(v_a_1283_);
lean_dec(v_a_1282_);
lean_dec_ref(v_a_1281_);
lean_dec(v_a_1280_);
lean_dec_ref(v_a_1279_);
lean_dec(v_a_1278_);
lean_dec_ref(v_a_1277_);
lean_dec(v_a_1276_);
lean_dec(v_a_1275_);
return v_res_1286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(lean_object* v_e_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_){
_start:
{
lean_object* v___x_1301_; 
v___x_1301_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1292_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1346_; 
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1304_ = v___x_1301_;
v_isShared_1305_ = v_isSharedCheck_1346_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_dec(v___x_1301_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1346_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
uint8_t v_lia_1306_; 
v_lia_1306_ = lean_ctor_get_uint8(v_a_1302_, sizeof(void*)*13 + 23);
lean_dec(v_a_1302_);
if (v_lia_1306_ == 0)
{
lean_object* v___x_1307_; lean_object* v___x_1309_; 
lean_dec_ref(v_e_1289_);
v___x_1307_ = lean_box(0);
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 0, v___x_1307_);
v___x_1309_ = v___x_1304_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___x_1307_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
else
{
lean_object* v___x_1311_; 
lean_del_object(v___x_1304_);
lean_inc_ref(v_e_1289_);
v___x_1311_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1289_, v_a_1297_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1337_; 
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1314_ = v___x_1311_;
v_isShared_1315_ = v_isSharedCheck_1337_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1311_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1337_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1321_; uint8_t v___x_1322_; 
v___x_1321_ = l_Lean_Expr_cleanupAnnotations(v_a_1312_);
v___x_1322_ = l_Lean_Expr_isApp(v___x_1321_);
if (v___x_1322_ == 0)
{
lean_dec_ref(v___x_1321_);
lean_dec_ref(v_e_1289_);
goto v___jp_1316_;
}
else
{
lean_object* v___x_1323_; uint8_t v___x_1324_; 
v___x_1323_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1321_);
v___x_1324_ = l_Lean_Expr_isApp(v___x_1323_);
if (v___x_1324_ == 0)
{
lean_dec_ref(v___x_1323_);
lean_dec_ref(v_e_1289_);
goto v___jp_1316_;
}
else
{
lean_object* v___x_1325_; uint8_t v___x_1326_; 
v___x_1325_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1323_);
v___x_1326_ = l_Lean_Expr_isApp(v___x_1325_);
if (v___x_1326_ == 0)
{
lean_dec_ref(v___x_1325_);
lean_dec_ref(v_e_1289_);
goto v___jp_1316_;
}
else
{
lean_object* v___x_1327_; uint8_t v___x_1328_; 
v___x_1327_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1325_);
v___x_1328_ = l_Lean_Expr_isApp(v___x_1327_);
if (v___x_1328_ == 0)
{
lean_dec_ref(v___x_1327_);
lean_dec_ref(v_e_1289_);
goto v___jp_1316_;
}
else
{
lean_object* v_arg_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; uint8_t v___x_1332_; 
v_arg_1329_ = lean_ctor_get(v___x_1327_, 1);
lean_inc_ref(v_arg_1329_);
v___x_1330_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1327_);
v___x_1331_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1332_ = l_Lean_Expr_isConstOf(v___x_1330_, v___x_1331_);
lean_dec_ref(v___x_1330_);
if (v___x_1332_ == 0)
{
lean_dec_ref(v_arg_1329_);
lean_dec_ref(v_e_1289_);
goto v___jp_1316_;
}
else
{
lean_object* v___x_1333_; uint8_t v___x_1334_; 
lean_del_object(v___x_1314_);
v___x_1333_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0));
v___x_1334_ = l_Lean_Expr_isConstOf(v_arg_1329_, v___x_1333_);
lean_dec_ref(v_arg_1329_);
if (v___x_1334_ == 0)
{
lean_object* v___x_1335_; 
v___x_1335_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(v_e_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_);
return v___x_1335_;
}
else
{
lean_object* v___x_1336_; 
v___x_1336_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(v_e_1289_, v_a_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_, v_a_1299_);
return v___x_1336_;
}
}
}
}
}
}
v___jp_1316_:
{
lean_object* v___x_1317_; lean_object* v___x_1319_; 
v___x_1317_ = lean_box(0);
if (v_isShared_1315_ == 0)
{
lean_ctor_set(v___x_1314_, 0, v___x_1317_);
v___x_1319_ = v___x_1314_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1320_; 
v_reuseFailAlloc_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1320_, 0, v___x_1317_);
v___x_1319_ = v_reuseFailAlloc_1320_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
return v___x_1319_;
}
}
}
}
else
{
lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1345_; 
lean_dec_ref(v_e_1289_);
v_a_1338_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1340_ = v___x_1311_;
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1311_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1343_; 
if (v_isShared_1341_ == 0)
{
v___x_1343_ = v___x_1340_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_a_1338_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
}
}
}
else
{
lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1354_; 
lean_dec_ref(v_e_1289_);
v_a_1347_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1349_ = v___x_1301_;
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v___x_1301_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1352_; 
if (v_isShared_1350_ == 0)
{
v___x_1352_ = v___x_1349_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v_a_1347_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed(lean_object* v_e_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_, lean_object* v_a_1363_, lean_object* v_a_1364_, lean_object* v_a_1365_, lean_object* v_a_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(v_e_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_, v_a_1360_, v_a_1361_, v_a_1362_, v_a_1363_, v_a_1364_, v_a_1365_);
lean_dec(v_a_1365_);
lean_dec_ref(v_a_1364_);
lean_dec(v_a_1363_);
lean_dec_ref(v_a_1362_);
lean_dec(v_a_1361_);
lean_dec_ref(v_a_1360_);
lean_dec(v_a_1359_);
lean_dec_ref(v_a_1358_);
lean_dec(v_a_1357_);
lean_dec(v_a_1356_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_8_(){
_start:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; 
v___x_1369_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1370_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed), 12, 0);
v___x_1371_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_1369_, v___x_1370_);
return v___x_1371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_8____boxed(lean_object* v_a_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_8_();
return v_res_1373_;
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
