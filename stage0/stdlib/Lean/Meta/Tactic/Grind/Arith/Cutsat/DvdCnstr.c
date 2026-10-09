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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
v___x_12_ = l_Int_Internal_Linear_Poly_getConst(v___y_10_);
v___x_13_ = lean_int_emod(v___x_12_, v___y_11_);
lean_dec(v___x_12_);
v___x_14_ = lean_int_dec_eq(v___x_13_, v___y_8_);
lean_dec(v___x_13_);
if (v___x_14_ == 0)
{
lean_dec(v___y_11_);
lean_dec_ref(v___y_10_);
lean_dec(v___y_9_);
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
v___x_17_ = lean_int_ediv(v___y_9_, v___y_11_);
lean_dec(v___y_9_);
v___x_18_ = l_Int_Internal_Linear_Poly_div(v___y_11_, v___y_10_);
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
lean_dec_ref(v___y_10_);
lean_dec(v___y_9_);
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
v___y_8_ = v___x_26_;
v___y_9_ = v_d_23_;
v___y_10_ = v_p_24_;
v___y_11_ = v_g_25_;
goto v___jp_6_;
}
else
{
lean_object* v___x_28_; 
v___x_28_ = lean_int_neg(v_g_25_);
lean_dec(v_g_25_);
v___y_7_ = v___y_22_;
v___y_8_ = v___x_26_;
v___y_9_ = v_d_23_;
v___y_10_ = v_p_24_;
v___y_11_ = v___x_28_;
goto v___jp_6_;
}
}
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0_spec__0(lean_object* v_msgData_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_){
_start:
{
lean_object* v___x_41_; lean_object* v_env_42_; uint8_t v___x_43_; lean_object* v_env_44_; lean_object* v___x_45_; lean_object* v_toCold_46_; lean_object* v_mctx_47_; lean_object* v_lctx_48_; lean_object* v_options_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_41_ = lean_st_ref_get(v___y_39_);
v_env_42_ = lean_ctor_get(v___x_41_, 0);
lean_inc_ref(v_env_42_);
lean_dec(v___x_41_);
v___x_43_ = 0;
v_env_44_ = l_Lean_Environment_setRecordingDeps(v_env_42_, v___x_43_);
v___x_45_ = lean_st_ref_get(v___y_37_);
v_toCold_46_ = lean_ctor_get(v___y_38_, 0);
v_mctx_47_ = lean_ctor_get(v___x_45_, 0);
lean_inc_ref(v_mctx_47_);
lean_dec(v___x_45_);
v_lctx_48_ = lean_ctor_get(v___y_36_, 2);
v_options_49_ = lean_ctor_get(v_toCold_46_, 2);
lean_inc_ref(v_options_49_);
lean_inc_ref(v_lctx_48_);
v___x_50_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_50_, 0, v_env_44_);
lean_ctor_set(v___x_50_, 1, v_mctx_47_);
lean_ctor_set(v___x_50_, 2, v_lctx_48_);
lean_ctor_set(v___x_50_, 3, v_options_49_);
v___x_51_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_51_, 0, v___x_50_);
lean_ctor_set(v___x_51_, 1, v_msgData_35_);
v___x_52_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_35_ = stack[0].m_obj;
lean_object* v___y_36_ = stack[1].m_obj;
lean_object* v___y_37_ = stack[2].m_obj;
lean_object* v___y_38_ = stack[3].m_obj;
lean_object* v___y_39_ = stack[4].m_obj;
lean_object* v_res_53_;
v_res_53_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0_spec__0(v_msgData_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_);
stack->m_obj
 = v_res_53_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0_spec__0___boxed(lean_object* v_msgData_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0_spec__0(v_msgData_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_);
lean_dec(v___y_58_);
lean_dec_ref(v___y_57_);
lean_dec(v___y_56_);
lean_dec_ref(v___y_55_);
return v_res_60_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_61_; double v___x_62_; 
v___x_61_ = lean_unsigned_to_nat(0u);
v___x_62_ = lean_float_of_nat(v___x_61_);
return v___x_62_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(lean_object* v_cls_66_, lean_object* v_msg_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_, lean_object* v___y_71_){
_start:
{
lean_object* v_ref_73_; lean_object* v___x_74_; lean_object* v_a_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_120_; 
v_ref_73_ = lean_ctor_get(v___y_70_, 2);
v___x_74_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0_spec__0(v_msg_67_, v___y_68_, v___y_69_, v___y_70_, v___y_71_);
v_a_75_ = lean_ctor_get(v___x_74_, 0);
v_isSharedCheck_120_ = !lean_is_exclusive(v___x_74_);
if (v_isSharedCheck_120_ == 0)
{
v___x_77_ = v___x_74_;
v_isShared_78_ = v_isSharedCheck_120_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_a_75_);
lean_dec(v___x_74_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_120_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_79_; lean_object* v_traceState_80_; lean_object* v_env_81_; lean_object* v_nextMacroScope_82_; lean_object* v_ngen_83_; lean_object* v_auxDeclNGen_84_; lean_object* v_cache_85_; lean_object* v_recordedDeps_86_; lean_object* v_messages_87_; lean_object* v_infoState_88_; lean_object* v_snapshotTasks_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_119_; 
v___x_79_ = lean_st_ref_take(v___y_71_);
v_traceState_80_ = lean_ctor_get(v___x_79_, 4);
v_env_81_ = lean_ctor_get(v___x_79_, 0);
v_nextMacroScope_82_ = lean_ctor_get(v___x_79_, 1);
v_ngen_83_ = lean_ctor_get(v___x_79_, 2);
v_auxDeclNGen_84_ = lean_ctor_get(v___x_79_, 3);
v_cache_85_ = lean_ctor_get(v___x_79_, 5);
v_recordedDeps_86_ = lean_ctor_get(v___x_79_, 6);
v_messages_87_ = lean_ctor_get(v___x_79_, 7);
v_infoState_88_ = lean_ctor_get(v___x_79_, 8);
v_snapshotTasks_89_ = lean_ctor_get(v___x_79_, 9);
v_isSharedCheck_119_ = !lean_is_exclusive(v___x_79_);
if (v_isSharedCheck_119_ == 0)
{
v___x_91_ = v___x_79_;
v_isShared_92_ = v_isSharedCheck_119_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_snapshotTasks_89_);
lean_inc(v_infoState_88_);
lean_inc(v_messages_87_);
lean_inc(v_recordedDeps_86_);
lean_inc(v_cache_85_);
lean_inc(v_traceState_80_);
lean_inc(v_auxDeclNGen_84_);
lean_inc(v_ngen_83_);
lean_inc(v_nextMacroScope_82_);
lean_inc(v_env_81_);
lean_dec(v___x_79_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_119_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
uint64_t v_tid_93_; lean_object* v_traces_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_118_; 
v_tid_93_ = lean_ctor_get_uint64(v_traceState_80_, sizeof(void*)*1);
v_traces_94_ = lean_ctor_get(v_traceState_80_, 0);
v_isSharedCheck_118_ = !lean_is_exclusive(v_traceState_80_);
if (v_isSharedCheck_118_ == 0)
{
v___x_96_ = v_traceState_80_;
v_isShared_97_ = v_isSharedCheck_118_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_traces_94_);
lean_dec(v_traceState_80_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_118_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_98_; lean_object* v___x_99_; double v___x_100_; uint8_t v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_109_; 
v___x_98_ = lean_box(0);
v___x_99_ = lean_box(0);
v___x_100_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__0);
v___x_101_ = 0;
v___x_102_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__1));
v___x_103_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_103_, 0, v_cls_66_);
lean_ctor_set(v___x_103_, 1, v___x_99_);
lean_ctor_set(v___x_103_, 2, v___x_102_);
lean_ctor_set_float(v___x_103_, sizeof(void*)*3, v___x_100_);
lean_ctor_set_float(v___x_103_, sizeof(void*)*3 + 8, v___x_100_);
lean_ctor_set_uint8(v___x_103_, sizeof(void*)*3 + 16, v___x_101_);
v___x_104_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg___closed__2));
v___x_105_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_105_, 0, v___x_103_);
lean_ctor_set(v___x_105_, 1, v_a_75_);
lean_ctor_set(v___x_105_, 2, v___x_104_);
lean_inc(v_ref_73_);
v___x_106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_106_, 0, v_ref_73_);
lean_ctor_set(v___x_106_, 1, v___x_105_);
v___x_107_ = l_Lean_PersistentArray_push___redArg(v_traces_94_, v___x_106_);
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 0, v___x_107_);
v___x_109_ = v___x_96_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_107_);
lean_ctor_set_uint64(v_reuseFailAlloc_117_, sizeof(void*)*1, v_tid_93_);
v___x_109_ = v_reuseFailAlloc_117_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v___x_111_; 
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 4, v___x_109_);
v___x_111_ = v___x_91_;
goto v_reusejp_110_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_env_81_);
lean_ctor_set(v_reuseFailAlloc_116_, 1, v_nextMacroScope_82_);
lean_ctor_set(v_reuseFailAlloc_116_, 2, v_ngen_83_);
lean_ctor_set(v_reuseFailAlloc_116_, 3, v_auxDeclNGen_84_);
lean_ctor_set(v_reuseFailAlloc_116_, 4, v___x_109_);
lean_ctor_set(v_reuseFailAlloc_116_, 5, v_cache_85_);
lean_ctor_set(v_reuseFailAlloc_116_, 6, v_recordedDeps_86_);
lean_ctor_set(v_reuseFailAlloc_116_, 7, v_messages_87_);
lean_ctor_set(v_reuseFailAlloc_116_, 8, v_infoState_88_);
lean_ctor_set(v_reuseFailAlloc_116_, 9, v_snapshotTasks_89_);
v___x_111_ = v_reuseFailAlloc_116_;
goto v_reusejp_110_;
}
v_reusejp_110_:
{
lean_object* v___x_112_; lean_object* v___x_114_; 
v___x_112_ = lean_st_ref_put(v___y_71_, v___x_111_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 0, v___x_98_);
v___x_114_ = v___x_77_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v___x_98_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
return v___x_114_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_66_ = stack[0].m_obj;
lean_object* v_msg_67_ = stack[1].m_obj;
lean_object* v___y_68_ = stack[2].m_obj;
lean_object* v___y_69_ = stack[3].m_obj;
lean_object* v___y_70_ = stack[4].m_obj;
lean_object* v___y_71_ = stack[5].m_obj;
lean_object* v_res_121_;
v_res_121_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v_cls_66_, v_msg_67_, v___y_68_, v___y_69_, v___y_70_, v___y_71_);
stack->m_obj
 = v_res_121_;
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
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(lean_object* v_a_148_, lean_object* v_x_149_, lean_object* v_c_u2081_150_, lean_object* v_b_151_, lean_object* v_c_u2082_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_, lean_object* v_a_162_){
_start:
{
lean_object* v_toCold_164_; lean_object* v_options_165_; lean_object* v_p_166_; lean_object* v_d_167_; lean_object* v_p_168_; lean_object* v_inheritedTraceOptions_169_; uint8_t v_hasTrace_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v_d_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v_p_177_; 
v_toCold_164_ = lean_ctor_get(v_a_161_, 0);
v_options_165_ = lean_ctor_get(v_toCold_164_, 2);
v_p_166_ = lean_ctor_get(v_c_u2081_150_, 0);
v_d_167_ = lean_ctor_get(v_c_u2082_152_, 0);
v_p_168_ = lean_ctor_get(v_c_u2082_152_, 1);
v_inheritedTraceOptions_169_ = lean_ctor_get(v_toCold_164_, 11);
v_hasTrace_170_ = lean_ctor_get_uint8(v_options_165_, sizeof(void*)*1);
v___x_171_ = lean_int_mul(v_a_148_, v_d_167_);
v___x_172_ = lean_nat_abs(v___x_171_);
lean_dec(v___x_171_);
v_d_173_ = lean_nat_to_int(v___x_172_);
lean_inc_ref(v_p_168_);
v___x_174_ = l_Int_Internal_Linear_Poly_mul(v_p_168_, v_a_148_);
v___x_175_ = lean_int_neg(v_b_151_);
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
v___x_185_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_x_149_, v_a_153_, v_a_161_);
if (lean_obj_tag(v___x_185_) == 0)
{
lean_object* v_a_186_; lean_object* v___x_187_; 
v_a_186_ = lean_ctor_get(v___x_185_, 0);
lean_inc(v_a_186_);
lean_dec_ref_known(v___x_185_, 1);
lean_inc_ref(v_c_u2081_150_);
v___x_187_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_u2081_150_, v_a_153_, v_a_161_);
if (lean_obj_tag(v___x_187_) == 0)
{
lean_object* v_a_188_; lean_object* v___x_189_; 
v_a_188_ = lean_ctor_get(v___x_187_, 0);
lean_inc(v_a_188_);
lean_dec_ref_known(v___x_187_, 1);
lean_inc_ref(v_c_u2082_152_);
v___x_189_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_u2082_152_, v_a_153_, v_a_161_);
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
v___x_197_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v_cls_182_, v___x_196_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
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
lean_dec_ref(v_c_u2082_152_);
lean_dec_ref(v_c_u2081_150_);
lean_dec(v_x_149_);
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
lean_dec_ref(v_c_u2082_152_);
lean_dec_ref(v_c_u2081_150_);
lean_dec(v_x_149_);
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
lean_dec_ref(v_c_u2082_152_);
lean_dec_ref(v_c_u2081_150_);
lean_dec(v_x_149_);
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
lean_dec_ref(v_c_u2082_152_);
lean_dec_ref(v_c_u2081_150_);
lean_dec(v_x_149_);
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
lean_ctor_set(v___x_179_, 0, v_x_149_);
lean_ctor_set(v___x_179_, 1, v_c_u2081_150_);
lean_ctor_set(v___x_179_, 2, v_c_u2082_152_);
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
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_148_ = stack[0].m_obj;
lean_object* v_x_149_ = stack[1].m_obj;
lean_object* v_c_u2081_150_ = stack[2].m_obj;
lean_object* v_b_151_ = stack[3].m_obj;
lean_object* v_c_u2082_152_ = stack[4].m_obj;
lean_object* v_a_153_ = stack[5].m_obj;
lean_object* v_a_154_ = stack[6].m_obj;
lean_object* v_a_155_ = stack[7].m_obj;
lean_object* v_a_156_ = stack[8].m_obj;
lean_object* v_a_157_ = stack[9].m_obj;
lean_object* v_a_158_ = stack[10].m_obj;
lean_object* v_a_159_ = stack[11].m_obj;
lean_object* v_a_160_ = stack[12].m_obj;
lean_object* v_a_161_ = stack[13].m_obj;
lean_object* v_a_162_ = stack[14].m_obj;
lean_object* v_res_230_;
v_res_230_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(v_a_148_, v_x_149_, v_c_u2081_150_, v_b_151_, v_c_u2082_152_, v_a_153_, v_a_154_, v_a_155_, v_a_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_, v_a_161_, v_a_162_);
stack->m_obj
 = v_res_230_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___boxed(lean_object* v_a_231_, lean_object* v_x_232_, lean_object* v_c_u2081_233_, lean_object* v_b_234_, lean_object* v_c_u2082_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(v_a_231_, v_x_232_, v_c_u2081_233_, v_b_234_, v_c_u2082_235_, v_a_236_, v_a_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_);
lean_dec(v_a_245_);
lean_dec_ref(v_a_244_);
lean_dec(v_a_243_);
lean_dec_ref(v_a_242_);
lean_dec(v_a_241_);
lean_dec_ref(v_a_240_);
lean_dec(v_a_239_);
lean_dec_ref(v_a_238_);
lean_dec(v_a_237_);
lean_dec(v_a_236_);
lean_dec(v_b_234_);
lean_dec(v_a_231_);
return v_res_247_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0(lean_object* v_cls_248_, lean_object* v_msg_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v_cls_248_, v_msg_249_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
return v___x_261_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_248_ = stack[0].m_obj;
lean_object* v_msg_249_ = stack[1].m_obj;
lean_object* v___y_250_ = stack[2].m_obj;
lean_object* v___y_251_ = stack[3].m_obj;
lean_object* v___y_252_ = stack[4].m_obj;
lean_object* v___y_253_ = stack[5].m_obj;
lean_object* v___y_254_ = stack[6].m_obj;
lean_object* v___y_255_ = stack[7].m_obj;
lean_object* v___y_256_ = stack[8].m_obj;
lean_object* v___y_257_ = stack[9].m_obj;
lean_object* v___y_258_ = stack[10].m_obj;
lean_object* v___y_259_ = stack[11].m_obj;
lean_object* v_res_262_;
v_res_262_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0(v_cls_248_, v_msg_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
stack->m_obj
 = v_res_262_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___boxed(lean_object* v_cls_263_, lean_object* v_msg_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0(v_cls_263_, v_msg_264_, v___y_265_, v___y_266_, v___y_267_, v___y_268_, v___y_269_, v___y_270_, v___y_271_, v___y_272_, v___y_273_, v___y_274_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
lean_dec(v___y_270_);
lean_dec_ref(v___y_269_);
lean_dec(v___y_268_);
lean_dec_ref(v___y_267_);
lean_dec(v___y_266_);
lean_dec(v___y_265_);
return v_res_276_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = l_Lean_maxRecDepthErrorMessage;
v___x_283_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
return v___x_283_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__3);
v___x_285_ = l_Lean_MessageData_ofFormat(v___x_284_);
return v___x_285_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_286_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__4);
v___x_287_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__2));
v___x_288_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
lean_ctor_set(v___x_288_, 1, v___x_286_);
return v___x_288_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(lean_object* v_ref_289_){
_start:
{
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_291_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___closed__5);
v___x_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_292_, 0, v_ref_289_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
v___x_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
return v___x_293_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_289_ = stack[0].m_obj;
lean_object* v_res_294_;
v_res_294_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_289_);
stack->m_obj
 = v_res_294_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg___boxed(lean_object* v_ref_295_, lean_object* v___y_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_295_);
return v_res_297_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0(lean_object* v_00_u03b1_298_, lean_object* v_ref_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_){
_start:
{
lean_object* v___x_311_; 
v___x_311_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_299_);
return v___x_311_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_299_ = stack[1].m_obj;
lean_object* v___y_300_ = stack[2].m_obj;
lean_object* v___y_301_ = stack[3].m_obj;
lean_object* v___y_302_ = stack[4].m_obj;
lean_object* v___y_303_ = stack[5].m_obj;
lean_object* v___y_304_ = stack[6].m_obj;
lean_object* v___y_305_ = stack[7].m_obj;
lean_object* v___y_306_ = stack[8].m_obj;
lean_object* v___y_307_ = stack[9].m_obj;
lean_object* v___y_308_ = stack[10].m_obj;
lean_object* v___y_309_ = stack[11].m_obj;
lean_object* v_res_312_;
v_res_312_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0(lean_box(0), v_ref_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
stack->m_obj
 = v_res_312_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___boxed(lean_object* v_00_u03b1_313_, lean_object* v_ref_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0(v_00_u03b1_313_, v_ref_314_, v___y_315_, v___y_316_, v___y_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
lean_dec(v___y_322_);
lean_dec_ref(v___y_321_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
lean_dec(v___y_318_);
lean_dec_ref(v___y_317_);
lean_dec(v___y_316_);
lean_dec(v___y_315_);
return v_res_326_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(lean_object* v_c_327_, lean_object* v_a_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_){
_start:
{
lean_object* v_p_339_; lean_object* v_toCold_340_; lean_object* v_currRecDepth_341_; lean_object* v_ref_342_; uint16_t v_optionFlags_343_; uint8_t v_suppressElabErrors_344_; uint8_t v_isRecordingDeps_345_; lean_object* v_maxRecDepth_377_; lean_object* v___x_378_; uint8_t v___x_379_; 
v_p_339_ = lean_ctor_get(v_c_327_, 1);
v_toCold_340_ = lean_ctor_get(v_a_336_, 0);
lean_inc_ref(v_toCold_340_);
v_currRecDepth_341_ = lean_ctor_get(v_a_336_, 1);
lean_inc(v_currRecDepth_341_);
v_ref_342_ = lean_ctor_get(v_a_336_, 2);
lean_inc(v_ref_342_);
v_optionFlags_343_ = lean_ctor_get_uint16(v_a_336_, sizeof(void*)*3);
v_suppressElabErrors_344_ = lean_ctor_get_uint8(v_a_336_, sizeof(void*)*3 + 2);
v_isRecordingDeps_345_ = lean_ctor_get_uint8(v_a_336_, sizeof(void*)*3 + 3);
lean_dec_ref(v_a_336_);
v_maxRecDepth_377_ = lean_ctor_get(v_toCold_340_, 3);
v___x_378_ = lean_unsigned_to_nat(0u);
v___x_379_ = lean_nat_dec_eq(v_maxRecDepth_377_, v___x_378_);
if (v___x_379_ == 0)
{
uint8_t v___x_380_; 
v___x_380_ = lean_nat_dec_eq(v_currRecDepth_341_, v_maxRecDepth_377_);
if (v___x_380_ == 0)
{
goto v___jp_346_;
}
else
{
lean_object* v___x_381_; 
lean_dec(v_currRecDepth_341_);
lean_dec_ref(v_toCold_340_);
lean_dec_ref(v_c_327_);
v___x_381_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_342_);
return v___x_381_;
}
}
else
{
goto v___jp_346_;
}
v___jp_346_:
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_347_ = lean_unsigned_to_nat(1u);
v___x_348_ = lean_nat_add(v_currRecDepth_341_, v___x_347_);
lean_dec(v_currRecDepth_341_);
v___x_349_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_349_, 0, v_toCold_340_);
lean_ctor_set(v___x_349_, 1, v___x_348_);
lean_ctor_set(v___x_349_, 2, v_ref_342_);
lean_ctor_set_uint16(v___x_349_, sizeof(void*)*3, v_optionFlags_343_);
lean_ctor_set_uint8(v___x_349_, sizeof(void*)*3 + 2, v_suppressElabErrors_344_);
lean_ctor_set_uint8(v___x_349_, sizeof(void*)*3 + 3, v_isRecordingDeps_345_);
lean_inc_ref(v_p_339_);
v___x_350_ = l_Int_Internal_Linear_Poly_findVarToSubst___redArg(v_p_339_, v_a_328_, v___x_349_);
if (lean_obj_tag(v___x_350_) == 0)
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_368_; 
v_a_351_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_368_ == 0)
{
v___x_353_ = v___x_350_;
v_isShared_354_ = v_isSharedCheck_368_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_350_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_368_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
if (lean_obj_tag(v_a_351_) == 1)
{
lean_object* v_val_355_; lean_object* v_snd_356_; lean_object* v_snd_357_; lean_object* v_fst_358_; lean_object* v_fst_359_; lean_object* v_p_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
lean_del_object(v___x_353_);
v_val_355_ = lean_ctor_get(v_a_351_, 0);
lean_inc(v_val_355_);
lean_dec_ref_known(v_a_351_, 1);
v_snd_356_ = lean_ctor_get(v_val_355_, 1);
lean_inc(v_snd_356_);
v_snd_357_ = lean_ctor_get(v_snd_356_, 1);
lean_inc(v_snd_357_);
v_fst_358_ = lean_ctor_get(v_val_355_, 0);
lean_inc(v_fst_358_);
lean_dec(v_val_355_);
v_fst_359_ = lean_ctor_get(v_snd_356_, 0);
lean_inc(v_fst_359_);
lean_dec(v_snd_356_);
v_p_360_ = lean_ctor_get(v_snd_357_, 0);
v___x_361_ = l_Int_Internal_Linear_Poly_coeff(v_p_360_, v_fst_359_);
v___x_362_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(v___x_361_, v_fst_359_, v_snd_357_, v_fst_358_, v_c_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v___x_349_, v_a_337_);
lean_dec(v_fst_358_);
lean_dec(v___x_361_);
if (lean_obj_tag(v___x_362_) == 0)
{
lean_object* v_a_363_; 
v_a_363_ = lean_ctor_get(v___x_362_, 0);
lean_inc(v_a_363_);
lean_dec_ref_known(v___x_362_, 1);
v_c_327_ = v_a_363_;
v_a_336_ = v___x_349_;
goto _start;
}
else
{
lean_dec_ref_known(v___x_349_, 3);
return v___x_362_;
}
}
else
{
lean_object* v___x_366_; 
lean_dec(v_a_351_);
lean_dec_ref_known(v___x_349_, 3);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 0, v_c_327_);
v___x_366_ = v___x_353_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_c_327_);
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
else
{
lean_object* v_a_369_; lean_object* v___x_371_; uint8_t v_isShared_372_; uint8_t v_isSharedCheck_376_; 
lean_dec_ref_known(v___x_349_, 3);
lean_dec_ref(v_c_327_);
v_a_369_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_376_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_376_ == 0)
{
v___x_371_ = v___x_350_;
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
else
{
lean_inc(v_a_369_);
lean_dec(v___x_350_);
v___x_371_ = lean_box(0);
v_isShared_372_ = v_isSharedCheck_376_;
goto v_resetjp_370_;
}
v_resetjp_370_:
{
lean_object* v___x_374_; 
if (v_isShared_372_ == 0)
{
v___x_374_ = v___x_371_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_a_369_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_327_ = stack[0].m_obj;
lean_object* v_a_328_ = stack[1].m_obj;
lean_object* v_a_329_ = stack[2].m_obj;
lean_object* v_a_330_ = stack[3].m_obj;
lean_object* v_a_331_ = stack[4].m_obj;
lean_object* v_a_332_ = stack[5].m_obj;
lean_object* v_a_333_ = stack[6].m_obj;
lean_object* v_a_334_ = stack[7].m_obj;
lean_object* v_a_335_ = stack[8].m_obj;
lean_object* v_a_336_ = stack[9].m_obj;
lean_object* v_a_337_ = stack[10].m_obj;
lean_object* v_res_382_;
v_res_382_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(v_c_327_, v_a_328_, v_a_329_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_);
stack->m_obj
 = v_res_382_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___boxed(lean_object* v_c_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_, lean_object* v_a_387_, lean_object* v_a_388_, lean_object* v_a_389_, lean_object* v_a_390_, lean_object* v_a_391_, lean_object* v_a_392_, lean_object* v_a_393_, lean_object* v_a_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(v_c_383_, v_a_384_, v_a_385_, v_a_386_, v_a_387_, v_a_388_, v_a_389_, v_a_390_, v_a_391_, v_a_392_, v_a_393_);
lean_dec(v_a_393_);
lean_dec(v_a_391_);
lean_dec_ref(v_a_390_);
lean_dec(v_a_389_);
lean_dec_ref(v_a_388_);
lean_dec(v_a_387_);
lean_dec_ref(v_a_386_);
lean_dec(v_a_385_);
lean_dec(v_a_384_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(lean_object* v_a_396_, lean_object* v_v_397_, lean_object* v_s_398_){
_start:
{
lean_object* v_vars_399_; lean_object* v_varMap_400_; lean_object* v_varsHistory_401_; lean_object* v_natToIntMap_402_; lean_object* v_natDef_403_; lean_object* v_dvds_404_; lean_object* v_lowers_405_; lean_object* v_uppers_406_; lean_object* v_diseqs_407_; lean_object* v_elimEqs_408_; lean_object* v_elimStack_409_; lean_object* v_occurs_410_; lean_object* v_assignment_411_; lean_object* v_nextCnstrId_412_; uint8_t v_caseSplits_413_; lean_object* v_steps_414_; lean_object* v_conflict_x3f_415_; lean_object* v_diseqSplits_416_; lean_object* v_divMod_417_; uint8_t v_usedCommRing_418_; lean_object* v_nonlinearOccs_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_428_; 
v_vars_399_ = lean_ctor_get(v_s_398_, 0);
v_varMap_400_ = lean_ctor_get(v_s_398_, 1);
v_varsHistory_401_ = lean_ctor_get(v_s_398_, 2);
v_natToIntMap_402_ = lean_ctor_get(v_s_398_, 3);
v_natDef_403_ = lean_ctor_get(v_s_398_, 4);
v_dvds_404_ = lean_ctor_get(v_s_398_, 5);
v_lowers_405_ = lean_ctor_get(v_s_398_, 6);
v_uppers_406_ = lean_ctor_get(v_s_398_, 7);
v_diseqs_407_ = lean_ctor_get(v_s_398_, 8);
v_elimEqs_408_ = lean_ctor_get(v_s_398_, 9);
v_elimStack_409_ = lean_ctor_get(v_s_398_, 10);
v_occurs_410_ = lean_ctor_get(v_s_398_, 11);
v_assignment_411_ = lean_ctor_get(v_s_398_, 12);
v_nextCnstrId_412_ = lean_ctor_get(v_s_398_, 13);
v_caseSplits_413_ = lean_ctor_get_uint8(v_s_398_, sizeof(void*)*19);
v_steps_414_ = lean_ctor_get(v_s_398_, 14);
v_conflict_x3f_415_ = lean_ctor_get(v_s_398_, 15);
v_diseqSplits_416_ = lean_ctor_get(v_s_398_, 16);
v_divMod_417_ = lean_ctor_get(v_s_398_, 17);
v_usedCommRing_418_ = lean_ctor_get_uint8(v_s_398_, sizeof(void*)*19 + 1);
v_nonlinearOccs_419_ = lean_ctor_get(v_s_398_, 18);
v_isSharedCheck_428_ = !lean_is_exclusive(v_s_398_);
if (v_isSharedCheck_428_ == 0)
{
v___x_421_ = v_s_398_;
v_isShared_422_ = v_isSharedCheck_428_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_nonlinearOccs_419_);
lean_inc(v_divMod_417_);
lean_inc(v_diseqSplits_416_);
lean_inc(v_conflict_x3f_415_);
lean_inc(v_steps_414_);
lean_inc(v_nextCnstrId_412_);
lean_inc(v_assignment_411_);
lean_inc(v_occurs_410_);
lean_inc(v_elimStack_409_);
lean_inc(v_elimEqs_408_);
lean_inc(v_diseqs_407_);
lean_inc(v_uppers_406_);
lean_inc(v_lowers_405_);
lean_inc(v_dvds_404_);
lean_inc(v_natDef_403_);
lean_inc(v_natToIntMap_402_);
lean_inc(v_varsHistory_401_);
lean_inc(v_varMap_400_);
lean_inc(v_vars_399_);
lean_dec(v_s_398_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_428_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_426_; 
v___x_423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_423_, 0, v_a_396_);
v___x_424_ = l_Lean_PersistentArray_set___redArg(v_dvds_404_, v_v_397_, v___x_423_);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 5, v___x_424_);
v___x_426_ = v___x_421_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_427_; 
v_reuseFailAlloc_427_ = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(v_reuseFailAlloc_427_, 0, v_vars_399_);
lean_ctor_set(v_reuseFailAlloc_427_, 1, v_varMap_400_);
lean_ctor_set(v_reuseFailAlloc_427_, 2, v_varsHistory_401_);
lean_ctor_set(v_reuseFailAlloc_427_, 3, v_natToIntMap_402_);
lean_ctor_set(v_reuseFailAlloc_427_, 4, v_natDef_403_);
lean_ctor_set(v_reuseFailAlloc_427_, 5, v___x_424_);
lean_ctor_set(v_reuseFailAlloc_427_, 6, v_lowers_405_);
lean_ctor_set(v_reuseFailAlloc_427_, 7, v_uppers_406_);
lean_ctor_set(v_reuseFailAlloc_427_, 8, v_diseqs_407_);
lean_ctor_set(v_reuseFailAlloc_427_, 9, v_elimEqs_408_);
lean_ctor_set(v_reuseFailAlloc_427_, 10, v_elimStack_409_);
lean_ctor_set(v_reuseFailAlloc_427_, 11, v_occurs_410_);
lean_ctor_set(v_reuseFailAlloc_427_, 12, v_assignment_411_);
lean_ctor_set(v_reuseFailAlloc_427_, 13, v_nextCnstrId_412_);
lean_ctor_set(v_reuseFailAlloc_427_, 14, v_steps_414_);
lean_ctor_set(v_reuseFailAlloc_427_, 15, v_conflict_x3f_415_);
lean_ctor_set(v_reuseFailAlloc_427_, 16, v_diseqSplits_416_);
lean_ctor_set(v_reuseFailAlloc_427_, 17, v_divMod_417_);
lean_ctor_set(v_reuseFailAlloc_427_, 18, v_nonlinearOccs_419_);
lean_ctor_set_uint8(v_reuseFailAlloc_427_, sizeof(void*)*19, v_caseSplits_413_);
lean_ctor_set_uint8(v_reuseFailAlloc_427_, sizeof(void*)*19 + 1, v_usedCommRing_418_);
v___x_426_ = v_reuseFailAlloc_427_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
return v___x_426_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed(lean_object* v_a_429_, lean_object* v_v_430_, lean_object* v_s_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0(v_a_429_, v_v_430_, v_s_431_);
lean_dec(v_v_430_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(lean_object* v_v_433_, lean_object* v_s_434_){
_start:
{
lean_object* v_vars_435_; lean_object* v_varMap_436_; lean_object* v_varsHistory_437_; lean_object* v_natToIntMap_438_; lean_object* v_natDef_439_; lean_object* v_dvds_440_; lean_object* v_lowers_441_; lean_object* v_uppers_442_; lean_object* v_diseqs_443_; lean_object* v_elimEqs_444_; lean_object* v_elimStack_445_; lean_object* v_occurs_446_; lean_object* v_assignment_447_; lean_object* v_nextCnstrId_448_; uint8_t v_caseSplits_449_; lean_object* v_steps_450_; lean_object* v_conflict_x3f_451_; lean_object* v_diseqSplits_452_; lean_object* v_divMod_453_; uint8_t v_usedCommRing_454_; lean_object* v_nonlinearOccs_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_464_; 
v_vars_435_ = lean_ctor_get(v_s_434_, 0);
v_varMap_436_ = lean_ctor_get(v_s_434_, 1);
v_varsHistory_437_ = lean_ctor_get(v_s_434_, 2);
v_natToIntMap_438_ = lean_ctor_get(v_s_434_, 3);
v_natDef_439_ = lean_ctor_get(v_s_434_, 4);
v_dvds_440_ = lean_ctor_get(v_s_434_, 5);
v_lowers_441_ = lean_ctor_get(v_s_434_, 6);
v_uppers_442_ = lean_ctor_get(v_s_434_, 7);
v_diseqs_443_ = lean_ctor_get(v_s_434_, 8);
v_elimEqs_444_ = lean_ctor_get(v_s_434_, 9);
v_elimStack_445_ = lean_ctor_get(v_s_434_, 10);
v_occurs_446_ = lean_ctor_get(v_s_434_, 11);
v_assignment_447_ = lean_ctor_get(v_s_434_, 12);
v_nextCnstrId_448_ = lean_ctor_get(v_s_434_, 13);
v_caseSplits_449_ = lean_ctor_get_uint8(v_s_434_, sizeof(void*)*19);
v_steps_450_ = lean_ctor_get(v_s_434_, 14);
v_conflict_x3f_451_ = lean_ctor_get(v_s_434_, 15);
v_diseqSplits_452_ = lean_ctor_get(v_s_434_, 16);
v_divMod_453_ = lean_ctor_get(v_s_434_, 17);
v_usedCommRing_454_ = lean_ctor_get_uint8(v_s_434_, sizeof(void*)*19 + 1);
v_nonlinearOccs_455_ = lean_ctor_get(v_s_434_, 18);
v_isSharedCheck_464_ = !lean_is_exclusive(v_s_434_);
if (v_isSharedCheck_464_ == 0)
{
v___x_457_ = v_s_434_;
v_isShared_458_ = v_isSharedCheck_464_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_nonlinearOccs_455_);
lean_inc(v_divMod_453_);
lean_inc(v_diseqSplits_452_);
lean_inc(v_conflict_x3f_451_);
lean_inc(v_steps_450_);
lean_inc(v_nextCnstrId_448_);
lean_inc(v_assignment_447_);
lean_inc(v_occurs_446_);
lean_inc(v_elimStack_445_);
lean_inc(v_elimEqs_444_);
lean_inc(v_diseqs_443_);
lean_inc(v_uppers_442_);
lean_inc(v_lowers_441_);
lean_inc(v_dvds_440_);
lean_inc(v_natDef_439_);
lean_inc(v_natToIntMap_438_);
lean_inc(v_varsHistory_437_);
lean_inc(v_varMap_436_);
lean_inc(v_vars_435_);
lean_dec(v_s_434_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_464_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_462_; 
v___x_459_ = lean_box(0);
v___x_460_ = l_Lean_PersistentArray_set___redArg(v_dvds_440_, v_v_433_, v___x_459_);
if (v_isShared_458_ == 0)
{
lean_ctor_set(v___x_457_, 5, v___x_460_);
v___x_462_ = v___x_457_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_vars_435_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v_varMap_436_);
lean_ctor_set(v_reuseFailAlloc_463_, 2, v_varsHistory_437_);
lean_ctor_set(v_reuseFailAlloc_463_, 3, v_natToIntMap_438_);
lean_ctor_set(v_reuseFailAlloc_463_, 4, v_natDef_439_);
lean_ctor_set(v_reuseFailAlloc_463_, 5, v___x_460_);
lean_ctor_set(v_reuseFailAlloc_463_, 6, v_lowers_441_);
lean_ctor_set(v_reuseFailAlloc_463_, 7, v_uppers_442_);
lean_ctor_set(v_reuseFailAlloc_463_, 8, v_diseqs_443_);
lean_ctor_set(v_reuseFailAlloc_463_, 9, v_elimEqs_444_);
lean_ctor_set(v_reuseFailAlloc_463_, 10, v_elimStack_445_);
lean_ctor_set(v_reuseFailAlloc_463_, 11, v_occurs_446_);
lean_ctor_set(v_reuseFailAlloc_463_, 12, v_assignment_447_);
lean_ctor_set(v_reuseFailAlloc_463_, 13, v_nextCnstrId_448_);
lean_ctor_set(v_reuseFailAlloc_463_, 14, v_steps_450_);
lean_ctor_set(v_reuseFailAlloc_463_, 15, v_conflict_x3f_451_);
lean_ctor_set(v_reuseFailAlloc_463_, 16, v_diseqSplits_452_);
lean_ctor_set(v_reuseFailAlloc_463_, 17, v_divMod_453_);
lean_ctor_set(v_reuseFailAlloc_463_, 18, v_nonlinearOccs_455_);
lean_ctor_set_uint8(v_reuseFailAlloc_463_, sizeof(void*)*19, v_caseSplits_449_);
lean_ctor_set_uint8(v_reuseFailAlloc_463_, sizeof(void*)*19 + 1, v_usedCommRing_454_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed(lean_object* v_v_465_, lean_object* v_s_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1(v_v_465_, v_s_466_);
lean_dec(v_v_465_);
return v_res_467_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5(void){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_476_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4));
v___x_477_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
v___x_478_ = l_Lean_Name_append(v___x_477_, v___x_476_);
return v___x_478_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(lean_object* v_c_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_, lean_object* v_a_484_, lean_object* v_a_485_, lean_object* v_a_486_, lean_object* v_a_487_, lean_object* v_a_488_, lean_object* v_a_489_){
_start:
{
lean_object* v___y_495_; lean_object* v___y_496_; lean_object* v___y_497_; lean_object* v___y_498_; lean_object* v___y_499_; lean_object* v___y_500_; lean_object* v___y_501_; lean_object* v___y_506_; lean_object* v___y_507_; lean_object* v___y_508_; lean_object* v___y_509_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; lean_object* v___y_514_; lean_object* v___y_515_; lean_object* v___y_516_; lean_object* v___y_517_; lean_object* v___y_518_; lean_object* v___y_519_; lean_object* v___y_520_; lean_object* v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_524_; lean_object* v___y_525_; lean_object* v___y_526_; lean_object* v___y_527_; lean_object* v___y_609_; lean_object* v___y_610_; lean_object* v___y_611_; lean_object* v___y_612_; lean_object* v___y_613_; lean_object* v___y_614_; lean_object* v___y_615_; lean_object* v___y_616_; lean_object* v___y_617_; lean_object* v___y_618_; lean_object* v___y_619_; lean_object* v_toCold_631_; lean_object* v_currRecDepth_632_; lean_object* v_ref_633_; uint16_t v_optionFlags_634_; uint8_t v_suppressElabErrors_635_; uint8_t v_isRecordingDeps_636_; lean_object* v_options_637_; lean_object* v_maxRecDepth_638_; lean_object* v_inheritedTraceOptions_639_; lean_object* v___x_640_; lean_object* v___y_642_; lean_object* v___y_643_; lean_object* v___y_644_; lean_object* v___y_645_; lean_object* v___y_646_; lean_object* v___y_647_; lean_object* v___y_648_; lean_object* v___y_649_; lean_object* v___y_650_; lean_object* v___y_651_; lean_object* v___y_652_; lean_object* v___y_653_; lean_object* v___y_654_; lean_object* v___y_655_; lean_object* v___y_656_; lean_object* v___y_657_; lean_object* v___y_658_; lean_object* v___y_659_; lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___x_822_; uint8_t v___x_823_; 
v_toCold_631_ = lean_ctor_get(v_a_488_, 0);
lean_inc_ref(v_toCold_631_);
v_currRecDepth_632_ = lean_ctor_get(v_a_488_, 1);
lean_inc(v_currRecDepth_632_);
v_ref_633_ = lean_ctor_get(v_a_488_, 2);
lean_inc(v_ref_633_);
v_optionFlags_634_ = lean_ctor_get_uint16(v_a_488_, sizeof(void*)*3);
v_suppressElabErrors_635_ = lean_ctor_get_uint8(v_a_488_, sizeof(void*)*3 + 2);
v_isRecordingDeps_636_ = lean_ctor_get_uint8(v_a_488_, sizeof(void*)*3 + 3);
lean_dec_ref(v_a_488_);
v_options_637_ = lean_ctor_get(v_toCold_631_, 2);
lean_inc_ref(v_options_637_);
v_maxRecDepth_638_ = lean_ctor_get(v_toCold_631_, 3);
v_inheritedTraceOptions_639_ = lean_ctor_get(v_toCold_631_, 11);
lean_inc_ref(v_inheritedTraceOptions_639_);
v___x_640_ = lean_box(0);
v___x_822_ = lean_unsigned_to_nat(0u);
v___x_823_ = lean_nat_dec_eq(v_maxRecDepth_638_, v___x_822_);
if (v___x_823_ == 0)
{
uint8_t v___x_824_; 
v___x_824_ = lean_nat_dec_eq(v_currRecDepth_632_, v_maxRecDepth_638_);
if (v___x_824_ == 0)
{
goto v___jp_781_;
}
else
{
lean_object* v___x_825_; 
lean_dec_ref(v_inheritedTraceOptions_639_);
lean_dec_ref(v_options_637_);
lean_dec(v_currRecDepth_632_);
lean_dec_ref(v_toCold_631_);
lean_dec_ref(v_c_479_);
v___x_825_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts_spec__0___redArg(v_ref_633_);
return v___x_825_;
}
}
else
{
goto v___jp_781_;
}
v___jp_491_:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = lean_box(0);
v___x_493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
return v___x_493_;
}
v___jp_494_:
{
lean_object* v___x_502_; 
v___x_502_ = l_Int_Internal_Linear_Poly_updateOccs___redArg(v___y_495_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
lean_dec_ref(v___y_500_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v___x_503_; lean_object* v___x_504_; 
lean_dec_ref_known(v___x_502_, 1);
v___x_503_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_504_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_503_, v___y_496_, v___y_497_);
return v___x_504_;
}
else
{
lean_dec_ref(v___y_496_);
return v___x_502_;
}
}
v___jp_505_:
{
if (lean_obj_tag(v___y_527_) == 1)
{
lean_object* v_val_528_; lean_object* v_p_529_; 
lean_dec_ref(v___y_510_);
lean_dec_ref(v___y_507_);
v_val_528_ = lean_ctor_get(v___y_527_, 0);
lean_inc(v_val_528_);
lean_dec_ref_known(v___y_527_, 1);
v_p_529_ = lean_ctor_get(v_val_528_, 1);
lean_inc_ref(v_p_529_);
if (lean_obj_tag(v_p_529_) == 1)
{
lean_object* v_d_530_; lean_object* v_k_531_; lean_object* v_p_532_; lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_585_; 
v_d_530_ = lean_ctor_get(v_val_528_, 0);
v_k_531_ = lean_ctor_get(v_p_529_, 0);
v_p_532_ = lean_ctor_get(v_p_529_, 2);
v_isSharedCheck_585_ = !lean_is_exclusive(v_p_529_);
if (v_isSharedCheck_585_ == 0)
{
lean_object* v_unused_586_; 
v_unused_586_ = lean_ctor_get(v_p_529_, 1);
lean_dec(v_unused_586_);
v___x_534_ = v_p_529_;
v_isShared_535_ = v_isSharedCheck_585_;
goto v_resetjp_533_;
}
else
{
lean_inc(v_p_532_);
lean_inc(v_k_531_);
lean_dec(v_p_529_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_585_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v_snd_539_; lean_object* v_fst_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_584_; 
v___x_536_ = lean_int_mul(v___y_512_, v_d_530_);
v___x_537_ = lean_int_mul(v_k_531_, v___y_506_);
v___x_538_ = l_Lean_Meta_Grind_Arith_gcdExt(v___x_536_, v___x_537_);
lean_dec(v___x_537_);
lean_dec(v___x_536_);
v_snd_539_ = lean_ctor_get(v___x_538_, 1);
v_fst_540_ = lean_ctor_get(v___x_538_, 0);
v_isSharedCheck_584_ = !lean_is_exclusive(v___x_538_);
if (v_isSharedCheck_584_ == 0)
{
v___x_542_ = v___x_538_;
v_isShared_543_ = v_isSharedCheck_584_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_snd_539_);
lean_inc(v_fst_540_);
lean_dec(v___x_538_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_584_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v_fst_544_; lean_object* v_snd_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_583_; 
v_fst_544_ = lean_ctor_get(v_snd_539_, 0);
v_snd_545_ = lean_ctor_get(v_snd_539_, 1);
v_isSharedCheck_583_ = !lean_is_exclusive(v_snd_539_);
if (v_isSharedCheck_583_ == 0)
{
v___x_547_ = v_snd_539_;
v_isShared_548_ = v_isSharedCheck_583_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_snd_545_);
lean_inc(v_fst_544_);
lean_dec(v_snd_539_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_583_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_556_; 
v___x_549_ = lean_int_mul(v_fst_544_, v_d_530_);
lean_dec(v_fst_544_);
lean_inc_ref(v___y_522_);
v___x_550_ = l_Int_Internal_Linear_Poly_mul(v___y_522_, v___x_549_);
lean_dec(v___x_549_);
v___x_551_ = lean_int_mul(v_snd_545_, v___y_506_);
lean_dec(v_snd_545_);
lean_inc_ref(v_p_532_);
v___x_552_ = l_Int_Internal_Linear_Poly_mul(v_p_532_, v___x_551_);
lean_dec(v___x_551_);
v___x_553_ = lean_int_mul(v___y_506_, v_d_530_);
lean_dec(v___y_506_);
v___x_554_ = l_Int_Internal_Linear_Poly_combine(v___x_550_, v___x_552_);
lean_inc(v_fst_540_);
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 2, v___x_554_);
lean_ctor_set(v___x_534_, 1, v___y_516_);
lean_ctor_set(v___x_534_, 0, v_fst_540_);
v___x_556_ = v___x_534_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_fst_540_);
lean_ctor_set(v_reuseFailAlloc_582_, 1, v___y_516_);
lean_ctor_set(v_reuseFailAlloc_582_, 2, v___x_554_);
v___x_556_ = v_reuseFailAlloc_582_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
lean_object* v___x_558_; 
lean_inc(v_val_528_);
lean_inc_ref(v___y_511_);
if (v_isShared_548_ == 0)
{
lean_ctor_set_tag(v___x_547_, 4);
lean_ctor_set(v___x_547_, 1, v_val_528_);
lean_ctor_set(v___x_547_, 0, v___y_511_);
v___x_558_ = v___x_547_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_581_; 
v_reuseFailAlloc_581_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_581_, 0, v___y_511_);
lean_ctor_set(v_reuseFailAlloc_581_, 1, v_val_528_);
v___x_558_ = v_reuseFailAlloc_581_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_559_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_559_, 0, v___x_553_);
lean_ctor_set(v___x_559_, 1, v___x_556_);
lean_ctor_set(v___x_559_, 2, v___x_558_);
v___x_560_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_561_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_560_, v___y_517_, v___y_508_);
if (lean_obj_tag(v___x_561_) == 0)
{
lean_object* v___x_562_; 
lean_dec_ref_known(v___x_561_, 1);
lean_inc_ref(v___y_520_);
v___x_562_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v___x_559_, v___y_508_, v___y_518_, v___y_509_, v___y_513_, v___y_521_, v___y_525_, v___y_515_, v___y_523_, v___y_520_, v___y_519_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_568_; 
lean_dec_ref_known(v___x_562_, 1);
v___x_563_ = l_Int_Internal_Linear_Poly_mul(v___y_522_, v_k_531_);
lean_dec(v_k_531_);
v___x_564_ = lean_int_neg(v___y_512_);
lean_dec(v___y_512_);
v___x_565_ = l_Int_Internal_Linear_Poly_mul(v_p_532_, v___x_564_);
lean_dec(v___x_564_);
v___x_566_ = l_Int_Internal_Linear_Poly_combine(v___x_563_, v___x_565_);
lean_inc(v_val_528_);
if (v_isShared_543_ == 0)
{
lean_ctor_set_tag(v___x_542_, 5);
lean_ctor_set(v___x_542_, 1, v_val_528_);
lean_ctor_set(v___x_542_, 0, v___y_511_);
v___x_568_ = v___x_542_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v___y_511_);
lean_ctor_set(v_reuseFailAlloc_580_, 1, v_val_528_);
v___x_568_ = v_reuseFailAlloc_580_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_576_; 
v_isSharedCheck_576_ = !lean_is_exclusive(v_val_528_);
if (v_isSharedCheck_576_ == 0)
{
lean_object* v_unused_577_; lean_object* v_unused_578_; lean_object* v_unused_579_; 
v_unused_577_ = lean_ctor_get(v_val_528_, 2);
lean_dec(v_unused_577_);
v_unused_578_ = lean_ctor_get(v_val_528_, 1);
lean_dec(v_unused_578_);
v_unused_579_ = lean_ctor_get(v_val_528_, 0);
lean_dec(v_unused_579_);
v___x_570_ = v_val_528_;
v_isShared_571_ = v_isSharedCheck_576_;
goto v_resetjp_569_;
}
else
{
lean_dec(v_val_528_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_576_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_573_; 
if (v_isShared_571_ == 0)
{
lean_ctor_set(v___x_570_, 2, v___x_568_);
lean_ctor_set(v___x_570_, 1, v___x_566_);
lean_ctor_set(v___x_570_, 0, v_fst_540_);
v___x_573_ = v___x_570_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_fst_540_);
lean_ctor_set(v_reuseFailAlloc_575_, 1, v___x_566_);
lean_ctor_set(v_reuseFailAlloc_575_, 2, v___x_568_);
v___x_573_ = v_reuseFailAlloc_575_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
v_c_479_ = v___x_573_;
v_a_480_ = v___y_508_;
v_a_481_ = v___y_518_;
v_a_482_ = v___y_509_;
v_a_483_ = v___y_513_;
v_a_484_ = v___y_521_;
v_a_485_ = v___y_525_;
v_a_486_ = v___y_515_;
v_a_487_ = v___y_523_;
v_a_488_ = v___y_520_;
v_a_489_ = v___y_519_;
goto _start;
}
}
}
}
else
{
lean_del_object(v___x_542_);
lean_dec(v_fst_540_);
lean_dec_ref(v_p_532_);
lean_dec(v_k_531_);
lean_dec(v_val_528_);
lean_dec_ref(v___y_522_);
lean_dec_ref(v___y_520_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
return v___x_562_;
}
}
else
{
lean_dec_ref_known(v___x_559_, 3);
lean_del_object(v___x_542_);
lean_dec(v_fst_540_);
lean_dec_ref(v_p_532_);
lean_dec(v_k_531_);
lean_dec(v_val_528_);
lean_dec_ref(v___y_522_);
lean_dec_ref(v___y_520_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
return v___x_561_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_587_; 
lean_dec_ref(v_p_529_);
lean_dec_ref(v___y_522_);
lean_dec_ref(v___y_517_);
lean_dec(v___y_516_);
lean_dec(v___y_512_);
lean_dec_ref(v___y_511_);
lean_dec(v___y_506_);
v___x_587_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_val_528_, v___y_508_, v___y_518_, v___y_509_, v___y_513_, v___y_521_, v___y_525_, v___y_515_, v___y_523_, v___y_520_, v___y_519_);
lean_dec_ref(v___y_520_);
return v___x_587_;
}
}
else
{
lean_object* v_toCold_588_; lean_object* v_options_589_; uint8_t v_hasTrace_590_; 
lean_dec(v___y_527_);
lean_dec_ref(v___y_522_);
lean_dec_ref(v___y_517_);
lean_dec(v___y_516_);
lean_dec(v___y_512_);
lean_dec(v___y_506_);
v_toCold_588_ = lean_ctor_get(v___y_520_, 0);
v_options_589_ = lean_ctor_get(v_toCold_588_, 2);
v_hasTrace_590_ = lean_ctor_get_uint8(v_options_589_, sizeof(void*)*1);
if (v_hasTrace_590_ == 0)
{
lean_dec_ref(v___y_511_);
v___y_495_ = v___y_507_;
v___y_496_ = v___y_510_;
v___y_497_ = v___y_508_;
v___y_498_ = v___y_515_;
v___y_499_ = v___y_523_;
v___y_500_ = v___y_520_;
v___y_501_ = v___y_519_;
goto v___jp_494_;
}
else
{
lean_object* v_inheritedTraceOptions_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; uint8_t v___x_596_; 
v_inheritedTraceOptions_591_ = lean_ctor_get(v_toCold_588_, 11);
v___x_592_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__0));
lean_inc_ref(v___y_526_);
lean_inc_ref(v___y_514_);
lean_inc_ref(v___y_524_);
v___x_593_ = l_Lean_Name_mkStr4(v___y_524_, v___y_514_, v___y_526_, v___x_592_);
v___x_594_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
lean_inc(v___x_593_);
v___x_595_ = l_Lean_Name_append(v___x_594_, v___x_593_);
v___x_596_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_591_, v_options_589_, v___x_595_);
lean_dec(v___x_595_);
if (v___x_596_ == 0)
{
lean_dec(v___x_593_);
lean_dec_ref(v___y_511_);
v___y_495_ = v___y_507_;
v___y_496_ = v___y_510_;
v___y_497_ = v___y_508_;
v___y_498_ = v___y_515_;
v___y_499_ = v___y_523_;
v___y_500_ = v___y_520_;
v___y_501_ = v___y_519_;
goto v___jp_494_;
}
else
{
lean_object* v___x_597_; 
v___x_597_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v___y_511_, v___y_508_, v___y_520_);
if (lean_obj_tag(v___x_597_) == 0)
{
lean_object* v_a_598_; lean_object* v___x_599_; 
v_a_598_ = lean_ctor_get(v___x_597_, 0);
lean_inc(v_a_598_);
lean_dec_ref_known(v___x_597_, 1);
v___x_599_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_593_, v_a_598_, v___y_515_, v___y_523_, v___y_520_, v___y_519_);
if (lean_obj_tag(v___x_599_) == 0)
{
lean_dec_ref_known(v___x_599_, 1);
v___y_495_ = v___y_507_;
v___y_496_ = v___y_510_;
v___y_497_ = v___y_508_;
v___y_498_ = v___y_515_;
v___y_499_ = v___y_523_;
v___y_500_ = v___y_520_;
v___y_501_ = v___y_519_;
goto v___jp_494_;
}
else
{
lean_dec_ref(v___y_520_);
lean_dec_ref(v___y_510_);
lean_dec_ref(v___y_507_);
return v___x_599_;
}
}
else
{
lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_607_; 
lean_dec(v___x_593_);
lean_dec_ref(v___y_520_);
lean_dec_ref(v___y_510_);
lean_dec_ref(v___y_507_);
v_a_600_ = lean_ctor_get(v___x_597_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_597_);
if (v_isSharedCheck_607_ == 0)
{
v___x_602_ = v___x_597_;
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_597_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_607_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_605_; 
if (v_isShared_603_ == 0)
{
v___x_605_ = v___x_602_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_a_600_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
}
}
}
}
}
v___jp_608_:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_620_, 0, v___y_609_);
v___x_621_ = l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(v___x_620_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
lean_dec_ref(v___y_618_);
if (lean_obj_tag(v___x_621_) == 0)
{
lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_629_; 
v_isSharedCheck_629_ = !lean_is_exclusive(v___x_621_);
if (v_isSharedCheck_629_ == 0)
{
lean_object* v_unused_630_; 
v_unused_630_ = lean_ctor_get(v___x_621_, 0);
lean_dec(v_unused_630_);
v___x_623_ = v___x_621_;
v_isShared_624_ = v_isSharedCheck_629_;
goto v_resetjp_622_;
}
else
{
lean_dec(v___x_621_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_629_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_625_; lean_object* v___x_627_; 
v___x_625_ = lean_box(0);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 0, v___x_625_);
v___x_627_ = v___x_623_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_628_, 0, v___x_625_);
v___x_627_ = v_reuseFailAlloc_628_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
return v___x_627_;
}
}
}
else
{
return v___x_621_;
}
}
v___jp_641_:
{
lean_object* v___x_663_; 
v___x_663_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v___y_653_, v___y_661_);
if (lean_obj_tag(v___x_663_) == 0)
{
lean_object* v_a_664_; lean_object* v_dvds_665_; lean_object* v_size_666_; uint8_t v___x_667_; 
v_a_664_ = lean_ctor_get(v___x_663_, 0);
lean_inc(v_a_664_);
lean_dec_ref_known(v___x_663_, 1);
v_dvds_665_ = lean_ctor_get(v_a_664_, 5);
lean_inc_ref(v_dvds_665_);
lean_dec(v_a_664_);
v_size_666_ = lean_ctor_get(v_dvds_665_, 2);
v___x_667_ = lean_nat_dec_lt(v___y_651_, v_size_666_);
if (v___x_667_ == 0)
{
lean_object* v___x_668_; 
lean_dec_ref(v_dvds_665_);
v___x_668_ = l_outOfBounds___redArg(v___x_640_);
v___y_506_ = v___y_642_;
v___y_507_ = v___y_643_;
v___y_508_ = v___y_653_;
v___y_509_ = v___y_655_;
v___y_510_ = v___y_644_;
v___y_511_ = v___y_645_;
v___y_512_ = v___y_647_;
v___y_513_ = v___y_656_;
v___y_514_ = v___y_652_;
v___y_515_ = v___y_659_;
v___y_516_ = v___y_651_;
v___y_517_ = v___y_650_;
v___y_518_ = v___y_654_;
v___y_519_ = v___y_662_;
v___y_520_ = v___y_661_;
v___y_521_ = v___y_657_;
v___y_522_ = v___y_646_;
v___y_523_ = v___y_660_;
v___y_524_ = v___y_648_;
v___y_525_ = v___y_658_;
v___y_526_ = v___y_649_;
v___y_527_ = v___x_668_;
goto v___jp_505_;
}
else
{
lean_object* v___x_669_; 
v___x_669_ = l_Lean_PersistentArray_get_x21___redArg(v___x_640_, v_dvds_665_, v___y_651_);
lean_dec_ref(v_dvds_665_);
v___y_506_ = v___y_642_;
v___y_507_ = v___y_643_;
v___y_508_ = v___y_653_;
v___y_509_ = v___y_655_;
v___y_510_ = v___y_644_;
v___y_511_ = v___y_645_;
v___y_512_ = v___y_647_;
v___y_513_ = v___y_656_;
v___y_514_ = v___y_652_;
v___y_515_ = v___y_659_;
v___y_516_ = v___y_651_;
v___y_517_ = v___y_650_;
v___y_518_ = v___y_654_;
v___y_519_ = v___y_662_;
v___y_520_ = v___y_661_;
v___y_521_ = v___y_657_;
v___y_522_ = v___y_646_;
v___y_523_ = v___y_660_;
v___y_524_ = v___y_648_;
v___y_525_ = v___y_658_;
v___y_526_ = v___y_649_;
v___y_527_ = v___x_669_;
goto v___jp_505_;
}
}
else
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
lean_dec_ref(v___y_661_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec_ref(v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v___y_642_);
v_a_670_ = lean_ctor_get(v___x_663_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_663_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v___x_663_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_663_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_670_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
v___jp_678_:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(v_c_479_);
lean_inc_ref(v___y_690_);
v___x_693_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(v___x_692_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v_a_694_; lean_object* v_d_695_; lean_object* v_p_696_; uint8_t v___x_697_; 
v_a_694_ = lean_ctor_get(v___x_693_, 0);
lean_inc(v_a_694_);
lean_dec_ref_known(v___x_693_, 1);
v_d_695_ = lean_ctor_get(v_a_694_, 0);
v_p_696_ = lean_ctor_get(v_a_694_, 1);
lean_inc(v_d_695_);
v___x_697_ = l_Int_Internal_Linear_Poly_isUnsatDvd(v_d_695_, v_p_696_);
if (v___x_697_ == 0)
{
uint8_t v___x_698_; 
v___x_698_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(v_a_694_);
if (v___x_698_ == 0)
{
lean_object* v___x_699_; uint8_t v___x_700_; 
v___x_699_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm___closed__1);
v___x_700_ = lean_int_dec_eq(v_d_695_, v___x_699_);
if (v___x_700_ == 0)
{
if (lean_obj_tag(v_p_696_) == 1)
{
lean_object* v_k_701_; lean_object* v_v_702_; lean_object* v_p_703_; lean_object* v___f_704_; lean_object* v___f_705_; lean_object* v___x_706_; 
lean_inc_ref(v_p_696_);
lean_inc(v_d_695_);
v_k_701_ = lean_ctor_get(v_p_696_, 0);
lean_inc(v_k_701_);
v_v_702_ = lean_ctor_get(v_p_696_, 1);
lean_inc_n(v_v_702_, 3);
v_p_703_ = lean_ctor_get(v_p_696_, 2);
lean_inc_ref(v_p_703_);
lean_inc_n(v_a_694_, 2);
v___f_704_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__0___boxed), 3, 2);
lean_closure_set(v___f_704_, 0, v_a_694_);
lean_closure_set(v___f_704_, 1, v_v_702_);
v___f_705_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___lam__1___boxed), 2, 1);
lean_closure_set(v___f_705_, 0, v_v_702_);
v___x_706_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(v_a_694_, v___y_682_, v___y_690_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_707_; uint8_t v___x_708_; uint8_t v___x_709_; uint8_t v___x_710_; 
v_a_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_a_707_);
lean_dec_ref_known(v___x_706_, 1);
v___x_708_ = 0;
v___x_709_ = lean_unbox(v_a_707_);
lean_dec(v_a_707_);
v___x_710_ = l_Lean_instBEqLBool_beq(v___x_709_, v___x_708_);
if (v___x_710_ == 0)
{
v___y_642_ = v_d_695_;
v___y_643_ = v_p_696_;
v___y_644_ = v___f_704_;
v___y_645_ = v_a_694_;
v___y_646_ = v_p_703_;
v___y_647_ = v_k_701_;
v___y_648_ = v___y_679_;
v___y_649_ = v___y_681_;
v___y_650_ = v___f_705_;
v___y_651_ = v_v_702_;
v___y_652_ = v___y_680_;
v___y_653_ = v___y_682_;
v___y_654_ = v___y_683_;
v___y_655_ = v___y_684_;
v___y_656_ = v___y_685_;
v___y_657_ = v___y_686_;
v___y_658_ = v___y_687_;
v___y_659_ = v___y_688_;
v___y_660_ = v___y_689_;
v___y_661_ = v___y_690_;
v___y_662_ = v___y_691_;
goto v___jp_641_;
}
else
{
lean_object* v___x_711_; 
lean_inc(v_v_702_);
v___x_711_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v_v_702_, v___y_682_);
if (lean_obj_tag(v___x_711_) == 0)
{
lean_dec_ref_known(v___x_711_, 1);
v___y_642_ = v_d_695_;
v___y_643_ = v_p_696_;
v___y_644_ = v___f_704_;
v___y_645_ = v_a_694_;
v___y_646_ = v_p_703_;
v___y_647_ = v_k_701_;
v___y_648_ = v___y_679_;
v___y_649_ = v___y_681_;
v___y_650_ = v___f_705_;
v___y_651_ = v_v_702_;
v___y_652_ = v___y_680_;
v___y_653_ = v___y_682_;
v___y_654_ = v___y_683_;
v___y_655_ = v___y_684_;
v___y_656_ = v___y_685_;
v___y_657_ = v___y_686_;
v___y_658_ = v___y_687_;
v___y_659_ = v___y_688_;
v___y_660_ = v___y_689_;
v___y_661_ = v___y_690_;
v___y_662_ = v___y_691_;
goto v___jp_641_;
}
else
{
lean_dec_ref(v___f_705_);
lean_dec_ref(v___f_704_);
lean_dec_ref(v_p_703_);
lean_dec(v_v_702_);
lean_dec(v_k_701_);
lean_dec_ref_known(v_p_696_, 3);
lean_dec(v_d_695_);
lean_dec(v_a_694_);
lean_dec_ref(v___y_690_);
return v___x_711_;
}
}
}
else
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_719_; 
lean_dec_ref(v___f_705_);
lean_dec_ref(v___f_704_);
lean_dec_ref(v_p_703_);
lean_dec(v_v_702_);
lean_dec(v_k_701_);
lean_dec_ref_known(v_p_696_, 3);
lean_dec(v_d_695_);
lean_dec(v_a_694_);
lean_dec_ref(v___y_690_);
v_a_712_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_719_ == 0)
{
v___x_714_ = v___x_706_;
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_706_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_715_ == 0)
{
v___x_717_ = v___x_714_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_a_712_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
else
{
lean_object* v___x_720_; 
v___x_720_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected___redArg(v_a_694_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
lean_dec_ref(v___y_690_);
return v___x_720_;
}
}
else
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; 
lean_inc_ref(v_p_696_);
v___x_721_ = lean_alloc_ctor(9, 1, 0);
lean_ctor_set(v___x_721_, 0, v_a_694_);
v___x_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_722_, 0, v_p_696_);
lean_ctor_set(v___x_722_, 1, v___x_721_);
lean_inc(v___y_691_);
lean_inc(v___y_689_);
lean_inc_ref(v___y_688_);
lean_inc(v___y_687_);
lean_inc_ref(v___y_686_);
lean_inc(v___y_685_);
lean_inc_ref(v___y_684_);
lean_inc(v___y_683_);
lean_inc(v___y_682_);
v___x_723_ = lean_grind_cutsat_assert_eq(v___x_722_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_731_; 
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_731_ == 0)
{
lean_object* v_unused_732_; 
v_unused_732_ = lean_ctor_get(v___x_723_, 0);
lean_dec(v_unused_732_);
v___x_725_ = v___x_723_;
v_isShared_726_ = v_isSharedCheck_731_;
goto v_resetjp_724_;
}
else
{
lean_dec(v___x_723_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_731_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_727_; lean_object* v___x_729_; 
v___x_727_ = lean_box(0);
if (v_isShared_726_ == 0)
{
lean_ctor_set(v___x_725_, 0, v___x_727_);
v___x_729_ = v___x_725_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_727_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
else
{
return v___x_723_;
}
}
}
else
{
lean_object* v_toCold_733_; lean_object* v_options_734_; uint8_t v_hasTrace_735_; 
v_toCold_733_ = lean_ctor_get(v___y_690_, 0);
v_options_734_ = lean_ctor_get(v_toCold_733_, 2);
v_hasTrace_735_ = lean_ctor_get_uint8(v_options_734_, sizeof(void*)*1);
if (v_hasTrace_735_ == 0)
{
lean_dec(v_a_694_);
lean_dec_ref(v___y_690_);
goto v___jp_491_;
}
else
{
lean_object* v_inheritedTraceOptions_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; uint8_t v___x_741_; 
v_inheritedTraceOptions_736_ = lean_ctor_get(v_toCold_733_, 11);
v___x_737_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__1));
lean_inc_ref(v___y_681_);
lean_inc_ref(v___y_680_);
lean_inc_ref(v___y_679_);
v___x_738_ = l_Lean_Name_mkStr4(v___y_679_, v___y_680_, v___y_681_, v___x_737_);
v___x_739_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
lean_inc(v___x_738_);
v___x_740_ = l_Lean_Name_append(v___x_739_, v___x_738_);
v___x_741_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_736_, v_options_734_, v___x_740_);
lean_dec(v___x_740_);
if (v___x_741_ == 0)
{
lean_dec(v___x_738_);
lean_dec(v_a_694_);
lean_dec_ref(v___y_690_);
goto v___jp_491_;
}
else
{
lean_object* v___x_742_; 
v___x_742_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_a_694_, v___y_682_, v___y_690_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_object* v_a_743_; lean_object* v___x_744_; 
v_a_743_ = lean_ctor_get(v___x_742_, 0);
lean_inc(v_a_743_);
lean_dec_ref_known(v___x_742_, 1);
v___x_744_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_738_, v_a_743_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
lean_dec_ref(v___y_690_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_dec_ref_known(v___x_744_, 1);
goto v___jp_491_;
}
else
{
return v___x_744_;
}
}
else
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
lean_dec(v___x_738_);
lean_dec_ref(v___y_690_);
v_a_745_ = lean_ctor_get(v___x_742_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___x_742_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_742_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_745_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
}
}
}
else
{
lean_object* v_toCold_753_; lean_object* v_options_754_; uint8_t v_hasTrace_755_; 
v_toCold_753_ = lean_ctor_get(v___y_690_, 0);
v_options_754_ = lean_ctor_get(v_toCold_753_, 2);
v_hasTrace_755_ = lean_ctor_get_uint8(v_options_754_, sizeof(void*)*1);
if (v_hasTrace_755_ == 0)
{
v___y_609_ = v_a_694_;
v___y_610_ = v___y_682_;
v___y_611_ = v___y_683_;
v___y_612_ = v___y_684_;
v___y_613_ = v___y_685_;
v___y_614_ = v___y_686_;
v___y_615_ = v___y_687_;
v___y_616_ = v___y_688_;
v___y_617_ = v___y_689_;
v___y_618_ = v___y_690_;
v___y_619_ = v___y_691_;
goto v___jp_608_;
}
else
{
lean_object* v_inheritedTraceOptions_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; uint8_t v___x_761_; 
v_inheritedTraceOptions_756_ = lean_ctor_get(v_toCold_753_, 11);
v___x_757_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__2));
lean_inc_ref(v___y_681_);
lean_inc_ref(v___y_680_);
lean_inc_ref(v___y_679_);
v___x_758_ = l_Lean_Name_mkStr4(v___y_679_, v___y_680_, v___y_681_, v___x_757_);
v___x_759_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__6));
lean_inc(v___x_758_);
v___x_760_ = l_Lean_Name_append(v___x_759_, v___x_758_);
v___x_761_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_756_, v_options_754_, v___x_760_);
lean_dec(v___x_760_);
if (v___x_761_ == 0)
{
lean_dec(v___x_758_);
v___y_609_ = v_a_694_;
v___y_610_ = v___y_682_;
v___y_611_ = v___y_683_;
v___y_612_ = v___y_684_;
v___y_613_ = v___y_685_;
v___y_614_ = v___y_686_;
v___y_615_ = v___y_687_;
v___y_616_ = v___y_688_;
v___y_617_ = v___y_689_;
v___y_618_ = v___y_690_;
v___y_619_ = v___y_691_;
goto v___jp_608_;
}
else
{
lean_object* v___x_762_; 
lean_inc(v_a_694_);
v___x_762_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_a_694_, v___y_682_, v___y_690_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v_a_763_; lean_object* v___x_764_; 
v_a_763_ = lean_ctor_get(v___x_762_, 0);
lean_inc(v_a_763_);
lean_dec_ref_known(v___x_762_, 1);
v___x_764_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_758_, v_a_763_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_dec_ref_known(v___x_764_, 1);
v___y_609_ = v_a_694_;
v___y_610_ = v___y_682_;
v___y_611_ = v___y_683_;
v___y_612_ = v___y_684_;
v___y_613_ = v___y_685_;
v___y_614_ = v___y_686_;
v___y_615_ = v___y_687_;
v___y_616_ = v___y_688_;
v___y_617_ = v___y_689_;
v___y_618_ = v___y_690_;
v___y_619_ = v___y_691_;
goto v___jp_608_;
}
else
{
lean_dec(v_a_694_);
lean_dec_ref(v___y_690_);
return v___x_764_;
}
}
else
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
lean_dec(v___x_758_);
lean_dec(v_a_694_);
lean_dec_ref(v___y_690_);
v_a_765_ = lean_ctor_get(v___x_762_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_762_);
if (v_isSharedCheck_772_ == 0)
{
v___x_767_ = v___x_762_;
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___x_762_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_770_; 
if (v_isShared_768_ == 0)
{
v___x_770_ = v___x_767_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_a_765_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
lean_dec_ref(v___y_690_);
v_a_773_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_780_ == 0)
{
v___x_775_ = v___x_693_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_693_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_773_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
v___jp_781_:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; 
v___x_782_ = lean_unsigned_to_nat(1u);
v___x_783_ = lean_nat_add(v_currRecDepth_632_, v___x_782_);
lean_dec(v_currRecDepth_632_);
v___x_784_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_784_, 0, v_toCold_631_);
lean_ctor_set(v___x_784_, 1, v___x_783_);
lean_ctor_set(v___x_784_, 2, v_ref_633_);
lean_ctor_set_uint16(v___x_784_, sizeof(void*)*3, v_optionFlags_634_);
lean_ctor_set_uint8(v___x_784_, sizeof(void*)*3 + 2, v_suppressElabErrors_635_);
lean_ctor_set_uint8(v___x_784_, sizeof(void*)*3 + 3, v_isRecordingDeps_636_);
v___x_785_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_480_, v___x_784_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_813_; 
v_a_786_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_813_ == 0)
{
v___x_788_ = v___x_785_;
v_isShared_789_ = v_isSharedCheck_813_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_785_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_813_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
uint8_t v___x_790_; 
v___x_790_ = lean_unbox(v_a_786_);
lean_dec(v_a_786_);
if (v___x_790_ == 0)
{
uint8_t v_hasTrace_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
lean_del_object(v___x_788_);
v_hasTrace_791_ = lean_ctor_get_uint8(v_options_637_, sizeof(void*)*1);
v___x_792_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__0));
v___x_793_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___closed__2));
v___x_794_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__3));
if (v_hasTrace_791_ == 0)
{
lean_dec_ref(v_inheritedTraceOptions_639_);
lean_dec_ref(v_options_637_);
v___y_679_ = v___x_792_;
v___y_680_ = v___x_793_;
v___y_681_ = v___x_794_;
v___y_682_ = v_a_480_;
v___y_683_ = v_a_481_;
v___y_684_ = v_a_482_;
v___y_685_ = v_a_483_;
v___y_686_ = v_a_484_;
v___y_687_ = v_a_485_;
v___y_688_ = v_a_486_;
v___y_689_ = v_a_487_;
v___y_690_ = v___x_784_;
v___y_691_ = v_a_489_;
goto v___jp_678_;
}
else
{
lean_object* v___x_795_; lean_object* v___x_796_; uint8_t v___x_797_; 
v___x_795_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__4));
v___x_796_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___closed__5);
v___x_797_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_639_, v_options_637_, v___x_796_);
lean_dec_ref(v_options_637_);
lean_dec_ref(v_inheritedTraceOptions_639_);
if (v___x_797_ == 0)
{
v___y_679_ = v___x_792_;
v___y_680_ = v___x_793_;
v___y_681_ = v___x_794_;
v___y_682_ = v_a_480_;
v___y_683_ = v_a_481_;
v___y_684_ = v_a_482_;
v___y_685_ = v_a_483_;
v___y_686_ = v_a_484_;
v___y_687_ = v_a_485_;
v___y_688_ = v_a_486_;
v___y_689_ = v_a_487_;
v___y_690_ = v___x_784_;
v___y_691_ = v_a_489_;
goto v___jp_678_;
}
else
{
lean_object* v___x_798_; 
lean_inc_ref(v_c_479_);
v___x_798_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(v_c_479_, v_a_480_, v___x_784_);
if (lean_obj_tag(v___x_798_) == 0)
{
lean_object* v_a_799_; lean_object* v___x_800_; 
v_a_799_ = lean_ctor_get(v___x_798_, 0);
lean_inc(v_a_799_);
lean_dec_ref_known(v___x_798_, 1);
v___x_800_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq_spec__0___redArg(v___x_795_, v_a_799_, v_a_486_, v_a_487_, v___x_784_, v_a_489_);
if (lean_obj_tag(v___x_800_) == 0)
{
lean_dec_ref_known(v___x_800_, 1);
v___y_679_ = v___x_792_;
v___y_680_ = v___x_793_;
v___y_681_ = v___x_794_;
v___y_682_ = v_a_480_;
v___y_683_ = v_a_481_;
v___y_684_ = v_a_482_;
v___y_685_ = v_a_483_;
v___y_686_ = v_a_484_;
v___y_687_ = v_a_485_;
v___y_688_ = v_a_486_;
v___y_689_ = v_a_487_;
v___y_690_ = v___x_784_;
v___y_691_ = v_a_489_;
goto v___jp_678_;
}
else
{
lean_dec_ref_known(v___x_784_, 3);
lean_dec_ref(v_c_479_);
return v___x_800_;
}
}
else
{
lean_object* v_a_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_808_; 
lean_dec_ref_known(v___x_784_, 3);
lean_dec_ref(v_c_479_);
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
lean_dec_ref_known(v___x_784_, 3);
lean_dec_ref(v_inheritedTraceOptions_639_);
lean_dec_ref(v_options_637_);
lean_dec_ref(v_c_479_);
v___x_809_ = lean_box(0);
if (v_isShared_789_ == 0)
{
lean_ctor_set(v___x_788_, 0, v___x_809_);
v___x_811_ = v___x_788_;
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
lean_dec_ref_known(v___x_784_, 3);
lean_dec_ref(v_inheritedTraceOptions_639_);
lean_dec_ref(v_options_637_);
lean_dec_ref(v_c_479_);
v_a_814_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_821_ == 0)
{
v___x_816_ = v___x_785_;
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_785_);
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
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_479_ = stack[0].m_obj;
lean_object* v_a_480_ = stack[1].m_obj;
lean_object* v_a_481_ = stack[2].m_obj;
lean_object* v_a_482_ = stack[3].m_obj;
lean_object* v_a_483_ = stack[4].m_obj;
lean_object* v_a_484_ = stack[5].m_obj;
lean_object* v_a_485_ = stack[6].m_obj;
lean_object* v_a_486_ = stack[7].m_obj;
lean_object* v_a_487_ = stack[8].m_obj;
lean_object* v_a_488_ = stack[9].m_obj;
lean_object* v_a_489_ = stack[10].m_obj;
lean_object* v_res_826_;
v_res_826_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v_c_479_, v_a_480_, v_a_481_, v_a_482_, v_a_483_, v_a_484_, v_a_485_, v_a_486_, v_a_487_, v_a_488_, v_a_489_);
stack->m_obj
 = v_res_826_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert___boxed(lean_object* v_c_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v_c_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_, v_a_837_);
lean_dec(v_a_837_);
lean_dec(v_a_835_);
lean_dec_ref(v_a_834_);
lean_dec(v_a_833_);
lean_dec_ref(v_a_832_);
lean_dec(v_a_831_);
lean_dec_ref(v_a_830_);
lean_dec(v_a_829_);
lean_dec(v_a_828_);
return v_res_839_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(lean_object* v_c_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_){
_start:
{
lean_object* v_d_852_; lean_object* v_p_853_; lean_object* v___x_854_; 
v_d_852_ = lean_ctor_get(v_c_840_, 0);
v_p_853_ = lean_ctor_get(v_c_840_, 1);
lean_inc_ref(v_p_853_);
v___x_854_ = l_Int_Internal_Linear_Poly_normCommRing_x3f(v_p_853_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_a_855_);
lean_dec_ref_known(v___x_854_, 1);
if (lean_obj_tag(v_a_855_) == 1)
{
lean_object* v_val_856_; lean_object* v_snd_857_; lean_object* v_fst_858_; lean_object* v_fst_859_; lean_object* v_snd_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
lean_inc(v_d_852_);
v_val_856_ = lean_ctor_get(v_a_855_, 0);
lean_inc(v_val_856_);
lean_dec_ref_known(v_a_855_, 1);
v_snd_857_ = lean_ctor_get(v_val_856_, 1);
lean_inc(v_snd_857_);
v_fst_858_ = lean_ctor_get(v_val_856_, 0);
lean_inc(v_fst_858_);
lean_dec(v_val_856_);
v_fst_859_ = lean_ctor_get(v_snd_857_, 0);
lean_inc(v_fst_859_);
v_snd_860_ = lean_ctor_get(v_snd_857_, 1);
lean_inc(v_snd_860_);
lean_dec(v_snd_857_);
v___x_861_ = lean_alloc_ctor(12, 3, 0);
lean_ctor_set(v___x_861_, 0, v_c_840_);
lean_ctor_set(v___x_861_, 1, v_fst_858_);
lean_ctor_set(v___x_861_, 2, v_fst_859_);
v___x_862_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_862_, 0, v_d_852_);
lean_ctor_set(v___x_862_, 1, v_snd_860_);
lean_ctor_set(v___x_862_, 2, v___x_861_);
lean_inc_ref(v_a_849_);
v___x_863_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v___x_862_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_);
return v___x_863_;
}
else
{
lean_object* v___x_864_; 
lean_dec(v_a_855_);
lean_inc_ref(v_a_849_);
v___x_864_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(v_c_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_);
return v___x_864_;
}
}
else
{
lean_object* v_a_865_; lean_object* v___x_867_; uint8_t v_isShared_868_; uint8_t v_isSharedCheck_872_; 
lean_dec_ref(v_c_840_);
v_a_865_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_872_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_872_ == 0)
{
v___x_867_ = v___x_854_;
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
else
{
lean_inc(v_a_865_);
lean_dec(v___x_854_);
v___x_867_ = lean_box(0);
v_isShared_868_ = v_isSharedCheck_872_;
goto v_resetjp_866_;
}
v_resetjp_866_:
{
lean_object* v___x_870_; 
if (v_isShared_868_ == 0)
{
v___x_870_ = v___x_867_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v_a_865_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_840_ = stack[0].m_obj;
lean_object* v_a_841_ = stack[1].m_obj;
lean_object* v_a_842_ = stack[2].m_obj;
lean_object* v_a_843_ = stack[3].m_obj;
lean_object* v_a_844_ = stack[4].m_obj;
lean_object* v_a_845_ = stack[5].m_obj;
lean_object* v_a_846_ = stack[6].m_obj;
lean_object* v_a_847_ = stack[7].m_obj;
lean_object* v_a_848_ = stack[8].m_obj;
lean_object* v_a_849_ = stack[9].m_obj;
lean_object* v_a_850_ = stack[10].m_obj;
lean_object* v_res_873_;
v_res_873_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v_c_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_);
stack->m_obj
 = v_res_873_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore___boxed(lean_object* v_c_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_){
_start:
{
lean_object* v_res_886_; 
v_res_886_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v_c_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_);
lean_dec(v_a_884_);
lean_dec_ref(v_a_883_);
lean_dec(v_a_882_);
lean_dec_ref(v_a_881_);
lean_dec(v_a_880_);
lean_dec_ref(v_a_879_);
lean_dec(v_a_878_);
lean_dec_ref(v_a_877_);
lean_dec(v_a_876_);
lean_dec(v_a_875_);
return v_res_886_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8(void){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; 
v___x_901_ = lean_box(0);
v___x_902_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__7));
v___x_903_ = l_Lean_mkConst(v___x_902_, v___x_901_);
return v___x_903_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10(void){
_start:
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__9));
v___x_906_ = l_Lean_stringToMessageData(v___x_905_);
return v___x_906_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(lean_object* v_e_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_){
_start:
{
lean_object* v___x_925_; 
lean_inc_ref(v_e_907_);
v___x_925_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_907_, v_a_915_);
if (lean_obj_tag(v___x_925_) == 0)
{
lean_object* v_a_926_; lean_object* v___x_927_; uint8_t v___x_928_; 
v_a_926_ = lean_ctor_get(v___x_925_, 0);
lean_inc(v_a_926_);
lean_dec_ref_known(v___x_925_, 1);
v___x_927_ = l_Lean_Expr_cleanupAnnotations(v_a_926_);
v___x_928_ = l_Lean_Expr_isApp(v___x_927_);
if (v___x_928_ == 0)
{
lean_dec_ref(v___x_927_);
lean_dec_ref(v_e_907_);
goto v___jp_919_;
}
else
{
lean_object* v_arg_929_; lean_object* v___x_930_; uint8_t v___x_931_; 
v_arg_929_ = lean_ctor_get(v___x_927_, 1);
lean_inc_ref(v_arg_929_);
v___x_930_ = l_Lean_Expr_appFnCleanup___redArg(v___x_927_);
v___x_931_ = l_Lean_Expr_isApp(v___x_930_);
if (v___x_931_ == 0)
{
lean_dec_ref(v___x_930_);
lean_dec_ref(v_arg_929_);
lean_dec_ref(v_e_907_);
goto v___jp_919_;
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
lean_dec_ref(v_arg_929_);
lean_dec_ref(v_e_907_);
goto v___jp_919_;
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
lean_dec_ref(v_arg_929_);
lean_dec_ref(v_e_907_);
goto v___jp_919_;
}
else
{
lean_object* v___x_938_; lean_object* v___x_939_; uint8_t v___x_940_; 
v___x_938_ = l_Lean_Expr_appFnCleanup___redArg(v___x_936_);
v___x_939_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_940_ = l_Lean_Expr_isConstOf(v___x_938_, v___x_939_);
lean_dec_ref(v___x_938_);
if (v___x_940_ == 0)
{
lean_dec_ref(v_arg_935_);
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_arg_929_);
lean_dec_ref(v_e_907_);
goto v___jp_919_;
}
else
{
lean_object* v___x_941_; 
v___x_941_ = l_Lean_Meta_Structural_isInstDvdInt___redArg(v_arg_935_, v_a_915_);
if (lean_obj_tag(v___x_941_) == 0)
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_1042_; 
v_a_942_ = lean_ctor_get(v___x_941_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_944_ = v___x_941_;
v_isShared_945_ = v_isSharedCheck_1042_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_941_);
v___x_944_ = lean_box(0);
v_isShared_945_ = v_isSharedCheck_1042_;
goto v_resetjp_943_;
}
v_resetjp_943_:
{
uint8_t v___x_946_; 
v___x_946_ = lean_unbox(v_a_942_);
lean_dec(v_a_942_);
if (v___x_946_ == 0)
{
lean_object* v___x_947_; lean_object* v___x_949_; 
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_arg_929_);
lean_dec_ref(v_e_907_);
v___x_947_ = lean_box(0);
if (v_isShared_945_ == 0)
{
lean_ctor_set(v___x_944_, 0, v___x_947_);
v___x_949_ = v___x_944_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_947_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
else
{
lean_object* v___x_951_; 
lean_del_object(v___x_944_);
lean_inc_ref(v_arg_932_);
v___x_951_ = l_Lean_Meta_getIntValue_x3f(v_arg_932_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v_a_952_; 
v_a_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_a_952_);
lean_dec_ref_known(v___x_951_, 1);
if (lean_obj_tag(v_a_952_) == 1)
{
lean_object* v_val_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_1018_; 
v_val_953_ = lean_ctor_get(v_a_952_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v_a_952_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_955_ = v_a_952_;
v_isShared_956_ = v_isSharedCheck_1018_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_val_953_);
lean_dec(v_a_952_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_1018_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_957_; 
lean_inc_ref(v_e_907_);
v___x_957_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_907_, v_a_908_, v_a_912_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v_a_958_; uint8_t v___x_959_; 
v_a_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_a_958_);
lean_dec_ref_known(v___x_957_, 1);
v___x_959_ = lean_unbox(v_a_958_);
lean_dec(v_a_958_);
if (v___x_959_ == 0)
{
lean_object* v___x_960_; 
lean_del_object(v___x_955_);
lean_dec(v_val_953_);
lean_inc_ref(v_e_907_);
v___x_960_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_907_, v_a_908_, v_a_912_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_986_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_986_ == 0)
{
v___x_963_ = v___x_960_;
v_isShared_964_ = v_isSharedCheck_986_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_960_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_986_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
uint8_t v___x_965_; 
v___x_965_ = lean_unbox(v_a_961_);
lean_dec(v_a_961_);
if (v___x_965_ == 0)
{
lean_object* v___x_966_; lean_object* v___x_968_; 
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_arg_929_);
lean_dec_ref(v_e_907_);
v___x_966_ = lean_box(0);
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 0, v___x_966_);
v___x_968_ = v___x_963_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v___x_966_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
else
{
lean_object* v___x_970_; 
lean_del_object(v___x_963_);
lean_inc_ref(v_e_907_);
v___x_970_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v_a_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v_a_971_ = lean_ctor_get(v___x_970_, 0);
lean_inc(v_a_971_);
lean_dec_ref_known(v___x_970_, 1);
v___x_972_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__8);
v___x_973_ = l_Lean_eagerReflBoolTrue;
v___x_974_ = l_Lean_Meta_mkOfEqFalseCore(v_e_907_, v_a_971_);
v___x_975_ = l_Lean_mkApp4(v___x_972_, v_arg_932_, v_arg_929_, v___x_973_, v___x_974_);
v___x_976_ = lean_unsigned_to_nat(0u);
v___x_977_ = l_Lean_Meta_Grind_pushNewFact(v___x_975_, v___x_976_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
return v___x_977_;
}
else
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_985_; 
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_arg_929_);
lean_dec_ref(v_e_907_);
v_a_978_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_985_ == 0)
{
v___x_980_ = v___x_970_;
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_970_);
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
}
}
else
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_994_; 
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_arg_929_);
lean_dec_ref(v_e_907_);
v_a_987_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_994_ == 0)
{
v___x_989_ = v___x_960_;
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_960_);
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
else
{
lean_object* v___x_995_; 
lean_dec_ref(v_arg_932_);
v___x_995_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(v_arg_929_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
if (lean_obj_tag(v___x_995_) == 0)
{
lean_object* v_a_996_; lean_object* v___x_998_; 
v_a_996_ = lean_ctor_get(v___x_995_, 0);
lean_inc(v_a_996_);
lean_dec_ref_known(v___x_995_, 1);
if (v_isShared_956_ == 0)
{
lean_ctor_set_tag(v___x_955_, 0);
lean_ctor_set(v___x_955_, 0, v_e_907_);
v___x_998_ = v___x_955_;
goto v_reusejp_997_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v_e_907_);
v___x_998_ = v_reuseFailAlloc_1001_;
goto v_reusejp_997_;
}
v_reusejp_997_:
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_999_, 0, v_val_953_);
lean_ctor_set(v___x_999_, 1, v_a_996_);
lean_ctor_set(v___x_999_, 2, v___x_998_);
v___x_1000_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v___x_999_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
return v___x_1000_;
}
}
else
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
lean_del_object(v___x_955_);
lean_dec(v_val_953_);
lean_dec_ref(v_e_907_);
v_a_1002_ = lean_ctor_get(v___x_995_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1004_ = v___x_995_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_995_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_a_1002_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
}
else
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
lean_del_object(v___x_955_);
lean_dec(v_val_953_);
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_arg_929_);
lean_dec_ref(v_e_907_);
v_a_1010_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_957_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_957_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_1013_ == 0)
{
v___x_1015_ = v___x_1012_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1010_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
}
else
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
lean_dec(v_a_952_);
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_arg_929_);
v___x_1019_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10);
v___x_1020_ = l_Lean_indentExpr(v_e_907_);
v___x_1021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1019_);
lean_ctor_set(v___x_1021_, 1, v___x_1020_);
v___x_1022_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_912_);
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
lean_dec_ref_known(v___x_1021_, 2);
goto v___jp_922_;
}
else
{
lean_object* v___x_1025_; 
v___x_1025_ = l_Lean_Meta_Sym_reportIssue(v___x_1021_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_dec_ref_known(v___x_1025_, 1);
goto v___jp_922_;
}
else
{
return v___x_1025_;
}
}
}
else
{
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1033_; 
lean_dec_ref_known(v___x_1021_, 2);
v_a_1026_ = lean_ctor_get(v___x_1022_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1022_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1028_ = v___x_1022_;
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1022_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
lean_object* v___x_1031_; 
if (v_isShared_1029_ == 0)
{
v___x_1031_ = v___x_1028_;
goto v_reusejp_1030_;
}
else
{
lean_object* v_reuseFailAlloc_1032_; 
v_reuseFailAlloc_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1026_);
v___x_1031_ = v_reuseFailAlloc_1032_;
goto v_reusejp_1030_;
}
v_reusejp_1030_:
{
return v___x_1031_;
}
}
}
}
}
else
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1041_; 
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_arg_929_);
lean_dec_ref(v_e_907_);
v_a_1034_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1036_ = v___x_951_;
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_951_);
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
else
{
lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1050_; 
lean_dec_ref(v_arg_932_);
lean_dec_ref(v_arg_929_);
lean_dec_ref(v_e_907_);
v_a_1043_ = lean_ctor_get(v___x_941_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_941_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1045_ = v___x_941_;
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___x_941_);
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
}
}
}
else
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1058_; 
lean_dec_ref(v_e_907_);
v_a_1051_ = lean_ctor_get(v___x_925_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_925_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1053_ = v___x_925_;
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_925_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1056_; 
if (v_isShared_1054_ == 0)
{
v___x_1056_ = v___x_1053_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_a_1051_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
v___jp_919_:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = lean_box(0);
v___x_921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_921_, 0, v___x_920_);
return v___x_921_;
}
v___jp_922_:
{
lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_923_ = lean_box(0);
v___x_924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_924_, 0, v___x_923_);
return v___x_924_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_907_ = stack[0].m_obj;
lean_object* v_a_908_ = stack[1].m_obj;
lean_object* v_a_909_ = stack[2].m_obj;
lean_object* v_a_910_ = stack[3].m_obj;
lean_object* v_a_911_ = stack[4].m_obj;
lean_object* v_a_912_ = stack[5].m_obj;
lean_object* v_a_913_ = stack[6].m_obj;
lean_object* v_a_914_ = stack[7].m_obj;
lean_object* v_a_915_ = stack[8].m_obj;
lean_object* v_a_916_ = stack[9].m_obj;
lean_object* v_a_917_ = stack[10].m_obj;
lean_object* v_res_1059_;
v_res_1059_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(v_e_907_, v_a_908_, v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_);
stack->m_obj
 = v_res_1059_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___boxed(lean_object* v_e_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(v_e_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_);
lean_dec(v_a_1070_);
lean_dec_ref(v_a_1069_);
lean_dec(v_a_1068_);
lean_dec_ref(v_a_1067_);
lean_dec(v_a_1066_);
lean_dec_ref(v_a_1065_);
lean_dec(v_a_1064_);
lean_dec_ref(v_a_1063_);
lean_dec(v_a_1062_);
lean_dec(v_a_1061_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd_spec__0(lean_object* v_a_1073_){
_start:
{
lean_object* v___x_1074_; 
v___x_1074_ = lean_nat_to_int(v_a_1073_);
return v___x_1074_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3(void){
_start:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1080_ = lean_box(0);
v___x_1081_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__2));
v___x_1082_ = l_Lean_mkConst(v___x_1081_, v___x_1080_);
return v___x_1082_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7(void){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1089_ = lean_box(0);
v___x_1090_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__6));
v___x_1091_ = l_Lean_mkConst(v___x_1090_, v___x_1089_);
return v___x_1091_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(lean_object* v_e_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_, lean_object* v_a_1101_, lean_object* v_a_1102_){
_start:
{
lean_object* v___x_1110_; uint8_t v___x_1111_; 
lean_inc_ref(v_e_1092_);
v___x_1110_ = l_Lean_Expr_cleanupAnnotations(v_e_1092_);
v___x_1111_ = l_Lean_Expr_isApp(v___x_1110_);
if (v___x_1111_ == 0)
{
lean_dec_ref(v___x_1110_);
lean_dec_ref(v_e_1092_);
goto v___jp_1104_;
}
else
{
lean_object* v_arg_1112_; lean_object* v___x_1113_; uint8_t v___x_1114_; 
v_arg_1112_ = lean_ctor_get(v___x_1110_, 1);
lean_inc_ref(v_arg_1112_);
v___x_1113_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1110_);
v___x_1114_ = l_Lean_Expr_isApp(v___x_1113_);
if (v___x_1114_ == 0)
{
lean_dec_ref(v___x_1113_);
lean_dec_ref(v_arg_1112_);
lean_dec_ref(v_e_1092_);
goto v___jp_1104_;
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
lean_dec_ref(v_arg_1112_);
lean_dec_ref(v_e_1092_);
goto v___jp_1104_;
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
lean_dec_ref(v_arg_1112_);
lean_dec_ref(v_e_1092_);
goto v___jp_1104_;
}
else
{
lean_object* v___x_1121_; lean_object* v___x_1122_; uint8_t v___x_1123_; 
v___x_1121_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1119_);
v___x_1122_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1123_ = l_Lean_Expr_isConstOf(v___x_1121_, v___x_1122_);
lean_dec_ref(v___x_1121_);
if (v___x_1123_ == 0)
{
lean_dec_ref(v_arg_1118_);
lean_dec_ref(v_arg_1115_);
lean_dec_ref(v_arg_1112_);
lean_dec_ref(v_e_1092_);
goto v___jp_1104_;
}
else
{
lean_object* v___x_1124_; 
v___x_1124_ = l_Lean_Meta_Structural_isInstDvdNat___redArg(v_arg_1118_, v_a_1100_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v_a_1125_; lean_object* v___x_1127_; uint8_t v_isShared_1128_; uint8_t v_isSharedCheck_1256_; 
v_a_1125_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1127_ = v___x_1124_;
v_isShared_1128_ = v_isSharedCheck_1256_;
goto v_resetjp_1126_;
}
else
{
lean_inc(v_a_1125_);
lean_dec(v___x_1124_);
v___x_1127_ = lean_box(0);
v_isShared_1128_ = v_isSharedCheck_1256_;
goto v_resetjp_1126_;
}
v_resetjp_1126_:
{
uint8_t v___x_1129_; 
v___x_1129_ = lean_unbox(v_a_1125_);
lean_dec(v_a_1125_);
if (v___x_1129_ == 0)
{
lean_object* v___x_1130_; lean_object* v___x_1132_; 
lean_dec_ref(v_arg_1115_);
lean_dec_ref(v_arg_1112_);
lean_dec_ref(v_e_1092_);
v___x_1130_ = lean_box(0);
if (v_isShared_1128_ == 0)
{
lean_ctor_set(v___x_1127_, 0, v___x_1130_);
v___x_1132_ = v___x_1127_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1130_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
else
{
lean_object* v___x_1134_; 
lean_del_object(v___x_1127_);
v___x_1134_ = l_Lean_Meta_getNatValue_x3f(v_arg_1115_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_);
if (lean_obj_tag(v___x_1134_) == 0)
{
lean_object* v_a_1135_; 
v_a_1135_ = lean_ctor_get(v___x_1134_, 0);
lean_inc(v_a_1135_);
lean_dec_ref_known(v___x_1134_, 1);
if (lean_obj_tag(v_a_1135_) == 1)
{
lean_object* v_val_1136_; lean_object* v___x_1137_; 
v_val_1136_ = lean_ctor_get(v_a_1135_, 0);
lean_inc(v_val_1136_);
lean_dec_ref_known(v_a_1135_, 1);
lean_inc_ref(v_e_1092_);
v___x_1137_ = l_Lean_Meta_Grind_isEqTrue___redArg(v_e_1092_, v_a_1093_, v_a_1097_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v_a_1138_; uint8_t v___x_1139_; 
v_a_1138_ = lean_ctor_get(v___x_1137_, 0);
lean_inc(v_a_1138_);
lean_dec_ref_known(v___x_1137_, 1);
v___x_1139_ = lean_unbox(v_a_1138_);
lean_dec(v_a_1138_);
if (v___x_1139_ == 0)
{
lean_object* v___x_1140_; 
lean_dec(v_val_1136_);
lean_inc_ref(v_e_1092_);
v___x_1140_ = l_Lean_Meta_Grind_isEqFalse___redArg(v_e_1092_, v_a_1093_, v_a_1097_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1165_; 
v_a_1141_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1143_ = v___x_1140_;
v_isShared_1144_ = v_isSharedCheck_1165_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1140_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1165_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
uint8_t v___x_1145_; 
v___x_1145_ = lean_unbox(v_a_1141_);
lean_dec(v_a_1141_);
if (v___x_1145_ == 0)
{
lean_object* v___x_1146_; lean_object* v___x_1148_; 
lean_dec_ref(v_arg_1115_);
lean_dec_ref(v_arg_1112_);
lean_dec_ref(v_e_1092_);
v___x_1146_ = lean_box(0);
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 0, v___x_1146_);
v___x_1148_ = v___x_1143_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v___x_1146_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
else
{
lean_object* v___x_1150_; 
lean_del_object(v___x_1143_);
lean_inc_ref(v_e_1092_);
v___x_1150_ = l_Lean_Meta_Grind_mkEqFalseProof(v_e_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_);
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_object* v_a_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; 
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
lean_inc(v_a_1151_);
lean_dec_ref_known(v___x_1150_, 1);
v___x_1152_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__3);
v___x_1153_ = l_Lean_Meta_mkOfEqFalseCore(v_e_1092_, v_a_1151_);
v___x_1154_ = l_Lean_mkApp3(v___x_1152_, v_arg_1115_, v_arg_1112_, v___x_1153_);
v___x_1155_ = lean_unsigned_to_nat(0u);
v___x_1156_ = l_Lean_Meta_Grind_pushNewFact(v___x_1154_, v___x_1155_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_);
return v___x_1156_;
}
else
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1164_; 
lean_dec_ref(v_arg_1115_);
lean_dec_ref(v_arg_1112_);
lean_dec_ref(v_e_1092_);
v_a_1157_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1159_ = v___x_1150_;
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1150_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_a_1157_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
}
}
else
{
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1173_; 
lean_dec_ref(v_arg_1115_);
lean_dec_ref(v_arg_1112_);
lean_dec_ref(v_e_1092_);
v_a_1166_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1168_ = v___x_1140_;
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1140_);
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
else
{
lean_object* v___x_1174_; 
lean_inc_ref(v_arg_1115_);
v___x_1174_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_1115_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v_a_1175_; lean_object* v_fst_1176_; lean_object* v_snd_1177_; lean_object* v___x_1178_; 
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_a_1175_);
lean_dec_ref_known(v___x_1174_, 1);
v_fst_1176_ = lean_ctor_get(v_a_1175_, 0);
lean_inc(v_fst_1176_);
v_snd_1177_ = lean_ctor_get(v_a_1175_, 1);
lean_inc(v_snd_1177_);
lean_dec(v_a_1175_);
lean_inc_ref(v_arg_1112_);
v___x_1178_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_1112_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_);
if (lean_obj_tag(v___x_1178_) == 0)
{
lean_object* v_a_1179_; lean_object* v_fst_1180_; lean_object* v_snd_1181_; lean_object* v___x_1182_; 
v_a_1179_ = lean_ctor_get(v___x_1178_, 0);
lean_inc(v_a_1179_);
lean_dec_ref_known(v___x_1178_, 1);
v_fst_1180_ = lean_ctor_get(v_a_1179_, 0);
lean_inc(v_fst_1180_);
v_snd_1181_ = lean_ctor_get(v_a_1179_, 1);
lean_inc(v_snd_1181_);
lean_dec(v_a_1179_);
v___x_1182_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_1092_, v_a_1093_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v_a_1183_; lean_object* v___x_1184_; 
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
lean_inc(v_a_1183_);
lean_dec_ref_known(v___x_1182_, 1);
lean_inc(v_fst_1180_);
v___x_1184_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_1180_, v_a_1183_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_);
if (lean_obj_tag(v___x_1184_) == 0)
{
lean_object* v_a_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; 
v_a_1185_ = lean_ctor_get(v___x_1184_, 0);
lean_inc(v_a_1185_);
lean_dec_ref_known(v___x_1184_, 1);
v___x_1186_ = l_Int_Internal_Linear_Expr_norm(v_a_1185_);
v___x_1187_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___closed__7);
v___x_1188_ = l_Lean_mkApp6(v___x_1187_, v_arg_1115_, v_arg_1112_, v_fst_1176_, v_fst_1180_, v_snd_1177_, v_snd_1181_);
lean_inc(v_val_1136_);
v___x_1189_ = lean_nat_to_int(v_val_1136_);
v___x_1190_ = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(v___x_1190_, 0, v_e_1092_);
lean_ctor_set(v___x_1190_, 1, v___x_1188_);
lean_ctor_set(v___x_1190_, 2, v_val_1136_);
lean_ctor_set(v___x_1190_, 3, v_a_1185_);
v___x_1191_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1189_);
lean_ctor_set(v___x_1191_, 1, v___x_1186_);
lean_ctor_set(v___x_1191_, 2, v___x_1190_);
v___x_1192_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assertCore(v___x_1191_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_);
return v___x_1192_;
}
else
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1200_; 
lean_dec(v_snd_1181_);
lean_dec(v_fst_1180_);
lean_dec(v_snd_1177_);
lean_dec(v_fst_1176_);
lean_dec(v_val_1136_);
lean_dec_ref(v_arg_1115_);
lean_dec_ref(v_arg_1112_);
lean_dec_ref(v_e_1092_);
v_a_1193_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1200_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1195_ = v___x_1184_;
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1184_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1200_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___x_1198_; 
if (v_isShared_1196_ == 0)
{
v___x_1198_ = v___x_1195_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_a_1193_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
}
else
{
lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1208_; 
lean_dec(v_snd_1181_);
lean_dec(v_fst_1180_);
lean_dec(v_snd_1177_);
lean_dec(v_fst_1176_);
lean_dec(v_val_1136_);
lean_dec_ref(v_arg_1115_);
lean_dec_ref(v_arg_1112_);
lean_dec_ref(v_e_1092_);
v_a_1201_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1203_ = v___x_1182_;
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v___x_1182_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1206_; 
if (v_isShared_1204_ == 0)
{
v___x_1206_ = v___x_1203_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_a_1201_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
else
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
lean_dec(v_snd_1177_);
lean_dec(v_fst_1176_);
lean_dec(v_val_1136_);
lean_dec_ref(v_arg_1115_);
lean_dec_ref(v_arg_1112_);
lean_dec_ref(v_e_1092_);
v_a_1209_ = lean_ctor_get(v___x_1178_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1178_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1211_ = v___x_1178_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1178_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1209_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
else
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1224_; 
lean_dec(v_val_1136_);
lean_dec_ref(v_arg_1115_);
lean_dec_ref(v_arg_1112_);
lean_dec_ref(v_e_1092_);
v_a_1217_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1219_ = v___x_1174_;
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v___x_1174_);
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
else
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1232_; 
lean_dec(v_val_1136_);
lean_dec_ref(v_arg_1115_);
lean_dec_ref(v_arg_1112_);
lean_dec_ref(v_e_1092_);
v_a_1225_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1227_ = v___x_1137_;
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1137_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1230_; 
if (v_isShared_1228_ == 0)
{
v___x_1230_ = v___x_1227_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_a_1225_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
}
else
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; 
lean_dec(v_a_1135_);
lean_dec_ref(v_arg_1115_);
lean_dec_ref(v_arg_1112_);
v___x_1233_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__10);
v___x_1234_ = l_Lean_indentExpr(v_e_1092_);
v___x_1235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1233_);
lean_ctor_set(v___x_1235_, 1, v___x_1234_);
v___x_1236_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1097_);
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
lean_dec_ref_known(v___x_1235_, 2);
goto v___jp_1107_;
}
else
{
lean_object* v___x_1239_; 
v___x_1239_ = l_Lean_Meta_Sym_reportIssue(v___x_1235_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_dec_ref_known(v___x_1239_, 1);
goto v___jp_1107_;
}
else
{
return v___x_1239_;
}
}
}
else
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
lean_dec_ref_known(v___x_1235_, 2);
v_a_1240_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1236_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1236_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1240_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
}
else
{
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1255_; 
lean_dec_ref(v_arg_1115_);
lean_dec_ref(v_arg_1112_);
lean_dec_ref(v_e_1092_);
v_a_1248_ = lean_ctor_get(v___x_1134_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1134_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1250_ = v___x_1134_;
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1134_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
if (v_isShared_1251_ == 0)
{
v___x_1253_ = v___x_1250_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_a_1248_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
}
}
else
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1264_; 
lean_dec_ref(v_arg_1115_);
lean_dec_ref(v_arg_1112_);
lean_dec_ref(v_e_1092_);
v_a_1257_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1259_ = v___x_1124_;
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1124_);
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
}
}
v___jp_1104_:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = lean_box(0);
v___x_1106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1105_);
return v___x_1106_;
}
v___jp_1107_:
{
lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1108_ = lean_box(0);
v___x_1109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1109_, 0, v___x_1108_);
return v___x_1109_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1092_ = stack[0].m_obj;
lean_object* v_a_1093_ = stack[1].m_obj;
lean_object* v_a_1094_ = stack[2].m_obj;
lean_object* v_a_1095_ = stack[3].m_obj;
lean_object* v_a_1096_ = stack[4].m_obj;
lean_object* v_a_1097_ = stack[5].m_obj;
lean_object* v_a_1098_ = stack[6].m_obj;
lean_object* v_a_1099_ = stack[7].m_obj;
lean_object* v_a_1100_ = stack[8].m_obj;
lean_object* v_a_1101_ = stack[9].m_obj;
lean_object* v_a_1102_ = stack[10].m_obj;
lean_object* v_res_1265_;
v_res_1265_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(v_e_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_, v_a_1099_, v_a_1100_, v_a_1101_, v_a_1102_);
stack->m_obj
 = v_res_1265_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd___boxed(lean_object* v_e_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(v_e_1266_, v_a_1267_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_);
lean_dec(v_a_1276_);
lean_dec_ref(v_a_1275_);
lean_dec(v_a_1274_);
lean_dec_ref(v_a_1273_);
lean_dec(v_a_1272_);
lean_dec_ref(v_a_1271_);
lean_dec(v_a_1270_);
lean_dec_ref(v_a_1269_);
lean_dec(v_a_1268_);
lean_dec(v_a_1267_);
return v_res_1278_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(lean_object* v_e_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_, lean_object* v_a_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_, lean_object* v_a_1290_, lean_object* v_a_1291_){
_start:
{
lean_object* v___x_1296_; 
v___x_1296_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_1284_);
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_a_1297_; lean_object* v___x_1299_; uint8_t v_isShared_1300_; uint8_t v_isSharedCheck_1332_; 
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1299_ = v___x_1296_;
v_isShared_1300_ = v_isSharedCheck_1332_;
goto v_resetjp_1298_;
}
else
{
lean_inc(v_a_1297_);
lean_dec(v___x_1296_);
v___x_1299_ = lean_box(0);
v_isShared_1300_ = v_isSharedCheck_1332_;
goto v_resetjp_1298_;
}
v_resetjp_1298_:
{
uint8_t v_lia_1301_; 
v_lia_1301_ = lean_ctor_get_uint8(v_a_1297_, sizeof(void*)*14 + 23);
lean_dec(v_a_1297_);
if (v_lia_1301_ == 0)
{
lean_object* v___x_1302_; lean_object* v___x_1304_; 
lean_dec_ref(v_e_1281_);
v___x_1302_ = lean_box(0);
if (v_isShared_1300_ == 0)
{
lean_ctor_set(v___x_1299_, 0, v___x_1302_);
v___x_1304_ = v___x_1299_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v___x_1302_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
else
{
lean_object* v___x_1306_; 
lean_del_object(v___x_1299_);
lean_inc_ref(v_e_1281_);
v___x_1306_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_1281_, v_a_1289_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_object* v_a_1307_; lean_object* v___x_1308_; uint8_t v___x_1309_; 
v_a_1307_ = lean_ctor_get(v___x_1306_, 0);
lean_inc(v_a_1307_);
lean_dec_ref_known(v___x_1306_, 1);
v___x_1308_ = l_Lean_Expr_cleanupAnnotations(v_a_1307_);
v___x_1309_ = l_Lean_Expr_isApp(v___x_1308_);
if (v___x_1309_ == 0)
{
lean_dec_ref(v___x_1308_);
lean_dec_ref(v_e_1281_);
goto v___jp_1293_;
}
else
{
lean_object* v___x_1310_; uint8_t v___x_1311_; 
v___x_1310_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1308_);
v___x_1311_ = l_Lean_Expr_isApp(v___x_1310_);
if (v___x_1311_ == 0)
{
lean_dec_ref(v___x_1310_);
lean_dec_ref(v_e_1281_);
goto v___jp_1293_;
}
else
{
lean_object* v___x_1312_; uint8_t v___x_1313_; 
v___x_1312_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1310_);
v___x_1313_ = l_Lean_Expr_isApp(v___x_1312_);
if (v___x_1313_ == 0)
{
lean_dec_ref(v___x_1312_);
lean_dec_ref(v_e_1281_);
goto v___jp_1293_;
}
else
{
lean_object* v___x_1314_; uint8_t v___x_1315_; 
v___x_1314_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1312_);
v___x_1315_ = l_Lean_Expr_isApp(v___x_1314_);
if (v___x_1315_ == 0)
{
lean_dec_ref(v___x_1314_);
lean_dec_ref(v_e_1281_);
goto v___jp_1293_;
}
else
{
lean_object* v_arg_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; uint8_t v___x_1319_; 
v_arg_1316_ = lean_ctor_get(v___x_1314_, 1);
lean_inc_ref(v_arg_1316_);
v___x_1317_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1314_);
v___x_1318_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1319_ = l_Lean_Expr_isConstOf(v___x_1317_, v___x_1318_);
lean_dec_ref(v___x_1317_);
if (v___x_1319_ == 0)
{
lean_dec_ref(v_arg_1316_);
lean_dec_ref(v_e_1281_);
goto v___jp_1293_;
}
else
{
lean_object* v___x_1320_; uint8_t v___x_1321_; 
v___x_1320_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___closed__0));
v___x_1321_ = l_Lean_Expr_isConstOf(v_arg_1316_, v___x_1320_);
lean_dec_ref(v_arg_1316_);
if (v___x_1321_ == 0)
{
lean_object* v___x_1322_; 
v___x_1322_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(v_e_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_);
return v___x_1322_;
}
else
{
lean_object* v___x_1323_; 
v___x_1323_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(v_e_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_);
return v___x_1323_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1331_; 
lean_dec_ref(v_e_1281_);
v_a_1324_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1326_ = v___x_1306_;
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v___x_1306_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1329_; 
if (v_isShared_1327_ == 0)
{
v___x_1329_ = v___x_1326_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_a_1324_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
}
}
}
else
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
lean_dec_ref(v_e_1281_);
v_a_1333_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1335_ = v___x_1296_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1296_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_a_1333_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
v___jp_1293_:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1294_ = lean_box(0);
v___x_1295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1295_, 0, v___x_1294_);
return v___x_1295_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1281_ = stack[0].m_obj;
lean_object* v_a_1282_ = stack[1].m_obj;
lean_object* v_a_1283_ = stack[2].m_obj;
lean_object* v_a_1284_ = stack[3].m_obj;
lean_object* v_a_1285_ = stack[4].m_obj;
lean_object* v_a_1286_ = stack[5].m_obj;
lean_object* v_a_1287_ = stack[6].m_obj;
lean_object* v_a_1288_ = stack[7].m_obj;
lean_object* v_a_1289_ = stack[8].m_obj;
lean_object* v_a_1290_ = stack[9].m_obj;
lean_object* v_a_1291_ = stack[10].m_obj;
lean_object* v_res_1341_;
v_res_1341_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(v_e_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_, v_a_1290_, v_a_1291_);
stack->m_obj
 = v_res_1341_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed(lean_object* v_e_1342_, lean_object* v_a_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_, lean_object* v_a_1346_, lean_object* v_a_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_, lean_object* v_a_1350_, lean_object* v_a_1351_, lean_object* v_a_1352_, lean_object* v_a_1353_){
_start:
{
lean_object* v_res_1354_; 
v_res_1354_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(v_e_1342_, v_a_1343_, v_a_1344_, v_a_1345_, v_a_1346_, v_a_1347_, v_a_1348_, v_a_1349_, v_a_1350_, v_a_1351_, v_a_1352_);
lean_dec(v_a_1352_);
lean_dec_ref(v_a_1351_);
lean_dec(v_a_1350_);
lean_dec_ref(v_a_1349_);
lean_dec(v_a_1348_);
lean_dec_ref(v_a_1347_);
lean_dec(v_a_1346_);
lean_dec_ref(v_a_1345_);
lean_dec(v_a_1344_);
lean_dec(v_a_1343_);
return v_res_1354_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_9_(){
_start:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1356_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd___closed__2));
v___x_1357_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd___boxed), 12, 0);
v___x_1358_ = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(v___x_1356_, v___x_1357_);
return v___x_1358_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_9__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1359_;
v_res_1359_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_9_();
stack->m_obj
 = v_res_1359_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_9____boxed(lean_object* v_a_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_0__Lean_Meta_Grind_Arith_Cutsat_propagateDvd___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr_1909565549____hygCtx___hyg_9_();
return v_res_1361_;
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
