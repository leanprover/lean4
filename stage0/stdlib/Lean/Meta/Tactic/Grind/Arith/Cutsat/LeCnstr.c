// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.LeCnstr
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Cutsat.ToInt import Init.Data.Int.OfNat import Lean.Meta.Tactic.Simp.Arith.Int import Lean.Meta.Tactic.Grind.Arith.Cutsat.Var import Lean.Meta.Tactic.Grind.Arith.Cutsat.Proof import Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat import Lean.Meta.Tactic.Grind.Arith.Cutsat.Norm import Lean.Meta.Tactic.Grind.Arith.Cutsat.CommRing
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
lean_object* l_Lean_instInhabitedPersistentArray_default(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Int_Linear_instBEqPoly_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_int_neg(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_cutsat_assert_eq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Expr_norm(lean_object*);
lean_object* l_Int_Linear_Poly_normCommRing_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_cutsat_assert_le(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntLit(lean_object*);
lean_object* l_Lean_mkIntAdd(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLE_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_ToIntM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstLEInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_mul(lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_addConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_natToInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqLBool_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_updateOccs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_gcdCoeffs_x27(lean_object*);
lean_object* l_Int_Linear_Poly_div(lean_object*, lean_object*);
uint8_t l_Int_Linear_Poly_isSorted(lean_object*);
lean_object* l_Int_Linear_Poly_norm(lean_object*);
lean_object* l_Int_Linear_Poly_findVarToSubst___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_coeff(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_combine(lean_object*, lean_object*);
uint8_t l_Int_Linear_Poly_isUnsatLe(lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLT_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_norm_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_norm(lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "grind"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "lia"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "subst"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(24, 23, 180, 58, 194, 72, 175, 153)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__3_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 228, 18, 139, 25, 122, 57, 58)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Int_Linear_Poly_isNegEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isNegEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___redArg(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__2_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "eq"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__3_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(87, 130, 109, 65, 232, 6, 169, 172)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__3_value),LEAN_SCALAR_PTR_LITERAL(150, 223, 246, 201, 117, 37, 26, 227)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "new eq: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__6;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___boxed(lean_object**);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___boxed(lean_object**);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___redArg(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__1_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___boxed(lean_object**);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0___redArg(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "assert"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "store"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(24, 23, 180, 58, 194, 72, 175, 153)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 137, 50, 202, 239, 114, 140, 141)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__1_value),LEAN_SCALAR_PTR_LITERAL(236, 213, 16, 64, 1, 14, 244, 141)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "trivial"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(24, 23, 180, 58, 194, 72, 175, 153)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 137, 50, 202, 239, 114, 140, 141)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3_value),LEAN_SCALAR_PTR_LITERAL(177, 38, 232, 206, 222, 75, 121, 224)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "unsat"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(24, 23, 180, 58, 194, 72, 175, 153)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 137, 50, 202, 239, 114, 140, 141)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 174, 99, 3, 215, 140, 75)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(24, 23, 180, 58, 194, 72, 175, 153)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 137, 50, 202, 239, 114, 140, 141)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__7_value;
LEAN_EXPORT lean_object* lean_grind_cutsat_assert_le(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "unexpected non normalized inequality constraint found"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ToInt"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "of_not_le"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__1_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__2_value),LEAN_SCALAR_PTR_LITERAL(4, 173, 245, 176, 99, 227, 18, 222)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__3_value),LEAN_SCALAR_PTR_LITERAL(79, 115, 36, 201, 96, 73, 90, 93)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "of_le"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__1_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__2_value),LEAN_SCALAR_PTR_LITERAL(4, 173, 245, 176, 99, 227, 18, 222)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(105, 164, 65, 191, 194, 192, 188, 236)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__1_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__1_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__0___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__1_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_norm_spec__0(lean_object* v_a_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_nat_to_int(v_a_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_norm(lean_object* v_c_3_){
_start:
{
lean_object* v___y_5_; lean_object* v_p_6_; lean_object* v_p_14_; uint8_t v___x_15_; 
v_p_14_ = lean_ctor_get(v_c_3_, 0);
v___x_15_ = l_Int_Linear_Poly_isSorted(v_p_14_);
if (v___x_15_ == 0)
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
lean_inc_ref(v_p_14_);
v___x_16_ = l_Int_Linear_Poly_norm(v_p_14_);
v___x_17_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_17_, 0, v_c_3_);
lean_inc_ref(v___x_16_);
v___x_18_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_18_, 0, v___x_16_);
lean_ctor_set(v___x_18_, 1, v___x_17_);
v___y_5_ = v___x_18_;
v_p_6_ = v___x_16_;
goto v___jp_4_;
}
else
{
lean_inc_ref(v_p_14_);
v___y_5_ = v_c_3_;
v_p_6_ = v_p_14_;
goto v___jp_4_;
}
v___jp_4_:
{
lean_object* v_k_7_; lean_object* v___x_8_; uint8_t v___x_9_; 
v_k_7_ = l_Int_Linear_Poly_gcdCoeffs_x27(v_p_6_);
v___x_8_ = lean_unsigned_to_nat(1u);
v___x_9_ = lean_nat_dec_eq(v_k_7_, v___x_8_);
if (v___x_9_ == 0)
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_10_ = lean_nat_to_int(v_k_7_);
v___x_11_ = l_Int_Linear_Poly_div(v___x_10_, v_p_6_);
lean_dec(v___x_10_);
v___x_12_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_12_, 0, v___y_5_);
v___x_13_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_13_, 0, v___x_11_);
lean_ctor_set(v___x_13_, 1, v___x_12_);
return v___x_13_;
}
else
{
lean_dec(v_k_7_);
lean_dec_ref(v_p_6_);
return v___y_5_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(lean_object* v_cls_22_, lean_object* v___y_23_){
_start:
{
lean_object* v_options_25_; uint8_t v_hasTrace_26_; 
v_options_25_ = lean_ctor_get(v___y_23_, 2);
v_hasTrace_26_ = lean_ctor_get_uint8(v_options_25_, sizeof(void*)*1);
if (v_hasTrace_26_ == 0)
{
lean_object* v___x_27_; lean_object* v___x_28_; 
lean_dec(v_cls_22_);
v___x_27_ = lean_box(v_hasTrace_26_);
v___x_28_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_28_, 0, v___x_27_);
return v___x_28_;
}
else
{
lean_object* v_inheritedTraceOptions_29_; lean_object* v___x_30_; lean_object* v___x_31_; uint8_t v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v_inheritedTraceOptions_29_ = lean_ctor_get(v___y_23_, 13);
v___x_30_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__1));
v___x_31_ = l_Lean_Name_append(v___x_30_, v_cls_22_);
v___x_32_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_29_, v_options_25_, v___x_31_);
lean_dec(v___x_31_);
v___x_33_ = lean_box(v___x_32_);
v___x_34_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_34_, 0, v___x_33_);
return v___x_34_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___boxed(lean_object* v_cls_35_, lean_object* v___y_36_, lean_object* v___y_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v_cls_35_, v___y_36_);
lean_dec_ref(v___y_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0(lean_object* v_cls_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_, lean_object* v___y_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v_cls_39_, v___y_48_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___boxed(lean_object* v_cls_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_, lean_object* v___y_61_, lean_object* v___y_62_, lean_object* v___y_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0(v_cls_52_, v___y_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_, v___y_60_, v___y_61_, v___y_62_);
lean_dec(v___y_62_);
lean_dec_ref(v___y_61_);
lean_dec(v___y_60_);
lean_dec_ref(v___y_59_);
lean_dec(v___y_58_);
lean_dec_ref(v___y_57_);
lean_dec(v___y_56_);
lean_dec_ref(v___y_55_);
lean_dec(v___y_54_);
lean_dec(v___y_53_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1_spec__1(lean_object* v_msgData_65_, lean_object* v___y_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_){
_start:
{
lean_object* v___x_71_; lean_object* v_env_72_; lean_object* v___x_73_; lean_object* v_mctx_74_; lean_object* v_lctx_75_; lean_object* v_options_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_71_ = lean_st_ref_get(v___y_69_);
v_env_72_ = lean_ctor_get(v___x_71_, 0);
lean_inc_ref(v_env_72_);
lean_dec(v___x_71_);
v___x_73_ = lean_st_ref_get(v___y_67_);
v_mctx_74_ = lean_ctor_get(v___x_73_, 0);
lean_inc_ref(v_mctx_74_);
lean_dec(v___x_73_);
v_lctx_75_ = lean_ctor_get(v___y_66_, 2);
v_options_76_ = lean_ctor_get(v___y_68_, 2);
lean_inc_ref(v_options_76_);
lean_inc_ref(v_lctx_75_);
v___x_77_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_77_, 0, v_env_72_);
lean_ctor_set(v___x_77_, 1, v_mctx_74_);
lean_ctor_set(v___x_77_, 2, v_lctx_75_);
lean_ctor_set(v___x_77_, 3, v_options_76_);
v___x_78_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_78_, 0, v___x_77_);
lean_ctor_set(v___x_78_, 1, v_msgData_65_);
v___x_79_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1_spec__1___boxed(lean_object* v_msgData_80_, lean_object* v___y_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1_spec__1(v_msgData_80_, v___y_81_, v___y_82_, v___y_83_, v___y_84_);
lean_dec(v___y_84_);
lean_dec_ref(v___y_83_);
lean_dec(v___y_82_);
lean_dec_ref(v___y_81_);
return v_res_86_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_87_; double v___x_88_; 
v___x_87_ = lean_unsigned_to_nat(0u);
v___x_88_ = lean_float_of_nat(v___x_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1___redArg(lean_object* v_cls_92_, lean_object* v_msg_93_, lean_object* v___y_94_, lean_object* v___y_95_, lean_object* v___y_96_, lean_object* v___y_97_){
_start:
{
lean_object* v_ref_99_; lean_object* v___x_100_; lean_object* v_a_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_145_; 
v_ref_99_ = lean_ctor_get(v___y_96_, 5);
v___x_100_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1_spec__1(v_msg_93_, v___y_94_, v___y_95_, v___y_96_, v___y_97_);
v_a_101_ = lean_ctor_get(v___x_100_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_145_ == 0)
{
v___x_103_ = v___x_100_;
v_isShared_104_ = v_isSharedCheck_145_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_a_101_);
lean_dec(v___x_100_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_145_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___x_105_; lean_object* v_traceState_106_; lean_object* v_env_107_; lean_object* v_nextMacroScope_108_; lean_object* v_ngen_109_; lean_object* v_auxDeclNGen_110_; lean_object* v_cache_111_; lean_object* v_messages_112_; lean_object* v_infoState_113_; lean_object* v_snapshotTasks_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_144_; 
v___x_105_ = lean_st_ref_take(v___y_97_);
v_traceState_106_ = lean_ctor_get(v___x_105_, 4);
v_env_107_ = lean_ctor_get(v___x_105_, 0);
v_nextMacroScope_108_ = lean_ctor_get(v___x_105_, 1);
v_ngen_109_ = lean_ctor_get(v___x_105_, 2);
v_auxDeclNGen_110_ = lean_ctor_get(v___x_105_, 3);
v_cache_111_ = lean_ctor_get(v___x_105_, 5);
v_messages_112_ = lean_ctor_get(v___x_105_, 6);
v_infoState_113_ = lean_ctor_get(v___x_105_, 7);
v_snapshotTasks_114_ = lean_ctor_get(v___x_105_, 8);
v_isSharedCheck_144_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_144_ == 0)
{
v___x_116_ = v___x_105_;
v_isShared_117_ = v_isSharedCheck_144_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_snapshotTasks_114_);
lean_inc(v_infoState_113_);
lean_inc(v_messages_112_);
lean_inc(v_cache_111_);
lean_inc(v_traceState_106_);
lean_inc(v_auxDeclNGen_110_);
lean_inc(v_ngen_109_);
lean_inc(v_nextMacroScope_108_);
lean_inc(v_env_107_);
lean_dec(v___x_105_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_144_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
uint64_t v_tid_118_; lean_object* v_traces_119_; lean_object* v___x_121_; uint8_t v_isShared_122_; uint8_t v_isSharedCheck_143_; 
v_tid_118_ = lean_ctor_get_uint64(v_traceState_106_, sizeof(void*)*1);
v_traces_119_ = lean_ctor_get(v_traceState_106_, 0);
v_isSharedCheck_143_ = !lean_is_exclusive(v_traceState_106_);
if (v_isSharedCheck_143_ == 0)
{
v___x_121_ = v_traceState_106_;
v_isShared_122_ = v_isSharedCheck_143_;
goto v_resetjp_120_;
}
else
{
lean_inc(v_traces_119_);
lean_dec(v_traceState_106_);
v___x_121_ = lean_box(0);
v_isShared_122_ = v_isSharedCheck_143_;
goto v_resetjp_120_;
}
v_resetjp_120_:
{
lean_object* v___x_123_; double v___x_124_; uint8_t v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_133_; 
v___x_123_ = lean_box(0);
v___x_124_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1___redArg___closed__0);
v___x_125_ = 0;
v___x_126_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1___redArg___closed__1));
v___x_127_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_127_, 0, v_cls_92_);
lean_ctor_set(v___x_127_, 1, v___x_123_);
lean_ctor_set(v___x_127_, 2, v___x_126_);
lean_ctor_set_float(v___x_127_, sizeof(void*)*3, v___x_124_);
lean_ctor_set_float(v___x_127_, sizeof(void*)*3 + 8, v___x_124_);
lean_ctor_set_uint8(v___x_127_, sizeof(void*)*3 + 16, v___x_125_);
v___x_128_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1___redArg___closed__2));
v___x_129_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_129_, 0, v___x_127_);
lean_ctor_set(v___x_129_, 1, v_a_101_);
lean_ctor_set(v___x_129_, 2, v___x_128_);
lean_inc(v_ref_99_);
v___x_130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_130_, 0, v_ref_99_);
lean_ctor_set(v___x_130_, 1, v___x_129_);
v___x_131_ = l_Lean_PersistentArray_push___redArg(v_traces_119_, v___x_130_);
if (v_isShared_122_ == 0)
{
lean_ctor_set(v___x_121_, 0, v___x_131_);
v___x_133_ = v___x_121_;
goto v_reusejp_132_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v___x_131_);
lean_ctor_set_uint64(v_reuseFailAlloc_142_, sizeof(void*)*1, v_tid_118_);
v___x_133_ = v_reuseFailAlloc_142_;
goto v_reusejp_132_;
}
v_reusejp_132_:
{
lean_object* v___x_135_; 
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 4, v___x_133_);
v___x_135_ = v___x_116_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_141_; 
v_reuseFailAlloc_141_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_141_, 0, v_env_107_);
lean_ctor_set(v_reuseFailAlloc_141_, 1, v_nextMacroScope_108_);
lean_ctor_set(v_reuseFailAlloc_141_, 2, v_ngen_109_);
lean_ctor_set(v_reuseFailAlloc_141_, 3, v_auxDeclNGen_110_);
lean_ctor_set(v_reuseFailAlloc_141_, 4, v___x_133_);
lean_ctor_set(v_reuseFailAlloc_141_, 5, v_cache_111_);
lean_ctor_set(v_reuseFailAlloc_141_, 6, v_messages_112_);
lean_ctor_set(v_reuseFailAlloc_141_, 7, v_infoState_113_);
lean_ctor_set(v_reuseFailAlloc_141_, 8, v_snapshotTasks_114_);
v___x_135_ = v_reuseFailAlloc_141_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_139_; 
v___x_136_ = lean_st_ref_set(v___y_97_, v___x_135_);
v___x_137_ = lean_box(0);
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 0, v___x_137_);
v___x_139_ = v___x_103_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v___x_137_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1___redArg___boxed(lean_object* v_cls_146_, lean_object* v_msg_147_, lean_object* v___y_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_){
_start:
{
lean_object* v_res_153_; 
v_res_153_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1___redArg(v_cls_146_, v_msg_147_, v___y_148_, v___y_149_, v___y_150_, v___y_151_);
lean_dec(v___y_151_);
lean_dec_ref(v___y_150_);
lean_dec(v___y_149_);
lean_dec_ref(v___y_148_);
return v_res_153_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__4));
v___x_163_ = l_Lean_stringToMessageData(v___x_162_);
return v___x_163_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = lean_unsigned_to_nat(0u);
v___x_165_ = lean_nat_to_int(v___x_164_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq(lean_object* v_a_166_, lean_object* v_x_167_, lean_object* v_c_u2081_168_, lean_object* v_b_169_, lean_object* v_c_u2082_170_, lean_object* v_a_171_, lean_object* v_a_172_, lean_object* v_a_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_){
_start:
{
lean_object* v___y_183_; lean_object* v___y_188_; lean_object* v_p_238_; lean_object* v_p_239_; lean_object* v___x_240_; uint8_t v___x_241_; 
v_p_238_ = lean_ctor_get(v_c_u2081_168_, 0);
v_p_239_ = lean_ctor_get(v_c_u2082_170_, 0);
v___x_240_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6);
v___x_241_ = lean_int_dec_le(v___x_240_, v_a_166_);
if (v___x_241_ == 0)
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
lean_inc_ref(v_p_238_);
v___x_242_ = l_Int_Linear_Poly_mul(v_p_238_, v_b_169_);
v___x_243_ = lean_int_neg(v_a_166_);
lean_inc_ref(v_p_239_);
v___x_244_ = l_Int_Linear_Poly_mul(v_p_239_, v___x_243_);
lean_dec(v___x_243_);
v___x_245_ = l_Int_Linear_Poly_combine(v___x_242_, v___x_244_);
v___y_188_ = v___x_245_;
goto v___jp_187_;
}
else
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
lean_inc_ref(v_p_239_);
v___x_246_ = l_Int_Linear_Poly_mul(v_p_239_, v_a_166_);
v___x_247_ = lean_int_neg(v_b_169_);
lean_inc_ref(v_p_238_);
v___x_248_ = l_Int_Linear_Poly_mul(v_p_238_, v___x_247_);
lean_dec(v___x_247_);
v___x_249_ = l_Int_Linear_Poly_combine(v___x_246_, v___x_248_);
v___y_188_ = v___x_249_;
goto v___jp_187_;
}
v___jp_182_:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_184_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v___x_184_, 0, v_x_167_);
lean_ctor_set(v___x_184_, 1, v_c_u2081_168_);
lean_ctor_set(v___x_184_, 2, v_c_u2082_170_);
v___x_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_185_, 0, v___y_183_);
lean_ctor_set(v___x_185_, 1, v___x_184_);
v___x_186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
return v___x_186_;
}
v___jp_187_:
{
lean_object* v_cls_189_; lean_object* v___x_190_; lean_object* v_a_191_; uint8_t v___x_192_; 
v_cls_189_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__3));
v___x_190_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v_cls_189_, v_a_179_);
v_a_191_ = lean_ctor_get(v___x_190_, 0);
lean_inc(v_a_191_);
lean_dec_ref(v___x_190_);
v___x_192_ = lean_unbox(v_a_191_);
lean_dec(v_a_191_);
if (v___x_192_ == 0)
{
v___y_183_ = v___y_188_;
goto v___jp_182_;
}
else
{
lean_object* v___x_193_; 
v___x_193_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_x_167_, v_a_171_, v_a_179_);
if (lean_obj_tag(v___x_193_) == 0)
{
lean_object* v_a_194_; lean_object* v___x_195_; 
v_a_194_ = lean_ctor_get(v___x_193_, 0);
lean_inc(v_a_194_);
lean_dec_ref(v___x_193_);
lean_inc_ref(v_c_u2081_168_);
v___x_195_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_u2081_168_, v_a_171_, v_a_179_);
if (lean_obj_tag(v___x_195_) == 0)
{
lean_object* v_a_196_; lean_object* v___x_197_; 
v_a_196_ = lean_ctor_get(v___x_195_, 0);
lean_inc(v_a_196_);
lean_dec_ref(v___x_195_);
lean_inc_ref(v_c_u2082_170_);
v___x_197_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2082_170_, v_a_171_, v_a_179_);
if (lean_obj_tag(v___x_197_) == 0)
{
lean_object* v_a_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v_a_198_ = lean_ctor_get(v___x_197_, 0);
lean_inc(v_a_198_);
lean_dec_ref(v___x_197_);
v___x_199_ = l_Lean_MessageData_ofExpr(v_a_194_);
v___x_200_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5);
v___x_201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_199_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
v___x_202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
lean_ctor_set(v___x_202_, 1, v_a_196_);
v___x_203_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_203_, 0, v___x_202_);
lean_ctor_set(v___x_203_, 1, v___x_200_);
v___x_204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
lean_ctor_set(v___x_204_, 1, v_a_198_);
v___x_205_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1___redArg(v_cls_189_, v___x_204_, v_a_177_, v_a_178_, v_a_179_, v_a_180_);
if (lean_obj_tag(v___x_205_) == 0)
{
lean_dec_ref(v___x_205_);
v___y_183_ = v___y_188_;
goto v___jp_182_;
}
else
{
lean_object* v_a_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_213_; 
lean_dec_ref(v___y_188_);
lean_dec_ref(v_c_u2082_170_);
lean_dec_ref(v_c_u2081_168_);
lean_dec(v_x_167_);
v_a_206_ = lean_ctor_get(v___x_205_, 0);
v_isSharedCheck_213_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_213_ == 0)
{
v___x_208_ = v___x_205_;
v_isShared_209_ = v_isSharedCheck_213_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_a_206_);
lean_dec(v___x_205_);
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
lean_dec(v_a_196_);
lean_dec(v_a_194_);
lean_dec_ref(v___y_188_);
lean_dec_ref(v_c_u2082_170_);
lean_dec_ref(v_c_u2081_168_);
lean_dec(v_x_167_);
v_a_214_ = lean_ctor_get(v___x_197_, 0);
v_isSharedCheck_221_ = !lean_is_exclusive(v___x_197_);
if (v_isSharedCheck_221_ == 0)
{
v___x_216_ = v___x_197_;
v_isShared_217_ = v_isSharedCheck_221_;
goto v_resetjp_215_;
}
else
{
lean_inc(v_a_214_);
lean_dec(v___x_197_);
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
lean_dec(v_a_194_);
lean_dec_ref(v___y_188_);
lean_dec_ref(v_c_u2082_170_);
lean_dec_ref(v_c_u2081_168_);
lean_dec(v_x_167_);
v_a_222_ = lean_ctor_get(v___x_195_, 0);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_195_);
if (v_isSharedCheck_229_ == 0)
{
v___x_224_ = v___x_195_;
v_isShared_225_ = v_isSharedCheck_229_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_a_222_);
lean_dec(v___x_195_);
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
else
{
lean_object* v_a_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_237_; 
lean_dec_ref(v___y_188_);
lean_dec_ref(v_c_u2082_170_);
lean_dec_ref(v_c_u2081_168_);
lean_dec(v_x_167_);
v_a_230_ = lean_ctor_get(v___x_193_, 0);
v_isSharedCheck_237_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_237_ == 0)
{
v___x_232_ = v___x_193_;
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_a_230_);
lean_dec(v___x_193_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_237_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_235_; 
if (v_isShared_233_ == 0)
{
v___x_235_ = v___x_232_;
goto v_reusejp_234_;
}
else
{
lean_object* v_reuseFailAlloc_236_; 
v_reuseFailAlloc_236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_236_, 0, v_a_230_);
v___x_235_ = v_reuseFailAlloc_236_;
goto v_reusejp_234_;
}
v_reusejp_234_:
{
return v___x_235_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___boxed(lean_object* v_a_250_, lean_object* v_x_251_, lean_object* v_c_u2081_252_, lean_object* v_b_253_, lean_object* v_c_u2082_254_, lean_object* v_a_255_, lean_object* v_a_256_, lean_object* v_a_257_, lean_object* v_a_258_, lean_object* v_a_259_, lean_object* v_a_260_, lean_object* v_a_261_, lean_object* v_a_262_, lean_object* v_a_263_, lean_object* v_a_264_, lean_object* v_a_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq(v_a_250_, v_x_251_, v_c_u2081_252_, v_b_253_, v_c_u2082_254_, v_a_255_, v_a_256_, v_a_257_, v_a_258_, v_a_259_, v_a_260_, v_a_261_, v_a_262_, v_a_263_, v_a_264_);
lean_dec(v_a_264_);
lean_dec_ref(v_a_263_);
lean_dec(v_a_262_);
lean_dec_ref(v_a_261_);
lean_dec(v_a_260_);
lean_dec_ref(v_a_259_);
lean_dec(v_a_258_);
lean_dec_ref(v_a_257_);
lean_dec(v_a_256_);
lean_dec(v_a_255_);
lean_dec(v_b_253_);
lean_dec(v_a_250_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1(lean_object* v_cls_267_, lean_object* v_msg_268_, lean_object* v___y_269_, lean_object* v___y_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1___redArg(v_cls_267_, v_msg_268_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1___boxed(lean_object* v_cls_281_, lean_object* v_msg_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1(v_cls_281_, v_msg_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
lean_dec(v___y_284_);
lean_dec(v___y_283_);
return v_res_294_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_300_ = l_Lean_maxRecDepthErrorMessage;
v___x_301_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
return v___x_301_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__3);
v___x_303_ = l_Lean_MessageData_ofFormat(v___x_302_);
return v___x_303_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v___x_304_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__4);
v___x_305_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__2));
v___x_306_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
lean_ctor_set(v___x_306_, 1, v___x_304_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg(lean_object* v_ref_307_){
_start:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v___x_309_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__5);
v___x_310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_310_, 0, v_ref_307_);
lean_ctor_set(v___x_310_, 1, v___x_309_);
v___x_311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
return v___x_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___boxed(lean_object* v_ref_312_, lean_object* v___y_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg(v_ref_312_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0(lean_object* v_00_u03b1_315_, lean_object* v_ref_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg(v_ref_316_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___boxed(lean_object* v_00_u03b1_329_, lean_object* v_ref_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0(v_00_u03b1_329_, v_ref_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
lean_dec(v___y_332_);
lean_dec(v___y_331_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts(lean_object* v_c_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_, lean_object* v_a_350_, lean_object* v_a_351_, lean_object* v_a_352_, lean_object* v_a_353_){
_start:
{
lean_object* v_fileName_355_; lean_object* v_fileMap_356_; lean_object* v_options_357_; lean_object* v_currRecDepth_358_; lean_object* v_maxRecDepth_359_; lean_object* v_ref_360_; lean_object* v_currNamespace_361_; lean_object* v_openDecls_362_; lean_object* v_initHeartbeats_363_; lean_object* v_maxHeartbeats_364_; lean_object* v_quotContext_365_; lean_object* v_currMacroScope_366_; uint8_t v_diag_367_; lean_object* v_cancelTk_x3f_368_; uint8_t v_suppressElabErrors_369_; lean_object* v_inheritedTraceOptions_370_; uint8_t v___x_371_; 
v_fileName_355_ = lean_ctor_get(v_a_352_, 0);
lean_inc_ref(v_fileName_355_);
v_fileMap_356_ = lean_ctor_get(v_a_352_, 1);
lean_inc_ref(v_fileMap_356_);
v_options_357_ = lean_ctor_get(v_a_352_, 2);
lean_inc_ref(v_options_357_);
v_currRecDepth_358_ = lean_ctor_get(v_a_352_, 3);
lean_inc(v_currRecDepth_358_);
v_maxRecDepth_359_ = lean_ctor_get(v_a_352_, 4);
lean_inc(v_maxRecDepth_359_);
v_ref_360_ = lean_ctor_get(v_a_352_, 5);
lean_inc(v_ref_360_);
v_currNamespace_361_ = lean_ctor_get(v_a_352_, 6);
lean_inc(v_currNamespace_361_);
v_openDecls_362_ = lean_ctor_get(v_a_352_, 7);
lean_inc(v_openDecls_362_);
v_initHeartbeats_363_ = lean_ctor_get(v_a_352_, 8);
lean_inc(v_initHeartbeats_363_);
v_maxHeartbeats_364_ = lean_ctor_get(v_a_352_, 9);
lean_inc(v_maxHeartbeats_364_);
v_quotContext_365_ = lean_ctor_get(v_a_352_, 10);
lean_inc(v_quotContext_365_);
v_currMacroScope_366_ = lean_ctor_get(v_a_352_, 11);
lean_inc(v_currMacroScope_366_);
v_diag_367_ = lean_ctor_get_uint8(v_a_352_, sizeof(void*)*14);
v_cancelTk_x3f_368_ = lean_ctor_get(v_a_352_, 12);
lean_inc(v_cancelTk_x3f_368_);
v_suppressElabErrors_369_ = lean_ctor_get_uint8(v_a_352_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_370_ = lean_ctor_get(v_a_352_, 13);
lean_inc_ref(v_inheritedTraceOptions_370_);
lean_dec_ref(v_a_352_);
v___x_371_ = lean_nat_dec_eq(v_currRecDepth_358_, v_maxRecDepth_359_);
if (v___x_371_ == 0)
{
lean_object* v_p_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v_p_372_ = lean_ctor_get(v_c_343_, 0);
v___x_373_ = lean_unsigned_to_nat(1u);
v___x_374_ = lean_nat_add(v_currRecDepth_358_, v___x_373_);
lean_dec(v_currRecDepth_358_);
v___x_375_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_375_, 0, v_fileName_355_);
lean_ctor_set(v___x_375_, 1, v_fileMap_356_);
lean_ctor_set(v___x_375_, 2, v_options_357_);
lean_ctor_set(v___x_375_, 3, v___x_374_);
lean_ctor_set(v___x_375_, 4, v_maxRecDepth_359_);
lean_ctor_set(v___x_375_, 5, v_ref_360_);
lean_ctor_set(v___x_375_, 6, v_currNamespace_361_);
lean_ctor_set(v___x_375_, 7, v_openDecls_362_);
lean_ctor_set(v___x_375_, 8, v_initHeartbeats_363_);
lean_ctor_set(v___x_375_, 9, v_maxHeartbeats_364_);
lean_ctor_set(v___x_375_, 10, v_quotContext_365_);
lean_ctor_set(v___x_375_, 11, v_currMacroScope_366_);
lean_ctor_set(v___x_375_, 12, v_cancelTk_x3f_368_);
lean_ctor_set(v___x_375_, 13, v_inheritedTraceOptions_370_);
lean_ctor_set_uint8(v___x_375_, sizeof(void*)*14, v_diag_367_);
lean_ctor_set_uint8(v___x_375_, sizeof(void*)*14 + 1, v_suppressElabErrors_369_);
lean_inc_ref(v_p_372_);
v___x_376_ = l_Int_Linear_Poly_findVarToSubst___redArg(v_p_372_, v_a_344_, v___x_375_);
if (lean_obj_tag(v___x_376_) == 0)
{
lean_object* v_a_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_394_; 
v_a_377_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_394_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_394_ == 0)
{
v___x_379_ = v___x_376_;
v_isShared_380_ = v_isSharedCheck_394_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_a_377_);
lean_dec(v___x_376_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_394_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
if (lean_obj_tag(v_a_377_) == 1)
{
lean_object* v_val_381_; lean_object* v_snd_382_; lean_object* v_snd_383_; lean_object* v_fst_384_; lean_object* v_fst_385_; lean_object* v_p_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
lean_del_object(v___x_379_);
v_val_381_ = lean_ctor_get(v_a_377_, 0);
lean_inc(v_val_381_);
lean_dec_ref(v_a_377_);
v_snd_382_ = lean_ctor_get(v_val_381_, 1);
lean_inc(v_snd_382_);
v_snd_383_ = lean_ctor_get(v_snd_382_, 1);
lean_inc(v_snd_383_);
v_fst_384_ = lean_ctor_get(v_val_381_, 0);
lean_inc(v_fst_384_);
lean_dec(v_val_381_);
v_fst_385_ = lean_ctor_get(v_snd_382_, 0);
lean_inc(v_fst_385_);
lean_dec(v_snd_382_);
v_p_386_ = lean_ctor_get(v_snd_383_, 0);
v___x_387_ = l_Int_Linear_Poly_coeff(v_p_386_, v_fst_385_);
v___x_388_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq(v___x_387_, v_fst_385_, v_snd_383_, v_fst_384_, v_c_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v___x_375_, v_a_353_);
lean_dec(v_fst_384_);
lean_dec(v___x_387_);
if (lean_obj_tag(v___x_388_) == 0)
{
lean_object* v_a_389_; 
v_a_389_ = lean_ctor_get(v___x_388_, 0);
lean_inc(v_a_389_);
lean_dec_ref(v___x_388_);
v_c_343_ = v_a_389_;
v_a_352_ = v___x_375_;
goto _start;
}
else
{
lean_dec_ref(v___x_375_);
return v___x_388_;
}
}
else
{
lean_object* v___x_392_; 
lean_dec(v_a_377_);
lean_dec_ref(v___x_375_);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 0, v_c_343_);
v___x_392_ = v___x_379_;
goto v_reusejp_391_;
}
else
{
lean_object* v_reuseFailAlloc_393_; 
v_reuseFailAlloc_393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_393_, 0, v_c_343_);
v___x_392_ = v_reuseFailAlloc_393_;
goto v_reusejp_391_;
}
v_reusejp_391_:
{
return v___x_392_;
}
}
}
}
else
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_402_; 
lean_dec_ref(v___x_375_);
lean_dec_ref(v_c_343_);
v_a_395_ = lean_ctor_get(v___x_376_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_376_);
if (v_isSharedCheck_402_ == 0)
{
v___x_397_ = v___x_376_;
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_376_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_400_; 
if (v_isShared_398_ == 0)
{
v___x_400_ = v___x_397_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_a_395_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
}
else
{
lean_object* v___x_403_; 
lean_dec_ref(v_inheritedTraceOptions_370_);
lean_dec(v_cancelTk_x3f_368_);
lean_dec(v_currMacroScope_366_);
lean_dec(v_quotContext_365_);
lean_dec(v_maxHeartbeats_364_);
lean_dec(v_initHeartbeats_363_);
lean_dec(v_openDecls_362_);
lean_dec(v_currNamespace_361_);
lean_dec(v_maxRecDepth_359_);
lean_dec(v_currRecDepth_358_);
lean_dec_ref(v_options_357_);
lean_dec_ref(v_fileMap_356_);
lean_dec_ref(v_fileName_355_);
lean_dec_ref(v_c_343_);
v___x_403_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg(v_ref_360_);
return v___x_403_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts___boxed(lean_object* v_c_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_, lean_object* v_a_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts(v_c_404_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, v_a_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_);
lean_dec(v_a_414_);
lean_dec(v_a_412_);
lean_dec_ref(v_a_411_);
lean_dec(v_a_410_);
lean_dec_ref(v_a_409_);
lean_dec(v_a_408_);
lean_dec_ref(v_a_407_);
lean_dec(v_a_406_);
lean_dec(v_a_405_);
return v_res_416_;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_Poly_isNegEq(lean_object* v_p_u2081_417_, lean_object* v_p_u2082_418_){
_start:
{
if (lean_obj_tag(v_p_u2081_417_) == 0)
{
if (lean_obj_tag(v_p_u2082_418_) == 0)
{
lean_object* v_k_419_; lean_object* v_k_420_; lean_object* v___x_421_; uint8_t v___x_422_; 
v_k_419_ = lean_ctor_get(v_p_u2081_417_, 0);
v_k_420_ = lean_ctor_get(v_p_u2082_418_, 0);
v___x_421_ = lean_int_neg(v_k_420_);
v___x_422_ = lean_int_dec_eq(v_k_419_, v___x_421_);
lean_dec(v___x_421_);
return v___x_422_;
}
else
{
uint8_t v___x_423_; 
v___x_423_ = 0;
return v___x_423_;
}
}
else
{
if (lean_obj_tag(v_p_u2082_418_) == 1)
{
lean_object* v_k_424_; lean_object* v_v_425_; lean_object* v_p_426_; lean_object* v_k_427_; lean_object* v_v_428_; lean_object* v_p_429_; uint8_t v___y_431_; lean_object* v___x_433_; uint8_t v___x_434_; 
v_k_424_ = lean_ctor_get(v_p_u2081_417_, 0);
v_v_425_ = lean_ctor_get(v_p_u2081_417_, 1);
v_p_426_ = lean_ctor_get(v_p_u2081_417_, 2);
v_k_427_ = lean_ctor_get(v_p_u2082_418_, 0);
v_v_428_ = lean_ctor_get(v_p_u2082_418_, 1);
v_p_429_ = lean_ctor_get(v_p_u2082_418_, 2);
v___x_433_ = lean_int_neg(v_k_427_);
v___x_434_ = lean_int_dec_eq(v_k_424_, v___x_433_);
lean_dec(v___x_433_);
if (v___x_434_ == 0)
{
v___y_431_ = v___x_434_;
goto v___jp_430_;
}
else
{
uint8_t v___x_435_; 
v___x_435_ = lean_nat_dec_eq(v_v_425_, v_v_428_);
v___y_431_ = v___x_435_;
goto v___jp_430_;
}
v___jp_430_:
{
if (v___y_431_ == 0)
{
return v___y_431_;
}
else
{
v_p_u2081_417_ = v_p_426_;
v_p_u2082_418_ = v_p_429_;
goto _start;
}
}
}
else
{
uint8_t v___x_436_; 
v___x_436_ = 0;
return v___x_436_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isNegEq___boxed(lean_object* v_p_u2081_437_, lean_object* v_p_u2082_438_){
_start:
{
uint8_t v_res_439_; lean_object* v_r_440_; 
v_res_439_ = l_Int_Linear_Poly_isNegEq(v_p_u2081_437_, v_p_u2082_438_);
lean_dec_ref(v_p_u2082_438_);
lean_dec_ref(v_p_u2081_437_);
v_r_440_ = lean_box(v_res_439_);
return v_r_440_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(lean_object* v___x_441_, lean_object* v_as_442_, size_t v_i_443_, size_t v_stop_444_, lean_object* v_b_445_){
_start:
{
lean_object* v___y_447_; uint8_t v___x_451_; 
v___x_451_ = lean_usize_dec_eq(v_i_443_, v_stop_444_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; lean_object* v_p_453_; uint8_t v___x_454_; 
v___x_452_ = lean_array_uget_borrowed(v_as_442_, v_i_443_);
v_p_453_ = lean_ctor_get(v___x_452_, 0);
v___x_454_ = l_Int_Linear_instBEqPoly_beq(v_p_453_, v___x_441_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; 
lean_inc(v___x_452_);
v___x_455_ = l_Lean_PersistentArray_push___redArg(v_b_445_, v___x_452_);
v___y_447_ = v___x_455_;
goto v___jp_446_;
}
else
{
v___y_447_ = v_b_445_;
goto v___jp_446_;
}
}
else
{
return v_b_445_;
}
v___jp_446_:
{
size_t v___x_448_; size_t v___x_449_; 
v___x_448_ = ((size_t)1ULL);
v___x_449_ = lean_usize_add(v_i_443_, v___x_448_);
v_i_443_ = v___x_449_;
v_b_445_ = v___y_447_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1___boxed(lean_object* v___x_456_, lean_object* v_as_457_, lean_object* v_i_458_, lean_object* v_stop_459_, lean_object* v_b_460_){
_start:
{
size_t v_i_boxed_461_; size_t v_stop_boxed_462_; lean_object* v_res_463_; 
v_i_boxed_461_ = lean_unbox_usize(v_i_458_);
lean_dec(v_i_458_);
v_stop_boxed_462_ = lean_unbox_usize(v_stop_459_);
lean_dec(v_stop_459_);
v_res_463_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_456_, v_as_457_, v_i_boxed_461_, v_stop_boxed_462_, v_b_460_);
lean_dec_ref(v_as_457_);
lean_dec_ref(v___x_456_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2(lean_object* v___x_464_, lean_object* v_x_465_, lean_object* v_x_466_){
_start:
{
if (lean_obj_tag(v_x_465_) == 0)
{
lean_object* v_cs_467_; lean_object* v___x_468_; lean_object* v___x_469_; uint8_t v___x_470_; 
v_cs_467_ = lean_ctor_get(v_x_465_, 0);
v___x_468_ = lean_unsigned_to_nat(0u);
v___x_469_ = lean_array_get_size(v_cs_467_);
v___x_470_ = lean_nat_dec_lt(v___x_468_, v___x_469_);
if (v___x_470_ == 0)
{
return v_x_466_;
}
else
{
uint8_t v___x_471_; 
v___x_471_ = lean_nat_dec_le(v___x_469_, v___x_469_);
if (v___x_471_ == 0)
{
if (v___x_470_ == 0)
{
return v_x_466_;
}
else
{
size_t v___x_472_; size_t v___x_473_; lean_object* v___x_474_; 
v___x_472_ = ((size_t)0ULL);
v___x_473_ = lean_usize_of_nat(v___x_469_);
v___x_474_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v___x_464_, v_cs_467_, v___x_472_, v___x_473_, v_x_466_);
return v___x_474_;
}
}
else
{
size_t v___x_475_; size_t v___x_476_; lean_object* v___x_477_; 
v___x_475_ = ((size_t)0ULL);
v___x_476_ = lean_usize_of_nat(v___x_469_);
v___x_477_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v___x_464_, v_cs_467_, v___x_475_, v___x_476_, v_x_466_);
return v___x_477_;
}
}
}
else
{
lean_object* v_vs_478_; lean_object* v___x_479_; lean_object* v___x_480_; uint8_t v___x_481_; 
v_vs_478_ = lean_ctor_get(v_x_465_, 0);
v___x_479_ = lean_unsigned_to_nat(0u);
v___x_480_ = lean_array_get_size(v_vs_478_);
v___x_481_ = lean_nat_dec_lt(v___x_479_, v___x_480_);
if (v___x_481_ == 0)
{
return v_x_466_;
}
else
{
uint8_t v___x_482_; 
v___x_482_ = lean_nat_dec_le(v___x_480_, v___x_480_);
if (v___x_482_ == 0)
{
if (v___x_481_ == 0)
{
return v_x_466_;
}
else
{
size_t v___x_483_; size_t v___x_484_; lean_object* v___x_485_; 
v___x_483_ = ((size_t)0ULL);
v___x_484_ = lean_usize_of_nat(v___x_480_);
v___x_485_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_464_, v_vs_478_, v___x_483_, v___x_484_, v_x_466_);
return v___x_485_;
}
}
else
{
size_t v___x_486_; size_t v___x_487_; lean_object* v___x_488_; 
v___x_486_ = ((size_t)0ULL);
v___x_487_ = lean_usize_of_nat(v___x_480_);
v___x_488_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_464_, v_vs_478_, v___x_486_, v___x_487_, v_x_466_);
return v___x_488_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(lean_object* v___x_489_, lean_object* v_as_490_, size_t v_i_491_, size_t v_stop_492_, lean_object* v_b_493_){
_start:
{
uint8_t v___x_494_; 
v___x_494_ = lean_usize_dec_eq(v_i_491_, v_stop_492_);
if (v___x_494_ == 0)
{
lean_object* v___x_495_; lean_object* v___x_496_; size_t v___x_497_; size_t v___x_498_; 
v___x_495_ = lean_array_uget_borrowed(v_as_490_, v_i_491_);
v___x_496_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2(v___x_489_, v___x_495_, v_b_493_);
v___x_497_ = ((size_t)1ULL);
v___x_498_ = lean_usize_add(v_i_491_, v___x_497_);
v_i_491_ = v___x_498_;
v_b_493_ = v___x_496_;
goto _start;
}
else
{
return v_b_493_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1___boxed(lean_object* v___x_500_, lean_object* v_as_501_, lean_object* v_i_502_, lean_object* v_stop_503_, lean_object* v_b_504_){
_start:
{
size_t v_i_boxed_505_; size_t v_stop_boxed_506_; lean_object* v_res_507_; 
v_i_boxed_505_ = lean_unbox_usize(v_i_502_);
lean_dec(v_i_502_);
v_stop_boxed_506_ = lean_unbox_usize(v_stop_503_);
lean_dec(v_stop_503_);
v_res_507_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v___x_500_, v_as_501_, v_i_boxed_505_, v_stop_boxed_506_, v_b_504_);
lean_dec_ref(v_as_501_);
lean_dec_ref(v___x_500_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2___boxed(lean_object* v___x_508_, lean_object* v_x_509_, lean_object* v_x_510_){
_start:
{
lean_object* v_res_511_; 
v_res_511_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2(v___x_508_, v_x_509_, v_x_510_);
lean_dec_ref(v_x_509_);
lean_dec_ref(v___x_508_);
return v_res_511_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_512_; 
v___x_512_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(lean_object* v___x_513_, lean_object* v_x_514_, size_t v_x_515_, size_t v_x_516_, lean_object* v_x_517_){
_start:
{
if (lean_obj_tag(v_x_514_) == 0)
{
lean_object* v_cs_518_; lean_object* v___x_519_; size_t v___x_520_; lean_object* v_j_521_; lean_object* v___x_522_; size_t v___x_523_; size_t v___x_524_; size_t v___x_525_; size_t v___x_526_; size_t v___x_527_; size_t v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; uint8_t v___x_533_; 
v_cs_518_ = lean_ctor_get(v_x_514_, 0);
v___x_519_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0);
v___x_520_ = lean_usize_shift_right(v_x_515_, v_x_516_);
v_j_521_ = lean_usize_to_nat(v___x_520_);
v___x_522_ = lean_array_get_borrowed(v___x_519_, v_cs_518_, v_j_521_);
v___x_523_ = ((size_t)1ULL);
v___x_524_ = lean_usize_shift_left(v___x_523_, v_x_516_);
v___x_525_ = lean_usize_sub(v___x_524_, v___x_523_);
v___x_526_ = lean_usize_land(v_x_515_, v___x_525_);
v___x_527_ = ((size_t)5ULL);
v___x_528_ = lean_usize_sub(v_x_516_, v___x_527_);
v___x_529_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(v___x_513_, v___x_522_, v___x_526_, v___x_528_, v_x_517_);
v___x_530_ = lean_unsigned_to_nat(1u);
v___x_531_ = lean_nat_add(v_j_521_, v___x_530_);
lean_dec(v_j_521_);
v___x_532_ = lean_array_get_size(v_cs_518_);
v___x_533_ = lean_nat_dec_lt(v___x_531_, v___x_532_);
if (v___x_533_ == 0)
{
lean_dec(v___x_531_);
return v___x_529_;
}
else
{
uint8_t v___x_534_; 
v___x_534_ = lean_nat_dec_le(v___x_532_, v___x_532_);
if (v___x_534_ == 0)
{
if (v___x_533_ == 0)
{
lean_dec(v___x_531_);
return v___x_529_;
}
else
{
size_t v___x_535_; size_t v___x_536_; lean_object* v___x_537_; 
v___x_535_ = lean_usize_of_nat(v___x_531_);
lean_dec(v___x_531_);
v___x_536_ = lean_usize_of_nat(v___x_532_);
v___x_537_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v___x_513_, v_cs_518_, v___x_535_, v___x_536_, v___x_529_);
return v___x_537_;
}
}
else
{
size_t v___x_538_; size_t v___x_539_; lean_object* v___x_540_; 
v___x_538_ = lean_usize_of_nat(v___x_531_);
lean_dec(v___x_531_);
v___x_539_ = lean_usize_of_nat(v___x_532_);
v___x_540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v___x_513_, v_cs_518_, v___x_538_, v___x_539_, v___x_529_);
return v___x_540_;
}
}
}
else
{
lean_object* v_vs_541_; lean_object* v___x_542_; lean_object* v___x_543_; uint8_t v___x_544_; 
v_vs_541_ = lean_ctor_get(v_x_514_, 0);
v___x_542_ = lean_usize_to_nat(v_x_515_);
v___x_543_ = lean_array_get_size(v_vs_541_);
v___x_544_ = lean_nat_dec_lt(v___x_542_, v___x_543_);
if (v___x_544_ == 0)
{
lean_dec(v___x_542_);
return v_x_517_;
}
else
{
uint8_t v___x_545_; 
v___x_545_ = lean_nat_dec_le(v___x_543_, v___x_543_);
if (v___x_545_ == 0)
{
if (v___x_544_ == 0)
{
lean_dec(v___x_542_);
return v_x_517_;
}
else
{
size_t v___x_546_; size_t v___x_547_; lean_object* v___x_548_; 
v___x_546_ = lean_usize_of_nat(v___x_542_);
lean_dec(v___x_542_);
v___x_547_ = lean_usize_of_nat(v___x_543_);
v___x_548_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_513_, v_vs_541_, v___x_546_, v___x_547_, v_x_517_);
return v___x_548_;
}
}
else
{
size_t v___x_549_; size_t v___x_550_; lean_object* v___x_551_; 
v___x_549_ = lean_usize_of_nat(v___x_542_);
lean_dec(v___x_542_);
v___x_550_ = lean_usize_of_nat(v___x_543_);
v___x_551_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_513_, v_vs_541_, v___x_549_, v___x_550_, v_x_517_);
return v___x_551_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___boxed(lean_object* v___x_552_, lean_object* v_x_553_, lean_object* v_x_554_, lean_object* v_x_555_, lean_object* v_x_556_){
_start:
{
size_t v_x_2076__boxed_557_; size_t v_x_2077__boxed_558_; lean_object* v_res_559_; 
v_x_2076__boxed_557_ = lean_unbox_usize(v_x_554_);
lean_dec(v_x_554_);
v_x_2077__boxed_558_ = lean_unbox_usize(v_x_555_);
lean_dec(v_x_555_);
v_res_559_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(v___x_552_, v_x_553_, v_x_2076__boxed_557_, v_x_2077__boxed_558_, v_x_556_);
lean_dec_ref(v_x_553_);
lean_dec_ref(v___x_552_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(lean_object* v___x_560_, lean_object* v_t_561_, lean_object* v_init_562_, lean_object* v_start_563_){
_start:
{
lean_object* v___x_564_; uint8_t v___x_565_; 
v___x_564_ = lean_unsigned_to_nat(0u);
v___x_565_ = lean_nat_dec_eq(v_start_563_, v___x_564_);
if (v___x_565_ == 0)
{
lean_object* v_root_566_; lean_object* v_tail_567_; size_t v_shift_568_; lean_object* v_tailOff_569_; uint8_t v___x_570_; 
v_root_566_ = lean_ctor_get(v_t_561_, 0);
v_tail_567_ = lean_ctor_get(v_t_561_, 1);
v_shift_568_ = lean_ctor_get_usize(v_t_561_, 4);
v_tailOff_569_ = lean_ctor_get(v_t_561_, 3);
v___x_570_ = lean_nat_dec_le(v_tailOff_569_, v_start_563_);
if (v___x_570_ == 0)
{
size_t v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; uint8_t v___x_574_; 
v___x_571_ = lean_usize_of_nat(v_start_563_);
v___x_572_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(v___x_560_, v_root_566_, v___x_571_, v_shift_568_, v_init_562_);
v___x_573_ = lean_array_get_size(v_tail_567_);
v___x_574_ = lean_nat_dec_lt(v___x_564_, v___x_573_);
if (v___x_574_ == 0)
{
return v___x_572_;
}
else
{
uint8_t v___x_575_; 
v___x_575_ = lean_nat_dec_le(v___x_573_, v___x_573_);
if (v___x_575_ == 0)
{
if (v___x_574_ == 0)
{
return v___x_572_;
}
else
{
size_t v___x_576_; size_t v___x_577_; lean_object* v___x_578_; 
v___x_576_ = ((size_t)0ULL);
v___x_577_ = lean_usize_of_nat(v___x_573_);
v___x_578_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_560_, v_tail_567_, v___x_576_, v___x_577_, v___x_572_);
return v___x_578_;
}
}
else
{
size_t v___x_579_; size_t v___x_580_; lean_object* v___x_581_; 
v___x_579_ = ((size_t)0ULL);
v___x_580_ = lean_usize_of_nat(v___x_573_);
v___x_581_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_560_, v_tail_567_, v___x_579_, v___x_580_, v___x_572_);
return v___x_581_;
}
}
}
else
{
lean_object* v___x_582_; lean_object* v___x_583_; uint8_t v___x_584_; 
v___x_582_ = lean_nat_sub(v_start_563_, v_tailOff_569_);
v___x_583_ = lean_array_get_size(v_tail_567_);
v___x_584_ = lean_nat_dec_lt(v___x_582_, v___x_583_);
if (v___x_584_ == 0)
{
lean_dec(v___x_582_);
return v_init_562_;
}
else
{
uint8_t v___x_585_; 
v___x_585_ = lean_nat_dec_le(v___x_583_, v___x_583_);
if (v___x_585_ == 0)
{
if (v___x_584_ == 0)
{
lean_dec(v___x_582_);
return v_init_562_;
}
else
{
size_t v___x_586_; size_t v___x_587_; lean_object* v___x_588_; 
v___x_586_ = lean_usize_of_nat(v___x_582_);
lean_dec(v___x_582_);
v___x_587_ = lean_usize_of_nat(v___x_583_);
v___x_588_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_560_, v_tail_567_, v___x_586_, v___x_587_, v_init_562_);
return v___x_588_;
}
}
else
{
size_t v___x_589_; size_t v___x_590_; lean_object* v___x_591_; 
v___x_589_ = lean_usize_of_nat(v___x_582_);
lean_dec(v___x_582_);
v___x_590_ = lean_usize_of_nat(v___x_583_);
v___x_591_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_560_, v_tail_567_, v___x_589_, v___x_590_, v_init_562_);
return v___x_591_;
}
}
}
}
else
{
lean_object* v_root_592_; lean_object* v_tail_593_; lean_object* v___x_594_; lean_object* v___x_595_; uint8_t v___x_596_; 
v_root_592_ = lean_ctor_get(v_t_561_, 0);
v_tail_593_ = lean_ctor_get(v_t_561_, 1);
v___x_594_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2(v___x_560_, v_root_592_, v_init_562_);
v___x_595_ = lean_array_get_size(v_tail_593_);
v___x_596_ = lean_nat_dec_lt(v___x_564_, v___x_595_);
if (v___x_596_ == 0)
{
return v___x_594_;
}
else
{
uint8_t v___x_597_; 
v___x_597_ = lean_nat_dec_le(v___x_595_, v___x_595_);
if (v___x_597_ == 0)
{
if (v___x_596_ == 0)
{
return v___x_594_;
}
else
{
size_t v___x_598_; size_t v___x_599_; lean_object* v___x_600_; 
v___x_598_ = ((size_t)0ULL);
v___x_599_ = lean_usize_of_nat(v___x_595_);
v___x_600_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_560_, v_tail_593_, v___x_598_, v___x_599_, v___x_594_);
return v___x_600_;
}
}
else
{
size_t v___x_601_; size_t v___x_602_; lean_object* v___x_603_; 
v___x_601_ = ((size_t)0ULL);
v___x_602_ = lean_usize_of_nat(v___x_595_);
v___x_603_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_560_, v_tail_593_, v___x_601_, v___x_602_, v___x_594_);
return v___x_603_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0___boxed(lean_object* v___x_604_, lean_object* v_t_605_, lean_object* v_init_606_, lean_object* v_start_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(v___x_604_, v_t_605_, v_init_606_, v_start_607_);
lean_dec(v_start_607_);
lean_dec_ref(v_t_605_);
lean_dec_ref(v___x_604_);
return v_res_608_;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_609_ = lean_unsigned_to_nat(32u);
v___x_610_ = lean_mk_empty_array_with_capacity(v___x_609_);
v___x_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_611_, 0, v___x_610_);
return v___x_611_;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_612_ = ((size_t)5ULL);
v___x_613_ = lean_unsigned_to_nat(0u);
v___x_614_ = lean_unsigned_to_nat(32u);
v___x_615_ = lean_mk_empty_array_with_capacity(v___x_614_);
v___x_616_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___redArg___closed__0, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___redArg___closed__0);
v___x_617_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_617_, 0, v___x_616_);
lean_ctor_set(v___x_617_, 1, v___x_615_);
lean_ctor_set(v___x_617_, 2, v___x_613_);
lean_ctor_set(v___x_617_, 3, v___x_613_);
lean_ctor_set_usize(v___x_617_, 4, v___x_612_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___redArg(lean_object* v___x_618_, lean_object* v_x_619_, size_t v_x_620_, size_t v_x_621_){
_start:
{
if (lean_obj_tag(v_x_619_) == 0)
{
lean_object* v_cs_622_; size_t v_j_623_; lean_object* v___x_624_; lean_object* v___x_625_; uint8_t v___x_626_; 
v_cs_622_ = lean_ctor_get(v_x_619_, 0);
v_j_623_ = lean_usize_shift_right(v_x_620_, v_x_621_);
v___x_624_ = lean_usize_to_nat(v_j_623_);
v___x_625_ = lean_array_get_size(v_cs_622_);
v___x_626_ = lean_nat_dec_lt(v___x_624_, v___x_625_);
if (v___x_626_ == 0)
{
lean_dec(v___x_624_);
return v_x_619_;
}
else
{
lean_object* v___x_628_; uint8_t v_isShared_629_; uint8_t v_isSharedCheck_644_; 
lean_inc_ref(v_cs_622_);
v_isSharedCheck_644_ = !lean_is_exclusive(v_x_619_);
if (v_isSharedCheck_644_ == 0)
{
lean_object* v_unused_645_; 
v_unused_645_ = lean_ctor_get(v_x_619_, 0);
lean_dec(v_unused_645_);
v___x_628_ = v_x_619_;
v_isShared_629_ = v_isSharedCheck_644_;
goto v_resetjp_627_;
}
else
{
lean_dec(v_x_619_);
v___x_628_ = lean_box(0);
v_isShared_629_ = v_isSharedCheck_644_;
goto v_resetjp_627_;
}
v_resetjp_627_:
{
size_t v___x_630_; size_t v___x_631_; size_t v___x_632_; size_t v_i_633_; size_t v___x_634_; size_t v_shift_635_; lean_object* v_v_636_; lean_object* v___x_637_; lean_object* v_xs_x27_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_642_; 
v___x_630_ = ((size_t)1ULL);
v___x_631_ = lean_usize_shift_left(v___x_630_, v_x_621_);
v___x_632_ = lean_usize_sub(v___x_631_, v___x_630_);
v_i_633_ = lean_usize_land(v_x_620_, v___x_632_);
v___x_634_ = ((size_t)5ULL);
v_shift_635_ = lean_usize_sub(v_x_621_, v___x_634_);
v_v_636_ = lean_array_fget(v_cs_622_, v___x_624_);
v___x_637_ = lean_box(0);
v_xs_x27_638_ = lean_array_fset(v_cs_622_, v___x_624_, v___x_637_);
v___x_639_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___redArg(v___x_618_, v_v_636_, v_i_633_, v_shift_635_);
v___x_640_ = lean_array_fset(v_xs_x27_638_, v___x_624_, v___x_639_);
lean_dec(v___x_624_);
if (v_isShared_629_ == 0)
{
lean_ctor_set(v___x_628_, 0, v___x_640_);
v___x_642_ = v___x_628_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_640_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
else
{
lean_object* v_vs_646_; lean_object* v___x_647_; lean_object* v___x_648_; uint8_t v___x_649_; 
v_vs_646_ = lean_ctor_get(v_x_619_, 0);
v___x_647_ = lean_usize_to_nat(v_x_620_);
v___x_648_ = lean_array_get_size(v_vs_646_);
v___x_649_ = lean_nat_dec_lt(v___x_647_, v___x_648_);
if (v___x_649_ == 0)
{
lean_dec(v___x_647_);
return v_x_619_;
}
else
{
lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_663_; 
lean_inc_ref(v_vs_646_);
v_isSharedCheck_663_ = !lean_is_exclusive(v_x_619_);
if (v_isSharedCheck_663_ == 0)
{
lean_object* v_unused_664_; 
v_unused_664_ = lean_ctor_get(v_x_619_, 0);
lean_dec(v_unused_664_);
v___x_651_ = v_x_619_;
v_isShared_652_ = v_isSharedCheck_663_;
goto v_resetjp_650_;
}
else
{
lean_dec(v_x_619_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_663_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v_v_653_; lean_object* v___x_654_; lean_object* v_xs_x27_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_661_; 
v_v_653_ = lean_array_fget(v_vs_646_, v___x_647_);
v___x_654_ = lean_box(0);
v_xs_x27_655_ = lean_array_fset(v_vs_646_, v___x_647_, v___x_654_);
v___x_656_ = lean_unsigned_to_nat(0u);
v___x_657_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___redArg___closed__1, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___redArg___closed__1);
v___x_658_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(v___x_618_, v_v_653_, v___x_657_, v___x_656_);
lean_dec(v_v_653_);
v___x_659_ = lean_array_fset(v_xs_x27_655_, v___x_647_, v___x_658_);
lean_dec(v___x_647_);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 0, v___x_659_);
v___x_661_ = v___x_651_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_659_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___redArg___boxed(lean_object* v___x_665_, lean_object* v_x_666_, lean_object* v_x_667_, lean_object* v_x_668_){
_start:
{
size_t v_x_2249__boxed_669_; size_t v_x_2250__boxed_670_; lean_object* v_res_671_; 
v_x_2249__boxed_669_ = lean_unbox_usize(v_x_667_);
lean_dec(v_x_667_);
v_x_2250__boxed_670_ = lean_unbox_usize(v_x_668_);
lean_dec(v_x_668_);
v_res_671_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___redArg(v___x_665_, v_x_666_, v_x_2249__boxed_669_, v_x_2250__boxed_670_);
lean_dec_ref(v___x_665_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(lean_object* v___x_672_, lean_object* v_inst_673_, lean_object* v_t_674_, lean_object* v_i_675_){
_start:
{
lean_object* v_root_676_; lean_object* v_tail_677_; lean_object* v_size_678_; size_t v_shift_679_; lean_object* v_tailOff_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_708_; 
v_root_676_ = lean_ctor_get(v_t_674_, 0);
v_tail_677_ = lean_ctor_get(v_t_674_, 1);
v_size_678_ = lean_ctor_get(v_t_674_, 2);
v_shift_679_ = lean_ctor_get_usize(v_t_674_, 4);
v_tailOff_680_ = lean_ctor_get(v_t_674_, 3);
v_isSharedCheck_708_ = !lean_is_exclusive(v_t_674_);
if (v_isSharedCheck_708_ == 0)
{
v___x_682_ = v_t_674_;
v_isShared_683_ = v_isSharedCheck_708_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_tailOff_680_);
lean_inc(v_size_678_);
lean_inc(v_tail_677_);
lean_inc(v_root_676_);
lean_dec(v_t_674_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_708_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
uint8_t v___x_684_; 
v___x_684_ = lean_nat_dec_le(v_tailOff_680_, v_i_675_);
if (v___x_684_ == 0)
{
size_t v___x_685_; lean_object* v___x_686_; lean_object* v___x_688_; 
v___x_685_ = lean_usize_of_nat(v_i_675_);
v___x_686_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___redArg(v___x_672_, v_root_676_, v___x_685_, v_shift_679_);
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 0, v___x_686_);
v___x_688_ = v___x_682_;
goto v_reusejp_687_;
}
else
{
lean_object* v_reuseFailAlloc_689_; 
v_reuseFailAlloc_689_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_689_, 0, v___x_686_);
lean_ctor_set(v_reuseFailAlloc_689_, 1, v_tail_677_);
lean_ctor_set(v_reuseFailAlloc_689_, 2, v_size_678_);
lean_ctor_set(v_reuseFailAlloc_689_, 3, v_tailOff_680_);
lean_ctor_set_usize(v_reuseFailAlloc_689_, 4, v_shift_679_);
v___x_688_ = v_reuseFailAlloc_689_;
goto v_reusejp_687_;
}
v_reusejp_687_:
{
return v___x_688_;
}
}
else
{
lean_object* v___x_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
v___x_690_ = lean_nat_sub(v_i_675_, v_tailOff_680_);
v___x_691_ = lean_array_get_size(v_tail_677_);
v___x_692_ = lean_nat_dec_lt(v___x_690_, v___x_691_);
if (v___x_692_ == 0)
{
lean_object* v___x_694_; 
lean_dec(v___x_690_);
if (v_isShared_683_ == 0)
{
v___x_694_ = v___x_682_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_root_676_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v_tail_677_);
lean_ctor_set(v_reuseFailAlloc_695_, 2, v_size_678_);
lean_ctor_set(v_reuseFailAlloc_695_, 3, v_tailOff_680_);
lean_ctor_set_usize(v_reuseFailAlloc_695_, 4, v_shift_679_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
return v___x_694_;
}
}
else
{
lean_object* v_v_696_; lean_object* v___x_697_; lean_object* v_xs_x27_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_706_; 
v_v_696_ = lean_array_fget(v_tail_677_, v___x_690_);
v___x_697_ = lean_box(0);
v_xs_x27_698_ = lean_array_fset(v_tail_677_, v___x_690_, v___x_697_);
v___x_699_ = lean_unsigned_to_nat(32u);
v___x_700_ = lean_mk_empty_array_with_capacity(v___x_699_);
lean_dec_ref(v___x_700_);
v___x_701_ = lean_unsigned_to_nat(0u);
v___x_702_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___redArg___closed__1, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___redArg___closed__1);
v___x_703_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(v___x_672_, v_v_696_, v___x_702_, v___x_701_);
lean_dec(v_v_696_);
v___x_704_ = lean_array_fset(v_xs_x27_698_, v___x_690_, v___x_703_);
lean_dec(v___x_690_);
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 1, v___x_704_);
v___x_706_ = v___x_682_;
goto v_reusejp_705_;
}
else
{
lean_object* v_reuseFailAlloc_707_; 
v_reuseFailAlloc_707_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_707_, 0, v_root_676_);
lean_ctor_set(v_reuseFailAlloc_707_, 1, v___x_704_);
lean_ctor_set(v_reuseFailAlloc_707_, 2, v_size_678_);
lean_ctor_set(v_reuseFailAlloc_707_, 3, v_tailOff_680_);
lean_ctor_set_usize(v_reuseFailAlloc_707_, 4, v_shift_679_);
v___x_706_ = v_reuseFailAlloc_707_;
goto v_reusejp_705_;
}
v_reusejp_705_:
{
return v___x_706_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1___boxed(lean_object* v___x_709_, lean_object* v_inst_710_, lean_object* v_t_711_, lean_object* v_i_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(v___x_709_, v_inst_710_, v_t_711_, v_i_712_);
lean_dec(v_i_712_);
lean_dec_ref(v_inst_710_);
lean_dec_ref(v___x_709_);
return v_res_713_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0(lean_object* v_p_715_, lean_object* v_v_716_, lean_object* v_s_717_){
_start:
{
lean_object* v_vars_718_; lean_object* v_varMap_719_; lean_object* v_vars_x27_720_; lean_object* v_varMap_x27_721_; lean_object* v_natToIntMap_722_; lean_object* v_natDef_723_; lean_object* v_dvds_724_; lean_object* v_lowers_725_; lean_object* v_uppers_726_; lean_object* v_diseqs_727_; lean_object* v_elimEqs_728_; lean_object* v_elimStack_729_; lean_object* v_occurs_730_; lean_object* v_assignment_731_; lean_object* v_nextCnstrId_732_; uint8_t v_caseSplits_733_; lean_object* v_conflict_x3f_734_; lean_object* v_diseqSplits_735_; lean_object* v_divMod_736_; lean_object* v_toIntIds_737_; lean_object* v_toIntInfos_738_; lean_object* v_toIntTermMap_739_; lean_object* v_toIntVarMap_740_; uint8_t v_usedCommRing_741_; lean_object* v_nonlinearOccs_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_751_; 
v_vars_718_ = lean_ctor_get(v_s_717_, 0);
v_varMap_719_ = lean_ctor_get(v_s_717_, 1);
v_vars_x27_720_ = lean_ctor_get(v_s_717_, 2);
v_varMap_x27_721_ = lean_ctor_get(v_s_717_, 3);
v_natToIntMap_722_ = lean_ctor_get(v_s_717_, 4);
v_natDef_723_ = lean_ctor_get(v_s_717_, 5);
v_dvds_724_ = lean_ctor_get(v_s_717_, 6);
v_lowers_725_ = lean_ctor_get(v_s_717_, 7);
v_uppers_726_ = lean_ctor_get(v_s_717_, 8);
v_diseqs_727_ = lean_ctor_get(v_s_717_, 9);
v_elimEqs_728_ = lean_ctor_get(v_s_717_, 10);
v_elimStack_729_ = lean_ctor_get(v_s_717_, 11);
v_occurs_730_ = lean_ctor_get(v_s_717_, 12);
v_assignment_731_ = lean_ctor_get(v_s_717_, 13);
v_nextCnstrId_732_ = lean_ctor_get(v_s_717_, 14);
v_caseSplits_733_ = lean_ctor_get_uint8(v_s_717_, sizeof(void*)*23);
v_conflict_x3f_734_ = lean_ctor_get(v_s_717_, 15);
v_diseqSplits_735_ = lean_ctor_get(v_s_717_, 16);
v_divMod_736_ = lean_ctor_get(v_s_717_, 17);
v_toIntIds_737_ = lean_ctor_get(v_s_717_, 18);
v_toIntInfos_738_ = lean_ctor_get(v_s_717_, 19);
v_toIntTermMap_739_ = lean_ctor_get(v_s_717_, 20);
v_toIntVarMap_740_ = lean_ctor_get(v_s_717_, 21);
v_usedCommRing_741_ = lean_ctor_get_uint8(v_s_717_, sizeof(void*)*23 + 1);
v_nonlinearOccs_742_ = lean_ctor_get(v_s_717_, 22);
v_isSharedCheck_751_ = !lean_is_exclusive(v_s_717_);
if (v_isSharedCheck_751_ == 0)
{
v___x_744_ = v_s_717_;
v_isShared_745_ = v_isSharedCheck_751_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_nonlinearOccs_742_);
lean_inc(v_toIntVarMap_740_);
lean_inc(v_toIntTermMap_739_);
lean_inc(v_toIntInfos_738_);
lean_inc(v_toIntIds_737_);
lean_inc(v_divMod_736_);
lean_inc(v_diseqSplits_735_);
lean_inc(v_conflict_x3f_734_);
lean_inc(v_nextCnstrId_732_);
lean_inc(v_assignment_731_);
lean_inc(v_occurs_730_);
lean_inc(v_elimStack_729_);
lean_inc(v_elimEqs_728_);
lean_inc(v_diseqs_727_);
lean_inc(v_uppers_726_);
lean_inc(v_lowers_725_);
lean_inc(v_dvds_724_);
lean_inc(v_natDef_723_);
lean_inc(v_natToIntMap_722_);
lean_inc(v_varMap_x27_721_);
lean_inc(v_vars_x27_720_);
lean_inc(v_varMap_719_);
lean_inc(v_vars_718_);
lean_dec(v_s_717_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_751_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_749_; 
v___x_746_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0);
v___x_747_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(v_p_715_, v___x_746_, v_uppers_726_, v_v_716_);
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 8, v___x_747_);
v___x_749_ = v___x_744_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_vars_718_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v_varMap_719_);
lean_ctor_set(v_reuseFailAlloc_750_, 2, v_vars_x27_720_);
lean_ctor_set(v_reuseFailAlloc_750_, 3, v_varMap_x27_721_);
lean_ctor_set(v_reuseFailAlloc_750_, 4, v_natToIntMap_722_);
lean_ctor_set(v_reuseFailAlloc_750_, 5, v_natDef_723_);
lean_ctor_set(v_reuseFailAlloc_750_, 6, v_dvds_724_);
lean_ctor_set(v_reuseFailAlloc_750_, 7, v_lowers_725_);
lean_ctor_set(v_reuseFailAlloc_750_, 8, v___x_747_);
lean_ctor_set(v_reuseFailAlloc_750_, 9, v_diseqs_727_);
lean_ctor_set(v_reuseFailAlloc_750_, 10, v_elimEqs_728_);
lean_ctor_set(v_reuseFailAlloc_750_, 11, v_elimStack_729_);
lean_ctor_set(v_reuseFailAlloc_750_, 12, v_occurs_730_);
lean_ctor_set(v_reuseFailAlloc_750_, 13, v_assignment_731_);
lean_ctor_set(v_reuseFailAlloc_750_, 14, v_nextCnstrId_732_);
lean_ctor_set(v_reuseFailAlloc_750_, 15, v_conflict_x3f_734_);
lean_ctor_set(v_reuseFailAlloc_750_, 16, v_diseqSplits_735_);
lean_ctor_set(v_reuseFailAlloc_750_, 17, v_divMod_736_);
lean_ctor_set(v_reuseFailAlloc_750_, 18, v_toIntIds_737_);
lean_ctor_set(v_reuseFailAlloc_750_, 19, v_toIntInfos_738_);
lean_ctor_set(v_reuseFailAlloc_750_, 20, v_toIntTermMap_739_);
lean_ctor_set(v_reuseFailAlloc_750_, 21, v_toIntVarMap_740_);
lean_ctor_set(v_reuseFailAlloc_750_, 22, v_nonlinearOccs_742_);
lean_ctor_set_uint8(v_reuseFailAlloc_750_, sizeof(void*)*23, v_caseSplits_733_);
lean_ctor_set_uint8(v_reuseFailAlloc_750_, sizeof(void*)*23 + 1, v_usedCommRing_741_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___boxed(lean_object* v_p_752_, lean_object* v_v_753_, lean_object* v_s_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0(v_p_752_, v_v_753_, v_s_754_);
lean_dec(v_v_753_);
lean_dec_ref(v_p_752_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1(lean_object* v_p_756_, lean_object* v_v_757_, lean_object* v_s_758_){
_start:
{
lean_object* v_vars_759_; lean_object* v_varMap_760_; lean_object* v_vars_x27_761_; lean_object* v_varMap_x27_762_; lean_object* v_natToIntMap_763_; lean_object* v_natDef_764_; lean_object* v_dvds_765_; lean_object* v_lowers_766_; lean_object* v_uppers_767_; lean_object* v_diseqs_768_; lean_object* v_elimEqs_769_; lean_object* v_elimStack_770_; lean_object* v_occurs_771_; lean_object* v_assignment_772_; lean_object* v_nextCnstrId_773_; uint8_t v_caseSplits_774_; lean_object* v_conflict_x3f_775_; lean_object* v_diseqSplits_776_; lean_object* v_divMod_777_; lean_object* v_toIntIds_778_; lean_object* v_toIntInfos_779_; lean_object* v_toIntTermMap_780_; lean_object* v_toIntVarMap_781_; uint8_t v_usedCommRing_782_; lean_object* v_nonlinearOccs_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_792_; 
v_vars_759_ = lean_ctor_get(v_s_758_, 0);
v_varMap_760_ = lean_ctor_get(v_s_758_, 1);
v_vars_x27_761_ = lean_ctor_get(v_s_758_, 2);
v_varMap_x27_762_ = lean_ctor_get(v_s_758_, 3);
v_natToIntMap_763_ = lean_ctor_get(v_s_758_, 4);
v_natDef_764_ = lean_ctor_get(v_s_758_, 5);
v_dvds_765_ = lean_ctor_get(v_s_758_, 6);
v_lowers_766_ = lean_ctor_get(v_s_758_, 7);
v_uppers_767_ = lean_ctor_get(v_s_758_, 8);
v_diseqs_768_ = lean_ctor_get(v_s_758_, 9);
v_elimEqs_769_ = lean_ctor_get(v_s_758_, 10);
v_elimStack_770_ = lean_ctor_get(v_s_758_, 11);
v_occurs_771_ = lean_ctor_get(v_s_758_, 12);
v_assignment_772_ = lean_ctor_get(v_s_758_, 13);
v_nextCnstrId_773_ = lean_ctor_get(v_s_758_, 14);
v_caseSplits_774_ = lean_ctor_get_uint8(v_s_758_, sizeof(void*)*23);
v_conflict_x3f_775_ = lean_ctor_get(v_s_758_, 15);
v_diseqSplits_776_ = lean_ctor_get(v_s_758_, 16);
v_divMod_777_ = lean_ctor_get(v_s_758_, 17);
v_toIntIds_778_ = lean_ctor_get(v_s_758_, 18);
v_toIntInfos_779_ = lean_ctor_get(v_s_758_, 19);
v_toIntTermMap_780_ = lean_ctor_get(v_s_758_, 20);
v_toIntVarMap_781_ = lean_ctor_get(v_s_758_, 21);
v_usedCommRing_782_ = lean_ctor_get_uint8(v_s_758_, sizeof(void*)*23 + 1);
v_nonlinearOccs_783_ = lean_ctor_get(v_s_758_, 22);
v_isSharedCheck_792_ = !lean_is_exclusive(v_s_758_);
if (v_isSharedCheck_792_ == 0)
{
v___x_785_ = v_s_758_;
v_isShared_786_ = v_isSharedCheck_792_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_nonlinearOccs_783_);
lean_inc(v_toIntVarMap_781_);
lean_inc(v_toIntTermMap_780_);
lean_inc(v_toIntInfos_779_);
lean_inc(v_toIntIds_778_);
lean_inc(v_divMod_777_);
lean_inc(v_diseqSplits_776_);
lean_inc(v_conflict_x3f_775_);
lean_inc(v_nextCnstrId_773_);
lean_inc(v_assignment_772_);
lean_inc(v_occurs_771_);
lean_inc(v_elimStack_770_);
lean_inc(v_elimEqs_769_);
lean_inc(v_diseqs_768_);
lean_inc(v_uppers_767_);
lean_inc(v_lowers_766_);
lean_inc(v_dvds_765_);
lean_inc(v_natDef_764_);
lean_inc(v_natToIntMap_763_);
lean_inc(v_varMap_x27_762_);
lean_inc(v_vars_x27_761_);
lean_inc(v_varMap_760_);
lean_inc(v_vars_759_);
lean_dec(v_s_758_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_792_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_790_; 
v___x_787_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0);
v___x_788_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(v_p_756_, v___x_787_, v_lowers_766_, v_v_757_);
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 7, v___x_788_);
v___x_790_ = v___x_785_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_vars_759_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v_varMap_760_);
lean_ctor_set(v_reuseFailAlloc_791_, 2, v_vars_x27_761_);
lean_ctor_set(v_reuseFailAlloc_791_, 3, v_varMap_x27_762_);
lean_ctor_set(v_reuseFailAlloc_791_, 4, v_natToIntMap_763_);
lean_ctor_set(v_reuseFailAlloc_791_, 5, v_natDef_764_);
lean_ctor_set(v_reuseFailAlloc_791_, 6, v_dvds_765_);
lean_ctor_set(v_reuseFailAlloc_791_, 7, v___x_788_);
lean_ctor_set(v_reuseFailAlloc_791_, 8, v_uppers_767_);
lean_ctor_set(v_reuseFailAlloc_791_, 9, v_diseqs_768_);
lean_ctor_set(v_reuseFailAlloc_791_, 10, v_elimEqs_769_);
lean_ctor_set(v_reuseFailAlloc_791_, 11, v_elimStack_770_);
lean_ctor_set(v_reuseFailAlloc_791_, 12, v_occurs_771_);
lean_ctor_set(v_reuseFailAlloc_791_, 13, v_assignment_772_);
lean_ctor_set(v_reuseFailAlloc_791_, 14, v_nextCnstrId_773_);
lean_ctor_set(v_reuseFailAlloc_791_, 15, v_conflict_x3f_775_);
lean_ctor_set(v_reuseFailAlloc_791_, 16, v_diseqSplits_776_);
lean_ctor_set(v_reuseFailAlloc_791_, 17, v_divMod_777_);
lean_ctor_set(v_reuseFailAlloc_791_, 18, v_toIntIds_778_);
lean_ctor_set(v_reuseFailAlloc_791_, 19, v_toIntInfos_779_);
lean_ctor_set(v_reuseFailAlloc_791_, 20, v_toIntTermMap_780_);
lean_ctor_set(v_reuseFailAlloc_791_, 21, v_toIntVarMap_781_);
lean_ctor_set(v_reuseFailAlloc_791_, 22, v_nonlinearOccs_783_);
lean_ctor_set_uint8(v_reuseFailAlloc_791_, sizeof(void*)*23, v_caseSplits_774_);
lean_ctor_set_uint8(v_reuseFailAlloc_791_, sizeof(void*)*23 + 1, v_usedCommRing_782_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1___boxed(lean_object* v_p_793_, lean_object* v_v_794_, lean_object* v_s_795_){
_start:
{
lean_object* v_res_796_; 
v_res_796_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1(v_p_793_, v_v_794_, v_s_795_);
lean_dec(v_v_794_);
lean_dec_ref(v_p_793_);
return v_res_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(lean_object* v_c_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_){
_start:
{
lean_object* v_p_804_; 
v_p_804_ = lean_ctor_get(v_c_797_, 0);
if (lean_obj_tag(v_p_804_) == 1)
{
lean_object* v_k_805_; lean_object* v_v_806_; lean_object* v___x_807_; uint8_t v___x_808_; 
lean_inc_ref(v_p_804_);
lean_dec_ref(v_c_797_);
v_k_805_ = lean_ctor_get(v_p_804_, 0);
v_v_806_ = lean_ctor_get(v_p_804_, 1);
lean_inc(v_v_806_);
v___x_807_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6);
v___x_808_ = lean_int_dec_lt(v_k_805_, v___x_807_);
if (v___x_808_ == 0)
{
lean_object* v___f_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v___f_809_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_809_, 0, v_p_804_);
lean_closure_set(v___f_809_, 1, v_v_806_);
v___x_810_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_811_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_810_, v___f_809_, v_a_798_);
return v___x_811_;
}
else
{
lean_object* v___f_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v___f_812_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_812_, 0, v_p_804_);
lean_closure_set(v___f_812_, 1, v_v_806_);
v___x_813_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_814_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_813_, v___f_812_, v_a_798_);
return v___x_814_;
}
}
else
{
lean_object* v___x_815_; 
v___x_815_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_);
return v___x_815_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___boxed(lean_object* v_c_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_c_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_, v_a_821_);
lean_dec(v_a_821_);
lean_dec_ref(v_a_820_);
lean_dec(v_a_819_);
lean_dec_ref(v_a_818_);
lean_dec(v_a_817_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase(lean_object* v_c_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_){
_start:
{
lean_object* v___x_836_; 
v___x_836_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_c_824_, v_a_825_, v_a_831_, v_a_832_, v_a_833_, v_a_834_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___boxed(lean_object* v_c_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase(v_c_837_, v_a_838_, v_a_839_, v_a_840_, v_a_841_, v_a_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_);
lean_dec(v_a_847_);
lean_dec_ref(v_a_846_);
lean_dec(v_a_845_);
lean_dec_ref(v_a_844_);
lean_dec(v_a_843_);
lean_dec_ref(v_a_842_);
lean_dec(v_a_841_);
lean_dec_ref(v_a_840_);
lean_dec(v_a_839_);
lean_dec(v_a_838_);
return v_res_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4(lean_object* v___x_850_, lean_object* v_inst_851_, lean_object* v_x_852_, size_t v_x_853_, size_t v_x_854_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___redArg(v___x_850_, v_x_852_, v_x_853_, v_x_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___boxed(lean_object* v___x_856_, lean_object* v_inst_857_, lean_object* v_x_858_, lean_object* v_x_859_, lean_object* v_x_860_){
_start:
{
size_t v_x_2493__boxed_861_; size_t v_x_2494__boxed_862_; lean_object* v_res_863_; 
v_x_2493__boxed_861_ = lean_unbox_usize(v_x_859_);
lean_dec(v_x_859_);
v_x_2494__boxed_862_ = lean_unbox_usize(v_x_860_);
lean_dec(v_x_860_);
v_res_863_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4(v___x_856_, v_inst_857_, v_x_858_, v_x_2493__boxed_861_, v_x_2494__boxed_862_);
lean_dec_ref(v_inst_857_);
lean_dec_ref(v___x_856_);
return v_res_863_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__6(void){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_878_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5));
v___x_879_ = l_Lean_stringToMessageData(v___x_878_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3(lean_object* v___x_880_, lean_object* v_c_881_, lean_object* v_as_882_, size_t v_sz_883_, size_t v_i_884_, lean_object* v_b_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
uint8_t v___x_897_; 
v___x_897_ = lean_usize_dec_lt(v_i_884_, v_sz_883_);
if (v___x_897_ == 0)
{
lean_object* v___x_898_; 
lean_dec_ref(v_c_881_);
lean_dec_ref(v___x_880_);
v___x_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_898_, 0, v_b_885_);
return v___x_898_;
}
else
{
lean_object* v_snd_899_; lean_object* v___x_901_; uint8_t v_isShared_902_; uint8_t v_isSharedCheck_991_; 
v_snd_899_ = lean_ctor_get(v_b_885_, 1);
v_isSharedCheck_991_ = !lean_is_exclusive(v_b_885_);
if (v_isSharedCheck_991_ == 0)
{
lean_object* v_unused_992_; 
v_unused_992_ = lean_ctor_get(v_b_885_, 0);
lean_dec(v_unused_992_);
v___x_901_ = v_b_885_;
v_isShared_902_ = v_isSharedCheck_991_;
goto v_resetjp_900_;
}
else
{
lean_inc(v_snd_899_);
lean_dec(v_b_885_);
v___x_901_ = lean_box(0);
v_isShared_902_ = v_isSharedCheck_991_;
goto v_resetjp_900_;
}
v_resetjp_900_:
{
lean_object* v_a_903_; lean_object* v_p_904_; lean_object* v___x_905_; uint8_t v___x_906_; 
v_a_903_ = lean_array_uget_borrowed(v_as_882_, v_i_884_);
v_p_904_ = lean_ctor_get(v_a_903_, 0);
v___x_905_ = lean_box(0);
v___x_906_ = l_Int_Linear_Poly_isNegEq(v___x_880_, v_p_904_);
if (v___x_906_ == 0)
{
lean_object* v___x_907_; size_t v___x_908_; size_t v___x_909_; 
lean_del_object(v___x_901_);
lean_dec(v_snd_899_);
v___x_907_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__1));
v___x_908_ = ((size_t)1ULL);
v___x_909_ = lean_usize_add(v_i_884_, v___x_908_);
v_i_884_ = v___x_909_;
v_b_885_ = v___x_907_;
goto _start;
}
else
{
lean_object* v___x_911_; 
lean_inc(v_a_903_);
v___x_911_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_903_, v___y_886_, v___y_892_, v___y_893_, v___y_894_, v___y_895_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v___x_912_; lean_object* v___x_913_; 
lean_dec_ref(v___x_911_);
v___x_912_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_913_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_912_, v___y_894_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_object* v_a_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___y_918_; lean_object* v___y_919_; lean_object* v___y_920_; lean_object* v___y_921_; lean_object* v___y_922_; lean_object* v___y_923_; lean_object* v___y_924_; lean_object* v___y_925_; lean_object* v___y_926_; lean_object* v___y_927_; uint8_t v___x_953_; 
v_a_914_ = lean_ctor_get(v___x_913_, 0);
lean_inc(v_a_914_);
lean_dec_ref(v___x_913_);
lean_inc(v_a_903_);
v___x_915_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_915_, 0, v_c_881_);
lean_ctor_set(v___x_915_, 1, v_a_903_);
v___x_916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_880_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
v___x_953_ = lean_unbox(v_a_914_);
lean_dec(v_a_914_);
if (v___x_953_ == 0)
{
v___y_918_ = v___y_886_;
v___y_919_ = v___y_887_;
v___y_920_ = v___y_888_;
v___y_921_ = v___y_889_;
v___y_922_ = v___y_890_;
v___y_923_ = v___y_891_;
v___y_924_ = v___y_892_;
v___y_925_ = v___y_893_;
v___y_926_ = v___y_894_;
v___y_927_ = v___y_895_;
goto v___jp_917_;
}
else
{
lean_object* v___x_954_; 
lean_inc_ref(v___x_916_);
v___x_954_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_916_, v___y_886_, v___y_894_);
if (lean_obj_tag(v___x_954_) == 0)
{
lean_object* v_a_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
v_a_955_ = lean_ctor_get(v___x_954_, 0);
lean_inc(v_a_955_);
lean_dec_ref(v___x_954_);
v___x_956_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__6);
v___x_957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
lean_ctor_set(v___x_957_, 1, v_a_955_);
v___x_958_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1___redArg(v___x_912_, v___x_957_, v___y_892_, v___y_893_, v___y_894_, v___y_895_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_dec_ref(v___x_958_);
v___y_918_ = v___y_886_;
v___y_919_ = v___y_887_;
v___y_920_ = v___y_888_;
v___y_921_ = v___y_889_;
v___y_922_ = v___y_890_;
v___y_923_ = v___y_891_;
v___y_924_ = v___y_892_;
v___y_925_ = v___y_893_;
v___y_926_ = v___y_894_;
v___y_927_ = v___y_895_;
goto v___jp_917_;
}
else
{
lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_966_; 
lean_dec_ref(v___x_916_);
lean_del_object(v___x_901_);
lean_dec(v_snd_899_);
v_a_959_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_966_ == 0)
{
v___x_961_ = v___x_958_;
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_dec(v___x_958_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_966_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v___x_964_; 
if (v_isShared_962_ == 0)
{
v___x_964_ = v___x_961_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v_a_959_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
}
else
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
lean_dec_ref(v___x_916_);
lean_del_object(v___x_901_);
lean_dec(v_snd_899_);
v_a_967_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_974_ == 0)
{
v___x_969_ = v___x_954_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_954_);
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
v___jp_917_:
{
lean_object* v___x_928_; 
lean_inc(v___y_927_);
lean_inc_ref(v___y_926_);
lean_inc(v___y_925_);
lean_inc_ref(v___y_924_);
lean_inc(v___y_923_);
lean_inc_ref(v___y_922_);
lean_inc(v___y_921_);
lean_inc_ref(v___y_920_);
lean_inc(v___y_919_);
lean_inc(v___y_918_);
v___x_928_ = lean_grind_cutsat_assert_eq(v___x_916_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
if (lean_obj_tag(v___x_928_) == 0)
{
lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_943_; 
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_943_ == 0)
{
lean_object* v_unused_944_; 
v_unused_944_ = lean_ctor_get(v___x_928_, 0);
lean_dec(v_unused_944_);
v___x_930_ = v___x_928_;
v_isShared_931_ = v_isSharedCheck_943_;
goto v_resetjp_929_;
}
else
{
lean_dec(v___x_928_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_943_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_935_; 
v___x_932_ = lean_box(v___x_906_);
v___x_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_933_, 0, v___x_932_);
if (v_isShared_902_ == 0)
{
lean_ctor_set(v___x_901_, 1, v___x_905_);
lean_ctor_set(v___x_901_, 0, v___x_933_);
v___x_935_ = v___x_901_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v___x_933_);
lean_ctor_set(v_reuseFailAlloc_942_, 1, v___x_905_);
v___x_935_ = v_reuseFailAlloc_942_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_940_; 
v___x_936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
v___x_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_937_, 0, v___x_936_);
v___x_938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_937_);
lean_ctor_set(v___x_938_, 1, v_snd_899_);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 0, v___x_938_);
v___x_940_ = v___x_930_;
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
}
}
else
{
lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_952_; 
lean_del_object(v___x_901_);
lean_dec(v_snd_899_);
v_a_945_ = lean_ctor_get(v___x_928_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_928_);
if (v_isSharedCheck_952_ == 0)
{
v___x_947_ = v___x_928_;
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_dec(v___x_928_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_950_; 
if (v_isShared_948_ == 0)
{
v___x_950_ = v___x_947_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_a_945_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
}
else
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
lean_del_object(v___x_901_);
lean_dec(v_snd_899_);
lean_dec_ref(v_c_881_);
lean_dec_ref(v___x_880_);
v_a_975_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_982_ == 0)
{
v___x_977_ = v___x_913_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_913_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_980_; 
if (v_isShared_978_ == 0)
{
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_a_975_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
else
{
lean_object* v_a_983_; lean_object* v___x_985_; uint8_t v_isShared_986_; uint8_t v_isSharedCheck_990_; 
lean_del_object(v___x_901_);
lean_dec(v_snd_899_);
lean_dec_ref(v_c_881_);
lean_dec_ref(v___x_880_);
v_a_983_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_990_ == 0)
{
v___x_985_ = v___x_911_;
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
else
{
lean_inc(v_a_983_);
lean_dec(v___x_911_);
v___x_985_ = lean_box(0);
v_isShared_986_ = v_isSharedCheck_990_;
goto v_resetjp_984_;
}
v_resetjp_984_:
{
lean_object* v___x_988_; 
if (v_isShared_986_ == 0)
{
v___x_988_ = v___x_985_;
goto v_reusejp_987_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v_a_983_);
v___x_988_ = v_reuseFailAlloc_989_;
goto v_reusejp_987_;
}
v_reusejp_987_:
{
return v___x_988_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___boxed(lean_object** _args){
lean_object* v___x_993_ = _args[0];
lean_object* v_c_994_ = _args[1];
lean_object* v_as_995_ = _args[2];
lean_object* v_sz_996_ = _args[3];
lean_object* v_i_997_ = _args[4];
lean_object* v_b_998_ = _args[5];
lean_object* v___y_999_ = _args[6];
lean_object* v___y_1000_ = _args[7];
lean_object* v___y_1001_ = _args[8];
lean_object* v___y_1002_ = _args[9];
lean_object* v___y_1003_ = _args[10];
lean_object* v___y_1004_ = _args[11];
lean_object* v___y_1005_ = _args[12];
lean_object* v___y_1006_ = _args[13];
lean_object* v___y_1007_ = _args[14];
lean_object* v___y_1008_ = _args[15];
lean_object* v___y_1009_ = _args[16];
_start:
{
size_t v_sz_boxed_1010_; size_t v_i_boxed_1011_; lean_object* v_res_1012_; 
v_sz_boxed_1010_ = lean_unbox_usize(v_sz_996_);
lean_dec(v_sz_996_);
v_i_boxed_1011_ = lean_unbox_usize(v_i_997_);
lean_dec(v_i_997_);
v_res_1012_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3(v___x_993_, v_c_994_, v_as_995_, v_sz_boxed_1010_, v_i_boxed_1011_, v_b_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec(v___y_999_);
lean_dec_ref(v_as_995_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2(lean_object* v___x_1019_, lean_object* v_c_1020_, lean_object* v_as_1021_, size_t v_sz_1022_, size_t v_i_1023_, lean_object* v_b_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_){
_start:
{
uint8_t v___x_1036_; 
v___x_1036_ = lean_usize_dec_lt(v_i_1023_, v_sz_1022_);
if (v___x_1036_ == 0)
{
lean_object* v___x_1037_; 
lean_dec_ref(v_c_1020_);
lean_dec_ref(v___x_1019_);
v___x_1037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1037_, 0, v_b_1024_);
return v___x_1037_;
}
else
{
lean_object* v_snd_1038_; lean_object* v___x_1040_; uint8_t v_isShared_1041_; uint8_t v_isSharedCheck_1130_; 
v_snd_1038_ = lean_ctor_get(v_b_1024_, 1);
v_isSharedCheck_1130_ = !lean_is_exclusive(v_b_1024_);
if (v_isSharedCheck_1130_ == 0)
{
lean_object* v_unused_1131_; 
v_unused_1131_ = lean_ctor_get(v_b_1024_, 0);
lean_dec(v_unused_1131_);
v___x_1040_ = v_b_1024_;
v_isShared_1041_ = v_isSharedCheck_1130_;
goto v_resetjp_1039_;
}
else
{
lean_inc(v_snd_1038_);
lean_dec(v_b_1024_);
v___x_1040_ = lean_box(0);
v_isShared_1041_ = v_isSharedCheck_1130_;
goto v_resetjp_1039_;
}
v_resetjp_1039_:
{
lean_object* v_a_1042_; lean_object* v_p_1043_; lean_object* v___x_1044_; uint8_t v___x_1045_; 
v_a_1042_ = lean_array_uget_borrowed(v_as_1021_, v_i_1023_);
v_p_1043_ = lean_ctor_get(v_a_1042_, 0);
v___x_1044_ = lean_box(0);
v___x_1045_ = l_Int_Linear_Poly_isNegEq(v___x_1019_, v_p_1043_);
if (v___x_1045_ == 0)
{
lean_object* v___x_1046_; size_t v___x_1047_; size_t v___x_1048_; lean_object* v___x_1049_; 
lean_del_object(v___x_1040_);
lean_dec(v_snd_1038_);
v___x_1046_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__1));
v___x_1047_ = ((size_t)1ULL);
v___x_1048_ = lean_usize_add(v_i_1023_, v___x_1047_);
v___x_1049_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3(v___x_1019_, v_c_1020_, v_as_1021_, v_sz_1022_, v___x_1048_, v___x_1046_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
return v___x_1049_;
}
else
{
lean_object* v___x_1050_; 
lean_inc(v_a_1042_);
v___x_1050_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_1042_, v___y_1025_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
lean_dec_ref(v___x_1050_);
v___x_1051_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_1052_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_1051_, v___y_1033_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___y_1057_; lean_object* v___y_1058_; lean_object* v___y_1059_; lean_object* v___y_1060_; lean_object* v___y_1061_; lean_object* v___y_1062_; lean_object* v___y_1063_; lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1066_; uint8_t v___x_1092_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_a_1053_);
lean_dec_ref(v___x_1052_);
lean_inc(v_a_1042_);
v___x_1054_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1054_, 0, v_c_1020_);
lean_ctor_set(v___x_1054_, 1, v_a_1042_);
v___x_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1019_);
lean_ctor_set(v___x_1055_, 1, v___x_1054_);
v___x_1092_ = lean_unbox(v_a_1053_);
lean_dec(v_a_1053_);
if (v___x_1092_ == 0)
{
v___y_1057_ = v___y_1025_;
v___y_1058_ = v___y_1026_;
v___y_1059_ = v___y_1027_;
v___y_1060_ = v___y_1028_;
v___y_1061_ = v___y_1029_;
v___y_1062_ = v___y_1030_;
v___y_1063_ = v___y_1031_;
v___y_1064_ = v___y_1032_;
v___y_1065_ = v___y_1033_;
v___y_1066_ = v___y_1034_;
goto v___jp_1056_;
}
else
{
lean_object* v___x_1093_; 
lean_inc_ref(v___x_1055_);
v___x_1093_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_1055_, v___y_1025_, v___y_1033_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v_a_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v_a_1094_ = lean_ctor_get(v___x_1093_, 0);
lean_inc(v_a_1094_);
lean_dec_ref(v___x_1093_);
v___x_1095_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__6);
v___x_1096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1095_);
lean_ctor_set(v___x_1096_, 1, v_a_1094_);
v___x_1097_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1___redArg(v___x_1051_, v___x_1096_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_dec_ref(v___x_1097_);
v___y_1057_ = v___y_1025_;
v___y_1058_ = v___y_1026_;
v___y_1059_ = v___y_1027_;
v___y_1060_ = v___y_1028_;
v___y_1061_ = v___y_1029_;
v___y_1062_ = v___y_1030_;
v___y_1063_ = v___y_1031_;
v___y_1064_ = v___y_1032_;
v___y_1065_ = v___y_1033_;
v___y_1066_ = v___y_1034_;
goto v___jp_1056_;
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
lean_dec_ref(v___x_1055_);
lean_del_object(v___x_1040_);
lean_dec(v_snd_1038_);
v_a_1098_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v___x_1097_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1097_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1098_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
else
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
lean_dec_ref(v___x_1055_);
lean_del_object(v___x_1040_);
lean_dec(v_snd_1038_);
v_a_1106_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1108_ = v___x_1093_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1093_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1109_ == 0)
{
v___x_1111_ = v___x_1108_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1106_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
v___jp_1056_:
{
lean_object* v___x_1067_; 
lean_inc(v___y_1066_);
lean_inc_ref(v___y_1065_);
lean_inc(v___y_1064_);
lean_inc_ref(v___y_1063_);
lean_inc(v___y_1062_);
lean_inc_ref(v___y_1061_);
lean_inc(v___y_1060_);
lean_inc_ref(v___y_1059_);
lean_inc(v___y_1058_);
lean_inc(v___y_1057_);
v___x_1067_ = lean_grind_cutsat_assert_eq(v___x_1055_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
if (lean_obj_tag(v___x_1067_) == 0)
{
lean_object* v___x_1069_; uint8_t v_isShared_1070_; uint8_t v_isSharedCheck_1082_; 
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1082_ == 0)
{
lean_object* v_unused_1083_; 
v_unused_1083_ = lean_ctor_get(v___x_1067_, 0);
lean_dec(v_unused_1083_);
v___x_1069_ = v___x_1067_;
v_isShared_1070_ = v_isSharedCheck_1082_;
goto v_resetjp_1068_;
}
else
{
lean_dec(v___x_1067_);
v___x_1069_ = lean_box(0);
v_isShared_1070_ = v_isSharedCheck_1082_;
goto v_resetjp_1068_;
}
v_resetjp_1068_:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1074_; 
v___x_1071_ = lean_box(v___x_1045_);
v___x_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
if (v_isShared_1041_ == 0)
{
lean_ctor_set(v___x_1040_, 1, v___x_1044_);
lean_ctor_set(v___x_1040_, 0, v___x_1072_);
v___x_1074_ = v___x_1040_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1072_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v___x_1044_);
v___x_1074_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1079_; 
v___x_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
v___x_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1075_);
v___x_1077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
lean_ctor_set(v___x_1077_, 1, v_snd_1038_);
if (v_isShared_1070_ == 0)
{
lean_ctor_set(v___x_1069_, 0, v___x_1077_);
v___x_1079_ = v___x_1069_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1077_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
}
else
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1091_; 
lean_del_object(v___x_1040_);
lean_dec(v_snd_1038_);
v_a_1084_ = lean_ctor_get(v___x_1067_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1067_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1086_ = v___x_1067_;
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1067_);
v___x_1086_ = lean_box(0);
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
v_resetjp_1085_:
{
lean_object* v___x_1089_; 
if (v_isShared_1087_ == 0)
{
v___x_1089_ = v___x_1086_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_a_1084_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
return v___x_1089_;
}
}
}
}
}
else
{
lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1121_; 
lean_del_object(v___x_1040_);
lean_dec(v_snd_1038_);
lean_dec_ref(v_c_1020_);
lean_dec_ref(v___x_1019_);
v_a_1114_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1116_ = v___x_1052_;
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_1052_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1117_ == 0)
{
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_a_1114_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
else
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
lean_del_object(v___x_1040_);
lean_dec(v_snd_1038_);
lean_dec_ref(v_c_1020_);
lean_dec_ref(v___x_1019_);
v_a_1122_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1124_ = v___x_1050_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___x_1050_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1125_ == 0)
{
v___x_1127_ = v___x_1124_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_a_1122_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___boxed(lean_object** _args){
lean_object* v___x_1132_ = _args[0];
lean_object* v_c_1133_ = _args[1];
lean_object* v_as_1134_ = _args[2];
lean_object* v_sz_1135_ = _args[3];
lean_object* v_i_1136_ = _args[4];
lean_object* v_b_1137_ = _args[5];
lean_object* v___y_1138_ = _args[6];
lean_object* v___y_1139_ = _args[7];
lean_object* v___y_1140_ = _args[8];
lean_object* v___y_1141_ = _args[9];
lean_object* v___y_1142_ = _args[10];
lean_object* v___y_1143_ = _args[11];
lean_object* v___y_1144_ = _args[12];
lean_object* v___y_1145_ = _args[13];
lean_object* v___y_1146_ = _args[14];
lean_object* v___y_1147_ = _args[15];
lean_object* v___y_1148_ = _args[16];
_start:
{
size_t v_sz_boxed_1149_; size_t v_i_boxed_1150_; lean_object* v_res_1151_; 
v_sz_boxed_1149_ = lean_unbox_usize(v_sz_1135_);
lean_dec(v_sz_1135_);
v_i_boxed_1150_ = lean_unbox_usize(v_i_1136_);
lean_dec(v_i_1136_);
v_res_1151_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2(v___x_1132_, v_c_1133_, v_as_1134_, v_sz_boxed_1149_, v_i_boxed_1150_, v_b_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
lean_dec(v___y_1143_);
lean_dec_ref(v___y_1142_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v___y_1139_);
lean_dec(v___y_1138_);
lean_dec_ref(v_as_1134_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(lean_object* v___x_1152_, lean_object* v_c_1153_, lean_object* v_inh_1154_, lean_object* v_n_1155_, lean_object* v_b_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_){
_start:
{
if (lean_obj_tag(v_n_1155_) == 0)
{
lean_object* v_cs_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1202_; 
v_cs_1168_ = lean_ctor_get(v_n_1155_, 0);
v_isSharedCheck_1202_ = !lean_is_exclusive(v_n_1155_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1170_ = v_n_1155_;
v_isShared_1171_ = v_isSharedCheck_1202_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_cs_1168_);
lean_dec(v_n_1155_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1202_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; size_t v_sz_1174_; size_t v___x_1175_; lean_object* v___x_1176_; 
v___x_1172_ = lean_box(0);
v___x_1173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1172_);
lean_ctor_set(v___x_1173_, 1, v_b_1156_);
v_sz_1174_ = lean_array_size(v_cs_1168_);
v___x_1175_ = ((size_t)0ULL);
v___x_1176_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(v___x_1152_, v_c_1153_, v_inh_1154_, v_cs_1168_, v_sz_1174_, v___x_1175_, v___x_1173_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
lean_dec_ref(v_cs_1168_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v_a_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1193_; 
v_a_1177_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1193_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1193_ == 0)
{
v___x_1179_ = v___x_1176_;
v_isShared_1180_ = v_isSharedCheck_1193_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_a_1177_);
lean_dec(v___x_1176_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1193_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v_fst_1181_; 
v_fst_1181_ = lean_ctor_get(v_a_1177_, 0);
if (lean_obj_tag(v_fst_1181_) == 0)
{
lean_object* v_snd_1182_; lean_object* v___x_1184_; 
v_snd_1182_ = lean_ctor_get(v_a_1177_, 1);
lean_inc(v_snd_1182_);
lean_dec(v_a_1177_);
if (v_isShared_1171_ == 0)
{
lean_ctor_set_tag(v___x_1170_, 1);
lean_ctor_set(v___x_1170_, 0, v_snd_1182_);
v___x_1184_ = v___x_1170_;
goto v_reusejp_1183_;
}
else
{
lean_object* v_reuseFailAlloc_1188_; 
v_reuseFailAlloc_1188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1188_, 0, v_snd_1182_);
v___x_1184_ = v_reuseFailAlloc_1188_;
goto v_reusejp_1183_;
}
v_reusejp_1183_:
{
lean_object* v___x_1186_; 
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 0, v___x_1184_);
v___x_1186_ = v___x_1179_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v___x_1184_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
else
{
lean_object* v_val_1189_; lean_object* v___x_1191_; 
lean_inc_ref(v_fst_1181_);
lean_dec(v_a_1177_);
lean_del_object(v___x_1170_);
v_val_1189_ = lean_ctor_get(v_fst_1181_, 0);
lean_inc(v_val_1189_);
lean_dec_ref(v_fst_1181_);
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 0, v_val_1189_);
v___x_1191_ = v___x_1179_;
goto v_reusejp_1190_;
}
else
{
lean_object* v_reuseFailAlloc_1192_; 
v_reuseFailAlloc_1192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_val_1189_);
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
lean_del_object(v___x_1170_);
v_a_1194_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1201_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1201_ == 0)
{
v___x_1196_ = v___x_1176_;
v_isShared_1197_ = v_isSharedCheck_1201_;
goto v_resetjp_1195_;
}
else
{
lean_inc(v_a_1194_);
lean_dec(v___x_1176_);
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
}
else
{
lean_object* v_vs_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1237_; 
v_vs_1203_ = lean_ctor_get(v_n_1155_, 0);
v_isSharedCheck_1237_ = !lean_is_exclusive(v_n_1155_);
if (v_isSharedCheck_1237_ == 0)
{
v___x_1205_ = v_n_1155_;
v_isShared_1206_ = v_isSharedCheck_1237_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_vs_1203_);
lean_dec(v_n_1155_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1237_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; size_t v_sz_1209_; size_t v___x_1210_; lean_object* v___x_1211_; 
v___x_1207_ = lean_box(0);
v___x_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1207_);
lean_ctor_set(v___x_1208_, 1, v_b_1156_);
v_sz_1209_ = lean_array_size(v_vs_1203_);
v___x_1210_ = ((size_t)0ULL);
v___x_1211_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2(v___x_1152_, v_c_1153_, v_vs_1203_, v_sz_1209_, v___x_1210_, v___x_1208_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_);
lean_dec_ref(v_vs_1203_);
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1228_; 
v_a_1212_ = lean_ctor_get(v___x_1211_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1214_ = v___x_1211_;
v_isShared_1215_ = v_isSharedCheck_1228_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1211_);
v___x_1214_ = lean_box(0);
v_isShared_1215_ = v_isSharedCheck_1228_;
goto v_resetjp_1213_;
}
v_resetjp_1213_:
{
lean_object* v_fst_1216_; 
v_fst_1216_ = lean_ctor_get(v_a_1212_, 0);
if (lean_obj_tag(v_fst_1216_) == 0)
{
lean_object* v_snd_1217_; lean_object* v___x_1219_; 
v_snd_1217_ = lean_ctor_get(v_a_1212_, 1);
lean_inc(v_snd_1217_);
lean_dec(v_a_1212_);
if (v_isShared_1206_ == 0)
{
lean_ctor_set(v___x_1205_, 0, v_snd_1217_);
v___x_1219_ = v___x_1205_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_snd_1217_);
v___x_1219_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
lean_object* v___x_1221_; 
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 0, v___x_1219_);
v___x_1221_ = v___x_1214_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v___x_1219_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
else
{
lean_object* v_val_1224_; lean_object* v___x_1226_; 
lean_inc_ref(v_fst_1216_);
lean_dec(v_a_1212_);
lean_del_object(v___x_1205_);
v_val_1224_ = lean_ctor_get(v_fst_1216_, 0);
lean_inc(v_val_1224_);
lean_dec_ref(v_fst_1216_);
if (v_isShared_1215_ == 0)
{
lean_ctor_set(v___x_1214_, 0, v_val_1224_);
v___x_1226_ = v___x_1214_;
goto v_reusejp_1225_;
}
else
{
lean_object* v_reuseFailAlloc_1227_; 
v_reuseFailAlloc_1227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1227_, 0, v_val_1224_);
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
lean_del_object(v___x_1205_);
v_a_1229_ = lean_ctor_get(v___x_1211_, 0);
v_isSharedCheck_1236_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1236_ == 0)
{
v___x_1231_ = v___x_1211_;
v_isShared_1232_ = v_isSharedCheck_1236_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_a_1229_);
lean_dec(v___x_1211_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(lean_object* v___x_1238_, lean_object* v_c_1239_, lean_object* v_inh_1240_, lean_object* v_as_1241_, size_t v_sz_1242_, size_t v_i_1243_, lean_object* v_b_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_){
_start:
{
uint8_t v___x_1256_; 
v___x_1256_ = lean_usize_dec_lt(v_i_1243_, v_sz_1242_);
if (v___x_1256_ == 0)
{
lean_object* v___x_1257_; 
lean_dec_ref(v_c_1239_);
lean_dec_ref(v___x_1238_);
v___x_1257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1257_, 0, v_b_1244_);
return v___x_1257_;
}
else
{
lean_object* v_snd_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1292_; 
v_snd_1258_ = lean_ctor_get(v_b_1244_, 1);
v_isSharedCheck_1292_ = !lean_is_exclusive(v_b_1244_);
if (v_isSharedCheck_1292_ == 0)
{
lean_object* v_unused_1293_; 
v_unused_1293_ = lean_ctor_get(v_b_1244_, 0);
lean_dec(v_unused_1293_);
v___x_1260_ = v_b_1244_;
v_isShared_1261_ = v_isSharedCheck_1292_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_snd_1258_);
lean_dec(v_b_1244_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1292_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v_a_1262_; lean_object* v___x_1263_; 
v_a_1262_ = lean_array_uget_borrowed(v_as_1241_, v_i_1243_);
lean_inc(v_snd_1258_);
lean_inc(v_a_1262_);
lean_inc_ref(v_c_1239_);
lean_inc_ref(v___x_1238_);
v___x_1263_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(v___x_1238_, v_c_1239_, v_inh_1240_, v_a_1262_, v_snd_1258_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_);
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1283_; 
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1283_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1283_ == 0)
{
v___x_1266_ = v___x_1263_;
v_isShared_1267_ = v_isSharedCheck_1283_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1263_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1283_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
if (lean_obj_tag(v_a_1264_) == 0)
{
lean_object* v___x_1268_; lean_object* v___x_1270_; 
lean_dec_ref(v_c_1239_);
lean_dec_ref(v___x_1238_);
v___x_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1268_, 0, v_a_1264_);
if (v_isShared_1261_ == 0)
{
lean_ctor_set(v___x_1260_, 0, v___x_1268_);
v___x_1270_ = v___x_1260_;
goto v_reusejp_1269_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1268_);
lean_ctor_set(v_reuseFailAlloc_1274_, 1, v_snd_1258_);
v___x_1270_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1269_;
}
v_reusejp_1269_:
{
lean_object* v___x_1272_; 
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 0, v___x_1270_);
v___x_1272_ = v___x_1266_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v___x_1270_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
else
{
lean_object* v_a_1275_; lean_object* v___x_1276_; lean_object* v___x_1278_; 
lean_del_object(v___x_1266_);
lean_dec(v_snd_1258_);
v_a_1275_ = lean_ctor_get(v_a_1264_, 0);
lean_inc(v_a_1275_);
lean_dec_ref(v_a_1264_);
v___x_1276_ = lean_box(0);
if (v_isShared_1261_ == 0)
{
lean_ctor_set(v___x_1260_, 1, v_a_1275_);
lean_ctor_set(v___x_1260_, 0, v___x_1276_);
v___x_1278_ = v___x_1260_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1282_; 
v_reuseFailAlloc_1282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1282_, 0, v___x_1276_);
lean_ctor_set(v_reuseFailAlloc_1282_, 1, v_a_1275_);
v___x_1278_ = v_reuseFailAlloc_1282_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
size_t v___x_1279_; size_t v___x_1280_; 
v___x_1279_ = ((size_t)1ULL);
v___x_1280_ = lean_usize_add(v_i_1243_, v___x_1279_);
v_i_1243_ = v___x_1280_;
v_b_1244_ = v___x_1278_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
lean_del_object(v___x_1260_);
lean_dec(v_snd_1258_);
lean_dec_ref(v_c_1239_);
lean_dec_ref(v___x_1238_);
v_a_1284_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1263_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1263_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1284_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v___x_1294_ = _args[0];
lean_object* v_c_1295_ = _args[1];
lean_object* v_inh_1296_ = _args[2];
lean_object* v_as_1297_ = _args[3];
lean_object* v_sz_1298_ = _args[4];
lean_object* v_i_1299_ = _args[5];
lean_object* v_b_1300_ = _args[6];
lean_object* v___y_1301_ = _args[7];
lean_object* v___y_1302_ = _args[8];
lean_object* v___y_1303_ = _args[9];
lean_object* v___y_1304_ = _args[10];
lean_object* v___y_1305_ = _args[11];
lean_object* v___y_1306_ = _args[12];
lean_object* v___y_1307_ = _args[13];
lean_object* v___y_1308_ = _args[14];
lean_object* v___y_1309_ = _args[15];
lean_object* v___y_1310_ = _args[16];
lean_object* v___y_1311_ = _args[17];
_start:
{
size_t v_sz_boxed_1312_; size_t v_i_boxed_1313_; lean_object* v_res_1314_; 
v_sz_boxed_1312_ = lean_unbox_usize(v_sz_1298_);
lean_dec(v_sz_1298_);
v_i_boxed_1313_ = lean_unbox_usize(v_i_1299_);
lean_dec(v_i_1299_);
v_res_1314_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(v___x_1294_, v_c_1295_, v_inh_1296_, v_as_1297_, v_sz_boxed_1312_, v_i_boxed_1313_, v_b_1300_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
lean_dec(v___y_1308_);
lean_dec_ref(v___y_1307_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec(v___y_1302_);
lean_dec(v___y_1301_);
lean_dec_ref(v_as_1297_);
lean_dec_ref(v_inh_1296_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___boxed(lean_object* v___x_1315_, lean_object* v_c_1316_, lean_object* v_inh_1317_, lean_object* v_n_1318_, lean_object* v_b_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(v___x_1315_, v_c_1316_, v_inh_1317_, v_n_1318_, v_b_1319_, v___y_1320_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_);
lean_dec(v___y_1329_);
lean_dec_ref(v___y_1328_);
lean_dec(v___y_1327_);
lean_dec_ref(v___y_1326_);
lean_dec(v___y_1325_);
lean_dec_ref(v___y_1324_);
lean_dec(v___y_1323_);
lean_dec_ref(v___y_1322_);
lean_dec(v___y_1321_);
lean_dec(v___y_1320_);
lean_dec_ref(v_inh_1317_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4(lean_object* v___x_1338_, lean_object* v_c_1339_, lean_object* v_as_1340_, size_t v_sz_1341_, size_t v_i_1342_, lean_object* v_b_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_){
_start:
{
uint8_t v___x_1355_; 
v___x_1355_ = lean_usize_dec_lt(v_i_1342_, v_sz_1341_);
if (v___x_1355_ == 0)
{
lean_object* v___x_1356_; 
lean_dec_ref(v_c_1339_);
lean_dec_ref(v___x_1338_);
v___x_1356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1356_, 0, v_b_1343_);
return v___x_1356_;
}
else
{
lean_object* v_snd_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1448_; 
v_snd_1357_ = lean_ctor_get(v_b_1343_, 1);
v_isSharedCheck_1448_ = !lean_is_exclusive(v_b_1343_);
if (v_isSharedCheck_1448_ == 0)
{
lean_object* v_unused_1449_; 
v_unused_1449_ = lean_ctor_get(v_b_1343_, 0);
lean_dec(v_unused_1449_);
v___x_1359_ = v_b_1343_;
v_isShared_1360_ = v_isSharedCheck_1448_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_snd_1357_);
lean_dec(v_b_1343_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1448_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v_a_1361_; lean_object* v_p_1362_; lean_object* v___x_1363_; uint8_t v___x_1364_; 
v_a_1361_ = lean_array_uget_borrowed(v_as_1340_, v_i_1342_);
v_p_1362_ = lean_ctor_get(v_a_1361_, 0);
v___x_1363_ = lean_box(0);
v___x_1364_ = l_Int_Linear_Poly_isNegEq(v___x_1338_, v_p_1362_);
if (v___x_1364_ == 0)
{
lean_object* v___x_1365_; size_t v___x_1366_; size_t v___x_1367_; 
lean_del_object(v___x_1359_);
lean_dec(v_snd_1357_);
v___x_1365_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___closed__1));
v___x_1366_ = ((size_t)1ULL);
v___x_1367_ = lean_usize_add(v_i_1342_, v___x_1366_);
v_i_1342_ = v___x_1367_;
v_b_1343_ = v___x_1365_;
goto _start;
}
else
{
lean_object* v___x_1369_; 
lean_inc(v_a_1361_);
v___x_1369_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_1361_, v___y_1344_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
if (lean_obj_tag(v___x_1369_) == 0)
{
lean_object* v___x_1370_; lean_object* v___x_1371_; 
lean_dec_ref(v___x_1369_);
v___x_1370_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_1371_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_1370_, v___y_1352_);
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_object* v_a_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___y_1376_; lean_object* v___y_1377_; lean_object* v___y_1378_; lean_object* v___y_1379_; lean_object* v___y_1380_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; uint8_t v___x_1410_; 
v_a_1372_ = lean_ctor_get(v___x_1371_, 0);
lean_inc(v_a_1372_);
lean_dec_ref(v___x_1371_);
lean_inc(v_a_1361_);
v___x_1373_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1373_, 0, v_c_1339_);
lean_ctor_set(v___x_1373_, 1, v_a_1361_);
v___x_1374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1374_, 0, v___x_1338_);
lean_ctor_set(v___x_1374_, 1, v___x_1373_);
v___x_1410_ = lean_unbox(v_a_1372_);
lean_dec(v_a_1372_);
if (v___x_1410_ == 0)
{
v___y_1376_ = v___y_1344_;
v___y_1377_ = v___y_1345_;
v___y_1378_ = v___y_1346_;
v___y_1379_ = v___y_1347_;
v___y_1380_ = v___y_1348_;
v___y_1381_ = v___y_1349_;
v___y_1382_ = v___y_1350_;
v___y_1383_ = v___y_1351_;
v___y_1384_ = v___y_1352_;
v___y_1385_ = v___y_1353_;
goto v___jp_1375_;
}
else
{
lean_object* v___x_1411_; 
lean_inc_ref(v___x_1374_);
v___x_1411_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_1374_, v___y_1344_, v___y_1352_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_object* v_a_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
lean_inc(v_a_1412_);
lean_dec_ref(v___x_1411_);
v___x_1413_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__6);
v___x_1414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1413_);
lean_ctor_set(v___x_1414_, 1, v_a_1412_);
v___x_1415_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1___redArg(v___x_1370_, v___x_1414_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_dec_ref(v___x_1415_);
v___y_1376_ = v___y_1344_;
v___y_1377_ = v___y_1345_;
v___y_1378_ = v___y_1346_;
v___y_1379_ = v___y_1347_;
v___y_1380_ = v___y_1348_;
v___y_1381_ = v___y_1349_;
v___y_1382_ = v___y_1350_;
v___y_1383_ = v___y_1351_;
v___y_1384_ = v___y_1352_;
v___y_1385_ = v___y_1353_;
goto v___jp_1375_;
}
else
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1423_; 
lean_dec_ref(v___x_1374_);
lean_del_object(v___x_1359_);
lean_dec(v_snd_1357_);
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1418_ = v___x_1415_;
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1415_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1421_; 
if (v_isShared_1419_ == 0)
{
v___x_1421_ = v___x_1418_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_a_1416_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
}
else
{
lean_object* v_a_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1431_; 
lean_dec_ref(v___x_1374_);
lean_del_object(v___x_1359_);
lean_dec(v_snd_1357_);
v_a_1424_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1431_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1431_ == 0)
{
v___x_1426_ = v___x_1411_;
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_a_1424_);
lean_dec(v___x_1411_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1431_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1429_; 
if (v_isShared_1427_ == 0)
{
v___x_1429_ = v___x_1426_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1430_; 
v_reuseFailAlloc_1430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1430_, 0, v_a_1424_);
v___x_1429_ = v_reuseFailAlloc_1430_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
return v___x_1429_;
}
}
}
}
v___jp_1375_:
{
lean_object* v___x_1386_; 
lean_inc(v___y_1385_);
lean_inc_ref(v___y_1384_);
lean_inc(v___y_1383_);
lean_inc_ref(v___y_1382_);
lean_inc(v___y_1381_);
lean_inc_ref(v___y_1380_);
lean_inc(v___y_1379_);
lean_inc_ref(v___y_1378_);
lean_inc(v___y_1377_);
lean_inc(v___y_1376_);
v___x_1386_ = lean_grind_cutsat_assert_eq(v___x_1374_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
if (lean_obj_tag(v___x_1386_) == 0)
{
lean_object* v___x_1388_; uint8_t v_isShared_1389_; uint8_t v_isSharedCheck_1400_; 
v_isSharedCheck_1400_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1400_ == 0)
{
lean_object* v_unused_1401_; 
v_unused_1401_ = lean_ctor_get(v___x_1386_, 0);
lean_dec(v_unused_1401_);
v___x_1388_ = v___x_1386_;
v_isShared_1389_ = v_isSharedCheck_1400_;
goto v_resetjp_1387_;
}
else
{
lean_dec(v___x_1386_);
v___x_1388_ = lean_box(0);
v_isShared_1389_ = v_isSharedCheck_1400_;
goto v_resetjp_1387_;
}
v_resetjp_1387_:
{
lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1393_; 
v___x_1390_ = lean_box(v___x_1364_);
v___x_1391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1390_);
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 1, v___x_1363_);
lean_ctor_set(v___x_1359_, 0, v___x_1391_);
v___x_1393_ = v___x_1359_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1391_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v___x_1363_);
v___x_1393_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1397_; 
v___x_1394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1394_, 0, v___x_1393_);
v___x_1395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1394_);
lean_ctor_set(v___x_1395_, 1, v_snd_1357_);
if (v_isShared_1389_ == 0)
{
lean_ctor_set(v___x_1388_, 0, v___x_1395_);
v___x_1397_ = v___x_1388_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1398_; 
v_reuseFailAlloc_1398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1398_, 0, v___x_1395_);
v___x_1397_ = v_reuseFailAlloc_1398_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
return v___x_1397_;
}
}
}
}
else
{
lean_object* v_a_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1409_; 
lean_del_object(v___x_1359_);
lean_dec(v_snd_1357_);
v_a_1402_ = lean_ctor_get(v___x_1386_, 0);
v_isSharedCheck_1409_ = !lean_is_exclusive(v___x_1386_);
if (v_isSharedCheck_1409_ == 0)
{
v___x_1404_ = v___x_1386_;
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_a_1402_);
lean_dec(v___x_1386_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1409_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v___x_1407_; 
if (v_isShared_1405_ == 0)
{
v___x_1407_ = v___x_1404_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_a_1402_);
v___x_1407_ = v_reuseFailAlloc_1408_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
return v___x_1407_;
}
}
}
}
}
else
{
lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1439_; 
lean_del_object(v___x_1359_);
lean_dec(v_snd_1357_);
lean_dec_ref(v_c_1339_);
lean_dec_ref(v___x_1338_);
v_a_1432_ = lean_ctor_get(v___x_1371_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1434_ = v___x_1371_;
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v___x_1371_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v___x_1437_; 
if (v_isShared_1435_ == 0)
{
v___x_1437_ = v___x_1434_;
goto v_reusejp_1436_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v_a_1432_);
v___x_1437_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1436_;
}
v_reusejp_1436_:
{
return v___x_1437_;
}
}
}
}
else
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1447_; 
lean_del_object(v___x_1359_);
lean_dec(v_snd_1357_);
lean_dec_ref(v_c_1339_);
lean_dec_ref(v___x_1338_);
v_a_1440_ = lean_ctor_get(v___x_1369_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1369_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1442_ = v___x_1369_;
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1369_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1445_; 
if (v_isShared_1443_ == 0)
{
v___x_1445_ = v___x_1442_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_a_1440_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v___x_1450_ = _args[0];
lean_object* v_c_1451_ = _args[1];
lean_object* v_as_1452_ = _args[2];
lean_object* v_sz_1453_ = _args[3];
lean_object* v_i_1454_ = _args[4];
lean_object* v_b_1455_ = _args[5];
lean_object* v___y_1456_ = _args[6];
lean_object* v___y_1457_ = _args[7];
lean_object* v___y_1458_ = _args[8];
lean_object* v___y_1459_ = _args[9];
lean_object* v___y_1460_ = _args[10];
lean_object* v___y_1461_ = _args[11];
lean_object* v___y_1462_ = _args[12];
lean_object* v___y_1463_ = _args[13];
lean_object* v___y_1464_ = _args[14];
lean_object* v___y_1465_ = _args[15];
lean_object* v___y_1466_ = _args[16];
_start:
{
size_t v_sz_boxed_1467_; size_t v_i_boxed_1468_; lean_object* v_res_1469_; 
v_sz_boxed_1467_ = lean_unbox_usize(v_sz_1453_);
lean_dec(v_sz_1453_);
v_i_boxed_1468_ = lean_unbox_usize(v_i_1454_);
lean_dec(v_i_1454_);
v_res_1469_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4(v___x_1450_, v_c_1451_, v_as_1452_, v_sz_boxed_1467_, v_i_boxed_1468_, v_b_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v___y_1457_);
lean_dec(v___y_1456_);
lean_dec_ref(v_as_1452_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1(lean_object* v___x_1473_, lean_object* v_c_1474_, lean_object* v_as_1475_, size_t v_sz_1476_, size_t v_i_1477_, lean_object* v_b_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_){
_start:
{
uint8_t v___x_1490_; 
v___x_1490_ = lean_usize_dec_lt(v_i_1477_, v_sz_1476_);
if (v___x_1490_ == 0)
{
lean_object* v___x_1491_; 
lean_dec_ref(v_c_1474_);
lean_dec_ref(v___x_1473_);
v___x_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1491_, 0, v_b_1478_);
return v___x_1491_;
}
else
{
lean_object* v_snd_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1583_; 
v_snd_1492_ = lean_ctor_get(v_b_1478_, 1);
v_isSharedCheck_1583_ = !lean_is_exclusive(v_b_1478_);
if (v_isSharedCheck_1583_ == 0)
{
lean_object* v_unused_1584_; 
v_unused_1584_ = lean_ctor_get(v_b_1478_, 0);
lean_dec(v_unused_1584_);
v___x_1494_ = v_b_1478_;
v_isShared_1495_ = v_isSharedCheck_1583_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_snd_1492_);
lean_dec(v_b_1478_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1583_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v_a_1496_; lean_object* v_p_1497_; lean_object* v___x_1498_; uint8_t v___x_1499_; 
v_a_1496_ = lean_array_uget_borrowed(v_as_1475_, v_i_1477_);
v_p_1497_ = lean_ctor_get(v_a_1496_, 0);
v___x_1498_ = lean_box(0);
v___x_1499_ = l_Int_Linear_Poly_isNegEq(v___x_1473_, v_p_1497_);
if (v___x_1499_ == 0)
{
lean_object* v___x_1500_; size_t v___x_1501_; size_t v___x_1502_; lean_object* v___x_1503_; 
lean_del_object(v___x_1494_);
lean_dec(v_snd_1492_);
v___x_1500_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1___closed__0));
v___x_1501_ = ((size_t)1ULL);
v___x_1502_ = lean_usize_add(v_i_1477_, v___x_1501_);
v___x_1503_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4(v___x_1473_, v_c_1474_, v_as_1475_, v_sz_1476_, v___x_1502_, v___x_1500_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
return v___x_1503_;
}
else
{
lean_object* v___x_1504_; 
lean_inc(v_a_1496_);
v___x_1504_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_1496_, v___y_1479_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v___x_1505_; lean_object* v___x_1506_; 
lean_dec_ref(v___x_1504_);
v___x_1505_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_1506_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_1505_, v___y_1487_);
if (lean_obj_tag(v___x_1506_) == 0)
{
lean_object* v_a_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___y_1511_; lean_object* v___y_1512_; lean_object* v___y_1513_; lean_object* v___y_1514_; lean_object* v___y_1515_; lean_object* v___y_1516_; lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; uint8_t v___x_1545_; 
v_a_1507_ = lean_ctor_get(v___x_1506_, 0);
lean_inc(v_a_1507_);
lean_dec_ref(v___x_1506_);
lean_inc(v_a_1496_);
v___x_1508_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1508_, 0, v_c_1474_);
lean_ctor_set(v___x_1508_, 1, v_a_1496_);
v___x_1509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1473_);
lean_ctor_set(v___x_1509_, 1, v___x_1508_);
v___x_1545_ = lean_unbox(v_a_1507_);
lean_dec(v_a_1507_);
if (v___x_1545_ == 0)
{
v___y_1511_ = v___y_1479_;
v___y_1512_ = v___y_1480_;
v___y_1513_ = v___y_1481_;
v___y_1514_ = v___y_1482_;
v___y_1515_ = v___y_1483_;
v___y_1516_ = v___y_1484_;
v___y_1517_ = v___y_1485_;
v___y_1518_ = v___y_1486_;
v___y_1519_ = v___y_1487_;
v___y_1520_ = v___y_1488_;
goto v___jp_1510_;
}
else
{
lean_object* v___x_1546_; 
lean_inc_ref(v___x_1509_);
v___x_1546_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_1509_, v___y_1479_, v___y_1487_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
lean_inc(v_a_1547_);
lean_dec_ref(v___x_1546_);
v___x_1548_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__6);
v___x_1549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1548_);
lean_ctor_set(v___x_1549_, 1, v_a_1547_);
v___x_1550_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1___redArg(v___x_1505_, v___x_1549_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_dec_ref(v___x_1550_);
v___y_1511_ = v___y_1479_;
v___y_1512_ = v___y_1480_;
v___y_1513_ = v___y_1481_;
v___y_1514_ = v___y_1482_;
v___y_1515_ = v___y_1483_;
v___y_1516_ = v___y_1484_;
v___y_1517_ = v___y_1485_;
v___y_1518_ = v___y_1486_;
v___y_1519_ = v___y_1487_;
v___y_1520_ = v___y_1488_;
goto v___jp_1510_;
}
else
{
lean_object* v_a_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1558_; 
lean_dec_ref(v___x_1509_);
lean_del_object(v___x_1494_);
lean_dec(v_snd_1492_);
v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1558_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1558_ == 0)
{
v___x_1553_ = v___x_1550_;
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_dec(v___x_1550_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1558_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1556_; 
if (v_isShared_1554_ == 0)
{
v___x_1556_ = v___x_1553_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v_a_1551_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
}
else
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1566_; 
lean_dec_ref(v___x_1509_);
lean_del_object(v___x_1494_);
lean_dec(v_snd_1492_);
v_a_1559_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1566_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1566_ == 0)
{
v___x_1561_ = v___x_1546_;
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1546_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1566_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1564_; 
if (v_isShared_1562_ == 0)
{
v___x_1564_ = v___x_1561_;
goto v_reusejp_1563_;
}
else
{
lean_object* v_reuseFailAlloc_1565_; 
v_reuseFailAlloc_1565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1565_, 0, v_a_1559_);
v___x_1564_ = v_reuseFailAlloc_1565_;
goto v_reusejp_1563_;
}
v_reusejp_1563_:
{
return v___x_1564_;
}
}
}
}
v___jp_1510_:
{
lean_object* v___x_1521_; 
lean_inc(v___y_1520_);
lean_inc_ref(v___y_1519_);
lean_inc(v___y_1518_);
lean_inc_ref(v___y_1517_);
lean_inc(v___y_1516_);
lean_inc_ref(v___y_1515_);
lean_inc(v___y_1514_);
lean_inc_ref(v___y_1513_);
lean_inc(v___y_1512_);
lean_inc(v___y_1511_);
v___x_1521_ = lean_grind_cutsat_assert_eq(v___x_1509_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1535_; 
v_isSharedCheck_1535_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1535_ == 0)
{
lean_object* v_unused_1536_; 
v_unused_1536_ = lean_ctor_get(v___x_1521_, 0);
lean_dec(v_unused_1536_);
v___x_1523_ = v___x_1521_;
v_isShared_1524_ = v_isSharedCheck_1535_;
goto v_resetjp_1522_;
}
else
{
lean_dec(v___x_1521_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1535_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1528_; 
v___x_1525_ = lean_box(v___x_1499_);
v___x_1526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
if (v_isShared_1495_ == 0)
{
lean_ctor_set(v___x_1494_, 1, v___x_1498_);
lean_ctor_set(v___x_1494_, 0, v___x_1526_);
v___x_1528_ = v___x_1494_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1534_; 
v_reuseFailAlloc_1534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1534_, 0, v___x_1526_);
lean_ctor_set(v_reuseFailAlloc_1534_, 1, v___x_1498_);
v___x_1528_ = v_reuseFailAlloc_1534_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1532_; 
v___x_1529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1528_);
v___x_1530_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1529_);
lean_ctor_set(v___x_1530_, 1, v_snd_1492_);
if (v_isShared_1524_ == 0)
{
lean_ctor_set(v___x_1523_, 0, v___x_1530_);
v___x_1532_ = v___x_1523_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v___x_1530_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
}
else
{
lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1544_; 
lean_del_object(v___x_1494_);
lean_dec(v_snd_1492_);
v_a_1537_ = lean_ctor_get(v___x_1521_, 0);
v_isSharedCheck_1544_ = !lean_is_exclusive(v___x_1521_);
if (v_isSharedCheck_1544_ == 0)
{
v___x_1539_ = v___x_1521_;
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1521_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1544_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
lean_object* v___x_1542_; 
if (v_isShared_1540_ == 0)
{
v___x_1542_ = v___x_1539_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_a_1537_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
}
}
}
else
{
lean_object* v_a_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1574_; 
lean_del_object(v___x_1494_);
lean_dec(v_snd_1492_);
lean_dec_ref(v_c_1474_);
lean_dec_ref(v___x_1473_);
v_a_1567_ = lean_ctor_get(v___x_1506_, 0);
v_isSharedCheck_1574_ = !lean_is_exclusive(v___x_1506_);
if (v_isSharedCheck_1574_ == 0)
{
v___x_1569_ = v___x_1506_;
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_a_1567_);
lean_dec(v___x_1506_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1574_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1572_; 
if (v_isShared_1570_ == 0)
{
v___x_1572_ = v___x_1569_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_a_1567_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
}
else
{
lean_object* v_a_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1582_; 
lean_del_object(v___x_1494_);
lean_dec(v_snd_1492_);
lean_dec_ref(v_c_1474_);
lean_dec_ref(v___x_1473_);
v_a_1575_ = lean_ctor_get(v___x_1504_, 0);
v_isSharedCheck_1582_ = !lean_is_exclusive(v___x_1504_);
if (v_isSharedCheck_1582_ == 0)
{
v___x_1577_ = v___x_1504_;
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_a_1575_);
lean_dec(v___x_1504_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1582_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
lean_object* v___x_1580_; 
if (v_isShared_1578_ == 0)
{
v___x_1580_ = v___x_1577_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1575_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v___x_1585_ = _args[0];
lean_object* v_c_1586_ = _args[1];
lean_object* v_as_1587_ = _args[2];
lean_object* v_sz_1588_ = _args[3];
lean_object* v_i_1589_ = _args[4];
lean_object* v_b_1590_ = _args[5];
lean_object* v___y_1591_ = _args[6];
lean_object* v___y_1592_ = _args[7];
lean_object* v___y_1593_ = _args[8];
lean_object* v___y_1594_ = _args[9];
lean_object* v___y_1595_ = _args[10];
lean_object* v___y_1596_ = _args[11];
lean_object* v___y_1597_ = _args[12];
lean_object* v___y_1598_ = _args[13];
lean_object* v___y_1599_ = _args[14];
lean_object* v___y_1600_ = _args[15];
lean_object* v___y_1601_ = _args[16];
_start:
{
size_t v_sz_boxed_1602_; size_t v_i_boxed_1603_; lean_object* v_res_1604_; 
v_sz_boxed_1602_ = lean_unbox_usize(v_sz_1588_);
lean_dec(v_sz_1588_);
v_i_boxed_1603_ = lean_unbox_usize(v_i_1589_);
lean_dec(v_i_1589_);
v_res_1604_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1(v___x_1585_, v_c_1586_, v_as_1587_, v_sz_boxed_1602_, v_i_boxed_1603_, v_b_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
lean_dec(v___y_1594_);
lean_dec_ref(v___y_1593_);
lean_dec(v___y_1592_);
lean_dec(v___y_1591_);
lean_dec_ref(v_as_1587_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0(lean_object* v___x_1605_, lean_object* v_c_1606_, lean_object* v_t_1607_, lean_object* v_init_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_){
_start:
{
lean_object* v_root_1620_; lean_object* v_tail_1621_; lean_object* v___x_1622_; 
v_root_1620_ = lean_ctor_get(v_t_1607_, 0);
lean_inc_ref(v_root_1620_);
v_tail_1621_ = lean_ctor_get(v_t_1607_, 1);
lean_inc_ref(v_tail_1621_);
lean_dec_ref(v_t_1607_);
lean_inc_ref(v_init_1608_);
lean_inc_ref(v_c_1606_);
lean_inc_ref(v___x_1605_);
v___x_1622_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(v___x_1605_, v_c_1606_, v_init_1608_, v_root_1620_, v_init_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_);
lean_dec_ref(v_init_1608_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1659_; 
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1659_ == 0)
{
v___x_1625_ = v___x_1622_;
v_isShared_1626_ = v_isSharedCheck_1659_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1622_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1659_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
if (lean_obj_tag(v_a_1623_) == 0)
{
lean_object* v_a_1627_; lean_object* v___x_1629_; 
lean_dec_ref(v_tail_1621_);
lean_dec_ref(v_c_1606_);
lean_dec_ref(v___x_1605_);
v_a_1627_ = lean_ctor_get(v_a_1623_, 0);
lean_inc(v_a_1627_);
lean_dec_ref(v_a_1623_);
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 0, v_a_1627_);
v___x_1629_ = v___x_1625_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_a_1627_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
else
{
lean_object* v_a_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; size_t v_sz_1634_; size_t v___x_1635_; lean_object* v___x_1636_; 
lean_del_object(v___x_1625_);
v_a_1631_ = lean_ctor_get(v_a_1623_, 0);
lean_inc(v_a_1631_);
lean_dec_ref(v_a_1623_);
v___x_1632_ = lean_box(0);
v___x_1633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1633_, 0, v___x_1632_);
lean_ctor_set(v___x_1633_, 1, v_a_1631_);
v_sz_1634_ = lean_array_size(v_tail_1621_);
v___x_1635_ = ((size_t)0ULL);
v___x_1636_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1(v___x_1605_, v_c_1606_, v_tail_1621_, v_sz_1634_, v___x_1635_, v___x_1633_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_);
lean_dec_ref(v_tail_1621_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v_a_1637_; lean_object* v___x_1639_; uint8_t v_isShared_1640_; uint8_t v_isSharedCheck_1650_; 
v_a_1637_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1639_ = v___x_1636_;
v_isShared_1640_ = v_isSharedCheck_1650_;
goto v_resetjp_1638_;
}
else
{
lean_inc(v_a_1637_);
lean_dec(v___x_1636_);
v___x_1639_ = lean_box(0);
v_isShared_1640_ = v_isSharedCheck_1650_;
goto v_resetjp_1638_;
}
v_resetjp_1638_:
{
lean_object* v_fst_1641_; 
v_fst_1641_ = lean_ctor_get(v_a_1637_, 0);
if (lean_obj_tag(v_fst_1641_) == 0)
{
lean_object* v_snd_1642_; lean_object* v___x_1644_; 
v_snd_1642_ = lean_ctor_get(v_a_1637_, 1);
lean_inc(v_snd_1642_);
lean_dec(v_a_1637_);
if (v_isShared_1640_ == 0)
{
lean_ctor_set(v___x_1639_, 0, v_snd_1642_);
v___x_1644_ = v___x_1639_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_snd_1642_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
else
{
lean_object* v_val_1646_; lean_object* v___x_1648_; 
lean_inc_ref(v_fst_1641_);
lean_dec(v_a_1637_);
v_val_1646_ = lean_ctor_get(v_fst_1641_, 0);
lean_inc(v_val_1646_);
lean_dec_ref(v_fst_1641_);
if (v_isShared_1640_ == 0)
{
lean_ctor_set(v___x_1639_, 0, v_val_1646_);
v___x_1648_ = v___x_1639_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_val_1646_);
v___x_1648_ = v_reuseFailAlloc_1649_;
goto v_reusejp_1647_;
}
v_reusejp_1647_:
{
return v___x_1648_;
}
}
}
}
else
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1658_; 
v_a_1651_ = lean_ctor_get(v___x_1636_, 0);
v_isSharedCheck_1658_ = !lean_is_exclusive(v___x_1636_);
if (v_isSharedCheck_1658_ == 0)
{
v___x_1653_ = v___x_1636_;
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1636_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1658_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1656_; 
if (v_isShared_1654_ == 0)
{
v___x_1656_ = v___x_1653_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1657_; 
v_reuseFailAlloc_1657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1657_, 0, v_a_1651_);
v___x_1656_ = v_reuseFailAlloc_1657_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
return v___x_1656_;
}
}
}
}
}
}
else
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1667_; 
lean_dec_ref(v_tail_1621_);
lean_dec_ref(v_c_1606_);
lean_dec_ref(v___x_1605_);
v_a_1660_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1662_ = v___x_1622_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1622_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1663_ == 0)
{
v___x_1665_ = v___x_1662_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1666_; 
v_reuseFailAlloc_1666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1666_, 0, v_a_1660_);
v___x_1665_ = v_reuseFailAlloc_1666_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
return v___x_1665_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0___boxed(lean_object* v___x_1668_, lean_object* v_c_1669_, lean_object* v_t_1670_, lean_object* v_init_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v_res_1683_; 
v_res_1683_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0(v___x_1668_, v_c_1669_, v_t_1670_, v_init_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
lean_dec(v___y_1673_);
lean_dec(v___y_1672_);
return v_res_1683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq(lean_object* v_c_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_, lean_object* v_a_1689_, lean_object* v_a_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_){
_start:
{
lean_object* v_p_1696_; 
v_p_1696_ = lean_ctor_get(v_c_1684_, 0);
if (lean_obj_tag(v_p_1696_) == 1)
{
lean_object* v_k_1697_; lean_object* v_v_1698_; lean_object* v___x_1699_; 
lean_inc_ref(v_p_1696_);
v_k_1697_ = lean_ctor_get(v_p_1696_, 0);
v_v_1698_ = lean_ctor_get(v_p_1696_, 1);
v___x_1699_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1685_, v_a_1693_);
if (lean_obj_tag(v___x_1699_) == 0)
{
lean_object* v_a_1700_; lean_object* v___y_1702_; lean_object* v___x_1728_; uint8_t v___x_1729_; 
v_a_1700_ = lean_ctor_get(v___x_1699_, 0);
lean_inc(v_a_1700_);
lean_dec_ref(v___x_1699_);
v___x_1728_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6);
v___x_1729_ = lean_int_dec_lt(v_k_1697_, v___x_1728_);
if (v___x_1729_ == 0)
{
lean_object* v_lowers_1730_; lean_object* v_size_1731_; lean_object* v___x_1732_; uint8_t v___x_1733_; 
v_lowers_1730_ = lean_ctor_get(v_a_1700_, 7);
lean_inc_ref(v_lowers_1730_);
lean_dec(v_a_1700_);
v_size_1731_ = lean_ctor_get(v_lowers_1730_, 2);
v___x_1732_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0);
v___x_1733_ = lean_nat_dec_lt(v_v_1698_, v_size_1731_);
if (v___x_1733_ == 0)
{
lean_object* v___x_1734_; 
lean_dec_ref(v_lowers_1730_);
v___x_1734_ = l_outOfBounds___redArg(v___x_1732_);
v___y_1702_ = v___x_1734_;
goto v___jp_1701_;
}
else
{
lean_object* v___x_1735_; 
v___x_1735_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1732_, v_lowers_1730_, v_v_1698_);
v___y_1702_ = v___x_1735_;
goto v___jp_1701_;
}
}
else
{
lean_object* v_uppers_1736_; lean_object* v_size_1737_; lean_object* v___x_1738_; uint8_t v___x_1739_; 
v_uppers_1736_ = lean_ctor_get(v_a_1700_, 8);
lean_inc_ref(v_uppers_1736_);
lean_dec(v_a_1700_);
v_size_1737_ = lean_ctor_get(v_uppers_1736_, 2);
v___x_1738_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0);
v___x_1739_ = lean_nat_dec_lt(v_v_1698_, v_size_1737_);
if (v___x_1739_ == 0)
{
lean_object* v___x_1740_; 
lean_dec_ref(v_uppers_1736_);
v___x_1740_ = l_outOfBounds___redArg(v___x_1738_);
v___y_1702_ = v___x_1740_;
goto v___jp_1701_;
}
else
{
lean_object* v___x_1741_; 
v___x_1741_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1738_, v_uppers_1736_, v_v_1698_);
v___y_1702_ = v___x_1741_;
goto v___jp_1701_;
}
}
v___jp_1701_:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1703_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__0));
v___x_1704_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0(v_p_1696_, v_c_1684_, v___y_1702_, v___x_1703_, v_a_1685_, v_a_1686_, v_a_1687_, v_a_1688_, v_a_1689_, v_a_1690_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_);
if (lean_obj_tag(v___x_1704_) == 0)
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1719_; 
v_a_1705_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1719_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1719_ == 0)
{
v___x_1707_ = v___x_1704_;
v_isShared_1708_ = v_isSharedCheck_1719_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1704_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1719_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v_fst_1709_; 
v_fst_1709_ = lean_ctor_get(v_a_1705_, 0);
lean_inc(v_fst_1709_);
lean_dec(v_a_1705_);
if (lean_obj_tag(v_fst_1709_) == 0)
{
uint8_t v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1713_; 
v___x_1710_ = 0;
v___x_1711_ = lean_box(v___x_1710_);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 0, v___x_1711_);
v___x_1713_ = v___x_1707_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v___x_1711_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
else
{
lean_object* v_val_1715_; lean_object* v___x_1717_; 
v_val_1715_ = lean_ctor_get(v_fst_1709_, 0);
lean_inc(v_val_1715_);
lean_dec_ref(v_fst_1709_);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 0, v_val_1715_);
v___x_1717_ = v___x_1707_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1718_; 
v_reuseFailAlloc_1718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_val_1715_);
v___x_1717_ = v_reuseFailAlloc_1718_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
return v___x_1717_;
}
}
}
}
else
{
lean_object* v_a_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1727_; 
v_a_1720_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1727_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1727_ == 0)
{
v___x_1722_ = v___x_1704_;
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_a_1720_);
lean_dec(v___x_1704_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1727_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v___x_1725_; 
if (v_isShared_1723_ == 0)
{
v___x_1725_ = v___x_1722_;
goto v_reusejp_1724_;
}
else
{
lean_object* v_reuseFailAlloc_1726_; 
v_reuseFailAlloc_1726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_a_1720_);
v___x_1725_ = v_reuseFailAlloc_1726_;
goto v_reusejp_1724_;
}
v_reusejp_1724_:
{
return v___x_1725_;
}
}
}
}
}
else
{
lean_object* v_a_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1749_; 
lean_dec_ref(v_p_1696_);
lean_dec_ref(v_c_1684_);
v_a_1742_ = lean_ctor_get(v___x_1699_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1699_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1744_ = v___x_1699_;
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_a_1742_);
lean_dec(v___x_1699_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1747_; 
if (v_isShared_1745_ == 0)
{
v___x_1747_ = v___x_1744_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_a_1742_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
}
else
{
lean_object* v___x_1750_; 
v___x_1750_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_1684_, v_a_1685_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_);
return v___x_1750_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___boxed(lean_object* v_c_1751_, lean_object* v_a_1752_, lean_object* v_a_1753_, lean_object* v_a_1754_, lean_object* v_a_1755_, lean_object* v_a_1756_, lean_object* v_a_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq(v_c_1751_, v_a_1752_, v_a_1753_, v_a_1754_, v_a_1755_, v_a_1756_, v_a_1757_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_);
lean_dec(v_a_1761_);
lean_dec_ref(v_a_1760_);
lean_dec(v_a_1759_);
lean_dec_ref(v_a_1758_);
lean_dec(v_a_1757_);
lean_dec_ref(v_a_1756_);
lean_dec(v_a_1755_);
lean_dec_ref(v_a_1754_);
lean_dec(v_a_1753_);
lean_dec(v_a_1752_);
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(lean_object* v___x_1764_, lean_object* v_as_1765_, size_t v_i_1766_, size_t v_stop_1767_, lean_object* v_b_1768_){
_start:
{
lean_object* v___y_1770_; uint8_t v___x_1774_; 
v___x_1774_ = lean_usize_dec_eq(v_i_1766_, v_stop_1767_);
if (v___x_1774_ == 0)
{
lean_object* v___x_1775_; lean_object* v_p_1776_; uint8_t v___x_1777_; 
v___x_1775_ = lean_array_uget_borrowed(v_as_1765_, v_i_1766_);
v_p_1776_ = lean_ctor_get(v___x_1775_, 0);
v___x_1777_ = l_Int_Linear_instBEqPoly_beq(v_p_1776_, v___x_1764_);
if (v___x_1777_ == 0)
{
lean_object* v___x_1778_; 
lean_inc(v___x_1775_);
v___x_1778_ = l_Lean_PersistentArray_push___redArg(v_b_1768_, v___x_1775_);
v___y_1770_ = v___x_1778_;
goto v___jp_1769_;
}
else
{
v___y_1770_ = v_b_1768_;
goto v___jp_1769_;
}
}
else
{
return v_b_1768_;
}
v___jp_1769_:
{
size_t v___x_1771_; size_t v___x_1772_; 
v___x_1771_ = ((size_t)1ULL);
v___x_1772_ = lean_usize_add(v_i_1766_, v___x_1771_);
v_i_1766_ = v___x_1772_;
v_b_1768_ = v___y_1770_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1___boxed(lean_object* v___x_1779_, lean_object* v_as_1780_, lean_object* v_i_1781_, lean_object* v_stop_1782_, lean_object* v_b_1783_){
_start:
{
size_t v_i_boxed_1784_; size_t v_stop_boxed_1785_; lean_object* v_res_1786_; 
v_i_boxed_1784_ = lean_unbox_usize(v_i_1781_);
lean_dec(v_i_1781_);
v_stop_boxed_1785_ = lean_unbox_usize(v_stop_1782_);
lean_dec(v_stop_1782_);
v_res_1786_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1779_, v_as_1780_, v_i_boxed_1784_, v_stop_boxed_1785_, v_b_1783_);
lean_dec_ref(v_as_1780_);
lean_dec_ref(v___x_1779_);
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(lean_object* v___x_1787_, lean_object* v_x_1788_, lean_object* v_x_1789_){
_start:
{
if (lean_obj_tag(v_x_1788_) == 0)
{
lean_object* v_cs_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; uint8_t v___x_1793_; 
v_cs_1790_ = lean_ctor_get(v_x_1788_, 0);
v___x_1791_ = lean_unsigned_to_nat(0u);
v___x_1792_ = lean_array_get_size(v_cs_1790_);
v___x_1793_ = lean_nat_dec_lt(v___x_1791_, v___x_1792_);
if (v___x_1793_ == 0)
{
return v_x_1789_;
}
else
{
uint8_t v___x_1794_; 
v___x_1794_ = lean_nat_dec_le(v___x_1792_, v___x_1792_);
if (v___x_1794_ == 0)
{
if (v___x_1793_ == 0)
{
return v_x_1789_;
}
else
{
size_t v___x_1795_; size_t v___x_1796_; lean_object* v___x_1797_; 
v___x_1795_ = ((size_t)0ULL);
v___x_1796_ = lean_usize_of_nat(v___x_1792_);
v___x_1797_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1787_, v_cs_1790_, v___x_1795_, v___x_1796_, v_x_1789_);
return v___x_1797_;
}
}
else
{
size_t v___x_1798_; size_t v___x_1799_; lean_object* v___x_1800_; 
v___x_1798_ = ((size_t)0ULL);
v___x_1799_ = lean_usize_of_nat(v___x_1792_);
v___x_1800_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1787_, v_cs_1790_, v___x_1798_, v___x_1799_, v_x_1789_);
return v___x_1800_;
}
}
}
else
{
lean_object* v_vs_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; uint8_t v___x_1804_; 
v_vs_1801_ = lean_ctor_get(v_x_1788_, 0);
v___x_1802_ = lean_unsigned_to_nat(0u);
v___x_1803_ = lean_array_get_size(v_vs_1801_);
v___x_1804_ = lean_nat_dec_lt(v___x_1802_, v___x_1803_);
if (v___x_1804_ == 0)
{
return v_x_1789_;
}
else
{
uint8_t v___x_1805_; 
v___x_1805_ = lean_nat_dec_le(v___x_1803_, v___x_1803_);
if (v___x_1805_ == 0)
{
if (v___x_1804_ == 0)
{
return v_x_1789_;
}
else
{
size_t v___x_1806_; size_t v___x_1807_; lean_object* v___x_1808_; 
v___x_1806_ = ((size_t)0ULL);
v___x_1807_ = lean_usize_of_nat(v___x_1803_);
v___x_1808_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1787_, v_vs_1801_, v___x_1806_, v___x_1807_, v_x_1789_);
return v___x_1808_;
}
}
else
{
size_t v___x_1809_; size_t v___x_1810_; lean_object* v___x_1811_; 
v___x_1809_ = ((size_t)0ULL);
v___x_1810_ = lean_usize_of_nat(v___x_1803_);
v___x_1811_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1787_, v_vs_1801_, v___x_1809_, v___x_1810_, v_x_1789_);
return v___x_1811_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(lean_object* v___x_1812_, lean_object* v_as_1813_, size_t v_i_1814_, size_t v_stop_1815_, lean_object* v_b_1816_){
_start:
{
uint8_t v___x_1817_; 
v___x_1817_ = lean_usize_dec_eq(v_i_1814_, v_stop_1815_);
if (v___x_1817_ == 0)
{
lean_object* v___x_1818_; lean_object* v___x_1819_; size_t v___x_1820_; size_t v___x_1821_; 
v___x_1818_ = lean_array_uget_borrowed(v_as_1813_, v_i_1814_);
v___x_1819_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(v___x_1812_, v___x_1818_, v_b_1816_);
v___x_1820_ = ((size_t)1ULL);
v___x_1821_ = lean_usize_add(v_i_1814_, v___x_1820_);
v_i_1814_ = v___x_1821_;
v_b_1816_ = v___x_1819_;
goto _start;
}
else
{
return v_b_1816_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v___x_1823_, lean_object* v_as_1824_, lean_object* v_i_1825_, lean_object* v_stop_1826_, lean_object* v_b_1827_){
_start:
{
size_t v_i_boxed_1828_; size_t v_stop_boxed_1829_; lean_object* v_res_1830_; 
v_i_boxed_1828_ = lean_unbox_usize(v_i_1825_);
lean_dec(v_i_1825_);
v_stop_boxed_1829_ = lean_unbox_usize(v_stop_1826_);
lean_dec(v_stop_1826_);
v_res_1830_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1823_, v_as_1824_, v_i_boxed_1828_, v_stop_boxed_1829_, v_b_1827_);
lean_dec_ref(v_as_1824_);
lean_dec_ref(v___x_1823_);
return v_res_1830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2___boxed(lean_object* v___x_1831_, lean_object* v_x_1832_, lean_object* v_x_1833_){
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(v___x_1831_, v_x_1832_, v_x_1833_);
lean_dec_ref(v_x_1832_);
lean_dec_ref(v___x_1831_);
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(lean_object* v___x_1835_, lean_object* v_x_1836_, size_t v_x_1837_, size_t v_x_1838_, lean_object* v_x_1839_){
_start:
{
if (lean_obj_tag(v_x_1836_) == 0)
{
lean_object* v_cs_1840_; lean_object* v___x_1841_; size_t v___x_1842_; lean_object* v_j_1843_; lean_object* v___x_1844_; size_t v___x_1845_; size_t v___x_1846_; size_t v___x_1847_; size_t v___x_1848_; size_t v___x_1849_; size_t v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; uint8_t v___x_1855_; 
v_cs_1840_ = lean_ctor_get(v_x_1836_, 0);
v___x_1841_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0);
v___x_1842_ = lean_usize_shift_right(v_x_1837_, v_x_1838_);
v_j_1843_ = lean_usize_to_nat(v___x_1842_);
v___x_1844_ = lean_array_get_borrowed(v___x_1841_, v_cs_1840_, v_j_1843_);
v___x_1845_ = ((size_t)1ULL);
v___x_1846_ = lean_usize_shift_left(v___x_1845_, v_x_1838_);
v___x_1847_ = lean_usize_sub(v___x_1846_, v___x_1845_);
v___x_1848_ = lean_usize_land(v_x_1837_, v___x_1847_);
v___x_1849_ = ((size_t)5ULL);
v___x_1850_ = lean_usize_sub(v_x_1838_, v___x_1849_);
v___x_1851_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(v___x_1835_, v___x_1844_, v___x_1848_, v___x_1850_, v_x_1839_);
v___x_1852_ = lean_unsigned_to_nat(1u);
v___x_1853_ = lean_nat_add(v_j_1843_, v___x_1852_);
lean_dec(v_j_1843_);
v___x_1854_ = lean_array_get_size(v_cs_1840_);
v___x_1855_ = lean_nat_dec_lt(v___x_1853_, v___x_1854_);
if (v___x_1855_ == 0)
{
lean_dec(v___x_1853_);
return v___x_1851_;
}
else
{
uint8_t v___x_1856_; 
v___x_1856_ = lean_nat_dec_le(v___x_1854_, v___x_1854_);
if (v___x_1856_ == 0)
{
if (v___x_1855_ == 0)
{
lean_dec(v___x_1853_);
return v___x_1851_;
}
else
{
size_t v___x_1857_; size_t v___x_1858_; lean_object* v___x_1859_; 
v___x_1857_ = lean_usize_of_nat(v___x_1853_);
lean_dec(v___x_1853_);
v___x_1858_ = lean_usize_of_nat(v___x_1854_);
v___x_1859_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1835_, v_cs_1840_, v___x_1857_, v___x_1858_, v___x_1851_);
return v___x_1859_;
}
}
else
{
size_t v___x_1860_; size_t v___x_1861_; lean_object* v___x_1862_; 
v___x_1860_ = lean_usize_of_nat(v___x_1853_);
lean_dec(v___x_1853_);
v___x_1861_ = lean_usize_of_nat(v___x_1854_);
v___x_1862_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1835_, v_cs_1840_, v___x_1860_, v___x_1861_, v___x_1851_);
return v___x_1862_;
}
}
}
else
{
lean_object* v_vs_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; uint8_t v___x_1866_; 
v_vs_1863_ = lean_ctor_get(v_x_1836_, 0);
v___x_1864_ = lean_usize_to_nat(v_x_1837_);
v___x_1865_ = lean_array_get_size(v_vs_1863_);
v___x_1866_ = lean_nat_dec_lt(v___x_1864_, v___x_1865_);
if (v___x_1866_ == 0)
{
lean_dec(v___x_1864_);
return v_x_1839_;
}
else
{
uint8_t v___x_1867_; 
v___x_1867_ = lean_nat_dec_le(v___x_1865_, v___x_1865_);
if (v___x_1867_ == 0)
{
if (v___x_1866_ == 0)
{
lean_dec(v___x_1864_);
return v_x_1839_;
}
else
{
size_t v___x_1868_; size_t v___x_1869_; lean_object* v___x_1870_; 
v___x_1868_ = lean_usize_of_nat(v___x_1864_);
lean_dec(v___x_1864_);
v___x_1869_ = lean_usize_of_nat(v___x_1865_);
v___x_1870_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1835_, v_vs_1863_, v___x_1868_, v___x_1869_, v_x_1839_);
return v___x_1870_;
}
}
else
{
size_t v___x_1871_; size_t v___x_1872_; lean_object* v___x_1873_; 
v___x_1871_ = lean_usize_of_nat(v___x_1864_);
lean_dec(v___x_1864_);
v___x_1872_ = lean_usize_of_nat(v___x_1865_);
v___x_1873_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1835_, v_vs_1863_, v___x_1871_, v___x_1872_, v_x_1839_);
return v___x_1873_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0___boxed(lean_object* v___x_1874_, lean_object* v_x_1875_, lean_object* v_x_1876_, lean_object* v_x_1877_, lean_object* v_x_1878_){
_start:
{
size_t v_x_21647__boxed_1879_; size_t v_x_21648__boxed_1880_; lean_object* v_res_1881_; 
v_x_21647__boxed_1879_ = lean_unbox_usize(v_x_1876_);
lean_dec(v_x_1876_);
v_x_21648__boxed_1880_ = lean_unbox_usize(v_x_1877_);
lean_dec(v_x_1877_);
v_res_1881_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(v___x_1874_, v_x_1875_, v_x_21647__boxed_1879_, v_x_21648__boxed_1880_, v_x_1878_);
lean_dec_ref(v_x_1875_);
lean_dec_ref(v___x_1874_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(lean_object* v___x_1882_, lean_object* v_t_1883_, lean_object* v_init_1884_, lean_object* v_start_1885_){
_start:
{
lean_object* v___x_1886_; uint8_t v___x_1887_; 
v___x_1886_ = lean_unsigned_to_nat(0u);
v___x_1887_ = lean_nat_dec_eq(v_start_1885_, v___x_1886_);
if (v___x_1887_ == 0)
{
lean_object* v_root_1888_; lean_object* v_tail_1889_; size_t v_shift_1890_; lean_object* v_tailOff_1891_; uint8_t v___x_1892_; 
v_root_1888_ = lean_ctor_get(v_t_1883_, 0);
v_tail_1889_ = lean_ctor_get(v_t_1883_, 1);
v_shift_1890_ = lean_ctor_get_usize(v_t_1883_, 4);
v_tailOff_1891_ = lean_ctor_get(v_t_1883_, 3);
v___x_1892_ = lean_nat_dec_le(v_tailOff_1891_, v_start_1885_);
if (v___x_1892_ == 0)
{
size_t v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; uint8_t v___x_1896_; 
v___x_1893_ = lean_usize_of_nat(v_start_1885_);
v___x_1894_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(v___x_1882_, v_root_1888_, v___x_1893_, v_shift_1890_, v_init_1884_);
v___x_1895_ = lean_array_get_size(v_tail_1889_);
v___x_1896_ = lean_nat_dec_lt(v___x_1886_, v___x_1895_);
if (v___x_1896_ == 0)
{
return v___x_1894_;
}
else
{
uint8_t v___x_1897_; 
v___x_1897_ = lean_nat_dec_le(v___x_1895_, v___x_1895_);
if (v___x_1897_ == 0)
{
if (v___x_1896_ == 0)
{
return v___x_1894_;
}
else
{
size_t v___x_1898_; size_t v___x_1899_; lean_object* v___x_1900_; 
v___x_1898_ = ((size_t)0ULL);
v___x_1899_ = lean_usize_of_nat(v___x_1895_);
v___x_1900_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1882_, v_tail_1889_, v___x_1898_, v___x_1899_, v___x_1894_);
return v___x_1900_;
}
}
else
{
size_t v___x_1901_; size_t v___x_1902_; lean_object* v___x_1903_; 
v___x_1901_ = ((size_t)0ULL);
v___x_1902_ = lean_usize_of_nat(v___x_1895_);
v___x_1903_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1882_, v_tail_1889_, v___x_1901_, v___x_1902_, v___x_1894_);
return v___x_1903_;
}
}
}
else
{
lean_object* v___x_1904_; lean_object* v___x_1905_; uint8_t v___x_1906_; 
v___x_1904_ = lean_nat_sub(v_start_1885_, v_tailOff_1891_);
v___x_1905_ = lean_array_get_size(v_tail_1889_);
v___x_1906_ = lean_nat_dec_lt(v___x_1904_, v___x_1905_);
if (v___x_1906_ == 0)
{
lean_dec(v___x_1904_);
return v_init_1884_;
}
else
{
uint8_t v___x_1907_; 
v___x_1907_ = lean_nat_dec_le(v___x_1905_, v___x_1905_);
if (v___x_1907_ == 0)
{
if (v___x_1906_ == 0)
{
lean_dec(v___x_1904_);
return v_init_1884_;
}
else
{
size_t v___x_1908_; size_t v___x_1909_; lean_object* v___x_1910_; 
v___x_1908_ = lean_usize_of_nat(v___x_1904_);
lean_dec(v___x_1904_);
v___x_1909_ = lean_usize_of_nat(v___x_1905_);
v___x_1910_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1882_, v_tail_1889_, v___x_1908_, v___x_1909_, v_init_1884_);
return v___x_1910_;
}
}
else
{
size_t v___x_1911_; size_t v___x_1912_; lean_object* v___x_1913_; 
v___x_1911_ = lean_usize_of_nat(v___x_1904_);
lean_dec(v___x_1904_);
v___x_1912_ = lean_usize_of_nat(v___x_1905_);
v___x_1913_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1882_, v_tail_1889_, v___x_1911_, v___x_1912_, v_init_1884_);
return v___x_1913_;
}
}
}
}
else
{
lean_object* v_root_1914_; lean_object* v_tail_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; uint8_t v___x_1918_; 
v_root_1914_ = lean_ctor_get(v_t_1883_, 0);
v_tail_1915_ = lean_ctor_get(v_t_1883_, 1);
v___x_1916_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(v___x_1882_, v_root_1914_, v_init_1884_);
v___x_1917_ = lean_array_get_size(v_tail_1915_);
v___x_1918_ = lean_nat_dec_lt(v___x_1886_, v___x_1917_);
if (v___x_1918_ == 0)
{
return v___x_1916_;
}
else
{
uint8_t v___x_1919_; 
v___x_1919_ = lean_nat_dec_le(v___x_1917_, v___x_1917_);
if (v___x_1919_ == 0)
{
if (v___x_1918_ == 0)
{
return v___x_1916_;
}
else
{
size_t v___x_1920_; size_t v___x_1921_; lean_object* v___x_1922_; 
v___x_1920_ = ((size_t)0ULL);
v___x_1921_ = lean_usize_of_nat(v___x_1917_);
v___x_1922_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1882_, v_tail_1915_, v___x_1920_, v___x_1921_, v___x_1916_);
return v___x_1922_;
}
}
else
{
size_t v___x_1923_; size_t v___x_1924_; lean_object* v___x_1925_; 
v___x_1923_ = ((size_t)0ULL);
v___x_1924_ = lean_usize_of_nat(v___x_1917_);
v___x_1925_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1882_, v_tail_1915_, v___x_1923_, v___x_1924_, v___x_1916_);
return v___x_1925_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0___boxed(lean_object* v___x_1926_, lean_object* v_t_1927_, lean_object* v_init_1928_, lean_object* v_start_1929_){
_start:
{
lean_object* v_res_1930_; 
v_res_1930_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(v___x_1926_, v_t_1927_, v_init_1928_, v_start_1929_);
lean_dec(v_start_1929_);
lean_dec_ref(v_t_1927_);
lean_dec_ref(v___x_1926_);
return v_res_1930_;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1931_ = lean_unsigned_to_nat(32u);
v___x_1932_ = lean_mk_empty_array_with_capacity(v___x_1931_);
v___x_1933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1932_);
return v___x_1933_;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1934_ = ((size_t)5ULL);
v___x_1935_ = lean_unsigned_to_nat(0u);
v___x_1936_ = lean_unsigned_to_nat(32u);
v___x_1937_ = lean_mk_empty_array_with_capacity(v___x_1936_);
v___x_1938_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___redArg___closed__0, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___redArg___closed__0);
v___x_1939_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1939_, 0, v___x_1938_);
lean_ctor_set(v___x_1939_, 1, v___x_1937_);
lean_ctor_set(v___x_1939_, 2, v___x_1935_);
lean_ctor_set(v___x_1939_, 3, v___x_1935_);
lean_ctor_set_usize(v___x_1939_, 4, v___x_1934_);
return v___x_1939_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___redArg(lean_object* v___x_1940_, lean_object* v_x_1941_, size_t v_x_1942_, size_t v_x_1943_){
_start:
{
if (lean_obj_tag(v_x_1941_) == 0)
{
lean_object* v_cs_1944_; size_t v_j_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; uint8_t v___x_1948_; 
v_cs_1944_ = lean_ctor_get(v_x_1941_, 0);
v_j_1945_ = lean_usize_shift_right(v_x_1942_, v_x_1943_);
v___x_1946_ = lean_usize_to_nat(v_j_1945_);
v___x_1947_ = lean_array_get_size(v_cs_1944_);
v___x_1948_ = lean_nat_dec_lt(v___x_1946_, v___x_1947_);
if (v___x_1948_ == 0)
{
lean_dec(v___x_1946_);
return v_x_1941_;
}
else
{
lean_object* v___x_1950_; uint8_t v_isShared_1951_; uint8_t v_isSharedCheck_1966_; 
lean_inc_ref(v_cs_1944_);
v_isSharedCheck_1966_ = !lean_is_exclusive(v_x_1941_);
if (v_isSharedCheck_1966_ == 0)
{
lean_object* v_unused_1967_; 
v_unused_1967_ = lean_ctor_get(v_x_1941_, 0);
lean_dec(v_unused_1967_);
v___x_1950_ = v_x_1941_;
v_isShared_1951_ = v_isSharedCheck_1966_;
goto v_resetjp_1949_;
}
else
{
lean_dec(v_x_1941_);
v___x_1950_ = lean_box(0);
v_isShared_1951_ = v_isSharedCheck_1966_;
goto v_resetjp_1949_;
}
v_resetjp_1949_:
{
size_t v___x_1952_; size_t v___x_1953_; size_t v___x_1954_; size_t v_i_1955_; size_t v___x_1956_; size_t v_shift_1957_; lean_object* v_v_1958_; lean_object* v___x_1959_; lean_object* v_xs_x27_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1964_; 
v___x_1952_ = ((size_t)1ULL);
v___x_1953_ = lean_usize_shift_left(v___x_1952_, v_x_1943_);
v___x_1954_ = lean_usize_sub(v___x_1953_, v___x_1952_);
v_i_1955_ = lean_usize_land(v_x_1942_, v___x_1954_);
v___x_1956_ = ((size_t)5ULL);
v_shift_1957_ = lean_usize_sub(v_x_1943_, v___x_1956_);
v_v_1958_ = lean_array_fget(v_cs_1944_, v___x_1946_);
v___x_1959_ = lean_box(0);
v_xs_x27_1960_ = lean_array_fset(v_cs_1944_, v___x_1946_, v___x_1959_);
v___x_1961_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___redArg(v___x_1940_, v_v_1958_, v_i_1955_, v_shift_1957_);
v___x_1962_ = lean_array_fset(v_xs_x27_1960_, v___x_1946_, v___x_1961_);
lean_dec(v___x_1946_);
if (v_isShared_1951_ == 0)
{
lean_ctor_set(v___x_1950_, 0, v___x_1962_);
v___x_1964_ = v___x_1950_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v___x_1962_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
}
else
{
lean_object* v_vs_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; uint8_t v___x_1971_; 
v_vs_1968_ = lean_ctor_get(v_x_1941_, 0);
v___x_1969_ = lean_usize_to_nat(v_x_1942_);
v___x_1970_ = lean_array_get_size(v_vs_1968_);
v___x_1971_ = lean_nat_dec_lt(v___x_1969_, v___x_1970_);
if (v___x_1971_ == 0)
{
lean_dec(v___x_1969_);
return v_x_1941_;
}
else
{
lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1985_; 
lean_inc_ref(v_vs_1968_);
v_isSharedCheck_1985_ = !lean_is_exclusive(v_x_1941_);
if (v_isSharedCheck_1985_ == 0)
{
lean_object* v_unused_1986_; 
v_unused_1986_ = lean_ctor_get(v_x_1941_, 0);
lean_dec(v_unused_1986_);
v___x_1973_ = v_x_1941_;
v_isShared_1974_ = v_isSharedCheck_1985_;
goto v_resetjp_1972_;
}
else
{
lean_dec(v_x_1941_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1985_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v_v_1975_; lean_object* v___x_1976_; lean_object* v_xs_x27_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1983_; 
v_v_1975_ = lean_array_fget(v_vs_1968_, v___x_1969_);
v___x_1976_ = lean_box(0);
v_xs_x27_1977_ = lean_array_fset(v_vs_1968_, v___x_1969_, v___x_1976_);
v___x_1978_ = lean_unsigned_to_nat(0u);
v___x_1979_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___redArg___closed__1, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___redArg___closed__1);
v___x_1980_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(v___x_1940_, v_v_1975_, v___x_1979_, v___x_1978_);
lean_dec(v_v_1975_);
v___x_1981_ = lean_array_fset(v_xs_x27_1977_, v___x_1969_, v___x_1980_);
lean_dec(v___x_1969_);
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 0, v___x_1981_);
v___x_1983_ = v___x_1973_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1984_, 0, v___x_1981_);
v___x_1983_ = v_reuseFailAlloc_1984_;
goto v_reusejp_1982_;
}
v_reusejp_1982_:
{
return v___x_1983_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___redArg___boxed(lean_object* v___x_1987_, lean_object* v_x_1988_, lean_object* v_x_1989_, lean_object* v_x_1990_){
_start:
{
size_t v_x_21819__boxed_1991_; size_t v_x_21820__boxed_1992_; lean_object* v_res_1993_; 
v_x_21819__boxed_1991_ = lean_unbox_usize(v_x_1989_);
lean_dec(v_x_1989_);
v_x_21820__boxed_1992_ = lean_unbox_usize(v_x_1990_);
lean_dec(v_x_1990_);
v_res_1993_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___redArg(v___x_1987_, v_x_1988_, v_x_21819__boxed_1991_, v_x_21820__boxed_1992_);
lean_dec_ref(v___x_1987_);
return v_res_1993_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1(lean_object* v___x_1994_, lean_object* v_inst_1995_, lean_object* v_t_1996_, lean_object* v_i_1997_){
_start:
{
lean_object* v_root_1998_; lean_object* v_tail_1999_; lean_object* v_size_2000_; size_t v_shift_2001_; lean_object* v_tailOff_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2030_; 
v_root_1998_ = lean_ctor_get(v_t_1996_, 0);
v_tail_1999_ = lean_ctor_get(v_t_1996_, 1);
v_size_2000_ = lean_ctor_get(v_t_1996_, 2);
v_shift_2001_ = lean_ctor_get_usize(v_t_1996_, 4);
v_tailOff_2002_ = lean_ctor_get(v_t_1996_, 3);
v_isSharedCheck_2030_ = !lean_is_exclusive(v_t_1996_);
if (v_isSharedCheck_2030_ == 0)
{
v___x_2004_ = v_t_1996_;
v_isShared_2005_ = v_isSharedCheck_2030_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_tailOff_2002_);
lean_inc(v_size_2000_);
lean_inc(v_tail_1999_);
lean_inc(v_root_1998_);
lean_dec(v_t_1996_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2030_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
uint8_t v___x_2006_; 
v___x_2006_ = lean_nat_dec_le(v_tailOff_2002_, v_i_1997_);
if (v___x_2006_ == 0)
{
size_t v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2010_; 
v___x_2007_ = lean_usize_of_nat(v_i_1997_);
v___x_2008_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___redArg(v___x_1994_, v_root_1998_, v___x_2007_, v_shift_2001_);
if (v_isShared_2005_ == 0)
{
lean_ctor_set(v___x_2004_, 0, v___x_2008_);
v___x_2010_ = v___x_2004_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v___x_2008_);
lean_ctor_set(v_reuseFailAlloc_2011_, 1, v_tail_1999_);
lean_ctor_set(v_reuseFailAlloc_2011_, 2, v_size_2000_);
lean_ctor_set(v_reuseFailAlloc_2011_, 3, v_tailOff_2002_);
lean_ctor_set_usize(v_reuseFailAlloc_2011_, 4, v_shift_2001_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
else
{
lean_object* v___x_2012_; lean_object* v___x_2013_; uint8_t v___x_2014_; 
v___x_2012_ = lean_nat_sub(v_i_1997_, v_tailOff_2002_);
v___x_2013_ = lean_array_get_size(v_tail_1999_);
v___x_2014_ = lean_nat_dec_lt(v___x_2012_, v___x_2013_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2016_; 
lean_dec(v___x_2012_);
if (v_isShared_2005_ == 0)
{
v___x_2016_ = v___x_2004_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v_root_1998_);
lean_ctor_set(v_reuseFailAlloc_2017_, 1, v_tail_1999_);
lean_ctor_set(v_reuseFailAlloc_2017_, 2, v_size_2000_);
lean_ctor_set(v_reuseFailAlloc_2017_, 3, v_tailOff_2002_);
lean_ctor_set_usize(v_reuseFailAlloc_2017_, 4, v_shift_2001_);
v___x_2016_ = v_reuseFailAlloc_2017_;
goto v_reusejp_2015_;
}
v_reusejp_2015_:
{
return v___x_2016_;
}
}
else
{
lean_object* v_v_2018_; lean_object* v___x_2019_; lean_object* v_xs_x27_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2028_; 
v_v_2018_ = lean_array_fget(v_tail_1999_, v___x_2012_);
v___x_2019_ = lean_box(0);
v_xs_x27_2020_ = lean_array_fset(v_tail_1999_, v___x_2012_, v___x_2019_);
v___x_2021_ = lean_unsigned_to_nat(32u);
v___x_2022_ = lean_mk_empty_array_with_capacity(v___x_2021_);
lean_dec_ref(v___x_2022_);
v___x_2023_ = lean_unsigned_to_nat(0u);
v___x_2024_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___redArg___closed__1, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___redArg___closed__1);
v___x_2025_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(v___x_1994_, v_v_2018_, v___x_2024_, v___x_2023_);
lean_dec(v_v_2018_);
v___x_2026_ = lean_array_fset(v_xs_x27_2020_, v___x_2012_, v___x_2025_);
lean_dec(v___x_2012_);
if (v_isShared_2005_ == 0)
{
lean_ctor_set(v___x_2004_, 1, v___x_2026_);
v___x_2028_ = v___x_2004_;
goto v_reusejp_2027_;
}
else
{
lean_object* v_reuseFailAlloc_2029_; 
v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2029_, 0, v_root_1998_);
lean_ctor_set(v_reuseFailAlloc_2029_, 1, v___x_2026_);
lean_ctor_set(v_reuseFailAlloc_2029_, 2, v_size_2000_);
lean_ctor_set(v_reuseFailAlloc_2029_, 3, v_tailOff_2002_);
lean_ctor_set_usize(v_reuseFailAlloc_2029_, 4, v_shift_2001_);
v___x_2028_ = v_reuseFailAlloc_2029_;
goto v_reusejp_2027_;
}
v_reusejp_2027_:
{
return v___x_2028_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1___boxed(lean_object* v___x_2031_, lean_object* v_inst_2032_, lean_object* v_t_2033_, lean_object* v_i_2034_){
_start:
{
lean_object* v_res_2035_; 
v_res_2035_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1(v___x_2031_, v_inst_2032_, v_t_2033_, v_i_2034_);
lean_dec(v_i_2034_);
lean_dec_ref(v_inst_2032_);
lean_dec_ref(v___x_2031_);
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0(lean_object* v_p_2036_, lean_object* v___x_2037_, lean_object* v_x_2038_, lean_object* v_s_2039_){
_start:
{
lean_object* v_vars_2040_; lean_object* v_varMap_2041_; lean_object* v_vars_x27_2042_; lean_object* v_varMap_x27_2043_; lean_object* v_natToIntMap_2044_; lean_object* v_natDef_2045_; lean_object* v_dvds_2046_; lean_object* v_lowers_2047_; lean_object* v_uppers_2048_; lean_object* v_diseqs_2049_; lean_object* v_elimEqs_2050_; lean_object* v_elimStack_2051_; lean_object* v_occurs_2052_; lean_object* v_assignment_2053_; lean_object* v_nextCnstrId_2054_; uint8_t v_caseSplits_2055_; lean_object* v_conflict_x3f_2056_; lean_object* v_diseqSplits_2057_; lean_object* v_divMod_2058_; lean_object* v_toIntIds_2059_; lean_object* v_toIntInfos_2060_; lean_object* v_toIntTermMap_2061_; lean_object* v_toIntVarMap_2062_; uint8_t v_usedCommRing_2063_; lean_object* v_nonlinearOccs_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2072_; 
v_vars_2040_ = lean_ctor_get(v_s_2039_, 0);
v_varMap_2041_ = lean_ctor_get(v_s_2039_, 1);
v_vars_x27_2042_ = lean_ctor_get(v_s_2039_, 2);
v_varMap_x27_2043_ = lean_ctor_get(v_s_2039_, 3);
v_natToIntMap_2044_ = lean_ctor_get(v_s_2039_, 4);
v_natDef_2045_ = lean_ctor_get(v_s_2039_, 5);
v_dvds_2046_ = lean_ctor_get(v_s_2039_, 6);
v_lowers_2047_ = lean_ctor_get(v_s_2039_, 7);
v_uppers_2048_ = lean_ctor_get(v_s_2039_, 8);
v_diseqs_2049_ = lean_ctor_get(v_s_2039_, 9);
v_elimEqs_2050_ = lean_ctor_get(v_s_2039_, 10);
v_elimStack_2051_ = lean_ctor_get(v_s_2039_, 11);
v_occurs_2052_ = lean_ctor_get(v_s_2039_, 12);
v_assignment_2053_ = lean_ctor_get(v_s_2039_, 13);
v_nextCnstrId_2054_ = lean_ctor_get(v_s_2039_, 14);
v_caseSplits_2055_ = lean_ctor_get_uint8(v_s_2039_, sizeof(void*)*23);
v_conflict_x3f_2056_ = lean_ctor_get(v_s_2039_, 15);
v_diseqSplits_2057_ = lean_ctor_get(v_s_2039_, 16);
v_divMod_2058_ = lean_ctor_get(v_s_2039_, 17);
v_toIntIds_2059_ = lean_ctor_get(v_s_2039_, 18);
v_toIntInfos_2060_ = lean_ctor_get(v_s_2039_, 19);
v_toIntTermMap_2061_ = lean_ctor_get(v_s_2039_, 20);
v_toIntVarMap_2062_ = lean_ctor_get(v_s_2039_, 21);
v_usedCommRing_2063_ = lean_ctor_get_uint8(v_s_2039_, sizeof(void*)*23 + 1);
v_nonlinearOccs_2064_ = lean_ctor_get(v_s_2039_, 22);
v_isSharedCheck_2072_ = !lean_is_exclusive(v_s_2039_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2066_ = v_s_2039_;
v_isShared_2067_ = v_isSharedCheck_2072_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_nonlinearOccs_2064_);
lean_inc(v_toIntVarMap_2062_);
lean_inc(v_toIntTermMap_2061_);
lean_inc(v_toIntInfos_2060_);
lean_inc(v_toIntIds_2059_);
lean_inc(v_divMod_2058_);
lean_inc(v_diseqSplits_2057_);
lean_inc(v_conflict_x3f_2056_);
lean_inc(v_nextCnstrId_2054_);
lean_inc(v_assignment_2053_);
lean_inc(v_occurs_2052_);
lean_inc(v_elimStack_2051_);
lean_inc(v_elimEqs_2050_);
lean_inc(v_diseqs_2049_);
lean_inc(v_uppers_2048_);
lean_inc(v_lowers_2047_);
lean_inc(v_dvds_2046_);
lean_inc(v_natDef_2045_);
lean_inc(v_natToIntMap_2044_);
lean_inc(v_varMap_x27_2043_);
lean_inc(v_vars_x27_2042_);
lean_inc(v_varMap_2041_);
lean_inc(v_vars_2040_);
lean_dec(v_s_2039_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2072_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2068_; lean_object* v___x_2070_; 
v___x_2068_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1(v_p_2036_, v___x_2037_, v_diseqs_2049_, v_x_2038_);
if (v_isShared_2067_ == 0)
{
lean_ctor_set(v___x_2066_, 9, v___x_2068_);
v___x_2070_ = v___x_2066_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_vars_2040_);
lean_ctor_set(v_reuseFailAlloc_2071_, 1, v_varMap_2041_);
lean_ctor_set(v_reuseFailAlloc_2071_, 2, v_vars_x27_2042_);
lean_ctor_set(v_reuseFailAlloc_2071_, 3, v_varMap_x27_2043_);
lean_ctor_set(v_reuseFailAlloc_2071_, 4, v_natToIntMap_2044_);
lean_ctor_set(v_reuseFailAlloc_2071_, 5, v_natDef_2045_);
lean_ctor_set(v_reuseFailAlloc_2071_, 6, v_dvds_2046_);
lean_ctor_set(v_reuseFailAlloc_2071_, 7, v_lowers_2047_);
lean_ctor_set(v_reuseFailAlloc_2071_, 8, v_uppers_2048_);
lean_ctor_set(v_reuseFailAlloc_2071_, 9, v___x_2068_);
lean_ctor_set(v_reuseFailAlloc_2071_, 10, v_elimEqs_2050_);
lean_ctor_set(v_reuseFailAlloc_2071_, 11, v_elimStack_2051_);
lean_ctor_set(v_reuseFailAlloc_2071_, 12, v_occurs_2052_);
lean_ctor_set(v_reuseFailAlloc_2071_, 13, v_assignment_2053_);
lean_ctor_set(v_reuseFailAlloc_2071_, 14, v_nextCnstrId_2054_);
lean_ctor_set(v_reuseFailAlloc_2071_, 15, v_conflict_x3f_2056_);
lean_ctor_set(v_reuseFailAlloc_2071_, 16, v_diseqSplits_2057_);
lean_ctor_set(v_reuseFailAlloc_2071_, 17, v_divMod_2058_);
lean_ctor_set(v_reuseFailAlloc_2071_, 18, v_toIntIds_2059_);
lean_ctor_set(v_reuseFailAlloc_2071_, 19, v_toIntInfos_2060_);
lean_ctor_set(v_reuseFailAlloc_2071_, 20, v_toIntTermMap_2061_);
lean_ctor_set(v_reuseFailAlloc_2071_, 21, v_toIntVarMap_2062_);
lean_ctor_set(v_reuseFailAlloc_2071_, 22, v_nonlinearOccs_2064_);
lean_ctor_set_uint8(v_reuseFailAlloc_2071_, sizeof(void*)*23, v_caseSplits_2055_);
lean_ctor_set_uint8(v_reuseFailAlloc_2071_, sizeof(void*)*23 + 1, v_usedCommRing_2063_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed(lean_object* v_p_2073_, lean_object* v___x_2074_, lean_object* v_x_2075_, lean_object* v_s_2076_){
_start:
{
lean_object* v_res_2077_; 
v_res_2077_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0(v_p_2073_, v___x_2074_, v_x_2075_, v_s_2076_);
lean_dec(v_x_2075_);
lean_dec_ref(v___x_2074_);
lean_dec_ref(v_p_2073_);
return v_res_2077_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2084_ = lean_unsigned_to_nat(1u);
v___x_2085_ = lean_nat_to_int(v___x_2084_);
return v___x_2085_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(lean_object* v_c_2086_, lean_object* v_x_2087_, lean_object* v_as_2088_, size_t v_sz_2089_, size_t v_i_2090_, lean_object* v_b_2091_, lean_object* v___y_2092_){
_start:
{
uint8_t v___x_2094_; 
v___x_2094_ = lean_usize_dec_lt(v_i_2090_, v_sz_2089_);
if (v___x_2094_ == 0)
{
lean_object* v___x_2095_; 
lean_dec(v_x_2087_);
lean_dec_ref(v_c_2086_);
v___x_2095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2095_, 0, v_b_2091_);
return v___x_2095_;
}
else
{
lean_object* v_snd_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2143_; 
v_snd_2096_ = lean_ctor_get(v_b_2091_, 1);
v_isSharedCheck_2143_ = !lean_is_exclusive(v_b_2091_);
if (v_isSharedCheck_2143_ == 0)
{
lean_object* v_unused_2144_; 
v_unused_2144_ = lean_ctor_get(v_b_2091_, 0);
lean_dec(v_unused_2144_);
v___x_2098_ = v_b_2091_;
v_isShared_2099_ = v_isSharedCheck_2143_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_snd_2096_);
lean_dec(v_b_2091_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2143_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v_p_2100_; lean_object* v_a_2101_; lean_object* v_p_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___f_2105_; uint8_t v___y_2107_; uint8_t v___x_2141_; 
v_p_2100_ = lean_ctor_get(v_c_2086_, 0);
v_a_2101_ = lean_array_uget_borrowed(v_as_2088_, v_i_2090_);
v_p_2102_ = lean_ctor_get(v_a_2101_, 0);
v___x_2103_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0);
v___x_2104_ = lean_box(0);
lean_inc(v_x_2087_);
lean_inc_ref(v_p_2102_);
v___f_2105_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2105_, 0, v_p_2102_);
lean_closure_set(v___f_2105_, 1, v___x_2103_);
lean_closure_set(v___f_2105_, 2, v_x_2087_);
v___x_2141_ = l_Int_Linear_instBEqPoly_beq(v_p_2100_, v_p_2102_);
if (v___x_2141_ == 0)
{
uint8_t v___x_2142_; 
v___x_2142_ = l_Int_Linear_Poly_isNegEq(v_p_2100_, v_p_2102_);
v___y_2107_ = v___x_2142_;
goto v___jp_2106_;
}
else
{
v___y_2107_ = v___x_2141_;
goto v___jp_2106_;
}
v___jp_2106_:
{
if (v___y_2107_ == 0)
{
lean_object* v___x_2108_; size_t v___x_2109_; size_t v___x_2110_; 
lean_dec_ref(v___f_2105_);
lean_del_object(v___x_2098_);
lean_dec(v_snd_2096_);
v___x_2108_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__1));
v___x_2109_ = ((size_t)1ULL);
v___x_2110_ = lean_usize_add(v_i_2090_, v___x_2109_);
v_i_2090_ = v___x_2110_;
v_b_2091_ = v___x_2108_;
goto _start;
}
else
{
lean_object* v___x_2112_; lean_object* v___x_2113_; 
lean_dec(v_x_2087_);
v___x_2112_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2113_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2112_, v___f_2105_, v___y_2092_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2131_; 
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2131_ == 0)
{
lean_object* v_unused_2132_; 
v_unused_2132_ = lean_ctor_get(v___x_2113_, 0);
lean_dec(v_unused_2132_);
v___x_2115_ = v___x_2113_;
v_isShared_2116_ = v_isSharedCheck_2131_;
goto v_resetjp_2114_;
}
else
{
lean_dec(v___x_2113_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2131_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2124_; 
v___x_2117_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
lean_inc_ref(v_p_2100_);
v___x_2118_ = l_Int_Linear_Poly_addConst(v_p_2100_, v___x_2117_);
lean_inc(v_a_2101_);
v___x_2119_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_2119_, 0, v_c_2086_);
lean_ctor_set(v___x_2119_, 1, v_a_2101_);
v___x_2120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2118_);
lean_ctor_set(v___x_2120_, 1, v___x_2119_);
v___x_2121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2120_);
v___x_2122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2121_);
if (v_isShared_2099_ == 0)
{
lean_ctor_set(v___x_2098_, 1, v___x_2104_);
lean_ctor_set(v___x_2098_, 0, v___x_2122_);
v___x_2124_ = v___x_2098_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___x_2122_);
lean_ctor_set(v_reuseFailAlloc_2130_, 1, v___x_2104_);
v___x_2124_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2128_; 
v___x_2125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2124_);
v___x_2126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2125_);
lean_ctor_set(v___x_2126_, 1, v_snd_2096_);
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 0, v___x_2126_);
v___x_2128_ = v___x_2115_;
goto v_reusejp_2127_;
}
else
{
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v___x_2126_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
}
else
{
lean_object* v_a_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2140_; 
lean_del_object(v___x_2098_);
lean_dec(v_snd_2096_);
lean_dec_ref(v_c_2086_);
v_a_2133_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2140_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2140_ == 0)
{
v___x_2135_ = v___x_2113_;
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_a_2133_);
lean_dec(v___x_2113_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2140_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2138_; 
if (v_isShared_2136_ == 0)
{
v___x_2138_ = v___x_2135_;
goto v_reusejp_2137_;
}
else
{
lean_object* v_reuseFailAlloc_2139_; 
v_reuseFailAlloc_2139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2139_, 0, v_a_2133_);
v___x_2138_ = v_reuseFailAlloc_2139_;
goto v_reusejp_2137_;
}
v_reusejp_2137_:
{
return v___x_2138_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___boxed(lean_object* v_c_2145_, lean_object* v_x_2146_, lean_object* v_as_2147_, lean_object* v_sz_2148_, lean_object* v_i_2149_, lean_object* v_b_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
size_t v_sz_boxed_2153_; size_t v_i_boxed_2154_; lean_object* v_res_2155_; 
v_sz_boxed_2153_ = lean_unbox_usize(v_sz_2148_);
lean_dec(v_sz_2148_);
v_i_boxed_2154_ = lean_unbox_usize(v_i_2149_);
lean_dec(v_i_2149_);
v_res_2155_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(v_c_2145_, v_x_2146_, v_as_2147_, v_sz_boxed_2153_, v_i_boxed_2154_, v_b_2150_, v___y_2151_);
lean_dec(v___y_2151_);
lean_dec_ref(v_as_2147_);
return v_res_2155_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7(lean_object* v_c_2162_, lean_object* v_x_2163_, lean_object* v_as_2164_, size_t v_sz_2165_, size_t v_i_2166_, lean_object* v_b_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_){
_start:
{
uint8_t v___x_2179_; 
v___x_2179_ = lean_usize_dec_lt(v_i_2166_, v_sz_2165_);
if (v___x_2179_ == 0)
{
lean_object* v___x_2180_; 
lean_dec(v_x_2163_);
lean_dec_ref(v_c_2162_);
v___x_2180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2180_, 0, v_b_2167_);
return v___x_2180_;
}
else
{
lean_object* v_snd_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2228_; 
v_snd_2181_ = lean_ctor_get(v_b_2167_, 1);
v_isSharedCheck_2228_ = !lean_is_exclusive(v_b_2167_);
if (v_isSharedCheck_2228_ == 0)
{
lean_object* v_unused_2229_; 
v_unused_2229_ = lean_ctor_get(v_b_2167_, 0);
lean_dec(v_unused_2229_);
v___x_2183_ = v_b_2167_;
v_isShared_2184_ = v_isSharedCheck_2228_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_snd_2181_);
lean_dec(v_b_2167_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2228_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v_p_2185_; lean_object* v_a_2186_; lean_object* v_p_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___f_2190_; uint8_t v___y_2192_; uint8_t v___x_2226_; 
v_p_2185_ = lean_ctor_get(v_c_2162_, 0);
v_a_2186_ = lean_array_uget_borrowed(v_as_2164_, v_i_2166_);
v_p_2187_ = lean_ctor_get(v_a_2186_, 0);
v___x_2188_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0);
v___x_2189_ = lean_box(0);
lean_inc(v_x_2163_);
lean_inc_ref(v_p_2187_);
v___f_2190_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2190_, 0, v_p_2187_);
lean_closure_set(v___f_2190_, 1, v___x_2188_);
lean_closure_set(v___f_2190_, 2, v_x_2163_);
v___x_2226_ = l_Int_Linear_instBEqPoly_beq(v_p_2185_, v_p_2187_);
if (v___x_2226_ == 0)
{
uint8_t v___x_2227_; 
v___x_2227_ = l_Int_Linear_Poly_isNegEq(v_p_2185_, v_p_2187_);
v___y_2192_ = v___x_2227_;
goto v___jp_2191_;
}
else
{
v___y_2192_ = v___x_2226_;
goto v___jp_2191_;
}
v___jp_2191_:
{
if (v___y_2192_ == 0)
{
lean_object* v___x_2193_; size_t v___x_2194_; size_t v___x_2195_; lean_object* v___x_2196_; 
lean_dec_ref(v___f_2190_);
lean_del_object(v___x_2183_);
lean_dec(v_snd_2181_);
v___x_2193_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___closed__1));
v___x_2194_ = ((size_t)1ULL);
v___x_2195_ = lean_usize_add(v_i_2166_, v___x_2194_);
v___x_2196_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(v_c_2162_, v_x_2163_, v_as_2164_, v_sz_2165_, v___x_2195_, v___x_2193_, v___y_2168_);
return v___x_2196_;
}
else
{
lean_object* v___x_2197_; lean_object* v___x_2198_; 
lean_dec(v_x_2163_);
v___x_2197_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2198_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2197_, v___f_2190_, v___y_2168_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2216_; 
v_isSharedCheck_2216_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2216_ == 0)
{
lean_object* v_unused_2217_; 
v_unused_2217_ = lean_ctor_get(v___x_2198_, 0);
lean_dec(v_unused_2217_);
v___x_2200_ = v___x_2198_;
v_isShared_2201_ = v_isSharedCheck_2216_;
goto v_resetjp_2199_;
}
else
{
lean_dec(v___x_2198_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2216_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2209_; 
v___x_2202_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
lean_inc_ref(v_p_2185_);
v___x_2203_ = l_Int_Linear_Poly_addConst(v_p_2185_, v___x_2202_);
lean_inc(v_a_2186_);
v___x_2204_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_2204_, 0, v_c_2162_);
lean_ctor_set(v___x_2204_, 1, v_a_2186_);
v___x_2205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2203_);
lean_ctor_set(v___x_2205_, 1, v___x_2204_);
v___x_2206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2205_);
v___x_2207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2206_);
if (v_isShared_2184_ == 0)
{
lean_ctor_set(v___x_2183_, 1, v___x_2189_);
lean_ctor_set(v___x_2183_, 0, v___x_2207_);
v___x_2209_ = v___x_2183_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v___x_2207_);
lean_ctor_set(v_reuseFailAlloc_2215_, 1, v___x_2189_);
v___x_2209_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2213_; 
v___x_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2209_);
v___x_2211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2210_);
lean_ctor_set(v___x_2211_, 1, v_snd_2181_);
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 0, v___x_2211_);
v___x_2213_ = v___x_2200_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v___x_2211_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
}
}
else
{
lean_object* v_a_2218_; lean_object* v___x_2220_; uint8_t v_isShared_2221_; uint8_t v_isSharedCheck_2225_; 
lean_del_object(v___x_2183_);
lean_dec(v_snd_2181_);
lean_dec_ref(v_c_2162_);
v_a_2218_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2220_ = v___x_2198_;
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
else
{
lean_inc(v_a_2218_);
lean_dec(v___x_2198_);
v___x_2220_ = lean_box(0);
v_isShared_2221_ = v_isSharedCheck_2225_;
goto v_resetjp_2219_;
}
v_resetjp_2219_:
{
lean_object* v___x_2223_; 
if (v_isShared_2221_ == 0)
{
v___x_2223_ = v___x_2220_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2218_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___boxed(lean_object** _args){
lean_object* v_c_2230_ = _args[0];
lean_object* v_x_2231_ = _args[1];
lean_object* v_as_2232_ = _args[2];
lean_object* v_sz_2233_ = _args[3];
lean_object* v_i_2234_ = _args[4];
lean_object* v_b_2235_ = _args[5];
lean_object* v___y_2236_ = _args[6];
lean_object* v___y_2237_ = _args[7];
lean_object* v___y_2238_ = _args[8];
lean_object* v___y_2239_ = _args[9];
lean_object* v___y_2240_ = _args[10];
lean_object* v___y_2241_ = _args[11];
lean_object* v___y_2242_ = _args[12];
lean_object* v___y_2243_ = _args[13];
lean_object* v___y_2244_ = _args[14];
lean_object* v___y_2245_ = _args[15];
lean_object* v___y_2246_ = _args[16];
_start:
{
size_t v_sz_boxed_2247_; size_t v_i_boxed_2248_; lean_object* v_res_2249_; 
v_sz_boxed_2247_ = lean_unbox_usize(v_sz_2233_);
lean_dec(v_sz_2233_);
v_i_boxed_2248_ = lean_unbox_usize(v_i_2234_);
lean_dec(v_i_2234_);
v_res_2249_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7(v_c_2230_, v_x_2231_, v_as_2232_, v_sz_boxed_2247_, v_i_boxed_2248_, v_b_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
lean_dec(v___y_2237_);
lean_dec(v___y_2236_);
lean_dec_ref(v_as_2232_);
return v_res_2249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(lean_object* v_c_2256_, lean_object* v_x_2257_, lean_object* v_as_2258_, size_t v_sz_2259_, size_t v_i_2260_, lean_object* v_b_2261_, lean_object* v___y_2262_){
_start:
{
uint8_t v___x_2264_; 
v___x_2264_ = lean_usize_dec_lt(v_i_2260_, v_sz_2259_);
if (v___x_2264_ == 0)
{
lean_object* v___x_2265_; 
lean_dec(v_x_2257_);
lean_dec_ref(v_c_2256_);
v___x_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2265_, 0, v_b_2261_);
return v___x_2265_;
}
else
{
lean_object* v_snd_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2314_; 
v_snd_2266_ = lean_ctor_get(v_b_2261_, 1);
v_isSharedCheck_2314_ = !lean_is_exclusive(v_b_2261_);
if (v_isSharedCheck_2314_ == 0)
{
lean_object* v_unused_2315_; 
v_unused_2315_ = lean_ctor_get(v_b_2261_, 0);
lean_dec(v_unused_2315_);
v___x_2268_ = v_b_2261_;
v_isShared_2269_ = v_isSharedCheck_2314_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_snd_2266_);
lean_dec(v_b_2261_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2314_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v_p_2270_; lean_object* v_a_2271_; lean_object* v_p_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___f_2275_; uint8_t v___y_2277_; uint8_t v___x_2312_; 
v_p_2270_ = lean_ctor_get(v_c_2256_, 0);
v_a_2271_ = lean_array_uget_borrowed(v_as_2258_, v_i_2260_);
v_p_2272_ = lean_ctor_get(v_a_2271_, 0);
v___x_2273_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0);
v___x_2274_ = lean_box(0);
lean_inc(v_x_2257_);
lean_inc_ref(v_p_2272_);
v___f_2275_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2275_, 0, v_p_2272_);
lean_closure_set(v___f_2275_, 1, v___x_2273_);
lean_closure_set(v___f_2275_, 2, v_x_2257_);
v___x_2312_ = l_Int_Linear_instBEqPoly_beq(v_p_2270_, v_p_2272_);
if (v___x_2312_ == 0)
{
uint8_t v___x_2313_; 
v___x_2313_ = l_Int_Linear_Poly_isNegEq(v_p_2270_, v_p_2272_);
v___y_2277_ = v___x_2313_;
goto v___jp_2276_;
}
else
{
v___y_2277_ = v___x_2312_;
goto v___jp_2276_;
}
v___jp_2276_:
{
if (v___y_2277_ == 0)
{
lean_object* v___x_2278_; size_t v___x_2279_; size_t v___x_2280_; 
lean_dec_ref(v___f_2275_);
lean_del_object(v___x_2268_);
lean_dec(v_snd_2266_);
v___x_2278_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg___closed__1));
v___x_2279_ = ((size_t)1ULL);
v___x_2280_ = lean_usize_add(v_i_2260_, v___x_2279_);
v_i_2260_ = v___x_2280_;
v_b_2261_ = v___x_2278_;
goto _start;
}
else
{
lean_object* v___x_2282_; lean_object* v___x_2283_; 
lean_dec(v_x_2257_);
v___x_2282_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2283_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2282_, v___f_2275_, v___y_2262_);
if (lean_obj_tag(v___x_2283_) == 0)
{
lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2302_; 
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2302_ == 0)
{
lean_object* v_unused_2303_; 
v_unused_2303_ = lean_ctor_get(v___x_2283_, 0);
lean_dec(v_unused_2303_);
v___x_2285_ = v___x_2283_;
v_isShared_2286_ = v_isSharedCheck_2302_;
goto v_resetjp_2284_;
}
else
{
lean_dec(v___x_2283_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2302_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2294_; 
v___x_2287_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
lean_inc_ref(v_p_2270_);
v___x_2288_ = l_Int_Linear_Poly_addConst(v_p_2270_, v___x_2287_);
lean_inc(v_a_2271_);
v___x_2289_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_2289_, 0, v_c_2256_);
lean_ctor_set(v___x_2289_, 1, v_a_2271_);
v___x_2290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2288_);
lean_ctor_set(v___x_2290_, 1, v___x_2289_);
v___x_2291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2290_);
v___x_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2291_);
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 1, v___x_2274_);
lean_ctor_set(v___x_2268_, 0, v___x_2292_);
v___x_2294_ = v___x_2268_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v___x_2292_);
lean_ctor_set(v_reuseFailAlloc_2301_, 1, v___x_2274_);
v___x_2294_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2299_; 
v___x_2295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2294_);
v___x_2296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2295_);
v___x_2297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2296_);
lean_ctor_set(v___x_2297_, 1, v_snd_2266_);
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 0, v___x_2297_);
v___x_2299_ = v___x_2285_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v___x_2297_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
}
else
{
lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2311_; 
lean_del_object(v___x_2268_);
lean_dec(v_snd_2266_);
lean_dec_ref(v_c_2256_);
v_a_2304_ = lean_ctor_get(v___x_2283_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2306_ = v___x_2283_;
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v___x_2283_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2309_; 
if (v_isShared_2307_ == 0)
{
v___x_2309_ = v___x_2306_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_a_2304_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg___boxed(lean_object* v_c_2316_, lean_object* v_x_2317_, lean_object* v_as_2318_, lean_object* v_sz_2319_, lean_object* v_i_2320_, lean_object* v_b_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_){
_start:
{
size_t v_sz_boxed_2324_; size_t v_i_boxed_2325_; lean_object* v_res_2326_; 
v_sz_boxed_2324_ = lean_unbox_usize(v_sz_2319_);
lean_dec(v_sz_2319_);
v_i_boxed_2325_ = lean_unbox_usize(v_i_2320_);
lean_dec(v_i_2320_);
v_res_2326_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(v_c_2316_, v_x_2317_, v_as_2318_, v_sz_boxed_2324_, v_i_boxed_2325_, v_b_2321_, v___y_2322_);
lean_dec(v___y_2322_);
lean_dec_ref(v_as_2318_);
return v_res_2326_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9(lean_object* v_c_2330_, lean_object* v_x_2331_, lean_object* v_as_2332_, size_t v_sz_2333_, size_t v_i_2334_, lean_object* v_b_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
uint8_t v___x_2347_; 
v___x_2347_ = lean_usize_dec_lt(v_i_2334_, v_sz_2333_);
if (v___x_2347_ == 0)
{
lean_object* v___x_2348_; 
lean_dec(v_x_2331_);
lean_dec_ref(v_c_2330_);
v___x_2348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2348_, 0, v_b_2335_);
return v___x_2348_;
}
else
{
lean_object* v_snd_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2397_; 
v_snd_2349_ = lean_ctor_get(v_b_2335_, 1);
v_isSharedCheck_2397_ = !lean_is_exclusive(v_b_2335_);
if (v_isSharedCheck_2397_ == 0)
{
lean_object* v_unused_2398_; 
v_unused_2398_ = lean_ctor_get(v_b_2335_, 0);
lean_dec(v_unused_2398_);
v___x_2351_ = v_b_2335_;
v_isShared_2352_ = v_isSharedCheck_2397_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_snd_2349_);
lean_dec(v_b_2335_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2397_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v_p_2353_; lean_object* v_a_2354_; lean_object* v_p_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___f_2358_; uint8_t v___y_2360_; uint8_t v___x_2395_; 
v_p_2353_ = lean_ctor_get(v_c_2330_, 0);
v_a_2354_ = lean_array_uget_borrowed(v_as_2332_, v_i_2334_);
v_p_2355_ = lean_ctor_get(v_a_2354_, 0);
v___x_2356_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0);
v___x_2357_ = lean_box(0);
lean_inc(v_x_2331_);
lean_inc_ref(v_p_2355_);
v___f_2358_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2358_, 0, v_p_2355_);
lean_closure_set(v___f_2358_, 1, v___x_2356_);
lean_closure_set(v___f_2358_, 2, v_x_2331_);
v___x_2395_ = l_Int_Linear_instBEqPoly_beq(v_p_2353_, v_p_2355_);
if (v___x_2395_ == 0)
{
uint8_t v___x_2396_; 
v___x_2396_ = l_Int_Linear_Poly_isNegEq(v_p_2353_, v_p_2355_);
v___y_2360_ = v___x_2396_;
goto v___jp_2359_;
}
else
{
v___y_2360_ = v___x_2395_;
goto v___jp_2359_;
}
v___jp_2359_:
{
if (v___y_2360_ == 0)
{
lean_object* v___x_2361_; size_t v___x_2362_; size_t v___x_2363_; lean_object* v___x_2364_; 
lean_dec_ref(v___f_2358_);
lean_del_object(v___x_2351_);
lean_dec(v_snd_2349_);
v___x_2361_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9___closed__0));
v___x_2362_ = ((size_t)1ULL);
v___x_2363_ = lean_usize_add(v_i_2334_, v___x_2362_);
v___x_2364_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(v_c_2330_, v_x_2331_, v_as_2332_, v_sz_2333_, v___x_2363_, v___x_2361_, v___y_2336_);
return v___x_2364_;
}
else
{
lean_object* v___x_2365_; lean_object* v___x_2366_; 
lean_dec(v_x_2331_);
v___x_2365_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2366_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2365_, v___f_2358_, v___y_2336_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2385_; 
v_isSharedCheck_2385_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2385_ == 0)
{
lean_object* v_unused_2386_; 
v_unused_2386_ = lean_ctor_get(v___x_2366_, 0);
lean_dec(v_unused_2386_);
v___x_2368_ = v___x_2366_;
v_isShared_2369_ = v_isSharedCheck_2385_;
goto v_resetjp_2367_;
}
else
{
lean_dec(v___x_2366_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2385_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2377_; 
v___x_2370_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
lean_inc_ref(v_p_2353_);
v___x_2371_ = l_Int_Linear_Poly_addConst(v_p_2353_, v___x_2370_);
lean_inc(v_a_2354_);
v___x_2372_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_2372_, 0, v_c_2330_);
lean_ctor_set(v___x_2372_, 1, v_a_2354_);
v___x_2373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2371_);
lean_ctor_set(v___x_2373_, 1, v___x_2372_);
v___x_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2373_);
v___x_2375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2375_, 0, v___x_2374_);
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 1, v___x_2357_);
lean_ctor_set(v___x_2351_, 0, v___x_2375_);
v___x_2377_ = v___x_2351_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v___x_2375_);
lean_ctor_set(v_reuseFailAlloc_2384_, 1, v___x_2357_);
v___x_2377_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2382_; 
v___x_2378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2378_, 0, v___x_2377_);
v___x_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2378_);
v___x_2380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2379_);
lean_ctor_set(v___x_2380_, 1, v_snd_2349_);
if (v_isShared_2369_ == 0)
{
lean_ctor_set(v___x_2368_, 0, v___x_2380_);
v___x_2382_ = v___x_2368_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v___x_2380_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
return v___x_2382_;
}
}
}
}
else
{
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2394_; 
lean_del_object(v___x_2351_);
lean_dec(v_snd_2349_);
lean_dec_ref(v_c_2330_);
v_a_2387_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2389_ = v___x_2366_;
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2366_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2392_; 
if (v_isShared_2390_ == 0)
{
v___x_2392_ = v___x_2389_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_a_2387_);
v___x_2392_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
return v___x_2392_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9___boxed(lean_object** _args){
lean_object* v_c_2399_ = _args[0];
lean_object* v_x_2400_ = _args[1];
lean_object* v_as_2401_ = _args[2];
lean_object* v_sz_2402_ = _args[3];
lean_object* v_i_2403_ = _args[4];
lean_object* v_b_2404_ = _args[5];
lean_object* v___y_2405_ = _args[6];
lean_object* v___y_2406_ = _args[7];
lean_object* v___y_2407_ = _args[8];
lean_object* v___y_2408_ = _args[9];
lean_object* v___y_2409_ = _args[10];
lean_object* v___y_2410_ = _args[11];
lean_object* v___y_2411_ = _args[12];
lean_object* v___y_2412_ = _args[13];
lean_object* v___y_2413_ = _args[14];
lean_object* v___y_2414_ = _args[15];
lean_object* v___y_2415_ = _args[16];
_start:
{
size_t v_sz_boxed_2416_; size_t v_i_boxed_2417_; lean_object* v_res_2418_; 
v_sz_boxed_2416_ = lean_unbox_usize(v_sz_2402_);
lean_dec(v_sz_2402_);
v_i_boxed_2417_ = lean_unbox_usize(v_i_2403_);
lean_dec(v_i_2403_);
v_res_2418_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9(v_c_2399_, v_x_2400_, v_as_2401_, v_sz_boxed_2416_, v_i_boxed_2417_, v_b_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec(v___y_2406_);
lean_dec(v___y_2405_);
lean_dec_ref(v_as_2401_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(lean_object* v_c_2419_, lean_object* v_x_2420_, lean_object* v_inh_2421_, lean_object* v_n_2422_, lean_object* v_b_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_){
_start:
{
if (lean_obj_tag(v_n_2422_) == 0)
{
lean_object* v_cs_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2469_; 
v_cs_2435_ = lean_ctor_get(v_n_2422_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v_n_2422_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2437_ = v_n_2422_;
v_isShared_2438_ = v_isSharedCheck_2469_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_cs_2435_);
lean_dec(v_n_2422_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2469_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; size_t v_sz_2441_; size_t v___x_2442_; lean_object* v___x_2443_; 
v___x_2439_ = lean_box(0);
v___x_2440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2440_, 0, v___x_2439_);
lean_ctor_set(v___x_2440_, 1, v_b_2423_);
v_sz_2441_ = lean_array_size(v_cs_2435_);
v___x_2442_ = ((size_t)0ULL);
v___x_2443_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8(v_c_2419_, v_x_2420_, v_inh_2421_, v_cs_2435_, v_sz_2441_, v___x_2442_, v___x_2440_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_);
lean_dec_ref(v_cs_2435_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2460_; 
v_a_2444_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2460_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2446_ = v___x_2443_;
v_isShared_2447_ = v_isSharedCheck_2460_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v___x_2443_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2460_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v_fst_2448_; 
v_fst_2448_ = lean_ctor_get(v_a_2444_, 0);
if (lean_obj_tag(v_fst_2448_) == 0)
{
lean_object* v_snd_2449_; lean_object* v___x_2451_; 
v_snd_2449_ = lean_ctor_get(v_a_2444_, 1);
lean_inc(v_snd_2449_);
lean_dec(v_a_2444_);
if (v_isShared_2438_ == 0)
{
lean_ctor_set_tag(v___x_2437_, 1);
lean_ctor_set(v___x_2437_, 0, v_snd_2449_);
v___x_2451_ = v___x_2437_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_snd_2449_);
v___x_2451_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
lean_object* v___x_2453_; 
if (v_isShared_2447_ == 0)
{
lean_ctor_set(v___x_2446_, 0, v___x_2451_);
v___x_2453_ = v___x_2446_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v___x_2451_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
else
{
lean_object* v_val_2456_; lean_object* v___x_2458_; 
lean_inc_ref(v_fst_2448_);
lean_dec(v_a_2444_);
lean_del_object(v___x_2437_);
v_val_2456_ = lean_ctor_get(v_fst_2448_, 0);
lean_inc(v_val_2456_);
lean_dec_ref(v_fst_2448_);
if (v_isShared_2447_ == 0)
{
lean_ctor_set(v___x_2446_, 0, v_val_2456_);
v___x_2458_ = v___x_2446_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_val_2456_);
v___x_2458_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
return v___x_2458_;
}
}
}
}
else
{
lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2468_; 
lean_del_object(v___x_2437_);
v_a_2461_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2463_ = v___x_2443_;
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v___x_2443_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2466_; 
if (v_isShared_2464_ == 0)
{
v___x_2466_ = v___x_2463_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_a_2461_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
}
}
else
{
lean_object* v_vs_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2504_; 
v_vs_2470_ = lean_ctor_get(v_n_2422_, 0);
v_isSharedCheck_2504_ = !lean_is_exclusive(v_n_2422_);
if (v_isSharedCheck_2504_ == 0)
{
v___x_2472_ = v_n_2422_;
v_isShared_2473_ = v_isSharedCheck_2504_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_vs_2470_);
lean_dec(v_n_2422_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2504_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; size_t v_sz_2476_; size_t v___x_2477_; lean_object* v___x_2478_; 
v___x_2474_ = lean_box(0);
v___x_2475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2475_, 0, v___x_2474_);
lean_ctor_set(v___x_2475_, 1, v_b_2423_);
v_sz_2476_ = lean_array_size(v_vs_2470_);
v___x_2477_ = ((size_t)0ULL);
v___x_2478_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9(v_c_2419_, v_x_2420_, v_vs_2470_, v_sz_2476_, v___x_2477_, v___x_2475_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_);
lean_dec_ref(v_vs_2470_);
if (lean_obj_tag(v___x_2478_) == 0)
{
lean_object* v_a_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2495_; 
v_a_2479_ = lean_ctor_get(v___x_2478_, 0);
v_isSharedCheck_2495_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2481_ = v___x_2478_;
v_isShared_2482_ = v_isSharedCheck_2495_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_a_2479_);
lean_dec(v___x_2478_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2495_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v_fst_2483_; 
v_fst_2483_ = lean_ctor_get(v_a_2479_, 0);
if (lean_obj_tag(v_fst_2483_) == 0)
{
lean_object* v_snd_2484_; lean_object* v___x_2486_; 
v_snd_2484_ = lean_ctor_get(v_a_2479_, 1);
lean_inc(v_snd_2484_);
lean_dec(v_a_2479_);
if (v_isShared_2473_ == 0)
{
lean_ctor_set(v___x_2472_, 0, v_snd_2484_);
v___x_2486_ = v___x_2472_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_snd_2484_);
v___x_2486_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
lean_object* v___x_2488_; 
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 0, v___x_2486_);
v___x_2488_ = v___x_2481_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v___x_2486_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
else
{
lean_object* v_val_2491_; lean_object* v___x_2493_; 
lean_inc_ref(v_fst_2483_);
lean_dec(v_a_2479_);
lean_del_object(v___x_2472_);
v_val_2491_ = lean_ctor_get(v_fst_2483_, 0);
lean_inc(v_val_2491_);
lean_dec_ref(v_fst_2483_);
if (v_isShared_2482_ == 0)
{
lean_ctor_set(v___x_2481_, 0, v_val_2491_);
v___x_2493_ = v___x_2481_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_val_2491_);
v___x_2493_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
return v___x_2493_;
}
}
}
}
else
{
lean_object* v_a_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2503_; 
lean_del_object(v___x_2472_);
v_a_2496_ = lean_ctor_get(v___x_2478_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2478_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2498_ = v___x_2478_;
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_a_2496_);
lean_dec(v___x_2478_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2501_; 
if (v_isShared_2499_ == 0)
{
v___x_2501_ = v___x_2498_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_a_2496_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8(lean_object* v_c_2505_, lean_object* v_x_2506_, lean_object* v_inh_2507_, lean_object* v_as_2508_, size_t v_sz_2509_, size_t v_i_2510_, lean_object* v_b_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_){
_start:
{
uint8_t v___x_2523_; 
v___x_2523_ = lean_usize_dec_lt(v_i_2510_, v_sz_2509_);
if (v___x_2523_ == 0)
{
lean_object* v___x_2524_; 
lean_dec(v_x_2506_);
lean_dec_ref(v_c_2505_);
v___x_2524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2524_, 0, v_b_2511_);
return v___x_2524_;
}
else
{
lean_object* v_snd_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2559_; 
v_snd_2525_ = lean_ctor_get(v_b_2511_, 1);
v_isSharedCheck_2559_ = !lean_is_exclusive(v_b_2511_);
if (v_isSharedCheck_2559_ == 0)
{
lean_object* v_unused_2560_; 
v_unused_2560_ = lean_ctor_get(v_b_2511_, 0);
lean_dec(v_unused_2560_);
v___x_2527_ = v_b_2511_;
v_isShared_2528_ = v_isSharedCheck_2559_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_snd_2525_);
lean_dec(v_b_2511_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2559_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v_a_2529_; lean_object* v___x_2530_; 
v_a_2529_ = lean_array_uget_borrowed(v_as_2508_, v_i_2510_);
lean_inc(v_snd_2525_);
lean_inc(v_a_2529_);
lean_inc(v_x_2506_);
lean_inc_ref(v_c_2505_);
v___x_2530_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(v_c_2505_, v_x_2506_, v_inh_2507_, v_a_2529_, v_snd_2525_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_);
if (lean_obj_tag(v___x_2530_) == 0)
{
lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2550_; 
v_a_2531_ = lean_ctor_get(v___x_2530_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2533_ = v___x_2530_;
v_isShared_2534_ = v_isSharedCheck_2550_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2530_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2550_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
if (lean_obj_tag(v_a_2531_) == 0)
{
lean_object* v___x_2535_; lean_object* v___x_2537_; 
lean_dec(v_x_2506_);
lean_dec_ref(v_c_2505_);
v___x_2535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2535_, 0, v_a_2531_);
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 0, v___x_2535_);
v___x_2537_ = v___x_2527_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v___x_2535_);
lean_ctor_set(v_reuseFailAlloc_2541_, 1, v_snd_2525_);
v___x_2537_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
lean_object* v___x_2539_; 
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 0, v___x_2537_);
v___x_2539_ = v___x_2533_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v___x_2537_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
}
else
{
lean_object* v_a_2542_; lean_object* v___x_2543_; lean_object* v___x_2545_; 
lean_del_object(v___x_2533_);
lean_dec(v_snd_2525_);
v_a_2542_ = lean_ctor_get(v_a_2531_, 0);
lean_inc(v_a_2542_);
lean_dec_ref(v_a_2531_);
v___x_2543_ = lean_box(0);
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 1, v_a_2542_);
lean_ctor_set(v___x_2527_, 0, v___x_2543_);
v___x_2545_ = v___x_2527_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v___x_2543_);
lean_ctor_set(v_reuseFailAlloc_2549_, 1, v_a_2542_);
v___x_2545_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
size_t v___x_2546_; size_t v___x_2547_; 
v___x_2546_ = ((size_t)1ULL);
v___x_2547_ = lean_usize_add(v_i_2510_, v___x_2546_);
v_i_2510_ = v___x_2547_;
v_b_2511_ = v___x_2545_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2558_; 
lean_del_object(v___x_2527_);
lean_dec(v_snd_2525_);
lean_dec(v_x_2506_);
lean_dec_ref(v_c_2505_);
v_a_2551_ = lean_ctor_get(v___x_2530_, 0);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2553_ = v___x_2530_;
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_a_2551_);
lean_dec(v___x_2530_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2556_; 
if (v_isShared_2554_ == 0)
{
v___x_2556_ = v___x_2553_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_a_2551_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8___boxed(lean_object** _args){
lean_object* v_c_2561_ = _args[0];
lean_object* v_x_2562_ = _args[1];
lean_object* v_inh_2563_ = _args[2];
lean_object* v_as_2564_ = _args[3];
lean_object* v_sz_2565_ = _args[4];
lean_object* v_i_2566_ = _args[5];
lean_object* v_b_2567_ = _args[6];
lean_object* v___y_2568_ = _args[7];
lean_object* v___y_2569_ = _args[8];
lean_object* v___y_2570_ = _args[9];
lean_object* v___y_2571_ = _args[10];
lean_object* v___y_2572_ = _args[11];
lean_object* v___y_2573_ = _args[12];
lean_object* v___y_2574_ = _args[13];
lean_object* v___y_2575_ = _args[14];
lean_object* v___y_2576_ = _args[15];
lean_object* v___y_2577_ = _args[16];
lean_object* v___y_2578_ = _args[17];
_start:
{
size_t v_sz_boxed_2579_; size_t v_i_boxed_2580_; lean_object* v_res_2581_; 
v_sz_boxed_2579_ = lean_unbox_usize(v_sz_2565_);
lean_dec(v_sz_2565_);
v_i_boxed_2580_ = lean_unbox_usize(v_i_2566_);
lean_dec(v_i_2566_);
v_res_2581_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8(v_c_2561_, v_x_2562_, v_inh_2563_, v_as_2564_, v_sz_boxed_2579_, v_i_boxed_2580_, v_b_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_);
lean_dec(v___y_2577_);
lean_dec_ref(v___y_2576_);
lean_dec(v___y_2575_);
lean_dec_ref(v___y_2574_);
lean_dec(v___y_2573_);
lean_dec_ref(v___y_2572_);
lean_dec(v___y_2571_);
lean_dec_ref(v___y_2570_);
lean_dec(v___y_2569_);
lean_dec(v___y_2568_);
lean_dec_ref(v_as_2564_);
lean_dec_ref(v_inh_2563_);
return v_res_2581_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6___boxed(lean_object* v_c_2582_, lean_object* v_x_2583_, lean_object* v_inh_2584_, lean_object* v_n_2585_, lean_object* v_b_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_){
_start:
{
lean_object* v_res_2598_; 
v_res_2598_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(v_c_2582_, v_x_2583_, v_inh_2584_, v_n_2585_, v_b_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
lean_dec(v___y_2596_);
lean_dec_ref(v___y_2595_);
lean_dec(v___y_2594_);
lean_dec_ref(v___y_2593_);
lean_dec(v___y_2592_);
lean_dec_ref(v___y_2591_);
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
lean_dec(v___y_2588_);
lean_dec(v___y_2587_);
lean_dec_ref(v_inh_2584_);
return v_res_2598_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2(lean_object* v_c_2599_, lean_object* v_x_2600_, lean_object* v_t_2601_, lean_object* v_init_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_){
_start:
{
lean_object* v_root_2614_; lean_object* v_tail_2615_; lean_object* v___x_2616_; 
v_root_2614_ = lean_ctor_get(v_t_2601_, 0);
lean_inc_ref(v_root_2614_);
v_tail_2615_ = lean_ctor_get(v_t_2601_, 1);
lean_inc_ref(v_tail_2615_);
lean_dec_ref(v_t_2601_);
lean_inc_ref(v_init_2602_);
lean_inc(v_x_2600_);
lean_inc_ref(v_c_2599_);
v___x_2616_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(v_c_2599_, v_x_2600_, v_init_2602_, v_root_2614_, v_init_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_);
lean_dec_ref(v_init_2602_);
if (lean_obj_tag(v___x_2616_) == 0)
{
lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2653_; 
v_a_2617_ = lean_ctor_get(v___x_2616_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2616_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2619_ = v___x_2616_;
v_isShared_2620_ = v_isSharedCheck_2653_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_dec(v___x_2616_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2653_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
if (lean_obj_tag(v_a_2617_) == 0)
{
lean_object* v_a_2621_; lean_object* v___x_2623_; 
lean_dec_ref(v_tail_2615_);
lean_dec(v_x_2600_);
lean_dec_ref(v_c_2599_);
v_a_2621_ = lean_ctor_get(v_a_2617_, 0);
lean_inc(v_a_2621_);
lean_dec_ref(v_a_2617_);
if (v_isShared_2620_ == 0)
{
lean_ctor_set(v___x_2619_, 0, v_a_2621_);
v___x_2623_ = v___x_2619_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_a_2621_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
else
{
lean_object* v_a_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; size_t v_sz_2628_; size_t v___x_2629_; lean_object* v___x_2630_; 
lean_del_object(v___x_2619_);
v_a_2625_ = lean_ctor_get(v_a_2617_, 0);
lean_inc(v_a_2625_);
lean_dec_ref(v_a_2617_);
v___x_2626_ = lean_box(0);
v___x_2627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2626_);
lean_ctor_set(v___x_2627_, 1, v_a_2625_);
v_sz_2628_ = lean_array_size(v_tail_2615_);
v___x_2629_ = ((size_t)0ULL);
v___x_2630_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7(v_c_2599_, v_x_2600_, v_tail_2615_, v_sz_2628_, v___x_2629_, v___x_2627_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_);
lean_dec_ref(v_tail_2615_);
if (lean_obj_tag(v___x_2630_) == 0)
{
lean_object* v_a_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2644_; 
v_a_2631_ = lean_ctor_get(v___x_2630_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2633_ = v___x_2630_;
v_isShared_2634_ = v_isSharedCheck_2644_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_a_2631_);
lean_dec(v___x_2630_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2644_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v_fst_2635_; 
v_fst_2635_ = lean_ctor_get(v_a_2631_, 0);
if (lean_obj_tag(v_fst_2635_) == 0)
{
lean_object* v_snd_2636_; lean_object* v___x_2638_; 
v_snd_2636_ = lean_ctor_get(v_a_2631_, 1);
lean_inc(v_snd_2636_);
lean_dec(v_a_2631_);
if (v_isShared_2634_ == 0)
{
lean_ctor_set(v___x_2633_, 0, v_snd_2636_);
v___x_2638_ = v___x_2633_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_snd_2636_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
else
{
lean_object* v_val_2640_; lean_object* v___x_2642_; 
lean_inc_ref(v_fst_2635_);
lean_dec(v_a_2631_);
v_val_2640_ = lean_ctor_get(v_fst_2635_, 0);
lean_inc(v_val_2640_);
lean_dec_ref(v_fst_2635_);
if (v_isShared_2634_ == 0)
{
lean_ctor_set(v___x_2633_, 0, v_val_2640_);
v___x_2642_ = v___x_2633_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_val_2640_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
}
}
else
{
lean_object* v_a_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2652_; 
v_a_2645_ = lean_ctor_get(v___x_2630_, 0);
v_isSharedCheck_2652_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2647_ = v___x_2630_;
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_a_2645_);
lean_dec(v___x_2630_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2650_; 
if (v_isShared_2648_ == 0)
{
v___x_2650_ = v___x_2647_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_a_2645_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
}
}
}
}
else
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2661_; 
lean_dec_ref(v_tail_2615_);
lean_dec(v_x_2600_);
lean_dec_ref(v_c_2599_);
v_a_2654_ = lean_ctor_get(v___x_2616_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2616_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2656_ = v___x_2616_;
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v___x_2616_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2659_; 
if (v_isShared_2657_ == 0)
{
v___x_2659_ = v___x_2656_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_a_2654_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2___boxed(lean_object* v_c_2662_, lean_object* v_x_2663_, lean_object* v_t_2664_, lean_object* v_init_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_){
_start:
{
lean_object* v_res_2677_; 
v_res_2677_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2(v_c_2662_, v_x_2663_, v_t_2664_, v_init_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
lean_dec(v___y_2673_);
lean_dec_ref(v___y_2672_);
lean_dec(v___y_2671_);
lean_dec_ref(v___y_2670_);
lean_dec(v___y_2669_);
lean_dec_ref(v___y_2668_);
lean_dec(v___y_2667_);
lean_dec(v___y_2666_);
return v_res_2677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(lean_object* v_x_2678_, lean_object* v_c_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_){
_start:
{
lean_object* v___x_2691_; 
v___x_2691_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2680_, v_a_2688_);
if (lean_obj_tag(v___x_2691_) == 0)
{
lean_object* v_a_2692_; lean_object* v___y_2694_; lean_object* v_diseqs_2719_; lean_object* v_size_2720_; lean_object* v___x_2721_; uint8_t v___x_2722_; 
v_a_2692_ = lean_ctor_get(v___x_2691_, 0);
lean_inc(v_a_2692_);
lean_dec_ref(v___x_2691_);
v_diseqs_2719_ = lean_ctor_get(v_a_2692_, 9);
lean_inc_ref(v_diseqs_2719_);
lean_dec(v_a_2692_);
v_size_2720_ = lean_ctor_get(v_diseqs_2719_, 2);
v___x_2721_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0);
v___x_2722_ = lean_nat_dec_lt(v_x_2678_, v_size_2720_);
if (v___x_2722_ == 0)
{
lean_object* v___x_2723_; 
lean_dec_ref(v_diseqs_2719_);
v___x_2723_ = l_outOfBounds___redArg(v___x_2721_);
v___y_2694_ = v___x_2723_;
goto v___jp_2693_;
}
else
{
lean_object* v___x_2724_; 
v___x_2724_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2721_, v_diseqs_2719_, v_x_2678_);
v___y_2694_ = v___x_2724_;
goto v___jp_2693_;
}
v___jp_2693_:
{
lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; 
v___x_2695_ = lean_box(0);
v___x_2696_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___closed__0));
v___x_2697_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2(v_c_2679_, v_x_2678_, v___y_2694_, v___x_2696_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_);
if (lean_obj_tag(v___x_2697_) == 0)
{
lean_object* v_a_2698_; lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2710_; 
v_a_2698_ = lean_ctor_get(v___x_2697_, 0);
v_isSharedCheck_2710_ = !lean_is_exclusive(v___x_2697_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2700_ = v___x_2697_;
v_isShared_2701_ = v_isSharedCheck_2710_;
goto v_resetjp_2699_;
}
else
{
lean_inc(v_a_2698_);
lean_dec(v___x_2697_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2710_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v_fst_2702_; 
v_fst_2702_ = lean_ctor_get(v_a_2698_, 0);
lean_inc(v_fst_2702_);
lean_dec(v_a_2698_);
if (lean_obj_tag(v_fst_2702_) == 0)
{
lean_object* v___x_2704_; 
if (v_isShared_2701_ == 0)
{
lean_ctor_set(v___x_2700_, 0, v___x_2695_);
v___x_2704_ = v___x_2700_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v___x_2695_);
v___x_2704_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
return v___x_2704_;
}
}
else
{
lean_object* v_val_2706_; lean_object* v___x_2708_; 
v_val_2706_ = lean_ctor_get(v_fst_2702_, 0);
lean_inc(v_val_2706_);
lean_dec_ref(v_fst_2702_);
if (v_isShared_2701_ == 0)
{
lean_ctor_set(v___x_2700_, 0, v_val_2706_);
v___x_2708_ = v___x_2700_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_val_2706_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
return v___x_2708_;
}
}
}
}
else
{
lean_object* v_a_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2718_; 
v_a_2711_ = lean_ctor_get(v___x_2697_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2697_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2713_ = v___x_2697_;
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_a_2711_);
lean_dec(v___x_2697_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2716_; 
if (v_isShared_2714_ == 0)
{
v___x_2716_ = v___x_2713_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_a_2711_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
}
}
}
else
{
lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2732_; 
lean_dec_ref(v_c_2679_);
lean_dec(v_x_2678_);
v_a_2725_ = lean_ctor_get(v___x_2691_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2691_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2727_ = v___x_2691_;
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v___x_2691_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2732_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2730_; 
if (v_isShared_2728_ == 0)
{
v___x_2730_ = v___x_2727_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v_a_2725_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f___boxed(lean_object* v_x_2733_, lean_object* v_c_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_){
_start:
{
lean_object* v_res_2746_; 
v_res_2746_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(v_x_2733_, v_c_2734_, v_a_2735_, v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_);
lean_dec(v_a_2744_);
lean_dec_ref(v_a_2743_);
lean_dec(v_a_2742_);
lean_dec_ref(v_a_2741_);
lean_dec(v_a_2740_);
lean_dec_ref(v_a_2739_);
lean_dec(v_a_2738_);
lean_dec_ref(v_a_2737_);
lean_dec(v_a_2736_);
lean_dec(v_a_2735_);
return v_res_2746_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(lean_object* v___x_2747_, lean_object* v_inst_2748_, lean_object* v_x_2749_, size_t v_x_2750_, size_t v_x_2751_){
_start:
{
lean_object* v___x_2752_; 
v___x_2752_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___redArg(v___x_2747_, v_x_2749_, v_x_2750_, v_x_2751_);
return v___x_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___boxed(lean_object* v___x_2753_, lean_object* v_inst_2754_, lean_object* v_x_2755_, lean_object* v_x_2756_, lean_object* v_x_2757_){
_start:
{
size_t v_x_23018__boxed_2758_; size_t v_x_23019__boxed_2759_; lean_object* v_res_2760_; 
v_x_23018__boxed_2758_ = lean_unbox_usize(v_x_2756_);
lean_dec(v_x_2756_);
v_x_23019__boxed_2759_ = lean_unbox_usize(v_x_2757_);
lean_dec(v_x_2757_);
v_res_2760_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(v___x_2753_, v_inst_2754_, v_x_2755_, v_x_23018__boxed_2758_, v_x_23019__boxed_2759_);
lean_dec_ref(v_inst_2754_);
lean_dec_ref(v___x_2753_);
return v_res_2760_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11(lean_object* v_c_2761_, lean_object* v_x_2762_, lean_object* v_as_2763_, size_t v_sz_2764_, size_t v_i_2765_, lean_object* v_b_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_){
_start:
{
lean_object* v___x_2778_; 
v___x_2778_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(v_c_2761_, v_x_2762_, v_as_2763_, v_sz_2764_, v_i_2765_, v_b_2766_, v___y_2767_);
return v___x_2778_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___boxed(lean_object** _args){
lean_object* v_c_2779_ = _args[0];
lean_object* v_x_2780_ = _args[1];
lean_object* v_as_2781_ = _args[2];
lean_object* v_sz_2782_ = _args[3];
lean_object* v_i_2783_ = _args[4];
lean_object* v_b_2784_ = _args[5];
lean_object* v___y_2785_ = _args[6];
lean_object* v___y_2786_ = _args[7];
lean_object* v___y_2787_ = _args[8];
lean_object* v___y_2788_ = _args[9];
lean_object* v___y_2789_ = _args[10];
lean_object* v___y_2790_ = _args[11];
lean_object* v___y_2791_ = _args[12];
lean_object* v___y_2792_ = _args[13];
lean_object* v___y_2793_ = _args[14];
lean_object* v___y_2794_ = _args[15];
lean_object* v___y_2795_ = _args[16];
_start:
{
size_t v_sz_boxed_2796_; size_t v_i_boxed_2797_; lean_object* v_res_2798_; 
v_sz_boxed_2796_ = lean_unbox_usize(v_sz_2782_);
lean_dec(v_sz_2782_);
v_i_boxed_2797_ = lean_unbox_usize(v_i_2783_);
lean_dec(v_i_2783_);
v_res_2798_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11(v_c_2779_, v_x_2780_, v_as_2781_, v_sz_boxed_2796_, v_i_boxed_2797_, v_b_2784_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec(v___y_2792_);
lean_dec_ref(v___y_2791_);
lean_dec(v___y_2790_);
lean_dec_ref(v___y_2789_);
lean_dec(v___y_2788_);
lean_dec_ref(v___y_2787_);
lean_dec(v___y_2786_);
lean_dec(v___y_2785_);
lean_dec_ref(v_as_2781_);
return v_res_2798_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10(lean_object* v_c_2799_, lean_object* v_x_2800_, lean_object* v_as_2801_, size_t v_sz_2802_, size_t v_i_2803_, lean_object* v_b_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_){
_start:
{
lean_object* v___x_2816_; 
v___x_2816_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(v_c_2799_, v_x_2800_, v_as_2801_, v_sz_2802_, v_i_2803_, v_b_2804_, v___y_2805_);
return v___x_2816_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___boxed(lean_object** _args){
lean_object* v_c_2817_ = _args[0];
lean_object* v_x_2818_ = _args[1];
lean_object* v_as_2819_ = _args[2];
lean_object* v_sz_2820_ = _args[3];
lean_object* v_i_2821_ = _args[4];
lean_object* v_b_2822_ = _args[5];
lean_object* v___y_2823_ = _args[6];
lean_object* v___y_2824_ = _args[7];
lean_object* v___y_2825_ = _args[8];
lean_object* v___y_2826_ = _args[9];
lean_object* v___y_2827_ = _args[10];
lean_object* v___y_2828_ = _args[11];
lean_object* v___y_2829_ = _args[12];
lean_object* v___y_2830_ = _args[13];
lean_object* v___y_2831_ = _args[14];
lean_object* v___y_2832_ = _args[15];
lean_object* v___y_2833_ = _args[16];
_start:
{
size_t v_sz_boxed_2834_; size_t v_i_boxed_2835_; lean_object* v_res_2836_; 
v_sz_boxed_2834_ = lean_unbox_usize(v_sz_2820_);
lean_dec(v_sz_2820_);
v_i_boxed_2835_ = lean_unbox_usize(v_i_2821_);
lean_dec(v_i_2821_);
v_res_2836_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10(v_c_2817_, v_x_2818_, v_as_2819_, v_sz_boxed_2834_, v_i_boxed_2835_, v_b_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_);
lean_dec(v___y_2832_);
lean_dec_ref(v___y_2831_);
lean_dec(v___y_2830_);
lean_dec_ref(v___y_2829_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec(v___y_2824_);
lean_dec(v___y_2823_);
lean_dec_ref(v_as_2819_);
return v_res_2836_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0(lean_object* v_v_2837_, lean_object* v_b_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_){
_start:
{
lean_object* v_snd_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2881_; 
v_snd_2850_ = lean_ctor_get(v_b_2838_, 1);
v_isSharedCheck_2881_ = !lean_is_exclusive(v_b_2838_);
if (v_isSharedCheck_2881_ == 0)
{
lean_object* v_unused_2882_; 
v_unused_2882_ = lean_ctor_get(v_b_2838_, 0);
lean_dec(v_unused_2882_);
v___x_2852_ = v_b_2838_;
v_isShared_2853_ = v_isSharedCheck_2881_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_snd_2850_);
lean_dec(v_b_2838_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2881_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v___x_2854_; 
lean_inc(v_snd_2850_);
lean_inc(v_v_2837_);
v___x_2854_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(v_v_2837_, v_snd_2850_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v_a_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2872_; 
v_a_2855_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2872_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2857_ = v___x_2854_;
v_isShared_2858_ = v_isSharedCheck_2872_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_a_2855_);
lean_dec(v___x_2854_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2872_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
if (lean_obj_tag(v_a_2855_) == 1)
{
lean_object* v_val_2859_; lean_object* v___x_2860_; lean_object* v___x_2862_; 
lean_del_object(v___x_2857_);
lean_dec(v_snd_2850_);
v_val_2859_ = lean_ctor_get(v_a_2855_, 0);
lean_inc(v_val_2859_);
lean_dec_ref(v_a_2855_);
v___x_2860_ = lean_box(0);
if (v_isShared_2853_ == 0)
{
lean_ctor_set(v___x_2852_, 1, v_val_2859_);
lean_ctor_set(v___x_2852_, 0, v___x_2860_);
v___x_2862_ = v___x_2852_;
goto v_reusejp_2861_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v___x_2860_);
lean_ctor_set(v_reuseFailAlloc_2864_, 1, v_val_2859_);
v___x_2862_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2861_;
}
v_reusejp_2861_:
{
v_b_2838_ = v___x_2862_;
goto _start;
}
}
else
{
lean_object* v___x_2865_; lean_object* v___x_2867_; 
lean_dec(v_a_2855_);
lean_dec(v_v_2837_);
lean_inc(v_snd_2850_);
v___x_2865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2865_, 0, v_snd_2850_);
if (v_isShared_2853_ == 0)
{
lean_ctor_set(v___x_2852_, 0, v___x_2865_);
v___x_2867_ = v___x_2852_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v___x_2865_);
lean_ctor_set(v_reuseFailAlloc_2871_, 1, v_snd_2850_);
v___x_2867_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
lean_object* v___x_2869_; 
if (v_isShared_2858_ == 0)
{
lean_ctor_set(v___x_2857_, 0, v___x_2867_);
v___x_2869_ = v___x_2857_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v___x_2867_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
}
}
else
{
lean_object* v_a_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2880_; 
lean_del_object(v___x_2852_);
lean_dec(v_snd_2850_);
lean_dec(v_v_2837_);
v_a_2873_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2880_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2880_ == 0)
{
v___x_2875_ = v___x_2854_;
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_a_2873_);
lean_dec(v___x_2854_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2880_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v___x_2878_; 
if (v_isShared_2876_ == 0)
{
v___x_2878_ = v___x_2875_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v_a_2873_);
v___x_2878_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2877_;
}
v_reusejp_2877_:
{
return v___x_2878_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___boxed(lean_object* v_v_2883_, lean_object* v_b_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_){
_start:
{
lean_object* v_res_2896_; 
v_res_2896_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0(v_v_2883_, v_b_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_);
lean_dec(v___y_2894_);
lean_dec_ref(v___y_2893_);
lean_dec(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec(v___y_2885_);
return v_res_2896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(lean_object* v_c_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_){
_start:
{
lean_object* v_p_2909_; 
v_p_2909_ = lean_ctor_get(v_c_2897_, 0);
if (lean_obj_tag(v_p_2909_) == 1)
{
lean_object* v_v_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; 
v_v_2910_ = lean_ctor_get(v_p_2909_, 1);
lean_inc(v_v_2910_);
v___x_2911_ = lean_box(0);
v___x_2912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2911_);
lean_ctor_set(v___x_2912_, 1, v_c_2897_);
v___x_2913_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0(v_v_2910_, v___x_2912_, v_a_2898_, v_a_2899_, v_a_2900_, v_a_2901_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_);
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2927_; 
v_a_2914_ = lean_ctor_get(v___x_2913_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2913_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2916_ = v___x_2913_;
v_isShared_2917_ = v_isSharedCheck_2927_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v___x_2913_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2927_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v_fst_2918_; 
v_fst_2918_ = lean_ctor_get(v_a_2914_, 0);
if (lean_obj_tag(v_fst_2918_) == 0)
{
lean_object* v_snd_2919_; lean_object* v___x_2921_; 
v_snd_2919_ = lean_ctor_get(v_a_2914_, 1);
lean_inc(v_snd_2919_);
lean_dec(v_a_2914_);
if (v_isShared_2917_ == 0)
{
lean_ctor_set(v___x_2916_, 0, v_snd_2919_);
v___x_2921_ = v___x_2916_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v_snd_2919_);
v___x_2921_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
return v___x_2921_;
}
}
else
{
lean_object* v_val_2923_; lean_object* v___x_2925_; 
lean_inc_ref(v_fst_2918_);
lean_dec(v_a_2914_);
v_val_2923_ = lean_ctor_get(v_fst_2918_, 0);
lean_inc(v_val_2923_);
lean_dec_ref(v_fst_2918_);
if (v_isShared_2917_ == 0)
{
lean_ctor_set(v___x_2916_, 0, v_val_2923_);
v___x_2925_ = v___x_2916_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v_val_2923_);
v___x_2925_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
return v___x_2925_;
}
}
}
}
else
{
lean_object* v_a_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2935_; 
v_a_2928_ = lean_ctor_get(v___x_2913_, 0);
v_isSharedCheck_2935_ = !lean_is_exclusive(v___x_2913_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2930_ = v___x_2913_;
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_a_2928_);
lean_dec(v___x_2913_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v___x_2933_; 
if (v_isShared_2931_ == 0)
{
v___x_2933_ = v___x_2930_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_a_2928_);
v___x_2933_ = v_reuseFailAlloc_2934_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
return v___x_2933_;
}
}
}
}
else
{
lean_object* v___x_2936_; 
v___x_2936_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_2897_, v_a_2898_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_);
return v___x_2936_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq___boxed(lean_object* v_c_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_, lean_object* v_a_2941_, lean_object* v_a_2942_, lean_object* v_a_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_){
_start:
{
lean_object* v_res_2949_; 
v_res_2949_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(v_c_2937_, v_a_2938_, v_a_2939_, v_a_2940_, v_a_2941_, v_a_2942_, v_a_2943_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_);
lean_dec(v_a_2947_);
lean_dec_ref(v_a_2946_);
lean_dec(v_a_2945_);
lean_dec_ref(v_a_2944_);
lean_dec(v_a_2943_);
lean_dec_ref(v_a_2942_);
lean_dec(v_a_2941_);
lean_dec_ref(v_a_2940_);
lean_dec(v_a_2939_);
lean_dec(v_a_2938_);
return v_res_2949_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0___redArg(lean_object* v_a_2950_, lean_object* v_x_2951_, size_t v_x_2952_, size_t v_x_2953_){
_start:
{
if (lean_obj_tag(v_x_2951_) == 0)
{
lean_object* v_cs_2954_; size_t v_j_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; uint8_t v___x_2958_; 
v_cs_2954_ = lean_ctor_get(v_x_2951_, 0);
v_j_2955_ = lean_usize_shift_right(v_x_2952_, v_x_2953_);
v___x_2956_ = lean_usize_to_nat(v_j_2955_);
v___x_2957_ = lean_array_get_size(v_cs_2954_);
v___x_2958_ = lean_nat_dec_lt(v___x_2956_, v___x_2957_);
if (v___x_2958_ == 0)
{
lean_dec(v___x_2956_);
lean_dec_ref(v_a_2950_);
return v_x_2951_;
}
else
{
lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2976_; 
lean_inc_ref(v_cs_2954_);
v_isSharedCheck_2976_ = !lean_is_exclusive(v_x_2951_);
if (v_isSharedCheck_2976_ == 0)
{
lean_object* v_unused_2977_; 
v_unused_2977_ = lean_ctor_get(v_x_2951_, 0);
lean_dec(v_unused_2977_);
v___x_2960_ = v_x_2951_;
v_isShared_2961_ = v_isSharedCheck_2976_;
goto v_resetjp_2959_;
}
else
{
lean_dec(v_x_2951_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2976_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
size_t v___x_2962_; size_t v___x_2963_; size_t v___x_2964_; size_t v_i_2965_; size_t v___x_2966_; size_t v_shift_2967_; lean_object* v_v_2968_; lean_object* v___x_2969_; lean_object* v_xs_x27_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2974_; 
v___x_2962_ = ((size_t)1ULL);
v___x_2963_ = lean_usize_shift_left(v___x_2962_, v_x_2953_);
v___x_2964_ = lean_usize_sub(v___x_2963_, v___x_2962_);
v_i_2965_ = lean_usize_land(v_x_2952_, v___x_2964_);
v___x_2966_ = ((size_t)5ULL);
v_shift_2967_ = lean_usize_sub(v_x_2953_, v___x_2966_);
v_v_2968_ = lean_array_fget(v_cs_2954_, v___x_2956_);
v___x_2969_ = lean_box(0);
v_xs_x27_2970_ = lean_array_fset(v_cs_2954_, v___x_2956_, v___x_2969_);
v___x_2971_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0___redArg(v_a_2950_, v_v_2968_, v_i_2965_, v_shift_2967_);
v___x_2972_ = lean_array_fset(v_xs_x27_2970_, v___x_2956_, v___x_2971_);
lean_dec(v___x_2956_);
if (v_isShared_2961_ == 0)
{
lean_ctor_set(v___x_2960_, 0, v___x_2972_);
v___x_2974_ = v___x_2960_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v___x_2972_);
v___x_2974_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
return v___x_2974_;
}
}
}
}
else
{
lean_object* v_vs_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; uint8_t v___x_2981_; 
v_vs_2978_ = lean_ctor_get(v_x_2951_, 0);
v___x_2979_ = lean_usize_to_nat(v_x_2952_);
v___x_2980_ = lean_array_get_size(v_vs_2978_);
v___x_2981_ = lean_nat_dec_lt(v___x_2979_, v___x_2980_);
if (v___x_2981_ == 0)
{
lean_dec(v___x_2979_);
lean_dec_ref(v_a_2950_);
return v_x_2951_;
}
else
{
lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2993_; 
lean_inc_ref(v_vs_2978_);
v_isSharedCheck_2993_ = !lean_is_exclusive(v_x_2951_);
if (v_isSharedCheck_2993_ == 0)
{
lean_object* v_unused_2994_; 
v_unused_2994_ = lean_ctor_get(v_x_2951_, 0);
lean_dec(v_unused_2994_);
v___x_2983_ = v_x_2951_;
v_isShared_2984_ = v_isSharedCheck_2993_;
goto v_resetjp_2982_;
}
else
{
lean_dec(v_x_2951_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2993_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v_v_2985_; lean_object* v___x_2986_; lean_object* v_xs_x27_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2991_; 
v_v_2985_ = lean_array_fget(v_vs_2978_, v___x_2979_);
v___x_2986_ = lean_box(0);
v_xs_x27_2987_ = lean_array_fset(v_vs_2978_, v___x_2979_, v___x_2986_);
v___x_2988_ = l_Lean_PersistentArray_push___redArg(v_v_2985_, v_a_2950_);
v___x_2989_ = lean_array_fset(v_xs_x27_2987_, v___x_2979_, v___x_2988_);
lean_dec(v___x_2979_);
if (v_isShared_2984_ == 0)
{
lean_ctor_set(v___x_2983_, 0, v___x_2989_);
v___x_2991_ = v___x_2983_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v___x_2989_);
v___x_2991_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
return v___x_2991_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0___redArg___boxed(lean_object* v_a_2995_, lean_object* v_x_2996_, lean_object* v_x_2997_, lean_object* v_x_2998_){
_start:
{
size_t v_x_73403__boxed_2999_; size_t v_x_73404__boxed_3000_; lean_object* v_res_3001_; 
v_x_73403__boxed_2999_ = lean_unbox_usize(v_x_2997_);
lean_dec(v_x_2997_);
v_x_73404__boxed_3000_ = lean_unbox_usize(v_x_2998_);
lean_dec(v_x_2998_);
v_res_3001_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0___redArg(v_a_2995_, v_x_2996_, v_x_73403__boxed_2999_, v_x_73404__boxed_3000_);
return v_res_3001_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(lean_object* v_a_3002_, lean_object* v_inst_3003_, lean_object* v_t_3004_, lean_object* v_i_3005_){
_start:
{
lean_object* v_root_3006_; lean_object* v_tail_3007_; lean_object* v_size_3008_; size_t v_shift_3009_; lean_object* v_tailOff_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3034_; 
v_root_3006_ = lean_ctor_get(v_t_3004_, 0);
v_tail_3007_ = lean_ctor_get(v_t_3004_, 1);
v_size_3008_ = lean_ctor_get(v_t_3004_, 2);
v_shift_3009_ = lean_ctor_get_usize(v_t_3004_, 4);
v_tailOff_3010_ = lean_ctor_get(v_t_3004_, 3);
v_isSharedCheck_3034_ = !lean_is_exclusive(v_t_3004_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3012_ = v_t_3004_;
v_isShared_3013_ = v_isSharedCheck_3034_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_tailOff_3010_);
lean_inc(v_size_3008_);
lean_inc(v_tail_3007_);
lean_inc(v_root_3006_);
lean_dec(v_t_3004_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3034_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
uint8_t v___x_3014_; 
v___x_3014_ = lean_nat_dec_le(v_tailOff_3010_, v_i_3005_);
if (v___x_3014_ == 0)
{
size_t v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3018_; 
v___x_3015_ = lean_usize_of_nat(v_i_3005_);
v___x_3016_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0___redArg(v_a_3002_, v_root_3006_, v___x_3015_, v_shift_3009_);
if (v_isShared_3013_ == 0)
{
lean_ctor_set(v___x_3012_, 0, v___x_3016_);
v___x_3018_ = v___x_3012_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v___x_3016_);
lean_ctor_set(v_reuseFailAlloc_3019_, 1, v_tail_3007_);
lean_ctor_set(v_reuseFailAlloc_3019_, 2, v_size_3008_);
lean_ctor_set(v_reuseFailAlloc_3019_, 3, v_tailOff_3010_);
lean_ctor_set_usize(v_reuseFailAlloc_3019_, 4, v_shift_3009_);
v___x_3018_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
return v___x_3018_;
}
}
else
{
lean_object* v___x_3020_; lean_object* v___x_3021_; uint8_t v___x_3022_; 
v___x_3020_ = lean_nat_sub(v_i_3005_, v_tailOff_3010_);
v___x_3021_ = lean_array_get_size(v_tail_3007_);
v___x_3022_ = lean_nat_dec_lt(v___x_3020_, v___x_3021_);
if (v___x_3022_ == 0)
{
lean_object* v___x_3024_; 
lean_dec(v___x_3020_);
lean_dec_ref(v_a_3002_);
if (v_isShared_3013_ == 0)
{
v___x_3024_ = v___x_3012_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_root_3006_);
lean_ctor_set(v_reuseFailAlloc_3025_, 1, v_tail_3007_);
lean_ctor_set(v_reuseFailAlloc_3025_, 2, v_size_3008_);
lean_ctor_set(v_reuseFailAlloc_3025_, 3, v_tailOff_3010_);
lean_ctor_set_usize(v_reuseFailAlloc_3025_, 4, v_shift_3009_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
return v___x_3024_;
}
}
else
{
lean_object* v_v_3026_; lean_object* v___x_3027_; lean_object* v_xs_x27_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3032_; 
v_v_3026_ = lean_array_fget(v_tail_3007_, v___x_3020_);
v___x_3027_ = lean_box(0);
v_xs_x27_3028_ = lean_array_fset(v_tail_3007_, v___x_3020_, v___x_3027_);
v___x_3029_ = l_Lean_PersistentArray_push___redArg(v_v_3026_, v_a_3002_);
v___x_3030_ = lean_array_fset(v_xs_x27_3028_, v___x_3020_, v___x_3029_);
lean_dec(v___x_3020_);
if (v_isShared_3013_ == 0)
{
lean_ctor_set(v___x_3012_, 1, v___x_3030_);
v___x_3032_ = v___x_3012_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_root_3006_);
lean_ctor_set(v_reuseFailAlloc_3033_, 1, v___x_3030_);
lean_ctor_set(v_reuseFailAlloc_3033_, 2, v_size_3008_);
lean_ctor_set(v_reuseFailAlloc_3033_, 3, v_tailOff_3010_);
lean_ctor_set_usize(v_reuseFailAlloc_3033_, 4, v_shift_3009_);
v___x_3032_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
return v___x_3032_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0___boxed(lean_object* v_a_3035_, lean_object* v_inst_3036_, lean_object* v_t_3037_, lean_object* v_i_3038_){
_start:
{
lean_object* v_res_3039_; 
v_res_3039_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(v_a_3035_, v_inst_3036_, v_t_3037_, v_i_3038_);
lean_dec(v_i_3038_);
lean_dec_ref(v_inst_3036_);
return v_res_3039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0(lean_object* v_a_3040_, lean_object* v_v_3041_, lean_object* v_s_3042_){
_start:
{
lean_object* v_vars_3043_; lean_object* v_varMap_3044_; lean_object* v_vars_x27_3045_; lean_object* v_varMap_x27_3046_; lean_object* v_natToIntMap_3047_; lean_object* v_natDef_3048_; lean_object* v_dvds_3049_; lean_object* v_lowers_3050_; lean_object* v_uppers_3051_; lean_object* v_diseqs_3052_; lean_object* v_elimEqs_3053_; lean_object* v_elimStack_3054_; lean_object* v_occurs_3055_; lean_object* v_assignment_3056_; lean_object* v_nextCnstrId_3057_; uint8_t v_caseSplits_3058_; lean_object* v_conflict_x3f_3059_; lean_object* v_diseqSplits_3060_; lean_object* v_divMod_3061_; lean_object* v_toIntIds_3062_; lean_object* v_toIntInfos_3063_; lean_object* v_toIntTermMap_3064_; lean_object* v_toIntVarMap_3065_; uint8_t v_usedCommRing_3066_; lean_object* v_nonlinearOccs_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3076_; 
v_vars_3043_ = lean_ctor_get(v_s_3042_, 0);
v_varMap_3044_ = lean_ctor_get(v_s_3042_, 1);
v_vars_x27_3045_ = lean_ctor_get(v_s_3042_, 2);
v_varMap_x27_3046_ = lean_ctor_get(v_s_3042_, 3);
v_natToIntMap_3047_ = lean_ctor_get(v_s_3042_, 4);
v_natDef_3048_ = lean_ctor_get(v_s_3042_, 5);
v_dvds_3049_ = lean_ctor_get(v_s_3042_, 6);
v_lowers_3050_ = lean_ctor_get(v_s_3042_, 7);
v_uppers_3051_ = lean_ctor_get(v_s_3042_, 8);
v_diseqs_3052_ = lean_ctor_get(v_s_3042_, 9);
v_elimEqs_3053_ = lean_ctor_get(v_s_3042_, 10);
v_elimStack_3054_ = lean_ctor_get(v_s_3042_, 11);
v_occurs_3055_ = lean_ctor_get(v_s_3042_, 12);
v_assignment_3056_ = lean_ctor_get(v_s_3042_, 13);
v_nextCnstrId_3057_ = lean_ctor_get(v_s_3042_, 14);
v_caseSplits_3058_ = lean_ctor_get_uint8(v_s_3042_, sizeof(void*)*23);
v_conflict_x3f_3059_ = lean_ctor_get(v_s_3042_, 15);
v_diseqSplits_3060_ = lean_ctor_get(v_s_3042_, 16);
v_divMod_3061_ = lean_ctor_get(v_s_3042_, 17);
v_toIntIds_3062_ = lean_ctor_get(v_s_3042_, 18);
v_toIntInfos_3063_ = lean_ctor_get(v_s_3042_, 19);
v_toIntTermMap_3064_ = lean_ctor_get(v_s_3042_, 20);
v_toIntVarMap_3065_ = lean_ctor_get(v_s_3042_, 21);
v_usedCommRing_3066_ = lean_ctor_get_uint8(v_s_3042_, sizeof(void*)*23 + 1);
v_nonlinearOccs_3067_ = lean_ctor_get(v_s_3042_, 22);
v_isSharedCheck_3076_ = !lean_is_exclusive(v_s_3042_);
if (v_isSharedCheck_3076_ == 0)
{
v___x_3069_ = v_s_3042_;
v_isShared_3070_ = v_isSharedCheck_3076_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_nonlinearOccs_3067_);
lean_inc(v_toIntVarMap_3065_);
lean_inc(v_toIntTermMap_3064_);
lean_inc(v_toIntInfos_3063_);
lean_inc(v_toIntIds_3062_);
lean_inc(v_divMod_3061_);
lean_inc(v_diseqSplits_3060_);
lean_inc(v_conflict_x3f_3059_);
lean_inc(v_nextCnstrId_3057_);
lean_inc(v_assignment_3056_);
lean_inc(v_occurs_3055_);
lean_inc(v_elimStack_3054_);
lean_inc(v_elimEqs_3053_);
lean_inc(v_diseqs_3052_);
lean_inc(v_uppers_3051_);
lean_inc(v_lowers_3050_);
lean_inc(v_dvds_3049_);
lean_inc(v_natDef_3048_);
lean_inc(v_natToIntMap_3047_);
lean_inc(v_varMap_x27_3046_);
lean_inc(v_vars_x27_3045_);
lean_inc(v_varMap_3044_);
lean_inc(v_vars_3043_);
lean_dec(v_s_3042_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3076_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3074_; 
v___x_3071_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0);
v___x_3072_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(v_a_3040_, v___x_3071_, v_uppers_3051_, v_v_3041_);
if (v_isShared_3070_ == 0)
{
lean_ctor_set(v___x_3069_, 8, v___x_3072_);
v___x_3074_ = v___x_3069_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v_vars_3043_);
lean_ctor_set(v_reuseFailAlloc_3075_, 1, v_varMap_3044_);
lean_ctor_set(v_reuseFailAlloc_3075_, 2, v_vars_x27_3045_);
lean_ctor_set(v_reuseFailAlloc_3075_, 3, v_varMap_x27_3046_);
lean_ctor_set(v_reuseFailAlloc_3075_, 4, v_natToIntMap_3047_);
lean_ctor_set(v_reuseFailAlloc_3075_, 5, v_natDef_3048_);
lean_ctor_set(v_reuseFailAlloc_3075_, 6, v_dvds_3049_);
lean_ctor_set(v_reuseFailAlloc_3075_, 7, v_lowers_3050_);
lean_ctor_set(v_reuseFailAlloc_3075_, 8, v___x_3072_);
lean_ctor_set(v_reuseFailAlloc_3075_, 9, v_diseqs_3052_);
lean_ctor_set(v_reuseFailAlloc_3075_, 10, v_elimEqs_3053_);
lean_ctor_set(v_reuseFailAlloc_3075_, 11, v_elimStack_3054_);
lean_ctor_set(v_reuseFailAlloc_3075_, 12, v_occurs_3055_);
lean_ctor_set(v_reuseFailAlloc_3075_, 13, v_assignment_3056_);
lean_ctor_set(v_reuseFailAlloc_3075_, 14, v_nextCnstrId_3057_);
lean_ctor_set(v_reuseFailAlloc_3075_, 15, v_conflict_x3f_3059_);
lean_ctor_set(v_reuseFailAlloc_3075_, 16, v_diseqSplits_3060_);
lean_ctor_set(v_reuseFailAlloc_3075_, 17, v_divMod_3061_);
lean_ctor_set(v_reuseFailAlloc_3075_, 18, v_toIntIds_3062_);
lean_ctor_set(v_reuseFailAlloc_3075_, 19, v_toIntInfos_3063_);
lean_ctor_set(v_reuseFailAlloc_3075_, 20, v_toIntTermMap_3064_);
lean_ctor_set(v_reuseFailAlloc_3075_, 21, v_toIntVarMap_3065_);
lean_ctor_set(v_reuseFailAlloc_3075_, 22, v_nonlinearOccs_3067_);
lean_ctor_set_uint8(v_reuseFailAlloc_3075_, sizeof(void*)*23, v_caseSplits_3058_);
lean_ctor_set_uint8(v_reuseFailAlloc_3075_, sizeof(void*)*23 + 1, v_usedCommRing_3066_);
v___x_3074_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
return v___x_3074_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0___boxed(lean_object* v_a_3077_, lean_object* v_v_3078_, lean_object* v_s_3079_){
_start:
{
lean_object* v_res_3080_; 
v_res_3080_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0(v_a_3077_, v_v_3078_, v_s_3079_);
lean_dec(v_v_3078_);
return v_res_3080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1(lean_object* v_a_3081_, lean_object* v_v_3082_, lean_object* v_s_3083_){
_start:
{
lean_object* v_vars_3084_; lean_object* v_varMap_3085_; lean_object* v_vars_x27_3086_; lean_object* v_varMap_x27_3087_; lean_object* v_natToIntMap_3088_; lean_object* v_natDef_3089_; lean_object* v_dvds_3090_; lean_object* v_lowers_3091_; lean_object* v_uppers_3092_; lean_object* v_diseqs_3093_; lean_object* v_elimEqs_3094_; lean_object* v_elimStack_3095_; lean_object* v_occurs_3096_; lean_object* v_assignment_3097_; lean_object* v_nextCnstrId_3098_; uint8_t v_caseSplits_3099_; lean_object* v_conflict_x3f_3100_; lean_object* v_diseqSplits_3101_; lean_object* v_divMod_3102_; lean_object* v_toIntIds_3103_; lean_object* v_toIntInfos_3104_; lean_object* v_toIntTermMap_3105_; lean_object* v_toIntVarMap_3106_; uint8_t v_usedCommRing_3107_; lean_object* v_nonlinearOccs_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3117_; 
v_vars_3084_ = lean_ctor_get(v_s_3083_, 0);
v_varMap_3085_ = lean_ctor_get(v_s_3083_, 1);
v_vars_x27_3086_ = lean_ctor_get(v_s_3083_, 2);
v_varMap_x27_3087_ = lean_ctor_get(v_s_3083_, 3);
v_natToIntMap_3088_ = lean_ctor_get(v_s_3083_, 4);
v_natDef_3089_ = lean_ctor_get(v_s_3083_, 5);
v_dvds_3090_ = lean_ctor_get(v_s_3083_, 6);
v_lowers_3091_ = lean_ctor_get(v_s_3083_, 7);
v_uppers_3092_ = lean_ctor_get(v_s_3083_, 8);
v_diseqs_3093_ = lean_ctor_get(v_s_3083_, 9);
v_elimEqs_3094_ = lean_ctor_get(v_s_3083_, 10);
v_elimStack_3095_ = lean_ctor_get(v_s_3083_, 11);
v_occurs_3096_ = lean_ctor_get(v_s_3083_, 12);
v_assignment_3097_ = lean_ctor_get(v_s_3083_, 13);
v_nextCnstrId_3098_ = lean_ctor_get(v_s_3083_, 14);
v_caseSplits_3099_ = lean_ctor_get_uint8(v_s_3083_, sizeof(void*)*23);
v_conflict_x3f_3100_ = lean_ctor_get(v_s_3083_, 15);
v_diseqSplits_3101_ = lean_ctor_get(v_s_3083_, 16);
v_divMod_3102_ = lean_ctor_get(v_s_3083_, 17);
v_toIntIds_3103_ = lean_ctor_get(v_s_3083_, 18);
v_toIntInfos_3104_ = lean_ctor_get(v_s_3083_, 19);
v_toIntTermMap_3105_ = lean_ctor_get(v_s_3083_, 20);
v_toIntVarMap_3106_ = lean_ctor_get(v_s_3083_, 21);
v_usedCommRing_3107_ = lean_ctor_get_uint8(v_s_3083_, sizeof(void*)*23 + 1);
v_nonlinearOccs_3108_ = lean_ctor_get(v_s_3083_, 22);
v_isSharedCheck_3117_ = !lean_is_exclusive(v_s_3083_);
if (v_isSharedCheck_3117_ == 0)
{
v___x_3110_ = v_s_3083_;
v_isShared_3111_ = v_isSharedCheck_3117_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_nonlinearOccs_3108_);
lean_inc(v_toIntVarMap_3106_);
lean_inc(v_toIntTermMap_3105_);
lean_inc(v_toIntInfos_3104_);
lean_inc(v_toIntIds_3103_);
lean_inc(v_divMod_3102_);
lean_inc(v_diseqSplits_3101_);
lean_inc(v_conflict_x3f_3100_);
lean_inc(v_nextCnstrId_3098_);
lean_inc(v_assignment_3097_);
lean_inc(v_occurs_3096_);
lean_inc(v_elimStack_3095_);
lean_inc(v_elimEqs_3094_);
lean_inc(v_diseqs_3093_);
lean_inc(v_uppers_3092_);
lean_inc(v_lowers_3091_);
lean_inc(v_dvds_3090_);
lean_inc(v_natDef_3089_);
lean_inc(v_natToIntMap_3088_);
lean_inc(v_varMap_x27_3087_);
lean_inc(v_vars_x27_3086_);
lean_inc(v_varMap_3085_);
lean_inc(v_vars_3084_);
lean_dec(v_s_3083_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3117_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3115_; 
v___x_3112_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0);
v___x_3113_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(v_a_3081_, v___x_3112_, v_lowers_3091_, v_v_3082_);
if (v_isShared_3111_ == 0)
{
lean_ctor_set(v___x_3110_, 7, v___x_3113_);
v___x_3115_ = v___x_3110_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v_vars_3084_);
lean_ctor_set(v_reuseFailAlloc_3116_, 1, v_varMap_3085_);
lean_ctor_set(v_reuseFailAlloc_3116_, 2, v_vars_x27_3086_);
lean_ctor_set(v_reuseFailAlloc_3116_, 3, v_varMap_x27_3087_);
lean_ctor_set(v_reuseFailAlloc_3116_, 4, v_natToIntMap_3088_);
lean_ctor_set(v_reuseFailAlloc_3116_, 5, v_natDef_3089_);
lean_ctor_set(v_reuseFailAlloc_3116_, 6, v_dvds_3090_);
lean_ctor_set(v_reuseFailAlloc_3116_, 7, v___x_3113_);
lean_ctor_set(v_reuseFailAlloc_3116_, 8, v_uppers_3092_);
lean_ctor_set(v_reuseFailAlloc_3116_, 9, v_diseqs_3093_);
lean_ctor_set(v_reuseFailAlloc_3116_, 10, v_elimEqs_3094_);
lean_ctor_set(v_reuseFailAlloc_3116_, 11, v_elimStack_3095_);
lean_ctor_set(v_reuseFailAlloc_3116_, 12, v_occurs_3096_);
lean_ctor_set(v_reuseFailAlloc_3116_, 13, v_assignment_3097_);
lean_ctor_set(v_reuseFailAlloc_3116_, 14, v_nextCnstrId_3098_);
lean_ctor_set(v_reuseFailAlloc_3116_, 15, v_conflict_x3f_3100_);
lean_ctor_set(v_reuseFailAlloc_3116_, 16, v_diseqSplits_3101_);
lean_ctor_set(v_reuseFailAlloc_3116_, 17, v_divMod_3102_);
lean_ctor_set(v_reuseFailAlloc_3116_, 18, v_toIntIds_3103_);
lean_ctor_set(v_reuseFailAlloc_3116_, 19, v_toIntInfos_3104_);
lean_ctor_set(v_reuseFailAlloc_3116_, 20, v_toIntTermMap_3105_);
lean_ctor_set(v_reuseFailAlloc_3116_, 21, v_toIntVarMap_3106_);
lean_ctor_set(v_reuseFailAlloc_3116_, 22, v_nonlinearOccs_3108_);
lean_ctor_set_uint8(v_reuseFailAlloc_3116_, sizeof(void*)*23, v_caseSplits_3099_);
lean_ctor_set_uint8(v_reuseFailAlloc_3116_, sizeof(void*)*23 + 1, v_usedCommRing_3107_);
v___x_3115_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
return v___x_3115_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1___boxed(lean_object* v_a_3118_, lean_object* v_v_3119_, lean_object* v_s_3120_){
_start:
{
lean_object* v_res_3121_; 
v_res_3121_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1(v_a_3118_, v_v_3119_, v_s_3120_);
lean_dec(v_v_3119_);
return v_res_3121_;
}
}
LEAN_EXPORT lean_object* lean_grind_cutsat_assert_le(lean_object* v_c_3145_, lean_object* v_a_3146_, lean_object* v_a_3147_, lean_object* v_a_3148_, lean_object* v_a_3149_, lean_object* v_a_3150_, lean_object* v_a_3151_, lean_object* v_a_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_){
_start:
{
lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v___y_3190_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___y_3193_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3207_; lean_object* v___y_3208_; lean_object* v___y_3209_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___x_3229_; 
v___x_3229_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_3146_, v_a_3154_);
if (lean_obj_tag(v___x_3229_) == 0)
{
lean_object* v_a_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3358_; 
v_a_3230_ = lean_ctor_get(v___x_3229_, 0);
v_isSharedCheck_3358_ = !lean_is_exclusive(v___x_3229_);
if (v_isSharedCheck_3358_ == 0)
{
v___x_3232_ = v___x_3229_;
v_isShared_3233_ = v_isSharedCheck_3358_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_a_3230_);
lean_dec(v___x_3229_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3358_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
uint8_t v___x_3234_; 
v___x_3234_ = lean_unbox(v_a_3230_);
lean_dec(v_a_3230_);
if (v___x_3234_ == 0)
{
lean_object* v___y_3236_; lean_object* v___y_3237_; lean_object* v___y_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___x_3339_; lean_object* v___x_3340_; lean_object* v_a_3341_; uint8_t v___x_3342_; 
lean_del_object(v___x_3232_);
v___x_3339_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__7));
v___x_3340_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3339_, v_a_3154_);
v_a_3341_ = lean_ctor_get(v___x_3340_, 0);
lean_inc(v_a_3341_);
lean_dec_ref(v___x_3340_);
v___x_3342_ = lean_unbox(v_a_3341_);
lean_dec(v_a_3341_);
if (v___x_3342_ == 0)
{
v___y_3236_ = v_a_3146_;
v___y_3237_ = v_a_3147_;
v___y_3238_ = v_a_3148_;
v___y_3239_ = v_a_3149_;
v___y_3240_ = v_a_3150_;
v___y_3241_ = v_a_3151_;
v___y_3242_ = v_a_3152_;
v___y_3243_ = v_a_3153_;
v___y_3244_ = v_a_3154_;
v___y_3245_ = v_a_3155_;
goto v___jp_3235_;
}
else
{
lean_object* v___x_3343_; 
lean_inc_ref(v_c_3145_);
v___x_3343_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_3145_, v_a_3146_, v_a_3154_);
if (lean_obj_tag(v___x_3343_) == 0)
{
lean_object* v_a_3344_; lean_object* v___x_3345_; 
v_a_3344_ = lean_ctor_get(v___x_3343_, 0);
lean_inc(v_a_3344_);
lean_dec_ref(v___x_3343_);
v___x_3345_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1___redArg(v___x_3339_, v_a_3344_, v_a_3152_, v_a_3153_, v_a_3154_, v_a_3155_);
if (lean_obj_tag(v___x_3345_) == 0)
{
lean_dec_ref(v___x_3345_);
v___y_3236_ = v_a_3146_;
v___y_3237_ = v_a_3147_;
v___y_3238_ = v_a_3148_;
v___y_3239_ = v_a_3149_;
v___y_3240_ = v_a_3150_;
v___y_3241_ = v_a_3151_;
v___y_3242_ = v_a_3152_;
v___y_3243_ = v_a_3153_;
v___y_3244_ = v_a_3154_;
v___y_3245_ = v_a_3155_;
goto v___jp_3235_;
}
else
{
lean_dec(v_a_3155_);
lean_dec_ref(v_a_3154_);
lean_dec(v_a_3153_);
lean_dec_ref(v_a_3152_);
lean_dec(v_a_3151_);
lean_dec_ref(v_a_3150_);
lean_dec(v_a_3149_);
lean_dec_ref(v_a_3148_);
lean_dec(v_a_3147_);
lean_dec(v_a_3146_);
lean_dec_ref(v_c_3145_);
return v___x_3345_;
}
}
else
{
lean_object* v_a_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3353_; 
lean_dec(v_a_3155_);
lean_dec_ref(v_a_3154_);
lean_dec(v_a_3153_);
lean_dec_ref(v_a_3152_);
lean_dec(v_a_3151_);
lean_dec_ref(v_a_3150_);
lean_dec(v_a_3149_);
lean_dec_ref(v_a_3148_);
lean_dec(v_a_3147_);
lean_dec(v_a_3146_);
lean_dec_ref(v_c_3145_);
v_a_3346_ = lean_ctor_get(v___x_3343_, 0);
v_isSharedCheck_3353_ = !lean_is_exclusive(v___x_3343_);
if (v_isSharedCheck_3353_ == 0)
{
v___x_3348_ = v___x_3343_;
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_a_3346_);
lean_dec(v___x_3343_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3353_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
lean_object* v___x_3351_; 
if (v_isShared_3349_ == 0)
{
v___x_3351_ = v___x_3348_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v_a_3346_);
v___x_3351_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
return v___x_3351_;
}
}
}
}
v___jp_3235_:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; 
v___x_3246_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_norm(v_c_3145_);
lean_inc_ref(v___y_3244_);
v___x_3247_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts(v___x_3246_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_);
if (lean_obj_tag(v___x_3247_) == 0)
{
lean_object* v_a_3248_; lean_object* v_p_3249_; uint8_t v___x_3250_; 
v_a_3248_ = lean_ctor_get(v___x_3247_, 0);
lean_inc(v_a_3248_);
lean_dec_ref(v___x_3247_);
v_p_3249_ = lean_ctor_get(v_a_3248_, 0);
v___x_3250_ = l_Int_Linear_Poly_isUnsatLe(v_p_3249_);
if (v___x_3250_ == 0)
{
uint8_t v___x_3251_; 
v___x_3251_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(v_a_3248_);
if (v___x_3251_ == 0)
{
if (lean_obj_tag(v_p_3249_) == 1)
{
lean_object* v_k_3252_; lean_object* v_v_3253_; lean_object* v___x_3254_; 
v_k_3252_ = lean_ctor_get(v_p_3249_, 0);
lean_inc(v_k_3252_);
v_v_3253_ = lean_ctor_get(v_p_3249_, 1);
lean_inc(v_v_3253_);
lean_inc(v_a_3248_);
v___x_3254_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq(v_a_3248_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_);
if (lean_obj_tag(v___x_3254_) == 0)
{
lean_object* v_a_3255_; lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3291_; 
v_a_3255_ = lean_ctor_get(v___x_3254_, 0);
v_isSharedCheck_3291_ = !lean_is_exclusive(v___x_3254_);
if (v_isSharedCheck_3291_ == 0)
{
v___x_3257_ = v___x_3254_;
v_isShared_3258_ = v_isSharedCheck_3291_;
goto v_resetjp_3256_;
}
else
{
lean_inc(v_a_3255_);
lean_dec(v___x_3254_);
v___x_3257_ = lean_box(0);
v_isShared_3258_ = v_isSharedCheck_3291_;
goto v_resetjp_3256_;
}
v_resetjp_3256_:
{
uint8_t v___x_3259_; 
v___x_3259_ = lean_unbox(v_a_3255_);
lean_dec(v_a_3255_);
if (v___x_3259_ == 0)
{
lean_object* v___x_3260_; 
lean_del_object(v___x_3257_);
v___x_3260_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(v_a_3248_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_);
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
lean_dec(v___y_3239_);
lean_dec_ref(v___y_3238_);
lean_dec(v___y_3237_);
if (lean_obj_tag(v___x_3260_) == 0)
{
lean_object* v_a_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v_a_3264_; lean_object* v___f_3265_; lean_object* v___f_3266_; uint8_t v___x_3267_; 
v_a_3261_ = lean_ctor_get(v___x_3260_, 0);
lean_inc(v_a_3261_);
lean_dec_ref(v___x_3260_);
v___x_3262_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2));
v___x_3263_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3262_, v___y_3244_);
v_a_3264_ = lean_ctor_get(v___x_3263_, 0);
lean_inc(v_a_3264_);
lean_dec_ref(v___x_3263_);
lean_inc(v_v_3253_);
lean_inc(v_a_3261_);
v___f_3265_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3265_, 0, v_a_3261_);
lean_closure_set(v___f_3265_, 1, v_v_3253_);
lean_inc(v_v_3253_);
lean_inc(v_a_3261_);
v___f_3266_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3266_, 0, v_a_3261_);
lean_closure_set(v___f_3266_, 1, v_v_3253_);
v___x_3267_ = lean_unbox(v_a_3264_);
lean_dec(v_a_3264_);
if (v___x_3267_ == 0)
{
v___y_3188_ = v___f_3266_;
v___y_3189_ = v___f_3265_;
v___y_3190_ = v_k_3252_;
v___y_3191_ = v_a_3261_;
v___y_3192_ = v_v_3253_;
v___y_3193_ = v___y_3236_;
v___y_3194_ = v___y_3242_;
v___y_3195_ = v___y_3243_;
v___y_3196_ = v___y_3244_;
v___y_3197_ = v___y_3245_;
goto v___jp_3187_;
}
else
{
lean_object* v___x_3268_; 
lean_inc(v_a_3261_);
v___x_3268_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_a_3261_, v___y_3236_, v___y_3244_);
if (lean_obj_tag(v___x_3268_) == 0)
{
lean_object* v_a_3269_; lean_object* v___x_3270_; 
v_a_3269_ = lean_ctor_get(v___x_3268_, 0);
lean_inc(v_a_3269_);
lean_dec_ref(v___x_3268_);
v___x_3270_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1___redArg(v___x_3262_, v_a_3269_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_);
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_dec_ref(v___x_3270_);
v___y_3188_ = v___f_3266_;
v___y_3189_ = v___f_3265_;
v___y_3190_ = v_k_3252_;
v___y_3191_ = v_a_3261_;
v___y_3192_ = v_v_3253_;
v___y_3193_ = v___y_3236_;
v___y_3194_ = v___y_3242_;
v___y_3195_ = v___y_3243_;
v___y_3196_ = v___y_3244_;
v___y_3197_ = v___y_3245_;
goto v___jp_3187_;
}
else
{
lean_dec_ref(v___f_3266_);
lean_dec_ref(v___f_3265_);
lean_dec(v_a_3261_);
lean_dec(v_v_3253_);
lean_dec(v_k_3252_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec(v___y_3236_);
return v___x_3270_;
}
}
else
{
lean_object* v_a_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3278_; 
lean_dec_ref(v___f_3266_);
lean_dec_ref(v___f_3265_);
lean_dec(v_a_3261_);
lean_dec(v_v_3253_);
lean_dec(v_k_3252_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec(v___y_3236_);
v_a_3271_ = lean_ctor_get(v___x_3268_, 0);
v_isSharedCheck_3278_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3273_ = v___x_3268_;
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_a_3271_);
lean_dec(v___x_3268_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3278_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v___x_3276_; 
if (v_isShared_3274_ == 0)
{
v___x_3276_ = v___x_3273_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v_a_3271_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
return v___x_3276_;
}
}
}
}
}
else
{
lean_object* v_a_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3286_; 
lean_dec(v_v_3253_);
lean_dec(v_k_3252_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec(v___y_3236_);
v_a_3279_ = lean_ctor_get(v___x_3260_, 0);
v_isSharedCheck_3286_ = !lean_is_exclusive(v___x_3260_);
if (v_isSharedCheck_3286_ == 0)
{
v___x_3281_ = v___x_3260_;
v_isShared_3282_ = v_isSharedCheck_3286_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_a_3279_);
lean_dec(v___x_3260_);
v___x_3281_ = lean_box(0);
v_isShared_3282_ = v_isSharedCheck_3286_;
goto v_resetjp_3280_;
}
v_resetjp_3280_:
{
lean_object* v___x_3284_; 
if (v_isShared_3282_ == 0)
{
v___x_3284_ = v___x_3281_;
goto v_reusejp_3283_;
}
else
{
lean_object* v_reuseFailAlloc_3285_; 
v_reuseFailAlloc_3285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3285_, 0, v_a_3279_);
v___x_3284_ = v_reuseFailAlloc_3285_;
goto v_reusejp_3283_;
}
v_reusejp_3283_:
{
return v___x_3284_;
}
}
}
}
else
{
lean_object* v___x_3287_; lean_object* v___x_3289_; 
lean_dec(v_v_3253_);
lean_dec(v_k_3252_);
lean_dec(v_a_3248_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
lean_dec(v___y_3239_);
lean_dec_ref(v___y_3238_);
lean_dec(v___y_3237_);
lean_dec(v___y_3236_);
v___x_3287_ = lean_box(0);
if (v_isShared_3258_ == 0)
{
lean_ctor_set(v___x_3257_, 0, v___x_3287_);
v___x_3289_ = v___x_3257_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v___x_3287_);
v___x_3289_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
return v___x_3289_;
}
}
}
}
else
{
lean_object* v_a_3292_; lean_object* v___x_3294_; uint8_t v_isShared_3295_; uint8_t v_isSharedCheck_3299_; 
lean_dec(v_v_3253_);
lean_dec(v_k_3252_);
lean_dec(v_a_3248_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
lean_dec(v___y_3239_);
lean_dec_ref(v___y_3238_);
lean_dec(v___y_3237_);
lean_dec(v___y_3236_);
v_a_3292_ = lean_ctor_get(v___x_3254_, 0);
v_isSharedCheck_3299_ = !lean_is_exclusive(v___x_3254_);
if (v_isSharedCheck_3299_ == 0)
{
v___x_3294_ = v___x_3254_;
v_isShared_3295_ = v_isSharedCheck_3299_;
goto v_resetjp_3293_;
}
else
{
lean_inc(v_a_3292_);
lean_dec(v___x_3254_);
v___x_3294_ = lean_box(0);
v_isShared_3295_ = v_isSharedCheck_3299_;
goto v_resetjp_3293_;
}
v_resetjp_3293_:
{
lean_object* v___x_3297_; 
if (v_isShared_3295_ == 0)
{
v___x_3297_ = v___x_3294_;
goto v_reusejp_3296_;
}
else
{
lean_object* v_reuseFailAlloc_3298_; 
v_reuseFailAlloc_3298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3298_, 0, v_a_3292_);
v___x_3297_ = v_reuseFailAlloc_3298_;
goto v_reusejp_3296_;
}
v_reusejp_3296_:
{
return v___x_3297_;
}
}
}
}
else
{
lean_object* v___x_3300_; 
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
lean_dec(v___y_3239_);
lean_dec_ref(v___y_3238_);
lean_dec(v___y_3237_);
v___x_3300_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_a_3248_, v___y_3236_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec(v___y_3236_);
return v___x_3300_;
}
}
else
{
lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v_a_3303_; uint8_t v___x_3304_; 
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
lean_dec(v___y_3239_);
lean_dec_ref(v___y_3238_);
lean_dec(v___y_3237_);
v___x_3301_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__4));
v___x_3302_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3301_, v___y_3244_);
v_a_3303_ = lean_ctor_get(v___x_3302_, 0);
lean_inc(v_a_3303_);
lean_dec_ref(v___x_3302_);
v___x_3304_ = lean_unbox(v_a_3303_);
lean_dec(v_a_3303_);
if (v___x_3304_ == 0)
{
lean_dec(v_a_3248_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec(v___y_3236_);
goto v___jp_3157_;
}
else
{
lean_object* v___x_3305_; 
v___x_3305_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_a_3248_, v___y_3236_, v___y_3244_);
lean_dec(v___y_3236_);
if (lean_obj_tag(v___x_3305_) == 0)
{
lean_object* v_a_3306_; lean_object* v___x_3307_; 
v_a_3306_ = lean_ctor_get(v___x_3305_, 0);
lean_inc(v_a_3306_);
lean_dec_ref(v___x_3305_);
v___x_3307_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1___redArg(v___x_3301_, v_a_3306_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
if (lean_obj_tag(v___x_3307_) == 0)
{
lean_dec_ref(v___x_3307_);
goto v___jp_3157_;
}
else
{
return v___x_3307_;
}
}
else
{
lean_object* v_a_3308_; lean_object* v___x_3310_; uint8_t v_isShared_3311_; uint8_t v_isSharedCheck_3315_; 
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
v_a_3308_ = lean_ctor_get(v___x_3305_, 0);
v_isSharedCheck_3315_ = !lean_is_exclusive(v___x_3305_);
if (v_isSharedCheck_3315_ == 0)
{
v___x_3310_ = v___x_3305_;
v_isShared_3311_ = v_isSharedCheck_3315_;
goto v_resetjp_3309_;
}
else
{
lean_inc(v_a_3308_);
lean_dec(v___x_3305_);
v___x_3310_ = lean_box(0);
v_isShared_3311_ = v_isSharedCheck_3315_;
goto v_resetjp_3309_;
}
v_resetjp_3309_:
{
lean_object* v___x_3313_; 
if (v_isShared_3311_ == 0)
{
v___x_3313_ = v___x_3310_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v_a_3308_);
v___x_3313_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
return v___x_3313_;
}
}
}
}
}
}
else
{
lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v_a_3318_; uint8_t v___x_3319_; 
v___x_3316_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6));
v___x_3317_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3316_, v___y_3244_);
v_a_3318_ = lean_ctor_get(v___x_3317_, 0);
lean_inc(v_a_3318_);
lean_dec_ref(v___x_3317_);
v___x_3319_ = lean_unbox(v_a_3318_);
lean_dec(v_a_3318_);
if (v___x_3319_ == 0)
{
v___y_3207_ = v_a_3248_;
v___y_3208_ = v___y_3236_;
v___y_3209_ = v___y_3237_;
v___y_3210_ = v___y_3238_;
v___y_3211_ = v___y_3239_;
v___y_3212_ = v___y_3240_;
v___y_3213_ = v___y_3241_;
v___y_3214_ = v___y_3242_;
v___y_3215_ = v___y_3243_;
v___y_3216_ = v___y_3244_;
v___y_3217_ = v___y_3245_;
goto v___jp_3206_;
}
else
{
lean_object* v___x_3320_; 
lean_inc(v_a_3248_);
v___x_3320_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_a_3248_, v___y_3236_, v___y_3244_);
if (lean_obj_tag(v___x_3320_) == 0)
{
lean_object* v_a_3321_; lean_object* v___x_3322_; 
v_a_3321_ = lean_ctor_get(v___x_3320_, 0);
lean_inc(v_a_3321_);
lean_dec_ref(v___x_3320_);
v___x_3322_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1___redArg(v___x_3316_, v_a_3321_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_);
if (lean_obj_tag(v___x_3322_) == 0)
{
lean_dec_ref(v___x_3322_);
v___y_3207_ = v_a_3248_;
v___y_3208_ = v___y_3236_;
v___y_3209_ = v___y_3237_;
v___y_3210_ = v___y_3238_;
v___y_3211_ = v___y_3239_;
v___y_3212_ = v___y_3240_;
v___y_3213_ = v___y_3241_;
v___y_3214_ = v___y_3242_;
v___y_3215_ = v___y_3243_;
v___y_3216_ = v___y_3244_;
v___y_3217_ = v___y_3245_;
goto v___jp_3206_;
}
else
{
lean_dec(v_a_3248_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
lean_dec(v___y_3239_);
lean_dec_ref(v___y_3238_);
lean_dec(v___y_3237_);
lean_dec(v___y_3236_);
return v___x_3322_;
}
}
else
{
lean_object* v_a_3323_; lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3330_; 
lean_dec(v_a_3248_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
lean_dec(v___y_3239_);
lean_dec_ref(v___y_3238_);
lean_dec(v___y_3237_);
lean_dec(v___y_3236_);
v_a_3323_ = lean_ctor_get(v___x_3320_, 0);
v_isSharedCheck_3330_ = !lean_is_exclusive(v___x_3320_);
if (v_isSharedCheck_3330_ == 0)
{
v___x_3325_ = v___x_3320_;
v_isShared_3326_ = v_isSharedCheck_3330_;
goto v_resetjp_3324_;
}
else
{
lean_inc(v_a_3323_);
lean_dec(v___x_3320_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3330_;
goto v_resetjp_3324_;
}
v_resetjp_3324_:
{
lean_object* v___x_3328_; 
if (v_isShared_3326_ == 0)
{
v___x_3328_ = v___x_3325_;
goto v_reusejp_3327_;
}
else
{
lean_object* v_reuseFailAlloc_3329_; 
v_reuseFailAlloc_3329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3329_, 0, v_a_3323_);
v___x_3328_ = v_reuseFailAlloc_3329_;
goto v_reusejp_3327_;
}
v_reusejp_3327_:
{
return v___x_3328_;
}
}
}
}
}
}
else
{
lean_object* v_a_3331_; lean_object* v___x_3333_; uint8_t v_isShared_3334_; uint8_t v_isSharedCheck_3338_; 
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
lean_dec(v___y_3239_);
lean_dec_ref(v___y_3238_);
lean_dec(v___y_3237_);
lean_dec(v___y_3236_);
v_a_3331_ = lean_ctor_get(v___x_3247_, 0);
v_isSharedCheck_3338_ = !lean_is_exclusive(v___x_3247_);
if (v_isSharedCheck_3338_ == 0)
{
v___x_3333_ = v___x_3247_;
v_isShared_3334_ = v_isSharedCheck_3338_;
goto v_resetjp_3332_;
}
else
{
lean_inc(v_a_3331_);
lean_dec(v___x_3247_);
v___x_3333_ = lean_box(0);
v_isShared_3334_ = v_isSharedCheck_3338_;
goto v_resetjp_3332_;
}
v_resetjp_3332_:
{
lean_object* v___x_3336_; 
if (v_isShared_3334_ == 0)
{
v___x_3336_ = v___x_3333_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v_a_3331_);
v___x_3336_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
return v___x_3336_;
}
}
}
}
}
else
{
lean_object* v___x_3354_; lean_object* v___x_3356_; 
lean_dec(v_a_3155_);
lean_dec_ref(v_a_3154_);
lean_dec(v_a_3153_);
lean_dec_ref(v_a_3152_);
lean_dec(v_a_3151_);
lean_dec_ref(v_a_3150_);
lean_dec(v_a_3149_);
lean_dec_ref(v_a_3148_);
lean_dec(v_a_3147_);
lean_dec(v_a_3146_);
lean_dec_ref(v_c_3145_);
v___x_3354_ = lean_box(0);
if (v_isShared_3233_ == 0)
{
lean_ctor_set(v___x_3232_, 0, v___x_3354_);
v___x_3356_ = v___x_3232_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v___x_3354_);
v___x_3356_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
return v___x_3356_;
}
}
}
}
else
{
lean_object* v_a_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3366_; 
lean_dec(v_a_3155_);
lean_dec_ref(v_a_3154_);
lean_dec(v_a_3153_);
lean_dec_ref(v_a_3152_);
lean_dec(v_a_3151_);
lean_dec_ref(v_a_3150_);
lean_dec(v_a_3149_);
lean_dec_ref(v_a_3148_);
lean_dec(v_a_3147_);
lean_dec(v_a_3146_);
lean_dec_ref(v_c_3145_);
v_a_3359_ = lean_ctor_get(v___x_3229_, 0);
v_isSharedCheck_3366_ = !lean_is_exclusive(v___x_3229_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3361_ = v___x_3229_;
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_a_3359_);
lean_dec(v___x_3229_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v___x_3364_; 
if (v_isShared_3362_ == 0)
{
v___x_3364_ = v___x_3361_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v_a_3359_);
v___x_3364_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
return v___x_3364_;
}
}
}
v___jp_3157_:
{
lean_object* v___x_3158_; lean_object* v___x_3159_; 
v___x_3158_ = lean_box(0);
v___x_3159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3159_, 0, v___x_3158_);
return v___x_3159_;
}
v___jp_3160_:
{
lean_object* v___x_3165_; 
v___x_3165_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(v___y_3161_, v___y_3163_, v___y_3164_);
lean_dec_ref(v___y_3164_);
if (lean_obj_tag(v___x_3165_) == 0)
{
lean_object* v_a_3166_; lean_object* v___x_3168_; uint8_t v_isShared_3169_; uint8_t v_isSharedCheck_3178_; 
v_a_3166_ = lean_ctor_get(v___x_3165_, 0);
v_isSharedCheck_3178_ = !lean_is_exclusive(v___x_3165_);
if (v_isSharedCheck_3178_ == 0)
{
v___x_3168_ = v___x_3165_;
v_isShared_3169_ = v_isSharedCheck_3178_;
goto v_resetjp_3167_;
}
else
{
lean_inc(v_a_3166_);
lean_dec(v___x_3165_);
v___x_3168_ = lean_box(0);
v_isShared_3169_ = v_isSharedCheck_3178_;
goto v_resetjp_3167_;
}
v_resetjp_3167_:
{
uint8_t v___x_3170_; uint8_t v___x_3171_; uint8_t v___x_3172_; 
v___x_3170_ = 0;
v___x_3171_ = lean_unbox(v_a_3166_);
lean_dec(v_a_3166_);
v___x_3172_ = l_Lean_instBEqLBool_beq(v___x_3171_, v___x_3170_);
if (v___x_3172_ == 0)
{
lean_object* v___x_3173_; lean_object* v___x_3175_; 
lean_dec(v___y_3163_);
lean_dec(v___y_3162_);
v___x_3173_ = lean_box(0);
if (v_isShared_3169_ == 0)
{
lean_ctor_set(v___x_3168_, 0, v___x_3173_);
v___x_3175_ = v___x_3168_;
goto v_reusejp_3174_;
}
else
{
lean_object* v_reuseFailAlloc_3176_; 
v_reuseFailAlloc_3176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3176_, 0, v___x_3173_);
v___x_3175_ = v_reuseFailAlloc_3176_;
goto v_reusejp_3174_;
}
v_reusejp_3174_:
{
return v___x_3175_;
}
}
else
{
lean_object* v___x_3177_; 
lean_del_object(v___x_3168_);
v___x_3177_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v___y_3162_, v___y_3163_);
lean_dec(v___y_3163_);
return v___x_3177_;
}
}
}
else
{
lean_object* v_a_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3186_; 
lean_dec(v___y_3163_);
lean_dec(v___y_3162_);
v_a_3179_ = lean_ctor_get(v___x_3165_, 0);
v_isSharedCheck_3186_ = !lean_is_exclusive(v___x_3165_);
if (v_isSharedCheck_3186_ == 0)
{
v___x_3181_ = v___x_3165_;
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_a_3179_);
lean_dec(v___x_3165_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3186_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v___x_3184_; 
if (v_isShared_3182_ == 0)
{
v___x_3184_ = v___x_3181_;
goto v_reusejp_3183_;
}
else
{
lean_object* v_reuseFailAlloc_3185_; 
v_reuseFailAlloc_3185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3185_, 0, v_a_3179_);
v___x_3184_ = v_reuseFailAlloc_3185_;
goto v_reusejp_3183_;
}
v_reusejp_3183_:
{
return v___x_3184_;
}
}
}
}
v___jp_3187_:
{
lean_object* v_p_3198_; lean_object* v___x_3199_; 
v_p_3198_ = lean_ctor_get(v___y_3191_, 0);
lean_inc_ref(v_p_3198_);
v___x_3199_ = l_Int_Linear_Poly_updateOccs___redArg(v_p_3198_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
lean_dec(v___y_3197_);
lean_dec(v___y_3195_);
lean_dec_ref(v___y_3194_);
if (lean_obj_tag(v___x_3199_) == 0)
{
lean_object* v___x_3200_; uint8_t v___x_3201_; 
lean_dec_ref(v___x_3199_);
v___x_3200_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6);
v___x_3201_ = lean_int_dec_lt(v___y_3190_, v___x_3200_);
lean_dec(v___y_3190_);
if (v___x_3201_ == 0)
{
lean_object* v___x_3202_; lean_object* v___x_3203_; 
lean_dec_ref(v___y_3188_);
v___x_3202_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_3203_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3202_, v___y_3189_, v___y_3193_);
if (lean_obj_tag(v___x_3203_) == 0)
{
lean_dec_ref(v___x_3203_);
v___y_3161_ = v___y_3191_;
v___y_3162_ = v___y_3192_;
v___y_3163_ = v___y_3193_;
v___y_3164_ = v___y_3196_;
goto v___jp_3160_;
}
else
{
lean_dec_ref(v___y_3196_);
lean_dec(v___y_3193_);
lean_dec(v___y_3192_);
lean_dec_ref(v___y_3191_);
return v___x_3203_;
}
}
else
{
lean_object* v___x_3204_; lean_object* v___x_3205_; 
lean_dec_ref(v___y_3189_);
v___x_3204_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_3205_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3204_, v___y_3188_, v___y_3193_);
if (lean_obj_tag(v___x_3205_) == 0)
{
lean_dec_ref(v___x_3205_);
v___y_3161_ = v___y_3191_;
v___y_3162_ = v___y_3192_;
v___y_3163_ = v___y_3193_;
v___y_3164_ = v___y_3196_;
goto v___jp_3160_;
}
else
{
lean_dec_ref(v___y_3196_);
lean_dec(v___y_3193_);
lean_dec(v___y_3192_);
lean_dec_ref(v___y_3191_);
return v___x_3205_;
}
}
}
else
{
lean_dec_ref(v___y_3196_);
lean_dec(v___y_3193_);
lean_dec(v___y_3192_);
lean_dec_ref(v___y_3191_);
lean_dec(v___y_3190_);
lean_dec_ref(v___y_3189_);
lean_dec_ref(v___y_3188_);
return v___x_3199_;
}
}
v___jp_3206_:
{
lean_object* v___x_3218_; lean_object* v___x_3219_; 
v___x_3218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3218_, 0, v___y_3207_);
v___x_3219_ = l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(v___x_3218_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_);
lean_dec(v___y_3217_);
lean_dec_ref(v___y_3216_);
lean_dec(v___y_3215_);
lean_dec_ref(v___y_3214_);
lean_dec(v___y_3213_);
lean_dec_ref(v___y_3212_);
lean_dec(v___y_3211_);
lean_dec_ref(v___y_3210_);
lean_dec(v___y_3209_);
lean_dec(v___y_3208_);
if (lean_obj_tag(v___x_3219_) == 0)
{
lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3227_; 
v_isSharedCheck_3227_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3227_ == 0)
{
lean_object* v_unused_3228_; 
v_unused_3228_ = lean_ctor_get(v___x_3219_, 0);
lean_dec(v_unused_3228_);
v___x_3221_ = v___x_3219_;
v_isShared_3222_ = v_isSharedCheck_3227_;
goto v_resetjp_3220_;
}
else
{
lean_dec(v___x_3219_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3227_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
lean_object* v___x_3223_; lean_object* v___x_3225_; 
v___x_3223_ = lean_box(0);
if (v_isShared_3222_ == 0)
{
lean_ctor_set(v___x_3221_, 0, v___x_3223_);
v___x_3225_ = v___x_3221_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v___x_3223_);
v___x_3225_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
return v___x_3225_;
}
}
}
else
{
return v___x_3219_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___boxed(lean_object* v_c_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_){
_start:
{
lean_object* v_res_3379_; 
v_res_3379_ = lean_grind_cutsat_assert_le(v_c_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_);
return v_res_3379_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(lean_object* v_a_3380_, lean_object* v_inst_3381_, lean_object* v_x_3382_, size_t v_x_3383_, size_t v_x_3384_){
_start:
{
lean_object* v___x_3385_; 
v___x_3385_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0___redArg(v_a_3380_, v_x_3382_, v_x_3383_, v_x_3384_);
return v___x_3385_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0___boxed(lean_object* v_a_3386_, lean_object* v_inst_3387_, lean_object* v_x_3388_, lean_object* v_x_3389_, lean_object* v_x_3390_){
_start:
{
size_t v_x_74097__boxed_3391_; size_t v_x_74098__boxed_3392_; lean_object* v_res_3393_; 
v_x_74097__boxed_3391_ = lean_unbox_usize(v_x_3389_);
lean_dec(v_x_3389_);
v_x_74098__boxed_3392_ = lean_unbox_usize(v_x_3390_);
lean_dec(v_x_3390_);
v_res_3393_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(v_a_3386_, v_inst_3387_, v_x_3388_, v_x_74097__boxed_3391_, v_x_74098__boxed_3392_);
lean_dec_ref(v_inst_3387_);
return v_res_3393_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1(void){
_start:
{
lean_object* v___x_3395_; lean_object* v___x_3396_; 
v___x_3395_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__0));
v___x_3396_ = l_Lean_stringToMessageData(v___x_3395_);
return v___x_3396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(lean_object* v_e_3397_, lean_object* v_a_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_){
_start:
{
lean_object* v___x_3408_; 
v___x_3408_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3399_);
if (lean_obj_tag(v___x_3408_) == 0)
{
lean_object* v_a_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3422_; 
v_a_3409_ = lean_ctor_get(v___x_3408_, 0);
v_isSharedCheck_3422_ = !lean_is_exclusive(v___x_3408_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3411_ = v___x_3408_;
v_isShared_3412_ = v_isSharedCheck_3422_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_a_3409_);
lean_dec(v___x_3408_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3422_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
uint8_t v_verbose_3413_; 
v_verbose_3413_ = lean_ctor_get_uint8(v_a_3409_, sizeof(void*)*11 + 15);
lean_dec(v_a_3409_);
if (v_verbose_3413_ == 0)
{
lean_object* v___x_3414_; lean_object* v___x_3416_; 
lean_dec_ref(v_e_3397_);
v___x_3414_ = lean_box(0);
if (v_isShared_3412_ == 0)
{
lean_ctor_set(v___x_3411_, 0, v___x_3414_);
v___x_3416_ = v___x_3411_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v___x_3414_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
return v___x_3416_;
}
}
else
{
lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3421_; 
lean_del_object(v___x_3411_);
v___x_3418_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1);
v___x_3419_ = l_Lean_indentExpr(v_e_3397_);
v___x_3420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3420_, 0, v___x_3418_);
lean_ctor_set(v___x_3420_, 1, v___x_3419_);
v___x_3421_ = l_Lean_Meta_Grind_reportIssue(v___x_3420_, v_a_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_, v_a_3405_, v_a_3406_);
return v___x_3421_;
}
}
}
else
{
lean_object* v_a_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3430_; 
lean_dec_ref(v_e_3397_);
v_a_3423_ = lean_ctor_get(v___x_3408_, 0);
v_isSharedCheck_3430_ = !lean_is_exclusive(v___x_3408_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3425_ = v___x_3408_;
v_isShared_3426_ = v_isSharedCheck_3430_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_a_3423_);
lean_dec(v___x_3408_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3430_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v___x_3428_; 
if (v_isShared_3426_ == 0)
{
v___x_3428_ = v___x_3425_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3429_; 
v_reuseFailAlloc_3429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3429_, 0, v_a_3423_);
v___x_3428_ = v_reuseFailAlloc_3429_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
return v___x_3428_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___boxed(lean_object* v_e_3431_, lean_object* v_a_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_, lean_object* v_a_3441_){
_start:
{
lean_object* v_res_3442_; 
v_res_3442_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(v_e_3431_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_, v_a_3440_);
lean_dec(v_a_3440_);
lean_dec_ref(v_a_3439_);
lean_dec(v_a_3438_);
lean_dec_ref(v_a_3437_);
lean_dec(v_a_3436_);
lean_dec_ref(v_a_3435_);
lean_dec(v_a_3434_);
lean_dec_ref(v_a_3433_);
lean_dec(v_a_3432_);
return v_res_3442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized(lean_object* v_e_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_){
_start:
{
lean_object* v___x_3455_; 
v___x_3455_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(v_e_3443_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_, v_a_3452_, v_a_3453_);
return v___x_3455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___boxed(lean_object* v_e_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_){
_start:
{
lean_object* v_res_3468_; 
v_res_3468_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized(v_e_3456_, v_a_3457_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_, v_a_3462_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_);
lean_dec(v_a_3466_);
lean_dec_ref(v_a_3465_);
lean_dec(v_a_3464_);
lean_dec_ref(v_a_3463_);
lean_dec(v_a_3462_);
lean_dec_ref(v_a_3461_);
lean_dec(v_a_3460_);
lean_dec_ref(v_a_3459_);
lean_dec(v_a_3458_);
lean_dec(v_a_3457_);
return v_res_3468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f(lean_object* v_e_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_){
_start:
{
lean_object* v___x_3486_; 
lean_inc_ref(v_e_3474_);
v___x_3486_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3474_, v_a_3482_);
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_object* v_a_3487_; lean_object* v___x_3489_; uint8_t v_isShared_3490_; uint8_t v_isSharedCheck_3602_; 
v_a_3487_ = lean_ctor_get(v___x_3486_, 0);
v_isSharedCheck_3602_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3602_ == 0)
{
v___x_3489_ = v___x_3486_;
v_isShared_3490_ = v_isSharedCheck_3602_;
goto v_resetjp_3488_;
}
else
{
lean_inc(v_a_3487_);
lean_dec(v___x_3486_);
v___x_3489_ = lean_box(0);
v_isShared_3490_ = v_isSharedCheck_3602_;
goto v_resetjp_3488_;
}
v_resetjp_3488_:
{
lean_object* v___x_3496_; uint8_t v___x_3497_; 
v___x_3496_ = l_Lean_Expr_cleanupAnnotations(v_a_3487_);
v___x_3497_ = l_Lean_Expr_isApp(v___x_3496_);
if (v___x_3497_ == 0)
{
lean_dec_ref(v___x_3496_);
lean_dec_ref(v_e_3474_);
goto v___jp_3491_;
}
else
{
lean_object* v_arg_3498_; lean_object* v___x_3499_; uint8_t v___x_3500_; 
v_arg_3498_ = lean_ctor_get(v___x_3496_, 1);
lean_inc_ref(v_arg_3498_);
v___x_3499_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3496_);
v___x_3500_ = l_Lean_Expr_isApp(v___x_3499_);
if (v___x_3500_ == 0)
{
lean_dec_ref(v___x_3499_);
lean_dec_ref(v_arg_3498_);
lean_dec_ref(v_e_3474_);
goto v___jp_3491_;
}
else
{
lean_object* v_arg_3501_; lean_object* v___x_3502_; uint8_t v___x_3503_; 
v_arg_3501_ = lean_ctor_get(v___x_3499_, 1);
lean_inc_ref(v_arg_3501_);
v___x_3502_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3499_);
v___x_3503_ = l_Lean_Expr_isApp(v___x_3502_);
if (v___x_3503_ == 0)
{
lean_dec_ref(v___x_3502_);
lean_dec_ref(v_arg_3501_);
lean_dec_ref(v_arg_3498_);
lean_dec_ref(v_e_3474_);
goto v___jp_3491_;
}
else
{
lean_object* v_arg_3504_; lean_object* v___x_3505_; uint8_t v___x_3506_; 
v_arg_3504_ = lean_ctor_get(v___x_3502_, 1);
lean_inc_ref(v_arg_3504_);
v___x_3505_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3502_);
v___x_3506_ = l_Lean_Expr_isApp(v___x_3505_);
if (v___x_3506_ == 0)
{
lean_dec_ref(v___x_3505_);
lean_dec_ref(v_arg_3504_);
lean_dec_ref(v_arg_3501_);
lean_dec_ref(v_arg_3498_);
lean_dec_ref(v_e_3474_);
goto v___jp_3491_;
}
else
{
lean_object* v___x_3507_; lean_object* v___x_3508_; uint8_t v___x_3509_; 
v___x_3507_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3505_);
v___x_3508_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2));
v___x_3509_ = l_Lean_Expr_isConstOf(v___x_3507_, v___x_3508_);
lean_dec_ref(v___x_3507_);
if (v___x_3509_ == 0)
{
lean_dec_ref(v_arg_3504_);
lean_dec_ref(v_arg_3501_);
lean_dec_ref(v_arg_3498_);
lean_dec_ref(v_e_3474_);
goto v___jp_3491_;
}
else
{
lean_object* v___x_3510_; 
lean_del_object(v___x_3489_);
v___x_3510_ = l_Lean_Meta_Structural_isInstLEInt___redArg(v_arg_3504_, v_a_3482_);
if (lean_obj_tag(v___x_3510_) == 0)
{
lean_object* v_a_3511_; lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3593_; 
v_a_3511_ = lean_ctor_get(v___x_3510_, 0);
v_isSharedCheck_3593_ = !lean_is_exclusive(v___x_3510_);
if (v_isSharedCheck_3593_ == 0)
{
v___x_3513_ = v___x_3510_;
v_isShared_3514_ = v_isSharedCheck_3593_;
goto v_resetjp_3512_;
}
else
{
lean_inc(v_a_3511_);
lean_dec(v___x_3510_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3593_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
uint8_t v___x_3515_; 
v___x_3515_ = lean_unbox(v_a_3511_);
lean_dec(v_a_3511_);
if (v___x_3515_ == 0)
{
lean_object* v___x_3516_; lean_object* v___x_3518_; 
lean_dec_ref(v_arg_3501_);
lean_dec_ref(v_arg_3498_);
lean_dec_ref(v_e_3474_);
v___x_3516_ = lean_box(0);
if (v_isShared_3514_ == 0)
{
lean_ctor_set(v___x_3513_, 0, v___x_3516_);
v___x_3518_ = v___x_3513_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v___x_3516_);
v___x_3518_ = v_reuseFailAlloc_3519_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
return v___x_3518_;
}
}
else
{
lean_object* v___x_3520_; 
lean_del_object(v___x_3513_);
v___x_3520_ = l_Lean_Meta_getIntValue_x3f(v_arg_3498_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_);
if (lean_obj_tag(v___x_3520_) == 0)
{
lean_object* v_a_3521_; 
v_a_3521_ = lean_ctor_get(v___x_3520_, 0);
lean_inc(v_a_3521_);
lean_dec_ref(v___x_3520_);
if (lean_obj_tag(v_a_3521_) == 1)
{
lean_object* v_val_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3566_; 
v_val_3522_ = lean_ctor_get(v_a_3521_, 0);
v_isSharedCheck_3566_ = !lean_is_exclusive(v_a_3521_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3524_ = v_a_3521_;
v_isShared_3525_ = v_isSharedCheck_3566_;
goto v_resetjp_3523_;
}
else
{
lean_inc(v_val_3522_);
lean_dec(v_a_3521_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3566_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
lean_object* v___x_3526_; uint8_t v___x_3527_; 
v___x_3526_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6);
v___x_3527_ = lean_int_dec_eq(v_val_3522_, v___x_3526_);
lean_dec(v_val_3522_);
if (v___x_3527_ == 0)
{
lean_object* v___x_3528_; 
lean_del_object(v___x_3524_);
lean_dec_ref(v_arg_3501_);
v___x_3528_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(v_e_3474_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_);
if (lean_obj_tag(v___x_3528_) == 0)
{
lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3536_; 
v_isSharedCheck_3536_ = !lean_is_exclusive(v___x_3528_);
if (v_isSharedCheck_3536_ == 0)
{
lean_object* v_unused_3537_; 
v_unused_3537_ = lean_ctor_get(v___x_3528_, 0);
lean_dec(v_unused_3537_);
v___x_3530_ = v___x_3528_;
v_isShared_3531_ = v_isSharedCheck_3536_;
goto v_resetjp_3529_;
}
else
{
lean_dec(v___x_3528_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3536_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v___x_3532_; lean_object* v___x_3534_; 
v___x_3532_ = lean_box(0);
if (v_isShared_3531_ == 0)
{
lean_ctor_set(v___x_3530_, 0, v___x_3532_);
v___x_3534_ = v___x_3530_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v___x_3532_);
v___x_3534_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
return v___x_3534_;
}
}
}
else
{
lean_object* v_a_3538_; lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3545_; 
v_a_3538_ = lean_ctor_get(v___x_3528_, 0);
v_isSharedCheck_3545_ = !lean_is_exclusive(v___x_3528_);
if (v_isSharedCheck_3545_ == 0)
{
v___x_3540_ = v___x_3528_;
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
else
{
lean_inc(v_a_3538_);
lean_dec(v___x_3528_);
v___x_3540_ = lean_box(0);
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
v_resetjp_3539_:
{
lean_object* v___x_3543_; 
if (v_isShared_3541_ == 0)
{
v___x_3543_ = v___x_3540_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v_a_3538_);
v___x_3543_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
return v___x_3543_;
}
}
}
}
else
{
lean_object* v___x_3546_; 
lean_dec_ref(v_e_3474_);
v___x_3546_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(v_arg_3501_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_);
if (lean_obj_tag(v___x_3546_) == 0)
{
lean_object* v_a_3547_; lean_object* v___x_3549_; uint8_t v_isShared_3550_; uint8_t v_isSharedCheck_3557_; 
v_a_3547_ = lean_ctor_get(v___x_3546_, 0);
v_isSharedCheck_3557_ = !lean_is_exclusive(v___x_3546_);
if (v_isSharedCheck_3557_ == 0)
{
v___x_3549_ = v___x_3546_;
v_isShared_3550_ = v_isSharedCheck_3557_;
goto v_resetjp_3548_;
}
else
{
lean_inc(v_a_3547_);
lean_dec(v___x_3546_);
v___x_3549_ = lean_box(0);
v_isShared_3550_ = v_isSharedCheck_3557_;
goto v_resetjp_3548_;
}
v_resetjp_3548_:
{
lean_object* v___x_3552_; 
if (v_isShared_3525_ == 0)
{
lean_ctor_set(v___x_3524_, 0, v_a_3547_);
v___x_3552_ = v___x_3524_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3556_; 
v_reuseFailAlloc_3556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3556_, 0, v_a_3547_);
v___x_3552_ = v_reuseFailAlloc_3556_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
lean_object* v___x_3554_; 
if (v_isShared_3550_ == 0)
{
lean_ctor_set(v___x_3549_, 0, v___x_3552_);
v___x_3554_ = v___x_3549_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v___x_3552_);
v___x_3554_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
return v___x_3554_;
}
}
}
}
else
{
lean_object* v_a_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3565_; 
lean_del_object(v___x_3524_);
v_a_3558_ = lean_ctor_get(v___x_3546_, 0);
v_isSharedCheck_3565_ = !lean_is_exclusive(v___x_3546_);
if (v_isSharedCheck_3565_ == 0)
{
v___x_3560_ = v___x_3546_;
v_isShared_3561_ = v_isSharedCheck_3565_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_a_3558_);
lean_dec(v___x_3546_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3565_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v___x_3563_; 
if (v_isShared_3561_ == 0)
{
v___x_3563_ = v___x_3560_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v_a_3558_);
v___x_3563_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
return v___x_3563_;
}
}
}
}
}
}
else
{
lean_object* v___x_3567_; 
lean_dec(v_a_3521_);
lean_dec_ref(v_arg_3501_);
v___x_3567_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(v_e_3474_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_);
if (lean_obj_tag(v___x_3567_) == 0)
{
lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3575_; 
v_isSharedCheck_3575_ = !lean_is_exclusive(v___x_3567_);
if (v_isSharedCheck_3575_ == 0)
{
lean_object* v_unused_3576_; 
v_unused_3576_ = lean_ctor_get(v___x_3567_, 0);
lean_dec(v_unused_3576_);
v___x_3569_ = v___x_3567_;
v_isShared_3570_ = v_isSharedCheck_3575_;
goto v_resetjp_3568_;
}
else
{
lean_dec(v___x_3567_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3575_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3571_; lean_object* v___x_3573_; 
v___x_3571_ = lean_box(0);
if (v_isShared_3570_ == 0)
{
lean_ctor_set(v___x_3569_, 0, v___x_3571_);
v___x_3573_ = v___x_3569_;
goto v_reusejp_3572_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v___x_3571_);
v___x_3573_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3572_;
}
v_reusejp_3572_:
{
return v___x_3573_;
}
}
}
else
{
lean_object* v_a_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3584_; 
v_a_3577_ = lean_ctor_get(v___x_3567_, 0);
v_isSharedCheck_3584_ = !lean_is_exclusive(v___x_3567_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3579_ = v___x_3567_;
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_a_3577_);
lean_dec(v___x_3567_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v___x_3582_; 
if (v_isShared_3580_ == 0)
{
v___x_3582_ = v___x_3579_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_a_3577_);
v___x_3582_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
return v___x_3582_;
}
}
}
}
}
else
{
lean_object* v_a_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3592_; 
lean_dec_ref(v_arg_3501_);
lean_dec_ref(v_e_3474_);
v_a_3585_ = lean_ctor_get(v___x_3520_, 0);
v_isSharedCheck_3592_ = !lean_is_exclusive(v___x_3520_);
if (v_isSharedCheck_3592_ == 0)
{
v___x_3587_ = v___x_3520_;
v_isShared_3588_ = v_isSharedCheck_3592_;
goto v_resetjp_3586_;
}
else
{
lean_inc(v_a_3585_);
lean_dec(v___x_3520_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3592_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
lean_object* v___x_3590_; 
if (v_isShared_3588_ == 0)
{
v___x_3590_ = v___x_3587_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v_a_3585_);
v___x_3590_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
return v___x_3590_;
}
}
}
}
}
}
else
{
lean_object* v_a_3594_; lean_object* v___x_3596_; uint8_t v_isShared_3597_; uint8_t v_isSharedCheck_3601_; 
lean_dec_ref(v_arg_3501_);
lean_dec_ref(v_arg_3498_);
lean_dec_ref(v_e_3474_);
v_a_3594_ = lean_ctor_get(v___x_3510_, 0);
v_isSharedCheck_3601_ = !lean_is_exclusive(v___x_3510_);
if (v_isSharedCheck_3601_ == 0)
{
v___x_3596_ = v___x_3510_;
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
else
{
lean_inc(v_a_3594_);
lean_dec(v___x_3510_);
v___x_3596_ = lean_box(0);
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
v_resetjp_3595_:
{
lean_object* v___x_3599_; 
if (v_isShared_3597_ == 0)
{
v___x_3599_ = v___x_3596_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v_a_3594_);
v___x_3599_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
return v___x_3599_;
}
}
}
}
}
}
}
}
v___jp_3491_:
{
lean_object* v___x_3492_; lean_object* v___x_3494_; 
v___x_3492_ = lean_box(0);
if (v_isShared_3490_ == 0)
{
lean_ctor_set(v___x_3489_, 0, v___x_3492_);
v___x_3494_ = v___x_3489_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v___x_3492_);
v___x_3494_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
return v___x_3494_;
}
}
}
}
else
{
lean_object* v_a_3603_; lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3610_; 
lean_dec_ref(v_e_3474_);
v_a_3603_ = lean_ctor_get(v___x_3486_, 0);
v_isSharedCheck_3610_ = !lean_is_exclusive(v___x_3486_);
if (v_isSharedCheck_3610_ == 0)
{
v___x_3605_ = v___x_3486_;
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
else
{
lean_inc(v_a_3603_);
lean_dec(v___x_3486_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
lean_object* v___x_3608_; 
if (v_isShared_3606_ == 0)
{
v___x_3608_ = v___x_3605_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v_a_3603_);
v___x_3608_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
return v___x_3608_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___boxed(lean_object* v_e_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_, lean_object* v_a_3615_, lean_object* v_a_3616_, lean_object* v_a_3617_, lean_object* v_a_3618_, lean_object* v_a_3619_, lean_object* v_a_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_){
_start:
{
lean_object* v_res_3623_; 
v_res_3623_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f(v_e_3611_, v_a_3612_, v_a_3613_, v_a_3614_, v_a_3615_, v_a_3616_, v_a_3617_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_);
lean_dec(v_a_3621_);
lean_dec_ref(v_a_3620_);
lean_dec(v_a_3619_);
lean_dec_ref(v_a_3618_);
lean_dec(v_a_3617_);
lean_dec_ref(v_a_3616_);
lean_dec(v_a_3615_);
lean_dec_ref(v_a_3614_);
lean_dec(v_a_3613_);
lean_dec(v_a_3612_);
return v_res_3623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(lean_object* v_c_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_){
_start:
{
lean_object* v_p_3636_; lean_object* v___x_3637_; 
v_p_3636_ = lean_ctor_get(v_c_3624_, 0);
lean_inc_ref(v_p_3636_);
v___x_3637_ = l_Int_Linear_Poly_normCommRing_x3f(v_p_3636_, v_a_3625_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_, v_a_3630_, v_a_3631_, v_a_3632_, v_a_3633_, v_a_3634_);
if (lean_obj_tag(v___x_3637_) == 0)
{
lean_object* v_a_3638_; 
v_a_3638_ = lean_ctor_get(v___x_3637_, 0);
lean_inc(v_a_3638_);
lean_dec_ref(v___x_3637_);
if (lean_obj_tag(v_a_3638_) == 1)
{
lean_object* v_val_3639_; lean_object* v_snd_3640_; lean_object* v_fst_3641_; lean_object* v_fst_3642_; lean_object* v_snd_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3652_; 
v_val_3639_ = lean_ctor_get(v_a_3638_, 0);
lean_inc(v_val_3639_);
lean_dec_ref(v_a_3638_);
v_snd_3640_ = lean_ctor_get(v_val_3639_, 1);
lean_inc(v_snd_3640_);
v_fst_3641_ = lean_ctor_get(v_val_3639_, 0);
lean_inc(v_fst_3641_);
lean_dec(v_val_3639_);
v_fst_3642_ = lean_ctor_get(v_snd_3640_, 0);
v_snd_3643_ = lean_ctor_get(v_snd_3640_, 1);
v_isSharedCheck_3652_ = !lean_is_exclusive(v_snd_3640_);
if (v_isSharedCheck_3652_ == 0)
{
v___x_3645_ = v_snd_3640_;
v_isShared_3646_ = v_isSharedCheck_3652_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_snd_3643_);
lean_inc(v_fst_3642_);
lean_dec(v_snd_3640_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3652_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
lean_object* v___x_3647_; lean_object* v___x_3649_; 
v___x_3647_ = lean_alloc_ctor(17, 3, 0);
lean_ctor_set(v___x_3647_, 0, v_c_3624_);
lean_ctor_set(v___x_3647_, 1, v_fst_3641_);
lean_ctor_set(v___x_3647_, 2, v_fst_3642_);
if (v_isShared_3646_ == 0)
{
lean_ctor_set(v___x_3645_, 1, v___x_3647_);
lean_ctor_set(v___x_3645_, 0, v_snd_3643_);
v___x_3649_ = v___x_3645_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v_snd_3643_);
lean_ctor_set(v_reuseFailAlloc_3651_, 1, v___x_3647_);
v___x_3649_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
lean_object* v___x_3650_; 
lean_inc(v_a_3634_);
lean_inc_ref(v_a_3633_);
lean_inc(v_a_3632_);
lean_inc_ref(v_a_3631_);
lean_inc(v_a_3630_);
lean_inc_ref(v_a_3629_);
lean_inc(v_a_3628_);
lean_inc_ref(v_a_3627_);
lean_inc(v_a_3626_);
lean_inc(v_a_3625_);
v___x_3650_ = lean_grind_cutsat_assert_le(v___x_3649_, v_a_3625_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_, v_a_3630_, v_a_3631_, v_a_3632_, v_a_3633_, v_a_3634_);
return v___x_3650_;
}
}
}
else
{
lean_object* v___x_3653_; 
lean_dec(v_a_3638_);
lean_inc(v_a_3634_);
lean_inc_ref(v_a_3633_);
lean_inc(v_a_3632_);
lean_inc_ref(v_a_3631_);
lean_inc(v_a_3630_);
lean_inc_ref(v_a_3629_);
lean_inc(v_a_3628_);
lean_inc_ref(v_a_3627_);
lean_inc(v_a_3626_);
lean_inc(v_a_3625_);
v___x_3653_ = lean_grind_cutsat_assert_le(v_c_3624_, v_a_3625_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_, v_a_3630_, v_a_3631_, v_a_3632_, v_a_3633_, v_a_3634_);
return v___x_3653_;
}
}
else
{
lean_object* v_a_3654_; lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3661_; 
lean_dec_ref(v_c_3624_);
v_a_3654_ = lean_ctor_get(v___x_3637_, 0);
v_isSharedCheck_3661_ = !lean_is_exclusive(v___x_3637_);
if (v_isSharedCheck_3661_ == 0)
{
v___x_3656_ = v___x_3637_;
v_isShared_3657_ = v_isSharedCheck_3661_;
goto v_resetjp_3655_;
}
else
{
lean_inc(v_a_3654_);
lean_dec(v___x_3637_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3661_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
lean_object* v___x_3659_; 
if (v_isShared_3657_ == 0)
{
v___x_3659_ = v___x_3656_;
goto v_reusejp_3658_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v_a_3654_);
v___x_3659_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3658_;
}
v_reusejp_3658_:
{
return v___x_3659_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore___boxed(lean_object* v_c_3662_, lean_object* v_a_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_){
_start:
{
lean_object* v_res_3674_; 
v_res_3674_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v_c_3662_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_);
lean_dec(v_a_3672_);
lean_dec_ref(v_a_3671_);
lean_dec(v_a_3670_);
lean_dec_ref(v_a_3669_);
lean_dec(v_a_3668_);
lean_dec_ref(v_a_3667_);
lean_dec(v_a_3666_);
lean_dec_ref(v_a_3665_);
lean_dec(v_a_3664_);
lean_dec(v_a_3663_);
return v_res_3674_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0(void){
_start:
{
lean_object* v___x_3675_; lean_object* v___x_3676_; 
v___x_3675_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
v___x_3676_ = lean_int_neg(v___x_3675_);
return v___x_3676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe(lean_object* v_e_3677_, uint8_t v_eqTrue_3678_, lean_object* v_a_3679_, lean_object* v_a_3680_, lean_object* v_a_3681_, lean_object* v_a_3682_, lean_object* v_a_3683_, lean_object* v_a_3684_, lean_object* v_a_3685_, lean_object* v_a_3686_, lean_object* v_a_3687_, lean_object* v_a_3688_){
_start:
{
lean_object* v___x_3690_; 
lean_inc_ref(v_e_3677_);
v___x_3690_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f(v_e_3677_, v_a_3679_, v_a_3680_, v_a_3681_, v_a_3682_, v_a_3683_, v_a_3684_, v_a_3685_, v_a_3686_, v_a_3687_, v_a_3688_);
if (lean_obj_tag(v___x_3690_) == 0)
{
lean_object* v_a_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3717_; 
v_a_3691_ = lean_ctor_get(v___x_3690_, 0);
v_isSharedCheck_3717_ = !lean_is_exclusive(v___x_3690_);
if (v_isSharedCheck_3717_ == 0)
{
v___x_3693_ = v___x_3690_;
v_isShared_3694_ = v_isSharedCheck_3717_;
goto v_resetjp_3692_;
}
else
{
lean_inc(v_a_3691_);
lean_dec(v___x_3690_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3717_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
if (lean_obj_tag(v_a_3691_) == 1)
{
lean_del_object(v___x_3693_);
if (v_eqTrue_3678_ == 0)
{
lean_object* v_val_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; 
v_val_3695_ = lean_ctor_get(v_a_3691_, 0);
lean_inc(v_val_3695_);
lean_dec_ref(v_a_3691_);
v___x_3696_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
v___x_3697_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0);
lean_inc(v_val_3695_);
v___x_3698_ = l_Int_Linear_Poly_mul(v_val_3695_, v___x_3697_);
v___x_3699_ = l_Int_Linear_Poly_addConst(v___x_3698_, v___x_3696_);
v___x_3700_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3700_, 0, v_e_3677_);
lean_ctor_set(v___x_3700_, 1, v_val_3695_);
v___x_3701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3701_, 0, v___x_3699_);
lean_ctor_set(v___x_3701_, 1, v___x_3700_);
v___x_3702_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v___x_3701_, v_a_3679_, v_a_3680_, v_a_3681_, v_a_3682_, v_a_3683_, v_a_3684_, v_a_3685_, v_a_3686_, v_a_3687_, v_a_3688_);
return v___x_3702_;
}
else
{
lean_object* v_val_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3712_; 
v_val_3703_ = lean_ctor_get(v_a_3691_, 0);
v_isSharedCheck_3712_ = !lean_is_exclusive(v_a_3691_);
if (v_isSharedCheck_3712_ == 0)
{
v___x_3705_ = v_a_3691_;
v_isShared_3706_ = v_isSharedCheck_3712_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_val_3703_);
lean_dec(v_a_3691_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3712_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
lean_object* v___x_3708_; 
if (v_isShared_3706_ == 0)
{
lean_ctor_set_tag(v___x_3705_, 0);
lean_ctor_set(v___x_3705_, 0, v_e_3677_);
v___x_3708_ = v___x_3705_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3711_; 
v_reuseFailAlloc_3711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3711_, 0, v_e_3677_);
v___x_3708_ = v_reuseFailAlloc_3711_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
lean_object* v___x_3709_; lean_object* v___x_3710_; 
v___x_3709_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3709_, 0, v_val_3703_);
lean_ctor_set(v___x_3709_, 1, v___x_3708_);
v___x_3710_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v___x_3709_, v_a_3679_, v_a_3680_, v_a_3681_, v_a_3682_, v_a_3683_, v_a_3684_, v_a_3685_, v_a_3686_, v_a_3687_, v_a_3688_);
return v___x_3710_;
}
}
}
}
else
{
lean_object* v___x_3713_; lean_object* v___x_3715_; 
lean_dec(v_a_3691_);
lean_dec_ref(v_e_3677_);
v___x_3713_ = lean_box(0);
if (v_isShared_3694_ == 0)
{
lean_ctor_set(v___x_3693_, 0, v___x_3713_);
v___x_3715_ = v___x_3693_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3716_; 
v_reuseFailAlloc_3716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3716_, 0, v___x_3713_);
v___x_3715_ = v_reuseFailAlloc_3716_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
return v___x_3715_;
}
}
}
}
else
{
lean_object* v_a_3718_; lean_object* v___x_3720_; uint8_t v_isShared_3721_; uint8_t v_isSharedCheck_3725_; 
lean_dec_ref(v_e_3677_);
v_a_3718_ = lean_ctor_get(v___x_3690_, 0);
v_isSharedCheck_3725_ = !lean_is_exclusive(v___x_3690_);
if (v_isSharedCheck_3725_ == 0)
{
v___x_3720_ = v___x_3690_;
v_isShared_3721_ = v_isSharedCheck_3725_;
goto v_resetjp_3719_;
}
else
{
lean_inc(v_a_3718_);
lean_dec(v___x_3690_);
v___x_3720_ = lean_box(0);
v_isShared_3721_ = v_isSharedCheck_3725_;
goto v_resetjp_3719_;
}
v_resetjp_3719_:
{
lean_object* v___x_3723_; 
if (v_isShared_3721_ == 0)
{
v___x_3723_ = v___x_3720_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v_a_3718_);
v___x_3723_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
return v___x_3723_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___boxed(lean_object* v_e_3726_, lean_object* v_eqTrue_3727_, lean_object* v_a_3728_, lean_object* v_a_3729_, lean_object* v_a_3730_, lean_object* v_a_3731_, lean_object* v_a_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_){
_start:
{
uint8_t v_eqTrue_boxed_3739_; lean_object* v_res_3740_; 
v_eqTrue_boxed_3739_ = lean_unbox(v_eqTrue_3727_);
v_res_3740_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe(v_e_3726_, v_eqTrue_boxed_3739_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_, v_a_3737_);
lean_dec(v_a_3737_);
lean_dec_ref(v_a_3736_);
lean_dec(v_a_3735_);
lean_dec_ref(v_a_3734_);
lean_dec(v_a_3733_);
lean_dec_ref(v_a_3732_);
lean_dec(v_a_3731_);
lean_dec_ref(v_a_3730_);
lean_dec(v_a_3729_);
lean_dec(v_a_3728_);
return v_res_3740_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0(void){
_start:
{
lean_object* v___x_3741_; lean_object* v___x_3742_; 
v___x_3741_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
v___x_3742_ = l_Lean_mkIntLit(v___x_3741_);
return v___x_3742_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5(void){
_start:
{
lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; 
v___x_3750_ = lean_box(0);
v___x_3751_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__4));
v___x_3752_ = l_Lean_mkConst(v___x_3751_, v___x_3750_);
return v___x_3752_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8(void){
_start:
{
lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; 
v___x_3758_ = lean_box(0);
v___x_3759_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__7));
v___x_3760_ = l_Lean_mkConst(v___x_3759_, v___x_3758_);
return v___x_3760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe(lean_object* v_e_3761_, uint8_t v_eqTrue_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_){
_start:
{
lean_object* v___y_3775_; lean_object* v___y_3776_; lean_object* v_fst_3777_; lean_object* v_snd_3778_; lean_object* v___x_3807_; uint8_t v___x_3808_; 
lean_inc_ref(v_e_3761_);
v___x_3807_ = l_Lean_Expr_cleanupAnnotations(v_e_3761_);
v___x_3808_ = l_Lean_Expr_isApp(v___x_3807_);
if (v___x_3808_ == 0)
{
lean_dec_ref(v___x_3807_);
lean_dec_ref(v_e_3761_);
goto v___jp_3804_;
}
else
{
lean_object* v_arg_3809_; lean_object* v___x_3810_; uint8_t v___x_3811_; 
v_arg_3809_ = lean_ctor_get(v___x_3807_, 1);
lean_inc_ref(v_arg_3809_);
v___x_3810_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3807_);
v___x_3811_ = l_Lean_Expr_isApp(v___x_3810_);
if (v___x_3811_ == 0)
{
lean_dec_ref(v___x_3810_);
lean_dec_ref(v_arg_3809_);
lean_dec_ref(v_e_3761_);
goto v___jp_3804_;
}
else
{
lean_object* v_arg_3812_; lean_object* v___y_3814_; lean_object* v___x_3852_; uint8_t v___x_3853_; 
v_arg_3812_ = lean_ctor_get(v___x_3810_, 1);
lean_inc_ref(v_arg_3812_);
v___x_3852_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3810_);
v___x_3853_ = l_Lean_Expr_isApp(v___x_3852_);
if (v___x_3853_ == 0)
{
lean_dec_ref(v___x_3852_);
lean_dec_ref(v_arg_3812_);
lean_dec_ref(v_arg_3809_);
lean_dec_ref(v_e_3761_);
goto v___jp_3804_;
}
else
{
lean_object* v___x_3854_; uint8_t v___x_3855_; 
v___x_3854_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3852_);
v___x_3855_ = l_Lean_Expr_isApp(v___x_3854_);
if (v___x_3855_ == 0)
{
lean_dec_ref(v___x_3854_);
lean_dec_ref(v_arg_3812_);
lean_dec_ref(v_arg_3809_);
lean_dec_ref(v_e_3761_);
goto v___jp_3804_;
}
else
{
lean_object* v___x_3856_; lean_object* v___x_3857_; uint8_t v___x_3858_; 
v___x_3856_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3854_);
v___x_3857_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2));
v___x_3858_ = l_Lean_Expr_isConstOf(v___x_3856_, v___x_3857_);
lean_dec_ref(v___x_3856_);
if (v___x_3858_ == 0)
{
lean_dec_ref(v_arg_3812_);
lean_dec_ref(v_arg_3809_);
lean_dec_ref(v_e_3761_);
goto v___jp_3804_;
}
else
{
if (v_eqTrue_3762_ == 0)
{
lean_object* v___x_3859_; 
v___x_3859_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5);
v___y_3814_ = v___x_3859_;
goto v___jp_3813_;
}
else
{
lean_object* v___x_3860_; 
v___x_3860_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8);
v___y_3814_ = v___x_3860_;
goto v___jp_3813_;
}
}
}
}
v___jp_3813_:
{
lean_object* v___x_3815_; 
v___x_3815_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_3761_, v_a_3763_);
if (lean_obj_tag(v___x_3815_) == 0)
{
lean_object* v_a_3816_; lean_object* v___x_3817_; 
v_a_3816_ = lean_ctor_get(v___x_3815_, 0);
lean_inc(v_a_3816_);
lean_dec_ref(v___x_3815_);
lean_inc_ref(v_arg_3812_);
v___x_3817_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_3812_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_);
if (lean_obj_tag(v___x_3817_) == 0)
{
lean_object* v_a_3818_; lean_object* v_fst_3819_; lean_object* v_snd_3820_; lean_object* v___x_3821_; 
v_a_3818_ = lean_ctor_get(v___x_3817_, 0);
lean_inc(v_a_3818_);
lean_dec_ref(v___x_3817_);
v_fst_3819_ = lean_ctor_get(v_a_3818_, 0);
lean_inc(v_fst_3819_);
v_snd_3820_ = lean_ctor_get(v_a_3818_, 1);
lean_inc(v_snd_3820_);
lean_dec(v_a_3818_);
lean_inc_ref(v_arg_3809_);
v___x_3821_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_3809_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_);
if (lean_obj_tag(v___x_3821_) == 0)
{
lean_object* v_a_3822_; lean_object* v_fst_3823_; lean_object* v_snd_3824_; lean_object* v___x_3825_; 
v_a_3822_ = lean_ctor_get(v___x_3821_, 0);
lean_inc(v_a_3822_);
lean_dec_ref(v___x_3821_);
v_fst_3823_ = lean_ctor_get(v_a_3822_, 0);
lean_inc(v_fst_3823_);
v_snd_3824_ = lean_ctor_get(v_a_3822_, 1);
lean_inc(v_snd_3824_);
lean_dec(v_a_3822_);
lean_inc(v_fst_3823_);
lean_inc(v_fst_3819_);
v___x_3825_ = l_Lean_mkApp6(v___y_3814_, v_arg_3812_, v_arg_3809_, v_fst_3819_, v_fst_3823_, v_snd_3820_, v_snd_3824_);
if (v_eqTrue_3762_ == 0)
{
lean_object* v___x_3826_; lean_object* v___x_3827_; 
v___x_3826_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0);
v___x_3827_ = l_Lean_mkIntAdd(v_fst_3823_, v___x_3826_);
v___y_3775_ = v_a_3816_;
v___y_3776_ = v___x_3825_;
v_fst_3777_ = v___x_3827_;
v_snd_3778_ = v_fst_3819_;
goto v___jp_3774_;
}
else
{
v___y_3775_ = v_a_3816_;
v___y_3776_ = v___x_3825_;
v_fst_3777_ = v_fst_3819_;
v_snd_3778_ = v_fst_3823_;
goto v___jp_3774_;
}
}
else
{
lean_object* v_a_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3835_; 
lean_dec(v_snd_3820_);
lean_dec(v_fst_3819_);
lean_dec(v_a_3816_);
lean_dec_ref(v___y_3814_);
lean_dec_ref(v_arg_3812_);
lean_dec_ref(v_arg_3809_);
lean_dec_ref(v_e_3761_);
v_a_3828_ = lean_ctor_get(v___x_3821_, 0);
v_isSharedCheck_3835_ = !lean_is_exclusive(v___x_3821_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3830_ = v___x_3821_;
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_a_3828_);
lean_dec(v___x_3821_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v___x_3833_; 
if (v_isShared_3831_ == 0)
{
v___x_3833_ = v___x_3830_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v_a_3828_);
v___x_3833_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
return v___x_3833_;
}
}
}
}
else
{
lean_object* v_a_3836_; lean_object* v___x_3838_; uint8_t v_isShared_3839_; uint8_t v_isSharedCheck_3843_; 
lean_dec(v_a_3816_);
lean_dec_ref(v___y_3814_);
lean_dec_ref(v_arg_3812_);
lean_dec_ref(v_arg_3809_);
lean_dec_ref(v_e_3761_);
v_a_3836_ = lean_ctor_get(v___x_3817_, 0);
v_isSharedCheck_3843_ = !lean_is_exclusive(v___x_3817_);
if (v_isSharedCheck_3843_ == 0)
{
v___x_3838_ = v___x_3817_;
v_isShared_3839_ = v_isSharedCheck_3843_;
goto v_resetjp_3837_;
}
else
{
lean_inc(v_a_3836_);
lean_dec(v___x_3817_);
v___x_3838_ = lean_box(0);
v_isShared_3839_ = v_isSharedCheck_3843_;
goto v_resetjp_3837_;
}
v_resetjp_3837_:
{
lean_object* v___x_3841_; 
if (v_isShared_3839_ == 0)
{
v___x_3841_ = v___x_3838_;
goto v_reusejp_3840_;
}
else
{
lean_object* v_reuseFailAlloc_3842_; 
v_reuseFailAlloc_3842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3842_, 0, v_a_3836_);
v___x_3841_ = v_reuseFailAlloc_3842_;
goto v_reusejp_3840_;
}
v_reusejp_3840_:
{
return v___x_3841_;
}
}
}
}
else
{
lean_object* v_a_3844_; lean_object* v___x_3846_; uint8_t v_isShared_3847_; uint8_t v_isSharedCheck_3851_; 
lean_dec_ref(v___y_3814_);
lean_dec_ref(v_arg_3812_);
lean_dec_ref(v_arg_3809_);
lean_dec_ref(v_e_3761_);
v_a_3844_ = lean_ctor_get(v___x_3815_, 0);
v_isSharedCheck_3851_ = !lean_is_exclusive(v___x_3815_);
if (v_isSharedCheck_3851_ == 0)
{
v___x_3846_ = v___x_3815_;
v_isShared_3847_ = v_isSharedCheck_3851_;
goto v_resetjp_3845_;
}
else
{
lean_inc(v_a_3844_);
lean_dec(v___x_3815_);
v___x_3846_ = lean_box(0);
v_isShared_3847_ = v_isSharedCheck_3851_;
goto v_resetjp_3845_;
}
v_resetjp_3845_:
{
lean_object* v___x_3849_; 
if (v_isShared_3847_ == 0)
{
v___x_3849_ = v___x_3846_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v_a_3844_);
v___x_3849_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
return v___x_3849_;
}
}
}
}
}
}
v___jp_3774_:
{
lean_object* v___x_3779_; 
lean_inc(v___y_3775_);
v___x_3779_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_3777_, v___y_3775_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_);
if (lean_obj_tag(v___x_3779_) == 0)
{
lean_object* v_a_3780_; lean_object* v___x_3781_; 
v_a_3780_ = lean_ctor_get(v___x_3779_, 0);
lean_inc(v_a_3780_);
lean_dec_ref(v___x_3779_);
v___x_3781_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_snd_3778_, v___y_3775_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_);
if (lean_obj_tag(v___x_3781_) == 0)
{
lean_object* v_a_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; 
v_a_3782_ = lean_ctor_get(v___x_3781_, 0);
lean_inc(v_a_3782_);
lean_dec_ref(v___x_3781_);
lean_inc(v_a_3782_);
lean_inc(v_a_3780_);
v___x_3783_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3783_, 0, v_a_3780_);
lean_ctor_set(v___x_3783_, 1, v_a_3782_);
v___x_3784_ = l_Int_Linear_Expr_norm(v___x_3783_);
lean_dec_ref(v___x_3783_);
v___x_3785_ = lean_alloc_ctor(2, 4, 1);
lean_ctor_set(v___x_3785_, 0, v_e_3761_);
lean_ctor_set(v___x_3785_, 1, v___y_3776_);
lean_ctor_set(v___x_3785_, 2, v_a_3780_);
lean_ctor_set(v___x_3785_, 3, v_a_3782_);
lean_ctor_set_uint8(v___x_3785_, sizeof(void*)*4, v_eqTrue_3762_);
v___x_3786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3786_, 0, v___x_3784_);
lean_ctor_set(v___x_3786_, 1, v___x_3785_);
v___x_3787_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v___x_3786_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_);
return v___x_3787_;
}
else
{
lean_object* v_a_3788_; lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3795_; 
lean_dec(v_a_3780_);
lean_dec_ref(v___y_3776_);
lean_dec_ref(v_e_3761_);
v_a_3788_ = lean_ctor_get(v___x_3781_, 0);
v_isSharedCheck_3795_ = !lean_is_exclusive(v___x_3781_);
if (v_isSharedCheck_3795_ == 0)
{
v___x_3790_ = v___x_3781_;
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
else
{
lean_inc(v_a_3788_);
lean_dec(v___x_3781_);
v___x_3790_ = lean_box(0);
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
v_resetjp_3789_:
{
lean_object* v___x_3793_; 
if (v_isShared_3791_ == 0)
{
v___x_3793_ = v___x_3790_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_a_3788_);
v___x_3793_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
return v___x_3793_;
}
}
}
}
else
{
lean_object* v_a_3796_; lean_object* v___x_3798_; uint8_t v_isShared_3799_; uint8_t v_isSharedCheck_3803_; 
lean_dec_ref(v_snd_3778_);
lean_dec_ref(v___y_3776_);
lean_dec(v___y_3775_);
lean_dec_ref(v_e_3761_);
v_a_3796_ = lean_ctor_get(v___x_3779_, 0);
v_isSharedCheck_3803_ = !lean_is_exclusive(v___x_3779_);
if (v_isSharedCheck_3803_ == 0)
{
v___x_3798_ = v___x_3779_;
v_isShared_3799_ = v_isSharedCheck_3803_;
goto v_resetjp_3797_;
}
else
{
lean_inc(v_a_3796_);
lean_dec(v___x_3779_);
v___x_3798_ = lean_box(0);
v_isShared_3799_ = v_isSharedCheck_3803_;
goto v_resetjp_3797_;
}
v_resetjp_3797_:
{
lean_object* v___x_3801_; 
if (v_isShared_3799_ == 0)
{
v___x_3801_ = v___x_3798_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3802_; 
v_reuseFailAlloc_3802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3802_, 0, v_a_3796_);
v___x_3801_ = v_reuseFailAlloc_3802_;
goto v_reusejp_3800_;
}
v_reusejp_3800_:
{
return v___x_3801_;
}
}
}
}
v___jp_3804_:
{
lean_object* v___x_3805_; lean_object* v___x_3806_; 
v___x_3805_ = lean_box(0);
v___x_3806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3806_, 0, v___x_3805_);
return v___x_3806_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___boxed(lean_object* v_e_3861_, lean_object* v_eqTrue_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_){
_start:
{
uint8_t v_eqTrue_boxed_3874_; lean_object* v_res_3875_; 
v_eqTrue_boxed_3874_ = lean_unbox(v_eqTrue_3862_);
v_res_3875_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe(v_e_3861_, v_eqTrue_boxed_3874_, v_a_3863_, v_a_3864_, v_a_3865_, v_a_3866_, v_a_3867_, v_a_3868_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_);
lean_dec(v_a_3872_);
lean_dec_ref(v_a_3871_);
lean_dec(v_a_3870_);
lean_dec_ref(v_a_3869_);
lean_dec(v_a_3868_);
lean_dec_ref(v_a_3867_);
lean_dec(v_a_3866_);
lean_dec_ref(v_a_3865_);
lean_dec(v_a_3864_);
lean_dec(v_a_3863_);
return v_res_3875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe(lean_object* v_e_3876_, uint8_t v_eqTrue_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_, lean_object* v_a_3885_, lean_object* v_a_3886_, lean_object* v_a_3887_, lean_object* v_a_3888_){
_start:
{
lean_object* v___y_3894_; lean_object* v___y_3895_; lean_object* v___y_3896_; lean_object* v___y_3897_; lean_object* v___y_3898_; lean_object* v___y_3899_; lean_object* v___y_3900_; lean_object* v___y_3901_; lean_object* v___y_3902_; lean_object* v___y_3903_; lean_object* v___y_3904_; lean_object* v___y_3905_; lean_object* v_fst_3906_; lean_object* v_snd_3907_; lean_object* v_____x_3934_; lean_object* v___y_3935_; lean_object* v___y_3936_; lean_object* v___y_3937_; lean_object* v___y_3938_; lean_object* v___y_3939_; lean_object* v___y_3940_; lean_object* v___y_3941_; lean_object* v___y_3942_; lean_object* v___y_3943_; lean_object* v___y_3944_; lean_object* v___y_3945_; 
if (v_eqTrue_3877_ == 0)
{
lean_object* v___x_3999_; 
v___x_3999_ = l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLE_x3f___redArg(v_a_3878_, v_a_3879_, v_a_3885_, v_a_3886_, v_a_3887_, v_a_3888_);
if (lean_obj_tag(v___x_3999_) == 0)
{
lean_object* v_a_4000_; 
v_a_4000_ = lean_ctor_get(v___x_3999_, 0);
lean_inc(v_a_4000_);
lean_dec_ref(v___x_3999_);
v_____x_3934_ = v_a_4000_;
v___y_3935_ = v_a_3878_;
v___y_3936_ = v_a_3879_;
v___y_3937_ = v_a_3880_;
v___y_3938_ = v_a_3881_;
v___y_3939_ = v_a_3882_;
v___y_3940_ = v_a_3883_;
v___y_3941_ = v_a_3884_;
v___y_3942_ = v_a_3885_;
v___y_3943_ = v_a_3886_;
v___y_3944_ = v_a_3887_;
v___y_3945_ = v_a_3888_;
goto v___jp_3933_;
}
else
{
lean_object* v_a_4001_; lean_object* v___x_4003_; uint8_t v_isShared_4004_; uint8_t v_isSharedCheck_4008_; 
lean_dec_ref(v_e_3876_);
v_a_4001_ = lean_ctor_get(v___x_3999_, 0);
v_isSharedCheck_4008_ = !lean_is_exclusive(v___x_3999_);
if (v_isSharedCheck_4008_ == 0)
{
v___x_4003_ = v___x_3999_;
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
else
{
lean_inc(v_a_4001_);
lean_dec(v___x_3999_);
v___x_4003_ = lean_box(0);
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
v_resetjp_4002_:
{
lean_object* v___x_4006_; 
if (v_isShared_4004_ == 0)
{
v___x_4006_ = v___x_4003_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v_a_4001_);
v___x_4006_ = v_reuseFailAlloc_4007_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
return v___x_4006_;
}
}
}
}
else
{
lean_object* v___x_4009_; 
v___x_4009_ = l_Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f___redArg(v_a_3878_, v_a_3879_, v_a_3885_, v_a_3886_, v_a_3887_, v_a_3888_);
if (lean_obj_tag(v___x_4009_) == 0)
{
lean_object* v_a_4010_; 
v_a_4010_ = lean_ctor_get(v___x_4009_, 0);
lean_inc(v_a_4010_);
lean_dec_ref(v___x_4009_);
v_____x_3934_ = v_a_4010_;
v___y_3935_ = v_a_3878_;
v___y_3936_ = v_a_3879_;
v___y_3937_ = v_a_3880_;
v___y_3938_ = v_a_3881_;
v___y_3939_ = v_a_3882_;
v___y_3940_ = v_a_3883_;
v___y_3941_ = v_a_3884_;
v___y_3942_ = v_a_3885_;
v___y_3943_ = v_a_3886_;
v___y_3944_ = v_a_3887_;
v___y_3945_ = v_a_3888_;
goto v___jp_3933_;
}
else
{
lean_object* v_a_4011_; lean_object* v___x_4013_; uint8_t v_isShared_4014_; uint8_t v_isSharedCheck_4018_; 
lean_dec_ref(v_e_3876_);
v_a_4011_ = lean_ctor_get(v___x_4009_, 0);
v_isSharedCheck_4018_ = !lean_is_exclusive(v___x_4009_);
if (v_isSharedCheck_4018_ == 0)
{
v___x_4013_ = v___x_4009_;
v_isShared_4014_ = v_isSharedCheck_4018_;
goto v_resetjp_4012_;
}
else
{
lean_inc(v_a_4011_);
lean_dec(v___x_4009_);
v___x_4013_ = lean_box(0);
v_isShared_4014_ = v_isSharedCheck_4018_;
goto v_resetjp_4012_;
}
v_resetjp_4012_:
{
lean_object* v___x_4016_; 
if (v_isShared_4014_ == 0)
{
v___x_4016_ = v___x_4013_;
goto v_reusejp_4015_;
}
else
{
lean_object* v_reuseFailAlloc_4017_; 
v_reuseFailAlloc_4017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4017_, 0, v_a_4011_);
v___x_4016_ = v_reuseFailAlloc_4017_;
goto v_reusejp_4015_;
}
v_reusejp_4015_:
{
return v___x_4016_;
}
}
}
}
v___jp_3890_:
{
lean_object* v___x_3891_; lean_object* v___x_3892_; 
v___x_3891_ = lean_box(0);
v___x_3892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3892_, 0, v___x_3891_);
return v___x_3892_;
}
v___jp_3893_:
{
lean_object* v___x_3908_; 
lean_inc(v___y_3899_);
v___x_3908_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_3906_, v___y_3899_, v___y_3896_, v___y_3894_, v___y_3903_, v___y_3900_, v___y_3897_, v___y_3904_, v___y_3898_, v___y_3901_, v___y_3895_, v___y_3902_);
if (lean_obj_tag(v___x_3908_) == 0)
{
lean_object* v_a_3909_; lean_object* v___x_3910_; 
v_a_3909_ = lean_ctor_get(v___x_3908_, 0);
lean_inc(v_a_3909_);
lean_dec_ref(v___x_3908_);
v___x_3910_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_snd_3907_, v___y_3899_, v___y_3896_, v___y_3894_, v___y_3903_, v___y_3900_, v___y_3897_, v___y_3904_, v___y_3898_, v___y_3901_, v___y_3895_, v___y_3902_);
if (lean_obj_tag(v___x_3910_) == 0)
{
lean_object* v_a_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; 
v_a_3911_ = lean_ctor_get(v___x_3910_, 0);
lean_inc(v_a_3911_);
lean_dec_ref(v___x_3910_);
lean_inc(v_a_3911_);
lean_inc(v_a_3909_);
v___x_3912_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3912_, 0, v_a_3909_);
lean_ctor_set(v___x_3912_, 1, v_a_3911_);
v___x_3913_ = l_Int_Linear_Expr_norm(v___x_3912_);
lean_dec_ref(v___x_3912_);
v___x_3914_ = lean_alloc_ctor(2, 4, 1);
lean_ctor_set(v___x_3914_, 0, v_e_3876_);
lean_ctor_set(v___x_3914_, 1, v___y_3905_);
lean_ctor_set(v___x_3914_, 2, v_a_3909_);
lean_ctor_set(v___x_3914_, 3, v_a_3911_);
lean_ctor_set_uint8(v___x_3914_, sizeof(void*)*4, v_eqTrue_3877_);
v___x_3915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3915_, 0, v___x_3913_);
lean_ctor_set(v___x_3915_, 1, v___x_3914_);
v___x_3916_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v___x_3915_, v___y_3896_, v___y_3894_, v___y_3903_, v___y_3900_, v___y_3897_, v___y_3904_, v___y_3898_, v___y_3901_, v___y_3895_, v___y_3902_);
return v___x_3916_;
}
else
{
lean_object* v_a_3917_; lean_object* v___x_3919_; uint8_t v_isShared_3920_; uint8_t v_isSharedCheck_3924_; 
lean_dec(v_a_3909_);
lean_dec_ref(v___y_3905_);
lean_dec_ref(v_e_3876_);
v_a_3917_ = lean_ctor_get(v___x_3910_, 0);
v_isSharedCheck_3924_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_3924_ == 0)
{
v___x_3919_ = v___x_3910_;
v_isShared_3920_ = v_isSharedCheck_3924_;
goto v_resetjp_3918_;
}
else
{
lean_inc(v_a_3917_);
lean_dec(v___x_3910_);
v___x_3919_ = lean_box(0);
v_isShared_3920_ = v_isSharedCheck_3924_;
goto v_resetjp_3918_;
}
v_resetjp_3918_:
{
lean_object* v___x_3922_; 
if (v_isShared_3920_ == 0)
{
v___x_3922_ = v___x_3919_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v_a_3917_);
v___x_3922_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
return v___x_3922_;
}
}
}
}
else
{
lean_object* v_a_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3932_; 
lean_dec_ref(v_snd_3907_);
lean_dec_ref(v___y_3905_);
lean_dec(v___y_3899_);
lean_dec_ref(v_e_3876_);
v_a_3925_ = lean_ctor_get(v___x_3908_, 0);
v_isSharedCheck_3932_ = !lean_is_exclusive(v___x_3908_);
if (v_isSharedCheck_3932_ == 0)
{
v___x_3927_ = v___x_3908_;
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_a_3925_);
lean_dec(v___x_3908_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v___x_3930_; 
if (v_isShared_3928_ == 0)
{
v___x_3930_ = v___x_3927_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3931_; 
v_reuseFailAlloc_3931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3931_, 0, v_a_3925_);
v___x_3930_ = v_reuseFailAlloc_3931_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
return v___x_3930_;
}
}
}
}
v___jp_3933_:
{
if (lean_obj_tag(v_____x_3934_) == 1)
{
lean_object* v_val_3946_; lean_object* v___x_3947_; uint8_t v___x_3948_; 
v_val_3946_ = lean_ctor_get(v_____x_3934_, 0);
lean_inc(v_val_3946_);
lean_dec_ref(v_____x_3934_);
lean_inc_ref(v_e_3876_);
v___x_3947_ = l_Lean_Expr_cleanupAnnotations(v_e_3876_);
v___x_3948_ = l_Lean_Expr_isApp(v___x_3947_);
if (v___x_3948_ == 0)
{
lean_dec_ref(v___x_3947_);
lean_dec(v_val_3946_);
lean_dec_ref(v_e_3876_);
goto v___jp_3890_;
}
else
{
lean_object* v_arg_3949_; lean_object* v___x_3950_; uint8_t v___x_3951_; 
v_arg_3949_ = lean_ctor_get(v___x_3947_, 1);
lean_inc_ref(v_arg_3949_);
v___x_3950_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3947_);
v___x_3951_ = l_Lean_Expr_isApp(v___x_3950_);
if (v___x_3951_ == 0)
{
lean_dec_ref(v___x_3950_);
lean_dec_ref(v_arg_3949_);
lean_dec(v_val_3946_);
lean_dec_ref(v_e_3876_);
goto v___jp_3890_;
}
else
{
lean_object* v_arg_3952_; lean_object* v___x_3953_; uint8_t v___x_3954_; 
v_arg_3952_ = lean_ctor_get(v___x_3950_, 1);
lean_inc_ref(v_arg_3952_);
v___x_3953_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3950_);
v___x_3954_ = l_Lean_Expr_isApp(v___x_3953_);
if (v___x_3954_ == 0)
{
lean_dec_ref(v___x_3953_);
lean_dec_ref(v_arg_3952_);
lean_dec_ref(v_arg_3949_);
lean_dec(v_val_3946_);
lean_dec_ref(v_e_3876_);
goto v___jp_3890_;
}
else
{
lean_object* v___x_3955_; uint8_t v___x_3956_; 
v___x_3955_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3953_);
v___x_3956_ = l_Lean_Expr_isApp(v___x_3955_);
if (v___x_3956_ == 0)
{
lean_dec_ref(v___x_3955_);
lean_dec_ref(v_arg_3952_);
lean_dec_ref(v_arg_3949_);
lean_dec(v_val_3946_);
lean_dec_ref(v_e_3876_);
goto v___jp_3890_;
}
else
{
lean_object* v___x_3957_; lean_object* v___x_3958_; uint8_t v___x_3959_; 
v___x_3957_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3955_);
v___x_3958_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2));
v___x_3959_ = l_Lean_Expr_isConstOf(v___x_3957_, v___x_3958_);
lean_dec_ref(v___x_3957_);
if (v___x_3959_ == 0)
{
lean_dec_ref(v_arg_3952_);
lean_dec_ref(v_arg_3949_);
lean_dec(v_val_3946_);
lean_dec_ref(v_e_3876_);
goto v___jp_3890_;
}
else
{
lean_object* v___x_3960_; 
v___x_3960_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_3876_, v___y_3936_);
if (lean_obj_tag(v___x_3960_) == 0)
{
lean_object* v_a_3961_; lean_object* v___x_3962_; 
v_a_3961_ = lean_ctor_get(v___x_3960_, 0);
lean_inc(v_a_3961_);
lean_dec_ref(v___x_3960_);
lean_inc_ref(v_arg_3952_);
v___x_3962_ = l_Lean_Meta_Grind_Arith_Cutsat_toInt(v_arg_3952_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_);
if (lean_obj_tag(v___x_3962_) == 0)
{
lean_object* v_a_3963_; lean_object* v_fst_3964_; lean_object* v_snd_3965_; lean_object* v___x_3966_; 
v_a_3963_ = lean_ctor_get(v___x_3962_, 0);
lean_inc(v_a_3963_);
lean_dec_ref(v___x_3962_);
v_fst_3964_ = lean_ctor_get(v_a_3963_, 0);
lean_inc(v_fst_3964_);
v_snd_3965_ = lean_ctor_get(v_a_3963_, 1);
lean_inc(v_snd_3965_);
lean_dec(v_a_3963_);
lean_inc_ref(v_arg_3949_);
v___x_3966_ = l_Lean_Meta_Grind_Arith_Cutsat_toInt(v_arg_3949_, v___y_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_);
if (lean_obj_tag(v___x_3966_) == 0)
{
lean_object* v_a_3967_; lean_object* v_fst_3968_; lean_object* v_snd_3969_; lean_object* v___x_3970_; 
v_a_3967_ = lean_ctor_get(v___x_3966_, 0);
lean_inc(v_a_3967_);
lean_dec_ref(v___x_3966_);
v_fst_3968_ = lean_ctor_get(v_a_3967_, 0);
lean_inc(v_fst_3968_);
v_snd_3969_ = lean_ctor_get(v_a_3967_, 1);
lean_inc(v_snd_3969_);
lean_dec(v_a_3967_);
lean_inc(v_fst_3968_);
lean_inc(v_fst_3964_);
v___x_3970_ = l_Lean_mkApp6(v_val_3946_, v_arg_3952_, v_arg_3949_, v_fst_3964_, v_fst_3968_, v_snd_3965_, v_snd_3969_);
if (v_eqTrue_3877_ == 0)
{
lean_object* v___x_3971_; lean_object* v___x_3972_; 
v___x_3971_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0);
v___x_3972_ = l_Lean_mkIntAdd(v_fst_3968_, v___x_3971_);
v___y_3894_ = v___y_3937_;
v___y_3895_ = v___y_3944_;
v___y_3896_ = v___y_3936_;
v___y_3897_ = v___y_3940_;
v___y_3898_ = v___y_3942_;
v___y_3899_ = v_a_3961_;
v___y_3900_ = v___y_3939_;
v___y_3901_ = v___y_3943_;
v___y_3902_ = v___y_3945_;
v___y_3903_ = v___y_3938_;
v___y_3904_ = v___y_3941_;
v___y_3905_ = v___x_3970_;
v_fst_3906_ = v___x_3972_;
v_snd_3907_ = v_fst_3964_;
goto v___jp_3893_;
}
else
{
v___y_3894_ = v___y_3937_;
v___y_3895_ = v___y_3944_;
v___y_3896_ = v___y_3936_;
v___y_3897_ = v___y_3940_;
v___y_3898_ = v___y_3942_;
v___y_3899_ = v_a_3961_;
v___y_3900_ = v___y_3939_;
v___y_3901_ = v___y_3943_;
v___y_3902_ = v___y_3945_;
v___y_3903_ = v___y_3938_;
v___y_3904_ = v___y_3941_;
v___y_3905_ = v___x_3970_;
v_fst_3906_ = v_fst_3964_;
v_snd_3907_ = v_fst_3968_;
goto v___jp_3893_;
}
}
else
{
lean_object* v_a_3973_; lean_object* v___x_3975_; uint8_t v_isShared_3976_; uint8_t v_isSharedCheck_3980_; 
lean_dec(v_snd_3965_);
lean_dec(v_fst_3964_);
lean_dec(v_a_3961_);
lean_dec_ref(v_arg_3952_);
lean_dec_ref(v_arg_3949_);
lean_dec(v_val_3946_);
lean_dec_ref(v_e_3876_);
v_a_3973_ = lean_ctor_get(v___x_3966_, 0);
v_isSharedCheck_3980_ = !lean_is_exclusive(v___x_3966_);
if (v_isSharedCheck_3980_ == 0)
{
v___x_3975_ = v___x_3966_;
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
else
{
lean_inc(v_a_3973_);
lean_dec(v___x_3966_);
v___x_3975_ = lean_box(0);
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
v_resetjp_3974_:
{
lean_object* v___x_3978_; 
if (v_isShared_3976_ == 0)
{
v___x_3978_ = v___x_3975_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v_a_3973_);
v___x_3978_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
return v___x_3978_;
}
}
}
}
else
{
lean_object* v_a_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_3988_; 
lean_dec(v_a_3961_);
lean_dec_ref(v_arg_3952_);
lean_dec_ref(v_arg_3949_);
lean_dec(v_val_3946_);
lean_dec_ref(v_e_3876_);
v_a_3981_ = lean_ctor_get(v___x_3962_, 0);
v_isSharedCheck_3988_ = !lean_is_exclusive(v___x_3962_);
if (v_isSharedCheck_3988_ == 0)
{
v___x_3983_ = v___x_3962_;
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_a_3981_);
lean_dec(v___x_3962_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v___x_3986_; 
if (v_isShared_3984_ == 0)
{
v___x_3986_ = v___x_3983_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v_a_3981_);
v___x_3986_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
return v___x_3986_;
}
}
}
}
else
{
lean_object* v_a_3989_; lean_object* v___x_3991_; uint8_t v_isShared_3992_; uint8_t v_isSharedCheck_3996_; 
lean_dec_ref(v_arg_3952_);
lean_dec_ref(v_arg_3949_);
lean_dec(v_val_3946_);
lean_dec_ref(v_e_3876_);
v_a_3989_ = lean_ctor_get(v___x_3960_, 0);
v_isSharedCheck_3996_ = !lean_is_exclusive(v___x_3960_);
if (v_isSharedCheck_3996_ == 0)
{
v___x_3991_ = v___x_3960_;
v_isShared_3992_ = v_isSharedCheck_3996_;
goto v_resetjp_3990_;
}
else
{
lean_inc(v_a_3989_);
lean_dec(v___x_3960_);
v___x_3991_ = lean_box(0);
v_isShared_3992_ = v_isSharedCheck_3996_;
goto v_resetjp_3990_;
}
v_resetjp_3990_:
{
lean_object* v___x_3994_; 
if (v_isShared_3992_ == 0)
{
v___x_3994_ = v___x_3991_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_3995_; 
v_reuseFailAlloc_3995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3995_, 0, v_a_3989_);
v___x_3994_ = v_reuseFailAlloc_3995_;
goto v_reusejp_3993_;
}
v_reusejp_3993_:
{
return v___x_3994_;
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
lean_object* v___x_3997_; lean_object* v___x_3998_; 
lean_dec(v_____x_3934_);
lean_dec_ref(v_e_3876_);
v___x_3997_ = lean_box(0);
v___x_3998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3998_, 0, v___x_3997_);
return v___x_3998_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe___boxed(lean_object* v_e_4019_, lean_object* v_eqTrue_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_, lean_object* v_a_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_){
_start:
{
uint8_t v_eqTrue_boxed_4033_; lean_object* v_res_4034_; 
v_eqTrue_boxed_4033_ = lean_unbox(v_eqTrue_4020_);
v_res_4034_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe(v_e_4019_, v_eqTrue_boxed_4033_, v_a_4021_, v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_, v_a_4026_, v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_);
lean_dec(v_a_4031_);
lean_dec_ref(v_a_4030_);
lean_dec(v_a_4029_);
lean_dec_ref(v_a_4028_);
lean_dec(v_a_4027_);
lean_dec_ref(v_a_4026_);
lean_dec(v_a_4025_);
lean_dec_ref(v_a_4024_);
lean_dec(v_a_4023_);
lean_dec(v_a_4022_);
lean_dec(v_a_4021_);
return v_res_4034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe(lean_object* v_e_4040_, uint8_t v_eqTrue_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_, lean_object* v_a_4044_, lean_object* v_a_4045_, lean_object* v_a_4046_, lean_object* v_a_4047_, lean_object* v_a_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_, lean_object* v_a_4051_){
_start:
{
lean_object* v___x_4056_; 
v___x_4056_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_4044_);
if (lean_obj_tag(v___x_4056_) == 0)
{
lean_object* v_a_4057_; lean_object* v___x_4059_; uint8_t v_isShared_4060_; uint8_t v_isSharedCheck_4087_; 
v_a_4057_ = lean_ctor_get(v___x_4056_, 0);
v_isSharedCheck_4087_ = !lean_is_exclusive(v___x_4056_);
if (v_isSharedCheck_4087_ == 0)
{
v___x_4059_ = v___x_4056_;
v_isShared_4060_ = v_isSharedCheck_4087_;
goto v_resetjp_4058_;
}
else
{
lean_inc(v_a_4057_);
lean_dec(v___x_4056_);
v___x_4059_ = lean_box(0);
v_isShared_4060_ = v_isSharedCheck_4087_;
goto v_resetjp_4058_;
}
v_resetjp_4058_:
{
uint8_t v_lia_4061_; 
v_lia_4061_ = lean_ctor_get_uint8(v_a_4057_, sizeof(void*)*11 + 23);
lean_dec(v_a_4057_);
if (v_lia_4061_ == 0)
{
lean_object* v___x_4062_; lean_object* v___x_4064_; 
lean_dec_ref(v_e_4040_);
v___x_4062_ = lean_box(0);
if (v_isShared_4060_ == 0)
{
lean_ctor_set(v___x_4059_, 0, v___x_4062_);
v___x_4064_ = v___x_4059_;
goto v_reusejp_4063_;
}
else
{
lean_object* v_reuseFailAlloc_4065_; 
v_reuseFailAlloc_4065_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4065_, 0, v___x_4062_);
v___x_4064_ = v_reuseFailAlloc_4065_;
goto v_reusejp_4063_;
}
v_reusejp_4063_:
{
return v___x_4064_;
}
}
else
{
lean_object* v___x_4066_; uint8_t v___x_4067_; 
lean_del_object(v___x_4059_);
lean_inc_ref(v_e_4040_);
v___x_4066_ = l_Lean_Expr_cleanupAnnotations(v_e_4040_);
v___x_4067_ = l_Lean_Expr_isApp(v___x_4066_);
if (v___x_4067_ == 0)
{
lean_dec_ref(v___x_4066_);
lean_dec_ref(v_e_4040_);
goto v___jp_4053_;
}
else
{
lean_object* v___x_4068_; uint8_t v___x_4069_; 
v___x_4068_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4066_);
v___x_4069_ = l_Lean_Expr_isApp(v___x_4068_);
if (v___x_4069_ == 0)
{
lean_dec_ref(v___x_4068_);
lean_dec_ref(v_e_4040_);
goto v___jp_4053_;
}
else
{
lean_object* v___x_4070_; uint8_t v___x_4071_; 
v___x_4070_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4068_);
v___x_4071_ = l_Lean_Expr_isApp(v___x_4070_);
if (v___x_4071_ == 0)
{
lean_dec_ref(v___x_4070_);
lean_dec_ref(v_e_4040_);
goto v___jp_4053_;
}
else
{
lean_object* v___x_4072_; uint8_t v___x_4073_; 
v___x_4072_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4070_);
v___x_4073_ = l_Lean_Expr_isApp(v___x_4072_);
if (v___x_4073_ == 0)
{
lean_dec_ref(v___x_4072_);
lean_dec_ref(v_e_4040_);
goto v___jp_4053_;
}
else
{
lean_object* v_arg_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; uint8_t v___x_4077_; 
v_arg_4074_ = lean_ctor_get(v___x_4072_, 1);
lean_inc_ref(v_arg_4074_);
v___x_4075_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4072_);
v___x_4076_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2));
v___x_4077_ = l_Lean_Expr_isConstOf(v___x_4075_, v___x_4076_);
lean_dec_ref(v___x_4075_);
if (v___x_4077_ == 0)
{
lean_dec_ref(v_arg_4074_);
lean_dec_ref(v_e_4040_);
goto v___jp_4053_;
}
else
{
lean_object* v___x_4078_; uint8_t v___x_4079_; 
v___x_4078_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__0));
v___x_4079_ = l_Lean_Expr_isConstOf(v_arg_4074_, v___x_4078_);
if (v___x_4079_ == 0)
{
lean_object* v___x_4080_; uint8_t v___x_4081_; 
v___x_4080_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__2));
v___x_4081_ = l_Lean_Expr_isConstOf(v_arg_4074_, v___x_4080_);
if (v___x_4081_ == 0)
{
lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; 
v___x_4082_ = lean_box(v_eqTrue_4041_);
v___x_4083_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe___boxed), 14, 2);
lean_closure_set(v___x_4083_, 0, v_e_4040_);
lean_closure_set(v___x_4083_, 1, v___x_4082_);
v___x_4084_ = l_Lean_Meta_Grind_Arith_Cutsat_ToIntM_run(v_arg_4074_, v___x_4083_, v_a_4042_, v_a_4043_, v_a_4044_, v_a_4045_, v_a_4046_, v_a_4047_, v_a_4048_, v_a_4049_, v_a_4050_, v_a_4051_);
return v___x_4084_;
}
else
{
lean_object* v___x_4085_; 
lean_dec_ref(v_arg_4074_);
v___x_4085_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe(v_e_4040_, v_eqTrue_4041_, v_a_4042_, v_a_4043_, v_a_4044_, v_a_4045_, v_a_4046_, v_a_4047_, v_a_4048_, v_a_4049_, v_a_4050_, v_a_4051_);
return v___x_4085_;
}
}
else
{
lean_object* v___x_4086_; 
lean_dec_ref(v_arg_4074_);
v___x_4086_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe(v_e_4040_, v_eqTrue_4041_, v_a_4042_, v_a_4043_, v_a_4044_, v_a_4045_, v_a_4046_, v_a_4047_, v_a_4048_, v_a_4049_, v_a_4050_, v_a_4051_);
return v___x_4086_;
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
lean_object* v_a_4088_; lean_object* v___x_4090_; uint8_t v_isShared_4091_; uint8_t v_isSharedCheck_4095_; 
lean_dec_ref(v_e_4040_);
v_a_4088_ = lean_ctor_get(v___x_4056_, 0);
v_isSharedCheck_4095_ = !lean_is_exclusive(v___x_4056_);
if (v_isSharedCheck_4095_ == 0)
{
v___x_4090_ = v___x_4056_;
v_isShared_4091_ = v_isSharedCheck_4095_;
goto v_resetjp_4089_;
}
else
{
lean_inc(v_a_4088_);
lean_dec(v___x_4056_);
v___x_4090_ = lean_box(0);
v_isShared_4091_ = v_isSharedCheck_4095_;
goto v_resetjp_4089_;
}
v_resetjp_4089_:
{
lean_object* v___x_4093_; 
if (v_isShared_4091_ == 0)
{
v___x_4093_ = v___x_4090_;
goto v_reusejp_4092_;
}
else
{
lean_object* v_reuseFailAlloc_4094_; 
v_reuseFailAlloc_4094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4094_, 0, v_a_4088_);
v___x_4093_ = v_reuseFailAlloc_4094_;
goto v_reusejp_4092_;
}
v_reusejp_4092_:
{
return v___x_4093_;
}
}
}
v___jp_4053_:
{
lean_object* v___x_4054_; lean_object* v___x_4055_; 
v___x_4054_ = lean_box(0);
v___x_4055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4055_, 0, v___x_4054_);
return v___x_4055_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___boxed(lean_object* v_e_4096_, lean_object* v_eqTrue_4097_, lean_object* v_a_4098_, lean_object* v_a_4099_, lean_object* v_a_4100_, lean_object* v_a_4101_, lean_object* v_a_4102_, lean_object* v_a_4103_, lean_object* v_a_4104_, lean_object* v_a_4105_, lean_object* v_a_4106_, lean_object* v_a_4107_, lean_object* v_a_4108_){
_start:
{
uint8_t v_eqTrue_boxed_4109_; lean_object* v_res_4110_; 
v_eqTrue_boxed_4109_ = lean_unbox(v_eqTrue_4097_);
v_res_4110_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLe(v_e_4096_, v_eqTrue_boxed_4109_, v_a_4098_, v_a_4099_, v_a_4100_, v_a_4101_, v_a_4102_, v_a_4103_, v_a_4104_, v_a_4105_, v_a_4106_, v_a_4107_);
lean_dec(v_a_4107_);
lean_dec_ref(v_a_4106_);
lean_dec(v_a_4105_);
lean_dec_ref(v_a_4104_);
lean_dec(v_a_4103_);
lean_dec_ref(v_a_4102_);
lean_dec(v_a_4101_);
lean_dec_ref(v_a_4100_);
lean_dec(v_a_4099_);
lean_dec(v_a_4098_);
return v_res_4110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__0(lean_object* v_e_4111_, lean_object* v_arg_4112_, lean_object* v_arg_4113_, uint8_t v_eqTrue_4114_, lean_object* v_____x_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_){
_start:
{
if (lean_obj_tag(v_____x_4115_) == 1)
{
lean_object* v_val_4128_; lean_object* v___x_4129_; 
v_val_4128_ = lean_ctor_get(v_____x_4115_, 0);
lean_inc(v_val_4128_);
lean_dec_ref(v_____x_4115_);
v___x_4129_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_4111_, v___y_4117_);
if (lean_obj_tag(v___x_4129_) == 0)
{
lean_object* v_a_4130_; lean_object* v___x_4131_; 
v_a_4130_ = lean_ctor_get(v___x_4129_, 0);
lean_inc(v_a_4130_);
lean_dec_ref(v___x_4129_);
lean_inc_ref(v_arg_4112_);
v___x_4131_ = l_Lean_Meta_Grind_Arith_Cutsat_toInt(v_arg_4112_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
if (lean_obj_tag(v___x_4131_) == 0)
{
lean_object* v_a_4132_; lean_object* v_fst_4133_; lean_object* v_snd_4134_; lean_object* v___x_4136_; uint8_t v_isShared_4137_; uint8_t v_isSharedCheck_4189_; 
v_a_4132_ = lean_ctor_get(v___x_4131_, 0);
lean_inc(v_a_4132_);
lean_dec_ref(v___x_4131_);
v_fst_4133_ = lean_ctor_get(v_a_4132_, 0);
v_snd_4134_ = lean_ctor_get(v_a_4132_, 1);
v_isSharedCheck_4189_ = !lean_is_exclusive(v_a_4132_);
if (v_isSharedCheck_4189_ == 0)
{
v___x_4136_ = v_a_4132_;
v_isShared_4137_ = v_isSharedCheck_4189_;
goto v_resetjp_4135_;
}
else
{
lean_inc(v_snd_4134_);
lean_inc(v_fst_4133_);
lean_dec(v_a_4132_);
v___x_4136_ = lean_box(0);
v_isShared_4137_ = v_isSharedCheck_4189_;
goto v_resetjp_4135_;
}
v_resetjp_4135_:
{
lean_object* v___x_4138_; 
lean_inc_ref(v_arg_4113_);
v___x_4138_ = l_Lean_Meta_Grind_Arith_Cutsat_toInt(v_arg_4113_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
if (lean_obj_tag(v___x_4138_) == 0)
{
lean_object* v_a_4139_; lean_object* v_fst_4140_; lean_object* v_snd_4141_; lean_object* v___x_4143_; uint8_t v_isShared_4144_; uint8_t v_isSharedCheck_4180_; 
v_a_4139_ = lean_ctor_get(v___x_4138_, 0);
lean_inc(v_a_4139_);
lean_dec_ref(v___x_4138_);
v_fst_4140_ = lean_ctor_get(v_a_4139_, 0);
v_snd_4141_ = lean_ctor_get(v_a_4139_, 1);
v_isSharedCheck_4180_ = !lean_is_exclusive(v_a_4139_);
if (v_isSharedCheck_4180_ == 0)
{
v___x_4143_ = v_a_4139_;
v_isShared_4144_ = v_isSharedCheck_4180_;
goto v_resetjp_4142_;
}
else
{
lean_inc(v_snd_4141_);
lean_inc(v_fst_4140_);
lean_dec(v_a_4139_);
v___x_4143_ = lean_box(0);
v_isShared_4144_ = v_isSharedCheck_4180_;
goto v_resetjp_4142_;
}
v_resetjp_4142_:
{
lean_object* v___x_4145_; lean_object* v_fst_4147_; lean_object* v_snd_4148_; 
lean_inc(v_fst_4140_);
lean_inc(v_fst_4133_);
v___x_4145_ = l_Lean_mkApp6(v_val_4128_, v_arg_4112_, v_arg_4113_, v_fst_4133_, v_fst_4140_, v_snd_4134_, v_snd_4141_);
if (v_eqTrue_4114_ == 0)
{
v_fst_4147_ = v_fst_4140_;
v_snd_4148_ = v_fst_4133_;
goto v___jp_4146_;
}
else
{
lean_object* v___x_4178_; lean_object* v___x_4179_; 
v___x_4178_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0);
v___x_4179_ = l_Lean_mkIntAdd(v_fst_4133_, v___x_4178_);
v_fst_4147_ = v___x_4179_;
v_snd_4148_ = v_fst_4140_;
goto v___jp_4146_;
}
v___jp_4146_:
{
lean_object* v___x_4149_; 
lean_inc(v_a_4130_);
v___x_4149_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_4147_, v_a_4130_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
if (lean_obj_tag(v___x_4149_) == 0)
{
lean_object* v_a_4150_; lean_object* v___x_4151_; 
v_a_4150_ = lean_ctor_get(v___x_4149_, 0);
lean_inc(v_a_4150_);
lean_dec_ref(v___x_4149_);
v___x_4151_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_snd_4148_, v_a_4130_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
if (lean_obj_tag(v___x_4151_) == 0)
{
lean_object* v_a_4152_; lean_object* v___x_4154_; 
v_a_4152_ = lean_ctor_get(v___x_4151_, 0);
lean_inc(v_a_4152_);
lean_dec_ref(v___x_4151_);
lean_inc(v_a_4152_);
lean_inc(v_a_4150_);
if (v_isShared_4144_ == 0)
{
lean_ctor_set_tag(v___x_4143_, 3);
lean_ctor_set(v___x_4143_, 1, v_a_4152_);
lean_ctor_set(v___x_4143_, 0, v_a_4150_);
v___x_4154_ = v___x_4143_;
goto v_reusejp_4153_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v_a_4150_);
lean_ctor_set(v_reuseFailAlloc_4161_, 1, v_a_4152_);
v___x_4154_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4153_;
}
v_reusejp_4153_:
{
lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4158_; 
v___x_4155_ = l_Int_Linear_Expr_norm(v___x_4154_);
lean_dec_ref(v___x_4154_);
v___x_4156_ = lean_alloc_ctor(2, 4, 1);
lean_ctor_set(v___x_4156_, 0, v_e_4111_);
lean_ctor_set(v___x_4156_, 1, v___x_4145_);
lean_ctor_set(v___x_4156_, 2, v_a_4150_);
lean_ctor_set(v___x_4156_, 3, v_a_4152_);
lean_ctor_set_uint8(v___x_4156_, sizeof(void*)*4, v_eqTrue_4114_);
if (v_isShared_4137_ == 0)
{
lean_ctor_set(v___x_4136_, 1, v___x_4156_);
lean_ctor_set(v___x_4136_, 0, v___x_4155_);
v___x_4158_ = v___x_4136_;
goto v_reusejp_4157_;
}
else
{
lean_object* v_reuseFailAlloc_4160_; 
v_reuseFailAlloc_4160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4160_, 0, v___x_4155_);
lean_ctor_set(v_reuseFailAlloc_4160_, 1, v___x_4156_);
v___x_4158_ = v_reuseFailAlloc_4160_;
goto v_reusejp_4157_;
}
v_reusejp_4157_:
{
lean_object* v___x_4159_; 
lean_inc(v___y_4126_);
lean_inc_ref(v___y_4125_);
lean_inc(v___y_4124_);
lean_inc_ref(v___y_4123_);
lean_inc(v___y_4122_);
lean_inc_ref(v___y_4121_);
lean_inc(v___y_4120_);
lean_inc_ref(v___y_4119_);
lean_inc(v___y_4118_);
lean_inc(v___y_4117_);
v___x_4159_ = lean_grind_cutsat_assert_le(v___x_4158_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
return v___x_4159_;
}
}
}
else
{
lean_object* v_a_4162_; lean_object* v___x_4164_; uint8_t v_isShared_4165_; uint8_t v_isSharedCheck_4169_; 
lean_dec(v_a_4150_);
lean_dec_ref(v___x_4145_);
lean_del_object(v___x_4143_);
lean_del_object(v___x_4136_);
lean_dec_ref(v_e_4111_);
v_a_4162_ = lean_ctor_get(v___x_4151_, 0);
v_isSharedCheck_4169_ = !lean_is_exclusive(v___x_4151_);
if (v_isSharedCheck_4169_ == 0)
{
v___x_4164_ = v___x_4151_;
v_isShared_4165_ = v_isSharedCheck_4169_;
goto v_resetjp_4163_;
}
else
{
lean_inc(v_a_4162_);
lean_dec(v___x_4151_);
v___x_4164_ = lean_box(0);
v_isShared_4165_ = v_isSharedCheck_4169_;
goto v_resetjp_4163_;
}
v_resetjp_4163_:
{
lean_object* v___x_4167_; 
if (v_isShared_4165_ == 0)
{
v___x_4167_ = v___x_4164_;
goto v_reusejp_4166_;
}
else
{
lean_object* v_reuseFailAlloc_4168_; 
v_reuseFailAlloc_4168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4168_, 0, v_a_4162_);
v___x_4167_ = v_reuseFailAlloc_4168_;
goto v_reusejp_4166_;
}
v_reusejp_4166_:
{
return v___x_4167_;
}
}
}
}
else
{
lean_object* v_a_4170_; lean_object* v___x_4172_; uint8_t v_isShared_4173_; uint8_t v_isSharedCheck_4177_; 
lean_dec_ref(v_snd_4148_);
lean_dec_ref(v___x_4145_);
lean_del_object(v___x_4143_);
lean_del_object(v___x_4136_);
lean_dec(v_a_4130_);
lean_dec_ref(v_e_4111_);
v_a_4170_ = lean_ctor_get(v___x_4149_, 0);
v_isSharedCheck_4177_ = !lean_is_exclusive(v___x_4149_);
if (v_isSharedCheck_4177_ == 0)
{
v___x_4172_ = v___x_4149_;
v_isShared_4173_ = v_isSharedCheck_4177_;
goto v_resetjp_4171_;
}
else
{
lean_inc(v_a_4170_);
lean_dec(v___x_4149_);
v___x_4172_ = lean_box(0);
v_isShared_4173_ = v_isSharedCheck_4177_;
goto v_resetjp_4171_;
}
v_resetjp_4171_:
{
lean_object* v___x_4175_; 
if (v_isShared_4173_ == 0)
{
v___x_4175_ = v___x_4172_;
goto v_reusejp_4174_;
}
else
{
lean_object* v_reuseFailAlloc_4176_; 
v_reuseFailAlloc_4176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4176_, 0, v_a_4170_);
v___x_4175_ = v_reuseFailAlloc_4176_;
goto v_reusejp_4174_;
}
v_reusejp_4174_:
{
return v___x_4175_;
}
}
}
}
}
}
else
{
lean_object* v_a_4181_; lean_object* v___x_4183_; uint8_t v_isShared_4184_; uint8_t v_isSharedCheck_4188_; 
lean_del_object(v___x_4136_);
lean_dec(v_snd_4134_);
lean_dec(v_fst_4133_);
lean_dec(v_a_4130_);
lean_dec(v_val_4128_);
lean_dec_ref(v_arg_4113_);
lean_dec_ref(v_arg_4112_);
lean_dec_ref(v_e_4111_);
v_a_4181_ = lean_ctor_get(v___x_4138_, 0);
v_isSharedCheck_4188_ = !lean_is_exclusive(v___x_4138_);
if (v_isSharedCheck_4188_ == 0)
{
v___x_4183_ = v___x_4138_;
v_isShared_4184_ = v_isSharedCheck_4188_;
goto v_resetjp_4182_;
}
else
{
lean_inc(v_a_4181_);
lean_dec(v___x_4138_);
v___x_4183_ = lean_box(0);
v_isShared_4184_ = v_isSharedCheck_4188_;
goto v_resetjp_4182_;
}
v_resetjp_4182_:
{
lean_object* v___x_4186_; 
if (v_isShared_4184_ == 0)
{
v___x_4186_ = v___x_4183_;
goto v_reusejp_4185_;
}
else
{
lean_object* v_reuseFailAlloc_4187_; 
v_reuseFailAlloc_4187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4187_, 0, v_a_4181_);
v___x_4186_ = v_reuseFailAlloc_4187_;
goto v_reusejp_4185_;
}
v_reusejp_4185_:
{
return v___x_4186_;
}
}
}
}
}
else
{
lean_object* v_a_4190_; lean_object* v___x_4192_; uint8_t v_isShared_4193_; uint8_t v_isSharedCheck_4197_; 
lean_dec(v_a_4130_);
lean_dec(v_val_4128_);
lean_dec_ref(v_arg_4113_);
lean_dec_ref(v_arg_4112_);
lean_dec_ref(v_e_4111_);
v_a_4190_ = lean_ctor_get(v___x_4131_, 0);
v_isSharedCheck_4197_ = !lean_is_exclusive(v___x_4131_);
if (v_isSharedCheck_4197_ == 0)
{
v___x_4192_ = v___x_4131_;
v_isShared_4193_ = v_isSharedCheck_4197_;
goto v_resetjp_4191_;
}
else
{
lean_inc(v_a_4190_);
lean_dec(v___x_4131_);
v___x_4192_ = lean_box(0);
v_isShared_4193_ = v_isSharedCheck_4197_;
goto v_resetjp_4191_;
}
v_resetjp_4191_:
{
lean_object* v___x_4195_; 
if (v_isShared_4193_ == 0)
{
v___x_4195_ = v___x_4192_;
goto v_reusejp_4194_;
}
else
{
lean_object* v_reuseFailAlloc_4196_; 
v_reuseFailAlloc_4196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4196_, 0, v_a_4190_);
v___x_4195_ = v_reuseFailAlloc_4196_;
goto v_reusejp_4194_;
}
v_reusejp_4194_:
{
return v___x_4195_;
}
}
}
}
else
{
lean_object* v_a_4198_; lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4205_; 
lean_dec(v_val_4128_);
lean_dec_ref(v_arg_4113_);
lean_dec_ref(v_arg_4112_);
lean_dec_ref(v_e_4111_);
v_a_4198_ = lean_ctor_get(v___x_4129_, 0);
v_isSharedCheck_4205_ = !lean_is_exclusive(v___x_4129_);
if (v_isSharedCheck_4205_ == 0)
{
v___x_4200_ = v___x_4129_;
v_isShared_4201_ = v_isSharedCheck_4205_;
goto v_resetjp_4199_;
}
else
{
lean_inc(v_a_4198_);
lean_dec(v___x_4129_);
v___x_4200_ = lean_box(0);
v_isShared_4201_ = v_isSharedCheck_4205_;
goto v_resetjp_4199_;
}
v_resetjp_4199_:
{
lean_object* v___x_4203_; 
if (v_isShared_4201_ == 0)
{
v___x_4203_ = v___x_4200_;
goto v_reusejp_4202_;
}
else
{
lean_object* v_reuseFailAlloc_4204_; 
v_reuseFailAlloc_4204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4204_, 0, v_a_4198_);
v___x_4203_ = v_reuseFailAlloc_4204_;
goto v_reusejp_4202_;
}
v_reusejp_4202_:
{
return v___x_4203_;
}
}
}
}
else
{
lean_object* v___x_4206_; lean_object* v___x_4207_; 
lean_dec(v_____x_4115_);
lean_dec_ref(v_arg_4113_);
lean_dec_ref(v_arg_4112_);
lean_dec_ref(v_e_4111_);
v___x_4206_ = lean_box(0);
v___x_4207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4207_, 0, v___x_4206_);
return v___x_4207_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__0___boxed(lean_object** _args){
lean_object* v_e_4208_ = _args[0];
lean_object* v_arg_4209_ = _args[1];
lean_object* v_arg_4210_ = _args[2];
lean_object* v_eqTrue_4211_ = _args[3];
lean_object* v_____x_4212_ = _args[4];
lean_object* v___y_4213_ = _args[5];
lean_object* v___y_4214_ = _args[6];
lean_object* v___y_4215_ = _args[7];
lean_object* v___y_4216_ = _args[8];
lean_object* v___y_4217_ = _args[9];
lean_object* v___y_4218_ = _args[10];
lean_object* v___y_4219_ = _args[11];
lean_object* v___y_4220_ = _args[12];
lean_object* v___y_4221_ = _args[13];
lean_object* v___y_4222_ = _args[14];
lean_object* v___y_4223_ = _args[15];
lean_object* v___y_4224_ = _args[16];
_start:
{
uint8_t v_eqTrue_boxed_4225_; lean_object* v_res_4226_; 
v_eqTrue_boxed_4225_ = lean_unbox(v_eqTrue_4211_);
v_res_4226_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__0(v_e_4208_, v_arg_4209_, v_arg_4210_, v_eqTrue_boxed_4225_, v_____x_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_);
lean_dec(v___y_4223_);
lean_dec_ref(v___y_4222_);
lean_dec(v___y_4221_);
lean_dec_ref(v___y_4220_);
lean_dec(v___y_4219_);
lean_dec_ref(v___y_4218_);
lean_dec(v___y_4217_);
lean_dec_ref(v___y_4216_);
lean_dec(v___y_4215_);
lean_dec(v___y_4214_);
lean_dec(v___y_4213_);
return v_res_4226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__1(uint8_t v_eqTrue_4227_, lean_object* v___f_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_){
_start:
{
if (v_eqTrue_4227_ == 0)
{
lean_object* v___x_4241_; 
v___x_4241_ = l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLT_x3f___redArg(v___y_4229_, v___y_4230_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_);
if (lean_obj_tag(v___x_4241_) == 0)
{
lean_object* v_a_4242_; lean_object* v___x_4243_; 
v_a_4242_ = lean_ctor_get(v___x_4241_, 0);
lean_inc(v_a_4242_);
lean_dec_ref(v___x_4241_);
lean_inc(v___y_4239_);
lean_inc_ref(v___y_4238_);
lean_inc(v___y_4237_);
lean_inc_ref(v___y_4236_);
lean_inc(v___y_4235_);
lean_inc_ref(v___y_4234_);
lean_inc(v___y_4233_);
lean_inc_ref(v___y_4232_);
lean_inc(v___y_4231_);
lean_inc(v___y_4230_);
lean_inc(v___y_4229_);
v___x_4243_ = lean_apply_13(v___f_4228_, v_a_4242_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_, lean_box(0));
return v___x_4243_;
}
else
{
lean_object* v_a_4244_; lean_object* v___x_4246_; uint8_t v_isShared_4247_; uint8_t v_isSharedCheck_4251_; 
lean_dec_ref(v___f_4228_);
v_a_4244_ = lean_ctor_get(v___x_4241_, 0);
v_isSharedCheck_4251_ = !lean_is_exclusive(v___x_4241_);
if (v_isSharedCheck_4251_ == 0)
{
v___x_4246_ = v___x_4241_;
v_isShared_4247_ = v_isSharedCheck_4251_;
goto v_resetjp_4245_;
}
else
{
lean_inc(v_a_4244_);
lean_dec(v___x_4241_);
v___x_4246_ = lean_box(0);
v_isShared_4247_ = v_isSharedCheck_4251_;
goto v_resetjp_4245_;
}
v_resetjp_4245_:
{
lean_object* v___x_4249_; 
if (v_isShared_4247_ == 0)
{
v___x_4249_ = v___x_4246_;
goto v_reusejp_4248_;
}
else
{
lean_object* v_reuseFailAlloc_4250_; 
v_reuseFailAlloc_4250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4250_, 0, v_a_4244_);
v___x_4249_ = v_reuseFailAlloc_4250_;
goto v_reusejp_4248_;
}
v_reusejp_4248_:
{
return v___x_4249_;
}
}
}
}
else
{
lean_object* v___x_4252_; 
v___x_4252_ = l_Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f___redArg(v___y_4229_, v___y_4230_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_);
if (lean_obj_tag(v___x_4252_) == 0)
{
lean_object* v_a_4253_; lean_object* v___x_4254_; 
v_a_4253_ = lean_ctor_get(v___x_4252_, 0);
lean_inc(v_a_4253_);
lean_dec_ref(v___x_4252_);
lean_inc(v___y_4239_);
lean_inc_ref(v___y_4238_);
lean_inc(v___y_4237_);
lean_inc_ref(v___y_4236_);
lean_inc(v___y_4235_);
lean_inc_ref(v___y_4234_);
lean_inc(v___y_4233_);
lean_inc_ref(v___y_4232_);
lean_inc(v___y_4231_);
lean_inc(v___y_4230_);
lean_inc(v___y_4229_);
v___x_4254_ = lean_apply_13(v___f_4228_, v_a_4253_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_, lean_box(0));
return v___x_4254_;
}
else
{
lean_object* v_a_4255_; lean_object* v___x_4257_; uint8_t v_isShared_4258_; uint8_t v_isSharedCheck_4262_; 
lean_dec_ref(v___f_4228_);
v_a_4255_ = lean_ctor_get(v___x_4252_, 0);
v_isSharedCheck_4262_ = !lean_is_exclusive(v___x_4252_);
if (v_isSharedCheck_4262_ == 0)
{
v___x_4257_ = v___x_4252_;
v_isShared_4258_ = v_isSharedCheck_4262_;
goto v_resetjp_4256_;
}
else
{
lean_inc(v_a_4255_);
lean_dec(v___x_4252_);
v___x_4257_ = lean_box(0);
v_isShared_4258_ = v_isSharedCheck_4262_;
goto v_resetjp_4256_;
}
v_resetjp_4256_:
{
lean_object* v___x_4260_; 
if (v_isShared_4258_ == 0)
{
v___x_4260_ = v___x_4257_;
goto v_reusejp_4259_;
}
else
{
lean_object* v_reuseFailAlloc_4261_; 
v_reuseFailAlloc_4261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4261_, 0, v_a_4255_);
v___x_4260_ = v_reuseFailAlloc_4261_;
goto v_reusejp_4259_;
}
v_reusejp_4259_:
{
return v___x_4260_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__1___boxed(lean_object* v_eqTrue_4263_, lean_object* v___f_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_){
_start:
{
uint8_t v_eqTrue_boxed_4277_; lean_object* v_res_4278_; 
v_eqTrue_boxed_4277_ = lean_unbox(v_eqTrue_4263_);
v_res_4278_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__1(v_eqTrue_boxed_4277_, v___f_4264_, v___y_4265_, v___y_4266_, v___y_4267_, v___y_4268_, v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_);
lean_dec(v___y_4275_);
lean_dec_ref(v___y_4274_);
lean_dec(v___y_4273_);
lean_dec_ref(v___y_4272_);
lean_dec(v___y_4271_);
lean_dec_ref(v___y_4270_);
lean_dec(v___y_4269_);
lean_dec_ref(v___y_4268_);
lean_dec(v___y_4267_);
lean_dec(v___y_4266_);
lean_dec(v___y_4265_);
return v_res_4278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt(lean_object* v_e_4284_, uint8_t v_eqTrue_4285_, lean_object* v_a_4286_, lean_object* v_a_4287_, lean_object* v_a_4288_, lean_object* v_a_4289_, lean_object* v_a_4290_, lean_object* v_a_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_, lean_object* v_a_4295_){
_start:
{
lean_object* v___x_4300_; 
v___x_4300_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_4288_);
if (lean_obj_tag(v___x_4300_) == 0)
{
lean_object* v_a_4301_; lean_object* v___x_4303_; uint8_t v_isShared_4304_; uint8_t v_isSharedCheck_4329_; 
v_a_4301_ = lean_ctor_get(v___x_4300_, 0);
v_isSharedCheck_4329_ = !lean_is_exclusive(v___x_4300_);
if (v_isSharedCheck_4329_ == 0)
{
v___x_4303_ = v___x_4300_;
v_isShared_4304_ = v_isSharedCheck_4329_;
goto v_resetjp_4302_;
}
else
{
lean_inc(v_a_4301_);
lean_dec(v___x_4300_);
v___x_4303_ = lean_box(0);
v_isShared_4304_ = v_isSharedCheck_4329_;
goto v_resetjp_4302_;
}
v_resetjp_4302_:
{
uint8_t v_lia_4305_; 
v_lia_4305_ = lean_ctor_get_uint8(v_a_4301_, sizeof(void*)*11 + 23);
lean_dec(v_a_4301_);
if (v_lia_4305_ == 0)
{
lean_object* v___x_4306_; lean_object* v___x_4308_; 
lean_dec_ref(v_e_4284_);
v___x_4306_ = lean_box(0);
if (v_isShared_4304_ == 0)
{
lean_ctor_set(v___x_4303_, 0, v___x_4306_);
v___x_4308_ = v___x_4303_;
goto v_reusejp_4307_;
}
else
{
lean_object* v_reuseFailAlloc_4309_; 
v_reuseFailAlloc_4309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4309_, 0, v___x_4306_);
v___x_4308_ = v_reuseFailAlloc_4309_;
goto v_reusejp_4307_;
}
v_reusejp_4307_:
{
return v___x_4308_;
}
}
else
{
lean_object* v___x_4310_; uint8_t v___x_4311_; 
lean_del_object(v___x_4303_);
lean_inc_ref(v_e_4284_);
v___x_4310_ = l_Lean_Expr_cleanupAnnotations(v_e_4284_);
v___x_4311_ = l_Lean_Expr_isApp(v___x_4310_);
if (v___x_4311_ == 0)
{
lean_dec_ref(v___x_4310_);
lean_dec_ref(v_e_4284_);
goto v___jp_4297_;
}
else
{
lean_object* v_arg_4312_; lean_object* v___x_4313_; uint8_t v___x_4314_; 
v_arg_4312_ = lean_ctor_get(v___x_4310_, 1);
lean_inc_ref(v_arg_4312_);
v___x_4313_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4310_);
v___x_4314_ = l_Lean_Expr_isApp(v___x_4313_);
if (v___x_4314_ == 0)
{
lean_dec_ref(v___x_4313_);
lean_dec_ref(v_arg_4312_);
lean_dec_ref(v_e_4284_);
goto v___jp_4297_;
}
else
{
lean_object* v_arg_4315_; lean_object* v___x_4316_; uint8_t v___x_4317_; 
v_arg_4315_ = lean_ctor_get(v___x_4313_, 1);
lean_inc_ref(v_arg_4315_);
v___x_4316_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4313_);
v___x_4317_ = l_Lean_Expr_isApp(v___x_4316_);
if (v___x_4317_ == 0)
{
lean_dec_ref(v___x_4316_);
lean_dec_ref(v_arg_4315_);
lean_dec_ref(v_arg_4312_);
lean_dec_ref(v_e_4284_);
goto v___jp_4297_;
}
else
{
lean_object* v___x_4318_; uint8_t v___x_4319_; 
v___x_4318_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4316_);
v___x_4319_ = l_Lean_Expr_isApp(v___x_4318_);
if (v___x_4319_ == 0)
{
lean_dec_ref(v___x_4318_);
lean_dec_ref(v_arg_4315_);
lean_dec_ref(v_arg_4312_);
lean_dec_ref(v_e_4284_);
goto v___jp_4297_;
}
else
{
lean_object* v_arg_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; uint8_t v___x_4323_; 
v_arg_4320_ = lean_ctor_get(v___x_4318_, 1);
lean_inc_ref(v_arg_4320_);
v___x_4321_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4318_);
v___x_4322_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__2));
v___x_4323_ = l_Lean_Expr_isConstOf(v___x_4321_, v___x_4322_);
lean_dec_ref(v___x_4321_);
if (v___x_4323_ == 0)
{
lean_dec_ref(v_arg_4320_);
lean_dec_ref(v_arg_4315_);
lean_dec_ref(v_arg_4312_);
lean_dec_ref(v_e_4284_);
goto v___jp_4297_;
}
else
{
lean_object* v___x_4324_; lean_object* v___f_4325_; lean_object* v___x_4326_; lean_object* v___y_4327_; lean_object* v___x_4328_; 
v___x_4324_ = lean_box(v_eqTrue_4285_);
v___f_4325_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__0___boxed), 17, 4);
lean_closure_set(v___f_4325_, 0, v_e_4284_);
lean_closure_set(v___f_4325_, 1, v_arg_4315_);
lean_closure_set(v___f_4325_, 2, v_arg_4312_);
lean_closure_set(v___f_4325_, 3, v___x_4324_);
v___x_4326_ = lean_box(v_eqTrue_4285_);
v___y_4327_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__1___boxed), 14, 2);
lean_closure_set(v___y_4327_, 0, v___x_4326_);
lean_closure_set(v___y_4327_, 1, v___f_4325_);
v___x_4328_ = l_Lean_Meta_Grind_Arith_Cutsat_ToIntM_run(v_arg_4320_, v___y_4327_, v_a_4286_, v_a_4287_, v_a_4288_, v_a_4289_, v_a_4290_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_, v_a_4295_);
return v___x_4328_;
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
lean_object* v_a_4330_; lean_object* v___x_4332_; uint8_t v_isShared_4333_; uint8_t v_isSharedCheck_4337_; 
lean_dec_ref(v_e_4284_);
v_a_4330_ = lean_ctor_get(v___x_4300_, 0);
v_isSharedCheck_4337_ = !lean_is_exclusive(v___x_4300_);
if (v_isSharedCheck_4337_ == 0)
{
v___x_4332_ = v___x_4300_;
v_isShared_4333_ = v_isSharedCheck_4337_;
goto v_resetjp_4331_;
}
else
{
lean_inc(v_a_4330_);
lean_dec(v___x_4300_);
v___x_4332_ = lean_box(0);
v_isShared_4333_ = v_isSharedCheck_4337_;
goto v_resetjp_4331_;
}
v_resetjp_4331_:
{
lean_object* v___x_4335_; 
if (v_isShared_4333_ == 0)
{
v___x_4335_ = v___x_4332_;
goto v_reusejp_4334_;
}
else
{
lean_object* v_reuseFailAlloc_4336_; 
v_reuseFailAlloc_4336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4336_, 0, v_a_4330_);
v___x_4335_ = v_reuseFailAlloc_4336_;
goto v_reusejp_4334_;
}
v_reusejp_4334_:
{
return v___x_4335_;
}
}
}
v___jp_4297_:
{
lean_object* v___x_4298_; lean_object* v___x_4299_; 
v___x_4298_ = lean_box(0);
v___x_4299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4299_, 0, v___x_4298_);
return v___x_4299_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___boxed(lean_object* v_e_4338_, lean_object* v_eqTrue_4339_, lean_object* v_a_4340_, lean_object* v_a_4341_, lean_object* v_a_4342_, lean_object* v_a_4343_, lean_object* v_a_4344_, lean_object* v_a_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_, lean_object* v_a_4348_, lean_object* v_a_4349_, lean_object* v_a_4350_){
_start:
{
uint8_t v_eqTrue_boxed_4351_; lean_object* v_res_4352_; 
v_eqTrue_boxed_4351_ = lean_unbox(v_eqTrue_4339_);
v_res_4352_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLt(v_e_4338_, v_eqTrue_boxed_4351_, v_a_4340_, v_a_4341_, v_a_4342_, v_a_4343_, v_a_4344_, v_a_4345_, v_a_4346_, v_a_4347_, v_a_4348_, v_a_4349_);
lean_dec(v_a_4349_);
lean_dec_ref(v_a_4348_);
lean_dec(v_a_4347_);
lean_dec_ref(v_a_4346_);
lean_dec(v_a_4345_);
lean_dec_ref(v_a_4344_);
lean_dec(v_a_4343_);
lean_dec_ref(v_a_4342_);
lean_dec(v_a_4341_);
lean_dec(v_a_4340_);
return v_res_4352_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Proof(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_OfNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Proof(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(uint8_t builtin);
lean_object* initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Int(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Proof(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_OfNat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Arith_Int(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Proof(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(builtin);
}
#ifdef __cplusplus
}
#endif
