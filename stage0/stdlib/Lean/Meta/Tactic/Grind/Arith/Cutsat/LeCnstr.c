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
lean_object* v_fileName_355_; lean_object* v_fileMap_356_; lean_object* v_options_357_; lean_object* v_currRecDepth_358_; lean_object* v_maxRecDepth_359_; lean_object* v_ref_360_; lean_object* v_currNamespace_361_; lean_object* v_openDecls_362_; lean_object* v_initHeartbeats_363_; lean_object* v_maxHeartbeats_364_; lean_object* v_quotContext_365_; lean_object* v_currMacroScope_366_; uint8_t v_diag_367_; lean_object* v_cancelTk_x3f_368_; uint8_t v_suppressElabErrors_369_; lean_object* v_inheritedTraceOptions_370_; lean_object* v___x_372_; uint8_t v_isShared_373_; uint8_t v_isSharedCheck_409_; 
v_fileName_355_ = lean_ctor_get(v_a_352_, 0);
v_fileMap_356_ = lean_ctor_get(v_a_352_, 1);
v_options_357_ = lean_ctor_get(v_a_352_, 2);
v_currRecDepth_358_ = lean_ctor_get(v_a_352_, 3);
v_maxRecDepth_359_ = lean_ctor_get(v_a_352_, 4);
v_ref_360_ = lean_ctor_get(v_a_352_, 5);
v_currNamespace_361_ = lean_ctor_get(v_a_352_, 6);
v_openDecls_362_ = lean_ctor_get(v_a_352_, 7);
v_initHeartbeats_363_ = lean_ctor_get(v_a_352_, 8);
v_maxHeartbeats_364_ = lean_ctor_get(v_a_352_, 9);
v_quotContext_365_ = lean_ctor_get(v_a_352_, 10);
v_currMacroScope_366_ = lean_ctor_get(v_a_352_, 11);
v_diag_367_ = lean_ctor_get_uint8(v_a_352_, sizeof(void*)*14);
v_cancelTk_x3f_368_ = lean_ctor_get(v_a_352_, 12);
v_suppressElabErrors_369_ = lean_ctor_get_uint8(v_a_352_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_370_ = lean_ctor_get(v_a_352_, 13);
v_isSharedCheck_409_ = !lean_is_exclusive(v_a_352_);
if (v_isSharedCheck_409_ == 0)
{
v___x_372_ = v_a_352_;
v_isShared_373_ = v_isSharedCheck_409_;
goto v_resetjp_371_;
}
else
{
lean_inc(v_inheritedTraceOptions_370_);
lean_inc(v_cancelTk_x3f_368_);
lean_inc(v_currMacroScope_366_);
lean_inc(v_quotContext_365_);
lean_inc(v_maxHeartbeats_364_);
lean_inc(v_initHeartbeats_363_);
lean_inc(v_openDecls_362_);
lean_inc(v_currNamespace_361_);
lean_inc(v_ref_360_);
lean_inc(v_maxRecDepth_359_);
lean_inc(v_currRecDepth_358_);
lean_inc(v_options_357_);
lean_inc(v_fileMap_356_);
lean_inc(v_fileName_355_);
lean_dec(v_a_352_);
v___x_372_ = lean_box(0);
v_isShared_373_ = v_isSharedCheck_409_;
goto v_resetjp_371_;
}
v_resetjp_371_:
{
uint8_t v___x_374_; 
v___x_374_ = lean_nat_dec_eq(v_currRecDepth_358_, v_maxRecDepth_359_);
if (v___x_374_ == 0)
{
lean_object* v_p_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_379_; 
v_p_375_ = lean_ctor_get(v_c_343_, 0);
v___x_376_ = lean_unsigned_to_nat(1u);
v___x_377_ = lean_nat_add(v_currRecDepth_358_, v___x_376_);
lean_dec(v_currRecDepth_358_);
if (v_isShared_373_ == 0)
{
lean_ctor_set(v___x_372_, 3, v___x_377_);
v___x_379_ = v___x_372_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_fileName_355_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v_fileMap_356_);
lean_ctor_set(v_reuseFailAlloc_407_, 2, v_options_357_);
lean_ctor_set(v_reuseFailAlloc_407_, 3, v___x_377_);
lean_ctor_set(v_reuseFailAlloc_407_, 4, v_maxRecDepth_359_);
lean_ctor_set(v_reuseFailAlloc_407_, 5, v_ref_360_);
lean_ctor_set(v_reuseFailAlloc_407_, 6, v_currNamespace_361_);
lean_ctor_set(v_reuseFailAlloc_407_, 7, v_openDecls_362_);
lean_ctor_set(v_reuseFailAlloc_407_, 8, v_initHeartbeats_363_);
lean_ctor_set(v_reuseFailAlloc_407_, 9, v_maxHeartbeats_364_);
lean_ctor_set(v_reuseFailAlloc_407_, 10, v_quotContext_365_);
lean_ctor_set(v_reuseFailAlloc_407_, 11, v_currMacroScope_366_);
lean_ctor_set(v_reuseFailAlloc_407_, 12, v_cancelTk_x3f_368_);
lean_ctor_set(v_reuseFailAlloc_407_, 13, v_inheritedTraceOptions_370_);
lean_ctor_set_uint8(v_reuseFailAlloc_407_, sizeof(void*)*14, v_diag_367_);
lean_ctor_set_uint8(v_reuseFailAlloc_407_, sizeof(void*)*14 + 1, v_suppressElabErrors_369_);
v___x_379_ = v_reuseFailAlloc_407_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
lean_object* v___x_380_; 
lean_inc_ref(v_p_375_);
v___x_380_ = l_Int_Linear_Poly_findVarToSubst___redArg(v_p_375_, v_a_344_, v___x_379_);
if (lean_obj_tag(v___x_380_) == 0)
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_398_; 
v_a_381_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_398_ == 0)
{
v___x_383_ = v___x_380_;
v_isShared_384_ = v_isSharedCheck_398_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_380_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_398_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
if (lean_obj_tag(v_a_381_) == 1)
{
lean_object* v_val_385_; lean_object* v_snd_386_; lean_object* v_snd_387_; lean_object* v_fst_388_; lean_object* v_fst_389_; lean_object* v_p_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
lean_del_object(v___x_383_);
v_val_385_ = lean_ctor_get(v_a_381_, 0);
lean_inc(v_val_385_);
lean_dec_ref(v_a_381_);
v_snd_386_ = lean_ctor_get(v_val_385_, 1);
lean_inc(v_snd_386_);
v_snd_387_ = lean_ctor_get(v_snd_386_, 1);
lean_inc(v_snd_387_);
v_fst_388_ = lean_ctor_get(v_val_385_, 0);
lean_inc(v_fst_388_);
lean_dec(v_val_385_);
v_fst_389_ = lean_ctor_get(v_snd_386_, 0);
lean_inc(v_fst_389_);
lean_dec(v_snd_386_);
v_p_390_ = lean_ctor_get(v_snd_387_, 0);
v___x_391_ = l_Int_Linear_Poly_coeff(v_p_390_, v_fst_389_);
v___x_392_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq(v___x_391_, v_fst_389_, v_snd_387_, v_fst_388_, v_c_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_, v_a_349_, v_a_350_, v_a_351_, v___x_379_, v_a_353_);
lean_dec(v_fst_388_);
lean_dec(v___x_391_);
if (lean_obj_tag(v___x_392_) == 0)
{
lean_object* v_a_393_; 
v_a_393_ = lean_ctor_get(v___x_392_, 0);
lean_inc(v_a_393_);
lean_dec_ref(v___x_392_);
v_c_343_ = v_a_393_;
v_a_352_ = v___x_379_;
goto _start;
}
else
{
lean_dec_ref(v___x_379_);
return v___x_392_;
}
}
else
{
lean_object* v___x_396_; 
lean_dec(v_a_381_);
lean_dec_ref(v___x_379_);
if (v_isShared_384_ == 0)
{
lean_ctor_set(v___x_383_, 0, v_c_343_);
v___x_396_ = v___x_383_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_c_343_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
}
else
{
lean_object* v_a_399_; lean_object* v___x_401_; uint8_t v_isShared_402_; uint8_t v_isSharedCheck_406_; 
lean_dec_ref(v___x_379_);
lean_dec_ref(v_c_343_);
v_a_399_ = lean_ctor_get(v___x_380_, 0);
v_isSharedCheck_406_ = !lean_is_exclusive(v___x_380_);
if (v_isSharedCheck_406_ == 0)
{
v___x_401_ = v___x_380_;
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
else
{
lean_inc(v_a_399_);
lean_dec(v___x_380_);
v___x_401_ = lean_box(0);
v_isShared_402_ = v_isSharedCheck_406_;
goto v_resetjp_400_;
}
v_resetjp_400_:
{
lean_object* v___x_404_; 
if (v_isShared_402_ == 0)
{
v___x_404_ = v___x_401_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v_a_399_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
}
else
{
lean_object* v___x_408_; 
lean_del_object(v___x_372_);
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
v___x_408_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg(v_ref_360_);
return v___x_408_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts___boxed(lean_object* v_c_410_, lean_object* v_a_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_, lean_object* v_a_420_, lean_object* v_a_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts(v_c_410_, v_a_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_, v_a_419_, v_a_420_);
lean_dec(v_a_420_);
lean_dec(v_a_418_);
lean_dec_ref(v_a_417_);
lean_dec(v_a_416_);
lean_dec_ref(v_a_415_);
lean_dec(v_a_414_);
lean_dec_ref(v_a_413_);
lean_dec(v_a_412_);
lean_dec(v_a_411_);
return v_res_422_;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_Poly_isNegEq(lean_object* v_p_u2081_423_, lean_object* v_p_u2082_424_){
_start:
{
if (lean_obj_tag(v_p_u2081_423_) == 0)
{
if (lean_obj_tag(v_p_u2082_424_) == 0)
{
lean_object* v_k_425_; lean_object* v_k_426_; lean_object* v___x_427_; uint8_t v___x_428_; 
v_k_425_ = lean_ctor_get(v_p_u2081_423_, 0);
v_k_426_ = lean_ctor_get(v_p_u2082_424_, 0);
v___x_427_ = lean_int_neg(v_k_426_);
v___x_428_ = lean_int_dec_eq(v_k_425_, v___x_427_);
lean_dec(v___x_427_);
return v___x_428_;
}
else
{
uint8_t v___x_429_; 
v___x_429_ = 0;
return v___x_429_;
}
}
else
{
if (lean_obj_tag(v_p_u2082_424_) == 1)
{
lean_object* v_k_430_; lean_object* v_v_431_; lean_object* v_p_432_; lean_object* v_k_433_; lean_object* v_v_434_; lean_object* v_p_435_; uint8_t v___y_437_; lean_object* v___x_439_; uint8_t v___x_440_; 
v_k_430_ = lean_ctor_get(v_p_u2081_423_, 0);
v_v_431_ = lean_ctor_get(v_p_u2081_423_, 1);
v_p_432_ = lean_ctor_get(v_p_u2081_423_, 2);
v_k_433_ = lean_ctor_get(v_p_u2082_424_, 0);
v_v_434_ = lean_ctor_get(v_p_u2082_424_, 1);
v_p_435_ = lean_ctor_get(v_p_u2082_424_, 2);
v___x_439_ = lean_int_neg(v_k_433_);
v___x_440_ = lean_int_dec_eq(v_k_430_, v___x_439_);
lean_dec(v___x_439_);
if (v___x_440_ == 0)
{
v___y_437_ = v___x_440_;
goto v___jp_436_;
}
else
{
uint8_t v___x_441_; 
v___x_441_ = lean_nat_dec_eq(v_v_431_, v_v_434_);
v___y_437_ = v___x_441_;
goto v___jp_436_;
}
v___jp_436_:
{
if (v___y_437_ == 0)
{
return v___y_437_;
}
else
{
v_p_u2081_423_ = v_p_432_;
v_p_u2082_424_ = v_p_435_;
goto _start;
}
}
}
else
{
uint8_t v___x_442_; 
v___x_442_ = 0;
return v___x_442_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isNegEq___boxed(lean_object* v_p_u2081_443_, lean_object* v_p_u2082_444_){
_start:
{
uint8_t v_res_445_; lean_object* v_r_446_; 
v_res_445_ = l_Int_Linear_Poly_isNegEq(v_p_u2081_443_, v_p_u2082_444_);
lean_dec_ref(v_p_u2082_444_);
lean_dec_ref(v_p_u2081_443_);
v_r_446_ = lean_box(v_res_445_);
return v_r_446_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(lean_object* v___x_447_, lean_object* v_as_448_, size_t v_i_449_, size_t v_stop_450_, lean_object* v_b_451_){
_start:
{
lean_object* v___y_453_; uint8_t v___x_457_; 
v___x_457_ = lean_usize_dec_eq(v_i_449_, v_stop_450_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; lean_object* v_p_459_; uint8_t v___x_460_; 
v___x_458_ = lean_array_uget_borrowed(v_as_448_, v_i_449_);
v_p_459_ = lean_ctor_get(v___x_458_, 0);
v___x_460_ = l_Int_Linear_instBEqPoly_beq(v_p_459_, v___x_447_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; 
lean_inc(v___x_458_);
v___x_461_ = l_Lean_PersistentArray_push___redArg(v_b_451_, v___x_458_);
v___y_453_ = v___x_461_;
goto v___jp_452_;
}
else
{
v___y_453_ = v_b_451_;
goto v___jp_452_;
}
}
else
{
return v_b_451_;
}
v___jp_452_:
{
size_t v___x_454_; size_t v___x_455_; 
v___x_454_ = ((size_t)1ULL);
v___x_455_ = lean_usize_add(v_i_449_, v___x_454_);
v_i_449_ = v___x_455_;
v_b_451_ = v___y_453_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1___boxed(lean_object* v___x_462_, lean_object* v_as_463_, lean_object* v_i_464_, lean_object* v_stop_465_, lean_object* v_b_466_){
_start:
{
size_t v_i_boxed_467_; size_t v_stop_boxed_468_; lean_object* v_res_469_; 
v_i_boxed_467_ = lean_unbox_usize(v_i_464_);
lean_dec(v_i_464_);
v_stop_boxed_468_ = lean_unbox_usize(v_stop_465_);
lean_dec(v_stop_465_);
v_res_469_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_462_, v_as_463_, v_i_boxed_467_, v_stop_boxed_468_, v_b_466_);
lean_dec_ref(v_as_463_);
lean_dec_ref(v___x_462_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2(lean_object* v___x_470_, lean_object* v_x_471_, lean_object* v_x_472_){
_start:
{
if (lean_obj_tag(v_x_471_) == 0)
{
lean_object* v_cs_473_; lean_object* v___x_474_; lean_object* v___x_475_; uint8_t v___x_476_; 
v_cs_473_ = lean_ctor_get(v_x_471_, 0);
v___x_474_ = lean_unsigned_to_nat(0u);
v___x_475_ = lean_array_get_size(v_cs_473_);
v___x_476_ = lean_nat_dec_lt(v___x_474_, v___x_475_);
if (v___x_476_ == 0)
{
return v_x_472_;
}
else
{
uint8_t v___x_477_; 
v___x_477_ = lean_nat_dec_le(v___x_475_, v___x_475_);
if (v___x_477_ == 0)
{
if (v___x_476_ == 0)
{
return v_x_472_;
}
else
{
size_t v___x_478_; size_t v___x_479_; lean_object* v___x_480_; 
v___x_478_ = ((size_t)0ULL);
v___x_479_ = lean_usize_of_nat(v___x_475_);
v___x_480_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v___x_470_, v_cs_473_, v___x_478_, v___x_479_, v_x_472_);
return v___x_480_;
}
}
else
{
size_t v___x_481_; size_t v___x_482_; lean_object* v___x_483_; 
v___x_481_ = ((size_t)0ULL);
v___x_482_ = lean_usize_of_nat(v___x_475_);
v___x_483_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v___x_470_, v_cs_473_, v___x_481_, v___x_482_, v_x_472_);
return v___x_483_;
}
}
}
else
{
lean_object* v_vs_484_; lean_object* v___x_485_; lean_object* v___x_486_; uint8_t v___x_487_; 
v_vs_484_ = lean_ctor_get(v_x_471_, 0);
v___x_485_ = lean_unsigned_to_nat(0u);
v___x_486_ = lean_array_get_size(v_vs_484_);
v___x_487_ = lean_nat_dec_lt(v___x_485_, v___x_486_);
if (v___x_487_ == 0)
{
return v_x_472_;
}
else
{
uint8_t v___x_488_; 
v___x_488_ = lean_nat_dec_le(v___x_486_, v___x_486_);
if (v___x_488_ == 0)
{
if (v___x_487_ == 0)
{
return v_x_472_;
}
else
{
size_t v___x_489_; size_t v___x_490_; lean_object* v___x_491_; 
v___x_489_ = ((size_t)0ULL);
v___x_490_ = lean_usize_of_nat(v___x_486_);
v___x_491_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_470_, v_vs_484_, v___x_489_, v___x_490_, v_x_472_);
return v___x_491_;
}
}
else
{
size_t v___x_492_; size_t v___x_493_; lean_object* v___x_494_; 
v___x_492_ = ((size_t)0ULL);
v___x_493_ = lean_usize_of_nat(v___x_486_);
v___x_494_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_470_, v_vs_484_, v___x_492_, v___x_493_, v_x_472_);
return v___x_494_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(lean_object* v___x_495_, lean_object* v_as_496_, size_t v_i_497_, size_t v_stop_498_, lean_object* v_b_499_){
_start:
{
uint8_t v___x_500_; 
v___x_500_ = lean_usize_dec_eq(v_i_497_, v_stop_498_);
if (v___x_500_ == 0)
{
lean_object* v___x_501_; lean_object* v___x_502_; size_t v___x_503_; size_t v___x_504_; 
v___x_501_ = lean_array_uget_borrowed(v_as_496_, v_i_497_);
v___x_502_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2(v___x_495_, v___x_501_, v_b_499_);
v___x_503_ = ((size_t)1ULL);
v___x_504_ = lean_usize_add(v_i_497_, v___x_503_);
v_i_497_ = v___x_504_;
v_b_499_ = v___x_502_;
goto _start;
}
else
{
return v_b_499_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1___boxed(lean_object* v___x_506_, lean_object* v_as_507_, lean_object* v_i_508_, lean_object* v_stop_509_, lean_object* v_b_510_){
_start:
{
size_t v_i_boxed_511_; size_t v_stop_boxed_512_; lean_object* v_res_513_; 
v_i_boxed_511_ = lean_unbox_usize(v_i_508_);
lean_dec(v_i_508_);
v_stop_boxed_512_ = lean_unbox_usize(v_stop_509_);
lean_dec(v_stop_509_);
v_res_513_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v___x_506_, v_as_507_, v_i_boxed_511_, v_stop_boxed_512_, v_b_510_);
lean_dec_ref(v_as_507_);
lean_dec_ref(v___x_506_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2___boxed(lean_object* v___x_514_, lean_object* v_x_515_, lean_object* v_x_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2(v___x_514_, v_x_515_, v_x_516_);
lean_dec_ref(v_x_515_);
lean_dec_ref(v___x_514_);
return v_res_517_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(lean_object* v___x_519_, lean_object* v_x_520_, size_t v_x_521_, size_t v_x_522_, lean_object* v_x_523_){
_start:
{
if (lean_obj_tag(v_x_520_) == 0)
{
lean_object* v_cs_524_; lean_object* v___x_525_; size_t v___x_526_; lean_object* v_j_527_; lean_object* v___x_528_; size_t v___x_529_; size_t v___x_530_; size_t v___x_531_; size_t v___x_532_; size_t v___x_533_; size_t v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; uint8_t v___x_539_; 
v_cs_524_ = lean_ctor_get(v_x_520_, 0);
v___x_525_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0);
v___x_526_ = lean_usize_shift_right(v_x_521_, v_x_522_);
v_j_527_ = lean_usize_to_nat(v___x_526_);
v___x_528_ = lean_array_get_borrowed(v___x_525_, v_cs_524_, v_j_527_);
v___x_529_ = ((size_t)1ULL);
v___x_530_ = lean_usize_shift_left(v___x_529_, v_x_522_);
v___x_531_ = lean_usize_sub(v___x_530_, v___x_529_);
v___x_532_ = lean_usize_land(v_x_521_, v___x_531_);
v___x_533_ = ((size_t)5ULL);
v___x_534_ = lean_usize_sub(v_x_522_, v___x_533_);
v___x_535_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(v___x_519_, v___x_528_, v___x_532_, v___x_534_, v_x_523_);
v___x_536_ = lean_unsigned_to_nat(1u);
v___x_537_ = lean_nat_add(v_j_527_, v___x_536_);
lean_dec(v_j_527_);
v___x_538_ = lean_array_get_size(v_cs_524_);
v___x_539_ = lean_nat_dec_lt(v___x_537_, v___x_538_);
if (v___x_539_ == 0)
{
lean_dec(v___x_537_);
return v___x_535_;
}
else
{
uint8_t v___x_540_; 
v___x_540_ = lean_nat_dec_le(v___x_538_, v___x_538_);
if (v___x_540_ == 0)
{
if (v___x_539_ == 0)
{
lean_dec(v___x_537_);
return v___x_535_;
}
else
{
size_t v___x_541_; size_t v___x_542_; lean_object* v___x_543_; 
v___x_541_ = lean_usize_of_nat(v___x_537_);
lean_dec(v___x_537_);
v___x_542_ = lean_usize_of_nat(v___x_538_);
v___x_543_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v___x_519_, v_cs_524_, v___x_541_, v___x_542_, v___x_535_);
return v___x_543_;
}
}
else
{
size_t v___x_544_; size_t v___x_545_; lean_object* v___x_546_; 
v___x_544_ = lean_usize_of_nat(v___x_537_);
lean_dec(v___x_537_);
v___x_545_ = lean_usize_of_nat(v___x_538_);
v___x_546_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v___x_519_, v_cs_524_, v___x_544_, v___x_545_, v___x_535_);
return v___x_546_;
}
}
}
else
{
lean_object* v_vs_547_; lean_object* v___x_548_; lean_object* v___x_549_; uint8_t v___x_550_; 
v_vs_547_ = lean_ctor_get(v_x_520_, 0);
v___x_548_ = lean_usize_to_nat(v_x_521_);
v___x_549_ = lean_array_get_size(v_vs_547_);
v___x_550_ = lean_nat_dec_lt(v___x_548_, v___x_549_);
if (v___x_550_ == 0)
{
lean_dec(v___x_548_);
return v_x_523_;
}
else
{
uint8_t v___x_551_; 
v___x_551_ = lean_nat_dec_le(v___x_549_, v___x_549_);
if (v___x_551_ == 0)
{
if (v___x_550_ == 0)
{
lean_dec(v___x_548_);
return v_x_523_;
}
else
{
size_t v___x_552_; size_t v___x_553_; lean_object* v___x_554_; 
v___x_552_ = lean_usize_of_nat(v___x_548_);
lean_dec(v___x_548_);
v___x_553_ = lean_usize_of_nat(v___x_549_);
v___x_554_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_519_, v_vs_547_, v___x_552_, v___x_553_, v_x_523_);
return v___x_554_;
}
}
else
{
size_t v___x_555_; size_t v___x_556_; lean_object* v___x_557_; 
v___x_555_ = lean_usize_of_nat(v___x_548_);
lean_dec(v___x_548_);
v___x_556_ = lean_usize_of_nat(v___x_549_);
v___x_557_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_519_, v_vs_547_, v___x_555_, v___x_556_, v_x_523_);
return v___x_557_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___boxed(lean_object* v___x_558_, lean_object* v_x_559_, lean_object* v_x_560_, lean_object* v_x_561_, lean_object* v_x_562_){
_start:
{
size_t v_x_2096__boxed_563_; size_t v_x_2097__boxed_564_; lean_object* v_res_565_; 
v_x_2096__boxed_563_ = lean_unbox_usize(v_x_560_);
lean_dec(v_x_560_);
v_x_2097__boxed_564_ = lean_unbox_usize(v_x_561_);
lean_dec(v_x_561_);
v_res_565_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(v___x_558_, v_x_559_, v_x_2096__boxed_563_, v_x_2097__boxed_564_, v_x_562_);
lean_dec_ref(v_x_559_);
lean_dec_ref(v___x_558_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(lean_object* v___x_566_, lean_object* v_t_567_, lean_object* v_init_568_, lean_object* v_start_569_){
_start:
{
lean_object* v___x_570_; uint8_t v___x_571_; 
v___x_570_ = lean_unsigned_to_nat(0u);
v___x_571_ = lean_nat_dec_eq(v_start_569_, v___x_570_);
if (v___x_571_ == 0)
{
lean_object* v_root_572_; lean_object* v_tail_573_; size_t v_shift_574_; lean_object* v_tailOff_575_; uint8_t v___x_576_; 
v_root_572_ = lean_ctor_get(v_t_567_, 0);
v_tail_573_ = lean_ctor_get(v_t_567_, 1);
v_shift_574_ = lean_ctor_get_usize(v_t_567_, 4);
v_tailOff_575_ = lean_ctor_get(v_t_567_, 3);
v___x_576_ = lean_nat_dec_le(v_tailOff_575_, v_start_569_);
if (v___x_576_ == 0)
{
size_t v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; uint8_t v___x_580_; 
v___x_577_ = lean_usize_of_nat(v_start_569_);
v___x_578_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(v___x_566_, v_root_572_, v___x_577_, v_shift_574_, v_init_568_);
v___x_579_ = lean_array_get_size(v_tail_573_);
v___x_580_ = lean_nat_dec_lt(v___x_570_, v___x_579_);
if (v___x_580_ == 0)
{
return v___x_578_;
}
else
{
uint8_t v___x_581_; 
v___x_581_ = lean_nat_dec_le(v___x_579_, v___x_579_);
if (v___x_581_ == 0)
{
if (v___x_580_ == 0)
{
return v___x_578_;
}
else
{
size_t v___x_582_; size_t v___x_583_; lean_object* v___x_584_; 
v___x_582_ = ((size_t)0ULL);
v___x_583_ = lean_usize_of_nat(v___x_579_);
v___x_584_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_566_, v_tail_573_, v___x_582_, v___x_583_, v___x_578_);
return v___x_584_;
}
}
else
{
size_t v___x_585_; size_t v___x_586_; lean_object* v___x_587_; 
v___x_585_ = ((size_t)0ULL);
v___x_586_ = lean_usize_of_nat(v___x_579_);
v___x_587_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_566_, v_tail_573_, v___x_585_, v___x_586_, v___x_578_);
return v___x_587_;
}
}
}
else
{
lean_object* v___x_588_; lean_object* v___x_589_; uint8_t v___x_590_; 
v___x_588_ = lean_nat_sub(v_start_569_, v_tailOff_575_);
v___x_589_ = lean_array_get_size(v_tail_573_);
v___x_590_ = lean_nat_dec_lt(v___x_588_, v___x_589_);
if (v___x_590_ == 0)
{
lean_dec(v___x_588_);
return v_init_568_;
}
else
{
uint8_t v___x_591_; 
v___x_591_ = lean_nat_dec_le(v___x_589_, v___x_589_);
if (v___x_591_ == 0)
{
if (v___x_590_ == 0)
{
lean_dec(v___x_588_);
return v_init_568_;
}
else
{
size_t v___x_592_; size_t v___x_593_; lean_object* v___x_594_; 
v___x_592_ = lean_usize_of_nat(v___x_588_);
lean_dec(v___x_588_);
v___x_593_ = lean_usize_of_nat(v___x_589_);
v___x_594_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_566_, v_tail_573_, v___x_592_, v___x_593_, v_init_568_);
return v___x_594_;
}
}
else
{
size_t v___x_595_; size_t v___x_596_; lean_object* v___x_597_; 
v___x_595_ = lean_usize_of_nat(v___x_588_);
lean_dec(v___x_588_);
v___x_596_ = lean_usize_of_nat(v___x_589_);
v___x_597_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_566_, v_tail_573_, v___x_595_, v___x_596_, v_init_568_);
return v___x_597_;
}
}
}
}
else
{
lean_object* v_root_598_; lean_object* v_tail_599_; lean_object* v___x_600_; lean_object* v___x_601_; uint8_t v___x_602_; 
v_root_598_ = lean_ctor_get(v_t_567_, 0);
v_tail_599_ = lean_ctor_get(v_t_567_, 1);
v___x_600_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2(v___x_566_, v_root_598_, v_init_568_);
v___x_601_ = lean_array_get_size(v_tail_599_);
v___x_602_ = lean_nat_dec_lt(v___x_570_, v___x_601_);
if (v___x_602_ == 0)
{
return v___x_600_;
}
else
{
uint8_t v___x_603_; 
v___x_603_ = lean_nat_dec_le(v___x_601_, v___x_601_);
if (v___x_603_ == 0)
{
if (v___x_602_ == 0)
{
return v___x_600_;
}
else
{
size_t v___x_604_; size_t v___x_605_; lean_object* v___x_606_; 
v___x_604_ = ((size_t)0ULL);
v___x_605_ = lean_usize_of_nat(v___x_601_);
v___x_606_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_566_, v_tail_599_, v___x_604_, v___x_605_, v___x_600_);
return v___x_606_;
}
}
else
{
size_t v___x_607_; size_t v___x_608_; lean_object* v___x_609_; 
v___x_607_ = ((size_t)0ULL);
v___x_608_ = lean_usize_of_nat(v___x_601_);
v___x_609_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_566_, v_tail_599_, v___x_607_, v___x_608_, v___x_600_);
return v___x_609_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0___boxed(lean_object* v___x_610_, lean_object* v_t_611_, lean_object* v_init_612_, lean_object* v_start_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(v___x_610_, v_t_611_, v_init_612_, v_start_613_);
lean_dec(v_start_613_);
lean_dec_ref(v_t_611_);
lean_dec_ref(v___x_610_);
return v_res_614_;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_615_ = lean_unsigned_to_nat(32u);
v___x_616_ = lean_mk_empty_array_with_capacity(v___x_615_);
v___x_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_617_, 0, v___x_616_);
return v___x_617_;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v___x_618_ = ((size_t)5ULL);
v___x_619_ = lean_unsigned_to_nat(0u);
v___x_620_ = lean_unsigned_to_nat(32u);
v___x_621_ = lean_mk_empty_array_with_capacity(v___x_620_);
v___x_622_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___redArg___closed__0, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___redArg___closed__0);
v___x_623_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_623_, 0, v___x_622_);
lean_ctor_set(v___x_623_, 1, v___x_621_);
lean_ctor_set(v___x_623_, 2, v___x_619_);
lean_ctor_set(v___x_623_, 3, v___x_619_);
lean_ctor_set_usize(v___x_623_, 4, v___x_618_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___redArg(lean_object* v___x_624_, lean_object* v_x_625_, size_t v_x_626_, size_t v_x_627_){
_start:
{
if (lean_obj_tag(v_x_625_) == 0)
{
lean_object* v_cs_628_; size_t v_j_629_; lean_object* v___x_630_; lean_object* v___x_631_; uint8_t v___x_632_; 
v_cs_628_ = lean_ctor_get(v_x_625_, 0);
v_j_629_ = lean_usize_shift_right(v_x_626_, v_x_627_);
v___x_630_ = lean_usize_to_nat(v_j_629_);
v___x_631_ = lean_array_get_size(v_cs_628_);
v___x_632_ = lean_nat_dec_lt(v___x_630_, v___x_631_);
if (v___x_632_ == 0)
{
lean_dec(v___x_630_);
return v_x_625_;
}
else
{
lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_650_; 
lean_inc_ref(v_cs_628_);
v_isSharedCheck_650_ = !lean_is_exclusive(v_x_625_);
if (v_isSharedCheck_650_ == 0)
{
lean_object* v_unused_651_; 
v_unused_651_ = lean_ctor_get(v_x_625_, 0);
lean_dec(v_unused_651_);
v___x_634_ = v_x_625_;
v_isShared_635_ = v_isSharedCheck_650_;
goto v_resetjp_633_;
}
else
{
lean_dec(v_x_625_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_650_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
size_t v___x_636_; size_t v___x_637_; size_t v___x_638_; size_t v_i_639_; size_t v___x_640_; size_t v_shift_641_; lean_object* v_v_642_; lean_object* v___x_643_; lean_object* v_xs_x27_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_648_; 
v___x_636_ = ((size_t)1ULL);
v___x_637_ = lean_usize_shift_left(v___x_636_, v_x_627_);
v___x_638_ = lean_usize_sub(v___x_637_, v___x_636_);
v_i_639_ = lean_usize_land(v_x_626_, v___x_638_);
v___x_640_ = ((size_t)5ULL);
v_shift_641_ = lean_usize_sub(v_x_627_, v___x_640_);
v_v_642_ = lean_array_fget(v_cs_628_, v___x_630_);
v___x_643_ = lean_box(0);
v_xs_x27_644_ = lean_array_fset(v_cs_628_, v___x_630_, v___x_643_);
v___x_645_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___redArg(v___x_624_, v_v_642_, v_i_639_, v_shift_641_);
v___x_646_ = lean_array_fset(v_xs_x27_644_, v___x_630_, v___x_645_);
lean_dec(v___x_630_);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 0, v___x_646_);
v___x_648_ = v___x_634_;
goto v_reusejp_647_;
}
else
{
lean_object* v_reuseFailAlloc_649_; 
v_reuseFailAlloc_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_649_, 0, v___x_646_);
v___x_648_ = v_reuseFailAlloc_649_;
goto v_reusejp_647_;
}
v_reusejp_647_:
{
return v___x_648_;
}
}
}
}
else
{
lean_object* v_vs_652_; lean_object* v___x_653_; lean_object* v___x_654_; uint8_t v___x_655_; 
v_vs_652_ = lean_ctor_get(v_x_625_, 0);
v___x_653_ = lean_usize_to_nat(v_x_626_);
v___x_654_ = lean_array_get_size(v_vs_652_);
v___x_655_ = lean_nat_dec_lt(v___x_653_, v___x_654_);
if (v___x_655_ == 0)
{
lean_dec(v___x_653_);
return v_x_625_;
}
else
{
lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_669_; 
lean_inc_ref(v_vs_652_);
v_isSharedCheck_669_ = !lean_is_exclusive(v_x_625_);
if (v_isSharedCheck_669_ == 0)
{
lean_object* v_unused_670_; 
v_unused_670_ = lean_ctor_get(v_x_625_, 0);
lean_dec(v_unused_670_);
v___x_657_ = v_x_625_;
v_isShared_658_ = v_isSharedCheck_669_;
goto v_resetjp_656_;
}
else
{
lean_dec(v_x_625_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_669_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v_v_659_; lean_object* v___x_660_; lean_object* v_xs_x27_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_667_; 
v_v_659_ = lean_array_fget(v_vs_652_, v___x_653_);
v___x_660_ = lean_box(0);
v_xs_x27_661_ = lean_array_fset(v_vs_652_, v___x_653_, v___x_660_);
v___x_662_ = lean_unsigned_to_nat(0u);
v___x_663_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___redArg___closed__1, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___redArg___closed__1);
v___x_664_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(v___x_624_, v_v_659_, v___x_663_, v___x_662_);
lean_dec(v_v_659_);
v___x_665_ = lean_array_fset(v_xs_x27_661_, v___x_653_, v___x_664_);
lean_dec(v___x_653_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v___x_665_);
v___x_667_ = v___x_657_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_665_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___redArg___boxed(lean_object* v___x_671_, lean_object* v_x_672_, lean_object* v_x_673_, lean_object* v_x_674_){
_start:
{
size_t v_x_2269__boxed_675_; size_t v_x_2270__boxed_676_; lean_object* v_res_677_; 
v_x_2269__boxed_675_ = lean_unbox_usize(v_x_673_);
lean_dec(v_x_673_);
v_x_2270__boxed_676_ = lean_unbox_usize(v_x_674_);
lean_dec(v_x_674_);
v_res_677_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___redArg(v___x_671_, v_x_672_, v_x_2269__boxed_675_, v_x_2270__boxed_676_);
lean_dec_ref(v___x_671_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(lean_object* v___x_678_, lean_object* v_inst_679_, lean_object* v_t_680_, lean_object* v_i_681_){
_start:
{
lean_object* v_root_682_; lean_object* v_tail_683_; lean_object* v_size_684_; size_t v_shift_685_; lean_object* v_tailOff_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_714_; 
v_root_682_ = lean_ctor_get(v_t_680_, 0);
v_tail_683_ = lean_ctor_get(v_t_680_, 1);
v_size_684_ = lean_ctor_get(v_t_680_, 2);
v_shift_685_ = lean_ctor_get_usize(v_t_680_, 4);
v_tailOff_686_ = lean_ctor_get(v_t_680_, 3);
v_isSharedCheck_714_ = !lean_is_exclusive(v_t_680_);
if (v_isSharedCheck_714_ == 0)
{
v___x_688_ = v_t_680_;
v_isShared_689_ = v_isSharedCheck_714_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_tailOff_686_);
lean_inc(v_size_684_);
lean_inc(v_tail_683_);
lean_inc(v_root_682_);
lean_dec(v_t_680_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_714_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
uint8_t v___x_690_; 
v___x_690_ = lean_nat_dec_le(v_tailOff_686_, v_i_681_);
if (v___x_690_ == 0)
{
size_t v___x_691_; lean_object* v___x_692_; lean_object* v___x_694_; 
v___x_691_ = lean_usize_of_nat(v_i_681_);
v___x_692_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___redArg(v___x_678_, v_root_682_, v___x_691_, v_shift_685_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 0, v___x_692_);
v___x_694_ = v___x_688_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_692_);
lean_ctor_set(v_reuseFailAlloc_695_, 1, v_tail_683_);
lean_ctor_set(v_reuseFailAlloc_695_, 2, v_size_684_);
lean_ctor_set(v_reuseFailAlloc_695_, 3, v_tailOff_686_);
lean_ctor_set_usize(v_reuseFailAlloc_695_, 4, v_shift_685_);
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
lean_object* v___x_696_; lean_object* v___x_697_; uint8_t v___x_698_; 
v___x_696_ = lean_nat_sub(v_i_681_, v_tailOff_686_);
v___x_697_ = lean_array_get_size(v_tail_683_);
v___x_698_ = lean_nat_dec_lt(v___x_696_, v___x_697_);
if (v___x_698_ == 0)
{
lean_object* v___x_700_; 
lean_dec(v___x_696_);
if (v_isShared_689_ == 0)
{
v___x_700_ = v___x_688_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_root_682_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_tail_683_);
lean_ctor_set(v_reuseFailAlloc_701_, 2, v_size_684_);
lean_ctor_set(v_reuseFailAlloc_701_, 3, v_tailOff_686_);
lean_ctor_set_usize(v_reuseFailAlloc_701_, 4, v_shift_685_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
else
{
lean_object* v_v_702_; lean_object* v___x_703_; lean_object* v_xs_x27_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_712_; 
v_v_702_ = lean_array_fget(v_tail_683_, v___x_696_);
v___x_703_ = lean_box(0);
v_xs_x27_704_ = lean_array_fset(v_tail_683_, v___x_696_, v___x_703_);
v___x_705_ = lean_unsigned_to_nat(32u);
v___x_706_ = lean_mk_empty_array_with_capacity(v___x_705_);
lean_dec_ref(v___x_706_);
v___x_707_ = lean_unsigned_to_nat(0u);
v___x_708_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___redArg___closed__1, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___redArg___closed__1);
v___x_709_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(v___x_678_, v_v_702_, v___x_708_, v___x_707_);
lean_dec(v_v_702_);
v___x_710_ = lean_array_fset(v_xs_x27_704_, v___x_696_, v___x_709_);
lean_dec(v___x_696_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 1, v___x_710_);
v___x_712_ = v___x_688_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_root_682_);
lean_ctor_set(v_reuseFailAlloc_713_, 1, v___x_710_);
lean_ctor_set(v_reuseFailAlloc_713_, 2, v_size_684_);
lean_ctor_set(v_reuseFailAlloc_713_, 3, v_tailOff_686_);
lean_ctor_set_usize(v_reuseFailAlloc_713_, 4, v_shift_685_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1___boxed(lean_object* v___x_715_, lean_object* v_inst_716_, lean_object* v_t_717_, lean_object* v_i_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(v___x_715_, v_inst_716_, v_t_717_, v_i_718_);
lean_dec(v_i_718_);
lean_dec_ref(v_inst_716_);
lean_dec_ref(v___x_715_);
return v_res_719_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0(void){
_start:
{
lean_object* v___x_720_; 
v___x_720_ = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0(lean_object* v_p_721_, lean_object* v_v_722_, lean_object* v_s_723_){
_start:
{
lean_object* v_vars_724_; lean_object* v_varMap_725_; lean_object* v_vars_x27_726_; lean_object* v_varMap_x27_727_; lean_object* v_natToIntMap_728_; lean_object* v_natDef_729_; lean_object* v_dvds_730_; lean_object* v_lowers_731_; lean_object* v_uppers_732_; lean_object* v_diseqs_733_; lean_object* v_elimEqs_734_; lean_object* v_elimStack_735_; lean_object* v_occurs_736_; lean_object* v_assignment_737_; lean_object* v_nextCnstrId_738_; uint8_t v_caseSplits_739_; lean_object* v_conflict_x3f_740_; lean_object* v_diseqSplits_741_; lean_object* v_divMod_742_; lean_object* v_toIntIds_743_; lean_object* v_toIntInfos_744_; lean_object* v_toIntTermMap_745_; lean_object* v_toIntVarMap_746_; uint8_t v_usedCommRing_747_; lean_object* v_nonlinearOccs_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_757_; 
v_vars_724_ = lean_ctor_get(v_s_723_, 0);
v_varMap_725_ = lean_ctor_get(v_s_723_, 1);
v_vars_x27_726_ = lean_ctor_get(v_s_723_, 2);
v_varMap_x27_727_ = lean_ctor_get(v_s_723_, 3);
v_natToIntMap_728_ = lean_ctor_get(v_s_723_, 4);
v_natDef_729_ = lean_ctor_get(v_s_723_, 5);
v_dvds_730_ = lean_ctor_get(v_s_723_, 6);
v_lowers_731_ = lean_ctor_get(v_s_723_, 7);
v_uppers_732_ = lean_ctor_get(v_s_723_, 8);
v_diseqs_733_ = lean_ctor_get(v_s_723_, 9);
v_elimEqs_734_ = lean_ctor_get(v_s_723_, 10);
v_elimStack_735_ = lean_ctor_get(v_s_723_, 11);
v_occurs_736_ = lean_ctor_get(v_s_723_, 12);
v_assignment_737_ = lean_ctor_get(v_s_723_, 13);
v_nextCnstrId_738_ = lean_ctor_get(v_s_723_, 14);
v_caseSplits_739_ = lean_ctor_get_uint8(v_s_723_, sizeof(void*)*23);
v_conflict_x3f_740_ = lean_ctor_get(v_s_723_, 15);
v_diseqSplits_741_ = lean_ctor_get(v_s_723_, 16);
v_divMod_742_ = lean_ctor_get(v_s_723_, 17);
v_toIntIds_743_ = lean_ctor_get(v_s_723_, 18);
v_toIntInfos_744_ = lean_ctor_get(v_s_723_, 19);
v_toIntTermMap_745_ = lean_ctor_get(v_s_723_, 20);
v_toIntVarMap_746_ = lean_ctor_get(v_s_723_, 21);
v_usedCommRing_747_ = lean_ctor_get_uint8(v_s_723_, sizeof(void*)*23 + 1);
v_nonlinearOccs_748_ = lean_ctor_get(v_s_723_, 22);
v_isSharedCheck_757_ = !lean_is_exclusive(v_s_723_);
if (v_isSharedCheck_757_ == 0)
{
v___x_750_ = v_s_723_;
v_isShared_751_ = v_isSharedCheck_757_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_nonlinearOccs_748_);
lean_inc(v_toIntVarMap_746_);
lean_inc(v_toIntTermMap_745_);
lean_inc(v_toIntInfos_744_);
lean_inc(v_toIntIds_743_);
lean_inc(v_divMod_742_);
lean_inc(v_diseqSplits_741_);
lean_inc(v_conflict_x3f_740_);
lean_inc(v_nextCnstrId_738_);
lean_inc(v_assignment_737_);
lean_inc(v_occurs_736_);
lean_inc(v_elimStack_735_);
lean_inc(v_elimEqs_734_);
lean_inc(v_diseqs_733_);
lean_inc(v_uppers_732_);
lean_inc(v_lowers_731_);
lean_inc(v_dvds_730_);
lean_inc(v_natDef_729_);
lean_inc(v_natToIntMap_728_);
lean_inc(v_varMap_x27_727_);
lean_inc(v_vars_x27_726_);
lean_inc(v_varMap_725_);
lean_inc(v_vars_724_);
lean_dec(v_s_723_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_757_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_755_; 
v___x_752_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0);
v___x_753_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(v_p_721_, v___x_752_, v_uppers_732_, v_v_722_);
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 8, v___x_753_);
v___x_755_ = v___x_750_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_vars_724_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v_varMap_725_);
lean_ctor_set(v_reuseFailAlloc_756_, 2, v_vars_x27_726_);
lean_ctor_set(v_reuseFailAlloc_756_, 3, v_varMap_x27_727_);
lean_ctor_set(v_reuseFailAlloc_756_, 4, v_natToIntMap_728_);
lean_ctor_set(v_reuseFailAlloc_756_, 5, v_natDef_729_);
lean_ctor_set(v_reuseFailAlloc_756_, 6, v_dvds_730_);
lean_ctor_set(v_reuseFailAlloc_756_, 7, v_lowers_731_);
lean_ctor_set(v_reuseFailAlloc_756_, 8, v___x_753_);
lean_ctor_set(v_reuseFailAlloc_756_, 9, v_diseqs_733_);
lean_ctor_set(v_reuseFailAlloc_756_, 10, v_elimEqs_734_);
lean_ctor_set(v_reuseFailAlloc_756_, 11, v_elimStack_735_);
lean_ctor_set(v_reuseFailAlloc_756_, 12, v_occurs_736_);
lean_ctor_set(v_reuseFailAlloc_756_, 13, v_assignment_737_);
lean_ctor_set(v_reuseFailAlloc_756_, 14, v_nextCnstrId_738_);
lean_ctor_set(v_reuseFailAlloc_756_, 15, v_conflict_x3f_740_);
lean_ctor_set(v_reuseFailAlloc_756_, 16, v_diseqSplits_741_);
lean_ctor_set(v_reuseFailAlloc_756_, 17, v_divMod_742_);
lean_ctor_set(v_reuseFailAlloc_756_, 18, v_toIntIds_743_);
lean_ctor_set(v_reuseFailAlloc_756_, 19, v_toIntInfos_744_);
lean_ctor_set(v_reuseFailAlloc_756_, 20, v_toIntTermMap_745_);
lean_ctor_set(v_reuseFailAlloc_756_, 21, v_toIntVarMap_746_);
lean_ctor_set(v_reuseFailAlloc_756_, 22, v_nonlinearOccs_748_);
lean_ctor_set_uint8(v_reuseFailAlloc_756_, sizeof(void*)*23, v_caseSplits_739_);
lean_ctor_set_uint8(v_reuseFailAlloc_756_, sizeof(void*)*23 + 1, v_usedCommRing_747_);
v___x_755_ = v_reuseFailAlloc_756_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
return v___x_755_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___boxed(lean_object* v_p_758_, lean_object* v_v_759_, lean_object* v_s_760_){
_start:
{
lean_object* v_res_761_; 
v_res_761_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0(v_p_758_, v_v_759_, v_s_760_);
lean_dec(v_v_759_);
lean_dec_ref(v_p_758_);
return v_res_761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1(lean_object* v_p_762_, lean_object* v_v_763_, lean_object* v_s_764_){
_start:
{
lean_object* v_vars_765_; lean_object* v_varMap_766_; lean_object* v_vars_x27_767_; lean_object* v_varMap_x27_768_; lean_object* v_natToIntMap_769_; lean_object* v_natDef_770_; lean_object* v_dvds_771_; lean_object* v_lowers_772_; lean_object* v_uppers_773_; lean_object* v_diseqs_774_; lean_object* v_elimEqs_775_; lean_object* v_elimStack_776_; lean_object* v_occurs_777_; lean_object* v_assignment_778_; lean_object* v_nextCnstrId_779_; uint8_t v_caseSplits_780_; lean_object* v_conflict_x3f_781_; lean_object* v_diseqSplits_782_; lean_object* v_divMod_783_; lean_object* v_toIntIds_784_; lean_object* v_toIntInfos_785_; lean_object* v_toIntTermMap_786_; lean_object* v_toIntVarMap_787_; uint8_t v_usedCommRing_788_; lean_object* v_nonlinearOccs_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_798_; 
v_vars_765_ = lean_ctor_get(v_s_764_, 0);
v_varMap_766_ = lean_ctor_get(v_s_764_, 1);
v_vars_x27_767_ = lean_ctor_get(v_s_764_, 2);
v_varMap_x27_768_ = lean_ctor_get(v_s_764_, 3);
v_natToIntMap_769_ = lean_ctor_get(v_s_764_, 4);
v_natDef_770_ = lean_ctor_get(v_s_764_, 5);
v_dvds_771_ = lean_ctor_get(v_s_764_, 6);
v_lowers_772_ = lean_ctor_get(v_s_764_, 7);
v_uppers_773_ = lean_ctor_get(v_s_764_, 8);
v_diseqs_774_ = lean_ctor_get(v_s_764_, 9);
v_elimEqs_775_ = lean_ctor_get(v_s_764_, 10);
v_elimStack_776_ = lean_ctor_get(v_s_764_, 11);
v_occurs_777_ = lean_ctor_get(v_s_764_, 12);
v_assignment_778_ = lean_ctor_get(v_s_764_, 13);
v_nextCnstrId_779_ = lean_ctor_get(v_s_764_, 14);
v_caseSplits_780_ = lean_ctor_get_uint8(v_s_764_, sizeof(void*)*23);
v_conflict_x3f_781_ = lean_ctor_get(v_s_764_, 15);
v_diseqSplits_782_ = lean_ctor_get(v_s_764_, 16);
v_divMod_783_ = lean_ctor_get(v_s_764_, 17);
v_toIntIds_784_ = lean_ctor_get(v_s_764_, 18);
v_toIntInfos_785_ = lean_ctor_get(v_s_764_, 19);
v_toIntTermMap_786_ = lean_ctor_get(v_s_764_, 20);
v_toIntVarMap_787_ = lean_ctor_get(v_s_764_, 21);
v_usedCommRing_788_ = lean_ctor_get_uint8(v_s_764_, sizeof(void*)*23 + 1);
v_nonlinearOccs_789_ = lean_ctor_get(v_s_764_, 22);
v_isSharedCheck_798_ = !lean_is_exclusive(v_s_764_);
if (v_isSharedCheck_798_ == 0)
{
v___x_791_ = v_s_764_;
v_isShared_792_ = v_isSharedCheck_798_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_nonlinearOccs_789_);
lean_inc(v_toIntVarMap_787_);
lean_inc(v_toIntTermMap_786_);
lean_inc(v_toIntInfos_785_);
lean_inc(v_toIntIds_784_);
lean_inc(v_divMod_783_);
lean_inc(v_diseqSplits_782_);
lean_inc(v_conflict_x3f_781_);
lean_inc(v_nextCnstrId_779_);
lean_inc(v_assignment_778_);
lean_inc(v_occurs_777_);
lean_inc(v_elimStack_776_);
lean_inc(v_elimEqs_775_);
lean_inc(v_diseqs_774_);
lean_inc(v_uppers_773_);
lean_inc(v_lowers_772_);
lean_inc(v_dvds_771_);
lean_inc(v_natDef_770_);
lean_inc(v_natToIntMap_769_);
lean_inc(v_varMap_x27_768_);
lean_inc(v_vars_x27_767_);
lean_inc(v_varMap_766_);
lean_inc(v_vars_765_);
lean_dec(v_s_764_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_798_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_796_; 
v___x_793_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0);
v___x_794_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(v_p_762_, v___x_793_, v_lowers_772_, v_v_763_);
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 7, v___x_794_);
v___x_796_ = v___x_791_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_vars_765_);
lean_ctor_set(v_reuseFailAlloc_797_, 1, v_varMap_766_);
lean_ctor_set(v_reuseFailAlloc_797_, 2, v_vars_x27_767_);
lean_ctor_set(v_reuseFailAlloc_797_, 3, v_varMap_x27_768_);
lean_ctor_set(v_reuseFailAlloc_797_, 4, v_natToIntMap_769_);
lean_ctor_set(v_reuseFailAlloc_797_, 5, v_natDef_770_);
lean_ctor_set(v_reuseFailAlloc_797_, 6, v_dvds_771_);
lean_ctor_set(v_reuseFailAlloc_797_, 7, v___x_794_);
lean_ctor_set(v_reuseFailAlloc_797_, 8, v_uppers_773_);
lean_ctor_set(v_reuseFailAlloc_797_, 9, v_diseqs_774_);
lean_ctor_set(v_reuseFailAlloc_797_, 10, v_elimEqs_775_);
lean_ctor_set(v_reuseFailAlloc_797_, 11, v_elimStack_776_);
lean_ctor_set(v_reuseFailAlloc_797_, 12, v_occurs_777_);
lean_ctor_set(v_reuseFailAlloc_797_, 13, v_assignment_778_);
lean_ctor_set(v_reuseFailAlloc_797_, 14, v_nextCnstrId_779_);
lean_ctor_set(v_reuseFailAlloc_797_, 15, v_conflict_x3f_781_);
lean_ctor_set(v_reuseFailAlloc_797_, 16, v_diseqSplits_782_);
lean_ctor_set(v_reuseFailAlloc_797_, 17, v_divMod_783_);
lean_ctor_set(v_reuseFailAlloc_797_, 18, v_toIntIds_784_);
lean_ctor_set(v_reuseFailAlloc_797_, 19, v_toIntInfos_785_);
lean_ctor_set(v_reuseFailAlloc_797_, 20, v_toIntTermMap_786_);
lean_ctor_set(v_reuseFailAlloc_797_, 21, v_toIntVarMap_787_);
lean_ctor_set(v_reuseFailAlloc_797_, 22, v_nonlinearOccs_789_);
lean_ctor_set_uint8(v_reuseFailAlloc_797_, sizeof(void*)*23, v_caseSplits_780_);
lean_ctor_set_uint8(v_reuseFailAlloc_797_, sizeof(void*)*23 + 1, v_usedCommRing_788_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1___boxed(lean_object* v_p_799_, lean_object* v_v_800_, lean_object* v_s_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1(v_p_799_, v_v_800_, v_s_801_);
lean_dec(v_v_800_);
lean_dec_ref(v_p_799_);
return v_res_802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(lean_object* v_c_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_){
_start:
{
lean_object* v_p_810_; 
v_p_810_ = lean_ctor_get(v_c_803_, 0);
if (lean_obj_tag(v_p_810_) == 1)
{
lean_object* v_k_811_; lean_object* v_v_812_; lean_object* v___x_813_; uint8_t v___x_814_; 
lean_inc_ref(v_p_810_);
lean_dec_ref(v_c_803_);
v_k_811_ = lean_ctor_get(v_p_810_, 0);
v_v_812_ = lean_ctor_get(v_p_810_, 1);
lean_inc(v_v_812_);
v___x_813_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6);
v___x_814_ = lean_int_dec_lt(v_k_811_, v___x_813_);
if (v___x_814_ == 0)
{
lean_object* v___f_815_; lean_object* v___x_816_; lean_object* v___x_817_; 
v___f_815_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_815_, 0, v_p_810_);
lean_closure_set(v___f_815_, 1, v_v_812_);
v___x_816_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_817_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_816_, v___f_815_, v_a_804_);
return v___x_817_;
}
else
{
lean_object* v___f_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___f_818_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_818_, 0, v_p_810_);
lean_closure_set(v___f_818_, 1, v_v_812_);
v___x_819_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_820_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_819_, v___f_818_, v_a_804_);
return v___x_820_;
}
}
else
{
lean_object* v___x_821_; 
v___x_821_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_);
return v___x_821_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___boxed(lean_object* v_c_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_c_822_, v_a_823_, v_a_824_, v_a_825_, v_a_826_, v_a_827_);
lean_dec(v_a_827_);
lean_dec_ref(v_a_826_);
lean_dec(v_a_825_);
lean_dec_ref(v_a_824_);
lean_dec(v_a_823_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase(lean_object* v_c_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_c_830_, v_a_831_, v_a_837_, v_a_838_, v_a_839_, v_a_840_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___boxed(lean_object* v_c_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase(v_c_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_);
lean_dec(v_a_853_);
lean_dec_ref(v_a_852_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4(lean_object* v___x_856_, lean_object* v_inst_857_, lean_object* v_x_858_, size_t v_x_859_, size_t v_x_860_){
_start:
{
lean_object* v___x_861_; 
v___x_861_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___redArg(v___x_856_, v_x_858_, v_x_859_, v_x_860_);
return v___x_861_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___boxed(lean_object* v___x_862_, lean_object* v_inst_863_, lean_object* v_x_864_, lean_object* v_x_865_, lean_object* v_x_866_){
_start:
{
size_t v_x_2558__boxed_867_; size_t v_x_2559__boxed_868_; lean_object* v_res_869_; 
v_x_2558__boxed_867_ = lean_unbox_usize(v_x_865_);
lean_dec(v_x_865_);
v_x_2559__boxed_868_ = lean_unbox_usize(v_x_866_);
lean_dec(v_x_866_);
v_res_869_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4(v___x_862_, v_inst_863_, v_x_864_, v_x_2558__boxed_867_, v_x_2559__boxed_868_);
lean_dec_ref(v_inst_863_);
lean_dec_ref(v___x_862_);
return v_res_869_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__6(void){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_884_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5));
v___x_885_ = l_Lean_stringToMessageData(v___x_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3(lean_object* v___x_886_, lean_object* v_c_887_, lean_object* v_as_888_, size_t v_sz_889_, size_t v_i_890_, lean_object* v_b_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
uint8_t v___x_903_; 
v___x_903_ = lean_usize_dec_lt(v_i_890_, v_sz_889_);
if (v___x_903_ == 0)
{
lean_object* v___x_904_; 
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec(v___y_893_);
lean_dec(v___y_892_);
lean_dec_ref(v_c_887_);
lean_dec_ref(v___x_886_);
v___x_904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_904_, 0, v_b_891_);
return v___x_904_;
}
else
{
lean_object* v_snd_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_997_; 
v_snd_905_ = lean_ctor_get(v_b_891_, 1);
v_isSharedCheck_997_ = !lean_is_exclusive(v_b_891_);
if (v_isSharedCheck_997_ == 0)
{
lean_object* v_unused_998_; 
v_unused_998_ = lean_ctor_get(v_b_891_, 0);
lean_dec(v_unused_998_);
v___x_907_ = v_b_891_;
v_isShared_908_ = v_isSharedCheck_997_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_snd_905_);
lean_dec(v_b_891_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_997_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v_a_909_; lean_object* v_p_910_; lean_object* v___x_911_; uint8_t v___x_912_; 
v_a_909_ = lean_array_uget_borrowed(v_as_888_, v_i_890_);
v_p_910_ = lean_ctor_get(v_a_909_, 0);
v___x_911_ = lean_box(0);
v___x_912_ = l_Int_Linear_Poly_isNegEq(v___x_886_, v_p_910_);
if (v___x_912_ == 0)
{
lean_object* v___x_913_; size_t v___x_914_; size_t v___x_915_; 
lean_del_object(v___x_907_);
lean_dec(v_snd_905_);
v___x_913_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__1));
v___x_914_ = ((size_t)1ULL);
v___x_915_ = lean_usize_add(v_i_890_, v___x_914_);
v_i_890_ = v___x_915_;
v_b_891_ = v___x_913_;
goto _start;
}
else
{
lean_object* v___x_917_; 
lean_inc(v_a_909_);
v___x_917_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_909_, v___y_892_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_object* v___x_918_; lean_object* v___x_919_; 
lean_dec_ref(v___x_917_);
v___x_918_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_919_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_918_, v___y_900_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_object* v_a_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___y_924_; lean_object* v___y_925_; lean_object* v___y_926_; lean_object* v___y_927_; lean_object* v___y_928_; lean_object* v___y_929_; lean_object* v___y_930_; lean_object* v___y_931_; lean_object* v___y_932_; lean_object* v___y_933_; uint8_t v___x_959_; 
v_a_920_ = lean_ctor_get(v___x_919_, 0);
lean_inc(v_a_920_);
lean_dec_ref(v___x_919_);
lean_inc(v_a_909_);
v___x_921_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_921_, 0, v_c_887_);
lean_ctor_set(v___x_921_, 1, v_a_909_);
v___x_922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_886_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
v___x_959_ = lean_unbox(v_a_920_);
lean_dec(v_a_920_);
if (v___x_959_ == 0)
{
v___y_924_ = v___y_892_;
v___y_925_ = v___y_893_;
v___y_926_ = v___y_894_;
v___y_927_ = v___y_895_;
v___y_928_ = v___y_896_;
v___y_929_ = v___y_897_;
v___y_930_ = v___y_898_;
v___y_931_ = v___y_899_;
v___y_932_ = v___y_900_;
v___y_933_ = v___y_901_;
goto v___jp_923_;
}
else
{
lean_object* v___x_960_; 
lean_inc_ref(v___x_922_);
v___x_960_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_922_, v___y_892_, v___y_900_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_a_961_);
lean_dec_ref(v___x_960_);
v___x_962_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__6);
v___x_963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_963_, 0, v___x_962_);
lean_ctor_set(v___x_963_, 1, v_a_961_);
v___x_964_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1___redArg(v___x_918_, v___x_963_, v___y_898_, v___y_899_, v___y_900_, v___y_901_);
if (lean_obj_tag(v___x_964_) == 0)
{
lean_dec_ref(v___x_964_);
v___y_924_ = v___y_892_;
v___y_925_ = v___y_893_;
v___y_926_ = v___y_894_;
v___y_927_ = v___y_895_;
v___y_928_ = v___y_896_;
v___y_929_ = v___y_897_;
v___y_930_ = v___y_898_;
v___y_931_ = v___y_899_;
v___y_932_ = v___y_900_;
v___y_933_ = v___y_901_;
goto v___jp_923_;
}
else
{
lean_object* v_a_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_972_; 
lean_dec_ref(v___x_922_);
lean_del_object(v___x_907_);
lean_dec(v_snd_905_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec(v___y_893_);
lean_dec(v___y_892_);
v_a_965_ = lean_ctor_get(v___x_964_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_964_);
if (v_isSharedCheck_972_ == 0)
{
v___x_967_ = v___x_964_;
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_a_965_);
lean_dec(v___x_964_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_970_; 
if (v_isShared_968_ == 0)
{
v___x_970_ = v___x_967_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_a_965_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
}
else
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
lean_dec_ref(v___x_922_);
lean_del_object(v___x_907_);
lean_dec(v_snd_905_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec(v___y_893_);
lean_dec(v___y_892_);
v_a_973_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_980_ == 0)
{
v___x_975_ = v___x_960_;
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_960_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_a_973_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
v___jp_923_:
{
lean_object* v___x_934_; 
v___x_934_ = lean_grind_cutsat_assert_eq(v___x_922_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
if (lean_obj_tag(v___x_934_) == 0)
{
lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_949_; 
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_949_ == 0)
{
lean_object* v_unused_950_; 
v_unused_950_ = lean_ctor_get(v___x_934_, 0);
lean_dec(v_unused_950_);
v___x_936_ = v___x_934_;
v_isShared_937_ = v_isSharedCheck_949_;
goto v_resetjp_935_;
}
else
{
lean_dec(v___x_934_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_949_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_941_; 
v___x_938_ = lean_box(v___x_912_);
v___x_939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_939_, 0, v___x_938_);
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 1, v___x_911_);
lean_ctor_set(v___x_907_, 0, v___x_939_);
v___x_941_ = v___x_907_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_948_; 
v_reuseFailAlloc_948_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_948_, 0, v___x_939_);
lean_ctor_set(v_reuseFailAlloc_948_, 1, v___x_911_);
v___x_941_ = v_reuseFailAlloc_948_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_946_; 
v___x_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_942_, 0, v___x_941_);
v___x_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_943_, 0, v___x_942_);
v___x_944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_943_);
lean_ctor_set(v___x_944_, 1, v_snd_905_);
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 0, v___x_944_);
v___x_946_ = v___x_936_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_944_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
else
{
lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_958_; 
lean_del_object(v___x_907_);
lean_dec(v_snd_905_);
v_a_951_ = lean_ctor_get(v___x_934_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_958_ == 0)
{
v___x_953_ = v___x_934_;
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_a_951_);
lean_dec(v___x_934_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_956_; 
if (v_isShared_954_ == 0)
{
v___x_956_ = v___x_953_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_a_951_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
}
}
else
{
lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_988_; 
lean_del_object(v___x_907_);
lean_dec(v_snd_905_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec(v___y_893_);
lean_dec(v___y_892_);
lean_dec_ref(v_c_887_);
lean_dec_ref(v___x_886_);
v_a_981_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_988_ == 0)
{
v___x_983_ = v___x_919_;
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v___x_919_);
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
else
{
lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_996_; 
lean_del_object(v___x_907_);
lean_dec(v_snd_905_);
lean_dec(v___y_901_);
lean_dec_ref(v___y_900_);
lean_dec(v___y_899_);
lean_dec_ref(v___y_898_);
lean_dec(v___y_897_);
lean_dec_ref(v___y_896_);
lean_dec(v___y_895_);
lean_dec_ref(v___y_894_);
lean_dec(v___y_893_);
lean_dec(v___y_892_);
lean_dec_ref(v_c_887_);
lean_dec_ref(v___x_886_);
v_a_989_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_996_ == 0)
{
v___x_991_ = v___x_917_;
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_917_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_994_; 
if (v_isShared_992_ == 0)
{
v___x_994_ = v___x_991_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_a_989_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___boxed(lean_object** _args){
lean_object* v___x_999_ = _args[0];
lean_object* v_c_1000_ = _args[1];
lean_object* v_as_1001_ = _args[2];
lean_object* v_sz_1002_ = _args[3];
lean_object* v_i_1003_ = _args[4];
lean_object* v_b_1004_ = _args[5];
lean_object* v___y_1005_ = _args[6];
lean_object* v___y_1006_ = _args[7];
lean_object* v___y_1007_ = _args[8];
lean_object* v___y_1008_ = _args[9];
lean_object* v___y_1009_ = _args[10];
lean_object* v___y_1010_ = _args[11];
lean_object* v___y_1011_ = _args[12];
lean_object* v___y_1012_ = _args[13];
lean_object* v___y_1013_ = _args[14];
lean_object* v___y_1014_ = _args[15];
lean_object* v___y_1015_ = _args[16];
_start:
{
size_t v_sz_boxed_1016_; size_t v_i_boxed_1017_; lean_object* v_res_1018_; 
v_sz_boxed_1016_ = lean_unbox_usize(v_sz_1002_);
lean_dec(v_sz_1002_);
v_i_boxed_1017_ = lean_unbox_usize(v_i_1003_);
lean_dec(v_i_1003_);
v_res_1018_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3(v___x_999_, v_c_1000_, v_as_1001_, v_sz_boxed_1016_, v_i_boxed_1017_, v_b_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_);
lean_dec_ref(v_as_1001_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2(lean_object* v___x_1025_, lean_object* v_c_1026_, lean_object* v_as_1027_, size_t v_sz_1028_, size_t v_i_1029_, lean_object* v_b_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
uint8_t v___x_1042_; 
v___x_1042_ = lean_usize_dec_lt(v_i_1029_, v_sz_1028_);
if (v___x_1042_ == 0)
{
lean_object* v___x_1043_; 
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec(v___y_1031_);
lean_dec_ref(v_c_1026_);
lean_dec_ref(v___x_1025_);
v___x_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1043_, 0, v_b_1030_);
return v___x_1043_;
}
else
{
lean_object* v_snd_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1136_; 
v_snd_1044_ = lean_ctor_get(v_b_1030_, 1);
v_isSharedCheck_1136_ = !lean_is_exclusive(v_b_1030_);
if (v_isSharedCheck_1136_ == 0)
{
lean_object* v_unused_1137_; 
v_unused_1137_ = lean_ctor_get(v_b_1030_, 0);
lean_dec(v_unused_1137_);
v___x_1046_ = v_b_1030_;
v_isShared_1047_ = v_isSharedCheck_1136_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_snd_1044_);
lean_dec(v_b_1030_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1136_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v_a_1048_; lean_object* v_p_1049_; lean_object* v___x_1050_; uint8_t v___x_1051_; 
v_a_1048_ = lean_array_uget_borrowed(v_as_1027_, v_i_1029_);
v_p_1049_ = lean_ctor_get(v_a_1048_, 0);
v___x_1050_ = lean_box(0);
v___x_1051_ = l_Int_Linear_Poly_isNegEq(v___x_1025_, v_p_1049_);
if (v___x_1051_ == 0)
{
lean_object* v___x_1052_; size_t v___x_1053_; size_t v___x_1054_; lean_object* v___x_1055_; 
lean_del_object(v___x_1046_);
lean_dec(v_snd_1044_);
v___x_1052_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__1));
v___x_1053_ = ((size_t)1ULL);
v___x_1054_ = lean_usize_add(v_i_1029_, v___x_1053_);
v___x_1055_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3(v___x_1025_, v_c_1026_, v_as_1027_, v_sz_1028_, v___x_1054_, v___x_1052_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
return v___x_1055_;
}
else
{
lean_object* v___x_1056_; 
lean_inc(v_a_1048_);
v___x_1056_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_1048_, v___y_1031_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
lean_dec_ref(v___x_1056_);
v___x_1057_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_1058_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_1057_, v___y_1039_);
if (lean_obj_tag(v___x_1058_) == 0)
{
lean_object* v_a_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___y_1063_; lean_object* v___y_1064_; lean_object* v___y_1065_; lean_object* v___y_1066_; lean_object* v___y_1067_; lean_object* v___y_1068_; lean_object* v___y_1069_; lean_object* v___y_1070_; lean_object* v___y_1071_; lean_object* v___y_1072_; uint8_t v___x_1098_; 
v_a_1059_ = lean_ctor_get(v___x_1058_, 0);
lean_inc(v_a_1059_);
lean_dec_ref(v___x_1058_);
lean_inc(v_a_1048_);
v___x_1060_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1060_, 0, v_c_1026_);
lean_ctor_set(v___x_1060_, 1, v_a_1048_);
v___x_1061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1025_);
lean_ctor_set(v___x_1061_, 1, v___x_1060_);
v___x_1098_ = lean_unbox(v_a_1059_);
lean_dec(v_a_1059_);
if (v___x_1098_ == 0)
{
v___y_1063_ = v___y_1031_;
v___y_1064_ = v___y_1032_;
v___y_1065_ = v___y_1033_;
v___y_1066_ = v___y_1034_;
v___y_1067_ = v___y_1035_;
v___y_1068_ = v___y_1036_;
v___y_1069_ = v___y_1037_;
v___y_1070_ = v___y_1038_;
v___y_1071_ = v___y_1039_;
v___y_1072_ = v___y_1040_;
goto v___jp_1062_;
}
else
{
lean_object* v___x_1099_; 
lean_inc_ref(v___x_1061_);
v___x_1099_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_1061_, v___y_1031_, v___y_1039_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v_a_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v_a_1100_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_a_1100_);
lean_dec_ref(v___x_1099_);
v___x_1101_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__6);
v___x_1102_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
lean_ctor_set(v___x_1102_, 1, v_a_1100_);
v___x_1103_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1___redArg(v___x_1057_, v___x_1102_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_);
if (lean_obj_tag(v___x_1103_) == 0)
{
lean_dec_ref(v___x_1103_);
v___y_1063_ = v___y_1031_;
v___y_1064_ = v___y_1032_;
v___y_1065_ = v___y_1033_;
v___y_1066_ = v___y_1034_;
v___y_1067_ = v___y_1035_;
v___y_1068_ = v___y_1036_;
v___y_1069_ = v___y_1037_;
v___y_1070_ = v___y_1038_;
v___y_1071_ = v___y_1039_;
v___y_1072_ = v___y_1040_;
goto v___jp_1062_;
}
else
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
lean_dec_ref(v___x_1061_);
lean_del_object(v___x_1046_);
lean_dec(v_snd_1044_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec(v___y_1031_);
v_a_1104_ = lean_ctor_get(v___x_1103_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1103_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___x_1103_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1103_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1109_; 
if (v_isShared_1107_ == 0)
{
v___x_1109_ = v___x_1106_;
goto v_reusejp_1108_;
}
else
{
lean_object* v_reuseFailAlloc_1110_; 
v_reuseFailAlloc_1110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1110_, 0, v_a_1104_);
v___x_1109_ = v_reuseFailAlloc_1110_;
goto v_reusejp_1108_;
}
v_reusejp_1108_:
{
return v___x_1109_;
}
}
}
}
else
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1119_; 
lean_dec_ref(v___x_1061_);
lean_del_object(v___x_1046_);
lean_dec(v_snd_1044_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec(v___y_1031_);
v_a_1112_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1114_ = v___x_1099_;
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1099_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1117_; 
if (v_isShared_1115_ == 0)
{
v___x_1117_ = v___x_1114_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_a_1112_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
}
v___jp_1062_:
{
lean_object* v___x_1073_; 
v___x_1073_ = lean_grind_cutsat_assert_eq(v___x_1061_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1088_; 
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1088_ == 0)
{
lean_object* v_unused_1089_; 
v_unused_1089_ = lean_ctor_get(v___x_1073_, 0);
lean_dec(v_unused_1089_);
v___x_1075_ = v___x_1073_;
v_isShared_1076_ = v_isSharedCheck_1088_;
goto v_resetjp_1074_;
}
else
{
lean_dec(v___x_1073_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1088_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1080_; 
v___x_1077_ = lean_box(v___x_1051_);
v___x_1078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
if (v_isShared_1047_ == 0)
{
lean_ctor_set(v___x_1046_, 1, v___x_1050_);
lean_ctor_set(v___x_1046_, 0, v___x_1078_);
v___x_1080_ = v___x_1046_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___x_1078_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v___x_1050_);
v___x_1080_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1085_; 
v___x_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
v___x_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
v___x_1083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1082_);
lean_ctor_set(v___x_1083_, 1, v_snd_1044_);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 0, v___x_1083_);
v___x_1085_ = v___x_1075_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1083_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
else
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1097_; 
lean_del_object(v___x_1046_);
lean_dec(v_snd_1044_);
v_a_1090_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1092_ = v___x_1073_;
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1073_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1097_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1095_; 
if (v_isShared_1093_ == 0)
{
v___x_1095_ = v___x_1092_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_a_1090_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
}
}
else
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
lean_del_object(v___x_1046_);
lean_dec(v_snd_1044_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec(v___y_1031_);
lean_dec_ref(v_c_1026_);
lean_dec_ref(v___x_1025_);
v_a_1120_ = lean_ctor_get(v___x_1058_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1058_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1058_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1058_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
return v___x_1125_;
}
}
}
}
else
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
lean_del_object(v___x_1046_);
lean_dec(v_snd_1044_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec(v___y_1031_);
lean_dec_ref(v_c_1026_);
lean_dec_ref(v___x_1025_);
v_a_1128_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1056_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1056_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1128_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___boxed(lean_object** _args){
lean_object* v___x_1138_ = _args[0];
lean_object* v_c_1139_ = _args[1];
lean_object* v_as_1140_ = _args[2];
lean_object* v_sz_1141_ = _args[3];
lean_object* v_i_1142_ = _args[4];
lean_object* v_b_1143_ = _args[5];
lean_object* v___y_1144_ = _args[6];
lean_object* v___y_1145_ = _args[7];
lean_object* v___y_1146_ = _args[8];
lean_object* v___y_1147_ = _args[9];
lean_object* v___y_1148_ = _args[10];
lean_object* v___y_1149_ = _args[11];
lean_object* v___y_1150_ = _args[12];
lean_object* v___y_1151_ = _args[13];
lean_object* v___y_1152_ = _args[14];
lean_object* v___y_1153_ = _args[15];
lean_object* v___y_1154_ = _args[16];
_start:
{
size_t v_sz_boxed_1155_; size_t v_i_boxed_1156_; lean_object* v_res_1157_; 
v_sz_boxed_1155_ = lean_unbox_usize(v_sz_1141_);
lean_dec(v_sz_1141_);
v_i_boxed_1156_ = lean_unbox_usize(v_i_1142_);
lean_dec(v_i_1142_);
v_res_1157_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2(v___x_1138_, v_c_1139_, v_as_1140_, v_sz_boxed_1155_, v_i_boxed_1156_, v_b_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
lean_dec_ref(v_as_1140_);
return v_res_1157_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(lean_object* v___x_1158_, lean_object* v_c_1159_, lean_object* v_inh_1160_, lean_object* v_n_1161_, lean_object* v_b_1162_, lean_object* v___y_1163_, lean_object* v___y_1164_, lean_object* v___y_1165_, lean_object* v___y_1166_, lean_object* v___y_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
if (lean_obj_tag(v_n_1161_) == 0)
{
lean_object* v_cs_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1208_; 
v_cs_1174_ = lean_ctor_get(v_n_1161_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v_n_1161_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1176_ = v_n_1161_;
v_isShared_1177_ = v_isSharedCheck_1208_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_cs_1174_);
lean_dec(v_n_1161_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1208_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; size_t v_sz_1180_; size_t v___x_1181_; lean_object* v___x_1182_; 
v___x_1178_ = lean_box(0);
v___x_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1178_);
lean_ctor_set(v___x_1179_, 1, v_b_1162_);
v_sz_1180_ = lean_array_size(v_cs_1174_);
v___x_1181_ = ((size_t)0ULL);
v___x_1182_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(v___x_1158_, v_c_1159_, v_inh_1160_, v_cs_1174_, v_sz_1180_, v___x_1181_, v___x_1179_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
lean_dec_ref(v_cs_1174_);
if (lean_obj_tag(v___x_1182_) == 0)
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1199_; 
v_a_1183_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1185_ = v___x_1182_;
v_isShared_1186_ = v_isSharedCheck_1199_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1182_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1199_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v_fst_1187_; 
v_fst_1187_ = lean_ctor_get(v_a_1183_, 0);
if (lean_obj_tag(v_fst_1187_) == 0)
{
lean_object* v_snd_1188_; lean_object* v___x_1190_; 
v_snd_1188_ = lean_ctor_get(v_a_1183_, 1);
lean_inc(v_snd_1188_);
lean_dec(v_a_1183_);
if (v_isShared_1177_ == 0)
{
lean_ctor_set_tag(v___x_1176_, 1);
lean_ctor_set(v___x_1176_, 0, v_snd_1188_);
v___x_1190_ = v___x_1176_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_snd_1188_);
v___x_1190_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
lean_object* v___x_1192_; 
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 0, v___x_1190_);
v___x_1192_ = v___x_1185_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v___x_1190_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
else
{
lean_object* v_val_1195_; lean_object* v___x_1197_; 
lean_inc_ref(v_fst_1187_);
lean_dec(v_a_1183_);
lean_del_object(v___x_1176_);
v_val_1195_ = lean_ctor_get(v_fst_1187_, 0);
lean_inc(v_val_1195_);
lean_dec_ref(v_fst_1187_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 0, v_val_1195_);
v___x_1197_ = v___x_1185_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_val_1195_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
}
else
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
lean_del_object(v___x_1176_);
v_a_1200_ = lean_ctor_get(v___x_1182_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1182_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1202_ = v___x_1182_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1182_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1205_; 
if (v_isShared_1203_ == 0)
{
v___x_1205_ = v___x_1202_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1200_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
}
else
{
lean_object* v_vs_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1243_; 
v_vs_1209_ = lean_ctor_get(v_n_1161_, 0);
v_isSharedCheck_1243_ = !lean_is_exclusive(v_n_1161_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1211_ = v_n_1161_;
v_isShared_1212_ = v_isSharedCheck_1243_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_vs_1209_);
lean_dec(v_n_1161_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1243_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; size_t v_sz_1215_; size_t v___x_1216_; lean_object* v___x_1217_; 
v___x_1213_ = lean_box(0);
v___x_1214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1214_, 0, v___x_1213_);
lean_ctor_set(v___x_1214_, 1, v_b_1162_);
v_sz_1215_ = lean_array_size(v_vs_1209_);
v___x_1216_ = ((size_t)0ULL);
v___x_1217_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2(v___x_1158_, v_c_1159_, v_vs_1209_, v_sz_1215_, v___x_1216_, v___x_1214_, v___y_1163_, v___y_1164_, v___y_1165_, v___y_1166_, v___y_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
lean_dec_ref(v_vs_1209_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1234_; 
v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
v_isSharedCheck_1234_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1234_ == 0)
{
v___x_1220_ = v___x_1217_;
v_isShared_1221_ = v_isSharedCheck_1234_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1217_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1234_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v_fst_1222_; 
v_fst_1222_ = lean_ctor_get(v_a_1218_, 0);
if (lean_obj_tag(v_fst_1222_) == 0)
{
lean_object* v_snd_1223_; lean_object* v___x_1225_; 
v_snd_1223_ = lean_ctor_get(v_a_1218_, 1);
lean_inc(v_snd_1223_);
lean_dec(v_a_1218_);
if (v_isShared_1212_ == 0)
{
lean_ctor_set(v___x_1211_, 0, v_snd_1223_);
v___x_1225_ = v___x_1211_;
goto v_reusejp_1224_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_snd_1223_);
v___x_1225_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1224_;
}
v_reusejp_1224_:
{
lean_object* v___x_1227_; 
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 0, v___x_1225_);
v___x_1227_ = v___x_1220_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v___x_1225_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
else
{
lean_object* v_val_1230_; lean_object* v___x_1232_; 
lean_inc_ref(v_fst_1222_);
lean_dec(v_a_1218_);
lean_del_object(v___x_1211_);
v_val_1230_ = lean_ctor_get(v_fst_1222_, 0);
lean_inc(v_val_1230_);
lean_dec_ref(v_fst_1222_);
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 0, v_val_1230_);
v___x_1232_ = v___x_1220_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1233_; 
v_reuseFailAlloc_1233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1233_, 0, v_val_1230_);
v___x_1232_ = v_reuseFailAlloc_1233_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
return v___x_1232_;
}
}
}
}
else
{
lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1242_; 
lean_del_object(v___x_1211_);
v_a_1235_ = lean_ctor_get(v___x_1217_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1237_ = v___x_1217_;
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_dec(v___x_1217_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1240_; 
if (v_isShared_1238_ == 0)
{
v___x_1240_ = v___x_1237_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_a_1235_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(lean_object* v___x_1244_, lean_object* v_c_1245_, lean_object* v_inh_1246_, lean_object* v_as_1247_, size_t v_sz_1248_, size_t v_i_1249_, lean_object* v_b_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_){
_start:
{
uint8_t v___x_1262_; 
v___x_1262_ = lean_usize_dec_lt(v_i_1249_, v_sz_1248_);
if (v___x_1262_ == 0)
{
lean_object* v___x_1263_; 
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v_c_1245_);
lean_dec_ref(v___x_1244_);
v___x_1263_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1263_, 0, v_b_1250_);
return v___x_1263_;
}
else
{
lean_object* v_snd_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1298_; 
v_snd_1264_ = lean_ctor_get(v_b_1250_, 1);
v_isSharedCheck_1298_ = !lean_is_exclusive(v_b_1250_);
if (v_isSharedCheck_1298_ == 0)
{
lean_object* v_unused_1299_; 
v_unused_1299_ = lean_ctor_get(v_b_1250_, 0);
lean_dec(v_unused_1299_);
v___x_1266_ = v_b_1250_;
v_isShared_1267_ = v_isSharedCheck_1298_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_snd_1264_);
lean_dec(v_b_1250_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1298_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v_a_1268_; lean_object* v___x_1269_; 
v_a_1268_ = lean_array_uget_borrowed(v_as_1247_, v_i_1249_);
lean_inc(v___y_1260_);
lean_inc_ref(v___y_1259_);
lean_inc(v___y_1258_);
lean_inc_ref(v___y_1257_);
lean_inc(v___y_1256_);
lean_inc_ref(v___y_1255_);
lean_inc(v___y_1254_);
lean_inc_ref(v___y_1253_);
lean_inc(v___y_1252_);
lean_inc(v___y_1251_);
lean_inc(v_snd_1264_);
lean_inc(v_a_1268_);
lean_inc_ref(v_c_1245_);
lean_inc_ref(v___x_1244_);
v___x_1269_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(v___x_1244_, v_c_1245_, v_inh_1246_, v_a_1268_, v_snd_1264_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
if (lean_obj_tag(v___x_1269_) == 0)
{
lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1289_; 
v_a_1270_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1272_ = v___x_1269_;
v_isShared_1273_ = v_isSharedCheck_1289_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_dec(v___x_1269_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1289_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
if (lean_obj_tag(v_a_1270_) == 0)
{
lean_object* v___x_1274_; lean_object* v___x_1276_; 
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v_c_1245_);
lean_dec_ref(v___x_1244_);
v___x_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1274_, 0, v_a_1270_);
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 0, v___x_1274_);
v___x_1276_ = v___x_1266_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v___x_1274_);
lean_ctor_set(v_reuseFailAlloc_1280_, 1, v_snd_1264_);
v___x_1276_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
lean_object* v___x_1278_; 
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 0, v___x_1276_);
v___x_1278_ = v___x_1272_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v___x_1276_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1282_; lean_object* v___x_1284_; 
lean_del_object(v___x_1272_);
lean_dec(v_snd_1264_);
v_a_1281_ = lean_ctor_get(v_a_1270_, 0);
lean_inc(v_a_1281_);
lean_dec_ref(v_a_1270_);
v___x_1282_ = lean_box(0);
if (v_isShared_1267_ == 0)
{
lean_ctor_set(v___x_1266_, 1, v_a_1281_);
lean_ctor_set(v___x_1266_, 0, v___x_1282_);
v___x_1284_ = v___x_1266_;
goto v_reusejp_1283_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v___x_1282_);
lean_ctor_set(v_reuseFailAlloc_1288_, 1, v_a_1281_);
v___x_1284_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1283_;
}
v_reusejp_1283_:
{
size_t v___x_1285_; size_t v___x_1286_; 
v___x_1285_ = ((size_t)1ULL);
v___x_1286_ = lean_usize_add(v_i_1249_, v___x_1285_);
v_i_1249_ = v___x_1286_;
v_b_1250_ = v___x_1284_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
lean_del_object(v___x_1266_);
lean_dec(v_snd_1264_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v_c_1245_);
lean_dec_ref(v___x_1244_);
v_a_1290_ = lean_ctor_get(v___x_1269_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1269_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1269_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1269_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1290_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v___x_1300_ = _args[0];
lean_object* v_c_1301_ = _args[1];
lean_object* v_inh_1302_ = _args[2];
lean_object* v_as_1303_ = _args[3];
lean_object* v_sz_1304_ = _args[4];
lean_object* v_i_1305_ = _args[5];
lean_object* v_b_1306_ = _args[6];
lean_object* v___y_1307_ = _args[7];
lean_object* v___y_1308_ = _args[8];
lean_object* v___y_1309_ = _args[9];
lean_object* v___y_1310_ = _args[10];
lean_object* v___y_1311_ = _args[11];
lean_object* v___y_1312_ = _args[12];
lean_object* v___y_1313_ = _args[13];
lean_object* v___y_1314_ = _args[14];
lean_object* v___y_1315_ = _args[15];
lean_object* v___y_1316_ = _args[16];
lean_object* v___y_1317_ = _args[17];
_start:
{
size_t v_sz_boxed_1318_; size_t v_i_boxed_1319_; lean_object* v_res_1320_; 
v_sz_boxed_1318_ = lean_unbox_usize(v_sz_1304_);
lean_dec(v_sz_1304_);
v_i_boxed_1319_ = lean_unbox_usize(v_i_1305_);
lean_dec(v_i_1305_);
v_res_1320_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(v___x_1300_, v_c_1301_, v_inh_1302_, v_as_1303_, v_sz_boxed_1318_, v_i_boxed_1319_, v_b_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
lean_dec_ref(v_as_1303_);
lean_dec_ref(v_inh_1302_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___boxed(lean_object* v___x_1321_, lean_object* v_c_1322_, lean_object* v_inh_1323_, lean_object* v_n_1324_, lean_object* v_b_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(v___x_1321_, v_c_1322_, v_inh_1323_, v_n_1324_, v_b_1325_, v___y_1326_, v___y_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
lean_dec_ref(v_inh_1323_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4(lean_object* v___x_1344_, lean_object* v_c_1345_, lean_object* v_as_1346_, size_t v_sz_1347_, size_t v_i_1348_, lean_object* v_b_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
uint8_t v___x_1361_; 
v___x_1361_ = lean_usize_dec_lt(v_i_1348_, v_sz_1347_);
if (v___x_1361_ == 0)
{
lean_object* v___x_1362_; 
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
lean_dec(v___y_1351_);
lean_dec(v___y_1350_);
lean_dec_ref(v_c_1345_);
lean_dec_ref(v___x_1344_);
v___x_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1362_, 0, v_b_1349_);
return v___x_1362_;
}
else
{
lean_object* v_snd_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1454_; 
v_snd_1363_ = lean_ctor_get(v_b_1349_, 1);
v_isSharedCheck_1454_ = !lean_is_exclusive(v_b_1349_);
if (v_isSharedCheck_1454_ == 0)
{
lean_object* v_unused_1455_; 
v_unused_1455_ = lean_ctor_get(v_b_1349_, 0);
lean_dec(v_unused_1455_);
v___x_1365_ = v_b_1349_;
v_isShared_1366_ = v_isSharedCheck_1454_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_snd_1363_);
lean_dec(v_b_1349_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1454_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v_a_1367_; lean_object* v_p_1368_; lean_object* v___x_1369_; uint8_t v___x_1370_; 
v_a_1367_ = lean_array_uget_borrowed(v_as_1346_, v_i_1348_);
v_p_1368_ = lean_ctor_get(v_a_1367_, 0);
v___x_1369_ = lean_box(0);
v___x_1370_ = l_Int_Linear_Poly_isNegEq(v___x_1344_, v_p_1368_);
if (v___x_1370_ == 0)
{
lean_object* v___x_1371_; size_t v___x_1372_; size_t v___x_1373_; 
lean_del_object(v___x_1365_);
lean_dec(v_snd_1363_);
v___x_1371_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___closed__1));
v___x_1372_ = ((size_t)1ULL);
v___x_1373_ = lean_usize_add(v_i_1348_, v___x_1372_);
v_i_1348_ = v___x_1373_;
v_b_1349_ = v___x_1371_;
goto _start;
}
else
{
lean_object* v___x_1375_; 
lean_inc(v_a_1367_);
v___x_1375_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_1367_, v___y_1350_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
lean_dec_ref(v___x_1375_);
v___x_1376_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_1377_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_1376_, v___y_1358_);
if (lean_obj_tag(v___x_1377_) == 0)
{
lean_object* v_a_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; uint8_t v___x_1416_; 
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc(v_a_1378_);
lean_dec_ref(v___x_1377_);
lean_inc(v_a_1367_);
v___x_1379_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1379_, 0, v_c_1345_);
lean_ctor_set(v___x_1379_, 1, v_a_1367_);
v___x_1380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1380_, 0, v___x_1344_);
lean_ctor_set(v___x_1380_, 1, v___x_1379_);
v___x_1416_ = lean_unbox(v_a_1378_);
lean_dec(v_a_1378_);
if (v___x_1416_ == 0)
{
v___y_1382_ = v___y_1350_;
v___y_1383_ = v___y_1351_;
v___y_1384_ = v___y_1352_;
v___y_1385_ = v___y_1353_;
v___y_1386_ = v___y_1354_;
v___y_1387_ = v___y_1355_;
v___y_1388_ = v___y_1356_;
v___y_1389_ = v___y_1357_;
v___y_1390_ = v___y_1358_;
v___y_1391_ = v___y_1359_;
goto v___jp_1381_;
}
else
{
lean_object* v___x_1417_; 
lean_inc_ref(v___x_1380_);
v___x_1417_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_1380_, v___y_1350_, v___y_1358_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_object* v_a_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v_a_1418_ = lean_ctor_get(v___x_1417_, 0);
lean_inc(v_a_1418_);
lean_dec_ref(v___x_1417_);
v___x_1419_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__6);
v___x_1420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1419_);
lean_ctor_set(v___x_1420_, 1, v_a_1418_);
v___x_1421_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1___redArg(v___x_1376_, v___x_1420_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_dec_ref(v___x_1421_);
v___y_1382_ = v___y_1350_;
v___y_1383_ = v___y_1351_;
v___y_1384_ = v___y_1352_;
v___y_1385_ = v___y_1353_;
v___y_1386_ = v___y_1354_;
v___y_1387_ = v___y_1355_;
v___y_1388_ = v___y_1356_;
v___y_1389_ = v___y_1357_;
v___y_1390_ = v___y_1358_;
v___y_1391_ = v___y_1359_;
goto v___jp_1381_;
}
else
{
lean_object* v_a_1422_; lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1429_; 
lean_dec_ref(v___x_1380_);
lean_del_object(v___x_1365_);
lean_dec(v_snd_1363_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
lean_dec(v___y_1351_);
lean_dec(v___y_1350_);
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1429_ == 0)
{
v___x_1424_ = v___x_1421_;
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
else
{
lean_inc(v_a_1422_);
lean_dec(v___x_1421_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1427_; 
if (v_isShared_1425_ == 0)
{
v___x_1427_ = v___x_1424_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_a_1422_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
}
else
{
lean_object* v_a_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1437_; 
lean_dec_ref(v___x_1380_);
lean_del_object(v___x_1365_);
lean_dec(v_snd_1363_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
lean_dec(v___y_1351_);
lean_dec(v___y_1350_);
v_a_1430_ = lean_ctor_get(v___x_1417_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1432_ = v___x_1417_;
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_a_1430_);
lean_dec(v___x_1417_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1437_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v___x_1435_; 
if (v_isShared_1433_ == 0)
{
v___x_1435_ = v___x_1432_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_a_1430_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
v___jp_1381_:
{
lean_object* v___x_1392_; 
v___x_1392_ = lean_grind_cutsat_assert_eq(v___x_1380_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v___x_1394_; uint8_t v_isShared_1395_; uint8_t v_isSharedCheck_1406_; 
v_isSharedCheck_1406_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1406_ == 0)
{
lean_object* v_unused_1407_; 
v_unused_1407_ = lean_ctor_get(v___x_1392_, 0);
lean_dec(v_unused_1407_);
v___x_1394_ = v___x_1392_;
v_isShared_1395_ = v_isSharedCheck_1406_;
goto v_resetjp_1393_;
}
else
{
lean_dec(v___x_1392_);
v___x_1394_ = lean_box(0);
v_isShared_1395_ = v_isSharedCheck_1406_;
goto v_resetjp_1393_;
}
v_resetjp_1393_:
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1399_; 
v___x_1396_ = lean_box(v___x_1370_);
v___x_1397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1396_);
if (v_isShared_1366_ == 0)
{
lean_ctor_set(v___x_1365_, 1, v___x_1369_);
lean_ctor_set(v___x_1365_, 0, v___x_1397_);
v___x_1399_ = v___x_1365_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___x_1397_);
lean_ctor_set(v_reuseFailAlloc_1405_, 1, v___x_1369_);
v___x_1399_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1403_; 
v___x_1400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1399_);
v___x_1401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1401_, 0, v___x_1400_);
lean_ctor_set(v___x_1401_, 1, v_snd_1363_);
if (v_isShared_1395_ == 0)
{
lean_ctor_set(v___x_1394_, 0, v___x_1401_);
v___x_1403_ = v___x_1394_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v___x_1401_);
v___x_1403_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
return v___x_1403_;
}
}
}
}
else
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1415_; 
lean_del_object(v___x_1365_);
lean_dec(v_snd_1363_);
v_a_1408_ = lean_ctor_get(v___x_1392_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1392_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1410_ = v___x_1392_;
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1392_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1411_ == 0)
{
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_a_1408_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
}
else
{
lean_object* v_a_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1445_; 
lean_del_object(v___x_1365_);
lean_dec(v_snd_1363_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
lean_dec(v___y_1351_);
lean_dec(v___y_1350_);
lean_dec_ref(v_c_1345_);
lean_dec_ref(v___x_1344_);
v_a_1438_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1445_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1440_ = v___x_1377_;
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_a_1438_);
lean_dec(v___x_1377_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1445_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1443_; 
if (v_isShared_1441_ == 0)
{
v___x_1443_ = v___x_1440_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1444_; 
v_reuseFailAlloc_1444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1444_, 0, v_a_1438_);
v___x_1443_ = v_reuseFailAlloc_1444_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
return v___x_1443_;
}
}
}
}
else
{
lean_object* v_a_1446_; lean_object* v___x_1448_; uint8_t v_isShared_1449_; uint8_t v_isSharedCheck_1453_; 
lean_del_object(v___x_1365_);
lean_dec(v_snd_1363_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
lean_dec(v___y_1351_);
lean_dec(v___y_1350_);
lean_dec_ref(v_c_1345_);
lean_dec_ref(v___x_1344_);
v_a_1446_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1448_ = v___x_1375_;
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
else
{
lean_inc(v_a_1446_);
lean_dec(v___x_1375_);
v___x_1448_ = lean_box(0);
v_isShared_1449_ = v_isSharedCheck_1453_;
goto v_resetjp_1447_;
}
v_resetjp_1447_:
{
lean_object* v___x_1451_; 
if (v_isShared_1449_ == 0)
{
v___x_1451_ = v___x_1448_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v_a_1446_);
v___x_1451_ = v_reuseFailAlloc_1452_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
return v___x_1451_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v___x_1456_ = _args[0];
lean_object* v_c_1457_ = _args[1];
lean_object* v_as_1458_ = _args[2];
lean_object* v_sz_1459_ = _args[3];
lean_object* v_i_1460_ = _args[4];
lean_object* v_b_1461_ = _args[5];
lean_object* v___y_1462_ = _args[6];
lean_object* v___y_1463_ = _args[7];
lean_object* v___y_1464_ = _args[8];
lean_object* v___y_1465_ = _args[9];
lean_object* v___y_1466_ = _args[10];
lean_object* v___y_1467_ = _args[11];
lean_object* v___y_1468_ = _args[12];
lean_object* v___y_1469_ = _args[13];
lean_object* v___y_1470_ = _args[14];
lean_object* v___y_1471_ = _args[15];
lean_object* v___y_1472_ = _args[16];
_start:
{
size_t v_sz_boxed_1473_; size_t v_i_boxed_1474_; lean_object* v_res_1475_; 
v_sz_boxed_1473_ = lean_unbox_usize(v_sz_1459_);
lean_dec(v_sz_1459_);
v_i_boxed_1474_ = lean_unbox_usize(v_i_1460_);
lean_dec(v_i_1460_);
v_res_1475_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4(v___x_1456_, v_c_1457_, v_as_1458_, v_sz_boxed_1473_, v_i_boxed_1474_, v_b_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_);
lean_dec_ref(v_as_1458_);
return v_res_1475_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1(lean_object* v___x_1479_, lean_object* v_c_1480_, lean_object* v_as_1481_, size_t v_sz_1482_, size_t v_i_1483_, lean_object* v_b_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_){
_start:
{
uint8_t v___x_1496_; 
v___x_1496_ = lean_usize_dec_lt(v_i_1483_, v_sz_1482_);
if (v___x_1496_ == 0)
{
lean_object* v___x_1497_; 
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec(v___y_1486_);
lean_dec(v___y_1485_);
lean_dec_ref(v_c_1480_);
lean_dec_ref(v___x_1479_);
v___x_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1497_, 0, v_b_1484_);
return v___x_1497_;
}
else
{
lean_object* v_snd_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1589_; 
v_snd_1498_ = lean_ctor_get(v_b_1484_, 1);
v_isSharedCheck_1589_ = !lean_is_exclusive(v_b_1484_);
if (v_isSharedCheck_1589_ == 0)
{
lean_object* v_unused_1590_; 
v_unused_1590_ = lean_ctor_get(v_b_1484_, 0);
lean_dec(v_unused_1590_);
v___x_1500_ = v_b_1484_;
v_isShared_1501_ = v_isSharedCheck_1589_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_snd_1498_);
lean_dec(v_b_1484_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1589_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v_a_1502_; lean_object* v_p_1503_; lean_object* v___x_1504_; uint8_t v___x_1505_; 
v_a_1502_ = lean_array_uget_borrowed(v_as_1481_, v_i_1483_);
v_p_1503_ = lean_ctor_get(v_a_1502_, 0);
v___x_1504_ = lean_box(0);
v___x_1505_ = l_Int_Linear_Poly_isNegEq(v___x_1479_, v_p_1503_);
if (v___x_1505_ == 0)
{
lean_object* v___x_1506_; size_t v___x_1507_; size_t v___x_1508_; lean_object* v___x_1509_; 
lean_del_object(v___x_1500_);
lean_dec(v_snd_1498_);
v___x_1506_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1___closed__0));
v___x_1507_ = ((size_t)1ULL);
v___x_1508_ = lean_usize_add(v_i_1483_, v___x_1507_);
v___x_1509_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4(v___x_1479_, v_c_1480_, v_as_1481_, v_sz_1482_, v___x_1508_, v___x_1506_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_);
return v___x_1509_;
}
else
{
lean_object* v___x_1510_; 
lean_inc(v_a_1502_);
v___x_1510_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_1502_, v___y_1485_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_);
if (lean_obj_tag(v___x_1510_) == 0)
{
lean_object* v___x_1511_; lean_object* v___x_1512_; 
lean_dec_ref(v___x_1510_);
v___x_1511_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_1512_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_1511_, v___y_1493_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_object* v_a_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___y_1517_; lean_object* v___y_1518_; lean_object* v___y_1519_; lean_object* v___y_1520_; lean_object* v___y_1521_; lean_object* v___y_1522_; lean_object* v___y_1523_; lean_object* v___y_1524_; lean_object* v___y_1525_; lean_object* v___y_1526_; uint8_t v___x_1551_; 
v_a_1513_ = lean_ctor_get(v___x_1512_, 0);
lean_inc(v_a_1513_);
lean_dec_ref(v___x_1512_);
lean_inc(v_a_1502_);
v___x_1514_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1514_, 0, v_c_1480_);
lean_ctor_set(v___x_1514_, 1, v_a_1502_);
v___x_1515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1479_);
lean_ctor_set(v___x_1515_, 1, v___x_1514_);
v___x_1551_ = lean_unbox(v_a_1513_);
lean_dec(v_a_1513_);
if (v___x_1551_ == 0)
{
v___y_1517_ = v___y_1485_;
v___y_1518_ = v___y_1486_;
v___y_1519_ = v___y_1487_;
v___y_1520_ = v___y_1488_;
v___y_1521_ = v___y_1489_;
v___y_1522_ = v___y_1490_;
v___y_1523_ = v___y_1491_;
v___y_1524_ = v___y_1492_;
v___y_1525_ = v___y_1493_;
v___y_1526_ = v___y_1494_;
goto v___jp_1516_;
}
else
{
lean_object* v___x_1552_; 
lean_inc_ref(v___x_1515_);
v___x_1552_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_1515_, v___y_1485_, v___y_1493_);
if (lean_obj_tag(v___x_1552_) == 0)
{
lean_object* v_a_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v_a_1553_ = lean_ctor_get(v___x_1552_, 0);
lean_inc(v_a_1553_);
lean_dec_ref(v___x_1552_);
v___x_1554_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__6);
v___x_1555_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1554_);
lean_ctor_set(v___x_1555_, 1, v_a_1553_);
v___x_1556_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1___redArg(v___x_1511_, v___x_1555_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_);
if (lean_obj_tag(v___x_1556_) == 0)
{
lean_dec_ref(v___x_1556_);
v___y_1517_ = v___y_1485_;
v___y_1518_ = v___y_1486_;
v___y_1519_ = v___y_1487_;
v___y_1520_ = v___y_1488_;
v___y_1521_ = v___y_1489_;
v___y_1522_ = v___y_1490_;
v___y_1523_ = v___y_1491_;
v___y_1524_ = v___y_1492_;
v___y_1525_ = v___y_1493_;
v___y_1526_ = v___y_1494_;
goto v___jp_1516_;
}
else
{
lean_object* v_a_1557_; lean_object* v___x_1559_; uint8_t v_isShared_1560_; uint8_t v_isSharedCheck_1564_; 
lean_dec_ref(v___x_1515_);
lean_del_object(v___x_1500_);
lean_dec(v_snd_1498_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec(v___y_1486_);
lean_dec(v___y_1485_);
v_a_1557_ = lean_ctor_get(v___x_1556_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1556_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1559_ = v___x_1556_;
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
else
{
lean_inc(v_a_1557_);
lean_dec(v___x_1556_);
v___x_1559_ = lean_box(0);
v_isShared_1560_ = v_isSharedCheck_1564_;
goto v_resetjp_1558_;
}
v_resetjp_1558_:
{
lean_object* v___x_1562_; 
if (v_isShared_1560_ == 0)
{
v___x_1562_ = v___x_1559_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_a_1557_);
v___x_1562_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1561_;
}
v_reusejp_1561_:
{
return v___x_1562_;
}
}
}
}
else
{
lean_object* v_a_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1572_; 
lean_dec_ref(v___x_1515_);
lean_del_object(v___x_1500_);
lean_dec(v_snd_1498_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec(v___y_1486_);
lean_dec(v___y_1485_);
v_a_1565_ = lean_ctor_get(v___x_1552_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1552_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1567_ = v___x_1552_;
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1552_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1570_; 
if (v_isShared_1568_ == 0)
{
v___x_1570_ = v___x_1567_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_a_1565_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
v___jp_1516_:
{
lean_object* v___x_1527_; 
v___x_1527_ = lean_grind_cutsat_assert_eq(v___x_1515_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
if (lean_obj_tag(v___x_1527_) == 0)
{
lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1541_; 
v_isSharedCheck_1541_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1541_ == 0)
{
lean_object* v_unused_1542_; 
v_unused_1542_ = lean_ctor_get(v___x_1527_, 0);
lean_dec(v_unused_1542_);
v___x_1529_ = v___x_1527_;
v_isShared_1530_ = v_isSharedCheck_1541_;
goto v_resetjp_1528_;
}
else
{
lean_dec(v___x_1527_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1541_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1534_; 
v___x_1531_ = lean_box(v___x_1505_);
v___x_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1531_);
if (v_isShared_1501_ == 0)
{
lean_ctor_set(v___x_1500_, 1, v___x_1504_);
lean_ctor_set(v___x_1500_, 0, v___x_1532_);
v___x_1534_ = v___x_1500_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v___x_1532_);
lean_ctor_set(v_reuseFailAlloc_1540_, 1, v___x_1504_);
v___x_1534_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1538_; 
v___x_1535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1534_);
v___x_1536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1535_);
lean_ctor_set(v___x_1536_, 1, v_snd_1498_);
if (v_isShared_1530_ == 0)
{
lean_ctor_set(v___x_1529_, 0, v___x_1536_);
v___x_1538_ = v___x_1529_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v___x_1536_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
}
else
{
lean_object* v_a_1543_; lean_object* v___x_1545_; uint8_t v_isShared_1546_; uint8_t v_isSharedCheck_1550_; 
lean_del_object(v___x_1500_);
lean_dec(v_snd_1498_);
v_a_1543_ = lean_ctor_get(v___x_1527_, 0);
v_isSharedCheck_1550_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1550_ == 0)
{
v___x_1545_ = v___x_1527_;
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
else
{
lean_inc(v_a_1543_);
lean_dec(v___x_1527_);
v___x_1545_ = lean_box(0);
v_isShared_1546_ = v_isSharedCheck_1550_;
goto v_resetjp_1544_;
}
v_resetjp_1544_:
{
lean_object* v___x_1548_; 
if (v_isShared_1546_ == 0)
{
v___x_1548_ = v___x_1545_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_a_1543_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
}
}
else
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1580_; 
lean_del_object(v___x_1500_);
lean_dec(v_snd_1498_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec(v___y_1486_);
lean_dec(v___y_1485_);
lean_dec_ref(v_c_1480_);
lean_dec_ref(v___x_1479_);
v_a_1573_ = lean_ctor_get(v___x_1512_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1512_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1575_ = v___x_1512_;
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1512_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v___x_1578_; 
if (v_isShared_1576_ == 0)
{
v___x_1578_ = v___x_1575_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_a_1573_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
else
{
lean_object* v_a_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1588_; 
lean_del_object(v___x_1500_);
lean_dec(v_snd_1498_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec(v___y_1486_);
lean_dec(v___y_1485_);
lean_dec_ref(v_c_1480_);
lean_dec_ref(v___x_1479_);
v_a_1581_ = lean_ctor_get(v___x_1510_, 0);
v_isSharedCheck_1588_ = !lean_is_exclusive(v___x_1510_);
if (v_isSharedCheck_1588_ == 0)
{
v___x_1583_ = v___x_1510_;
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_a_1581_);
lean_dec(v___x_1510_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1588_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1586_; 
if (v_isShared_1584_ == 0)
{
v___x_1586_ = v___x_1583_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_a_1581_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v___x_1591_ = _args[0];
lean_object* v_c_1592_ = _args[1];
lean_object* v_as_1593_ = _args[2];
lean_object* v_sz_1594_ = _args[3];
lean_object* v_i_1595_ = _args[4];
lean_object* v_b_1596_ = _args[5];
lean_object* v___y_1597_ = _args[6];
lean_object* v___y_1598_ = _args[7];
lean_object* v___y_1599_ = _args[8];
lean_object* v___y_1600_ = _args[9];
lean_object* v___y_1601_ = _args[10];
lean_object* v___y_1602_ = _args[11];
lean_object* v___y_1603_ = _args[12];
lean_object* v___y_1604_ = _args[13];
lean_object* v___y_1605_ = _args[14];
lean_object* v___y_1606_ = _args[15];
lean_object* v___y_1607_ = _args[16];
_start:
{
size_t v_sz_boxed_1608_; size_t v_i_boxed_1609_; lean_object* v_res_1610_; 
v_sz_boxed_1608_ = lean_unbox_usize(v_sz_1594_);
lean_dec(v_sz_1594_);
v_i_boxed_1609_ = lean_unbox_usize(v_i_1595_);
lean_dec(v_i_1595_);
v_res_1610_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1(v___x_1591_, v_c_1592_, v_as_1593_, v_sz_boxed_1608_, v_i_boxed_1609_, v_b_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
lean_dec_ref(v_as_1593_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0(lean_object* v___x_1611_, lean_object* v_c_1612_, lean_object* v_t_1613_, lean_object* v_init_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
lean_object* v_root_1626_; lean_object* v_tail_1627_; lean_object* v___x_1628_; 
v_root_1626_ = lean_ctor_get(v_t_1613_, 0);
lean_inc_ref(v_root_1626_);
v_tail_1627_ = lean_ctor_get(v_t_1613_, 1);
lean_inc_ref(v_tail_1627_);
lean_dec_ref(v_t_1613_);
lean_inc(v___y_1624_);
lean_inc_ref(v___y_1623_);
lean_inc(v___y_1622_);
lean_inc_ref(v___y_1621_);
lean_inc(v___y_1620_);
lean_inc_ref(v___y_1619_);
lean_inc(v___y_1618_);
lean_inc_ref(v___y_1617_);
lean_inc(v___y_1616_);
lean_inc(v___y_1615_);
lean_inc_ref(v_init_1614_);
lean_inc_ref(v_c_1612_);
lean_inc_ref(v___x_1611_);
v___x_1628_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(v___x_1611_, v_c_1612_, v_init_1614_, v_root_1626_, v_init_1614_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
lean_dec_ref(v_init_1614_);
if (lean_obj_tag(v___x_1628_) == 0)
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1665_; 
v_a_1629_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1665_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1631_ = v___x_1628_;
v_isShared_1632_ = v_isSharedCheck_1665_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1628_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1665_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
if (lean_obj_tag(v_a_1629_) == 0)
{
lean_object* v_a_1633_; lean_object* v___x_1635_; 
lean_dec_ref(v_tail_1627_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec_ref(v_c_1612_);
lean_dec_ref(v___x_1611_);
v_a_1633_ = lean_ctor_get(v_a_1629_, 0);
lean_inc(v_a_1633_);
lean_dec_ref(v_a_1629_);
if (v_isShared_1632_ == 0)
{
lean_ctor_set(v___x_1631_, 0, v_a_1633_);
v___x_1635_ = v___x_1631_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_a_1633_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
else
{
lean_object* v_a_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; size_t v_sz_1640_; size_t v___x_1641_; lean_object* v___x_1642_; 
lean_del_object(v___x_1631_);
v_a_1637_ = lean_ctor_get(v_a_1629_, 0);
lean_inc(v_a_1637_);
lean_dec_ref(v_a_1629_);
v___x_1638_ = lean_box(0);
v___x_1639_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1638_);
lean_ctor_set(v___x_1639_, 1, v_a_1637_);
v_sz_1640_ = lean_array_size(v_tail_1627_);
v___x_1641_ = ((size_t)0ULL);
v___x_1642_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1(v___x_1611_, v_c_1612_, v_tail_1627_, v_sz_1640_, v___x_1641_, v___x_1639_, v___y_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_, v___y_1624_);
lean_dec_ref(v_tail_1627_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1656_; 
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1656_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1656_ == 0)
{
v___x_1645_ = v___x_1642_;
v_isShared_1646_ = v_isSharedCheck_1656_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1642_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1656_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v_fst_1647_; 
v_fst_1647_ = lean_ctor_get(v_a_1643_, 0);
if (lean_obj_tag(v_fst_1647_) == 0)
{
lean_object* v_snd_1648_; lean_object* v___x_1650_; 
v_snd_1648_ = lean_ctor_get(v_a_1643_, 1);
lean_inc(v_snd_1648_);
lean_dec(v_a_1643_);
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 0, v_snd_1648_);
v___x_1650_ = v___x_1645_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_snd_1648_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
else
{
lean_object* v_val_1652_; lean_object* v___x_1654_; 
lean_inc_ref(v_fst_1647_);
lean_dec(v_a_1643_);
v_val_1652_ = lean_ctor_get(v_fst_1647_, 0);
lean_inc(v_val_1652_);
lean_dec_ref(v_fst_1647_);
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 0, v_val_1652_);
v___x_1654_ = v___x_1645_;
goto v_reusejp_1653_;
}
else
{
lean_object* v_reuseFailAlloc_1655_; 
v_reuseFailAlloc_1655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1655_, 0, v_val_1652_);
v___x_1654_ = v_reuseFailAlloc_1655_;
goto v_reusejp_1653_;
}
v_reusejp_1653_:
{
return v___x_1654_;
}
}
}
}
else
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
v_a_1657_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1659_ = v___x_1642_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1642_);
v___x_1659_ = lean_box(0);
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
v_resetjp_1658_:
{
lean_object* v___x_1662_; 
if (v_isShared_1660_ == 0)
{
v___x_1662_ = v___x_1659_;
goto v_reusejp_1661_;
}
else
{
lean_object* v_reuseFailAlloc_1663_; 
v_reuseFailAlloc_1663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1663_, 0, v_a_1657_);
v___x_1662_ = v_reuseFailAlloc_1663_;
goto v_reusejp_1661_;
}
v_reusejp_1661_:
{
return v___x_1662_;
}
}
}
}
}
}
else
{
lean_object* v_a_1666_; lean_object* v___x_1668_; uint8_t v_isShared_1669_; uint8_t v_isSharedCheck_1673_; 
lean_dec_ref(v_tail_1627_);
lean_dec(v___y_1624_);
lean_dec_ref(v___y_1623_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec(v___y_1618_);
lean_dec_ref(v___y_1617_);
lean_dec(v___y_1616_);
lean_dec(v___y_1615_);
lean_dec_ref(v_c_1612_);
lean_dec_ref(v___x_1611_);
v_a_1666_ = lean_ctor_get(v___x_1628_, 0);
v_isSharedCheck_1673_ = !lean_is_exclusive(v___x_1628_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1668_ = v___x_1628_;
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
else
{
lean_inc(v_a_1666_);
lean_dec(v___x_1628_);
v___x_1668_ = lean_box(0);
v_isShared_1669_ = v_isSharedCheck_1673_;
goto v_resetjp_1667_;
}
v_resetjp_1667_:
{
lean_object* v___x_1671_; 
if (v_isShared_1669_ == 0)
{
v___x_1671_ = v___x_1668_;
goto v_reusejp_1670_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_a_1666_);
v___x_1671_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1670_;
}
v_reusejp_1670_:
{
return v___x_1671_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0___boxed(lean_object* v___x_1674_, lean_object* v_c_1675_, lean_object* v_t_1676_, lean_object* v_init_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0(v___x_1674_, v_c_1675_, v_t_1676_, v_init_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq(lean_object* v_c_1690_, lean_object* v_a_1691_, lean_object* v_a_1692_, lean_object* v_a_1693_, lean_object* v_a_1694_, lean_object* v_a_1695_, lean_object* v_a_1696_, lean_object* v_a_1697_, lean_object* v_a_1698_, lean_object* v_a_1699_, lean_object* v_a_1700_){
_start:
{
lean_object* v_p_1702_; 
v_p_1702_ = lean_ctor_get(v_c_1690_, 0);
if (lean_obj_tag(v_p_1702_) == 1)
{
lean_object* v_k_1703_; lean_object* v_v_1704_; lean_object* v___x_1705_; 
lean_inc_ref(v_p_1702_);
v_k_1703_ = lean_ctor_get(v_p_1702_, 0);
v_v_1704_ = lean_ctor_get(v_p_1702_, 1);
v___x_1705_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1691_, v_a_1699_);
if (lean_obj_tag(v___x_1705_) == 0)
{
lean_object* v_a_1706_; lean_object* v___y_1708_; lean_object* v___x_1734_; uint8_t v___x_1735_; 
v_a_1706_ = lean_ctor_get(v___x_1705_, 0);
lean_inc(v_a_1706_);
lean_dec_ref(v___x_1705_);
v___x_1734_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6);
v___x_1735_ = lean_int_dec_lt(v_k_1703_, v___x_1734_);
if (v___x_1735_ == 0)
{
lean_object* v_lowers_1736_; lean_object* v_size_1737_; lean_object* v___x_1738_; uint8_t v___x_1739_; 
v_lowers_1736_ = lean_ctor_get(v_a_1706_, 7);
lean_inc_ref(v_lowers_1736_);
lean_dec(v_a_1706_);
v_size_1737_ = lean_ctor_get(v_lowers_1736_, 2);
v___x_1738_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0);
v___x_1739_ = lean_nat_dec_lt(v_v_1704_, v_size_1737_);
if (v___x_1739_ == 0)
{
lean_object* v___x_1740_; 
lean_dec_ref(v_lowers_1736_);
v___x_1740_ = l_outOfBounds___redArg(v___x_1738_);
v___y_1708_ = v___x_1740_;
goto v___jp_1707_;
}
else
{
lean_object* v___x_1741_; 
v___x_1741_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1738_, v_lowers_1736_, v_v_1704_);
v___y_1708_ = v___x_1741_;
goto v___jp_1707_;
}
}
else
{
lean_object* v_uppers_1742_; lean_object* v_size_1743_; lean_object* v___x_1744_; uint8_t v___x_1745_; 
v_uppers_1742_ = lean_ctor_get(v_a_1706_, 8);
lean_inc_ref(v_uppers_1742_);
lean_dec(v_a_1706_);
v_size_1743_ = lean_ctor_get(v_uppers_1742_, 2);
v___x_1744_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0);
v___x_1745_ = lean_nat_dec_lt(v_v_1704_, v_size_1743_);
if (v___x_1745_ == 0)
{
lean_object* v___x_1746_; 
lean_dec_ref(v_uppers_1742_);
v___x_1746_ = l_outOfBounds___redArg(v___x_1744_);
v___y_1708_ = v___x_1746_;
goto v___jp_1707_;
}
else
{
lean_object* v___x_1747_; 
v___x_1747_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1744_, v_uppers_1742_, v_v_1704_);
v___y_1708_ = v___x_1747_;
goto v___jp_1707_;
}
}
v___jp_1707_:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1709_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__0));
v___x_1710_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0(v_p_1702_, v_c_1690_, v___y_1708_, v___x_1709_, v_a_1691_, v_a_1692_, v_a_1693_, v_a_1694_, v_a_1695_, v_a_1696_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_object* v_a_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1725_; 
v_a_1711_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1725_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1725_ == 0)
{
v___x_1713_ = v___x_1710_;
v_isShared_1714_ = v_isSharedCheck_1725_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_a_1711_);
lean_dec(v___x_1710_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1725_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
lean_object* v_fst_1715_; 
v_fst_1715_ = lean_ctor_get(v_a_1711_, 0);
lean_inc(v_fst_1715_);
lean_dec(v_a_1711_);
if (lean_obj_tag(v_fst_1715_) == 0)
{
uint8_t v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1719_; 
v___x_1716_ = 0;
v___x_1717_ = lean_box(v___x_1716_);
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 0, v___x_1717_);
v___x_1719_ = v___x_1713_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v___x_1717_);
v___x_1719_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
return v___x_1719_;
}
}
else
{
lean_object* v_val_1721_; lean_object* v___x_1723_; 
v_val_1721_ = lean_ctor_get(v_fst_1715_, 0);
lean_inc(v_val_1721_);
lean_dec_ref(v_fst_1715_);
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 0, v_val_1721_);
v___x_1723_ = v___x_1713_;
goto v_reusejp_1722_;
}
else
{
lean_object* v_reuseFailAlloc_1724_; 
v_reuseFailAlloc_1724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1724_, 0, v_val_1721_);
v___x_1723_ = v_reuseFailAlloc_1724_;
goto v_reusejp_1722_;
}
v_reusejp_1722_:
{
return v___x_1723_;
}
}
}
}
else
{
lean_object* v_a_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1733_; 
v_a_1726_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1728_ = v___x_1710_;
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_a_1726_);
lean_dec(v___x_1710_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1733_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1731_; 
if (v_isShared_1729_ == 0)
{
v___x_1731_ = v___x_1728_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v_a_1726_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
}
}
else
{
lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1755_; 
lean_dec_ref(v_p_1702_);
lean_dec(v_a_1700_);
lean_dec_ref(v_a_1699_);
lean_dec(v_a_1698_);
lean_dec_ref(v_a_1697_);
lean_dec(v_a_1696_);
lean_dec_ref(v_a_1695_);
lean_dec(v_a_1694_);
lean_dec_ref(v_a_1693_);
lean_dec(v_a_1692_);
lean_dec(v_a_1691_);
lean_dec_ref(v_c_1690_);
v_a_1748_ = lean_ctor_get(v___x_1705_, 0);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1705_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1750_ = v___x_1705_;
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_dec(v___x_1705_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1753_; 
if (v_isShared_1751_ == 0)
{
v___x_1753_ = v___x_1750_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_a_1748_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
}
}
else
{
lean_object* v___x_1756_; 
lean_dec(v_a_1696_);
lean_dec_ref(v_a_1695_);
lean_dec(v_a_1694_);
lean_dec_ref(v_a_1693_);
lean_dec(v_a_1692_);
v___x_1756_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_1690_, v_a_1691_, v_a_1697_, v_a_1698_, v_a_1699_, v_a_1700_);
lean_dec(v_a_1700_);
lean_dec_ref(v_a_1699_);
lean_dec(v_a_1698_);
lean_dec_ref(v_a_1697_);
lean_dec(v_a_1691_);
return v___x_1756_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___boxed(lean_object* v_c_1757_, lean_object* v_a_1758_, lean_object* v_a_1759_, lean_object* v_a_1760_, lean_object* v_a_1761_, lean_object* v_a_1762_, lean_object* v_a_1763_, lean_object* v_a_1764_, lean_object* v_a_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_){
_start:
{
lean_object* v_res_1769_; 
v_res_1769_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq(v_c_1757_, v_a_1758_, v_a_1759_, v_a_1760_, v_a_1761_, v_a_1762_, v_a_1763_, v_a_1764_, v_a_1765_, v_a_1766_, v_a_1767_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(lean_object* v___x_1770_, lean_object* v_as_1771_, size_t v_i_1772_, size_t v_stop_1773_, lean_object* v_b_1774_){
_start:
{
lean_object* v___y_1776_; uint8_t v___x_1780_; 
v___x_1780_ = lean_usize_dec_eq(v_i_1772_, v_stop_1773_);
if (v___x_1780_ == 0)
{
lean_object* v___x_1781_; lean_object* v_p_1782_; uint8_t v___x_1783_; 
v___x_1781_ = lean_array_uget_borrowed(v_as_1771_, v_i_1772_);
v_p_1782_ = lean_ctor_get(v___x_1781_, 0);
v___x_1783_ = l_Int_Linear_instBEqPoly_beq(v_p_1782_, v___x_1770_);
if (v___x_1783_ == 0)
{
lean_object* v___x_1784_; 
lean_inc(v___x_1781_);
v___x_1784_ = l_Lean_PersistentArray_push___redArg(v_b_1774_, v___x_1781_);
v___y_1776_ = v___x_1784_;
goto v___jp_1775_;
}
else
{
v___y_1776_ = v_b_1774_;
goto v___jp_1775_;
}
}
else
{
return v_b_1774_;
}
v___jp_1775_:
{
size_t v___x_1777_; size_t v___x_1778_; 
v___x_1777_ = ((size_t)1ULL);
v___x_1778_ = lean_usize_add(v_i_1772_, v___x_1777_);
v_i_1772_ = v___x_1778_;
v_b_1774_ = v___y_1776_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1___boxed(lean_object* v___x_1785_, lean_object* v_as_1786_, lean_object* v_i_1787_, lean_object* v_stop_1788_, lean_object* v_b_1789_){
_start:
{
size_t v_i_boxed_1790_; size_t v_stop_boxed_1791_; lean_object* v_res_1792_; 
v_i_boxed_1790_ = lean_unbox_usize(v_i_1787_);
lean_dec(v_i_1787_);
v_stop_boxed_1791_ = lean_unbox_usize(v_stop_1788_);
lean_dec(v_stop_1788_);
v_res_1792_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1785_, v_as_1786_, v_i_boxed_1790_, v_stop_boxed_1791_, v_b_1789_);
lean_dec_ref(v_as_1786_);
lean_dec_ref(v___x_1785_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(lean_object* v___x_1793_, lean_object* v_x_1794_, lean_object* v_x_1795_){
_start:
{
if (lean_obj_tag(v_x_1794_) == 0)
{
lean_object* v_cs_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; uint8_t v___x_1799_; 
v_cs_1796_ = lean_ctor_get(v_x_1794_, 0);
v___x_1797_ = lean_unsigned_to_nat(0u);
v___x_1798_ = lean_array_get_size(v_cs_1796_);
v___x_1799_ = lean_nat_dec_lt(v___x_1797_, v___x_1798_);
if (v___x_1799_ == 0)
{
return v_x_1795_;
}
else
{
uint8_t v___x_1800_; 
v___x_1800_ = lean_nat_dec_le(v___x_1798_, v___x_1798_);
if (v___x_1800_ == 0)
{
if (v___x_1799_ == 0)
{
return v_x_1795_;
}
else
{
size_t v___x_1801_; size_t v___x_1802_; lean_object* v___x_1803_; 
v___x_1801_ = ((size_t)0ULL);
v___x_1802_ = lean_usize_of_nat(v___x_1798_);
v___x_1803_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1793_, v_cs_1796_, v___x_1801_, v___x_1802_, v_x_1795_);
return v___x_1803_;
}
}
else
{
size_t v___x_1804_; size_t v___x_1805_; lean_object* v___x_1806_; 
v___x_1804_ = ((size_t)0ULL);
v___x_1805_ = lean_usize_of_nat(v___x_1798_);
v___x_1806_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1793_, v_cs_1796_, v___x_1804_, v___x_1805_, v_x_1795_);
return v___x_1806_;
}
}
}
else
{
lean_object* v_vs_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; uint8_t v___x_1810_; 
v_vs_1807_ = lean_ctor_get(v_x_1794_, 0);
v___x_1808_ = lean_unsigned_to_nat(0u);
v___x_1809_ = lean_array_get_size(v_vs_1807_);
v___x_1810_ = lean_nat_dec_lt(v___x_1808_, v___x_1809_);
if (v___x_1810_ == 0)
{
return v_x_1795_;
}
else
{
uint8_t v___x_1811_; 
v___x_1811_ = lean_nat_dec_le(v___x_1809_, v___x_1809_);
if (v___x_1811_ == 0)
{
if (v___x_1810_ == 0)
{
return v_x_1795_;
}
else
{
size_t v___x_1812_; size_t v___x_1813_; lean_object* v___x_1814_; 
v___x_1812_ = ((size_t)0ULL);
v___x_1813_ = lean_usize_of_nat(v___x_1809_);
v___x_1814_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1793_, v_vs_1807_, v___x_1812_, v___x_1813_, v_x_1795_);
return v___x_1814_;
}
}
else
{
size_t v___x_1815_; size_t v___x_1816_; lean_object* v___x_1817_; 
v___x_1815_ = ((size_t)0ULL);
v___x_1816_ = lean_usize_of_nat(v___x_1809_);
v___x_1817_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1793_, v_vs_1807_, v___x_1815_, v___x_1816_, v_x_1795_);
return v___x_1817_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(lean_object* v___x_1818_, lean_object* v_as_1819_, size_t v_i_1820_, size_t v_stop_1821_, lean_object* v_b_1822_){
_start:
{
uint8_t v___x_1823_; 
v___x_1823_ = lean_usize_dec_eq(v_i_1820_, v_stop_1821_);
if (v___x_1823_ == 0)
{
lean_object* v___x_1824_; lean_object* v___x_1825_; size_t v___x_1826_; size_t v___x_1827_; 
v___x_1824_ = lean_array_uget_borrowed(v_as_1819_, v_i_1820_);
v___x_1825_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(v___x_1818_, v___x_1824_, v_b_1822_);
v___x_1826_ = ((size_t)1ULL);
v___x_1827_ = lean_usize_add(v_i_1820_, v___x_1826_);
v_i_1820_ = v___x_1827_;
v_b_1822_ = v___x_1825_;
goto _start;
}
else
{
return v_b_1822_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v___x_1829_, lean_object* v_as_1830_, lean_object* v_i_1831_, lean_object* v_stop_1832_, lean_object* v_b_1833_){
_start:
{
size_t v_i_boxed_1834_; size_t v_stop_boxed_1835_; lean_object* v_res_1836_; 
v_i_boxed_1834_ = lean_unbox_usize(v_i_1831_);
lean_dec(v_i_1831_);
v_stop_boxed_1835_ = lean_unbox_usize(v_stop_1832_);
lean_dec(v_stop_1832_);
v_res_1836_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1829_, v_as_1830_, v_i_boxed_1834_, v_stop_boxed_1835_, v_b_1833_);
lean_dec_ref(v_as_1830_);
lean_dec_ref(v___x_1829_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2___boxed(lean_object* v___x_1837_, lean_object* v_x_1838_, lean_object* v_x_1839_){
_start:
{
lean_object* v_res_1840_; 
v_res_1840_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(v___x_1837_, v_x_1838_, v_x_1839_);
lean_dec_ref(v_x_1838_);
lean_dec_ref(v___x_1837_);
return v_res_1840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(lean_object* v___x_1841_, lean_object* v_x_1842_, size_t v_x_1843_, size_t v_x_1844_, lean_object* v_x_1845_){
_start:
{
if (lean_obj_tag(v_x_1842_) == 0)
{
lean_object* v_cs_1846_; lean_object* v___x_1847_; size_t v___x_1848_; lean_object* v_j_1849_; lean_object* v___x_1850_; size_t v___x_1851_; size_t v___x_1852_; size_t v___x_1853_; size_t v___x_1854_; size_t v___x_1855_; size_t v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; uint8_t v___x_1861_; 
v_cs_1846_ = lean_ctor_get(v_x_1842_, 0);
v___x_1847_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0);
v___x_1848_ = lean_usize_shift_right(v_x_1843_, v_x_1844_);
v_j_1849_ = lean_usize_to_nat(v___x_1848_);
v___x_1850_ = lean_array_get_borrowed(v___x_1847_, v_cs_1846_, v_j_1849_);
v___x_1851_ = ((size_t)1ULL);
v___x_1852_ = lean_usize_shift_left(v___x_1851_, v_x_1844_);
v___x_1853_ = lean_usize_sub(v___x_1852_, v___x_1851_);
v___x_1854_ = lean_usize_land(v_x_1843_, v___x_1853_);
v___x_1855_ = ((size_t)5ULL);
v___x_1856_ = lean_usize_sub(v_x_1844_, v___x_1855_);
v___x_1857_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(v___x_1841_, v___x_1850_, v___x_1854_, v___x_1856_, v_x_1845_);
v___x_1858_ = lean_unsigned_to_nat(1u);
v___x_1859_ = lean_nat_add(v_j_1849_, v___x_1858_);
lean_dec(v_j_1849_);
v___x_1860_ = lean_array_get_size(v_cs_1846_);
v___x_1861_ = lean_nat_dec_lt(v___x_1859_, v___x_1860_);
if (v___x_1861_ == 0)
{
lean_dec(v___x_1859_);
return v___x_1857_;
}
else
{
uint8_t v___x_1862_; 
v___x_1862_ = lean_nat_dec_le(v___x_1860_, v___x_1860_);
if (v___x_1862_ == 0)
{
if (v___x_1861_ == 0)
{
lean_dec(v___x_1859_);
return v___x_1857_;
}
else
{
size_t v___x_1863_; size_t v___x_1864_; lean_object* v___x_1865_; 
v___x_1863_ = lean_usize_of_nat(v___x_1859_);
lean_dec(v___x_1859_);
v___x_1864_ = lean_usize_of_nat(v___x_1860_);
v___x_1865_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1841_, v_cs_1846_, v___x_1863_, v___x_1864_, v___x_1857_);
return v___x_1865_;
}
}
else
{
size_t v___x_1866_; size_t v___x_1867_; lean_object* v___x_1868_; 
v___x_1866_ = lean_usize_of_nat(v___x_1859_);
lean_dec(v___x_1859_);
v___x_1867_ = lean_usize_of_nat(v___x_1860_);
v___x_1868_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1841_, v_cs_1846_, v___x_1866_, v___x_1867_, v___x_1857_);
return v___x_1868_;
}
}
}
else
{
lean_object* v_vs_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; uint8_t v___x_1872_; 
v_vs_1869_ = lean_ctor_get(v_x_1842_, 0);
v___x_1870_ = lean_usize_to_nat(v_x_1843_);
v___x_1871_ = lean_array_get_size(v_vs_1869_);
v___x_1872_ = lean_nat_dec_lt(v___x_1870_, v___x_1871_);
if (v___x_1872_ == 0)
{
lean_dec(v___x_1870_);
return v_x_1845_;
}
else
{
uint8_t v___x_1873_; 
v___x_1873_ = lean_nat_dec_le(v___x_1871_, v___x_1871_);
if (v___x_1873_ == 0)
{
if (v___x_1872_ == 0)
{
lean_dec(v___x_1870_);
return v_x_1845_;
}
else
{
size_t v___x_1874_; size_t v___x_1875_; lean_object* v___x_1876_; 
v___x_1874_ = lean_usize_of_nat(v___x_1870_);
lean_dec(v___x_1870_);
v___x_1875_ = lean_usize_of_nat(v___x_1871_);
v___x_1876_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1841_, v_vs_1869_, v___x_1874_, v___x_1875_, v_x_1845_);
return v___x_1876_;
}
}
else
{
size_t v___x_1877_; size_t v___x_1878_; lean_object* v___x_1879_; 
v___x_1877_ = lean_usize_of_nat(v___x_1870_);
lean_dec(v___x_1870_);
v___x_1878_ = lean_usize_of_nat(v___x_1871_);
v___x_1879_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1841_, v_vs_1869_, v___x_1877_, v___x_1878_, v_x_1845_);
return v___x_1879_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0___boxed(lean_object* v___x_1880_, lean_object* v_x_1881_, lean_object* v_x_1882_, lean_object* v_x_1883_, lean_object* v_x_1884_){
_start:
{
size_t v_x_23725__boxed_1885_; size_t v_x_23726__boxed_1886_; lean_object* v_res_1887_; 
v_x_23725__boxed_1885_ = lean_unbox_usize(v_x_1882_);
lean_dec(v_x_1882_);
v_x_23726__boxed_1886_ = lean_unbox_usize(v_x_1883_);
lean_dec(v_x_1883_);
v_res_1887_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(v___x_1880_, v_x_1881_, v_x_23725__boxed_1885_, v_x_23726__boxed_1886_, v_x_1884_);
lean_dec_ref(v_x_1881_);
lean_dec_ref(v___x_1880_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(lean_object* v___x_1888_, lean_object* v_t_1889_, lean_object* v_init_1890_, lean_object* v_start_1891_){
_start:
{
lean_object* v___x_1892_; uint8_t v___x_1893_; 
v___x_1892_ = lean_unsigned_to_nat(0u);
v___x_1893_ = lean_nat_dec_eq(v_start_1891_, v___x_1892_);
if (v___x_1893_ == 0)
{
lean_object* v_root_1894_; lean_object* v_tail_1895_; size_t v_shift_1896_; lean_object* v_tailOff_1897_; uint8_t v___x_1898_; 
v_root_1894_ = lean_ctor_get(v_t_1889_, 0);
v_tail_1895_ = lean_ctor_get(v_t_1889_, 1);
v_shift_1896_ = lean_ctor_get_usize(v_t_1889_, 4);
v_tailOff_1897_ = lean_ctor_get(v_t_1889_, 3);
v___x_1898_ = lean_nat_dec_le(v_tailOff_1897_, v_start_1891_);
if (v___x_1898_ == 0)
{
size_t v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; uint8_t v___x_1902_; 
v___x_1899_ = lean_usize_of_nat(v_start_1891_);
v___x_1900_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(v___x_1888_, v_root_1894_, v___x_1899_, v_shift_1896_, v_init_1890_);
v___x_1901_ = lean_array_get_size(v_tail_1895_);
v___x_1902_ = lean_nat_dec_lt(v___x_1892_, v___x_1901_);
if (v___x_1902_ == 0)
{
return v___x_1900_;
}
else
{
uint8_t v___x_1903_; 
v___x_1903_ = lean_nat_dec_le(v___x_1901_, v___x_1901_);
if (v___x_1903_ == 0)
{
if (v___x_1902_ == 0)
{
return v___x_1900_;
}
else
{
size_t v___x_1904_; size_t v___x_1905_; lean_object* v___x_1906_; 
v___x_1904_ = ((size_t)0ULL);
v___x_1905_ = lean_usize_of_nat(v___x_1901_);
v___x_1906_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1888_, v_tail_1895_, v___x_1904_, v___x_1905_, v___x_1900_);
return v___x_1906_;
}
}
else
{
size_t v___x_1907_; size_t v___x_1908_; lean_object* v___x_1909_; 
v___x_1907_ = ((size_t)0ULL);
v___x_1908_ = lean_usize_of_nat(v___x_1901_);
v___x_1909_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1888_, v_tail_1895_, v___x_1907_, v___x_1908_, v___x_1900_);
return v___x_1909_;
}
}
}
else
{
lean_object* v___x_1910_; lean_object* v___x_1911_; uint8_t v___x_1912_; 
v___x_1910_ = lean_nat_sub(v_start_1891_, v_tailOff_1897_);
v___x_1911_ = lean_array_get_size(v_tail_1895_);
v___x_1912_ = lean_nat_dec_lt(v___x_1910_, v___x_1911_);
if (v___x_1912_ == 0)
{
lean_dec(v___x_1910_);
return v_init_1890_;
}
else
{
uint8_t v___x_1913_; 
v___x_1913_ = lean_nat_dec_le(v___x_1911_, v___x_1911_);
if (v___x_1913_ == 0)
{
if (v___x_1912_ == 0)
{
lean_dec(v___x_1910_);
return v_init_1890_;
}
else
{
size_t v___x_1914_; size_t v___x_1915_; lean_object* v___x_1916_; 
v___x_1914_ = lean_usize_of_nat(v___x_1910_);
lean_dec(v___x_1910_);
v___x_1915_ = lean_usize_of_nat(v___x_1911_);
v___x_1916_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1888_, v_tail_1895_, v___x_1914_, v___x_1915_, v_init_1890_);
return v___x_1916_;
}
}
else
{
size_t v___x_1917_; size_t v___x_1918_; lean_object* v___x_1919_; 
v___x_1917_ = lean_usize_of_nat(v___x_1910_);
lean_dec(v___x_1910_);
v___x_1918_ = lean_usize_of_nat(v___x_1911_);
v___x_1919_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1888_, v_tail_1895_, v___x_1917_, v___x_1918_, v_init_1890_);
return v___x_1919_;
}
}
}
}
else
{
lean_object* v_root_1920_; lean_object* v_tail_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; uint8_t v___x_1924_; 
v_root_1920_ = lean_ctor_get(v_t_1889_, 0);
v_tail_1921_ = lean_ctor_get(v_t_1889_, 1);
v___x_1922_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(v___x_1888_, v_root_1920_, v_init_1890_);
v___x_1923_ = lean_array_get_size(v_tail_1921_);
v___x_1924_ = lean_nat_dec_lt(v___x_1892_, v___x_1923_);
if (v___x_1924_ == 0)
{
return v___x_1922_;
}
else
{
uint8_t v___x_1925_; 
v___x_1925_ = lean_nat_dec_le(v___x_1923_, v___x_1923_);
if (v___x_1925_ == 0)
{
if (v___x_1924_ == 0)
{
return v___x_1922_;
}
else
{
size_t v___x_1926_; size_t v___x_1927_; lean_object* v___x_1928_; 
v___x_1926_ = ((size_t)0ULL);
v___x_1927_ = lean_usize_of_nat(v___x_1923_);
v___x_1928_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1888_, v_tail_1921_, v___x_1926_, v___x_1927_, v___x_1922_);
return v___x_1928_;
}
}
else
{
size_t v___x_1929_; size_t v___x_1930_; lean_object* v___x_1931_; 
v___x_1929_ = ((size_t)0ULL);
v___x_1930_ = lean_usize_of_nat(v___x_1923_);
v___x_1931_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1888_, v_tail_1921_, v___x_1929_, v___x_1930_, v___x_1922_);
return v___x_1931_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0___boxed(lean_object* v___x_1932_, lean_object* v_t_1933_, lean_object* v_init_1934_, lean_object* v_start_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(v___x_1932_, v_t_1933_, v_init_1934_, v_start_1935_);
lean_dec(v_start_1935_);
lean_dec_ref(v_t_1933_);
lean_dec_ref(v___x_1932_);
return v_res_1936_;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1937_ = lean_unsigned_to_nat(32u);
v___x_1938_ = lean_mk_empty_array_with_capacity(v___x_1937_);
v___x_1939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1939_, 0, v___x_1938_);
return v___x_1939_;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1940_ = ((size_t)5ULL);
v___x_1941_ = lean_unsigned_to_nat(0u);
v___x_1942_ = lean_unsigned_to_nat(32u);
v___x_1943_ = lean_mk_empty_array_with_capacity(v___x_1942_);
v___x_1944_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___redArg___closed__0, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___redArg___closed__0);
v___x_1945_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1945_, 0, v___x_1944_);
lean_ctor_set(v___x_1945_, 1, v___x_1943_);
lean_ctor_set(v___x_1945_, 2, v___x_1941_);
lean_ctor_set(v___x_1945_, 3, v___x_1941_);
lean_ctor_set_usize(v___x_1945_, 4, v___x_1940_);
return v___x_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___redArg(lean_object* v___x_1946_, lean_object* v_x_1947_, size_t v_x_1948_, size_t v_x_1949_){
_start:
{
if (lean_obj_tag(v_x_1947_) == 0)
{
lean_object* v_cs_1950_; size_t v_j_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; uint8_t v___x_1954_; 
v_cs_1950_ = lean_ctor_get(v_x_1947_, 0);
v_j_1951_ = lean_usize_shift_right(v_x_1948_, v_x_1949_);
v___x_1952_ = lean_usize_to_nat(v_j_1951_);
v___x_1953_ = lean_array_get_size(v_cs_1950_);
v___x_1954_ = lean_nat_dec_lt(v___x_1952_, v___x_1953_);
if (v___x_1954_ == 0)
{
lean_dec(v___x_1952_);
return v_x_1947_;
}
else
{
lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1972_; 
lean_inc_ref(v_cs_1950_);
v_isSharedCheck_1972_ = !lean_is_exclusive(v_x_1947_);
if (v_isSharedCheck_1972_ == 0)
{
lean_object* v_unused_1973_; 
v_unused_1973_ = lean_ctor_get(v_x_1947_, 0);
lean_dec(v_unused_1973_);
v___x_1956_ = v_x_1947_;
v_isShared_1957_ = v_isSharedCheck_1972_;
goto v_resetjp_1955_;
}
else
{
lean_dec(v_x_1947_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1972_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
size_t v___x_1958_; size_t v___x_1959_; size_t v___x_1960_; size_t v_i_1961_; size_t v___x_1962_; size_t v_shift_1963_; lean_object* v_v_1964_; lean_object* v___x_1965_; lean_object* v_xs_x27_1966_; lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1970_; 
v___x_1958_ = ((size_t)1ULL);
v___x_1959_ = lean_usize_shift_left(v___x_1958_, v_x_1949_);
v___x_1960_ = lean_usize_sub(v___x_1959_, v___x_1958_);
v_i_1961_ = lean_usize_land(v_x_1948_, v___x_1960_);
v___x_1962_ = ((size_t)5ULL);
v_shift_1963_ = lean_usize_sub(v_x_1949_, v___x_1962_);
v_v_1964_ = lean_array_fget(v_cs_1950_, v___x_1952_);
v___x_1965_ = lean_box(0);
v_xs_x27_1966_ = lean_array_fset(v_cs_1950_, v___x_1952_, v___x_1965_);
v___x_1967_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___redArg(v___x_1946_, v_v_1964_, v_i_1961_, v_shift_1963_);
v___x_1968_ = lean_array_fset(v_xs_x27_1966_, v___x_1952_, v___x_1967_);
lean_dec(v___x_1952_);
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 0, v___x_1968_);
v___x_1970_ = v___x_1956_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v___x_1968_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
}
else
{
lean_object* v_vs_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; uint8_t v___x_1977_; 
v_vs_1974_ = lean_ctor_get(v_x_1947_, 0);
v___x_1975_ = lean_usize_to_nat(v_x_1948_);
v___x_1976_ = lean_array_get_size(v_vs_1974_);
v___x_1977_ = lean_nat_dec_lt(v___x_1975_, v___x_1976_);
if (v___x_1977_ == 0)
{
lean_dec(v___x_1975_);
return v_x_1947_;
}
else
{
lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_1991_; 
lean_inc_ref(v_vs_1974_);
v_isSharedCheck_1991_ = !lean_is_exclusive(v_x_1947_);
if (v_isSharedCheck_1991_ == 0)
{
lean_object* v_unused_1992_; 
v_unused_1992_ = lean_ctor_get(v_x_1947_, 0);
lean_dec(v_unused_1992_);
v___x_1979_ = v_x_1947_;
v_isShared_1980_ = v_isSharedCheck_1991_;
goto v_resetjp_1978_;
}
else
{
lean_dec(v_x_1947_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_1991_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
lean_object* v_v_1981_; lean_object* v___x_1982_; lean_object* v_xs_x27_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1989_; 
v_v_1981_ = lean_array_fget(v_vs_1974_, v___x_1975_);
v___x_1982_ = lean_box(0);
v_xs_x27_1983_ = lean_array_fset(v_vs_1974_, v___x_1975_, v___x_1982_);
v___x_1984_ = lean_unsigned_to_nat(0u);
v___x_1985_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___redArg___closed__1, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___redArg___closed__1);
v___x_1986_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(v___x_1946_, v_v_1981_, v___x_1985_, v___x_1984_);
lean_dec(v_v_1981_);
v___x_1987_ = lean_array_fset(v_xs_x27_1983_, v___x_1975_, v___x_1986_);
lean_dec(v___x_1975_);
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 0, v___x_1987_);
v___x_1989_ = v___x_1979_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1987_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___redArg___boxed(lean_object* v___x_1993_, lean_object* v_x_1994_, lean_object* v_x_1995_, lean_object* v_x_1996_){
_start:
{
size_t v_x_23897__boxed_1997_; size_t v_x_23898__boxed_1998_; lean_object* v_res_1999_; 
v_x_23897__boxed_1997_ = lean_unbox_usize(v_x_1995_);
lean_dec(v_x_1995_);
v_x_23898__boxed_1998_ = lean_unbox_usize(v_x_1996_);
lean_dec(v_x_1996_);
v_res_1999_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___redArg(v___x_1993_, v_x_1994_, v_x_23897__boxed_1997_, v_x_23898__boxed_1998_);
lean_dec_ref(v___x_1993_);
return v_res_1999_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1(lean_object* v___x_2000_, lean_object* v_inst_2001_, lean_object* v_t_2002_, lean_object* v_i_2003_){
_start:
{
lean_object* v_root_2004_; lean_object* v_tail_2005_; lean_object* v_size_2006_; size_t v_shift_2007_; lean_object* v_tailOff_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2036_; 
v_root_2004_ = lean_ctor_get(v_t_2002_, 0);
v_tail_2005_ = lean_ctor_get(v_t_2002_, 1);
v_size_2006_ = lean_ctor_get(v_t_2002_, 2);
v_shift_2007_ = lean_ctor_get_usize(v_t_2002_, 4);
v_tailOff_2008_ = lean_ctor_get(v_t_2002_, 3);
v_isSharedCheck_2036_ = !lean_is_exclusive(v_t_2002_);
if (v_isSharedCheck_2036_ == 0)
{
v___x_2010_ = v_t_2002_;
v_isShared_2011_ = v_isSharedCheck_2036_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_tailOff_2008_);
lean_inc(v_size_2006_);
lean_inc(v_tail_2005_);
lean_inc(v_root_2004_);
lean_dec(v_t_2002_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2036_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
uint8_t v___x_2012_; 
v___x_2012_ = lean_nat_dec_le(v_tailOff_2008_, v_i_2003_);
if (v___x_2012_ == 0)
{
size_t v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2016_; 
v___x_2013_ = lean_usize_of_nat(v_i_2003_);
v___x_2014_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___redArg(v___x_2000_, v_root_2004_, v___x_2013_, v_shift_2007_);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 0, v___x_2014_);
v___x_2016_ = v___x_2010_;
goto v_reusejp_2015_;
}
else
{
lean_object* v_reuseFailAlloc_2017_; 
v_reuseFailAlloc_2017_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2017_, 0, v___x_2014_);
lean_ctor_set(v_reuseFailAlloc_2017_, 1, v_tail_2005_);
lean_ctor_set(v_reuseFailAlloc_2017_, 2, v_size_2006_);
lean_ctor_set(v_reuseFailAlloc_2017_, 3, v_tailOff_2008_);
lean_ctor_set_usize(v_reuseFailAlloc_2017_, 4, v_shift_2007_);
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
lean_object* v___x_2018_; lean_object* v___x_2019_; uint8_t v___x_2020_; 
v___x_2018_ = lean_nat_sub(v_i_2003_, v_tailOff_2008_);
v___x_2019_ = lean_array_get_size(v_tail_2005_);
v___x_2020_ = lean_nat_dec_lt(v___x_2018_, v___x_2019_);
if (v___x_2020_ == 0)
{
lean_object* v___x_2022_; 
lean_dec(v___x_2018_);
if (v_isShared_2011_ == 0)
{
v___x_2022_ = v___x_2010_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_root_2004_);
lean_ctor_set(v_reuseFailAlloc_2023_, 1, v_tail_2005_);
lean_ctor_set(v_reuseFailAlloc_2023_, 2, v_size_2006_);
lean_ctor_set(v_reuseFailAlloc_2023_, 3, v_tailOff_2008_);
lean_ctor_set_usize(v_reuseFailAlloc_2023_, 4, v_shift_2007_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
else
{
lean_object* v_v_2024_; lean_object* v___x_2025_; lean_object* v_xs_x27_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2034_; 
v_v_2024_ = lean_array_fget(v_tail_2005_, v___x_2018_);
v___x_2025_ = lean_box(0);
v_xs_x27_2026_ = lean_array_fset(v_tail_2005_, v___x_2018_, v___x_2025_);
v___x_2027_ = lean_unsigned_to_nat(32u);
v___x_2028_ = lean_mk_empty_array_with_capacity(v___x_2027_);
lean_dec_ref(v___x_2028_);
v___x_2029_ = lean_unsigned_to_nat(0u);
v___x_2030_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___redArg___closed__1, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___redArg___closed__1_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___redArg___closed__1);
v___x_2031_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(v___x_2000_, v_v_2024_, v___x_2030_, v___x_2029_);
lean_dec(v_v_2024_);
v___x_2032_ = lean_array_fset(v_xs_x27_2026_, v___x_2018_, v___x_2031_);
lean_dec(v___x_2018_);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 1, v___x_2032_);
v___x_2034_ = v___x_2010_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_root_2004_);
lean_ctor_set(v_reuseFailAlloc_2035_, 1, v___x_2032_);
lean_ctor_set(v_reuseFailAlloc_2035_, 2, v_size_2006_);
lean_ctor_set(v_reuseFailAlloc_2035_, 3, v_tailOff_2008_);
lean_ctor_set_usize(v_reuseFailAlloc_2035_, 4, v_shift_2007_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1___boxed(lean_object* v___x_2037_, lean_object* v_inst_2038_, lean_object* v_t_2039_, lean_object* v_i_2040_){
_start:
{
lean_object* v_res_2041_; 
v_res_2041_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1(v___x_2037_, v_inst_2038_, v_t_2039_, v_i_2040_);
lean_dec(v_i_2040_);
lean_dec_ref(v_inst_2038_);
lean_dec_ref(v___x_2037_);
return v_res_2041_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0(lean_object* v_p_2042_, lean_object* v___x_2043_, lean_object* v_x_2044_, lean_object* v_s_2045_){
_start:
{
lean_object* v_vars_2046_; lean_object* v_varMap_2047_; lean_object* v_vars_x27_2048_; lean_object* v_varMap_x27_2049_; lean_object* v_natToIntMap_2050_; lean_object* v_natDef_2051_; lean_object* v_dvds_2052_; lean_object* v_lowers_2053_; lean_object* v_uppers_2054_; lean_object* v_diseqs_2055_; lean_object* v_elimEqs_2056_; lean_object* v_elimStack_2057_; lean_object* v_occurs_2058_; lean_object* v_assignment_2059_; lean_object* v_nextCnstrId_2060_; uint8_t v_caseSplits_2061_; lean_object* v_conflict_x3f_2062_; lean_object* v_diseqSplits_2063_; lean_object* v_divMod_2064_; lean_object* v_toIntIds_2065_; lean_object* v_toIntInfos_2066_; lean_object* v_toIntTermMap_2067_; lean_object* v_toIntVarMap_2068_; uint8_t v_usedCommRing_2069_; lean_object* v_nonlinearOccs_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2078_; 
v_vars_2046_ = lean_ctor_get(v_s_2045_, 0);
v_varMap_2047_ = lean_ctor_get(v_s_2045_, 1);
v_vars_x27_2048_ = lean_ctor_get(v_s_2045_, 2);
v_varMap_x27_2049_ = lean_ctor_get(v_s_2045_, 3);
v_natToIntMap_2050_ = lean_ctor_get(v_s_2045_, 4);
v_natDef_2051_ = lean_ctor_get(v_s_2045_, 5);
v_dvds_2052_ = lean_ctor_get(v_s_2045_, 6);
v_lowers_2053_ = lean_ctor_get(v_s_2045_, 7);
v_uppers_2054_ = lean_ctor_get(v_s_2045_, 8);
v_diseqs_2055_ = lean_ctor_get(v_s_2045_, 9);
v_elimEqs_2056_ = lean_ctor_get(v_s_2045_, 10);
v_elimStack_2057_ = lean_ctor_get(v_s_2045_, 11);
v_occurs_2058_ = lean_ctor_get(v_s_2045_, 12);
v_assignment_2059_ = lean_ctor_get(v_s_2045_, 13);
v_nextCnstrId_2060_ = lean_ctor_get(v_s_2045_, 14);
v_caseSplits_2061_ = lean_ctor_get_uint8(v_s_2045_, sizeof(void*)*23);
v_conflict_x3f_2062_ = lean_ctor_get(v_s_2045_, 15);
v_diseqSplits_2063_ = lean_ctor_get(v_s_2045_, 16);
v_divMod_2064_ = lean_ctor_get(v_s_2045_, 17);
v_toIntIds_2065_ = lean_ctor_get(v_s_2045_, 18);
v_toIntInfos_2066_ = lean_ctor_get(v_s_2045_, 19);
v_toIntTermMap_2067_ = lean_ctor_get(v_s_2045_, 20);
v_toIntVarMap_2068_ = lean_ctor_get(v_s_2045_, 21);
v_usedCommRing_2069_ = lean_ctor_get_uint8(v_s_2045_, sizeof(void*)*23 + 1);
v_nonlinearOccs_2070_ = lean_ctor_get(v_s_2045_, 22);
v_isSharedCheck_2078_ = !lean_is_exclusive(v_s_2045_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2072_ = v_s_2045_;
v_isShared_2073_ = v_isSharedCheck_2078_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_nonlinearOccs_2070_);
lean_inc(v_toIntVarMap_2068_);
lean_inc(v_toIntTermMap_2067_);
lean_inc(v_toIntInfos_2066_);
lean_inc(v_toIntIds_2065_);
lean_inc(v_divMod_2064_);
lean_inc(v_diseqSplits_2063_);
lean_inc(v_conflict_x3f_2062_);
lean_inc(v_nextCnstrId_2060_);
lean_inc(v_assignment_2059_);
lean_inc(v_occurs_2058_);
lean_inc(v_elimStack_2057_);
lean_inc(v_elimEqs_2056_);
lean_inc(v_diseqs_2055_);
lean_inc(v_uppers_2054_);
lean_inc(v_lowers_2053_);
lean_inc(v_dvds_2052_);
lean_inc(v_natDef_2051_);
lean_inc(v_natToIntMap_2050_);
lean_inc(v_varMap_x27_2049_);
lean_inc(v_vars_x27_2048_);
lean_inc(v_varMap_2047_);
lean_inc(v_vars_2046_);
lean_dec(v_s_2045_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2078_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2074_; lean_object* v___x_2076_; 
v___x_2074_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1(v_p_2042_, v___x_2043_, v_diseqs_2055_, v_x_2044_);
if (v_isShared_2073_ == 0)
{
lean_ctor_set(v___x_2072_, 9, v___x_2074_);
v___x_2076_ = v___x_2072_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_vars_2046_);
lean_ctor_set(v_reuseFailAlloc_2077_, 1, v_varMap_2047_);
lean_ctor_set(v_reuseFailAlloc_2077_, 2, v_vars_x27_2048_);
lean_ctor_set(v_reuseFailAlloc_2077_, 3, v_varMap_x27_2049_);
lean_ctor_set(v_reuseFailAlloc_2077_, 4, v_natToIntMap_2050_);
lean_ctor_set(v_reuseFailAlloc_2077_, 5, v_natDef_2051_);
lean_ctor_set(v_reuseFailAlloc_2077_, 6, v_dvds_2052_);
lean_ctor_set(v_reuseFailAlloc_2077_, 7, v_lowers_2053_);
lean_ctor_set(v_reuseFailAlloc_2077_, 8, v_uppers_2054_);
lean_ctor_set(v_reuseFailAlloc_2077_, 9, v___x_2074_);
lean_ctor_set(v_reuseFailAlloc_2077_, 10, v_elimEqs_2056_);
lean_ctor_set(v_reuseFailAlloc_2077_, 11, v_elimStack_2057_);
lean_ctor_set(v_reuseFailAlloc_2077_, 12, v_occurs_2058_);
lean_ctor_set(v_reuseFailAlloc_2077_, 13, v_assignment_2059_);
lean_ctor_set(v_reuseFailAlloc_2077_, 14, v_nextCnstrId_2060_);
lean_ctor_set(v_reuseFailAlloc_2077_, 15, v_conflict_x3f_2062_);
lean_ctor_set(v_reuseFailAlloc_2077_, 16, v_diseqSplits_2063_);
lean_ctor_set(v_reuseFailAlloc_2077_, 17, v_divMod_2064_);
lean_ctor_set(v_reuseFailAlloc_2077_, 18, v_toIntIds_2065_);
lean_ctor_set(v_reuseFailAlloc_2077_, 19, v_toIntInfos_2066_);
lean_ctor_set(v_reuseFailAlloc_2077_, 20, v_toIntTermMap_2067_);
lean_ctor_set(v_reuseFailAlloc_2077_, 21, v_toIntVarMap_2068_);
lean_ctor_set(v_reuseFailAlloc_2077_, 22, v_nonlinearOccs_2070_);
lean_ctor_set_uint8(v_reuseFailAlloc_2077_, sizeof(void*)*23, v_caseSplits_2061_);
lean_ctor_set_uint8(v_reuseFailAlloc_2077_, sizeof(void*)*23 + 1, v_usedCommRing_2069_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed(lean_object* v_p_2079_, lean_object* v___x_2080_, lean_object* v_x_2081_, lean_object* v_s_2082_){
_start:
{
lean_object* v_res_2083_; 
v_res_2083_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0(v_p_2079_, v___x_2080_, v_x_2081_, v_s_2082_);
lean_dec(v_x_2081_);
lean_dec_ref(v___x_2080_);
lean_dec_ref(v_p_2079_);
return v_res_2083_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2090_ = lean_unsigned_to_nat(1u);
v___x_2091_ = lean_nat_to_int(v___x_2090_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(lean_object* v_c_2092_, lean_object* v_x_2093_, lean_object* v_as_2094_, size_t v_sz_2095_, size_t v_i_2096_, lean_object* v_b_2097_, lean_object* v___y_2098_){
_start:
{
uint8_t v___x_2100_; 
v___x_2100_ = lean_usize_dec_lt(v_i_2096_, v_sz_2095_);
if (v___x_2100_ == 0)
{
lean_object* v___x_2101_; 
lean_dec(v_x_2093_);
lean_dec_ref(v_c_2092_);
v___x_2101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2101_, 0, v_b_2097_);
return v___x_2101_;
}
else
{
lean_object* v_snd_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2149_; 
v_snd_2102_ = lean_ctor_get(v_b_2097_, 1);
v_isSharedCheck_2149_ = !lean_is_exclusive(v_b_2097_);
if (v_isSharedCheck_2149_ == 0)
{
lean_object* v_unused_2150_; 
v_unused_2150_ = lean_ctor_get(v_b_2097_, 0);
lean_dec(v_unused_2150_);
v___x_2104_ = v_b_2097_;
v_isShared_2105_ = v_isSharedCheck_2149_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_snd_2102_);
lean_dec(v_b_2097_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2149_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v_p_2106_; lean_object* v_a_2107_; lean_object* v_p_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___f_2111_; uint8_t v___y_2113_; uint8_t v___x_2147_; 
v_p_2106_ = lean_ctor_get(v_c_2092_, 0);
v_a_2107_ = lean_array_uget_borrowed(v_as_2094_, v_i_2096_);
v_p_2108_ = lean_ctor_get(v_a_2107_, 0);
v___x_2109_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0);
v___x_2110_ = lean_box(0);
lean_inc(v_x_2093_);
lean_inc_ref(v_p_2108_);
v___f_2111_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2111_, 0, v_p_2108_);
lean_closure_set(v___f_2111_, 1, v___x_2109_);
lean_closure_set(v___f_2111_, 2, v_x_2093_);
v___x_2147_ = l_Int_Linear_instBEqPoly_beq(v_p_2106_, v_p_2108_);
if (v___x_2147_ == 0)
{
uint8_t v___x_2148_; 
v___x_2148_ = l_Int_Linear_Poly_isNegEq(v_p_2106_, v_p_2108_);
v___y_2113_ = v___x_2148_;
goto v___jp_2112_;
}
else
{
v___y_2113_ = v___x_2147_;
goto v___jp_2112_;
}
v___jp_2112_:
{
if (v___y_2113_ == 0)
{
lean_object* v___x_2114_; size_t v___x_2115_; size_t v___x_2116_; 
lean_dec_ref(v___f_2111_);
lean_del_object(v___x_2104_);
lean_dec(v_snd_2102_);
v___x_2114_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__1));
v___x_2115_ = ((size_t)1ULL);
v___x_2116_ = lean_usize_add(v_i_2096_, v___x_2115_);
v_i_2096_ = v___x_2116_;
v_b_2097_ = v___x_2114_;
goto _start;
}
else
{
lean_object* v___x_2118_; lean_object* v___x_2119_; 
lean_dec(v_x_2093_);
v___x_2118_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2119_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2118_, v___f_2111_, v___y_2098_);
if (lean_obj_tag(v___x_2119_) == 0)
{
lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2137_; 
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2137_ == 0)
{
lean_object* v_unused_2138_; 
v_unused_2138_ = lean_ctor_get(v___x_2119_, 0);
lean_dec(v_unused_2138_);
v___x_2121_ = v___x_2119_;
v_isShared_2122_ = v_isSharedCheck_2137_;
goto v_resetjp_2120_;
}
else
{
lean_dec(v___x_2119_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2137_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2130_; 
v___x_2123_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
lean_inc_ref(v_p_2106_);
v___x_2124_ = l_Int_Linear_Poly_addConst(v_p_2106_, v___x_2123_);
lean_inc(v_a_2107_);
v___x_2125_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_2125_, 0, v_c_2092_);
lean_ctor_set(v___x_2125_, 1, v_a_2107_);
v___x_2126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2124_);
lean_ctor_set(v___x_2126_, 1, v___x_2125_);
v___x_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2126_);
v___x_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2127_);
if (v_isShared_2105_ == 0)
{
lean_ctor_set(v___x_2104_, 1, v___x_2110_);
lean_ctor_set(v___x_2104_, 0, v___x_2128_);
v___x_2130_ = v___x_2104_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v___x_2128_);
lean_ctor_set(v_reuseFailAlloc_2136_, 1, v___x_2110_);
v___x_2130_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2134_; 
v___x_2131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2130_);
v___x_2132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2132_, 0, v___x_2131_);
lean_ctor_set(v___x_2132_, 1, v_snd_2102_);
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 0, v___x_2132_);
v___x_2134_ = v___x_2121_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v___x_2132_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
}
else
{
lean_object* v_a_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2146_; 
lean_del_object(v___x_2104_);
lean_dec(v_snd_2102_);
lean_dec_ref(v_c_2092_);
v_a_2139_ = lean_ctor_get(v___x_2119_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2119_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2141_ = v___x_2119_;
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_a_2139_);
lean_dec(v___x_2119_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2144_; 
if (v_isShared_2142_ == 0)
{
v___x_2144_ = v___x_2141_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_a_2139_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___boxed(lean_object* v_c_2151_, lean_object* v_x_2152_, lean_object* v_as_2153_, lean_object* v_sz_2154_, lean_object* v_i_2155_, lean_object* v_b_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
size_t v_sz_boxed_2159_; size_t v_i_boxed_2160_; lean_object* v_res_2161_; 
v_sz_boxed_2159_ = lean_unbox_usize(v_sz_2154_);
lean_dec(v_sz_2154_);
v_i_boxed_2160_ = lean_unbox_usize(v_i_2155_);
lean_dec(v_i_2155_);
v_res_2161_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(v_c_2151_, v_x_2152_, v_as_2153_, v_sz_boxed_2159_, v_i_boxed_2160_, v_b_2156_, v___y_2157_);
lean_dec(v___y_2157_);
lean_dec_ref(v_as_2153_);
return v_res_2161_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7(lean_object* v_c_2168_, lean_object* v_x_2169_, lean_object* v_as_2170_, size_t v_sz_2171_, size_t v_i_2172_, lean_object* v_b_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
uint8_t v___x_2185_; 
v___x_2185_ = lean_usize_dec_lt(v_i_2172_, v_sz_2171_);
if (v___x_2185_ == 0)
{
lean_object* v___x_2186_; 
lean_dec(v_x_2169_);
lean_dec_ref(v_c_2168_);
v___x_2186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2186_, 0, v_b_2173_);
return v___x_2186_;
}
else
{
lean_object* v_snd_2187_; lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2234_; 
v_snd_2187_ = lean_ctor_get(v_b_2173_, 1);
v_isSharedCheck_2234_ = !lean_is_exclusive(v_b_2173_);
if (v_isSharedCheck_2234_ == 0)
{
lean_object* v_unused_2235_; 
v_unused_2235_ = lean_ctor_get(v_b_2173_, 0);
lean_dec(v_unused_2235_);
v___x_2189_ = v_b_2173_;
v_isShared_2190_ = v_isSharedCheck_2234_;
goto v_resetjp_2188_;
}
else
{
lean_inc(v_snd_2187_);
lean_dec(v_b_2173_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2234_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v_p_2191_; lean_object* v_a_2192_; lean_object* v_p_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___f_2196_; uint8_t v___y_2198_; uint8_t v___x_2232_; 
v_p_2191_ = lean_ctor_get(v_c_2168_, 0);
v_a_2192_ = lean_array_uget_borrowed(v_as_2170_, v_i_2172_);
v_p_2193_ = lean_ctor_get(v_a_2192_, 0);
v___x_2194_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0);
v___x_2195_ = lean_box(0);
lean_inc(v_x_2169_);
lean_inc_ref(v_p_2193_);
v___f_2196_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2196_, 0, v_p_2193_);
lean_closure_set(v___f_2196_, 1, v___x_2194_);
lean_closure_set(v___f_2196_, 2, v_x_2169_);
v___x_2232_ = l_Int_Linear_instBEqPoly_beq(v_p_2191_, v_p_2193_);
if (v___x_2232_ == 0)
{
uint8_t v___x_2233_; 
v___x_2233_ = l_Int_Linear_Poly_isNegEq(v_p_2191_, v_p_2193_);
v___y_2198_ = v___x_2233_;
goto v___jp_2197_;
}
else
{
v___y_2198_ = v___x_2232_;
goto v___jp_2197_;
}
v___jp_2197_:
{
if (v___y_2198_ == 0)
{
lean_object* v___x_2199_; size_t v___x_2200_; size_t v___x_2201_; lean_object* v___x_2202_; 
lean_dec_ref(v___f_2196_);
lean_del_object(v___x_2189_);
lean_dec(v_snd_2187_);
v___x_2199_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___closed__1));
v___x_2200_ = ((size_t)1ULL);
v___x_2201_ = lean_usize_add(v_i_2172_, v___x_2200_);
v___x_2202_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(v_c_2168_, v_x_2169_, v_as_2170_, v_sz_2171_, v___x_2201_, v___x_2199_, v___y_2174_);
return v___x_2202_;
}
else
{
lean_object* v___x_2203_; lean_object* v___x_2204_; 
lean_dec(v_x_2169_);
v___x_2203_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2204_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2203_, v___f_2196_, v___y_2174_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v___x_2206_; uint8_t v_isShared_2207_; uint8_t v_isSharedCheck_2222_; 
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2222_ == 0)
{
lean_object* v_unused_2223_; 
v_unused_2223_ = lean_ctor_get(v___x_2204_, 0);
lean_dec(v_unused_2223_);
v___x_2206_ = v___x_2204_;
v_isShared_2207_ = v_isSharedCheck_2222_;
goto v_resetjp_2205_;
}
else
{
lean_dec(v___x_2204_);
v___x_2206_ = lean_box(0);
v_isShared_2207_ = v_isSharedCheck_2222_;
goto v_resetjp_2205_;
}
v_resetjp_2205_:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2215_; 
v___x_2208_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
lean_inc_ref(v_p_2191_);
v___x_2209_ = l_Int_Linear_Poly_addConst(v_p_2191_, v___x_2208_);
lean_inc(v_a_2192_);
v___x_2210_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_2210_, 0, v_c_2168_);
lean_ctor_set(v___x_2210_, 1, v_a_2192_);
v___x_2211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2209_);
lean_ctor_set(v___x_2211_, 1, v___x_2210_);
v___x_2212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2211_);
v___x_2213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2212_);
if (v_isShared_2190_ == 0)
{
lean_ctor_set(v___x_2189_, 1, v___x_2195_);
lean_ctor_set(v___x_2189_, 0, v___x_2213_);
v___x_2215_ = v___x_2189_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v___x_2213_);
lean_ctor_set(v_reuseFailAlloc_2221_, 1, v___x_2195_);
v___x_2215_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2219_; 
v___x_2216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2215_);
v___x_2217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2216_);
lean_ctor_set(v___x_2217_, 1, v_snd_2187_);
if (v_isShared_2207_ == 0)
{
lean_ctor_set(v___x_2206_, 0, v___x_2217_);
v___x_2219_ = v___x_2206_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v___x_2217_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
}
else
{
lean_object* v_a_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2231_; 
lean_del_object(v___x_2189_);
lean_dec(v_snd_2187_);
lean_dec_ref(v_c_2168_);
v_a_2224_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2226_ = v___x_2204_;
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_a_2224_);
lean_dec(v___x_2204_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2229_; 
if (v_isShared_2227_ == 0)
{
v___x_2229_ = v___x_2226_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_a_2224_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
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
lean_object* v_c_2236_ = _args[0];
lean_object* v_x_2237_ = _args[1];
lean_object* v_as_2238_ = _args[2];
lean_object* v_sz_2239_ = _args[3];
lean_object* v_i_2240_ = _args[4];
lean_object* v_b_2241_ = _args[5];
lean_object* v___y_2242_ = _args[6];
lean_object* v___y_2243_ = _args[7];
lean_object* v___y_2244_ = _args[8];
lean_object* v___y_2245_ = _args[9];
lean_object* v___y_2246_ = _args[10];
lean_object* v___y_2247_ = _args[11];
lean_object* v___y_2248_ = _args[12];
lean_object* v___y_2249_ = _args[13];
lean_object* v___y_2250_ = _args[14];
lean_object* v___y_2251_ = _args[15];
lean_object* v___y_2252_ = _args[16];
_start:
{
size_t v_sz_boxed_2253_; size_t v_i_boxed_2254_; lean_object* v_res_2255_; 
v_sz_boxed_2253_ = lean_unbox_usize(v_sz_2239_);
lean_dec(v_sz_2239_);
v_i_boxed_2254_ = lean_unbox_usize(v_i_2240_);
lean_dec(v_i_2240_);
v_res_2255_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7(v_c_2236_, v_x_2237_, v_as_2238_, v_sz_boxed_2253_, v_i_boxed_2254_, v_b_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec(v___y_2242_);
lean_dec_ref(v_as_2238_);
return v_res_2255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(lean_object* v_c_2262_, lean_object* v_x_2263_, lean_object* v_as_2264_, size_t v_sz_2265_, size_t v_i_2266_, lean_object* v_b_2267_, lean_object* v___y_2268_){
_start:
{
uint8_t v___x_2270_; 
v___x_2270_ = lean_usize_dec_lt(v_i_2266_, v_sz_2265_);
if (v___x_2270_ == 0)
{
lean_object* v___x_2271_; 
lean_dec(v_x_2263_);
lean_dec_ref(v_c_2262_);
v___x_2271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2271_, 0, v_b_2267_);
return v___x_2271_;
}
else
{
lean_object* v_snd_2272_; lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2320_; 
v_snd_2272_ = lean_ctor_get(v_b_2267_, 1);
v_isSharedCheck_2320_ = !lean_is_exclusive(v_b_2267_);
if (v_isSharedCheck_2320_ == 0)
{
lean_object* v_unused_2321_; 
v_unused_2321_ = lean_ctor_get(v_b_2267_, 0);
lean_dec(v_unused_2321_);
v___x_2274_ = v_b_2267_;
v_isShared_2275_ = v_isSharedCheck_2320_;
goto v_resetjp_2273_;
}
else
{
lean_inc(v_snd_2272_);
lean_dec(v_b_2267_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2320_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v_p_2276_; lean_object* v_a_2277_; lean_object* v_p_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___f_2281_; uint8_t v___y_2283_; uint8_t v___x_2318_; 
v_p_2276_ = lean_ctor_get(v_c_2262_, 0);
v_a_2277_ = lean_array_uget_borrowed(v_as_2264_, v_i_2266_);
v_p_2278_ = lean_ctor_get(v_a_2277_, 0);
v___x_2279_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0);
v___x_2280_ = lean_box(0);
lean_inc(v_x_2263_);
lean_inc_ref(v_p_2278_);
v___f_2281_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2281_, 0, v_p_2278_);
lean_closure_set(v___f_2281_, 1, v___x_2279_);
lean_closure_set(v___f_2281_, 2, v_x_2263_);
v___x_2318_ = l_Int_Linear_instBEqPoly_beq(v_p_2276_, v_p_2278_);
if (v___x_2318_ == 0)
{
uint8_t v___x_2319_; 
v___x_2319_ = l_Int_Linear_Poly_isNegEq(v_p_2276_, v_p_2278_);
v___y_2283_ = v___x_2319_;
goto v___jp_2282_;
}
else
{
v___y_2283_ = v___x_2318_;
goto v___jp_2282_;
}
v___jp_2282_:
{
if (v___y_2283_ == 0)
{
lean_object* v___x_2284_; size_t v___x_2285_; size_t v___x_2286_; 
lean_dec_ref(v___f_2281_);
lean_del_object(v___x_2274_);
lean_dec(v_snd_2272_);
v___x_2284_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg___closed__1));
v___x_2285_ = ((size_t)1ULL);
v___x_2286_ = lean_usize_add(v_i_2266_, v___x_2285_);
v_i_2266_ = v___x_2286_;
v_b_2267_ = v___x_2284_;
goto _start;
}
else
{
lean_object* v___x_2288_; lean_object* v___x_2289_; 
lean_dec(v_x_2263_);
v___x_2288_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2289_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2288_, v___f_2281_, v___y_2268_);
if (lean_obj_tag(v___x_2289_) == 0)
{
lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2308_; 
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2289_);
if (v_isSharedCheck_2308_ == 0)
{
lean_object* v_unused_2309_; 
v_unused_2309_ = lean_ctor_get(v___x_2289_, 0);
lean_dec(v_unused_2309_);
v___x_2291_ = v___x_2289_;
v_isShared_2292_ = v_isSharedCheck_2308_;
goto v_resetjp_2290_;
}
else
{
lean_dec(v___x_2289_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2308_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2300_; 
v___x_2293_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
lean_inc_ref(v_p_2276_);
v___x_2294_ = l_Int_Linear_Poly_addConst(v_p_2276_, v___x_2293_);
lean_inc(v_a_2277_);
v___x_2295_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_2295_, 0, v_c_2262_);
lean_ctor_set(v___x_2295_, 1, v_a_2277_);
v___x_2296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2294_);
lean_ctor_set(v___x_2296_, 1, v___x_2295_);
v___x_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2296_);
v___x_2298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2297_);
if (v_isShared_2275_ == 0)
{
lean_ctor_set(v___x_2274_, 1, v___x_2280_);
lean_ctor_set(v___x_2274_, 0, v___x_2298_);
v___x_2300_ = v___x_2274_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v___x_2298_);
lean_ctor_set(v_reuseFailAlloc_2307_, 1, v___x_2280_);
v___x_2300_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2305_; 
v___x_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2300_);
v___x_2302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2302_, 0, v___x_2301_);
v___x_2303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2302_);
lean_ctor_set(v___x_2303_, 1, v_snd_2272_);
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 0, v___x_2303_);
v___x_2305_ = v___x_2291_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v___x_2303_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
}
}
else
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2317_; 
lean_del_object(v___x_2274_);
lean_dec(v_snd_2272_);
lean_dec_ref(v_c_2262_);
v_a_2310_ = lean_ctor_get(v___x_2289_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2289_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2312_ = v___x_2289_;
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2289_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2315_; 
if (v_isShared_2313_ == 0)
{
v___x_2315_ = v___x_2312_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_a_2310_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg___boxed(lean_object* v_c_2322_, lean_object* v_x_2323_, lean_object* v_as_2324_, lean_object* v_sz_2325_, lean_object* v_i_2326_, lean_object* v_b_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_){
_start:
{
size_t v_sz_boxed_2330_; size_t v_i_boxed_2331_; lean_object* v_res_2332_; 
v_sz_boxed_2330_ = lean_unbox_usize(v_sz_2325_);
lean_dec(v_sz_2325_);
v_i_boxed_2331_ = lean_unbox_usize(v_i_2326_);
lean_dec(v_i_2326_);
v_res_2332_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(v_c_2322_, v_x_2323_, v_as_2324_, v_sz_boxed_2330_, v_i_boxed_2331_, v_b_2327_, v___y_2328_);
lean_dec(v___y_2328_);
lean_dec_ref(v_as_2324_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9(lean_object* v_c_2336_, lean_object* v_x_2337_, lean_object* v_as_2338_, size_t v_sz_2339_, size_t v_i_2340_, lean_object* v_b_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
uint8_t v___x_2353_; 
v___x_2353_ = lean_usize_dec_lt(v_i_2340_, v_sz_2339_);
if (v___x_2353_ == 0)
{
lean_object* v___x_2354_; 
lean_dec(v_x_2337_);
lean_dec_ref(v_c_2336_);
v___x_2354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2354_, 0, v_b_2341_);
return v___x_2354_;
}
else
{
lean_object* v_snd_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2403_; 
v_snd_2355_ = lean_ctor_get(v_b_2341_, 1);
v_isSharedCheck_2403_ = !lean_is_exclusive(v_b_2341_);
if (v_isSharedCheck_2403_ == 0)
{
lean_object* v_unused_2404_; 
v_unused_2404_ = lean_ctor_get(v_b_2341_, 0);
lean_dec(v_unused_2404_);
v___x_2357_ = v_b_2341_;
v_isShared_2358_ = v_isSharedCheck_2403_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_snd_2355_);
lean_dec(v_b_2341_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2403_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v_p_2359_; lean_object* v_a_2360_; lean_object* v_p_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___f_2364_; uint8_t v___y_2366_; uint8_t v___x_2401_; 
v_p_2359_ = lean_ctor_get(v_c_2336_, 0);
v_a_2360_ = lean_array_uget_borrowed(v_as_2338_, v_i_2340_);
v_p_2361_ = lean_ctor_get(v_a_2360_, 0);
v___x_2362_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0);
v___x_2363_ = lean_box(0);
lean_inc(v_x_2337_);
lean_inc_ref(v_p_2361_);
v___f_2364_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 4, 3);
lean_closure_set(v___f_2364_, 0, v_p_2361_);
lean_closure_set(v___f_2364_, 1, v___x_2362_);
lean_closure_set(v___f_2364_, 2, v_x_2337_);
v___x_2401_ = l_Int_Linear_instBEqPoly_beq(v_p_2359_, v_p_2361_);
if (v___x_2401_ == 0)
{
uint8_t v___x_2402_; 
v___x_2402_ = l_Int_Linear_Poly_isNegEq(v_p_2359_, v_p_2361_);
v___y_2366_ = v___x_2402_;
goto v___jp_2365_;
}
else
{
v___y_2366_ = v___x_2401_;
goto v___jp_2365_;
}
v___jp_2365_:
{
if (v___y_2366_ == 0)
{
lean_object* v___x_2367_; size_t v___x_2368_; size_t v___x_2369_; lean_object* v___x_2370_; 
lean_dec_ref(v___f_2364_);
lean_del_object(v___x_2357_);
lean_dec(v_snd_2355_);
v___x_2367_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9___closed__0));
v___x_2368_ = ((size_t)1ULL);
v___x_2369_ = lean_usize_add(v_i_2340_, v___x_2368_);
v___x_2370_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(v_c_2336_, v_x_2337_, v_as_2338_, v_sz_2339_, v___x_2369_, v___x_2367_, v___y_2342_);
return v___x_2370_;
}
else
{
lean_object* v___x_2371_; lean_object* v___x_2372_; 
lean_dec(v_x_2337_);
v___x_2371_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2372_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2371_, v___f_2364_, v___y_2342_);
if (lean_obj_tag(v___x_2372_) == 0)
{
lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2391_; 
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2391_ == 0)
{
lean_object* v_unused_2392_; 
v_unused_2392_ = lean_ctor_get(v___x_2372_, 0);
lean_dec(v_unused_2392_);
v___x_2374_ = v___x_2372_;
v_isShared_2375_ = v_isSharedCheck_2391_;
goto v_resetjp_2373_;
}
else
{
lean_dec(v___x_2372_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2391_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2383_; 
v___x_2376_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
lean_inc_ref(v_p_2359_);
v___x_2377_ = l_Int_Linear_Poly_addConst(v_p_2359_, v___x_2376_);
lean_inc(v_a_2360_);
v___x_2378_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_2378_, 0, v_c_2336_);
lean_ctor_set(v___x_2378_, 1, v_a_2360_);
v___x_2379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2379_, 0, v___x_2377_);
lean_ctor_set(v___x_2379_, 1, v___x_2378_);
v___x_2380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2380_, 0, v___x_2379_);
v___x_2381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2381_, 0, v___x_2380_);
if (v_isShared_2358_ == 0)
{
lean_ctor_set(v___x_2357_, 1, v___x_2363_);
lean_ctor_set(v___x_2357_, 0, v___x_2381_);
v___x_2383_ = v___x_2357_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v___x_2381_);
lean_ctor_set(v_reuseFailAlloc_2390_, 1, v___x_2363_);
v___x_2383_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2388_; 
v___x_2384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2384_, 0, v___x_2383_);
v___x_2385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2385_, 0, v___x_2384_);
v___x_2386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2385_);
lean_ctor_set(v___x_2386_, 1, v_snd_2355_);
if (v_isShared_2375_ == 0)
{
lean_ctor_set(v___x_2374_, 0, v___x_2386_);
v___x_2388_ = v___x_2374_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v___x_2386_);
v___x_2388_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
return v___x_2388_;
}
}
}
}
else
{
lean_object* v_a_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2400_; 
lean_del_object(v___x_2357_);
lean_dec(v_snd_2355_);
lean_dec_ref(v_c_2336_);
v_a_2393_ = lean_ctor_get(v___x_2372_, 0);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___x_2372_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2395_ = v___x_2372_;
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_a_2393_);
lean_dec(v___x_2372_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2400_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2398_; 
if (v_isShared_2396_ == 0)
{
v___x_2398_ = v___x_2395_;
goto v_reusejp_2397_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_a_2393_);
v___x_2398_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2397_;
}
v_reusejp_2397_:
{
return v___x_2398_;
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
lean_object* v_c_2405_ = _args[0];
lean_object* v_x_2406_ = _args[1];
lean_object* v_as_2407_ = _args[2];
lean_object* v_sz_2408_ = _args[3];
lean_object* v_i_2409_ = _args[4];
lean_object* v_b_2410_ = _args[5];
lean_object* v___y_2411_ = _args[6];
lean_object* v___y_2412_ = _args[7];
lean_object* v___y_2413_ = _args[8];
lean_object* v___y_2414_ = _args[9];
lean_object* v___y_2415_ = _args[10];
lean_object* v___y_2416_ = _args[11];
lean_object* v___y_2417_ = _args[12];
lean_object* v___y_2418_ = _args[13];
lean_object* v___y_2419_ = _args[14];
lean_object* v___y_2420_ = _args[15];
lean_object* v___y_2421_ = _args[16];
_start:
{
size_t v_sz_boxed_2422_; size_t v_i_boxed_2423_; lean_object* v_res_2424_; 
v_sz_boxed_2422_ = lean_unbox_usize(v_sz_2408_);
lean_dec(v_sz_2408_);
v_i_boxed_2423_ = lean_unbox_usize(v_i_2409_);
lean_dec(v_i_2409_);
v_res_2424_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9(v_c_2405_, v_x_2406_, v_as_2407_, v_sz_boxed_2422_, v_i_boxed_2423_, v_b_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
lean_dec(v___y_2420_);
lean_dec_ref(v___y_2419_);
lean_dec(v___y_2418_);
lean_dec_ref(v___y_2417_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec(v___y_2412_);
lean_dec(v___y_2411_);
lean_dec_ref(v_as_2407_);
return v_res_2424_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(lean_object* v_c_2425_, lean_object* v_x_2426_, lean_object* v_inh_2427_, lean_object* v_n_2428_, lean_object* v_b_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_){
_start:
{
if (lean_obj_tag(v_n_2428_) == 0)
{
lean_object* v_cs_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2475_; 
v_cs_2441_ = lean_ctor_get(v_n_2428_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v_n_2428_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2443_ = v_n_2428_;
v_isShared_2444_ = v_isSharedCheck_2475_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_cs_2441_);
lean_dec(v_n_2428_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2475_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; size_t v_sz_2447_; size_t v___x_2448_; lean_object* v___x_2449_; 
v___x_2445_ = lean_box(0);
v___x_2446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2446_, 0, v___x_2445_);
lean_ctor_set(v___x_2446_, 1, v_b_2429_);
v_sz_2447_ = lean_array_size(v_cs_2441_);
v___x_2448_ = ((size_t)0ULL);
v___x_2449_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8(v_c_2425_, v_x_2426_, v_inh_2427_, v_cs_2441_, v_sz_2447_, v___x_2448_, v___x_2446_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
lean_dec_ref(v_cs_2441_);
if (lean_obj_tag(v___x_2449_) == 0)
{
lean_object* v_a_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2466_; 
v_a_2450_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2452_ = v___x_2449_;
v_isShared_2453_ = v_isSharedCheck_2466_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_a_2450_);
lean_dec(v___x_2449_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2466_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v_fst_2454_; 
v_fst_2454_ = lean_ctor_get(v_a_2450_, 0);
if (lean_obj_tag(v_fst_2454_) == 0)
{
lean_object* v_snd_2455_; lean_object* v___x_2457_; 
v_snd_2455_ = lean_ctor_get(v_a_2450_, 1);
lean_inc(v_snd_2455_);
lean_dec(v_a_2450_);
if (v_isShared_2444_ == 0)
{
lean_ctor_set_tag(v___x_2443_, 1);
lean_ctor_set(v___x_2443_, 0, v_snd_2455_);
v___x_2457_ = v___x_2443_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_snd_2455_);
v___x_2457_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
lean_object* v___x_2459_; 
if (v_isShared_2453_ == 0)
{
lean_ctor_set(v___x_2452_, 0, v___x_2457_);
v___x_2459_ = v___x_2452_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v___x_2457_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
}
else
{
lean_object* v_val_2462_; lean_object* v___x_2464_; 
lean_inc_ref(v_fst_2454_);
lean_dec(v_a_2450_);
lean_del_object(v___x_2443_);
v_val_2462_ = lean_ctor_get(v_fst_2454_, 0);
lean_inc(v_val_2462_);
lean_dec_ref(v_fst_2454_);
if (v_isShared_2453_ == 0)
{
lean_ctor_set(v___x_2452_, 0, v_val_2462_);
v___x_2464_ = v___x_2452_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_val_2462_);
v___x_2464_ = v_reuseFailAlloc_2465_;
goto v_reusejp_2463_;
}
v_reusejp_2463_:
{
return v___x_2464_;
}
}
}
}
else
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2474_; 
lean_del_object(v___x_2443_);
v_a_2467_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2469_ = v___x_2449_;
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2449_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2472_; 
if (v_isShared_2470_ == 0)
{
v___x_2472_ = v___x_2469_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_a_2467_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
}
}
else
{
lean_object* v_vs_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2510_; 
v_vs_2476_ = lean_ctor_get(v_n_2428_, 0);
v_isSharedCheck_2510_ = !lean_is_exclusive(v_n_2428_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2478_ = v_n_2428_;
v_isShared_2479_ = v_isSharedCheck_2510_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_vs_2476_);
lean_dec(v_n_2428_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2510_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2480_; lean_object* v___x_2481_; size_t v_sz_2482_; size_t v___x_2483_; lean_object* v___x_2484_; 
v___x_2480_ = lean_box(0);
v___x_2481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2480_);
lean_ctor_set(v___x_2481_, 1, v_b_2429_);
v_sz_2482_ = lean_array_size(v_vs_2476_);
v___x_2483_ = ((size_t)0ULL);
v___x_2484_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9(v_c_2425_, v_x_2426_, v_vs_2476_, v_sz_2482_, v___x_2483_, v___x_2481_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
lean_dec_ref(v_vs_2476_);
if (lean_obj_tag(v___x_2484_) == 0)
{
lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2501_; 
v_a_2485_ = lean_ctor_get(v___x_2484_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2484_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2487_ = v___x_2484_;
v_isShared_2488_ = v_isSharedCheck_2501_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_dec(v___x_2484_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2501_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v_fst_2489_; 
v_fst_2489_ = lean_ctor_get(v_a_2485_, 0);
if (lean_obj_tag(v_fst_2489_) == 0)
{
lean_object* v_snd_2490_; lean_object* v___x_2492_; 
v_snd_2490_ = lean_ctor_get(v_a_2485_, 1);
lean_inc(v_snd_2490_);
lean_dec(v_a_2485_);
if (v_isShared_2479_ == 0)
{
lean_ctor_set(v___x_2478_, 0, v_snd_2490_);
v___x_2492_ = v___x_2478_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2496_; 
v_reuseFailAlloc_2496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2496_, 0, v_snd_2490_);
v___x_2492_ = v_reuseFailAlloc_2496_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
lean_object* v___x_2494_; 
if (v_isShared_2488_ == 0)
{
lean_ctor_set(v___x_2487_, 0, v___x_2492_);
v___x_2494_ = v___x_2487_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v___x_2492_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
}
}
}
else
{
lean_object* v_val_2497_; lean_object* v___x_2499_; 
lean_inc_ref(v_fst_2489_);
lean_dec(v_a_2485_);
lean_del_object(v___x_2478_);
v_val_2497_ = lean_ctor_get(v_fst_2489_, 0);
lean_inc(v_val_2497_);
lean_dec_ref(v_fst_2489_);
if (v_isShared_2488_ == 0)
{
lean_ctor_set(v___x_2487_, 0, v_val_2497_);
v___x_2499_ = v___x_2487_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_val_2497_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
return v___x_2499_;
}
}
}
}
else
{
lean_object* v_a_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2509_; 
lean_del_object(v___x_2478_);
v_a_2502_ = lean_ctor_get(v___x_2484_, 0);
v_isSharedCheck_2509_ = !lean_is_exclusive(v___x_2484_);
if (v_isSharedCheck_2509_ == 0)
{
v___x_2504_ = v___x_2484_;
v_isShared_2505_ = v_isSharedCheck_2509_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_a_2502_);
lean_dec(v___x_2484_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2509_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2507_; 
if (v_isShared_2505_ == 0)
{
v___x_2507_ = v___x_2504_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v_a_2502_);
v___x_2507_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
return v___x_2507_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8(lean_object* v_c_2511_, lean_object* v_x_2512_, lean_object* v_inh_2513_, lean_object* v_as_2514_, size_t v_sz_2515_, size_t v_i_2516_, lean_object* v_b_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_){
_start:
{
uint8_t v___x_2529_; 
v___x_2529_ = lean_usize_dec_lt(v_i_2516_, v_sz_2515_);
if (v___x_2529_ == 0)
{
lean_object* v___x_2530_; 
lean_dec(v_x_2512_);
lean_dec_ref(v_c_2511_);
v___x_2530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2530_, 0, v_b_2517_);
return v___x_2530_;
}
else
{
lean_object* v_snd_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2565_; 
v_snd_2531_ = lean_ctor_get(v_b_2517_, 1);
v_isSharedCheck_2565_ = !lean_is_exclusive(v_b_2517_);
if (v_isSharedCheck_2565_ == 0)
{
lean_object* v_unused_2566_; 
v_unused_2566_ = lean_ctor_get(v_b_2517_, 0);
lean_dec(v_unused_2566_);
v___x_2533_ = v_b_2517_;
v_isShared_2534_ = v_isSharedCheck_2565_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_snd_2531_);
lean_dec(v_b_2517_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2565_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v_a_2535_; lean_object* v___x_2536_; 
v_a_2535_ = lean_array_uget_borrowed(v_as_2514_, v_i_2516_);
lean_inc(v_snd_2531_);
lean_inc(v_a_2535_);
lean_inc(v_x_2512_);
lean_inc_ref(v_c_2511_);
v___x_2536_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(v_c_2511_, v_x_2512_, v_inh_2513_, v_a_2535_, v_snd_2531_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_object* v_a_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2556_; 
v_a_2537_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2539_ = v___x_2536_;
v_isShared_2540_ = v_isSharedCheck_2556_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_a_2537_);
lean_dec(v___x_2536_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2556_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
if (lean_obj_tag(v_a_2537_) == 0)
{
lean_object* v___x_2541_; lean_object* v___x_2543_; 
lean_dec(v_x_2512_);
lean_dec_ref(v_c_2511_);
v___x_2541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2541_, 0, v_a_2537_);
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 0, v___x_2541_);
v___x_2543_ = v___x_2533_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v___x_2541_);
lean_ctor_set(v_reuseFailAlloc_2547_, 1, v_snd_2531_);
v___x_2543_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
lean_object* v___x_2545_; 
if (v_isShared_2540_ == 0)
{
lean_ctor_set(v___x_2539_, 0, v___x_2543_);
v___x_2545_ = v___x_2539_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v___x_2543_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
else
{
lean_object* v_a_2548_; lean_object* v___x_2549_; lean_object* v___x_2551_; 
lean_del_object(v___x_2539_);
lean_dec(v_snd_2531_);
v_a_2548_ = lean_ctor_get(v_a_2537_, 0);
lean_inc(v_a_2548_);
lean_dec_ref(v_a_2537_);
v___x_2549_ = lean_box(0);
if (v_isShared_2534_ == 0)
{
lean_ctor_set(v___x_2533_, 1, v_a_2548_);
lean_ctor_set(v___x_2533_, 0, v___x_2549_);
v___x_2551_ = v___x_2533_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v___x_2549_);
lean_ctor_set(v_reuseFailAlloc_2555_, 1, v_a_2548_);
v___x_2551_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
size_t v___x_2552_; size_t v___x_2553_; 
v___x_2552_ = ((size_t)1ULL);
v___x_2553_ = lean_usize_add(v_i_2516_, v___x_2552_);
v_i_2516_ = v___x_2553_;
v_b_2517_ = v___x_2551_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2564_; 
lean_del_object(v___x_2533_);
lean_dec(v_snd_2531_);
lean_dec(v_x_2512_);
lean_dec_ref(v_c_2511_);
v_a_2557_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2559_ = v___x_2536_;
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_a_2557_);
lean_dec(v___x_2536_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2562_; 
if (v_isShared_2560_ == 0)
{
v___x_2562_ = v___x_2559_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_a_2557_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8___boxed(lean_object** _args){
lean_object* v_c_2567_ = _args[0];
lean_object* v_x_2568_ = _args[1];
lean_object* v_inh_2569_ = _args[2];
lean_object* v_as_2570_ = _args[3];
lean_object* v_sz_2571_ = _args[4];
lean_object* v_i_2572_ = _args[5];
lean_object* v_b_2573_ = _args[6];
lean_object* v___y_2574_ = _args[7];
lean_object* v___y_2575_ = _args[8];
lean_object* v___y_2576_ = _args[9];
lean_object* v___y_2577_ = _args[10];
lean_object* v___y_2578_ = _args[11];
lean_object* v___y_2579_ = _args[12];
lean_object* v___y_2580_ = _args[13];
lean_object* v___y_2581_ = _args[14];
lean_object* v___y_2582_ = _args[15];
lean_object* v___y_2583_ = _args[16];
lean_object* v___y_2584_ = _args[17];
_start:
{
size_t v_sz_boxed_2585_; size_t v_i_boxed_2586_; lean_object* v_res_2587_; 
v_sz_boxed_2585_ = lean_unbox_usize(v_sz_2571_);
lean_dec(v_sz_2571_);
v_i_boxed_2586_ = lean_unbox_usize(v_i_2572_);
lean_dec(v_i_2572_);
v_res_2587_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8(v_c_2567_, v_x_2568_, v_inh_2569_, v_as_2570_, v_sz_boxed_2585_, v_i_boxed_2586_, v_b_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
lean_dec(v___y_2583_);
lean_dec_ref(v___y_2582_);
lean_dec(v___y_2581_);
lean_dec_ref(v___y_2580_);
lean_dec(v___y_2579_);
lean_dec_ref(v___y_2578_);
lean_dec(v___y_2577_);
lean_dec_ref(v___y_2576_);
lean_dec(v___y_2575_);
lean_dec(v___y_2574_);
lean_dec_ref(v_as_2570_);
lean_dec_ref(v_inh_2569_);
return v_res_2587_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6___boxed(lean_object* v_c_2588_, lean_object* v_x_2589_, lean_object* v_inh_2590_, lean_object* v_n_2591_, lean_object* v_b_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_){
_start:
{
lean_object* v_res_2604_; 
v_res_2604_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(v_c_2588_, v_x_2589_, v_inh_2590_, v_n_2591_, v_b_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
lean_dec(v___y_2602_);
lean_dec_ref(v___y_2601_);
lean_dec(v___y_2600_);
lean_dec_ref(v___y_2599_);
lean_dec(v___y_2598_);
lean_dec_ref(v___y_2597_);
lean_dec(v___y_2596_);
lean_dec_ref(v___y_2595_);
lean_dec(v___y_2594_);
lean_dec(v___y_2593_);
lean_dec_ref(v_inh_2590_);
return v_res_2604_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2(lean_object* v_c_2605_, lean_object* v_x_2606_, lean_object* v_t_2607_, lean_object* v_init_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_){
_start:
{
lean_object* v_root_2620_; lean_object* v_tail_2621_; lean_object* v___x_2622_; 
v_root_2620_ = lean_ctor_get(v_t_2607_, 0);
lean_inc_ref(v_root_2620_);
v_tail_2621_ = lean_ctor_get(v_t_2607_, 1);
lean_inc_ref(v_tail_2621_);
lean_dec_ref(v_t_2607_);
lean_inc_ref(v_init_2608_);
lean_inc(v_x_2606_);
lean_inc_ref(v_c_2605_);
v___x_2622_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(v_c_2605_, v_x_2606_, v_init_2608_, v_root_2620_, v_init_2608_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
lean_dec_ref(v_init_2608_);
if (lean_obj_tag(v___x_2622_) == 0)
{
lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2659_; 
v_a_2623_ = lean_ctor_get(v___x_2622_, 0);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2622_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2625_ = v___x_2622_;
v_isShared_2626_ = v_isSharedCheck_2659_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_a_2623_);
lean_dec(v___x_2622_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2659_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
if (lean_obj_tag(v_a_2623_) == 0)
{
lean_object* v_a_2627_; lean_object* v___x_2629_; 
lean_dec_ref(v_tail_2621_);
lean_dec(v_x_2606_);
lean_dec_ref(v_c_2605_);
v_a_2627_ = lean_ctor_get(v_a_2623_, 0);
lean_inc(v_a_2627_);
lean_dec_ref(v_a_2623_);
if (v_isShared_2626_ == 0)
{
lean_ctor_set(v___x_2625_, 0, v_a_2627_);
v___x_2629_ = v___x_2625_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_a_2627_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
else
{
lean_object* v_a_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; size_t v_sz_2634_; size_t v___x_2635_; lean_object* v___x_2636_; 
lean_del_object(v___x_2625_);
v_a_2631_ = lean_ctor_get(v_a_2623_, 0);
lean_inc(v_a_2631_);
lean_dec_ref(v_a_2623_);
v___x_2632_ = lean_box(0);
v___x_2633_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2633_, 0, v___x_2632_);
lean_ctor_set(v___x_2633_, 1, v_a_2631_);
v_sz_2634_ = lean_array_size(v_tail_2621_);
v___x_2635_ = ((size_t)0ULL);
v___x_2636_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7(v_c_2605_, v_x_2606_, v_tail_2621_, v_sz_2634_, v___x_2635_, v___x_2633_, v___y_2609_, v___y_2610_, v___y_2611_, v___y_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
lean_dec_ref(v_tail_2621_);
if (lean_obj_tag(v___x_2636_) == 0)
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2650_; 
v_a_2637_ = lean_ctor_get(v___x_2636_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2639_ = v___x_2636_;
v_isShared_2640_ = v_isSharedCheck_2650_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___x_2636_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2650_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v_fst_2641_; 
v_fst_2641_ = lean_ctor_get(v_a_2637_, 0);
if (lean_obj_tag(v_fst_2641_) == 0)
{
lean_object* v_snd_2642_; lean_object* v___x_2644_; 
v_snd_2642_ = lean_ctor_get(v_a_2637_, 1);
lean_inc(v_snd_2642_);
lean_dec(v_a_2637_);
if (v_isShared_2640_ == 0)
{
lean_ctor_set(v___x_2639_, 0, v_snd_2642_);
v___x_2644_ = v___x_2639_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v_snd_2642_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
else
{
lean_object* v_val_2646_; lean_object* v___x_2648_; 
lean_inc_ref(v_fst_2641_);
lean_dec(v_a_2637_);
v_val_2646_ = lean_ctor_get(v_fst_2641_, 0);
lean_inc(v_val_2646_);
lean_dec_ref(v_fst_2641_);
if (v_isShared_2640_ == 0)
{
lean_ctor_set(v___x_2639_, 0, v_val_2646_);
v___x_2648_ = v___x_2639_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_val_2646_);
v___x_2648_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
return v___x_2648_;
}
}
}
}
else
{
lean_object* v_a_2651_; lean_object* v___x_2653_; uint8_t v_isShared_2654_; uint8_t v_isSharedCheck_2658_; 
v_a_2651_ = lean_ctor_get(v___x_2636_, 0);
v_isSharedCheck_2658_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2658_ == 0)
{
v___x_2653_ = v___x_2636_;
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
else
{
lean_inc(v_a_2651_);
lean_dec(v___x_2636_);
v___x_2653_ = lean_box(0);
v_isShared_2654_ = v_isSharedCheck_2658_;
goto v_resetjp_2652_;
}
v_resetjp_2652_:
{
lean_object* v___x_2656_; 
if (v_isShared_2654_ == 0)
{
v___x_2656_ = v___x_2653_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_a_2651_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
}
}
}
}
else
{
lean_object* v_a_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2667_; 
lean_dec_ref(v_tail_2621_);
lean_dec(v_x_2606_);
lean_dec_ref(v_c_2605_);
v_a_2660_ = lean_ctor_get(v___x_2622_, 0);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2622_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2662_ = v___x_2622_;
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_a_2660_);
lean_dec(v___x_2622_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2665_; 
if (v_isShared_2663_ == 0)
{
v___x_2665_ = v___x_2662_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v_a_2660_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
return v___x_2665_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2___boxed(lean_object* v_c_2668_, lean_object* v_x_2669_, lean_object* v_t_2670_, lean_object* v_init_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_){
_start:
{
lean_object* v_res_2683_; 
v_res_2683_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2(v_c_2668_, v_x_2669_, v_t_2670_, v_init_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
lean_dec(v___y_2677_);
lean_dec_ref(v___y_2676_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
lean_dec(v___y_2673_);
lean_dec(v___y_2672_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(lean_object* v_x_2684_, lean_object* v_c_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_){
_start:
{
lean_object* v___x_2697_; 
v___x_2697_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2686_, v_a_2694_);
if (lean_obj_tag(v___x_2697_) == 0)
{
lean_object* v_a_2698_; lean_object* v___y_2700_; lean_object* v_diseqs_2725_; lean_object* v_size_2726_; lean_object* v___x_2727_; uint8_t v___x_2728_; 
v_a_2698_ = lean_ctor_get(v___x_2697_, 0);
lean_inc(v_a_2698_);
lean_dec_ref(v___x_2697_);
v_diseqs_2725_ = lean_ctor_get(v_a_2698_, 9);
lean_inc_ref(v_diseqs_2725_);
lean_dec(v_a_2698_);
v_size_2726_ = lean_ctor_get(v_diseqs_2725_, 2);
v___x_2727_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0);
v___x_2728_ = lean_nat_dec_lt(v_x_2684_, v_size_2726_);
if (v___x_2728_ == 0)
{
lean_object* v___x_2729_; 
lean_dec_ref(v_diseqs_2725_);
v___x_2729_ = l_outOfBounds___redArg(v___x_2727_);
v___y_2700_ = v___x_2729_;
goto v___jp_2699_;
}
else
{
lean_object* v___x_2730_; 
v___x_2730_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2727_, v_diseqs_2725_, v_x_2684_);
v___y_2700_ = v___x_2730_;
goto v___jp_2699_;
}
v___jp_2699_:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2701_ = lean_box(0);
v___x_2702_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___closed__0));
v___x_2703_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2(v_c_2685_, v_x_2684_, v___y_2700_, v___x_2702_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_);
if (lean_obj_tag(v___x_2703_) == 0)
{
lean_object* v_a_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2716_; 
v_a_2704_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2706_ = v___x_2703_;
v_isShared_2707_ = v_isSharedCheck_2716_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_a_2704_);
lean_dec(v___x_2703_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2716_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v_fst_2708_; 
v_fst_2708_ = lean_ctor_get(v_a_2704_, 0);
lean_inc(v_fst_2708_);
lean_dec(v_a_2704_);
if (lean_obj_tag(v_fst_2708_) == 0)
{
lean_object* v___x_2710_; 
if (v_isShared_2707_ == 0)
{
lean_ctor_set(v___x_2706_, 0, v___x_2701_);
v___x_2710_ = v___x_2706_;
goto v_reusejp_2709_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v___x_2701_);
v___x_2710_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2709_;
}
v_reusejp_2709_:
{
return v___x_2710_;
}
}
else
{
lean_object* v_val_2712_; lean_object* v___x_2714_; 
v_val_2712_ = lean_ctor_get(v_fst_2708_, 0);
lean_inc(v_val_2712_);
lean_dec_ref(v_fst_2708_);
if (v_isShared_2707_ == 0)
{
lean_ctor_set(v___x_2706_, 0, v_val_2712_);
v___x_2714_ = v___x_2706_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v_val_2712_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
return v___x_2714_;
}
}
}
}
else
{
lean_object* v_a_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2724_; 
v_a_2717_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2724_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2724_ == 0)
{
v___x_2719_ = v___x_2703_;
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_a_2717_);
lean_dec(v___x_2703_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2724_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v___x_2722_; 
if (v_isShared_2720_ == 0)
{
v___x_2722_ = v___x_2719_;
goto v_reusejp_2721_;
}
else
{
lean_object* v_reuseFailAlloc_2723_; 
v_reuseFailAlloc_2723_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_a_2717_);
v___x_2722_ = v_reuseFailAlloc_2723_;
goto v_reusejp_2721_;
}
v_reusejp_2721_:
{
return v___x_2722_;
}
}
}
}
}
else
{
lean_object* v_a_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2738_; 
lean_dec_ref(v_c_2685_);
lean_dec(v_x_2684_);
v_a_2731_ = lean_ctor_get(v___x_2697_, 0);
v_isSharedCheck_2738_ = !lean_is_exclusive(v___x_2697_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2733_ = v___x_2697_;
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_a_2731_);
lean_dec(v___x_2697_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v___x_2736_; 
if (v_isShared_2734_ == 0)
{
v___x_2736_ = v___x_2733_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v_a_2731_);
v___x_2736_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
return v___x_2736_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f___boxed(lean_object* v_x_2739_, lean_object* v_c_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(v_x_2739_, v_c_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_);
lean_dec(v_a_2750_);
lean_dec_ref(v_a_2749_);
lean_dec(v_a_2748_);
lean_dec_ref(v_a_2747_);
lean_dec(v_a_2746_);
lean_dec_ref(v_a_2745_);
lean_dec(v_a_2744_);
lean_dec_ref(v_a_2743_);
lean_dec(v_a_2742_);
lean_dec(v_a_2741_);
return v_res_2752_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(lean_object* v___x_2753_, lean_object* v_inst_2754_, lean_object* v_x_2755_, size_t v_x_2756_, size_t v_x_2757_){
_start:
{
lean_object* v___x_2758_; 
v___x_2758_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___redArg(v___x_2753_, v_x_2755_, v_x_2756_, v_x_2757_);
return v___x_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___boxed(lean_object* v___x_2759_, lean_object* v_inst_2760_, lean_object* v_x_2761_, lean_object* v_x_2762_, lean_object* v_x_2763_){
_start:
{
size_t v_x_25126__boxed_2764_; size_t v_x_25127__boxed_2765_; lean_object* v_res_2766_; 
v_x_25126__boxed_2764_ = lean_unbox_usize(v_x_2762_);
lean_dec(v_x_2762_);
v_x_25127__boxed_2765_ = lean_unbox_usize(v_x_2763_);
lean_dec(v_x_2763_);
v_res_2766_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(v___x_2759_, v_inst_2760_, v_x_2761_, v_x_25126__boxed_2764_, v_x_25127__boxed_2765_);
lean_dec_ref(v_inst_2760_);
lean_dec_ref(v___x_2759_);
return v_res_2766_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11(lean_object* v_c_2767_, lean_object* v_x_2768_, lean_object* v_as_2769_, size_t v_sz_2770_, size_t v_i_2771_, lean_object* v_b_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_){
_start:
{
lean_object* v___x_2784_; 
v___x_2784_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(v_c_2767_, v_x_2768_, v_as_2769_, v_sz_2770_, v_i_2771_, v_b_2772_, v___y_2773_);
return v___x_2784_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___boxed(lean_object** _args){
lean_object* v_c_2785_ = _args[0];
lean_object* v_x_2786_ = _args[1];
lean_object* v_as_2787_ = _args[2];
lean_object* v_sz_2788_ = _args[3];
lean_object* v_i_2789_ = _args[4];
lean_object* v_b_2790_ = _args[5];
lean_object* v___y_2791_ = _args[6];
lean_object* v___y_2792_ = _args[7];
lean_object* v___y_2793_ = _args[8];
lean_object* v___y_2794_ = _args[9];
lean_object* v___y_2795_ = _args[10];
lean_object* v___y_2796_ = _args[11];
lean_object* v___y_2797_ = _args[12];
lean_object* v___y_2798_ = _args[13];
lean_object* v___y_2799_ = _args[14];
lean_object* v___y_2800_ = _args[15];
lean_object* v___y_2801_ = _args[16];
_start:
{
size_t v_sz_boxed_2802_; size_t v_i_boxed_2803_; lean_object* v_res_2804_; 
v_sz_boxed_2802_ = lean_unbox_usize(v_sz_2788_);
lean_dec(v_sz_2788_);
v_i_boxed_2803_ = lean_unbox_usize(v_i_2789_);
lean_dec(v_i_2789_);
v_res_2804_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11(v_c_2785_, v_x_2786_, v_as_2787_, v_sz_boxed_2802_, v_i_boxed_2803_, v_b_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
lean_dec(v___y_2800_);
lean_dec_ref(v___y_2799_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec(v___y_2792_);
lean_dec(v___y_2791_);
lean_dec_ref(v_as_2787_);
return v_res_2804_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10(lean_object* v_c_2805_, lean_object* v_x_2806_, lean_object* v_as_2807_, size_t v_sz_2808_, size_t v_i_2809_, lean_object* v_b_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_){
_start:
{
lean_object* v___x_2822_; 
v___x_2822_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(v_c_2805_, v_x_2806_, v_as_2807_, v_sz_2808_, v_i_2809_, v_b_2810_, v___y_2811_);
return v___x_2822_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___boxed(lean_object** _args){
lean_object* v_c_2823_ = _args[0];
lean_object* v_x_2824_ = _args[1];
lean_object* v_as_2825_ = _args[2];
lean_object* v_sz_2826_ = _args[3];
lean_object* v_i_2827_ = _args[4];
lean_object* v_b_2828_ = _args[5];
lean_object* v___y_2829_ = _args[6];
lean_object* v___y_2830_ = _args[7];
lean_object* v___y_2831_ = _args[8];
lean_object* v___y_2832_ = _args[9];
lean_object* v___y_2833_ = _args[10];
lean_object* v___y_2834_ = _args[11];
lean_object* v___y_2835_ = _args[12];
lean_object* v___y_2836_ = _args[13];
lean_object* v___y_2837_ = _args[14];
lean_object* v___y_2838_ = _args[15];
lean_object* v___y_2839_ = _args[16];
_start:
{
size_t v_sz_boxed_2840_; size_t v_i_boxed_2841_; lean_object* v_res_2842_; 
v_sz_boxed_2840_ = lean_unbox_usize(v_sz_2826_);
lean_dec(v_sz_2826_);
v_i_boxed_2841_ = lean_unbox_usize(v_i_2827_);
lean_dec(v_i_2827_);
v_res_2842_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10(v_c_2823_, v_x_2824_, v_as_2825_, v_sz_boxed_2840_, v_i_boxed_2841_, v_b_2828_, v___y_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_);
lean_dec(v___y_2838_);
lean_dec_ref(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec_ref(v___y_2835_);
lean_dec(v___y_2834_);
lean_dec_ref(v___y_2833_);
lean_dec(v___y_2832_);
lean_dec_ref(v___y_2831_);
lean_dec(v___y_2830_);
lean_dec(v___y_2829_);
lean_dec_ref(v_as_2825_);
return v_res_2842_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0(lean_object* v_v_2843_, lean_object* v_b_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_){
_start:
{
lean_object* v_snd_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2887_; 
v_snd_2856_ = lean_ctor_get(v_b_2844_, 1);
v_isSharedCheck_2887_ = !lean_is_exclusive(v_b_2844_);
if (v_isSharedCheck_2887_ == 0)
{
lean_object* v_unused_2888_; 
v_unused_2888_ = lean_ctor_get(v_b_2844_, 0);
lean_dec(v_unused_2888_);
v___x_2858_ = v_b_2844_;
v_isShared_2859_ = v_isSharedCheck_2887_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_snd_2856_);
lean_dec(v_b_2844_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2887_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v___x_2860_; 
lean_inc(v_snd_2856_);
lean_inc(v_v_2843_);
v___x_2860_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(v_v_2843_, v_snd_2856_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_);
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_object* v_a_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2878_; 
v_a_2861_ = lean_ctor_get(v___x_2860_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2863_ = v___x_2860_;
v_isShared_2864_ = v_isSharedCheck_2878_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_a_2861_);
lean_dec(v___x_2860_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2878_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
if (lean_obj_tag(v_a_2861_) == 1)
{
lean_object* v_val_2865_; lean_object* v___x_2866_; lean_object* v___x_2868_; 
lean_del_object(v___x_2863_);
lean_dec(v_snd_2856_);
v_val_2865_ = lean_ctor_get(v_a_2861_, 0);
lean_inc(v_val_2865_);
lean_dec_ref(v_a_2861_);
v___x_2866_ = lean_box(0);
if (v_isShared_2859_ == 0)
{
lean_ctor_set(v___x_2858_, 1, v_val_2865_);
lean_ctor_set(v___x_2858_, 0, v___x_2866_);
v___x_2868_ = v___x_2858_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v___x_2866_);
lean_ctor_set(v_reuseFailAlloc_2870_, 1, v_val_2865_);
v___x_2868_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
v_b_2844_ = v___x_2868_;
goto _start;
}
}
else
{
lean_object* v___x_2871_; lean_object* v___x_2873_; 
lean_dec(v_a_2861_);
lean_dec(v_v_2843_);
lean_inc(v_snd_2856_);
v___x_2871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2871_, 0, v_snd_2856_);
if (v_isShared_2859_ == 0)
{
lean_ctor_set(v___x_2858_, 0, v___x_2871_);
v___x_2873_ = v___x_2858_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v___x_2871_);
lean_ctor_set(v_reuseFailAlloc_2877_, 1, v_snd_2856_);
v___x_2873_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
lean_object* v___x_2875_; 
if (v_isShared_2864_ == 0)
{
lean_ctor_set(v___x_2863_, 0, v___x_2873_);
v___x_2875_ = v___x_2863_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v___x_2873_);
v___x_2875_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
return v___x_2875_;
}
}
}
}
}
else
{
lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2886_; 
lean_del_object(v___x_2858_);
lean_dec(v_snd_2856_);
lean_dec(v_v_2843_);
v_a_2879_ = lean_ctor_get(v___x_2860_, 0);
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2881_ = v___x_2860_;
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v___x_2860_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2884_; 
if (v_isShared_2882_ == 0)
{
v___x_2884_ = v___x_2881_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_a_2879_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___boxed(lean_object* v_v_2889_, lean_object* v_b_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_){
_start:
{
lean_object* v_res_2902_; 
v_res_2902_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0(v_v_2889_, v_b_2890_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_, v___y_2900_);
lean_dec(v___y_2900_);
lean_dec_ref(v___y_2899_);
lean_dec(v___y_2898_);
lean_dec_ref(v___y_2897_);
lean_dec(v___y_2896_);
lean_dec_ref(v___y_2895_);
lean_dec(v___y_2894_);
lean_dec_ref(v___y_2893_);
lean_dec(v___y_2892_);
lean_dec(v___y_2891_);
return v_res_2902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(lean_object* v_c_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_, lean_object* v_a_2909_, lean_object* v_a_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_){
_start:
{
lean_object* v_p_2915_; 
v_p_2915_ = lean_ctor_get(v_c_2903_, 0);
if (lean_obj_tag(v_p_2915_) == 1)
{
lean_object* v_v_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
v_v_2916_ = lean_ctor_get(v_p_2915_, 1);
lean_inc(v_v_2916_);
v___x_2917_ = lean_box(0);
v___x_2918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2918_, 0, v___x_2917_);
lean_ctor_set(v___x_2918_, 1, v_c_2903_);
v___x_2919_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0(v_v_2916_, v___x_2918_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_, v_a_2908_, v_a_2909_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_);
if (lean_obj_tag(v___x_2919_) == 0)
{
lean_object* v_a_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2933_; 
v_a_2920_ = lean_ctor_get(v___x_2919_, 0);
v_isSharedCheck_2933_ = !lean_is_exclusive(v___x_2919_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2922_ = v___x_2919_;
v_isShared_2923_ = v_isSharedCheck_2933_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_a_2920_);
lean_dec(v___x_2919_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2933_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v_fst_2924_; 
v_fst_2924_ = lean_ctor_get(v_a_2920_, 0);
if (lean_obj_tag(v_fst_2924_) == 0)
{
lean_object* v_snd_2925_; lean_object* v___x_2927_; 
v_snd_2925_ = lean_ctor_get(v_a_2920_, 1);
lean_inc(v_snd_2925_);
lean_dec(v_a_2920_);
if (v_isShared_2923_ == 0)
{
lean_ctor_set(v___x_2922_, 0, v_snd_2925_);
v___x_2927_ = v___x_2922_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_snd_2925_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
else
{
lean_object* v_val_2929_; lean_object* v___x_2931_; 
lean_inc_ref(v_fst_2924_);
lean_dec(v_a_2920_);
v_val_2929_ = lean_ctor_get(v_fst_2924_, 0);
lean_inc(v_val_2929_);
lean_dec_ref(v_fst_2924_);
if (v_isShared_2923_ == 0)
{
lean_ctor_set(v___x_2922_, 0, v_val_2929_);
v___x_2931_ = v___x_2922_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_val_2929_);
v___x_2931_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
return v___x_2931_;
}
}
}
}
else
{
lean_object* v_a_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2941_; 
v_a_2934_ = lean_ctor_get(v___x_2919_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2919_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2936_ = v___x_2919_;
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_a_2934_);
lean_dec(v___x_2919_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2939_; 
if (v_isShared_2937_ == 0)
{
v___x_2939_ = v___x_2936_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_a_2934_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
}
}
else
{
lean_object* v___x_2942_; 
v___x_2942_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_2903_, v_a_2904_, v_a_2910_, v_a_2911_, v_a_2912_, v_a_2913_);
return v___x_2942_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq___boxed(lean_object* v_c_2943_, lean_object* v_a_2944_, lean_object* v_a_2945_, lean_object* v_a_2946_, lean_object* v_a_2947_, lean_object* v_a_2948_, lean_object* v_a_2949_, lean_object* v_a_2950_, lean_object* v_a_2951_, lean_object* v_a_2952_, lean_object* v_a_2953_, lean_object* v_a_2954_){
_start:
{
lean_object* v_res_2955_; 
v_res_2955_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(v_c_2943_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_, v_a_2948_, v_a_2949_, v_a_2950_, v_a_2951_, v_a_2952_, v_a_2953_);
lean_dec(v_a_2953_);
lean_dec_ref(v_a_2952_);
lean_dec(v_a_2951_);
lean_dec_ref(v_a_2950_);
lean_dec(v_a_2949_);
lean_dec_ref(v_a_2948_);
lean_dec(v_a_2947_);
lean_dec_ref(v_a_2946_);
lean_dec(v_a_2945_);
lean_dec(v_a_2944_);
return v_res_2955_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0___redArg(lean_object* v_a_2956_, lean_object* v_x_2957_, size_t v_x_2958_, size_t v_x_2959_){
_start:
{
if (lean_obj_tag(v_x_2957_) == 0)
{
lean_object* v_cs_2960_; size_t v_j_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; uint8_t v___x_2964_; 
v_cs_2960_ = lean_ctor_get(v_x_2957_, 0);
v_j_2961_ = lean_usize_shift_right(v_x_2958_, v_x_2959_);
v___x_2962_ = lean_usize_to_nat(v_j_2961_);
v___x_2963_ = lean_array_get_size(v_cs_2960_);
v___x_2964_ = lean_nat_dec_lt(v___x_2962_, v___x_2963_);
if (v___x_2964_ == 0)
{
lean_dec(v___x_2962_);
lean_dec_ref(v_a_2956_);
return v_x_2957_;
}
else
{
lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2982_; 
lean_inc_ref(v_cs_2960_);
v_isSharedCheck_2982_ = !lean_is_exclusive(v_x_2957_);
if (v_isSharedCheck_2982_ == 0)
{
lean_object* v_unused_2983_; 
v_unused_2983_ = lean_ctor_get(v_x_2957_, 0);
lean_dec(v_unused_2983_);
v___x_2966_ = v_x_2957_;
v_isShared_2967_ = v_isSharedCheck_2982_;
goto v_resetjp_2965_;
}
else
{
lean_dec(v_x_2957_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_2982_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
size_t v___x_2968_; size_t v___x_2969_; size_t v___x_2970_; size_t v_i_2971_; size_t v___x_2972_; size_t v_shift_2973_; lean_object* v_v_2974_; lean_object* v___x_2975_; lean_object* v_xs_x27_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2980_; 
v___x_2968_ = ((size_t)1ULL);
v___x_2969_ = lean_usize_shift_left(v___x_2968_, v_x_2959_);
v___x_2970_ = lean_usize_sub(v___x_2969_, v___x_2968_);
v_i_2971_ = lean_usize_land(v_x_2958_, v___x_2970_);
v___x_2972_ = ((size_t)5ULL);
v_shift_2973_ = lean_usize_sub(v_x_2959_, v___x_2972_);
v_v_2974_ = lean_array_fget(v_cs_2960_, v___x_2962_);
v___x_2975_ = lean_box(0);
v_xs_x27_2976_ = lean_array_fset(v_cs_2960_, v___x_2962_, v___x_2975_);
v___x_2977_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0___redArg(v_a_2956_, v_v_2974_, v_i_2971_, v_shift_2973_);
v___x_2978_ = lean_array_fset(v_xs_x27_2976_, v___x_2962_, v___x_2977_);
lean_dec(v___x_2962_);
if (v_isShared_2967_ == 0)
{
lean_ctor_set(v___x_2966_, 0, v___x_2978_);
v___x_2980_ = v___x_2966_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v___x_2978_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
}
}
else
{
lean_object* v_vs_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; uint8_t v___x_2987_; 
v_vs_2984_ = lean_ctor_get(v_x_2957_, 0);
v___x_2985_ = lean_usize_to_nat(v_x_2958_);
v___x_2986_ = lean_array_get_size(v_vs_2984_);
v___x_2987_ = lean_nat_dec_lt(v___x_2985_, v___x_2986_);
if (v___x_2987_ == 0)
{
lean_dec(v___x_2985_);
lean_dec_ref(v_a_2956_);
return v_x_2957_;
}
else
{
lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_2999_; 
lean_inc_ref(v_vs_2984_);
v_isSharedCheck_2999_ = !lean_is_exclusive(v_x_2957_);
if (v_isSharedCheck_2999_ == 0)
{
lean_object* v_unused_3000_; 
v_unused_3000_ = lean_ctor_get(v_x_2957_, 0);
lean_dec(v_unused_3000_);
v___x_2989_ = v_x_2957_;
v_isShared_2990_ = v_isSharedCheck_2999_;
goto v_resetjp_2988_;
}
else
{
lean_dec(v_x_2957_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_2999_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v_v_2991_; lean_object* v___x_2992_; lean_object* v_xs_x27_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2997_; 
v_v_2991_ = lean_array_fget(v_vs_2984_, v___x_2985_);
v___x_2992_ = lean_box(0);
v_xs_x27_2993_ = lean_array_fset(v_vs_2984_, v___x_2985_, v___x_2992_);
v___x_2994_ = l_Lean_PersistentArray_push___redArg(v_v_2991_, v_a_2956_);
v___x_2995_ = lean_array_fset(v_xs_x27_2993_, v___x_2985_, v___x_2994_);
lean_dec(v___x_2985_);
if (v_isShared_2990_ == 0)
{
lean_ctor_set(v___x_2989_, 0, v___x_2995_);
v___x_2997_ = v___x_2989_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v___x_2995_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
return v___x_2997_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0___redArg___boxed(lean_object* v_a_3001_, lean_object* v_x_3002_, lean_object* v_x_3003_, lean_object* v_x_3004_){
_start:
{
size_t v_x_73498__boxed_3005_; size_t v_x_73499__boxed_3006_; lean_object* v_res_3007_; 
v_x_73498__boxed_3005_ = lean_unbox_usize(v_x_3003_);
lean_dec(v_x_3003_);
v_x_73499__boxed_3006_ = lean_unbox_usize(v_x_3004_);
lean_dec(v_x_3004_);
v_res_3007_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0___redArg(v_a_3001_, v_x_3002_, v_x_73498__boxed_3005_, v_x_73499__boxed_3006_);
return v_res_3007_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(lean_object* v_a_3008_, lean_object* v_inst_3009_, lean_object* v_t_3010_, lean_object* v_i_3011_){
_start:
{
lean_object* v_root_3012_; lean_object* v_tail_3013_; lean_object* v_size_3014_; size_t v_shift_3015_; lean_object* v_tailOff_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3040_; 
v_root_3012_ = lean_ctor_get(v_t_3010_, 0);
v_tail_3013_ = lean_ctor_get(v_t_3010_, 1);
v_size_3014_ = lean_ctor_get(v_t_3010_, 2);
v_shift_3015_ = lean_ctor_get_usize(v_t_3010_, 4);
v_tailOff_3016_ = lean_ctor_get(v_t_3010_, 3);
v_isSharedCheck_3040_ = !lean_is_exclusive(v_t_3010_);
if (v_isSharedCheck_3040_ == 0)
{
v___x_3018_ = v_t_3010_;
v_isShared_3019_ = v_isSharedCheck_3040_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_tailOff_3016_);
lean_inc(v_size_3014_);
lean_inc(v_tail_3013_);
lean_inc(v_root_3012_);
lean_dec(v_t_3010_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3040_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
uint8_t v___x_3020_; 
v___x_3020_ = lean_nat_dec_le(v_tailOff_3016_, v_i_3011_);
if (v___x_3020_ == 0)
{
size_t v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3024_; 
v___x_3021_ = lean_usize_of_nat(v_i_3011_);
v___x_3022_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0___redArg(v_a_3008_, v_root_3012_, v___x_3021_, v_shift_3015_);
if (v_isShared_3019_ == 0)
{
lean_ctor_set(v___x_3018_, 0, v___x_3022_);
v___x_3024_ = v___x_3018_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v___x_3022_);
lean_ctor_set(v_reuseFailAlloc_3025_, 1, v_tail_3013_);
lean_ctor_set(v_reuseFailAlloc_3025_, 2, v_size_3014_);
lean_ctor_set(v_reuseFailAlloc_3025_, 3, v_tailOff_3016_);
lean_ctor_set_usize(v_reuseFailAlloc_3025_, 4, v_shift_3015_);
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
lean_object* v___x_3026_; lean_object* v___x_3027_; uint8_t v___x_3028_; 
v___x_3026_ = lean_nat_sub(v_i_3011_, v_tailOff_3016_);
v___x_3027_ = lean_array_get_size(v_tail_3013_);
v___x_3028_ = lean_nat_dec_lt(v___x_3026_, v___x_3027_);
if (v___x_3028_ == 0)
{
lean_object* v___x_3030_; 
lean_dec(v___x_3026_);
lean_dec_ref(v_a_3008_);
if (v_isShared_3019_ == 0)
{
v___x_3030_ = v___x_3018_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_root_3012_);
lean_ctor_set(v_reuseFailAlloc_3031_, 1, v_tail_3013_);
lean_ctor_set(v_reuseFailAlloc_3031_, 2, v_size_3014_);
lean_ctor_set(v_reuseFailAlloc_3031_, 3, v_tailOff_3016_);
lean_ctor_set_usize(v_reuseFailAlloc_3031_, 4, v_shift_3015_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
else
{
lean_object* v_v_3032_; lean_object* v___x_3033_; lean_object* v_xs_x27_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3038_; 
v_v_3032_ = lean_array_fget(v_tail_3013_, v___x_3026_);
v___x_3033_ = lean_box(0);
v_xs_x27_3034_ = lean_array_fset(v_tail_3013_, v___x_3026_, v___x_3033_);
v___x_3035_ = l_Lean_PersistentArray_push___redArg(v_v_3032_, v_a_3008_);
v___x_3036_ = lean_array_fset(v_xs_x27_3034_, v___x_3026_, v___x_3035_);
lean_dec(v___x_3026_);
if (v_isShared_3019_ == 0)
{
lean_ctor_set(v___x_3018_, 1, v___x_3036_);
v___x_3038_ = v___x_3018_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v_root_3012_);
lean_ctor_set(v_reuseFailAlloc_3039_, 1, v___x_3036_);
lean_ctor_set(v_reuseFailAlloc_3039_, 2, v_size_3014_);
lean_ctor_set(v_reuseFailAlloc_3039_, 3, v_tailOff_3016_);
lean_ctor_set_usize(v_reuseFailAlloc_3039_, 4, v_shift_3015_);
v___x_3038_ = v_reuseFailAlloc_3039_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
return v___x_3038_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0___boxed(lean_object* v_a_3041_, lean_object* v_inst_3042_, lean_object* v_t_3043_, lean_object* v_i_3044_){
_start:
{
lean_object* v_res_3045_; 
v_res_3045_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(v_a_3041_, v_inst_3042_, v_t_3043_, v_i_3044_);
lean_dec(v_i_3044_);
lean_dec_ref(v_inst_3042_);
return v_res_3045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0(lean_object* v_a_3046_, lean_object* v_v_3047_, lean_object* v_s_3048_){
_start:
{
lean_object* v_vars_3049_; lean_object* v_varMap_3050_; lean_object* v_vars_x27_3051_; lean_object* v_varMap_x27_3052_; lean_object* v_natToIntMap_3053_; lean_object* v_natDef_3054_; lean_object* v_dvds_3055_; lean_object* v_lowers_3056_; lean_object* v_uppers_3057_; lean_object* v_diseqs_3058_; lean_object* v_elimEqs_3059_; lean_object* v_elimStack_3060_; lean_object* v_occurs_3061_; lean_object* v_assignment_3062_; lean_object* v_nextCnstrId_3063_; uint8_t v_caseSplits_3064_; lean_object* v_conflict_x3f_3065_; lean_object* v_diseqSplits_3066_; lean_object* v_divMod_3067_; lean_object* v_toIntIds_3068_; lean_object* v_toIntInfos_3069_; lean_object* v_toIntTermMap_3070_; lean_object* v_toIntVarMap_3071_; uint8_t v_usedCommRing_3072_; lean_object* v_nonlinearOccs_3073_; lean_object* v___x_3075_; uint8_t v_isShared_3076_; uint8_t v_isSharedCheck_3082_; 
v_vars_3049_ = lean_ctor_get(v_s_3048_, 0);
v_varMap_3050_ = lean_ctor_get(v_s_3048_, 1);
v_vars_x27_3051_ = lean_ctor_get(v_s_3048_, 2);
v_varMap_x27_3052_ = lean_ctor_get(v_s_3048_, 3);
v_natToIntMap_3053_ = lean_ctor_get(v_s_3048_, 4);
v_natDef_3054_ = lean_ctor_get(v_s_3048_, 5);
v_dvds_3055_ = lean_ctor_get(v_s_3048_, 6);
v_lowers_3056_ = lean_ctor_get(v_s_3048_, 7);
v_uppers_3057_ = lean_ctor_get(v_s_3048_, 8);
v_diseqs_3058_ = lean_ctor_get(v_s_3048_, 9);
v_elimEqs_3059_ = lean_ctor_get(v_s_3048_, 10);
v_elimStack_3060_ = lean_ctor_get(v_s_3048_, 11);
v_occurs_3061_ = lean_ctor_get(v_s_3048_, 12);
v_assignment_3062_ = lean_ctor_get(v_s_3048_, 13);
v_nextCnstrId_3063_ = lean_ctor_get(v_s_3048_, 14);
v_caseSplits_3064_ = lean_ctor_get_uint8(v_s_3048_, sizeof(void*)*23);
v_conflict_x3f_3065_ = lean_ctor_get(v_s_3048_, 15);
v_diseqSplits_3066_ = lean_ctor_get(v_s_3048_, 16);
v_divMod_3067_ = lean_ctor_get(v_s_3048_, 17);
v_toIntIds_3068_ = lean_ctor_get(v_s_3048_, 18);
v_toIntInfos_3069_ = lean_ctor_get(v_s_3048_, 19);
v_toIntTermMap_3070_ = lean_ctor_get(v_s_3048_, 20);
v_toIntVarMap_3071_ = lean_ctor_get(v_s_3048_, 21);
v_usedCommRing_3072_ = lean_ctor_get_uint8(v_s_3048_, sizeof(void*)*23 + 1);
v_nonlinearOccs_3073_ = lean_ctor_get(v_s_3048_, 22);
v_isSharedCheck_3082_ = !lean_is_exclusive(v_s_3048_);
if (v_isSharedCheck_3082_ == 0)
{
v___x_3075_ = v_s_3048_;
v_isShared_3076_ = v_isSharedCheck_3082_;
goto v_resetjp_3074_;
}
else
{
lean_inc(v_nonlinearOccs_3073_);
lean_inc(v_toIntVarMap_3071_);
lean_inc(v_toIntTermMap_3070_);
lean_inc(v_toIntInfos_3069_);
lean_inc(v_toIntIds_3068_);
lean_inc(v_divMod_3067_);
lean_inc(v_diseqSplits_3066_);
lean_inc(v_conflict_x3f_3065_);
lean_inc(v_nextCnstrId_3063_);
lean_inc(v_assignment_3062_);
lean_inc(v_occurs_3061_);
lean_inc(v_elimStack_3060_);
lean_inc(v_elimEqs_3059_);
lean_inc(v_diseqs_3058_);
lean_inc(v_uppers_3057_);
lean_inc(v_lowers_3056_);
lean_inc(v_dvds_3055_);
lean_inc(v_natDef_3054_);
lean_inc(v_natToIntMap_3053_);
lean_inc(v_varMap_x27_3052_);
lean_inc(v_vars_x27_3051_);
lean_inc(v_varMap_3050_);
lean_inc(v_vars_3049_);
lean_dec(v_s_3048_);
v___x_3075_ = lean_box(0);
v_isShared_3076_ = v_isSharedCheck_3082_;
goto v_resetjp_3074_;
}
v_resetjp_3074_:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3080_; 
v___x_3077_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0);
v___x_3078_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(v_a_3046_, v___x_3077_, v_uppers_3057_, v_v_3047_);
if (v_isShared_3076_ == 0)
{
lean_ctor_set(v___x_3075_, 8, v___x_3078_);
v___x_3080_ = v___x_3075_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v_vars_3049_);
lean_ctor_set(v_reuseFailAlloc_3081_, 1, v_varMap_3050_);
lean_ctor_set(v_reuseFailAlloc_3081_, 2, v_vars_x27_3051_);
lean_ctor_set(v_reuseFailAlloc_3081_, 3, v_varMap_x27_3052_);
lean_ctor_set(v_reuseFailAlloc_3081_, 4, v_natToIntMap_3053_);
lean_ctor_set(v_reuseFailAlloc_3081_, 5, v_natDef_3054_);
lean_ctor_set(v_reuseFailAlloc_3081_, 6, v_dvds_3055_);
lean_ctor_set(v_reuseFailAlloc_3081_, 7, v_lowers_3056_);
lean_ctor_set(v_reuseFailAlloc_3081_, 8, v___x_3078_);
lean_ctor_set(v_reuseFailAlloc_3081_, 9, v_diseqs_3058_);
lean_ctor_set(v_reuseFailAlloc_3081_, 10, v_elimEqs_3059_);
lean_ctor_set(v_reuseFailAlloc_3081_, 11, v_elimStack_3060_);
lean_ctor_set(v_reuseFailAlloc_3081_, 12, v_occurs_3061_);
lean_ctor_set(v_reuseFailAlloc_3081_, 13, v_assignment_3062_);
lean_ctor_set(v_reuseFailAlloc_3081_, 14, v_nextCnstrId_3063_);
lean_ctor_set(v_reuseFailAlloc_3081_, 15, v_conflict_x3f_3065_);
lean_ctor_set(v_reuseFailAlloc_3081_, 16, v_diseqSplits_3066_);
lean_ctor_set(v_reuseFailAlloc_3081_, 17, v_divMod_3067_);
lean_ctor_set(v_reuseFailAlloc_3081_, 18, v_toIntIds_3068_);
lean_ctor_set(v_reuseFailAlloc_3081_, 19, v_toIntInfos_3069_);
lean_ctor_set(v_reuseFailAlloc_3081_, 20, v_toIntTermMap_3070_);
lean_ctor_set(v_reuseFailAlloc_3081_, 21, v_toIntVarMap_3071_);
lean_ctor_set(v_reuseFailAlloc_3081_, 22, v_nonlinearOccs_3073_);
lean_ctor_set_uint8(v_reuseFailAlloc_3081_, sizeof(void*)*23, v_caseSplits_3064_);
lean_ctor_set_uint8(v_reuseFailAlloc_3081_, sizeof(void*)*23 + 1, v_usedCommRing_3072_);
v___x_3080_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
return v___x_3080_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0___boxed(lean_object* v_a_3083_, lean_object* v_v_3084_, lean_object* v_s_3085_){
_start:
{
lean_object* v_res_3086_; 
v_res_3086_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0(v_a_3083_, v_v_3084_, v_s_3085_);
lean_dec(v_v_3084_);
return v_res_3086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1(lean_object* v_a_3087_, lean_object* v_v_3088_, lean_object* v_s_3089_){
_start:
{
lean_object* v_vars_3090_; lean_object* v_varMap_3091_; lean_object* v_vars_x27_3092_; lean_object* v_varMap_x27_3093_; lean_object* v_natToIntMap_3094_; lean_object* v_natDef_3095_; lean_object* v_dvds_3096_; lean_object* v_lowers_3097_; lean_object* v_uppers_3098_; lean_object* v_diseqs_3099_; lean_object* v_elimEqs_3100_; lean_object* v_elimStack_3101_; lean_object* v_occurs_3102_; lean_object* v_assignment_3103_; lean_object* v_nextCnstrId_3104_; uint8_t v_caseSplits_3105_; lean_object* v_conflict_x3f_3106_; lean_object* v_diseqSplits_3107_; lean_object* v_divMod_3108_; lean_object* v_toIntIds_3109_; lean_object* v_toIntInfos_3110_; lean_object* v_toIntTermMap_3111_; lean_object* v_toIntVarMap_3112_; uint8_t v_usedCommRing_3113_; lean_object* v_nonlinearOccs_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3123_; 
v_vars_3090_ = lean_ctor_get(v_s_3089_, 0);
v_varMap_3091_ = lean_ctor_get(v_s_3089_, 1);
v_vars_x27_3092_ = lean_ctor_get(v_s_3089_, 2);
v_varMap_x27_3093_ = lean_ctor_get(v_s_3089_, 3);
v_natToIntMap_3094_ = lean_ctor_get(v_s_3089_, 4);
v_natDef_3095_ = lean_ctor_get(v_s_3089_, 5);
v_dvds_3096_ = lean_ctor_get(v_s_3089_, 6);
v_lowers_3097_ = lean_ctor_get(v_s_3089_, 7);
v_uppers_3098_ = lean_ctor_get(v_s_3089_, 8);
v_diseqs_3099_ = lean_ctor_get(v_s_3089_, 9);
v_elimEqs_3100_ = lean_ctor_get(v_s_3089_, 10);
v_elimStack_3101_ = lean_ctor_get(v_s_3089_, 11);
v_occurs_3102_ = lean_ctor_get(v_s_3089_, 12);
v_assignment_3103_ = lean_ctor_get(v_s_3089_, 13);
v_nextCnstrId_3104_ = lean_ctor_get(v_s_3089_, 14);
v_caseSplits_3105_ = lean_ctor_get_uint8(v_s_3089_, sizeof(void*)*23);
v_conflict_x3f_3106_ = lean_ctor_get(v_s_3089_, 15);
v_diseqSplits_3107_ = lean_ctor_get(v_s_3089_, 16);
v_divMod_3108_ = lean_ctor_get(v_s_3089_, 17);
v_toIntIds_3109_ = lean_ctor_get(v_s_3089_, 18);
v_toIntInfos_3110_ = lean_ctor_get(v_s_3089_, 19);
v_toIntTermMap_3111_ = lean_ctor_get(v_s_3089_, 20);
v_toIntVarMap_3112_ = lean_ctor_get(v_s_3089_, 21);
v_usedCommRing_3113_ = lean_ctor_get_uint8(v_s_3089_, sizeof(void*)*23 + 1);
v_nonlinearOccs_3114_ = lean_ctor_get(v_s_3089_, 22);
v_isSharedCheck_3123_ = !lean_is_exclusive(v_s_3089_);
if (v_isSharedCheck_3123_ == 0)
{
v___x_3116_ = v_s_3089_;
v_isShared_3117_ = v_isSharedCheck_3123_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_nonlinearOccs_3114_);
lean_inc(v_toIntVarMap_3112_);
lean_inc(v_toIntTermMap_3111_);
lean_inc(v_toIntInfos_3110_);
lean_inc(v_toIntIds_3109_);
lean_inc(v_divMod_3108_);
lean_inc(v_diseqSplits_3107_);
lean_inc(v_conflict_x3f_3106_);
lean_inc(v_nextCnstrId_3104_);
lean_inc(v_assignment_3103_);
lean_inc(v_occurs_3102_);
lean_inc(v_elimStack_3101_);
lean_inc(v_elimEqs_3100_);
lean_inc(v_diseqs_3099_);
lean_inc(v_uppers_3098_);
lean_inc(v_lowers_3097_);
lean_inc(v_dvds_3096_);
lean_inc(v_natDef_3095_);
lean_inc(v_natToIntMap_3094_);
lean_inc(v_varMap_x27_3093_);
lean_inc(v_vars_x27_3092_);
lean_inc(v_varMap_3091_);
lean_inc(v_vars_3090_);
lean_dec(v_s_3089_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3123_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3121_; 
v___x_3118_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___closed__0);
v___x_3119_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(v_a_3087_, v___x_3118_, v_lowers_3097_, v_v_3088_);
if (v_isShared_3117_ == 0)
{
lean_ctor_set(v___x_3116_, 7, v___x_3119_);
v___x_3121_ = v___x_3116_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_vars_3090_);
lean_ctor_set(v_reuseFailAlloc_3122_, 1, v_varMap_3091_);
lean_ctor_set(v_reuseFailAlloc_3122_, 2, v_vars_x27_3092_);
lean_ctor_set(v_reuseFailAlloc_3122_, 3, v_varMap_x27_3093_);
lean_ctor_set(v_reuseFailAlloc_3122_, 4, v_natToIntMap_3094_);
lean_ctor_set(v_reuseFailAlloc_3122_, 5, v_natDef_3095_);
lean_ctor_set(v_reuseFailAlloc_3122_, 6, v_dvds_3096_);
lean_ctor_set(v_reuseFailAlloc_3122_, 7, v___x_3119_);
lean_ctor_set(v_reuseFailAlloc_3122_, 8, v_uppers_3098_);
lean_ctor_set(v_reuseFailAlloc_3122_, 9, v_diseqs_3099_);
lean_ctor_set(v_reuseFailAlloc_3122_, 10, v_elimEqs_3100_);
lean_ctor_set(v_reuseFailAlloc_3122_, 11, v_elimStack_3101_);
lean_ctor_set(v_reuseFailAlloc_3122_, 12, v_occurs_3102_);
lean_ctor_set(v_reuseFailAlloc_3122_, 13, v_assignment_3103_);
lean_ctor_set(v_reuseFailAlloc_3122_, 14, v_nextCnstrId_3104_);
lean_ctor_set(v_reuseFailAlloc_3122_, 15, v_conflict_x3f_3106_);
lean_ctor_set(v_reuseFailAlloc_3122_, 16, v_diseqSplits_3107_);
lean_ctor_set(v_reuseFailAlloc_3122_, 17, v_divMod_3108_);
lean_ctor_set(v_reuseFailAlloc_3122_, 18, v_toIntIds_3109_);
lean_ctor_set(v_reuseFailAlloc_3122_, 19, v_toIntInfos_3110_);
lean_ctor_set(v_reuseFailAlloc_3122_, 20, v_toIntTermMap_3111_);
lean_ctor_set(v_reuseFailAlloc_3122_, 21, v_toIntVarMap_3112_);
lean_ctor_set(v_reuseFailAlloc_3122_, 22, v_nonlinearOccs_3114_);
lean_ctor_set_uint8(v_reuseFailAlloc_3122_, sizeof(void*)*23, v_caseSplits_3105_);
lean_ctor_set_uint8(v_reuseFailAlloc_3122_, sizeof(void*)*23 + 1, v_usedCommRing_3113_);
v___x_3121_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
return v___x_3121_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1___boxed(lean_object* v_a_3124_, lean_object* v_v_3125_, lean_object* v_s_3126_){
_start:
{
lean_object* v_res_3127_; 
v_res_3127_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1(v_a_3124_, v_v_3125_, v_s_3126_);
lean_dec(v_v_3125_);
return v_res_3127_;
}
}
LEAN_EXPORT lean_object* lean_grind_cutsat_assert_le(lean_object* v_c_3151_, lean_object* v_a_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_, lean_object* v_a_3157_, lean_object* v_a_3158_, lean_object* v_a_3159_, lean_object* v_a_3160_, lean_object* v_a_3161_){
_start:
{
lean_object* v___y_3167_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v___y_3198_; lean_object* v___y_3199_; lean_object* v___y_3200_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___y_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___x_3235_; 
v___x_3235_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_3152_, v_a_3160_);
if (lean_obj_tag(v___x_3235_) == 0)
{
lean_object* v_a_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3364_; 
v_a_3236_ = lean_ctor_get(v___x_3235_, 0);
v_isSharedCheck_3364_ = !lean_is_exclusive(v___x_3235_);
if (v_isSharedCheck_3364_ == 0)
{
v___x_3238_ = v___x_3235_;
v_isShared_3239_ = v_isSharedCheck_3364_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_a_3236_);
lean_dec(v___x_3235_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3364_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
uint8_t v___x_3240_; 
v___x_3240_ = lean_unbox(v_a_3236_);
lean_dec(v_a_3236_);
if (v___x_3240_ == 0)
{
lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v_a_3347_; uint8_t v___x_3348_; 
lean_del_object(v___x_3238_);
v___x_3345_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__7));
v___x_3346_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3345_, v_a_3160_);
v_a_3347_ = lean_ctor_get(v___x_3346_, 0);
lean_inc(v_a_3347_);
lean_dec_ref(v___x_3346_);
v___x_3348_ = lean_unbox(v_a_3347_);
lean_dec(v_a_3347_);
if (v___x_3348_ == 0)
{
v___y_3242_ = v_a_3152_;
v___y_3243_ = v_a_3153_;
v___y_3244_ = v_a_3154_;
v___y_3245_ = v_a_3155_;
v___y_3246_ = v_a_3156_;
v___y_3247_ = v_a_3157_;
v___y_3248_ = v_a_3158_;
v___y_3249_ = v_a_3159_;
v___y_3250_ = v_a_3160_;
v___y_3251_ = v_a_3161_;
goto v___jp_3241_;
}
else
{
lean_object* v___x_3349_; 
lean_inc_ref(v_c_3151_);
v___x_3349_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_3151_, v_a_3152_, v_a_3160_);
if (lean_obj_tag(v___x_3349_) == 0)
{
lean_object* v_a_3350_; lean_object* v___x_3351_; 
v_a_3350_ = lean_ctor_get(v___x_3349_, 0);
lean_inc(v_a_3350_);
lean_dec_ref(v___x_3349_);
v___x_3351_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1___redArg(v___x_3345_, v_a_3350_, v_a_3158_, v_a_3159_, v_a_3160_, v_a_3161_);
if (lean_obj_tag(v___x_3351_) == 0)
{
lean_dec_ref(v___x_3351_);
v___y_3242_ = v_a_3152_;
v___y_3243_ = v_a_3153_;
v___y_3244_ = v_a_3154_;
v___y_3245_ = v_a_3155_;
v___y_3246_ = v_a_3156_;
v___y_3247_ = v_a_3157_;
v___y_3248_ = v_a_3158_;
v___y_3249_ = v_a_3159_;
v___y_3250_ = v_a_3160_;
v___y_3251_ = v_a_3161_;
goto v___jp_3241_;
}
else
{
lean_dec(v_a_3161_);
lean_dec_ref(v_a_3160_);
lean_dec(v_a_3159_);
lean_dec_ref(v_a_3158_);
lean_dec(v_a_3157_);
lean_dec_ref(v_a_3156_);
lean_dec(v_a_3155_);
lean_dec_ref(v_a_3154_);
lean_dec(v_a_3153_);
lean_dec(v_a_3152_);
lean_dec_ref(v_c_3151_);
return v___x_3351_;
}
}
else
{
lean_object* v_a_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3359_; 
lean_dec(v_a_3161_);
lean_dec_ref(v_a_3160_);
lean_dec(v_a_3159_);
lean_dec_ref(v_a_3158_);
lean_dec(v_a_3157_);
lean_dec_ref(v_a_3156_);
lean_dec(v_a_3155_);
lean_dec_ref(v_a_3154_);
lean_dec(v_a_3153_);
lean_dec(v_a_3152_);
lean_dec_ref(v_c_3151_);
v_a_3352_ = lean_ctor_get(v___x_3349_, 0);
v_isSharedCheck_3359_ = !lean_is_exclusive(v___x_3349_);
if (v_isSharedCheck_3359_ == 0)
{
v___x_3354_ = v___x_3349_;
v_isShared_3355_ = v_isSharedCheck_3359_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_a_3352_);
lean_dec(v___x_3349_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3359_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
lean_object* v___x_3357_; 
if (v_isShared_3355_ == 0)
{
v___x_3357_ = v___x_3354_;
goto v_reusejp_3356_;
}
else
{
lean_object* v_reuseFailAlloc_3358_; 
v_reuseFailAlloc_3358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3358_, 0, v_a_3352_);
v___x_3357_ = v_reuseFailAlloc_3358_;
goto v_reusejp_3356_;
}
v_reusejp_3356_:
{
return v___x_3357_;
}
}
}
}
v___jp_3241_:
{
lean_object* v___x_3252_; lean_object* v___x_3253_; 
v___x_3252_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_norm(v_c_3151_);
lean_inc_ref(v___y_3250_);
v___x_3253_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts(v___x_3252_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
if (lean_obj_tag(v___x_3253_) == 0)
{
lean_object* v_a_3254_; lean_object* v_p_3255_; uint8_t v___x_3256_; 
v_a_3254_ = lean_ctor_get(v___x_3253_, 0);
lean_inc(v_a_3254_);
lean_dec_ref(v___x_3253_);
v_p_3255_ = lean_ctor_get(v_a_3254_, 0);
v___x_3256_ = l_Int_Linear_Poly_isUnsatLe(v_p_3255_);
if (v___x_3256_ == 0)
{
uint8_t v___x_3257_; 
v___x_3257_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(v_a_3254_);
if (v___x_3257_ == 0)
{
if (lean_obj_tag(v_p_3255_) == 1)
{
lean_object* v_k_3258_; lean_object* v_v_3259_; lean_object* v___x_3260_; 
v_k_3258_ = lean_ctor_get(v_p_3255_, 0);
lean_inc(v_k_3258_);
v_v_3259_ = lean_ctor_get(v_p_3255_, 1);
lean_inc(v_v_3259_);
lean_inc(v___y_3251_);
lean_inc_ref(v___y_3250_);
lean_inc(v___y_3249_);
lean_inc_ref(v___y_3248_);
lean_inc(v___y_3247_);
lean_inc_ref(v___y_3246_);
lean_inc(v___y_3245_);
lean_inc_ref(v___y_3244_);
lean_inc(v___y_3243_);
lean_inc(v___y_3242_);
lean_inc(v_a_3254_);
v___x_3260_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq(v_a_3254_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
if (lean_obj_tag(v___x_3260_) == 0)
{
lean_object* v_a_3261_; lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3297_; 
v_a_3261_ = lean_ctor_get(v___x_3260_, 0);
v_isSharedCheck_3297_ = !lean_is_exclusive(v___x_3260_);
if (v_isSharedCheck_3297_ == 0)
{
v___x_3263_ = v___x_3260_;
v_isShared_3264_ = v_isSharedCheck_3297_;
goto v_resetjp_3262_;
}
else
{
lean_inc(v_a_3261_);
lean_dec(v___x_3260_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3297_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
uint8_t v___x_3265_; 
v___x_3265_ = lean_unbox(v_a_3261_);
lean_dec(v_a_3261_);
if (v___x_3265_ == 0)
{
lean_object* v___x_3266_; 
lean_del_object(v___x_3263_);
v___x_3266_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(v_a_3254_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_, v___y_3247_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
if (lean_obj_tag(v___x_3266_) == 0)
{
lean_object* v_a_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v_a_3270_; lean_object* v___f_3271_; lean_object* v___f_3272_; uint8_t v___x_3273_; 
v_a_3267_ = lean_ctor_get(v___x_3266_, 0);
lean_inc(v_a_3267_);
lean_dec_ref(v___x_3266_);
v___x_3268_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2));
v___x_3269_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3268_, v___y_3250_);
v_a_3270_ = lean_ctor_get(v___x_3269_, 0);
lean_inc(v_a_3270_);
lean_dec_ref(v___x_3269_);
lean_inc(v_v_3259_);
lean_inc(v_a_3267_);
v___f_3271_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3271_, 0, v_a_3267_);
lean_closure_set(v___f_3271_, 1, v_v_3259_);
lean_inc(v_v_3259_);
lean_inc(v_a_3267_);
v___f_3272_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3272_, 0, v_a_3267_);
lean_closure_set(v___f_3272_, 1, v_v_3259_);
v___x_3273_ = lean_unbox(v_a_3270_);
lean_dec(v_a_3270_);
if (v___x_3273_ == 0)
{
v___y_3194_ = v___f_3271_;
v___y_3195_ = v___f_3272_;
v___y_3196_ = v_a_3267_;
v___y_3197_ = v_k_3258_;
v___y_3198_ = v_v_3259_;
v___y_3199_ = v___y_3242_;
v___y_3200_ = v___y_3248_;
v___y_3201_ = v___y_3249_;
v___y_3202_ = v___y_3250_;
v___y_3203_ = v___y_3251_;
goto v___jp_3193_;
}
else
{
lean_object* v___x_3274_; 
lean_inc(v_a_3267_);
v___x_3274_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_a_3267_, v___y_3242_, v___y_3250_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v_a_3275_; lean_object* v___x_3276_; 
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
lean_inc(v_a_3275_);
lean_dec_ref(v___x_3274_);
v___x_3276_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1___redArg(v___x_3268_, v_a_3275_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
if (lean_obj_tag(v___x_3276_) == 0)
{
lean_dec_ref(v___x_3276_);
v___y_3194_ = v___f_3271_;
v___y_3195_ = v___f_3272_;
v___y_3196_ = v_a_3267_;
v___y_3197_ = v_k_3258_;
v___y_3198_ = v_v_3259_;
v___y_3199_ = v___y_3242_;
v___y_3200_ = v___y_3248_;
v___y_3201_ = v___y_3249_;
v___y_3202_ = v___y_3250_;
v___y_3203_ = v___y_3251_;
goto v___jp_3193_;
}
else
{
lean_dec_ref(v___f_3272_);
lean_dec_ref(v___f_3271_);
lean_dec(v_a_3267_);
lean_dec(v_v_3259_);
lean_dec(v_k_3258_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v___y_3242_);
return v___x_3276_;
}
}
else
{
lean_object* v_a_3277_; lean_object* v___x_3279_; uint8_t v_isShared_3280_; uint8_t v_isSharedCheck_3284_; 
lean_dec_ref(v___f_3272_);
lean_dec_ref(v___f_3271_);
lean_dec(v_a_3267_);
lean_dec(v_v_3259_);
lean_dec(v_k_3258_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v___y_3242_);
v_a_3277_ = lean_ctor_get(v___x_3274_, 0);
v_isSharedCheck_3284_ = !lean_is_exclusive(v___x_3274_);
if (v_isSharedCheck_3284_ == 0)
{
v___x_3279_ = v___x_3274_;
v_isShared_3280_ = v_isSharedCheck_3284_;
goto v_resetjp_3278_;
}
else
{
lean_inc(v_a_3277_);
lean_dec(v___x_3274_);
v___x_3279_ = lean_box(0);
v_isShared_3280_ = v_isSharedCheck_3284_;
goto v_resetjp_3278_;
}
v_resetjp_3278_:
{
lean_object* v___x_3282_; 
if (v_isShared_3280_ == 0)
{
v___x_3282_ = v___x_3279_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3283_; 
v_reuseFailAlloc_3283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3283_, 0, v_a_3277_);
v___x_3282_ = v_reuseFailAlloc_3283_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
return v___x_3282_;
}
}
}
}
}
else
{
lean_object* v_a_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3292_; 
lean_dec(v_v_3259_);
lean_dec(v_k_3258_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v___y_3242_);
v_a_3285_ = lean_ctor_get(v___x_3266_, 0);
v_isSharedCheck_3292_ = !lean_is_exclusive(v___x_3266_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3287_ = v___x_3266_;
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_a_3285_);
lean_dec(v___x_3266_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
lean_object* v___x_3290_; 
if (v_isShared_3288_ == 0)
{
v___x_3290_ = v___x_3287_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_a_3285_);
v___x_3290_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
return v___x_3290_;
}
}
}
}
else
{
lean_object* v___x_3293_; lean_object* v___x_3295_; 
lean_dec(v_v_3259_);
lean_dec(v_k_3258_);
lean_dec(v_a_3254_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec(v___y_3242_);
v___x_3293_ = lean_box(0);
if (v_isShared_3264_ == 0)
{
lean_ctor_set(v___x_3263_, 0, v___x_3293_);
v___x_3295_ = v___x_3263_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v___x_3293_);
v___x_3295_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
return v___x_3295_;
}
}
}
}
else
{
lean_object* v_a_3298_; lean_object* v___x_3300_; uint8_t v_isShared_3301_; uint8_t v_isSharedCheck_3305_; 
lean_dec(v_v_3259_);
lean_dec(v_k_3258_);
lean_dec(v_a_3254_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec(v___y_3242_);
v_a_3298_ = lean_ctor_get(v___x_3260_, 0);
v_isSharedCheck_3305_ = !lean_is_exclusive(v___x_3260_);
if (v_isSharedCheck_3305_ == 0)
{
v___x_3300_ = v___x_3260_;
v_isShared_3301_ = v_isSharedCheck_3305_;
goto v_resetjp_3299_;
}
else
{
lean_inc(v_a_3298_);
lean_dec(v___x_3260_);
v___x_3300_ = lean_box(0);
v_isShared_3301_ = v_isSharedCheck_3305_;
goto v_resetjp_3299_;
}
v_resetjp_3299_:
{
lean_object* v___x_3303_; 
if (v_isShared_3301_ == 0)
{
v___x_3303_ = v___x_3300_;
goto v_reusejp_3302_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v_a_3298_);
v___x_3303_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3302_;
}
v_reusejp_3302_:
{
return v___x_3303_;
}
}
}
}
else
{
lean_object* v___x_3306_; 
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
v___x_3306_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_a_3254_, v___y_3242_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v___y_3242_);
return v___x_3306_;
}
}
else
{
lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v_a_3309_; uint8_t v___x_3310_; 
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
v___x_3307_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__4));
v___x_3308_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3307_, v___y_3250_);
v_a_3309_ = lean_ctor_get(v___x_3308_, 0);
lean_inc(v_a_3309_);
lean_dec_ref(v___x_3308_);
v___x_3310_ = lean_unbox(v_a_3309_);
lean_dec(v_a_3309_);
if (v___x_3310_ == 0)
{
lean_dec(v_a_3254_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v___y_3242_);
goto v___jp_3163_;
}
else
{
lean_object* v___x_3311_; 
v___x_3311_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_a_3254_, v___y_3242_, v___y_3250_);
lean_dec(v___y_3242_);
if (lean_obj_tag(v___x_3311_) == 0)
{
lean_object* v_a_3312_; lean_object* v___x_3313_; 
v_a_3312_ = lean_ctor_get(v___x_3311_, 0);
lean_inc(v_a_3312_);
lean_dec_ref(v___x_3311_);
v___x_3313_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1___redArg(v___x_3307_, v_a_3312_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
if (lean_obj_tag(v___x_3313_) == 0)
{
lean_dec_ref(v___x_3313_);
goto v___jp_3163_;
}
else
{
return v___x_3313_;
}
}
else
{
lean_object* v_a_3314_; lean_object* v___x_3316_; uint8_t v_isShared_3317_; uint8_t v_isSharedCheck_3321_; 
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
v_a_3314_ = lean_ctor_get(v___x_3311_, 0);
v_isSharedCheck_3321_ = !lean_is_exclusive(v___x_3311_);
if (v_isSharedCheck_3321_ == 0)
{
v___x_3316_ = v___x_3311_;
v_isShared_3317_ = v_isSharedCheck_3321_;
goto v_resetjp_3315_;
}
else
{
lean_inc(v_a_3314_);
lean_dec(v___x_3311_);
v___x_3316_ = lean_box(0);
v_isShared_3317_ = v_isSharedCheck_3321_;
goto v_resetjp_3315_;
}
v_resetjp_3315_:
{
lean_object* v___x_3319_; 
if (v_isShared_3317_ == 0)
{
v___x_3319_ = v___x_3316_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v_a_3314_);
v___x_3319_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
return v___x_3319_;
}
}
}
}
}
}
else
{
lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v_a_3324_; uint8_t v___x_3325_; 
v___x_3322_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6));
v___x_3323_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3322_, v___y_3250_);
v_a_3324_ = lean_ctor_get(v___x_3323_, 0);
lean_inc(v_a_3324_);
lean_dec_ref(v___x_3323_);
v___x_3325_ = lean_unbox(v_a_3324_);
lean_dec(v_a_3324_);
if (v___x_3325_ == 0)
{
v___y_3213_ = v_a_3254_;
v___y_3214_ = v___y_3242_;
v___y_3215_ = v___y_3243_;
v___y_3216_ = v___y_3244_;
v___y_3217_ = v___y_3245_;
v___y_3218_ = v___y_3246_;
v___y_3219_ = v___y_3247_;
v___y_3220_ = v___y_3248_;
v___y_3221_ = v___y_3249_;
v___y_3222_ = v___y_3250_;
v___y_3223_ = v___y_3251_;
goto v___jp_3212_;
}
else
{
lean_object* v___x_3326_; 
lean_inc(v_a_3254_);
v___x_3326_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_a_3254_, v___y_3242_, v___y_3250_);
if (lean_obj_tag(v___x_3326_) == 0)
{
lean_object* v_a_3327_; lean_object* v___x_3328_; 
v_a_3327_ = lean_ctor_get(v___x_3326_, 0);
lean_inc(v_a_3327_);
lean_dec_ref(v___x_3326_);
v___x_3328_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__1___redArg(v___x_3322_, v_a_3327_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_);
if (lean_obj_tag(v___x_3328_) == 0)
{
lean_dec_ref(v___x_3328_);
v___y_3213_ = v_a_3254_;
v___y_3214_ = v___y_3242_;
v___y_3215_ = v___y_3243_;
v___y_3216_ = v___y_3244_;
v___y_3217_ = v___y_3245_;
v___y_3218_ = v___y_3246_;
v___y_3219_ = v___y_3247_;
v___y_3220_ = v___y_3248_;
v___y_3221_ = v___y_3249_;
v___y_3222_ = v___y_3250_;
v___y_3223_ = v___y_3251_;
goto v___jp_3212_;
}
else
{
lean_dec(v_a_3254_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec(v___y_3242_);
return v___x_3328_;
}
}
else
{
lean_object* v_a_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3336_; 
lean_dec(v_a_3254_);
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec(v___y_3242_);
v_a_3329_ = lean_ctor_get(v___x_3326_, 0);
v_isSharedCheck_3336_ = !lean_is_exclusive(v___x_3326_);
if (v_isSharedCheck_3336_ == 0)
{
v___x_3331_ = v___x_3326_;
v_isShared_3332_ = v_isSharedCheck_3336_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_a_3329_);
lean_dec(v___x_3326_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3336_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v___x_3334_; 
if (v_isShared_3332_ == 0)
{
v___x_3334_ = v___x_3331_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v_a_3329_);
v___x_3334_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
return v___x_3334_;
}
}
}
}
}
}
else
{
lean_object* v_a_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3344_; 
lean_dec(v___y_3251_);
lean_dec_ref(v___y_3250_);
lean_dec(v___y_3249_);
lean_dec_ref(v___y_3248_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
lean_dec(v___y_3245_);
lean_dec_ref(v___y_3244_);
lean_dec(v___y_3243_);
lean_dec(v___y_3242_);
v_a_3337_ = lean_ctor_get(v___x_3253_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v___x_3253_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3339_ = v___x_3253_;
v_isShared_3340_ = v_isSharedCheck_3344_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_a_3337_);
lean_dec(v___x_3253_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3344_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v___x_3342_; 
if (v_isShared_3340_ == 0)
{
v___x_3342_ = v___x_3339_;
goto v_reusejp_3341_;
}
else
{
lean_object* v_reuseFailAlloc_3343_; 
v_reuseFailAlloc_3343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3343_, 0, v_a_3337_);
v___x_3342_ = v_reuseFailAlloc_3343_;
goto v_reusejp_3341_;
}
v_reusejp_3341_:
{
return v___x_3342_;
}
}
}
}
}
else
{
lean_object* v___x_3360_; lean_object* v___x_3362_; 
lean_dec(v_a_3161_);
lean_dec_ref(v_a_3160_);
lean_dec(v_a_3159_);
lean_dec_ref(v_a_3158_);
lean_dec(v_a_3157_);
lean_dec_ref(v_a_3156_);
lean_dec(v_a_3155_);
lean_dec_ref(v_a_3154_);
lean_dec(v_a_3153_);
lean_dec(v_a_3152_);
lean_dec_ref(v_c_3151_);
v___x_3360_ = lean_box(0);
if (v_isShared_3239_ == 0)
{
lean_ctor_set(v___x_3238_, 0, v___x_3360_);
v___x_3362_ = v___x_3238_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v___x_3360_);
v___x_3362_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
return v___x_3362_;
}
}
}
}
else
{
lean_object* v_a_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3372_; 
lean_dec(v_a_3161_);
lean_dec_ref(v_a_3160_);
lean_dec(v_a_3159_);
lean_dec_ref(v_a_3158_);
lean_dec(v_a_3157_);
lean_dec_ref(v_a_3156_);
lean_dec(v_a_3155_);
lean_dec_ref(v_a_3154_);
lean_dec(v_a_3153_);
lean_dec(v_a_3152_);
lean_dec_ref(v_c_3151_);
v_a_3365_ = lean_ctor_get(v___x_3235_, 0);
v_isSharedCheck_3372_ = !lean_is_exclusive(v___x_3235_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_3367_ = v___x_3235_;
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
else
{
lean_inc(v_a_3365_);
lean_dec(v___x_3235_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3372_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v___x_3370_; 
if (v_isShared_3368_ == 0)
{
v___x_3370_ = v___x_3367_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v_a_3365_);
v___x_3370_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
return v___x_3370_;
}
}
}
v___jp_3163_:
{
lean_object* v___x_3164_; lean_object* v___x_3165_; 
v___x_3164_ = lean_box(0);
v___x_3165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3165_, 0, v___x_3164_);
return v___x_3165_;
}
v___jp_3166_:
{
lean_object* v___x_3171_; 
v___x_3171_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(v___y_3167_, v___y_3169_, v___y_3170_);
lean_dec_ref(v___y_3170_);
if (lean_obj_tag(v___x_3171_) == 0)
{
lean_object* v_a_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3184_; 
v_a_3172_ = lean_ctor_get(v___x_3171_, 0);
v_isSharedCheck_3184_ = !lean_is_exclusive(v___x_3171_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3174_ = v___x_3171_;
v_isShared_3175_ = v_isSharedCheck_3184_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_a_3172_);
lean_dec(v___x_3171_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3184_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
uint8_t v___x_3176_; uint8_t v___x_3177_; uint8_t v___x_3178_; 
v___x_3176_ = 0;
v___x_3177_ = lean_unbox(v_a_3172_);
lean_dec(v_a_3172_);
v___x_3178_ = l_Lean_instBEqLBool_beq(v___x_3177_, v___x_3176_);
if (v___x_3178_ == 0)
{
lean_object* v___x_3179_; lean_object* v___x_3181_; 
lean_dec(v___y_3169_);
lean_dec(v___y_3168_);
v___x_3179_ = lean_box(0);
if (v_isShared_3175_ == 0)
{
lean_ctor_set(v___x_3174_, 0, v___x_3179_);
v___x_3181_ = v___x_3174_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v___x_3179_);
v___x_3181_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
return v___x_3181_;
}
}
else
{
lean_object* v___x_3183_; 
lean_del_object(v___x_3174_);
v___x_3183_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v___y_3168_, v___y_3169_);
lean_dec(v___y_3169_);
return v___x_3183_;
}
}
}
else
{
lean_object* v_a_3185_; lean_object* v___x_3187_; uint8_t v_isShared_3188_; uint8_t v_isSharedCheck_3192_; 
lean_dec(v___y_3169_);
lean_dec(v___y_3168_);
v_a_3185_ = lean_ctor_get(v___x_3171_, 0);
v_isSharedCheck_3192_ = !lean_is_exclusive(v___x_3171_);
if (v_isSharedCheck_3192_ == 0)
{
v___x_3187_ = v___x_3171_;
v_isShared_3188_ = v_isSharedCheck_3192_;
goto v_resetjp_3186_;
}
else
{
lean_inc(v_a_3185_);
lean_dec(v___x_3171_);
v___x_3187_ = lean_box(0);
v_isShared_3188_ = v_isSharedCheck_3192_;
goto v_resetjp_3186_;
}
v_resetjp_3186_:
{
lean_object* v___x_3190_; 
if (v_isShared_3188_ == 0)
{
v___x_3190_ = v___x_3187_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v_a_3185_);
v___x_3190_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
return v___x_3190_;
}
}
}
}
v___jp_3193_:
{
lean_object* v_p_3204_; lean_object* v___x_3205_; 
v_p_3204_ = lean_ctor_get(v___y_3196_, 0);
lean_inc_ref(v_p_3204_);
v___x_3205_ = l_Int_Linear_Poly_updateOccs___redArg(v_p_3204_, v___y_3199_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_);
lean_dec(v___y_3203_);
lean_dec(v___y_3201_);
lean_dec_ref(v___y_3200_);
if (lean_obj_tag(v___x_3205_) == 0)
{
lean_object* v___x_3206_; uint8_t v___x_3207_; 
lean_dec_ref(v___x_3205_);
v___x_3206_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6);
v___x_3207_ = lean_int_dec_lt(v___y_3197_, v___x_3206_);
lean_dec(v___y_3197_);
if (v___x_3207_ == 0)
{
lean_object* v___x_3208_; lean_object* v___x_3209_; 
lean_dec_ref(v___y_3195_);
v___x_3208_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_3209_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3208_, v___y_3194_, v___y_3199_);
if (lean_obj_tag(v___x_3209_) == 0)
{
lean_dec_ref(v___x_3209_);
v___y_3167_ = v___y_3196_;
v___y_3168_ = v___y_3198_;
v___y_3169_ = v___y_3199_;
v___y_3170_ = v___y_3202_;
goto v___jp_3166_;
}
else
{
lean_dec_ref(v___y_3202_);
lean_dec(v___y_3199_);
lean_dec(v___y_3198_);
lean_dec_ref(v___y_3196_);
return v___x_3209_;
}
}
else
{
lean_object* v___x_3210_; lean_object* v___x_3211_; 
lean_dec_ref(v___y_3194_);
v___x_3210_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_3211_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3210_, v___y_3195_, v___y_3199_);
if (lean_obj_tag(v___x_3211_) == 0)
{
lean_dec_ref(v___x_3211_);
v___y_3167_ = v___y_3196_;
v___y_3168_ = v___y_3198_;
v___y_3169_ = v___y_3199_;
v___y_3170_ = v___y_3202_;
goto v___jp_3166_;
}
else
{
lean_dec_ref(v___y_3202_);
lean_dec(v___y_3199_);
lean_dec(v___y_3198_);
lean_dec_ref(v___y_3196_);
return v___x_3211_;
}
}
}
else
{
lean_dec_ref(v___y_3202_);
lean_dec(v___y_3199_);
lean_dec(v___y_3198_);
lean_dec(v___y_3197_);
lean_dec_ref(v___y_3196_);
lean_dec_ref(v___y_3195_);
lean_dec_ref(v___y_3194_);
return v___x_3205_;
}
}
v___jp_3212_:
{
lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3224_, 0, v___y_3213_);
v___x_3225_ = l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(v___x_3224_, v___y_3214_, v___y_3215_, v___y_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_, v___y_3222_, v___y_3223_);
if (lean_obj_tag(v___x_3225_) == 0)
{
lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3233_; 
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3233_ == 0)
{
lean_object* v_unused_3234_; 
v_unused_3234_ = lean_ctor_get(v___x_3225_, 0);
lean_dec(v_unused_3234_);
v___x_3227_ = v___x_3225_;
v_isShared_3228_ = v_isSharedCheck_3233_;
goto v_resetjp_3226_;
}
else
{
lean_dec(v___x_3225_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3233_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v___x_3229_; lean_object* v___x_3231_; 
v___x_3229_ = lean_box(0);
if (v_isShared_3228_ == 0)
{
lean_ctor_set(v___x_3227_, 0, v___x_3229_);
v___x_3231_ = v___x_3227_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v___x_3229_);
v___x_3231_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
return v___x_3231_;
}
}
}
else
{
return v___x_3225_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___boxed(lean_object* v_c_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_){
_start:
{
lean_object* v_res_3385_; 
v_res_3385_ = lean_grind_cutsat_assert_le(v_c_3373_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_);
return v_res_3385_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(lean_object* v_a_3386_, lean_object* v_inst_3387_, lean_object* v_x_3388_, size_t v_x_3389_, size_t v_x_3390_){
_start:
{
lean_object* v___x_3391_; 
v___x_3391_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0___redArg(v_a_3386_, v_x_3388_, v_x_3389_, v_x_3390_);
return v___x_3391_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0___boxed(lean_object* v_a_3392_, lean_object* v_inst_3393_, lean_object* v_x_3394_, lean_object* v_x_3395_, lean_object* v_x_3396_){
_start:
{
size_t v_x_74222__boxed_3397_; size_t v_x_74223__boxed_3398_; lean_object* v_res_3399_; 
v_x_74222__boxed_3397_ = lean_unbox_usize(v_x_3395_);
lean_dec(v_x_3395_);
v_x_74223__boxed_3398_ = lean_unbox_usize(v_x_3396_);
lean_dec(v_x_3396_);
v_res_3399_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(v_a_3392_, v_inst_3393_, v_x_3394_, v_x_74222__boxed_3397_, v_x_74223__boxed_3398_);
lean_dec_ref(v_inst_3393_);
return v_res_3399_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1(void){
_start:
{
lean_object* v___x_3401_; lean_object* v___x_3402_; 
v___x_3401_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__0));
v___x_3402_ = l_Lean_stringToMessageData(v___x_3401_);
return v___x_3402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(lean_object* v_e_3403_, lean_object* v_a_3404_, lean_object* v_a_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_, lean_object* v_a_3409_, lean_object* v_a_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_){
_start:
{
lean_object* v___x_3414_; 
v___x_3414_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3405_);
if (lean_obj_tag(v___x_3414_) == 0)
{
lean_object* v_a_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3428_; 
v_a_3415_ = lean_ctor_get(v___x_3414_, 0);
v_isSharedCheck_3428_ = !lean_is_exclusive(v___x_3414_);
if (v_isSharedCheck_3428_ == 0)
{
v___x_3417_ = v___x_3414_;
v_isShared_3418_ = v_isSharedCheck_3428_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_a_3415_);
lean_dec(v___x_3414_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3428_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
uint8_t v_verbose_3419_; 
v_verbose_3419_ = lean_ctor_get_uint8(v_a_3415_, sizeof(void*)*11 + 15);
lean_dec(v_a_3415_);
if (v_verbose_3419_ == 0)
{
lean_object* v___x_3420_; lean_object* v___x_3422_; 
lean_dec_ref(v_e_3403_);
v___x_3420_ = lean_box(0);
if (v_isShared_3418_ == 0)
{
lean_ctor_set(v___x_3417_, 0, v___x_3420_);
v___x_3422_ = v___x_3417_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v___x_3420_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
return v___x_3422_;
}
}
else
{
lean_object* v___x_3424_; lean_object* v___x_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; 
lean_del_object(v___x_3417_);
v___x_3424_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1);
v___x_3425_ = l_Lean_indentExpr(v_e_3403_);
v___x_3426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3426_, 0, v___x_3424_);
lean_ctor_set(v___x_3426_, 1, v___x_3425_);
v___x_3427_ = l_Lean_Meta_Grind_reportIssue(v___x_3426_, v_a_3404_, v_a_3405_, v_a_3406_, v_a_3407_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_);
return v___x_3427_;
}
}
}
else
{
lean_object* v_a_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3436_; 
lean_dec_ref(v_e_3403_);
v_a_3429_ = lean_ctor_get(v___x_3414_, 0);
v_isSharedCheck_3436_ = !lean_is_exclusive(v___x_3414_);
if (v_isSharedCheck_3436_ == 0)
{
v___x_3431_ = v___x_3414_;
v_isShared_3432_ = v_isSharedCheck_3436_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_a_3429_);
lean_dec(v___x_3414_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3436_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v___x_3434_; 
if (v_isShared_3432_ == 0)
{
v___x_3434_ = v___x_3431_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3435_; 
v_reuseFailAlloc_3435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3435_, 0, v_a_3429_);
v___x_3434_ = v_reuseFailAlloc_3435_;
goto v_reusejp_3433_;
}
v_reusejp_3433_:
{
return v___x_3434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___boxed(lean_object* v_e_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_, lean_object* v_a_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_){
_start:
{
lean_object* v_res_3448_; 
v_res_3448_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(v_e_3437_, v_a_3438_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_);
lean_dec(v_a_3446_);
lean_dec_ref(v_a_3445_);
lean_dec(v_a_3444_);
lean_dec_ref(v_a_3443_);
lean_dec(v_a_3442_);
lean_dec_ref(v_a_3441_);
lean_dec(v_a_3440_);
lean_dec_ref(v_a_3439_);
lean_dec(v_a_3438_);
return v_res_3448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized(lean_object* v_e_3449_, lean_object* v_a_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_){
_start:
{
lean_object* v___x_3461_; 
v___x_3461_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(v_e_3449_, v_a_3451_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_, v_a_3457_, v_a_3458_, v_a_3459_);
return v___x_3461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___boxed(lean_object* v_e_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_, lean_object* v_a_3468_, lean_object* v_a_3469_, lean_object* v_a_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_){
_start:
{
lean_object* v_res_3474_; 
v_res_3474_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized(v_e_3462_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_, v_a_3469_, v_a_3470_, v_a_3471_, v_a_3472_);
lean_dec(v_a_3472_);
lean_dec_ref(v_a_3471_);
lean_dec(v_a_3470_);
lean_dec_ref(v_a_3469_);
lean_dec(v_a_3468_);
lean_dec_ref(v_a_3467_);
lean_dec(v_a_3466_);
lean_dec_ref(v_a_3465_);
lean_dec(v_a_3464_);
lean_dec(v_a_3463_);
return v_res_3474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f(lean_object* v_e_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_){
_start:
{
lean_object* v___x_3492_; 
lean_inc_ref(v_e_3480_);
v___x_3492_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3480_, v_a_3488_);
if (lean_obj_tag(v___x_3492_) == 0)
{
lean_object* v_a_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3608_; 
v_a_3493_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3608_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3608_ == 0)
{
v___x_3495_ = v___x_3492_;
v_isShared_3496_ = v_isSharedCheck_3608_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_a_3493_);
lean_dec(v___x_3492_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3608_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
lean_object* v___x_3502_; uint8_t v___x_3503_; 
v___x_3502_ = l_Lean_Expr_cleanupAnnotations(v_a_3493_);
v___x_3503_ = l_Lean_Expr_isApp(v___x_3502_);
if (v___x_3503_ == 0)
{
lean_dec_ref(v___x_3502_);
lean_dec(v_a_3490_);
lean_dec_ref(v_a_3489_);
lean_dec(v_a_3488_);
lean_dec_ref(v_a_3487_);
lean_dec(v_a_3486_);
lean_dec_ref(v_a_3485_);
lean_dec(v_a_3484_);
lean_dec_ref(v_a_3483_);
lean_dec(v_a_3482_);
lean_dec(v_a_3481_);
lean_dec_ref(v_e_3480_);
goto v___jp_3497_;
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
lean_dec(v_a_3490_);
lean_dec_ref(v_a_3489_);
lean_dec(v_a_3488_);
lean_dec_ref(v_a_3487_);
lean_dec(v_a_3486_);
lean_dec_ref(v_a_3485_);
lean_dec(v_a_3484_);
lean_dec_ref(v_a_3483_);
lean_dec(v_a_3482_);
lean_dec(v_a_3481_);
lean_dec_ref(v_e_3480_);
goto v___jp_3497_;
}
else
{
lean_object* v_arg_3507_; lean_object* v___x_3508_; uint8_t v___x_3509_; 
v_arg_3507_ = lean_ctor_get(v___x_3505_, 1);
lean_inc_ref(v_arg_3507_);
v___x_3508_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3505_);
v___x_3509_ = l_Lean_Expr_isApp(v___x_3508_);
if (v___x_3509_ == 0)
{
lean_dec_ref(v___x_3508_);
lean_dec_ref(v_arg_3507_);
lean_dec_ref(v_arg_3504_);
lean_dec(v_a_3490_);
lean_dec_ref(v_a_3489_);
lean_dec(v_a_3488_);
lean_dec_ref(v_a_3487_);
lean_dec(v_a_3486_);
lean_dec_ref(v_a_3485_);
lean_dec(v_a_3484_);
lean_dec_ref(v_a_3483_);
lean_dec(v_a_3482_);
lean_dec(v_a_3481_);
lean_dec_ref(v_e_3480_);
goto v___jp_3497_;
}
else
{
lean_object* v_arg_3510_; lean_object* v___x_3511_; uint8_t v___x_3512_; 
v_arg_3510_ = lean_ctor_get(v___x_3508_, 1);
lean_inc_ref(v_arg_3510_);
v___x_3511_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3508_);
v___x_3512_ = l_Lean_Expr_isApp(v___x_3511_);
if (v___x_3512_ == 0)
{
lean_dec_ref(v___x_3511_);
lean_dec_ref(v_arg_3510_);
lean_dec_ref(v_arg_3507_);
lean_dec_ref(v_arg_3504_);
lean_dec(v_a_3490_);
lean_dec_ref(v_a_3489_);
lean_dec(v_a_3488_);
lean_dec_ref(v_a_3487_);
lean_dec(v_a_3486_);
lean_dec_ref(v_a_3485_);
lean_dec(v_a_3484_);
lean_dec_ref(v_a_3483_);
lean_dec(v_a_3482_);
lean_dec(v_a_3481_);
lean_dec_ref(v_e_3480_);
goto v___jp_3497_;
}
else
{
lean_object* v___x_3513_; lean_object* v___x_3514_; uint8_t v___x_3515_; 
v___x_3513_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3511_);
v___x_3514_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2));
v___x_3515_ = l_Lean_Expr_isConstOf(v___x_3513_, v___x_3514_);
lean_dec_ref(v___x_3513_);
if (v___x_3515_ == 0)
{
lean_dec_ref(v_arg_3510_);
lean_dec_ref(v_arg_3507_);
lean_dec_ref(v_arg_3504_);
lean_dec(v_a_3490_);
lean_dec_ref(v_a_3489_);
lean_dec(v_a_3488_);
lean_dec_ref(v_a_3487_);
lean_dec(v_a_3486_);
lean_dec_ref(v_a_3485_);
lean_dec(v_a_3484_);
lean_dec_ref(v_a_3483_);
lean_dec(v_a_3482_);
lean_dec(v_a_3481_);
lean_dec_ref(v_e_3480_);
goto v___jp_3497_;
}
else
{
lean_object* v___x_3516_; 
lean_del_object(v___x_3495_);
v___x_3516_ = l_Lean_Meta_Structural_isInstLEInt___redArg(v_arg_3510_, v_a_3488_);
if (lean_obj_tag(v___x_3516_) == 0)
{
lean_object* v_a_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3599_; 
v_a_3517_ = lean_ctor_get(v___x_3516_, 0);
v_isSharedCheck_3599_ = !lean_is_exclusive(v___x_3516_);
if (v_isSharedCheck_3599_ == 0)
{
v___x_3519_ = v___x_3516_;
v_isShared_3520_ = v_isSharedCheck_3599_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_a_3517_);
lean_dec(v___x_3516_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3599_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
uint8_t v___x_3521_; 
v___x_3521_ = lean_unbox(v_a_3517_);
lean_dec(v_a_3517_);
if (v___x_3521_ == 0)
{
lean_object* v___x_3522_; lean_object* v___x_3524_; 
lean_dec_ref(v_arg_3507_);
lean_dec_ref(v_arg_3504_);
lean_dec(v_a_3490_);
lean_dec_ref(v_a_3489_);
lean_dec(v_a_3488_);
lean_dec_ref(v_a_3487_);
lean_dec(v_a_3486_);
lean_dec_ref(v_a_3485_);
lean_dec(v_a_3484_);
lean_dec_ref(v_a_3483_);
lean_dec(v_a_3482_);
lean_dec(v_a_3481_);
lean_dec_ref(v_e_3480_);
v___x_3522_ = lean_box(0);
if (v_isShared_3520_ == 0)
{
lean_ctor_set(v___x_3519_, 0, v___x_3522_);
v___x_3524_ = v___x_3519_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v___x_3522_);
v___x_3524_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
return v___x_3524_;
}
}
else
{
lean_object* v___x_3526_; 
lean_del_object(v___x_3519_);
lean_inc(v_a_3490_);
lean_inc_ref(v_a_3489_);
lean_inc(v_a_3488_);
lean_inc_ref(v_a_3487_);
v___x_3526_ = l_Lean_Meta_getIntValue_x3f(v_arg_3504_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_);
if (lean_obj_tag(v___x_3526_) == 0)
{
lean_object* v_a_3527_; 
v_a_3527_ = lean_ctor_get(v___x_3526_, 0);
lean_inc(v_a_3527_);
lean_dec_ref(v___x_3526_);
if (lean_obj_tag(v_a_3527_) == 1)
{
lean_object* v_val_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3572_; 
v_val_3528_ = lean_ctor_get(v_a_3527_, 0);
v_isSharedCheck_3572_ = !lean_is_exclusive(v_a_3527_);
if (v_isSharedCheck_3572_ == 0)
{
v___x_3530_ = v_a_3527_;
v_isShared_3531_ = v_isSharedCheck_3572_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_val_3528_);
lean_dec(v_a_3527_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3572_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v___x_3532_; uint8_t v___x_3533_; 
v___x_3532_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6);
v___x_3533_ = lean_int_dec_eq(v_val_3528_, v___x_3532_);
lean_dec(v_val_3528_);
if (v___x_3533_ == 0)
{
lean_object* v___x_3534_; 
lean_del_object(v___x_3530_);
lean_dec_ref(v_arg_3507_);
lean_dec(v_a_3481_);
v___x_3534_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(v_e_3480_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_);
lean_dec(v_a_3490_);
lean_dec_ref(v_a_3489_);
lean_dec(v_a_3488_);
lean_dec_ref(v_a_3487_);
lean_dec(v_a_3486_);
lean_dec_ref(v_a_3485_);
lean_dec(v_a_3484_);
lean_dec_ref(v_a_3483_);
lean_dec(v_a_3482_);
if (lean_obj_tag(v___x_3534_) == 0)
{
lean_object* v___x_3536_; uint8_t v_isShared_3537_; uint8_t v_isSharedCheck_3542_; 
v_isSharedCheck_3542_ = !lean_is_exclusive(v___x_3534_);
if (v_isSharedCheck_3542_ == 0)
{
lean_object* v_unused_3543_; 
v_unused_3543_ = lean_ctor_get(v___x_3534_, 0);
lean_dec(v_unused_3543_);
v___x_3536_ = v___x_3534_;
v_isShared_3537_ = v_isSharedCheck_3542_;
goto v_resetjp_3535_;
}
else
{
lean_dec(v___x_3534_);
v___x_3536_ = lean_box(0);
v_isShared_3537_ = v_isSharedCheck_3542_;
goto v_resetjp_3535_;
}
v_resetjp_3535_:
{
lean_object* v___x_3538_; lean_object* v___x_3540_; 
v___x_3538_ = lean_box(0);
if (v_isShared_3537_ == 0)
{
lean_ctor_set(v___x_3536_, 0, v___x_3538_);
v___x_3540_ = v___x_3536_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v___x_3538_);
v___x_3540_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
return v___x_3540_;
}
}
}
else
{
lean_object* v_a_3544_; lean_object* v___x_3546_; uint8_t v_isShared_3547_; uint8_t v_isSharedCheck_3551_; 
v_a_3544_ = lean_ctor_get(v___x_3534_, 0);
v_isSharedCheck_3551_ = !lean_is_exclusive(v___x_3534_);
if (v_isSharedCheck_3551_ == 0)
{
v___x_3546_ = v___x_3534_;
v_isShared_3547_ = v_isSharedCheck_3551_;
goto v_resetjp_3545_;
}
else
{
lean_inc(v_a_3544_);
lean_dec(v___x_3534_);
v___x_3546_ = lean_box(0);
v_isShared_3547_ = v_isSharedCheck_3551_;
goto v_resetjp_3545_;
}
v_resetjp_3545_:
{
lean_object* v___x_3549_; 
if (v_isShared_3547_ == 0)
{
v___x_3549_ = v___x_3546_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3550_; 
v_reuseFailAlloc_3550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3550_, 0, v_a_3544_);
v___x_3549_ = v_reuseFailAlloc_3550_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
return v___x_3549_;
}
}
}
}
else
{
lean_object* v___x_3552_; 
lean_dec_ref(v_e_3480_);
v___x_3552_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(v_arg_3507_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_);
if (lean_obj_tag(v___x_3552_) == 0)
{
lean_object* v_a_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3563_; 
v_a_3553_ = lean_ctor_get(v___x_3552_, 0);
v_isSharedCheck_3563_ = !lean_is_exclusive(v___x_3552_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3555_ = v___x_3552_;
v_isShared_3556_ = v_isSharedCheck_3563_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_a_3553_);
lean_dec(v___x_3552_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3563_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v___x_3558_; 
if (v_isShared_3531_ == 0)
{
lean_ctor_set(v___x_3530_, 0, v_a_3553_);
v___x_3558_ = v___x_3530_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v_a_3553_);
v___x_3558_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
lean_object* v___x_3560_; 
if (v_isShared_3556_ == 0)
{
lean_ctor_set(v___x_3555_, 0, v___x_3558_);
v___x_3560_ = v___x_3555_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v___x_3558_);
v___x_3560_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
return v___x_3560_;
}
}
}
}
else
{
lean_object* v_a_3564_; lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3571_; 
lean_del_object(v___x_3530_);
v_a_3564_ = lean_ctor_get(v___x_3552_, 0);
v_isSharedCheck_3571_ = !lean_is_exclusive(v___x_3552_);
if (v_isSharedCheck_3571_ == 0)
{
v___x_3566_ = v___x_3552_;
v_isShared_3567_ = v_isSharedCheck_3571_;
goto v_resetjp_3565_;
}
else
{
lean_inc(v_a_3564_);
lean_dec(v___x_3552_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3571_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
lean_object* v___x_3569_; 
if (v_isShared_3567_ == 0)
{
v___x_3569_ = v___x_3566_;
goto v_reusejp_3568_;
}
else
{
lean_object* v_reuseFailAlloc_3570_; 
v_reuseFailAlloc_3570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3570_, 0, v_a_3564_);
v___x_3569_ = v_reuseFailAlloc_3570_;
goto v_reusejp_3568_;
}
v_reusejp_3568_:
{
return v___x_3569_;
}
}
}
}
}
}
else
{
lean_object* v___x_3573_; 
lean_dec(v_a_3527_);
lean_dec_ref(v_arg_3507_);
lean_dec(v_a_3481_);
v___x_3573_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(v_e_3480_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_);
lean_dec(v_a_3490_);
lean_dec_ref(v_a_3489_);
lean_dec(v_a_3488_);
lean_dec_ref(v_a_3487_);
lean_dec(v_a_3486_);
lean_dec_ref(v_a_3485_);
lean_dec(v_a_3484_);
lean_dec_ref(v_a_3483_);
lean_dec(v_a_3482_);
if (lean_obj_tag(v___x_3573_) == 0)
{
lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3581_; 
v_isSharedCheck_3581_ = !lean_is_exclusive(v___x_3573_);
if (v_isSharedCheck_3581_ == 0)
{
lean_object* v_unused_3582_; 
v_unused_3582_ = lean_ctor_get(v___x_3573_, 0);
lean_dec(v_unused_3582_);
v___x_3575_ = v___x_3573_;
v_isShared_3576_ = v_isSharedCheck_3581_;
goto v_resetjp_3574_;
}
else
{
lean_dec(v___x_3573_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3581_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
lean_object* v___x_3577_; lean_object* v___x_3579_; 
v___x_3577_ = lean_box(0);
if (v_isShared_3576_ == 0)
{
lean_ctor_set(v___x_3575_, 0, v___x_3577_);
v___x_3579_ = v___x_3575_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v___x_3577_);
v___x_3579_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
return v___x_3579_;
}
}
}
else
{
lean_object* v_a_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3590_; 
v_a_3583_ = lean_ctor_get(v___x_3573_, 0);
v_isSharedCheck_3590_ = !lean_is_exclusive(v___x_3573_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3585_ = v___x_3573_;
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_a_3583_);
lean_dec(v___x_3573_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v___x_3588_; 
if (v_isShared_3586_ == 0)
{
v___x_3588_ = v___x_3585_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v_a_3583_);
v___x_3588_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
return v___x_3588_;
}
}
}
}
}
else
{
lean_object* v_a_3591_; lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3598_; 
lean_dec_ref(v_arg_3507_);
lean_dec(v_a_3490_);
lean_dec_ref(v_a_3489_);
lean_dec(v_a_3488_);
lean_dec_ref(v_a_3487_);
lean_dec(v_a_3486_);
lean_dec_ref(v_a_3485_);
lean_dec(v_a_3484_);
lean_dec_ref(v_a_3483_);
lean_dec(v_a_3482_);
lean_dec(v_a_3481_);
lean_dec_ref(v_e_3480_);
v_a_3591_ = lean_ctor_get(v___x_3526_, 0);
v_isSharedCheck_3598_ = !lean_is_exclusive(v___x_3526_);
if (v_isSharedCheck_3598_ == 0)
{
v___x_3593_ = v___x_3526_;
v_isShared_3594_ = v_isSharedCheck_3598_;
goto v_resetjp_3592_;
}
else
{
lean_inc(v_a_3591_);
lean_dec(v___x_3526_);
v___x_3593_ = lean_box(0);
v_isShared_3594_ = v_isSharedCheck_3598_;
goto v_resetjp_3592_;
}
v_resetjp_3592_:
{
lean_object* v___x_3596_; 
if (v_isShared_3594_ == 0)
{
v___x_3596_ = v___x_3593_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v_a_3591_);
v___x_3596_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
return v___x_3596_;
}
}
}
}
}
}
else
{
lean_object* v_a_3600_; lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3607_; 
lean_dec_ref(v_arg_3507_);
lean_dec_ref(v_arg_3504_);
lean_dec(v_a_3490_);
lean_dec_ref(v_a_3489_);
lean_dec(v_a_3488_);
lean_dec_ref(v_a_3487_);
lean_dec(v_a_3486_);
lean_dec_ref(v_a_3485_);
lean_dec(v_a_3484_);
lean_dec_ref(v_a_3483_);
lean_dec(v_a_3482_);
lean_dec(v_a_3481_);
lean_dec_ref(v_e_3480_);
v_a_3600_ = lean_ctor_get(v___x_3516_, 0);
v_isSharedCheck_3607_ = !lean_is_exclusive(v___x_3516_);
if (v_isSharedCheck_3607_ == 0)
{
v___x_3602_ = v___x_3516_;
v_isShared_3603_ = v_isSharedCheck_3607_;
goto v_resetjp_3601_;
}
else
{
lean_inc(v_a_3600_);
lean_dec(v___x_3516_);
v___x_3602_ = lean_box(0);
v_isShared_3603_ = v_isSharedCheck_3607_;
goto v_resetjp_3601_;
}
v_resetjp_3601_:
{
lean_object* v___x_3605_; 
if (v_isShared_3603_ == 0)
{
v___x_3605_ = v___x_3602_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v_a_3600_);
v___x_3605_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
return v___x_3605_;
}
}
}
}
}
}
}
}
v___jp_3497_:
{
lean_object* v___x_3498_; lean_object* v___x_3500_; 
v___x_3498_ = lean_box(0);
if (v_isShared_3496_ == 0)
{
lean_ctor_set(v___x_3495_, 0, v___x_3498_);
v___x_3500_ = v___x_3495_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v___x_3498_);
v___x_3500_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
return v___x_3500_;
}
}
}
}
else
{
lean_object* v_a_3609_; lean_object* v___x_3611_; uint8_t v_isShared_3612_; uint8_t v_isSharedCheck_3616_; 
lean_dec(v_a_3490_);
lean_dec_ref(v_a_3489_);
lean_dec(v_a_3488_);
lean_dec_ref(v_a_3487_);
lean_dec(v_a_3486_);
lean_dec_ref(v_a_3485_);
lean_dec(v_a_3484_);
lean_dec_ref(v_a_3483_);
lean_dec(v_a_3482_);
lean_dec(v_a_3481_);
lean_dec_ref(v_e_3480_);
v_a_3609_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3616_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3616_ == 0)
{
v___x_3611_ = v___x_3492_;
v_isShared_3612_ = v_isSharedCheck_3616_;
goto v_resetjp_3610_;
}
else
{
lean_inc(v_a_3609_);
lean_dec(v___x_3492_);
v___x_3611_ = lean_box(0);
v_isShared_3612_ = v_isSharedCheck_3616_;
goto v_resetjp_3610_;
}
v_resetjp_3610_:
{
lean_object* v___x_3614_; 
if (v_isShared_3612_ == 0)
{
v___x_3614_ = v___x_3611_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v_a_3609_);
v___x_3614_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
return v___x_3614_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___boxed(lean_object* v_e_3617_, lean_object* v_a_3618_, lean_object* v_a_3619_, lean_object* v_a_3620_, lean_object* v_a_3621_, lean_object* v_a_3622_, lean_object* v_a_3623_, lean_object* v_a_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_, lean_object* v_a_3628_){
_start:
{
lean_object* v_res_3629_; 
v_res_3629_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f(v_e_3617_, v_a_3618_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_, v_a_3624_, v_a_3625_, v_a_3626_, v_a_3627_);
return v_res_3629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(lean_object* v_c_3630_, lean_object* v_a_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_, lean_object* v_a_3636_, lean_object* v_a_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_){
_start:
{
lean_object* v_p_3642_; lean_object* v___x_3643_; 
v_p_3642_ = lean_ctor_get(v_c_3630_, 0);
lean_inc(v_a_3640_);
lean_inc_ref(v_a_3639_);
lean_inc(v_a_3638_);
lean_inc_ref(v_a_3637_);
lean_inc(v_a_3636_);
lean_inc_ref(v_a_3635_);
lean_inc(v_a_3634_);
lean_inc_ref(v_a_3633_);
lean_inc(v_a_3632_);
lean_inc(v_a_3631_);
lean_inc_ref(v_p_3642_);
v___x_3643_ = l_Int_Linear_Poly_normCommRing_x3f(v_p_3642_, v_a_3631_, v_a_3632_, v_a_3633_, v_a_3634_, v_a_3635_, v_a_3636_, v_a_3637_, v_a_3638_, v_a_3639_, v_a_3640_);
if (lean_obj_tag(v___x_3643_) == 0)
{
lean_object* v_a_3644_; 
v_a_3644_ = lean_ctor_get(v___x_3643_, 0);
lean_inc(v_a_3644_);
lean_dec_ref(v___x_3643_);
if (lean_obj_tag(v_a_3644_) == 1)
{
lean_object* v_val_3645_; lean_object* v_snd_3646_; lean_object* v_fst_3647_; lean_object* v_fst_3648_; lean_object* v_snd_3649_; lean_object* v___x_3651_; uint8_t v_isShared_3652_; uint8_t v_isSharedCheck_3658_; 
v_val_3645_ = lean_ctor_get(v_a_3644_, 0);
lean_inc(v_val_3645_);
lean_dec_ref(v_a_3644_);
v_snd_3646_ = lean_ctor_get(v_val_3645_, 1);
lean_inc(v_snd_3646_);
v_fst_3647_ = lean_ctor_get(v_val_3645_, 0);
lean_inc(v_fst_3647_);
lean_dec(v_val_3645_);
v_fst_3648_ = lean_ctor_get(v_snd_3646_, 0);
v_snd_3649_ = lean_ctor_get(v_snd_3646_, 1);
v_isSharedCheck_3658_ = !lean_is_exclusive(v_snd_3646_);
if (v_isSharedCheck_3658_ == 0)
{
v___x_3651_ = v_snd_3646_;
v_isShared_3652_ = v_isSharedCheck_3658_;
goto v_resetjp_3650_;
}
else
{
lean_inc(v_snd_3649_);
lean_inc(v_fst_3648_);
lean_dec(v_snd_3646_);
v___x_3651_ = lean_box(0);
v_isShared_3652_ = v_isSharedCheck_3658_;
goto v_resetjp_3650_;
}
v_resetjp_3650_:
{
lean_object* v___x_3653_; lean_object* v___x_3655_; 
v___x_3653_ = lean_alloc_ctor(17, 3, 0);
lean_ctor_set(v___x_3653_, 0, v_c_3630_);
lean_ctor_set(v___x_3653_, 1, v_fst_3647_);
lean_ctor_set(v___x_3653_, 2, v_fst_3648_);
if (v_isShared_3652_ == 0)
{
lean_ctor_set(v___x_3651_, 1, v___x_3653_);
lean_ctor_set(v___x_3651_, 0, v_snd_3649_);
v___x_3655_ = v___x_3651_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v_snd_3649_);
lean_ctor_set(v_reuseFailAlloc_3657_, 1, v___x_3653_);
v___x_3655_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
lean_object* v___x_3656_; 
v___x_3656_ = lean_grind_cutsat_assert_le(v___x_3655_, v_a_3631_, v_a_3632_, v_a_3633_, v_a_3634_, v_a_3635_, v_a_3636_, v_a_3637_, v_a_3638_, v_a_3639_, v_a_3640_);
return v___x_3656_;
}
}
}
else
{
lean_object* v___x_3659_; 
lean_dec(v_a_3644_);
v___x_3659_ = lean_grind_cutsat_assert_le(v_c_3630_, v_a_3631_, v_a_3632_, v_a_3633_, v_a_3634_, v_a_3635_, v_a_3636_, v_a_3637_, v_a_3638_, v_a_3639_, v_a_3640_);
return v___x_3659_;
}
}
else
{
lean_object* v_a_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3667_; 
lean_dec(v_a_3640_);
lean_dec_ref(v_a_3639_);
lean_dec(v_a_3638_);
lean_dec_ref(v_a_3637_);
lean_dec(v_a_3636_);
lean_dec_ref(v_a_3635_);
lean_dec(v_a_3634_);
lean_dec_ref(v_a_3633_);
lean_dec(v_a_3632_);
lean_dec(v_a_3631_);
lean_dec_ref(v_c_3630_);
v_a_3660_ = lean_ctor_get(v___x_3643_, 0);
v_isSharedCheck_3667_ = !lean_is_exclusive(v___x_3643_);
if (v_isSharedCheck_3667_ == 0)
{
v___x_3662_ = v___x_3643_;
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_a_3660_);
lean_dec(v___x_3643_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
lean_object* v___x_3665_; 
if (v_isShared_3663_ == 0)
{
v___x_3665_ = v___x_3662_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v_a_3660_);
v___x_3665_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
return v___x_3665_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore___boxed(lean_object* v_c_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_){
_start:
{
lean_object* v_res_3680_; 
v_res_3680_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v_c_3668_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_, v_a_3678_);
return v_res_3680_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0(void){
_start:
{
lean_object* v___x_3681_; lean_object* v___x_3682_; 
v___x_3681_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
v___x_3682_ = lean_int_neg(v___x_3681_);
return v___x_3682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe(lean_object* v_e_3683_, uint8_t v_eqTrue_3684_, lean_object* v_a_3685_, lean_object* v_a_3686_, lean_object* v_a_3687_, lean_object* v_a_3688_, lean_object* v_a_3689_, lean_object* v_a_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_){
_start:
{
lean_object* v___x_3696_; 
lean_inc(v_a_3694_);
lean_inc_ref(v_a_3693_);
lean_inc(v_a_3692_);
lean_inc_ref(v_a_3691_);
lean_inc(v_a_3690_);
lean_inc_ref(v_a_3689_);
lean_inc(v_a_3688_);
lean_inc_ref(v_a_3687_);
lean_inc(v_a_3686_);
lean_inc(v_a_3685_);
lean_inc_ref(v_e_3683_);
v___x_3696_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f(v_e_3683_, v_a_3685_, v_a_3686_, v_a_3687_, v_a_3688_, v_a_3689_, v_a_3690_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_);
if (lean_obj_tag(v___x_3696_) == 0)
{
lean_object* v_a_3697_; lean_object* v___x_3699_; uint8_t v_isShared_3700_; uint8_t v_isSharedCheck_3723_; 
v_a_3697_ = lean_ctor_get(v___x_3696_, 0);
v_isSharedCheck_3723_ = !lean_is_exclusive(v___x_3696_);
if (v_isSharedCheck_3723_ == 0)
{
v___x_3699_ = v___x_3696_;
v_isShared_3700_ = v_isSharedCheck_3723_;
goto v_resetjp_3698_;
}
else
{
lean_inc(v_a_3697_);
lean_dec(v___x_3696_);
v___x_3699_ = lean_box(0);
v_isShared_3700_ = v_isSharedCheck_3723_;
goto v_resetjp_3698_;
}
v_resetjp_3698_:
{
if (lean_obj_tag(v_a_3697_) == 1)
{
lean_del_object(v___x_3699_);
if (v_eqTrue_3684_ == 0)
{
lean_object* v_val_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; 
v_val_3701_ = lean_ctor_get(v_a_3697_, 0);
lean_inc(v_val_3701_);
lean_dec_ref(v_a_3697_);
v___x_3702_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
v___x_3703_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0);
lean_inc(v_val_3701_);
v___x_3704_ = l_Int_Linear_Poly_mul(v_val_3701_, v___x_3703_);
v___x_3705_ = l_Int_Linear_Poly_addConst(v___x_3704_, v___x_3702_);
v___x_3706_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3706_, 0, v_e_3683_);
lean_ctor_set(v___x_3706_, 1, v_val_3701_);
v___x_3707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3707_, 0, v___x_3705_);
lean_ctor_set(v___x_3707_, 1, v___x_3706_);
v___x_3708_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v___x_3707_, v_a_3685_, v_a_3686_, v_a_3687_, v_a_3688_, v_a_3689_, v_a_3690_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_);
return v___x_3708_;
}
else
{
lean_object* v_val_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3718_; 
v_val_3709_ = lean_ctor_get(v_a_3697_, 0);
v_isSharedCheck_3718_ = !lean_is_exclusive(v_a_3697_);
if (v_isSharedCheck_3718_ == 0)
{
v___x_3711_ = v_a_3697_;
v_isShared_3712_ = v_isSharedCheck_3718_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_val_3709_);
lean_dec(v_a_3697_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3718_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
lean_object* v___x_3714_; 
if (v_isShared_3712_ == 0)
{
lean_ctor_set_tag(v___x_3711_, 0);
lean_ctor_set(v___x_3711_, 0, v_e_3683_);
v___x_3714_ = v___x_3711_;
goto v_reusejp_3713_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v_e_3683_);
v___x_3714_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3713_;
}
v_reusejp_3713_:
{
lean_object* v___x_3715_; lean_object* v___x_3716_; 
v___x_3715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3715_, 0, v_val_3709_);
lean_ctor_set(v___x_3715_, 1, v___x_3714_);
v___x_3716_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v___x_3715_, v_a_3685_, v_a_3686_, v_a_3687_, v_a_3688_, v_a_3689_, v_a_3690_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_);
return v___x_3716_;
}
}
}
}
else
{
lean_object* v___x_3719_; lean_object* v___x_3721_; 
lean_dec(v_a_3697_);
lean_dec(v_a_3694_);
lean_dec_ref(v_a_3693_);
lean_dec(v_a_3692_);
lean_dec_ref(v_a_3691_);
lean_dec(v_a_3690_);
lean_dec_ref(v_a_3689_);
lean_dec(v_a_3688_);
lean_dec_ref(v_a_3687_);
lean_dec(v_a_3686_);
lean_dec(v_a_3685_);
lean_dec_ref(v_e_3683_);
v___x_3719_ = lean_box(0);
if (v_isShared_3700_ == 0)
{
lean_ctor_set(v___x_3699_, 0, v___x_3719_);
v___x_3721_ = v___x_3699_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3722_; 
v_reuseFailAlloc_3722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3722_, 0, v___x_3719_);
v___x_3721_ = v_reuseFailAlloc_3722_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
return v___x_3721_;
}
}
}
}
else
{
lean_object* v_a_3724_; lean_object* v___x_3726_; uint8_t v_isShared_3727_; uint8_t v_isSharedCheck_3731_; 
lean_dec(v_a_3694_);
lean_dec_ref(v_a_3693_);
lean_dec(v_a_3692_);
lean_dec_ref(v_a_3691_);
lean_dec(v_a_3690_);
lean_dec_ref(v_a_3689_);
lean_dec(v_a_3688_);
lean_dec_ref(v_a_3687_);
lean_dec(v_a_3686_);
lean_dec(v_a_3685_);
lean_dec_ref(v_e_3683_);
v_a_3724_ = lean_ctor_get(v___x_3696_, 0);
v_isSharedCheck_3731_ = !lean_is_exclusive(v___x_3696_);
if (v_isSharedCheck_3731_ == 0)
{
v___x_3726_ = v___x_3696_;
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
else
{
lean_inc(v_a_3724_);
lean_dec(v___x_3696_);
v___x_3726_ = lean_box(0);
v_isShared_3727_ = v_isSharedCheck_3731_;
goto v_resetjp_3725_;
}
v_resetjp_3725_:
{
lean_object* v___x_3729_; 
if (v_isShared_3727_ == 0)
{
v___x_3729_ = v___x_3726_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v_a_3724_);
v___x_3729_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
return v___x_3729_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___boxed(lean_object* v_e_3732_, lean_object* v_eqTrue_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_, lean_object* v_a_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_, lean_object* v_a_3739_, lean_object* v_a_3740_, lean_object* v_a_3741_, lean_object* v_a_3742_, lean_object* v_a_3743_, lean_object* v_a_3744_){
_start:
{
uint8_t v_eqTrue_boxed_3745_; lean_object* v_res_3746_; 
v_eqTrue_boxed_3745_ = lean_unbox(v_eqTrue_3733_);
v_res_3746_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe(v_e_3732_, v_eqTrue_boxed_3745_, v_a_3734_, v_a_3735_, v_a_3736_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_, v_a_3741_, v_a_3742_, v_a_3743_);
return v_res_3746_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0(void){
_start:
{
lean_object* v___x_3747_; lean_object* v___x_3748_; 
v___x_3747_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
v___x_3748_ = l_Lean_mkIntLit(v___x_3747_);
return v___x_3748_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5(void){
_start:
{
lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; 
v___x_3756_ = lean_box(0);
v___x_3757_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__4));
v___x_3758_ = l_Lean_mkConst(v___x_3757_, v___x_3756_);
return v___x_3758_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8(void){
_start:
{
lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; 
v___x_3764_ = lean_box(0);
v___x_3765_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__7));
v___x_3766_ = l_Lean_mkConst(v___x_3765_, v___x_3764_);
return v___x_3766_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe(lean_object* v_e_3767_, uint8_t v_eqTrue_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_){
_start:
{
lean_object* v___y_3781_; lean_object* v___y_3782_; lean_object* v_fst_3783_; lean_object* v_snd_3784_; lean_object* v___x_3813_; uint8_t v___x_3814_; 
lean_inc_ref(v_e_3767_);
v___x_3813_ = l_Lean_Expr_cleanupAnnotations(v_e_3767_);
v___x_3814_ = l_Lean_Expr_isApp(v___x_3813_);
if (v___x_3814_ == 0)
{
lean_dec_ref(v___x_3813_);
lean_dec(v_a_3778_);
lean_dec_ref(v_a_3777_);
lean_dec(v_a_3776_);
lean_dec_ref(v_a_3775_);
lean_dec(v_a_3774_);
lean_dec_ref(v_a_3773_);
lean_dec(v_a_3772_);
lean_dec_ref(v_a_3771_);
lean_dec(v_a_3770_);
lean_dec(v_a_3769_);
lean_dec_ref(v_e_3767_);
goto v___jp_3810_;
}
else
{
lean_object* v_arg_3815_; lean_object* v___x_3816_; uint8_t v___x_3817_; 
v_arg_3815_ = lean_ctor_get(v___x_3813_, 1);
lean_inc_ref(v_arg_3815_);
v___x_3816_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3813_);
v___x_3817_ = l_Lean_Expr_isApp(v___x_3816_);
if (v___x_3817_ == 0)
{
lean_dec_ref(v___x_3816_);
lean_dec_ref(v_arg_3815_);
lean_dec(v_a_3778_);
lean_dec_ref(v_a_3777_);
lean_dec(v_a_3776_);
lean_dec_ref(v_a_3775_);
lean_dec(v_a_3774_);
lean_dec_ref(v_a_3773_);
lean_dec(v_a_3772_);
lean_dec_ref(v_a_3771_);
lean_dec(v_a_3770_);
lean_dec(v_a_3769_);
lean_dec_ref(v_e_3767_);
goto v___jp_3810_;
}
else
{
lean_object* v_arg_3818_; lean_object* v___y_3820_; lean_object* v___x_3858_; uint8_t v___x_3859_; 
v_arg_3818_ = lean_ctor_get(v___x_3816_, 1);
lean_inc_ref(v_arg_3818_);
v___x_3858_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3816_);
v___x_3859_ = l_Lean_Expr_isApp(v___x_3858_);
if (v___x_3859_ == 0)
{
lean_dec_ref(v___x_3858_);
lean_dec_ref(v_arg_3818_);
lean_dec_ref(v_arg_3815_);
lean_dec(v_a_3778_);
lean_dec_ref(v_a_3777_);
lean_dec(v_a_3776_);
lean_dec_ref(v_a_3775_);
lean_dec(v_a_3774_);
lean_dec_ref(v_a_3773_);
lean_dec(v_a_3772_);
lean_dec_ref(v_a_3771_);
lean_dec(v_a_3770_);
lean_dec(v_a_3769_);
lean_dec_ref(v_e_3767_);
goto v___jp_3810_;
}
else
{
lean_object* v___x_3860_; uint8_t v___x_3861_; 
v___x_3860_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3858_);
v___x_3861_ = l_Lean_Expr_isApp(v___x_3860_);
if (v___x_3861_ == 0)
{
lean_dec_ref(v___x_3860_);
lean_dec_ref(v_arg_3818_);
lean_dec_ref(v_arg_3815_);
lean_dec(v_a_3778_);
lean_dec_ref(v_a_3777_);
lean_dec(v_a_3776_);
lean_dec_ref(v_a_3775_);
lean_dec(v_a_3774_);
lean_dec_ref(v_a_3773_);
lean_dec(v_a_3772_);
lean_dec_ref(v_a_3771_);
lean_dec(v_a_3770_);
lean_dec(v_a_3769_);
lean_dec_ref(v_e_3767_);
goto v___jp_3810_;
}
else
{
lean_object* v___x_3862_; lean_object* v___x_3863_; uint8_t v___x_3864_; 
v___x_3862_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3860_);
v___x_3863_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2));
v___x_3864_ = l_Lean_Expr_isConstOf(v___x_3862_, v___x_3863_);
lean_dec_ref(v___x_3862_);
if (v___x_3864_ == 0)
{
lean_dec_ref(v_arg_3818_);
lean_dec_ref(v_arg_3815_);
lean_dec(v_a_3778_);
lean_dec_ref(v_a_3777_);
lean_dec(v_a_3776_);
lean_dec_ref(v_a_3775_);
lean_dec(v_a_3774_);
lean_dec_ref(v_a_3773_);
lean_dec(v_a_3772_);
lean_dec_ref(v_a_3771_);
lean_dec(v_a_3770_);
lean_dec(v_a_3769_);
lean_dec_ref(v_e_3767_);
goto v___jp_3810_;
}
else
{
if (v_eqTrue_3768_ == 0)
{
lean_object* v___x_3865_; 
v___x_3865_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5);
v___y_3820_ = v___x_3865_;
goto v___jp_3819_;
}
else
{
lean_object* v___x_3866_; 
v___x_3866_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8);
v___y_3820_ = v___x_3866_;
goto v___jp_3819_;
}
}
}
}
v___jp_3819_:
{
lean_object* v___x_3821_; 
v___x_3821_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_3767_, v_a_3769_);
if (lean_obj_tag(v___x_3821_) == 0)
{
lean_object* v_a_3822_; lean_object* v___x_3823_; 
v_a_3822_ = lean_ctor_get(v___x_3821_, 0);
lean_inc(v_a_3822_);
lean_dec_ref(v___x_3821_);
lean_inc(v_a_3778_);
lean_inc_ref(v_a_3777_);
lean_inc(v_a_3776_);
lean_inc_ref(v_a_3775_);
lean_inc(v_a_3774_);
lean_inc_ref(v_a_3773_);
lean_inc(v_a_3772_);
lean_inc_ref(v_a_3771_);
lean_inc(v_a_3770_);
lean_inc(v_a_3769_);
lean_inc_ref(v_arg_3818_);
v___x_3823_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_3818_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_);
if (lean_obj_tag(v___x_3823_) == 0)
{
lean_object* v_a_3824_; lean_object* v_fst_3825_; lean_object* v_snd_3826_; lean_object* v___x_3827_; 
v_a_3824_ = lean_ctor_get(v___x_3823_, 0);
lean_inc(v_a_3824_);
lean_dec_ref(v___x_3823_);
v_fst_3825_ = lean_ctor_get(v_a_3824_, 0);
lean_inc(v_fst_3825_);
v_snd_3826_ = lean_ctor_get(v_a_3824_, 1);
lean_inc(v_snd_3826_);
lean_dec(v_a_3824_);
lean_inc(v_a_3778_);
lean_inc_ref(v_a_3777_);
lean_inc(v_a_3776_);
lean_inc_ref(v_a_3775_);
lean_inc(v_a_3774_);
lean_inc_ref(v_a_3773_);
lean_inc(v_a_3772_);
lean_inc_ref(v_a_3771_);
lean_inc(v_a_3770_);
lean_inc(v_a_3769_);
lean_inc_ref(v_arg_3815_);
v___x_3827_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_3815_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_);
if (lean_obj_tag(v___x_3827_) == 0)
{
lean_object* v_a_3828_; lean_object* v_fst_3829_; lean_object* v_snd_3830_; lean_object* v___x_3831_; 
v_a_3828_ = lean_ctor_get(v___x_3827_, 0);
lean_inc(v_a_3828_);
lean_dec_ref(v___x_3827_);
v_fst_3829_ = lean_ctor_get(v_a_3828_, 0);
lean_inc(v_fst_3829_);
v_snd_3830_ = lean_ctor_get(v_a_3828_, 1);
lean_inc(v_snd_3830_);
lean_dec(v_a_3828_);
lean_inc(v_fst_3829_);
lean_inc(v_fst_3825_);
v___x_3831_ = l_Lean_mkApp6(v___y_3820_, v_arg_3818_, v_arg_3815_, v_fst_3825_, v_fst_3829_, v_snd_3826_, v_snd_3830_);
if (v_eqTrue_3768_ == 0)
{
lean_object* v___x_3832_; lean_object* v___x_3833_; 
v___x_3832_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0);
v___x_3833_ = l_Lean_mkIntAdd(v_fst_3829_, v___x_3832_);
v___y_3781_ = v_a_3822_;
v___y_3782_ = v___x_3831_;
v_fst_3783_ = v___x_3833_;
v_snd_3784_ = v_fst_3825_;
goto v___jp_3780_;
}
else
{
v___y_3781_ = v_a_3822_;
v___y_3782_ = v___x_3831_;
v_fst_3783_ = v_fst_3825_;
v_snd_3784_ = v_fst_3829_;
goto v___jp_3780_;
}
}
else
{
lean_object* v_a_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3841_; 
lean_dec(v_snd_3826_);
lean_dec(v_fst_3825_);
lean_dec(v_a_3822_);
lean_dec_ref(v___y_3820_);
lean_dec_ref(v_arg_3818_);
lean_dec_ref(v_arg_3815_);
lean_dec(v_a_3778_);
lean_dec_ref(v_a_3777_);
lean_dec(v_a_3776_);
lean_dec_ref(v_a_3775_);
lean_dec(v_a_3774_);
lean_dec_ref(v_a_3773_);
lean_dec(v_a_3772_);
lean_dec_ref(v_a_3771_);
lean_dec(v_a_3770_);
lean_dec(v_a_3769_);
lean_dec_ref(v_e_3767_);
v_a_3834_ = lean_ctor_get(v___x_3827_, 0);
v_isSharedCheck_3841_ = !lean_is_exclusive(v___x_3827_);
if (v_isSharedCheck_3841_ == 0)
{
v___x_3836_ = v___x_3827_;
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_a_3834_);
lean_dec(v___x_3827_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v___x_3839_; 
if (v_isShared_3837_ == 0)
{
v___x_3839_ = v___x_3836_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v_a_3834_);
v___x_3839_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
return v___x_3839_;
}
}
}
}
else
{
lean_object* v_a_3842_; lean_object* v___x_3844_; uint8_t v_isShared_3845_; uint8_t v_isSharedCheck_3849_; 
lean_dec(v_a_3822_);
lean_dec_ref(v___y_3820_);
lean_dec_ref(v_arg_3818_);
lean_dec_ref(v_arg_3815_);
lean_dec(v_a_3778_);
lean_dec_ref(v_a_3777_);
lean_dec(v_a_3776_);
lean_dec_ref(v_a_3775_);
lean_dec(v_a_3774_);
lean_dec_ref(v_a_3773_);
lean_dec(v_a_3772_);
lean_dec_ref(v_a_3771_);
lean_dec(v_a_3770_);
lean_dec(v_a_3769_);
lean_dec_ref(v_e_3767_);
v_a_3842_ = lean_ctor_get(v___x_3823_, 0);
v_isSharedCheck_3849_ = !lean_is_exclusive(v___x_3823_);
if (v_isSharedCheck_3849_ == 0)
{
v___x_3844_ = v___x_3823_;
v_isShared_3845_ = v_isSharedCheck_3849_;
goto v_resetjp_3843_;
}
else
{
lean_inc(v_a_3842_);
lean_dec(v___x_3823_);
v___x_3844_ = lean_box(0);
v_isShared_3845_ = v_isSharedCheck_3849_;
goto v_resetjp_3843_;
}
v_resetjp_3843_:
{
lean_object* v___x_3847_; 
if (v_isShared_3845_ == 0)
{
v___x_3847_ = v___x_3844_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v_a_3842_);
v___x_3847_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
return v___x_3847_;
}
}
}
}
else
{
lean_object* v_a_3850_; lean_object* v___x_3852_; uint8_t v_isShared_3853_; uint8_t v_isSharedCheck_3857_; 
lean_dec_ref(v___y_3820_);
lean_dec_ref(v_arg_3818_);
lean_dec_ref(v_arg_3815_);
lean_dec(v_a_3778_);
lean_dec_ref(v_a_3777_);
lean_dec(v_a_3776_);
lean_dec_ref(v_a_3775_);
lean_dec(v_a_3774_);
lean_dec_ref(v_a_3773_);
lean_dec(v_a_3772_);
lean_dec_ref(v_a_3771_);
lean_dec(v_a_3770_);
lean_dec(v_a_3769_);
lean_dec_ref(v_e_3767_);
v_a_3850_ = lean_ctor_get(v___x_3821_, 0);
v_isSharedCheck_3857_ = !lean_is_exclusive(v___x_3821_);
if (v_isSharedCheck_3857_ == 0)
{
v___x_3852_ = v___x_3821_;
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
else
{
lean_inc(v_a_3850_);
lean_dec(v___x_3821_);
v___x_3852_ = lean_box(0);
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
v_resetjp_3851_:
{
lean_object* v___x_3855_; 
if (v_isShared_3853_ == 0)
{
v___x_3855_ = v___x_3852_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v_a_3850_);
v___x_3855_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
return v___x_3855_;
}
}
}
}
}
}
v___jp_3780_:
{
lean_object* v___x_3785_; 
lean_inc(v_a_3778_);
lean_inc_ref(v_a_3777_);
lean_inc(v_a_3776_);
lean_inc_ref(v_a_3775_);
lean_inc(v_a_3774_);
lean_inc_ref(v_a_3773_);
lean_inc(v_a_3772_);
lean_inc_ref(v_a_3771_);
lean_inc(v_a_3770_);
lean_inc(v_a_3769_);
lean_inc(v___y_3781_);
v___x_3785_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_3783_, v___y_3781_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_);
if (lean_obj_tag(v___x_3785_) == 0)
{
lean_object* v_a_3786_; lean_object* v___x_3787_; 
v_a_3786_ = lean_ctor_get(v___x_3785_, 0);
lean_inc(v_a_3786_);
lean_dec_ref(v___x_3785_);
lean_inc(v_a_3778_);
lean_inc_ref(v_a_3777_);
lean_inc(v_a_3776_);
lean_inc_ref(v_a_3775_);
lean_inc(v_a_3774_);
lean_inc_ref(v_a_3773_);
lean_inc(v_a_3772_);
lean_inc_ref(v_a_3771_);
lean_inc(v_a_3770_);
lean_inc(v_a_3769_);
v___x_3787_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_snd_3784_, v___y_3781_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_);
if (lean_obj_tag(v___x_3787_) == 0)
{
lean_object* v_a_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; 
v_a_3788_ = lean_ctor_get(v___x_3787_, 0);
lean_inc(v_a_3788_);
lean_dec_ref(v___x_3787_);
lean_inc(v_a_3788_);
lean_inc(v_a_3786_);
v___x_3789_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3789_, 0, v_a_3786_);
lean_ctor_set(v___x_3789_, 1, v_a_3788_);
v___x_3790_ = l_Int_Linear_Expr_norm(v___x_3789_);
lean_dec_ref(v___x_3789_);
v___x_3791_ = lean_alloc_ctor(2, 4, 1);
lean_ctor_set(v___x_3791_, 0, v_e_3767_);
lean_ctor_set(v___x_3791_, 1, v___y_3782_);
lean_ctor_set(v___x_3791_, 2, v_a_3786_);
lean_ctor_set(v___x_3791_, 3, v_a_3788_);
lean_ctor_set_uint8(v___x_3791_, sizeof(void*)*4, v_eqTrue_3768_);
v___x_3792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3792_, 0, v___x_3790_);
lean_ctor_set(v___x_3792_, 1, v___x_3791_);
v___x_3793_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v___x_3792_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_);
return v___x_3793_;
}
else
{
lean_object* v_a_3794_; lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3801_; 
lean_dec(v_a_3786_);
lean_dec_ref(v___y_3782_);
lean_dec(v_a_3778_);
lean_dec_ref(v_a_3777_);
lean_dec(v_a_3776_);
lean_dec_ref(v_a_3775_);
lean_dec(v_a_3774_);
lean_dec_ref(v_a_3773_);
lean_dec(v_a_3772_);
lean_dec_ref(v_a_3771_);
lean_dec(v_a_3770_);
lean_dec(v_a_3769_);
lean_dec_ref(v_e_3767_);
v_a_3794_ = lean_ctor_get(v___x_3787_, 0);
v_isSharedCheck_3801_ = !lean_is_exclusive(v___x_3787_);
if (v_isSharedCheck_3801_ == 0)
{
v___x_3796_ = v___x_3787_;
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
else
{
lean_inc(v_a_3794_);
lean_dec(v___x_3787_);
v___x_3796_ = lean_box(0);
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
v_resetjp_3795_:
{
lean_object* v___x_3799_; 
if (v_isShared_3797_ == 0)
{
v___x_3799_ = v___x_3796_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v_a_3794_);
v___x_3799_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3798_;
}
v_reusejp_3798_:
{
return v___x_3799_;
}
}
}
}
else
{
lean_object* v_a_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3809_; 
lean_dec_ref(v_snd_3784_);
lean_dec_ref(v___y_3782_);
lean_dec(v___y_3781_);
lean_dec(v_a_3778_);
lean_dec_ref(v_a_3777_);
lean_dec(v_a_3776_);
lean_dec_ref(v_a_3775_);
lean_dec(v_a_3774_);
lean_dec_ref(v_a_3773_);
lean_dec(v_a_3772_);
lean_dec_ref(v_a_3771_);
lean_dec(v_a_3770_);
lean_dec(v_a_3769_);
lean_dec_ref(v_e_3767_);
v_a_3802_ = lean_ctor_get(v___x_3785_, 0);
v_isSharedCheck_3809_ = !lean_is_exclusive(v___x_3785_);
if (v_isSharedCheck_3809_ == 0)
{
v___x_3804_ = v___x_3785_;
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_a_3802_);
lean_dec(v___x_3785_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
lean_object* v___x_3807_; 
if (v_isShared_3805_ == 0)
{
v___x_3807_ = v___x_3804_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v_a_3802_);
v___x_3807_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
return v___x_3807_;
}
}
}
}
v___jp_3810_:
{
lean_object* v___x_3811_; lean_object* v___x_3812_; 
v___x_3811_ = lean_box(0);
v___x_3812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3812_, 0, v___x_3811_);
return v___x_3812_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___boxed(lean_object* v_e_3867_, lean_object* v_eqTrue_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_, lean_object* v_a_3875_, lean_object* v_a_3876_, lean_object* v_a_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_){
_start:
{
uint8_t v_eqTrue_boxed_3880_; lean_object* v_res_3881_; 
v_eqTrue_boxed_3880_ = lean_unbox(v_eqTrue_3868_);
v_res_3881_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe(v_e_3867_, v_eqTrue_boxed_3880_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_, v_a_3876_, v_a_3877_, v_a_3878_);
return v_res_3881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe(lean_object* v_e_3882_, uint8_t v_eqTrue_3883_, lean_object* v_a_3884_, lean_object* v_a_3885_, lean_object* v_a_3886_, lean_object* v_a_3887_, lean_object* v_a_3888_, lean_object* v_a_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_){
_start:
{
lean_object* v___y_3900_; lean_object* v___y_3901_; lean_object* v___y_3902_; lean_object* v___y_3903_; lean_object* v___y_3904_; lean_object* v___y_3905_; lean_object* v___y_3906_; lean_object* v___y_3907_; lean_object* v___y_3908_; lean_object* v___y_3909_; lean_object* v___y_3910_; lean_object* v___y_3911_; lean_object* v_fst_3912_; lean_object* v_snd_3913_; lean_object* v_____x_3940_; lean_object* v___y_3941_; lean_object* v___y_3942_; lean_object* v___y_3943_; lean_object* v___y_3944_; lean_object* v___y_3945_; lean_object* v___y_3946_; lean_object* v___y_3947_; lean_object* v___y_3948_; lean_object* v___y_3949_; lean_object* v___y_3950_; lean_object* v___y_3951_; 
if (v_eqTrue_3883_ == 0)
{
lean_object* v___x_4005_; 
lean_inc(v_a_3894_);
lean_inc_ref(v_a_3893_);
lean_inc(v_a_3892_);
lean_inc_ref(v_a_3891_);
lean_inc(v_a_3884_);
v___x_4005_ = l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLE_x3f___redArg(v_a_3884_, v_a_3885_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_);
if (lean_obj_tag(v___x_4005_) == 0)
{
lean_object* v_a_4006_; 
v_a_4006_ = lean_ctor_get(v___x_4005_, 0);
lean_inc(v_a_4006_);
lean_dec_ref(v___x_4005_);
v_____x_3940_ = v_a_4006_;
v___y_3941_ = v_a_3884_;
v___y_3942_ = v_a_3885_;
v___y_3943_ = v_a_3886_;
v___y_3944_ = v_a_3887_;
v___y_3945_ = v_a_3888_;
v___y_3946_ = v_a_3889_;
v___y_3947_ = v_a_3890_;
v___y_3948_ = v_a_3891_;
v___y_3949_ = v_a_3892_;
v___y_3950_ = v_a_3893_;
v___y_3951_ = v_a_3894_;
goto v___jp_3939_;
}
else
{
lean_object* v_a_4007_; lean_object* v___x_4009_; uint8_t v_isShared_4010_; uint8_t v_isSharedCheck_4014_; 
lean_dec(v_a_3894_);
lean_dec_ref(v_a_3893_);
lean_dec(v_a_3892_);
lean_dec_ref(v_a_3891_);
lean_dec(v_a_3890_);
lean_dec_ref(v_a_3889_);
lean_dec(v_a_3888_);
lean_dec_ref(v_a_3887_);
lean_dec(v_a_3886_);
lean_dec(v_a_3885_);
lean_dec(v_a_3884_);
lean_dec_ref(v_e_3882_);
v_a_4007_ = lean_ctor_get(v___x_4005_, 0);
v_isSharedCheck_4014_ = !lean_is_exclusive(v___x_4005_);
if (v_isSharedCheck_4014_ == 0)
{
v___x_4009_ = v___x_4005_;
v_isShared_4010_ = v_isSharedCheck_4014_;
goto v_resetjp_4008_;
}
else
{
lean_inc(v_a_4007_);
lean_dec(v___x_4005_);
v___x_4009_ = lean_box(0);
v_isShared_4010_ = v_isSharedCheck_4014_;
goto v_resetjp_4008_;
}
v_resetjp_4008_:
{
lean_object* v___x_4012_; 
if (v_isShared_4010_ == 0)
{
v___x_4012_ = v___x_4009_;
goto v_reusejp_4011_;
}
else
{
lean_object* v_reuseFailAlloc_4013_; 
v_reuseFailAlloc_4013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4013_, 0, v_a_4007_);
v___x_4012_ = v_reuseFailAlloc_4013_;
goto v_reusejp_4011_;
}
v_reusejp_4011_:
{
return v___x_4012_;
}
}
}
}
else
{
lean_object* v___x_4015_; 
lean_inc(v_a_3894_);
lean_inc_ref(v_a_3893_);
lean_inc(v_a_3892_);
lean_inc_ref(v_a_3891_);
lean_inc(v_a_3884_);
v___x_4015_ = l_Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f___redArg(v_a_3884_, v_a_3885_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_);
if (lean_obj_tag(v___x_4015_) == 0)
{
lean_object* v_a_4016_; 
v_a_4016_ = lean_ctor_get(v___x_4015_, 0);
lean_inc(v_a_4016_);
lean_dec_ref(v___x_4015_);
v_____x_3940_ = v_a_4016_;
v___y_3941_ = v_a_3884_;
v___y_3942_ = v_a_3885_;
v___y_3943_ = v_a_3886_;
v___y_3944_ = v_a_3887_;
v___y_3945_ = v_a_3888_;
v___y_3946_ = v_a_3889_;
v___y_3947_ = v_a_3890_;
v___y_3948_ = v_a_3891_;
v___y_3949_ = v_a_3892_;
v___y_3950_ = v_a_3893_;
v___y_3951_ = v_a_3894_;
goto v___jp_3939_;
}
else
{
lean_object* v_a_4017_; lean_object* v___x_4019_; uint8_t v_isShared_4020_; uint8_t v_isSharedCheck_4024_; 
lean_dec(v_a_3894_);
lean_dec_ref(v_a_3893_);
lean_dec(v_a_3892_);
lean_dec_ref(v_a_3891_);
lean_dec(v_a_3890_);
lean_dec_ref(v_a_3889_);
lean_dec(v_a_3888_);
lean_dec_ref(v_a_3887_);
lean_dec(v_a_3886_);
lean_dec(v_a_3885_);
lean_dec(v_a_3884_);
lean_dec_ref(v_e_3882_);
v_a_4017_ = lean_ctor_get(v___x_4015_, 0);
v_isSharedCheck_4024_ = !lean_is_exclusive(v___x_4015_);
if (v_isSharedCheck_4024_ == 0)
{
v___x_4019_ = v___x_4015_;
v_isShared_4020_ = v_isSharedCheck_4024_;
goto v_resetjp_4018_;
}
else
{
lean_inc(v_a_4017_);
lean_dec(v___x_4015_);
v___x_4019_ = lean_box(0);
v_isShared_4020_ = v_isSharedCheck_4024_;
goto v_resetjp_4018_;
}
v_resetjp_4018_:
{
lean_object* v___x_4022_; 
if (v_isShared_4020_ == 0)
{
v___x_4022_ = v___x_4019_;
goto v_reusejp_4021_;
}
else
{
lean_object* v_reuseFailAlloc_4023_; 
v_reuseFailAlloc_4023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4023_, 0, v_a_4017_);
v___x_4022_ = v_reuseFailAlloc_4023_;
goto v_reusejp_4021_;
}
v_reusejp_4021_:
{
return v___x_4022_;
}
}
}
}
v___jp_3896_:
{
lean_object* v___x_3897_; lean_object* v___x_3898_; 
v___x_3897_ = lean_box(0);
v___x_3898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3898_, 0, v___x_3897_);
return v___x_3898_;
}
v___jp_3899_:
{
lean_object* v___x_3914_; 
lean_inc(v___y_3903_);
lean_inc_ref(v___y_3910_);
lean_inc(v___y_3904_);
lean_inc_ref(v___y_3901_);
lean_inc(v___y_3907_);
lean_inc_ref(v___y_3902_);
lean_inc(v___y_3906_);
lean_inc_ref(v___y_3908_);
lean_inc(v___y_3900_);
lean_inc(v___y_3905_);
lean_inc(v___y_3909_);
v___x_3914_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_3912_, v___y_3909_, v___y_3905_, v___y_3900_, v___y_3908_, v___y_3906_, v___y_3902_, v___y_3907_, v___y_3901_, v___y_3904_, v___y_3910_, v___y_3903_);
if (lean_obj_tag(v___x_3914_) == 0)
{
lean_object* v_a_3915_; lean_object* v___x_3916_; 
v_a_3915_ = lean_ctor_get(v___x_3914_, 0);
lean_inc(v_a_3915_);
lean_dec_ref(v___x_3914_);
lean_inc(v___y_3903_);
lean_inc_ref(v___y_3910_);
lean_inc(v___y_3904_);
lean_inc_ref(v___y_3901_);
lean_inc(v___y_3907_);
lean_inc_ref(v___y_3902_);
lean_inc(v___y_3906_);
lean_inc_ref(v___y_3908_);
lean_inc(v___y_3900_);
lean_inc(v___y_3905_);
v___x_3916_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_snd_3913_, v___y_3909_, v___y_3905_, v___y_3900_, v___y_3908_, v___y_3906_, v___y_3902_, v___y_3907_, v___y_3901_, v___y_3904_, v___y_3910_, v___y_3903_);
if (lean_obj_tag(v___x_3916_) == 0)
{
lean_object* v_a_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; 
v_a_3917_ = lean_ctor_get(v___x_3916_, 0);
lean_inc(v_a_3917_);
lean_dec_ref(v___x_3916_);
lean_inc(v_a_3917_);
lean_inc(v_a_3915_);
v___x_3918_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3918_, 0, v_a_3915_);
lean_ctor_set(v___x_3918_, 1, v_a_3917_);
v___x_3919_ = l_Int_Linear_Expr_norm(v___x_3918_);
lean_dec_ref(v___x_3918_);
v___x_3920_ = lean_alloc_ctor(2, 4, 1);
lean_ctor_set(v___x_3920_, 0, v_e_3882_);
lean_ctor_set(v___x_3920_, 1, v___y_3911_);
lean_ctor_set(v___x_3920_, 2, v_a_3915_);
lean_ctor_set(v___x_3920_, 3, v_a_3917_);
lean_ctor_set_uint8(v___x_3920_, sizeof(void*)*4, v_eqTrue_3883_);
v___x_3921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3921_, 0, v___x_3919_);
lean_ctor_set(v___x_3921_, 1, v___x_3920_);
v___x_3922_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v___x_3921_, v___y_3905_, v___y_3900_, v___y_3908_, v___y_3906_, v___y_3902_, v___y_3907_, v___y_3901_, v___y_3904_, v___y_3910_, v___y_3903_);
return v___x_3922_;
}
else
{
lean_object* v_a_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3930_; 
lean_dec(v_a_3915_);
lean_dec_ref(v___y_3911_);
lean_dec_ref(v___y_3910_);
lean_dec_ref(v___y_3908_);
lean_dec(v___y_3907_);
lean_dec(v___y_3906_);
lean_dec(v___y_3905_);
lean_dec(v___y_3904_);
lean_dec(v___y_3903_);
lean_dec_ref(v___y_3902_);
lean_dec_ref(v___y_3901_);
lean_dec(v___y_3900_);
lean_dec_ref(v_e_3882_);
v_a_3923_ = lean_ctor_get(v___x_3916_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v___x_3916_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3925_ = v___x_3916_;
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_a_3923_);
lean_dec(v___x_3916_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v___x_3928_; 
if (v_isShared_3926_ == 0)
{
v___x_3928_ = v___x_3925_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v_a_3923_);
v___x_3928_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
return v___x_3928_;
}
}
}
}
else
{
lean_object* v_a_3931_; lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3938_; 
lean_dec_ref(v_snd_3913_);
lean_dec_ref(v___y_3911_);
lean_dec_ref(v___y_3910_);
lean_dec(v___y_3909_);
lean_dec_ref(v___y_3908_);
lean_dec(v___y_3907_);
lean_dec(v___y_3906_);
lean_dec(v___y_3905_);
lean_dec(v___y_3904_);
lean_dec(v___y_3903_);
lean_dec_ref(v___y_3902_);
lean_dec_ref(v___y_3901_);
lean_dec(v___y_3900_);
lean_dec_ref(v_e_3882_);
v_a_3931_ = lean_ctor_get(v___x_3914_, 0);
v_isSharedCheck_3938_ = !lean_is_exclusive(v___x_3914_);
if (v_isSharedCheck_3938_ == 0)
{
v___x_3933_ = v___x_3914_;
v_isShared_3934_ = v_isSharedCheck_3938_;
goto v_resetjp_3932_;
}
else
{
lean_inc(v_a_3931_);
lean_dec(v___x_3914_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_3938_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
lean_object* v___x_3936_; 
if (v_isShared_3934_ == 0)
{
v___x_3936_ = v___x_3933_;
goto v_reusejp_3935_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v_a_3931_);
v___x_3936_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3935_;
}
v_reusejp_3935_:
{
return v___x_3936_;
}
}
}
}
v___jp_3939_:
{
if (lean_obj_tag(v_____x_3940_) == 1)
{
lean_object* v_val_3952_; lean_object* v___x_3953_; uint8_t v___x_3954_; 
v_val_3952_ = lean_ctor_get(v_____x_3940_, 0);
lean_inc(v_val_3952_);
lean_dec_ref(v_____x_3940_);
lean_inc_ref(v_e_3882_);
v___x_3953_ = l_Lean_Expr_cleanupAnnotations(v_e_3882_);
v___x_3954_ = l_Lean_Expr_isApp(v___x_3953_);
if (v___x_3954_ == 0)
{
lean_dec_ref(v___x_3953_);
lean_dec(v_val_3952_);
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3950_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3946_);
lean_dec(v___y_3945_);
lean_dec_ref(v___y_3944_);
lean_dec(v___y_3943_);
lean_dec(v___y_3942_);
lean_dec(v___y_3941_);
lean_dec_ref(v_e_3882_);
goto v___jp_3896_;
}
else
{
lean_object* v_arg_3955_; lean_object* v___x_3956_; uint8_t v___x_3957_; 
v_arg_3955_ = lean_ctor_get(v___x_3953_, 1);
lean_inc_ref(v_arg_3955_);
v___x_3956_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3953_);
v___x_3957_ = l_Lean_Expr_isApp(v___x_3956_);
if (v___x_3957_ == 0)
{
lean_dec_ref(v___x_3956_);
lean_dec_ref(v_arg_3955_);
lean_dec(v_val_3952_);
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3950_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3946_);
lean_dec(v___y_3945_);
lean_dec_ref(v___y_3944_);
lean_dec(v___y_3943_);
lean_dec(v___y_3942_);
lean_dec(v___y_3941_);
lean_dec_ref(v_e_3882_);
goto v___jp_3896_;
}
else
{
lean_object* v_arg_3958_; lean_object* v___x_3959_; uint8_t v___x_3960_; 
v_arg_3958_ = lean_ctor_get(v___x_3956_, 1);
lean_inc_ref(v_arg_3958_);
v___x_3959_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3956_);
v___x_3960_ = l_Lean_Expr_isApp(v___x_3959_);
if (v___x_3960_ == 0)
{
lean_dec_ref(v___x_3959_);
lean_dec_ref(v_arg_3958_);
lean_dec_ref(v_arg_3955_);
lean_dec(v_val_3952_);
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3950_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3946_);
lean_dec(v___y_3945_);
lean_dec_ref(v___y_3944_);
lean_dec(v___y_3943_);
lean_dec(v___y_3942_);
lean_dec(v___y_3941_);
lean_dec_ref(v_e_3882_);
goto v___jp_3896_;
}
else
{
lean_object* v___x_3961_; uint8_t v___x_3962_; 
v___x_3961_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3959_);
v___x_3962_ = l_Lean_Expr_isApp(v___x_3961_);
if (v___x_3962_ == 0)
{
lean_dec_ref(v___x_3961_);
lean_dec_ref(v_arg_3958_);
lean_dec_ref(v_arg_3955_);
lean_dec(v_val_3952_);
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3950_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3946_);
lean_dec(v___y_3945_);
lean_dec_ref(v___y_3944_);
lean_dec(v___y_3943_);
lean_dec(v___y_3942_);
lean_dec(v___y_3941_);
lean_dec_ref(v_e_3882_);
goto v___jp_3896_;
}
else
{
lean_object* v___x_3963_; lean_object* v___x_3964_; uint8_t v___x_3965_; 
v___x_3963_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3961_);
v___x_3964_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2));
v___x_3965_ = l_Lean_Expr_isConstOf(v___x_3963_, v___x_3964_);
lean_dec_ref(v___x_3963_);
if (v___x_3965_ == 0)
{
lean_dec_ref(v_arg_3958_);
lean_dec_ref(v_arg_3955_);
lean_dec(v_val_3952_);
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3950_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3946_);
lean_dec(v___y_3945_);
lean_dec_ref(v___y_3944_);
lean_dec(v___y_3943_);
lean_dec(v___y_3942_);
lean_dec(v___y_3941_);
lean_dec_ref(v_e_3882_);
goto v___jp_3896_;
}
else
{
lean_object* v___x_3966_; 
v___x_3966_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_3882_, v___y_3942_);
if (lean_obj_tag(v___x_3966_) == 0)
{
lean_object* v_a_3967_; lean_object* v___x_3968_; 
v_a_3967_ = lean_ctor_get(v___x_3966_, 0);
lean_inc(v_a_3967_);
lean_dec_ref(v___x_3966_);
lean_inc(v___y_3951_);
lean_inc_ref(v___y_3950_);
lean_inc(v___y_3949_);
lean_inc_ref(v___y_3948_);
lean_inc(v___y_3947_);
lean_inc_ref(v___y_3946_);
lean_inc(v___y_3945_);
lean_inc_ref(v___y_3944_);
lean_inc(v___y_3943_);
lean_inc(v___y_3942_);
lean_inc(v___y_3941_);
lean_inc_ref(v_arg_3958_);
v___x_3968_ = l_Lean_Meta_Grind_Arith_Cutsat_toInt(v_arg_3958_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_);
if (lean_obj_tag(v___x_3968_) == 0)
{
lean_object* v_a_3969_; lean_object* v_fst_3970_; lean_object* v_snd_3971_; lean_object* v___x_3972_; 
v_a_3969_ = lean_ctor_get(v___x_3968_, 0);
lean_inc(v_a_3969_);
lean_dec_ref(v___x_3968_);
v_fst_3970_ = lean_ctor_get(v_a_3969_, 0);
lean_inc(v_fst_3970_);
v_snd_3971_ = lean_ctor_get(v_a_3969_, 1);
lean_inc(v_snd_3971_);
lean_dec(v_a_3969_);
lean_inc(v___y_3951_);
lean_inc_ref(v___y_3950_);
lean_inc(v___y_3949_);
lean_inc_ref(v___y_3948_);
lean_inc(v___y_3947_);
lean_inc_ref(v___y_3946_);
lean_inc(v___y_3945_);
lean_inc_ref(v___y_3944_);
lean_inc(v___y_3943_);
lean_inc(v___y_3942_);
lean_inc_ref(v_arg_3955_);
v___x_3972_ = l_Lean_Meta_Grind_Arith_Cutsat_toInt(v_arg_3955_, v___y_3941_, v___y_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_, v___y_3951_);
if (lean_obj_tag(v___x_3972_) == 0)
{
lean_object* v_a_3973_; lean_object* v_fst_3974_; lean_object* v_snd_3975_; lean_object* v___x_3976_; 
v_a_3973_ = lean_ctor_get(v___x_3972_, 0);
lean_inc(v_a_3973_);
lean_dec_ref(v___x_3972_);
v_fst_3974_ = lean_ctor_get(v_a_3973_, 0);
lean_inc(v_fst_3974_);
v_snd_3975_ = lean_ctor_get(v_a_3973_, 1);
lean_inc(v_snd_3975_);
lean_dec(v_a_3973_);
lean_inc(v_fst_3974_);
lean_inc(v_fst_3970_);
v___x_3976_ = l_Lean_mkApp6(v_val_3952_, v_arg_3958_, v_arg_3955_, v_fst_3970_, v_fst_3974_, v_snd_3971_, v_snd_3975_);
if (v_eqTrue_3883_ == 0)
{
lean_object* v___x_3977_; lean_object* v___x_3978_; 
v___x_3977_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0);
v___x_3978_ = l_Lean_mkIntAdd(v_fst_3974_, v___x_3977_);
v___y_3900_ = v___y_3943_;
v___y_3901_ = v___y_3948_;
v___y_3902_ = v___y_3946_;
v___y_3903_ = v___y_3951_;
v___y_3904_ = v___y_3949_;
v___y_3905_ = v___y_3942_;
v___y_3906_ = v___y_3945_;
v___y_3907_ = v___y_3947_;
v___y_3908_ = v___y_3944_;
v___y_3909_ = v_a_3967_;
v___y_3910_ = v___y_3950_;
v___y_3911_ = v___x_3976_;
v_fst_3912_ = v___x_3978_;
v_snd_3913_ = v_fst_3970_;
goto v___jp_3899_;
}
else
{
v___y_3900_ = v___y_3943_;
v___y_3901_ = v___y_3948_;
v___y_3902_ = v___y_3946_;
v___y_3903_ = v___y_3951_;
v___y_3904_ = v___y_3949_;
v___y_3905_ = v___y_3942_;
v___y_3906_ = v___y_3945_;
v___y_3907_ = v___y_3947_;
v___y_3908_ = v___y_3944_;
v___y_3909_ = v_a_3967_;
v___y_3910_ = v___y_3950_;
v___y_3911_ = v___x_3976_;
v_fst_3912_ = v_fst_3970_;
v_snd_3913_ = v_fst_3974_;
goto v___jp_3899_;
}
}
else
{
lean_object* v_a_3979_; lean_object* v___x_3981_; uint8_t v_isShared_3982_; uint8_t v_isSharedCheck_3986_; 
lean_dec(v_snd_3971_);
lean_dec(v_fst_3970_);
lean_dec(v_a_3967_);
lean_dec_ref(v_arg_3958_);
lean_dec_ref(v_arg_3955_);
lean_dec(v_val_3952_);
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3950_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3946_);
lean_dec(v___y_3945_);
lean_dec_ref(v___y_3944_);
lean_dec(v___y_3943_);
lean_dec(v___y_3942_);
lean_dec_ref(v_e_3882_);
v_a_3979_ = lean_ctor_get(v___x_3972_, 0);
v_isSharedCheck_3986_ = !lean_is_exclusive(v___x_3972_);
if (v_isSharedCheck_3986_ == 0)
{
v___x_3981_ = v___x_3972_;
v_isShared_3982_ = v_isSharedCheck_3986_;
goto v_resetjp_3980_;
}
else
{
lean_inc(v_a_3979_);
lean_dec(v___x_3972_);
v___x_3981_ = lean_box(0);
v_isShared_3982_ = v_isSharedCheck_3986_;
goto v_resetjp_3980_;
}
v_resetjp_3980_:
{
lean_object* v___x_3984_; 
if (v_isShared_3982_ == 0)
{
v___x_3984_ = v___x_3981_;
goto v_reusejp_3983_;
}
else
{
lean_object* v_reuseFailAlloc_3985_; 
v_reuseFailAlloc_3985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3985_, 0, v_a_3979_);
v___x_3984_ = v_reuseFailAlloc_3985_;
goto v_reusejp_3983_;
}
v_reusejp_3983_:
{
return v___x_3984_;
}
}
}
}
else
{
lean_object* v_a_3987_; lean_object* v___x_3989_; uint8_t v_isShared_3990_; uint8_t v_isSharedCheck_3994_; 
lean_dec(v_a_3967_);
lean_dec_ref(v_arg_3958_);
lean_dec_ref(v_arg_3955_);
lean_dec(v_val_3952_);
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3950_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3946_);
lean_dec(v___y_3945_);
lean_dec_ref(v___y_3944_);
lean_dec(v___y_3943_);
lean_dec(v___y_3942_);
lean_dec(v___y_3941_);
lean_dec_ref(v_e_3882_);
v_a_3987_ = lean_ctor_get(v___x_3968_, 0);
v_isSharedCheck_3994_ = !lean_is_exclusive(v___x_3968_);
if (v_isSharedCheck_3994_ == 0)
{
v___x_3989_ = v___x_3968_;
v_isShared_3990_ = v_isSharedCheck_3994_;
goto v_resetjp_3988_;
}
else
{
lean_inc(v_a_3987_);
lean_dec(v___x_3968_);
v___x_3989_ = lean_box(0);
v_isShared_3990_ = v_isSharedCheck_3994_;
goto v_resetjp_3988_;
}
v_resetjp_3988_:
{
lean_object* v___x_3992_; 
if (v_isShared_3990_ == 0)
{
v___x_3992_ = v___x_3989_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v_a_3987_);
v___x_3992_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
return v___x_3992_;
}
}
}
}
else
{
lean_object* v_a_3995_; lean_object* v___x_3997_; uint8_t v_isShared_3998_; uint8_t v_isSharedCheck_4002_; 
lean_dec_ref(v_arg_3958_);
lean_dec_ref(v_arg_3955_);
lean_dec(v_val_3952_);
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3950_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3946_);
lean_dec(v___y_3945_);
lean_dec_ref(v___y_3944_);
lean_dec(v___y_3943_);
lean_dec(v___y_3942_);
lean_dec(v___y_3941_);
lean_dec_ref(v_e_3882_);
v_a_3995_ = lean_ctor_get(v___x_3966_, 0);
v_isSharedCheck_4002_ = !lean_is_exclusive(v___x_3966_);
if (v_isSharedCheck_4002_ == 0)
{
v___x_3997_ = v___x_3966_;
v_isShared_3998_ = v_isSharedCheck_4002_;
goto v_resetjp_3996_;
}
else
{
lean_inc(v_a_3995_);
lean_dec(v___x_3966_);
v___x_3997_ = lean_box(0);
v_isShared_3998_ = v_isSharedCheck_4002_;
goto v_resetjp_3996_;
}
v_resetjp_3996_:
{
lean_object* v___x_4000_; 
if (v_isShared_3998_ == 0)
{
v___x_4000_ = v___x_3997_;
goto v_reusejp_3999_;
}
else
{
lean_object* v_reuseFailAlloc_4001_; 
v_reuseFailAlloc_4001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4001_, 0, v_a_3995_);
v___x_4000_ = v_reuseFailAlloc_4001_;
goto v_reusejp_3999_;
}
v_reusejp_3999_:
{
return v___x_4000_;
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
lean_object* v___x_4003_; lean_object* v___x_4004_; 
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3950_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3946_);
lean_dec(v___y_3945_);
lean_dec_ref(v___y_3944_);
lean_dec(v___y_3943_);
lean_dec(v___y_3942_);
lean_dec(v___y_3941_);
lean_dec(v_____x_3940_);
lean_dec_ref(v_e_3882_);
v___x_4003_ = lean_box(0);
v___x_4004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4004_, 0, v___x_4003_);
return v___x_4004_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe___boxed(lean_object* v_e_4025_, lean_object* v_eqTrue_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_){
_start:
{
uint8_t v_eqTrue_boxed_4039_; lean_object* v_res_4040_; 
v_eqTrue_boxed_4039_ = lean_unbox(v_eqTrue_4026_);
v_res_4040_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe(v_e_4025_, v_eqTrue_boxed_4039_, v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_, v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_, v_a_4037_);
return v_res_4040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe(lean_object* v_e_4046_, uint8_t v_eqTrue_4047_, lean_object* v_a_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_, lean_object* v_a_4051_, lean_object* v_a_4052_, lean_object* v_a_4053_, lean_object* v_a_4054_, lean_object* v_a_4055_, lean_object* v_a_4056_, lean_object* v_a_4057_){
_start:
{
lean_object* v___x_4062_; 
v___x_4062_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_4050_);
if (lean_obj_tag(v___x_4062_) == 0)
{
lean_object* v_a_4063_; lean_object* v___x_4065_; uint8_t v_isShared_4066_; uint8_t v_isSharedCheck_4093_; 
v_a_4063_ = lean_ctor_get(v___x_4062_, 0);
v_isSharedCheck_4093_ = !lean_is_exclusive(v___x_4062_);
if (v_isSharedCheck_4093_ == 0)
{
v___x_4065_ = v___x_4062_;
v_isShared_4066_ = v_isSharedCheck_4093_;
goto v_resetjp_4064_;
}
else
{
lean_inc(v_a_4063_);
lean_dec(v___x_4062_);
v___x_4065_ = lean_box(0);
v_isShared_4066_ = v_isSharedCheck_4093_;
goto v_resetjp_4064_;
}
v_resetjp_4064_:
{
uint8_t v_lia_4067_; 
v_lia_4067_ = lean_ctor_get_uint8(v_a_4063_, sizeof(void*)*11 + 23);
lean_dec(v_a_4063_);
if (v_lia_4067_ == 0)
{
lean_object* v___x_4068_; lean_object* v___x_4070_; 
lean_dec(v_a_4057_);
lean_dec_ref(v_a_4056_);
lean_dec(v_a_4055_);
lean_dec_ref(v_a_4054_);
lean_dec(v_a_4053_);
lean_dec_ref(v_a_4052_);
lean_dec(v_a_4051_);
lean_dec_ref(v_a_4050_);
lean_dec(v_a_4049_);
lean_dec(v_a_4048_);
lean_dec_ref(v_e_4046_);
v___x_4068_ = lean_box(0);
if (v_isShared_4066_ == 0)
{
lean_ctor_set(v___x_4065_, 0, v___x_4068_);
v___x_4070_ = v___x_4065_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v___x_4068_);
v___x_4070_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
return v___x_4070_;
}
}
else
{
lean_object* v___x_4072_; uint8_t v___x_4073_; 
lean_del_object(v___x_4065_);
lean_inc_ref(v_e_4046_);
v___x_4072_ = l_Lean_Expr_cleanupAnnotations(v_e_4046_);
v___x_4073_ = l_Lean_Expr_isApp(v___x_4072_);
if (v___x_4073_ == 0)
{
lean_dec_ref(v___x_4072_);
lean_dec(v_a_4057_);
lean_dec_ref(v_a_4056_);
lean_dec(v_a_4055_);
lean_dec_ref(v_a_4054_);
lean_dec(v_a_4053_);
lean_dec_ref(v_a_4052_);
lean_dec(v_a_4051_);
lean_dec_ref(v_a_4050_);
lean_dec(v_a_4049_);
lean_dec(v_a_4048_);
lean_dec_ref(v_e_4046_);
goto v___jp_4059_;
}
else
{
lean_object* v___x_4074_; uint8_t v___x_4075_; 
v___x_4074_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4072_);
v___x_4075_ = l_Lean_Expr_isApp(v___x_4074_);
if (v___x_4075_ == 0)
{
lean_dec_ref(v___x_4074_);
lean_dec(v_a_4057_);
lean_dec_ref(v_a_4056_);
lean_dec(v_a_4055_);
lean_dec_ref(v_a_4054_);
lean_dec(v_a_4053_);
lean_dec_ref(v_a_4052_);
lean_dec(v_a_4051_);
lean_dec_ref(v_a_4050_);
lean_dec(v_a_4049_);
lean_dec(v_a_4048_);
lean_dec_ref(v_e_4046_);
goto v___jp_4059_;
}
else
{
lean_object* v___x_4076_; uint8_t v___x_4077_; 
v___x_4076_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4074_);
v___x_4077_ = l_Lean_Expr_isApp(v___x_4076_);
if (v___x_4077_ == 0)
{
lean_dec_ref(v___x_4076_);
lean_dec(v_a_4057_);
lean_dec_ref(v_a_4056_);
lean_dec(v_a_4055_);
lean_dec_ref(v_a_4054_);
lean_dec(v_a_4053_);
lean_dec_ref(v_a_4052_);
lean_dec(v_a_4051_);
lean_dec_ref(v_a_4050_);
lean_dec(v_a_4049_);
lean_dec(v_a_4048_);
lean_dec_ref(v_e_4046_);
goto v___jp_4059_;
}
else
{
lean_object* v___x_4078_; uint8_t v___x_4079_; 
v___x_4078_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4076_);
v___x_4079_ = l_Lean_Expr_isApp(v___x_4078_);
if (v___x_4079_ == 0)
{
lean_dec_ref(v___x_4078_);
lean_dec(v_a_4057_);
lean_dec_ref(v_a_4056_);
lean_dec(v_a_4055_);
lean_dec_ref(v_a_4054_);
lean_dec(v_a_4053_);
lean_dec_ref(v_a_4052_);
lean_dec(v_a_4051_);
lean_dec_ref(v_a_4050_);
lean_dec(v_a_4049_);
lean_dec(v_a_4048_);
lean_dec_ref(v_e_4046_);
goto v___jp_4059_;
}
else
{
lean_object* v_arg_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; uint8_t v___x_4083_; 
v_arg_4080_ = lean_ctor_get(v___x_4078_, 1);
lean_inc_ref(v_arg_4080_);
v___x_4081_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4078_);
v___x_4082_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2));
v___x_4083_ = l_Lean_Expr_isConstOf(v___x_4081_, v___x_4082_);
lean_dec_ref(v___x_4081_);
if (v___x_4083_ == 0)
{
lean_dec_ref(v_arg_4080_);
lean_dec(v_a_4057_);
lean_dec_ref(v_a_4056_);
lean_dec(v_a_4055_);
lean_dec_ref(v_a_4054_);
lean_dec(v_a_4053_);
lean_dec_ref(v_a_4052_);
lean_dec(v_a_4051_);
lean_dec_ref(v_a_4050_);
lean_dec(v_a_4049_);
lean_dec(v_a_4048_);
lean_dec_ref(v_e_4046_);
goto v___jp_4059_;
}
else
{
lean_object* v___x_4084_; uint8_t v___x_4085_; 
v___x_4084_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__0));
v___x_4085_ = l_Lean_Expr_isConstOf(v_arg_4080_, v___x_4084_);
if (v___x_4085_ == 0)
{
lean_object* v___x_4086_; uint8_t v___x_4087_; 
v___x_4086_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__2));
v___x_4087_ = l_Lean_Expr_isConstOf(v_arg_4080_, v___x_4086_);
if (v___x_4087_ == 0)
{
lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; 
v___x_4088_ = lean_box(v_eqTrue_4047_);
v___x_4089_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe___boxed), 14, 2);
lean_closure_set(v___x_4089_, 0, v_e_4046_);
lean_closure_set(v___x_4089_, 1, v___x_4088_);
v___x_4090_ = l_Lean_Meta_Grind_Arith_Cutsat_ToIntM_run(v_arg_4080_, v___x_4089_, v_a_4048_, v_a_4049_, v_a_4050_, v_a_4051_, v_a_4052_, v_a_4053_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_);
return v___x_4090_;
}
else
{
lean_object* v___x_4091_; 
lean_dec_ref(v_arg_4080_);
v___x_4091_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe(v_e_4046_, v_eqTrue_4047_, v_a_4048_, v_a_4049_, v_a_4050_, v_a_4051_, v_a_4052_, v_a_4053_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_);
return v___x_4091_;
}
}
else
{
lean_object* v___x_4092_; 
lean_dec_ref(v_arg_4080_);
v___x_4092_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe(v_e_4046_, v_eqTrue_4047_, v_a_4048_, v_a_4049_, v_a_4050_, v_a_4051_, v_a_4052_, v_a_4053_, v_a_4054_, v_a_4055_, v_a_4056_, v_a_4057_);
return v___x_4092_;
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
lean_object* v_a_4094_; lean_object* v___x_4096_; uint8_t v_isShared_4097_; uint8_t v_isSharedCheck_4101_; 
lean_dec(v_a_4057_);
lean_dec_ref(v_a_4056_);
lean_dec(v_a_4055_);
lean_dec_ref(v_a_4054_);
lean_dec(v_a_4053_);
lean_dec_ref(v_a_4052_);
lean_dec(v_a_4051_);
lean_dec_ref(v_a_4050_);
lean_dec(v_a_4049_);
lean_dec(v_a_4048_);
lean_dec_ref(v_e_4046_);
v_a_4094_ = lean_ctor_get(v___x_4062_, 0);
v_isSharedCheck_4101_ = !lean_is_exclusive(v___x_4062_);
if (v_isSharedCheck_4101_ == 0)
{
v___x_4096_ = v___x_4062_;
v_isShared_4097_ = v_isSharedCheck_4101_;
goto v_resetjp_4095_;
}
else
{
lean_inc(v_a_4094_);
lean_dec(v___x_4062_);
v___x_4096_ = lean_box(0);
v_isShared_4097_ = v_isSharedCheck_4101_;
goto v_resetjp_4095_;
}
v_resetjp_4095_:
{
lean_object* v___x_4099_; 
if (v_isShared_4097_ == 0)
{
v___x_4099_ = v___x_4096_;
goto v_reusejp_4098_;
}
else
{
lean_object* v_reuseFailAlloc_4100_; 
v_reuseFailAlloc_4100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4100_, 0, v_a_4094_);
v___x_4099_ = v_reuseFailAlloc_4100_;
goto v_reusejp_4098_;
}
v_reusejp_4098_:
{
return v___x_4099_;
}
}
}
v___jp_4059_:
{
lean_object* v___x_4060_; lean_object* v___x_4061_; 
v___x_4060_ = lean_box(0);
v___x_4061_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4061_, 0, v___x_4060_);
return v___x_4061_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___boxed(lean_object* v_e_4102_, lean_object* v_eqTrue_4103_, lean_object* v_a_4104_, lean_object* v_a_4105_, lean_object* v_a_4106_, lean_object* v_a_4107_, lean_object* v_a_4108_, lean_object* v_a_4109_, lean_object* v_a_4110_, lean_object* v_a_4111_, lean_object* v_a_4112_, lean_object* v_a_4113_, lean_object* v_a_4114_){
_start:
{
uint8_t v_eqTrue_boxed_4115_; lean_object* v_res_4116_; 
v_eqTrue_boxed_4115_ = lean_unbox(v_eqTrue_4103_);
v_res_4116_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLe(v_e_4102_, v_eqTrue_boxed_4115_, v_a_4104_, v_a_4105_, v_a_4106_, v_a_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_);
return v_res_4116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__0(lean_object* v_e_4117_, lean_object* v_arg_4118_, lean_object* v_arg_4119_, uint8_t v_eqTrue_4120_, lean_object* v_____x_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_){
_start:
{
if (lean_obj_tag(v_____x_4121_) == 1)
{
lean_object* v_val_4134_; lean_object* v___x_4135_; 
v_val_4134_ = lean_ctor_get(v_____x_4121_, 0);
lean_inc(v_val_4134_);
lean_dec_ref(v_____x_4121_);
v___x_4135_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_4117_, v___y_4123_);
if (lean_obj_tag(v___x_4135_) == 0)
{
lean_object* v_a_4136_; lean_object* v___x_4137_; 
v_a_4136_ = lean_ctor_get(v___x_4135_, 0);
lean_inc(v_a_4136_);
lean_dec_ref(v___x_4135_);
lean_inc(v___y_4132_);
lean_inc_ref(v___y_4131_);
lean_inc(v___y_4130_);
lean_inc_ref(v___y_4129_);
lean_inc(v___y_4128_);
lean_inc_ref(v___y_4127_);
lean_inc(v___y_4126_);
lean_inc_ref(v___y_4125_);
lean_inc(v___y_4124_);
lean_inc(v___y_4123_);
lean_inc(v___y_4122_);
lean_inc_ref(v_arg_4118_);
v___x_4137_ = l_Lean_Meta_Grind_Arith_Cutsat_toInt(v_arg_4118_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_);
if (lean_obj_tag(v___x_4137_) == 0)
{
lean_object* v_a_4138_; lean_object* v_fst_4139_; lean_object* v_snd_4140_; lean_object* v___x_4142_; uint8_t v_isShared_4143_; uint8_t v_isSharedCheck_4195_; 
v_a_4138_ = lean_ctor_get(v___x_4137_, 0);
lean_inc(v_a_4138_);
lean_dec_ref(v___x_4137_);
v_fst_4139_ = lean_ctor_get(v_a_4138_, 0);
v_snd_4140_ = lean_ctor_get(v_a_4138_, 1);
v_isSharedCheck_4195_ = !lean_is_exclusive(v_a_4138_);
if (v_isSharedCheck_4195_ == 0)
{
v___x_4142_ = v_a_4138_;
v_isShared_4143_ = v_isSharedCheck_4195_;
goto v_resetjp_4141_;
}
else
{
lean_inc(v_snd_4140_);
lean_inc(v_fst_4139_);
lean_dec(v_a_4138_);
v___x_4142_ = lean_box(0);
v_isShared_4143_ = v_isSharedCheck_4195_;
goto v_resetjp_4141_;
}
v_resetjp_4141_:
{
lean_object* v___x_4144_; 
lean_inc(v___y_4132_);
lean_inc_ref(v___y_4131_);
lean_inc(v___y_4130_);
lean_inc_ref(v___y_4129_);
lean_inc(v___y_4128_);
lean_inc_ref(v___y_4127_);
lean_inc(v___y_4126_);
lean_inc_ref(v___y_4125_);
lean_inc(v___y_4124_);
lean_inc(v___y_4123_);
lean_inc_ref(v_arg_4119_);
v___x_4144_ = l_Lean_Meta_Grind_Arith_Cutsat_toInt(v_arg_4119_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_);
if (lean_obj_tag(v___x_4144_) == 0)
{
lean_object* v_a_4145_; lean_object* v_fst_4146_; lean_object* v_snd_4147_; lean_object* v___x_4149_; uint8_t v_isShared_4150_; uint8_t v_isSharedCheck_4186_; 
v_a_4145_ = lean_ctor_get(v___x_4144_, 0);
lean_inc(v_a_4145_);
lean_dec_ref(v___x_4144_);
v_fst_4146_ = lean_ctor_get(v_a_4145_, 0);
v_snd_4147_ = lean_ctor_get(v_a_4145_, 1);
v_isSharedCheck_4186_ = !lean_is_exclusive(v_a_4145_);
if (v_isSharedCheck_4186_ == 0)
{
v___x_4149_ = v_a_4145_;
v_isShared_4150_ = v_isSharedCheck_4186_;
goto v_resetjp_4148_;
}
else
{
lean_inc(v_snd_4147_);
lean_inc(v_fst_4146_);
lean_dec(v_a_4145_);
v___x_4149_ = lean_box(0);
v_isShared_4150_ = v_isSharedCheck_4186_;
goto v_resetjp_4148_;
}
v_resetjp_4148_:
{
lean_object* v___x_4151_; lean_object* v_fst_4153_; lean_object* v_snd_4154_; 
lean_inc(v_fst_4146_);
lean_inc(v_fst_4139_);
v___x_4151_ = l_Lean_mkApp6(v_val_4134_, v_arg_4118_, v_arg_4119_, v_fst_4139_, v_fst_4146_, v_snd_4140_, v_snd_4147_);
if (v_eqTrue_4120_ == 0)
{
v_fst_4153_ = v_fst_4146_;
v_snd_4154_ = v_fst_4139_;
goto v___jp_4152_;
}
else
{
lean_object* v___x_4184_; lean_object* v___x_4185_; 
v___x_4184_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0);
v___x_4185_ = l_Lean_mkIntAdd(v_fst_4139_, v___x_4184_);
v_fst_4153_ = v___x_4185_;
v_snd_4154_ = v_fst_4146_;
goto v___jp_4152_;
}
v___jp_4152_:
{
lean_object* v___x_4155_; 
lean_inc(v___y_4132_);
lean_inc_ref(v___y_4131_);
lean_inc(v___y_4130_);
lean_inc_ref(v___y_4129_);
lean_inc(v___y_4128_);
lean_inc_ref(v___y_4127_);
lean_inc(v___y_4126_);
lean_inc_ref(v___y_4125_);
lean_inc(v___y_4124_);
lean_inc(v___y_4123_);
lean_inc(v_a_4136_);
v___x_4155_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_4153_, v_a_4136_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_);
if (lean_obj_tag(v___x_4155_) == 0)
{
lean_object* v_a_4156_; lean_object* v___x_4157_; 
v_a_4156_ = lean_ctor_get(v___x_4155_, 0);
lean_inc(v_a_4156_);
lean_dec_ref(v___x_4155_);
lean_inc(v___y_4132_);
lean_inc_ref(v___y_4131_);
lean_inc(v___y_4130_);
lean_inc_ref(v___y_4129_);
lean_inc(v___y_4128_);
lean_inc_ref(v___y_4127_);
lean_inc(v___y_4126_);
lean_inc_ref(v___y_4125_);
lean_inc(v___y_4124_);
lean_inc(v___y_4123_);
v___x_4157_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_snd_4154_, v_a_4136_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_);
if (lean_obj_tag(v___x_4157_) == 0)
{
lean_object* v_a_4158_; lean_object* v___x_4160_; 
v_a_4158_ = lean_ctor_get(v___x_4157_, 0);
lean_inc(v_a_4158_);
lean_dec_ref(v___x_4157_);
lean_inc(v_a_4158_);
lean_inc(v_a_4156_);
if (v_isShared_4150_ == 0)
{
lean_ctor_set_tag(v___x_4149_, 3);
lean_ctor_set(v___x_4149_, 1, v_a_4158_);
lean_ctor_set(v___x_4149_, 0, v_a_4156_);
v___x_4160_ = v___x_4149_;
goto v_reusejp_4159_;
}
else
{
lean_object* v_reuseFailAlloc_4167_; 
v_reuseFailAlloc_4167_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4167_, 0, v_a_4156_);
lean_ctor_set(v_reuseFailAlloc_4167_, 1, v_a_4158_);
v___x_4160_ = v_reuseFailAlloc_4167_;
goto v_reusejp_4159_;
}
v_reusejp_4159_:
{
lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4164_; 
v___x_4161_ = l_Int_Linear_Expr_norm(v___x_4160_);
lean_dec_ref(v___x_4160_);
v___x_4162_ = lean_alloc_ctor(2, 4, 1);
lean_ctor_set(v___x_4162_, 0, v_e_4117_);
lean_ctor_set(v___x_4162_, 1, v___x_4151_);
lean_ctor_set(v___x_4162_, 2, v_a_4156_);
lean_ctor_set(v___x_4162_, 3, v_a_4158_);
lean_ctor_set_uint8(v___x_4162_, sizeof(void*)*4, v_eqTrue_4120_);
if (v_isShared_4143_ == 0)
{
lean_ctor_set(v___x_4142_, 1, v___x_4162_);
lean_ctor_set(v___x_4142_, 0, v___x_4161_);
v___x_4164_ = v___x_4142_;
goto v_reusejp_4163_;
}
else
{
lean_object* v_reuseFailAlloc_4166_; 
v_reuseFailAlloc_4166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4166_, 0, v___x_4161_);
lean_ctor_set(v_reuseFailAlloc_4166_, 1, v___x_4162_);
v___x_4164_ = v_reuseFailAlloc_4166_;
goto v_reusejp_4163_;
}
v_reusejp_4163_:
{
lean_object* v___x_4165_; 
v___x_4165_ = lean_grind_cutsat_assert_le(v___x_4164_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_);
return v___x_4165_;
}
}
}
else
{
lean_object* v_a_4168_; lean_object* v___x_4170_; uint8_t v_isShared_4171_; uint8_t v_isSharedCheck_4175_; 
lean_dec(v_a_4156_);
lean_dec_ref(v___x_4151_);
lean_del_object(v___x_4149_);
lean_del_object(v___x_4142_);
lean_dec(v___y_4132_);
lean_dec_ref(v___y_4131_);
lean_dec(v___y_4130_);
lean_dec_ref(v___y_4129_);
lean_dec(v___y_4128_);
lean_dec_ref(v___y_4127_);
lean_dec(v___y_4126_);
lean_dec_ref(v___y_4125_);
lean_dec(v___y_4124_);
lean_dec(v___y_4123_);
lean_dec_ref(v_e_4117_);
v_a_4168_ = lean_ctor_get(v___x_4157_, 0);
v_isSharedCheck_4175_ = !lean_is_exclusive(v___x_4157_);
if (v_isSharedCheck_4175_ == 0)
{
v___x_4170_ = v___x_4157_;
v_isShared_4171_ = v_isSharedCheck_4175_;
goto v_resetjp_4169_;
}
else
{
lean_inc(v_a_4168_);
lean_dec(v___x_4157_);
v___x_4170_ = lean_box(0);
v_isShared_4171_ = v_isSharedCheck_4175_;
goto v_resetjp_4169_;
}
v_resetjp_4169_:
{
lean_object* v___x_4173_; 
if (v_isShared_4171_ == 0)
{
v___x_4173_ = v___x_4170_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v_a_4168_);
v___x_4173_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4172_;
}
v_reusejp_4172_:
{
return v___x_4173_;
}
}
}
}
else
{
lean_object* v_a_4176_; lean_object* v___x_4178_; uint8_t v_isShared_4179_; uint8_t v_isSharedCheck_4183_; 
lean_dec_ref(v_snd_4154_);
lean_dec_ref(v___x_4151_);
lean_del_object(v___x_4149_);
lean_del_object(v___x_4142_);
lean_dec(v_a_4136_);
lean_dec(v___y_4132_);
lean_dec_ref(v___y_4131_);
lean_dec(v___y_4130_);
lean_dec_ref(v___y_4129_);
lean_dec(v___y_4128_);
lean_dec_ref(v___y_4127_);
lean_dec(v___y_4126_);
lean_dec_ref(v___y_4125_);
lean_dec(v___y_4124_);
lean_dec(v___y_4123_);
lean_dec_ref(v_e_4117_);
v_a_4176_ = lean_ctor_get(v___x_4155_, 0);
v_isSharedCheck_4183_ = !lean_is_exclusive(v___x_4155_);
if (v_isSharedCheck_4183_ == 0)
{
v___x_4178_ = v___x_4155_;
v_isShared_4179_ = v_isSharedCheck_4183_;
goto v_resetjp_4177_;
}
else
{
lean_inc(v_a_4176_);
lean_dec(v___x_4155_);
v___x_4178_ = lean_box(0);
v_isShared_4179_ = v_isSharedCheck_4183_;
goto v_resetjp_4177_;
}
v_resetjp_4177_:
{
lean_object* v___x_4181_; 
if (v_isShared_4179_ == 0)
{
v___x_4181_ = v___x_4178_;
goto v_reusejp_4180_;
}
else
{
lean_object* v_reuseFailAlloc_4182_; 
v_reuseFailAlloc_4182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4182_, 0, v_a_4176_);
v___x_4181_ = v_reuseFailAlloc_4182_;
goto v_reusejp_4180_;
}
v_reusejp_4180_:
{
return v___x_4181_;
}
}
}
}
}
}
else
{
lean_object* v_a_4187_; lean_object* v___x_4189_; uint8_t v_isShared_4190_; uint8_t v_isSharedCheck_4194_; 
lean_del_object(v___x_4142_);
lean_dec(v_snd_4140_);
lean_dec(v_fst_4139_);
lean_dec(v_a_4136_);
lean_dec(v_val_4134_);
lean_dec(v___y_4132_);
lean_dec_ref(v___y_4131_);
lean_dec(v___y_4130_);
lean_dec_ref(v___y_4129_);
lean_dec(v___y_4128_);
lean_dec_ref(v___y_4127_);
lean_dec(v___y_4126_);
lean_dec_ref(v___y_4125_);
lean_dec(v___y_4124_);
lean_dec(v___y_4123_);
lean_dec_ref(v_arg_4119_);
lean_dec_ref(v_arg_4118_);
lean_dec_ref(v_e_4117_);
v_a_4187_ = lean_ctor_get(v___x_4144_, 0);
v_isSharedCheck_4194_ = !lean_is_exclusive(v___x_4144_);
if (v_isSharedCheck_4194_ == 0)
{
v___x_4189_ = v___x_4144_;
v_isShared_4190_ = v_isSharedCheck_4194_;
goto v_resetjp_4188_;
}
else
{
lean_inc(v_a_4187_);
lean_dec(v___x_4144_);
v___x_4189_ = lean_box(0);
v_isShared_4190_ = v_isSharedCheck_4194_;
goto v_resetjp_4188_;
}
v_resetjp_4188_:
{
lean_object* v___x_4192_; 
if (v_isShared_4190_ == 0)
{
v___x_4192_ = v___x_4189_;
goto v_reusejp_4191_;
}
else
{
lean_object* v_reuseFailAlloc_4193_; 
v_reuseFailAlloc_4193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4193_, 0, v_a_4187_);
v___x_4192_ = v_reuseFailAlloc_4193_;
goto v_reusejp_4191_;
}
v_reusejp_4191_:
{
return v___x_4192_;
}
}
}
}
}
else
{
lean_object* v_a_4196_; lean_object* v___x_4198_; uint8_t v_isShared_4199_; uint8_t v_isSharedCheck_4203_; 
lean_dec(v_a_4136_);
lean_dec(v_val_4134_);
lean_dec(v___y_4132_);
lean_dec_ref(v___y_4131_);
lean_dec(v___y_4130_);
lean_dec_ref(v___y_4129_);
lean_dec(v___y_4128_);
lean_dec_ref(v___y_4127_);
lean_dec(v___y_4126_);
lean_dec_ref(v___y_4125_);
lean_dec(v___y_4124_);
lean_dec(v___y_4123_);
lean_dec(v___y_4122_);
lean_dec_ref(v_arg_4119_);
lean_dec_ref(v_arg_4118_);
lean_dec_ref(v_e_4117_);
v_a_4196_ = lean_ctor_get(v___x_4137_, 0);
v_isSharedCheck_4203_ = !lean_is_exclusive(v___x_4137_);
if (v_isSharedCheck_4203_ == 0)
{
v___x_4198_ = v___x_4137_;
v_isShared_4199_ = v_isSharedCheck_4203_;
goto v_resetjp_4197_;
}
else
{
lean_inc(v_a_4196_);
lean_dec(v___x_4137_);
v___x_4198_ = lean_box(0);
v_isShared_4199_ = v_isSharedCheck_4203_;
goto v_resetjp_4197_;
}
v_resetjp_4197_:
{
lean_object* v___x_4201_; 
if (v_isShared_4199_ == 0)
{
v___x_4201_ = v___x_4198_;
goto v_reusejp_4200_;
}
else
{
lean_object* v_reuseFailAlloc_4202_; 
v_reuseFailAlloc_4202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4202_, 0, v_a_4196_);
v___x_4201_ = v_reuseFailAlloc_4202_;
goto v_reusejp_4200_;
}
v_reusejp_4200_:
{
return v___x_4201_;
}
}
}
}
else
{
lean_object* v_a_4204_; lean_object* v___x_4206_; uint8_t v_isShared_4207_; uint8_t v_isSharedCheck_4211_; 
lean_dec(v_val_4134_);
lean_dec(v___y_4132_);
lean_dec_ref(v___y_4131_);
lean_dec(v___y_4130_);
lean_dec_ref(v___y_4129_);
lean_dec(v___y_4128_);
lean_dec_ref(v___y_4127_);
lean_dec(v___y_4126_);
lean_dec_ref(v___y_4125_);
lean_dec(v___y_4124_);
lean_dec(v___y_4123_);
lean_dec(v___y_4122_);
lean_dec_ref(v_arg_4119_);
lean_dec_ref(v_arg_4118_);
lean_dec_ref(v_e_4117_);
v_a_4204_ = lean_ctor_get(v___x_4135_, 0);
v_isSharedCheck_4211_ = !lean_is_exclusive(v___x_4135_);
if (v_isSharedCheck_4211_ == 0)
{
v___x_4206_ = v___x_4135_;
v_isShared_4207_ = v_isSharedCheck_4211_;
goto v_resetjp_4205_;
}
else
{
lean_inc(v_a_4204_);
lean_dec(v___x_4135_);
v___x_4206_ = lean_box(0);
v_isShared_4207_ = v_isSharedCheck_4211_;
goto v_resetjp_4205_;
}
v_resetjp_4205_:
{
lean_object* v___x_4209_; 
if (v_isShared_4207_ == 0)
{
v___x_4209_ = v___x_4206_;
goto v_reusejp_4208_;
}
else
{
lean_object* v_reuseFailAlloc_4210_; 
v_reuseFailAlloc_4210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4210_, 0, v_a_4204_);
v___x_4209_ = v_reuseFailAlloc_4210_;
goto v_reusejp_4208_;
}
v_reusejp_4208_:
{
return v___x_4209_;
}
}
}
}
else
{
lean_object* v___x_4212_; lean_object* v___x_4213_; 
lean_dec(v___y_4132_);
lean_dec_ref(v___y_4131_);
lean_dec(v___y_4130_);
lean_dec_ref(v___y_4129_);
lean_dec(v___y_4128_);
lean_dec_ref(v___y_4127_);
lean_dec(v___y_4126_);
lean_dec_ref(v___y_4125_);
lean_dec(v___y_4124_);
lean_dec(v___y_4123_);
lean_dec(v___y_4122_);
lean_dec(v_____x_4121_);
lean_dec_ref(v_arg_4119_);
lean_dec_ref(v_arg_4118_);
lean_dec_ref(v_e_4117_);
v___x_4212_ = lean_box(0);
v___x_4213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4213_, 0, v___x_4212_);
return v___x_4213_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__0___boxed(lean_object** _args){
lean_object* v_e_4214_ = _args[0];
lean_object* v_arg_4215_ = _args[1];
lean_object* v_arg_4216_ = _args[2];
lean_object* v_eqTrue_4217_ = _args[3];
lean_object* v_____x_4218_ = _args[4];
lean_object* v___y_4219_ = _args[5];
lean_object* v___y_4220_ = _args[6];
lean_object* v___y_4221_ = _args[7];
lean_object* v___y_4222_ = _args[8];
lean_object* v___y_4223_ = _args[9];
lean_object* v___y_4224_ = _args[10];
lean_object* v___y_4225_ = _args[11];
lean_object* v___y_4226_ = _args[12];
lean_object* v___y_4227_ = _args[13];
lean_object* v___y_4228_ = _args[14];
lean_object* v___y_4229_ = _args[15];
lean_object* v___y_4230_ = _args[16];
_start:
{
uint8_t v_eqTrue_boxed_4231_; lean_object* v_res_4232_; 
v_eqTrue_boxed_4231_ = lean_unbox(v_eqTrue_4217_);
v_res_4232_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__0(v_e_4214_, v_arg_4215_, v_arg_4216_, v_eqTrue_boxed_4231_, v_____x_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_);
return v_res_4232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__1(uint8_t v_eqTrue_4233_, lean_object* v___f_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_){
_start:
{
if (v_eqTrue_4233_ == 0)
{
lean_object* v___x_4247_; 
lean_inc(v___y_4245_);
lean_inc_ref(v___y_4244_);
lean_inc(v___y_4243_);
lean_inc_ref(v___y_4242_);
lean_inc(v___y_4235_);
v___x_4247_ = l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLT_x3f___redArg(v___y_4235_, v___y_4236_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_);
if (lean_obj_tag(v___x_4247_) == 0)
{
lean_object* v_a_4248_; lean_object* v___x_4249_; 
v_a_4248_ = lean_ctor_get(v___x_4247_, 0);
lean_inc(v_a_4248_);
lean_dec_ref(v___x_4247_);
v___x_4249_ = lean_apply_13(v___f_4234_, v_a_4248_, v___y_4235_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, lean_box(0));
return v___x_4249_;
}
else
{
lean_object* v_a_4250_; lean_object* v___x_4252_; uint8_t v_isShared_4253_; uint8_t v_isSharedCheck_4257_; 
lean_dec(v___y_4245_);
lean_dec_ref(v___y_4244_);
lean_dec(v___y_4243_);
lean_dec_ref(v___y_4242_);
lean_dec(v___y_4241_);
lean_dec_ref(v___y_4240_);
lean_dec(v___y_4239_);
lean_dec_ref(v___y_4238_);
lean_dec(v___y_4237_);
lean_dec(v___y_4236_);
lean_dec(v___y_4235_);
lean_dec_ref(v___f_4234_);
v_a_4250_ = lean_ctor_get(v___x_4247_, 0);
v_isSharedCheck_4257_ = !lean_is_exclusive(v___x_4247_);
if (v_isSharedCheck_4257_ == 0)
{
v___x_4252_ = v___x_4247_;
v_isShared_4253_ = v_isSharedCheck_4257_;
goto v_resetjp_4251_;
}
else
{
lean_inc(v_a_4250_);
lean_dec(v___x_4247_);
v___x_4252_ = lean_box(0);
v_isShared_4253_ = v_isSharedCheck_4257_;
goto v_resetjp_4251_;
}
v_resetjp_4251_:
{
lean_object* v___x_4255_; 
if (v_isShared_4253_ == 0)
{
v___x_4255_ = v___x_4252_;
goto v_reusejp_4254_;
}
else
{
lean_object* v_reuseFailAlloc_4256_; 
v_reuseFailAlloc_4256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4256_, 0, v_a_4250_);
v___x_4255_ = v_reuseFailAlloc_4256_;
goto v_reusejp_4254_;
}
v_reusejp_4254_:
{
return v___x_4255_;
}
}
}
}
else
{
lean_object* v___x_4258_; 
lean_inc(v___y_4245_);
lean_inc_ref(v___y_4244_);
lean_inc(v___y_4243_);
lean_inc_ref(v___y_4242_);
lean_inc(v___y_4235_);
v___x_4258_ = l_Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f___redArg(v___y_4235_, v___y_4236_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_);
if (lean_obj_tag(v___x_4258_) == 0)
{
lean_object* v_a_4259_; lean_object* v___x_4260_; 
v_a_4259_ = lean_ctor_get(v___x_4258_, 0);
lean_inc(v_a_4259_);
lean_dec_ref(v___x_4258_);
v___x_4260_ = lean_apply_13(v___f_4234_, v_a_4259_, v___y_4235_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, lean_box(0));
return v___x_4260_;
}
else
{
lean_object* v_a_4261_; lean_object* v___x_4263_; uint8_t v_isShared_4264_; uint8_t v_isSharedCheck_4268_; 
lean_dec(v___y_4245_);
lean_dec_ref(v___y_4244_);
lean_dec(v___y_4243_);
lean_dec_ref(v___y_4242_);
lean_dec(v___y_4241_);
lean_dec_ref(v___y_4240_);
lean_dec(v___y_4239_);
lean_dec_ref(v___y_4238_);
lean_dec(v___y_4237_);
lean_dec(v___y_4236_);
lean_dec(v___y_4235_);
lean_dec_ref(v___f_4234_);
v_a_4261_ = lean_ctor_get(v___x_4258_, 0);
v_isSharedCheck_4268_ = !lean_is_exclusive(v___x_4258_);
if (v_isSharedCheck_4268_ == 0)
{
v___x_4263_ = v___x_4258_;
v_isShared_4264_ = v_isSharedCheck_4268_;
goto v_resetjp_4262_;
}
else
{
lean_inc(v_a_4261_);
lean_dec(v___x_4258_);
v___x_4263_ = lean_box(0);
v_isShared_4264_ = v_isSharedCheck_4268_;
goto v_resetjp_4262_;
}
v_resetjp_4262_:
{
lean_object* v___x_4266_; 
if (v_isShared_4264_ == 0)
{
v___x_4266_ = v___x_4263_;
goto v_reusejp_4265_;
}
else
{
lean_object* v_reuseFailAlloc_4267_; 
v_reuseFailAlloc_4267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4267_, 0, v_a_4261_);
v___x_4266_ = v_reuseFailAlloc_4267_;
goto v_reusejp_4265_;
}
v_reusejp_4265_:
{
return v___x_4266_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__1___boxed(lean_object* v_eqTrue_4269_, lean_object* v___f_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_){
_start:
{
uint8_t v_eqTrue_boxed_4283_; lean_object* v_res_4284_; 
v_eqTrue_boxed_4283_ = lean_unbox(v_eqTrue_4269_);
v_res_4284_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__1(v_eqTrue_boxed_4283_, v___f_4270_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_, v___y_4278_, v___y_4279_, v___y_4280_, v___y_4281_);
return v_res_4284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt(lean_object* v_e_4290_, uint8_t v_eqTrue_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_, lean_object* v_a_4295_, lean_object* v_a_4296_, lean_object* v_a_4297_, lean_object* v_a_4298_, lean_object* v_a_4299_, lean_object* v_a_4300_, lean_object* v_a_4301_){
_start:
{
lean_object* v___x_4306_; 
v___x_4306_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_4294_);
if (lean_obj_tag(v___x_4306_) == 0)
{
lean_object* v_a_4307_; lean_object* v___x_4309_; uint8_t v_isShared_4310_; uint8_t v_isSharedCheck_4335_; 
v_a_4307_ = lean_ctor_get(v___x_4306_, 0);
v_isSharedCheck_4335_ = !lean_is_exclusive(v___x_4306_);
if (v_isSharedCheck_4335_ == 0)
{
v___x_4309_ = v___x_4306_;
v_isShared_4310_ = v_isSharedCheck_4335_;
goto v_resetjp_4308_;
}
else
{
lean_inc(v_a_4307_);
lean_dec(v___x_4306_);
v___x_4309_ = lean_box(0);
v_isShared_4310_ = v_isSharedCheck_4335_;
goto v_resetjp_4308_;
}
v_resetjp_4308_:
{
uint8_t v_lia_4311_; 
v_lia_4311_ = lean_ctor_get_uint8(v_a_4307_, sizeof(void*)*11 + 23);
lean_dec(v_a_4307_);
if (v_lia_4311_ == 0)
{
lean_object* v___x_4312_; lean_object* v___x_4314_; 
lean_dec(v_a_4301_);
lean_dec_ref(v_a_4300_);
lean_dec(v_a_4299_);
lean_dec_ref(v_a_4298_);
lean_dec(v_a_4297_);
lean_dec_ref(v_a_4296_);
lean_dec(v_a_4295_);
lean_dec_ref(v_a_4294_);
lean_dec(v_a_4293_);
lean_dec(v_a_4292_);
lean_dec_ref(v_e_4290_);
v___x_4312_ = lean_box(0);
if (v_isShared_4310_ == 0)
{
lean_ctor_set(v___x_4309_, 0, v___x_4312_);
v___x_4314_ = v___x_4309_;
goto v_reusejp_4313_;
}
else
{
lean_object* v_reuseFailAlloc_4315_; 
v_reuseFailAlloc_4315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4315_, 0, v___x_4312_);
v___x_4314_ = v_reuseFailAlloc_4315_;
goto v_reusejp_4313_;
}
v_reusejp_4313_:
{
return v___x_4314_;
}
}
else
{
lean_object* v___x_4316_; uint8_t v___x_4317_; 
lean_del_object(v___x_4309_);
lean_inc_ref(v_e_4290_);
v___x_4316_ = l_Lean_Expr_cleanupAnnotations(v_e_4290_);
v___x_4317_ = l_Lean_Expr_isApp(v___x_4316_);
if (v___x_4317_ == 0)
{
lean_dec_ref(v___x_4316_);
lean_dec(v_a_4301_);
lean_dec_ref(v_a_4300_);
lean_dec(v_a_4299_);
lean_dec_ref(v_a_4298_);
lean_dec(v_a_4297_);
lean_dec_ref(v_a_4296_);
lean_dec(v_a_4295_);
lean_dec_ref(v_a_4294_);
lean_dec(v_a_4293_);
lean_dec(v_a_4292_);
lean_dec_ref(v_e_4290_);
goto v___jp_4303_;
}
else
{
lean_object* v_arg_4318_; lean_object* v___x_4319_; uint8_t v___x_4320_; 
v_arg_4318_ = lean_ctor_get(v___x_4316_, 1);
lean_inc_ref(v_arg_4318_);
v___x_4319_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4316_);
v___x_4320_ = l_Lean_Expr_isApp(v___x_4319_);
if (v___x_4320_ == 0)
{
lean_dec_ref(v___x_4319_);
lean_dec_ref(v_arg_4318_);
lean_dec(v_a_4301_);
lean_dec_ref(v_a_4300_);
lean_dec(v_a_4299_);
lean_dec_ref(v_a_4298_);
lean_dec(v_a_4297_);
lean_dec_ref(v_a_4296_);
lean_dec(v_a_4295_);
lean_dec_ref(v_a_4294_);
lean_dec(v_a_4293_);
lean_dec(v_a_4292_);
lean_dec_ref(v_e_4290_);
goto v___jp_4303_;
}
else
{
lean_object* v_arg_4321_; lean_object* v___x_4322_; uint8_t v___x_4323_; 
v_arg_4321_ = lean_ctor_get(v___x_4319_, 1);
lean_inc_ref(v_arg_4321_);
v___x_4322_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4319_);
v___x_4323_ = l_Lean_Expr_isApp(v___x_4322_);
if (v___x_4323_ == 0)
{
lean_dec_ref(v___x_4322_);
lean_dec_ref(v_arg_4321_);
lean_dec_ref(v_arg_4318_);
lean_dec(v_a_4301_);
lean_dec_ref(v_a_4300_);
lean_dec(v_a_4299_);
lean_dec_ref(v_a_4298_);
lean_dec(v_a_4297_);
lean_dec_ref(v_a_4296_);
lean_dec(v_a_4295_);
lean_dec_ref(v_a_4294_);
lean_dec(v_a_4293_);
lean_dec(v_a_4292_);
lean_dec_ref(v_e_4290_);
goto v___jp_4303_;
}
else
{
lean_object* v___x_4324_; uint8_t v___x_4325_; 
v___x_4324_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4322_);
v___x_4325_ = l_Lean_Expr_isApp(v___x_4324_);
if (v___x_4325_ == 0)
{
lean_dec_ref(v___x_4324_);
lean_dec_ref(v_arg_4321_);
lean_dec_ref(v_arg_4318_);
lean_dec(v_a_4301_);
lean_dec_ref(v_a_4300_);
lean_dec(v_a_4299_);
lean_dec_ref(v_a_4298_);
lean_dec(v_a_4297_);
lean_dec_ref(v_a_4296_);
lean_dec(v_a_4295_);
lean_dec_ref(v_a_4294_);
lean_dec(v_a_4293_);
lean_dec(v_a_4292_);
lean_dec_ref(v_e_4290_);
goto v___jp_4303_;
}
else
{
lean_object* v_arg_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; uint8_t v___x_4329_; 
v_arg_4326_ = lean_ctor_get(v___x_4324_, 1);
lean_inc_ref(v_arg_4326_);
v___x_4327_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4324_);
v___x_4328_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__2));
v___x_4329_ = l_Lean_Expr_isConstOf(v___x_4327_, v___x_4328_);
lean_dec_ref(v___x_4327_);
if (v___x_4329_ == 0)
{
lean_dec_ref(v_arg_4326_);
lean_dec_ref(v_arg_4321_);
lean_dec_ref(v_arg_4318_);
lean_dec(v_a_4301_);
lean_dec_ref(v_a_4300_);
lean_dec(v_a_4299_);
lean_dec_ref(v_a_4298_);
lean_dec(v_a_4297_);
lean_dec_ref(v_a_4296_);
lean_dec(v_a_4295_);
lean_dec_ref(v_a_4294_);
lean_dec(v_a_4293_);
lean_dec(v_a_4292_);
lean_dec_ref(v_e_4290_);
goto v___jp_4303_;
}
else
{
lean_object* v___x_4330_; lean_object* v___f_4331_; lean_object* v___x_4332_; lean_object* v___y_4333_; lean_object* v___x_4334_; 
v___x_4330_ = lean_box(v_eqTrue_4291_);
v___f_4331_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__0___boxed), 17, 4);
lean_closure_set(v___f_4331_, 0, v_e_4290_);
lean_closure_set(v___f_4331_, 1, v_arg_4321_);
lean_closure_set(v___f_4331_, 2, v_arg_4318_);
lean_closure_set(v___f_4331_, 3, v___x_4330_);
v___x_4332_ = lean_box(v_eqTrue_4291_);
v___y_4333_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__1___boxed), 14, 2);
lean_closure_set(v___y_4333_, 0, v___x_4332_);
lean_closure_set(v___y_4333_, 1, v___f_4331_);
v___x_4334_ = l_Lean_Meta_Grind_Arith_Cutsat_ToIntM_run(v_arg_4326_, v___y_4333_, v_a_4292_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_, v_a_4297_, v_a_4298_, v_a_4299_, v_a_4300_, v_a_4301_);
return v___x_4334_;
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
lean_object* v_a_4336_; lean_object* v___x_4338_; uint8_t v_isShared_4339_; uint8_t v_isSharedCheck_4343_; 
lean_dec(v_a_4301_);
lean_dec_ref(v_a_4300_);
lean_dec(v_a_4299_);
lean_dec_ref(v_a_4298_);
lean_dec(v_a_4297_);
lean_dec_ref(v_a_4296_);
lean_dec(v_a_4295_);
lean_dec_ref(v_a_4294_);
lean_dec(v_a_4293_);
lean_dec(v_a_4292_);
lean_dec_ref(v_e_4290_);
v_a_4336_ = lean_ctor_get(v___x_4306_, 0);
v_isSharedCheck_4343_ = !lean_is_exclusive(v___x_4306_);
if (v_isSharedCheck_4343_ == 0)
{
v___x_4338_ = v___x_4306_;
v_isShared_4339_ = v_isSharedCheck_4343_;
goto v_resetjp_4337_;
}
else
{
lean_inc(v_a_4336_);
lean_dec(v___x_4306_);
v___x_4338_ = lean_box(0);
v_isShared_4339_ = v_isSharedCheck_4343_;
goto v_resetjp_4337_;
}
v_resetjp_4337_:
{
lean_object* v___x_4341_; 
if (v_isShared_4339_ == 0)
{
v___x_4341_ = v___x_4338_;
goto v_reusejp_4340_;
}
else
{
lean_object* v_reuseFailAlloc_4342_; 
v_reuseFailAlloc_4342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4342_, 0, v_a_4336_);
v___x_4341_ = v_reuseFailAlloc_4342_;
goto v_reusejp_4340_;
}
v_reusejp_4340_:
{
return v___x_4341_;
}
}
}
v___jp_4303_:
{
lean_object* v___x_4304_; lean_object* v___x_4305_; 
v___x_4304_ = lean_box(0);
v___x_4305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4305_, 0, v___x_4304_);
return v___x_4305_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___boxed(lean_object* v_e_4344_, lean_object* v_eqTrue_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_, lean_object* v_a_4348_, lean_object* v_a_4349_, lean_object* v_a_4350_, lean_object* v_a_4351_, lean_object* v_a_4352_, lean_object* v_a_4353_, lean_object* v_a_4354_, lean_object* v_a_4355_, lean_object* v_a_4356_){
_start:
{
uint8_t v_eqTrue_boxed_4357_; lean_object* v_res_4358_; 
v_eqTrue_boxed_4357_ = lean_unbox(v_eqTrue_4345_);
v_res_4358_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLt(v_e_4344_, v_eqTrue_boxed_4357_, v_a_4346_, v_a_4347_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_);
return v_res_4358_;
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
