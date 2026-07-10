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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Int_Internal_Linear_instBEqPoly_beq(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
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
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_int_neg(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
lean_object* l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_cutsat_assert_eq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_instInhabitedPersistentArray_default(lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Expr_norm(lean_object*);
lean_object* l_Int_Internal_Linear_Poly_normCommRing_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_cutsat_assert_le(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntLit(lean_object*);
lean_object* l_Lean_mkIntAdd(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLE_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_ToIntM_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstLEInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_mul(lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_addConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_natToInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqLBool_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_updateOccs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_gcdCoeffs_x27(lean_object*);
lean_object* l_Int_Internal_Linear_Poly_div(lean_object*, lean_object*);
uint8_t l_Int_Internal_Linear_Poly_isSorted(lean_object*);
lean_object* l_Int_Internal_Linear_Poly_norm(lean_object*);
lean_object* l_Int_Internal_Linear_Poly_findVarToSubst___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_coeff(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_combine(lean_object*, lean_object*);
uint8_t l_Int_Internal_Linear_Poly_isUnsatLe(lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLT_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_norm_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_norm(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__8;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_isNegEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isNegEq___boxed(lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__0;
static lean_once_cell_t l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "new eq: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__6_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7;
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
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0;
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
static lean_once_cell_t l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0;
static lean_once_cell_t l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "trivial"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(24, 23, 180, 58, 194, 72, 175, 153)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 137, 50, 202, 239, 114, 140, 141)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__4_value),LEAN_SCALAR_PTR_LITERAL(177, 38, 232, 206, 222, 75, 121, 224)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "unsat"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(24, 23, 180, 58, 194, 72, 175, 153)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__8_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 137, 50, 202, 239, 114, 140, 141)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__8_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__7_value),LEAN_SCALAR_PTR_LITERAL(216, 204, 174, 99, 3, 215, 140, 75)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(24, 23, 180, 58, 194, 72, 175, 153)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__10_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(198, 137, 50, 202, 239, 114, 140, 141)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11;
LEAN_EXPORT lean_object* lean_grind_cutsat_assert_le(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "unexpected non normalized inequality constraint found"};
static const lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___y_5_; lean_object* v_p_6_; lean_object* v_p_15_; uint8_t v___x_16_; 
v_p_15_ = lean_ctor_get(v_c_3_, 0);
v___x_16_ = l_Int_Internal_Linear_Poly_isSorted(v_p_15_);
if (v___x_16_ == 0)
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
lean_inc_ref(v_p_15_);
v___x_17_ = l_Int_Internal_Linear_Poly_norm(v_p_15_);
v___x_18_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_18_, 0, v_c_3_);
lean_inc_ref(v___x_17_);
v___x_19_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_19_, 0, v___x_17_);
lean_ctor_set(v___x_19_, 1, v___x_18_);
v___y_5_ = v___x_19_;
v_p_6_ = v___x_17_;
goto v___jp_4_;
}
else
{
lean_inc_ref(v_p_15_);
v___y_5_ = v_c_3_;
v_p_6_ = v_p_15_;
goto v___jp_4_;
}
v___jp_4_:
{
lean_object* v_k_7_; lean_object* v___x_8_; uint8_t v___x_9_; uint8_t v___x_10_; 
v_k_7_ = l_Int_Internal_Linear_Poly_gcdCoeffs_x27(v_p_6_);
v___x_8_ = lean_unsigned_to_nat(1u);
v___x_9_ = lean_nat_dec_eq(v_k_7_, v___x_8_);
v___x_10_ = lean_bool_not(v___x_9_);
if (v___x_10_ == 0)
{
lean_dec(v_k_7_);
lean_dec_ref(v_p_6_);
return v___y_5_;
}
else
{
lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_11_ = lean_nat_to_int(v_k_7_);
v___x_12_ = l_Int_Internal_Linear_Poly_div(v___x_11_, v_p_6_);
lean_dec(v___x_11_);
v___x_13_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_13_, 0, v___y_5_);
v___x_14_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_14_, 0, v___x_12_);
lean_ctor_set(v___x_14_, 1, v___x_13_);
return v___x_14_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0_spec__0(lean_object* v_msgData_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_, lean_object* v___y_24_){
_start:
{
lean_object* v___x_26_; lean_object* v_env_27_; lean_object* v___x_28_; lean_object* v_mctx_29_; lean_object* v_lctx_30_; lean_object* v_options_31_; lean_object* v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_26_ = lean_st_ref_get(v___y_24_);
v_env_27_ = lean_ctor_get(v___x_26_, 0);
lean_inc_ref(v_env_27_);
lean_dec(v___x_26_);
v___x_28_ = lean_st_ref_get(v___y_22_);
v_mctx_29_ = lean_ctor_get(v___x_28_, 0);
lean_inc_ref(v_mctx_29_);
lean_dec(v___x_28_);
v_lctx_30_ = lean_ctor_get(v___y_21_, 2);
v_options_31_ = lean_ctor_get(v___y_23_, 2);
lean_inc_ref(v_options_31_);
lean_inc_ref(v_lctx_30_);
v___x_32_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_32_, 0, v_env_27_);
lean_ctor_set(v___x_32_, 1, v_mctx_29_);
lean_ctor_set(v___x_32_, 2, v_lctx_30_);
lean_ctor_set(v___x_32_, 3, v_options_31_);
v___x_33_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_33_, 0, v___x_32_);
lean_ctor_set(v___x_33_, 1, v_msgData_20_);
v___x_34_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_34_, 0, v___x_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0_spec__0___boxed(lean_object* v_msgData_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_){
_start:
{
lean_object* v_res_41_; 
v_res_41_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0_spec__0(v_msgData_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_);
lean_dec(v___y_39_);
lean_dec_ref(v___y_38_);
lean_dec(v___y_37_);
lean_dec_ref(v___y_36_);
return v_res_41_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_42_; double v___x_43_; 
v___x_42_ = lean_unsigned_to_nat(0u);
v___x_43_ = lean_float_of_nat(v___x_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(lean_object* v_cls_47_, lean_object* v_msg_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_){
_start:
{
lean_object* v_ref_54_; lean_object* v___x_55_; lean_object* v_a_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_100_; 
v_ref_54_ = lean_ctor_get(v___y_51_, 5);
v___x_55_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0_spec__0(v_msg_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_);
v_a_56_ = lean_ctor_get(v___x_55_, 0);
v_isSharedCheck_100_ = !lean_is_exclusive(v___x_55_);
if (v_isSharedCheck_100_ == 0)
{
v___x_58_ = v___x_55_;
v_isShared_59_ = v_isSharedCheck_100_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_a_56_);
lean_dec(v___x_55_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_100_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___x_60_; lean_object* v_traceState_61_; lean_object* v_env_62_; lean_object* v_nextMacroScope_63_; lean_object* v_ngen_64_; lean_object* v_auxDeclNGen_65_; lean_object* v_cache_66_; lean_object* v_messages_67_; lean_object* v_infoState_68_; lean_object* v_snapshotTasks_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_99_; 
v___x_60_ = lean_st_ref_take(v___y_52_);
v_traceState_61_ = lean_ctor_get(v___x_60_, 4);
v_env_62_ = lean_ctor_get(v___x_60_, 0);
v_nextMacroScope_63_ = lean_ctor_get(v___x_60_, 1);
v_ngen_64_ = lean_ctor_get(v___x_60_, 2);
v_auxDeclNGen_65_ = lean_ctor_get(v___x_60_, 3);
v_cache_66_ = lean_ctor_get(v___x_60_, 5);
v_messages_67_ = lean_ctor_get(v___x_60_, 6);
v_infoState_68_ = lean_ctor_get(v___x_60_, 7);
v_snapshotTasks_69_ = lean_ctor_get(v___x_60_, 8);
v_isSharedCheck_99_ = !lean_is_exclusive(v___x_60_);
if (v_isSharedCheck_99_ == 0)
{
v___x_71_ = v___x_60_;
v_isShared_72_ = v_isSharedCheck_99_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_snapshotTasks_69_);
lean_inc(v_infoState_68_);
lean_inc(v_messages_67_);
lean_inc(v_cache_66_);
lean_inc(v_traceState_61_);
lean_inc(v_auxDeclNGen_65_);
lean_inc(v_ngen_64_);
lean_inc(v_nextMacroScope_63_);
lean_inc(v_env_62_);
lean_dec(v___x_60_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_99_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
uint64_t v_tid_73_; lean_object* v_traces_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_98_; 
v_tid_73_ = lean_ctor_get_uint64(v_traceState_61_, sizeof(void*)*1);
v_traces_74_ = lean_ctor_get(v_traceState_61_, 0);
v_isSharedCheck_98_ = !lean_is_exclusive(v_traceState_61_);
if (v_isSharedCheck_98_ == 0)
{
v___x_76_ = v_traceState_61_;
v_isShared_77_ = v_isSharedCheck_98_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_traces_74_);
lean_dec(v_traceState_61_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_98_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
lean_object* v___x_78_; double v___x_79_; uint8_t v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_88_; 
v___x_78_ = lean_box(0);
v___x_79_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__0);
v___x_80_ = 0;
v___x_81_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__1));
v___x_82_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_82_, 0, v_cls_47_);
lean_ctor_set(v___x_82_, 1, v___x_78_);
lean_ctor_set(v___x_82_, 2, v___x_81_);
lean_ctor_set_float(v___x_82_, sizeof(void*)*3, v___x_79_);
lean_ctor_set_float(v___x_82_, sizeof(void*)*3 + 8, v___x_79_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*3 + 16, v___x_80_);
v___x_83_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__2));
v___x_84_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_84_, 0, v___x_82_);
lean_ctor_set(v___x_84_, 1, v_a_56_);
lean_ctor_set(v___x_84_, 2, v___x_83_);
lean_inc(v_ref_54_);
v___x_85_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_85_, 0, v_ref_54_);
lean_ctor_set(v___x_85_, 1, v___x_84_);
v___x_86_ = l_Lean_PersistentArray_push___redArg(v_traces_74_, v___x_85_);
if (v_isShared_77_ == 0)
{
lean_ctor_set(v___x_76_, 0, v___x_86_);
v___x_88_ = v___x_76_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v___x_86_);
lean_ctor_set_uint64(v_reuseFailAlloc_97_, sizeof(void*)*1, v_tid_73_);
v___x_88_ = v_reuseFailAlloc_97_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
lean_object* v___x_90_; 
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 4, v___x_88_);
v___x_90_ = v___x_71_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v_env_62_);
lean_ctor_set(v_reuseFailAlloc_96_, 1, v_nextMacroScope_63_);
lean_ctor_set(v_reuseFailAlloc_96_, 2, v_ngen_64_);
lean_ctor_set(v_reuseFailAlloc_96_, 3, v_auxDeclNGen_65_);
lean_ctor_set(v_reuseFailAlloc_96_, 4, v___x_88_);
lean_ctor_set(v_reuseFailAlloc_96_, 5, v_cache_66_);
lean_ctor_set(v_reuseFailAlloc_96_, 6, v_messages_67_);
lean_ctor_set(v_reuseFailAlloc_96_, 7, v_infoState_68_);
lean_ctor_set(v_reuseFailAlloc_96_, 8, v_snapshotTasks_69_);
v___x_90_ = v_reuseFailAlloc_96_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_94_; 
v___x_91_ = lean_st_ref_set(v___y_52_, v___x_90_);
v___x_92_ = lean_box(0);
if (v_isShared_59_ == 0)
{
lean_ctor_set(v___x_58_, 0, v___x_92_);
v___x_94_ = v___x_58_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v___x_92_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___boxed(lean_object* v_cls_101_, lean_object* v_msg_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v_cls_101_, v_msg_102_, v___y_103_, v___y_104_, v___y_105_, v___y_106_);
lean_dec(v___y_106_);
lean_dec_ref(v___y_105_);
lean_dec(v___y_104_);
lean_dec_ref(v___y_103_);
return v_res_108_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6(void){
_start:
{
lean_object* v_cls_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v_cls_119_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__3));
v___x_120_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_121_ = l_Lean_Name_append(v___x_120_, v_cls_119_);
return v___x_121_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__8(void){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__7));
v___x_124_ = l_Lean_stringToMessageData(v___x_123_);
return v___x_124_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; 
v___x_125_ = lean_unsigned_to_nat(0u);
v___x_126_ = lean_nat_to_int(v___x_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq(lean_object* v_a_127_, lean_object* v_x_128_, lean_object* v_c_u2081_129_, lean_object* v_b_130_, lean_object* v_c_u2082_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_){
_start:
{
lean_object* v___y_144_; lean_object* v___y_149_; lean_object* v_p_201_; lean_object* v_p_202_; lean_object* v___x_203_; uint8_t v___x_204_; 
v_p_201_ = lean_ctor_get(v_c_u2081_129_, 0);
v_p_202_ = lean_ctor_get(v_c_u2082_131_, 0);
v___x_203_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9);
v___x_204_ = lean_int_dec_le(v___x_203_, v_a_127_);
if (v___x_204_ == 0)
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
lean_inc_ref(v_p_201_);
v___x_205_ = l_Int_Internal_Linear_Poly_mul(v_p_201_, v_b_130_);
v___x_206_ = lean_int_neg(v_a_127_);
lean_inc_ref(v_p_202_);
v___x_207_ = l_Int_Internal_Linear_Poly_mul(v_p_202_, v___x_206_);
lean_dec(v___x_206_);
v___x_208_ = l_Int_Internal_Linear_Poly_combine(v___x_205_, v___x_207_);
v___y_149_ = v___x_208_;
goto v___jp_148_;
}
else
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
lean_inc_ref(v_p_202_);
v___x_209_ = l_Int_Internal_Linear_Poly_mul(v_p_202_, v_a_127_);
v___x_210_ = lean_int_neg(v_b_130_);
lean_inc_ref(v_p_201_);
v___x_211_ = l_Int_Internal_Linear_Poly_mul(v_p_201_, v___x_210_);
lean_dec(v___x_210_);
v___x_212_ = l_Int_Internal_Linear_Poly_combine(v___x_209_, v___x_211_);
v___y_149_ = v___x_212_;
goto v___jp_148_;
}
v___jp_143_:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_145_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v___x_145_, 0, v_x_128_);
lean_ctor_set(v___x_145_, 1, v_c_u2081_129_);
lean_ctor_set(v___x_145_, 2, v_c_u2082_131_);
v___x_146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_146_, 0, v___y_144_);
lean_ctor_set(v___x_146_, 1, v___x_145_);
v___x_147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_147_, 0, v___x_146_);
return v___x_147_;
}
v___jp_148_:
{
lean_object* v_options_150_; uint8_t v_hasTrace_151_; 
v_options_150_ = lean_ctor_get(v_a_140_, 2);
v_hasTrace_151_ = lean_ctor_get_uint8(v_options_150_, sizeof(void*)*1);
if (v_hasTrace_151_ == 0)
{
v___y_144_ = v___y_149_;
goto v___jp_143_;
}
else
{
lean_object* v_inheritedTraceOptions_152_; lean_object* v_cls_153_; lean_object* v___x_154_; uint8_t v___x_155_; 
v_inheritedTraceOptions_152_ = lean_ctor_get(v_a_140_, 13);
v_cls_153_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__3));
v___x_154_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6);
v___x_155_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_152_, v_options_150_, v___x_154_);
if (v___x_155_ == 0)
{
v___y_144_ = v___y_149_;
goto v___jp_143_;
}
else
{
lean_object* v___x_156_; 
v___x_156_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_x_128_, v_a_132_, v_a_140_);
if (lean_obj_tag(v___x_156_) == 0)
{
lean_object* v_a_157_; lean_object* v___x_158_; 
v_a_157_ = lean_ctor_get(v___x_156_, 0);
lean_inc(v_a_157_);
lean_dec_ref_known(v___x_156_, 1);
lean_inc_ref(v_c_u2081_129_);
v___x_158_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_u2081_129_, v_a_132_, v_a_140_);
if (lean_obj_tag(v___x_158_) == 0)
{
lean_object* v_a_159_; lean_object* v___x_160_; 
v_a_159_ = lean_ctor_get(v___x_158_, 0);
lean_inc(v_a_159_);
lean_dec_ref_known(v___x_158_, 1);
lean_inc_ref(v_c_u2082_131_);
v___x_160_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2082_131_, v_a_132_, v_a_140_);
if (lean_obj_tag(v___x_160_) == 0)
{
lean_object* v_a_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v_a_161_ = lean_ctor_get(v___x_160_, 0);
lean_inc(v_a_161_);
lean_dec_ref_known(v___x_160_, 1);
v___x_162_ = l_Lean_MessageData_ofExpr(v_a_157_);
v___x_163_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__8);
v___x_164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_162_);
lean_ctor_set(v___x_164_, 1, v___x_163_);
v___x_165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
lean_ctor_set(v___x_165_, 1, v_a_159_);
v___x_166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
lean_ctor_set(v___x_166_, 1, v___x_163_);
v___x_167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
lean_ctor_set(v___x_167_, 1, v_a_161_);
v___x_168_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v_cls_153_, v___x_167_, v_a_138_, v_a_139_, v_a_140_, v_a_141_);
if (lean_obj_tag(v___x_168_) == 0)
{
lean_dec_ref_known(v___x_168_, 1);
v___y_144_ = v___y_149_;
goto v___jp_143_;
}
else
{
lean_object* v_a_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_176_; 
lean_dec_ref(v___y_149_);
lean_dec_ref(v_c_u2082_131_);
lean_dec_ref(v_c_u2081_129_);
lean_dec(v_x_128_);
v_a_169_ = lean_ctor_get(v___x_168_, 0);
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_168_);
if (v_isSharedCheck_176_ == 0)
{
v___x_171_ = v___x_168_;
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_a_169_);
lean_dec(v___x_168_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_174_; 
if (v_isShared_172_ == 0)
{
v___x_174_ = v___x_171_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_a_169_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
}
else
{
lean_object* v_a_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_184_; 
lean_dec(v_a_159_);
lean_dec(v_a_157_);
lean_dec_ref(v___y_149_);
lean_dec_ref(v_c_u2082_131_);
lean_dec_ref(v_c_u2081_129_);
lean_dec(v_x_128_);
v_a_177_ = lean_ctor_get(v___x_160_, 0);
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_184_ == 0)
{
v___x_179_ = v___x_160_;
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_a_177_);
lean_dec(v___x_160_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_182_; 
if (v_isShared_180_ == 0)
{
v___x_182_ = v___x_179_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_a_177_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
}
}
else
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_192_; 
lean_dec(v_a_157_);
lean_dec_ref(v___y_149_);
lean_dec_ref(v_c_u2082_131_);
lean_dec_ref(v_c_u2081_129_);
lean_dec(v_x_128_);
v_a_185_ = lean_ctor_get(v___x_158_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_192_ == 0)
{
v___x_187_ = v___x_158_;
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_158_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_190_; 
if (v_isShared_188_ == 0)
{
v___x_190_ = v___x_187_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_a_185_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
}
else
{
lean_object* v_a_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_200_; 
lean_dec_ref(v___y_149_);
lean_dec_ref(v_c_u2082_131_);
lean_dec_ref(v_c_u2081_129_);
lean_dec(v_x_128_);
v_a_193_ = lean_ctor_get(v___x_156_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_156_);
if (v_isSharedCheck_200_ == 0)
{
v___x_195_ = v___x_156_;
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_a_193_);
lean_dec(v___x_156_);
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___boxed(lean_object* v_a_213_, lean_object* v_x_214_, lean_object* v_c_u2081_215_, lean_object* v_b_216_, lean_object* v_c_u2082_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq(v_a_213_, v_x_214_, v_c_u2081_215_, v_b_216_, v_c_u2082_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_);
lean_dec(v_a_227_);
lean_dec_ref(v_a_226_);
lean_dec(v_a_225_);
lean_dec_ref(v_a_224_);
lean_dec(v_a_223_);
lean_dec_ref(v_a_222_);
lean_dec(v_a_221_);
lean_dec_ref(v_a_220_);
lean_dec(v_a_219_);
lean_dec(v_a_218_);
lean_dec(v_b_216_);
lean_dec(v_a_213_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0(lean_object* v_cls_230_, lean_object* v_msg_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v_cls_230_, v_msg_231_, v___y_238_, v___y_239_, v___y_240_, v___y_241_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___boxed(lean_object* v_cls_244_, lean_object* v_msg_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0(v_cls_244_, v_msg_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_);
lean_dec(v___y_255_);
lean_dec_ref(v___y_254_);
lean_dec(v___y_253_);
lean_dec_ref(v___y_252_);
lean_dec(v___y_251_);
lean_dec_ref(v___y_250_);
lean_dec(v___y_249_);
lean_dec_ref(v___y_248_);
lean_dec(v___y_247_);
lean_dec(v___y_246_);
return v_res_257_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = l_Lean_maxRecDepthErrorMessage;
v___x_264_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
return v___x_264_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__3);
v___x_266_ = l_Lean_MessageData_ofFormat(v___x_265_);
return v___x_266_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_267_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__4);
v___x_268_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__2));
v___x_269_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_269_, 0, v___x_268_);
lean_ctor_set(v___x_269_, 1, v___x_267_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg(lean_object* v_ref_270_){
_start:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_272_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__5);
v___x_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_273_, 0, v_ref_270_);
lean_ctor_set(v___x_273_, 1, v___x_272_);
v___x_274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_274_, 0, v___x_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___boxed(lean_object* v_ref_275_, lean_object* v___y_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg(v_ref_275_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0(lean_object* v_00_u03b1_278_, lean_object* v_ref_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg(v_ref_279_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___boxed(lean_object* v_00_u03b1_292_, lean_object* v_ref_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0(v_00_u03b1_292_, v_ref_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec(v___y_299_);
lean_dec_ref(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
lean_dec(v___y_294_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts(lean_object* v_c_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_){
_start:
{
lean_object* v_p_318_; lean_object* v_fileName_319_; lean_object* v_fileMap_320_; lean_object* v_options_321_; lean_object* v_currRecDepth_322_; lean_object* v_maxRecDepth_323_; lean_object* v_ref_324_; lean_object* v_currNamespace_325_; lean_object* v_openDecls_326_; lean_object* v_initHeartbeats_327_; lean_object* v_maxHeartbeats_328_; lean_object* v_quotContext_329_; lean_object* v_currMacroScope_330_; uint8_t v_diag_331_; lean_object* v_cancelTk_x3f_332_; uint8_t v_suppressElabErrors_333_; lean_object* v_inheritedTraceOptions_334_; uint8_t v___y_336_; lean_object* v___x_368_; uint8_t v___x_369_; uint8_t v___x_370_; 
v_p_318_ = lean_ctor_get(v_c_306_, 0);
v_fileName_319_ = lean_ctor_get(v_a_315_, 0);
lean_inc_ref(v_fileName_319_);
v_fileMap_320_ = lean_ctor_get(v_a_315_, 1);
lean_inc_ref(v_fileMap_320_);
v_options_321_ = lean_ctor_get(v_a_315_, 2);
lean_inc_ref(v_options_321_);
v_currRecDepth_322_ = lean_ctor_get(v_a_315_, 3);
lean_inc(v_currRecDepth_322_);
v_maxRecDepth_323_ = lean_ctor_get(v_a_315_, 4);
lean_inc(v_maxRecDepth_323_);
v_ref_324_ = lean_ctor_get(v_a_315_, 5);
lean_inc(v_ref_324_);
v_currNamespace_325_ = lean_ctor_get(v_a_315_, 6);
lean_inc(v_currNamespace_325_);
v_openDecls_326_ = lean_ctor_get(v_a_315_, 7);
lean_inc(v_openDecls_326_);
v_initHeartbeats_327_ = lean_ctor_get(v_a_315_, 8);
lean_inc(v_initHeartbeats_327_);
v_maxHeartbeats_328_ = lean_ctor_get(v_a_315_, 9);
lean_inc(v_maxHeartbeats_328_);
v_quotContext_329_ = lean_ctor_get(v_a_315_, 10);
lean_inc(v_quotContext_329_);
v_currMacroScope_330_ = lean_ctor_get(v_a_315_, 11);
lean_inc(v_currMacroScope_330_);
v_diag_331_ = lean_ctor_get_uint8(v_a_315_, sizeof(void*)*14);
v_cancelTk_x3f_332_ = lean_ctor_get(v_a_315_, 12);
lean_inc(v_cancelTk_x3f_332_);
v_suppressElabErrors_333_ = lean_ctor_get_uint8(v_a_315_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_334_ = lean_ctor_get(v_a_315_, 13);
lean_inc_ref(v_inheritedTraceOptions_334_);
lean_dec_ref(v_a_315_);
v___x_368_ = lean_unsigned_to_nat(0u);
v___x_369_ = lean_nat_dec_eq(v_maxRecDepth_323_, v___x_368_);
v___x_370_ = lean_bool_not(v___x_369_);
if (v___x_370_ == 0)
{
v___y_336_ = v___x_370_;
goto v___jp_335_;
}
else
{
uint8_t v___x_371_; 
v___x_371_ = lean_nat_dec_eq(v_currRecDepth_322_, v_maxRecDepth_323_);
v___y_336_ = v___x_371_;
goto v___jp_335_;
}
v___jp_335_:
{
if (v___y_336_ == 0)
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_337_ = lean_unsigned_to_nat(1u);
v___x_338_ = lean_nat_add(v_currRecDepth_322_, v___x_337_);
lean_dec(v_currRecDepth_322_);
v___x_339_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_339_, 0, v_fileName_319_);
lean_ctor_set(v___x_339_, 1, v_fileMap_320_);
lean_ctor_set(v___x_339_, 2, v_options_321_);
lean_ctor_set(v___x_339_, 3, v___x_338_);
lean_ctor_set(v___x_339_, 4, v_maxRecDepth_323_);
lean_ctor_set(v___x_339_, 5, v_ref_324_);
lean_ctor_set(v___x_339_, 6, v_currNamespace_325_);
lean_ctor_set(v___x_339_, 7, v_openDecls_326_);
lean_ctor_set(v___x_339_, 8, v_initHeartbeats_327_);
lean_ctor_set(v___x_339_, 9, v_maxHeartbeats_328_);
lean_ctor_set(v___x_339_, 10, v_quotContext_329_);
lean_ctor_set(v___x_339_, 11, v_currMacroScope_330_);
lean_ctor_set(v___x_339_, 12, v_cancelTk_x3f_332_);
lean_ctor_set(v___x_339_, 13, v_inheritedTraceOptions_334_);
lean_ctor_set_uint8(v___x_339_, sizeof(void*)*14, v_diag_331_);
lean_ctor_set_uint8(v___x_339_, sizeof(void*)*14 + 1, v_suppressElabErrors_333_);
lean_inc_ref(v_p_318_);
v___x_340_ = l_Int_Internal_Linear_Poly_findVarToSubst___redArg(v_p_318_, v_a_307_, v___x_339_);
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
v___x_352_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq(v___x_351_, v_fst_349_, v_snd_347_, v_fst_348_, v_c_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_, v___x_339_, v_a_316_);
lean_dec(v_fst_348_);
lean_dec(v___x_351_);
if (lean_obj_tag(v___x_352_) == 0)
{
lean_object* v_a_353_; 
v_a_353_ = lean_ctor_get(v___x_352_, 0);
lean_inc(v_a_353_);
lean_dec_ref_known(v___x_352_, 1);
v_c_306_ = v_a_353_;
v_a_315_ = v___x_339_;
goto _start;
}
else
{
lean_dec_ref_known(v___x_339_, 14);
return v___x_352_;
}
}
else
{
lean_object* v___x_356_; 
lean_dec(v_a_341_);
lean_dec_ref_known(v___x_339_, 14);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 0, v_c_306_);
v___x_356_ = v___x_343_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_c_306_);
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
lean_dec_ref_known(v___x_339_, 14);
lean_dec_ref(v_c_306_);
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
else
{
lean_object* v___x_367_; 
lean_dec_ref(v_inheritedTraceOptions_334_);
lean_dec(v_cancelTk_x3f_332_);
lean_dec(v_currMacroScope_330_);
lean_dec(v_quotContext_329_);
lean_dec(v_maxHeartbeats_328_);
lean_dec(v_initHeartbeats_327_);
lean_dec(v_openDecls_326_);
lean_dec(v_currNamespace_325_);
lean_dec(v_maxRecDepth_323_);
lean_dec(v_currRecDepth_322_);
lean_dec_ref(v_options_321_);
lean_dec_ref(v_fileMap_320_);
lean_dec_ref(v_fileName_319_);
lean_dec_ref(v_c_306_);
v___x_367_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg(v_ref_324_);
return v___x_367_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts___boxed(lean_object* v_c_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts(v_c_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
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
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_isNegEq(lean_object* v_p_u2081_385_, lean_object* v_p_u2082_386_){
_start:
{
if (lean_obj_tag(v_p_u2081_385_) == 0)
{
if (lean_obj_tag(v_p_u2082_386_) == 0)
{
lean_object* v_k_387_; lean_object* v_k_388_; lean_object* v___x_389_; uint8_t v___x_390_; 
v_k_387_ = lean_ctor_get(v_p_u2081_385_, 0);
v_k_388_ = lean_ctor_get(v_p_u2082_386_, 0);
v___x_389_ = lean_int_neg(v_k_388_);
v___x_390_ = lean_int_dec_eq(v_k_387_, v___x_389_);
lean_dec(v___x_389_);
return v___x_390_;
}
else
{
uint8_t v___x_391_; 
v___x_391_ = 0;
return v___x_391_;
}
}
else
{
if (lean_obj_tag(v_p_u2082_386_) == 1)
{
lean_object* v_k_392_; lean_object* v_v_393_; lean_object* v_p_394_; lean_object* v_k_395_; lean_object* v_v_396_; lean_object* v_p_397_; uint8_t v___y_399_; lean_object* v___x_401_; uint8_t v___x_402_; 
v_k_392_ = lean_ctor_get(v_p_u2081_385_, 0);
v_v_393_ = lean_ctor_get(v_p_u2081_385_, 1);
v_p_394_ = lean_ctor_get(v_p_u2081_385_, 2);
v_k_395_ = lean_ctor_get(v_p_u2082_386_, 0);
v_v_396_ = lean_ctor_get(v_p_u2082_386_, 1);
v_p_397_ = lean_ctor_get(v_p_u2082_386_, 2);
v___x_401_ = lean_int_neg(v_k_395_);
v___x_402_ = lean_int_dec_eq(v_k_392_, v___x_401_);
lean_dec(v___x_401_);
if (v___x_402_ == 0)
{
v___y_399_ = v___x_402_;
goto v___jp_398_;
}
else
{
uint8_t v___x_403_; 
v___x_403_ = lean_nat_dec_eq(v_v_393_, v_v_396_);
v___y_399_ = v___x_403_;
goto v___jp_398_;
}
v___jp_398_:
{
if (v___y_399_ == 0)
{
return v___y_399_;
}
else
{
v_p_u2081_385_ = v_p_394_;
v_p_u2082_386_ = v_p_397_;
goto _start;
}
}
}
else
{
uint8_t v___x_404_; 
v___x_404_ = 0;
return v___x_404_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isNegEq___boxed(lean_object* v_p_u2081_405_, lean_object* v_p_u2082_406_){
_start:
{
uint8_t v_res_407_; lean_object* v_r_408_; 
v_res_407_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_u2081_405_, v_p_u2082_406_);
lean_dec_ref(v_p_u2082_406_);
lean_dec_ref(v_p_u2081_405_);
v_r_408_ = lean_box(v_res_407_);
return v_r_408_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(lean_object* v___x_409_, lean_object* v_as_410_, size_t v_i_411_, size_t v_stop_412_, lean_object* v_b_413_){
_start:
{
lean_object* v___y_415_; uint8_t v___x_419_; 
v___x_419_ = lean_usize_dec_eq(v_i_411_, v_stop_412_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; lean_object* v_p_421_; uint8_t v___x_422_; uint8_t v___x_423_; 
v___x_420_ = lean_array_uget_borrowed(v_as_410_, v_i_411_);
v_p_421_ = lean_ctor_get(v___x_420_, 0);
v___x_422_ = l_Int_Internal_Linear_instBEqPoly_beq(v_p_421_, v___x_409_);
v___x_423_ = lean_bool_not(v___x_422_);
if (v___x_423_ == 0)
{
v___y_415_ = v_b_413_;
goto v___jp_414_;
}
else
{
lean_object* v___x_424_; 
lean_inc(v___x_420_);
v___x_424_ = l_Lean_PersistentArray_push___redArg(v_b_413_, v___x_420_);
v___y_415_ = v___x_424_;
goto v___jp_414_;
}
}
else
{
return v_b_413_;
}
v___jp_414_:
{
size_t v___x_416_; size_t v___x_417_; 
v___x_416_ = ((size_t)1ULL);
v___x_417_ = lean_usize_add(v_i_411_, v___x_416_);
v_i_411_ = v___x_417_;
v_b_413_ = v___y_415_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1___boxed(lean_object* v___x_425_, lean_object* v_as_426_, lean_object* v_i_427_, lean_object* v_stop_428_, lean_object* v_b_429_){
_start:
{
size_t v_i_boxed_430_; size_t v_stop_boxed_431_; lean_object* v_res_432_; 
v_i_boxed_430_ = lean_unbox_usize(v_i_427_);
lean_dec(v_i_427_);
v_stop_boxed_431_ = lean_unbox_usize(v_stop_428_);
lean_dec(v_stop_428_);
v_res_432_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_425_, v_as_426_, v_i_boxed_430_, v_stop_boxed_431_, v_b_429_);
lean_dec_ref(v_as_426_);
lean_dec_ref(v___x_425_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2(lean_object* v___x_433_, lean_object* v_x_434_, lean_object* v_x_435_){
_start:
{
if (lean_obj_tag(v_x_434_) == 0)
{
lean_object* v_cs_436_; lean_object* v___x_437_; lean_object* v___x_438_; uint8_t v___x_439_; 
v_cs_436_ = lean_ctor_get(v_x_434_, 0);
v___x_437_ = lean_unsigned_to_nat(0u);
v___x_438_ = lean_array_get_size(v_cs_436_);
v___x_439_ = lean_nat_dec_lt(v___x_437_, v___x_438_);
if (v___x_439_ == 0)
{
return v_x_435_;
}
else
{
uint8_t v___x_440_; 
v___x_440_ = lean_nat_dec_le(v___x_438_, v___x_438_);
if (v___x_440_ == 0)
{
if (v___x_439_ == 0)
{
return v_x_435_;
}
else
{
size_t v___x_441_; size_t v___x_442_; lean_object* v___x_443_; 
v___x_441_ = ((size_t)0ULL);
v___x_442_ = lean_usize_of_nat(v___x_438_);
v___x_443_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v___x_433_, v_cs_436_, v___x_441_, v___x_442_, v_x_435_);
return v___x_443_;
}
}
else
{
size_t v___x_444_; size_t v___x_445_; lean_object* v___x_446_; 
v___x_444_ = ((size_t)0ULL);
v___x_445_ = lean_usize_of_nat(v___x_438_);
v___x_446_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v___x_433_, v_cs_436_, v___x_444_, v___x_445_, v_x_435_);
return v___x_446_;
}
}
}
else
{
lean_object* v_vs_447_; lean_object* v___x_448_; lean_object* v___x_449_; uint8_t v___x_450_; 
v_vs_447_ = lean_ctor_get(v_x_434_, 0);
v___x_448_ = lean_unsigned_to_nat(0u);
v___x_449_ = lean_array_get_size(v_vs_447_);
v___x_450_ = lean_nat_dec_lt(v___x_448_, v___x_449_);
if (v___x_450_ == 0)
{
return v_x_435_;
}
else
{
uint8_t v___x_451_; 
v___x_451_ = lean_nat_dec_le(v___x_449_, v___x_449_);
if (v___x_451_ == 0)
{
if (v___x_450_ == 0)
{
return v_x_435_;
}
else
{
size_t v___x_452_; size_t v___x_453_; lean_object* v___x_454_; 
v___x_452_ = ((size_t)0ULL);
v___x_453_ = lean_usize_of_nat(v___x_449_);
v___x_454_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_433_, v_vs_447_, v___x_452_, v___x_453_, v_x_435_);
return v___x_454_;
}
}
else
{
size_t v___x_455_; size_t v___x_456_; lean_object* v___x_457_; 
v___x_455_ = ((size_t)0ULL);
v___x_456_ = lean_usize_of_nat(v___x_449_);
v___x_457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_433_, v_vs_447_, v___x_455_, v___x_456_, v_x_435_);
return v___x_457_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(lean_object* v___x_458_, lean_object* v_as_459_, size_t v_i_460_, size_t v_stop_461_, lean_object* v_b_462_){
_start:
{
uint8_t v___x_463_; 
v___x_463_ = lean_usize_dec_eq(v_i_460_, v_stop_461_);
if (v___x_463_ == 0)
{
lean_object* v___x_464_; lean_object* v___x_465_; size_t v___x_466_; size_t v___x_467_; 
v___x_464_ = lean_array_uget_borrowed(v_as_459_, v_i_460_);
v___x_465_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2(v___x_458_, v___x_464_, v_b_462_);
v___x_466_ = ((size_t)1ULL);
v___x_467_ = lean_usize_add(v_i_460_, v___x_466_);
v_i_460_ = v___x_467_;
v_b_462_ = v___x_465_;
goto _start;
}
else
{
return v_b_462_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1___boxed(lean_object* v___x_469_, lean_object* v_as_470_, lean_object* v_i_471_, lean_object* v_stop_472_, lean_object* v_b_473_){
_start:
{
size_t v_i_boxed_474_; size_t v_stop_boxed_475_; lean_object* v_res_476_; 
v_i_boxed_474_ = lean_unbox_usize(v_i_471_);
lean_dec(v_i_471_);
v_stop_boxed_475_ = lean_unbox_usize(v_stop_472_);
lean_dec(v_stop_472_);
v_res_476_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v___x_469_, v_as_470_, v_i_boxed_474_, v_stop_boxed_475_, v_b_473_);
lean_dec_ref(v_as_470_);
lean_dec_ref(v___x_469_);
return v_res_476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2___boxed(lean_object* v___x_477_, lean_object* v_x_478_, lean_object* v_x_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2(v___x_477_, v_x_478_, v_x_479_);
lean_dec_ref(v_x_478_);
lean_dec_ref(v___x_477_);
return v_res_480_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(lean_object* v___x_482_, lean_object* v_x_483_, size_t v_x_484_, size_t v_x_485_, lean_object* v_x_486_){
_start:
{
if (lean_obj_tag(v_x_483_) == 0)
{
lean_object* v_cs_487_; lean_object* v___x_488_; size_t v___x_489_; lean_object* v_j_490_; lean_object* v___x_491_; size_t v___x_492_; size_t v___x_493_; size_t v___x_494_; size_t v___x_495_; size_t v___x_496_; size_t v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; uint8_t v___x_502_; 
v_cs_487_ = lean_ctor_get(v_x_483_, 0);
v___x_488_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0);
v___x_489_ = lean_usize_shift_right(v_x_484_, v_x_485_);
v_j_490_ = lean_usize_to_nat(v___x_489_);
v___x_491_ = lean_array_get_borrowed(v___x_488_, v_cs_487_, v_j_490_);
v___x_492_ = ((size_t)1ULL);
v___x_493_ = lean_usize_shift_left(v___x_492_, v_x_485_);
v___x_494_ = lean_usize_sub(v___x_493_, v___x_492_);
v___x_495_ = lean_usize_land(v_x_484_, v___x_494_);
v___x_496_ = ((size_t)5ULL);
v___x_497_ = lean_usize_sub(v_x_485_, v___x_496_);
v___x_498_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(v___x_482_, v___x_491_, v___x_495_, v___x_497_, v_x_486_);
v___x_499_ = lean_unsigned_to_nat(1u);
v___x_500_ = lean_nat_add(v_j_490_, v___x_499_);
lean_dec(v_j_490_);
v___x_501_ = lean_array_get_size(v_cs_487_);
v___x_502_ = lean_nat_dec_lt(v___x_500_, v___x_501_);
if (v___x_502_ == 0)
{
lean_dec(v___x_500_);
return v___x_498_;
}
else
{
uint8_t v___x_503_; 
v___x_503_ = lean_nat_dec_le(v___x_501_, v___x_501_);
if (v___x_503_ == 0)
{
if (v___x_502_ == 0)
{
lean_dec(v___x_500_);
return v___x_498_;
}
else
{
size_t v___x_504_; size_t v___x_505_; lean_object* v___x_506_; 
v___x_504_ = lean_usize_of_nat(v___x_500_);
lean_dec(v___x_500_);
v___x_505_ = lean_usize_of_nat(v___x_501_);
v___x_506_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v___x_482_, v_cs_487_, v___x_504_, v___x_505_, v___x_498_);
return v___x_506_;
}
}
else
{
size_t v___x_507_; size_t v___x_508_; lean_object* v___x_509_; 
v___x_507_ = lean_usize_of_nat(v___x_500_);
lean_dec(v___x_500_);
v___x_508_ = lean_usize_of_nat(v___x_501_);
v___x_509_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v___x_482_, v_cs_487_, v___x_507_, v___x_508_, v___x_498_);
return v___x_509_;
}
}
}
else
{
lean_object* v_vs_510_; lean_object* v___x_511_; lean_object* v___x_512_; uint8_t v___x_513_; 
v_vs_510_ = lean_ctor_get(v_x_483_, 0);
v___x_511_ = lean_usize_to_nat(v_x_484_);
v___x_512_ = lean_array_get_size(v_vs_510_);
v___x_513_ = lean_nat_dec_lt(v___x_511_, v___x_512_);
if (v___x_513_ == 0)
{
lean_dec(v___x_511_);
return v_x_486_;
}
else
{
uint8_t v___x_514_; 
v___x_514_ = lean_nat_dec_le(v___x_512_, v___x_512_);
if (v___x_514_ == 0)
{
if (v___x_513_ == 0)
{
lean_dec(v___x_511_);
return v_x_486_;
}
else
{
size_t v___x_515_; size_t v___x_516_; lean_object* v___x_517_; 
v___x_515_ = lean_usize_of_nat(v___x_511_);
lean_dec(v___x_511_);
v___x_516_ = lean_usize_of_nat(v___x_512_);
v___x_517_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_482_, v_vs_510_, v___x_515_, v___x_516_, v_x_486_);
return v___x_517_;
}
}
else
{
size_t v___x_518_; size_t v___x_519_; lean_object* v___x_520_; 
v___x_518_ = lean_usize_of_nat(v___x_511_);
lean_dec(v___x_511_);
v___x_519_ = lean_usize_of_nat(v___x_512_);
v___x_520_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_482_, v_vs_510_, v___x_518_, v___x_519_, v_x_486_);
return v___x_520_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___boxed(lean_object* v___x_521_, lean_object* v_x_522_, lean_object* v_x_523_, lean_object* v_x_524_, lean_object* v_x_525_){
_start:
{
size_t v_x_2052__boxed_526_; size_t v_x_2053__boxed_527_; lean_object* v_res_528_; 
v_x_2052__boxed_526_ = lean_unbox_usize(v_x_523_);
lean_dec(v_x_523_);
v_x_2053__boxed_527_ = lean_unbox_usize(v_x_524_);
lean_dec(v_x_524_);
v_res_528_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(v___x_521_, v_x_522_, v_x_2052__boxed_526_, v_x_2053__boxed_527_, v_x_525_);
lean_dec_ref(v_x_522_);
lean_dec_ref(v___x_521_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(lean_object* v___x_529_, lean_object* v_t_530_, lean_object* v_init_531_, lean_object* v_start_532_){
_start:
{
lean_object* v___x_533_; uint8_t v___x_534_; 
v___x_533_ = lean_unsigned_to_nat(0u);
v___x_534_ = lean_nat_dec_eq(v_start_532_, v___x_533_);
if (v___x_534_ == 0)
{
lean_object* v_root_535_; lean_object* v_tail_536_; size_t v_shift_537_; lean_object* v_tailOff_538_; uint8_t v___x_539_; 
v_root_535_ = lean_ctor_get(v_t_530_, 0);
v_tail_536_ = lean_ctor_get(v_t_530_, 1);
v_shift_537_ = lean_ctor_get_usize(v_t_530_, 4);
v_tailOff_538_ = lean_ctor_get(v_t_530_, 3);
v___x_539_ = lean_nat_dec_le(v_tailOff_538_, v_start_532_);
if (v___x_539_ == 0)
{
size_t v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; uint8_t v___x_543_; 
v___x_540_ = lean_usize_of_nat(v_start_532_);
v___x_541_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(v___x_529_, v_root_535_, v___x_540_, v_shift_537_, v_init_531_);
v___x_542_ = lean_array_get_size(v_tail_536_);
v___x_543_ = lean_nat_dec_lt(v___x_533_, v___x_542_);
if (v___x_543_ == 0)
{
return v___x_541_;
}
else
{
uint8_t v___x_544_; 
v___x_544_ = lean_nat_dec_le(v___x_542_, v___x_542_);
if (v___x_544_ == 0)
{
if (v___x_543_ == 0)
{
return v___x_541_;
}
else
{
size_t v___x_545_; size_t v___x_546_; lean_object* v___x_547_; 
v___x_545_ = ((size_t)0ULL);
v___x_546_ = lean_usize_of_nat(v___x_542_);
v___x_547_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_529_, v_tail_536_, v___x_545_, v___x_546_, v___x_541_);
return v___x_547_;
}
}
else
{
size_t v___x_548_; size_t v___x_549_; lean_object* v___x_550_; 
v___x_548_ = ((size_t)0ULL);
v___x_549_ = lean_usize_of_nat(v___x_542_);
v___x_550_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_529_, v_tail_536_, v___x_548_, v___x_549_, v___x_541_);
return v___x_550_;
}
}
}
else
{
lean_object* v___x_551_; lean_object* v___x_552_; uint8_t v___x_553_; 
v___x_551_ = lean_nat_sub(v_start_532_, v_tailOff_538_);
v___x_552_ = lean_array_get_size(v_tail_536_);
v___x_553_ = lean_nat_dec_lt(v___x_551_, v___x_552_);
if (v___x_553_ == 0)
{
lean_dec(v___x_551_);
return v_init_531_;
}
else
{
uint8_t v___x_554_; 
v___x_554_ = lean_nat_dec_le(v___x_552_, v___x_552_);
if (v___x_554_ == 0)
{
if (v___x_553_ == 0)
{
lean_dec(v___x_551_);
return v_init_531_;
}
else
{
size_t v___x_555_; size_t v___x_556_; lean_object* v___x_557_; 
v___x_555_ = lean_usize_of_nat(v___x_551_);
lean_dec(v___x_551_);
v___x_556_ = lean_usize_of_nat(v___x_552_);
v___x_557_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_529_, v_tail_536_, v___x_555_, v___x_556_, v_init_531_);
return v___x_557_;
}
}
else
{
size_t v___x_558_; size_t v___x_559_; lean_object* v___x_560_; 
v___x_558_ = lean_usize_of_nat(v___x_551_);
lean_dec(v___x_551_);
v___x_559_ = lean_usize_of_nat(v___x_552_);
v___x_560_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_529_, v_tail_536_, v___x_558_, v___x_559_, v_init_531_);
return v___x_560_;
}
}
}
}
else
{
lean_object* v_root_561_; lean_object* v_tail_562_; lean_object* v___x_563_; lean_object* v___x_564_; uint8_t v___x_565_; 
v_root_561_ = lean_ctor_get(v_t_530_, 0);
v_tail_562_ = lean_ctor_get(v_t_530_, 1);
v___x_563_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2(v___x_529_, v_root_561_, v_init_531_);
v___x_564_ = lean_array_get_size(v_tail_562_);
v___x_565_ = lean_nat_dec_lt(v___x_533_, v___x_564_);
if (v___x_565_ == 0)
{
return v___x_563_;
}
else
{
uint8_t v___x_566_; 
v___x_566_ = lean_nat_dec_le(v___x_564_, v___x_564_);
if (v___x_566_ == 0)
{
if (v___x_565_ == 0)
{
return v___x_563_;
}
else
{
size_t v___x_567_; size_t v___x_568_; lean_object* v___x_569_; 
v___x_567_ = ((size_t)0ULL);
v___x_568_ = lean_usize_of_nat(v___x_564_);
v___x_569_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_529_, v_tail_562_, v___x_567_, v___x_568_, v___x_563_);
return v___x_569_;
}
}
else
{
size_t v___x_570_; size_t v___x_571_; lean_object* v___x_572_; 
v___x_570_ = ((size_t)0ULL);
v___x_571_ = lean_usize_of_nat(v___x_564_);
v___x_572_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_529_, v_tail_562_, v___x_570_, v___x_571_, v___x_563_);
return v___x_572_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0___boxed(lean_object* v___x_573_, lean_object* v_t_574_, lean_object* v_init_575_, lean_object* v_start_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(v___x_573_, v_t_574_, v_init_575_, v_start_576_);
lean_dec(v_start_576_);
lean_dec_ref(v_t_574_);
lean_dec_ref(v___x_573_);
return v_res_577_;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_578_ = lean_unsigned_to_nat(32u);
v___x_579_ = lean_mk_empty_array_with_capacity(v___x_578_);
v___x_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
return v___x_580_;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1(void){
_start:
{
size_t v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_581_ = ((size_t)5ULL);
v___x_582_ = lean_unsigned_to_nat(0u);
v___x_583_ = lean_unsigned_to_nat(32u);
v___x_584_ = lean_mk_empty_array_with_capacity(v___x_583_);
v___x_585_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__0, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__0_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__0);
v___x_586_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_586_, 0, v___x_585_);
lean_ctor_set(v___x_586_, 1, v___x_584_);
lean_ctor_set(v___x_586_, 2, v___x_582_);
lean_ctor_set(v___x_586_, 3, v___x_582_);
lean_ctor_set_usize(v___x_586_, 4, v___x_581_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4(lean_object* v___x_587_, lean_object* v_x_588_, size_t v_x_589_, size_t v_x_590_){
_start:
{
if (lean_obj_tag(v_x_588_) == 0)
{
lean_object* v_cs_591_; size_t v_j_592_; lean_object* v___x_593_; lean_object* v___x_594_; uint8_t v___x_595_; 
v_cs_591_ = lean_ctor_get(v_x_588_, 0);
v_j_592_ = lean_usize_shift_right(v_x_589_, v_x_590_);
v___x_593_ = lean_usize_to_nat(v_j_592_);
v___x_594_ = lean_array_get_size(v_cs_591_);
v___x_595_ = lean_nat_dec_lt(v___x_593_, v___x_594_);
if (v___x_595_ == 0)
{
lean_dec(v___x_593_);
return v_x_588_;
}
else
{
lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_613_; 
lean_inc_ref(v_cs_591_);
v_isSharedCheck_613_ = !lean_is_exclusive(v_x_588_);
if (v_isSharedCheck_613_ == 0)
{
lean_object* v_unused_614_; 
v_unused_614_ = lean_ctor_get(v_x_588_, 0);
lean_dec(v_unused_614_);
v___x_597_ = v_x_588_;
v_isShared_598_ = v_isSharedCheck_613_;
goto v_resetjp_596_;
}
else
{
lean_dec(v_x_588_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_613_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
size_t v___x_599_; size_t v___x_600_; size_t v___x_601_; size_t v_i_602_; size_t v___x_603_; size_t v_shift_604_; lean_object* v_v_605_; lean_object* v___x_606_; lean_object* v_xs_x27_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_611_; 
v___x_599_ = ((size_t)1ULL);
v___x_600_ = lean_usize_shift_left(v___x_599_, v_x_590_);
v___x_601_ = lean_usize_sub(v___x_600_, v___x_599_);
v_i_602_ = lean_usize_land(v_x_589_, v___x_601_);
v___x_603_ = ((size_t)5ULL);
v_shift_604_ = lean_usize_sub(v_x_590_, v___x_603_);
v_v_605_ = lean_array_fget(v_cs_591_, v___x_593_);
v___x_606_ = lean_box(0);
v_xs_x27_607_ = lean_array_fset(v_cs_591_, v___x_593_, v___x_606_);
v___x_608_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4(v___x_587_, v_v_605_, v_i_602_, v_shift_604_);
v___x_609_ = lean_array_fset(v_xs_x27_607_, v___x_593_, v___x_608_);
lean_dec(v___x_593_);
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 0, v___x_609_);
v___x_611_ = v___x_597_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v___x_609_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
else
{
lean_object* v_vs_615_; lean_object* v___x_616_; lean_object* v___x_617_; uint8_t v___x_618_; 
v_vs_615_ = lean_ctor_get(v_x_588_, 0);
v___x_616_ = lean_usize_to_nat(v_x_589_);
v___x_617_ = lean_array_get_size(v_vs_615_);
v___x_618_ = lean_nat_dec_lt(v___x_616_, v___x_617_);
if (v___x_618_ == 0)
{
lean_dec(v___x_616_);
return v_x_588_;
}
else
{
lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_632_; 
lean_inc_ref(v_vs_615_);
v_isSharedCheck_632_ = !lean_is_exclusive(v_x_588_);
if (v_isSharedCheck_632_ == 0)
{
lean_object* v_unused_633_; 
v_unused_633_ = lean_ctor_get(v_x_588_, 0);
lean_dec(v_unused_633_);
v___x_620_ = v_x_588_;
v_isShared_621_ = v_isSharedCheck_632_;
goto v_resetjp_619_;
}
else
{
lean_dec(v_x_588_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_632_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v_v_622_; lean_object* v___x_623_; lean_object* v_xs_x27_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_630_; 
v_v_622_ = lean_array_fget(v_vs_615_, v___x_616_);
v___x_623_ = lean_box(0);
v_xs_x27_624_ = lean_array_fset(v_vs_615_, v___x_616_, v___x_623_);
v___x_625_ = lean_unsigned_to_nat(0u);
v___x_626_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1);
v___x_627_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(v___x_587_, v_v_622_, v___x_626_, v___x_625_);
lean_dec(v_v_622_);
v___x_628_ = lean_array_fset(v_xs_x27_624_, v___x_616_, v___x_627_);
lean_dec(v___x_616_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v___x_628_);
v___x_630_ = v___x_620_;
goto v_reusejp_629_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_628_);
v___x_630_ = v_reuseFailAlloc_631_;
goto v_reusejp_629_;
}
v_reusejp_629_:
{
return v___x_630_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___boxed(lean_object* v___x_634_, lean_object* v_x_635_, lean_object* v_x_636_, lean_object* v_x_637_){
_start:
{
size_t v_x_2225__boxed_638_; size_t v_x_2226__boxed_639_; lean_object* v_res_640_; 
v_x_2225__boxed_638_ = lean_unbox_usize(v_x_636_);
lean_dec(v_x_636_);
v_x_2226__boxed_639_ = lean_unbox_usize(v_x_637_);
lean_dec(v_x_637_);
v_res_640_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4(v___x_634_, v_x_635_, v_x_2225__boxed_638_, v_x_2226__boxed_639_);
lean_dec_ref(v___x_634_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(lean_object* v___x_641_, lean_object* v_t_642_, lean_object* v_i_643_){
_start:
{
lean_object* v_root_644_; lean_object* v_tail_645_; lean_object* v_size_646_; size_t v_shift_647_; lean_object* v_tailOff_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_676_; 
v_root_644_ = lean_ctor_get(v_t_642_, 0);
v_tail_645_ = lean_ctor_get(v_t_642_, 1);
v_size_646_ = lean_ctor_get(v_t_642_, 2);
v_shift_647_ = lean_ctor_get_usize(v_t_642_, 4);
v_tailOff_648_ = lean_ctor_get(v_t_642_, 3);
v_isSharedCheck_676_ = !lean_is_exclusive(v_t_642_);
if (v_isSharedCheck_676_ == 0)
{
v___x_650_ = v_t_642_;
v_isShared_651_ = v_isSharedCheck_676_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_tailOff_648_);
lean_inc(v_size_646_);
lean_inc(v_tail_645_);
lean_inc(v_root_644_);
lean_dec(v_t_642_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_676_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
uint8_t v___x_652_; 
v___x_652_ = lean_nat_dec_le(v_tailOff_648_, v_i_643_);
if (v___x_652_ == 0)
{
size_t v___x_653_; lean_object* v___x_654_; lean_object* v___x_656_; 
v___x_653_ = lean_usize_of_nat(v_i_643_);
v___x_654_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4(v___x_641_, v_root_644_, v___x_653_, v_shift_647_);
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 0, v___x_654_);
v___x_656_ = v___x_650_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v___x_654_);
lean_ctor_set(v_reuseFailAlloc_657_, 1, v_tail_645_);
lean_ctor_set(v_reuseFailAlloc_657_, 2, v_size_646_);
lean_ctor_set(v_reuseFailAlloc_657_, 3, v_tailOff_648_);
lean_ctor_set_usize(v_reuseFailAlloc_657_, 4, v_shift_647_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
else
{
lean_object* v___x_658_; lean_object* v___x_659_; uint8_t v___x_660_; 
v___x_658_ = lean_nat_sub(v_i_643_, v_tailOff_648_);
v___x_659_ = lean_array_get_size(v_tail_645_);
v___x_660_ = lean_nat_dec_lt(v___x_658_, v___x_659_);
if (v___x_660_ == 0)
{
lean_object* v___x_662_; 
lean_dec(v___x_658_);
if (v_isShared_651_ == 0)
{
v___x_662_ = v___x_650_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v_root_644_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v_tail_645_);
lean_ctor_set(v_reuseFailAlloc_663_, 2, v_size_646_);
lean_ctor_set(v_reuseFailAlloc_663_, 3, v_tailOff_648_);
lean_ctor_set_usize(v_reuseFailAlloc_663_, 4, v_shift_647_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
else
{
lean_object* v_v_664_; lean_object* v___x_665_; lean_object* v_xs_x27_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_674_; 
v_v_664_ = lean_array_fget(v_tail_645_, v___x_658_);
v___x_665_ = lean_box(0);
v_xs_x27_666_ = lean_array_fset(v_tail_645_, v___x_658_, v___x_665_);
v___x_667_ = lean_unsigned_to_nat(32u);
v___x_668_ = lean_mk_empty_array_with_capacity(v___x_667_);
lean_dec_ref(v___x_668_);
v___x_669_ = lean_unsigned_to_nat(0u);
v___x_670_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1);
v___x_671_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(v___x_641_, v_v_664_, v___x_670_, v___x_669_);
lean_dec(v_v_664_);
v___x_672_ = lean_array_fset(v_xs_x27_666_, v___x_658_, v___x_671_);
lean_dec(v___x_658_);
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 1, v___x_672_);
v___x_674_ = v___x_650_;
goto v_reusejp_673_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_root_644_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v___x_672_);
lean_ctor_set(v_reuseFailAlloc_675_, 2, v_size_646_);
lean_ctor_set(v_reuseFailAlloc_675_, 3, v_tailOff_648_);
lean_ctor_set_usize(v_reuseFailAlloc_675_, 4, v_shift_647_);
v___x_674_ = v_reuseFailAlloc_675_;
goto v_reusejp_673_;
}
v_reusejp_673_:
{
return v___x_674_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1___boxed(lean_object* v___x_677_, lean_object* v_t_678_, lean_object* v_i_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(v___x_677_, v_t_678_, v_i_679_);
lean_dec(v_i_679_);
lean_dec_ref(v___x_677_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0(lean_object* v_p_681_, lean_object* v_v_682_, lean_object* v_s_683_){
_start:
{
lean_object* v_vars_684_; lean_object* v_varMap_685_; lean_object* v_vars_x27_686_; lean_object* v_varMap_x27_687_; lean_object* v_natToIntMap_688_; lean_object* v_natDef_689_; lean_object* v_dvds_690_; lean_object* v_lowers_691_; lean_object* v_uppers_692_; lean_object* v_diseqs_693_; lean_object* v_elimEqs_694_; lean_object* v_elimStack_695_; lean_object* v_occurs_696_; lean_object* v_assignment_697_; lean_object* v_nextCnstrId_698_; uint8_t v_caseSplits_699_; lean_object* v_conflict_x3f_700_; lean_object* v_diseqSplits_701_; lean_object* v_divMod_702_; lean_object* v_toIntIds_703_; lean_object* v_toIntInfos_704_; lean_object* v_toIntTermMap_705_; lean_object* v_toIntVarMap_706_; uint8_t v_usedCommRing_707_; lean_object* v_nonlinearOccs_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_716_; 
v_vars_684_ = lean_ctor_get(v_s_683_, 0);
v_varMap_685_ = lean_ctor_get(v_s_683_, 1);
v_vars_x27_686_ = lean_ctor_get(v_s_683_, 2);
v_varMap_x27_687_ = lean_ctor_get(v_s_683_, 3);
v_natToIntMap_688_ = lean_ctor_get(v_s_683_, 4);
v_natDef_689_ = lean_ctor_get(v_s_683_, 5);
v_dvds_690_ = lean_ctor_get(v_s_683_, 6);
v_lowers_691_ = lean_ctor_get(v_s_683_, 7);
v_uppers_692_ = lean_ctor_get(v_s_683_, 8);
v_diseqs_693_ = lean_ctor_get(v_s_683_, 9);
v_elimEqs_694_ = lean_ctor_get(v_s_683_, 10);
v_elimStack_695_ = lean_ctor_get(v_s_683_, 11);
v_occurs_696_ = lean_ctor_get(v_s_683_, 12);
v_assignment_697_ = lean_ctor_get(v_s_683_, 13);
v_nextCnstrId_698_ = lean_ctor_get(v_s_683_, 14);
v_caseSplits_699_ = lean_ctor_get_uint8(v_s_683_, sizeof(void*)*23);
v_conflict_x3f_700_ = lean_ctor_get(v_s_683_, 15);
v_diseqSplits_701_ = lean_ctor_get(v_s_683_, 16);
v_divMod_702_ = lean_ctor_get(v_s_683_, 17);
v_toIntIds_703_ = lean_ctor_get(v_s_683_, 18);
v_toIntInfos_704_ = lean_ctor_get(v_s_683_, 19);
v_toIntTermMap_705_ = lean_ctor_get(v_s_683_, 20);
v_toIntVarMap_706_ = lean_ctor_get(v_s_683_, 21);
v_usedCommRing_707_ = lean_ctor_get_uint8(v_s_683_, sizeof(void*)*23 + 1);
v_nonlinearOccs_708_ = lean_ctor_get(v_s_683_, 22);
v_isSharedCheck_716_ = !lean_is_exclusive(v_s_683_);
if (v_isSharedCheck_716_ == 0)
{
v___x_710_ = v_s_683_;
v_isShared_711_ = v_isSharedCheck_716_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_nonlinearOccs_708_);
lean_inc(v_toIntVarMap_706_);
lean_inc(v_toIntTermMap_705_);
lean_inc(v_toIntInfos_704_);
lean_inc(v_toIntIds_703_);
lean_inc(v_divMod_702_);
lean_inc(v_diseqSplits_701_);
lean_inc(v_conflict_x3f_700_);
lean_inc(v_nextCnstrId_698_);
lean_inc(v_assignment_697_);
lean_inc(v_occurs_696_);
lean_inc(v_elimStack_695_);
lean_inc(v_elimEqs_694_);
lean_inc(v_diseqs_693_);
lean_inc(v_uppers_692_);
lean_inc(v_lowers_691_);
lean_inc(v_dvds_690_);
lean_inc(v_natDef_689_);
lean_inc(v_natToIntMap_688_);
lean_inc(v_varMap_x27_687_);
lean_inc(v_vars_x27_686_);
lean_inc(v_varMap_685_);
lean_inc(v_vars_684_);
lean_dec(v_s_683_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_716_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_712_; lean_object* v___x_714_; 
v___x_712_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(v_p_681_, v_uppers_692_, v_v_682_);
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 8, v___x_712_);
v___x_714_ = v___x_710_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_vars_684_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v_varMap_685_);
lean_ctor_set(v_reuseFailAlloc_715_, 2, v_vars_x27_686_);
lean_ctor_set(v_reuseFailAlloc_715_, 3, v_varMap_x27_687_);
lean_ctor_set(v_reuseFailAlloc_715_, 4, v_natToIntMap_688_);
lean_ctor_set(v_reuseFailAlloc_715_, 5, v_natDef_689_);
lean_ctor_set(v_reuseFailAlloc_715_, 6, v_dvds_690_);
lean_ctor_set(v_reuseFailAlloc_715_, 7, v_lowers_691_);
lean_ctor_set(v_reuseFailAlloc_715_, 8, v___x_712_);
lean_ctor_set(v_reuseFailAlloc_715_, 9, v_diseqs_693_);
lean_ctor_set(v_reuseFailAlloc_715_, 10, v_elimEqs_694_);
lean_ctor_set(v_reuseFailAlloc_715_, 11, v_elimStack_695_);
lean_ctor_set(v_reuseFailAlloc_715_, 12, v_occurs_696_);
lean_ctor_set(v_reuseFailAlloc_715_, 13, v_assignment_697_);
lean_ctor_set(v_reuseFailAlloc_715_, 14, v_nextCnstrId_698_);
lean_ctor_set(v_reuseFailAlloc_715_, 15, v_conflict_x3f_700_);
lean_ctor_set(v_reuseFailAlloc_715_, 16, v_diseqSplits_701_);
lean_ctor_set(v_reuseFailAlloc_715_, 17, v_divMod_702_);
lean_ctor_set(v_reuseFailAlloc_715_, 18, v_toIntIds_703_);
lean_ctor_set(v_reuseFailAlloc_715_, 19, v_toIntInfos_704_);
lean_ctor_set(v_reuseFailAlloc_715_, 20, v_toIntTermMap_705_);
lean_ctor_set(v_reuseFailAlloc_715_, 21, v_toIntVarMap_706_);
lean_ctor_set(v_reuseFailAlloc_715_, 22, v_nonlinearOccs_708_);
lean_ctor_set_uint8(v_reuseFailAlloc_715_, sizeof(void*)*23, v_caseSplits_699_);
lean_ctor_set_uint8(v_reuseFailAlloc_715_, sizeof(void*)*23 + 1, v_usedCommRing_707_);
v___x_714_ = v_reuseFailAlloc_715_;
goto v_reusejp_713_;
}
v_reusejp_713_:
{
return v___x_714_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___boxed(lean_object* v_p_717_, lean_object* v_v_718_, lean_object* v_s_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0(v_p_717_, v_v_718_, v_s_719_);
lean_dec(v_v_718_);
lean_dec_ref(v_p_717_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1(lean_object* v_p_721_, lean_object* v_v_722_, lean_object* v_s_723_){
_start:
{
lean_object* v_vars_724_; lean_object* v_varMap_725_; lean_object* v_vars_x27_726_; lean_object* v_varMap_x27_727_; lean_object* v_natToIntMap_728_; lean_object* v_natDef_729_; lean_object* v_dvds_730_; lean_object* v_lowers_731_; lean_object* v_uppers_732_; lean_object* v_diseqs_733_; lean_object* v_elimEqs_734_; lean_object* v_elimStack_735_; lean_object* v_occurs_736_; lean_object* v_assignment_737_; lean_object* v_nextCnstrId_738_; uint8_t v_caseSplits_739_; lean_object* v_conflict_x3f_740_; lean_object* v_diseqSplits_741_; lean_object* v_divMod_742_; lean_object* v_toIntIds_743_; lean_object* v_toIntInfos_744_; lean_object* v_toIntTermMap_745_; lean_object* v_toIntVarMap_746_; uint8_t v_usedCommRing_747_; lean_object* v_nonlinearOccs_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_756_; 
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
v_isSharedCheck_756_ = !lean_is_exclusive(v_s_723_);
if (v_isSharedCheck_756_ == 0)
{
v___x_750_ = v_s_723_;
v_isShared_751_ = v_isSharedCheck_756_;
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
v_isShared_751_ = v_isSharedCheck_756_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_752_; lean_object* v___x_754_; 
v___x_752_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(v_p_721_, v_lowers_731_, v_v_722_);
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 7, v___x_752_);
v___x_754_ = v___x_750_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_vars_724_);
lean_ctor_set(v_reuseFailAlloc_755_, 1, v_varMap_725_);
lean_ctor_set(v_reuseFailAlloc_755_, 2, v_vars_x27_726_);
lean_ctor_set(v_reuseFailAlloc_755_, 3, v_varMap_x27_727_);
lean_ctor_set(v_reuseFailAlloc_755_, 4, v_natToIntMap_728_);
lean_ctor_set(v_reuseFailAlloc_755_, 5, v_natDef_729_);
lean_ctor_set(v_reuseFailAlloc_755_, 6, v_dvds_730_);
lean_ctor_set(v_reuseFailAlloc_755_, 7, v___x_752_);
lean_ctor_set(v_reuseFailAlloc_755_, 8, v_uppers_732_);
lean_ctor_set(v_reuseFailAlloc_755_, 9, v_diseqs_733_);
lean_ctor_set(v_reuseFailAlloc_755_, 10, v_elimEqs_734_);
lean_ctor_set(v_reuseFailAlloc_755_, 11, v_elimStack_735_);
lean_ctor_set(v_reuseFailAlloc_755_, 12, v_occurs_736_);
lean_ctor_set(v_reuseFailAlloc_755_, 13, v_assignment_737_);
lean_ctor_set(v_reuseFailAlloc_755_, 14, v_nextCnstrId_738_);
lean_ctor_set(v_reuseFailAlloc_755_, 15, v_conflict_x3f_740_);
lean_ctor_set(v_reuseFailAlloc_755_, 16, v_diseqSplits_741_);
lean_ctor_set(v_reuseFailAlloc_755_, 17, v_divMod_742_);
lean_ctor_set(v_reuseFailAlloc_755_, 18, v_toIntIds_743_);
lean_ctor_set(v_reuseFailAlloc_755_, 19, v_toIntInfos_744_);
lean_ctor_set(v_reuseFailAlloc_755_, 20, v_toIntTermMap_745_);
lean_ctor_set(v_reuseFailAlloc_755_, 21, v_toIntVarMap_746_);
lean_ctor_set(v_reuseFailAlloc_755_, 22, v_nonlinearOccs_748_);
lean_ctor_set_uint8(v_reuseFailAlloc_755_, sizeof(void*)*23, v_caseSplits_739_);
lean_ctor_set_uint8(v_reuseFailAlloc_755_, sizeof(void*)*23 + 1, v_usedCommRing_747_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1___boxed(lean_object* v_p_757_, lean_object* v_v_758_, lean_object* v_s_759_){
_start:
{
lean_object* v_res_760_; 
v_res_760_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1(v_p_757_, v_v_758_, v_s_759_);
lean_dec(v_v_758_);
lean_dec_ref(v_p_757_);
return v_res_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(lean_object* v_c_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_){
_start:
{
lean_object* v_p_768_; 
v_p_768_ = lean_ctor_get(v_c_761_, 0);
if (lean_obj_tag(v_p_768_) == 1)
{
lean_object* v_k_769_; lean_object* v_v_770_; lean_object* v___x_771_; uint8_t v___x_772_; 
lean_inc_ref(v_p_768_);
lean_dec_ref(v_c_761_);
v_k_769_ = lean_ctor_get(v_p_768_, 0);
v_v_770_ = lean_ctor_get(v_p_768_, 1);
lean_inc(v_v_770_);
v___x_771_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9);
v___x_772_ = lean_int_dec_lt(v_k_769_, v___x_771_);
if (v___x_772_ == 0)
{
lean_object* v___f_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___f_773_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_773_, 0, v_p_768_);
lean_closure_set(v___f_773_, 1, v_v_770_);
v___x_774_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_775_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_774_, v___f_773_, v_a_762_);
return v___x_775_;
}
else
{
lean_object* v___f_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___f_776_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_776_, 0, v_p_768_);
lean_closure_set(v___f_776_, 1, v_v_770_);
v___x_777_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_778_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_777_, v___f_776_, v_a_762_);
return v___x_778_;
}
}
else
{
lean_object* v___x_779_; 
v___x_779_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_);
return v___x_779_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___boxed(lean_object* v_c_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_c_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_);
lean_dec(v_a_785_);
lean_dec_ref(v_a_784_);
lean_dec(v_a_783_);
lean_dec_ref(v_a_782_);
lean_dec(v_a_781_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase(lean_object* v_c_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_c_788_, v_a_789_, v_a_795_, v_a_796_, v_a_797_, v_a_798_);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___boxed(lean_object* v_c_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase(v_c_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec(v_a_803_);
lean_dec(v_a_802_);
return v_res_813_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5(void){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_827_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_828_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_829_ = l_Lean_Name_append(v___x_828_, v___x_827_);
return v___x_829_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7(void){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__6));
v___x_832_ = l_Lean_stringToMessageData(v___x_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3(lean_object* v___x_833_, lean_object* v_c_834_, lean_object* v_as_835_, size_t v_sz_836_, size_t v_i_837_, lean_object* v_b_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
uint8_t v___x_850_; 
v___x_850_ = lean_usize_dec_lt(v_i_837_, v_sz_836_);
if (v___x_850_ == 0)
{
lean_object* v___x_851_; 
lean_dec_ref(v_c_834_);
lean_dec_ref(v___x_833_);
v___x_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_851_, 0, v_b_838_);
return v___x_851_;
}
else
{
lean_object* v_snd_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_938_; 
v_snd_852_ = lean_ctor_get(v_b_838_, 1);
v_isSharedCheck_938_ = !lean_is_exclusive(v_b_838_);
if (v_isSharedCheck_938_ == 0)
{
lean_object* v_unused_939_; 
v_unused_939_ = lean_ctor_get(v_b_838_, 0);
lean_dec(v_unused_939_);
v___x_854_ = v_b_838_;
v_isShared_855_ = v_isSharedCheck_938_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_snd_852_);
lean_dec(v_b_838_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_938_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v_a_856_; lean_object* v_p_857_; lean_object* v___x_858_; uint8_t v___x_859_; 
v_a_856_ = lean_array_uget_borrowed(v_as_835_, v_i_837_);
v_p_857_ = lean_ctor_get(v_a_856_, 0);
v___x_858_ = lean_box(0);
v___x_859_ = l_Int_Internal_Linear_Poly_isNegEq(v___x_833_, v_p_857_);
if (v___x_859_ == 0)
{
lean_object* v___x_860_; size_t v___x_861_; size_t v___x_862_; 
lean_del_object(v___x_854_);
lean_dec(v_snd_852_);
v___x_860_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__1));
v___x_861_ = ((size_t)1ULL);
v___x_862_ = lean_usize_add(v_i_837_, v___x_861_);
v_i_837_ = v___x_862_;
v_b_838_ = v___x_860_;
goto _start;
}
else
{
lean_object* v___x_864_; 
lean_inc(v_a_856_);
v___x_864_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_856_, v___y_839_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v_options_865_; lean_object* v_inheritedTraceOptions_866_; uint8_t v_hasTrace_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___y_871_; lean_object* v___y_872_; lean_object* v___y_873_; lean_object* v___y_874_; lean_object* v___y_875_; lean_object* v___y_876_; lean_object* v___y_877_; lean_object* v___y_878_; lean_object* v___y_879_; lean_object* v___y_880_; 
lean_dec_ref_known(v___x_864_, 1);
v_options_865_ = lean_ctor_get(v___y_847_, 2);
v_inheritedTraceOptions_866_ = lean_ctor_get(v___y_847_, 13);
v_hasTrace_867_ = lean_ctor_get_uint8(v_options_865_, sizeof(void*)*1);
lean_inc(v_a_856_);
v___x_868_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_868_, 0, v_c_834_);
lean_ctor_set(v___x_868_, 1, v_a_856_);
v___x_869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_869_, 0, v___x_833_);
lean_ctor_set(v___x_869_, 1, v___x_868_);
if (v_hasTrace_867_ == 0)
{
v___y_871_ = v___y_839_;
v___y_872_ = v___y_840_;
v___y_873_ = v___y_841_;
v___y_874_ = v___y_842_;
v___y_875_ = v___y_843_;
v___y_876_ = v___y_844_;
v___y_877_ = v___y_845_;
v___y_878_ = v___y_846_;
v___y_879_ = v___y_847_;
v___y_880_ = v___y_848_;
goto v___jp_870_;
}
else
{
lean_object* v___x_906_; lean_object* v___x_907_; uint8_t v___x_908_; 
v___x_906_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_907_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5);
v___x_908_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_866_, v_options_865_, v___x_907_);
if (v___x_908_ == 0)
{
v___y_871_ = v___y_839_;
v___y_872_ = v___y_840_;
v___y_873_ = v___y_841_;
v___y_874_ = v___y_842_;
v___y_875_ = v___y_843_;
v___y_876_ = v___y_844_;
v___y_877_ = v___y_845_;
v___y_878_ = v___y_846_;
v___y_879_ = v___y_847_;
v___y_880_ = v___y_848_;
goto v___jp_870_;
}
else
{
lean_object* v___x_909_; 
lean_inc_ref(v___x_869_);
v___x_909_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_869_, v___y_839_, v___y_847_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_object* v_a_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v_a_910_ = lean_ctor_get(v___x_909_, 0);
lean_inc(v_a_910_);
lean_dec_ref_known(v___x_909_, 1);
v___x_911_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7);
v___x_912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
lean_ctor_set(v___x_912_, 1, v_a_910_);
v___x_913_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_906_, v___x_912_, v___y_845_, v___y_846_, v___y_847_, v___y_848_);
if (lean_obj_tag(v___x_913_) == 0)
{
lean_dec_ref_known(v___x_913_, 1);
v___y_871_ = v___y_839_;
v___y_872_ = v___y_840_;
v___y_873_ = v___y_841_;
v___y_874_ = v___y_842_;
v___y_875_ = v___y_843_;
v___y_876_ = v___y_844_;
v___y_877_ = v___y_845_;
v___y_878_ = v___y_846_;
v___y_879_ = v___y_847_;
v___y_880_ = v___y_848_;
goto v___jp_870_;
}
else
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_921_; 
lean_dec_ref_known(v___x_869_, 2);
lean_del_object(v___x_854_);
lean_dec(v_snd_852_);
v_a_914_ = lean_ctor_get(v___x_913_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_913_);
if (v_isSharedCheck_921_ == 0)
{
v___x_916_ = v___x_913_;
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_913_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_919_; 
if (v_isShared_917_ == 0)
{
v___x_919_ = v___x_916_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_a_914_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
else
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
lean_dec_ref_known(v___x_869_, 2);
lean_del_object(v___x_854_);
lean_dec(v_snd_852_);
v_a_922_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_929_ == 0)
{
v___x_924_ = v___x_909_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_909_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_a_922_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
}
v___jp_870_:
{
lean_object* v___x_881_; 
lean_inc(v___y_880_);
lean_inc_ref(v___y_879_);
lean_inc(v___y_878_);
lean_inc_ref(v___y_877_);
lean_inc(v___y_876_);
lean_inc_ref(v___y_875_);
lean_inc(v___y_874_);
lean_inc_ref(v___y_873_);
lean_inc(v___y_872_);
lean_inc(v___y_871_);
v___x_881_ = lean_grind_cutsat_assert_eq(v___x_869_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_896_; 
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_896_ == 0)
{
lean_object* v_unused_897_; 
v_unused_897_ = lean_ctor_get(v___x_881_, 0);
lean_dec(v_unused_897_);
v___x_883_ = v___x_881_;
v_isShared_884_ = v_isSharedCheck_896_;
goto v_resetjp_882_;
}
else
{
lean_dec(v___x_881_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_896_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_888_; 
v___x_885_ = lean_box(v___x_859_);
v___x_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_886_, 0, v___x_885_);
if (v_isShared_855_ == 0)
{
lean_ctor_set(v___x_854_, 1, v___x_858_);
lean_ctor_set(v___x_854_, 0, v___x_886_);
v___x_888_ = v___x_854_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_886_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v___x_858_);
v___x_888_ = v_reuseFailAlloc_895_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_893_; 
v___x_889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_889_, 0, v___x_888_);
v___x_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_890_, 0, v___x_889_);
v___x_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_891_, 0, v___x_890_);
lean_ctor_set(v___x_891_, 1, v_snd_852_);
if (v_isShared_884_ == 0)
{
lean_ctor_set(v___x_883_, 0, v___x_891_);
v___x_893_ = v___x_883_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_891_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
else
{
lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_905_; 
lean_del_object(v___x_854_);
lean_dec(v_snd_852_);
v_a_898_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_905_ == 0)
{
v___x_900_ = v___x_881_;
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v___x_881_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_903_; 
if (v_isShared_901_ == 0)
{
v___x_903_ = v___x_900_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_a_898_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
}
}
else
{
lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_937_; 
lean_del_object(v___x_854_);
lean_dec(v_snd_852_);
lean_dec_ref(v_c_834_);
lean_dec_ref(v___x_833_);
v_a_930_ = lean_ctor_get(v___x_864_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_864_);
if (v_isSharedCheck_937_ == 0)
{
v___x_932_ = v___x_864_;
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___x_864_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_935_; 
if (v_isShared_933_ == 0)
{
v___x_935_ = v___x_932_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_a_930_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___boxed(lean_object** _args){
lean_object* v___x_940_ = _args[0];
lean_object* v_c_941_ = _args[1];
lean_object* v_as_942_ = _args[2];
lean_object* v_sz_943_ = _args[3];
lean_object* v_i_944_ = _args[4];
lean_object* v_b_945_ = _args[5];
lean_object* v___y_946_ = _args[6];
lean_object* v___y_947_ = _args[7];
lean_object* v___y_948_ = _args[8];
lean_object* v___y_949_ = _args[9];
lean_object* v___y_950_ = _args[10];
lean_object* v___y_951_ = _args[11];
lean_object* v___y_952_ = _args[12];
lean_object* v___y_953_ = _args[13];
lean_object* v___y_954_ = _args[14];
lean_object* v___y_955_ = _args[15];
lean_object* v___y_956_ = _args[16];
_start:
{
size_t v_sz_boxed_957_; size_t v_i_boxed_958_; lean_object* v_res_959_; 
v_sz_boxed_957_ = lean_unbox_usize(v_sz_943_);
lean_dec(v_sz_943_);
v_i_boxed_958_ = lean_unbox_usize(v_i_944_);
lean_dec(v_i_944_);
v_res_959_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3(v___x_940_, v_c_941_, v_as_942_, v_sz_boxed_957_, v_i_boxed_958_, v_b_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
lean_dec(v___y_955_);
lean_dec_ref(v___y_954_);
lean_dec(v___y_953_);
lean_dec_ref(v___y_952_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v___y_947_);
lean_dec(v___y_946_);
lean_dec_ref(v_as_942_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2(lean_object* v___x_966_, lean_object* v_c_967_, lean_object* v_as_968_, size_t v_sz_969_, size_t v_i_970_, lean_object* v_b_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
uint8_t v___x_983_; 
v___x_983_ = lean_usize_dec_lt(v_i_970_, v_sz_969_);
if (v___x_983_ == 0)
{
lean_object* v___x_984_; 
lean_dec_ref(v_c_967_);
lean_dec_ref(v___x_966_);
v___x_984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_984_, 0, v_b_971_);
return v___x_984_;
}
else
{
lean_object* v_snd_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_1071_; 
v_snd_985_ = lean_ctor_get(v_b_971_, 1);
v_isSharedCheck_1071_ = !lean_is_exclusive(v_b_971_);
if (v_isSharedCheck_1071_ == 0)
{
lean_object* v_unused_1072_; 
v_unused_1072_ = lean_ctor_get(v_b_971_, 0);
lean_dec(v_unused_1072_);
v___x_987_ = v_b_971_;
v_isShared_988_ = v_isSharedCheck_1071_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_snd_985_);
lean_dec(v_b_971_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_1071_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v_a_989_; lean_object* v_p_990_; lean_object* v___x_991_; uint8_t v___x_992_; 
v_a_989_ = lean_array_uget_borrowed(v_as_968_, v_i_970_);
v_p_990_ = lean_ctor_get(v_a_989_, 0);
v___x_991_ = lean_box(0);
v___x_992_ = l_Int_Internal_Linear_Poly_isNegEq(v___x_966_, v_p_990_);
if (v___x_992_ == 0)
{
lean_object* v___x_993_; size_t v___x_994_; size_t v___x_995_; lean_object* v___x_996_; 
lean_del_object(v___x_987_);
lean_dec(v_snd_985_);
v___x_993_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__1));
v___x_994_ = ((size_t)1ULL);
v___x_995_ = lean_usize_add(v_i_970_, v___x_994_);
v___x_996_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3(v___x_966_, v_c_967_, v_as_968_, v_sz_969_, v___x_995_, v___x_993_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_);
return v___x_996_;
}
else
{
lean_object* v___x_997_; 
lean_inc(v_a_989_);
v___x_997_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_989_, v___y_972_, v___y_978_, v___y_979_, v___y_980_, v___y_981_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_options_998_; lean_object* v_inheritedTraceOptions_999_; uint8_t v_hasTrace_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v___y_1006_; lean_object* v___y_1007_; lean_object* v___y_1008_; lean_object* v___y_1009_; lean_object* v___y_1010_; lean_object* v___y_1011_; lean_object* v___y_1012_; lean_object* v___y_1013_; 
lean_dec_ref_known(v___x_997_, 1);
v_options_998_ = lean_ctor_get(v___y_980_, 2);
v_inheritedTraceOptions_999_ = lean_ctor_get(v___y_980_, 13);
v_hasTrace_1000_ = lean_ctor_get_uint8(v_options_998_, sizeof(void*)*1);
lean_inc(v_a_989_);
v___x_1001_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1001_, 0, v_c_967_);
lean_ctor_set(v___x_1001_, 1, v_a_989_);
v___x_1002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___x_966_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
if (v_hasTrace_1000_ == 0)
{
v___y_1004_ = v___y_972_;
v___y_1005_ = v___y_973_;
v___y_1006_ = v___y_974_;
v___y_1007_ = v___y_975_;
v___y_1008_ = v___y_976_;
v___y_1009_ = v___y_977_;
v___y_1010_ = v___y_978_;
v___y_1011_ = v___y_979_;
v___y_1012_ = v___y_980_;
v___y_1013_ = v___y_981_;
goto v___jp_1003_;
}
else
{
lean_object* v___x_1039_; lean_object* v___x_1040_; uint8_t v___x_1041_; 
v___x_1039_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_1040_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5);
v___x_1041_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_999_, v_options_998_, v___x_1040_);
if (v___x_1041_ == 0)
{
v___y_1004_ = v___y_972_;
v___y_1005_ = v___y_973_;
v___y_1006_ = v___y_974_;
v___y_1007_ = v___y_975_;
v___y_1008_ = v___y_976_;
v___y_1009_ = v___y_977_;
v___y_1010_ = v___y_978_;
v___y_1011_ = v___y_979_;
v___y_1012_ = v___y_980_;
v___y_1013_ = v___y_981_;
goto v___jp_1003_;
}
else
{
lean_object* v___x_1042_; 
lean_inc_ref(v___x_1002_);
v___x_1042_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_1002_, v___y_972_, v___y_980_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_object* v_a_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
lean_inc(v_a_1043_);
lean_dec_ref_known(v___x_1042_, 1);
v___x_1044_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7);
v___x_1045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1045_, 0, v___x_1044_);
lean_ctor_set(v___x_1045_, 1, v_a_1043_);
v___x_1046_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_1039_, v___x_1045_, v___y_978_, v___y_979_, v___y_980_, v___y_981_);
if (lean_obj_tag(v___x_1046_) == 0)
{
lean_dec_ref_known(v___x_1046_, 1);
v___y_1004_ = v___y_972_;
v___y_1005_ = v___y_973_;
v___y_1006_ = v___y_974_;
v___y_1007_ = v___y_975_;
v___y_1008_ = v___y_976_;
v___y_1009_ = v___y_977_;
v___y_1010_ = v___y_978_;
v___y_1011_ = v___y_979_;
v___y_1012_ = v___y_980_;
v___y_1013_ = v___y_981_;
goto v___jp_1003_;
}
else
{
lean_object* v_a_1047_; lean_object* v___x_1049_; uint8_t v_isShared_1050_; uint8_t v_isSharedCheck_1054_; 
lean_dec_ref_known(v___x_1002_, 2);
lean_del_object(v___x_987_);
lean_dec(v_snd_985_);
v_a_1047_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1054_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1054_ == 0)
{
v___x_1049_ = v___x_1046_;
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
else
{
lean_inc(v_a_1047_);
lean_dec(v___x_1046_);
v___x_1049_ = lean_box(0);
v_isShared_1050_ = v_isSharedCheck_1054_;
goto v_resetjp_1048_;
}
v_resetjp_1048_:
{
lean_object* v___x_1052_; 
if (v_isShared_1050_ == 0)
{
v___x_1052_ = v___x_1049_;
goto v_reusejp_1051_;
}
else
{
lean_object* v_reuseFailAlloc_1053_; 
v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1047_);
v___x_1052_ = v_reuseFailAlloc_1053_;
goto v_reusejp_1051_;
}
v_reusejp_1051_:
{
return v___x_1052_;
}
}
}
}
else
{
lean_object* v_a_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1062_; 
lean_dec_ref_known(v___x_1002_, 2);
lean_del_object(v___x_987_);
lean_dec(v_snd_985_);
v_a_1055_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1062_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1062_ == 0)
{
v___x_1057_ = v___x_1042_;
v_isShared_1058_ = v_isSharedCheck_1062_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_a_1055_);
lean_dec(v___x_1042_);
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
v___jp_1003_:
{
lean_object* v___x_1014_; 
lean_inc(v___y_1013_);
lean_inc_ref(v___y_1012_);
lean_inc(v___y_1011_);
lean_inc_ref(v___y_1010_);
lean_inc(v___y_1009_);
lean_inc_ref(v___y_1008_);
lean_inc(v___y_1007_);
lean_inc_ref(v___y_1006_);
lean_inc(v___y_1005_);
lean_inc(v___y_1004_);
v___x_1014_ = lean_grind_cutsat_assert_eq(v___x_1002_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1029_; 
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1029_ == 0)
{
lean_object* v_unused_1030_; 
v_unused_1030_ = lean_ctor_get(v___x_1014_, 0);
lean_dec(v_unused_1030_);
v___x_1016_ = v___x_1014_;
v_isShared_1017_ = v_isSharedCheck_1029_;
goto v_resetjp_1015_;
}
else
{
lean_dec(v___x_1014_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1029_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1021_; 
v___x_1018_ = lean_box(v___x_992_);
v___x_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1018_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 1, v___x_991_);
lean_ctor_set(v___x_987_, 0, v___x_1019_);
v___x_1021_ = v___x_987_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v___x_1019_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v___x_991_);
v___x_1021_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1026_; 
v___x_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1022_, 0, v___x_1021_);
v___x_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1023_, 0, v___x_1022_);
v___x_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1024_, 0, v___x_1023_);
lean_ctor_set(v___x_1024_, 1, v_snd_985_);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 0, v___x_1024_);
v___x_1026_ = v___x_1016_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1024_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
else
{
lean_object* v_a_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1038_; 
lean_del_object(v___x_987_);
lean_dec(v_snd_985_);
v_a_1031_ = lean_ctor_get(v___x_1014_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v___x_1014_);
if (v_isSharedCheck_1038_ == 0)
{
v___x_1033_ = v___x_1014_;
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_a_1031_);
lean_dec(v___x_1014_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1038_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1034_ == 0)
{
v___x_1036_ = v___x_1033_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v_a_1031_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
}
else
{
lean_object* v_a_1063_; lean_object* v___x_1065_; uint8_t v_isShared_1066_; uint8_t v_isSharedCheck_1070_; 
lean_del_object(v___x_987_);
lean_dec(v_snd_985_);
lean_dec_ref(v_c_967_);
lean_dec_ref(v___x_966_);
v_a_1063_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1070_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1070_ == 0)
{
v___x_1065_ = v___x_997_;
v_isShared_1066_ = v_isSharedCheck_1070_;
goto v_resetjp_1064_;
}
else
{
lean_inc(v_a_1063_);
lean_dec(v___x_997_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___boxed(lean_object** _args){
lean_object* v___x_1073_ = _args[0];
lean_object* v_c_1074_ = _args[1];
lean_object* v_as_1075_ = _args[2];
lean_object* v_sz_1076_ = _args[3];
lean_object* v_i_1077_ = _args[4];
lean_object* v_b_1078_ = _args[5];
lean_object* v___y_1079_ = _args[6];
lean_object* v___y_1080_ = _args[7];
lean_object* v___y_1081_ = _args[8];
lean_object* v___y_1082_ = _args[9];
lean_object* v___y_1083_ = _args[10];
lean_object* v___y_1084_ = _args[11];
lean_object* v___y_1085_ = _args[12];
lean_object* v___y_1086_ = _args[13];
lean_object* v___y_1087_ = _args[14];
lean_object* v___y_1088_ = _args[15];
lean_object* v___y_1089_ = _args[16];
_start:
{
size_t v_sz_boxed_1090_; size_t v_i_boxed_1091_; lean_object* v_res_1092_; 
v_sz_boxed_1090_ = lean_unbox_usize(v_sz_1076_);
lean_dec(v_sz_1076_);
v_i_boxed_1091_ = lean_unbox_usize(v_i_1077_);
lean_dec(v_i_1077_);
v_res_1092_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2(v___x_1073_, v_c_1074_, v_as_1075_, v_sz_boxed_1090_, v_i_boxed_1091_, v_b_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_);
lean_dec(v___y_1088_);
lean_dec_ref(v___y_1087_);
lean_dec(v___y_1086_);
lean_dec_ref(v___y_1085_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v_as_1075_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(lean_object* v_init_1093_, lean_object* v___x_1094_, lean_object* v_c_1095_, lean_object* v_n_1096_, lean_object* v_b_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
if (lean_obj_tag(v_n_1096_) == 0)
{
lean_object* v_cs_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; size_t v_sz_1112_; size_t v___x_1113_; lean_object* v___x_1114_; 
v_cs_1109_ = lean_ctor_get(v_n_1096_, 0);
v___x_1110_ = lean_box(0);
v___x_1111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1110_);
lean_ctor_set(v___x_1111_, 1, v_b_1097_);
v_sz_1112_ = lean_array_size(v_cs_1109_);
v___x_1113_ = ((size_t)0ULL);
v___x_1114_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(v_init_1093_, v___x_1094_, v_c_1095_, v_cs_1109_, v_sz_1112_, v___x_1113_, v___x_1111_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; lean_object* v___x_1117_; uint8_t v_isShared_1118_; uint8_t v_isSharedCheck_1129_; 
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1117_ = v___x_1114_;
v_isShared_1118_ = v_isSharedCheck_1129_;
goto v_resetjp_1116_;
}
else
{
lean_inc(v_a_1115_);
lean_dec(v___x_1114_);
v___x_1117_ = lean_box(0);
v_isShared_1118_ = v_isSharedCheck_1129_;
goto v_resetjp_1116_;
}
v_resetjp_1116_:
{
lean_object* v_fst_1119_; 
v_fst_1119_ = lean_ctor_get(v_a_1115_, 0);
if (lean_obj_tag(v_fst_1119_) == 0)
{
lean_object* v_snd_1120_; lean_object* v___x_1121_; lean_object* v___x_1123_; 
v_snd_1120_ = lean_ctor_get(v_a_1115_, 1);
lean_inc(v_snd_1120_);
lean_dec(v_a_1115_);
v___x_1121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1121_, 0, v_snd_1120_);
if (v_isShared_1118_ == 0)
{
lean_ctor_set(v___x_1117_, 0, v___x_1121_);
v___x_1123_ = v___x_1117_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v___x_1121_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
else
{
lean_object* v_val_1125_; lean_object* v___x_1127_; 
lean_inc_ref(v_fst_1119_);
lean_dec(v_a_1115_);
v_val_1125_ = lean_ctor_get(v_fst_1119_, 0);
lean_inc(v_val_1125_);
lean_dec_ref_known(v_fst_1119_, 1);
if (v_isShared_1118_ == 0)
{
lean_ctor_set(v___x_1117_, 0, v_val_1125_);
v___x_1127_ = v___x_1117_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_val_1125_);
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
else
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
v_a_1130_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1132_ = v___x_1114_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v___x_1114_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_a_1130_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
else
{
lean_object* v_vs_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; size_t v_sz_1141_; size_t v___x_1142_; lean_object* v___x_1143_; 
v_vs_1138_ = lean_ctor_get(v_n_1096_, 0);
v___x_1139_ = lean_box(0);
v___x_1140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1139_);
lean_ctor_set(v___x_1140_, 1, v_b_1097_);
v_sz_1141_ = lean_array_size(v_vs_1138_);
v___x_1142_ = ((size_t)0ULL);
v___x_1143_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2(v___x_1094_, v_c_1095_, v_vs_1138_, v_sz_1141_, v___x_1142_, v___x_1140_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
if (lean_obj_tag(v___x_1143_) == 0)
{
lean_object* v_a_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1158_; 
v_a_1144_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1146_ = v___x_1143_;
v_isShared_1147_ = v_isSharedCheck_1158_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_a_1144_);
lean_dec(v___x_1143_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1158_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v_fst_1148_; 
v_fst_1148_ = lean_ctor_get(v_a_1144_, 0);
if (lean_obj_tag(v_fst_1148_) == 0)
{
lean_object* v_snd_1149_; lean_object* v___x_1150_; lean_object* v___x_1152_; 
v_snd_1149_ = lean_ctor_get(v_a_1144_, 1);
lean_inc(v_snd_1149_);
lean_dec(v_a_1144_);
v___x_1150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1150_, 0, v_snd_1149_);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 0, v___x_1150_);
v___x_1152_ = v___x_1146_;
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
lean_object* v_val_1154_; lean_object* v___x_1156_; 
lean_inc_ref(v_fst_1148_);
lean_dec(v_a_1144_);
v_val_1154_ = lean_ctor_get(v_fst_1148_, 0);
lean_inc(v_val_1154_);
lean_dec_ref_known(v_fst_1148_, 1);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 0, v_val_1154_);
v___x_1156_ = v___x_1146_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_val_1154_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
}
else
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
v_a_1159_ = lean_ctor_get(v___x_1143_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1143_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1161_ = v___x_1143_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1143_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(lean_object* v_init_1167_, lean_object* v___x_1168_, lean_object* v_c_1169_, lean_object* v_as_1170_, size_t v_sz_1171_, size_t v_i_1172_, lean_object* v_b_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
uint8_t v___x_1185_; 
v___x_1185_ = lean_usize_dec_lt(v_i_1172_, v_sz_1171_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1186_; 
lean_dec_ref(v_c_1169_);
lean_dec_ref(v___x_1168_);
v___x_1186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1186_, 0, v_b_1173_);
return v___x_1186_;
}
else
{
lean_object* v_snd_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1221_; 
v_snd_1187_ = lean_ctor_get(v_b_1173_, 1);
v_isSharedCheck_1221_ = !lean_is_exclusive(v_b_1173_);
if (v_isSharedCheck_1221_ == 0)
{
lean_object* v_unused_1222_; 
v_unused_1222_ = lean_ctor_get(v_b_1173_, 0);
lean_dec(v_unused_1222_);
v___x_1189_ = v_b_1173_;
v_isShared_1190_ = v_isSharedCheck_1221_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_snd_1187_);
lean_dec(v_b_1173_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1221_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v_a_1191_; lean_object* v___x_1192_; 
v_a_1191_ = lean_array_uget_borrowed(v_as_1170_, v_i_1172_);
lean_inc(v_snd_1187_);
lean_inc_ref(v_c_1169_);
lean_inc_ref(v___x_1168_);
v___x_1192_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(v_init_1167_, v___x_1168_, v_c_1169_, v_a_1191_, v_snd_1187_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_object* v_a_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1212_; 
v_a_1193_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1212_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1212_ == 0)
{
v___x_1195_ = v___x_1192_;
v_isShared_1196_ = v_isSharedCheck_1212_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_a_1193_);
lean_dec(v___x_1192_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1212_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
if (lean_obj_tag(v_a_1193_) == 0)
{
lean_object* v___x_1197_; lean_object* v___x_1199_; 
lean_dec_ref(v_c_1169_);
lean_dec_ref(v___x_1168_);
v___x_1197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1197_, 0, v_a_1193_);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 0, v___x_1197_);
v___x_1199_ = v___x_1189_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1197_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v_snd_1187_);
v___x_1199_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
lean_object* v___x_1201_; 
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 0, v___x_1199_);
v___x_1201_ = v___x_1195_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1199_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
else
{
lean_object* v_a_1204_; lean_object* v___x_1205_; lean_object* v___x_1207_; 
lean_del_object(v___x_1195_);
lean_dec(v_snd_1187_);
v_a_1204_ = lean_ctor_get(v_a_1193_, 0);
lean_inc(v_a_1204_);
lean_dec_ref_known(v_a_1193_, 1);
v___x_1205_ = lean_box(0);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 1, v_a_1204_);
lean_ctor_set(v___x_1189_, 0, v___x_1205_);
v___x_1207_ = v___x_1189_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1205_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v_a_1204_);
v___x_1207_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
size_t v___x_1208_; size_t v___x_1209_; 
v___x_1208_ = ((size_t)1ULL);
v___x_1209_ = lean_usize_add(v_i_1172_, v___x_1208_);
v_i_1172_ = v___x_1209_;
v_b_1173_ = v___x_1207_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1220_; 
lean_del_object(v___x_1189_);
lean_dec(v_snd_1187_);
lean_dec_ref(v_c_1169_);
lean_dec_ref(v___x_1168_);
v_a_1213_ = lean_ctor_get(v___x_1192_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1192_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1215_ = v___x_1192_;
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v___x_1192_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_init_1223_ = _args[0];
lean_object* v___x_1224_ = _args[1];
lean_object* v_c_1225_ = _args[2];
lean_object* v_as_1226_ = _args[3];
lean_object* v_sz_1227_ = _args[4];
lean_object* v_i_1228_ = _args[5];
lean_object* v_b_1229_ = _args[6];
lean_object* v___y_1230_ = _args[7];
lean_object* v___y_1231_ = _args[8];
lean_object* v___y_1232_ = _args[9];
lean_object* v___y_1233_ = _args[10];
lean_object* v___y_1234_ = _args[11];
lean_object* v___y_1235_ = _args[12];
lean_object* v___y_1236_ = _args[13];
lean_object* v___y_1237_ = _args[14];
lean_object* v___y_1238_ = _args[15];
lean_object* v___y_1239_ = _args[16];
lean_object* v___y_1240_ = _args[17];
_start:
{
size_t v_sz_boxed_1241_; size_t v_i_boxed_1242_; lean_object* v_res_1243_; 
v_sz_boxed_1241_ = lean_unbox_usize(v_sz_1227_);
lean_dec(v_sz_1227_);
v_i_boxed_1242_ = lean_unbox_usize(v_i_1228_);
lean_dec(v_i_1228_);
v_res_1243_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(v_init_1223_, v___x_1224_, v_c_1225_, v_as_1226_, v_sz_boxed_1241_, v_i_boxed_1242_, v_b_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v_as_1226_);
lean_dec_ref(v_init_1223_);
return v_res_1243_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___boxed(lean_object* v_init_1244_, lean_object* v___x_1245_, lean_object* v_c_1246_, lean_object* v_n_1247_, lean_object* v_b_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(v_init_1244_, v___x_1245_, v_c_1246_, v_n_1247_, v_b_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v_n_1247_);
lean_dec_ref(v_init_1244_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4(lean_object* v___x_1267_, lean_object* v_c_1268_, lean_object* v_as_1269_, size_t v_sz_1270_, size_t v_i_1271_, lean_object* v_b_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_){
_start:
{
uint8_t v___x_1284_; 
v___x_1284_ = lean_usize_dec_lt(v_i_1271_, v_sz_1270_);
if (v___x_1284_ == 0)
{
lean_object* v___x_1285_; 
lean_dec_ref(v_c_1268_);
lean_dec_ref(v___x_1267_);
v___x_1285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1285_, 0, v_b_1272_);
return v___x_1285_;
}
else
{
lean_object* v_snd_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1371_; 
v_snd_1286_ = lean_ctor_get(v_b_1272_, 1);
v_isSharedCheck_1371_ = !lean_is_exclusive(v_b_1272_);
if (v_isSharedCheck_1371_ == 0)
{
lean_object* v_unused_1372_; 
v_unused_1372_ = lean_ctor_get(v_b_1272_, 0);
lean_dec(v_unused_1372_);
v___x_1288_ = v_b_1272_;
v_isShared_1289_ = v_isSharedCheck_1371_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_snd_1286_);
lean_dec(v_b_1272_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1371_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v_a_1290_; lean_object* v_p_1291_; lean_object* v___x_1292_; uint8_t v___x_1293_; 
v_a_1290_ = lean_array_uget_borrowed(v_as_1269_, v_i_1271_);
v_p_1291_ = lean_ctor_get(v_a_1290_, 0);
v___x_1292_ = lean_box(0);
v___x_1293_ = l_Int_Internal_Linear_Poly_isNegEq(v___x_1267_, v_p_1291_);
if (v___x_1293_ == 0)
{
lean_object* v___x_1294_; size_t v___x_1295_; size_t v___x_1296_; 
lean_del_object(v___x_1288_);
lean_dec(v_snd_1286_);
v___x_1294_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___closed__1));
v___x_1295_ = ((size_t)1ULL);
v___x_1296_ = lean_usize_add(v_i_1271_, v___x_1295_);
v_i_1271_ = v___x_1296_;
v_b_1272_ = v___x_1294_;
goto _start;
}
else
{
lean_object* v___x_1298_; 
lean_inc(v_a_1290_);
v___x_1298_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_1290_, v___y_1273_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v_options_1299_; lean_object* v_inheritedTraceOptions_1300_; uint8_t v_hasTrace_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___y_1305_; lean_object* v___y_1306_; lean_object* v___y_1307_; lean_object* v___y_1308_; lean_object* v___y_1309_; lean_object* v___y_1310_; lean_object* v___y_1311_; lean_object* v___y_1312_; lean_object* v___y_1313_; lean_object* v___y_1314_; 
lean_dec_ref_known(v___x_1298_, 1);
v_options_1299_ = lean_ctor_get(v___y_1281_, 2);
v_inheritedTraceOptions_1300_ = lean_ctor_get(v___y_1281_, 13);
v_hasTrace_1301_ = lean_ctor_get_uint8(v_options_1299_, sizeof(void*)*1);
lean_inc(v_a_1290_);
v___x_1302_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1302_, 0, v_c_1268_);
lean_ctor_set(v___x_1302_, 1, v_a_1290_);
v___x_1303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1303_, 0, v___x_1267_);
lean_ctor_set(v___x_1303_, 1, v___x_1302_);
if (v_hasTrace_1301_ == 0)
{
v___y_1305_ = v___y_1273_;
v___y_1306_ = v___y_1274_;
v___y_1307_ = v___y_1275_;
v___y_1308_ = v___y_1276_;
v___y_1309_ = v___y_1277_;
v___y_1310_ = v___y_1278_;
v___y_1311_ = v___y_1279_;
v___y_1312_ = v___y_1280_;
v___y_1313_ = v___y_1281_;
v___y_1314_ = v___y_1282_;
goto v___jp_1304_;
}
else
{
lean_object* v___x_1339_; lean_object* v___x_1340_; uint8_t v___x_1341_; 
v___x_1339_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_1340_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5);
v___x_1341_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1300_, v_options_1299_, v___x_1340_);
if (v___x_1341_ == 0)
{
v___y_1305_ = v___y_1273_;
v___y_1306_ = v___y_1274_;
v___y_1307_ = v___y_1275_;
v___y_1308_ = v___y_1276_;
v___y_1309_ = v___y_1277_;
v___y_1310_ = v___y_1278_;
v___y_1311_ = v___y_1279_;
v___y_1312_ = v___y_1280_;
v___y_1313_ = v___y_1281_;
v___y_1314_ = v___y_1282_;
goto v___jp_1304_;
}
else
{
lean_object* v___x_1342_; 
lean_inc_ref(v___x_1303_);
v___x_1342_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_1303_, v___y_1273_, v___y_1281_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v_a_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
lean_inc(v_a_1343_);
lean_dec_ref_known(v___x_1342_, 1);
v___x_1344_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7);
v___x_1345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1344_);
lean_ctor_set(v___x_1345_, 1, v_a_1343_);
v___x_1346_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_1339_, v___x_1345_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_);
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_dec_ref_known(v___x_1346_, 1);
v___y_1305_ = v___y_1273_;
v___y_1306_ = v___y_1274_;
v___y_1307_ = v___y_1275_;
v___y_1308_ = v___y_1276_;
v___y_1309_ = v___y_1277_;
v___y_1310_ = v___y_1278_;
v___y_1311_ = v___y_1279_;
v___y_1312_ = v___y_1280_;
v___y_1313_ = v___y_1281_;
v___y_1314_ = v___y_1282_;
goto v___jp_1304_;
}
else
{
lean_object* v_a_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1354_; 
lean_dec_ref_known(v___x_1303_, 2);
lean_del_object(v___x_1288_);
lean_dec(v_snd_1286_);
v_a_1347_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1354_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1354_ == 0)
{
v___x_1349_ = v___x_1346_;
v_isShared_1350_ = v_isSharedCheck_1354_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_a_1347_);
lean_dec(v___x_1346_);
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
else
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1362_; 
lean_dec_ref_known(v___x_1303_, 2);
lean_del_object(v___x_1288_);
lean_dec(v_snd_1286_);
v_a_1355_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1357_ = v___x_1342_;
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1342_);
v___x_1357_ = lean_box(0);
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
v_resetjp_1356_:
{
lean_object* v___x_1360_; 
if (v_isShared_1358_ == 0)
{
v___x_1360_ = v___x_1357_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1361_; 
v_reuseFailAlloc_1361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_a_1355_);
v___x_1360_ = v_reuseFailAlloc_1361_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
return v___x_1360_;
}
}
}
}
}
v___jp_1304_:
{
lean_object* v___x_1315_; 
lean_inc(v___y_1314_);
lean_inc_ref(v___y_1313_);
lean_inc(v___y_1312_);
lean_inc_ref(v___y_1311_);
lean_inc(v___y_1310_);
lean_inc_ref(v___y_1309_);
lean_inc(v___y_1308_);
lean_inc_ref(v___y_1307_);
lean_inc(v___y_1306_);
lean_inc(v___y_1305_);
v___x_1315_ = lean_grind_cutsat_assert_eq(v___x_1303_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1329_; 
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1329_ == 0)
{
lean_object* v_unused_1330_; 
v_unused_1330_ = lean_ctor_get(v___x_1315_, 0);
lean_dec(v_unused_1330_);
v___x_1317_ = v___x_1315_;
v_isShared_1318_ = v_isSharedCheck_1329_;
goto v_resetjp_1316_;
}
else
{
lean_dec(v___x_1315_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1329_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1322_; 
v___x_1319_ = lean_box(v___x_1293_);
v___x_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 1, v___x_1292_);
lean_ctor_set(v___x_1288_, 0, v___x_1320_);
v___x_1322_ = v___x_1288_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v___x_1320_);
lean_ctor_set(v_reuseFailAlloc_1328_, 1, v___x_1292_);
v___x_1322_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1326_; 
v___x_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1322_);
v___x_1324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1323_);
lean_ctor_set(v___x_1324_, 1, v_snd_1286_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 0, v___x_1324_);
v___x_1326_ = v___x_1317_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v___x_1324_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
else
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1338_; 
lean_del_object(v___x_1288_);
lean_dec(v_snd_1286_);
v_a_1331_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1333_ = v___x_1315_;
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1315_);
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
else
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1370_; 
lean_del_object(v___x_1288_);
lean_dec(v_snd_1286_);
lean_dec_ref(v_c_1268_);
lean_dec_ref(v___x_1267_);
v_a_1363_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1365_ = v___x_1298_;
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1298_);
v___x_1365_ = lean_box(0);
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
v_resetjp_1364_:
{
lean_object* v___x_1368_; 
if (v_isShared_1366_ == 0)
{
v___x_1368_ = v___x_1365_;
goto v_reusejp_1367_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_a_1363_);
v___x_1368_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1367_;
}
v_reusejp_1367_:
{
return v___x_1368_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v___x_1373_ = _args[0];
lean_object* v_c_1374_ = _args[1];
lean_object* v_as_1375_ = _args[2];
lean_object* v_sz_1376_ = _args[3];
lean_object* v_i_1377_ = _args[4];
lean_object* v_b_1378_ = _args[5];
lean_object* v___y_1379_ = _args[6];
lean_object* v___y_1380_ = _args[7];
lean_object* v___y_1381_ = _args[8];
lean_object* v___y_1382_ = _args[9];
lean_object* v___y_1383_ = _args[10];
lean_object* v___y_1384_ = _args[11];
lean_object* v___y_1385_ = _args[12];
lean_object* v___y_1386_ = _args[13];
lean_object* v___y_1387_ = _args[14];
lean_object* v___y_1388_ = _args[15];
lean_object* v___y_1389_ = _args[16];
_start:
{
size_t v_sz_boxed_1390_; size_t v_i_boxed_1391_; lean_object* v_res_1392_; 
v_sz_boxed_1390_ = lean_unbox_usize(v_sz_1376_);
lean_dec(v_sz_1376_);
v_i_boxed_1391_ = lean_unbox_usize(v_i_1377_);
lean_dec(v_i_1377_);
v_res_1392_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4(v___x_1373_, v_c_1374_, v_as_1375_, v_sz_boxed_1390_, v_i_boxed_1391_, v_b_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec(v___y_1380_);
lean_dec(v___y_1379_);
lean_dec_ref(v_as_1375_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1(lean_object* v___x_1396_, lean_object* v_c_1397_, lean_object* v_as_1398_, size_t v_sz_1399_, size_t v_i_1400_, lean_object* v_b_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
uint8_t v___x_1413_; 
v___x_1413_ = lean_usize_dec_lt(v_i_1400_, v_sz_1399_);
if (v___x_1413_ == 0)
{
lean_object* v___x_1414_; 
lean_dec_ref(v_c_1397_);
lean_dec_ref(v___x_1396_);
v___x_1414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1414_, 0, v_b_1401_);
return v___x_1414_;
}
else
{
lean_object* v_snd_1415_; lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1500_; 
v_snd_1415_ = lean_ctor_get(v_b_1401_, 1);
v_isSharedCheck_1500_ = !lean_is_exclusive(v_b_1401_);
if (v_isSharedCheck_1500_ == 0)
{
lean_object* v_unused_1501_; 
v_unused_1501_ = lean_ctor_get(v_b_1401_, 0);
lean_dec(v_unused_1501_);
v___x_1417_ = v_b_1401_;
v_isShared_1418_ = v_isSharedCheck_1500_;
goto v_resetjp_1416_;
}
else
{
lean_inc(v_snd_1415_);
lean_dec(v_b_1401_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1500_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v_a_1419_; lean_object* v_p_1420_; lean_object* v___x_1421_; uint8_t v___x_1422_; 
v_a_1419_ = lean_array_uget_borrowed(v_as_1398_, v_i_1400_);
v_p_1420_ = lean_ctor_get(v_a_1419_, 0);
v___x_1421_ = lean_box(0);
v___x_1422_ = l_Int_Internal_Linear_Poly_isNegEq(v___x_1396_, v_p_1420_);
if (v___x_1422_ == 0)
{
lean_object* v___x_1423_; size_t v___x_1424_; size_t v___x_1425_; lean_object* v___x_1426_; 
lean_del_object(v___x_1417_);
lean_dec(v_snd_1415_);
v___x_1423_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1___closed__0));
v___x_1424_ = ((size_t)1ULL);
v___x_1425_ = lean_usize_add(v_i_1400_, v___x_1424_);
v___x_1426_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4(v___x_1396_, v_c_1397_, v_as_1398_, v_sz_1399_, v___x_1425_, v___x_1423_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
return v___x_1426_;
}
else
{
lean_object* v___x_1427_; 
lean_inc(v_a_1419_);
v___x_1427_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_1419_, v___y_1402_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v_options_1428_; lean_object* v_inheritedTraceOptions_1429_; uint8_t v_hasTrace_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; 
lean_dec_ref_known(v___x_1427_, 1);
v_options_1428_ = lean_ctor_get(v___y_1410_, 2);
v_inheritedTraceOptions_1429_ = lean_ctor_get(v___y_1410_, 13);
v_hasTrace_1430_ = lean_ctor_get_uint8(v_options_1428_, sizeof(void*)*1);
lean_inc(v_a_1419_);
v___x_1431_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1431_, 0, v_c_1397_);
lean_ctor_set(v___x_1431_, 1, v_a_1419_);
v___x_1432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1396_);
lean_ctor_set(v___x_1432_, 1, v___x_1431_);
if (v_hasTrace_1430_ == 0)
{
v___y_1434_ = v___y_1402_;
v___y_1435_ = v___y_1403_;
v___y_1436_ = v___y_1404_;
v___y_1437_ = v___y_1405_;
v___y_1438_ = v___y_1406_;
v___y_1439_ = v___y_1407_;
v___y_1440_ = v___y_1408_;
v___y_1441_ = v___y_1409_;
v___y_1442_ = v___y_1410_;
v___y_1443_ = v___y_1411_;
goto v___jp_1433_;
}
else
{
lean_object* v___x_1468_; lean_object* v___x_1469_; uint8_t v___x_1470_; 
v___x_1468_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_1469_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5);
v___x_1470_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1429_, v_options_1428_, v___x_1469_);
if (v___x_1470_ == 0)
{
v___y_1434_ = v___y_1402_;
v___y_1435_ = v___y_1403_;
v___y_1436_ = v___y_1404_;
v___y_1437_ = v___y_1405_;
v___y_1438_ = v___y_1406_;
v___y_1439_ = v___y_1407_;
v___y_1440_ = v___y_1408_;
v___y_1441_ = v___y_1409_;
v___y_1442_ = v___y_1410_;
v___y_1443_ = v___y_1411_;
goto v___jp_1433_;
}
else
{
lean_object* v___x_1471_; 
lean_inc_ref(v___x_1432_);
v___x_1471_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_1432_, v___y_1402_, v___y_1410_);
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_object* v_a_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; 
v_a_1472_ = lean_ctor_get(v___x_1471_, 0);
lean_inc(v_a_1472_);
lean_dec_ref_known(v___x_1471_, 1);
v___x_1473_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7);
v___x_1474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1473_);
lean_ctor_set(v___x_1474_, 1, v_a_1472_);
v___x_1475_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_1468_, v___x_1474_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_dec_ref_known(v___x_1475_, 1);
v___y_1434_ = v___y_1402_;
v___y_1435_ = v___y_1403_;
v___y_1436_ = v___y_1404_;
v___y_1437_ = v___y_1405_;
v___y_1438_ = v___y_1406_;
v___y_1439_ = v___y_1407_;
v___y_1440_ = v___y_1408_;
v___y_1441_ = v___y_1409_;
v___y_1442_ = v___y_1410_;
v___y_1443_ = v___y_1411_;
goto v___jp_1433_;
}
else
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1483_; 
lean_dec_ref_known(v___x_1432_, 2);
lean_del_object(v___x_1417_);
lean_dec(v_snd_1415_);
v_a_1476_ = lean_ctor_get(v___x_1475_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1475_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1478_ = v___x_1475_;
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1475_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1481_; 
if (v_isShared_1479_ == 0)
{
v___x_1481_ = v___x_1478_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_a_1476_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
}
else
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1491_; 
lean_dec_ref_known(v___x_1432_, 2);
lean_del_object(v___x_1417_);
lean_dec(v_snd_1415_);
v_a_1484_ = lean_ctor_get(v___x_1471_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1471_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1486_ = v___x_1471_;
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v___x_1471_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1489_; 
if (v_isShared_1487_ == 0)
{
v___x_1489_ = v___x_1486_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_a_1484_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
}
}
v___jp_1433_:
{
lean_object* v___x_1444_; 
lean_inc(v___y_1443_);
lean_inc_ref(v___y_1442_);
lean_inc(v___y_1441_);
lean_inc_ref(v___y_1440_);
lean_inc(v___y_1439_);
lean_inc_ref(v___y_1438_);
lean_inc(v___y_1437_);
lean_inc_ref(v___y_1436_);
lean_inc(v___y_1435_);
lean_inc(v___y_1434_);
v___x_1444_ = lean_grind_cutsat_assert_eq(v___x_1432_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1458_; 
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1458_ == 0)
{
lean_object* v_unused_1459_; 
v_unused_1459_ = lean_ctor_get(v___x_1444_, 0);
lean_dec(v_unused_1459_);
v___x_1446_ = v___x_1444_;
v_isShared_1447_ = v_isSharedCheck_1458_;
goto v_resetjp_1445_;
}
else
{
lean_dec(v___x_1444_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1458_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1451_; 
v___x_1448_ = lean_box(v___x_1422_);
v___x_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1448_);
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 1, v___x_1421_);
lean_ctor_set(v___x_1417_, 0, v___x_1449_);
v___x_1451_ = v___x_1417_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v___x_1449_);
lean_ctor_set(v_reuseFailAlloc_1457_, 1, v___x_1421_);
v___x_1451_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1455_; 
v___x_1452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1451_);
v___x_1453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1453_, 0, v___x_1452_);
lean_ctor_set(v___x_1453_, 1, v_snd_1415_);
if (v_isShared_1447_ == 0)
{
lean_ctor_set(v___x_1446_, 0, v___x_1453_);
v___x_1455_ = v___x_1446_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v___x_1453_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
else
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1467_; 
lean_del_object(v___x_1417_);
lean_dec(v_snd_1415_);
v_a_1460_ = lean_ctor_get(v___x_1444_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1462_ = v___x_1444_;
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1444_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1465_; 
if (v_isShared_1463_ == 0)
{
v___x_1465_ = v___x_1462_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1460_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
}
}
}
}
}
else
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1499_; 
lean_del_object(v___x_1417_);
lean_dec(v_snd_1415_);
lean_dec_ref(v_c_1397_);
lean_dec_ref(v___x_1396_);
v_a_1492_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1494_ = v___x_1427_;
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1427_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1497_; 
if (v_isShared_1495_ == 0)
{
v___x_1497_ = v___x_1494_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1492_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v___x_1502_ = _args[0];
lean_object* v_c_1503_ = _args[1];
lean_object* v_as_1504_ = _args[2];
lean_object* v_sz_1505_ = _args[3];
lean_object* v_i_1506_ = _args[4];
lean_object* v_b_1507_ = _args[5];
lean_object* v___y_1508_ = _args[6];
lean_object* v___y_1509_ = _args[7];
lean_object* v___y_1510_ = _args[8];
lean_object* v___y_1511_ = _args[9];
lean_object* v___y_1512_ = _args[10];
lean_object* v___y_1513_ = _args[11];
lean_object* v___y_1514_ = _args[12];
lean_object* v___y_1515_ = _args[13];
lean_object* v___y_1516_ = _args[14];
lean_object* v___y_1517_ = _args[15];
lean_object* v___y_1518_ = _args[16];
_start:
{
size_t v_sz_boxed_1519_; size_t v_i_boxed_1520_; lean_object* v_res_1521_; 
v_sz_boxed_1519_ = lean_unbox_usize(v_sz_1505_);
lean_dec(v_sz_1505_);
v_i_boxed_1520_ = lean_unbox_usize(v_i_1506_);
lean_dec(v_i_1506_);
v_res_1521_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1(v___x_1502_, v_c_1503_, v_as_1504_, v_sz_boxed_1519_, v_i_boxed_1520_, v_b_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_);
lean_dec(v___y_1517_);
lean_dec_ref(v___y_1516_);
lean_dec(v___y_1515_);
lean_dec_ref(v___y_1514_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
lean_dec(v___y_1509_);
lean_dec(v___y_1508_);
lean_dec_ref(v_as_1504_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0(lean_object* v___x_1522_, lean_object* v_c_1523_, lean_object* v_t_1524_, lean_object* v_init_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
lean_object* v_root_1537_; lean_object* v_tail_1538_; lean_object* v___x_1539_; 
v_root_1537_ = lean_ctor_get(v_t_1524_, 0);
v_tail_1538_ = lean_ctor_get(v_t_1524_, 1);
lean_inc_ref(v_c_1523_);
lean_inc_ref(v___x_1522_);
lean_inc_ref(v_init_1525_);
v___x_1539_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(v_init_1525_, v___x_1522_, v_c_1523_, v_root_1537_, v_init_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
lean_dec_ref(v_init_1525_);
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_object* v_a_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1576_; 
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1542_ = v___x_1539_;
v_isShared_1543_ = v_isSharedCheck_1576_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_a_1540_);
lean_dec(v___x_1539_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1576_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
if (lean_obj_tag(v_a_1540_) == 0)
{
lean_object* v_a_1544_; lean_object* v___x_1546_; 
lean_dec_ref(v_c_1523_);
lean_dec_ref(v___x_1522_);
v_a_1544_ = lean_ctor_get(v_a_1540_, 0);
lean_inc(v_a_1544_);
lean_dec_ref_known(v_a_1540_, 1);
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 0, v_a_1544_);
v___x_1546_ = v___x_1542_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1547_; 
v_reuseFailAlloc_1547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1547_, 0, v_a_1544_);
v___x_1546_ = v_reuseFailAlloc_1547_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
return v___x_1546_;
}
}
else
{
lean_object* v_a_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; size_t v_sz_1551_; size_t v___x_1552_; lean_object* v___x_1553_; 
lean_del_object(v___x_1542_);
v_a_1548_ = lean_ctor_get(v_a_1540_, 0);
lean_inc(v_a_1548_);
lean_dec_ref_known(v_a_1540_, 1);
v___x_1549_ = lean_box(0);
v___x_1550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1549_);
lean_ctor_set(v___x_1550_, 1, v_a_1548_);
v_sz_1551_ = lean_array_size(v_tail_1538_);
v___x_1552_ = ((size_t)0ULL);
v___x_1553_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1(v___x_1522_, v_c_1523_, v_tail_1538_, v_sz_1551_, v___x_1552_, v___x_1550_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
if (lean_obj_tag(v___x_1553_) == 0)
{
lean_object* v_a_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1567_; 
v_a_1554_ = lean_ctor_get(v___x_1553_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1556_ = v___x_1553_;
v_isShared_1557_ = v_isSharedCheck_1567_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_a_1554_);
lean_dec(v___x_1553_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1567_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v_fst_1558_; 
v_fst_1558_ = lean_ctor_get(v_a_1554_, 0);
if (lean_obj_tag(v_fst_1558_) == 0)
{
lean_object* v_snd_1559_; lean_object* v___x_1561_; 
v_snd_1559_ = lean_ctor_get(v_a_1554_, 1);
lean_inc(v_snd_1559_);
lean_dec(v_a_1554_);
if (v_isShared_1557_ == 0)
{
lean_ctor_set(v___x_1556_, 0, v_snd_1559_);
v___x_1561_ = v___x_1556_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_snd_1559_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
else
{
lean_object* v_val_1563_; lean_object* v___x_1565_; 
lean_inc_ref(v_fst_1558_);
lean_dec(v_a_1554_);
v_val_1563_ = lean_ctor_get(v_fst_1558_, 0);
lean_inc(v_val_1563_);
lean_dec_ref_known(v_fst_1558_, 1);
if (v_isShared_1557_ == 0)
{
lean_ctor_set(v___x_1556_, 0, v_val_1563_);
v___x_1565_ = v___x_1556_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_val_1563_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
else
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1575_; 
v_a_1568_ = lean_ctor_get(v___x_1553_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1553_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1570_ = v___x_1553_;
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1553_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1573_; 
if (v_isShared_1571_ == 0)
{
v___x_1573_ = v___x_1570_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_a_1568_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
}
}
}
else
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1584_; 
lean_dec_ref(v_c_1523_);
lean_dec_ref(v___x_1522_);
v_a_1577_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1579_ = v___x_1539_;
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1539_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1580_ == 0)
{
v___x_1582_ = v___x_1579_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1577_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0___boxed(lean_object* v___x_1585_, lean_object* v_c_1586_, lean_object* v_t_1587_, lean_object* v_init_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_){
_start:
{
lean_object* v_res_1600_; 
v_res_1600_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0(v___x_1585_, v_c_1586_, v_t_1587_, v_init_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec(v___y_1596_);
lean_dec_ref(v___y_1595_);
lean_dec(v___y_1594_);
lean_dec_ref(v___y_1593_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
lean_dec(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec_ref(v_t_1587_);
return v_res_1600_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0(void){
_start:
{
lean_object* v___x_1601_; 
v___x_1601_ = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return v___x_1601_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq(lean_object* v_c_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_){
_start:
{
lean_object* v_p_1614_; 
v_p_1614_ = lean_ctor_get(v_c_1602_, 0);
if (lean_obj_tag(v_p_1614_) == 1)
{
lean_object* v_k_1615_; lean_object* v_v_1616_; lean_object* v___x_1617_; 
lean_inc_ref(v_p_1614_);
v_k_1615_ = lean_ctor_get(v_p_1614_, 0);
v_v_1616_ = lean_ctor_get(v_p_1614_, 1);
v___x_1617_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1603_, v_a_1611_);
if (lean_obj_tag(v___x_1617_) == 0)
{
lean_object* v_a_1618_; lean_object* v___y_1620_; lean_object* v___x_1646_; uint8_t v___x_1647_; 
v_a_1618_ = lean_ctor_get(v___x_1617_, 0);
lean_inc(v_a_1618_);
lean_dec_ref_known(v___x_1617_, 1);
v___x_1646_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9);
v___x_1647_ = lean_int_dec_lt(v_k_1615_, v___x_1646_);
if (v___x_1647_ == 0)
{
lean_object* v_lowers_1648_; lean_object* v_size_1649_; lean_object* v___x_1650_; uint8_t v___x_1651_; 
v_lowers_1648_ = lean_ctor_get(v_a_1618_, 7);
lean_inc_ref(v_lowers_1648_);
lean_dec(v_a_1618_);
v_size_1649_ = lean_ctor_get(v_lowers_1648_, 2);
v___x_1650_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0);
v___x_1651_ = lean_nat_dec_lt(v_v_1616_, v_size_1649_);
if (v___x_1651_ == 0)
{
lean_object* v___x_1652_; 
lean_dec_ref(v_lowers_1648_);
v___x_1652_ = l_outOfBounds___redArg(v___x_1650_);
v___y_1620_ = v___x_1652_;
goto v___jp_1619_;
}
else
{
lean_object* v___x_1653_; 
v___x_1653_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1650_, v_lowers_1648_, v_v_1616_);
lean_dec_ref(v_lowers_1648_);
v___y_1620_ = v___x_1653_;
goto v___jp_1619_;
}
}
else
{
lean_object* v_uppers_1654_; lean_object* v_size_1655_; lean_object* v___x_1656_; uint8_t v___x_1657_; 
v_uppers_1654_ = lean_ctor_get(v_a_1618_, 8);
lean_inc_ref(v_uppers_1654_);
lean_dec(v_a_1618_);
v_size_1655_ = lean_ctor_get(v_uppers_1654_, 2);
v___x_1656_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0);
v___x_1657_ = lean_nat_dec_lt(v_v_1616_, v_size_1655_);
if (v___x_1657_ == 0)
{
lean_object* v___x_1658_; 
lean_dec_ref(v_uppers_1654_);
v___x_1658_ = l_outOfBounds___redArg(v___x_1656_);
v___y_1620_ = v___x_1658_;
goto v___jp_1619_;
}
else
{
lean_object* v___x_1659_; 
v___x_1659_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1656_, v_uppers_1654_, v_v_1616_);
lean_dec_ref(v_uppers_1654_);
v___y_1620_ = v___x_1659_;
goto v___jp_1619_;
}
}
v___jp_1619_:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1621_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__0));
v___x_1622_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0(v_p_1614_, v_c_1602_, v___y_1620_, v___x_1621_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_);
lean_dec_ref(v___y_1620_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1637_; 
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1637_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1637_ == 0)
{
v___x_1625_ = v___x_1622_;
v_isShared_1626_ = v_isSharedCheck_1637_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1622_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1637_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v_fst_1627_; 
v_fst_1627_ = lean_ctor_get(v_a_1623_, 0);
lean_inc(v_fst_1627_);
lean_dec(v_a_1623_);
if (lean_obj_tag(v_fst_1627_) == 0)
{
uint8_t v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1631_; 
v___x_1628_ = 0;
v___x_1629_ = lean_box(v___x_1628_);
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 0, v___x_1629_);
v___x_1631_ = v___x_1625_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v___x_1629_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
else
{
lean_object* v_val_1633_; lean_object* v___x_1635_; 
v_val_1633_ = lean_ctor_get(v_fst_1627_, 0);
lean_inc(v_val_1633_);
lean_dec_ref_known(v_fst_1627_, 1);
if (v_isShared_1626_ == 0)
{
lean_ctor_set(v___x_1625_, 0, v_val_1633_);
v___x_1635_ = v___x_1625_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1636_; 
v_reuseFailAlloc_1636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1636_, 0, v_val_1633_);
v___x_1635_ = v_reuseFailAlloc_1636_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
return v___x_1635_;
}
}
}
}
else
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1645_; 
v_a_1638_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1640_ = v___x_1622_;
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1622_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
if (v_isShared_1641_ == 0)
{
v___x_1643_ = v___x_1640_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1638_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
}
}
else
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1667_; 
lean_dec_ref_known(v_p_1614_, 3);
lean_dec_ref(v_c_1602_);
v_a_1660_ = lean_ctor_get(v___x_1617_, 0);
v_isSharedCheck_1667_ = !lean_is_exclusive(v___x_1617_);
if (v_isSharedCheck_1667_ == 0)
{
v___x_1662_ = v___x_1617_;
v_isShared_1663_ = v_isSharedCheck_1667_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1617_);
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
else
{
lean_object* v___x_1668_; 
v___x_1668_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_1602_, v_a_1603_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_);
return v___x_1668_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___boxed(lean_object* v_c_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_){
_start:
{
lean_object* v_res_1681_; 
v_res_1681_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq(v_c_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_);
lean_dec(v_a_1679_);
lean_dec_ref(v_a_1678_);
lean_dec(v_a_1677_);
lean_dec_ref(v_a_1676_);
lean_dec(v_a_1675_);
lean_dec_ref(v_a_1674_);
lean_dec(v_a_1673_);
lean_dec_ref(v_a_1672_);
lean_dec(v_a_1671_);
lean_dec(v_a_1670_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(lean_object* v___x_1682_, lean_object* v_as_1683_, size_t v_i_1684_, size_t v_stop_1685_, lean_object* v_b_1686_){
_start:
{
lean_object* v___y_1688_; uint8_t v___x_1692_; 
v___x_1692_ = lean_usize_dec_eq(v_i_1684_, v_stop_1685_);
if (v___x_1692_ == 0)
{
lean_object* v___x_1693_; lean_object* v_p_1694_; uint8_t v___x_1695_; uint8_t v___x_1696_; 
v___x_1693_ = lean_array_uget_borrowed(v_as_1683_, v_i_1684_);
v_p_1694_ = lean_ctor_get(v___x_1693_, 0);
v___x_1695_ = l_Int_Internal_Linear_instBEqPoly_beq(v_p_1694_, v___x_1682_);
v___x_1696_ = lean_bool_not(v___x_1695_);
if (v___x_1696_ == 0)
{
v___y_1688_ = v_b_1686_;
goto v___jp_1687_;
}
else
{
lean_object* v___x_1697_; 
lean_inc(v___x_1693_);
v___x_1697_ = l_Lean_PersistentArray_push___redArg(v_b_1686_, v___x_1693_);
v___y_1688_ = v___x_1697_;
goto v___jp_1687_;
}
}
else
{
return v_b_1686_;
}
v___jp_1687_:
{
size_t v___x_1689_; size_t v___x_1690_; 
v___x_1689_ = ((size_t)1ULL);
v___x_1690_ = lean_usize_add(v_i_1684_, v___x_1689_);
v_i_1684_ = v___x_1690_;
v_b_1686_ = v___y_1688_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1___boxed(lean_object* v___x_1698_, lean_object* v_as_1699_, lean_object* v_i_1700_, lean_object* v_stop_1701_, lean_object* v_b_1702_){
_start:
{
size_t v_i_boxed_1703_; size_t v_stop_boxed_1704_; lean_object* v_res_1705_; 
v_i_boxed_1703_ = lean_unbox_usize(v_i_1700_);
lean_dec(v_i_1700_);
v_stop_boxed_1704_ = lean_unbox_usize(v_stop_1701_);
lean_dec(v_stop_1701_);
v_res_1705_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1698_, v_as_1699_, v_i_boxed_1703_, v_stop_boxed_1704_, v_b_1702_);
lean_dec_ref(v_as_1699_);
lean_dec_ref(v___x_1698_);
return v_res_1705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(lean_object* v___x_1706_, lean_object* v_x_1707_, lean_object* v_x_1708_){
_start:
{
if (lean_obj_tag(v_x_1707_) == 0)
{
lean_object* v_cs_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; uint8_t v___x_1712_; 
v_cs_1709_ = lean_ctor_get(v_x_1707_, 0);
v___x_1710_ = lean_unsigned_to_nat(0u);
v___x_1711_ = lean_array_get_size(v_cs_1709_);
v___x_1712_ = lean_nat_dec_lt(v___x_1710_, v___x_1711_);
if (v___x_1712_ == 0)
{
return v_x_1708_;
}
else
{
uint8_t v___x_1713_; 
v___x_1713_ = lean_nat_dec_le(v___x_1711_, v___x_1711_);
if (v___x_1713_ == 0)
{
if (v___x_1712_ == 0)
{
return v_x_1708_;
}
else
{
size_t v___x_1714_; size_t v___x_1715_; lean_object* v___x_1716_; 
v___x_1714_ = ((size_t)0ULL);
v___x_1715_ = lean_usize_of_nat(v___x_1711_);
v___x_1716_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1706_, v_cs_1709_, v___x_1714_, v___x_1715_, v_x_1708_);
return v___x_1716_;
}
}
else
{
size_t v___x_1717_; size_t v___x_1718_; lean_object* v___x_1719_; 
v___x_1717_ = ((size_t)0ULL);
v___x_1718_ = lean_usize_of_nat(v___x_1711_);
v___x_1719_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1706_, v_cs_1709_, v___x_1717_, v___x_1718_, v_x_1708_);
return v___x_1719_;
}
}
}
else
{
lean_object* v_vs_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; uint8_t v___x_1723_; 
v_vs_1720_ = lean_ctor_get(v_x_1707_, 0);
v___x_1721_ = lean_unsigned_to_nat(0u);
v___x_1722_ = lean_array_get_size(v_vs_1720_);
v___x_1723_ = lean_nat_dec_lt(v___x_1721_, v___x_1722_);
if (v___x_1723_ == 0)
{
return v_x_1708_;
}
else
{
uint8_t v___x_1724_; 
v___x_1724_ = lean_nat_dec_le(v___x_1722_, v___x_1722_);
if (v___x_1724_ == 0)
{
if (v___x_1723_ == 0)
{
return v_x_1708_;
}
else
{
size_t v___x_1725_; size_t v___x_1726_; lean_object* v___x_1727_; 
v___x_1725_ = ((size_t)0ULL);
v___x_1726_ = lean_usize_of_nat(v___x_1722_);
v___x_1727_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1706_, v_vs_1720_, v___x_1725_, v___x_1726_, v_x_1708_);
return v___x_1727_;
}
}
else
{
size_t v___x_1728_; size_t v___x_1729_; lean_object* v___x_1730_; 
v___x_1728_ = ((size_t)0ULL);
v___x_1729_ = lean_usize_of_nat(v___x_1722_);
v___x_1730_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1706_, v_vs_1720_, v___x_1728_, v___x_1729_, v_x_1708_);
return v___x_1730_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(lean_object* v___x_1731_, lean_object* v_as_1732_, size_t v_i_1733_, size_t v_stop_1734_, lean_object* v_b_1735_){
_start:
{
uint8_t v___x_1736_; 
v___x_1736_ = lean_usize_dec_eq(v_i_1733_, v_stop_1734_);
if (v___x_1736_ == 0)
{
lean_object* v___x_1737_; lean_object* v___x_1738_; size_t v___x_1739_; size_t v___x_1740_; 
v___x_1737_ = lean_array_uget_borrowed(v_as_1732_, v_i_1733_);
v___x_1738_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(v___x_1731_, v___x_1737_, v_b_1735_);
v___x_1739_ = ((size_t)1ULL);
v___x_1740_ = lean_usize_add(v_i_1733_, v___x_1739_);
v_i_1733_ = v___x_1740_;
v_b_1735_ = v___x_1738_;
goto _start;
}
else
{
return v_b_1735_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v___x_1742_, lean_object* v_as_1743_, lean_object* v_i_1744_, lean_object* v_stop_1745_, lean_object* v_b_1746_){
_start:
{
size_t v_i_boxed_1747_; size_t v_stop_boxed_1748_; lean_object* v_res_1749_; 
v_i_boxed_1747_ = lean_unbox_usize(v_i_1744_);
lean_dec(v_i_1744_);
v_stop_boxed_1748_ = lean_unbox_usize(v_stop_1745_);
lean_dec(v_stop_1745_);
v_res_1749_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1742_, v_as_1743_, v_i_boxed_1747_, v_stop_boxed_1748_, v_b_1746_);
lean_dec_ref(v_as_1743_);
lean_dec_ref(v___x_1742_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2___boxed(lean_object* v___x_1750_, lean_object* v_x_1751_, lean_object* v_x_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(v___x_1750_, v_x_1751_, v_x_1752_);
lean_dec_ref(v_x_1751_);
lean_dec_ref(v___x_1750_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(lean_object* v___x_1754_, lean_object* v_x_1755_, size_t v_x_1756_, size_t v_x_1757_, lean_object* v_x_1758_){
_start:
{
if (lean_obj_tag(v_x_1755_) == 0)
{
lean_object* v_cs_1759_; lean_object* v___x_1760_; size_t v___x_1761_; lean_object* v_j_1762_; lean_object* v___x_1763_; size_t v___x_1764_; size_t v___x_1765_; size_t v___x_1766_; size_t v___x_1767_; size_t v___x_1768_; size_t v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; uint8_t v___x_1774_; 
v_cs_1759_ = lean_ctor_get(v_x_1755_, 0);
v___x_1760_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0);
v___x_1761_ = lean_usize_shift_right(v_x_1756_, v_x_1757_);
v_j_1762_ = lean_usize_to_nat(v___x_1761_);
v___x_1763_ = lean_array_get_borrowed(v___x_1760_, v_cs_1759_, v_j_1762_);
v___x_1764_ = ((size_t)1ULL);
v___x_1765_ = lean_usize_shift_left(v___x_1764_, v_x_1757_);
v___x_1766_ = lean_usize_sub(v___x_1765_, v___x_1764_);
v___x_1767_ = lean_usize_land(v_x_1756_, v___x_1766_);
v___x_1768_ = ((size_t)5ULL);
v___x_1769_ = lean_usize_sub(v_x_1757_, v___x_1768_);
v___x_1770_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(v___x_1754_, v___x_1763_, v___x_1767_, v___x_1769_, v_x_1758_);
v___x_1771_ = lean_unsigned_to_nat(1u);
v___x_1772_ = lean_nat_add(v_j_1762_, v___x_1771_);
lean_dec(v_j_1762_);
v___x_1773_ = lean_array_get_size(v_cs_1759_);
v___x_1774_ = lean_nat_dec_lt(v___x_1772_, v___x_1773_);
if (v___x_1774_ == 0)
{
lean_dec(v___x_1772_);
return v___x_1770_;
}
else
{
uint8_t v___x_1775_; 
v___x_1775_ = lean_nat_dec_le(v___x_1773_, v___x_1773_);
if (v___x_1775_ == 0)
{
if (v___x_1774_ == 0)
{
lean_dec(v___x_1772_);
return v___x_1770_;
}
else
{
size_t v___x_1776_; size_t v___x_1777_; lean_object* v___x_1778_; 
v___x_1776_ = lean_usize_of_nat(v___x_1772_);
lean_dec(v___x_1772_);
v___x_1777_ = lean_usize_of_nat(v___x_1773_);
v___x_1778_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1754_, v_cs_1759_, v___x_1776_, v___x_1777_, v___x_1770_);
return v___x_1778_;
}
}
else
{
size_t v___x_1779_; size_t v___x_1780_; lean_object* v___x_1781_; 
v___x_1779_ = lean_usize_of_nat(v___x_1772_);
lean_dec(v___x_1772_);
v___x_1780_ = lean_usize_of_nat(v___x_1773_);
v___x_1781_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1754_, v_cs_1759_, v___x_1779_, v___x_1780_, v___x_1770_);
return v___x_1781_;
}
}
}
else
{
lean_object* v_vs_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; uint8_t v___x_1785_; 
v_vs_1782_ = lean_ctor_get(v_x_1755_, 0);
v___x_1783_ = lean_usize_to_nat(v_x_1756_);
v___x_1784_ = lean_array_get_size(v_vs_1782_);
v___x_1785_ = lean_nat_dec_lt(v___x_1783_, v___x_1784_);
if (v___x_1785_ == 0)
{
lean_dec(v___x_1783_);
return v_x_1758_;
}
else
{
uint8_t v___x_1786_; 
v___x_1786_ = lean_nat_dec_le(v___x_1784_, v___x_1784_);
if (v___x_1786_ == 0)
{
if (v___x_1785_ == 0)
{
lean_dec(v___x_1783_);
return v_x_1758_;
}
else
{
size_t v___x_1787_; size_t v___x_1788_; lean_object* v___x_1789_; 
v___x_1787_ = lean_usize_of_nat(v___x_1783_);
lean_dec(v___x_1783_);
v___x_1788_ = lean_usize_of_nat(v___x_1784_);
v___x_1789_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1754_, v_vs_1782_, v___x_1787_, v___x_1788_, v_x_1758_);
return v___x_1789_;
}
}
else
{
size_t v___x_1790_; size_t v___x_1791_; lean_object* v___x_1792_; 
v___x_1790_ = lean_usize_of_nat(v___x_1783_);
lean_dec(v___x_1783_);
v___x_1791_ = lean_usize_of_nat(v___x_1784_);
v___x_1792_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1754_, v_vs_1782_, v___x_1790_, v___x_1791_, v_x_1758_);
return v___x_1792_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0___boxed(lean_object* v___x_1793_, lean_object* v_x_1794_, lean_object* v_x_1795_, lean_object* v_x_1796_, lean_object* v_x_1797_){
_start:
{
size_t v_x_21565__boxed_1798_; size_t v_x_21566__boxed_1799_; lean_object* v_res_1800_; 
v_x_21565__boxed_1798_ = lean_unbox_usize(v_x_1795_);
lean_dec(v_x_1795_);
v_x_21566__boxed_1799_ = lean_unbox_usize(v_x_1796_);
lean_dec(v_x_1796_);
v_res_1800_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(v___x_1793_, v_x_1794_, v_x_21565__boxed_1798_, v_x_21566__boxed_1799_, v_x_1797_);
lean_dec_ref(v_x_1794_);
lean_dec_ref(v___x_1793_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(lean_object* v___x_1801_, lean_object* v_t_1802_, lean_object* v_init_1803_, lean_object* v_start_1804_){
_start:
{
lean_object* v___x_1805_; uint8_t v___x_1806_; 
v___x_1805_ = lean_unsigned_to_nat(0u);
v___x_1806_ = lean_nat_dec_eq(v_start_1804_, v___x_1805_);
if (v___x_1806_ == 0)
{
lean_object* v_root_1807_; lean_object* v_tail_1808_; size_t v_shift_1809_; lean_object* v_tailOff_1810_; uint8_t v___x_1811_; 
v_root_1807_ = lean_ctor_get(v_t_1802_, 0);
v_tail_1808_ = lean_ctor_get(v_t_1802_, 1);
v_shift_1809_ = lean_ctor_get_usize(v_t_1802_, 4);
v_tailOff_1810_ = lean_ctor_get(v_t_1802_, 3);
v___x_1811_ = lean_nat_dec_le(v_tailOff_1810_, v_start_1804_);
if (v___x_1811_ == 0)
{
size_t v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; uint8_t v___x_1815_; 
v___x_1812_ = lean_usize_of_nat(v_start_1804_);
v___x_1813_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(v___x_1801_, v_root_1807_, v___x_1812_, v_shift_1809_, v_init_1803_);
v___x_1814_ = lean_array_get_size(v_tail_1808_);
v___x_1815_ = lean_nat_dec_lt(v___x_1805_, v___x_1814_);
if (v___x_1815_ == 0)
{
return v___x_1813_;
}
else
{
uint8_t v___x_1816_; 
v___x_1816_ = lean_nat_dec_le(v___x_1814_, v___x_1814_);
if (v___x_1816_ == 0)
{
if (v___x_1815_ == 0)
{
return v___x_1813_;
}
else
{
size_t v___x_1817_; size_t v___x_1818_; lean_object* v___x_1819_; 
v___x_1817_ = ((size_t)0ULL);
v___x_1818_ = lean_usize_of_nat(v___x_1814_);
v___x_1819_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1801_, v_tail_1808_, v___x_1817_, v___x_1818_, v___x_1813_);
return v___x_1819_;
}
}
else
{
size_t v___x_1820_; size_t v___x_1821_; lean_object* v___x_1822_; 
v___x_1820_ = ((size_t)0ULL);
v___x_1821_ = lean_usize_of_nat(v___x_1814_);
v___x_1822_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1801_, v_tail_1808_, v___x_1820_, v___x_1821_, v___x_1813_);
return v___x_1822_;
}
}
}
else
{
lean_object* v___x_1823_; lean_object* v___x_1824_; uint8_t v___x_1825_; 
v___x_1823_ = lean_nat_sub(v_start_1804_, v_tailOff_1810_);
v___x_1824_ = lean_array_get_size(v_tail_1808_);
v___x_1825_ = lean_nat_dec_lt(v___x_1823_, v___x_1824_);
if (v___x_1825_ == 0)
{
lean_dec(v___x_1823_);
return v_init_1803_;
}
else
{
uint8_t v___x_1826_; 
v___x_1826_ = lean_nat_dec_le(v___x_1824_, v___x_1824_);
if (v___x_1826_ == 0)
{
if (v___x_1825_ == 0)
{
lean_dec(v___x_1823_);
return v_init_1803_;
}
else
{
size_t v___x_1827_; size_t v___x_1828_; lean_object* v___x_1829_; 
v___x_1827_ = lean_usize_of_nat(v___x_1823_);
lean_dec(v___x_1823_);
v___x_1828_ = lean_usize_of_nat(v___x_1824_);
v___x_1829_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1801_, v_tail_1808_, v___x_1827_, v___x_1828_, v_init_1803_);
return v___x_1829_;
}
}
else
{
size_t v___x_1830_; size_t v___x_1831_; lean_object* v___x_1832_; 
v___x_1830_ = lean_usize_of_nat(v___x_1823_);
lean_dec(v___x_1823_);
v___x_1831_ = lean_usize_of_nat(v___x_1824_);
v___x_1832_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1801_, v_tail_1808_, v___x_1830_, v___x_1831_, v_init_1803_);
return v___x_1832_;
}
}
}
}
else
{
lean_object* v_root_1833_; lean_object* v_tail_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; uint8_t v___x_1837_; 
v_root_1833_ = lean_ctor_get(v_t_1802_, 0);
v_tail_1834_ = lean_ctor_get(v_t_1802_, 1);
v___x_1835_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(v___x_1801_, v_root_1833_, v_init_1803_);
v___x_1836_ = lean_array_get_size(v_tail_1834_);
v___x_1837_ = lean_nat_dec_lt(v___x_1805_, v___x_1836_);
if (v___x_1837_ == 0)
{
return v___x_1835_;
}
else
{
uint8_t v___x_1838_; 
v___x_1838_ = lean_nat_dec_le(v___x_1836_, v___x_1836_);
if (v___x_1838_ == 0)
{
if (v___x_1837_ == 0)
{
return v___x_1835_;
}
else
{
size_t v___x_1839_; size_t v___x_1840_; lean_object* v___x_1841_; 
v___x_1839_ = ((size_t)0ULL);
v___x_1840_ = lean_usize_of_nat(v___x_1836_);
v___x_1841_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1801_, v_tail_1834_, v___x_1839_, v___x_1840_, v___x_1835_);
return v___x_1841_;
}
}
else
{
size_t v___x_1842_; size_t v___x_1843_; lean_object* v___x_1844_; 
v___x_1842_ = ((size_t)0ULL);
v___x_1843_ = lean_usize_of_nat(v___x_1836_);
v___x_1844_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1801_, v_tail_1834_, v___x_1842_, v___x_1843_, v___x_1835_);
return v___x_1844_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0___boxed(lean_object* v___x_1845_, lean_object* v_t_1846_, lean_object* v_init_1847_, lean_object* v_start_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(v___x_1845_, v_t_1846_, v_init_1847_, v_start_1848_);
lean_dec(v_start_1848_);
lean_dec_ref(v_t_1846_);
lean_dec_ref(v___x_1845_);
return v_res_1849_;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1850_ = lean_unsigned_to_nat(32u);
v___x_1851_ = lean_mk_empty_array_with_capacity(v___x_1850_);
v___x_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1851_);
return v___x_1852_;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1(void){
_start:
{
size_t v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1853_ = ((size_t)5ULL);
v___x_1854_ = lean_unsigned_to_nat(0u);
v___x_1855_ = lean_unsigned_to_nat(32u);
v___x_1856_ = lean_mk_empty_array_with_capacity(v___x_1855_);
v___x_1857_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0);
v___x_1858_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1858_, 0, v___x_1857_);
lean_ctor_set(v___x_1858_, 1, v___x_1856_);
lean_ctor_set(v___x_1858_, 2, v___x_1854_);
lean_ctor_set(v___x_1858_, 3, v___x_1854_);
lean_ctor_set_usize(v___x_1858_, 4, v___x_1853_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(lean_object* v___x_1859_, lean_object* v_x_1860_, size_t v_x_1861_, size_t v_x_1862_){
_start:
{
if (lean_obj_tag(v_x_1860_) == 0)
{
lean_object* v_cs_1863_; size_t v_j_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; uint8_t v___x_1867_; 
v_cs_1863_ = lean_ctor_get(v_x_1860_, 0);
v_j_1864_ = lean_usize_shift_right(v_x_1861_, v_x_1862_);
v___x_1865_ = lean_usize_to_nat(v_j_1864_);
v___x_1866_ = lean_array_get_size(v_cs_1863_);
v___x_1867_ = lean_nat_dec_lt(v___x_1865_, v___x_1866_);
if (v___x_1867_ == 0)
{
lean_dec(v___x_1865_);
return v_x_1860_;
}
else
{
lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1885_; 
lean_inc_ref(v_cs_1863_);
v_isSharedCheck_1885_ = !lean_is_exclusive(v_x_1860_);
if (v_isSharedCheck_1885_ == 0)
{
lean_object* v_unused_1886_; 
v_unused_1886_ = lean_ctor_get(v_x_1860_, 0);
lean_dec(v_unused_1886_);
v___x_1869_ = v_x_1860_;
v_isShared_1870_ = v_isSharedCheck_1885_;
goto v_resetjp_1868_;
}
else
{
lean_dec(v_x_1860_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1885_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
size_t v___x_1871_; size_t v___x_1872_; size_t v___x_1873_; size_t v_i_1874_; size_t v___x_1875_; size_t v_shift_1876_; lean_object* v_v_1877_; lean_object* v___x_1878_; lean_object* v_xs_x27_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1883_; 
v___x_1871_ = ((size_t)1ULL);
v___x_1872_ = lean_usize_shift_left(v___x_1871_, v_x_1862_);
v___x_1873_ = lean_usize_sub(v___x_1872_, v___x_1871_);
v_i_1874_ = lean_usize_land(v_x_1861_, v___x_1873_);
v___x_1875_ = ((size_t)5ULL);
v_shift_1876_ = lean_usize_sub(v_x_1862_, v___x_1875_);
v_v_1877_ = lean_array_fget(v_cs_1863_, v___x_1865_);
v___x_1878_ = lean_box(0);
v_xs_x27_1879_ = lean_array_fset(v_cs_1863_, v___x_1865_, v___x_1878_);
v___x_1880_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(v___x_1859_, v_v_1877_, v_i_1874_, v_shift_1876_);
v___x_1881_ = lean_array_fset(v_xs_x27_1879_, v___x_1865_, v___x_1880_);
lean_dec(v___x_1865_);
if (v_isShared_1870_ == 0)
{
lean_ctor_set(v___x_1869_, 0, v___x_1881_);
v___x_1883_ = v___x_1869_;
goto v_reusejp_1882_;
}
else
{
lean_object* v_reuseFailAlloc_1884_; 
v_reuseFailAlloc_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1884_, 0, v___x_1881_);
v___x_1883_ = v_reuseFailAlloc_1884_;
goto v_reusejp_1882_;
}
v_reusejp_1882_:
{
return v___x_1883_;
}
}
}
}
else
{
lean_object* v_vs_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; uint8_t v___x_1890_; 
v_vs_1887_ = lean_ctor_get(v_x_1860_, 0);
v___x_1888_ = lean_usize_to_nat(v_x_1861_);
v___x_1889_ = lean_array_get_size(v_vs_1887_);
v___x_1890_ = lean_nat_dec_lt(v___x_1888_, v___x_1889_);
if (v___x_1890_ == 0)
{
lean_dec(v___x_1888_);
return v_x_1860_;
}
else
{
lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1904_; 
lean_inc_ref(v_vs_1887_);
v_isSharedCheck_1904_ = !lean_is_exclusive(v_x_1860_);
if (v_isSharedCheck_1904_ == 0)
{
lean_object* v_unused_1905_; 
v_unused_1905_ = lean_ctor_get(v_x_1860_, 0);
lean_dec(v_unused_1905_);
v___x_1892_ = v_x_1860_;
v_isShared_1893_ = v_isSharedCheck_1904_;
goto v_resetjp_1891_;
}
else
{
lean_dec(v_x_1860_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1904_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v_v_1894_; lean_object* v___x_1895_; lean_object* v_xs_x27_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1902_; 
v_v_1894_ = lean_array_fget(v_vs_1887_, v___x_1888_);
v___x_1895_ = lean_box(0);
v_xs_x27_1896_ = lean_array_fset(v_vs_1887_, v___x_1888_, v___x_1895_);
v___x_1897_ = lean_unsigned_to_nat(0u);
v___x_1898_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1);
v___x_1899_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(v___x_1859_, v_v_1894_, v___x_1898_, v___x_1897_);
lean_dec(v_v_1894_);
v___x_1900_ = lean_array_fset(v_xs_x27_1896_, v___x_1888_, v___x_1899_);
lean_dec(v___x_1888_);
if (v_isShared_1893_ == 0)
{
lean_ctor_set(v___x_1892_, 0, v___x_1900_);
v___x_1902_ = v___x_1892_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v___x_1900_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___boxed(lean_object* v___x_1906_, lean_object* v_x_1907_, lean_object* v_x_1908_, lean_object* v_x_1909_){
_start:
{
size_t v_x_21737__boxed_1910_; size_t v_x_21738__boxed_1911_; lean_object* v_res_1912_; 
v_x_21737__boxed_1910_ = lean_unbox_usize(v_x_1908_);
lean_dec(v_x_1908_);
v_x_21738__boxed_1911_ = lean_unbox_usize(v_x_1909_);
lean_dec(v_x_1909_);
v_res_1912_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(v___x_1906_, v_x_1907_, v_x_21737__boxed_1910_, v_x_21738__boxed_1911_);
lean_dec_ref(v___x_1906_);
return v_res_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1(lean_object* v___x_1913_, lean_object* v_t_1914_, lean_object* v_i_1915_){
_start:
{
lean_object* v_root_1916_; lean_object* v_tail_1917_; lean_object* v_size_1918_; size_t v_shift_1919_; lean_object* v_tailOff_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1948_; 
v_root_1916_ = lean_ctor_get(v_t_1914_, 0);
v_tail_1917_ = lean_ctor_get(v_t_1914_, 1);
v_size_1918_ = lean_ctor_get(v_t_1914_, 2);
v_shift_1919_ = lean_ctor_get_usize(v_t_1914_, 4);
v_tailOff_1920_ = lean_ctor_get(v_t_1914_, 3);
v_isSharedCheck_1948_ = !lean_is_exclusive(v_t_1914_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1922_ = v_t_1914_;
v_isShared_1923_ = v_isSharedCheck_1948_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_tailOff_1920_);
lean_inc(v_size_1918_);
lean_inc(v_tail_1917_);
lean_inc(v_root_1916_);
lean_dec(v_t_1914_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1948_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
uint8_t v___x_1924_; 
v___x_1924_ = lean_nat_dec_le(v_tailOff_1920_, v_i_1915_);
if (v___x_1924_ == 0)
{
size_t v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1928_; 
v___x_1925_ = lean_usize_of_nat(v_i_1915_);
v___x_1926_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(v___x_1913_, v_root_1916_, v___x_1925_, v_shift_1919_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 0, v___x_1926_);
v___x_1928_ = v___x_1922_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v___x_1926_);
lean_ctor_set(v_reuseFailAlloc_1929_, 1, v_tail_1917_);
lean_ctor_set(v_reuseFailAlloc_1929_, 2, v_size_1918_);
lean_ctor_set(v_reuseFailAlloc_1929_, 3, v_tailOff_1920_);
lean_ctor_set_usize(v_reuseFailAlloc_1929_, 4, v_shift_1919_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
else
{
lean_object* v___x_1930_; lean_object* v___x_1931_; uint8_t v___x_1932_; 
v___x_1930_ = lean_nat_sub(v_i_1915_, v_tailOff_1920_);
v___x_1931_ = lean_array_get_size(v_tail_1917_);
v___x_1932_ = lean_nat_dec_lt(v___x_1930_, v___x_1931_);
if (v___x_1932_ == 0)
{
lean_object* v___x_1934_; 
lean_dec(v___x_1930_);
if (v_isShared_1923_ == 0)
{
v___x_1934_ = v___x_1922_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_root_1916_);
lean_ctor_set(v_reuseFailAlloc_1935_, 1, v_tail_1917_);
lean_ctor_set(v_reuseFailAlloc_1935_, 2, v_size_1918_);
lean_ctor_set(v_reuseFailAlloc_1935_, 3, v_tailOff_1920_);
lean_ctor_set_usize(v_reuseFailAlloc_1935_, 4, v_shift_1919_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
else
{
lean_object* v_v_1936_; lean_object* v___x_1937_; lean_object* v_xs_x27_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1946_; 
v_v_1936_ = lean_array_fget(v_tail_1917_, v___x_1930_);
v___x_1937_ = lean_box(0);
v_xs_x27_1938_ = lean_array_fset(v_tail_1917_, v___x_1930_, v___x_1937_);
v___x_1939_ = lean_unsigned_to_nat(32u);
v___x_1940_ = lean_mk_empty_array_with_capacity(v___x_1939_);
lean_dec_ref(v___x_1940_);
v___x_1941_ = lean_unsigned_to_nat(0u);
v___x_1942_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1);
v___x_1943_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(v___x_1913_, v_v_1936_, v___x_1942_, v___x_1941_);
lean_dec(v_v_1936_);
v___x_1944_ = lean_array_fset(v_xs_x27_1938_, v___x_1930_, v___x_1943_);
lean_dec(v___x_1930_);
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 1, v___x_1944_);
v___x_1946_ = v___x_1922_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1947_; 
v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_1947_, 0, v_root_1916_);
lean_ctor_set(v_reuseFailAlloc_1947_, 1, v___x_1944_);
lean_ctor_set(v_reuseFailAlloc_1947_, 2, v_size_1918_);
lean_ctor_set(v_reuseFailAlloc_1947_, 3, v_tailOff_1920_);
lean_ctor_set_usize(v_reuseFailAlloc_1947_, 4, v_shift_1919_);
v___x_1946_ = v_reuseFailAlloc_1947_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
return v___x_1946_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1___boxed(lean_object* v___x_1949_, lean_object* v_t_1950_, lean_object* v_i_1951_){
_start:
{
lean_object* v_res_1952_; 
v_res_1952_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1(v___x_1949_, v_t_1950_, v_i_1951_);
lean_dec(v_i_1951_);
lean_dec_ref(v___x_1949_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0(lean_object* v_p_1953_, lean_object* v_x_1954_, lean_object* v_s_1955_){
_start:
{
lean_object* v_vars_1956_; lean_object* v_varMap_1957_; lean_object* v_vars_x27_1958_; lean_object* v_varMap_x27_1959_; lean_object* v_natToIntMap_1960_; lean_object* v_natDef_1961_; lean_object* v_dvds_1962_; lean_object* v_lowers_1963_; lean_object* v_uppers_1964_; lean_object* v_diseqs_1965_; lean_object* v_elimEqs_1966_; lean_object* v_elimStack_1967_; lean_object* v_occurs_1968_; lean_object* v_assignment_1969_; lean_object* v_nextCnstrId_1970_; uint8_t v_caseSplits_1971_; lean_object* v_conflict_x3f_1972_; lean_object* v_diseqSplits_1973_; lean_object* v_divMod_1974_; lean_object* v_toIntIds_1975_; lean_object* v_toIntInfos_1976_; lean_object* v_toIntTermMap_1977_; lean_object* v_toIntVarMap_1978_; uint8_t v_usedCommRing_1979_; lean_object* v_nonlinearOccs_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1988_; 
v_vars_1956_ = lean_ctor_get(v_s_1955_, 0);
v_varMap_1957_ = lean_ctor_get(v_s_1955_, 1);
v_vars_x27_1958_ = lean_ctor_get(v_s_1955_, 2);
v_varMap_x27_1959_ = lean_ctor_get(v_s_1955_, 3);
v_natToIntMap_1960_ = lean_ctor_get(v_s_1955_, 4);
v_natDef_1961_ = lean_ctor_get(v_s_1955_, 5);
v_dvds_1962_ = lean_ctor_get(v_s_1955_, 6);
v_lowers_1963_ = lean_ctor_get(v_s_1955_, 7);
v_uppers_1964_ = lean_ctor_get(v_s_1955_, 8);
v_diseqs_1965_ = lean_ctor_get(v_s_1955_, 9);
v_elimEqs_1966_ = lean_ctor_get(v_s_1955_, 10);
v_elimStack_1967_ = lean_ctor_get(v_s_1955_, 11);
v_occurs_1968_ = lean_ctor_get(v_s_1955_, 12);
v_assignment_1969_ = lean_ctor_get(v_s_1955_, 13);
v_nextCnstrId_1970_ = lean_ctor_get(v_s_1955_, 14);
v_caseSplits_1971_ = lean_ctor_get_uint8(v_s_1955_, sizeof(void*)*23);
v_conflict_x3f_1972_ = lean_ctor_get(v_s_1955_, 15);
v_diseqSplits_1973_ = lean_ctor_get(v_s_1955_, 16);
v_divMod_1974_ = lean_ctor_get(v_s_1955_, 17);
v_toIntIds_1975_ = lean_ctor_get(v_s_1955_, 18);
v_toIntInfos_1976_ = lean_ctor_get(v_s_1955_, 19);
v_toIntTermMap_1977_ = lean_ctor_get(v_s_1955_, 20);
v_toIntVarMap_1978_ = lean_ctor_get(v_s_1955_, 21);
v_usedCommRing_1979_ = lean_ctor_get_uint8(v_s_1955_, sizeof(void*)*23 + 1);
v_nonlinearOccs_1980_ = lean_ctor_get(v_s_1955_, 22);
v_isSharedCheck_1988_ = !lean_is_exclusive(v_s_1955_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1982_ = v_s_1955_;
v_isShared_1983_ = v_isSharedCheck_1988_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_nonlinearOccs_1980_);
lean_inc(v_toIntVarMap_1978_);
lean_inc(v_toIntTermMap_1977_);
lean_inc(v_toIntInfos_1976_);
lean_inc(v_toIntIds_1975_);
lean_inc(v_divMod_1974_);
lean_inc(v_diseqSplits_1973_);
lean_inc(v_conflict_x3f_1972_);
lean_inc(v_nextCnstrId_1970_);
lean_inc(v_assignment_1969_);
lean_inc(v_occurs_1968_);
lean_inc(v_elimStack_1967_);
lean_inc(v_elimEqs_1966_);
lean_inc(v_diseqs_1965_);
lean_inc(v_uppers_1964_);
lean_inc(v_lowers_1963_);
lean_inc(v_dvds_1962_);
lean_inc(v_natDef_1961_);
lean_inc(v_natToIntMap_1960_);
lean_inc(v_varMap_x27_1959_);
lean_inc(v_vars_x27_1958_);
lean_inc(v_varMap_1957_);
lean_inc(v_vars_1956_);
lean_dec(v_s_1955_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1988_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1984_; lean_object* v___x_1986_; 
v___x_1984_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1(v_p_1953_, v_diseqs_1965_, v_x_1954_);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 9, v___x_1984_);
v___x_1986_ = v___x_1982_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_vars_1956_);
lean_ctor_set(v_reuseFailAlloc_1987_, 1, v_varMap_1957_);
lean_ctor_set(v_reuseFailAlloc_1987_, 2, v_vars_x27_1958_);
lean_ctor_set(v_reuseFailAlloc_1987_, 3, v_varMap_x27_1959_);
lean_ctor_set(v_reuseFailAlloc_1987_, 4, v_natToIntMap_1960_);
lean_ctor_set(v_reuseFailAlloc_1987_, 5, v_natDef_1961_);
lean_ctor_set(v_reuseFailAlloc_1987_, 6, v_dvds_1962_);
lean_ctor_set(v_reuseFailAlloc_1987_, 7, v_lowers_1963_);
lean_ctor_set(v_reuseFailAlloc_1987_, 8, v_uppers_1964_);
lean_ctor_set(v_reuseFailAlloc_1987_, 9, v___x_1984_);
lean_ctor_set(v_reuseFailAlloc_1987_, 10, v_elimEqs_1966_);
lean_ctor_set(v_reuseFailAlloc_1987_, 11, v_elimStack_1967_);
lean_ctor_set(v_reuseFailAlloc_1987_, 12, v_occurs_1968_);
lean_ctor_set(v_reuseFailAlloc_1987_, 13, v_assignment_1969_);
lean_ctor_set(v_reuseFailAlloc_1987_, 14, v_nextCnstrId_1970_);
lean_ctor_set(v_reuseFailAlloc_1987_, 15, v_conflict_x3f_1972_);
lean_ctor_set(v_reuseFailAlloc_1987_, 16, v_diseqSplits_1973_);
lean_ctor_set(v_reuseFailAlloc_1987_, 17, v_divMod_1974_);
lean_ctor_set(v_reuseFailAlloc_1987_, 18, v_toIntIds_1975_);
lean_ctor_set(v_reuseFailAlloc_1987_, 19, v_toIntInfos_1976_);
lean_ctor_set(v_reuseFailAlloc_1987_, 20, v_toIntTermMap_1977_);
lean_ctor_set(v_reuseFailAlloc_1987_, 21, v_toIntVarMap_1978_);
lean_ctor_set(v_reuseFailAlloc_1987_, 22, v_nonlinearOccs_1980_);
lean_ctor_set_uint8(v_reuseFailAlloc_1987_, sizeof(void*)*23, v_caseSplits_1971_);
lean_ctor_set_uint8(v_reuseFailAlloc_1987_, sizeof(void*)*23 + 1, v_usedCommRing_1979_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed(lean_object* v_p_1989_, lean_object* v_x_1990_, lean_object* v_s_1991_){
_start:
{
lean_object* v_res_1992_; 
v_res_1992_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0(v_p_1989_, v_x_1990_, v_s_1991_);
lean_dec(v_x_1990_);
lean_dec_ref(v_p_1989_);
return v_res_1992_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1999_ = lean_unsigned_to_nat(1u);
v___x_2000_ = lean_nat_to_int(v___x_1999_);
return v___x_2000_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(lean_object* v_c_2001_, lean_object* v_x_2002_, lean_object* v_as_2003_, size_t v_sz_2004_, size_t v_i_2005_, lean_object* v_b_2006_, lean_object* v___y_2007_){
_start:
{
uint8_t v___x_2009_; 
v___x_2009_ = lean_usize_dec_lt(v_i_2005_, v_sz_2004_);
if (v___x_2009_ == 0)
{
lean_object* v___x_2010_; 
lean_dec(v_x_2002_);
lean_dec_ref(v_c_2001_);
v___x_2010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2010_, 0, v_b_2006_);
return v___x_2010_;
}
else
{
lean_object* v_snd_2011_; lean_object* v___x_2013_; uint8_t v_isShared_2014_; uint8_t v_isSharedCheck_2057_; 
v_snd_2011_ = lean_ctor_get(v_b_2006_, 1);
v_isSharedCheck_2057_ = !lean_is_exclusive(v_b_2006_);
if (v_isSharedCheck_2057_ == 0)
{
lean_object* v_unused_2058_; 
v_unused_2058_ = lean_ctor_get(v_b_2006_, 0);
lean_dec(v_unused_2058_);
v___x_2013_ = v_b_2006_;
v_isShared_2014_ = v_isSharedCheck_2057_;
goto v_resetjp_2012_;
}
else
{
lean_inc(v_snd_2011_);
lean_dec(v_b_2006_);
v___x_2013_ = lean_box(0);
v_isShared_2014_ = v_isSharedCheck_2057_;
goto v_resetjp_2012_;
}
v_resetjp_2012_:
{
lean_object* v_p_2015_; lean_object* v_a_2016_; lean_object* v_p_2017_; lean_object* v___x_2018_; lean_object* v___f_2019_; uint8_t v___y_2021_; uint8_t v___x_2055_; 
v_p_2015_ = lean_ctor_get(v_c_2001_, 0);
v_a_2016_ = lean_array_uget_borrowed(v_as_2003_, v_i_2005_);
v_p_2017_ = lean_ctor_get(v_a_2016_, 0);
v___x_2018_ = lean_box(0);
lean_inc(v_x_2002_);
lean_inc_ref(v_p_2017_);
v___f_2019_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2019_, 0, v_p_2017_);
lean_closure_set(v___f_2019_, 1, v_x_2002_);
v___x_2055_ = l_Int_Internal_Linear_instBEqPoly_beq(v_p_2015_, v_p_2017_);
if (v___x_2055_ == 0)
{
uint8_t v___x_2056_; 
v___x_2056_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_2015_, v_p_2017_);
v___y_2021_ = v___x_2056_;
goto v___jp_2020_;
}
else
{
v___y_2021_ = v___x_2055_;
goto v___jp_2020_;
}
v___jp_2020_:
{
if (v___y_2021_ == 0)
{
lean_object* v___x_2022_; size_t v___x_2023_; size_t v___x_2024_; 
lean_dec_ref(v___f_2019_);
lean_del_object(v___x_2013_);
lean_dec(v_snd_2011_);
v___x_2022_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__1));
v___x_2023_ = ((size_t)1ULL);
v___x_2024_ = lean_usize_add(v_i_2005_, v___x_2023_);
v_i_2005_ = v___x_2024_;
v_b_2006_ = v___x_2022_;
goto _start;
}
else
{
lean_object* v___x_2026_; lean_object* v___x_2027_; 
lean_dec(v_x_2002_);
v___x_2026_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2027_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2026_, v___f_2019_, v___y_2007_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2045_; 
v_isSharedCheck_2045_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2045_ == 0)
{
lean_object* v_unused_2046_; 
v_unused_2046_ = lean_ctor_get(v___x_2027_, 0);
lean_dec(v_unused_2046_);
v___x_2029_ = v___x_2027_;
v_isShared_2030_ = v_isSharedCheck_2045_;
goto v_resetjp_2028_;
}
else
{
lean_dec(v___x_2027_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2045_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2038_; 
v___x_2031_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
lean_inc_ref(v_p_2015_);
v___x_2032_ = l_Int_Internal_Linear_Poly_addConst(v_p_2015_, v___x_2031_);
lean_inc(v_a_2016_);
v___x_2033_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_2033_, 0, v_c_2001_);
lean_ctor_set(v___x_2033_, 1, v_a_2016_);
v___x_2034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2032_);
lean_ctor_set(v___x_2034_, 1, v___x_2033_);
v___x_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2034_);
v___x_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2035_);
if (v_isShared_2014_ == 0)
{
lean_ctor_set(v___x_2013_, 1, v___x_2018_);
lean_ctor_set(v___x_2013_, 0, v___x_2036_);
v___x_2038_ = v___x_2013_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v___x_2036_);
lean_ctor_set(v_reuseFailAlloc_2044_, 1, v___x_2018_);
v___x_2038_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2042_; 
v___x_2039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2038_);
v___x_2040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2039_);
lean_ctor_set(v___x_2040_, 1, v_snd_2011_);
if (v_isShared_2030_ == 0)
{
lean_ctor_set(v___x_2029_, 0, v___x_2040_);
v___x_2042_ = v___x_2029_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2040_);
v___x_2042_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
return v___x_2042_;
}
}
}
}
else
{
lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2054_; 
lean_del_object(v___x_2013_);
lean_dec(v_snd_2011_);
lean_dec_ref(v_c_2001_);
v_a_2047_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2049_ = v___x_2027_;
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_dec(v___x_2027_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2052_; 
if (v_isShared_2050_ == 0)
{
v___x_2052_ = v___x_2049_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_a_2047_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___boxed(lean_object* v_c_2059_, lean_object* v_x_2060_, lean_object* v_as_2061_, lean_object* v_sz_2062_, lean_object* v_i_2063_, lean_object* v_b_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
size_t v_sz_boxed_2067_; size_t v_i_boxed_2068_; lean_object* v_res_2069_; 
v_sz_boxed_2067_ = lean_unbox_usize(v_sz_2062_);
lean_dec(v_sz_2062_);
v_i_boxed_2068_ = lean_unbox_usize(v_i_2063_);
lean_dec(v_i_2063_);
v_res_2069_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(v_c_2059_, v_x_2060_, v_as_2061_, v_sz_boxed_2067_, v_i_boxed_2068_, v_b_2064_, v___y_2065_);
lean_dec(v___y_2065_);
lean_dec_ref(v_as_2061_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7(lean_object* v_c_2076_, lean_object* v_x_2077_, lean_object* v_as_2078_, size_t v_sz_2079_, size_t v_i_2080_, lean_object* v_b_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_){
_start:
{
uint8_t v___x_2093_; 
v___x_2093_ = lean_usize_dec_lt(v_i_2080_, v_sz_2079_);
if (v___x_2093_ == 0)
{
lean_object* v___x_2094_; 
lean_dec(v_x_2077_);
lean_dec_ref(v_c_2076_);
v___x_2094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2094_, 0, v_b_2081_);
return v___x_2094_;
}
else
{
lean_object* v_snd_2095_; lean_object* v___x_2097_; uint8_t v_isShared_2098_; uint8_t v_isSharedCheck_2141_; 
v_snd_2095_ = lean_ctor_get(v_b_2081_, 1);
v_isSharedCheck_2141_ = !lean_is_exclusive(v_b_2081_);
if (v_isSharedCheck_2141_ == 0)
{
lean_object* v_unused_2142_; 
v_unused_2142_ = lean_ctor_get(v_b_2081_, 0);
lean_dec(v_unused_2142_);
v___x_2097_ = v_b_2081_;
v_isShared_2098_ = v_isSharedCheck_2141_;
goto v_resetjp_2096_;
}
else
{
lean_inc(v_snd_2095_);
lean_dec(v_b_2081_);
v___x_2097_ = lean_box(0);
v_isShared_2098_ = v_isSharedCheck_2141_;
goto v_resetjp_2096_;
}
v_resetjp_2096_:
{
lean_object* v_p_2099_; lean_object* v_a_2100_; lean_object* v_p_2101_; lean_object* v___x_2102_; lean_object* v___f_2103_; uint8_t v___y_2105_; uint8_t v___x_2139_; 
v_p_2099_ = lean_ctor_get(v_c_2076_, 0);
v_a_2100_ = lean_array_uget_borrowed(v_as_2078_, v_i_2080_);
v_p_2101_ = lean_ctor_get(v_a_2100_, 0);
v___x_2102_ = lean_box(0);
lean_inc(v_x_2077_);
lean_inc_ref(v_p_2101_);
v___f_2103_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2103_, 0, v_p_2101_);
lean_closure_set(v___f_2103_, 1, v_x_2077_);
v___x_2139_ = l_Int_Internal_Linear_instBEqPoly_beq(v_p_2099_, v_p_2101_);
if (v___x_2139_ == 0)
{
uint8_t v___x_2140_; 
v___x_2140_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_2099_, v_p_2101_);
v___y_2105_ = v___x_2140_;
goto v___jp_2104_;
}
else
{
v___y_2105_ = v___x_2139_;
goto v___jp_2104_;
}
v___jp_2104_:
{
if (v___y_2105_ == 0)
{
lean_object* v___x_2106_; size_t v___x_2107_; size_t v___x_2108_; lean_object* v___x_2109_; 
lean_dec_ref(v___f_2103_);
lean_del_object(v___x_2097_);
lean_dec(v_snd_2095_);
v___x_2106_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___closed__1));
v___x_2107_ = ((size_t)1ULL);
v___x_2108_ = lean_usize_add(v_i_2080_, v___x_2107_);
v___x_2109_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(v_c_2076_, v_x_2077_, v_as_2078_, v_sz_2079_, v___x_2108_, v___x_2106_, v___y_2082_);
return v___x_2109_;
}
else
{
lean_object* v___x_2110_; lean_object* v___x_2111_; 
lean_dec(v_x_2077_);
v___x_2110_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2111_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2110_, v___f_2103_, v___y_2082_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2129_; 
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2129_ == 0)
{
lean_object* v_unused_2130_; 
v_unused_2130_ = lean_ctor_get(v___x_2111_, 0);
lean_dec(v_unused_2130_);
v___x_2113_ = v___x_2111_;
v_isShared_2114_ = v_isSharedCheck_2129_;
goto v_resetjp_2112_;
}
else
{
lean_dec(v___x_2111_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2129_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2122_; 
v___x_2115_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
lean_inc_ref(v_p_2099_);
v___x_2116_ = l_Int_Internal_Linear_Poly_addConst(v_p_2099_, v___x_2115_);
lean_inc(v_a_2100_);
v___x_2117_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_2117_, 0, v_c_2076_);
lean_ctor_set(v___x_2117_, 1, v_a_2100_);
v___x_2118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2116_);
lean_ctor_set(v___x_2118_, 1, v___x_2117_);
v___x_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2118_);
v___x_2120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2119_);
if (v_isShared_2098_ == 0)
{
lean_ctor_set(v___x_2097_, 1, v___x_2102_);
lean_ctor_set(v___x_2097_, 0, v___x_2120_);
v___x_2122_ = v___x_2097_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v___x_2120_);
lean_ctor_set(v_reuseFailAlloc_2128_, 1, v___x_2102_);
v___x_2122_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2126_; 
v___x_2123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2122_);
v___x_2124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2123_);
lean_ctor_set(v___x_2124_, 1, v_snd_2095_);
if (v_isShared_2114_ == 0)
{
lean_ctor_set(v___x_2113_, 0, v___x_2124_);
v___x_2126_ = v___x_2113_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v___x_2124_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
}
else
{
lean_object* v_a_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2138_; 
lean_del_object(v___x_2097_);
lean_dec(v_snd_2095_);
lean_dec_ref(v_c_2076_);
v_a_2131_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2133_ = v___x_2111_;
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_a_2131_);
lean_dec(v___x_2111_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2136_; 
if (v_isShared_2134_ == 0)
{
v___x_2136_ = v___x_2133_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_a_2131_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
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
lean_object* v_c_2143_ = _args[0];
lean_object* v_x_2144_ = _args[1];
lean_object* v_as_2145_ = _args[2];
lean_object* v_sz_2146_ = _args[3];
lean_object* v_i_2147_ = _args[4];
lean_object* v_b_2148_ = _args[5];
lean_object* v___y_2149_ = _args[6];
lean_object* v___y_2150_ = _args[7];
lean_object* v___y_2151_ = _args[8];
lean_object* v___y_2152_ = _args[9];
lean_object* v___y_2153_ = _args[10];
lean_object* v___y_2154_ = _args[11];
lean_object* v___y_2155_ = _args[12];
lean_object* v___y_2156_ = _args[13];
lean_object* v___y_2157_ = _args[14];
lean_object* v___y_2158_ = _args[15];
lean_object* v___y_2159_ = _args[16];
_start:
{
size_t v_sz_boxed_2160_; size_t v_i_boxed_2161_; lean_object* v_res_2162_; 
v_sz_boxed_2160_ = lean_unbox_usize(v_sz_2146_);
lean_dec(v_sz_2146_);
v_i_boxed_2161_ = lean_unbox_usize(v_i_2147_);
lean_dec(v_i_2147_);
v_res_2162_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7(v_c_2143_, v_x_2144_, v_as_2145_, v_sz_boxed_2160_, v_i_boxed_2161_, v_b_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
lean_dec(v___y_2150_);
lean_dec(v___y_2149_);
lean_dec_ref(v_as_2145_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(lean_object* v_c_2169_, lean_object* v_x_2170_, lean_object* v_as_2171_, size_t v_sz_2172_, size_t v_i_2173_, lean_object* v_b_2174_, lean_object* v___y_2175_){
_start:
{
uint8_t v___x_2177_; 
v___x_2177_ = lean_usize_dec_lt(v_i_2173_, v_sz_2172_);
if (v___x_2177_ == 0)
{
lean_object* v___x_2178_; 
lean_dec(v_x_2170_);
lean_dec_ref(v_c_2169_);
v___x_2178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2178_, 0, v_b_2174_);
return v___x_2178_;
}
else
{
lean_object* v_snd_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2226_; 
v_snd_2179_ = lean_ctor_get(v_b_2174_, 1);
v_isSharedCheck_2226_ = !lean_is_exclusive(v_b_2174_);
if (v_isSharedCheck_2226_ == 0)
{
lean_object* v_unused_2227_; 
v_unused_2227_ = lean_ctor_get(v_b_2174_, 0);
lean_dec(v_unused_2227_);
v___x_2181_ = v_b_2174_;
v_isShared_2182_ = v_isSharedCheck_2226_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_snd_2179_);
lean_dec(v_b_2174_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2226_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v_p_2183_; lean_object* v_a_2184_; lean_object* v_p_2185_; lean_object* v___x_2186_; lean_object* v___f_2187_; uint8_t v___y_2189_; uint8_t v___x_2224_; 
v_p_2183_ = lean_ctor_get(v_c_2169_, 0);
v_a_2184_ = lean_array_uget_borrowed(v_as_2171_, v_i_2173_);
v_p_2185_ = lean_ctor_get(v_a_2184_, 0);
v___x_2186_ = lean_box(0);
lean_inc(v_x_2170_);
lean_inc_ref(v_p_2185_);
v___f_2187_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2187_, 0, v_p_2185_);
lean_closure_set(v___f_2187_, 1, v_x_2170_);
v___x_2224_ = l_Int_Internal_Linear_instBEqPoly_beq(v_p_2183_, v_p_2185_);
if (v___x_2224_ == 0)
{
uint8_t v___x_2225_; 
v___x_2225_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_2183_, v_p_2185_);
v___y_2189_ = v___x_2225_;
goto v___jp_2188_;
}
else
{
v___y_2189_ = v___x_2224_;
goto v___jp_2188_;
}
v___jp_2188_:
{
if (v___y_2189_ == 0)
{
lean_object* v___x_2190_; size_t v___x_2191_; size_t v___x_2192_; 
lean_dec_ref(v___f_2187_);
lean_del_object(v___x_2181_);
lean_dec(v_snd_2179_);
v___x_2190_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg___closed__1));
v___x_2191_ = ((size_t)1ULL);
v___x_2192_ = lean_usize_add(v_i_2173_, v___x_2191_);
v_i_2173_ = v___x_2192_;
v_b_2174_ = v___x_2190_;
goto _start;
}
else
{
lean_object* v___x_2194_; lean_object* v___x_2195_; 
lean_dec(v_x_2170_);
v___x_2194_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2195_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2194_, v___f_2187_, v___y_2175_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v___x_2197_; uint8_t v_isShared_2198_; uint8_t v_isSharedCheck_2214_; 
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2214_ == 0)
{
lean_object* v_unused_2215_; 
v_unused_2215_ = lean_ctor_get(v___x_2195_, 0);
lean_dec(v_unused_2215_);
v___x_2197_ = v___x_2195_;
v_isShared_2198_ = v_isSharedCheck_2214_;
goto v_resetjp_2196_;
}
else
{
lean_dec(v___x_2195_);
v___x_2197_ = lean_box(0);
v_isShared_2198_ = v_isSharedCheck_2214_;
goto v_resetjp_2196_;
}
v_resetjp_2196_:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2206_; 
v___x_2199_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
lean_inc_ref(v_p_2183_);
v___x_2200_ = l_Int_Internal_Linear_Poly_addConst(v_p_2183_, v___x_2199_);
lean_inc(v_a_2184_);
v___x_2201_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_2201_, 0, v_c_2169_);
lean_ctor_set(v___x_2201_, 1, v_a_2184_);
v___x_2202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2200_);
lean_ctor_set(v___x_2202_, 1, v___x_2201_);
v___x_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2202_);
v___x_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2203_);
if (v_isShared_2182_ == 0)
{
lean_ctor_set(v___x_2181_, 1, v___x_2186_);
lean_ctor_set(v___x_2181_, 0, v___x_2204_);
v___x_2206_ = v___x_2181_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v___x_2204_);
lean_ctor_set(v_reuseFailAlloc_2213_, 1, v___x_2186_);
v___x_2206_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2211_; 
v___x_2207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2206_);
v___x_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
v___x_2209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2208_);
lean_ctor_set(v___x_2209_, 1, v_snd_2179_);
if (v_isShared_2198_ == 0)
{
lean_ctor_set(v___x_2197_, 0, v___x_2209_);
v___x_2211_ = v___x_2197_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v___x_2209_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
}
else
{
lean_object* v_a_2216_; lean_object* v___x_2218_; uint8_t v_isShared_2219_; uint8_t v_isSharedCheck_2223_; 
lean_del_object(v___x_2181_);
lean_dec(v_snd_2179_);
lean_dec_ref(v_c_2169_);
v_a_2216_ = lean_ctor_get(v___x_2195_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2218_ = v___x_2195_;
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
else
{
lean_inc(v_a_2216_);
lean_dec(v___x_2195_);
v___x_2218_ = lean_box(0);
v_isShared_2219_ = v_isSharedCheck_2223_;
goto v_resetjp_2217_;
}
v_resetjp_2217_:
{
lean_object* v___x_2221_; 
if (v_isShared_2219_ == 0)
{
v___x_2221_ = v___x_2218_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_a_2216_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg___boxed(lean_object* v_c_2228_, lean_object* v_x_2229_, lean_object* v_as_2230_, lean_object* v_sz_2231_, lean_object* v_i_2232_, lean_object* v_b_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
size_t v_sz_boxed_2236_; size_t v_i_boxed_2237_; lean_object* v_res_2238_; 
v_sz_boxed_2236_ = lean_unbox_usize(v_sz_2231_);
lean_dec(v_sz_2231_);
v_i_boxed_2237_ = lean_unbox_usize(v_i_2232_);
lean_dec(v_i_2232_);
v_res_2238_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(v_c_2228_, v_x_2229_, v_as_2230_, v_sz_boxed_2236_, v_i_boxed_2237_, v_b_2233_, v___y_2234_);
lean_dec(v___y_2234_);
lean_dec_ref(v_as_2230_);
return v_res_2238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9(lean_object* v_c_2242_, lean_object* v_x_2243_, lean_object* v_as_2244_, size_t v_sz_2245_, size_t v_i_2246_, lean_object* v_b_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_){
_start:
{
uint8_t v___x_2259_; 
v___x_2259_ = lean_usize_dec_lt(v_i_2246_, v_sz_2245_);
if (v___x_2259_ == 0)
{
lean_object* v___x_2260_; 
lean_dec(v_x_2243_);
lean_dec_ref(v_c_2242_);
v___x_2260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2260_, 0, v_b_2247_);
return v___x_2260_;
}
else
{
lean_object* v_snd_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2308_; 
v_snd_2261_ = lean_ctor_get(v_b_2247_, 1);
v_isSharedCheck_2308_ = !lean_is_exclusive(v_b_2247_);
if (v_isSharedCheck_2308_ == 0)
{
lean_object* v_unused_2309_; 
v_unused_2309_ = lean_ctor_get(v_b_2247_, 0);
lean_dec(v_unused_2309_);
v___x_2263_ = v_b_2247_;
v_isShared_2264_ = v_isSharedCheck_2308_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_snd_2261_);
lean_dec(v_b_2247_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2308_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v_p_2265_; lean_object* v_a_2266_; lean_object* v_p_2267_; lean_object* v___x_2268_; lean_object* v___f_2269_; uint8_t v___y_2271_; uint8_t v___x_2306_; 
v_p_2265_ = lean_ctor_get(v_c_2242_, 0);
v_a_2266_ = lean_array_uget_borrowed(v_as_2244_, v_i_2246_);
v_p_2267_ = lean_ctor_get(v_a_2266_, 0);
v___x_2268_ = lean_box(0);
lean_inc(v_x_2243_);
lean_inc_ref(v_p_2267_);
v___f_2269_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2269_, 0, v_p_2267_);
lean_closure_set(v___f_2269_, 1, v_x_2243_);
v___x_2306_ = l_Int_Internal_Linear_instBEqPoly_beq(v_p_2265_, v_p_2267_);
if (v___x_2306_ == 0)
{
uint8_t v___x_2307_; 
v___x_2307_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_2265_, v_p_2267_);
v___y_2271_ = v___x_2307_;
goto v___jp_2270_;
}
else
{
v___y_2271_ = v___x_2306_;
goto v___jp_2270_;
}
v___jp_2270_:
{
if (v___y_2271_ == 0)
{
lean_object* v___x_2272_; size_t v___x_2273_; size_t v___x_2274_; lean_object* v___x_2275_; 
lean_dec_ref(v___f_2269_);
lean_del_object(v___x_2263_);
lean_dec(v_snd_2261_);
v___x_2272_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9___closed__0));
v___x_2273_ = ((size_t)1ULL);
v___x_2274_ = lean_usize_add(v_i_2246_, v___x_2273_);
v___x_2275_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(v_c_2242_, v_x_2243_, v_as_2244_, v_sz_2245_, v___x_2274_, v___x_2272_, v___y_2248_);
return v___x_2275_;
}
else
{
lean_object* v___x_2276_; lean_object* v___x_2277_; 
lean_dec(v_x_2243_);
v___x_2276_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2277_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2276_, v___f_2269_, v___y_2248_);
if (lean_obj_tag(v___x_2277_) == 0)
{
lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2296_; 
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2277_);
if (v_isSharedCheck_2296_ == 0)
{
lean_object* v_unused_2297_; 
v_unused_2297_ = lean_ctor_get(v___x_2277_, 0);
lean_dec(v_unused_2297_);
v___x_2279_ = v___x_2277_;
v_isShared_2280_ = v_isSharedCheck_2296_;
goto v_resetjp_2278_;
}
else
{
lean_dec(v___x_2277_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2296_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2288_; 
v___x_2281_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
lean_inc_ref(v_p_2265_);
v___x_2282_ = l_Int_Internal_Linear_Poly_addConst(v_p_2265_, v___x_2281_);
lean_inc(v_a_2266_);
v___x_2283_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_2283_, 0, v_c_2242_);
lean_ctor_set(v___x_2283_, 1, v_a_2266_);
v___x_2284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2282_);
lean_ctor_set(v___x_2284_, 1, v___x_2283_);
v___x_2285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2284_);
v___x_2286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2285_);
if (v_isShared_2264_ == 0)
{
lean_ctor_set(v___x_2263_, 1, v___x_2268_);
lean_ctor_set(v___x_2263_, 0, v___x_2286_);
v___x_2288_ = v___x_2263_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v___x_2286_);
lean_ctor_set(v_reuseFailAlloc_2295_, 1, v___x_2268_);
v___x_2288_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2293_; 
v___x_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2288_);
v___x_2290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2289_);
v___x_2291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2290_);
lean_ctor_set(v___x_2291_, 1, v_snd_2261_);
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 0, v___x_2291_);
v___x_2293_ = v___x_2279_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v___x_2291_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
return v___x_2293_;
}
}
}
}
else
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2305_; 
lean_del_object(v___x_2263_);
lean_dec(v_snd_2261_);
lean_dec_ref(v_c_2242_);
v_a_2298_ = lean_ctor_get(v___x_2277_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2277_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2300_ = v___x_2277_;
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2277_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2303_; 
if (v_isShared_2301_ == 0)
{
v___x_2303_ = v___x_2300_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_a_2298_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
return v___x_2303_;
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
lean_object* v_c_2310_ = _args[0];
lean_object* v_x_2311_ = _args[1];
lean_object* v_as_2312_ = _args[2];
lean_object* v_sz_2313_ = _args[3];
lean_object* v_i_2314_ = _args[4];
lean_object* v_b_2315_ = _args[5];
lean_object* v___y_2316_ = _args[6];
lean_object* v___y_2317_ = _args[7];
lean_object* v___y_2318_ = _args[8];
lean_object* v___y_2319_ = _args[9];
lean_object* v___y_2320_ = _args[10];
lean_object* v___y_2321_ = _args[11];
lean_object* v___y_2322_ = _args[12];
lean_object* v___y_2323_ = _args[13];
lean_object* v___y_2324_ = _args[14];
lean_object* v___y_2325_ = _args[15];
lean_object* v___y_2326_ = _args[16];
_start:
{
size_t v_sz_boxed_2327_; size_t v_i_boxed_2328_; lean_object* v_res_2329_; 
v_sz_boxed_2327_ = lean_unbox_usize(v_sz_2313_);
lean_dec(v_sz_2313_);
v_i_boxed_2328_ = lean_unbox_usize(v_i_2314_);
lean_dec(v_i_2314_);
v_res_2329_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9(v_c_2310_, v_x_2311_, v_as_2312_, v_sz_boxed_2327_, v_i_boxed_2328_, v_b_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec(v___y_2317_);
lean_dec(v___y_2316_);
lean_dec_ref(v_as_2312_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(lean_object* v_init_2330_, lean_object* v_c_2331_, lean_object* v_x_2332_, lean_object* v_n_2333_, lean_object* v_b_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_){
_start:
{
if (lean_obj_tag(v_n_2333_) == 0)
{
lean_object* v_cs_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; size_t v_sz_2349_; size_t v___x_2350_; lean_object* v___x_2351_; 
v_cs_2346_ = lean_ctor_get(v_n_2333_, 0);
v___x_2347_ = lean_box(0);
v___x_2348_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2347_);
lean_ctor_set(v___x_2348_, 1, v_b_2334_);
v_sz_2349_ = lean_array_size(v_cs_2346_);
v___x_2350_ = ((size_t)0ULL);
v___x_2351_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8(v_init_2330_, v_c_2331_, v_x_2332_, v_cs_2346_, v_sz_2349_, v___x_2350_, v___x_2348_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2366_; 
v_a_2352_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2366_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2354_ = v___x_2351_;
v_isShared_2355_ = v_isSharedCheck_2366_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___x_2351_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2366_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v_fst_2356_; 
v_fst_2356_ = lean_ctor_get(v_a_2352_, 0);
if (lean_obj_tag(v_fst_2356_) == 0)
{
lean_object* v_snd_2357_; lean_object* v___x_2358_; lean_object* v___x_2360_; 
v_snd_2357_ = lean_ctor_get(v_a_2352_, 1);
lean_inc(v_snd_2357_);
lean_dec(v_a_2352_);
v___x_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2358_, 0, v_snd_2357_);
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 0, v___x_2358_);
v___x_2360_ = v___x_2354_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v___x_2358_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
else
{
lean_object* v_val_2362_; lean_object* v___x_2364_; 
lean_inc_ref(v_fst_2356_);
lean_dec(v_a_2352_);
v_val_2362_ = lean_ctor_get(v_fst_2356_, 0);
lean_inc(v_val_2362_);
lean_dec_ref_known(v_fst_2356_, 1);
if (v_isShared_2355_ == 0)
{
lean_ctor_set(v___x_2354_, 0, v_val_2362_);
v___x_2364_ = v___x_2354_;
goto v_reusejp_2363_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v_val_2362_);
v___x_2364_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2363_;
}
v_reusejp_2363_:
{
return v___x_2364_;
}
}
}
}
else
{
lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2374_; 
v_a_2367_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2369_ = v___x_2351_;
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v___x_2351_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2372_; 
if (v_isShared_2370_ == 0)
{
v___x_2372_ = v___x_2369_;
goto v_reusejp_2371_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_a_2367_);
v___x_2372_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2371_;
}
v_reusejp_2371_:
{
return v___x_2372_;
}
}
}
}
else
{
lean_object* v_vs_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; size_t v_sz_2378_; size_t v___x_2379_; lean_object* v___x_2380_; 
v_vs_2375_ = lean_ctor_get(v_n_2333_, 0);
v___x_2376_ = lean_box(0);
v___x_2377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2376_);
lean_ctor_set(v___x_2377_, 1, v_b_2334_);
v_sz_2378_ = lean_array_size(v_vs_2375_);
v___x_2379_ = ((size_t)0ULL);
v___x_2380_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9(v_c_2331_, v_x_2332_, v_vs_2375_, v_sz_2378_, v___x_2379_, v___x_2377_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_);
if (lean_obj_tag(v___x_2380_) == 0)
{
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2395_; 
v_a_2381_ = lean_ctor_get(v___x_2380_, 0);
v_isSharedCheck_2395_ = !lean_is_exclusive(v___x_2380_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2383_ = v___x_2380_;
v_isShared_2384_ = v_isSharedCheck_2395_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___x_2380_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2395_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v_fst_2385_; 
v_fst_2385_ = lean_ctor_get(v_a_2381_, 0);
if (lean_obj_tag(v_fst_2385_) == 0)
{
lean_object* v_snd_2386_; lean_object* v___x_2387_; lean_object* v___x_2389_; 
v_snd_2386_ = lean_ctor_get(v_a_2381_, 1);
lean_inc(v_snd_2386_);
lean_dec(v_a_2381_);
v___x_2387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2387_, 0, v_snd_2386_);
if (v_isShared_2384_ == 0)
{
lean_ctor_set(v___x_2383_, 0, v___x_2387_);
v___x_2389_ = v___x_2383_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v___x_2387_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
else
{
lean_object* v_val_2391_; lean_object* v___x_2393_; 
lean_inc_ref(v_fst_2385_);
lean_dec(v_a_2381_);
v_val_2391_ = lean_ctor_get(v_fst_2385_, 0);
lean_inc(v_val_2391_);
lean_dec_ref_known(v_fst_2385_, 1);
if (v_isShared_2384_ == 0)
{
lean_ctor_set(v___x_2383_, 0, v_val_2391_);
v___x_2393_ = v___x_2383_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_val_2391_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
}
}
else
{
lean_object* v_a_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2403_; 
v_a_2396_ = lean_ctor_get(v___x_2380_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2380_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2398_ = v___x_2380_;
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_a_2396_);
lean_dec(v___x_2380_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2401_; 
if (v_isShared_2399_ == 0)
{
v___x_2401_ = v___x_2398_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v_a_2396_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8(lean_object* v_init_2404_, lean_object* v_c_2405_, lean_object* v_x_2406_, lean_object* v_as_2407_, size_t v_sz_2408_, size_t v_i_2409_, lean_object* v_b_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_){
_start:
{
uint8_t v___x_2422_; 
v___x_2422_ = lean_usize_dec_lt(v_i_2409_, v_sz_2408_);
if (v___x_2422_ == 0)
{
lean_object* v___x_2423_; 
lean_dec(v_x_2406_);
lean_dec_ref(v_c_2405_);
v___x_2423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2423_, 0, v_b_2410_);
return v___x_2423_;
}
else
{
lean_object* v_snd_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2458_; 
v_snd_2424_ = lean_ctor_get(v_b_2410_, 1);
v_isSharedCheck_2458_ = !lean_is_exclusive(v_b_2410_);
if (v_isSharedCheck_2458_ == 0)
{
lean_object* v_unused_2459_; 
v_unused_2459_ = lean_ctor_get(v_b_2410_, 0);
lean_dec(v_unused_2459_);
v___x_2426_ = v_b_2410_;
v_isShared_2427_ = v_isSharedCheck_2458_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_snd_2424_);
lean_dec(v_b_2410_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2458_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v_a_2428_; lean_object* v___x_2429_; 
v_a_2428_ = lean_array_uget_borrowed(v_as_2407_, v_i_2409_);
lean_inc(v_snd_2424_);
lean_inc(v_x_2406_);
lean_inc_ref(v_c_2405_);
v___x_2429_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(v_init_2404_, v_c_2405_, v_x_2406_, v_a_2428_, v_snd_2424_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
if (lean_obj_tag(v___x_2429_) == 0)
{
lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2449_; 
v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2449_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2432_ = v___x_2429_;
v_isShared_2433_ = v_isSharedCheck_2449_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2429_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2449_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
if (lean_obj_tag(v_a_2430_) == 0)
{
lean_object* v___x_2434_; lean_object* v___x_2436_; 
lean_dec(v_x_2406_);
lean_dec_ref(v_c_2405_);
v___x_2434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2434_, 0, v_a_2430_);
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 0, v___x_2434_);
v___x_2436_ = v___x_2426_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v___x_2434_);
lean_ctor_set(v_reuseFailAlloc_2440_, 1, v_snd_2424_);
v___x_2436_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
lean_object* v___x_2438_; 
if (v_isShared_2433_ == 0)
{
lean_ctor_set(v___x_2432_, 0, v___x_2436_);
v___x_2438_ = v___x_2432_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v___x_2436_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
else
{
lean_object* v_a_2441_; lean_object* v___x_2442_; lean_object* v___x_2444_; 
lean_del_object(v___x_2432_);
lean_dec(v_snd_2424_);
v_a_2441_ = lean_ctor_get(v_a_2430_, 0);
lean_inc(v_a_2441_);
lean_dec_ref_known(v_a_2430_, 1);
v___x_2442_ = lean_box(0);
if (v_isShared_2427_ == 0)
{
lean_ctor_set(v___x_2426_, 1, v_a_2441_);
lean_ctor_set(v___x_2426_, 0, v___x_2442_);
v___x_2444_ = v___x_2426_;
goto v_reusejp_2443_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v___x_2442_);
lean_ctor_set(v_reuseFailAlloc_2448_, 1, v_a_2441_);
v___x_2444_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2443_;
}
v_reusejp_2443_:
{
size_t v___x_2445_; size_t v___x_2446_; 
v___x_2445_ = ((size_t)1ULL);
v___x_2446_ = lean_usize_add(v_i_2409_, v___x_2445_);
v_i_2409_ = v___x_2446_;
v_b_2410_ = v___x_2444_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2450_; lean_object* v___x_2452_; uint8_t v_isShared_2453_; uint8_t v_isSharedCheck_2457_; 
lean_del_object(v___x_2426_);
lean_dec(v_snd_2424_);
lean_dec(v_x_2406_);
lean_dec_ref(v_c_2405_);
v_a_2450_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2452_ = v___x_2429_;
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
else
{
lean_inc(v_a_2450_);
lean_dec(v___x_2429_);
v___x_2452_ = lean_box(0);
v_isShared_2453_ = v_isSharedCheck_2457_;
goto v_resetjp_2451_;
}
v_resetjp_2451_:
{
lean_object* v___x_2455_; 
if (v_isShared_2453_ == 0)
{
v___x_2455_ = v___x_2452_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_a_2450_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8___boxed(lean_object** _args){
lean_object* v_init_2460_ = _args[0];
lean_object* v_c_2461_ = _args[1];
lean_object* v_x_2462_ = _args[2];
lean_object* v_as_2463_ = _args[3];
lean_object* v_sz_2464_ = _args[4];
lean_object* v_i_2465_ = _args[5];
lean_object* v_b_2466_ = _args[6];
lean_object* v___y_2467_ = _args[7];
lean_object* v___y_2468_ = _args[8];
lean_object* v___y_2469_ = _args[9];
lean_object* v___y_2470_ = _args[10];
lean_object* v___y_2471_ = _args[11];
lean_object* v___y_2472_ = _args[12];
lean_object* v___y_2473_ = _args[13];
lean_object* v___y_2474_ = _args[14];
lean_object* v___y_2475_ = _args[15];
lean_object* v___y_2476_ = _args[16];
lean_object* v___y_2477_ = _args[17];
_start:
{
size_t v_sz_boxed_2478_; size_t v_i_boxed_2479_; lean_object* v_res_2480_; 
v_sz_boxed_2478_ = lean_unbox_usize(v_sz_2464_);
lean_dec(v_sz_2464_);
v_i_boxed_2479_ = lean_unbox_usize(v_i_2465_);
lean_dec(v_i_2465_);
v_res_2480_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8(v_init_2460_, v_c_2461_, v_x_2462_, v_as_2463_, v_sz_boxed_2478_, v_i_boxed_2479_, v_b_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_, v___y_2475_, v___y_2476_);
lean_dec(v___y_2476_);
lean_dec_ref(v___y_2475_);
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
lean_dec(v___y_2468_);
lean_dec(v___y_2467_);
lean_dec_ref(v_as_2463_);
lean_dec_ref(v_init_2460_);
return v_res_2480_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6___boxed(lean_object* v_init_2481_, lean_object* v_c_2482_, lean_object* v_x_2483_, lean_object* v_n_2484_, lean_object* v_b_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_){
_start:
{
lean_object* v_res_2497_; 
v_res_2497_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(v_init_2481_, v_c_2482_, v_x_2483_, v_n_2484_, v_b_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec(v___y_2487_);
lean_dec(v___y_2486_);
lean_dec_ref(v_n_2484_);
lean_dec_ref(v_init_2481_);
return v_res_2497_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2(lean_object* v_c_2498_, lean_object* v_x_2499_, lean_object* v_t_2500_, lean_object* v_init_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_){
_start:
{
lean_object* v_root_2513_; lean_object* v_tail_2514_; lean_object* v___x_2515_; 
v_root_2513_ = lean_ctor_get(v_t_2500_, 0);
v_tail_2514_ = lean_ctor_get(v_t_2500_, 1);
lean_inc(v_x_2499_);
lean_inc_ref(v_c_2498_);
lean_inc_ref(v_init_2501_);
v___x_2515_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(v_init_2501_, v_c_2498_, v_x_2499_, v_root_2513_, v_init_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
lean_dec_ref(v_init_2501_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2552_; 
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2518_ = v___x_2515_;
v_isShared_2519_ = v_isSharedCheck_2552_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2515_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2552_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
if (lean_obj_tag(v_a_2516_) == 0)
{
lean_object* v_a_2520_; lean_object* v___x_2522_; 
lean_dec(v_x_2499_);
lean_dec_ref(v_c_2498_);
v_a_2520_ = lean_ctor_get(v_a_2516_, 0);
lean_inc(v_a_2520_);
lean_dec_ref_known(v_a_2516_, 1);
if (v_isShared_2519_ == 0)
{
lean_ctor_set(v___x_2518_, 0, v_a_2520_);
v___x_2522_ = v___x_2518_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v_a_2520_);
v___x_2522_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
return v___x_2522_;
}
}
else
{
lean_object* v_a_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; size_t v_sz_2527_; size_t v___x_2528_; lean_object* v___x_2529_; 
lean_del_object(v___x_2518_);
v_a_2524_ = lean_ctor_get(v_a_2516_, 0);
lean_inc(v_a_2524_);
lean_dec_ref_known(v_a_2516_, 1);
v___x_2525_ = lean_box(0);
v___x_2526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2526_, 0, v___x_2525_);
lean_ctor_set(v___x_2526_, 1, v_a_2524_);
v_sz_2527_ = lean_array_size(v_tail_2514_);
v___x_2528_ = ((size_t)0ULL);
v___x_2529_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7(v_c_2498_, v_x_2499_, v_tail_2514_, v_sz_2527_, v___x_2528_, v___x_2526_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_object* v_a_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2543_; 
v_a_2530_ = lean_ctor_get(v___x_2529_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2532_ = v___x_2529_;
v_isShared_2533_ = v_isSharedCheck_2543_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_a_2530_);
lean_dec(v___x_2529_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2543_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v_fst_2534_; 
v_fst_2534_ = lean_ctor_get(v_a_2530_, 0);
if (lean_obj_tag(v_fst_2534_) == 0)
{
lean_object* v_snd_2535_; lean_object* v___x_2537_; 
v_snd_2535_ = lean_ctor_get(v_a_2530_, 1);
lean_inc(v_snd_2535_);
lean_dec(v_a_2530_);
if (v_isShared_2533_ == 0)
{
lean_ctor_set(v___x_2532_, 0, v_snd_2535_);
v___x_2537_ = v___x_2532_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_snd_2535_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
else
{
lean_object* v_val_2539_; lean_object* v___x_2541_; 
lean_inc_ref(v_fst_2534_);
lean_dec(v_a_2530_);
v_val_2539_ = lean_ctor_get(v_fst_2534_, 0);
lean_inc(v_val_2539_);
lean_dec_ref_known(v_fst_2534_, 1);
if (v_isShared_2533_ == 0)
{
lean_ctor_set(v___x_2532_, 0, v_val_2539_);
v___x_2541_ = v___x_2532_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_val_2539_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
}
else
{
lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2551_; 
v_a_2544_ = lean_ctor_get(v___x_2529_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2546_ = v___x_2529_;
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_dec(v___x_2529_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2549_; 
if (v_isShared_2547_ == 0)
{
v___x_2549_ = v___x_2546_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_a_2544_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
}
}
}
else
{
lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2560_; 
lean_dec(v_x_2499_);
lean_dec_ref(v_c_2498_);
v_a_2553_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2560_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2560_ == 0)
{
v___x_2555_ = v___x_2515_;
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___x_2515_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2560_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
lean_object* v___x_2558_; 
if (v_isShared_2556_ == 0)
{
v___x_2558_ = v___x_2555_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v_a_2553_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
return v___x_2558_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2___boxed(lean_object* v_c_2561_, lean_object* v_x_2562_, lean_object* v_t_2563_, lean_object* v_init_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_){
_start:
{
lean_object* v_res_2576_; 
v_res_2576_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2(v_c_2561_, v_x_2562_, v_t_2563_, v_init_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_, v___y_2574_);
lean_dec(v___y_2574_);
lean_dec_ref(v___y_2573_);
lean_dec(v___y_2572_);
lean_dec_ref(v___y_2571_);
lean_dec(v___y_2570_);
lean_dec_ref(v___y_2569_);
lean_dec(v___y_2568_);
lean_dec_ref(v___y_2567_);
lean_dec(v___y_2566_);
lean_dec(v___y_2565_);
lean_dec_ref(v_t_2563_);
return v_res_2576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(lean_object* v_x_2577_, lean_object* v_c_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_){
_start:
{
lean_object* v___x_2590_; 
v___x_2590_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2579_, v_a_2587_);
if (lean_obj_tag(v___x_2590_) == 0)
{
lean_object* v_a_2591_; lean_object* v___y_2593_; lean_object* v_diseqs_2618_; lean_object* v_size_2619_; lean_object* v___x_2620_; uint8_t v___x_2621_; 
v_a_2591_ = lean_ctor_get(v___x_2590_, 0);
lean_inc(v_a_2591_);
lean_dec_ref_known(v___x_2590_, 1);
v_diseqs_2618_ = lean_ctor_get(v_a_2591_, 9);
lean_inc_ref(v_diseqs_2618_);
lean_dec(v_a_2591_);
v_size_2619_ = lean_ctor_get(v_diseqs_2618_, 2);
v___x_2620_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0);
v___x_2621_ = lean_nat_dec_lt(v_x_2577_, v_size_2619_);
if (v___x_2621_ == 0)
{
lean_object* v___x_2622_; 
lean_dec_ref(v_diseqs_2618_);
v___x_2622_ = l_outOfBounds___redArg(v___x_2620_);
v___y_2593_ = v___x_2622_;
goto v___jp_2592_;
}
else
{
lean_object* v___x_2623_; 
v___x_2623_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2620_, v_diseqs_2618_, v_x_2577_);
lean_dec_ref(v_diseqs_2618_);
v___y_2593_ = v___x_2623_;
goto v___jp_2592_;
}
v___jp_2592_:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
v___x_2594_ = lean_box(0);
v___x_2595_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___closed__0));
v___x_2596_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2(v_c_2578_, v_x_2577_, v___y_2593_, v___x_2595_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_);
lean_dec_ref(v___y_2593_);
if (lean_obj_tag(v___x_2596_) == 0)
{
lean_object* v_a_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2609_; 
v_a_2597_ = lean_ctor_get(v___x_2596_, 0);
v_isSharedCheck_2609_ = !lean_is_exclusive(v___x_2596_);
if (v_isSharedCheck_2609_ == 0)
{
v___x_2599_ = v___x_2596_;
v_isShared_2600_ = v_isSharedCheck_2609_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_a_2597_);
lean_dec(v___x_2596_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2609_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
lean_object* v_fst_2601_; 
v_fst_2601_ = lean_ctor_get(v_a_2597_, 0);
lean_inc(v_fst_2601_);
lean_dec(v_a_2597_);
if (lean_obj_tag(v_fst_2601_) == 0)
{
lean_object* v___x_2603_; 
if (v_isShared_2600_ == 0)
{
lean_ctor_set(v___x_2599_, 0, v___x_2594_);
v___x_2603_ = v___x_2599_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v___x_2594_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
else
{
lean_object* v_val_2605_; lean_object* v___x_2607_; 
v_val_2605_ = lean_ctor_get(v_fst_2601_, 0);
lean_inc(v_val_2605_);
lean_dec_ref_known(v_fst_2601_, 1);
if (v_isShared_2600_ == 0)
{
lean_ctor_set(v___x_2599_, 0, v_val_2605_);
v___x_2607_ = v___x_2599_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v_val_2605_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
return v___x_2607_;
}
}
}
}
else
{
lean_object* v_a_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2617_; 
v_a_2610_ = lean_ctor_get(v___x_2596_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2596_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2612_ = v___x_2596_;
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_a_2610_);
lean_dec(v___x_2596_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___x_2615_; 
if (v_isShared_2613_ == 0)
{
v___x_2615_ = v___x_2612_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_a_2610_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
}
}
}
else
{
lean_object* v_a_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2631_; 
lean_dec_ref(v_c_2578_);
lean_dec(v_x_2577_);
v_a_2624_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2626_ = v___x_2590_;
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_a_2624_);
lean_dec(v___x_2590_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2629_; 
if (v_isShared_2627_ == 0)
{
v___x_2629_ = v___x_2626_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_a_2624_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f___boxed(lean_object* v_x_2632_, lean_object* v_c_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_){
_start:
{
lean_object* v_res_2645_; 
v_res_2645_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(v_x_2632_, v_c_2633_, v_a_2634_, v_a_2635_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_, v_a_2643_);
lean_dec(v_a_2643_);
lean_dec_ref(v_a_2642_);
lean_dec(v_a_2641_);
lean_dec_ref(v_a_2640_);
lean_dec(v_a_2639_);
lean_dec_ref(v_a_2638_);
lean_dec(v_a_2637_);
lean_dec_ref(v_a_2636_);
lean_dec(v_a_2635_);
lean_dec(v_a_2634_);
return v_res_2645_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11(lean_object* v_c_2646_, lean_object* v_x_2647_, lean_object* v_as_2648_, size_t v_sz_2649_, size_t v_i_2650_, lean_object* v_b_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_){
_start:
{
lean_object* v___x_2663_; 
v___x_2663_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(v_c_2646_, v_x_2647_, v_as_2648_, v_sz_2649_, v_i_2650_, v_b_2651_, v___y_2652_);
return v___x_2663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___boxed(lean_object** _args){
lean_object* v_c_2664_ = _args[0];
lean_object* v_x_2665_ = _args[1];
lean_object* v_as_2666_ = _args[2];
lean_object* v_sz_2667_ = _args[3];
lean_object* v_i_2668_ = _args[4];
lean_object* v_b_2669_ = _args[5];
lean_object* v___y_2670_ = _args[6];
lean_object* v___y_2671_ = _args[7];
lean_object* v___y_2672_ = _args[8];
lean_object* v___y_2673_ = _args[9];
lean_object* v___y_2674_ = _args[10];
lean_object* v___y_2675_ = _args[11];
lean_object* v___y_2676_ = _args[12];
lean_object* v___y_2677_ = _args[13];
lean_object* v___y_2678_ = _args[14];
lean_object* v___y_2679_ = _args[15];
lean_object* v___y_2680_ = _args[16];
_start:
{
size_t v_sz_boxed_2681_; size_t v_i_boxed_2682_; lean_object* v_res_2683_; 
v_sz_boxed_2681_ = lean_unbox_usize(v_sz_2667_);
lean_dec(v_sz_2667_);
v_i_boxed_2682_ = lean_unbox_usize(v_i_2668_);
lean_dec(v_i_2668_);
v_res_2683_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11(v_c_2664_, v_x_2665_, v_as_2666_, v_sz_boxed_2681_, v_i_boxed_2682_, v_b_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
lean_dec(v___y_2677_);
lean_dec_ref(v___y_2676_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
lean_dec(v___y_2673_);
lean_dec_ref(v___y_2672_);
lean_dec(v___y_2671_);
lean_dec(v___y_2670_);
lean_dec_ref(v_as_2666_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10(lean_object* v_c_2684_, lean_object* v_x_2685_, lean_object* v_as_2686_, size_t v_sz_2687_, size_t v_i_2688_, lean_object* v_b_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_){
_start:
{
lean_object* v___x_2701_; 
v___x_2701_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(v_c_2684_, v_x_2685_, v_as_2686_, v_sz_2687_, v_i_2688_, v_b_2689_, v___y_2690_);
return v___x_2701_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___boxed(lean_object** _args){
lean_object* v_c_2702_ = _args[0];
lean_object* v_x_2703_ = _args[1];
lean_object* v_as_2704_ = _args[2];
lean_object* v_sz_2705_ = _args[3];
lean_object* v_i_2706_ = _args[4];
lean_object* v_b_2707_ = _args[5];
lean_object* v___y_2708_ = _args[6];
lean_object* v___y_2709_ = _args[7];
lean_object* v___y_2710_ = _args[8];
lean_object* v___y_2711_ = _args[9];
lean_object* v___y_2712_ = _args[10];
lean_object* v___y_2713_ = _args[11];
lean_object* v___y_2714_ = _args[12];
lean_object* v___y_2715_ = _args[13];
lean_object* v___y_2716_ = _args[14];
lean_object* v___y_2717_ = _args[15];
lean_object* v___y_2718_ = _args[16];
_start:
{
size_t v_sz_boxed_2719_; size_t v_i_boxed_2720_; lean_object* v_res_2721_; 
v_sz_boxed_2719_ = lean_unbox_usize(v_sz_2705_);
lean_dec(v_sz_2705_);
v_i_boxed_2720_ = lean_unbox_usize(v_i_2706_);
lean_dec(v_i_2706_);
v_res_2721_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10(v_c_2702_, v_x_2703_, v_as_2704_, v_sz_boxed_2719_, v_i_boxed_2720_, v_b_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
lean_dec(v___y_2713_);
lean_dec_ref(v___y_2712_);
lean_dec(v___y_2711_);
lean_dec_ref(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec_ref(v_as_2704_);
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg(lean_object* v_v_2722_, lean_object* v_a_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_){
_start:
{
lean_object* v_snd_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2766_; 
v_snd_2735_ = lean_ctor_get(v_a_2723_, 1);
v_isSharedCheck_2766_ = !lean_is_exclusive(v_a_2723_);
if (v_isSharedCheck_2766_ == 0)
{
lean_object* v_unused_2767_; 
v_unused_2767_ = lean_ctor_get(v_a_2723_, 0);
lean_dec(v_unused_2767_);
v___x_2737_ = v_a_2723_;
v_isShared_2738_ = v_isSharedCheck_2766_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_snd_2735_);
lean_dec(v_a_2723_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2766_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2739_; 
lean_inc(v_snd_2735_);
lean_inc(v_v_2722_);
v___x_2739_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(v_v_2722_, v_snd_2735_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
if (lean_obj_tag(v___x_2739_) == 0)
{
lean_object* v_a_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2757_; 
v_a_2740_ = lean_ctor_get(v___x_2739_, 0);
v_isSharedCheck_2757_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2742_ = v___x_2739_;
v_isShared_2743_ = v_isSharedCheck_2757_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_a_2740_);
lean_dec(v___x_2739_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2757_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
if (lean_obj_tag(v_a_2740_) == 1)
{
lean_object* v_val_2744_; lean_object* v___x_2745_; lean_object* v___x_2747_; 
lean_del_object(v___x_2742_);
lean_dec(v_snd_2735_);
v_val_2744_ = lean_ctor_get(v_a_2740_, 0);
lean_inc(v_val_2744_);
lean_dec_ref_known(v_a_2740_, 1);
v___x_2745_ = lean_box(0);
if (v_isShared_2738_ == 0)
{
lean_ctor_set(v___x_2737_, 1, v_val_2744_);
lean_ctor_set(v___x_2737_, 0, v___x_2745_);
v___x_2747_ = v___x_2737_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v___x_2745_);
lean_ctor_set(v_reuseFailAlloc_2749_, 1, v_val_2744_);
v___x_2747_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
v_a_2723_ = v___x_2747_;
goto _start;
}
}
else
{
lean_object* v___x_2750_; lean_object* v___x_2752_; 
lean_dec(v_a_2740_);
lean_dec(v_v_2722_);
lean_inc(v_snd_2735_);
v___x_2750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2750_, 0, v_snd_2735_);
if (v_isShared_2738_ == 0)
{
lean_ctor_set(v___x_2737_, 0, v___x_2750_);
v___x_2752_ = v___x_2737_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v___x_2750_);
lean_ctor_set(v_reuseFailAlloc_2756_, 1, v_snd_2735_);
v___x_2752_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
lean_object* v___x_2754_; 
if (v_isShared_2743_ == 0)
{
lean_ctor_set(v___x_2742_, 0, v___x_2752_);
v___x_2754_ = v___x_2742_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v___x_2752_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
}
}
}
}
}
else
{
lean_object* v_a_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2765_; 
lean_del_object(v___x_2737_);
lean_dec(v_snd_2735_);
lean_dec(v_v_2722_);
v_a_2758_ = lean_ctor_get(v___x_2739_, 0);
v_isSharedCheck_2765_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2765_ == 0)
{
v___x_2760_ = v___x_2739_;
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_a_2758_);
lean_dec(v___x_2739_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2765_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2763_; 
if (v_isShared_2761_ == 0)
{
v___x_2763_ = v___x_2760_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v_a_2758_);
v___x_2763_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
return v___x_2763_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg___boxed(lean_object* v_v_2768_, lean_object* v_a_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_){
_start:
{
lean_object* v_res_2781_; 
v_res_2781_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg(v_v_2768_, v_a_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_);
lean_dec(v___y_2779_);
lean_dec_ref(v___y_2778_);
lean_dec(v___y_2777_);
lean_dec_ref(v___y_2776_);
lean_dec(v___y_2775_);
lean_dec_ref(v___y_2774_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
lean_dec(v___y_2771_);
lean_dec(v___y_2770_);
return v_res_2781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(lean_object* v_c_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_){
_start:
{
lean_object* v_p_2794_; 
v_p_2794_ = lean_ctor_get(v_c_2782_, 0);
if (lean_obj_tag(v_p_2794_) == 1)
{
lean_object* v_v_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; 
v_v_2795_ = lean_ctor_get(v_p_2794_, 1);
lean_inc(v_v_2795_);
v___x_2796_ = lean_box(0);
v___x_2797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2797_, 0, v___x_2796_);
lean_ctor_set(v___x_2797_, 1, v_c_2782_);
v___x_2798_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg(v_v_2795_, v___x_2797_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_, v_a_2789_, v_a_2790_, v_a_2791_, v_a_2792_);
if (lean_obj_tag(v___x_2798_) == 0)
{
lean_object* v_a_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2812_; 
v_a_2799_ = lean_ctor_get(v___x_2798_, 0);
v_isSharedCheck_2812_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2812_ == 0)
{
v___x_2801_ = v___x_2798_;
v_isShared_2802_ = v_isSharedCheck_2812_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_a_2799_);
lean_dec(v___x_2798_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2812_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v_fst_2803_; 
v_fst_2803_ = lean_ctor_get(v_a_2799_, 0);
if (lean_obj_tag(v_fst_2803_) == 0)
{
lean_object* v_snd_2804_; lean_object* v___x_2806_; 
v_snd_2804_ = lean_ctor_get(v_a_2799_, 1);
lean_inc(v_snd_2804_);
lean_dec(v_a_2799_);
if (v_isShared_2802_ == 0)
{
lean_ctor_set(v___x_2801_, 0, v_snd_2804_);
v___x_2806_ = v___x_2801_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_snd_2804_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
return v___x_2806_;
}
}
else
{
lean_object* v_val_2808_; lean_object* v___x_2810_; 
lean_inc_ref(v_fst_2803_);
lean_dec(v_a_2799_);
v_val_2808_ = lean_ctor_get(v_fst_2803_, 0);
lean_inc(v_val_2808_);
lean_dec_ref_known(v_fst_2803_, 1);
if (v_isShared_2802_ == 0)
{
lean_ctor_set(v___x_2801_, 0, v_val_2808_);
v___x_2810_ = v___x_2801_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_val_2808_);
v___x_2810_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
return v___x_2810_;
}
}
}
}
else
{
lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2820_; 
v_a_2813_ = lean_ctor_get(v___x_2798_, 0);
v_isSharedCheck_2820_ = !lean_is_exclusive(v___x_2798_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2815_ = v___x_2798_;
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_dec(v___x_2798_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2818_; 
if (v_isShared_2816_ == 0)
{
v___x_2818_ = v___x_2815_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_a_2813_);
v___x_2818_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
return v___x_2818_;
}
}
}
}
else
{
lean_object* v___x_2821_; 
v___x_2821_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_2782_, v_a_2783_, v_a_2789_, v_a_2790_, v_a_2791_, v_a_2792_);
return v___x_2821_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq___boxed(lean_object* v_c_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_){
_start:
{
lean_object* v_res_2834_; 
v_res_2834_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(v_c_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_, v_a_2828_, v_a_2829_, v_a_2830_, v_a_2831_, v_a_2832_);
lean_dec(v_a_2832_);
lean_dec_ref(v_a_2831_);
lean_dec(v_a_2830_);
lean_dec_ref(v_a_2829_);
lean_dec(v_a_2828_);
lean_dec_ref(v_a_2827_);
lean_dec(v_a_2826_);
lean_dec_ref(v_a_2825_);
lean_dec(v_a_2824_);
lean_dec(v_a_2823_);
return v_res_2834_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0(lean_object* v_v_2835_, lean_object* v_inst_2836_, lean_object* v_a_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_){
_start:
{
lean_object* v___x_2849_; 
v___x_2849_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg(v_v_2835_, v_a_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_);
return v___x_2849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___boxed(lean_object* v_v_2850_, lean_object* v_inst_2851_, lean_object* v_a_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_, lean_object* v___y_2862_, lean_object* v___y_2863_){
_start:
{
lean_object* v_res_2864_; 
v_res_2864_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0(v_v_2850_, v_inst_2851_, v_a_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
lean_dec(v___y_2862_);
lean_dec_ref(v___y_2861_);
lean_dec(v___y_2860_);
lean_dec_ref(v___y_2859_);
lean_dec(v___y_2858_);
lean_dec_ref(v___y_2857_);
lean_dec(v___y_2856_);
lean_dec_ref(v___y_2855_);
lean_dec(v___y_2854_);
lean_dec(v___y_2853_);
return v_res_2864_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(lean_object* v_a_2865_, lean_object* v_x_2866_, size_t v_x_2867_, size_t v_x_2868_){
_start:
{
if (lean_obj_tag(v_x_2866_) == 0)
{
lean_object* v_cs_2869_; size_t v_j_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; uint8_t v___x_2873_; 
v_cs_2869_ = lean_ctor_get(v_x_2866_, 0);
v_j_2870_ = lean_usize_shift_right(v_x_2867_, v_x_2868_);
v___x_2871_ = lean_usize_to_nat(v_j_2870_);
v___x_2872_ = lean_array_get_size(v_cs_2869_);
v___x_2873_ = lean_nat_dec_lt(v___x_2871_, v___x_2872_);
if (v___x_2873_ == 0)
{
lean_dec(v___x_2871_);
lean_dec_ref(v_a_2865_);
return v_x_2866_;
}
else
{
lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2891_; 
lean_inc_ref(v_cs_2869_);
v_isSharedCheck_2891_ = !lean_is_exclusive(v_x_2866_);
if (v_isSharedCheck_2891_ == 0)
{
lean_object* v_unused_2892_; 
v_unused_2892_ = lean_ctor_get(v_x_2866_, 0);
lean_dec(v_unused_2892_);
v___x_2875_ = v_x_2866_;
v_isShared_2876_ = v_isSharedCheck_2891_;
goto v_resetjp_2874_;
}
else
{
lean_dec(v_x_2866_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2891_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
size_t v___x_2877_; size_t v___x_2878_; size_t v___x_2879_; size_t v_i_2880_; size_t v___x_2881_; size_t v_shift_2882_; lean_object* v_v_2883_; lean_object* v___x_2884_; lean_object* v_xs_x27_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2889_; 
v___x_2877_ = ((size_t)1ULL);
v___x_2878_ = lean_usize_shift_left(v___x_2877_, v_x_2868_);
v___x_2879_ = lean_usize_sub(v___x_2878_, v___x_2877_);
v_i_2880_ = lean_usize_land(v_x_2867_, v___x_2879_);
v___x_2881_ = ((size_t)5ULL);
v_shift_2882_ = lean_usize_sub(v_x_2868_, v___x_2881_);
v_v_2883_ = lean_array_fget(v_cs_2869_, v___x_2871_);
v___x_2884_ = lean_box(0);
v_xs_x27_2885_ = lean_array_fset(v_cs_2869_, v___x_2871_, v___x_2884_);
v___x_2886_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(v_a_2865_, v_v_2883_, v_i_2880_, v_shift_2882_);
v___x_2887_ = lean_array_fset(v_xs_x27_2885_, v___x_2871_, v___x_2886_);
lean_dec(v___x_2871_);
if (v_isShared_2876_ == 0)
{
lean_ctor_set(v___x_2875_, 0, v___x_2887_);
v___x_2889_ = v___x_2875_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v___x_2887_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
return v___x_2889_;
}
}
}
}
else
{
lean_object* v_vs_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; uint8_t v___x_2896_; 
v_vs_2893_ = lean_ctor_get(v_x_2866_, 0);
v___x_2894_ = lean_usize_to_nat(v_x_2867_);
v___x_2895_ = lean_array_get_size(v_vs_2893_);
v___x_2896_ = lean_nat_dec_lt(v___x_2894_, v___x_2895_);
if (v___x_2896_ == 0)
{
lean_dec(v___x_2894_);
lean_dec_ref(v_a_2865_);
return v_x_2866_;
}
else
{
lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2908_; 
lean_inc_ref(v_vs_2893_);
v_isSharedCheck_2908_ = !lean_is_exclusive(v_x_2866_);
if (v_isSharedCheck_2908_ == 0)
{
lean_object* v_unused_2909_; 
v_unused_2909_ = lean_ctor_get(v_x_2866_, 0);
lean_dec(v_unused_2909_);
v___x_2898_ = v_x_2866_;
v_isShared_2899_ = v_isSharedCheck_2908_;
goto v_resetjp_2897_;
}
else
{
lean_dec(v_x_2866_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2908_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v_v_2900_; lean_object* v___x_2901_; lean_object* v_xs_x27_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2906_; 
v_v_2900_ = lean_array_fget(v_vs_2893_, v___x_2894_);
v___x_2901_ = lean_box(0);
v_xs_x27_2902_ = lean_array_fset(v_vs_2893_, v___x_2894_, v___x_2901_);
v___x_2903_ = l_Lean_PersistentArray_push___redArg(v_v_2900_, v_a_2865_);
v___x_2904_ = lean_array_fset(v_xs_x27_2902_, v___x_2894_, v___x_2903_);
lean_dec(v___x_2894_);
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 0, v___x_2904_);
v___x_2906_ = v___x_2898_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v___x_2904_);
v___x_2906_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
return v___x_2906_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0___boxed(lean_object* v_a_2910_, lean_object* v_x_2911_, lean_object* v_x_2912_, lean_object* v_x_2913_){
_start:
{
size_t v_x_93999__boxed_2914_; size_t v_x_94000__boxed_2915_; lean_object* v_res_2916_; 
v_x_93999__boxed_2914_ = lean_unbox_usize(v_x_2912_);
lean_dec(v_x_2912_);
v_x_94000__boxed_2915_ = lean_unbox_usize(v_x_2913_);
lean_dec(v_x_2913_);
v_res_2916_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(v_a_2910_, v_x_2911_, v_x_93999__boxed_2914_, v_x_94000__boxed_2915_);
return v_res_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(lean_object* v_a_2917_, lean_object* v_t_2918_, lean_object* v_i_2919_){
_start:
{
lean_object* v_root_2920_; lean_object* v_tail_2921_; lean_object* v_size_2922_; size_t v_shift_2923_; lean_object* v_tailOff_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2948_; 
v_root_2920_ = lean_ctor_get(v_t_2918_, 0);
v_tail_2921_ = lean_ctor_get(v_t_2918_, 1);
v_size_2922_ = lean_ctor_get(v_t_2918_, 2);
v_shift_2923_ = lean_ctor_get_usize(v_t_2918_, 4);
v_tailOff_2924_ = lean_ctor_get(v_t_2918_, 3);
v_isSharedCheck_2948_ = !lean_is_exclusive(v_t_2918_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2926_ = v_t_2918_;
v_isShared_2927_ = v_isSharedCheck_2948_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_tailOff_2924_);
lean_inc(v_size_2922_);
lean_inc(v_tail_2921_);
lean_inc(v_root_2920_);
lean_dec(v_t_2918_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2948_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
uint8_t v___x_2928_; 
v___x_2928_ = lean_nat_dec_le(v_tailOff_2924_, v_i_2919_);
if (v___x_2928_ == 0)
{
size_t v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2932_; 
v___x_2929_ = lean_usize_of_nat(v_i_2919_);
v___x_2930_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(v_a_2917_, v_root_2920_, v___x_2929_, v_shift_2923_);
if (v_isShared_2927_ == 0)
{
lean_ctor_set(v___x_2926_, 0, v___x_2930_);
v___x_2932_ = v___x_2926_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v___x_2930_);
lean_ctor_set(v_reuseFailAlloc_2933_, 1, v_tail_2921_);
lean_ctor_set(v_reuseFailAlloc_2933_, 2, v_size_2922_);
lean_ctor_set(v_reuseFailAlloc_2933_, 3, v_tailOff_2924_);
lean_ctor_set_usize(v_reuseFailAlloc_2933_, 4, v_shift_2923_);
v___x_2932_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
return v___x_2932_;
}
}
else
{
lean_object* v___x_2934_; lean_object* v___x_2935_; uint8_t v___x_2936_; 
v___x_2934_ = lean_nat_sub(v_i_2919_, v_tailOff_2924_);
v___x_2935_ = lean_array_get_size(v_tail_2921_);
v___x_2936_ = lean_nat_dec_lt(v___x_2934_, v___x_2935_);
if (v___x_2936_ == 0)
{
lean_object* v___x_2938_; 
lean_dec(v___x_2934_);
lean_dec_ref(v_a_2917_);
if (v_isShared_2927_ == 0)
{
v___x_2938_ = v___x_2926_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_root_2920_);
lean_ctor_set(v_reuseFailAlloc_2939_, 1, v_tail_2921_);
lean_ctor_set(v_reuseFailAlloc_2939_, 2, v_size_2922_);
lean_ctor_set(v_reuseFailAlloc_2939_, 3, v_tailOff_2924_);
lean_ctor_set_usize(v_reuseFailAlloc_2939_, 4, v_shift_2923_);
v___x_2938_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
return v___x_2938_;
}
}
else
{
lean_object* v_v_2940_; lean_object* v___x_2941_; lean_object* v_xs_x27_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2946_; 
v_v_2940_ = lean_array_fget(v_tail_2921_, v___x_2934_);
v___x_2941_ = lean_box(0);
v_xs_x27_2942_ = lean_array_fset(v_tail_2921_, v___x_2934_, v___x_2941_);
v___x_2943_ = l_Lean_PersistentArray_push___redArg(v_v_2940_, v_a_2917_);
v___x_2944_ = lean_array_fset(v_xs_x27_2942_, v___x_2934_, v___x_2943_);
lean_dec(v___x_2934_);
if (v_isShared_2927_ == 0)
{
lean_ctor_set(v___x_2926_, 1, v___x_2944_);
v___x_2946_ = v___x_2926_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v_root_2920_);
lean_ctor_set(v_reuseFailAlloc_2947_, 1, v___x_2944_);
lean_ctor_set(v_reuseFailAlloc_2947_, 2, v_size_2922_);
lean_ctor_set(v_reuseFailAlloc_2947_, 3, v_tailOff_2924_);
lean_ctor_set_usize(v_reuseFailAlloc_2947_, 4, v_shift_2923_);
v___x_2946_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
return v___x_2946_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0___boxed(lean_object* v_a_2949_, lean_object* v_t_2950_, lean_object* v_i_2951_){
_start:
{
lean_object* v_res_2952_; 
v_res_2952_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(v_a_2949_, v_t_2950_, v_i_2951_);
lean_dec(v_i_2951_);
return v_res_2952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0(lean_object* v_a_2953_, lean_object* v_v_2954_, lean_object* v_s_2955_){
_start:
{
lean_object* v_vars_2956_; lean_object* v_varMap_2957_; lean_object* v_vars_x27_2958_; lean_object* v_varMap_x27_2959_; lean_object* v_natToIntMap_2960_; lean_object* v_natDef_2961_; lean_object* v_dvds_2962_; lean_object* v_lowers_2963_; lean_object* v_uppers_2964_; lean_object* v_diseqs_2965_; lean_object* v_elimEqs_2966_; lean_object* v_elimStack_2967_; lean_object* v_occurs_2968_; lean_object* v_assignment_2969_; lean_object* v_nextCnstrId_2970_; uint8_t v_caseSplits_2971_; lean_object* v_conflict_x3f_2972_; lean_object* v_diseqSplits_2973_; lean_object* v_divMod_2974_; lean_object* v_toIntIds_2975_; lean_object* v_toIntInfos_2976_; lean_object* v_toIntTermMap_2977_; lean_object* v_toIntVarMap_2978_; uint8_t v_usedCommRing_2979_; lean_object* v_nonlinearOccs_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_2988_; 
v_vars_2956_ = lean_ctor_get(v_s_2955_, 0);
v_varMap_2957_ = lean_ctor_get(v_s_2955_, 1);
v_vars_x27_2958_ = lean_ctor_get(v_s_2955_, 2);
v_varMap_x27_2959_ = lean_ctor_get(v_s_2955_, 3);
v_natToIntMap_2960_ = lean_ctor_get(v_s_2955_, 4);
v_natDef_2961_ = lean_ctor_get(v_s_2955_, 5);
v_dvds_2962_ = lean_ctor_get(v_s_2955_, 6);
v_lowers_2963_ = lean_ctor_get(v_s_2955_, 7);
v_uppers_2964_ = lean_ctor_get(v_s_2955_, 8);
v_diseqs_2965_ = lean_ctor_get(v_s_2955_, 9);
v_elimEqs_2966_ = lean_ctor_get(v_s_2955_, 10);
v_elimStack_2967_ = lean_ctor_get(v_s_2955_, 11);
v_occurs_2968_ = lean_ctor_get(v_s_2955_, 12);
v_assignment_2969_ = lean_ctor_get(v_s_2955_, 13);
v_nextCnstrId_2970_ = lean_ctor_get(v_s_2955_, 14);
v_caseSplits_2971_ = lean_ctor_get_uint8(v_s_2955_, sizeof(void*)*23);
v_conflict_x3f_2972_ = lean_ctor_get(v_s_2955_, 15);
v_diseqSplits_2973_ = lean_ctor_get(v_s_2955_, 16);
v_divMod_2974_ = lean_ctor_get(v_s_2955_, 17);
v_toIntIds_2975_ = lean_ctor_get(v_s_2955_, 18);
v_toIntInfos_2976_ = lean_ctor_get(v_s_2955_, 19);
v_toIntTermMap_2977_ = lean_ctor_get(v_s_2955_, 20);
v_toIntVarMap_2978_ = lean_ctor_get(v_s_2955_, 21);
v_usedCommRing_2979_ = lean_ctor_get_uint8(v_s_2955_, sizeof(void*)*23 + 1);
v_nonlinearOccs_2980_ = lean_ctor_get(v_s_2955_, 22);
v_isSharedCheck_2988_ = !lean_is_exclusive(v_s_2955_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2982_ = v_s_2955_;
v_isShared_2983_ = v_isSharedCheck_2988_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_nonlinearOccs_2980_);
lean_inc(v_toIntVarMap_2978_);
lean_inc(v_toIntTermMap_2977_);
lean_inc(v_toIntInfos_2976_);
lean_inc(v_toIntIds_2975_);
lean_inc(v_divMod_2974_);
lean_inc(v_diseqSplits_2973_);
lean_inc(v_conflict_x3f_2972_);
lean_inc(v_nextCnstrId_2970_);
lean_inc(v_assignment_2969_);
lean_inc(v_occurs_2968_);
lean_inc(v_elimStack_2967_);
lean_inc(v_elimEqs_2966_);
lean_inc(v_diseqs_2965_);
lean_inc(v_uppers_2964_);
lean_inc(v_lowers_2963_);
lean_inc(v_dvds_2962_);
lean_inc(v_natDef_2961_);
lean_inc(v_natToIntMap_2960_);
lean_inc(v_varMap_x27_2959_);
lean_inc(v_vars_x27_2958_);
lean_inc(v_varMap_2957_);
lean_inc(v_vars_2956_);
lean_dec(v_s_2955_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_2988_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2984_; lean_object* v___x_2986_; 
v___x_2984_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(v_a_2953_, v_lowers_2963_, v_v_2954_);
if (v_isShared_2983_ == 0)
{
lean_ctor_set(v___x_2982_, 7, v___x_2984_);
v___x_2986_ = v___x_2982_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v_vars_2956_);
lean_ctor_set(v_reuseFailAlloc_2987_, 1, v_varMap_2957_);
lean_ctor_set(v_reuseFailAlloc_2987_, 2, v_vars_x27_2958_);
lean_ctor_set(v_reuseFailAlloc_2987_, 3, v_varMap_x27_2959_);
lean_ctor_set(v_reuseFailAlloc_2987_, 4, v_natToIntMap_2960_);
lean_ctor_set(v_reuseFailAlloc_2987_, 5, v_natDef_2961_);
lean_ctor_set(v_reuseFailAlloc_2987_, 6, v_dvds_2962_);
lean_ctor_set(v_reuseFailAlloc_2987_, 7, v___x_2984_);
lean_ctor_set(v_reuseFailAlloc_2987_, 8, v_uppers_2964_);
lean_ctor_set(v_reuseFailAlloc_2987_, 9, v_diseqs_2965_);
lean_ctor_set(v_reuseFailAlloc_2987_, 10, v_elimEqs_2966_);
lean_ctor_set(v_reuseFailAlloc_2987_, 11, v_elimStack_2967_);
lean_ctor_set(v_reuseFailAlloc_2987_, 12, v_occurs_2968_);
lean_ctor_set(v_reuseFailAlloc_2987_, 13, v_assignment_2969_);
lean_ctor_set(v_reuseFailAlloc_2987_, 14, v_nextCnstrId_2970_);
lean_ctor_set(v_reuseFailAlloc_2987_, 15, v_conflict_x3f_2972_);
lean_ctor_set(v_reuseFailAlloc_2987_, 16, v_diseqSplits_2973_);
lean_ctor_set(v_reuseFailAlloc_2987_, 17, v_divMod_2974_);
lean_ctor_set(v_reuseFailAlloc_2987_, 18, v_toIntIds_2975_);
lean_ctor_set(v_reuseFailAlloc_2987_, 19, v_toIntInfos_2976_);
lean_ctor_set(v_reuseFailAlloc_2987_, 20, v_toIntTermMap_2977_);
lean_ctor_set(v_reuseFailAlloc_2987_, 21, v_toIntVarMap_2978_);
lean_ctor_set(v_reuseFailAlloc_2987_, 22, v_nonlinearOccs_2980_);
lean_ctor_set_uint8(v_reuseFailAlloc_2987_, sizeof(void*)*23, v_caseSplits_2971_);
lean_ctor_set_uint8(v_reuseFailAlloc_2987_, sizeof(void*)*23 + 1, v_usedCommRing_2979_);
v___x_2986_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
return v___x_2986_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0___boxed(lean_object* v_a_2989_, lean_object* v_v_2990_, lean_object* v_s_2991_){
_start:
{
lean_object* v_res_2992_; 
v_res_2992_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0(v_a_2989_, v_v_2990_, v_s_2991_);
lean_dec(v_v_2990_);
return v_res_2992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1(lean_object* v_a_2993_, lean_object* v_v_2994_, lean_object* v_s_2995_){
_start:
{
lean_object* v_vars_2996_; lean_object* v_varMap_2997_; lean_object* v_vars_x27_2998_; lean_object* v_varMap_x27_2999_; lean_object* v_natToIntMap_3000_; lean_object* v_natDef_3001_; lean_object* v_dvds_3002_; lean_object* v_lowers_3003_; lean_object* v_uppers_3004_; lean_object* v_diseqs_3005_; lean_object* v_elimEqs_3006_; lean_object* v_elimStack_3007_; lean_object* v_occurs_3008_; lean_object* v_assignment_3009_; lean_object* v_nextCnstrId_3010_; uint8_t v_caseSplits_3011_; lean_object* v_conflict_x3f_3012_; lean_object* v_diseqSplits_3013_; lean_object* v_divMod_3014_; lean_object* v_toIntIds_3015_; lean_object* v_toIntInfos_3016_; lean_object* v_toIntTermMap_3017_; lean_object* v_toIntVarMap_3018_; uint8_t v_usedCommRing_3019_; lean_object* v_nonlinearOccs_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3028_; 
v_vars_2996_ = lean_ctor_get(v_s_2995_, 0);
v_varMap_2997_ = lean_ctor_get(v_s_2995_, 1);
v_vars_x27_2998_ = lean_ctor_get(v_s_2995_, 2);
v_varMap_x27_2999_ = lean_ctor_get(v_s_2995_, 3);
v_natToIntMap_3000_ = lean_ctor_get(v_s_2995_, 4);
v_natDef_3001_ = lean_ctor_get(v_s_2995_, 5);
v_dvds_3002_ = lean_ctor_get(v_s_2995_, 6);
v_lowers_3003_ = lean_ctor_get(v_s_2995_, 7);
v_uppers_3004_ = lean_ctor_get(v_s_2995_, 8);
v_diseqs_3005_ = lean_ctor_get(v_s_2995_, 9);
v_elimEqs_3006_ = lean_ctor_get(v_s_2995_, 10);
v_elimStack_3007_ = lean_ctor_get(v_s_2995_, 11);
v_occurs_3008_ = lean_ctor_get(v_s_2995_, 12);
v_assignment_3009_ = lean_ctor_get(v_s_2995_, 13);
v_nextCnstrId_3010_ = lean_ctor_get(v_s_2995_, 14);
v_caseSplits_3011_ = lean_ctor_get_uint8(v_s_2995_, sizeof(void*)*23);
v_conflict_x3f_3012_ = lean_ctor_get(v_s_2995_, 15);
v_diseqSplits_3013_ = lean_ctor_get(v_s_2995_, 16);
v_divMod_3014_ = lean_ctor_get(v_s_2995_, 17);
v_toIntIds_3015_ = lean_ctor_get(v_s_2995_, 18);
v_toIntInfos_3016_ = lean_ctor_get(v_s_2995_, 19);
v_toIntTermMap_3017_ = lean_ctor_get(v_s_2995_, 20);
v_toIntVarMap_3018_ = lean_ctor_get(v_s_2995_, 21);
v_usedCommRing_3019_ = lean_ctor_get_uint8(v_s_2995_, sizeof(void*)*23 + 1);
v_nonlinearOccs_3020_ = lean_ctor_get(v_s_2995_, 22);
v_isSharedCheck_3028_ = !lean_is_exclusive(v_s_2995_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_3022_ = v_s_2995_;
v_isShared_3023_ = v_isSharedCheck_3028_;
goto v_resetjp_3021_;
}
else
{
lean_inc(v_nonlinearOccs_3020_);
lean_inc(v_toIntVarMap_3018_);
lean_inc(v_toIntTermMap_3017_);
lean_inc(v_toIntInfos_3016_);
lean_inc(v_toIntIds_3015_);
lean_inc(v_divMod_3014_);
lean_inc(v_diseqSplits_3013_);
lean_inc(v_conflict_x3f_3012_);
lean_inc(v_nextCnstrId_3010_);
lean_inc(v_assignment_3009_);
lean_inc(v_occurs_3008_);
lean_inc(v_elimStack_3007_);
lean_inc(v_elimEqs_3006_);
lean_inc(v_diseqs_3005_);
lean_inc(v_uppers_3004_);
lean_inc(v_lowers_3003_);
lean_inc(v_dvds_3002_);
lean_inc(v_natDef_3001_);
lean_inc(v_natToIntMap_3000_);
lean_inc(v_varMap_x27_2999_);
lean_inc(v_vars_x27_2998_);
lean_inc(v_varMap_2997_);
lean_inc(v_vars_2996_);
lean_dec(v_s_2995_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3028_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v___x_3024_; lean_object* v___x_3026_; 
v___x_3024_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(v_a_2993_, v_uppers_3004_, v_v_2994_);
if (v_isShared_3023_ == 0)
{
lean_ctor_set(v___x_3022_, 8, v___x_3024_);
v___x_3026_ = v___x_3022_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v_vars_2996_);
lean_ctor_set(v_reuseFailAlloc_3027_, 1, v_varMap_2997_);
lean_ctor_set(v_reuseFailAlloc_3027_, 2, v_vars_x27_2998_);
lean_ctor_set(v_reuseFailAlloc_3027_, 3, v_varMap_x27_2999_);
lean_ctor_set(v_reuseFailAlloc_3027_, 4, v_natToIntMap_3000_);
lean_ctor_set(v_reuseFailAlloc_3027_, 5, v_natDef_3001_);
lean_ctor_set(v_reuseFailAlloc_3027_, 6, v_dvds_3002_);
lean_ctor_set(v_reuseFailAlloc_3027_, 7, v_lowers_3003_);
lean_ctor_set(v_reuseFailAlloc_3027_, 8, v___x_3024_);
lean_ctor_set(v_reuseFailAlloc_3027_, 9, v_diseqs_3005_);
lean_ctor_set(v_reuseFailAlloc_3027_, 10, v_elimEqs_3006_);
lean_ctor_set(v_reuseFailAlloc_3027_, 11, v_elimStack_3007_);
lean_ctor_set(v_reuseFailAlloc_3027_, 12, v_occurs_3008_);
lean_ctor_set(v_reuseFailAlloc_3027_, 13, v_assignment_3009_);
lean_ctor_set(v_reuseFailAlloc_3027_, 14, v_nextCnstrId_3010_);
lean_ctor_set(v_reuseFailAlloc_3027_, 15, v_conflict_x3f_3012_);
lean_ctor_set(v_reuseFailAlloc_3027_, 16, v_diseqSplits_3013_);
lean_ctor_set(v_reuseFailAlloc_3027_, 17, v_divMod_3014_);
lean_ctor_set(v_reuseFailAlloc_3027_, 18, v_toIntIds_3015_);
lean_ctor_set(v_reuseFailAlloc_3027_, 19, v_toIntInfos_3016_);
lean_ctor_set(v_reuseFailAlloc_3027_, 20, v_toIntTermMap_3017_);
lean_ctor_set(v_reuseFailAlloc_3027_, 21, v_toIntVarMap_3018_);
lean_ctor_set(v_reuseFailAlloc_3027_, 22, v_nonlinearOccs_3020_);
lean_ctor_set_uint8(v_reuseFailAlloc_3027_, sizeof(void*)*23, v_caseSplits_3011_);
lean_ctor_set_uint8(v_reuseFailAlloc_3027_, sizeof(void*)*23 + 1, v_usedCommRing_3019_);
v___x_3026_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
return v___x_3026_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1___boxed(lean_object* v_a_3029_, lean_object* v_v_3030_, lean_object* v_s_3031_){
_start:
{
lean_object* v_res_3032_; 
v_res_3032_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1(v_a_3029_, v_v_3030_, v_s_3031_);
lean_dec(v_v_3030_);
return v_res_3032_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3(void){
_start:
{
lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___x_3040_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2));
v___x_3041_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_3042_ = l_Lean_Name_append(v___x_3041_, v___x_3040_);
return v___x_3042_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6(void){
_start:
{
lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3049_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5));
v___x_3050_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_3051_ = l_Lean_Name_append(v___x_3050_, v___x_3049_);
return v___x_3051_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9(void){
_start:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3058_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__8));
v___x_3059_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_3060_ = l_Lean_Name_append(v___x_3059_, v___x_3058_);
return v___x_3060_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11(void){
_start:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3065_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__10));
v___x_3066_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_3067_ = l_Lean_Name_append(v___x_3066_, v___x_3065_);
return v___x_3067_;
}
}
LEAN_EXPORT lean_object* lean_grind_cutsat_assert_le(lean_object* v_c_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_, lean_object* v_a_3076_, lean_object* v_a_3077_, lean_object* v_a_3078_){
_start:
{
lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3140_; lean_object* v___x_3152_; 
v___x_3152_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_3069_, v_a_3077_);
if (lean_obj_tag(v___x_3152_) == 0)
{
lean_object* v_a_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3289_; 
v_a_3153_ = lean_ctor_get(v___x_3152_, 0);
v_isSharedCheck_3289_ = !lean_is_exclusive(v___x_3152_);
if (v_isSharedCheck_3289_ == 0)
{
v___x_3155_ = v___x_3152_;
v_isShared_3156_ = v_isSharedCheck_3289_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_a_3153_);
lean_dec(v___x_3152_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3289_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
uint8_t v___x_3157_; 
v___x_3157_ = lean_unbox(v_a_3153_);
lean_dec(v_a_3153_);
if (v___x_3157_ == 0)
{
lean_object* v_options_3158_; lean_object* v_inheritedTraceOptions_3159_; uint8_t v_hasTrace_3160_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3167_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3170_; lean_object* v___y_3171_; 
lean_del_object(v___x_3155_);
v_options_3158_ = lean_ctor_get(v_a_3077_, 2);
v_inheritedTraceOptions_3159_ = lean_ctor_get(v_a_3077_, 13);
v_hasTrace_3160_ = lean_ctor_get_uint8(v_options_3158_, sizeof(void*)*1);
if (v_hasTrace_3160_ == 0)
{
v___y_3162_ = v_a_3069_;
v___y_3163_ = v_a_3070_;
v___y_3164_ = v_a_3071_;
v___y_3165_ = v_a_3072_;
v___y_3166_ = v_a_3073_;
v___y_3167_ = v_a_3074_;
v___y_3168_ = v_a_3075_;
v___y_3169_ = v_a_3076_;
v___y_3170_ = v_a_3077_;
v___y_3171_ = v_a_3078_;
goto v___jp_3161_;
}
else
{
lean_object* v___x_3271_; lean_object* v___x_3272_; uint8_t v___x_3273_; 
v___x_3271_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__10));
v___x_3272_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11);
v___x_3273_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3159_, v_options_3158_, v___x_3272_);
if (v___x_3273_ == 0)
{
v___y_3162_ = v_a_3069_;
v___y_3163_ = v_a_3070_;
v___y_3164_ = v_a_3071_;
v___y_3165_ = v_a_3072_;
v___y_3166_ = v_a_3073_;
v___y_3167_ = v_a_3074_;
v___y_3168_ = v_a_3075_;
v___y_3169_ = v_a_3076_;
v___y_3170_ = v_a_3077_;
v___y_3171_ = v_a_3078_;
goto v___jp_3161_;
}
else
{
lean_object* v___x_3274_; 
lean_inc_ref(v_c_3068_);
v___x_3274_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_3068_, v_a_3069_, v_a_3077_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_object* v_a_3275_; lean_object* v___x_3276_; 
v_a_3275_ = lean_ctor_get(v___x_3274_, 0);
lean_inc(v_a_3275_);
lean_dec_ref_known(v___x_3274_, 1);
v___x_3276_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3271_, v_a_3275_, v_a_3075_, v_a_3076_, v_a_3077_, v_a_3078_);
if (lean_obj_tag(v___x_3276_) == 0)
{
lean_dec_ref_known(v___x_3276_, 1);
v___y_3162_ = v_a_3069_;
v___y_3163_ = v_a_3070_;
v___y_3164_ = v_a_3071_;
v___y_3165_ = v_a_3072_;
v___y_3166_ = v_a_3073_;
v___y_3167_ = v_a_3074_;
v___y_3168_ = v_a_3075_;
v___y_3169_ = v_a_3076_;
v___y_3170_ = v_a_3077_;
v___y_3171_ = v_a_3078_;
goto v___jp_3161_;
}
else
{
lean_dec(v_a_3078_);
lean_dec_ref(v_a_3077_);
lean_dec(v_a_3076_);
lean_dec_ref(v_a_3075_);
lean_dec(v_a_3074_);
lean_dec_ref(v_a_3073_);
lean_dec(v_a_3072_);
lean_dec_ref(v_a_3071_);
lean_dec(v_a_3070_);
lean_dec(v_a_3069_);
lean_dec_ref(v_c_3068_);
return v___x_3276_;
}
}
else
{
lean_object* v_a_3277_; lean_object* v___x_3279_; uint8_t v_isShared_3280_; uint8_t v_isSharedCheck_3284_; 
lean_dec(v_a_3078_);
lean_dec_ref(v_a_3077_);
lean_dec(v_a_3076_);
lean_dec_ref(v_a_3075_);
lean_dec(v_a_3074_);
lean_dec_ref(v_a_3073_);
lean_dec(v_a_3072_);
lean_dec_ref(v_a_3071_);
lean_dec(v_a_3070_);
lean_dec(v_a_3069_);
lean_dec_ref(v_c_3068_);
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
v___jp_3161_:
{
lean_object* v___x_3172_; lean_object* v___x_3173_; 
v___x_3172_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_norm(v_c_3068_);
lean_inc_ref(v___y_3170_);
v___x_3173_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts(v___x_3172_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_);
if (lean_obj_tag(v___x_3173_) == 0)
{
lean_object* v_a_3174_; lean_object* v_p_3175_; uint8_t v___x_3176_; 
v_a_3174_ = lean_ctor_get(v___x_3173_, 0);
lean_inc(v_a_3174_);
lean_dec_ref_known(v___x_3173_, 1);
v_p_3175_ = lean_ctor_get(v_a_3174_, 0);
v___x_3176_ = l_Int_Internal_Linear_Poly_isUnsatLe(v_p_3175_);
if (v___x_3176_ == 0)
{
uint8_t v___x_3177_; 
v___x_3177_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(v_a_3174_);
if (v___x_3177_ == 0)
{
if (lean_obj_tag(v_p_3175_) == 1)
{
lean_object* v_k_3178_; lean_object* v_v_3179_; lean_object* v___x_3180_; 
v_k_3178_ = lean_ctor_get(v_p_3175_, 0);
lean_inc(v_k_3178_);
v_v_3179_ = lean_ctor_get(v_p_3175_, 1);
lean_inc(v_v_3179_);
lean_inc(v_a_3174_);
v___x_3180_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq(v_a_3174_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_);
if (lean_obj_tag(v___x_3180_) == 0)
{
lean_object* v_a_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3219_; 
v_a_3181_ = lean_ctor_get(v___x_3180_, 0);
v_isSharedCheck_3219_ = !lean_is_exclusive(v___x_3180_);
if (v_isSharedCheck_3219_ == 0)
{
v___x_3183_ = v___x_3180_;
v_isShared_3184_ = v_isSharedCheck_3219_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_a_3181_);
lean_dec(v___x_3180_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3219_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
uint8_t v___x_3185_; 
v___x_3185_ = lean_unbox(v_a_3181_);
lean_dec(v_a_3181_);
if (v___x_3185_ == 0)
{
lean_object* v___x_3186_; 
lean_del_object(v___x_3183_);
v___x_3186_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(v_a_3174_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec(v___y_3163_);
if (lean_obj_tag(v___x_3186_) == 0)
{
lean_object* v_options_3187_; lean_object* v_a_3188_; lean_object* v_inheritedTraceOptions_3189_; uint8_t v_hasTrace_3190_; lean_object* v___f_3191_; lean_object* v___f_3192_; 
v_options_3187_ = lean_ctor_get(v___y_3170_, 2);
v_a_3188_ = lean_ctor_get(v___x_3186_, 0);
lean_inc_n(v_a_3188_, 3);
lean_dec_ref_known(v___x_3186_, 1);
v_inheritedTraceOptions_3189_ = lean_ctor_get(v___y_3170_, 13);
v_hasTrace_3190_ = lean_ctor_get_uint8(v_options_3187_, sizeof(void*)*1);
lean_inc_n(v_v_3179_, 2);
v___f_3191_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3191_, 0, v_a_3188_);
lean_closure_set(v___f_3191_, 1, v_v_3179_);
v___f_3192_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3192_, 0, v_a_3188_);
lean_closure_set(v___f_3192_, 1, v_v_3179_);
if (v_hasTrace_3190_ == 0)
{
v___y_3111_ = v_v_3179_;
v___y_3112_ = v___f_3191_;
v___y_3113_ = v_k_3178_;
v___y_3114_ = v_a_3188_;
v___y_3115_ = v___f_3192_;
v___y_3116_ = v___y_3162_;
v___y_3117_ = v___y_3168_;
v___y_3118_ = v___y_3169_;
v___y_3119_ = v___y_3170_;
v___y_3120_ = v___y_3171_;
goto v___jp_3110_;
}
else
{
lean_object* v___x_3193_; lean_object* v___x_3194_; uint8_t v___x_3195_; 
v___x_3193_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2));
v___x_3194_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3);
v___x_3195_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3189_, v_options_3187_, v___x_3194_);
if (v___x_3195_ == 0)
{
v___y_3111_ = v_v_3179_;
v___y_3112_ = v___f_3191_;
v___y_3113_ = v_k_3178_;
v___y_3114_ = v_a_3188_;
v___y_3115_ = v___f_3192_;
v___y_3116_ = v___y_3162_;
v___y_3117_ = v___y_3168_;
v___y_3118_ = v___y_3169_;
v___y_3119_ = v___y_3170_;
v___y_3120_ = v___y_3171_;
goto v___jp_3110_;
}
else
{
lean_object* v___x_3196_; 
lean_inc(v_a_3188_);
v___x_3196_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_a_3188_, v___y_3162_, v___y_3170_);
if (lean_obj_tag(v___x_3196_) == 0)
{
lean_object* v_a_3197_; lean_object* v___x_3198_; 
v_a_3197_ = lean_ctor_get(v___x_3196_, 0);
lean_inc(v_a_3197_);
lean_dec_ref_known(v___x_3196_, 1);
v___x_3198_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3193_, v_a_3197_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_);
if (lean_obj_tag(v___x_3198_) == 0)
{
lean_dec_ref_known(v___x_3198_, 1);
v___y_3111_ = v_v_3179_;
v___y_3112_ = v___f_3191_;
v___y_3113_ = v_k_3178_;
v___y_3114_ = v_a_3188_;
v___y_3115_ = v___f_3192_;
v___y_3116_ = v___y_3162_;
v___y_3117_ = v___y_3168_;
v___y_3118_ = v___y_3169_;
v___y_3119_ = v___y_3170_;
v___y_3120_ = v___y_3171_;
goto v___jp_3110_;
}
else
{
lean_dec_ref(v___f_3192_);
lean_dec_ref(v___f_3191_);
lean_dec(v_a_3188_);
lean_dec(v_v_3179_);
lean_dec(v_k_3178_);
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
lean_dec(v___y_3162_);
return v___x_3198_;
}
}
else
{
lean_object* v_a_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3206_; 
lean_dec_ref(v___f_3192_);
lean_dec_ref(v___f_3191_);
lean_dec(v_a_3188_);
lean_dec(v_v_3179_);
lean_dec(v_k_3178_);
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
lean_dec(v___y_3162_);
v_a_3199_ = lean_ctor_get(v___x_3196_, 0);
v_isSharedCheck_3206_ = !lean_is_exclusive(v___x_3196_);
if (v_isSharedCheck_3206_ == 0)
{
v___x_3201_ = v___x_3196_;
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_a_3199_);
lean_dec(v___x_3196_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3204_; 
if (v_isShared_3202_ == 0)
{
v___x_3204_ = v___x_3201_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v_a_3199_);
v___x_3204_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
return v___x_3204_;
}
}
}
}
}
}
else
{
lean_object* v_a_3207_; lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3214_; 
lean_dec(v_v_3179_);
lean_dec(v_k_3178_);
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
lean_dec(v___y_3162_);
v_a_3207_ = lean_ctor_get(v___x_3186_, 0);
v_isSharedCheck_3214_ = !lean_is_exclusive(v___x_3186_);
if (v_isSharedCheck_3214_ == 0)
{
v___x_3209_ = v___x_3186_;
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
else
{
lean_inc(v_a_3207_);
lean_dec(v___x_3186_);
v___x_3209_ = lean_box(0);
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
v_resetjp_3208_:
{
lean_object* v___x_3212_; 
if (v_isShared_3210_ == 0)
{
v___x_3212_ = v___x_3209_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3213_; 
v_reuseFailAlloc_3213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3213_, 0, v_a_3207_);
v___x_3212_ = v_reuseFailAlloc_3213_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
return v___x_3212_;
}
}
}
}
else
{
lean_object* v___x_3215_; lean_object* v___x_3217_; 
lean_dec(v_v_3179_);
lean_dec(v_k_3178_);
lean_dec(v_a_3174_);
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec(v___y_3163_);
lean_dec(v___y_3162_);
v___x_3215_ = lean_box(0);
if (v_isShared_3184_ == 0)
{
lean_ctor_set(v___x_3183_, 0, v___x_3215_);
v___x_3217_ = v___x_3183_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v___x_3215_);
v___x_3217_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
return v___x_3217_;
}
}
}
}
else
{
lean_object* v_a_3220_; lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3227_; 
lean_dec(v_v_3179_);
lean_dec(v_k_3178_);
lean_dec(v_a_3174_);
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec(v___y_3163_);
lean_dec(v___y_3162_);
v_a_3220_ = lean_ctor_get(v___x_3180_, 0);
v_isSharedCheck_3227_ = !lean_is_exclusive(v___x_3180_);
if (v_isSharedCheck_3227_ == 0)
{
v___x_3222_ = v___x_3180_;
v_isShared_3223_ = v_isSharedCheck_3227_;
goto v_resetjp_3221_;
}
else
{
lean_inc(v_a_3220_);
lean_dec(v___x_3180_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3227_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
lean_object* v___x_3225_; 
if (v_isShared_3223_ == 0)
{
v___x_3225_ = v___x_3222_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v_a_3220_);
v___x_3225_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
return v___x_3225_;
}
}
}
}
else
{
lean_object* v___x_3228_; 
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec(v___y_3163_);
v___x_3228_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_a_3174_, v___y_3162_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_);
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
lean_dec(v___y_3162_);
return v___x_3228_;
}
}
else
{
lean_object* v_options_3229_; uint8_t v_hasTrace_3230_; 
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec(v___y_3163_);
v_options_3229_ = lean_ctor_get(v___y_3170_, 2);
v_hasTrace_3230_ = lean_ctor_get_uint8(v_options_3229_, sizeof(void*)*1);
if (v_hasTrace_3230_ == 0)
{
lean_dec(v_a_3174_);
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
lean_dec(v___y_3162_);
goto v___jp_3080_;
}
else
{
lean_object* v_inheritedTraceOptions_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; uint8_t v___x_3234_; 
v_inheritedTraceOptions_3231_ = lean_ctor_get(v___y_3170_, 13);
v___x_3232_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5));
v___x_3233_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6);
v___x_3234_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3231_, v_options_3229_, v___x_3233_);
if (v___x_3234_ == 0)
{
lean_dec(v_a_3174_);
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
lean_dec(v___y_3162_);
goto v___jp_3080_;
}
else
{
lean_object* v___x_3235_; 
v___x_3235_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_a_3174_, v___y_3162_, v___y_3170_);
lean_dec(v___y_3162_);
if (lean_obj_tag(v___x_3235_) == 0)
{
lean_object* v_a_3236_; lean_object* v___x_3237_; 
v_a_3236_ = lean_ctor_get(v___x_3235_, 0);
lean_inc(v_a_3236_);
lean_dec_ref_known(v___x_3235_, 1);
v___x_3237_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3232_, v_a_3236_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_);
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
if (lean_obj_tag(v___x_3237_) == 0)
{
lean_dec_ref_known(v___x_3237_, 1);
goto v___jp_3080_;
}
else
{
return v___x_3237_;
}
}
else
{
lean_object* v_a_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3245_; 
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
v_a_3238_ = lean_ctor_get(v___x_3235_, 0);
v_isSharedCheck_3245_ = !lean_is_exclusive(v___x_3235_);
if (v_isSharedCheck_3245_ == 0)
{
v___x_3240_ = v___x_3235_;
v_isShared_3241_ = v_isSharedCheck_3245_;
goto v_resetjp_3239_;
}
else
{
lean_inc(v_a_3238_);
lean_dec(v___x_3235_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3245_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
lean_object* v___x_3243_; 
if (v_isShared_3241_ == 0)
{
v___x_3243_ = v___x_3240_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v_a_3238_);
v___x_3243_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
return v___x_3243_;
}
}
}
}
}
}
}
else
{
lean_object* v_options_3246_; uint8_t v_hasTrace_3247_; 
v_options_3246_ = lean_ctor_get(v___y_3170_, 2);
v_hasTrace_3247_ = lean_ctor_get_uint8(v_options_3246_, sizeof(void*)*1);
if (v_hasTrace_3247_ == 0)
{
v___y_3130_ = v_a_3174_;
v___y_3131_ = v___y_3162_;
v___y_3132_ = v___y_3163_;
v___y_3133_ = v___y_3164_;
v___y_3134_ = v___y_3165_;
v___y_3135_ = v___y_3166_;
v___y_3136_ = v___y_3167_;
v___y_3137_ = v___y_3168_;
v___y_3138_ = v___y_3169_;
v___y_3139_ = v___y_3170_;
v___y_3140_ = v___y_3171_;
goto v___jp_3129_;
}
else
{
lean_object* v_inheritedTraceOptions_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; uint8_t v___x_3251_; 
v_inheritedTraceOptions_3248_ = lean_ctor_get(v___y_3170_, 13);
v___x_3249_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__8));
v___x_3250_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9);
v___x_3251_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3248_, v_options_3246_, v___x_3250_);
if (v___x_3251_ == 0)
{
v___y_3130_ = v_a_3174_;
v___y_3131_ = v___y_3162_;
v___y_3132_ = v___y_3163_;
v___y_3133_ = v___y_3164_;
v___y_3134_ = v___y_3165_;
v___y_3135_ = v___y_3166_;
v___y_3136_ = v___y_3167_;
v___y_3137_ = v___y_3168_;
v___y_3138_ = v___y_3169_;
v___y_3139_ = v___y_3170_;
v___y_3140_ = v___y_3171_;
goto v___jp_3129_;
}
else
{
lean_object* v___x_3252_; 
lean_inc(v_a_3174_);
v___x_3252_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_a_3174_, v___y_3162_, v___y_3170_);
if (lean_obj_tag(v___x_3252_) == 0)
{
lean_object* v_a_3253_; lean_object* v___x_3254_; 
v_a_3253_ = lean_ctor_get(v___x_3252_, 0);
lean_inc(v_a_3253_);
lean_dec_ref_known(v___x_3252_, 1);
v___x_3254_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3249_, v_a_3253_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_);
if (lean_obj_tag(v___x_3254_) == 0)
{
lean_dec_ref_known(v___x_3254_, 1);
v___y_3130_ = v_a_3174_;
v___y_3131_ = v___y_3162_;
v___y_3132_ = v___y_3163_;
v___y_3133_ = v___y_3164_;
v___y_3134_ = v___y_3165_;
v___y_3135_ = v___y_3166_;
v___y_3136_ = v___y_3167_;
v___y_3137_ = v___y_3168_;
v___y_3138_ = v___y_3169_;
v___y_3139_ = v___y_3170_;
v___y_3140_ = v___y_3171_;
goto v___jp_3129_;
}
else
{
lean_dec(v_a_3174_);
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec(v___y_3163_);
lean_dec(v___y_3162_);
return v___x_3254_;
}
}
else
{
lean_object* v_a_3255_; lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3262_; 
lean_dec(v_a_3174_);
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec(v___y_3163_);
lean_dec(v___y_3162_);
v_a_3255_ = lean_ctor_get(v___x_3252_, 0);
v_isSharedCheck_3262_ = !lean_is_exclusive(v___x_3252_);
if (v_isSharedCheck_3262_ == 0)
{
v___x_3257_ = v___x_3252_;
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
else
{
lean_inc(v_a_3255_);
lean_dec(v___x_3252_);
v___x_3257_ = lean_box(0);
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
v_resetjp_3256_:
{
lean_object* v___x_3260_; 
if (v_isShared_3258_ == 0)
{
v___x_3260_ = v___x_3257_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_a_3255_);
v___x_3260_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
return v___x_3260_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3263_; lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3270_; 
lean_dec(v___y_3171_);
lean_dec_ref(v___y_3170_);
lean_dec(v___y_3169_);
lean_dec_ref(v___y_3168_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec(v___y_3163_);
lean_dec(v___y_3162_);
v_a_3263_ = lean_ctor_get(v___x_3173_, 0);
v_isSharedCheck_3270_ = !lean_is_exclusive(v___x_3173_);
if (v_isSharedCheck_3270_ == 0)
{
v___x_3265_ = v___x_3173_;
v_isShared_3266_ = v_isSharedCheck_3270_;
goto v_resetjp_3264_;
}
else
{
lean_inc(v_a_3263_);
lean_dec(v___x_3173_);
v___x_3265_ = lean_box(0);
v_isShared_3266_ = v_isSharedCheck_3270_;
goto v_resetjp_3264_;
}
v_resetjp_3264_:
{
lean_object* v___x_3268_; 
if (v_isShared_3266_ == 0)
{
v___x_3268_ = v___x_3265_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3269_; 
v_reuseFailAlloc_3269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3269_, 0, v_a_3263_);
v___x_3268_ = v_reuseFailAlloc_3269_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
return v___x_3268_;
}
}
}
}
}
else
{
lean_object* v___x_3285_; lean_object* v___x_3287_; 
lean_dec(v_a_3078_);
lean_dec_ref(v_a_3077_);
lean_dec(v_a_3076_);
lean_dec_ref(v_a_3075_);
lean_dec(v_a_3074_);
lean_dec_ref(v_a_3073_);
lean_dec(v_a_3072_);
lean_dec_ref(v_a_3071_);
lean_dec(v_a_3070_);
lean_dec(v_a_3069_);
lean_dec_ref(v_c_3068_);
v___x_3285_ = lean_box(0);
if (v_isShared_3156_ == 0)
{
lean_ctor_set(v___x_3155_, 0, v___x_3285_);
v___x_3287_ = v___x_3155_;
goto v_reusejp_3286_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v___x_3285_);
v___x_3287_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3286_;
}
v_reusejp_3286_:
{
return v___x_3287_;
}
}
}
}
else
{
lean_object* v_a_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3297_; 
lean_dec(v_a_3078_);
lean_dec_ref(v_a_3077_);
lean_dec(v_a_3076_);
lean_dec_ref(v_a_3075_);
lean_dec(v_a_3074_);
lean_dec_ref(v_a_3073_);
lean_dec(v_a_3072_);
lean_dec_ref(v_a_3071_);
lean_dec(v_a_3070_);
lean_dec(v_a_3069_);
lean_dec_ref(v_c_3068_);
v_a_3290_ = lean_ctor_get(v___x_3152_, 0);
v_isSharedCheck_3297_ = !lean_is_exclusive(v___x_3152_);
if (v_isSharedCheck_3297_ == 0)
{
v___x_3292_ = v___x_3152_;
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_a_3290_);
lean_dec(v___x_3152_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3297_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
lean_object* v___x_3295_; 
if (v_isShared_3293_ == 0)
{
v___x_3295_ = v___x_3292_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v_a_3290_);
v___x_3295_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
return v___x_3295_;
}
}
}
v___jp_3080_:
{
lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3081_ = lean_box(0);
v___x_3082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3081_);
return v___x_3082_;
}
v___jp_3083_:
{
lean_object* v___x_3088_; 
v___x_3088_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(v___y_3085_, v___y_3086_, v___y_3087_);
lean_dec_ref(v___y_3087_);
if (lean_obj_tag(v___x_3088_) == 0)
{
lean_object* v_a_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3101_; 
v_a_3089_ = lean_ctor_get(v___x_3088_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_3088_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3091_ = v___x_3088_;
v_isShared_3092_ = v_isSharedCheck_3101_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_a_3089_);
lean_dec(v___x_3088_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3101_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
uint8_t v___x_3093_; uint8_t v___x_3094_; uint8_t v___x_3095_; 
v___x_3093_ = 0;
v___x_3094_ = lean_unbox(v_a_3089_);
lean_dec(v_a_3089_);
v___x_3095_ = l_Lean_instBEqLBool_beq(v___x_3094_, v___x_3093_);
if (v___x_3095_ == 0)
{
lean_object* v___x_3096_; lean_object* v___x_3098_; 
lean_dec(v___y_3086_);
lean_dec(v___y_3084_);
v___x_3096_ = lean_box(0);
if (v_isShared_3092_ == 0)
{
lean_ctor_set(v___x_3091_, 0, v___x_3096_);
v___x_3098_ = v___x_3091_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v___x_3096_);
v___x_3098_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
return v___x_3098_;
}
}
else
{
lean_object* v___x_3100_; 
lean_del_object(v___x_3091_);
v___x_3100_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v___y_3084_, v___y_3086_);
lean_dec(v___y_3086_);
return v___x_3100_;
}
}
}
else
{
lean_object* v_a_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3109_; 
lean_dec(v___y_3086_);
lean_dec(v___y_3084_);
v_a_3102_ = lean_ctor_get(v___x_3088_, 0);
v_isSharedCheck_3109_ = !lean_is_exclusive(v___x_3088_);
if (v_isSharedCheck_3109_ == 0)
{
v___x_3104_ = v___x_3088_;
v_isShared_3105_ = v_isSharedCheck_3109_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_a_3102_);
lean_dec(v___x_3088_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3109_;
goto v_resetjp_3103_;
}
v_resetjp_3103_:
{
lean_object* v___x_3107_; 
if (v_isShared_3105_ == 0)
{
v___x_3107_ = v___x_3104_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v_a_3102_);
v___x_3107_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
return v___x_3107_;
}
}
}
}
v___jp_3110_:
{
lean_object* v_p_3121_; lean_object* v___x_3122_; 
v_p_3121_ = lean_ctor_get(v___y_3114_, 0);
lean_inc_ref(v_p_3121_);
v___x_3122_ = l_Int_Internal_Linear_Poly_updateOccs___redArg(v_p_3121_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_);
lean_dec(v___y_3120_);
lean_dec(v___y_3118_);
lean_dec_ref(v___y_3117_);
if (lean_obj_tag(v___x_3122_) == 0)
{
lean_object* v___x_3123_; uint8_t v___x_3124_; 
lean_dec_ref_known(v___x_3122_, 1);
v___x_3123_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9);
v___x_3124_ = lean_int_dec_lt(v___y_3113_, v___x_3123_);
lean_dec(v___y_3113_);
if (v___x_3124_ == 0)
{
lean_object* v___x_3125_; lean_object* v___x_3126_; 
lean_dec_ref(v___y_3112_);
v___x_3125_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_3126_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3125_, v___y_3115_, v___y_3116_);
if (lean_obj_tag(v___x_3126_) == 0)
{
lean_dec_ref_known(v___x_3126_, 1);
v___y_3084_ = v___y_3111_;
v___y_3085_ = v___y_3114_;
v___y_3086_ = v___y_3116_;
v___y_3087_ = v___y_3119_;
goto v___jp_3083_;
}
else
{
lean_dec_ref(v___y_3119_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3111_);
return v___x_3126_;
}
}
else
{
lean_object* v___x_3127_; lean_object* v___x_3128_; 
lean_dec_ref(v___y_3115_);
v___x_3127_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_3128_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3127_, v___y_3112_, v___y_3116_);
if (lean_obj_tag(v___x_3128_) == 0)
{
lean_dec_ref_known(v___x_3128_, 1);
v___y_3084_ = v___y_3111_;
v___y_3085_ = v___y_3114_;
v___y_3086_ = v___y_3116_;
v___y_3087_ = v___y_3119_;
goto v___jp_3083_;
}
else
{
lean_dec_ref(v___y_3119_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3111_);
return v___x_3128_;
}
}
}
else
{
lean_dec_ref(v___y_3119_);
lean_dec(v___y_3116_);
lean_dec_ref(v___y_3115_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec(v___y_3111_);
return v___x_3122_;
}
}
v___jp_3129_:
{
lean_object* v___x_3141_; lean_object* v___x_3142_; 
v___x_3141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3141_, 0, v___y_3130_);
v___x_3142_ = l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(v___x_3141_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_);
lean_dec(v___y_3140_);
lean_dec_ref(v___y_3139_);
lean_dec(v___y_3138_);
lean_dec_ref(v___y_3137_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3132_);
lean_dec(v___y_3131_);
if (lean_obj_tag(v___x_3142_) == 0)
{
lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3150_; 
v_isSharedCheck_3150_ = !lean_is_exclusive(v___x_3142_);
if (v_isSharedCheck_3150_ == 0)
{
lean_object* v_unused_3151_; 
v_unused_3151_ = lean_ctor_get(v___x_3142_, 0);
lean_dec(v_unused_3151_);
v___x_3144_ = v___x_3142_;
v_isShared_3145_ = v_isSharedCheck_3150_;
goto v_resetjp_3143_;
}
else
{
lean_dec(v___x_3142_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3150_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v___x_3146_; lean_object* v___x_3148_; 
v___x_3146_ = lean_box(0);
if (v_isShared_3145_ == 0)
{
lean_ctor_set(v___x_3144_, 0, v___x_3146_);
v___x_3148_ = v___x_3144_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v___x_3146_);
v___x_3148_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
return v___x_3148_;
}
}
}
else
{
return v___x_3142_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___boxed(lean_object* v_c_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_){
_start:
{
lean_object* v_res_3310_; 
v_res_3310_ = lean_grind_cutsat_assert_le(v_c_3298_, v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_);
return v_res_3310_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1(void){
_start:
{
lean_object* v___x_3312_; lean_object* v___x_3313_; 
v___x_3312_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__0));
v___x_3313_ = l_Lean_stringToMessageData(v___x_3312_);
return v___x_3313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(lean_object* v_e_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_, lean_object* v_a_3318_, lean_object* v_a_3319_, lean_object* v_a_3320_){
_start:
{
lean_object* v___x_3322_; 
v___x_3322_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_3315_);
if (lean_obj_tag(v___x_3322_) == 0)
{
lean_object* v_a_3323_; lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3336_; 
v_a_3323_ = lean_ctor_get(v___x_3322_, 0);
v_isSharedCheck_3336_ = !lean_is_exclusive(v___x_3322_);
if (v_isSharedCheck_3336_ == 0)
{
v___x_3325_ = v___x_3322_;
v_isShared_3326_ = v_isSharedCheck_3336_;
goto v_resetjp_3324_;
}
else
{
lean_inc(v_a_3323_);
lean_dec(v___x_3322_);
v___x_3325_ = lean_box(0);
v_isShared_3326_ = v_isSharedCheck_3336_;
goto v_resetjp_3324_;
}
v_resetjp_3324_:
{
uint8_t v_verbose_3327_; 
v_verbose_3327_ = lean_ctor_get_uint8(v_a_3323_, 0);
lean_dec(v_a_3323_);
if (v_verbose_3327_ == 0)
{
lean_object* v___x_3328_; lean_object* v___x_3330_; 
lean_dec_ref(v_e_3314_);
v___x_3328_ = lean_box(0);
if (v_isShared_3326_ == 0)
{
lean_ctor_set(v___x_3325_, 0, v___x_3328_);
v___x_3330_ = v___x_3325_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3331_; 
v_reuseFailAlloc_3331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3331_, 0, v___x_3328_);
v___x_3330_ = v_reuseFailAlloc_3331_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
return v___x_3330_;
}
}
else
{
lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
lean_del_object(v___x_3325_);
v___x_3332_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1);
v___x_3333_ = l_Lean_indentExpr(v_e_3314_);
v___x_3334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3332_);
lean_ctor_set(v___x_3334_, 1, v___x_3333_);
v___x_3335_ = l_Lean_Meta_Sym_reportIssue(v___x_3334_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_, v_a_3320_);
return v___x_3335_;
}
}
}
else
{
lean_object* v_a_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3344_; 
lean_dec_ref(v_e_3314_);
v_a_3337_ = lean_ctor_get(v___x_3322_, 0);
v_isSharedCheck_3344_ = !lean_is_exclusive(v___x_3322_);
if (v_isSharedCheck_3344_ == 0)
{
v___x_3339_ = v___x_3322_;
v_isShared_3340_ = v_isSharedCheck_3344_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_a_3337_);
lean_dec(v___x_3322_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___boxed(lean_object* v_e_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_){
_start:
{
lean_object* v_res_3353_; 
v_res_3353_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(v_e_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_);
lean_dec(v_a_3351_);
lean_dec_ref(v_a_3350_);
lean_dec(v_a_3349_);
lean_dec_ref(v_a_3348_);
lean_dec(v_a_3347_);
lean_dec_ref(v_a_3346_);
return v_res_3353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized(lean_object* v_e_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_){
_start:
{
lean_object* v___x_3366_; 
v___x_3366_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(v_e_3354_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_);
return v___x_3366_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___boxed(lean_object* v_e_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_){
_start:
{
lean_object* v_res_3379_; 
v_res_3379_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized(v_e_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_);
lean_dec(v_a_3377_);
lean_dec_ref(v_a_3376_);
lean_dec(v_a_3375_);
lean_dec_ref(v_a_3374_);
lean_dec(v_a_3373_);
lean_dec_ref(v_a_3372_);
lean_dec(v_a_3371_);
lean_dec_ref(v_a_3370_);
lean_dec(v_a_3369_);
lean_dec(v_a_3368_);
return v_res_3379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f(lean_object* v_e_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_){
_start:
{
lean_object* v___x_3397_; 
lean_inc_ref(v_e_3385_);
v___x_3397_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3385_, v_a_3393_);
if (lean_obj_tag(v___x_3397_) == 0)
{
lean_object* v_a_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3513_; 
v_a_3398_ = lean_ctor_get(v___x_3397_, 0);
v_isSharedCheck_3513_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3513_ == 0)
{
v___x_3400_ = v___x_3397_;
v_isShared_3401_ = v_isSharedCheck_3513_;
goto v_resetjp_3399_;
}
else
{
lean_inc(v_a_3398_);
lean_dec(v___x_3397_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3513_;
goto v_resetjp_3399_;
}
v_resetjp_3399_:
{
lean_object* v___x_3407_; uint8_t v___x_3408_; 
v___x_3407_ = l_Lean_Expr_cleanupAnnotations(v_a_3398_);
v___x_3408_ = l_Lean_Expr_isApp(v___x_3407_);
if (v___x_3408_ == 0)
{
lean_dec_ref(v___x_3407_);
lean_dec_ref(v_e_3385_);
goto v___jp_3402_;
}
else
{
lean_object* v_arg_3409_; lean_object* v___x_3410_; uint8_t v___x_3411_; 
v_arg_3409_ = lean_ctor_get(v___x_3407_, 1);
lean_inc_ref(v_arg_3409_);
v___x_3410_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3407_);
v___x_3411_ = l_Lean_Expr_isApp(v___x_3410_);
if (v___x_3411_ == 0)
{
lean_dec_ref(v___x_3410_);
lean_dec_ref(v_arg_3409_);
lean_dec_ref(v_e_3385_);
goto v___jp_3402_;
}
else
{
lean_object* v_arg_3412_; lean_object* v___x_3413_; uint8_t v___x_3414_; 
v_arg_3412_ = lean_ctor_get(v___x_3410_, 1);
lean_inc_ref(v_arg_3412_);
v___x_3413_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3410_);
v___x_3414_ = l_Lean_Expr_isApp(v___x_3413_);
if (v___x_3414_ == 0)
{
lean_dec_ref(v___x_3413_);
lean_dec_ref(v_arg_3412_);
lean_dec_ref(v_arg_3409_);
lean_dec_ref(v_e_3385_);
goto v___jp_3402_;
}
else
{
lean_object* v_arg_3415_; lean_object* v___x_3416_; uint8_t v___x_3417_; 
v_arg_3415_ = lean_ctor_get(v___x_3413_, 1);
lean_inc_ref(v_arg_3415_);
v___x_3416_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3413_);
v___x_3417_ = l_Lean_Expr_isApp(v___x_3416_);
if (v___x_3417_ == 0)
{
lean_dec_ref(v___x_3416_);
lean_dec_ref(v_arg_3415_);
lean_dec_ref(v_arg_3412_);
lean_dec_ref(v_arg_3409_);
lean_dec_ref(v_e_3385_);
goto v___jp_3402_;
}
else
{
lean_object* v___x_3418_; lean_object* v___x_3419_; uint8_t v___x_3420_; 
v___x_3418_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3416_);
v___x_3419_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2));
v___x_3420_ = l_Lean_Expr_isConstOf(v___x_3418_, v___x_3419_);
lean_dec_ref(v___x_3418_);
if (v___x_3420_ == 0)
{
lean_dec_ref(v_arg_3415_);
lean_dec_ref(v_arg_3412_);
lean_dec_ref(v_arg_3409_);
lean_dec_ref(v_e_3385_);
goto v___jp_3402_;
}
else
{
lean_object* v___x_3421_; 
lean_del_object(v___x_3400_);
v___x_3421_ = l_Lean_Meta_Structural_isInstLEInt___redArg(v_arg_3415_, v_a_3393_);
if (lean_obj_tag(v___x_3421_) == 0)
{
lean_object* v_a_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3504_; 
v_a_3422_ = lean_ctor_get(v___x_3421_, 0);
v_isSharedCheck_3504_ = !lean_is_exclusive(v___x_3421_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3424_ = v___x_3421_;
v_isShared_3425_ = v_isSharedCheck_3504_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_a_3422_);
lean_dec(v___x_3421_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3504_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
uint8_t v___x_3426_; 
v___x_3426_ = lean_unbox(v_a_3422_);
lean_dec(v_a_3422_);
if (v___x_3426_ == 0)
{
lean_object* v___x_3427_; lean_object* v___x_3429_; 
lean_dec_ref(v_arg_3412_);
lean_dec_ref(v_arg_3409_);
lean_dec_ref(v_e_3385_);
v___x_3427_ = lean_box(0);
if (v_isShared_3425_ == 0)
{
lean_ctor_set(v___x_3424_, 0, v___x_3427_);
v___x_3429_ = v___x_3424_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v___x_3427_);
v___x_3429_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
return v___x_3429_;
}
}
else
{
lean_object* v___x_3431_; 
lean_del_object(v___x_3424_);
v___x_3431_ = l_Lean_Meta_getIntValue_x3f(v_arg_3409_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_);
if (lean_obj_tag(v___x_3431_) == 0)
{
lean_object* v_a_3432_; 
v_a_3432_ = lean_ctor_get(v___x_3431_, 0);
lean_inc(v_a_3432_);
lean_dec_ref_known(v___x_3431_, 1);
if (lean_obj_tag(v_a_3432_) == 1)
{
lean_object* v_val_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3477_; 
v_val_3433_ = lean_ctor_get(v_a_3432_, 0);
v_isSharedCheck_3477_ = !lean_is_exclusive(v_a_3432_);
if (v_isSharedCheck_3477_ == 0)
{
v___x_3435_ = v_a_3432_;
v_isShared_3436_ = v_isSharedCheck_3477_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_val_3433_);
lean_dec(v_a_3432_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3477_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v___x_3437_; uint8_t v___x_3438_; 
v___x_3437_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9);
v___x_3438_ = lean_int_dec_eq(v_val_3433_, v___x_3437_);
lean_dec(v_val_3433_);
if (v___x_3438_ == 0)
{
lean_object* v___x_3439_; 
lean_del_object(v___x_3435_);
lean_dec_ref(v_arg_3412_);
v___x_3439_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(v_e_3385_, v_a_3390_, v_a_3391_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_);
if (lean_obj_tag(v___x_3439_) == 0)
{
lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3447_; 
v_isSharedCheck_3447_ = !lean_is_exclusive(v___x_3439_);
if (v_isSharedCheck_3447_ == 0)
{
lean_object* v_unused_3448_; 
v_unused_3448_ = lean_ctor_get(v___x_3439_, 0);
lean_dec(v_unused_3448_);
v___x_3441_ = v___x_3439_;
v_isShared_3442_ = v_isSharedCheck_3447_;
goto v_resetjp_3440_;
}
else
{
lean_dec(v___x_3439_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3447_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
lean_object* v___x_3443_; lean_object* v___x_3445_; 
v___x_3443_ = lean_box(0);
if (v_isShared_3442_ == 0)
{
lean_ctor_set(v___x_3441_, 0, v___x_3443_);
v___x_3445_ = v___x_3441_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3446_; 
v_reuseFailAlloc_3446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3446_, 0, v___x_3443_);
v___x_3445_ = v_reuseFailAlloc_3446_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
return v___x_3445_;
}
}
}
else
{
lean_object* v_a_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3456_; 
v_a_3449_ = lean_ctor_get(v___x_3439_, 0);
v_isSharedCheck_3456_ = !lean_is_exclusive(v___x_3439_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3451_ = v___x_3439_;
v_isShared_3452_ = v_isSharedCheck_3456_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_a_3449_);
lean_dec(v___x_3439_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3456_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
lean_object* v___x_3454_; 
if (v_isShared_3452_ == 0)
{
v___x_3454_ = v___x_3451_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v_a_3449_);
v___x_3454_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
return v___x_3454_;
}
}
}
}
else
{
lean_object* v___x_3457_; 
lean_dec_ref(v_e_3385_);
v___x_3457_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(v_arg_3412_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_, v_a_3390_, v_a_3391_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_);
if (lean_obj_tag(v___x_3457_) == 0)
{
lean_object* v_a_3458_; lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3468_; 
v_a_3458_ = lean_ctor_get(v___x_3457_, 0);
v_isSharedCheck_3468_ = !lean_is_exclusive(v___x_3457_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3460_ = v___x_3457_;
v_isShared_3461_ = v_isSharedCheck_3468_;
goto v_resetjp_3459_;
}
else
{
lean_inc(v_a_3458_);
lean_dec(v___x_3457_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3468_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
lean_object* v___x_3463_; 
if (v_isShared_3436_ == 0)
{
lean_ctor_set(v___x_3435_, 0, v_a_3458_);
v___x_3463_ = v___x_3435_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_a_3458_);
v___x_3463_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
lean_object* v___x_3465_; 
if (v_isShared_3461_ == 0)
{
lean_ctor_set(v___x_3460_, 0, v___x_3463_);
v___x_3465_ = v___x_3460_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3466_; 
v_reuseFailAlloc_3466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3466_, 0, v___x_3463_);
v___x_3465_ = v_reuseFailAlloc_3466_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
return v___x_3465_;
}
}
}
}
else
{
lean_object* v_a_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3476_; 
lean_del_object(v___x_3435_);
v_a_3469_ = lean_ctor_get(v___x_3457_, 0);
v_isSharedCheck_3476_ = !lean_is_exclusive(v___x_3457_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3471_ = v___x_3457_;
v_isShared_3472_ = v_isSharedCheck_3476_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_a_3469_);
lean_dec(v___x_3457_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3476_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
lean_object* v___x_3474_; 
if (v_isShared_3472_ == 0)
{
v___x_3474_ = v___x_3471_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v_a_3469_);
v___x_3474_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
return v___x_3474_;
}
}
}
}
}
}
else
{
lean_object* v___x_3478_; 
lean_dec(v_a_3432_);
lean_dec_ref(v_arg_3412_);
v___x_3478_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(v_e_3385_, v_a_3390_, v_a_3391_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_);
if (lean_obj_tag(v___x_3478_) == 0)
{
lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3486_; 
v_isSharedCheck_3486_ = !lean_is_exclusive(v___x_3478_);
if (v_isSharedCheck_3486_ == 0)
{
lean_object* v_unused_3487_; 
v_unused_3487_ = lean_ctor_get(v___x_3478_, 0);
lean_dec(v_unused_3487_);
v___x_3480_ = v___x_3478_;
v_isShared_3481_ = v_isSharedCheck_3486_;
goto v_resetjp_3479_;
}
else
{
lean_dec(v___x_3478_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3486_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
lean_object* v___x_3482_; lean_object* v___x_3484_; 
v___x_3482_ = lean_box(0);
if (v_isShared_3481_ == 0)
{
lean_ctor_set(v___x_3480_, 0, v___x_3482_);
v___x_3484_ = v___x_3480_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v___x_3482_);
v___x_3484_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
return v___x_3484_;
}
}
}
else
{
lean_object* v_a_3488_; lean_object* v___x_3490_; uint8_t v_isShared_3491_; uint8_t v_isSharedCheck_3495_; 
v_a_3488_ = lean_ctor_get(v___x_3478_, 0);
v_isSharedCheck_3495_ = !lean_is_exclusive(v___x_3478_);
if (v_isSharedCheck_3495_ == 0)
{
v___x_3490_ = v___x_3478_;
v_isShared_3491_ = v_isSharedCheck_3495_;
goto v_resetjp_3489_;
}
else
{
lean_inc(v_a_3488_);
lean_dec(v___x_3478_);
v___x_3490_ = lean_box(0);
v_isShared_3491_ = v_isSharedCheck_3495_;
goto v_resetjp_3489_;
}
v_resetjp_3489_:
{
lean_object* v___x_3493_; 
if (v_isShared_3491_ == 0)
{
v___x_3493_ = v___x_3490_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v_a_3488_);
v___x_3493_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
return v___x_3493_;
}
}
}
}
}
else
{
lean_object* v_a_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3503_; 
lean_dec_ref(v_arg_3412_);
lean_dec_ref(v_e_3385_);
v_a_3496_ = lean_ctor_get(v___x_3431_, 0);
v_isSharedCheck_3503_ = !lean_is_exclusive(v___x_3431_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3498_ = v___x_3431_;
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_a_3496_);
lean_dec(v___x_3431_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v___x_3501_; 
if (v_isShared_3499_ == 0)
{
v___x_3501_ = v___x_3498_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_a_3496_);
v___x_3501_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
return v___x_3501_;
}
}
}
}
}
}
else
{
lean_object* v_a_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3512_; 
lean_dec_ref(v_arg_3412_);
lean_dec_ref(v_arg_3409_);
lean_dec_ref(v_e_3385_);
v_a_3505_ = lean_ctor_get(v___x_3421_, 0);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3421_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3507_ = v___x_3421_;
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_a_3505_);
lean_dec(v___x_3421_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___x_3510_; 
if (v_isShared_3508_ == 0)
{
v___x_3510_ = v___x_3507_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_a_3505_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
return v___x_3510_;
}
}
}
}
}
}
}
}
v___jp_3402_:
{
lean_object* v___x_3403_; lean_object* v___x_3405_; 
v___x_3403_ = lean_box(0);
if (v_isShared_3401_ == 0)
{
lean_ctor_set(v___x_3400_, 0, v___x_3403_);
v___x_3405_ = v___x_3400_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v___x_3403_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
}
else
{
lean_object* v_a_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3521_; 
lean_dec_ref(v_e_3385_);
v_a_3514_ = lean_ctor_get(v___x_3397_, 0);
v_isSharedCheck_3521_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3521_ == 0)
{
v___x_3516_ = v___x_3397_;
v_isShared_3517_ = v_isSharedCheck_3521_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_a_3514_);
lean_dec(v___x_3397_);
v___x_3516_ = lean_box(0);
v_isShared_3517_ = v_isSharedCheck_3521_;
goto v_resetjp_3515_;
}
v_resetjp_3515_:
{
lean_object* v___x_3519_; 
if (v_isShared_3517_ == 0)
{
v___x_3519_ = v___x_3516_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3520_; 
v_reuseFailAlloc_3520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3520_, 0, v_a_3514_);
v___x_3519_ = v_reuseFailAlloc_3520_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
return v___x_3519_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___boxed(lean_object* v_e_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_){
_start:
{
lean_object* v_res_3534_; 
v_res_3534_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f(v_e_3522_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_);
lean_dec(v_a_3532_);
lean_dec_ref(v_a_3531_);
lean_dec(v_a_3530_);
lean_dec_ref(v_a_3529_);
lean_dec(v_a_3528_);
lean_dec_ref(v_a_3527_);
lean_dec(v_a_3526_);
lean_dec_ref(v_a_3525_);
lean_dec(v_a_3524_);
lean_dec(v_a_3523_);
return v_res_3534_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(lean_object* v_c_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_){
_start:
{
lean_object* v_p_3547_; lean_object* v___x_3548_; 
v_p_3547_ = lean_ctor_get(v_c_3535_, 0);
lean_inc_ref(v_p_3547_);
v___x_3548_ = l_Int_Internal_Linear_Poly_normCommRing_x3f(v_p_3547_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_, v_a_3543_, v_a_3544_, v_a_3545_);
if (lean_obj_tag(v___x_3548_) == 0)
{
lean_object* v_a_3549_; 
v_a_3549_ = lean_ctor_get(v___x_3548_, 0);
lean_inc(v_a_3549_);
lean_dec_ref_known(v___x_3548_, 1);
if (lean_obj_tag(v_a_3549_) == 1)
{
lean_object* v_val_3550_; lean_object* v_snd_3551_; lean_object* v_fst_3552_; lean_object* v_fst_3553_; lean_object* v_snd_3554_; lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3563_; 
v_val_3550_ = lean_ctor_get(v_a_3549_, 0);
lean_inc(v_val_3550_);
lean_dec_ref_known(v_a_3549_, 1);
v_snd_3551_ = lean_ctor_get(v_val_3550_, 1);
lean_inc(v_snd_3551_);
v_fst_3552_ = lean_ctor_get(v_val_3550_, 0);
lean_inc(v_fst_3552_);
lean_dec(v_val_3550_);
v_fst_3553_ = lean_ctor_get(v_snd_3551_, 0);
v_snd_3554_ = lean_ctor_get(v_snd_3551_, 1);
v_isSharedCheck_3563_ = !lean_is_exclusive(v_snd_3551_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3556_ = v_snd_3551_;
v_isShared_3557_ = v_isSharedCheck_3563_;
goto v_resetjp_3555_;
}
else
{
lean_inc(v_snd_3554_);
lean_inc(v_fst_3553_);
lean_dec(v_snd_3551_);
v___x_3556_ = lean_box(0);
v_isShared_3557_ = v_isSharedCheck_3563_;
goto v_resetjp_3555_;
}
v_resetjp_3555_:
{
lean_object* v___x_3558_; lean_object* v___x_3560_; 
v___x_3558_ = lean_alloc_ctor(17, 3, 0);
lean_ctor_set(v___x_3558_, 0, v_c_3535_);
lean_ctor_set(v___x_3558_, 1, v_fst_3552_);
lean_ctor_set(v___x_3558_, 2, v_fst_3553_);
if (v_isShared_3557_ == 0)
{
lean_ctor_set(v___x_3556_, 1, v___x_3558_);
lean_ctor_set(v___x_3556_, 0, v_snd_3554_);
v___x_3560_ = v___x_3556_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v_snd_3554_);
lean_ctor_set(v_reuseFailAlloc_3562_, 1, v___x_3558_);
v___x_3560_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
lean_object* v___x_3561_; 
lean_inc(v_a_3545_);
lean_inc_ref(v_a_3544_);
lean_inc(v_a_3543_);
lean_inc_ref(v_a_3542_);
lean_inc(v_a_3541_);
lean_inc_ref(v_a_3540_);
lean_inc(v_a_3539_);
lean_inc_ref(v_a_3538_);
lean_inc(v_a_3537_);
lean_inc(v_a_3536_);
v___x_3561_ = lean_grind_cutsat_assert_le(v___x_3560_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_, v_a_3543_, v_a_3544_, v_a_3545_);
return v___x_3561_;
}
}
}
else
{
lean_object* v___x_3564_; 
lean_dec(v_a_3549_);
lean_inc(v_a_3545_);
lean_inc_ref(v_a_3544_);
lean_inc(v_a_3543_);
lean_inc_ref(v_a_3542_);
lean_inc(v_a_3541_);
lean_inc_ref(v_a_3540_);
lean_inc(v_a_3539_);
lean_inc_ref(v_a_3538_);
lean_inc(v_a_3537_);
lean_inc(v_a_3536_);
v___x_3564_ = lean_grind_cutsat_assert_le(v_c_3535_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_, v_a_3543_, v_a_3544_, v_a_3545_);
return v___x_3564_;
}
}
else
{
lean_object* v_a_3565_; lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3572_; 
lean_dec_ref(v_c_3535_);
v_a_3565_ = lean_ctor_get(v___x_3548_, 0);
v_isSharedCheck_3572_ = !lean_is_exclusive(v___x_3548_);
if (v_isSharedCheck_3572_ == 0)
{
v___x_3567_ = v___x_3548_;
v_isShared_3568_ = v_isSharedCheck_3572_;
goto v_resetjp_3566_;
}
else
{
lean_inc(v_a_3565_);
lean_dec(v___x_3548_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3572_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
lean_object* v___x_3570_; 
if (v_isShared_3568_ == 0)
{
v___x_3570_ = v___x_3567_;
goto v_reusejp_3569_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v_a_3565_);
v___x_3570_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3569_;
}
v_reusejp_3569_:
{
return v___x_3570_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore___boxed(lean_object* v_c_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_){
_start:
{
lean_object* v_res_3585_; 
v_res_3585_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v_c_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_);
lean_dec(v_a_3583_);
lean_dec_ref(v_a_3582_);
lean_dec(v_a_3581_);
lean_dec_ref(v_a_3580_);
lean_dec(v_a_3579_);
lean_dec_ref(v_a_3578_);
lean_dec(v_a_3577_);
lean_dec_ref(v_a_3576_);
lean_dec(v_a_3575_);
lean_dec(v_a_3574_);
return v_res_3585_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0(void){
_start:
{
lean_object* v___x_3586_; lean_object* v___x_3587_; 
v___x_3586_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
v___x_3587_ = lean_int_neg(v___x_3586_);
return v___x_3587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe(lean_object* v_e_3588_, uint8_t v_eqTrue_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_){
_start:
{
lean_object* v___x_3601_; 
lean_inc_ref(v_e_3588_);
v___x_3601_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f(v_e_3588_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_);
if (lean_obj_tag(v___x_3601_) == 0)
{
lean_object* v_a_3602_; lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3628_; 
v_a_3602_ = lean_ctor_get(v___x_3601_, 0);
v_isSharedCheck_3628_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_3628_ == 0)
{
v___x_3604_ = v___x_3601_;
v_isShared_3605_ = v_isSharedCheck_3628_;
goto v_resetjp_3603_;
}
else
{
lean_inc(v_a_3602_);
lean_dec(v___x_3601_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3628_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
if (lean_obj_tag(v_a_3602_) == 1)
{
lean_del_object(v___x_3604_);
if (v_eqTrue_3589_ == 0)
{
lean_object* v_val_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; 
v_val_3606_ = lean_ctor_get(v_a_3602_, 0);
lean_inc_n(v_val_3606_, 2);
lean_dec_ref_known(v_a_3602_, 1);
v___x_3607_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
v___x_3608_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0);
v___x_3609_ = l_Int_Internal_Linear_Poly_mul(v_val_3606_, v___x_3608_);
v___x_3610_ = l_Int_Internal_Linear_Poly_addConst(v___x_3609_, v___x_3607_);
v___x_3611_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3611_, 0, v_e_3588_);
lean_ctor_set(v___x_3611_, 1, v_val_3606_);
v___x_3612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3612_, 0, v___x_3610_);
lean_ctor_set(v___x_3612_, 1, v___x_3611_);
v___x_3613_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v___x_3612_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_);
return v___x_3613_;
}
else
{
lean_object* v_val_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3623_; 
v_val_3614_ = lean_ctor_get(v_a_3602_, 0);
v_isSharedCheck_3623_ = !lean_is_exclusive(v_a_3602_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3616_ = v_a_3602_;
v_isShared_3617_ = v_isSharedCheck_3623_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_val_3614_);
lean_dec(v_a_3602_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3623_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
lean_object* v___x_3619_; 
if (v_isShared_3617_ == 0)
{
lean_ctor_set_tag(v___x_3616_, 0);
lean_ctor_set(v___x_3616_, 0, v_e_3588_);
v___x_3619_ = v___x_3616_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v_e_3588_);
v___x_3619_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
lean_object* v___x_3620_; lean_object* v___x_3621_; 
v___x_3620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3620_, 0, v_val_3614_);
lean_ctor_set(v___x_3620_, 1, v___x_3619_);
v___x_3621_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v___x_3620_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_);
return v___x_3621_;
}
}
}
}
else
{
lean_object* v___x_3624_; lean_object* v___x_3626_; 
lean_dec(v_a_3602_);
lean_dec_ref(v_e_3588_);
v___x_3624_ = lean_box(0);
if (v_isShared_3605_ == 0)
{
lean_ctor_set(v___x_3604_, 0, v___x_3624_);
v___x_3626_ = v___x_3604_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v___x_3624_);
v___x_3626_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
return v___x_3626_;
}
}
}
}
else
{
lean_object* v_a_3629_; lean_object* v___x_3631_; uint8_t v_isShared_3632_; uint8_t v_isSharedCheck_3636_; 
lean_dec_ref(v_e_3588_);
v_a_3629_ = lean_ctor_get(v___x_3601_, 0);
v_isSharedCheck_3636_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_3636_ == 0)
{
v___x_3631_ = v___x_3601_;
v_isShared_3632_ = v_isSharedCheck_3636_;
goto v_resetjp_3630_;
}
else
{
lean_inc(v_a_3629_);
lean_dec(v___x_3601_);
v___x_3631_ = lean_box(0);
v_isShared_3632_ = v_isSharedCheck_3636_;
goto v_resetjp_3630_;
}
v_resetjp_3630_:
{
lean_object* v___x_3634_; 
if (v_isShared_3632_ == 0)
{
v___x_3634_ = v___x_3631_;
goto v_reusejp_3633_;
}
else
{
lean_object* v_reuseFailAlloc_3635_; 
v_reuseFailAlloc_3635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3635_, 0, v_a_3629_);
v___x_3634_ = v_reuseFailAlloc_3635_;
goto v_reusejp_3633_;
}
v_reusejp_3633_:
{
return v___x_3634_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___boxed(lean_object* v_e_3637_, lean_object* v_eqTrue_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_, lean_object* v_a_3648_, lean_object* v_a_3649_){
_start:
{
uint8_t v_eqTrue_boxed_3650_; lean_object* v_res_3651_; 
v_eqTrue_boxed_3650_ = lean_unbox(v_eqTrue_3638_);
v_res_3651_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe(v_e_3637_, v_eqTrue_boxed_3650_, v_a_3639_, v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_, v_a_3645_, v_a_3646_, v_a_3647_, v_a_3648_);
lean_dec(v_a_3648_);
lean_dec_ref(v_a_3647_);
lean_dec(v_a_3646_);
lean_dec_ref(v_a_3645_);
lean_dec(v_a_3644_);
lean_dec_ref(v_a_3643_);
lean_dec(v_a_3642_);
lean_dec_ref(v_a_3641_);
lean_dec(v_a_3640_);
lean_dec(v_a_3639_);
return v_res_3651_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0(void){
_start:
{
lean_object* v___x_3652_; lean_object* v___x_3653_; 
v___x_3652_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
v___x_3653_ = l_Lean_mkIntLit(v___x_3652_);
return v___x_3653_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5(void){
_start:
{
lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; 
v___x_3661_ = lean_box(0);
v___x_3662_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__4));
v___x_3663_ = l_Lean_mkConst(v___x_3662_, v___x_3661_);
return v___x_3663_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8(void){
_start:
{
lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; 
v___x_3669_ = lean_box(0);
v___x_3670_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__7));
v___x_3671_ = l_Lean_mkConst(v___x_3670_, v___x_3669_);
return v___x_3671_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe(lean_object* v_e_3672_, uint8_t v_eqTrue_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_, lean_object* v_a_3680_, lean_object* v_a_3681_, lean_object* v_a_3682_, lean_object* v_a_3683_){
_start:
{
lean_object* v___y_3686_; lean_object* v___y_3687_; lean_object* v_fst_3688_; lean_object* v_snd_3689_; lean_object* v___x_3718_; uint8_t v___x_3719_; 
lean_inc_ref(v_e_3672_);
v___x_3718_ = l_Lean_Expr_cleanupAnnotations(v_e_3672_);
v___x_3719_ = l_Lean_Expr_isApp(v___x_3718_);
if (v___x_3719_ == 0)
{
lean_dec_ref(v___x_3718_);
lean_dec_ref(v_e_3672_);
goto v___jp_3715_;
}
else
{
lean_object* v_arg_3720_; lean_object* v___x_3721_; uint8_t v___x_3722_; 
v_arg_3720_ = lean_ctor_get(v___x_3718_, 1);
lean_inc_ref(v_arg_3720_);
v___x_3721_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3718_);
v___x_3722_ = l_Lean_Expr_isApp(v___x_3721_);
if (v___x_3722_ == 0)
{
lean_dec_ref(v___x_3721_);
lean_dec_ref(v_arg_3720_);
lean_dec_ref(v_e_3672_);
goto v___jp_3715_;
}
else
{
lean_object* v_arg_3723_; lean_object* v___y_3725_; lean_object* v___x_3763_; uint8_t v___x_3764_; 
v_arg_3723_ = lean_ctor_get(v___x_3721_, 1);
lean_inc_ref(v_arg_3723_);
v___x_3763_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3721_);
v___x_3764_ = l_Lean_Expr_isApp(v___x_3763_);
if (v___x_3764_ == 0)
{
lean_dec_ref(v___x_3763_);
lean_dec_ref(v_arg_3723_);
lean_dec_ref(v_arg_3720_);
lean_dec_ref(v_e_3672_);
goto v___jp_3715_;
}
else
{
lean_object* v___x_3765_; uint8_t v___x_3766_; 
v___x_3765_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3763_);
v___x_3766_ = l_Lean_Expr_isApp(v___x_3765_);
if (v___x_3766_ == 0)
{
lean_dec_ref(v___x_3765_);
lean_dec_ref(v_arg_3723_);
lean_dec_ref(v_arg_3720_);
lean_dec_ref(v_e_3672_);
goto v___jp_3715_;
}
else
{
lean_object* v___x_3767_; lean_object* v___x_3768_; uint8_t v___x_3769_; 
v___x_3767_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3765_);
v___x_3768_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2));
v___x_3769_ = l_Lean_Expr_isConstOf(v___x_3767_, v___x_3768_);
lean_dec_ref(v___x_3767_);
if (v___x_3769_ == 0)
{
lean_dec_ref(v_arg_3723_);
lean_dec_ref(v_arg_3720_);
lean_dec_ref(v_e_3672_);
goto v___jp_3715_;
}
else
{
if (v_eqTrue_3673_ == 0)
{
lean_object* v___x_3770_; 
v___x_3770_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5);
v___y_3725_ = v___x_3770_;
goto v___jp_3724_;
}
else
{
lean_object* v___x_3771_; 
v___x_3771_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8);
v___y_3725_ = v___x_3771_;
goto v___jp_3724_;
}
}
}
}
v___jp_3724_:
{
lean_object* v___x_3726_; 
v___x_3726_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_3672_, v_a_3674_);
if (lean_obj_tag(v___x_3726_) == 0)
{
lean_object* v_a_3727_; lean_object* v___x_3728_; 
v_a_3727_ = lean_ctor_get(v___x_3726_, 0);
lean_inc(v_a_3727_);
lean_dec_ref_known(v___x_3726_, 1);
lean_inc_ref(v_arg_3723_);
v___x_3728_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_3723_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_, v_a_3680_, v_a_3681_, v_a_3682_, v_a_3683_);
if (lean_obj_tag(v___x_3728_) == 0)
{
lean_object* v_a_3729_; lean_object* v_fst_3730_; lean_object* v_snd_3731_; lean_object* v___x_3732_; 
v_a_3729_ = lean_ctor_get(v___x_3728_, 0);
lean_inc(v_a_3729_);
lean_dec_ref_known(v___x_3728_, 1);
v_fst_3730_ = lean_ctor_get(v_a_3729_, 0);
lean_inc(v_fst_3730_);
v_snd_3731_ = lean_ctor_get(v_a_3729_, 1);
lean_inc(v_snd_3731_);
lean_dec(v_a_3729_);
lean_inc_ref(v_arg_3720_);
v___x_3732_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_3720_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_, v_a_3680_, v_a_3681_, v_a_3682_, v_a_3683_);
if (lean_obj_tag(v___x_3732_) == 0)
{
lean_object* v_a_3733_; lean_object* v_fst_3734_; lean_object* v_snd_3735_; lean_object* v___x_3736_; 
v_a_3733_ = lean_ctor_get(v___x_3732_, 0);
lean_inc(v_a_3733_);
lean_dec_ref_known(v___x_3732_, 1);
v_fst_3734_ = lean_ctor_get(v_a_3733_, 0);
lean_inc_n(v_fst_3734_, 2);
v_snd_3735_ = lean_ctor_get(v_a_3733_, 1);
lean_inc(v_snd_3735_);
lean_dec(v_a_3733_);
lean_inc(v_fst_3730_);
lean_inc_ref(v___y_3725_);
v___x_3736_ = l_Lean_mkApp6(v___y_3725_, v_arg_3723_, v_arg_3720_, v_fst_3730_, v_fst_3734_, v_snd_3731_, v_snd_3735_);
if (v_eqTrue_3673_ == 0)
{
lean_object* v___x_3737_; lean_object* v___x_3738_; 
v___x_3737_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0);
v___x_3738_ = l_Lean_mkIntAdd(v_fst_3734_, v___x_3737_);
v___y_3686_ = v___x_3736_;
v___y_3687_ = v_a_3727_;
v_fst_3688_ = v___x_3738_;
v_snd_3689_ = v_fst_3730_;
goto v___jp_3685_;
}
else
{
v___y_3686_ = v___x_3736_;
v___y_3687_ = v_a_3727_;
v_fst_3688_ = v_fst_3730_;
v_snd_3689_ = v_fst_3734_;
goto v___jp_3685_;
}
}
else
{
lean_object* v_a_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3746_; 
lean_dec(v_snd_3731_);
lean_dec(v_fst_3730_);
lean_dec(v_a_3727_);
lean_dec_ref(v_arg_3723_);
lean_dec_ref(v_arg_3720_);
lean_dec_ref(v_e_3672_);
v_a_3739_ = lean_ctor_get(v___x_3732_, 0);
v_isSharedCheck_3746_ = !lean_is_exclusive(v___x_3732_);
if (v_isSharedCheck_3746_ == 0)
{
v___x_3741_ = v___x_3732_;
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_a_3739_);
lean_dec(v___x_3732_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v___x_3744_; 
if (v_isShared_3742_ == 0)
{
v___x_3744_ = v___x_3741_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v_a_3739_);
v___x_3744_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
return v___x_3744_;
}
}
}
}
else
{
lean_object* v_a_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3754_; 
lean_dec(v_a_3727_);
lean_dec_ref(v_arg_3723_);
lean_dec_ref(v_arg_3720_);
lean_dec_ref(v_e_3672_);
v_a_3747_ = lean_ctor_get(v___x_3728_, 0);
v_isSharedCheck_3754_ = !lean_is_exclusive(v___x_3728_);
if (v_isSharedCheck_3754_ == 0)
{
v___x_3749_ = v___x_3728_;
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_a_3747_);
lean_dec(v___x_3728_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v___x_3752_; 
if (v_isShared_3750_ == 0)
{
v___x_3752_ = v___x_3749_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v_a_3747_);
v___x_3752_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
return v___x_3752_;
}
}
}
}
else
{
lean_object* v_a_3755_; lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3762_; 
lean_dec_ref(v_arg_3723_);
lean_dec_ref(v_arg_3720_);
lean_dec_ref(v_e_3672_);
v_a_3755_ = lean_ctor_get(v___x_3726_, 0);
v_isSharedCheck_3762_ = !lean_is_exclusive(v___x_3726_);
if (v_isSharedCheck_3762_ == 0)
{
v___x_3757_ = v___x_3726_;
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
else
{
lean_inc(v_a_3755_);
lean_dec(v___x_3726_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
lean_object* v___x_3760_; 
if (v_isShared_3758_ == 0)
{
v___x_3760_ = v___x_3757_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v_a_3755_);
v___x_3760_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
return v___x_3760_;
}
}
}
}
}
}
v___jp_3685_:
{
lean_object* v___x_3690_; 
lean_inc(v___y_3687_);
v___x_3690_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_3688_, v___y_3687_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_, v_a_3680_, v_a_3681_, v_a_3682_, v_a_3683_);
if (lean_obj_tag(v___x_3690_) == 0)
{
lean_object* v_a_3691_; lean_object* v___x_3692_; 
v_a_3691_ = lean_ctor_get(v___x_3690_, 0);
lean_inc(v_a_3691_);
lean_dec_ref_known(v___x_3690_, 1);
v___x_3692_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_snd_3689_, v___y_3687_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_, v_a_3680_, v_a_3681_, v_a_3682_, v_a_3683_);
if (lean_obj_tag(v___x_3692_) == 0)
{
lean_object* v_a_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; lean_object* v___x_3698_; 
v_a_3693_ = lean_ctor_get(v___x_3692_, 0);
lean_inc_n(v_a_3693_, 2);
lean_dec_ref_known(v___x_3692_, 1);
lean_inc(v_a_3691_);
v___x_3694_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3694_, 0, v_a_3691_);
lean_ctor_set(v___x_3694_, 1, v_a_3693_);
v___x_3695_ = l_Int_Internal_Linear_Expr_norm(v___x_3694_);
lean_dec_ref_known(v___x_3694_, 2);
v___x_3696_ = lean_alloc_ctor(2, 4, 1);
lean_ctor_set(v___x_3696_, 0, v_e_3672_);
lean_ctor_set(v___x_3696_, 1, v___y_3686_);
lean_ctor_set(v___x_3696_, 2, v_a_3691_);
lean_ctor_set(v___x_3696_, 3, v_a_3693_);
lean_ctor_set_uint8(v___x_3696_, sizeof(void*)*4, v_eqTrue_3673_);
v___x_3697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3697_, 0, v___x_3695_);
lean_ctor_set(v___x_3697_, 1, v___x_3696_);
v___x_3698_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v___x_3697_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_, v_a_3680_, v_a_3681_, v_a_3682_, v_a_3683_);
return v___x_3698_;
}
else
{
lean_object* v_a_3699_; lean_object* v___x_3701_; uint8_t v_isShared_3702_; uint8_t v_isSharedCheck_3706_; 
lean_dec(v_a_3691_);
lean_dec_ref(v___y_3686_);
lean_dec_ref(v_e_3672_);
v_a_3699_ = lean_ctor_get(v___x_3692_, 0);
v_isSharedCheck_3706_ = !lean_is_exclusive(v___x_3692_);
if (v_isSharedCheck_3706_ == 0)
{
v___x_3701_ = v___x_3692_;
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
else
{
lean_inc(v_a_3699_);
lean_dec(v___x_3692_);
v___x_3701_ = lean_box(0);
v_isShared_3702_ = v_isSharedCheck_3706_;
goto v_resetjp_3700_;
}
v_resetjp_3700_:
{
lean_object* v___x_3704_; 
if (v_isShared_3702_ == 0)
{
v___x_3704_ = v___x_3701_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v_a_3699_);
v___x_3704_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
return v___x_3704_;
}
}
}
}
else
{
lean_object* v_a_3707_; lean_object* v___x_3709_; uint8_t v_isShared_3710_; uint8_t v_isSharedCheck_3714_; 
lean_dec_ref(v_snd_3689_);
lean_dec(v___y_3687_);
lean_dec_ref(v___y_3686_);
lean_dec_ref(v_e_3672_);
v_a_3707_ = lean_ctor_get(v___x_3690_, 0);
v_isSharedCheck_3714_ = !lean_is_exclusive(v___x_3690_);
if (v_isSharedCheck_3714_ == 0)
{
v___x_3709_ = v___x_3690_;
v_isShared_3710_ = v_isSharedCheck_3714_;
goto v_resetjp_3708_;
}
else
{
lean_inc(v_a_3707_);
lean_dec(v___x_3690_);
v___x_3709_ = lean_box(0);
v_isShared_3710_ = v_isSharedCheck_3714_;
goto v_resetjp_3708_;
}
v_resetjp_3708_:
{
lean_object* v___x_3712_; 
if (v_isShared_3710_ == 0)
{
v___x_3712_ = v___x_3709_;
goto v_reusejp_3711_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v_a_3707_);
v___x_3712_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3711_;
}
v_reusejp_3711_:
{
return v___x_3712_;
}
}
}
}
v___jp_3715_:
{
lean_object* v___x_3716_; lean_object* v___x_3717_; 
v___x_3716_ = lean_box(0);
v___x_3717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3716_);
return v___x_3717_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___boxed(lean_object* v_e_3772_, lean_object* v_eqTrue_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_, lean_object* v_a_3783_, lean_object* v_a_3784_){
_start:
{
uint8_t v_eqTrue_boxed_3785_; lean_object* v_res_3786_; 
v_eqTrue_boxed_3785_ = lean_unbox(v_eqTrue_3773_);
v_res_3786_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe(v_e_3772_, v_eqTrue_boxed_3785_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_, v_a_3782_, v_a_3783_);
lean_dec(v_a_3783_);
lean_dec_ref(v_a_3782_);
lean_dec(v_a_3781_);
lean_dec_ref(v_a_3780_);
lean_dec(v_a_3779_);
lean_dec_ref(v_a_3778_);
lean_dec(v_a_3777_);
lean_dec_ref(v_a_3776_);
lean_dec(v_a_3775_);
lean_dec(v_a_3774_);
return v_res_3786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe(lean_object* v_e_3787_, uint8_t v_eqTrue_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_, lean_object* v_a_3792_, lean_object* v_a_3793_, lean_object* v_a_3794_, lean_object* v_a_3795_, lean_object* v_a_3796_, lean_object* v_a_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_){
_start:
{
lean_object* v___y_3805_; lean_object* v___y_3806_; lean_object* v___y_3807_; lean_object* v___y_3808_; lean_object* v___y_3809_; lean_object* v___y_3810_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3814_; lean_object* v___y_3815_; lean_object* v___y_3816_; lean_object* v_fst_3817_; lean_object* v_snd_3818_; lean_object* v_____x_3845_; lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v___y_3850_; lean_object* v___y_3851_; lean_object* v___y_3852_; lean_object* v___y_3853_; lean_object* v___y_3854_; lean_object* v___y_3855_; lean_object* v___y_3856_; 
if (v_eqTrue_3788_ == 0)
{
lean_object* v___x_3910_; 
v___x_3910_ = l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLE_x3f___redArg(v_a_3789_, v_a_3790_, v_a_3795_, v_a_3796_, v_a_3797_, v_a_3798_, v_a_3799_);
if (lean_obj_tag(v___x_3910_) == 0)
{
lean_object* v_a_3911_; 
v_a_3911_ = lean_ctor_get(v___x_3910_, 0);
lean_inc(v_a_3911_);
lean_dec_ref_known(v___x_3910_, 1);
v_____x_3845_ = v_a_3911_;
v___y_3846_ = v_a_3789_;
v___y_3847_ = v_a_3790_;
v___y_3848_ = v_a_3791_;
v___y_3849_ = v_a_3792_;
v___y_3850_ = v_a_3793_;
v___y_3851_ = v_a_3794_;
v___y_3852_ = v_a_3795_;
v___y_3853_ = v_a_3796_;
v___y_3854_ = v_a_3797_;
v___y_3855_ = v_a_3798_;
v___y_3856_ = v_a_3799_;
goto v___jp_3844_;
}
else
{
lean_object* v_a_3912_; lean_object* v___x_3914_; uint8_t v_isShared_3915_; uint8_t v_isSharedCheck_3919_; 
lean_dec_ref(v_e_3787_);
v_a_3912_ = lean_ctor_get(v___x_3910_, 0);
v_isSharedCheck_3919_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_3919_ == 0)
{
v___x_3914_ = v___x_3910_;
v_isShared_3915_ = v_isSharedCheck_3919_;
goto v_resetjp_3913_;
}
else
{
lean_inc(v_a_3912_);
lean_dec(v___x_3910_);
v___x_3914_ = lean_box(0);
v_isShared_3915_ = v_isSharedCheck_3919_;
goto v_resetjp_3913_;
}
v_resetjp_3913_:
{
lean_object* v___x_3917_; 
if (v_isShared_3915_ == 0)
{
v___x_3917_ = v___x_3914_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v_a_3912_);
v___x_3917_ = v_reuseFailAlloc_3918_;
goto v_reusejp_3916_;
}
v_reusejp_3916_:
{
return v___x_3917_;
}
}
}
}
else
{
lean_object* v___x_3920_; 
v___x_3920_ = l_Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f___redArg(v_a_3789_, v_a_3790_, v_a_3795_, v_a_3796_, v_a_3797_, v_a_3798_, v_a_3799_);
if (lean_obj_tag(v___x_3920_) == 0)
{
lean_object* v_a_3921_; 
v_a_3921_ = lean_ctor_get(v___x_3920_, 0);
lean_inc(v_a_3921_);
lean_dec_ref_known(v___x_3920_, 1);
v_____x_3845_ = v_a_3921_;
v___y_3846_ = v_a_3789_;
v___y_3847_ = v_a_3790_;
v___y_3848_ = v_a_3791_;
v___y_3849_ = v_a_3792_;
v___y_3850_ = v_a_3793_;
v___y_3851_ = v_a_3794_;
v___y_3852_ = v_a_3795_;
v___y_3853_ = v_a_3796_;
v___y_3854_ = v_a_3797_;
v___y_3855_ = v_a_3798_;
v___y_3856_ = v_a_3799_;
goto v___jp_3844_;
}
else
{
lean_object* v_a_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3929_; 
lean_dec_ref(v_e_3787_);
v_a_3922_ = lean_ctor_get(v___x_3920_, 0);
v_isSharedCheck_3929_ = !lean_is_exclusive(v___x_3920_);
if (v_isSharedCheck_3929_ == 0)
{
v___x_3924_ = v___x_3920_;
v_isShared_3925_ = v_isSharedCheck_3929_;
goto v_resetjp_3923_;
}
else
{
lean_inc(v_a_3922_);
lean_dec(v___x_3920_);
v___x_3924_ = lean_box(0);
v_isShared_3925_ = v_isSharedCheck_3929_;
goto v_resetjp_3923_;
}
v_resetjp_3923_:
{
lean_object* v___x_3927_; 
if (v_isShared_3925_ == 0)
{
v___x_3927_ = v___x_3924_;
goto v_reusejp_3926_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v_a_3922_);
v___x_3927_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3926_;
}
v_reusejp_3926_:
{
return v___x_3927_;
}
}
}
}
v___jp_3801_:
{
lean_object* v___x_3802_; lean_object* v___x_3803_; 
v___x_3802_ = lean_box(0);
v___x_3803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3803_, 0, v___x_3802_);
return v___x_3803_;
}
v___jp_3804_:
{
lean_object* v___x_3819_; 
lean_inc(v___y_3815_);
v___x_3819_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_3817_, v___y_3815_, v___y_3812_, v___y_3809_, v___y_3806_, v___y_3808_, v___y_3807_, v___y_3813_, v___y_3811_, v___y_3814_, v___y_3805_, v___y_3816_);
if (lean_obj_tag(v___x_3819_) == 0)
{
lean_object* v_a_3820_; lean_object* v___x_3821_; 
v_a_3820_ = lean_ctor_get(v___x_3819_, 0);
lean_inc(v_a_3820_);
lean_dec_ref_known(v___x_3819_, 1);
v___x_3821_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_snd_3818_, v___y_3815_, v___y_3812_, v___y_3809_, v___y_3806_, v___y_3808_, v___y_3807_, v___y_3813_, v___y_3811_, v___y_3814_, v___y_3805_, v___y_3816_);
if (lean_obj_tag(v___x_3821_) == 0)
{
lean_object* v_a_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; 
v_a_3822_ = lean_ctor_get(v___x_3821_, 0);
lean_inc_n(v_a_3822_, 2);
lean_dec_ref_known(v___x_3821_, 1);
lean_inc(v_a_3820_);
v___x_3823_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3823_, 0, v_a_3820_);
lean_ctor_set(v___x_3823_, 1, v_a_3822_);
v___x_3824_ = l_Int_Internal_Linear_Expr_norm(v___x_3823_);
lean_dec_ref_known(v___x_3823_, 2);
v___x_3825_ = lean_alloc_ctor(2, 4, 1);
lean_ctor_set(v___x_3825_, 0, v_e_3787_);
lean_ctor_set(v___x_3825_, 1, v___y_3810_);
lean_ctor_set(v___x_3825_, 2, v_a_3820_);
lean_ctor_set(v___x_3825_, 3, v_a_3822_);
lean_ctor_set_uint8(v___x_3825_, sizeof(void*)*4, v_eqTrue_3788_);
v___x_3826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3826_, 0, v___x_3824_);
lean_ctor_set(v___x_3826_, 1, v___x_3825_);
v___x_3827_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v___x_3826_, v___y_3812_, v___y_3809_, v___y_3806_, v___y_3808_, v___y_3807_, v___y_3813_, v___y_3811_, v___y_3814_, v___y_3805_, v___y_3816_);
return v___x_3827_;
}
else
{
lean_object* v_a_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3835_; 
lean_dec(v_a_3820_);
lean_dec_ref(v___y_3810_);
lean_dec_ref(v_e_3787_);
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
lean_dec_ref(v_snd_3818_);
lean_dec(v___y_3815_);
lean_dec_ref(v___y_3810_);
lean_dec_ref(v_e_3787_);
v_a_3836_ = lean_ctor_get(v___x_3819_, 0);
v_isSharedCheck_3843_ = !lean_is_exclusive(v___x_3819_);
if (v_isSharedCheck_3843_ == 0)
{
v___x_3838_ = v___x_3819_;
v_isShared_3839_ = v_isSharedCheck_3843_;
goto v_resetjp_3837_;
}
else
{
lean_inc(v_a_3836_);
lean_dec(v___x_3819_);
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
v___jp_3844_:
{
if (lean_obj_tag(v_____x_3845_) == 1)
{
lean_object* v_val_3857_; lean_object* v___x_3858_; uint8_t v___x_3859_; 
v_val_3857_ = lean_ctor_get(v_____x_3845_, 0);
lean_inc(v_val_3857_);
lean_dec_ref_known(v_____x_3845_, 1);
lean_inc_ref(v_e_3787_);
v___x_3858_ = l_Lean_Expr_cleanupAnnotations(v_e_3787_);
v___x_3859_ = l_Lean_Expr_isApp(v___x_3858_);
if (v___x_3859_ == 0)
{
lean_dec_ref(v___x_3858_);
lean_dec(v_val_3857_);
lean_dec_ref(v_e_3787_);
goto v___jp_3801_;
}
else
{
lean_object* v_arg_3860_; lean_object* v___x_3861_; uint8_t v___x_3862_; 
v_arg_3860_ = lean_ctor_get(v___x_3858_, 1);
lean_inc_ref(v_arg_3860_);
v___x_3861_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3858_);
v___x_3862_ = l_Lean_Expr_isApp(v___x_3861_);
if (v___x_3862_ == 0)
{
lean_dec_ref(v___x_3861_);
lean_dec_ref(v_arg_3860_);
lean_dec(v_val_3857_);
lean_dec_ref(v_e_3787_);
goto v___jp_3801_;
}
else
{
lean_object* v_arg_3863_; lean_object* v___x_3864_; uint8_t v___x_3865_; 
v_arg_3863_ = lean_ctor_get(v___x_3861_, 1);
lean_inc_ref(v_arg_3863_);
v___x_3864_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3861_);
v___x_3865_ = l_Lean_Expr_isApp(v___x_3864_);
if (v___x_3865_ == 0)
{
lean_dec_ref(v___x_3864_);
lean_dec_ref(v_arg_3863_);
lean_dec_ref(v_arg_3860_);
lean_dec(v_val_3857_);
lean_dec_ref(v_e_3787_);
goto v___jp_3801_;
}
else
{
lean_object* v___x_3866_; uint8_t v___x_3867_; 
v___x_3866_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3864_);
v___x_3867_ = l_Lean_Expr_isApp(v___x_3866_);
if (v___x_3867_ == 0)
{
lean_dec_ref(v___x_3866_);
lean_dec_ref(v_arg_3863_);
lean_dec_ref(v_arg_3860_);
lean_dec(v_val_3857_);
lean_dec_ref(v_e_3787_);
goto v___jp_3801_;
}
else
{
lean_object* v___x_3868_; lean_object* v___x_3869_; uint8_t v___x_3870_; 
v___x_3868_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3866_);
v___x_3869_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2));
v___x_3870_ = l_Lean_Expr_isConstOf(v___x_3868_, v___x_3869_);
lean_dec_ref(v___x_3868_);
if (v___x_3870_ == 0)
{
lean_dec_ref(v_arg_3863_);
lean_dec_ref(v_arg_3860_);
lean_dec(v_val_3857_);
lean_dec_ref(v_e_3787_);
goto v___jp_3801_;
}
else
{
lean_object* v___x_3871_; 
v___x_3871_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_3787_, v___y_3847_);
if (lean_obj_tag(v___x_3871_) == 0)
{
lean_object* v_a_3872_; lean_object* v___x_3873_; 
v_a_3872_ = lean_ctor_get(v___x_3871_, 0);
lean_inc(v_a_3872_);
lean_dec_ref_known(v___x_3871_, 1);
lean_inc_ref(v_arg_3863_);
v___x_3873_ = l_Lean_Meta_Grind_Arith_Cutsat_toInt(v_arg_3863_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_);
if (lean_obj_tag(v___x_3873_) == 0)
{
lean_object* v_a_3874_; lean_object* v_fst_3875_; lean_object* v_snd_3876_; lean_object* v___x_3877_; 
v_a_3874_ = lean_ctor_get(v___x_3873_, 0);
lean_inc(v_a_3874_);
lean_dec_ref_known(v___x_3873_, 1);
v_fst_3875_ = lean_ctor_get(v_a_3874_, 0);
lean_inc(v_fst_3875_);
v_snd_3876_ = lean_ctor_get(v_a_3874_, 1);
lean_inc(v_snd_3876_);
lean_dec(v_a_3874_);
lean_inc_ref(v_arg_3860_);
v___x_3877_ = l_Lean_Meta_Grind_Arith_Cutsat_toInt(v_arg_3860_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_, v___y_3856_);
if (lean_obj_tag(v___x_3877_) == 0)
{
lean_object* v_a_3878_; lean_object* v_fst_3879_; lean_object* v_snd_3880_; lean_object* v___x_3881_; 
v_a_3878_ = lean_ctor_get(v___x_3877_, 0);
lean_inc(v_a_3878_);
lean_dec_ref_known(v___x_3877_, 1);
v_fst_3879_ = lean_ctor_get(v_a_3878_, 0);
lean_inc_n(v_fst_3879_, 2);
v_snd_3880_ = lean_ctor_get(v_a_3878_, 1);
lean_inc(v_snd_3880_);
lean_dec(v_a_3878_);
lean_inc(v_fst_3875_);
v___x_3881_ = l_Lean_mkApp6(v_val_3857_, v_arg_3863_, v_arg_3860_, v_fst_3875_, v_fst_3879_, v_snd_3876_, v_snd_3880_);
if (v_eqTrue_3788_ == 0)
{
lean_object* v___x_3882_; lean_object* v___x_3883_; 
v___x_3882_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0);
v___x_3883_ = l_Lean_mkIntAdd(v_fst_3879_, v___x_3882_);
v___y_3805_ = v___y_3855_;
v___y_3806_ = v___y_3849_;
v___y_3807_ = v___y_3851_;
v___y_3808_ = v___y_3850_;
v___y_3809_ = v___y_3848_;
v___y_3810_ = v___x_3881_;
v___y_3811_ = v___y_3853_;
v___y_3812_ = v___y_3847_;
v___y_3813_ = v___y_3852_;
v___y_3814_ = v___y_3854_;
v___y_3815_ = v_a_3872_;
v___y_3816_ = v___y_3856_;
v_fst_3817_ = v___x_3883_;
v_snd_3818_ = v_fst_3875_;
goto v___jp_3804_;
}
else
{
v___y_3805_ = v___y_3855_;
v___y_3806_ = v___y_3849_;
v___y_3807_ = v___y_3851_;
v___y_3808_ = v___y_3850_;
v___y_3809_ = v___y_3848_;
v___y_3810_ = v___x_3881_;
v___y_3811_ = v___y_3853_;
v___y_3812_ = v___y_3847_;
v___y_3813_ = v___y_3852_;
v___y_3814_ = v___y_3854_;
v___y_3815_ = v_a_3872_;
v___y_3816_ = v___y_3856_;
v_fst_3817_ = v_fst_3875_;
v_snd_3818_ = v_fst_3879_;
goto v___jp_3804_;
}
}
else
{
lean_object* v_a_3884_; lean_object* v___x_3886_; uint8_t v_isShared_3887_; uint8_t v_isSharedCheck_3891_; 
lean_dec(v_snd_3876_);
lean_dec(v_fst_3875_);
lean_dec(v_a_3872_);
lean_dec_ref(v_arg_3863_);
lean_dec_ref(v_arg_3860_);
lean_dec(v_val_3857_);
lean_dec_ref(v_e_3787_);
v_a_3884_ = lean_ctor_get(v___x_3877_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v___x_3877_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3886_ = v___x_3877_;
v_isShared_3887_ = v_isSharedCheck_3891_;
goto v_resetjp_3885_;
}
else
{
lean_inc(v_a_3884_);
lean_dec(v___x_3877_);
v___x_3886_ = lean_box(0);
v_isShared_3887_ = v_isSharedCheck_3891_;
goto v_resetjp_3885_;
}
v_resetjp_3885_:
{
lean_object* v___x_3889_; 
if (v_isShared_3887_ == 0)
{
v___x_3889_ = v___x_3886_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v_a_3884_);
v___x_3889_ = v_reuseFailAlloc_3890_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
return v___x_3889_;
}
}
}
}
else
{
lean_object* v_a_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_3899_; 
lean_dec(v_a_3872_);
lean_dec_ref(v_arg_3863_);
lean_dec_ref(v_arg_3860_);
lean_dec(v_val_3857_);
lean_dec_ref(v_e_3787_);
v_a_3892_ = lean_ctor_get(v___x_3873_, 0);
v_isSharedCheck_3899_ = !lean_is_exclusive(v___x_3873_);
if (v_isSharedCheck_3899_ == 0)
{
v___x_3894_ = v___x_3873_;
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_a_3892_);
lean_dec(v___x_3873_);
v___x_3894_ = lean_box(0);
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
v_resetjp_3893_:
{
lean_object* v___x_3897_; 
if (v_isShared_3895_ == 0)
{
v___x_3897_ = v___x_3894_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v_a_3892_);
v___x_3897_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
return v___x_3897_;
}
}
}
}
else
{
lean_object* v_a_3900_; lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_3907_; 
lean_dec_ref(v_arg_3863_);
lean_dec_ref(v_arg_3860_);
lean_dec(v_val_3857_);
lean_dec_ref(v_e_3787_);
v_a_3900_ = lean_ctor_get(v___x_3871_, 0);
v_isSharedCheck_3907_ = !lean_is_exclusive(v___x_3871_);
if (v_isSharedCheck_3907_ == 0)
{
v___x_3902_ = v___x_3871_;
v_isShared_3903_ = v_isSharedCheck_3907_;
goto v_resetjp_3901_;
}
else
{
lean_inc(v_a_3900_);
lean_dec(v___x_3871_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_3907_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
lean_object* v___x_3905_; 
if (v_isShared_3903_ == 0)
{
v___x_3905_ = v___x_3902_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v_a_3900_);
v___x_3905_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
return v___x_3905_;
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
lean_object* v___x_3908_; lean_object* v___x_3909_; 
lean_dec(v_____x_3845_);
lean_dec_ref(v_e_3787_);
v___x_3908_ = lean_box(0);
v___x_3909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3909_, 0, v___x_3908_);
return v___x_3909_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe___boxed(lean_object* v_e_3930_, lean_object* v_eqTrue_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_){
_start:
{
uint8_t v_eqTrue_boxed_3944_; lean_object* v_res_3945_; 
v_eqTrue_boxed_3944_ = lean_unbox(v_eqTrue_3931_);
v_res_3945_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe(v_e_3930_, v_eqTrue_boxed_3944_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_, v_a_3941_, v_a_3942_);
lean_dec(v_a_3942_);
lean_dec_ref(v_a_3941_);
lean_dec(v_a_3940_);
lean_dec_ref(v_a_3939_);
lean_dec(v_a_3938_);
lean_dec_ref(v_a_3937_);
lean_dec(v_a_3936_);
lean_dec_ref(v_a_3935_);
lean_dec(v_a_3934_);
lean_dec(v_a_3933_);
lean_dec(v_a_3932_);
return v_res_3945_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe(lean_object* v_e_3951_, uint8_t v_eqTrue_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_){
_start:
{
lean_object* v___x_3967_; 
v___x_3967_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3955_);
if (lean_obj_tag(v___x_3967_) == 0)
{
lean_object* v_a_3968_; lean_object* v___x_3970_; uint8_t v_isShared_3971_; uint8_t v_isSharedCheck_3998_; 
v_a_3968_ = lean_ctor_get(v___x_3967_, 0);
v_isSharedCheck_3998_ = !lean_is_exclusive(v___x_3967_);
if (v_isSharedCheck_3998_ == 0)
{
v___x_3970_ = v___x_3967_;
v_isShared_3971_ = v_isSharedCheck_3998_;
goto v_resetjp_3969_;
}
else
{
lean_inc(v_a_3968_);
lean_dec(v___x_3967_);
v___x_3970_ = lean_box(0);
v_isShared_3971_ = v_isSharedCheck_3998_;
goto v_resetjp_3969_;
}
v_resetjp_3969_:
{
uint8_t v_lia_3972_; 
v_lia_3972_ = lean_ctor_get_uint8(v_a_3968_, sizeof(void*)*13 + 23);
lean_dec(v_a_3968_);
if (v_lia_3972_ == 0)
{
lean_object* v___x_3973_; lean_object* v___x_3975_; 
lean_dec_ref(v_e_3951_);
v___x_3973_ = lean_box(0);
if (v_isShared_3971_ == 0)
{
lean_ctor_set(v___x_3970_, 0, v___x_3973_);
v___x_3975_ = v___x_3970_;
goto v_reusejp_3974_;
}
else
{
lean_object* v_reuseFailAlloc_3976_; 
v_reuseFailAlloc_3976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3976_, 0, v___x_3973_);
v___x_3975_ = v_reuseFailAlloc_3976_;
goto v_reusejp_3974_;
}
v_reusejp_3974_:
{
return v___x_3975_;
}
}
else
{
lean_object* v___x_3977_; uint8_t v___x_3978_; 
lean_del_object(v___x_3970_);
lean_inc_ref(v_e_3951_);
v___x_3977_ = l_Lean_Expr_cleanupAnnotations(v_e_3951_);
v___x_3978_ = l_Lean_Expr_isApp(v___x_3977_);
if (v___x_3978_ == 0)
{
lean_dec_ref(v___x_3977_);
lean_dec_ref(v_e_3951_);
goto v___jp_3964_;
}
else
{
lean_object* v___x_3979_; uint8_t v___x_3980_; 
v___x_3979_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3977_);
v___x_3980_ = l_Lean_Expr_isApp(v___x_3979_);
if (v___x_3980_ == 0)
{
lean_dec_ref(v___x_3979_);
lean_dec_ref(v_e_3951_);
goto v___jp_3964_;
}
else
{
lean_object* v___x_3981_; uint8_t v___x_3982_; 
v___x_3981_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3979_);
v___x_3982_ = l_Lean_Expr_isApp(v___x_3981_);
if (v___x_3982_ == 0)
{
lean_dec_ref(v___x_3981_);
lean_dec_ref(v_e_3951_);
goto v___jp_3964_;
}
else
{
lean_object* v___x_3983_; uint8_t v___x_3984_; 
v___x_3983_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3981_);
v___x_3984_ = l_Lean_Expr_isApp(v___x_3983_);
if (v___x_3984_ == 0)
{
lean_dec_ref(v___x_3983_);
lean_dec_ref(v_e_3951_);
goto v___jp_3964_;
}
else
{
lean_object* v_arg_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; uint8_t v___x_3988_; 
v_arg_3985_ = lean_ctor_get(v___x_3983_, 1);
lean_inc_ref(v_arg_3985_);
v___x_3986_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3983_);
v___x_3987_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2));
v___x_3988_ = l_Lean_Expr_isConstOf(v___x_3986_, v___x_3987_);
lean_dec_ref(v___x_3986_);
if (v___x_3988_ == 0)
{
lean_dec_ref(v_arg_3985_);
lean_dec_ref(v_e_3951_);
goto v___jp_3964_;
}
else
{
lean_object* v___x_3989_; uint8_t v___x_3990_; 
v___x_3989_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__0));
v___x_3990_ = l_Lean_Expr_isConstOf(v_arg_3985_, v___x_3989_);
if (v___x_3990_ == 0)
{
lean_object* v___x_3991_; uint8_t v___x_3992_; 
v___x_3991_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__2));
v___x_3992_ = l_Lean_Expr_isConstOf(v_arg_3985_, v___x_3991_);
if (v___x_3992_ == 0)
{
lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; 
v___x_3993_ = lean_box(v_eqTrue_3952_);
v___x_3994_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe___boxed), 14, 2);
lean_closure_set(v___x_3994_, 0, v_e_3951_);
lean_closure_set(v___x_3994_, 1, v___x_3993_);
v___x_3995_ = l_Lean_Meta_Grind_Arith_Cutsat_ToIntM_run(v_arg_3985_, v___x_3994_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_, v_a_3960_, v_a_3961_, v_a_3962_);
return v___x_3995_;
}
else
{
lean_object* v___x_3996_; 
lean_dec_ref(v_arg_3985_);
v___x_3996_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe(v_e_3951_, v_eqTrue_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_, v_a_3960_, v_a_3961_, v_a_3962_);
return v___x_3996_;
}
}
else
{
lean_object* v___x_3997_; 
lean_dec_ref(v_arg_3985_);
v___x_3997_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe(v_e_3951_, v_eqTrue_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_, v_a_3960_, v_a_3961_, v_a_3962_);
return v___x_3997_;
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
lean_object* v_a_3999_; lean_object* v___x_4001_; uint8_t v_isShared_4002_; uint8_t v_isSharedCheck_4006_; 
lean_dec_ref(v_e_3951_);
v_a_3999_ = lean_ctor_get(v___x_3967_, 0);
v_isSharedCheck_4006_ = !lean_is_exclusive(v___x_3967_);
if (v_isSharedCheck_4006_ == 0)
{
v___x_4001_ = v___x_3967_;
v_isShared_4002_ = v_isSharedCheck_4006_;
goto v_resetjp_4000_;
}
else
{
lean_inc(v_a_3999_);
lean_dec(v___x_3967_);
v___x_4001_ = lean_box(0);
v_isShared_4002_ = v_isSharedCheck_4006_;
goto v_resetjp_4000_;
}
v_resetjp_4000_:
{
lean_object* v___x_4004_; 
if (v_isShared_4002_ == 0)
{
v___x_4004_ = v___x_4001_;
goto v_reusejp_4003_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v_a_3999_);
v___x_4004_ = v_reuseFailAlloc_4005_;
goto v_reusejp_4003_;
}
v_reusejp_4003_:
{
return v___x_4004_;
}
}
}
v___jp_3964_:
{
lean_object* v___x_3965_; lean_object* v___x_3966_; 
v___x_3965_ = lean_box(0);
v___x_3966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3966_, 0, v___x_3965_);
return v___x_3966_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___boxed(lean_object* v_e_4007_, lean_object* v_eqTrue_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_){
_start:
{
uint8_t v_eqTrue_boxed_4020_; lean_object* v_res_4021_; 
v_eqTrue_boxed_4020_ = lean_unbox(v_eqTrue_4008_);
v_res_4021_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLe(v_e_4007_, v_eqTrue_boxed_4020_, v_a_4009_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_, v_a_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_);
lean_dec(v_a_4018_);
lean_dec_ref(v_a_4017_);
lean_dec(v_a_4016_);
lean_dec_ref(v_a_4015_);
lean_dec(v_a_4014_);
lean_dec_ref(v_a_4013_);
lean_dec(v_a_4012_);
lean_dec_ref(v_a_4011_);
lean_dec(v_a_4010_);
lean_dec(v_a_4009_);
return v_res_4021_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__0(lean_object* v_e_4022_, lean_object* v_arg_4023_, lean_object* v_arg_4024_, uint8_t v_eqTrue_4025_, lean_object* v_____x_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_){
_start:
{
if (lean_obj_tag(v_____x_4026_) == 1)
{
lean_object* v_val_4039_; lean_object* v___x_4040_; 
v_val_4039_ = lean_ctor_get(v_____x_4026_, 0);
lean_inc(v_val_4039_);
lean_dec_ref_known(v_____x_4026_, 1);
v___x_4040_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_4022_, v___y_4028_);
if (lean_obj_tag(v___x_4040_) == 0)
{
lean_object* v_a_4041_; lean_object* v___x_4042_; 
v_a_4041_ = lean_ctor_get(v___x_4040_, 0);
lean_inc(v_a_4041_);
lean_dec_ref_known(v___x_4040_, 1);
lean_inc_ref(v_arg_4023_);
v___x_4042_ = l_Lean_Meta_Grind_Arith_Cutsat_toInt(v_arg_4023_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_);
if (lean_obj_tag(v___x_4042_) == 0)
{
lean_object* v_a_4043_; lean_object* v_fst_4044_; lean_object* v_snd_4045_; lean_object* v___x_4047_; uint8_t v_isShared_4048_; uint8_t v_isSharedCheck_4100_; 
v_a_4043_ = lean_ctor_get(v___x_4042_, 0);
lean_inc(v_a_4043_);
lean_dec_ref_known(v___x_4042_, 1);
v_fst_4044_ = lean_ctor_get(v_a_4043_, 0);
v_snd_4045_ = lean_ctor_get(v_a_4043_, 1);
v_isSharedCheck_4100_ = !lean_is_exclusive(v_a_4043_);
if (v_isSharedCheck_4100_ == 0)
{
v___x_4047_ = v_a_4043_;
v_isShared_4048_ = v_isSharedCheck_4100_;
goto v_resetjp_4046_;
}
else
{
lean_inc(v_snd_4045_);
lean_inc(v_fst_4044_);
lean_dec(v_a_4043_);
v___x_4047_ = lean_box(0);
v_isShared_4048_ = v_isSharedCheck_4100_;
goto v_resetjp_4046_;
}
v_resetjp_4046_:
{
lean_object* v___x_4049_; 
lean_inc_ref(v_arg_4024_);
v___x_4049_ = l_Lean_Meta_Grind_Arith_Cutsat_toInt(v_arg_4024_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_);
if (lean_obj_tag(v___x_4049_) == 0)
{
lean_object* v_a_4050_; lean_object* v_fst_4051_; lean_object* v_snd_4052_; lean_object* v___x_4054_; uint8_t v_isShared_4055_; uint8_t v_isSharedCheck_4091_; 
v_a_4050_ = lean_ctor_get(v___x_4049_, 0);
lean_inc(v_a_4050_);
lean_dec_ref_known(v___x_4049_, 1);
v_fst_4051_ = lean_ctor_get(v_a_4050_, 0);
v_snd_4052_ = lean_ctor_get(v_a_4050_, 1);
v_isSharedCheck_4091_ = !lean_is_exclusive(v_a_4050_);
if (v_isSharedCheck_4091_ == 0)
{
v___x_4054_ = v_a_4050_;
v_isShared_4055_ = v_isSharedCheck_4091_;
goto v_resetjp_4053_;
}
else
{
lean_inc(v_snd_4052_);
lean_inc(v_fst_4051_);
lean_dec(v_a_4050_);
v___x_4054_ = lean_box(0);
v_isShared_4055_ = v_isSharedCheck_4091_;
goto v_resetjp_4053_;
}
v_resetjp_4053_:
{
lean_object* v___x_4056_; lean_object* v_fst_4058_; lean_object* v_snd_4059_; 
lean_inc(v_fst_4051_);
lean_inc(v_fst_4044_);
v___x_4056_ = l_Lean_mkApp6(v_val_4039_, v_arg_4023_, v_arg_4024_, v_fst_4044_, v_fst_4051_, v_snd_4045_, v_snd_4052_);
if (v_eqTrue_4025_ == 0)
{
v_fst_4058_ = v_fst_4051_;
v_snd_4059_ = v_fst_4044_;
goto v___jp_4057_;
}
else
{
lean_object* v___x_4089_; lean_object* v___x_4090_; 
v___x_4089_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0);
v___x_4090_ = l_Lean_mkIntAdd(v_fst_4044_, v___x_4089_);
v_fst_4058_ = v___x_4090_;
v_snd_4059_ = v_fst_4051_;
goto v___jp_4057_;
}
v___jp_4057_:
{
lean_object* v___x_4060_; 
lean_inc(v_a_4041_);
v___x_4060_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_4058_, v_a_4041_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_);
if (lean_obj_tag(v___x_4060_) == 0)
{
lean_object* v_a_4061_; lean_object* v___x_4062_; 
v_a_4061_ = lean_ctor_get(v___x_4060_, 0);
lean_inc(v_a_4061_);
lean_dec_ref_known(v___x_4060_, 1);
v___x_4062_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_snd_4059_, v_a_4041_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_);
if (lean_obj_tag(v___x_4062_) == 0)
{
lean_object* v_a_4063_; lean_object* v___x_4065_; 
v_a_4063_ = lean_ctor_get(v___x_4062_, 0);
lean_inc_n(v_a_4063_, 2);
lean_dec_ref_known(v___x_4062_, 1);
lean_inc(v_a_4061_);
if (v_isShared_4055_ == 0)
{
lean_ctor_set_tag(v___x_4054_, 3);
lean_ctor_set(v___x_4054_, 1, v_a_4063_);
lean_ctor_set(v___x_4054_, 0, v_a_4061_);
v___x_4065_ = v___x_4054_;
goto v_reusejp_4064_;
}
else
{
lean_object* v_reuseFailAlloc_4072_; 
v_reuseFailAlloc_4072_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4072_, 0, v_a_4061_);
lean_ctor_set(v_reuseFailAlloc_4072_, 1, v_a_4063_);
v___x_4065_ = v_reuseFailAlloc_4072_;
goto v_reusejp_4064_;
}
v_reusejp_4064_:
{
lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4069_; 
v___x_4066_ = l_Int_Internal_Linear_Expr_norm(v___x_4065_);
lean_dec_ref(v___x_4065_);
v___x_4067_ = lean_alloc_ctor(2, 4, 1);
lean_ctor_set(v___x_4067_, 0, v_e_4022_);
lean_ctor_set(v___x_4067_, 1, v___x_4056_);
lean_ctor_set(v___x_4067_, 2, v_a_4061_);
lean_ctor_set(v___x_4067_, 3, v_a_4063_);
lean_ctor_set_uint8(v___x_4067_, sizeof(void*)*4, v_eqTrue_4025_);
if (v_isShared_4048_ == 0)
{
lean_ctor_set(v___x_4047_, 1, v___x_4067_);
lean_ctor_set(v___x_4047_, 0, v___x_4066_);
v___x_4069_ = v___x_4047_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v___x_4066_);
lean_ctor_set(v_reuseFailAlloc_4071_, 1, v___x_4067_);
v___x_4069_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
lean_object* v___x_4070_; 
lean_inc(v___y_4037_);
lean_inc_ref(v___y_4036_);
lean_inc(v___y_4035_);
lean_inc_ref(v___y_4034_);
lean_inc(v___y_4033_);
lean_inc_ref(v___y_4032_);
lean_inc(v___y_4031_);
lean_inc_ref(v___y_4030_);
lean_inc(v___y_4029_);
lean_inc(v___y_4028_);
v___x_4070_ = lean_grind_cutsat_assert_le(v___x_4069_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_);
return v___x_4070_;
}
}
}
else
{
lean_object* v_a_4073_; lean_object* v___x_4075_; uint8_t v_isShared_4076_; uint8_t v_isSharedCheck_4080_; 
lean_dec(v_a_4061_);
lean_dec_ref(v___x_4056_);
lean_del_object(v___x_4054_);
lean_del_object(v___x_4047_);
lean_dec_ref(v_e_4022_);
v_a_4073_ = lean_ctor_get(v___x_4062_, 0);
v_isSharedCheck_4080_ = !lean_is_exclusive(v___x_4062_);
if (v_isSharedCheck_4080_ == 0)
{
v___x_4075_ = v___x_4062_;
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
else
{
lean_inc(v_a_4073_);
lean_dec(v___x_4062_);
v___x_4075_ = lean_box(0);
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
v_resetjp_4074_:
{
lean_object* v___x_4078_; 
if (v_isShared_4076_ == 0)
{
v___x_4078_ = v___x_4075_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v_a_4073_);
v___x_4078_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
return v___x_4078_;
}
}
}
}
else
{
lean_object* v_a_4081_; lean_object* v___x_4083_; uint8_t v_isShared_4084_; uint8_t v_isSharedCheck_4088_; 
lean_dec_ref(v_snd_4059_);
lean_dec_ref(v___x_4056_);
lean_del_object(v___x_4054_);
lean_del_object(v___x_4047_);
lean_dec(v_a_4041_);
lean_dec_ref(v_e_4022_);
v_a_4081_ = lean_ctor_get(v___x_4060_, 0);
v_isSharedCheck_4088_ = !lean_is_exclusive(v___x_4060_);
if (v_isSharedCheck_4088_ == 0)
{
v___x_4083_ = v___x_4060_;
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
else
{
lean_inc(v_a_4081_);
lean_dec(v___x_4060_);
v___x_4083_ = lean_box(0);
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
v_resetjp_4082_:
{
lean_object* v___x_4086_; 
if (v_isShared_4084_ == 0)
{
v___x_4086_ = v___x_4083_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v_a_4081_);
v___x_4086_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
return v___x_4086_;
}
}
}
}
}
}
else
{
lean_object* v_a_4092_; lean_object* v___x_4094_; uint8_t v_isShared_4095_; uint8_t v_isSharedCheck_4099_; 
lean_del_object(v___x_4047_);
lean_dec(v_snd_4045_);
lean_dec(v_fst_4044_);
lean_dec(v_a_4041_);
lean_dec(v_val_4039_);
lean_dec_ref(v_arg_4024_);
lean_dec_ref(v_arg_4023_);
lean_dec_ref(v_e_4022_);
v_a_4092_ = lean_ctor_get(v___x_4049_, 0);
v_isSharedCheck_4099_ = !lean_is_exclusive(v___x_4049_);
if (v_isSharedCheck_4099_ == 0)
{
v___x_4094_ = v___x_4049_;
v_isShared_4095_ = v_isSharedCheck_4099_;
goto v_resetjp_4093_;
}
else
{
lean_inc(v_a_4092_);
lean_dec(v___x_4049_);
v___x_4094_ = lean_box(0);
v_isShared_4095_ = v_isSharedCheck_4099_;
goto v_resetjp_4093_;
}
v_resetjp_4093_:
{
lean_object* v___x_4097_; 
if (v_isShared_4095_ == 0)
{
v___x_4097_ = v___x_4094_;
goto v_reusejp_4096_;
}
else
{
lean_object* v_reuseFailAlloc_4098_; 
v_reuseFailAlloc_4098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4098_, 0, v_a_4092_);
v___x_4097_ = v_reuseFailAlloc_4098_;
goto v_reusejp_4096_;
}
v_reusejp_4096_:
{
return v___x_4097_;
}
}
}
}
}
else
{
lean_object* v_a_4101_; lean_object* v___x_4103_; uint8_t v_isShared_4104_; uint8_t v_isSharedCheck_4108_; 
lean_dec(v_a_4041_);
lean_dec(v_val_4039_);
lean_dec_ref(v_arg_4024_);
lean_dec_ref(v_arg_4023_);
lean_dec_ref(v_e_4022_);
v_a_4101_ = lean_ctor_get(v___x_4042_, 0);
v_isSharedCheck_4108_ = !lean_is_exclusive(v___x_4042_);
if (v_isSharedCheck_4108_ == 0)
{
v___x_4103_ = v___x_4042_;
v_isShared_4104_ = v_isSharedCheck_4108_;
goto v_resetjp_4102_;
}
else
{
lean_inc(v_a_4101_);
lean_dec(v___x_4042_);
v___x_4103_ = lean_box(0);
v_isShared_4104_ = v_isSharedCheck_4108_;
goto v_resetjp_4102_;
}
v_resetjp_4102_:
{
lean_object* v___x_4106_; 
if (v_isShared_4104_ == 0)
{
v___x_4106_ = v___x_4103_;
goto v_reusejp_4105_;
}
else
{
lean_object* v_reuseFailAlloc_4107_; 
v_reuseFailAlloc_4107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4107_, 0, v_a_4101_);
v___x_4106_ = v_reuseFailAlloc_4107_;
goto v_reusejp_4105_;
}
v_reusejp_4105_:
{
return v___x_4106_;
}
}
}
}
else
{
lean_object* v_a_4109_; lean_object* v___x_4111_; uint8_t v_isShared_4112_; uint8_t v_isSharedCheck_4116_; 
lean_dec(v_val_4039_);
lean_dec_ref(v_arg_4024_);
lean_dec_ref(v_arg_4023_);
lean_dec_ref(v_e_4022_);
v_a_4109_ = lean_ctor_get(v___x_4040_, 0);
v_isSharedCheck_4116_ = !lean_is_exclusive(v___x_4040_);
if (v_isSharedCheck_4116_ == 0)
{
v___x_4111_ = v___x_4040_;
v_isShared_4112_ = v_isSharedCheck_4116_;
goto v_resetjp_4110_;
}
else
{
lean_inc(v_a_4109_);
lean_dec(v___x_4040_);
v___x_4111_ = lean_box(0);
v_isShared_4112_ = v_isSharedCheck_4116_;
goto v_resetjp_4110_;
}
v_resetjp_4110_:
{
lean_object* v___x_4114_; 
if (v_isShared_4112_ == 0)
{
v___x_4114_ = v___x_4111_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4115_; 
v_reuseFailAlloc_4115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4115_, 0, v_a_4109_);
v___x_4114_ = v_reuseFailAlloc_4115_;
goto v_reusejp_4113_;
}
v_reusejp_4113_:
{
return v___x_4114_;
}
}
}
}
else
{
lean_object* v___x_4117_; lean_object* v___x_4118_; 
lean_dec(v_____x_4026_);
lean_dec_ref(v_arg_4024_);
lean_dec_ref(v_arg_4023_);
lean_dec_ref(v_e_4022_);
v___x_4117_ = lean_box(0);
v___x_4118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4118_, 0, v___x_4117_);
return v___x_4118_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__0___boxed(lean_object** _args){
lean_object* v_e_4119_ = _args[0];
lean_object* v_arg_4120_ = _args[1];
lean_object* v_arg_4121_ = _args[2];
lean_object* v_eqTrue_4122_ = _args[3];
lean_object* v_____x_4123_ = _args[4];
lean_object* v___y_4124_ = _args[5];
lean_object* v___y_4125_ = _args[6];
lean_object* v___y_4126_ = _args[7];
lean_object* v___y_4127_ = _args[8];
lean_object* v___y_4128_ = _args[9];
lean_object* v___y_4129_ = _args[10];
lean_object* v___y_4130_ = _args[11];
lean_object* v___y_4131_ = _args[12];
lean_object* v___y_4132_ = _args[13];
lean_object* v___y_4133_ = _args[14];
lean_object* v___y_4134_ = _args[15];
lean_object* v___y_4135_ = _args[16];
_start:
{
uint8_t v_eqTrue_boxed_4136_; lean_object* v_res_4137_; 
v_eqTrue_boxed_4136_ = lean_unbox(v_eqTrue_4122_);
v_res_4137_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__0(v_e_4119_, v_arg_4120_, v_arg_4121_, v_eqTrue_boxed_4136_, v_____x_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_);
lean_dec(v___y_4134_);
lean_dec_ref(v___y_4133_);
lean_dec(v___y_4132_);
lean_dec_ref(v___y_4131_);
lean_dec(v___y_4130_);
lean_dec_ref(v___y_4129_);
lean_dec(v___y_4128_);
lean_dec_ref(v___y_4127_);
lean_dec(v___y_4126_);
lean_dec(v___y_4125_);
lean_dec(v___y_4124_);
return v_res_4137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__1(uint8_t v_eqTrue_4138_, lean_object* v___f_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_){
_start:
{
if (v_eqTrue_4138_ == 0)
{
lean_object* v___x_4152_; 
v___x_4152_ = l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLT_x3f___redArg(v___y_4140_, v___y_4141_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_);
if (lean_obj_tag(v___x_4152_) == 0)
{
lean_object* v_a_4153_; lean_object* v___x_4154_; 
v_a_4153_ = lean_ctor_get(v___x_4152_, 0);
lean_inc(v_a_4153_);
lean_dec_ref_known(v___x_4152_, 1);
lean_inc(v___y_4150_);
lean_inc_ref(v___y_4149_);
lean_inc(v___y_4148_);
lean_inc_ref(v___y_4147_);
lean_inc(v___y_4146_);
lean_inc_ref(v___y_4145_);
lean_inc(v___y_4144_);
lean_inc_ref(v___y_4143_);
lean_inc(v___y_4142_);
lean_inc(v___y_4141_);
lean_inc(v___y_4140_);
v___x_4154_ = lean_apply_13(v___f_4139_, v_a_4153_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_, lean_box(0));
return v___x_4154_;
}
else
{
lean_object* v_a_4155_; lean_object* v___x_4157_; uint8_t v_isShared_4158_; uint8_t v_isSharedCheck_4162_; 
lean_dec_ref(v___f_4139_);
v_a_4155_ = lean_ctor_get(v___x_4152_, 0);
v_isSharedCheck_4162_ = !lean_is_exclusive(v___x_4152_);
if (v_isSharedCheck_4162_ == 0)
{
v___x_4157_ = v___x_4152_;
v_isShared_4158_ = v_isSharedCheck_4162_;
goto v_resetjp_4156_;
}
else
{
lean_inc(v_a_4155_);
lean_dec(v___x_4152_);
v___x_4157_ = lean_box(0);
v_isShared_4158_ = v_isSharedCheck_4162_;
goto v_resetjp_4156_;
}
v_resetjp_4156_:
{
lean_object* v___x_4160_; 
if (v_isShared_4158_ == 0)
{
v___x_4160_ = v___x_4157_;
goto v_reusejp_4159_;
}
else
{
lean_object* v_reuseFailAlloc_4161_; 
v_reuseFailAlloc_4161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4161_, 0, v_a_4155_);
v___x_4160_ = v_reuseFailAlloc_4161_;
goto v_reusejp_4159_;
}
v_reusejp_4159_:
{
return v___x_4160_;
}
}
}
}
else
{
lean_object* v___x_4163_; 
v___x_4163_ = l_Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f___redArg(v___y_4140_, v___y_4141_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_);
if (lean_obj_tag(v___x_4163_) == 0)
{
lean_object* v_a_4164_; lean_object* v___x_4165_; 
v_a_4164_ = lean_ctor_get(v___x_4163_, 0);
lean_inc(v_a_4164_);
lean_dec_ref_known(v___x_4163_, 1);
lean_inc(v___y_4150_);
lean_inc_ref(v___y_4149_);
lean_inc(v___y_4148_);
lean_inc_ref(v___y_4147_);
lean_inc(v___y_4146_);
lean_inc_ref(v___y_4145_);
lean_inc(v___y_4144_);
lean_inc_ref(v___y_4143_);
lean_inc(v___y_4142_);
lean_inc(v___y_4141_);
lean_inc(v___y_4140_);
v___x_4165_ = lean_apply_13(v___f_4139_, v_a_4164_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_, lean_box(0));
return v___x_4165_;
}
else
{
lean_object* v_a_4166_; lean_object* v___x_4168_; uint8_t v_isShared_4169_; uint8_t v_isSharedCheck_4173_; 
lean_dec_ref(v___f_4139_);
v_a_4166_ = lean_ctor_get(v___x_4163_, 0);
v_isSharedCheck_4173_ = !lean_is_exclusive(v___x_4163_);
if (v_isSharedCheck_4173_ == 0)
{
v___x_4168_ = v___x_4163_;
v_isShared_4169_ = v_isSharedCheck_4173_;
goto v_resetjp_4167_;
}
else
{
lean_inc(v_a_4166_);
lean_dec(v___x_4163_);
v___x_4168_ = lean_box(0);
v_isShared_4169_ = v_isSharedCheck_4173_;
goto v_resetjp_4167_;
}
v_resetjp_4167_:
{
lean_object* v___x_4171_; 
if (v_isShared_4169_ == 0)
{
v___x_4171_ = v___x_4168_;
goto v_reusejp_4170_;
}
else
{
lean_object* v_reuseFailAlloc_4172_; 
v_reuseFailAlloc_4172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4172_, 0, v_a_4166_);
v___x_4171_ = v_reuseFailAlloc_4172_;
goto v_reusejp_4170_;
}
v_reusejp_4170_:
{
return v___x_4171_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__1___boxed(lean_object* v_eqTrue_4174_, lean_object* v___f_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_){
_start:
{
uint8_t v_eqTrue_boxed_4188_; lean_object* v_res_4189_; 
v_eqTrue_boxed_4188_ = lean_unbox(v_eqTrue_4174_);
v_res_4189_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__1(v_eqTrue_boxed_4188_, v___f_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_);
lean_dec(v___y_4186_);
lean_dec_ref(v___y_4185_);
lean_dec(v___y_4184_);
lean_dec_ref(v___y_4183_);
lean_dec(v___y_4182_);
lean_dec_ref(v___y_4181_);
lean_dec(v___y_4180_);
lean_dec_ref(v___y_4179_);
lean_dec(v___y_4178_);
lean_dec(v___y_4177_);
lean_dec(v___y_4176_);
return v_res_4189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt(lean_object* v_e_4195_, uint8_t v_eqTrue_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_, lean_object* v_a_4206_){
_start:
{
lean_object* v___x_4211_; 
v___x_4211_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_4199_);
if (lean_obj_tag(v___x_4211_) == 0)
{
lean_object* v_a_4212_; lean_object* v___x_4214_; uint8_t v_isShared_4215_; uint8_t v_isSharedCheck_4240_; 
v_a_4212_ = lean_ctor_get(v___x_4211_, 0);
v_isSharedCheck_4240_ = !lean_is_exclusive(v___x_4211_);
if (v_isSharedCheck_4240_ == 0)
{
v___x_4214_ = v___x_4211_;
v_isShared_4215_ = v_isSharedCheck_4240_;
goto v_resetjp_4213_;
}
else
{
lean_inc(v_a_4212_);
lean_dec(v___x_4211_);
v___x_4214_ = lean_box(0);
v_isShared_4215_ = v_isSharedCheck_4240_;
goto v_resetjp_4213_;
}
v_resetjp_4213_:
{
uint8_t v_lia_4216_; 
v_lia_4216_ = lean_ctor_get_uint8(v_a_4212_, sizeof(void*)*13 + 23);
lean_dec(v_a_4212_);
if (v_lia_4216_ == 0)
{
lean_object* v___x_4217_; lean_object* v___x_4219_; 
lean_dec_ref(v_e_4195_);
v___x_4217_ = lean_box(0);
if (v_isShared_4215_ == 0)
{
lean_ctor_set(v___x_4214_, 0, v___x_4217_);
v___x_4219_ = v___x_4214_;
goto v_reusejp_4218_;
}
else
{
lean_object* v_reuseFailAlloc_4220_; 
v_reuseFailAlloc_4220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4220_, 0, v___x_4217_);
v___x_4219_ = v_reuseFailAlloc_4220_;
goto v_reusejp_4218_;
}
v_reusejp_4218_:
{
return v___x_4219_;
}
}
else
{
lean_object* v___x_4221_; uint8_t v___x_4222_; 
lean_del_object(v___x_4214_);
lean_inc_ref(v_e_4195_);
v___x_4221_ = l_Lean_Expr_cleanupAnnotations(v_e_4195_);
v___x_4222_ = l_Lean_Expr_isApp(v___x_4221_);
if (v___x_4222_ == 0)
{
lean_dec_ref(v___x_4221_);
lean_dec_ref(v_e_4195_);
goto v___jp_4208_;
}
else
{
lean_object* v_arg_4223_; lean_object* v___x_4224_; uint8_t v___x_4225_; 
v_arg_4223_ = lean_ctor_get(v___x_4221_, 1);
lean_inc_ref(v_arg_4223_);
v___x_4224_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4221_);
v___x_4225_ = l_Lean_Expr_isApp(v___x_4224_);
if (v___x_4225_ == 0)
{
lean_dec_ref(v___x_4224_);
lean_dec_ref(v_arg_4223_);
lean_dec_ref(v_e_4195_);
goto v___jp_4208_;
}
else
{
lean_object* v_arg_4226_; lean_object* v___x_4227_; uint8_t v___x_4228_; 
v_arg_4226_ = lean_ctor_get(v___x_4224_, 1);
lean_inc_ref(v_arg_4226_);
v___x_4227_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4224_);
v___x_4228_ = l_Lean_Expr_isApp(v___x_4227_);
if (v___x_4228_ == 0)
{
lean_dec_ref(v___x_4227_);
lean_dec_ref(v_arg_4226_);
lean_dec_ref(v_arg_4223_);
lean_dec_ref(v_e_4195_);
goto v___jp_4208_;
}
else
{
lean_object* v___x_4229_; uint8_t v___x_4230_; 
v___x_4229_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4227_);
v___x_4230_ = l_Lean_Expr_isApp(v___x_4229_);
if (v___x_4230_ == 0)
{
lean_dec_ref(v___x_4229_);
lean_dec_ref(v_arg_4226_);
lean_dec_ref(v_arg_4223_);
lean_dec_ref(v_e_4195_);
goto v___jp_4208_;
}
else
{
lean_object* v_arg_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; uint8_t v___x_4234_; 
v_arg_4231_ = lean_ctor_get(v___x_4229_, 1);
lean_inc_ref(v_arg_4231_);
v___x_4232_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4229_);
v___x_4233_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__2));
v___x_4234_ = l_Lean_Expr_isConstOf(v___x_4232_, v___x_4233_);
lean_dec_ref(v___x_4232_);
if (v___x_4234_ == 0)
{
lean_dec_ref(v_arg_4231_);
lean_dec_ref(v_arg_4226_);
lean_dec_ref(v_arg_4223_);
lean_dec_ref(v_e_4195_);
goto v___jp_4208_;
}
else
{
lean_object* v___x_4235_; lean_object* v___f_4236_; lean_object* v___x_4237_; lean_object* v___y_4238_; lean_object* v___x_4239_; 
v___x_4235_ = lean_box(v_eqTrue_4196_);
v___f_4236_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__0___boxed), 17, 4);
lean_closure_set(v___f_4236_, 0, v_e_4195_);
lean_closure_set(v___f_4236_, 1, v_arg_4226_);
lean_closure_set(v___f_4236_, 2, v_arg_4223_);
lean_closure_set(v___f_4236_, 3, v___x_4235_);
v___x_4237_ = lean_box(v_eqTrue_4196_);
v___y_4238_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__1___boxed), 14, 2);
lean_closure_set(v___y_4238_, 0, v___x_4237_);
lean_closure_set(v___y_4238_, 1, v___f_4236_);
v___x_4239_ = l_Lean_Meta_Grind_Arith_Cutsat_ToIntM_run(v_arg_4231_, v___y_4238_, v_a_4197_, v_a_4198_, v_a_4199_, v_a_4200_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_, v_a_4206_);
return v___x_4239_;
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
lean_object* v_a_4241_; lean_object* v___x_4243_; uint8_t v_isShared_4244_; uint8_t v_isSharedCheck_4248_; 
lean_dec_ref(v_e_4195_);
v_a_4241_ = lean_ctor_get(v___x_4211_, 0);
v_isSharedCheck_4248_ = !lean_is_exclusive(v___x_4211_);
if (v_isSharedCheck_4248_ == 0)
{
v___x_4243_ = v___x_4211_;
v_isShared_4244_ = v_isSharedCheck_4248_;
goto v_resetjp_4242_;
}
else
{
lean_inc(v_a_4241_);
lean_dec(v___x_4211_);
v___x_4243_ = lean_box(0);
v_isShared_4244_ = v_isSharedCheck_4248_;
goto v_resetjp_4242_;
}
v_resetjp_4242_:
{
lean_object* v___x_4246_; 
if (v_isShared_4244_ == 0)
{
v___x_4246_ = v___x_4243_;
goto v_reusejp_4245_;
}
else
{
lean_object* v_reuseFailAlloc_4247_; 
v_reuseFailAlloc_4247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4247_, 0, v_a_4241_);
v___x_4246_ = v_reuseFailAlloc_4247_;
goto v_reusejp_4245_;
}
v_reusejp_4245_:
{
return v___x_4246_;
}
}
}
v___jp_4208_:
{
lean_object* v___x_4209_; lean_object* v___x_4210_; 
v___x_4209_ = lean_box(0);
v___x_4210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4210_, 0, v___x_4209_);
return v___x_4210_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___boxed(lean_object* v_e_4249_, lean_object* v_eqTrue_4250_, lean_object* v_a_4251_, lean_object* v_a_4252_, lean_object* v_a_4253_, lean_object* v_a_4254_, lean_object* v_a_4255_, lean_object* v_a_4256_, lean_object* v_a_4257_, lean_object* v_a_4258_, lean_object* v_a_4259_, lean_object* v_a_4260_, lean_object* v_a_4261_){
_start:
{
uint8_t v_eqTrue_boxed_4262_; lean_object* v_res_4263_; 
v_eqTrue_boxed_4262_ = lean_unbox(v_eqTrue_4250_);
v_res_4263_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLt(v_e_4249_, v_eqTrue_boxed_4262_, v_a_4251_, v_a_4252_, v_a_4253_, v_a_4254_, v_a_4255_, v_a_4256_, v_a_4257_, v_a_4258_, v_a_4259_, v_a_4260_);
lean_dec(v_a_4260_);
lean_dec_ref(v_a_4259_);
lean_dec(v_a_4258_);
lean_dec_ref(v_a_4257_);
lean_dec(v_a_4256_);
lean_dec_ref(v_a_4255_);
lean_dec(v_a_4254_);
lean_dec_ref(v_a_4253_);
lean_dec(v_a_4252_);
lean_dec(v_a_4251_);
return v_res_4263_;
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
