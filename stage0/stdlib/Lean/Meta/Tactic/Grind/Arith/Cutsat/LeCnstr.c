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
uint8_t l_Int_Linear_instBEqPoly_beq(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0_spec__0(lean_object* v_msgData_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_){
_start:
{
lean_object* v___x_25_; lean_object* v_env_26_; lean_object* v___x_27_; lean_object* v_mctx_28_; lean_object* v_lctx_29_; lean_object* v_options_30_; lean_object* v___x_31_; lean_object* v___x_32_; lean_object* v___x_33_; 
v___x_25_ = lean_st_ref_get(v___y_23_);
v_env_26_ = lean_ctor_get(v___x_25_, 0);
lean_inc_ref(v_env_26_);
lean_dec(v___x_25_);
v___x_27_ = lean_st_ref_get(v___y_21_);
v_mctx_28_ = lean_ctor_get(v___x_27_, 0);
lean_inc_ref(v_mctx_28_);
lean_dec(v___x_27_);
v_lctx_29_ = lean_ctor_get(v___y_20_, 2);
v_options_30_ = lean_ctor_get(v___y_22_, 2);
lean_inc_ref(v_options_30_);
lean_inc_ref(v_lctx_29_);
v___x_31_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_31_, 0, v_env_26_);
lean_ctor_set(v___x_31_, 1, v_mctx_28_);
lean_ctor_set(v___x_31_, 2, v_lctx_29_);
lean_ctor_set(v___x_31_, 3, v_options_30_);
v___x_32_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_32_, 0, v___x_31_);
lean_ctor_set(v___x_32_, 1, v_msgData_19_);
v___x_33_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_33_, 0, v___x_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0_spec__0___boxed(lean_object* v_msgData_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0_spec__0(v_msgData_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_);
lean_dec(v___y_38_);
lean_dec_ref(v___y_37_);
lean_dec(v___y_36_);
lean_dec_ref(v___y_35_);
return v_res_40_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_41_; double v___x_42_; 
v___x_41_ = lean_unsigned_to_nat(0u);
v___x_42_ = lean_float_of_nat(v___x_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(lean_object* v_cls_46_, lean_object* v_msg_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_){
_start:
{
lean_object* v_ref_53_; lean_object* v___x_54_; lean_object* v_a_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_99_; 
v_ref_53_ = lean_ctor_get(v___y_50_, 5);
v___x_54_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0_spec__0(v_msg_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_);
v_a_55_ = lean_ctor_get(v___x_54_, 0);
v_isSharedCheck_99_ = !lean_is_exclusive(v___x_54_);
if (v_isSharedCheck_99_ == 0)
{
v___x_57_ = v___x_54_;
v_isShared_58_ = v_isSharedCheck_99_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_a_55_);
lean_dec(v___x_54_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_99_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v___x_59_; lean_object* v_traceState_60_; lean_object* v_env_61_; lean_object* v_nextMacroScope_62_; lean_object* v_ngen_63_; lean_object* v_auxDeclNGen_64_; lean_object* v_cache_65_; lean_object* v_messages_66_; lean_object* v_infoState_67_; lean_object* v_snapshotTasks_68_; lean_object* v___x_70_; uint8_t v_isShared_71_; uint8_t v_isSharedCheck_98_; 
v___x_59_ = lean_st_ref_take(v___y_51_);
v_traceState_60_ = lean_ctor_get(v___x_59_, 4);
v_env_61_ = lean_ctor_get(v___x_59_, 0);
v_nextMacroScope_62_ = lean_ctor_get(v___x_59_, 1);
v_ngen_63_ = lean_ctor_get(v___x_59_, 2);
v_auxDeclNGen_64_ = lean_ctor_get(v___x_59_, 3);
v_cache_65_ = lean_ctor_get(v___x_59_, 5);
v_messages_66_ = lean_ctor_get(v___x_59_, 6);
v_infoState_67_ = lean_ctor_get(v___x_59_, 7);
v_snapshotTasks_68_ = lean_ctor_get(v___x_59_, 8);
v_isSharedCheck_98_ = !lean_is_exclusive(v___x_59_);
if (v_isSharedCheck_98_ == 0)
{
v___x_70_ = v___x_59_;
v_isShared_71_ = v_isSharedCheck_98_;
goto v_resetjp_69_;
}
else
{
lean_inc(v_snapshotTasks_68_);
lean_inc(v_infoState_67_);
lean_inc(v_messages_66_);
lean_inc(v_cache_65_);
lean_inc(v_traceState_60_);
lean_inc(v_auxDeclNGen_64_);
lean_inc(v_ngen_63_);
lean_inc(v_nextMacroScope_62_);
lean_inc(v_env_61_);
lean_dec(v___x_59_);
v___x_70_ = lean_box(0);
v_isShared_71_ = v_isSharedCheck_98_;
goto v_resetjp_69_;
}
v_resetjp_69_:
{
uint64_t v_tid_72_; lean_object* v_traces_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_97_; 
v_tid_72_ = lean_ctor_get_uint64(v_traceState_60_, sizeof(void*)*1);
v_traces_73_ = lean_ctor_get(v_traceState_60_, 0);
v_isSharedCheck_97_ = !lean_is_exclusive(v_traceState_60_);
if (v_isSharedCheck_97_ == 0)
{
v___x_75_ = v_traceState_60_;
v_isShared_76_ = v_isSharedCheck_97_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_traces_73_);
lean_dec(v_traceState_60_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_97_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_77_; double v___x_78_; uint8_t v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_87_; 
v___x_77_ = lean_box(0);
v___x_78_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__0);
v___x_79_ = 0;
v___x_80_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__1));
v___x_81_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_81_, 0, v_cls_46_);
lean_ctor_set(v___x_81_, 1, v___x_77_);
lean_ctor_set(v___x_81_, 2, v___x_80_);
lean_ctor_set_float(v___x_81_, sizeof(void*)*3, v___x_78_);
lean_ctor_set_float(v___x_81_, sizeof(void*)*3 + 8, v___x_78_);
lean_ctor_set_uint8(v___x_81_, sizeof(void*)*3 + 16, v___x_79_);
v___x_82_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__2));
v___x_83_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_83_, 0, v___x_81_);
lean_ctor_set(v___x_83_, 1, v_a_55_);
lean_ctor_set(v___x_83_, 2, v___x_82_);
lean_inc(v_ref_53_);
v___x_84_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_84_, 0, v_ref_53_);
lean_ctor_set(v___x_84_, 1, v___x_83_);
v___x_85_ = l_Lean_PersistentArray_push___redArg(v_traces_73_, v___x_84_);
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 0, v___x_85_);
v___x_87_ = v___x_75_;
goto v_reusejp_86_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v___x_85_);
lean_ctor_set_uint64(v_reuseFailAlloc_96_, sizeof(void*)*1, v_tid_72_);
v___x_87_ = v_reuseFailAlloc_96_;
goto v_reusejp_86_;
}
v_reusejp_86_:
{
lean_object* v___x_89_; 
if (v_isShared_71_ == 0)
{
lean_ctor_set(v___x_70_, 4, v___x_87_);
v___x_89_ = v___x_70_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_env_61_);
lean_ctor_set(v_reuseFailAlloc_95_, 1, v_nextMacroScope_62_);
lean_ctor_set(v_reuseFailAlloc_95_, 2, v_ngen_63_);
lean_ctor_set(v_reuseFailAlloc_95_, 3, v_auxDeclNGen_64_);
lean_ctor_set(v_reuseFailAlloc_95_, 4, v___x_87_);
lean_ctor_set(v_reuseFailAlloc_95_, 5, v_cache_65_);
lean_ctor_set(v_reuseFailAlloc_95_, 6, v_messages_66_);
lean_ctor_set(v_reuseFailAlloc_95_, 7, v_infoState_67_);
lean_ctor_set(v_reuseFailAlloc_95_, 8, v_snapshotTasks_68_);
v___x_89_ = v_reuseFailAlloc_95_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_93_; 
v___x_90_ = lean_st_ref_set(v___y_51_, v___x_89_);
v___x_91_ = lean_box(0);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 0, v___x_91_);
v___x_93_ = v___x_57_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_94_; 
v_reuseFailAlloc_94_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_94_, 0, v___x_91_);
v___x_93_ = v_reuseFailAlloc_94_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
return v___x_93_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___boxed(lean_object* v_cls_100_, lean_object* v_msg_101_, lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v_cls_100_, v_msg_101_, v___y_102_, v___y_103_, v___y_104_, v___y_105_);
lean_dec(v___y_105_);
lean_dec_ref(v___y_104_);
lean_dec(v___y_103_);
lean_dec_ref(v___y_102_);
return v_res_107_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6(void){
_start:
{
lean_object* v_cls_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v_cls_118_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__3));
v___x_119_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_120_ = l_Lean_Name_append(v___x_119_, v_cls_118_);
return v___x_120_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__8(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_122_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__7));
v___x_123_ = l_Lean_stringToMessageData(v___x_122_);
return v___x_123_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = lean_unsigned_to_nat(0u);
v___x_125_ = lean_nat_to_int(v___x_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq(lean_object* v_a_126_, lean_object* v_x_127_, lean_object* v_c_u2081_128_, lean_object* v_b_129_, lean_object* v_c_u2082_130_, lean_object* v_a_131_, lean_object* v_a_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_){
_start:
{
lean_object* v___y_143_; lean_object* v___y_148_; lean_object* v_p_200_; lean_object* v_p_201_; lean_object* v___x_202_; uint8_t v___x_203_; 
v_p_200_ = lean_ctor_get(v_c_u2081_128_, 0);
v_p_201_ = lean_ctor_get(v_c_u2082_130_, 0);
v___x_202_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9);
v___x_203_ = lean_int_dec_le(v___x_202_, v_a_126_);
if (v___x_203_ == 0)
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
lean_inc_ref(v_p_200_);
v___x_204_ = l_Int_Linear_Poly_mul(v_p_200_, v_b_129_);
v___x_205_ = lean_int_neg(v_a_126_);
lean_inc_ref(v_p_201_);
v___x_206_ = l_Int_Linear_Poly_mul(v_p_201_, v___x_205_);
lean_dec(v___x_205_);
v___x_207_ = l_Int_Linear_Poly_combine(v___x_204_, v___x_206_);
v___y_148_ = v___x_207_;
goto v___jp_147_;
}
else
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
lean_inc_ref(v_p_201_);
v___x_208_ = l_Int_Linear_Poly_mul(v_p_201_, v_a_126_);
v___x_209_ = lean_int_neg(v_b_129_);
lean_inc_ref(v_p_200_);
v___x_210_ = l_Int_Linear_Poly_mul(v_p_200_, v___x_209_);
lean_dec(v___x_209_);
v___x_211_ = l_Int_Linear_Poly_combine(v___x_208_, v___x_210_);
v___y_148_ = v___x_211_;
goto v___jp_147_;
}
v___jp_142_:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_144_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v___x_144_, 0, v_x_127_);
lean_ctor_set(v___x_144_, 1, v_c_u2081_128_);
lean_ctor_set(v___x_144_, 2, v_c_u2082_130_);
v___x_145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_145_, 0, v___y_143_);
lean_ctor_set(v___x_145_, 1, v___x_144_);
v___x_146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_146_, 0, v___x_145_);
return v___x_146_;
}
v___jp_147_:
{
lean_object* v_options_149_; uint8_t v_hasTrace_150_; 
v_options_149_ = lean_ctor_get(v_a_139_, 2);
v_hasTrace_150_ = lean_ctor_get_uint8(v_options_149_, sizeof(void*)*1);
if (v_hasTrace_150_ == 0)
{
v___y_143_ = v___y_148_;
goto v___jp_142_;
}
else
{
lean_object* v_inheritedTraceOptions_151_; lean_object* v_cls_152_; lean_object* v___x_153_; uint8_t v___x_154_; 
v_inheritedTraceOptions_151_ = lean_ctor_get(v_a_139_, 13);
v_cls_152_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__3));
v___x_153_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6);
v___x_154_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_151_, v_options_149_, v___x_153_);
if (v___x_154_ == 0)
{
v___y_143_ = v___y_148_;
goto v___jp_142_;
}
else
{
lean_object* v___x_155_; 
v___x_155_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_x_127_, v_a_131_, v_a_139_);
if (lean_obj_tag(v___x_155_) == 0)
{
lean_object* v_a_156_; lean_object* v___x_157_; 
v_a_156_ = lean_ctor_get(v___x_155_, 0);
lean_inc(v_a_156_);
lean_dec_ref(v___x_155_);
lean_inc_ref(v_c_u2081_128_);
v___x_157_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_u2081_128_, v_a_131_, v_a_139_);
if (lean_obj_tag(v___x_157_) == 0)
{
lean_object* v_a_158_; lean_object* v___x_159_; 
v_a_158_ = lean_ctor_get(v___x_157_, 0);
lean_inc(v_a_158_);
lean_dec_ref(v___x_157_);
lean_inc_ref(v_c_u2082_130_);
v___x_159_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2082_130_, v_a_131_, v_a_139_);
if (lean_obj_tag(v___x_159_) == 0)
{
lean_object* v_a_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v_a_160_ = lean_ctor_get(v___x_159_, 0);
lean_inc(v_a_160_);
lean_dec_ref(v___x_159_);
v___x_161_ = l_Lean_MessageData_ofExpr(v_a_156_);
v___x_162_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__8);
v___x_163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_163_, 0, v___x_161_);
lean_ctor_set(v___x_163_, 1, v___x_162_);
v___x_164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
lean_ctor_set(v___x_164_, 1, v_a_158_);
v___x_165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
lean_ctor_set(v___x_165_, 1, v___x_162_);
v___x_166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_165_);
lean_ctor_set(v___x_166_, 1, v_a_160_);
v___x_167_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v_cls_152_, v___x_166_, v_a_137_, v_a_138_, v_a_139_, v_a_140_);
if (lean_obj_tag(v___x_167_) == 0)
{
lean_dec_ref(v___x_167_);
v___y_143_ = v___y_148_;
goto v___jp_142_;
}
else
{
lean_object* v_a_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_175_; 
lean_dec_ref(v___y_148_);
lean_dec_ref(v_c_u2082_130_);
lean_dec_ref(v_c_u2081_128_);
lean_dec(v_x_127_);
v_a_168_ = lean_ctor_get(v___x_167_, 0);
v_isSharedCheck_175_ = !lean_is_exclusive(v___x_167_);
if (v_isSharedCheck_175_ == 0)
{
v___x_170_ = v___x_167_;
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_a_168_);
lean_dec(v___x_167_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_175_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_173_; 
if (v_isShared_171_ == 0)
{
v___x_173_ = v___x_170_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v_a_168_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
else
{
lean_object* v_a_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_183_; 
lean_dec(v_a_158_);
lean_dec(v_a_156_);
lean_dec_ref(v___y_148_);
lean_dec_ref(v_c_u2082_130_);
lean_dec_ref(v_c_u2081_128_);
lean_dec(v_x_127_);
v_a_176_ = lean_ctor_get(v___x_159_, 0);
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_159_);
if (v_isSharedCheck_183_ == 0)
{
v___x_178_ = v___x_159_;
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_a_176_);
lean_dec(v___x_159_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_183_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v___x_181_; 
if (v_isShared_179_ == 0)
{
v___x_181_ = v___x_178_;
goto v_reusejp_180_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v_a_176_);
v___x_181_ = v_reuseFailAlloc_182_;
goto v_reusejp_180_;
}
v_reusejp_180_:
{
return v___x_181_;
}
}
}
}
else
{
lean_object* v_a_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_191_; 
lean_dec(v_a_156_);
lean_dec_ref(v___y_148_);
lean_dec_ref(v_c_u2082_130_);
lean_dec_ref(v_c_u2081_128_);
lean_dec(v_x_127_);
v_a_184_ = lean_ctor_get(v___x_157_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_157_);
if (v_isSharedCheck_191_ == 0)
{
v___x_186_ = v___x_157_;
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_a_184_);
lean_dec(v___x_157_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_191_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_189_; 
if (v_isShared_187_ == 0)
{
v___x_189_ = v___x_186_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v_a_184_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
}
else
{
lean_object* v_a_192_; lean_object* v___x_194_; uint8_t v_isShared_195_; uint8_t v_isSharedCheck_199_; 
lean_dec_ref(v___y_148_);
lean_dec_ref(v_c_u2082_130_);
lean_dec_ref(v_c_u2081_128_);
lean_dec(v_x_127_);
v_a_192_ = lean_ctor_get(v___x_155_, 0);
v_isSharedCheck_199_ = !lean_is_exclusive(v___x_155_);
if (v_isSharedCheck_199_ == 0)
{
v___x_194_ = v___x_155_;
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
else
{
lean_inc(v_a_192_);
lean_dec(v___x_155_);
v___x_194_ = lean_box(0);
v_isShared_195_ = v_isSharedCheck_199_;
goto v_resetjp_193_;
}
v_resetjp_193_:
{
lean_object* v___x_197_; 
if (v_isShared_195_ == 0)
{
v___x_197_ = v___x_194_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_198_; 
v_reuseFailAlloc_198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_198_, 0, v_a_192_);
v___x_197_ = v_reuseFailAlloc_198_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
return v___x_197_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___boxed(lean_object* v_a_212_, lean_object* v_x_213_, lean_object* v_c_u2081_214_, lean_object* v_b_215_, lean_object* v_c_u2082_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq(v_a_212_, v_x_213_, v_c_u2081_214_, v_b_215_, v_c_u2082_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
lean_dec(v_a_226_);
lean_dec_ref(v_a_225_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
lean_dec(v_a_222_);
lean_dec_ref(v_a_221_);
lean_dec(v_a_220_);
lean_dec_ref(v_a_219_);
lean_dec(v_a_218_);
lean_dec(v_a_217_);
lean_dec(v_b_215_);
lean_dec(v_a_212_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0(lean_object* v_cls_229_, lean_object* v_msg_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_){
_start:
{
lean_object* v___x_242_; 
v___x_242_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v_cls_229_, v_msg_230_, v___y_237_, v___y_238_, v___y_239_, v___y_240_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___boxed(lean_object* v_cls_243_, lean_object* v_msg_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0(v_cls_243_, v_msg_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_);
lean_dec(v___y_254_);
lean_dec_ref(v___y_253_);
lean_dec(v___y_252_);
lean_dec_ref(v___y_251_);
lean_dec(v___y_250_);
lean_dec_ref(v___y_249_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
lean_dec(v___y_246_);
lean_dec(v___y_245_);
return v_res_256_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_262_ = l_Lean_maxRecDepthErrorMessage;
v___x_263_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
return v___x_263_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__3);
v___x_265_ = l_Lean_MessageData_ofFormat(v___x_264_);
return v___x_265_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_266_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__4);
v___x_267_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__2));
v___x_268_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
lean_ctor_set(v___x_268_, 1, v___x_266_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg(lean_object* v_ref_269_){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_271_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__5);
v___x_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_272_, 0, v_ref_269_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
v___x_273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___boxed(lean_object* v_ref_274_, lean_object* v___y_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg(v_ref_274_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0(lean_object* v_00_u03b1_277_, lean_object* v_ref_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg(v_ref_278_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___boxed(lean_object* v_00_u03b1_291_, lean_object* v_ref_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0(v_00_u03b1_291_, v_ref_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
lean_dec(v___y_298_);
lean_dec_ref(v___y_297_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
lean_dec(v___y_294_);
lean_dec(v___y_293_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts(lean_object* v_c_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_){
_start:
{
lean_object* v_p_317_; lean_object* v_fileName_318_; lean_object* v_fileMap_319_; lean_object* v_options_320_; lean_object* v_currRecDepth_321_; lean_object* v_maxRecDepth_322_; lean_object* v_ref_323_; lean_object* v_currNamespace_324_; lean_object* v_openDecls_325_; lean_object* v_initHeartbeats_326_; lean_object* v_maxHeartbeats_327_; lean_object* v_quotContext_328_; lean_object* v_currMacroScope_329_; uint8_t v_diag_330_; lean_object* v_cancelTk_x3f_331_; uint8_t v_suppressElabErrors_332_; lean_object* v_inheritedTraceOptions_333_; lean_object* v___x_365_; uint8_t v___x_366_; 
v_p_317_ = lean_ctor_get(v_c_305_, 0);
v_fileName_318_ = lean_ctor_get(v_a_314_, 0);
lean_inc_ref(v_fileName_318_);
v_fileMap_319_ = lean_ctor_get(v_a_314_, 1);
lean_inc_ref(v_fileMap_319_);
v_options_320_ = lean_ctor_get(v_a_314_, 2);
lean_inc_ref(v_options_320_);
v_currRecDepth_321_ = lean_ctor_get(v_a_314_, 3);
lean_inc(v_currRecDepth_321_);
v_maxRecDepth_322_ = lean_ctor_get(v_a_314_, 4);
lean_inc(v_maxRecDepth_322_);
v_ref_323_ = lean_ctor_get(v_a_314_, 5);
lean_inc(v_ref_323_);
v_currNamespace_324_ = lean_ctor_get(v_a_314_, 6);
lean_inc(v_currNamespace_324_);
v_openDecls_325_ = lean_ctor_get(v_a_314_, 7);
lean_inc(v_openDecls_325_);
v_initHeartbeats_326_ = lean_ctor_get(v_a_314_, 8);
lean_inc(v_initHeartbeats_326_);
v_maxHeartbeats_327_ = lean_ctor_get(v_a_314_, 9);
lean_inc(v_maxHeartbeats_327_);
v_quotContext_328_ = lean_ctor_get(v_a_314_, 10);
lean_inc(v_quotContext_328_);
v_currMacroScope_329_ = lean_ctor_get(v_a_314_, 11);
lean_inc(v_currMacroScope_329_);
v_diag_330_ = lean_ctor_get_uint8(v_a_314_, sizeof(void*)*14);
v_cancelTk_x3f_331_ = lean_ctor_get(v_a_314_, 12);
lean_inc(v_cancelTk_x3f_331_);
v_suppressElabErrors_332_ = lean_ctor_get_uint8(v_a_314_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_333_ = lean_ctor_get(v_a_314_, 13);
lean_inc_ref(v_inheritedTraceOptions_333_);
lean_dec_ref(v_a_314_);
v___x_365_ = lean_unsigned_to_nat(0u);
v___x_366_ = lean_nat_dec_eq(v_maxRecDepth_322_, v___x_365_);
if (v___x_366_ == 0)
{
uint8_t v___x_367_; 
v___x_367_ = lean_nat_dec_eq(v_currRecDepth_321_, v_maxRecDepth_322_);
if (v___x_367_ == 0)
{
goto v___jp_334_;
}
else
{
lean_object* v___x_368_; 
lean_dec_ref(v_inheritedTraceOptions_333_);
lean_dec(v_cancelTk_x3f_331_);
lean_dec(v_currMacroScope_329_);
lean_dec(v_quotContext_328_);
lean_dec(v_maxHeartbeats_327_);
lean_dec(v_initHeartbeats_326_);
lean_dec(v_openDecls_325_);
lean_dec(v_currNamespace_324_);
lean_dec(v_maxRecDepth_322_);
lean_dec(v_currRecDepth_321_);
lean_dec_ref(v_options_320_);
lean_dec_ref(v_fileMap_319_);
lean_dec_ref(v_fileName_318_);
lean_dec_ref(v_c_305_);
v___x_368_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg(v_ref_323_);
return v___x_368_;
}
}
else
{
goto v___jp_334_;
}
v___jp_334_:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_335_ = lean_unsigned_to_nat(1u);
v___x_336_ = lean_nat_add(v_currRecDepth_321_, v___x_335_);
lean_dec(v_currRecDepth_321_);
v___x_337_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_337_, 0, v_fileName_318_);
lean_ctor_set(v___x_337_, 1, v_fileMap_319_);
lean_ctor_set(v___x_337_, 2, v_options_320_);
lean_ctor_set(v___x_337_, 3, v___x_336_);
lean_ctor_set(v___x_337_, 4, v_maxRecDepth_322_);
lean_ctor_set(v___x_337_, 5, v_ref_323_);
lean_ctor_set(v___x_337_, 6, v_currNamespace_324_);
lean_ctor_set(v___x_337_, 7, v_openDecls_325_);
lean_ctor_set(v___x_337_, 8, v_initHeartbeats_326_);
lean_ctor_set(v___x_337_, 9, v_maxHeartbeats_327_);
lean_ctor_set(v___x_337_, 10, v_quotContext_328_);
lean_ctor_set(v___x_337_, 11, v_currMacroScope_329_);
lean_ctor_set(v___x_337_, 12, v_cancelTk_x3f_331_);
lean_ctor_set(v___x_337_, 13, v_inheritedTraceOptions_333_);
lean_ctor_set_uint8(v___x_337_, sizeof(void*)*14, v_diag_330_);
lean_ctor_set_uint8(v___x_337_, sizeof(void*)*14 + 1, v_suppressElabErrors_332_);
lean_inc_ref(v_p_317_);
v___x_338_ = l_Int_Linear_Poly_findVarToSubst___redArg(v_p_317_, v_a_306_, v___x_337_);
if (lean_obj_tag(v___x_338_) == 0)
{
lean_object* v_a_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_356_; 
v_a_339_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_356_ == 0)
{
v___x_341_ = v___x_338_;
v_isShared_342_ = v_isSharedCheck_356_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_a_339_);
lean_dec(v___x_338_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_356_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
if (lean_obj_tag(v_a_339_) == 1)
{
lean_object* v_val_343_; lean_object* v_snd_344_; lean_object* v_snd_345_; lean_object* v_fst_346_; lean_object* v_fst_347_; lean_object* v_p_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
lean_del_object(v___x_341_);
v_val_343_ = lean_ctor_get(v_a_339_, 0);
lean_inc(v_val_343_);
lean_dec_ref(v_a_339_);
v_snd_344_ = lean_ctor_get(v_val_343_, 1);
lean_inc(v_snd_344_);
v_snd_345_ = lean_ctor_get(v_snd_344_, 1);
lean_inc(v_snd_345_);
v_fst_346_ = lean_ctor_get(v_val_343_, 0);
lean_inc(v_fst_346_);
lean_dec(v_val_343_);
v_fst_347_ = lean_ctor_get(v_snd_344_, 0);
lean_inc(v_fst_347_);
lean_dec(v_snd_344_);
v_p_348_ = lean_ctor_get(v_snd_345_, 0);
v___x_349_ = l_Int_Linear_Poly_coeff(v_p_348_, v_fst_347_);
v___x_350_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq(v___x_349_, v_fst_347_, v_snd_345_, v_fst_346_, v_c_305_, v_a_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_, v___x_337_, v_a_315_);
lean_dec(v_fst_346_);
lean_dec(v___x_349_);
if (lean_obj_tag(v___x_350_) == 0)
{
lean_object* v_a_351_; 
v_a_351_ = lean_ctor_get(v___x_350_, 0);
lean_inc(v_a_351_);
lean_dec_ref(v___x_350_);
v_c_305_ = v_a_351_;
v_a_314_ = v___x_337_;
goto _start;
}
else
{
lean_dec_ref(v___x_337_);
return v___x_350_;
}
}
else
{
lean_object* v___x_354_; 
lean_dec(v_a_339_);
lean_dec_ref(v___x_337_);
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 0, v_c_305_);
v___x_354_ = v___x_341_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_c_305_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
}
else
{
lean_object* v_a_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_364_; 
lean_dec_ref(v___x_337_);
lean_dec_ref(v_c_305_);
v_a_357_ = lean_ctor_get(v___x_338_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_338_);
if (v_isSharedCheck_364_ == 0)
{
v___x_359_ = v___x_338_;
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_dec(v___x_338_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_362_; 
if (v_isShared_360_ == 0)
{
v___x_362_ = v___x_359_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_a_357_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts___boxed(lean_object* v_c_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_){
_start:
{
lean_object* v_res_381_; 
v_res_381_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts(v_c_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_);
lean_dec(v_a_379_);
lean_dec(v_a_377_);
lean_dec_ref(v_a_376_);
lean_dec(v_a_375_);
lean_dec_ref(v_a_374_);
lean_dec(v_a_373_);
lean_dec_ref(v_a_372_);
lean_dec(v_a_371_);
lean_dec(v_a_370_);
return v_res_381_;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_Poly_isNegEq(lean_object* v_p_u2081_382_, lean_object* v_p_u2082_383_){
_start:
{
if (lean_obj_tag(v_p_u2081_382_) == 0)
{
if (lean_obj_tag(v_p_u2082_383_) == 0)
{
lean_object* v_k_384_; lean_object* v_k_385_; lean_object* v___x_386_; uint8_t v___x_387_; 
v_k_384_ = lean_ctor_get(v_p_u2081_382_, 0);
v_k_385_ = lean_ctor_get(v_p_u2082_383_, 0);
v___x_386_ = lean_int_neg(v_k_385_);
v___x_387_ = lean_int_dec_eq(v_k_384_, v___x_386_);
lean_dec(v___x_386_);
return v___x_387_;
}
else
{
uint8_t v___x_388_; 
v___x_388_ = 0;
return v___x_388_;
}
}
else
{
if (lean_obj_tag(v_p_u2082_383_) == 1)
{
lean_object* v_k_389_; lean_object* v_v_390_; lean_object* v_p_391_; lean_object* v_k_392_; lean_object* v_v_393_; lean_object* v_p_394_; uint8_t v___y_396_; lean_object* v___x_398_; uint8_t v___x_399_; 
v_k_389_ = lean_ctor_get(v_p_u2081_382_, 0);
v_v_390_ = lean_ctor_get(v_p_u2081_382_, 1);
v_p_391_ = lean_ctor_get(v_p_u2081_382_, 2);
v_k_392_ = lean_ctor_get(v_p_u2082_383_, 0);
v_v_393_ = lean_ctor_get(v_p_u2082_383_, 1);
v_p_394_ = lean_ctor_get(v_p_u2082_383_, 2);
v___x_398_ = lean_int_neg(v_k_392_);
v___x_399_ = lean_int_dec_eq(v_k_389_, v___x_398_);
lean_dec(v___x_398_);
if (v___x_399_ == 0)
{
v___y_396_ = v___x_399_;
goto v___jp_395_;
}
else
{
uint8_t v___x_400_; 
v___x_400_ = lean_nat_dec_eq(v_v_390_, v_v_393_);
v___y_396_ = v___x_400_;
goto v___jp_395_;
}
v___jp_395_:
{
if (v___y_396_ == 0)
{
return v___y_396_;
}
else
{
v_p_u2081_382_ = v_p_391_;
v_p_u2082_383_ = v_p_394_;
goto _start;
}
}
}
else
{
uint8_t v___x_401_; 
v___x_401_ = 0;
return v___x_401_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isNegEq___boxed(lean_object* v_p_u2081_402_, lean_object* v_p_u2082_403_){
_start:
{
uint8_t v_res_404_; lean_object* v_r_405_; 
v_res_404_ = l_Int_Linear_Poly_isNegEq(v_p_u2081_402_, v_p_u2082_403_);
lean_dec_ref(v_p_u2082_403_);
lean_dec_ref(v_p_u2081_402_);
v_r_405_ = lean_box(v_res_404_);
return v_r_405_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(lean_object* v___x_406_, lean_object* v_as_407_, size_t v_i_408_, size_t v_stop_409_, lean_object* v_b_410_){
_start:
{
lean_object* v___y_412_; uint8_t v___x_416_; 
v___x_416_ = lean_usize_dec_eq(v_i_408_, v_stop_409_);
if (v___x_416_ == 0)
{
lean_object* v___x_417_; lean_object* v_p_418_; uint8_t v___x_419_; 
v___x_417_ = lean_array_uget_borrowed(v_as_407_, v_i_408_);
v_p_418_ = lean_ctor_get(v___x_417_, 0);
v___x_419_ = l_Int_Linear_instBEqPoly_beq(v_p_418_, v___x_406_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; 
lean_inc(v___x_417_);
v___x_420_ = l_Lean_PersistentArray_push___redArg(v_b_410_, v___x_417_);
v___y_412_ = v___x_420_;
goto v___jp_411_;
}
else
{
v___y_412_ = v_b_410_;
goto v___jp_411_;
}
}
else
{
return v_b_410_;
}
v___jp_411_:
{
size_t v___x_413_; size_t v___x_414_; 
v___x_413_ = ((size_t)1ULL);
v___x_414_ = lean_usize_add(v_i_408_, v___x_413_);
v_i_408_ = v___x_414_;
v_b_410_ = v___y_412_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1___boxed(lean_object* v___x_421_, lean_object* v_as_422_, lean_object* v_i_423_, lean_object* v_stop_424_, lean_object* v_b_425_){
_start:
{
size_t v_i_boxed_426_; size_t v_stop_boxed_427_; lean_object* v_res_428_; 
v_i_boxed_426_ = lean_unbox_usize(v_i_423_);
lean_dec(v_i_423_);
v_stop_boxed_427_ = lean_unbox_usize(v_stop_424_);
lean_dec(v_stop_424_);
v_res_428_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_421_, v_as_422_, v_i_boxed_426_, v_stop_boxed_427_, v_b_425_);
lean_dec_ref(v_as_422_);
lean_dec_ref(v___x_421_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2(lean_object* v___x_429_, lean_object* v_x_430_, lean_object* v_x_431_){
_start:
{
if (lean_obj_tag(v_x_430_) == 0)
{
lean_object* v_cs_432_; lean_object* v___x_433_; lean_object* v___x_434_; uint8_t v___x_435_; 
v_cs_432_ = lean_ctor_get(v_x_430_, 0);
v___x_433_ = lean_unsigned_to_nat(0u);
v___x_434_ = lean_array_get_size(v_cs_432_);
v___x_435_ = lean_nat_dec_lt(v___x_433_, v___x_434_);
if (v___x_435_ == 0)
{
return v_x_431_;
}
else
{
uint8_t v___x_436_; 
v___x_436_ = lean_nat_dec_le(v___x_434_, v___x_434_);
if (v___x_436_ == 0)
{
if (v___x_435_ == 0)
{
return v_x_431_;
}
else
{
size_t v___x_437_; size_t v___x_438_; lean_object* v___x_439_; 
v___x_437_ = ((size_t)0ULL);
v___x_438_ = lean_usize_of_nat(v___x_434_);
v___x_439_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v___x_429_, v_cs_432_, v___x_437_, v___x_438_, v_x_431_);
return v___x_439_;
}
}
else
{
size_t v___x_440_; size_t v___x_441_; lean_object* v___x_442_; 
v___x_440_ = ((size_t)0ULL);
v___x_441_ = lean_usize_of_nat(v___x_434_);
v___x_442_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v___x_429_, v_cs_432_, v___x_440_, v___x_441_, v_x_431_);
return v___x_442_;
}
}
}
else
{
lean_object* v_vs_443_; lean_object* v___x_444_; lean_object* v___x_445_; uint8_t v___x_446_; 
v_vs_443_ = lean_ctor_get(v_x_430_, 0);
v___x_444_ = lean_unsigned_to_nat(0u);
v___x_445_ = lean_array_get_size(v_vs_443_);
v___x_446_ = lean_nat_dec_lt(v___x_444_, v___x_445_);
if (v___x_446_ == 0)
{
return v_x_431_;
}
else
{
uint8_t v___x_447_; 
v___x_447_ = lean_nat_dec_le(v___x_445_, v___x_445_);
if (v___x_447_ == 0)
{
if (v___x_446_ == 0)
{
return v_x_431_;
}
else
{
size_t v___x_448_; size_t v___x_449_; lean_object* v___x_450_; 
v___x_448_ = ((size_t)0ULL);
v___x_449_ = lean_usize_of_nat(v___x_445_);
v___x_450_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_429_, v_vs_443_, v___x_448_, v___x_449_, v_x_431_);
return v___x_450_;
}
}
else
{
size_t v___x_451_; size_t v___x_452_; lean_object* v___x_453_; 
v___x_451_ = ((size_t)0ULL);
v___x_452_ = lean_usize_of_nat(v___x_445_);
v___x_453_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_429_, v_vs_443_, v___x_451_, v___x_452_, v_x_431_);
return v___x_453_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(lean_object* v___x_454_, lean_object* v_as_455_, size_t v_i_456_, size_t v_stop_457_, lean_object* v_b_458_){
_start:
{
uint8_t v___x_459_; 
v___x_459_ = lean_usize_dec_eq(v_i_456_, v_stop_457_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; lean_object* v___x_461_; size_t v___x_462_; size_t v___x_463_; 
v___x_460_ = lean_array_uget_borrowed(v_as_455_, v_i_456_);
v___x_461_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2(v___x_454_, v___x_460_, v_b_458_);
v___x_462_ = ((size_t)1ULL);
v___x_463_ = lean_usize_add(v_i_456_, v___x_462_);
v_i_456_ = v___x_463_;
v_b_458_ = v___x_461_;
goto _start;
}
else
{
return v_b_458_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1___boxed(lean_object* v___x_465_, lean_object* v_as_466_, lean_object* v_i_467_, lean_object* v_stop_468_, lean_object* v_b_469_){
_start:
{
size_t v_i_boxed_470_; size_t v_stop_boxed_471_; lean_object* v_res_472_; 
v_i_boxed_470_ = lean_unbox_usize(v_i_467_);
lean_dec(v_i_467_);
v_stop_boxed_471_ = lean_unbox_usize(v_stop_468_);
lean_dec(v_stop_468_);
v_res_472_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v___x_465_, v_as_466_, v_i_boxed_470_, v_stop_boxed_471_, v_b_469_);
lean_dec_ref(v_as_466_);
lean_dec_ref(v___x_465_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2___boxed(lean_object* v___x_473_, lean_object* v_x_474_, lean_object* v_x_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2(v___x_473_, v_x_474_, v_x_475_);
lean_dec_ref(v_x_474_);
lean_dec_ref(v___x_473_);
return v_res_476_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(lean_object* v___x_478_, lean_object* v_x_479_, size_t v_x_480_, size_t v_x_481_, lean_object* v_x_482_){
_start:
{
if (lean_obj_tag(v_x_479_) == 0)
{
lean_object* v_cs_483_; lean_object* v___x_484_; size_t v___x_485_; lean_object* v_j_486_; lean_object* v___x_487_; size_t v___x_488_; size_t v___x_489_; size_t v___x_490_; size_t v___x_491_; size_t v___x_492_; size_t v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; uint8_t v___x_498_; 
v_cs_483_ = lean_ctor_get(v_x_479_, 0);
v___x_484_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0);
v___x_485_ = lean_usize_shift_right(v_x_480_, v_x_481_);
v_j_486_ = lean_usize_to_nat(v___x_485_);
v___x_487_ = lean_array_get_borrowed(v___x_484_, v_cs_483_, v_j_486_);
v___x_488_ = ((size_t)1ULL);
v___x_489_ = lean_usize_shift_left(v___x_488_, v_x_481_);
v___x_490_ = lean_usize_sub(v___x_489_, v___x_488_);
v___x_491_ = lean_usize_land(v_x_480_, v___x_490_);
v___x_492_ = ((size_t)5ULL);
v___x_493_ = lean_usize_sub(v_x_481_, v___x_492_);
v___x_494_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(v___x_478_, v___x_487_, v___x_491_, v___x_493_, v_x_482_);
v___x_495_ = lean_unsigned_to_nat(1u);
v___x_496_ = lean_nat_add(v_j_486_, v___x_495_);
lean_dec(v_j_486_);
v___x_497_ = lean_array_get_size(v_cs_483_);
v___x_498_ = lean_nat_dec_lt(v___x_496_, v___x_497_);
if (v___x_498_ == 0)
{
lean_dec(v___x_496_);
return v___x_494_;
}
else
{
uint8_t v___x_499_; 
v___x_499_ = lean_nat_dec_le(v___x_497_, v___x_497_);
if (v___x_499_ == 0)
{
if (v___x_498_ == 0)
{
lean_dec(v___x_496_);
return v___x_494_;
}
else
{
size_t v___x_500_; size_t v___x_501_; lean_object* v___x_502_; 
v___x_500_ = lean_usize_of_nat(v___x_496_);
lean_dec(v___x_496_);
v___x_501_ = lean_usize_of_nat(v___x_497_);
v___x_502_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v___x_478_, v_cs_483_, v___x_500_, v___x_501_, v___x_494_);
return v___x_502_;
}
}
else
{
size_t v___x_503_; size_t v___x_504_; lean_object* v___x_505_; 
v___x_503_ = lean_usize_of_nat(v___x_496_);
lean_dec(v___x_496_);
v___x_504_ = lean_usize_of_nat(v___x_497_);
v___x_505_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v___x_478_, v_cs_483_, v___x_503_, v___x_504_, v___x_494_);
return v___x_505_;
}
}
}
else
{
lean_object* v_vs_506_; lean_object* v___x_507_; lean_object* v___x_508_; uint8_t v___x_509_; 
v_vs_506_ = lean_ctor_get(v_x_479_, 0);
v___x_507_ = lean_usize_to_nat(v_x_480_);
v___x_508_ = lean_array_get_size(v_vs_506_);
v___x_509_ = lean_nat_dec_lt(v___x_507_, v___x_508_);
if (v___x_509_ == 0)
{
lean_dec(v___x_507_);
return v_x_482_;
}
else
{
uint8_t v___x_510_; 
v___x_510_ = lean_nat_dec_le(v___x_508_, v___x_508_);
if (v___x_510_ == 0)
{
if (v___x_509_ == 0)
{
lean_dec(v___x_507_);
return v_x_482_;
}
else
{
size_t v___x_511_; size_t v___x_512_; lean_object* v___x_513_; 
v___x_511_ = lean_usize_of_nat(v___x_507_);
lean_dec(v___x_507_);
v___x_512_ = lean_usize_of_nat(v___x_508_);
v___x_513_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_478_, v_vs_506_, v___x_511_, v___x_512_, v_x_482_);
return v___x_513_;
}
}
else
{
size_t v___x_514_; size_t v___x_515_; lean_object* v___x_516_; 
v___x_514_ = lean_usize_of_nat(v___x_507_);
lean_dec(v___x_507_);
v___x_515_ = lean_usize_of_nat(v___x_508_);
v___x_516_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_478_, v_vs_506_, v___x_514_, v___x_515_, v_x_482_);
return v___x_516_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___boxed(lean_object* v___x_517_, lean_object* v_x_518_, lean_object* v_x_519_, lean_object* v_x_520_, lean_object* v_x_521_){
_start:
{
size_t v_x_2065__boxed_522_; size_t v_x_2066__boxed_523_; lean_object* v_res_524_; 
v_x_2065__boxed_522_ = lean_unbox_usize(v_x_519_);
lean_dec(v_x_519_);
v_x_2066__boxed_523_ = lean_unbox_usize(v_x_520_);
lean_dec(v_x_520_);
v_res_524_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(v___x_517_, v_x_518_, v_x_2065__boxed_522_, v_x_2066__boxed_523_, v_x_521_);
lean_dec_ref(v_x_518_);
lean_dec_ref(v___x_517_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(lean_object* v___x_525_, lean_object* v_t_526_, lean_object* v_init_527_, lean_object* v_start_528_){
_start:
{
lean_object* v___x_529_; uint8_t v___x_530_; 
v___x_529_ = lean_unsigned_to_nat(0u);
v___x_530_ = lean_nat_dec_eq(v_start_528_, v___x_529_);
if (v___x_530_ == 0)
{
lean_object* v_root_531_; lean_object* v_tail_532_; size_t v_shift_533_; lean_object* v_tailOff_534_; uint8_t v___x_535_; 
v_root_531_ = lean_ctor_get(v_t_526_, 0);
v_tail_532_ = lean_ctor_get(v_t_526_, 1);
v_shift_533_ = lean_ctor_get_usize(v_t_526_, 4);
v_tailOff_534_ = lean_ctor_get(v_t_526_, 3);
v___x_535_ = lean_nat_dec_le(v_tailOff_534_, v_start_528_);
if (v___x_535_ == 0)
{
size_t v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; uint8_t v___x_539_; 
v___x_536_ = lean_usize_of_nat(v_start_528_);
v___x_537_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(v___x_525_, v_root_531_, v___x_536_, v_shift_533_, v_init_527_);
v___x_538_ = lean_array_get_size(v_tail_532_);
v___x_539_ = lean_nat_dec_lt(v___x_529_, v___x_538_);
if (v___x_539_ == 0)
{
return v___x_537_;
}
else
{
uint8_t v___x_540_; 
v___x_540_ = lean_nat_dec_le(v___x_538_, v___x_538_);
if (v___x_540_ == 0)
{
if (v___x_539_ == 0)
{
return v___x_537_;
}
else
{
size_t v___x_541_; size_t v___x_542_; lean_object* v___x_543_; 
v___x_541_ = ((size_t)0ULL);
v___x_542_ = lean_usize_of_nat(v___x_538_);
v___x_543_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_525_, v_tail_532_, v___x_541_, v___x_542_, v___x_537_);
return v___x_543_;
}
}
else
{
size_t v___x_544_; size_t v___x_545_; lean_object* v___x_546_; 
v___x_544_ = ((size_t)0ULL);
v___x_545_ = lean_usize_of_nat(v___x_538_);
v___x_546_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_525_, v_tail_532_, v___x_544_, v___x_545_, v___x_537_);
return v___x_546_;
}
}
}
else
{
lean_object* v___x_547_; lean_object* v___x_548_; uint8_t v___x_549_; 
v___x_547_ = lean_nat_sub(v_start_528_, v_tailOff_534_);
v___x_548_ = lean_array_get_size(v_tail_532_);
v___x_549_ = lean_nat_dec_lt(v___x_547_, v___x_548_);
if (v___x_549_ == 0)
{
lean_dec(v___x_547_);
return v_init_527_;
}
else
{
uint8_t v___x_550_; 
v___x_550_ = lean_nat_dec_le(v___x_548_, v___x_548_);
if (v___x_550_ == 0)
{
if (v___x_549_ == 0)
{
lean_dec(v___x_547_);
return v_init_527_;
}
else
{
size_t v___x_551_; size_t v___x_552_; lean_object* v___x_553_; 
v___x_551_ = lean_usize_of_nat(v___x_547_);
lean_dec(v___x_547_);
v___x_552_ = lean_usize_of_nat(v___x_548_);
v___x_553_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_525_, v_tail_532_, v___x_551_, v___x_552_, v_init_527_);
return v___x_553_;
}
}
else
{
size_t v___x_554_; size_t v___x_555_; lean_object* v___x_556_; 
v___x_554_ = lean_usize_of_nat(v___x_547_);
lean_dec(v___x_547_);
v___x_555_ = lean_usize_of_nat(v___x_548_);
v___x_556_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_525_, v_tail_532_, v___x_554_, v___x_555_, v_init_527_);
return v___x_556_;
}
}
}
}
else
{
lean_object* v_root_557_; lean_object* v_tail_558_; lean_object* v___x_559_; lean_object* v___x_560_; uint8_t v___x_561_; 
v_root_557_ = lean_ctor_get(v_t_526_, 0);
v_tail_558_ = lean_ctor_get(v_t_526_, 1);
v___x_559_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2(v___x_525_, v_root_557_, v_init_527_);
v___x_560_ = lean_array_get_size(v_tail_558_);
v___x_561_ = lean_nat_dec_lt(v___x_529_, v___x_560_);
if (v___x_561_ == 0)
{
return v___x_559_;
}
else
{
uint8_t v___x_562_; 
v___x_562_ = lean_nat_dec_le(v___x_560_, v___x_560_);
if (v___x_562_ == 0)
{
if (v___x_561_ == 0)
{
return v___x_559_;
}
else
{
size_t v___x_563_; size_t v___x_564_; lean_object* v___x_565_; 
v___x_563_ = ((size_t)0ULL);
v___x_564_ = lean_usize_of_nat(v___x_560_);
v___x_565_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_525_, v_tail_558_, v___x_563_, v___x_564_, v___x_559_);
return v___x_565_;
}
}
else
{
size_t v___x_566_; size_t v___x_567_; lean_object* v___x_568_; 
v___x_566_ = ((size_t)0ULL);
v___x_567_ = lean_usize_of_nat(v___x_560_);
v___x_568_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_525_, v_tail_558_, v___x_566_, v___x_567_, v___x_559_);
return v___x_568_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0___boxed(lean_object* v___x_569_, lean_object* v_t_570_, lean_object* v_init_571_, lean_object* v_start_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(v___x_569_, v_t_570_, v_init_571_, v_start_572_);
lean_dec(v_start_572_);
lean_dec_ref(v_t_570_);
lean_dec_ref(v___x_569_);
return v_res_573_;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_574_ = lean_unsigned_to_nat(32u);
v___x_575_ = lean_mk_empty_array_with_capacity(v___x_574_);
v___x_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
return v___x_576_;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1(void){
_start:
{
size_t v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_577_ = ((size_t)5ULL);
v___x_578_ = lean_unsigned_to_nat(0u);
v___x_579_ = lean_unsigned_to_nat(32u);
v___x_580_ = lean_mk_empty_array_with_capacity(v___x_579_);
v___x_581_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__0, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__0_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__0);
v___x_582_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_582_, 0, v___x_581_);
lean_ctor_set(v___x_582_, 1, v___x_580_);
lean_ctor_set(v___x_582_, 2, v___x_578_);
lean_ctor_set(v___x_582_, 3, v___x_578_);
lean_ctor_set_usize(v___x_582_, 4, v___x_577_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4(lean_object* v___x_583_, lean_object* v_x_584_, size_t v_x_585_, size_t v_x_586_){
_start:
{
if (lean_obj_tag(v_x_584_) == 0)
{
lean_object* v_cs_587_; size_t v_j_588_; lean_object* v___x_589_; lean_object* v___x_590_; uint8_t v___x_591_; 
v_cs_587_ = lean_ctor_get(v_x_584_, 0);
v_j_588_ = lean_usize_shift_right(v_x_585_, v_x_586_);
v___x_589_ = lean_usize_to_nat(v_j_588_);
v___x_590_ = lean_array_get_size(v_cs_587_);
v___x_591_ = lean_nat_dec_lt(v___x_589_, v___x_590_);
if (v___x_591_ == 0)
{
lean_dec(v___x_589_);
return v_x_584_;
}
else
{
lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_609_; 
lean_inc_ref(v_cs_587_);
v_isSharedCheck_609_ = !lean_is_exclusive(v_x_584_);
if (v_isSharedCheck_609_ == 0)
{
lean_object* v_unused_610_; 
v_unused_610_ = lean_ctor_get(v_x_584_, 0);
lean_dec(v_unused_610_);
v___x_593_ = v_x_584_;
v_isShared_594_ = v_isSharedCheck_609_;
goto v_resetjp_592_;
}
else
{
lean_dec(v_x_584_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_609_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
size_t v___x_595_; size_t v___x_596_; size_t v___x_597_; size_t v_i_598_; size_t v___x_599_; size_t v_shift_600_; lean_object* v_v_601_; lean_object* v___x_602_; lean_object* v_xs_x27_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_607_; 
v___x_595_ = ((size_t)1ULL);
v___x_596_ = lean_usize_shift_left(v___x_595_, v_x_586_);
v___x_597_ = lean_usize_sub(v___x_596_, v___x_595_);
v_i_598_ = lean_usize_land(v_x_585_, v___x_597_);
v___x_599_ = ((size_t)5ULL);
v_shift_600_ = lean_usize_sub(v_x_586_, v___x_599_);
v_v_601_ = lean_array_fget(v_cs_587_, v___x_589_);
v___x_602_ = lean_box(0);
v_xs_x27_603_ = lean_array_fset(v_cs_587_, v___x_589_, v___x_602_);
v___x_604_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4(v___x_583_, v_v_601_, v_i_598_, v_shift_600_);
v___x_605_ = lean_array_fset(v_xs_x27_603_, v___x_589_, v___x_604_);
lean_dec(v___x_589_);
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_605_);
v___x_607_ = v___x_593_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_605_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
}
else
{
lean_object* v_vs_611_; lean_object* v___x_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v_vs_611_ = lean_ctor_get(v_x_584_, 0);
v___x_612_ = lean_usize_to_nat(v_x_585_);
v___x_613_ = lean_array_get_size(v_vs_611_);
v___x_614_ = lean_nat_dec_lt(v___x_612_, v___x_613_);
if (v___x_614_ == 0)
{
lean_dec(v___x_612_);
return v_x_584_;
}
else
{
lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_628_; 
lean_inc_ref(v_vs_611_);
v_isSharedCheck_628_ = !lean_is_exclusive(v_x_584_);
if (v_isSharedCheck_628_ == 0)
{
lean_object* v_unused_629_; 
v_unused_629_ = lean_ctor_get(v_x_584_, 0);
lean_dec(v_unused_629_);
v___x_616_ = v_x_584_;
v_isShared_617_ = v_isSharedCheck_628_;
goto v_resetjp_615_;
}
else
{
lean_dec(v_x_584_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_628_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v_v_618_; lean_object* v___x_619_; lean_object* v_xs_x27_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_626_; 
v_v_618_ = lean_array_fget(v_vs_611_, v___x_612_);
v___x_619_ = lean_box(0);
v_xs_x27_620_ = lean_array_fset(v_vs_611_, v___x_612_, v___x_619_);
v___x_621_ = lean_unsigned_to_nat(0u);
v___x_622_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1);
v___x_623_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(v___x_583_, v_v_618_, v___x_622_, v___x_621_);
lean_dec(v_v_618_);
v___x_624_ = lean_array_fset(v_xs_x27_620_, v___x_612_, v___x_623_);
lean_dec(v___x_612_);
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 0, v___x_624_);
v___x_626_ = v___x_616_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v___x_624_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___boxed(lean_object* v___x_630_, lean_object* v_x_631_, lean_object* v_x_632_, lean_object* v_x_633_){
_start:
{
size_t v_x_2238__boxed_634_; size_t v_x_2239__boxed_635_; lean_object* v_res_636_; 
v_x_2238__boxed_634_ = lean_unbox_usize(v_x_632_);
lean_dec(v_x_632_);
v_x_2239__boxed_635_ = lean_unbox_usize(v_x_633_);
lean_dec(v_x_633_);
v_res_636_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4(v___x_630_, v_x_631_, v_x_2238__boxed_634_, v_x_2239__boxed_635_);
lean_dec_ref(v___x_630_);
return v_res_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(lean_object* v___x_637_, lean_object* v_t_638_, lean_object* v_i_639_){
_start:
{
lean_object* v_root_640_; lean_object* v_tail_641_; lean_object* v_size_642_; size_t v_shift_643_; lean_object* v_tailOff_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_672_; 
v_root_640_ = lean_ctor_get(v_t_638_, 0);
v_tail_641_ = lean_ctor_get(v_t_638_, 1);
v_size_642_ = lean_ctor_get(v_t_638_, 2);
v_shift_643_ = lean_ctor_get_usize(v_t_638_, 4);
v_tailOff_644_ = lean_ctor_get(v_t_638_, 3);
v_isSharedCheck_672_ = !lean_is_exclusive(v_t_638_);
if (v_isSharedCheck_672_ == 0)
{
v___x_646_ = v_t_638_;
v_isShared_647_ = v_isSharedCheck_672_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_tailOff_644_);
lean_inc(v_size_642_);
lean_inc(v_tail_641_);
lean_inc(v_root_640_);
lean_dec(v_t_638_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_672_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
uint8_t v___x_648_; 
v___x_648_ = lean_nat_dec_le(v_tailOff_644_, v_i_639_);
if (v___x_648_ == 0)
{
size_t v___x_649_; lean_object* v___x_650_; lean_object* v___x_652_; 
v___x_649_ = lean_usize_of_nat(v_i_639_);
v___x_650_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4(v___x_637_, v_root_640_, v___x_649_, v_shift_643_);
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 0, v___x_650_);
v___x_652_ = v___x_646_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_650_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v_tail_641_);
lean_ctor_set(v_reuseFailAlloc_653_, 2, v_size_642_);
lean_ctor_set(v_reuseFailAlloc_653_, 3, v_tailOff_644_);
lean_ctor_set_usize(v_reuseFailAlloc_653_, 4, v_shift_643_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
else
{
lean_object* v___x_654_; lean_object* v___x_655_; uint8_t v___x_656_; 
v___x_654_ = lean_nat_sub(v_i_639_, v_tailOff_644_);
v___x_655_ = lean_array_get_size(v_tail_641_);
v___x_656_ = lean_nat_dec_lt(v___x_654_, v___x_655_);
if (v___x_656_ == 0)
{
lean_object* v___x_658_; 
lean_dec(v___x_654_);
if (v_isShared_647_ == 0)
{
v___x_658_ = v___x_646_;
goto v_reusejp_657_;
}
else
{
lean_object* v_reuseFailAlloc_659_; 
v_reuseFailAlloc_659_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_659_, 0, v_root_640_);
lean_ctor_set(v_reuseFailAlloc_659_, 1, v_tail_641_);
lean_ctor_set(v_reuseFailAlloc_659_, 2, v_size_642_);
lean_ctor_set(v_reuseFailAlloc_659_, 3, v_tailOff_644_);
lean_ctor_set_usize(v_reuseFailAlloc_659_, 4, v_shift_643_);
v___x_658_ = v_reuseFailAlloc_659_;
goto v_reusejp_657_;
}
v_reusejp_657_:
{
return v___x_658_;
}
}
else
{
lean_object* v_v_660_; lean_object* v___x_661_; lean_object* v_xs_x27_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_670_; 
v_v_660_ = lean_array_fget(v_tail_641_, v___x_654_);
v___x_661_ = lean_box(0);
v_xs_x27_662_ = lean_array_fset(v_tail_641_, v___x_654_, v___x_661_);
v___x_663_ = lean_unsigned_to_nat(32u);
v___x_664_ = lean_mk_empty_array_with_capacity(v___x_663_);
lean_dec_ref(v___x_664_);
v___x_665_ = lean_unsigned_to_nat(0u);
v___x_666_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1);
v___x_667_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(v___x_637_, v_v_660_, v___x_666_, v___x_665_);
lean_dec(v_v_660_);
v___x_668_ = lean_array_fset(v_xs_x27_662_, v___x_654_, v___x_667_);
lean_dec(v___x_654_);
if (v_isShared_647_ == 0)
{
lean_ctor_set(v___x_646_, 1, v___x_668_);
v___x_670_ = v___x_646_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_root_640_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v___x_668_);
lean_ctor_set(v_reuseFailAlloc_671_, 2, v_size_642_);
lean_ctor_set(v_reuseFailAlloc_671_, 3, v_tailOff_644_);
lean_ctor_set_usize(v_reuseFailAlloc_671_, 4, v_shift_643_);
v___x_670_ = v_reuseFailAlloc_671_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
return v___x_670_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1___boxed(lean_object* v___x_673_, lean_object* v_t_674_, lean_object* v_i_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(v___x_673_, v_t_674_, v_i_675_);
lean_dec(v_i_675_);
lean_dec_ref(v___x_673_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0(lean_object* v_p_677_, lean_object* v_v_678_, lean_object* v_s_679_){
_start:
{
lean_object* v_vars_680_; lean_object* v_varMap_681_; lean_object* v_vars_x27_682_; lean_object* v_varMap_x27_683_; lean_object* v_natToIntMap_684_; lean_object* v_natDef_685_; lean_object* v_dvds_686_; lean_object* v_lowers_687_; lean_object* v_uppers_688_; lean_object* v_diseqs_689_; lean_object* v_elimEqs_690_; lean_object* v_elimStack_691_; lean_object* v_occurs_692_; lean_object* v_assignment_693_; lean_object* v_nextCnstrId_694_; uint8_t v_caseSplits_695_; lean_object* v_conflict_x3f_696_; lean_object* v_diseqSplits_697_; lean_object* v_divMod_698_; lean_object* v_toIntIds_699_; lean_object* v_toIntInfos_700_; lean_object* v_toIntTermMap_701_; lean_object* v_toIntVarMap_702_; uint8_t v_usedCommRing_703_; lean_object* v_nonlinearOccs_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_712_; 
v_vars_680_ = lean_ctor_get(v_s_679_, 0);
v_varMap_681_ = lean_ctor_get(v_s_679_, 1);
v_vars_x27_682_ = lean_ctor_get(v_s_679_, 2);
v_varMap_x27_683_ = lean_ctor_get(v_s_679_, 3);
v_natToIntMap_684_ = lean_ctor_get(v_s_679_, 4);
v_natDef_685_ = lean_ctor_get(v_s_679_, 5);
v_dvds_686_ = lean_ctor_get(v_s_679_, 6);
v_lowers_687_ = lean_ctor_get(v_s_679_, 7);
v_uppers_688_ = lean_ctor_get(v_s_679_, 8);
v_diseqs_689_ = lean_ctor_get(v_s_679_, 9);
v_elimEqs_690_ = lean_ctor_get(v_s_679_, 10);
v_elimStack_691_ = lean_ctor_get(v_s_679_, 11);
v_occurs_692_ = lean_ctor_get(v_s_679_, 12);
v_assignment_693_ = lean_ctor_get(v_s_679_, 13);
v_nextCnstrId_694_ = lean_ctor_get(v_s_679_, 14);
v_caseSplits_695_ = lean_ctor_get_uint8(v_s_679_, sizeof(void*)*23);
v_conflict_x3f_696_ = lean_ctor_get(v_s_679_, 15);
v_diseqSplits_697_ = lean_ctor_get(v_s_679_, 16);
v_divMod_698_ = lean_ctor_get(v_s_679_, 17);
v_toIntIds_699_ = lean_ctor_get(v_s_679_, 18);
v_toIntInfos_700_ = lean_ctor_get(v_s_679_, 19);
v_toIntTermMap_701_ = lean_ctor_get(v_s_679_, 20);
v_toIntVarMap_702_ = lean_ctor_get(v_s_679_, 21);
v_usedCommRing_703_ = lean_ctor_get_uint8(v_s_679_, sizeof(void*)*23 + 1);
v_nonlinearOccs_704_ = lean_ctor_get(v_s_679_, 22);
v_isSharedCheck_712_ = !lean_is_exclusive(v_s_679_);
if (v_isSharedCheck_712_ == 0)
{
v___x_706_ = v_s_679_;
v_isShared_707_ = v_isSharedCheck_712_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_nonlinearOccs_704_);
lean_inc(v_toIntVarMap_702_);
lean_inc(v_toIntTermMap_701_);
lean_inc(v_toIntInfos_700_);
lean_inc(v_toIntIds_699_);
lean_inc(v_divMod_698_);
lean_inc(v_diseqSplits_697_);
lean_inc(v_conflict_x3f_696_);
lean_inc(v_nextCnstrId_694_);
lean_inc(v_assignment_693_);
lean_inc(v_occurs_692_);
lean_inc(v_elimStack_691_);
lean_inc(v_elimEqs_690_);
lean_inc(v_diseqs_689_);
lean_inc(v_uppers_688_);
lean_inc(v_lowers_687_);
lean_inc(v_dvds_686_);
lean_inc(v_natDef_685_);
lean_inc(v_natToIntMap_684_);
lean_inc(v_varMap_x27_683_);
lean_inc(v_vars_x27_682_);
lean_inc(v_varMap_681_);
lean_inc(v_vars_680_);
lean_dec(v_s_679_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_712_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_708_; lean_object* v___x_710_; 
v___x_708_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(v_p_677_, v_uppers_688_, v_v_678_);
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 8, v___x_708_);
v___x_710_ = v___x_706_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_711_; 
v_reuseFailAlloc_711_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_711_, 0, v_vars_680_);
lean_ctor_set(v_reuseFailAlloc_711_, 1, v_varMap_681_);
lean_ctor_set(v_reuseFailAlloc_711_, 2, v_vars_x27_682_);
lean_ctor_set(v_reuseFailAlloc_711_, 3, v_varMap_x27_683_);
lean_ctor_set(v_reuseFailAlloc_711_, 4, v_natToIntMap_684_);
lean_ctor_set(v_reuseFailAlloc_711_, 5, v_natDef_685_);
lean_ctor_set(v_reuseFailAlloc_711_, 6, v_dvds_686_);
lean_ctor_set(v_reuseFailAlloc_711_, 7, v_lowers_687_);
lean_ctor_set(v_reuseFailAlloc_711_, 8, v___x_708_);
lean_ctor_set(v_reuseFailAlloc_711_, 9, v_diseqs_689_);
lean_ctor_set(v_reuseFailAlloc_711_, 10, v_elimEqs_690_);
lean_ctor_set(v_reuseFailAlloc_711_, 11, v_elimStack_691_);
lean_ctor_set(v_reuseFailAlloc_711_, 12, v_occurs_692_);
lean_ctor_set(v_reuseFailAlloc_711_, 13, v_assignment_693_);
lean_ctor_set(v_reuseFailAlloc_711_, 14, v_nextCnstrId_694_);
lean_ctor_set(v_reuseFailAlloc_711_, 15, v_conflict_x3f_696_);
lean_ctor_set(v_reuseFailAlloc_711_, 16, v_diseqSplits_697_);
lean_ctor_set(v_reuseFailAlloc_711_, 17, v_divMod_698_);
lean_ctor_set(v_reuseFailAlloc_711_, 18, v_toIntIds_699_);
lean_ctor_set(v_reuseFailAlloc_711_, 19, v_toIntInfos_700_);
lean_ctor_set(v_reuseFailAlloc_711_, 20, v_toIntTermMap_701_);
lean_ctor_set(v_reuseFailAlloc_711_, 21, v_toIntVarMap_702_);
lean_ctor_set(v_reuseFailAlloc_711_, 22, v_nonlinearOccs_704_);
lean_ctor_set_uint8(v_reuseFailAlloc_711_, sizeof(void*)*23, v_caseSplits_695_);
lean_ctor_set_uint8(v_reuseFailAlloc_711_, sizeof(void*)*23 + 1, v_usedCommRing_703_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___boxed(lean_object* v_p_713_, lean_object* v_v_714_, lean_object* v_s_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0(v_p_713_, v_v_714_, v_s_715_);
lean_dec(v_v_714_);
lean_dec_ref(v_p_713_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1(lean_object* v_p_717_, lean_object* v_v_718_, lean_object* v_s_719_){
_start:
{
lean_object* v_vars_720_; lean_object* v_varMap_721_; lean_object* v_vars_x27_722_; lean_object* v_varMap_x27_723_; lean_object* v_natToIntMap_724_; lean_object* v_natDef_725_; lean_object* v_dvds_726_; lean_object* v_lowers_727_; lean_object* v_uppers_728_; lean_object* v_diseqs_729_; lean_object* v_elimEqs_730_; lean_object* v_elimStack_731_; lean_object* v_occurs_732_; lean_object* v_assignment_733_; lean_object* v_nextCnstrId_734_; uint8_t v_caseSplits_735_; lean_object* v_conflict_x3f_736_; lean_object* v_diseqSplits_737_; lean_object* v_divMod_738_; lean_object* v_toIntIds_739_; lean_object* v_toIntInfos_740_; lean_object* v_toIntTermMap_741_; lean_object* v_toIntVarMap_742_; uint8_t v_usedCommRing_743_; lean_object* v_nonlinearOccs_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_752_; 
v_vars_720_ = lean_ctor_get(v_s_719_, 0);
v_varMap_721_ = lean_ctor_get(v_s_719_, 1);
v_vars_x27_722_ = lean_ctor_get(v_s_719_, 2);
v_varMap_x27_723_ = lean_ctor_get(v_s_719_, 3);
v_natToIntMap_724_ = lean_ctor_get(v_s_719_, 4);
v_natDef_725_ = lean_ctor_get(v_s_719_, 5);
v_dvds_726_ = lean_ctor_get(v_s_719_, 6);
v_lowers_727_ = lean_ctor_get(v_s_719_, 7);
v_uppers_728_ = lean_ctor_get(v_s_719_, 8);
v_diseqs_729_ = lean_ctor_get(v_s_719_, 9);
v_elimEqs_730_ = lean_ctor_get(v_s_719_, 10);
v_elimStack_731_ = lean_ctor_get(v_s_719_, 11);
v_occurs_732_ = lean_ctor_get(v_s_719_, 12);
v_assignment_733_ = lean_ctor_get(v_s_719_, 13);
v_nextCnstrId_734_ = lean_ctor_get(v_s_719_, 14);
v_caseSplits_735_ = lean_ctor_get_uint8(v_s_719_, sizeof(void*)*23);
v_conflict_x3f_736_ = lean_ctor_get(v_s_719_, 15);
v_diseqSplits_737_ = lean_ctor_get(v_s_719_, 16);
v_divMod_738_ = lean_ctor_get(v_s_719_, 17);
v_toIntIds_739_ = lean_ctor_get(v_s_719_, 18);
v_toIntInfos_740_ = lean_ctor_get(v_s_719_, 19);
v_toIntTermMap_741_ = lean_ctor_get(v_s_719_, 20);
v_toIntVarMap_742_ = lean_ctor_get(v_s_719_, 21);
v_usedCommRing_743_ = lean_ctor_get_uint8(v_s_719_, sizeof(void*)*23 + 1);
v_nonlinearOccs_744_ = lean_ctor_get(v_s_719_, 22);
v_isSharedCheck_752_ = !lean_is_exclusive(v_s_719_);
if (v_isSharedCheck_752_ == 0)
{
v___x_746_ = v_s_719_;
v_isShared_747_ = v_isSharedCheck_752_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_nonlinearOccs_744_);
lean_inc(v_toIntVarMap_742_);
lean_inc(v_toIntTermMap_741_);
lean_inc(v_toIntInfos_740_);
lean_inc(v_toIntIds_739_);
lean_inc(v_divMod_738_);
lean_inc(v_diseqSplits_737_);
lean_inc(v_conflict_x3f_736_);
lean_inc(v_nextCnstrId_734_);
lean_inc(v_assignment_733_);
lean_inc(v_occurs_732_);
lean_inc(v_elimStack_731_);
lean_inc(v_elimEqs_730_);
lean_inc(v_diseqs_729_);
lean_inc(v_uppers_728_);
lean_inc(v_lowers_727_);
lean_inc(v_dvds_726_);
lean_inc(v_natDef_725_);
lean_inc(v_natToIntMap_724_);
lean_inc(v_varMap_x27_723_);
lean_inc(v_vars_x27_722_);
lean_inc(v_varMap_721_);
lean_inc(v_vars_720_);
lean_dec(v_s_719_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_752_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_748_; lean_object* v___x_750_; 
v___x_748_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(v_p_717_, v_lowers_727_, v_v_718_);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 7, v___x_748_);
v___x_750_ = v___x_746_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_vars_720_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v_varMap_721_);
lean_ctor_set(v_reuseFailAlloc_751_, 2, v_vars_x27_722_);
lean_ctor_set(v_reuseFailAlloc_751_, 3, v_varMap_x27_723_);
lean_ctor_set(v_reuseFailAlloc_751_, 4, v_natToIntMap_724_);
lean_ctor_set(v_reuseFailAlloc_751_, 5, v_natDef_725_);
lean_ctor_set(v_reuseFailAlloc_751_, 6, v_dvds_726_);
lean_ctor_set(v_reuseFailAlloc_751_, 7, v___x_748_);
lean_ctor_set(v_reuseFailAlloc_751_, 8, v_uppers_728_);
lean_ctor_set(v_reuseFailAlloc_751_, 9, v_diseqs_729_);
lean_ctor_set(v_reuseFailAlloc_751_, 10, v_elimEqs_730_);
lean_ctor_set(v_reuseFailAlloc_751_, 11, v_elimStack_731_);
lean_ctor_set(v_reuseFailAlloc_751_, 12, v_occurs_732_);
lean_ctor_set(v_reuseFailAlloc_751_, 13, v_assignment_733_);
lean_ctor_set(v_reuseFailAlloc_751_, 14, v_nextCnstrId_734_);
lean_ctor_set(v_reuseFailAlloc_751_, 15, v_conflict_x3f_736_);
lean_ctor_set(v_reuseFailAlloc_751_, 16, v_diseqSplits_737_);
lean_ctor_set(v_reuseFailAlloc_751_, 17, v_divMod_738_);
lean_ctor_set(v_reuseFailAlloc_751_, 18, v_toIntIds_739_);
lean_ctor_set(v_reuseFailAlloc_751_, 19, v_toIntInfos_740_);
lean_ctor_set(v_reuseFailAlloc_751_, 20, v_toIntTermMap_741_);
lean_ctor_set(v_reuseFailAlloc_751_, 21, v_toIntVarMap_742_);
lean_ctor_set(v_reuseFailAlloc_751_, 22, v_nonlinearOccs_744_);
lean_ctor_set_uint8(v_reuseFailAlloc_751_, sizeof(void*)*23, v_caseSplits_735_);
lean_ctor_set_uint8(v_reuseFailAlloc_751_, sizeof(void*)*23 + 1, v_usedCommRing_743_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1___boxed(lean_object* v_p_753_, lean_object* v_v_754_, lean_object* v_s_755_){
_start:
{
lean_object* v_res_756_; 
v_res_756_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1(v_p_753_, v_v_754_, v_s_755_);
lean_dec(v_v_754_);
lean_dec_ref(v_p_753_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(lean_object* v_c_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_){
_start:
{
lean_object* v_p_764_; 
v_p_764_ = lean_ctor_get(v_c_757_, 0);
if (lean_obj_tag(v_p_764_) == 1)
{
lean_object* v_k_765_; lean_object* v_v_766_; lean_object* v___x_767_; uint8_t v___x_768_; 
lean_inc_ref(v_p_764_);
lean_dec_ref(v_c_757_);
v_k_765_ = lean_ctor_get(v_p_764_, 0);
v_v_766_ = lean_ctor_get(v_p_764_, 1);
lean_inc(v_v_766_);
v___x_767_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9);
v___x_768_ = lean_int_dec_lt(v_k_765_, v___x_767_);
if (v___x_768_ == 0)
{
lean_object* v___f_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v___f_769_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_769_, 0, v_p_764_);
lean_closure_set(v___f_769_, 1, v_v_766_);
v___x_770_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_771_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_770_, v___f_769_, v_a_758_);
return v___x_771_;
}
else
{
lean_object* v___f_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v___f_772_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_772_, 0, v_p_764_);
lean_closure_set(v___f_772_, 1, v_v_766_);
v___x_773_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_774_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_773_, v___f_772_, v_a_758_);
return v___x_774_;
}
}
else
{
lean_object* v___x_775_; 
v___x_775_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_);
return v___x_775_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___boxed(lean_object* v_c_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_){
_start:
{
lean_object* v_res_783_; 
v_res_783_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_c_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_, v_a_781_);
lean_dec(v_a_781_);
lean_dec_ref(v_a_780_);
lean_dec(v_a_779_);
lean_dec_ref(v_a_778_);
lean_dec(v_a_777_);
return v_res_783_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase(lean_object* v_c_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_c_784_, v_a_785_, v_a_791_, v_a_792_, v_a_793_, v_a_794_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___boxed(lean_object* v_c_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase(v_c_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
lean_dec(v_a_799_);
lean_dec(v_a_798_);
return v_res_809_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5(void){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_823_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_824_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_825_ = l_Lean_Name_append(v___x_824_, v___x_823_);
return v___x_825_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7(void){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_827_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__6));
v___x_828_ = l_Lean_stringToMessageData(v___x_827_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3(lean_object* v___x_829_, lean_object* v_c_830_, lean_object* v_as_831_, size_t v_sz_832_, size_t v_i_833_, lean_object* v_b_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
uint8_t v___x_846_; 
v___x_846_ = lean_usize_dec_lt(v_i_833_, v_sz_832_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; 
lean_dec_ref(v_c_830_);
lean_dec_ref(v___x_829_);
v___x_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_847_, 0, v_b_834_);
return v___x_847_;
}
else
{
lean_object* v_snd_848_; lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_934_; 
v_snd_848_ = lean_ctor_get(v_b_834_, 1);
v_isSharedCheck_934_ = !lean_is_exclusive(v_b_834_);
if (v_isSharedCheck_934_ == 0)
{
lean_object* v_unused_935_; 
v_unused_935_ = lean_ctor_get(v_b_834_, 0);
lean_dec(v_unused_935_);
v___x_850_ = v_b_834_;
v_isShared_851_ = v_isSharedCheck_934_;
goto v_resetjp_849_;
}
else
{
lean_inc(v_snd_848_);
lean_dec(v_b_834_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_934_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v_a_852_; lean_object* v_p_853_; lean_object* v___x_854_; uint8_t v___x_855_; 
v_a_852_ = lean_array_uget_borrowed(v_as_831_, v_i_833_);
v_p_853_ = lean_ctor_get(v_a_852_, 0);
v___x_854_ = lean_box(0);
v___x_855_ = l_Int_Linear_Poly_isNegEq(v___x_829_, v_p_853_);
if (v___x_855_ == 0)
{
lean_object* v___x_856_; size_t v___x_857_; size_t v___x_858_; 
lean_del_object(v___x_850_);
lean_dec(v_snd_848_);
v___x_856_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__1));
v___x_857_ = ((size_t)1ULL);
v___x_858_ = lean_usize_add(v_i_833_, v___x_857_);
v_i_833_ = v___x_858_;
v_b_834_ = v___x_856_;
goto _start;
}
else
{
lean_object* v___x_860_; 
lean_inc(v_a_852_);
v___x_860_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_852_, v___y_835_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
if (lean_obj_tag(v___x_860_) == 0)
{
lean_object* v_options_861_; lean_object* v_inheritedTraceOptions_862_; uint8_t v_hasTrace_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___y_872_; lean_object* v___y_873_; lean_object* v___y_874_; lean_object* v___y_875_; lean_object* v___y_876_; 
lean_dec_ref(v___x_860_);
v_options_861_ = lean_ctor_get(v___y_843_, 2);
v_inheritedTraceOptions_862_ = lean_ctor_get(v___y_843_, 13);
v_hasTrace_863_ = lean_ctor_get_uint8(v_options_861_, sizeof(void*)*1);
lean_inc(v_a_852_);
v___x_864_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_864_, 0, v_c_830_);
lean_ctor_set(v___x_864_, 1, v_a_852_);
v___x_865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_865_, 0, v___x_829_);
lean_ctor_set(v___x_865_, 1, v___x_864_);
if (v_hasTrace_863_ == 0)
{
v___y_867_ = v___y_835_;
v___y_868_ = v___y_836_;
v___y_869_ = v___y_837_;
v___y_870_ = v___y_838_;
v___y_871_ = v___y_839_;
v___y_872_ = v___y_840_;
v___y_873_ = v___y_841_;
v___y_874_ = v___y_842_;
v___y_875_ = v___y_843_;
v___y_876_ = v___y_844_;
goto v___jp_866_;
}
else
{
lean_object* v___x_902_; lean_object* v___x_903_; uint8_t v___x_904_; 
v___x_902_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_903_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5);
v___x_904_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_862_, v_options_861_, v___x_903_);
if (v___x_904_ == 0)
{
v___y_867_ = v___y_835_;
v___y_868_ = v___y_836_;
v___y_869_ = v___y_837_;
v___y_870_ = v___y_838_;
v___y_871_ = v___y_839_;
v___y_872_ = v___y_840_;
v___y_873_ = v___y_841_;
v___y_874_ = v___y_842_;
v___y_875_ = v___y_843_;
v___y_876_ = v___y_844_;
goto v___jp_866_;
}
else
{
lean_object* v___x_905_; 
lean_inc_ref(v___x_865_);
v___x_905_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_865_, v___y_835_, v___y_843_);
if (lean_obj_tag(v___x_905_) == 0)
{
lean_object* v_a_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
v_a_906_ = lean_ctor_get(v___x_905_, 0);
lean_inc(v_a_906_);
lean_dec_ref(v___x_905_);
v___x_907_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7);
v___x_908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_907_);
lean_ctor_set(v___x_908_, 1, v_a_906_);
v___x_909_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_902_, v___x_908_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
if (lean_obj_tag(v___x_909_) == 0)
{
lean_dec_ref(v___x_909_);
v___y_867_ = v___y_835_;
v___y_868_ = v___y_836_;
v___y_869_ = v___y_837_;
v___y_870_ = v___y_838_;
v___y_871_ = v___y_839_;
v___y_872_ = v___y_840_;
v___y_873_ = v___y_841_;
v___y_874_ = v___y_842_;
v___y_875_ = v___y_843_;
v___y_876_ = v___y_844_;
goto v___jp_866_;
}
else
{
lean_object* v_a_910_; lean_object* v___x_912_; uint8_t v_isShared_913_; uint8_t v_isSharedCheck_917_; 
lean_dec_ref(v___x_865_);
lean_del_object(v___x_850_);
lean_dec(v_snd_848_);
v_a_910_ = lean_ctor_get(v___x_909_, 0);
v_isSharedCheck_917_ = !lean_is_exclusive(v___x_909_);
if (v_isSharedCheck_917_ == 0)
{
v___x_912_ = v___x_909_;
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
else
{
lean_inc(v_a_910_);
lean_dec(v___x_909_);
v___x_912_ = lean_box(0);
v_isShared_913_ = v_isSharedCheck_917_;
goto v_resetjp_911_;
}
v_resetjp_911_:
{
lean_object* v___x_915_; 
if (v_isShared_913_ == 0)
{
v___x_915_ = v___x_912_;
goto v_reusejp_914_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_a_910_);
v___x_915_ = v_reuseFailAlloc_916_;
goto v_reusejp_914_;
}
v_reusejp_914_:
{
return v___x_915_;
}
}
}
}
else
{
lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_925_; 
lean_dec_ref(v___x_865_);
lean_del_object(v___x_850_);
lean_dec(v_snd_848_);
v_a_918_ = lean_ctor_get(v___x_905_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_925_ == 0)
{
v___x_920_ = v___x_905_;
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_905_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_923_; 
if (v_isShared_921_ == 0)
{
v___x_923_ = v___x_920_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_a_918_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
}
v___jp_866_:
{
lean_object* v___x_877_; 
lean_inc(v___y_876_);
lean_inc_ref(v___y_875_);
lean_inc(v___y_874_);
lean_inc_ref(v___y_873_);
lean_inc(v___y_872_);
lean_inc_ref(v___y_871_);
lean_inc(v___y_870_);
lean_inc_ref(v___y_869_);
lean_inc(v___y_868_);
lean_inc(v___y_867_);
v___x_877_ = lean_grind_cutsat_assert_eq(v___x_865_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_892_; 
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_892_ == 0)
{
lean_object* v_unused_893_; 
v_unused_893_ = lean_ctor_get(v___x_877_, 0);
lean_dec(v_unused_893_);
v___x_879_ = v___x_877_;
v_isShared_880_ = v_isSharedCheck_892_;
goto v_resetjp_878_;
}
else
{
lean_dec(v___x_877_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_892_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_884_; 
v___x_881_ = lean_box(v___x_855_);
v___x_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 1, v___x_854_);
lean_ctor_set(v___x_850_, 0, v___x_882_);
v___x_884_ = v___x_850_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_882_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v___x_854_);
v___x_884_ = v_reuseFailAlloc_891_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_889_; 
v___x_885_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_885_, 0, v___x_884_);
v___x_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_886_, 0, v___x_885_);
v___x_887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_887_, 0, v___x_886_);
lean_ctor_set(v___x_887_, 1, v_snd_848_);
if (v_isShared_880_ == 0)
{
lean_ctor_set(v___x_879_, 0, v___x_887_);
v___x_889_ = v___x_879_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_887_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
else
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_901_; 
lean_del_object(v___x_850_);
lean_dec(v_snd_848_);
v_a_894_ = lean_ctor_get(v___x_877_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_901_ == 0)
{
v___x_896_ = v___x_877_;
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_877_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_899_; 
if (v_isShared_897_ == 0)
{
v___x_899_ = v___x_896_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_894_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
}
else
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
lean_del_object(v___x_850_);
lean_dec(v_snd_848_);
lean_dec_ref(v_c_830_);
lean_dec_ref(v___x_829_);
v_a_926_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v___x_860_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_860_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_926_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___boxed(lean_object** _args){
lean_object* v___x_936_ = _args[0];
lean_object* v_c_937_ = _args[1];
lean_object* v_as_938_ = _args[2];
lean_object* v_sz_939_ = _args[3];
lean_object* v_i_940_ = _args[4];
lean_object* v_b_941_ = _args[5];
lean_object* v___y_942_ = _args[6];
lean_object* v___y_943_ = _args[7];
lean_object* v___y_944_ = _args[8];
lean_object* v___y_945_ = _args[9];
lean_object* v___y_946_ = _args[10];
lean_object* v___y_947_ = _args[11];
lean_object* v___y_948_ = _args[12];
lean_object* v___y_949_ = _args[13];
lean_object* v___y_950_ = _args[14];
lean_object* v___y_951_ = _args[15];
lean_object* v___y_952_ = _args[16];
_start:
{
size_t v_sz_boxed_953_; size_t v_i_boxed_954_; lean_object* v_res_955_; 
v_sz_boxed_953_ = lean_unbox_usize(v_sz_939_);
lean_dec(v_sz_939_);
v_i_boxed_954_ = lean_unbox_usize(v_i_940_);
lean_dec(v_i_940_);
v_res_955_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3(v___x_936_, v_c_937_, v_as_938_, v_sz_boxed_953_, v_i_boxed_954_, v_b_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec(v___y_942_);
lean_dec_ref(v_as_938_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2(lean_object* v___x_962_, lean_object* v_c_963_, lean_object* v_as_964_, size_t v_sz_965_, size_t v_i_966_, lean_object* v_b_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
uint8_t v___x_979_; 
v___x_979_ = lean_usize_dec_lt(v_i_966_, v_sz_965_);
if (v___x_979_ == 0)
{
lean_object* v___x_980_; 
lean_dec_ref(v_c_963_);
lean_dec_ref(v___x_962_);
v___x_980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_980_, 0, v_b_967_);
return v___x_980_;
}
else
{
lean_object* v_snd_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_1067_; 
v_snd_981_ = lean_ctor_get(v_b_967_, 1);
v_isSharedCheck_1067_ = !lean_is_exclusive(v_b_967_);
if (v_isSharedCheck_1067_ == 0)
{
lean_object* v_unused_1068_; 
v_unused_1068_ = lean_ctor_get(v_b_967_, 0);
lean_dec(v_unused_1068_);
v___x_983_ = v_b_967_;
v_isShared_984_ = v_isSharedCheck_1067_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_snd_981_);
lean_dec(v_b_967_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_1067_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v_a_985_; lean_object* v_p_986_; lean_object* v___x_987_; uint8_t v___x_988_; 
v_a_985_ = lean_array_uget_borrowed(v_as_964_, v_i_966_);
v_p_986_ = lean_ctor_get(v_a_985_, 0);
v___x_987_ = lean_box(0);
v___x_988_ = l_Int_Linear_Poly_isNegEq(v___x_962_, v_p_986_);
if (v___x_988_ == 0)
{
lean_object* v___x_989_; size_t v___x_990_; size_t v___x_991_; lean_object* v___x_992_; 
lean_del_object(v___x_983_);
lean_dec(v_snd_981_);
v___x_989_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__1));
v___x_990_ = ((size_t)1ULL);
v___x_991_ = lean_usize_add(v_i_966_, v___x_990_);
v___x_992_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3(v___x_962_, v_c_963_, v_as_964_, v_sz_965_, v___x_991_, v___x_989_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
return v___x_992_;
}
else
{
lean_object* v___x_993_; 
lean_inc(v_a_985_);
v___x_993_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_985_, v___y_968_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
if (lean_obj_tag(v___x_993_) == 0)
{
lean_object* v_options_994_; lean_object* v_inheritedTraceOptions_995_; uint8_t v_hasTrace_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___y_1000_; lean_object* v___y_1001_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v___y_1006_; lean_object* v___y_1007_; lean_object* v___y_1008_; lean_object* v___y_1009_; 
lean_dec_ref(v___x_993_);
v_options_994_ = lean_ctor_get(v___y_976_, 2);
v_inheritedTraceOptions_995_ = lean_ctor_get(v___y_976_, 13);
v_hasTrace_996_ = lean_ctor_get_uint8(v_options_994_, sizeof(void*)*1);
lean_inc(v_a_985_);
v___x_997_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_997_, 0, v_c_963_);
lean_ctor_set(v___x_997_, 1, v_a_985_);
v___x_998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_962_);
lean_ctor_set(v___x_998_, 1, v___x_997_);
if (v_hasTrace_996_ == 0)
{
v___y_1000_ = v___y_968_;
v___y_1001_ = v___y_969_;
v___y_1002_ = v___y_970_;
v___y_1003_ = v___y_971_;
v___y_1004_ = v___y_972_;
v___y_1005_ = v___y_973_;
v___y_1006_ = v___y_974_;
v___y_1007_ = v___y_975_;
v___y_1008_ = v___y_976_;
v___y_1009_ = v___y_977_;
goto v___jp_999_;
}
else
{
lean_object* v___x_1035_; lean_object* v___x_1036_; uint8_t v___x_1037_; 
v___x_1035_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_1036_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5);
v___x_1037_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_995_, v_options_994_, v___x_1036_);
if (v___x_1037_ == 0)
{
v___y_1000_ = v___y_968_;
v___y_1001_ = v___y_969_;
v___y_1002_ = v___y_970_;
v___y_1003_ = v___y_971_;
v___y_1004_ = v___y_972_;
v___y_1005_ = v___y_973_;
v___y_1006_ = v___y_974_;
v___y_1007_ = v___y_975_;
v___y_1008_ = v___y_976_;
v___y_1009_ = v___y_977_;
goto v___jp_999_;
}
else
{
lean_object* v___x_1038_; 
lean_inc_ref(v___x_998_);
v___x_1038_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_998_, v___y_968_, v___y_976_);
if (lean_obj_tag(v___x_1038_) == 0)
{
lean_object* v_a_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v_a_1039_ = lean_ctor_get(v___x_1038_, 0);
lean_inc(v_a_1039_);
lean_dec_ref(v___x_1038_);
v___x_1040_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7);
v___x_1041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1041_, 0, v___x_1040_);
lean_ctor_set(v___x_1041_, 1, v_a_1039_);
v___x_1042_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_1035_, v___x_1041_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
if (lean_obj_tag(v___x_1042_) == 0)
{
lean_dec_ref(v___x_1042_);
v___y_1000_ = v___y_968_;
v___y_1001_ = v___y_969_;
v___y_1002_ = v___y_970_;
v___y_1003_ = v___y_971_;
v___y_1004_ = v___y_972_;
v___y_1005_ = v___y_973_;
v___y_1006_ = v___y_974_;
v___y_1007_ = v___y_975_;
v___y_1008_ = v___y_976_;
v___y_1009_ = v___y_977_;
goto v___jp_999_;
}
else
{
lean_object* v_a_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1050_; 
lean_dec_ref(v___x_998_);
lean_del_object(v___x_983_);
lean_dec(v_snd_981_);
v_a_1043_ = lean_ctor_get(v___x_1042_, 0);
v_isSharedCheck_1050_ = !lean_is_exclusive(v___x_1042_);
if (v_isSharedCheck_1050_ == 0)
{
v___x_1045_ = v___x_1042_;
v_isShared_1046_ = v_isSharedCheck_1050_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_a_1043_);
lean_dec(v___x_1042_);
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
else
{
lean_object* v_a_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1058_; 
lean_dec_ref(v___x_998_);
lean_del_object(v___x_983_);
lean_dec(v_snd_981_);
v_a_1051_ = lean_ctor_get(v___x_1038_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1058_ == 0)
{
v___x_1053_ = v___x_1038_;
v_isShared_1054_ = v_isSharedCheck_1058_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_a_1051_);
lean_dec(v___x_1038_);
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
}
}
v___jp_999_:
{
lean_object* v___x_1010_; 
lean_inc(v___y_1009_);
lean_inc_ref(v___y_1008_);
lean_inc(v___y_1007_);
lean_inc_ref(v___y_1006_);
lean_inc(v___y_1005_);
lean_inc_ref(v___y_1004_);
lean_inc(v___y_1003_);
lean_inc_ref(v___y_1002_);
lean_inc(v___y_1001_);
lean_inc(v___y_1000_);
v___x_1010_ = lean_grind_cutsat_assert_eq(v___x_998_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1025_; 
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1025_ == 0)
{
lean_object* v_unused_1026_; 
v_unused_1026_ = lean_ctor_get(v___x_1010_, 0);
lean_dec(v_unused_1026_);
v___x_1012_ = v___x_1010_;
v_isShared_1013_ = v_isSharedCheck_1025_;
goto v_resetjp_1011_;
}
else
{
lean_dec(v___x_1010_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1025_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1017_; 
v___x_1014_ = lean_box(v___x_988_);
v___x_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
if (v_isShared_984_ == 0)
{
lean_ctor_set(v___x_983_, 1, v___x_987_);
lean_ctor_set(v___x_983_, 0, v___x_1015_);
v___x_1017_ = v___x_983_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1015_);
lean_ctor_set(v_reuseFailAlloc_1024_, 1, v___x_987_);
v___x_1017_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1022_; 
v___x_1018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1018_, 0, v___x_1017_);
v___x_1019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1018_);
v___x_1020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
lean_ctor_set(v___x_1020_, 1, v_snd_981_);
if (v_isShared_1013_ == 0)
{
lean_ctor_set(v___x_1012_, 0, v___x_1020_);
v___x_1022_ = v___x_1012_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v___x_1020_);
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
else
{
lean_object* v_a_1027_; lean_object* v___x_1029_; uint8_t v_isShared_1030_; uint8_t v_isSharedCheck_1034_; 
lean_del_object(v___x_983_);
lean_dec(v_snd_981_);
v_a_1027_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1034_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1034_ == 0)
{
v___x_1029_ = v___x_1010_;
v_isShared_1030_ = v_isSharedCheck_1034_;
goto v_resetjp_1028_;
}
else
{
lean_inc(v_a_1027_);
lean_dec(v___x_1010_);
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
else
{
lean_object* v_a_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1066_; 
lean_del_object(v___x_983_);
lean_dec(v_snd_981_);
lean_dec_ref(v_c_963_);
lean_dec_ref(v___x_962_);
v_a_1059_ = lean_ctor_get(v___x_993_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v___x_993_);
if (v_isSharedCheck_1066_ == 0)
{
v___x_1061_ = v___x_993_;
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_a_1059_);
lean_dec(v___x_993_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1066_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1064_; 
if (v_isShared_1062_ == 0)
{
v___x_1064_ = v___x_1061_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v_a_1059_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___boxed(lean_object** _args){
lean_object* v___x_1069_ = _args[0];
lean_object* v_c_1070_ = _args[1];
lean_object* v_as_1071_ = _args[2];
lean_object* v_sz_1072_ = _args[3];
lean_object* v_i_1073_ = _args[4];
lean_object* v_b_1074_ = _args[5];
lean_object* v___y_1075_ = _args[6];
lean_object* v___y_1076_ = _args[7];
lean_object* v___y_1077_ = _args[8];
lean_object* v___y_1078_ = _args[9];
lean_object* v___y_1079_ = _args[10];
lean_object* v___y_1080_ = _args[11];
lean_object* v___y_1081_ = _args[12];
lean_object* v___y_1082_ = _args[13];
lean_object* v___y_1083_ = _args[14];
lean_object* v___y_1084_ = _args[15];
lean_object* v___y_1085_ = _args[16];
_start:
{
size_t v_sz_boxed_1086_; size_t v_i_boxed_1087_; lean_object* v_res_1088_; 
v_sz_boxed_1086_ = lean_unbox_usize(v_sz_1072_);
lean_dec(v_sz_1072_);
v_i_boxed_1087_ = lean_unbox_usize(v_i_1073_);
lean_dec(v_i_1073_);
v_res_1088_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2(v___x_1069_, v_c_1070_, v_as_1071_, v_sz_boxed_1086_, v_i_boxed_1087_, v_b_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec_ref(v_as_1071_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(lean_object* v_init_1089_, lean_object* v___x_1090_, lean_object* v_c_1091_, lean_object* v_n_1092_, lean_object* v_b_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
if (lean_obj_tag(v_n_1092_) == 0)
{
lean_object* v_cs_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1139_; 
v_cs_1105_ = lean_ctor_get(v_n_1092_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v_n_1092_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1107_ = v_n_1092_;
v_isShared_1108_ = v_isSharedCheck_1139_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_cs_1105_);
lean_dec(v_n_1092_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1139_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; size_t v_sz_1111_; size_t v___x_1112_; lean_object* v___x_1113_; 
v___x_1109_ = lean_box(0);
v___x_1110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1109_);
lean_ctor_set(v___x_1110_, 1, v_b_1093_);
v_sz_1111_ = lean_array_size(v_cs_1105_);
v___x_1112_ = ((size_t)0ULL);
v___x_1113_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(v_init_1089_, v___x_1090_, v_c_1091_, v_cs_1105_, v_sz_1111_, v___x_1112_, v___x_1110_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
lean_dec_ref(v_cs_1105_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1130_; 
v_a_1114_ = lean_ctor_get(v___x_1113_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1116_ = v___x_1113_;
v_isShared_1117_ = v_isSharedCheck_1130_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_1113_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1130_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v_fst_1118_; 
v_fst_1118_ = lean_ctor_get(v_a_1114_, 0);
if (lean_obj_tag(v_fst_1118_) == 0)
{
lean_object* v_snd_1119_; lean_object* v___x_1121_; 
v_snd_1119_ = lean_ctor_get(v_a_1114_, 1);
lean_inc(v_snd_1119_);
lean_dec(v_a_1114_);
if (v_isShared_1108_ == 0)
{
lean_ctor_set_tag(v___x_1107_, 1);
lean_ctor_set(v___x_1107_, 0, v_snd_1119_);
v___x_1121_ = v___x_1107_;
goto v_reusejp_1120_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_snd_1119_);
v___x_1121_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1120_;
}
v_reusejp_1120_:
{
lean_object* v___x_1123_; 
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 0, v___x_1121_);
v___x_1123_ = v___x_1116_;
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
}
else
{
lean_object* v_val_1126_; lean_object* v___x_1128_; 
lean_inc_ref(v_fst_1118_);
lean_dec(v_a_1114_);
lean_del_object(v___x_1107_);
v_val_1126_ = lean_ctor_get(v_fst_1118_, 0);
lean_inc(v_val_1126_);
lean_dec_ref(v_fst_1118_);
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 0, v_val_1126_);
v___x_1128_ = v___x_1116_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_val_1126_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
}
else
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
lean_del_object(v___x_1107_);
v_a_1131_ = lean_ctor_get(v___x_1113_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1133_ = v___x_1113_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1113_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_a_1131_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
}
else
{
lean_object* v_vs_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1174_; 
v_vs_1140_ = lean_ctor_get(v_n_1092_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v_n_1092_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1142_ = v_n_1092_;
v_isShared_1143_ = v_isSharedCheck_1174_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_vs_1140_);
lean_dec(v_n_1092_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1174_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1144_; lean_object* v___x_1145_; size_t v_sz_1146_; size_t v___x_1147_; lean_object* v___x_1148_; 
v___x_1144_ = lean_box(0);
v___x_1145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1145_, 0, v___x_1144_);
lean_ctor_set(v___x_1145_, 1, v_b_1093_);
v_sz_1146_ = lean_array_size(v_vs_1140_);
v___x_1147_ = ((size_t)0ULL);
v___x_1148_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2(v___x_1090_, v_c_1091_, v_vs_1140_, v_sz_1146_, v___x_1147_, v___x_1145_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
lean_dec_ref(v_vs_1140_);
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1165_; 
v_a_1149_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1151_ = v___x_1148_;
v_isShared_1152_ = v_isSharedCheck_1165_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1148_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1165_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v_fst_1153_; 
v_fst_1153_ = lean_ctor_get(v_a_1149_, 0);
if (lean_obj_tag(v_fst_1153_) == 0)
{
lean_object* v_snd_1154_; lean_object* v___x_1156_; 
v_snd_1154_ = lean_ctor_get(v_a_1149_, 1);
lean_inc(v_snd_1154_);
lean_dec(v_a_1149_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 0, v_snd_1154_);
v___x_1156_ = v___x_1142_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_snd_1154_);
v___x_1156_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
lean_object* v___x_1158_; 
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 0, v___x_1156_);
v___x_1158_ = v___x_1151_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v___x_1156_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
else
{
lean_object* v_val_1161_; lean_object* v___x_1163_; 
lean_inc_ref(v_fst_1153_);
lean_dec(v_a_1149_);
lean_del_object(v___x_1142_);
v_val_1161_ = lean_ctor_get(v_fst_1153_, 0);
lean_inc(v_val_1161_);
lean_dec_ref(v_fst_1153_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 0, v_val_1161_);
v___x_1163_ = v___x_1151_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_val_1161_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
else
{
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1173_; 
lean_del_object(v___x_1142_);
v_a_1166_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1168_ = v___x_1148_;
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1148_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(lean_object* v_init_1175_, lean_object* v___x_1176_, lean_object* v_c_1177_, lean_object* v_as_1178_, size_t v_sz_1179_, size_t v_i_1180_, lean_object* v_b_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
uint8_t v___x_1193_; 
v___x_1193_ = lean_usize_dec_lt(v_i_1180_, v_sz_1179_);
if (v___x_1193_ == 0)
{
lean_object* v___x_1194_; 
lean_dec_ref(v_c_1177_);
lean_dec_ref(v___x_1176_);
v___x_1194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1194_, 0, v_b_1181_);
return v___x_1194_;
}
else
{
lean_object* v_snd_1195_; lean_object* v___x_1197_; uint8_t v_isShared_1198_; uint8_t v_isSharedCheck_1229_; 
v_snd_1195_ = lean_ctor_get(v_b_1181_, 1);
v_isSharedCheck_1229_ = !lean_is_exclusive(v_b_1181_);
if (v_isSharedCheck_1229_ == 0)
{
lean_object* v_unused_1230_; 
v_unused_1230_ = lean_ctor_get(v_b_1181_, 0);
lean_dec(v_unused_1230_);
v___x_1197_ = v_b_1181_;
v_isShared_1198_ = v_isSharedCheck_1229_;
goto v_resetjp_1196_;
}
else
{
lean_inc(v_snd_1195_);
lean_dec(v_b_1181_);
v___x_1197_ = lean_box(0);
v_isShared_1198_ = v_isSharedCheck_1229_;
goto v_resetjp_1196_;
}
v_resetjp_1196_:
{
lean_object* v_a_1199_; lean_object* v___x_1200_; 
v_a_1199_ = lean_array_uget_borrowed(v_as_1178_, v_i_1180_);
lean_inc(v_snd_1195_);
lean_inc(v_a_1199_);
lean_inc_ref(v_c_1177_);
lean_inc_ref(v___x_1176_);
v___x_1200_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(v_init_1175_, v___x_1176_, v_c_1177_, v_a_1199_, v_snd_1195_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
if (lean_obj_tag(v___x_1200_) == 0)
{
lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1220_; 
v_a_1201_ = lean_ctor_get(v___x_1200_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1203_ = v___x_1200_;
v_isShared_1204_ = v_isSharedCheck_1220_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v___x_1200_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1220_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
if (lean_obj_tag(v_a_1201_) == 0)
{
lean_object* v___x_1205_; lean_object* v___x_1207_; 
lean_dec_ref(v_c_1177_);
lean_dec_ref(v___x_1176_);
v___x_1205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1205_, 0, v_a_1201_);
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 0, v___x_1205_);
v___x_1207_ = v___x_1197_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1211_; 
v_reuseFailAlloc_1211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1211_, 0, v___x_1205_);
lean_ctor_set(v_reuseFailAlloc_1211_, 1, v_snd_1195_);
v___x_1207_ = v_reuseFailAlloc_1211_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
lean_object* v___x_1209_; 
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 0, v___x_1207_);
v___x_1209_ = v___x_1203_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v___x_1207_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
else
{
lean_object* v_a_1212_; lean_object* v___x_1213_; lean_object* v___x_1215_; 
lean_del_object(v___x_1203_);
lean_dec(v_snd_1195_);
v_a_1212_ = lean_ctor_get(v_a_1201_, 0);
lean_inc(v_a_1212_);
lean_dec_ref(v_a_1201_);
v___x_1213_ = lean_box(0);
if (v_isShared_1198_ == 0)
{
lean_ctor_set(v___x_1197_, 1, v_a_1212_);
lean_ctor_set(v___x_1197_, 0, v___x_1213_);
v___x_1215_ = v___x_1197_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1213_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v_a_1212_);
v___x_1215_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
size_t v___x_1216_; size_t v___x_1217_; 
v___x_1216_ = ((size_t)1ULL);
v___x_1217_ = lean_usize_add(v_i_1180_, v___x_1216_);
v_i_1180_ = v___x_1217_;
v_b_1181_ = v___x_1215_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1228_; 
lean_del_object(v___x_1197_);
lean_dec(v_snd_1195_);
lean_dec_ref(v_c_1177_);
lean_dec_ref(v___x_1176_);
v_a_1221_ = lean_ctor_get(v___x_1200_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1228_ == 0)
{
v___x_1223_ = v___x_1200_;
v_isShared_1224_ = v_isSharedCheck_1228_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_a_1221_);
lean_dec(v___x_1200_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_init_1231_ = _args[0];
lean_object* v___x_1232_ = _args[1];
lean_object* v_c_1233_ = _args[2];
lean_object* v_as_1234_ = _args[3];
lean_object* v_sz_1235_ = _args[4];
lean_object* v_i_1236_ = _args[5];
lean_object* v_b_1237_ = _args[6];
lean_object* v___y_1238_ = _args[7];
lean_object* v___y_1239_ = _args[8];
lean_object* v___y_1240_ = _args[9];
lean_object* v___y_1241_ = _args[10];
lean_object* v___y_1242_ = _args[11];
lean_object* v___y_1243_ = _args[12];
lean_object* v___y_1244_ = _args[13];
lean_object* v___y_1245_ = _args[14];
lean_object* v___y_1246_ = _args[15];
lean_object* v___y_1247_ = _args[16];
lean_object* v___y_1248_ = _args[17];
_start:
{
size_t v_sz_boxed_1249_; size_t v_i_boxed_1250_; lean_object* v_res_1251_; 
v_sz_boxed_1249_ = lean_unbox_usize(v_sz_1235_);
lean_dec(v_sz_1235_);
v_i_boxed_1250_ = lean_unbox_usize(v_i_1236_);
lean_dec(v_i_1236_);
v_res_1251_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(v_init_1231_, v___x_1232_, v_c_1233_, v_as_1234_, v_sz_boxed_1249_, v_i_boxed_1250_, v_b_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec(v___y_1239_);
lean_dec(v___y_1238_);
lean_dec_ref(v_as_1234_);
lean_dec_ref(v_init_1231_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___boxed(lean_object* v_init_1252_, lean_object* v___x_1253_, lean_object* v_c_1254_, lean_object* v_n_1255_, lean_object* v_b_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_){
_start:
{
lean_object* v_res_1268_; 
v_res_1268_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(v_init_1252_, v___x_1253_, v_c_1254_, v_n_1255_, v_b_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec(v___y_1257_);
lean_dec_ref(v_init_1252_);
return v_res_1268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4(lean_object* v___x_1275_, lean_object* v_c_1276_, lean_object* v_as_1277_, size_t v_sz_1278_, size_t v_i_1279_, lean_object* v_b_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_, lean_object* v___y_1288_, lean_object* v___y_1289_, lean_object* v___y_1290_){
_start:
{
uint8_t v___x_1292_; 
v___x_1292_ = lean_usize_dec_lt(v_i_1279_, v_sz_1278_);
if (v___x_1292_ == 0)
{
lean_object* v___x_1293_; 
lean_dec_ref(v_c_1276_);
lean_dec_ref(v___x_1275_);
v___x_1293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1293_, 0, v_b_1280_);
return v___x_1293_;
}
else
{
lean_object* v_snd_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1379_; 
v_snd_1294_ = lean_ctor_get(v_b_1280_, 1);
v_isSharedCheck_1379_ = !lean_is_exclusive(v_b_1280_);
if (v_isSharedCheck_1379_ == 0)
{
lean_object* v_unused_1380_; 
v_unused_1380_ = lean_ctor_get(v_b_1280_, 0);
lean_dec(v_unused_1380_);
v___x_1296_ = v_b_1280_;
v_isShared_1297_ = v_isSharedCheck_1379_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_snd_1294_);
lean_dec(v_b_1280_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1379_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v_a_1298_; lean_object* v_p_1299_; lean_object* v___x_1300_; uint8_t v___x_1301_; 
v_a_1298_ = lean_array_uget_borrowed(v_as_1277_, v_i_1279_);
v_p_1299_ = lean_ctor_get(v_a_1298_, 0);
v___x_1300_ = lean_box(0);
v___x_1301_ = l_Int_Linear_Poly_isNegEq(v___x_1275_, v_p_1299_);
if (v___x_1301_ == 0)
{
lean_object* v___x_1302_; size_t v___x_1303_; size_t v___x_1304_; 
lean_del_object(v___x_1296_);
lean_dec(v_snd_1294_);
v___x_1302_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___closed__1));
v___x_1303_ = ((size_t)1ULL);
v___x_1304_ = lean_usize_add(v_i_1279_, v___x_1303_);
v_i_1279_ = v___x_1304_;
v_b_1280_ = v___x_1302_;
goto _start;
}
else
{
lean_object* v___x_1306_; 
lean_inc(v_a_1298_);
v___x_1306_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_1298_, v___y_1281_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_object* v_options_1307_; lean_object* v_inheritedTraceOptions_1308_; uint8_t v_hasTrace_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___y_1313_; lean_object* v___y_1314_; lean_object* v___y_1315_; lean_object* v___y_1316_; lean_object* v___y_1317_; lean_object* v___y_1318_; lean_object* v___y_1319_; lean_object* v___y_1320_; lean_object* v___y_1321_; lean_object* v___y_1322_; 
lean_dec_ref(v___x_1306_);
v_options_1307_ = lean_ctor_get(v___y_1289_, 2);
v_inheritedTraceOptions_1308_ = lean_ctor_get(v___y_1289_, 13);
v_hasTrace_1309_ = lean_ctor_get_uint8(v_options_1307_, sizeof(void*)*1);
lean_inc(v_a_1298_);
v___x_1310_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1310_, 0, v_c_1276_);
lean_ctor_set(v___x_1310_, 1, v_a_1298_);
v___x_1311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1275_);
lean_ctor_set(v___x_1311_, 1, v___x_1310_);
if (v_hasTrace_1309_ == 0)
{
v___y_1313_ = v___y_1281_;
v___y_1314_ = v___y_1282_;
v___y_1315_ = v___y_1283_;
v___y_1316_ = v___y_1284_;
v___y_1317_ = v___y_1285_;
v___y_1318_ = v___y_1286_;
v___y_1319_ = v___y_1287_;
v___y_1320_ = v___y_1288_;
v___y_1321_ = v___y_1289_;
v___y_1322_ = v___y_1290_;
goto v___jp_1312_;
}
else
{
lean_object* v___x_1347_; lean_object* v___x_1348_; uint8_t v___x_1349_; 
v___x_1347_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_1348_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5);
v___x_1349_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1308_, v_options_1307_, v___x_1348_);
if (v___x_1349_ == 0)
{
v___y_1313_ = v___y_1281_;
v___y_1314_ = v___y_1282_;
v___y_1315_ = v___y_1283_;
v___y_1316_ = v___y_1284_;
v___y_1317_ = v___y_1285_;
v___y_1318_ = v___y_1286_;
v___y_1319_ = v___y_1287_;
v___y_1320_ = v___y_1288_;
v___y_1321_ = v___y_1289_;
v___y_1322_ = v___y_1290_;
goto v___jp_1312_;
}
else
{
lean_object* v___x_1350_; 
lean_inc_ref(v___x_1311_);
v___x_1350_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_1311_, v___y_1281_, v___y_1289_);
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v_a_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
lean_inc(v_a_1351_);
lean_dec_ref(v___x_1350_);
v___x_1352_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7);
v___x_1353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1352_);
lean_ctor_set(v___x_1353_, 1, v_a_1351_);
v___x_1354_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_1347_, v___x_1353_, v___y_1287_, v___y_1288_, v___y_1289_, v___y_1290_);
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_dec_ref(v___x_1354_);
v___y_1313_ = v___y_1281_;
v___y_1314_ = v___y_1282_;
v___y_1315_ = v___y_1283_;
v___y_1316_ = v___y_1284_;
v___y_1317_ = v___y_1285_;
v___y_1318_ = v___y_1286_;
v___y_1319_ = v___y_1287_;
v___y_1320_ = v___y_1288_;
v___y_1321_ = v___y_1289_;
v___y_1322_ = v___y_1290_;
goto v___jp_1312_;
}
else
{
lean_object* v_a_1355_; lean_object* v___x_1357_; uint8_t v_isShared_1358_; uint8_t v_isSharedCheck_1362_; 
lean_dec_ref(v___x_1311_);
lean_del_object(v___x_1296_);
lean_dec(v_snd_1294_);
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1362_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1362_ == 0)
{
v___x_1357_ = v___x_1354_;
v_isShared_1358_ = v_isSharedCheck_1362_;
goto v_resetjp_1356_;
}
else
{
lean_inc(v_a_1355_);
lean_dec(v___x_1354_);
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
else
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1370_; 
lean_dec_ref(v___x_1311_);
lean_del_object(v___x_1296_);
lean_dec(v_snd_1294_);
v_a_1363_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1365_ = v___x_1350_;
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1350_);
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
v___jp_1312_:
{
lean_object* v___x_1323_; 
lean_inc(v___y_1322_);
lean_inc_ref(v___y_1321_);
lean_inc(v___y_1320_);
lean_inc_ref(v___y_1319_);
lean_inc(v___y_1318_);
lean_inc_ref(v___y_1317_);
lean_inc(v___y_1316_);
lean_inc_ref(v___y_1315_);
lean_inc(v___y_1314_);
lean_inc(v___y_1313_);
v___x_1323_ = lean_grind_cutsat_assert_eq(v___x_1311_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1337_; 
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1337_ == 0)
{
lean_object* v_unused_1338_; 
v_unused_1338_ = lean_ctor_get(v___x_1323_, 0);
lean_dec(v_unused_1338_);
v___x_1325_ = v___x_1323_;
v_isShared_1326_ = v_isSharedCheck_1337_;
goto v_resetjp_1324_;
}
else
{
lean_dec(v___x_1323_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1337_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1330_; 
v___x_1327_ = lean_box(v___x_1301_);
v___x_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1327_);
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 1, v___x_1300_);
lean_ctor_set(v___x_1296_, 0, v___x_1328_);
v___x_1330_ = v___x_1296_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1328_);
lean_ctor_set(v_reuseFailAlloc_1336_, 1, v___x_1300_);
v___x_1330_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1334_; 
v___x_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1330_);
v___x_1332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1331_);
lean_ctor_set(v___x_1332_, 1, v_snd_1294_);
if (v_isShared_1326_ == 0)
{
lean_ctor_set(v___x_1325_, 0, v___x_1332_);
v___x_1334_ = v___x_1325_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v___x_1332_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
}
else
{
lean_object* v_a_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1346_; 
lean_del_object(v___x_1296_);
lean_dec(v_snd_1294_);
v_a_1339_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1346_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1346_ == 0)
{
v___x_1341_ = v___x_1323_;
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_a_1339_);
lean_dec(v___x_1323_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1346_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1344_; 
if (v_isShared_1342_ == 0)
{
v___x_1344_ = v___x_1341_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1345_; 
v_reuseFailAlloc_1345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1345_, 0, v_a_1339_);
v___x_1344_ = v_reuseFailAlloc_1345_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
return v___x_1344_;
}
}
}
}
}
else
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
lean_del_object(v___x_1296_);
lean_dec(v_snd_1294_);
lean_dec_ref(v_c_1276_);
lean_dec_ref(v___x_1275_);
v_a_1371_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1373_ = v___x_1306_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1306_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v___x_1381_ = _args[0];
lean_object* v_c_1382_ = _args[1];
lean_object* v_as_1383_ = _args[2];
lean_object* v_sz_1384_ = _args[3];
lean_object* v_i_1385_ = _args[4];
lean_object* v_b_1386_ = _args[5];
lean_object* v___y_1387_ = _args[6];
lean_object* v___y_1388_ = _args[7];
lean_object* v___y_1389_ = _args[8];
lean_object* v___y_1390_ = _args[9];
lean_object* v___y_1391_ = _args[10];
lean_object* v___y_1392_ = _args[11];
lean_object* v___y_1393_ = _args[12];
lean_object* v___y_1394_ = _args[13];
lean_object* v___y_1395_ = _args[14];
lean_object* v___y_1396_ = _args[15];
lean_object* v___y_1397_ = _args[16];
_start:
{
size_t v_sz_boxed_1398_; size_t v_i_boxed_1399_; lean_object* v_res_1400_; 
v_sz_boxed_1398_ = lean_unbox_usize(v_sz_1384_);
lean_dec(v_sz_1384_);
v_i_boxed_1399_ = lean_unbox_usize(v_i_1385_);
lean_dec(v_i_1385_);
v_res_1400_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4(v___x_1381_, v_c_1382_, v_as_1383_, v_sz_boxed_1398_, v_i_boxed_1399_, v_b_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
lean_dec(v___y_1392_);
lean_dec_ref(v___y_1391_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec(v___y_1388_);
lean_dec(v___y_1387_);
lean_dec_ref(v_as_1383_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1(lean_object* v___x_1404_, lean_object* v_c_1405_, lean_object* v_as_1406_, size_t v_sz_1407_, size_t v_i_1408_, lean_object* v_b_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
uint8_t v___x_1421_; 
v___x_1421_ = lean_usize_dec_lt(v_i_1408_, v_sz_1407_);
if (v___x_1421_ == 0)
{
lean_object* v___x_1422_; 
lean_dec_ref(v_c_1405_);
lean_dec_ref(v___x_1404_);
v___x_1422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1422_, 0, v_b_1409_);
return v___x_1422_;
}
else
{
lean_object* v_snd_1423_; lean_object* v___x_1425_; uint8_t v_isShared_1426_; uint8_t v_isSharedCheck_1508_; 
v_snd_1423_ = lean_ctor_get(v_b_1409_, 1);
v_isSharedCheck_1508_ = !lean_is_exclusive(v_b_1409_);
if (v_isSharedCheck_1508_ == 0)
{
lean_object* v_unused_1509_; 
v_unused_1509_ = lean_ctor_get(v_b_1409_, 0);
lean_dec(v_unused_1509_);
v___x_1425_ = v_b_1409_;
v_isShared_1426_ = v_isSharedCheck_1508_;
goto v_resetjp_1424_;
}
else
{
lean_inc(v_snd_1423_);
lean_dec(v_b_1409_);
v___x_1425_ = lean_box(0);
v_isShared_1426_ = v_isSharedCheck_1508_;
goto v_resetjp_1424_;
}
v_resetjp_1424_:
{
lean_object* v_a_1427_; lean_object* v_p_1428_; lean_object* v___x_1429_; uint8_t v___x_1430_; 
v_a_1427_ = lean_array_uget_borrowed(v_as_1406_, v_i_1408_);
v_p_1428_ = lean_ctor_get(v_a_1427_, 0);
v___x_1429_ = lean_box(0);
v___x_1430_ = l_Int_Linear_Poly_isNegEq(v___x_1404_, v_p_1428_);
if (v___x_1430_ == 0)
{
lean_object* v___x_1431_; size_t v___x_1432_; size_t v___x_1433_; lean_object* v___x_1434_; 
lean_del_object(v___x_1425_);
lean_dec(v_snd_1423_);
v___x_1431_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1___closed__0));
v___x_1432_ = ((size_t)1ULL);
v___x_1433_ = lean_usize_add(v_i_1408_, v___x_1432_);
v___x_1434_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4(v___x_1404_, v_c_1405_, v_as_1406_, v_sz_1407_, v___x_1433_, v___x_1431_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
return v___x_1434_;
}
else
{
lean_object* v___x_1435_; 
lean_inc(v_a_1427_);
v___x_1435_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_1427_, v___y_1410_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
if (lean_obj_tag(v___x_1435_) == 0)
{
lean_object* v_options_1436_; lean_object* v_inheritedTraceOptions_1437_; uint8_t v_hasTrace_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1448_; lean_object* v___y_1449_; lean_object* v___y_1450_; lean_object* v___y_1451_; 
lean_dec_ref(v___x_1435_);
v_options_1436_ = lean_ctor_get(v___y_1418_, 2);
v_inheritedTraceOptions_1437_ = lean_ctor_get(v___y_1418_, 13);
v_hasTrace_1438_ = lean_ctor_get_uint8(v_options_1436_, sizeof(void*)*1);
lean_inc(v_a_1427_);
v___x_1439_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1439_, 0, v_c_1405_);
lean_ctor_set(v___x_1439_, 1, v_a_1427_);
v___x_1440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1404_);
lean_ctor_set(v___x_1440_, 1, v___x_1439_);
if (v_hasTrace_1438_ == 0)
{
v___y_1442_ = v___y_1410_;
v___y_1443_ = v___y_1411_;
v___y_1444_ = v___y_1412_;
v___y_1445_ = v___y_1413_;
v___y_1446_ = v___y_1414_;
v___y_1447_ = v___y_1415_;
v___y_1448_ = v___y_1416_;
v___y_1449_ = v___y_1417_;
v___y_1450_ = v___y_1418_;
v___y_1451_ = v___y_1419_;
goto v___jp_1441_;
}
else
{
lean_object* v___x_1476_; lean_object* v___x_1477_; uint8_t v___x_1478_; 
v___x_1476_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_1477_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5);
v___x_1478_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1437_, v_options_1436_, v___x_1477_);
if (v___x_1478_ == 0)
{
v___y_1442_ = v___y_1410_;
v___y_1443_ = v___y_1411_;
v___y_1444_ = v___y_1412_;
v___y_1445_ = v___y_1413_;
v___y_1446_ = v___y_1414_;
v___y_1447_ = v___y_1415_;
v___y_1448_ = v___y_1416_;
v___y_1449_ = v___y_1417_;
v___y_1450_ = v___y_1418_;
v___y_1451_ = v___y_1419_;
goto v___jp_1441_;
}
else
{
lean_object* v___x_1479_; 
lean_inc_ref(v___x_1440_);
v___x_1479_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_1440_, v___y_1410_, v___y_1418_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v_a_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; 
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
lean_inc(v_a_1480_);
lean_dec_ref(v___x_1479_);
v___x_1481_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7);
v___x_1482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1482_, 0, v___x_1481_);
lean_ctor_set(v___x_1482_, 1, v_a_1480_);
v___x_1483_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_1476_, v___x_1482_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_dec_ref(v___x_1483_);
v___y_1442_ = v___y_1410_;
v___y_1443_ = v___y_1411_;
v___y_1444_ = v___y_1412_;
v___y_1445_ = v___y_1413_;
v___y_1446_ = v___y_1414_;
v___y_1447_ = v___y_1415_;
v___y_1448_ = v___y_1416_;
v___y_1449_ = v___y_1417_;
v___y_1450_ = v___y_1418_;
v___y_1451_ = v___y_1419_;
goto v___jp_1441_;
}
else
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1491_; 
lean_dec_ref(v___x_1440_);
lean_del_object(v___x_1425_);
lean_dec(v_snd_1423_);
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1486_ = v___x_1483_;
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v___x_1483_);
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
else
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1499_; 
lean_dec_ref(v___x_1440_);
lean_del_object(v___x_1425_);
lean_dec(v_snd_1423_);
v_a_1492_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1494_ = v___x_1479_;
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1479_);
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
v___jp_1441_:
{
lean_object* v___x_1452_; 
lean_inc(v___y_1451_);
lean_inc_ref(v___y_1450_);
lean_inc(v___y_1449_);
lean_inc_ref(v___y_1448_);
lean_inc(v___y_1447_);
lean_inc_ref(v___y_1446_);
lean_inc(v___y_1445_);
lean_inc_ref(v___y_1444_);
lean_inc(v___y_1443_);
lean_inc(v___y_1442_);
v___x_1452_ = lean_grind_cutsat_assert_eq(v___x_1440_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_, v___y_1451_);
if (lean_obj_tag(v___x_1452_) == 0)
{
lean_object* v___x_1454_; uint8_t v_isShared_1455_; uint8_t v_isSharedCheck_1466_; 
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1466_ == 0)
{
lean_object* v_unused_1467_; 
v_unused_1467_ = lean_ctor_get(v___x_1452_, 0);
lean_dec(v_unused_1467_);
v___x_1454_ = v___x_1452_;
v_isShared_1455_ = v_isSharedCheck_1466_;
goto v_resetjp_1453_;
}
else
{
lean_dec(v___x_1452_);
v___x_1454_ = lean_box(0);
v_isShared_1455_ = v_isSharedCheck_1466_;
goto v_resetjp_1453_;
}
v_resetjp_1453_:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1459_; 
v___x_1456_ = lean_box(v___x_1430_);
v___x_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1456_);
if (v_isShared_1426_ == 0)
{
lean_ctor_set(v___x_1425_, 1, v___x_1429_);
lean_ctor_set(v___x_1425_, 0, v___x_1457_);
v___x_1459_ = v___x_1425_;
goto v_reusejp_1458_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v___x_1457_);
lean_ctor_set(v_reuseFailAlloc_1465_, 1, v___x_1429_);
v___x_1459_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1458_;
}
v_reusejp_1458_:
{
lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1463_; 
v___x_1460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1459_);
v___x_1461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1461_, 0, v___x_1460_);
lean_ctor_set(v___x_1461_, 1, v_snd_1423_);
if (v_isShared_1455_ == 0)
{
lean_ctor_set(v___x_1454_, 0, v___x_1461_);
v___x_1463_ = v___x_1454_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v___x_1461_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
}
else
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1475_; 
lean_del_object(v___x_1425_);
lean_dec(v_snd_1423_);
v_a_1468_ = lean_ctor_get(v___x_1452_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1452_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1470_ = v___x_1452_;
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1452_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1473_; 
if (v_isShared_1471_ == 0)
{
v___x_1473_ = v___x_1470_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_a_1468_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
}
}
else
{
lean_object* v_a_1500_; lean_object* v___x_1502_; uint8_t v_isShared_1503_; uint8_t v_isSharedCheck_1507_; 
lean_del_object(v___x_1425_);
lean_dec(v_snd_1423_);
lean_dec_ref(v_c_1405_);
lean_dec_ref(v___x_1404_);
v_a_1500_ = lean_ctor_get(v___x_1435_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v___x_1435_);
if (v_isSharedCheck_1507_ == 0)
{
v___x_1502_ = v___x_1435_;
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
else
{
lean_inc(v_a_1500_);
lean_dec(v___x_1435_);
v___x_1502_ = lean_box(0);
v_isShared_1503_ = v_isSharedCheck_1507_;
goto v_resetjp_1501_;
}
v_resetjp_1501_:
{
lean_object* v___x_1505_; 
if (v_isShared_1503_ == 0)
{
v___x_1505_ = v___x_1502_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1506_; 
v_reuseFailAlloc_1506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1506_, 0, v_a_1500_);
v___x_1505_ = v_reuseFailAlloc_1506_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
return v___x_1505_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v___x_1510_ = _args[0];
lean_object* v_c_1511_ = _args[1];
lean_object* v_as_1512_ = _args[2];
lean_object* v_sz_1513_ = _args[3];
lean_object* v_i_1514_ = _args[4];
lean_object* v_b_1515_ = _args[5];
lean_object* v___y_1516_ = _args[6];
lean_object* v___y_1517_ = _args[7];
lean_object* v___y_1518_ = _args[8];
lean_object* v___y_1519_ = _args[9];
lean_object* v___y_1520_ = _args[10];
lean_object* v___y_1521_ = _args[11];
lean_object* v___y_1522_ = _args[12];
lean_object* v___y_1523_ = _args[13];
lean_object* v___y_1524_ = _args[14];
lean_object* v___y_1525_ = _args[15];
lean_object* v___y_1526_ = _args[16];
_start:
{
size_t v_sz_boxed_1527_; size_t v_i_boxed_1528_; lean_object* v_res_1529_; 
v_sz_boxed_1527_ = lean_unbox_usize(v_sz_1513_);
lean_dec(v_sz_1513_);
v_i_boxed_1528_ = lean_unbox_usize(v_i_1514_);
lean_dec(v_i_1514_);
v_res_1529_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1(v___x_1510_, v_c_1511_, v_as_1512_, v_sz_boxed_1527_, v_i_boxed_1528_, v_b_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
lean_dec(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec_ref(v_as_1512_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0(lean_object* v___x_1530_, lean_object* v_c_1531_, lean_object* v_t_1532_, lean_object* v_init_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v_root_1545_; lean_object* v_tail_1546_; lean_object* v___x_1547_; 
v_root_1545_ = lean_ctor_get(v_t_1532_, 0);
lean_inc_ref(v_root_1545_);
v_tail_1546_ = lean_ctor_get(v_t_1532_, 1);
lean_inc_ref(v_tail_1546_);
lean_dec_ref(v_t_1532_);
lean_inc_ref(v_c_1531_);
lean_inc_ref(v___x_1530_);
lean_inc_ref(v_init_1533_);
v___x_1547_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(v_init_1533_, v___x_1530_, v_c_1531_, v_root_1545_, v_init_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
lean_dec_ref(v_init_1533_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1584_; 
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1550_ = v___x_1547_;
v_isShared_1551_ = v_isSharedCheck_1584_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___x_1547_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1584_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
if (lean_obj_tag(v_a_1548_) == 0)
{
lean_object* v_a_1552_; lean_object* v___x_1554_; 
lean_dec_ref(v_tail_1546_);
lean_dec_ref(v_c_1531_);
lean_dec_ref(v___x_1530_);
v_a_1552_ = lean_ctor_get(v_a_1548_, 0);
lean_inc(v_a_1552_);
lean_dec_ref(v_a_1548_);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 0, v_a_1552_);
v___x_1554_ = v___x_1550_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_a_1552_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
else
{
lean_object* v_a_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; size_t v_sz_1559_; size_t v___x_1560_; lean_object* v___x_1561_; 
lean_del_object(v___x_1550_);
v_a_1556_ = lean_ctor_get(v_a_1548_, 0);
lean_inc(v_a_1556_);
lean_dec_ref(v_a_1548_);
v___x_1557_ = lean_box(0);
v___x_1558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1558_, 0, v___x_1557_);
lean_ctor_set(v___x_1558_, 1, v_a_1556_);
v_sz_1559_ = lean_array_size(v_tail_1546_);
v___x_1560_ = ((size_t)0ULL);
v___x_1561_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1(v___x_1530_, v_c_1531_, v_tail_1546_, v_sz_1559_, v___x_1560_, v___x_1558_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
lean_dec_ref(v_tail_1546_);
if (lean_obj_tag(v___x_1561_) == 0)
{
lean_object* v_a_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1575_; 
v_a_1562_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1564_ = v___x_1561_;
v_isShared_1565_ = v_isSharedCheck_1575_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_a_1562_);
lean_dec(v___x_1561_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1575_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v_fst_1566_; 
v_fst_1566_ = lean_ctor_get(v_a_1562_, 0);
if (lean_obj_tag(v_fst_1566_) == 0)
{
lean_object* v_snd_1567_; lean_object* v___x_1569_; 
v_snd_1567_ = lean_ctor_get(v_a_1562_, 1);
lean_inc(v_snd_1567_);
lean_dec(v_a_1562_);
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 0, v_snd_1567_);
v___x_1569_ = v___x_1564_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_snd_1567_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
else
{
lean_object* v_val_1571_; lean_object* v___x_1573_; 
lean_inc_ref(v_fst_1566_);
lean_dec(v_a_1562_);
v_val_1571_ = lean_ctor_get(v_fst_1566_, 0);
lean_inc(v_val_1571_);
lean_dec_ref(v_fst_1566_);
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 0, v_val_1571_);
v___x_1573_ = v___x_1564_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_val_1571_);
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
else
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1583_; 
v_a_1576_ = lean_ctor_get(v___x_1561_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1561_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1578_ = v___x_1561_;
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1561_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1579_ == 0)
{
v___x_1581_ = v___x_1578_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_a_1576_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
}
}
else
{
lean_object* v_a_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1592_; 
lean_dec_ref(v_tail_1546_);
lean_dec_ref(v_c_1531_);
lean_dec_ref(v___x_1530_);
v_a_1585_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1587_ = v___x_1547_;
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_a_1585_);
lean_dec(v___x_1547_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1592_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
lean_object* v___x_1590_; 
if (v_isShared_1588_ == 0)
{
v___x_1590_ = v___x_1587_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_a_1585_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0___boxed(lean_object* v___x_1593_, lean_object* v_c_1594_, lean_object* v_t_1595_, lean_object* v_init_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
lean_object* v_res_1608_; 
v_res_1608_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0(v___x_1593_, v_c_1594_, v_t_1595_, v_init_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec(v___y_1598_);
lean_dec(v___y_1597_);
return v_res_1608_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0(void){
_start:
{
lean_object* v___x_1609_; 
v___x_1609_ = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return v___x_1609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq(lean_object* v_c_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_){
_start:
{
lean_object* v_p_1622_; 
v_p_1622_ = lean_ctor_get(v_c_1610_, 0);
if (lean_obj_tag(v_p_1622_) == 1)
{
lean_object* v_k_1623_; lean_object* v_v_1624_; lean_object* v___x_1625_; 
lean_inc_ref(v_p_1622_);
v_k_1623_ = lean_ctor_get(v_p_1622_, 0);
v_v_1624_ = lean_ctor_get(v_p_1622_, 1);
v___x_1625_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1611_, v_a_1619_);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v_a_1626_; lean_object* v___y_1628_; lean_object* v___x_1654_; uint8_t v___x_1655_; 
v_a_1626_ = lean_ctor_get(v___x_1625_, 0);
lean_inc(v_a_1626_);
lean_dec_ref(v___x_1625_);
v___x_1654_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9);
v___x_1655_ = lean_int_dec_lt(v_k_1623_, v___x_1654_);
if (v___x_1655_ == 0)
{
lean_object* v_lowers_1656_; lean_object* v_size_1657_; lean_object* v___x_1658_; uint8_t v___x_1659_; 
v_lowers_1656_ = lean_ctor_get(v_a_1626_, 7);
lean_inc_ref(v_lowers_1656_);
lean_dec(v_a_1626_);
v_size_1657_ = lean_ctor_get(v_lowers_1656_, 2);
v___x_1658_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0);
v___x_1659_ = lean_nat_dec_lt(v_v_1624_, v_size_1657_);
if (v___x_1659_ == 0)
{
lean_object* v___x_1660_; 
lean_dec_ref(v_lowers_1656_);
v___x_1660_ = l_outOfBounds___redArg(v___x_1658_);
v___y_1628_ = v___x_1660_;
goto v___jp_1627_;
}
else
{
lean_object* v___x_1661_; 
v___x_1661_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1658_, v_lowers_1656_, v_v_1624_);
lean_dec_ref(v_lowers_1656_);
v___y_1628_ = v___x_1661_;
goto v___jp_1627_;
}
}
else
{
lean_object* v_uppers_1662_; lean_object* v_size_1663_; lean_object* v___x_1664_; uint8_t v___x_1665_; 
v_uppers_1662_ = lean_ctor_get(v_a_1626_, 8);
lean_inc_ref(v_uppers_1662_);
lean_dec(v_a_1626_);
v_size_1663_ = lean_ctor_get(v_uppers_1662_, 2);
v___x_1664_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0);
v___x_1665_ = lean_nat_dec_lt(v_v_1624_, v_size_1663_);
if (v___x_1665_ == 0)
{
lean_object* v___x_1666_; 
lean_dec_ref(v_uppers_1662_);
v___x_1666_ = l_outOfBounds___redArg(v___x_1664_);
v___y_1628_ = v___x_1666_;
goto v___jp_1627_;
}
else
{
lean_object* v___x_1667_; 
v___x_1667_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1664_, v_uppers_1662_, v_v_1624_);
lean_dec_ref(v_uppers_1662_);
v___y_1628_ = v___x_1667_;
goto v___jp_1627_;
}
}
v___jp_1627_:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; 
v___x_1629_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__0));
v___x_1630_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0(v_p_1622_, v_c_1610_, v___y_1628_, v___x_1629_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_);
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1645_; 
v_a_1631_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1633_ = v___x_1630_;
v_isShared_1634_ = v_isSharedCheck_1645_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1630_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1645_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v_fst_1635_; 
v_fst_1635_ = lean_ctor_get(v_a_1631_, 0);
lean_inc(v_fst_1635_);
lean_dec(v_a_1631_);
if (lean_obj_tag(v_fst_1635_) == 0)
{
uint8_t v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1639_; 
v___x_1636_ = 0;
v___x_1637_ = lean_box(v___x_1636_);
if (v_isShared_1634_ == 0)
{
lean_ctor_set(v___x_1633_, 0, v___x_1637_);
v___x_1639_ = v___x_1633_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v___x_1637_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
else
{
lean_object* v_val_1641_; lean_object* v___x_1643_; 
v_val_1641_ = lean_ctor_get(v_fst_1635_, 0);
lean_inc(v_val_1641_);
lean_dec_ref(v_fst_1635_);
if (v_isShared_1634_ == 0)
{
lean_ctor_set(v___x_1633_, 0, v_val_1641_);
v___x_1643_ = v___x_1633_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_val_1641_);
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
else
{
lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1653_; 
v_a_1646_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1648_ = v___x_1630_;
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v___x_1630_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1653_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1651_; 
if (v_isShared_1649_ == 0)
{
v___x_1651_ = v___x_1648_;
goto v_reusejp_1650_;
}
else
{
lean_object* v_reuseFailAlloc_1652_; 
v_reuseFailAlloc_1652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1652_, 0, v_a_1646_);
v___x_1651_ = v_reuseFailAlloc_1652_;
goto v_reusejp_1650_;
}
v_reusejp_1650_:
{
return v___x_1651_;
}
}
}
}
}
else
{
lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1675_; 
lean_dec_ref(v_p_1622_);
lean_dec_ref(v_c_1610_);
v_a_1668_ = lean_ctor_get(v___x_1625_, 0);
v_isSharedCheck_1675_ = !lean_is_exclusive(v___x_1625_);
if (v_isSharedCheck_1675_ == 0)
{
v___x_1670_ = v___x_1625_;
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_dec(v___x_1625_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1675_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1673_; 
if (v_isShared_1671_ == 0)
{
v___x_1673_ = v___x_1670_;
goto v_reusejp_1672_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_a_1668_);
v___x_1673_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1672_;
}
v_reusejp_1672_:
{
return v___x_1673_;
}
}
}
}
else
{
lean_object* v___x_1676_; 
v___x_1676_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_1610_, v_a_1611_, v_a_1617_, v_a_1618_, v_a_1619_, v_a_1620_);
return v___x_1676_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___boxed(lean_object* v_c_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_, lean_object* v_a_1686_, lean_object* v_a_1687_, lean_object* v_a_1688_){
_start:
{
lean_object* v_res_1689_; 
v_res_1689_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq(v_c_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_, v_a_1685_, v_a_1686_, v_a_1687_);
lean_dec(v_a_1687_);
lean_dec_ref(v_a_1686_);
lean_dec(v_a_1685_);
lean_dec_ref(v_a_1684_);
lean_dec(v_a_1683_);
lean_dec_ref(v_a_1682_);
lean_dec(v_a_1681_);
lean_dec_ref(v_a_1680_);
lean_dec(v_a_1679_);
lean_dec(v_a_1678_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(lean_object* v___x_1690_, lean_object* v_as_1691_, size_t v_i_1692_, size_t v_stop_1693_, lean_object* v_b_1694_){
_start:
{
lean_object* v___y_1696_; uint8_t v___x_1700_; 
v___x_1700_ = lean_usize_dec_eq(v_i_1692_, v_stop_1693_);
if (v___x_1700_ == 0)
{
lean_object* v___x_1701_; lean_object* v_p_1702_; uint8_t v___x_1703_; 
v___x_1701_ = lean_array_uget_borrowed(v_as_1691_, v_i_1692_);
v_p_1702_ = lean_ctor_get(v___x_1701_, 0);
v___x_1703_ = l_Int_Linear_instBEqPoly_beq(v_p_1702_, v___x_1690_);
if (v___x_1703_ == 0)
{
lean_object* v___x_1704_; 
lean_inc(v___x_1701_);
v___x_1704_ = l_Lean_PersistentArray_push___redArg(v_b_1694_, v___x_1701_);
v___y_1696_ = v___x_1704_;
goto v___jp_1695_;
}
else
{
v___y_1696_ = v_b_1694_;
goto v___jp_1695_;
}
}
else
{
return v_b_1694_;
}
v___jp_1695_:
{
size_t v___x_1697_; size_t v___x_1698_; 
v___x_1697_ = ((size_t)1ULL);
v___x_1698_ = lean_usize_add(v_i_1692_, v___x_1697_);
v_i_1692_ = v___x_1698_;
v_b_1694_ = v___y_1696_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1___boxed(lean_object* v___x_1705_, lean_object* v_as_1706_, lean_object* v_i_1707_, lean_object* v_stop_1708_, lean_object* v_b_1709_){
_start:
{
size_t v_i_boxed_1710_; size_t v_stop_boxed_1711_; lean_object* v_res_1712_; 
v_i_boxed_1710_ = lean_unbox_usize(v_i_1707_);
lean_dec(v_i_1707_);
v_stop_boxed_1711_ = lean_unbox_usize(v_stop_1708_);
lean_dec(v_stop_1708_);
v_res_1712_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1705_, v_as_1706_, v_i_boxed_1710_, v_stop_boxed_1711_, v_b_1709_);
lean_dec_ref(v_as_1706_);
lean_dec_ref(v___x_1705_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(lean_object* v___x_1713_, lean_object* v_x_1714_, lean_object* v_x_1715_){
_start:
{
if (lean_obj_tag(v_x_1714_) == 0)
{
lean_object* v_cs_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; uint8_t v___x_1719_; 
v_cs_1716_ = lean_ctor_get(v_x_1714_, 0);
v___x_1717_ = lean_unsigned_to_nat(0u);
v___x_1718_ = lean_array_get_size(v_cs_1716_);
v___x_1719_ = lean_nat_dec_lt(v___x_1717_, v___x_1718_);
if (v___x_1719_ == 0)
{
return v_x_1715_;
}
else
{
uint8_t v___x_1720_; 
v___x_1720_ = lean_nat_dec_le(v___x_1718_, v___x_1718_);
if (v___x_1720_ == 0)
{
if (v___x_1719_ == 0)
{
return v_x_1715_;
}
else
{
size_t v___x_1721_; size_t v___x_1722_; lean_object* v___x_1723_; 
v___x_1721_ = ((size_t)0ULL);
v___x_1722_ = lean_usize_of_nat(v___x_1718_);
v___x_1723_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1713_, v_cs_1716_, v___x_1721_, v___x_1722_, v_x_1715_);
return v___x_1723_;
}
}
else
{
size_t v___x_1724_; size_t v___x_1725_; lean_object* v___x_1726_; 
v___x_1724_ = ((size_t)0ULL);
v___x_1725_ = lean_usize_of_nat(v___x_1718_);
v___x_1726_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1713_, v_cs_1716_, v___x_1724_, v___x_1725_, v_x_1715_);
return v___x_1726_;
}
}
}
else
{
lean_object* v_vs_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; uint8_t v___x_1730_; 
v_vs_1727_ = lean_ctor_get(v_x_1714_, 0);
v___x_1728_ = lean_unsigned_to_nat(0u);
v___x_1729_ = lean_array_get_size(v_vs_1727_);
v___x_1730_ = lean_nat_dec_lt(v___x_1728_, v___x_1729_);
if (v___x_1730_ == 0)
{
return v_x_1715_;
}
else
{
uint8_t v___x_1731_; 
v___x_1731_ = lean_nat_dec_le(v___x_1729_, v___x_1729_);
if (v___x_1731_ == 0)
{
if (v___x_1730_ == 0)
{
return v_x_1715_;
}
else
{
size_t v___x_1732_; size_t v___x_1733_; lean_object* v___x_1734_; 
v___x_1732_ = ((size_t)0ULL);
v___x_1733_ = lean_usize_of_nat(v___x_1729_);
v___x_1734_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1713_, v_vs_1727_, v___x_1732_, v___x_1733_, v_x_1715_);
return v___x_1734_;
}
}
else
{
size_t v___x_1735_; size_t v___x_1736_; lean_object* v___x_1737_; 
v___x_1735_ = ((size_t)0ULL);
v___x_1736_ = lean_usize_of_nat(v___x_1729_);
v___x_1737_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1713_, v_vs_1727_, v___x_1735_, v___x_1736_, v_x_1715_);
return v___x_1737_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(lean_object* v___x_1738_, lean_object* v_as_1739_, size_t v_i_1740_, size_t v_stop_1741_, lean_object* v_b_1742_){
_start:
{
uint8_t v___x_1743_; 
v___x_1743_ = lean_usize_dec_eq(v_i_1740_, v_stop_1741_);
if (v___x_1743_ == 0)
{
lean_object* v___x_1744_; lean_object* v___x_1745_; size_t v___x_1746_; size_t v___x_1747_; 
v___x_1744_ = lean_array_uget_borrowed(v_as_1739_, v_i_1740_);
v___x_1745_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(v___x_1738_, v___x_1744_, v_b_1742_);
v___x_1746_ = ((size_t)1ULL);
v___x_1747_ = lean_usize_add(v_i_1740_, v___x_1746_);
v_i_1740_ = v___x_1747_;
v_b_1742_ = v___x_1745_;
goto _start;
}
else
{
return v_b_1742_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v___x_1749_, lean_object* v_as_1750_, lean_object* v_i_1751_, lean_object* v_stop_1752_, lean_object* v_b_1753_){
_start:
{
size_t v_i_boxed_1754_; size_t v_stop_boxed_1755_; lean_object* v_res_1756_; 
v_i_boxed_1754_ = lean_unbox_usize(v_i_1751_);
lean_dec(v_i_1751_);
v_stop_boxed_1755_ = lean_unbox_usize(v_stop_1752_);
lean_dec(v_stop_1752_);
v_res_1756_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1749_, v_as_1750_, v_i_boxed_1754_, v_stop_boxed_1755_, v_b_1753_);
lean_dec_ref(v_as_1750_);
lean_dec_ref(v___x_1749_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2___boxed(lean_object* v___x_1757_, lean_object* v_x_1758_, lean_object* v_x_1759_){
_start:
{
lean_object* v_res_1760_; 
v_res_1760_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(v___x_1757_, v_x_1758_, v_x_1759_);
lean_dec_ref(v_x_1758_);
lean_dec_ref(v___x_1757_);
return v_res_1760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(lean_object* v___x_1761_, lean_object* v_x_1762_, size_t v_x_1763_, size_t v_x_1764_, lean_object* v_x_1765_){
_start:
{
if (lean_obj_tag(v_x_1762_) == 0)
{
lean_object* v_cs_1766_; lean_object* v___x_1767_; size_t v___x_1768_; lean_object* v_j_1769_; lean_object* v___x_1770_; size_t v___x_1771_; size_t v___x_1772_; size_t v___x_1773_; size_t v___x_1774_; size_t v___x_1775_; size_t v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; uint8_t v___x_1781_; 
v_cs_1766_ = lean_ctor_get(v_x_1762_, 0);
v___x_1767_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0);
v___x_1768_ = lean_usize_shift_right(v_x_1763_, v_x_1764_);
v_j_1769_ = lean_usize_to_nat(v___x_1768_);
v___x_1770_ = lean_array_get_borrowed(v___x_1767_, v_cs_1766_, v_j_1769_);
v___x_1771_ = ((size_t)1ULL);
v___x_1772_ = lean_usize_shift_left(v___x_1771_, v_x_1764_);
v___x_1773_ = lean_usize_sub(v___x_1772_, v___x_1771_);
v___x_1774_ = lean_usize_land(v_x_1763_, v___x_1773_);
v___x_1775_ = ((size_t)5ULL);
v___x_1776_ = lean_usize_sub(v_x_1764_, v___x_1775_);
v___x_1777_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(v___x_1761_, v___x_1770_, v___x_1774_, v___x_1776_, v_x_1765_);
v___x_1778_ = lean_unsigned_to_nat(1u);
v___x_1779_ = lean_nat_add(v_j_1769_, v___x_1778_);
lean_dec(v_j_1769_);
v___x_1780_ = lean_array_get_size(v_cs_1766_);
v___x_1781_ = lean_nat_dec_lt(v___x_1779_, v___x_1780_);
if (v___x_1781_ == 0)
{
lean_dec(v___x_1779_);
return v___x_1777_;
}
else
{
uint8_t v___x_1782_; 
v___x_1782_ = lean_nat_dec_le(v___x_1780_, v___x_1780_);
if (v___x_1782_ == 0)
{
if (v___x_1781_ == 0)
{
lean_dec(v___x_1779_);
return v___x_1777_;
}
else
{
size_t v___x_1783_; size_t v___x_1784_; lean_object* v___x_1785_; 
v___x_1783_ = lean_usize_of_nat(v___x_1779_);
lean_dec(v___x_1779_);
v___x_1784_ = lean_usize_of_nat(v___x_1780_);
v___x_1785_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1761_, v_cs_1766_, v___x_1783_, v___x_1784_, v___x_1777_);
return v___x_1785_;
}
}
else
{
size_t v___x_1786_; size_t v___x_1787_; lean_object* v___x_1788_; 
v___x_1786_ = lean_usize_of_nat(v___x_1779_);
lean_dec(v___x_1779_);
v___x_1787_ = lean_usize_of_nat(v___x_1780_);
v___x_1788_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1761_, v_cs_1766_, v___x_1786_, v___x_1787_, v___x_1777_);
return v___x_1788_;
}
}
}
else
{
lean_object* v_vs_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; uint8_t v___x_1792_; 
v_vs_1789_ = lean_ctor_get(v_x_1762_, 0);
v___x_1790_ = lean_usize_to_nat(v_x_1763_);
v___x_1791_ = lean_array_get_size(v_vs_1789_);
v___x_1792_ = lean_nat_dec_lt(v___x_1790_, v___x_1791_);
if (v___x_1792_ == 0)
{
lean_dec(v___x_1790_);
return v_x_1765_;
}
else
{
uint8_t v___x_1793_; 
v___x_1793_ = lean_nat_dec_le(v___x_1791_, v___x_1791_);
if (v___x_1793_ == 0)
{
if (v___x_1792_ == 0)
{
lean_dec(v___x_1790_);
return v_x_1765_;
}
else
{
size_t v___x_1794_; size_t v___x_1795_; lean_object* v___x_1796_; 
v___x_1794_ = lean_usize_of_nat(v___x_1790_);
lean_dec(v___x_1790_);
v___x_1795_ = lean_usize_of_nat(v___x_1791_);
v___x_1796_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1761_, v_vs_1789_, v___x_1794_, v___x_1795_, v_x_1765_);
return v___x_1796_;
}
}
else
{
size_t v___x_1797_; size_t v___x_1798_; lean_object* v___x_1799_; 
v___x_1797_ = lean_usize_of_nat(v___x_1790_);
lean_dec(v___x_1790_);
v___x_1798_ = lean_usize_of_nat(v___x_1791_);
v___x_1799_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1761_, v_vs_1789_, v___x_1797_, v___x_1798_, v_x_1765_);
return v___x_1799_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0___boxed(lean_object* v___x_1800_, lean_object* v_x_1801_, lean_object* v_x_1802_, lean_object* v_x_1803_, lean_object* v_x_1804_){
_start:
{
size_t v_x_21627__boxed_1805_; size_t v_x_21628__boxed_1806_; lean_object* v_res_1807_; 
v_x_21627__boxed_1805_ = lean_unbox_usize(v_x_1802_);
lean_dec(v_x_1802_);
v_x_21628__boxed_1806_ = lean_unbox_usize(v_x_1803_);
lean_dec(v_x_1803_);
v_res_1807_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(v___x_1800_, v_x_1801_, v_x_21627__boxed_1805_, v_x_21628__boxed_1806_, v_x_1804_);
lean_dec_ref(v_x_1801_);
lean_dec_ref(v___x_1800_);
return v_res_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(lean_object* v___x_1808_, lean_object* v_t_1809_, lean_object* v_init_1810_, lean_object* v_start_1811_){
_start:
{
lean_object* v___x_1812_; uint8_t v___x_1813_; 
v___x_1812_ = lean_unsigned_to_nat(0u);
v___x_1813_ = lean_nat_dec_eq(v_start_1811_, v___x_1812_);
if (v___x_1813_ == 0)
{
lean_object* v_root_1814_; lean_object* v_tail_1815_; size_t v_shift_1816_; lean_object* v_tailOff_1817_; uint8_t v___x_1818_; 
v_root_1814_ = lean_ctor_get(v_t_1809_, 0);
v_tail_1815_ = lean_ctor_get(v_t_1809_, 1);
v_shift_1816_ = lean_ctor_get_usize(v_t_1809_, 4);
v_tailOff_1817_ = lean_ctor_get(v_t_1809_, 3);
v___x_1818_ = lean_nat_dec_le(v_tailOff_1817_, v_start_1811_);
if (v___x_1818_ == 0)
{
size_t v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; uint8_t v___x_1822_; 
v___x_1819_ = lean_usize_of_nat(v_start_1811_);
v___x_1820_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(v___x_1808_, v_root_1814_, v___x_1819_, v_shift_1816_, v_init_1810_);
v___x_1821_ = lean_array_get_size(v_tail_1815_);
v___x_1822_ = lean_nat_dec_lt(v___x_1812_, v___x_1821_);
if (v___x_1822_ == 0)
{
return v___x_1820_;
}
else
{
uint8_t v___x_1823_; 
v___x_1823_ = lean_nat_dec_le(v___x_1821_, v___x_1821_);
if (v___x_1823_ == 0)
{
if (v___x_1822_ == 0)
{
return v___x_1820_;
}
else
{
size_t v___x_1824_; size_t v___x_1825_; lean_object* v___x_1826_; 
v___x_1824_ = ((size_t)0ULL);
v___x_1825_ = lean_usize_of_nat(v___x_1821_);
v___x_1826_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1808_, v_tail_1815_, v___x_1824_, v___x_1825_, v___x_1820_);
return v___x_1826_;
}
}
else
{
size_t v___x_1827_; size_t v___x_1828_; lean_object* v___x_1829_; 
v___x_1827_ = ((size_t)0ULL);
v___x_1828_ = lean_usize_of_nat(v___x_1821_);
v___x_1829_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1808_, v_tail_1815_, v___x_1827_, v___x_1828_, v___x_1820_);
return v___x_1829_;
}
}
}
else
{
lean_object* v___x_1830_; lean_object* v___x_1831_; uint8_t v___x_1832_; 
v___x_1830_ = lean_nat_sub(v_start_1811_, v_tailOff_1817_);
v___x_1831_ = lean_array_get_size(v_tail_1815_);
v___x_1832_ = lean_nat_dec_lt(v___x_1830_, v___x_1831_);
if (v___x_1832_ == 0)
{
lean_dec(v___x_1830_);
return v_init_1810_;
}
else
{
uint8_t v___x_1833_; 
v___x_1833_ = lean_nat_dec_le(v___x_1831_, v___x_1831_);
if (v___x_1833_ == 0)
{
if (v___x_1832_ == 0)
{
lean_dec(v___x_1830_);
return v_init_1810_;
}
else
{
size_t v___x_1834_; size_t v___x_1835_; lean_object* v___x_1836_; 
v___x_1834_ = lean_usize_of_nat(v___x_1830_);
lean_dec(v___x_1830_);
v___x_1835_ = lean_usize_of_nat(v___x_1831_);
v___x_1836_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1808_, v_tail_1815_, v___x_1834_, v___x_1835_, v_init_1810_);
return v___x_1836_;
}
}
else
{
size_t v___x_1837_; size_t v___x_1838_; lean_object* v___x_1839_; 
v___x_1837_ = lean_usize_of_nat(v___x_1830_);
lean_dec(v___x_1830_);
v___x_1838_ = lean_usize_of_nat(v___x_1831_);
v___x_1839_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1808_, v_tail_1815_, v___x_1837_, v___x_1838_, v_init_1810_);
return v___x_1839_;
}
}
}
}
else
{
lean_object* v_root_1840_; lean_object* v_tail_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; uint8_t v___x_1844_; 
v_root_1840_ = lean_ctor_get(v_t_1809_, 0);
v_tail_1841_ = lean_ctor_get(v_t_1809_, 1);
v___x_1842_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(v___x_1808_, v_root_1840_, v_init_1810_);
v___x_1843_ = lean_array_get_size(v_tail_1841_);
v___x_1844_ = lean_nat_dec_lt(v___x_1812_, v___x_1843_);
if (v___x_1844_ == 0)
{
return v___x_1842_;
}
else
{
uint8_t v___x_1845_; 
v___x_1845_ = lean_nat_dec_le(v___x_1843_, v___x_1843_);
if (v___x_1845_ == 0)
{
if (v___x_1844_ == 0)
{
return v___x_1842_;
}
else
{
size_t v___x_1846_; size_t v___x_1847_; lean_object* v___x_1848_; 
v___x_1846_ = ((size_t)0ULL);
v___x_1847_ = lean_usize_of_nat(v___x_1843_);
v___x_1848_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1808_, v_tail_1841_, v___x_1846_, v___x_1847_, v___x_1842_);
return v___x_1848_;
}
}
else
{
size_t v___x_1849_; size_t v___x_1850_; lean_object* v___x_1851_; 
v___x_1849_ = ((size_t)0ULL);
v___x_1850_ = lean_usize_of_nat(v___x_1843_);
v___x_1851_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1808_, v_tail_1841_, v___x_1849_, v___x_1850_, v___x_1842_);
return v___x_1851_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0___boxed(lean_object* v___x_1852_, lean_object* v_t_1853_, lean_object* v_init_1854_, lean_object* v_start_1855_){
_start:
{
lean_object* v_res_1856_; 
v_res_1856_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(v___x_1852_, v_t_1853_, v_init_1854_, v_start_1855_);
lean_dec(v_start_1855_);
lean_dec_ref(v_t_1853_);
lean_dec_ref(v___x_1852_);
return v_res_1856_;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1857_ = lean_unsigned_to_nat(32u);
v___x_1858_ = lean_mk_empty_array_with_capacity(v___x_1857_);
v___x_1859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1858_);
return v___x_1859_;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1(void){
_start:
{
size_t v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1860_ = ((size_t)5ULL);
v___x_1861_ = lean_unsigned_to_nat(0u);
v___x_1862_ = lean_unsigned_to_nat(32u);
v___x_1863_ = lean_mk_empty_array_with_capacity(v___x_1862_);
v___x_1864_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0);
v___x_1865_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1865_, 0, v___x_1864_);
lean_ctor_set(v___x_1865_, 1, v___x_1863_);
lean_ctor_set(v___x_1865_, 2, v___x_1861_);
lean_ctor_set(v___x_1865_, 3, v___x_1861_);
lean_ctor_set_usize(v___x_1865_, 4, v___x_1860_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(lean_object* v___x_1866_, lean_object* v_x_1867_, size_t v_x_1868_, size_t v_x_1869_){
_start:
{
if (lean_obj_tag(v_x_1867_) == 0)
{
lean_object* v_cs_1870_; size_t v_j_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; uint8_t v___x_1874_; 
v_cs_1870_ = lean_ctor_get(v_x_1867_, 0);
v_j_1871_ = lean_usize_shift_right(v_x_1868_, v_x_1869_);
v___x_1872_ = lean_usize_to_nat(v_j_1871_);
v___x_1873_ = lean_array_get_size(v_cs_1870_);
v___x_1874_ = lean_nat_dec_lt(v___x_1872_, v___x_1873_);
if (v___x_1874_ == 0)
{
lean_dec(v___x_1872_);
return v_x_1867_;
}
else
{
lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1892_; 
lean_inc_ref(v_cs_1870_);
v_isSharedCheck_1892_ = !lean_is_exclusive(v_x_1867_);
if (v_isSharedCheck_1892_ == 0)
{
lean_object* v_unused_1893_; 
v_unused_1893_ = lean_ctor_get(v_x_1867_, 0);
lean_dec(v_unused_1893_);
v___x_1876_ = v_x_1867_;
v_isShared_1877_ = v_isSharedCheck_1892_;
goto v_resetjp_1875_;
}
else
{
lean_dec(v_x_1867_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1892_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
size_t v___x_1878_; size_t v___x_1879_; size_t v___x_1880_; size_t v_i_1881_; size_t v___x_1882_; size_t v_shift_1883_; lean_object* v_v_1884_; lean_object* v___x_1885_; lean_object* v_xs_x27_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1890_; 
v___x_1878_ = ((size_t)1ULL);
v___x_1879_ = lean_usize_shift_left(v___x_1878_, v_x_1869_);
v___x_1880_ = lean_usize_sub(v___x_1879_, v___x_1878_);
v_i_1881_ = lean_usize_land(v_x_1868_, v___x_1880_);
v___x_1882_ = ((size_t)5ULL);
v_shift_1883_ = lean_usize_sub(v_x_1869_, v___x_1882_);
v_v_1884_ = lean_array_fget(v_cs_1870_, v___x_1872_);
v___x_1885_ = lean_box(0);
v_xs_x27_1886_ = lean_array_fset(v_cs_1870_, v___x_1872_, v___x_1885_);
v___x_1887_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(v___x_1866_, v_v_1884_, v_i_1881_, v_shift_1883_);
v___x_1888_ = lean_array_fset(v_xs_x27_1886_, v___x_1872_, v___x_1887_);
lean_dec(v___x_1872_);
if (v_isShared_1877_ == 0)
{
lean_ctor_set(v___x_1876_, 0, v___x_1888_);
v___x_1890_ = v___x_1876_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___x_1888_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
}
else
{
lean_object* v_vs_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; uint8_t v___x_1897_; 
v_vs_1894_ = lean_ctor_get(v_x_1867_, 0);
v___x_1895_ = lean_usize_to_nat(v_x_1868_);
v___x_1896_ = lean_array_get_size(v_vs_1894_);
v___x_1897_ = lean_nat_dec_lt(v___x_1895_, v___x_1896_);
if (v___x_1897_ == 0)
{
lean_dec(v___x_1895_);
return v_x_1867_;
}
else
{
lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1911_; 
lean_inc_ref(v_vs_1894_);
v_isSharedCheck_1911_ = !lean_is_exclusive(v_x_1867_);
if (v_isSharedCheck_1911_ == 0)
{
lean_object* v_unused_1912_; 
v_unused_1912_ = lean_ctor_get(v_x_1867_, 0);
lean_dec(v_unused_1912_);
v___x_1899_ = v_x_1867_;
v_isShared_1900_ = v_isSharedCheck_1911_;
goto v_resetjp_1898_;
}
else
{
lean_dec(v_x_1867_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1911_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v_v_1901_; lean_object* v___x_1902_; lean_object* v_xs_x27_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1909_; 
v_v_1901_ = lean_array_fget(v_vs_1894_, v___x_1895_);
v___x_1902_ = lean_box(0);
v_xs_x27_1903_ = lean_array_fset(v_vs_1894_, v___x_1895_, v___x_1902_);
v___x_1904_ = lean_unsigned_to_nat(0u);
v___x_1905_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1);
v___x_1906_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(v___x_1866_, v_v_1901_, v___x_1905_, v___x_1904_);
lean_dec(v_v_1901_);
v___x_1907_ = lean_array_fset(v_xs_x27_1903_, v___x_1895_, v___x_1906_);
lean_dec(v___x_1895_);
if (v_isShared_1900_ == 0)
{
lean_ctor_set(v___x_1899_, 0, v___x_1907_);
v___x_1909_ = v___x_1899_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___x_1907_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___boxed(lean_object* v___x_1913_, lean_object* v_x_1914_, lean_object* v_x_1915_, lean_object* v_x_1916_){
_start:
{
size_t v_x_21799__boxed_1917_; size_t v_x_21800__boxed_1918_; lean_object* v_res_1919_; 
v_x_21799__boxed_1917_ = lean_unbox_usize(v_x_1915_);
lean_dec(v_x_1915_);
v_x_21800__boxed_1918_ = lean_unbox_usize(v_x_1916_);
lean_dec(v_x_1916_);
v_res_1919_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(v___x_1913_, v_x_1914_, v_x_21799__boxed_1917_, v_x_21800__boxed_1918_);
lean_dec_ref(v___x_1913_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1(lean_object* v___x_1920_, lean_object* v_t_1921_, lean_object* v_i_1922_){
_start:
{
lean_object* v_root_1923_; lean_object* v_tail_1924_; lean_object* v_size_1925_; size_t v_shift_1926_; lean_object* v_tailOff_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1955_; 
v_root_1923_ = lean_ctor_get(v_t_1921_, 0);
v_tail_1924_ = lean_ctor_get(v_t_1921_, 1);
v_size_1925_ = lean_ctor_get(v_t_1921_, 2);
v_shift_1926_ = lean_ctor_get_usize(v_t_1921_, 4);
v_tailOff_1927_ = lean_ctor_get(v_t_1921_, 3);
v_isSharedCheck_1955_ = !lean_is_exclusive(v_t_1921_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1929_ = v_t_1921_;
v_isShared_1930_ = v_isSharedCheck_1955_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_tailOff_1927_);
lean_inc(v_size_1925_);
lean_inc(v_tail_1924_);
lean_inc(v_root_1923_);
lean_dec(v_t_1921_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1955_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
uint8_t v___x_1931_; 
v___x_1931_ = lean_nat_dec_le(v_tailOff_1927_, v_i_1922_);
if (v___x_1931_ == 0)
{
size_t v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1935_; 
v___x_1932_ = lean_usize_of_nat(v_i_1922_);
v___x_1933_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(v___x_1920_, v_root_1923_, v___x_1932_, v_shift_1926_);
if (v_isShared_1930_ == 0)
{
lean_ctor_set(v___x_1929_, 0, v___x_1933_);
v___x_1935_ = v___x_1929_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v___x_1933_);
lean_ctor_set(v_reuseFailAlloc_1936_, 1, v_tail_1924_);
lean_ctor_set(v_reuseFailAlloc_1936_, 2, v_size_1925_);
lean_ctor_set(v_reuseFailAlloc_1936_, 3, v_tailOff_1927_);
lean_ctor_set_usize(v_reuseFailAlloc_1936_, 4, v_shift_1926_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
else
{
lean_object* v___x_1937_; lean_object* v___x_1938_; uint8_t v___x_1939_; 
v___x_1937_ = lean_nat_sub(v_i_1922_, v_tailOff_1927_);
v___x_1938_ = lean_array_get_size(v_tail_1924_);
v___x_1939_ = lean_nat_dec_lt(v___x_1937_, v___x_1938_);
if (v___x_1939_ == 0)
{
lean_object* v___x_1941_; 
lean_dec(v___x_1937_);
if (v_isShared_1930_ == 0)
{
v___x_1941_ = v___x_1929_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_root_1923_);
lean_ctor_set(v_reuseFailAlloc_1942_, 1, v_tail_1924_);
lean_ctor_set(v_reuseFailAlloc_1942_, 2, v_size_1925_);
lean_ctor_set(v_reuseFailAlloc_1942_, 3, v_tailOff_1927_);
lean_ctor_set_usize(v_reuseFailAlloc_1942_, 4, v_shift_1926_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
else
{
lean_object* v_v_1943_; lean_object* v___x_1944_; lean_object* v_xs_x27_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1953_; 
v_v_1943_ = lean_array_fget(v_tail_1924_, v___x_1937_);
v___x_1944_ = lean_box(0);
v_xs_x27_1945_ = lean_array_fset(v_tail_1924_, v___x_1937_, v___x_1944_);
v___x_1946_ = lean_unsigned_to_nat(32u);
v___x_1947_ = lean_mk_empty_array_with_capacity(v___x_1946_);
lean_dec_ref(v___x_1947_);
v___x_1948_ = lean_unsigned_to_nat(0u);
v___x_1949_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1);
v___x_1950_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(v___x_1920_, v_v_1943_, v___x_1949_, v___x_1948_);
lean_dec(v_v_1943_);
v___x_1951_ = lean_array_fset(v_xs_x27_1945_, v___x_1937_, v___x_1950_);
lean_dec(v___x_1937_);
if (v_isShared_1930_ == 0)
{
lean_ctor_set(v___x_1929_, 1, v___x_1951_);
v___x_1953_ = v___x_1929_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_root_1923_);
lean_ctor_set(v_reuseFailAlloc_1954_, 1, v___x_1951_);
lean_ctor_set(v_reuseFailAlloc_1954_, 2, v_size_1925_);
lean_ctor_set(v_reuseFailAlloc_1954_, 3, v_tailOff_1927_);
lean_ctor_set_usize(v_reuseFailAlloc_1954_, 4, v_shift_1926_);
v___x_1953_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
return v___x_1953_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1___boxed(lean_object* v___x_1956_, lean_object* v_t_1957_, lean_object* v_i_1958_){
_start:
{
lean_object* v_res_1959_; 
v_res_1959_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1(v___x_1956_, v_t_1957_, v_i_1958_);
lean_dec(v_i_1958_);
lean_dec_ref(v___x_1956_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0(lean_object* v_p_1960_, lean_object* v_x_1961_, lean_object* v_s_1962_){
_start:
{
lean_object* v_vars_1963_; lean_object* v_varMap_1964_; lean_object* v_vars_x27_1965_; lean_object* v_varMap_x27_1966_; lean_object* v_natToIntMap_1967_; lean_object* v_natDef_1968_; lean_object* v_dvds_1969_; lean_object* v_lowers_1970_; lean_object* v_uppers_1971_; lean_object* v_diseqs_1972_; lean_object* v_elimEqs_1973_; lean_object* v_elimStack_1974_; lean_object* v_occurs_1975_; lean_object* v_assignment_1976_; lean_object* v_nextCnstrId_1977_; uint8_t v_caseSplits_1978_; lean_object* v_conflict_x3f_1979_; lean_object* v_diseqSplits_1980_; lean_object* v_divMod_1981_; lean_object* v_toIntIds_1982_; lean_object* v_toIntInfos_1983_; lean_object* v_toIntTermMap_1984_; lean_object* v_toIntVarMap_1985_; uint8_t v_usedCommRing_1986_; lean_object* v_nonlinearOccs_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1995_; 
v_vars_1963_ = lean_ctor_get(v_s_1962_, 0);
v_varMap_1964_ = lean_ctor_get(v_s_1962_, 1);
v_vars_x27_1965_ = lean_ctor_get(v_s_1962_, 2);
v_varMap_x27_1966_ = lean_ctor_get(v_s_1962_, 3);
v_natToIntMap_1967_ = lean_ctor_get(v_s_1962_, 4);
v_natDef_1968_ = lean_ctor_get(v_s_1962_, 5);
v_dvds_1969_ = lean_ctor_get(v_s_1962_, 6);
v_lowers_1970_ = lean_ctor_get(v_s_1962_, 7);
v_uppers_1971_ = lean_ctor_get(v_s_1962_, 8);
v_diseqs_1972_ = lean_ctor_get(v_s_1962_, 9);
v_elimEqs_1973_ = lean_ctor_get(v_s_1962_, 10);
v_elimStack_1974_ = lean_ctor_get(v_s_1962_, 11);
v_occurs_1975_ = lean_ctor_get(v_s_1962_, 12);
v_assignment_1976_ = lean_ctor_get(v_s_1962_, 13);
v_nextCnstrId_1977_ = lean_ctor_get(v_s_1962_, 14);
v_caseSplits_1978_ = lean_ctor_get_uint8(v_s_1962_, sizeof(void*)*23);
v_conflict_x3f_1979_ = lean_ctor_get(v_s_1962_, 15);
v_diseqSplits_1980_ = lean_ctor_get(v_s_1962_, 16);
v_divMod_1981_ = lean_ctor_get(v_s_1962_, 17);
v_toIntIds_1982_ = lean_ctor_get(v_s_1962_, 18);
v_toIntInfos_1983_ = lean_ctor_get(v_s_1962_, 19);
v_toIntTermMap_1984_ = lean_ctor_get(v_s_1962_, 20);
v_toIntVarMap_1985_ = lean_ctor_get(v_s_1962_, 21);
v_usedCommRing_1986_ = lean_ctor_get_uint8(v_s_1962_, sizeof(void*)*23 + 1);
v_nonlinearOccs_1987_ = lean_ctor_get(v_s_1962_, 22);
v_isSharedCheck_1995_ = !lean_is_exclusive(v_s_1962_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1989_ = v_s_1962_;
v_isShared_1990_ = v_isSharedCheck_1995_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_nonlinearOccs_1987_);
lean_inc(v_toIntVarMap_1985_);
lean_inc(v_toIntTermMap_1984_);
lean_inc(v_toIntInfos_1983_);
lean_inc(v_toIntIds_1982_);
lean_inc(v_divMod_1981_);
lean_inc(v_diseqSplits_1980_);
lean_inc(v_conflict_x3f_1979_);
lean_inc(v_nextCnstrId_1977_);
lean_inc(v_assignment_1976_);
lean_inc(v_occurs_1975_);
lean_inc(v_elimStack_1974_);
lean_inc(v_elimEqs_1973_);
lean_inc(v_diseqs_1972_);
lean_inc(v_uppers_1971_);
lean_inc(v_lowers_1970_);
lean_inc(v_dvds_1969_);
lean_inc(v_natDef_1968_);
lean_inc(v_natToIntMap_1967_);
lean_inc(v_varMap_x27_1966_);
lean_inc(v_vars_x27_1965_);
lean_inc(v_varMap_1964_);
lean_inc(v_vars_1963_);
lean_dec(v_s_1962_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1995_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1991_; lean_object* v___x_1993_; 
v___x_1991_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1(v_p_1960_, v_diseqs_1972_, v_x_1961_);
if (v_isShared_1990_ == 0)
{
lean_ctor_set(v___x_1989_, 9, v___x_1991_);
v___x_1993_ = v___x_1989_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_vars_1963_);
lean_ctor_set(v_reuseFailAlloc_1994_, 1, v_varMap_1964_);
lean_ctor_set(v_reuseFailAlloc_1994_, 2, v_vars_x27_1965_);
lean_ctor_set(v_reuseFailAlloc_1994_, 3, v_varMap_x27_1966_);
lean_ctor_set(v_reuseFailAlloc_1994_, 4, v_natToIntMap_1967_);
lean_ctor_set(v_reuseFailAlloc_1994_, 5, v_natDef_1968_);
lean_ctor_set(v_reuseFailAlloc_1994_, 6, v_dvds_1969_);
lean_ctor_set(v_reuseFailAlloc_1994_, 7, v_lowers_1970_);
lean_ctor_set(v_reuseFailAlloc_1994_, 8, v_uppers_1971_);
lean_ctor_set(v_reuseFailAlloc_1994_, 9, v___x_1991_);
lean_ctor_set(v_reuseFailAlloc_1994_, 10, v_elimEqs_1973_);
lean_ctor_set(v_reuseFailAlloc_1994_, 11, v_elimStack_1974_);
lean_ctor_set(v_reuseFailAlloc_1994_, 12, v_occurs_1975_);
lean_ctor_set(v_reuseFailAlloc_1994_, 13, v_assignment_1976_);
lean_ctor_set(v_reuseFailAlloc_1994_, 14, v_nextCnstrId_1977_);
lean_ctor_set(v_reuseFailAlloc_1994_, 15, v_conflict_x3f_1979_);
lean_ctor_set(v_reuseFailAlloc_1994_, 16, v_diseqSplits_1980_);
lean_ctor_set(v_reuseFailAlloc_1994_, 17, v_divMod_1981_);
lean_ctor_set(v_reuseFailAlloc_1994_, 18, v_toIntIds_1982_);
lean_ctor_set(v_reuseFailAlloc_1994_, 19, v_toIntInfos_1983_);
lean_ctor_set(v_reuseFailAlloc_1994_, 20, v_toIntTermMap_1984_);
lean_ctor_set(v_reuseFailAlloc_1994_, 21, v_toIntVarMap_1985_);
lean_ctor_set(v_reuseFailAlloc_1994_, 22, v_nonlinearOccs_1987_);
lean_ctor_set_uint8(v_reuseFailAlloc_1994_, sizeof(void*)*23, v_caseSplits_1978_);
lean_ctor_set_uint8(v_reuseFailAlloc_1994_, sizeof(void*)*23 + 1, v_usedCommRing_1986_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed(lean_object* v_p_1996_, lean_object* v_x_1997_, lean_object* v_s_1998_){
_start:
{
lean_object* v_res_1999_; 
v_res_1999_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0(v_p_1996_, v_x_1997_, v_s_1998_);
lean_dec(v_x_1997_);
lean_dec_ref(v_p_1996_);
return v_res_1999_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2006_ = lean_unsigned_to_nat(1u);
v___x_2007_ = lean_nat_to_int(v___x_2006_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(lean_object* v_c_2008_, lean_object* v_x_2009_, lean_object* v_as_2010_, size_t v_sz_2011_, size_t v_i_2012_, lean_object* v_b_2013_, lean_object* v___y_2014_){
_start:
{
uint8_t v___x_2016_; 
v___x_2016_ = lean_usize_dec_lt(v_i_2012_, v_sz_2011_);
if (v___x_2016_ == 0)
{
lean_object* v___x_2017_; 
lean_dec(v_x_2009_);
lean_dec_ref(v_c_2008_);
v___x_2017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2017_, 0, v_b_2013_);
return v___x_2017_;
}
else
{
lean_object* v_snd_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2064_; 
v_snd_2018_ = lean_ctor_get(v_b_2013_, 1);
v_isSharedCheck_2064_ = !lean_is_exclusive(v_b_2013_);
if (v_isSharedCheck_2064_ == 0)
{
lean_object* v_unused_2065_; 
v_unused_2065_ = lean_ctor_get(v_b_2013_, 0);
lean_dec(v_unused_2065_);
v___x_2020_ = v_b_2013_;
v_isShared_2021_ = v_isSharedCheck_2064_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_snd_2018_);
lean_dec(v_b_2013_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2064_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v_p_2022_; lean_object* v_a_2023_; lean_object* v_p_2024_; lean_object* v___x_2025_; lean_object* v___f_2026_; uint8_t v___y_2028_; uint8_t v___x_2062_; 
v_p_2022_ = lean_ctor_get(v_c_2008_, 0);
v_a_2023_ = lean_array_uget_borrowed(v_as_2010_, v_i_2012_);
v_p_2024_ = lean_ctor_get(v_a_2023_, 0);
v___x_2025_ = lean_box(0);
lean_inc(v_x_2009_);
lean_inc_ref(v_p_2024_);
v___f_2026_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2026_, 0, v_p_2024_);
lean_closure_set(v___f_2026_, 1, v_x_2009_);
v___x_2062_ = l_Int_Linear_instBEqPoly_beq(v_p_2022_, v_p_2024_);
if (v___x_2062_ == 0)
{
uint8_t v___x_2063_; 
v___x_2063_ = l_Int_Linear_Poly_isNegEq(v_p_2022_, v_p_2024_);
v___y_2028_ = v___x_2063_;
goto v___jp_2027_;
}
else
{
v___y_2028_ = v___x_2062_;
goto v___jp_2027_;
}
v___jp_2027_:
{
if (v___y_2028_ == 0)
{
lean_object* v___x_2029_; size_t v___x_2030_; size_t v___x_2031_; 
lean_dec_ref(v___f_2026_);
lean_del_object(v___x_2020_);
lean_dec(v_snd_2018_);
v___x_2029_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__1));
v___x_2030_ = ((size_t)1ULL);
v___x_2031_ = lean_usize_add(v_i_2012_, v___x_2030_);
v_i_2012_ = v___x_2031_;
v_b_2013_ = v___x_2029_;
goto _start;
}
else
{
lean_object* v___x_2033_; lean_object* v___x_2034_; 
lean_dec(v_x_2009_);
v___x_2033_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2034_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2033_, v___f_2026_, v___y_2014_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2052_; 
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2052_ == 0)
{
lean_object* v_unused_2053_; 
v_unused_2053_ = lean_ctor_get(v___x_2034_, 0);
lean_dec(v_unused_2053_);
v___x_2036_ = v___x_2034_;
v_isShared_2037_ = v_isSharedCheck_2052_;
goto v_resetjp_2035_;
}
else
{
lean_dec(v___x_2034_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2052_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2045_; 
v___x_2038_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
lean_inc_ref(v_p_2022_);
v___x_2039_ = l_Int_Linear_Poly_addConst(v_p_2022_, v___x_2038_);
lean_inc(v_a_2023_);
v___x_2040_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_2040_, 0, v_c_2008_);
lean_ctor_set(v___x_2040_, 1, v_a_2023_);
v___x_2041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2041_, 0, v___x_2039_);
lean_ctor_set(v___x_2041_, 1, v___x_2040_);
v___x_2042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2042_, 0, v___x_2041_);
v___x_2043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2043_, 0, v___x_2042_);
if (v_isShared_2021_ == 0)
{
lean_ctor_set(v___x_2020_, 1, v___x_2025_);
lean_ctor_set(v___x_2020_, 0, v___x_2043_);
v___x_2045_ = v___x_2020_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v___x_2043_);
lean_ctor_set(v_reuseFailAlloc_2051_, 1, v___x_2025_);
v___x_2045_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2049_; 
v___x_2046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2046_, 0, v___x_2045_);
v___x_2047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2047_, 0, v___x_2046_);
lean_ctor_set(v___x_2047_, 1, v_snd_2018_);
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 0, v___x_2047_);
v___x_2049_ = v___x_2036_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v___x_2047_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
}
else
{
lean_object* v_a_2054_; lean_object* v___x_2056_; uint8_t v_isShared_2057_; uint8_t v_isSharedCheck_2061_; 
lean_del_object(v___x_2020_);
lean_dec(v_snd_2018_);
lean_dec_ref(v_c_2008_);
v_a_2054_ = lean_ctor_get(v___x_2034_, 0);
v_isSharedCheck_2061_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2061_ == 0)
{
v___x_2056_ = v___x_2034_;
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
else
{
lean_inc(v_a_2054_);
lean_dec(v___x_2034_);
v___x_2056_ = lean_box(0);
v_isShared_2057_ = v_isSharedCheck_2061_;
goto v_resetjp_2055_;
}
v_resetjp_2055_:
{
lean_object* v___x_2059_; 
if (v_isShared_2057_ == 0)
{
v___x_2059_ = v___x_2056_;
goto v_reusejp_2058_;
}
else
{
lean_object* v_reuseFailAlloc_2060_; 
v_reuseFailAlloc_2060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2060_, 0, v_a_2054_);
v___x_2059_ = v_reuseFailAlloc_2060_;
goto v_reusejp_2058_;
}
v_reusejp_2058_:
{
return v___x_2059_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___boxed(lean_object* v_c_2066_, lean_object* v_x_2067_, lean_object* v_as_2068_, lean_object* v_sz_2069_, lean_object* v_i_2070_, lean_object* v_b_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_){
_start:
{
size_t v_sz_boxed_2074_; size_t v_i_boxed_2075_; lean_object* v_res_2076_; 
v_sz_boxed_2074_ = lean_unbox_usize(v_sz_2069_);
lean_dec(v_sz_2069_);
v_i_boxed_2075_ = lean_unbox_usize(v_i_2070_);
lean_dec(v_i_2070_);
v_res_2076_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(v_c_2066_, v_x_2067_, v_as_2068_, v_sz_boxed_2074_, v_i_boxed_2075_, v_b_2071_, v___y_2072_);
lean_dec(v___y_2072_);
lean_dec_ref(v_as_2068_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7(lean_object* v_c_2083_, lean_object* v_x_2084_, lean_object* v_as_2085_, size_t v_sz_2086_, size_t v_i_2087_, lean_object* v_b_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_){
_start:
{
uint8_t v___x_2100_; 
v___x_2100_ = lean_usize_dec_lt(v_i_2087_, v_sz_2086_);
if (v___x_2100_ == 0)
{
lean_object* v___x_2101_; 
lean_dec(v_x_2084_);
lean_dec_ref(v_c_2083_);
v___x_2101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2101_, 0, v_b_2088_);
return v___x_2101_;
}
else
{
lean_object* v_snd_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2148_; 
v_snd_2102_ = lean_ctor_get(v_b_2088_, 1);
v_isSharedCheck_2148_ = !lean_is_exclusive(v_b_2088_);
if (v_isSharedCheck_2148_ == 0)
{
lean_object* v_unused_2149_; 
v_unused_2149_ = lean_ctor_get(v_b_2088_, 0);
lean_dec(v_unused_2149_);
v___x_2104_ = v_b_2088_;
v_isShared_2105_ = v_isSharedCheck_2148_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_snd_2102_);
lean_dec(v_b_2088_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2148_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v_p_2106_; lean_object* v_a_2107_; lean_object* v_p_2108_; lean_object* v___x_2109_; lean_object* v___f_2110_; uint8_t v___y_2112_; uint8_t v___x_2146_; 
v_p_2106_ = lean_ctor_get(v_c_2083_, 0);
v_a_2107_ = lean_array_uget_borrowed(v_as_2085_, v_i_2087_);
v_p_2108_ = lean_ctor_get(v_a_2107_, 0);
v___x_2109_ = lean_box(0);
lean_inc(v_x_2084_);
lean_inc_ref(v_p_2108_);
v___f_2110_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2110_, 0, v_p_2108_);
lean_closure_set(v___f_2110_, 1, v_x_2084_);
v___x_2146_ = l_Int_Linear_instBEqPoly_beq(v_p_2106_, v_p_2108_);
if (v___x_2146_ == 0)
{
uint8_t v___x_2147_; 
v___x_2147_ = l_Int_Linear_Poly_isNegEq(v_p_2106_, v_p_2108_);
v___y_2112_ = v___x_2147_;
goto v___jp_2111_;
}
else
{
v___y_2112_ = v___x_2146_;
goto v___jp_2111_;
}
v___jp_2111_:
{
if (v___y_2112_ == 0)
{
lean_object* v___x_2113_; size_t v___x_2114_; size_t v___x_2115_; lean_object* v___x_2116_; 
lean_dec_ref(v___f_2110_);
lean_del_object(v___x_2104_);
lean_dec(v_snd_2102_);
v___x_2113_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___closed__1));
v___x_2114_ = ((size_t)1ULL);
v___x_2115_ = lean_usize_add(v_i_2087_, v___x_2114_);
v___x_2116_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(v_c_2083_, v_x_2084_, v_as_2085_, v_sz_2086_, v___x_2115_, v___x_2113_, v___y_2089_);
return v___x_2116_;
}
else
{
lean_object* v___x_2117_; lean_object* v___x_2118_; 
lean_dec(v_x_2084_);
v___x_2117_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2118_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2117_, v___f_2110_, v___y_2089_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2136_; 
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2136_ == 0)
{
lean_object* v_unused_2137_; 
v_unused_2137_ = lean_ctor_get(v___x_2118_, 0);
lean_dec(v_unused_2137_);
v___x_2120_ = v___x_2118_;
v_isShared_2121_ = v_isSharedCheck_2136_;
goto v_resetjp_2119_;
}
else
{
lean_dec(v___x_2118_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2136_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2129_; 
v___x_2122_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
lean_inc_ref(v_p_2106_);
v___x_2123_ = l_Int_Linear_Poly_addConst(v_p_2106_, v___x_2122_);
lean_inc(v_a_2107_);
v___x_2124_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_2124_, 0, v_c_2083_);
lean_ctor_set(v___x_2124_, 1, v_a_2107_);
v___x_2125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2123_);
lean_ctor_set(v___x_2125_, 1, v___x_2124_);
v___x_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2126_, 0, v___x_2125_);
v___x_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2126_);
if (v_isShared_2105_ == 0)
{
lean_ctor_set(v___x_2104_, 1, v___x_2109_);
lean_ctor_set(v___x_2104_, 0, v___x_2127_);
v___x_2129_ = v___x_2104_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v___x_2127_);
lean_ctor_set(v_reuseFailAlloc_2135_, 1, v___x_2109_);
v___x_2129_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2133_; 
v___x_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2129_);
v___x_2131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2130_);
lean_ctor_set(v___x_2131_, 1, v_snd_2102_);
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 0, v___x_2131_);
v___x_2133_ = v___x_2120_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v___x_2131_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
}
else
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2145_; 
lean_del_object(v___x_2104_);
lean_dec(v_snd_2102_);
lean_dec_ref(v_c_2083_);
v_a_2138_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2140_ = v___x_2118_;
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2118_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2143_; 
if (v_isShared_2141_ == 0)
{
v___x_2143_ = v___x_2140_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_a_2138_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
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
lean_object* v_c_2150_ = _args[0];
lean_object* v_x_2151_ = _args[1];
lean_object* v_as_2152_ = _args[2];
lean_object* v_sz_2153_ = _args[3];
lean_object* v_i_2154_ = _args[4];
lean_object* v_b_2155_ = _args[5];
lean_object* v___y_2156_ = _args[6];
lean_object* v___y_2157_ = _args[7];
lean_object* v___y_2158_ = _args[8];
lean_object* v___y_2159_ = _args[9];
lean_object* v___y_2160_ = _args[10];
lean_object* v___y_2161_ = _args[11];
lean_object* v___y_2162_ = _args[12];
lean_object* v___y_2163_ = _args[13];
lean_object* v___y_2164_ = _args[14];
lean_object* v___y_2165_ = _args[15];
lean_object* v___y_2166_ = _args[16];
_start:
{
size_t v_sz_boxed_2167_; size_t v_i_boxed_2168_; lean_object* v_res_2169_; 
v_sz_boxed_2167_ = lean_unbox_usize(v_sz_2153_);
lean_dec(v_sz_2153_);
v_i_boxed_2168_ = lean_unbox_usize(v_i_2154_);
lean_dec(v_i_2154_);
v_res_2169_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7(v_c_2150_, v_x_2151_, v_as_2152_, v_sz_boxed_2167_, v_i_boxed_2168_, v_b_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec(v___y_2161_);
lean_dec_ref(v___y_2160_);
lean_dec(v___y_2159_);
lean_dec_ref(v___y_2158_);
lean_dec(v___y_2157_);
lean_dec(v___y_2156_);
lean_dec_ref(v_as_2152_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(lean_object* v_c_2176_, lean_object* v_x_2177_, lean_object* v_as_2178_, size_t v_sz_2179_, size_t v_i_2180_, lean_object* v_b_2181_, lean_object* v___y_2182_){
_start:
{
uint8_t v___x_2184_; 
v___x_2184_ = lean_usize_dec_lt(v_i_2180_, v_sz_2179_);
if (v___x_2184_ == 0)
{
lean_object* v___x_2185_; 
lean_dec(v_x_2177_);
lean_dec_ref(v_c_2176_);
v___x_2185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2185_, 0, v_b_2181_);
return v___x_2185_;
}
else
{
lean_object* v_snd_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2233_; 
v_snd_2186_ = lean_ctor_get(v_b_2181_, 1);
v_isSharedCheck_2233_ = !lean_is_exclusive(v_b_2181_);
if (v_isSharedCheck_2233_ == 0)
{
lean_object* v_unused_2234_; 
v_unused_2234_ = lean_ctor_get(v_b_2181_, 0);
lean_dec(v_unused_2234_);
v___x_2188_ = v_b_2181_;
v_isShared_2189_ = v_isSharedCheck_2233_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_snd_2186_);
lean_dec(v_b_2181_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2233_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v_p_2190_; lean_object* v_a_2191_; lean_object* v_p_2192_; lean_object* v___x_2193_; lean_object* v___f_2194_; uint8_t v___y_2196_; uint8_t v___x_2231_; 
v_p_2190_ = lean_ctor_get(v_c_2176_, 0);
v_a_2191_ = lean_array_uget_borrowed(v_as_2178_, v_i_2180_);
v_p_2192_ = lean_ctor_get(v_a_2191_, 0);
v___x_2193_ = lean_box(0);
lean_inc(v_x_2177_);
lean_inc_ref(v_p_2192_);
v___f_2194_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2194_, 0, v_p_2192_);
lean_closure_set(v___f_2194_, 1, v_x_2177_);
v___x_2231_ = l_Int_Linear_instBEqPoly_beq(v_p_2190_, v_p_2192_);
if (v___x_2231_ == 0)
{
uint8_t v___x_2232_; 
v___x_2232_ = l_Int_Linear_Poly_isNegEq(v_p_2190_, v_p_2192_);
v___y_2196_ = v___x_2232_;
goto v___jp_2195_;
}
else
{
v___y_2196_ = v___x_2231_;
goto v___jp_2195_;
}
v___jp_2195_:
{
if (v___y_2196_ == 0)
{
lean_object* v___x_2197_; size_t v___x_2198_; size_t v___x_2199_; 
lean_dec_ref(v___f_2194_);
lean_del_object(v___x_2188_);
lean_dec(v_snd_2186_);
v___x_2197_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg___closed__1));
v___x_2198_ = ((size_t)1ULL);
v___x_2199_ = lean_usize_add(v_i_2180_, v___x_2198_);
v_i_2180_ = v___x_2199_;
v_b_2181_ = v___x_2197_;
goto _start;
}
else
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
lean_dec(v_x_2177_);
v___x_2201_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2202_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2201_, v___f_2194_, v___y_2182_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2221_; 
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2221_ == 0)
{
lean_object* v_unused_2222_; 
v_unused_2222_ = lean_ctor_get(v___x_2202_, 0);
lean_dec(v_unused_2222_);
v___x_2204_ = v___x_2202_;
v_isShared_2205_ = v_isSharedCheck_2221_;
goto v_resetjp_2203_;
}
else
{
lean_dec(v___x_2202_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2221_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2213_; 
v___x_2206_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
lean_inc_ref(v_p_2190_);
v___x_2207_ = l_Int_Linear_Poly_addConst(v_p_2190_, v___x_2206_);
lean_inc(v_a_2191_);
v___x_2208_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_2208_, 0, v_c_2176_);
lean_ctor_set(v___x_2208_, 1, v_a_2191_);
v___x_2209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2207_);
lean_ctor_set(v___x_2209_, 1, v___x_2208_);
v___x_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2209_);
v___x_2211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2210_);
if (v_isShared_2189_ == 0)
{
lean_ctor_set(v___x_2188_, 1, v___x_2193_);
lean_ctor_set(v___x_2188_, 0, v___x_2211_);
v___x_2213_ = v___x_2188_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v___x_2211_);
lean_ctor_set(v_reuseFailAlloc_2220_, 1, v___x_2193_);
v___x_2213_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2218_; 
v___x_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2214_, 0, v___x_2213_);
v___x_2215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2214_);
v___x_2216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2216_, 0, v___x_2215_);
lean_ctor_set(v___x_2216_, 1, v_snd_2186_);
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 0, v___x_2216_);
v___x_2218_ = v___x_2204_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v___x_2216_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
}
else
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2230_; 
lean_del_object(v___x_2188_);
lean_dec(v_snd_2186_);
lean_dec_ref(v_c_2176_);
v_a_2223_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2225_ = v___x_2202_;
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2202_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2228_; 
if (v_isShared_2226_ == 0)
{
v___x_2228_ = v___x_2225_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2223_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg___boxed(lean_object* v_c_2235_, lean_object* v_x_2236_, lean_object* v_as_2237_, lean_object* v_sz_2238_, lean_object* v_i_2239_, lean_object* v_b_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
size_t v_sz_boxed_2243_; size_t v_i_boxed_2244_; lean_object* v_res_2245_; 
v_sz_boxed_2243_ = lean_unbox_usize(v_sz_2238_);
lean_dec(v_sz_2238_);
v_i_boxed_2244_ = lean_unbox_usize(v_i_2239_);
lean_dec(v_i_2239_);
v_res_2245_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(v_c_2235_, v_x_2236_, v_as_2237_, v_sz_boxed_2243_, v_i_boxed_2244_, v_b_2240_, v___y_2241_);
lean_dec(v___y_2241_);
lean_dec_ref(v_as_2237_);
return v_res_2245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9(lean_object* v_c_2249_, lean_object* v_x_2250_, lean_object* v_as_2251_, size_t v_sz_2252_, size_t v_i_2253_, lean_object* v_b_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_){
_start:
{
uint8_t v___x_2266_; 
v___x_2266_ = lean_usize_dec_lt(v_i_2253_, v_sz_2252_);
if (v___x_2266_ == 0)
{
lean_object* v___x_2267_; 
lean_dec(v_x_2250_);
lean_dec_ref(v_c_2249_);
v___x_2267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2267_, 0, v_b_2254_);
return v___x_2267_;
}
else
{
lean_object* v_snd_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2315_; 
v_snd_2268_ = lean_ctor_get(v_b_2254_, 1);
v_isSharedCheck_2315_ = !lean_is_exclusive(v_b_2254_);
if (v_isSharedCheck_2315_ == 0)
{
lean_object* v_unused_2316_; 
v_unused_2316_ = lean_ctor_get(v_b_2254_, 0);
lean_dec(v_unused_2316_);
v___x_2270_ = v_b_2254_;
v_isShared_2271_ = v_isSharedCheck_2315_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_snd_2268_);
lean_dec(v_b_2254_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2315_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v_p_2272_; lean_object* v_a_2273_; lean_object* v_p_2274_; lean_object* v___x_2275_; lean_object* v___f_2276_; uint8_t v___y_2278_; uint8_t v___x_2313_; 
v_p_2272_ = lean_ctor_get(v_c_2249_, 0);
v_a_2273_ = lean_array_uget_borrowed(v_as_2251_, v_i_2253_);
v_p_2274_ = lean_ctor_get(v_a_2273_, 0);
v___x_2275_ = lean_box(0);
lean_inc(v_x_2250_);
lean_inc_ref(v_p_2274_);
v___f_2276_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2276_, 0, v_p_2274_);
lean_closure_set(v___f_2276_, 1, v_x_2250_);
v___x_2313_ = l_Int_Linear_instBEqPoly_beq(v_p_2272_, v_p_2274_);
if (v___x_2313_ == 0)
{
uint8_t v___x_2314_; 
v___x_2314_ = l_Int_Linear_Poly_isNegEq(v_p_2272_, v_p_2274_);
v___y_2278_ = v___x_2314_;
goto v___jp_2277_;
}
else
{
v___y_2278_ = v___x_2313_;
goto v___jp_2277_;
}
v___jp_2277_:
{
if (v___y_2278_ == 0)
{
lean_object* v___x_2279_; size_t v___x_2280_; size_t v___x_2281_; lean_object* v___x_2282_; 
lean_dec_ref(v___f_2276_);
lean_del_object(v___x_2270_);
lean_dec(v_snd_2268_);
v___x_2279_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9___closed__0));
v___x_2280_ = ((size_t)1ULL);
v___x_2281_ = lean_usize_add(v_i_2253_, v___x_2280_);
v___x_2282_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(v_c_2249_, v_x_2250_, v_as_2251_, v_sz_2252_, v___x_2281_, v___x_2279_, v___y_2255_);
return v___x_2282_;
}
else
{
lean_object* v___x_2283_; lean_object* v___x_2284_; 
lean_dec(v_x_2250_);
v___x_2283_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2284_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2283_, v___f_2276_, v___y_2255_);
if (lean_obj_tag(v___x_2284_) == 0)
{
lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2303_; 
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2303_ == 0)
{
lean_object* v_unused_2304_; 
v_unused_2304_ = lean_ctor_get(v___x_2284_, 0);
lean_dec(v_unused_2304_);
v___x_2286_ = v___x_2284_;
v_isShared_2287_ = v_isSharedCheck_2303_;
goto v_resetjp_2285_;
}
else
{
lean_dec(v___x_2284_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2303_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2295_; 
v___x_2288_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
lean_inc_ref(v_p_2272_);
v___x_2289_ = l_Int_Linear_Poly_addConst(v_p_2272_, v___x_2288_);
lean_inc(v_a_2273_);
v___x_2290_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_2290_, 0, v_c_2249_);
lean_ctor_set(v___x_2290_, 1, v_a_2273_);
v___x_2291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2289_);
lean_ctor_set(v___x_2291_, 1, v___x_2290_);
v___x_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2291_);
v___x_2293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2292_);
if (v_isShared_2271_ == 0)
{
lean_ctor_set(v___x_2270_, 1, v___x_2275_);
lean_ctor_set(v___x_2270_, 0, v___x_2293_);
v___x_2295_ = v___x_2270_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v___x_2293_);
lean_ctor_set(v_reuseFailAlloc_2302_, 1, v___x_2275_);
v___x_2295_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2300_; 
v___x_2296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2295_);
v___x_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2296_);
v___x_2298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2297_);
lean_ctor_set(v___x_2298_, 1, v_snd_2268_);
if (v_isShared_2287_ == 0)
{
lean_ctor_set(v___x_2286_, 0, v___x_2298_);
v___x_2300_ = v___x_2286_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v___x_2298_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
}
else
{
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2312_; 
lean_del_object(v___x_2270_);
lean_dec(v_snd_2268_);
lean_dec_ref(v_c_2249_);
v_a_2305_ = lean_ctor_get(v___x_2284_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2284_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2307_ = v___x_2284_;
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___x_2284_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2310_; 
if (v_isShared_2308_ == 0)
{
v___x_2310_ = v___x_2307_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_a_2305_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
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
lean_object* v_c_2317_ = _args[0];
lean_object* v_x_2318_ = _args[1];
lean_object* v_as_2319_ = _args[2];
lean_object* v_sz_2320_ = _args[3];
lean_object* v_i_2321_ = _args[4];
lean_object* v_b_2322_ = _args[5];
lean_object* v___y_2323_ = _args[6];
lean_object* v___y_2324_ = _args[7];
lean_object* v___y_2325_ = _args[8];
lean_object* v___y_2326_ = _args[9];
lean_object* v___y_2327_ = _args[10];
lean_object* v___y_2328_ = _args[11];
lean_object* v___y_2329_ = _args[12];
lean_object* v___y_2330_ = _args[13];
lean_object* v___y_2331_ = _args[14];
lean_object* v___y_2332_ = _args[15];
lean_object* v___y_2333_ = _args[16];
_start:
{
size_t v_sz_boxed_2334_; size_t v_i_boxed_2335_; lean_object* v_res_2336_; 
v_sz_boxed_2334_ = lean_unbox_usize(v_sz_2320_);
lean_dec(v_sz_2320_);
v_i_boxed_2335_ = lean_unbox_usize(v_i_2321_);
lean_dec(v_i_2321_);
v_res_2336_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9(v_c_2317_, v_x_2318_, v_as_2319_, v_sz_boxed_2334_, v_i_boxed_2335_, v_b_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_);
lean_dec(v___y_2332_);
lean_dec_ref(v___y_2331_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
lean_dec(v___y_2326_);
lean_dec_ref(v___y_2325_);
lean_dec(v___y_2324_);
lean_dec(v___y_2323_);
lean_dec_ref(v_as_2319_);
return v_res_2336_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(lean_object* v_init_2337_, lean_object* v_c_2338_, lean_object* v_x_2339_, lean_object* v_n_2340_, lean_object* v_b_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
if (lean_obj_tag(v_n_2340_) == 0)
{
lean_object* v_cs_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2387_; 
v_cs_2353_ = lean_ctor_get(v_n_2340_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v_n_2340_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2355_ = v_n_2340_;
v_isShared_2356_ = v_isSharedCheck_2387_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_cs_2353_);
lean_dec(v_n_2340_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2387_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; size_t v_sz_2359_; size_t v___x_2360_; lean_object* v___x_2361_; 
v___x_2357_ = lean_box(0);
v___x_2358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2357_);
lean_ctor_set(v___x_2358_, 1, v_b_2341_);
v_sz_2359_ = lean_array_size(v_cs_2353_);
v___x_2360_ = ((size_t)0ULL);
v___x_2361_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8(v_init_2337_, v_c_2338_, v_x_2339_, v_cs_2353_, v_sz_2359_, v___x_2360_, v___x_2358_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
lean_dec_ref(v_cs_2353_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2378_; 
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2364_ = v___x_2361_;
v_isShared_2365_ = v_isSharedCheck_2378_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2361_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2378_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v_fst_2366_; 
v_fst_2366_ = lean_ctor_get(v_a_2362_, 0);
if (lean_obj_tag(v_fst_2366_) == 0)
{
lean_object* v_snd_2367_; lean_object* v___x_2369_; 
v_snd_2367_ = lean_ctor_get(v_a_2362_, 1);
lean_inc(v_snd_2367_);
lean_dec(v_a_2362_);
if (v_isShared_2356_ == 0)
{
lean_ctor_set_tag(v___x_2355_, 1);
lean_ctor_set(v___x_2355_, 0, v_snd_2367_);
v___x_2369_ = v___x_2355_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2373_; 
v_reuseFailAlloc_2373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2373_, 0, v_snd_2367_);
v___x_2369_ = v_reuseFailAlloc_2373_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
lean_object* v___x_2371_; 
if (v_isShared_2365_ == 0)
{
lean_ctor_set(v___x_2364_, 0, v___x_2369_);
v___x_2371_ = v___x_2364_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v___x_2369_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
else
{
lean_object* v_val_2374_; lean_object* v___x_2376_; 
lean_inc_ref(v_fst_2366_);
lean_dec(v_a_2362_);
lean_del_object(v___x_2355_);
v_val_2374_ = lean_ctor_get(v_fst_2366_, 0);
lean_inc(v_val_2374_);
lean_dec_ref(v_fst_2366_);
if (v_isShared_2365_ == 0)
{
lean_ctor_set(v___x_2364_, 0, v_val_2374_);
v___x_2376_ = v___x_2364_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_val_2374_);
v___x_2376_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
return v___x_2376_;
}
}
}
}
else
{
lean_object* v_a_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2386_; 
lean_del_object(v___x_2355_);
v_a_2379_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2381_ = v___x_2361_;
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_a_2379_);
lean_dec(v___x_2361_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2384_; 
if (v_isShared_2382_ == 0)
{
v___x_2384_ = v___x_2381_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_a_2379_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
return v___x_2384_;
}
}
}
}
}
else
{
lean_object* v_vs_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2422_; 
v_vs_2388_ = lean_ctor_get(v_n_2340_, 0);
v_isSharedCheck_2422_ = !lean_is_exclusive(v_n_2340_);
if (v_isSharedCheck_2422_ == 0)
{
v___x_2390_ = v_n_2340_;
v_isShared_2391_ = v_isSharedCheck_2422_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_vs_2388_);
lean_dec(v_n_2340_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2422_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; size_t v_sz_2394_; size_t v___x_2395_; lean_object* v___x_2396_; 
v___x_2392_ = lean_box(0);
v___x_2393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2392_);
lean_ctor_set(v___x_2393_, 1, v_b_2341_);
v_sz_2394_ = lean_array_size(v_vs_2388_);
v___x_2395_ = ((size_t)0ULL);
v___x_2396_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9(v_c_2338_, v_x_2339_, v_vs_2388_, v_sz_2394_, v___x_2395_, v___x_2393_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_);
lean_dec_ref(v_vs_2388_);
if (lean_obj_tag(v___x_2396_) == 0)
{
lean_object* v_a_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2413_; 
v_a_2397_ = lean_ctor_get(v___x_2396_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2399_ = v___x_2396_;
v_isShared_2400_ = v_isSharedCheck_2413_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_a_2397_);
lean_dec(v___x_2396_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2413_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v_fst_2401_; 
v_fst_2401_ = lean_ctor_get(v_a_2397_, 0);
if (lean_obj_tag(v_fst_2401_) == 0)
{
lean_object* v_snd_2402_; lean_object* v___x_2404_; 
v_snd_2402_ = lean_ctor_get(v_a_2397_, 1);
lean_inc(v_snd_2402_);
lean_dec(v_a_2397_);
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 0, v_snd_2402_);
v___x_2404_ = v___x_2390_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v_snd_2402_);
v___x_2404_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
lean_object* v___x_2406_; 
if (v_isShared_2400_ == 0)
{
lean_ctor_set(v___x_2399_, 0, v___x_2404_);
v___x_2406_ = v___x_2399_;
goto v_reusejp_2405_;
}
else
{
lean_object* v_reuseFailAlloc_2407_; 
v_reuseFailAlloc_2407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2407_, 0, v___x_2404_);
v___x_2406_ = v_reuseFailAlloc_2407_;
goto v_reusejp_2405_;
}
v_reusejp_2405_:
{
return v___x_2406_;
}
}
}
else
{
lean_object* v_val_2409_; lean_object* v___x_2411_; 
lean_inc_ref(v_fst_2401_);
lean_dec(v_a_2397_);
lean_del_object(v___x_2390_);
v_val_2409_ = lean_ctor_get(v_fst_2401_, 0);
lean_inc(v_val_2409_);
lean_dec_ref(v_fst_2401_);
if (v_isShared_2400_ == 0)
{
lean_ctor_set(v___x_2399_, 0, v_val_2409_);
v___x_2411_ = v___x_2399_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_val_2409_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
}
else
{
lean_object* v_a_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2421_; 
lean_del_object(v___x_2390_);
v_a_2414_ = lean_ctor_get(v___x_2396_, 0);
v_isSharedCheck_2421_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2416_ = v___x_2396_;
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_a_2414_);
lean_dec(v___x_2396_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2421_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
lean_object* v___x_2419_; 
if (v_isShared_2417_ == 0)
{
v___x_2419_ = v___x_2416_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v_a_2414_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8(lean_object* v_init_2423_, lean_object* v_c_2424_, lean_object* v_x_2425_, lean_object* v_as_2426_, size_t v_sz_2427_, size_t v_i_2428_, lean_object* v_b_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_){
_start:
{
uint8_t v___x_2441_; 
v___x_2441_ = lean_usize_dec_lt(v_i_2428_, v_sz_2427_);
if (v___x_2441_ == 0)
{
lean_object* v___x_2442_; 
lean_dec(v_x_2425_);
lean_dec_ref(v_c_2424_);
v___x_2442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2442_, 0, v_b_2429_);
return v___x_2442_;
}
else
{
lean_object* v_snd_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2477_; 
v_snd_2443_ = lean_ctor_get(v_b_2429_, 1);
v_isSharedCheck_2477_ = !lean_is_exclusive(v_b_2429_);
if (v_isSharedCheck_2477_ == 0)
{
lean_object* v_unused_2478_; 
v_unused_2478_ = lean_ctor_get(v_b_2429_, 0);
lean_dec(v_unused_2478_);
v___x_2445_ = v_b_2429_;
v_isShared_2446_ = v_isSharedCheck_2477_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_snd_2443_);
lean_dec(v_b_2429_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2477_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v_a_2447_; lean_object* v___x_2448_; 
v_a_2447_ = lean_array_uget_borrowed(v_as_2426_, v_i_2428_);
lean_inc(v_snd_2443_);
lean_inc(v_a_2447_);
lean_inc(v_x_2425_);
lean_inc_ref(v_c_2424_);
v___x_2448_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(v_init_2423_, v_c_2424_, v_x_2425_, v_a_2447_, v_snd_2443_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
if (lean_obj_tag(v___x_2448_) == 0)
{
lean_object* v_a_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2468_; 
v_a_2449_ = lean_ctor_get(v___x_2448_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2448_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2451_ = v___x_2448_;
v_isShared_2452_ = v_isSharedCheck_2468_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_a_2449_);
lean_dec(v___x_2448_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2468_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
if (lean_obj_tag(v_a_2449_) == 0)
{
lean_object* v___x_2453_; lean_object* v___x_2455_; 
lean_dec(v_x_2425_);
lean_dec_ref(v_c_2424_);
v___x_2453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2453_, 0, v_a_2449_);
if (v_isShared_2446_ == 0)
{
lean_ctor_set(v___x_2445_, 0, v___x_2453_);
v___x_2455_ = v___x_2445_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v___x_2453_);
lean_ctor_set(v_reuseFailAlloc_2459_, 1, v_snd_2443_);
v___x_2455_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
lean_object* v___x_2457_; 
if (v_isShared_2452_ == 0)
{
lean_ctor_set(v___x_2451_, 0, v___x_2455_);
v___x_2457_ = v___x_2451_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v___x_2455_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
return v___x_2457_;
}
}
}
else
{
lean_object* v_a_2460_; lean_object* v___x_2461_; lean_object* v___x_2463_; 
lean_del_object(v___x_2451_);
lean_dec(v_snd_2443_);
v_a_2460_ = lean_ctor_get(v_a_2449_, 0);
lean_inc(v_a_2460_);
lean_dec_ref(v_a_2449_);
v___x_2461_ = lean_box(0);
if (v_isShared_2446_ == 0)
{
lean_ctor_set(v___x_2445_, 1, v_a_2460_);
lean_ctor_set(v___x_2445_, 0, v___x_2461_);
v___x_2463_ = v___x_2445_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v___x_2461_);
lean_ctor_set(v_reuseFailAlloc_2467_, 1, v_a_2460_);
v___x_2463_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
size_t v___x_2464_; size_t v___x_2465_; 
v___x_2464_ = ((size_t)1ULL);
v___x_2465_ = lean_usize_add(v_i_2428_, v___x_2464_);
v_i_2428_ = v___x_2465_;
v_b_2429_ = v___x_2463_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2476_; 
lean_del_object(v___x_2445_);
lean_dec(v_snd_2443_);
lean_dec(v_x_2425_);
lean_dec_ref(v_c_2424_);
v_a_2469_ = lean_ctor_get(v___x_2448_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2448_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2471_ = v___x_2448_;
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___x_2448_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2474_; 
if (v_isShared_2472_ == 0)
{
v___x_2474_ = v___x_2471_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_a_2469_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8___boxed(lean_object** _args){
lean_object* v_init_2479_ = _args[0];
lean_object* v_c_2480_ = _args[1];
lean_object* v_x_2481_ = _args[2];
lean_object* v_as_2482_ = _args[3];
lean_object* v_sz_2483_ = _args[4];
lean_object* v_i_2484_ = _args[5];
lean_object* v_b_2485_ = _args[6];
lean_object* v___y_2486_ = _args[7];
lean_object* v___y_2487_ = _args[8];
lean_object* v___y_2488_ = _args[9];
lean_object* v___y_2489_ = _args[10];
lean_object* v___y_2490_ = _args[11];
lean_object* v___y_2491_ = _args[12];
lean_object* v___y_2492_ = _args[13];
lean_object* v___y_2493_ = _args[14];
lean_object* v___y_2494_ = _args[15];
lean_object* v___y_2495_ = _args[16];
lean_object* v___y_2496_ = _args[17];
_start:
{
size_t v_sz_boxed_2497_; size_t v_i_boxed_2498_; lean_object* v_res_2499_; 
v_sz_boxed_2497_ = lean_unbox_usize(v_sz_2483_);
lean_dec(v_sz_2483_);
v_i_boxed_2498_ = lean_unbox_usize(v_i_2484_);
lean_dec(v_i_2484_);
v_res_2499_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8(v_init_2479_, v_c_2480_, v_x_2481_, v_as_2482_, v_sz_boxed_2497_, v_i_boxed_2498_, v_b_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
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
lean_dec_ref(v_as_2482_);
lean_dec_ref(v_init_2479_);
return v_res_2499_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6___boxed(lean_object* v_init_2500_, lean_object* v_c_2501_, lean_object* v_x_2502_, lean_object* v_n_2503_, lean_object* v_b_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_){
_start:
{
lean_object* v_res_2516_; 
v_res_2516_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(v_init_2500_, v_c_2501_, v_x_2502_, v_n_2503_, v_b_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_);
lean_dec(v___y_2514_);
lean_dec_ref(v___y_2513_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
lean_dec(v___y_2510_);
lean_dec_ref(v___y_2509_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec(v___y_2505_);
lean_dec_ref(v_init_2500_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2(lean_object* v_c_2517_, lean_object* v_x_2518_, lean_object* v_t_2519_, lean_object* v_init_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_){
_start:
{
lean_object* v_root_2532_; lean_object* v_tail_2533_; lean_object* v___x_2534_; 
v_root_2532_ = lean_ctor_get(v_t_2519_, 0);
lean_inc_ref(v_root_2532_);
v_tail_2533_ = lean_ctor_get(v_t_2519_, 1);
lean_inc_ref(v_tail_2533_);
lean_dec_ref(v_t_2519_);
lean_inc(v_x_2518_);
lean_inc_ref(v_c_2517_);
lean_inc_ref(v_init_2520_);
v___x_2534_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(v_init_2520_, v_c_2517_, v_x_2518_, v_root_2532_, v_init_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
lean_dec_ref(v_init_2520_);
if (lean_obj_tag(v___x_2534_) == 0)
{
lean_object* v_a_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2571_; 
v_a_2535_ = lean_ctor_get(v___x_2534_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2534_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2537_ = v___x_2534_;
v_isShared_2538_ = v_isSharedCheck_2571_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_a_2535_);
lean_dec(v___x_2534_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2571_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
if (lean_obj_tag(v_a_2535_) == 0)
{
lean_object* v_a_2539_; lean_object* v___x_2541_; 
lean_dec_ref(v_tail_2533_);
lean_dec(v_x_2518_);
lean_dec_ref(v_c_2517_);
v_a_2539_ = lean_ctor_get(v_a_2535_, 0);
lean_inc(v_a_2539_);
lean_dec_ref(v_a_2535_);
if (v_isShared_2538_ == 0)
{
lean_ctor_set(v___x_2537_, 0, v_a_2539_);
v___x_2541_ = v___x_2537_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_a_2539_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
else
{
lean_object* v_a_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; size_t v_sz_2546_; size_t v___x_2547_; lean_object* v___x_2548_; 
lean_del_object(v___x_2537_);
v_a_2543_ = lean_ctor_get(v_a_2535_, 0);
lean_inc(v_a_2543_);
lean_dec_ref(v_a_2535_);
v___x_2544_ = lean_box(0);
v___x_2545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2545_, 0, v___x_2544_);
lean_ctor_set(v___x_2545_, 1, v_a_2543_);
v_sz_2546_ = lean_array_size(v_tail_2533_);
v___x_2547_ = ((size_t)0ULL);
v___x_2548_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7(v_c_2517_, v_x_2518_, v_tail_2533_, v_sz_2546_, v___x_2547_, v___x_2545_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
lean_dec_ref(v_tail_2533_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2562_; 
v_a_2549_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2551_ = v___x_2548_;
v_isShared_2552_ = v_isSharedCheck_2562_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_dec(v___x_2548_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2562_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v_fst_2553_; 
v_fst_2553_ = lean_ctor_get(v_a_2549_, 0);
if (lean_obj_tag(v_fst_2553_) == 0)
{
lean_object* v_snd_2554_; lean_object* v___x_2556_; 
v_snd_2554_ = lean_ctor_get(v_a_2549_, 1);
lean_inc(v_snd_2554_);
lean_dec(v_a_2549_);
if (v_isShared_2552_ == 0)
{
lean_ctor_set(v___x_2551_, 0, v_snd_2554_);
v___x_2556_ = v___x_2551_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_snd_2554_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
else
{
lean_object* v_val_2558_; lean_object* v___x_2560_; 
lean_inc_ref(v_fst_2553_);
lean_dec(v_a_2549_);
v_val_2558_ = lean_ctor_get(v_fst_2553_, 0);
lean_inc(v_val_2558_);
lean_dec_ref(v_fst_2553_);
if (v_isShared_2552_ == 0)
{
lean_ctor_set(v___x_2551_, 0, v_val_2558_);
v___x_2560_ = v___x_2551_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_val_2558_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
}
else
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2570_; 
v_a_2563_ = lean_ctor_get(v___x_2548_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2548_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2565_ = v___x_2548_;
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___x_2548_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2568_; 
if (v_isShared_2566_ == 0)
{
v___x_2568_ = v___x_2565_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_a_2563_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
}
}
}
else
{
lean_object* v_a_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2579_; 
lean_dec_ref(v_tail_2533_);
lean_dec(v_x_2518_);
lean_dec_ref(v_c_2517_);
v_a_2572_ = lean_ctor_get(v___x_2534_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2534_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2574_ = v___x_2534_;
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_a_2572_);
lean_dec(v___x_2534_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2577_; 
if (v_isShared_2575_ == 0)
{
v___x_2577_ = v___x_2574_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_a_2572_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2___boxed(lean_object* v_c_2580_, lean_object* v_x_2581_, lean_object* v_t_2582_, lean_object* v_init_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_, lean_object* v___y_2593_, lean_object* v___y_2594_){
_start:
{
lean_object* v_res_2595_; 
v_res_2595_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2(v_c_2580_, v_x_2581_, v_t_2582_, v_init_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_);
lean_dec(v___y_2593_);
lean_dec_ref(v___y_2592_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2588_);
lean_dec(v___y_2587_);
lean_dec_ref(v___y_2586_);
lean_dec(v___y_2585_);
lean_dec(v___y_2584_);
return v_res_2595_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(lean_object* v_x_2596_, lean_object* v_c_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_){
_start:
{
lean_object* v___x_2609_; 
v___x_2609_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2598_, v_a_2606_);
if (lean_obj_tag(v___x_2609_) == 0)
{
lean_object* v_a_2610_; lean_object* v___y_2612_; lean_object* v_diseqs_2637_; lean_object* v_size_2638_; lean_object* v___x_2639_; uint8_t v___x_2640_; 
v_a_2610_ = lean_ctor_get(v___x_2609_, 0);
lean_inc(v_a_2610_);
lean_dec_ref(v___x_2609_);
v_diseqs_2637_ = lean_ctor_get(v_a_2610_, 9);
lean_inc_ref(v_diseqs_2637_);
lean_dec(v_a_2610_);
v_size_2638_ = lean_ctor_get(v_diseqs_2637_, 2);
v___x_2639_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0);
v___x_2640_ = lean_nat_dec_lt(v_x_2596_, v_size_2638_);
if (v___x_2640_ == 0)
{
lean_object* v___x_2641_; 
lean_dec_ref(v_diseqs_2637_);
v___x_2641_ = l_outOfBounds___redArg(v___x_2639_);
v___y_2612_ = v___x_2641_;
goto v___jp_2611_;
}
else
{
lean_object* v___x_2642_; 
v___x_2642_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2639_, v_diseqs_2637_, v_x_2596_);
lean_dec_ref(v_diseqs_2637_);
v___y_2612_ = v___x_2642_;
goto v___jp_2611_;
}
v___jp_2611_:
{
lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2613_ = lean_box(0);
v___x_2614_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___closed__0));
v___x_2615_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2(v_c_2597_, v_x_2596_, v___y_2612_, v___x_2614_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, v_a_2607_);
if (lean_obj_tag(v___x_2615_) == 0)
{
lean_object* v_a_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2628_; 
v_a_2616_ = lean_ctor_get(v___x_2615_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2615_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2618_ = v___x_2615_;
v_isShared_2619_ = v_isSharedCheck_2628_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_a_2616_);
lean_dec(v___x_2615_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2628_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v_fst_2620_; 
v_fst_2620_ = lean_ctor_get(v_a_2616_, 0);
lean_inc(v_fst_2620_);
lean_dec(v_a_2616_);
if (lean_obj_tag(v_fst_2620_) == 0)
{
lean_object* v___x_2622_; 
if (v_isShared_2619_ == 0)
{
lean_ctor_set(v___x_2618_, 0, v___x_2613_);
v___x_2622_ = v___x_2618_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v___x_2613_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
else
{
lean_object* v_val_2624_; lean_object* v___x_2626_; 
v_val_2624_ = lean_ctor_get(v_fst_2620_, 0);
lean_inc(v_val_2624_);
lean_dec_ref(v_fst_2620_);
if (v_isShared_2619_ == 0)
{
lean_ctor_set(v___x_2618_, 0, v_val_2624_);
v___x_2626_ = v___x_2618_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_val_2624_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
else
{
lean_object* v_a_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2636_; 
v_a_2629_ = lean_ctor_get(v___x_2615_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2615_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2631_ = v___x_2615_;
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_a_2629_);
lean_dec(v___x_2615_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2634_; 
if (v_isShared_2632_ == 0)
{
v___x_2634_ = v___x_2631_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_a_2629_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
}
}
else
{
lean_object* v_a_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2650_; 
lean_dec_ref(v_c_2597_);
lean_dec(v_x_2596_);
v_a_2643_ = lean_ctor_get(v___x_2609_, 0);
v_isSharedCheck_2650_ = !lean_is_exclusive(v___x_2609_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2645_ = v___x_2609_;
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_a_2643_);
lean_dec(v___x_2609_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2650_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v___x_2648_; 
if (v_isShared_2646_ == 0)
{
v___x_2648_ = v___x_2645_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_a_2643_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f___boxed(lean_object* v_x_2651_, lean_object* v_c_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_){
_start:
{
lean_object* v_res_2664_; 
v_res_2664_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(v_x_2651_, v_c_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_);
lean_dec(v_a_2662_);
lean_dec_ref(v_a_2661_);
lean_dec(v_a_2660_);
lean_dec_ref(v_a_2659_);
lean_dec(v_a_2658_);
lean_dec_ref(v_a_2657_);
lean_dec(v_a_2656_);
lean_dec_ref(v_a_2655_);
lean_dec(v_a_2654_);
lean_dec(v_a_2653_);
return v_res_2664_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11(lean_object* v_c_2665_, lean_object* v_x_2666_, lean_object* v_as_2667_, size_t v_sz_2668_, size_t v_i_2669_, lean_object* v_b_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_){
_start:
{
lean_object* v___x_2682_; 
v___x_2682_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(v_c_2665_, v_x_2666_, v_as_2667_, v_sz_2668_, v_i_2669_, v_b_2670_, v___y_2671_);
return v___x_2682_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___boxed(lean_object** _args){
lean_object* v_c_2683_ = _args[0];
lean_object* v_x_2684_ = _args[1];
lean_object* v_as_2685_ = _args[2];
lean_object* v_sz_2686_ = _args[3];
lean_object* v_i_2687_ = _args[4];
lean_object* v_b_2688_ = _args[5];
lean_object* v___y_2689_ = _args[6];
lean_object* v___y_2690_ = _args[7];
lean_object* v___y_2691_ = _args[8];
lean_object* v___y_2692_ = _args[9];
lean_object* v___y_2693_ = _args[10];
lean_object* v___y_2694_ = _args[11];
lean_object* v___y_2695_ = _args[12];
lean_object* v___y_2696_ = _args[13];
lean_object* v___y_2697_ = _args[14];
lean_object* v___y_2698_ = _args[15];
lean_object* v___y_2699_ = _args[16];
_start:
{
size_t v_sz_boxed_2700_; size_t v_i_boxed_2701_; lean_object* v_res_2702_; 
v_sz_boxed_2700_ = lean_unbox_usize(v_sz_2686_);
lean_dec(v_sz_2686_);
v_i_boxed_2701_ = lean_unbox_usize(v_i_2687_);
lean_dec(v_i_2687_);
v_res_2702_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11(v_c_2683_, v_x_2684_, v_as_2685_, v_sz_boxed_2700_, v_i_boxed_2701_, v_b_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
lean_dec(v___y_2698_);
lean_dec_ref(v___y_2697_);
lean_dec(v___y_2696_);
lean_dec_ref(v___y_2695_);
lean_dec(v___y_2694_);
lean_dec_ref(v___y_2693_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
lean_dec(v___y_2690_);
lean_dec(v___y_2689_);
lean_dec_ref(v_as_2685_);
return v_res_2702_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10(lean_object* v_c_2703_, lean_object* v_x_2704_, lean_object* v_as_2705_, size_t v_sz_2706_, size_t v_i_2707_, lean_object* v_b_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
lean_object* v___x_2720_; 
v___x_2720_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(v_c_2703_, v_x_2704_, v_as_2705_, v_sz_2706_, v_i_2707_, v_b_2708_, v___y_2709_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___boxed(lean_object** _args){
lean_object* v_c_2721_ = _args[0];
lean_object* v_x_2722_ = _args[1];
lean_object* v_as_2723_ = _args[2];
lean_object* v_sz_2724_ = _args[3];
lean_object* v_i_2725_ = _args[4];
lean_object* v_b_2726_ = _args[5];
lean_object* v___y_2727_ = _args[6];
lean_object* v___y_2728_ = _args[7];
lean_object* v___y_2729_ = _args[8];
lean_object* v___y_2730_ = _args[9];
lean_object* v___y_2731_ = _args[10];
lean_object* v___y_2732_ = _args[11];
lean_object* v___y_2733_ = _args[12];
lean_object* v___y_2734_ = _args[13];
lean_object* v___y_2735_ = _args[14];
lean_object* v___y_2736_ = _args[15];
lean_object* v___y_2737_ = _args[16];
_start:
{
size_t v_sz_boxed_2738_; size_t v_i_boxed_2739_; lean_object* v_res_2740_; 
v_sz_boxed_2738_ = lean_unbox_usize(v_sz_2724_);
lean_dec(v_sz_2724_);
v_i_boxed_2739_ = lean_unbox_usize(v_i_2725_);
lean_dec(v_i_2725_);
v_res_2740_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10(v_c_2721_, v_x_2722_, v_as_2723_, v_sz_boxed_2738_, v_i_boxed_2739_, v_b_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_, v___y_2735_, v___y_2736_);
lean_dec(v___y_2736_);
lean_dec_ref(v___y_2735_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec(v___y_2730_);
lean_dec_ref(v___y_2729_);
lean_dec(v___y_2728_);
lean_dec(v___y_2727_);
lean_dec_ref(v_as_2723_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0(lean_object* v_v_2741_, lean_object* v_b_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_){
_start:
{
lean_object* v_snd_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2785_; 
v_snd_2754_ = lean_ctor_get(v_b_2742_, 1);
v_isSharedCheck_2785_ = !lean_is_exclusive(v_b_2742_);
if (v_isSharedCheck_2785_ == 0)
{
lean_object* v_unused_2786_; 
v_unused_2786_ = lean_ctor_get(v_b_2742_, 0);
lean_dec(v_unused_2786_);
v___x_2756_ = v_b_2742_;
v_isShared_2757_ = v_isSharedCheck_2785_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_snd_2754_);
lean_dec(v_b_2742_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2785_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v___x_2758_; 
lean_inc(v_snd_2754_);
lean_inc(v_v_2741_);
v___x_2758_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(v_v_2741_, v_snd_2754_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
if (lean_obj_tag(v___x_2758_) == 0)
{
lean_object* v_a_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2776_; 
v_a_2759_ = lean_ctor_get(v___x_2758_, 0);
v_isSharedCheck_2776_ = !lean_is_exclusive(v___x_2758_);
if (v_isSharedCheck_2776_ == 0)
{
v___x_2761_ = v___x_2758_;
v_isShared_2762_ = v_isSharedCheck_2776_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_a_2759_);
lean_dec(v___x_2758_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2776_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
if (lean_obj_tag(v_a_2759_) == 1)
{
lean_object* v_val_2763_; lean_object* v___x_2764_; lean_object* v___x_2766_; 
lean_del_object(v___x_2761_);
lean_dec(v_snd_2754_);
v_val_2763_ = lean_ctor_get(v_a_2759_, 0);
lean_inc(v_val_2763_);
lean_dec_ref(v_a_2759_);
v___x_2764_ = lean_box(0);
if (v_isShared_2757_ == 0)
{
lean_ctor_set(v___x_2756_, 1, v_val_2763_);
lean_ctor_set(v___x_2756_, 0, v___x_2764_);
v___x_2766_ = v___x_2756_;
goto v_reusejp_2765_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v___x_2764_);
lean_ctor_set(v_reuseFailAlloc_2768_, 1, v_val_2763_);
v___x_2766_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2765_;
}
v_reusejp_2765_:
{
v_b_2742_ = v___x_2766_;
goto _start;
}
}
else
{
lean_object* v___x_2769_; lean_object* v___x_2771_; 
lean_dec(v_a_2759_);
lean_dec(v_v_2741_);
lean_inc(v_snd_2754_);
v___x_2769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2769_, 0, v_snd_2754_);
if (v_isShared_2757_ == 0)
{
lean_ctor_set(v___x_2756_, 0, v___x_2769_);
v___x_2771_ = v___x_2756_;
goto v_reusejp_2770_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v___x_2769_);
lean_ctor_set(v_reuseFailAlloc_2775_, 1, v_snd_2754_);
v___x_2771_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2770_;
}
v_reusejp_2770_:
{
lean_object* v___x_2773_; 
if (v_isShared_2762_ == 0)
{
lean_ctor_set(v___x_2761_, 0, v___x_2771_);
v___x_2773_ = v___x_2761_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v___x_2771_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
}
}
}
else
{
lean_object* v_a_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2784_; 
lean_del_object(v___x_2756_);
lean_dec(v_snd_2754_);
lean_dec(v_v_2741_);
v_a_2777_ = lean_ctor_get(v___x_2758_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v___x_2758_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2779_ = v___x_2758_;
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v___x_2758_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2784_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___x_2782_; 
if (v_isShared_2780_ == 0)
{
v___x_2782_ = v___x_2779_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2783_; 
v_reuseFailAlloc_2783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2783_, 0, v_a_2777_);
v___x_2782_ = v_reuseFailAlloc_2783_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
return v___x_2782_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___boxed(lean_object* v_v_2787_, lean_object* v_b_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_){
_start:
{
lean_object* v_res_2800_; 
v_res_2800_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0(v_v_2787_, v_b_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
lean_dec(v___y_2798_);
lean_dec_ref(v___y_2797_);
lean_dec(v___y_2796_);
lean_dec_ref(v___y_2795_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec(v___y_2792_);
lean_dec_ref(v___y_2791_);
lean_dec(v___y_2790_);
lean_dec(v___y_2789_);
return v_res_2800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(lean_object* v_c_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_, lean_object* v_a_2811_){
_start:
{
lean_object* v_p_2813_; 
v_p_2813_ = lean_ctor_get(v_c_2801_, 0);
if (lean_obj_tag(v_p_2813_) == 1)
{
lean_object* v_v_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; 
v_v_2814_ = lean_ctor_get(v_p_2813_, 1);
lean_inc(v_v_2814_);
v___x_2815_ = lean_box(0);
v___x_2816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2816_, 0, v___x_2815_);
lean_ctor_set(v___x_2816_, 1, v_c_2801_);
v___x_2817_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0(v_v_2814_, v___x_2816_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_);
if (lean_obj_tag(v___x_2817_) == 0)
{
lean_object* v_a_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2831_; 
v_a_2818_ = lean_ctor_get(v___x_2817_, 0);
v_isSharedCheck_2831_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2820_ = v___x_2817_;
v_isShared_2821_ = v_isSharedCheck_2831_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_a_2818_);
lean_dec(v___x_2817_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2831_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v_fst_2822_; 
v_fst_2822_ = lean_ctor_get(v_a_2818_, 0);
if (lean_obj_tag(v_fst_2822_) == 0)
{
lean_object* v_snd_2823_; lean_object* v___x_2825_; 
v_snd_2823_ = lean_ctor_get(v_a_2818_, 1);
lean_inc(v_snd_2823_);
lean_dec(v_a_2818_);
if (v_isShared_2821_ == 0)
{
lean_ctor_set(v___x_2820_, 0, v_snd_2823_);
v___x_2825_ = v___x_2820_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_snd_2823_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
else
{
lean_object* v_val_2827_; lean_object* v___x_2829_; 
lean_inc_ref(v_fst_2822_);
lean_dec(v_a_2818_);
v_val_2827_ = lean_ctor_get(v_fst_2822_, 0);
lean_inc(v_val_2827_);
lean_dec_ref(v_fst_2822_);
if (v_isShared_2821_ == 0)
{
lean_ctor_set(v___x_2820_, 0, v_val_2827_);
v___x_2829_ = v___x_2820_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v_val_2827_);
v___x_2829_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
return v___x_2829_;
}
}
}
}
else
{
lean_object* v_a_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2839_; 
v_a_2832_ = lean_ctor_get(v___x_2817_, 0);
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2817_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2834_ = v___x_2817_;
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_a_2832_);
lean_dec(v___x_2817_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2837_; 
if (v_isShared_2835_ == 0)
{
v___x_2837_ = v___x_2834_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_a_2832_);
v___x_2837_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
return v___x_2837_;
}
}
}
}
else
{
lean_object* v___x_2840_; 
v___x_2840_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_2801_, v_a_2802_, v_a_2808_, v_a_2809_, v_a_2810_, v_a_2811_);
return v___x_2840_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq___boxed(lean_object* v_c_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_){
_start:
{
lean_object* v_res_2853_; 
v_res_2853_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(v_c_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_);
lean_dec(v_a_2851_);
lean_dec_ref(v_a_2850_);
lean_dec(v_a_2849_);
lean_dec_ref(v_a_2848_);
lean_dec(v_a_2847_);
lean_dec_ref(v_a_2846_);
lean_dec(v_a_2845_);
lean_dec_ref(v_a_2844_);
lean_dec(v_a_2843_);
lean_dec(v_a_2842_);
return v_res_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(lean_object* v_a_2854_, lean_object* v_x_2855_, size_t v_x_2856_, size_t v_x_2857_){
_start:
{
if (lean_obj_tag(v_x_2855_) == 0)
{
lean_object* v_cs_2858_; size_t v_j_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; uint8_t v___x_2862_; 
v_cs_2858_ = lean_ctor_get(v_x_2855_, 0);
v_j_2859_ = lean_usize_shift_right(v_x_2856_, v_x_2857_);
v___x_2860_ = lean_usize_to_nat(v_j_2859_);
v___x_2861_ = lean_array_get_size(v_cs_2858_);
v___x_2862_ = lean_nat_dec_lt(v___x_2860_, v___x_2861_);
if (v___x_2862_ == 0)
{
lean_dec(v___x_2860_);
lean_dec_ref(v_a_2854_);
return v_x_2855_;
}
else
{
lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2880_; 
lean_inc_ref(v_cs_2858_);
v_isSharedCheck_2880_ = !lean_is_exclusive(v_x_2855_);
if (v_isSharedCheck_2880_ == 0)
{
lean_object* v_unused_2881_; 
v_unused_2881_ = lean_ctor_get(v_x_2855_, 0);
lean_dec(v_unused_2881_);
v___x_2864_ = v_x_2855_;
v_isShared_2865_ = v_isSharedCheck_2880_;
goto v_resetjp_2863_;
}
else
{
lean_dec(v_x_2855_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2880_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
size_t v___x_2866_; size_t v___x_2867_; size_t v___x_2868_; size_t v_i_2869_; size_t v___x_2870_; size_t v_shift_2871_; lean_object* v_v_2872_; lean_object* v___x_2873_; lean_object* v_xs_x27_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2878_; 
v___x_2866_ = ((size_t)1ULL);
v___x_2867_ = lean_usize_shift_left(v___x_2866_, v_x_2857_);
v___x_2868_ = lean_usize_sub(v___x_2867_, v___x_2866_);
v_i_2869_ = lean_usize_land(v_x_2856_, v___x_2868_);
v___x_2870_ = ((size_t)5ULL);
v_shift_2871_ = lean_usize_sub(v_x_2857_, v___x_2870_);
v_v_2872_ = lean_array_fget(v_cs_2858_, v___x_2860_);
v___x_2873_ = lean_box(0);
v_xs_x27_2874_ = lean_array_fset(v_cs_2858_, v___x_2860_, v___x_2873_);
v___x_2875_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(v_a_2854_, v_v_2872_, v_i_2869_, v_shift_2871_);
v___x_2876_ = lean_array_fset(v_xs_x27_2874_, v___x_2860_, v___x_2875_);
lean_dec(v___x_2860_);
if (v_isShared_2865_ == 0)
{
lean_ctor_set(v___x_2864_, 0, v___x_2876_);
v___x_2878_ = v___x_2864_;
goto v_reusejp_2877_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v___x_2876_);
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
else
{
lean_object* v_vs_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; uint8_t v___x_2885_; 
v_vs_2882_ = lean_ctor_get(v_x_2855_, 0);
v___x_2883_ = lean_usize_to_nat(v_x_2856_);
v___x_2884_ = lean_array_get_size(v_vs_2882_);
v___x_2885_ = lean_nat_dec_lt(v___x_2883_, v___x_2884_);
if (v___x_2885_ == 0)
{
lean_dec(v___x_2883_);
lean_dec_ref(v_a_2854_);
return v_x_2855_;
}
else
{
lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2897_; 
lean_inc_ref(v_vs_2882_);
v_isSharedCheck_2897_ = !lean_is_exclusive(v_x_2855_);
if (v_isSharedCheck_2897_ == 0)
{
lean_object* v_unused_2898_; 
v_unused_2898_ = lean_ctor_get(v_x_2855_, 0);
lean_dec(v_unused_2898_);
v___x_2887_ = v_x_2855_;
v_isShared_2888_ = v_isSharedCheck_2897_;
goto v_resetjp_2886_;
}
else
{
lean_dec(v_x_2855_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2897_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v_v_2889_; lean_object* v___x_2890_; lean_object* v_xs_x27_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2895_; 
v_v_2889_ = lean_array_fget(v_vs_2882_, v___x_2883_);
v___x_2890_ = lean_box(0);
v_xs_x27_2891_ = lean_array_fset(v_vs_2882_, v___x_2883_, v___x_2890_);
v___x_2892_ = l_Lean_PersistentArray_push___redArg(v_v_2889_, v_a_2854_);
v___x_2893_ = lean_array_fset(v_xs_x27_2891_, v___x_2883_, v___x_2892_);
lean_dec(v___x_2883_);
if (v_isShared_2888_ == 0)
{
lean_ctor_set(v___x_2887_, 0, v___x_2893_);
v___x_2895_ = v___x_2887_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v___x_2893_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
return v___x_2895_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0___boxed(lean_object* v_a_2899_, lean_object* v_x_2900_, lean_object* v_x_2901_, lean_object* v_x_2902_){
_start:
{
size_t v_x_93919__boxed_2903_; size_t v_x_93920__boxed_2904_; lean_object* v_res_2905_; 
v_x_93919__boxed_2903_ = lean_unbox_usize(v_x_2901_);
lean_dec(v_x_2901_);
v_x_93920__boxed_2904_ = lean_unbox_usize(v_x_2902_);
lean_dec(v_x_2902_);
v_res_2905_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(v_a_2899_, v_x_2900_, v_x_93919__boxed_2903_, v_x_93920__boxed_2904_);
return v_res_2905_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(lean_object* v_a_2906_, lean_object* v_t_2907_, lean_object* v_i_2908_){
_start:
{
lean_object* v_root_2909_; lean_object* v_tail_2910_; lean_object* v_size_2911_; size_t v_shift_2912_; lean_object* v_tailOff_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2937_; 
v_root_2909_ = lean_ctor_get(v_t_2907_, 0);
v_tail_2910_ = lean_ctor_get(v_t_2907_, 1);
v_size_2911_ = lean_ctor_get(v_t_2907_, 2);
v_shift_2912_ = lean_ctor_get_usize(v_t_2907_, 4);
v_tailOff_2913_ = lean_ctor_get(v_t_2907_, 3);
v_isSharedCheck_2937_ = !lean_is_exclusive(v_t_2907_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2915_ = v_t_2907_;
v_isShared_2916_ = v_isSharedCheck_2937_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_tailOff_2913_);
lean_inc(v_size_2911_);
lean_inc(v_tail_2910_);
lean_inc(v_root_2909_);
lean_dec(v_t_2907_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2937_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
uint8_t v___x_2917_; 
v___x_2917_ = lean_nat_dec_le(v_tailOff_2913_, v_i_2908_);
if (v___x_2917_ == 0)
{
size_t v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2921_; 
v___x_2918_ = lean_usize_of_nat(v_i_2908_);
v___x_2919_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(v_a_2906_, v_root_2909_, v___x_2918_, v_shift_2912_);
if (v_isShared_2916_ == 0)
{
lean_ctor_set(v___x_2915_, 0, v___x_2919_);
v___x_2921_ = v___x_2915_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v___x_2919_);
lean_ctor_set(v_reuseFailAlloc_2922_, 1, v_tail_2910_);
lean_ctor_set(v_reuseFailAlloc_2922_, 2, v_size_2911_);
lean_ctor_set(v_reuseFailAlloc_2922_, 3, v_tailOff_2913_);
lean_ctor_set_usize(v_reuseFailAlloc_2922_, 4, v_shift_2912_);
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
lean_object* v___x_2923_; lean_object* v___x_2924_; uint8_t v___x_2925_; 
v___x_2923_ = lean_nat_sub(v_i_2908_, v_tailOff_2913_);
v___x_2924_ = lean_array_get_size(v_tail_2910_);
v___x_2925_ = lean_nat_dec_lt(v___x_2923_, v___x_2924_);
if (v___x_2925_ == 0)
{
lean_object* v___x_2927_; 
lean_dec(v___x_2923_);
lean_dec_ref(v_a_2906_);
if (v_isShared_2916_ == 0)
{
v___x_2927_ = v___x_2915_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_root_2909_);
lean_ctor_set(v_reuseFailAlloc_2928_, 1, v_tail_2910_);
lean_ctor_set(v_reuseFailAlloc_2928_, 2, v_size_2911_);
lean_ctor_set(v_reuseFailAlloc_2928_, 3, v_tailOff_2913_);
lean_ctor_set_usize(v_reuseFailAlloc_2928_, 4, v_shift_2912_);
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
lean_object* v_v_2929_; lean_object* v___x_2930_; lean_object* v_xs_x27_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2935_; 
v_v_2929_ = lean_array_fget(v_tail_2910_, v___x_2923_);
v___x_2930_ = lean_box(0);
v_xs_x27_2931_ = lean_array_fset(v_tail_2910_, v___x_2923_, v___x_2930_);
v___x_2932_ = l_Lean_PersistentArray_push___redArg(v_v_2929_, v_a_2906_);
v___x_2933_ = lean_array_fset(v_xs_x27_2931_, v___x_2923_, v___x_2932_);
lean_dec(v___x_2923_);
if (v_isShared_2916_ == 0)
{
lean_ctor_set(v___x_2915_, 1, v___x_2933_);
v___x_2935_ = v___x_2915_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_root_2909_);
lean_ctor_set(v_reuseFailAlloc_2936_, 1, v___x_2933_);
lean_ctor_set(v_reuseFailAlloc_2936_, 2, v_size_2911_);
lean_ctor_set(v_reuseFailAlloc_2936_, 3, v_tailOff_2913_);
lean_ctor_set_usize(v_reuseFailAlloc_2936_, 4, v_shift_2912_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0___boxed(lean_object* v_a_2938_, lean_object* v_t_2939_, lean_object* v_i_2940_){
_start:
{
lean_object* v_res_2941_; 
v_res_2941_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(v_a_2938_, v_t_2939_, v_i_2940_);
lean_dec(v_i_2940_);
return v_res_2941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0(lean_object* v_a_2942_, lean_object* v_v_2943_, lean_object* v_s_2944_){
_start:
{
lean_object* v_vars_2945_; lean_object* v_varMap_2946_; lean_object* v_vars_x27_2947_; lean_object* v_varMap_x27_2948_; lean_object* v_natToIntMap_2949_; lean_object* v_natDef_2950_; lean_object* v_dvds_2951_; lean_object* v_lowers_2952_; lean_object* v_uppers_2953_; lean_object* v_diseqs_2954_; lean_object* v_elimEqs_2955_; lean_object* v_elimStack_2956_; lean_object* v_occurs_2957_; lean_object* v_assignment_2958_; lean_object* v_nextCnstrId_2959_; uint8_t v_caseSplits_2960_; lean_object* v_conflict_x3f_2961_; lean_object* v_diseqSplits_2962_; lean_object* v_divMod_2963_; lean_object* v_toIntIds_2964_; lean_object* v_toIntInfos_2965_; lean_object* v_toIntTermMap_2966_; lean_object* v_toIntVarMap_2967_; uint8_t v_usedCommRing_2968_; lean_object* v_nonlinearOccs_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_2977_; 
v_vars_2945_ = lean_ctor_get(v_s_2944_, 0);
v_varMap_2946_ = lean_ctor_get(v_s_2944_, 1);
v_vars_x27_2947_ = lean_ctor_get(v_s_2944_, 2);
v_varMap_x27_2948_ = lean_ctor_get(v_s_2944_, 3);
v_natToIntMap_2949_ = lean_ctor_get(v_s_2944_, 4);
v_natDef_2950_ = lean_ctor_get(v_s_2944_, 5);
v_dvds_2951_ = lean_ctor_get(v_s_2944_, 6);
v_lowers_2952_ = lean_ctor_get(v_s_2944_, 7);
v_uppers_2953_ = lean_ctor_get(v_s_2944_, 8);
v_diseqs_2954_ = lean_ctor_get(v_s_2944_, 9);
v_elimEqs_2955_ = lean_ctor_get(v_s_2944_, 10);
v_elimStack_2956_ = lean_ctor_get(v_s_2944_, 11);
v_occurs_2957_ = lean_ctor_get(v_s_2944_, 12);
v_assignment_2958_ = lean_ctor_get(v_s_2944_, 13);
v_nextCnstrId_2959_ = lean_ctor_get(v_s_2944_, 14);
v_caseSplits_2960_ = lean_ctor_get_uint8(v_s_2944_, sizeof(void*)*23);
v_conflict_x3f_2961_ = lean_ctor_get(v_s_2944_, 15);
v_diseqSplits_2962_ = lean_ctor_get(v_s_2944_, 16);
v_divMod_2963_ = lean_ctor_get(v_s_2944_, 17);
v_toIntIds_2964_ = lean_ctor_get(v_s_2944_, 18);
v_toIntInfos_2965_ = lean_ctor_get(v_s_2944_, 19);
v_toIntTermMap_2966_ = lean_ctor_get(v_s_2944_, 20);
v_toIntVarMap_2967_ = lean_ctor_get(v_s_2944_, 21);
v_usedCommRing_2968_ = lean_ctor_get_uint8(v_s_2944_, sizeof(void*)*23 + 1);
v_nonlinearOccs_2969_ = lean_ctor_get(v_s_2944_, 22);
v_isSharedCheck_2977_ = !lean_is_exclusive(v_s_2944_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2971_ = v_s_2944_;
v_isShared_2972_ = v_isSharedCheck_2977_;
goto v_resetjp_2970_;
}
else
{
lean_inc(v_nonlinearOccs_2969_);
lean_inc(v_toIntVarMap_2967_);
lean_inc(v_toIntTermMap_2966_);
lean_inc(v_toIntInfos_2965_);
lean_inc(v_toIntIds_2964_);
lean_inc(v_divMod_2963_);
lean_inc(v_diseqSplits_2962_);
lean_inc(v_conflict_x3f_2961_);
lean_inc(v_nextCnstrId_2959_);
lean_inc(v_assignment_2958_);
lean_inc(v_occurs_2957_);
lean_inc(v_elimStack_2956_);
lean_inc(v_elimEqs_2955_);
lean_inc(v_diseqs_2954_);
lean_inc(v_uppers_2953_);
lean_inc(v_lowers_2952_);
lean_inc(v_dvds_2951_);
lean_inc(v_natDef_2950_);
lean_inc(v_natToIntMap_2949_);
lean_inc(v_varMap_x27_2948_);
lean_inc(v_vars_x27_2947_);
lean_inc(v_varMap_2946_);
lean_inc(v_vars_2945_);
lean_dec(v_s_2944_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_2977_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
lean_object* v___x_2973_; lean_object* v___x_2975_; 
v___x_2973_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(v_a_2942_, v_lowers_2952_, v_v_2943_);
if (v_isShared_2972_ == 0)
{
lean_ctor_set(v___x_2971_, 7, v___x_2973_);
v___x_2975_ = v___x_2971_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_vars_2945_);
lean_ctor_set(v_reuseFailAlloc_2976_, 1, v_varMap_2946_);
lean_ctor_set(v_reuseFailAlloc_2976_, 2, v_vars_x27_2947_);
lean_ctor_set(v_reuseFailAlloc_2976_, 3, v_varMap_x27_2948_);
lean_ctor_set(v_reuseFailAlloc_2976_, 4, v_natToIntMap_2949_);
lean_ctor_set(v_reuseFailAlloc_2976_, 5, v_natDef_2950_);
lean_ctor_set(v_reuseFailAlloc_2976_, 6, v_dvds_2951_);
lean_ctor_set(v_reuseFailAlloc_2976_, 7, v___x_2973_);
lean_ctor_set(v_reuseFailAlloc_2976_, 8, v_uppers_2953_);
lean_ctor_set(v_reuseFailAlloc_2976_, 9, v_diseqs_2954_);
lean_ctor_set(v_reuseFailAlloc_2976_, 10, v_elimEqs_2955_);
lean_ctor_set(v_reuseFailAlloc_2976_, 11, v_elimStack_2956_);
lean_ctor_set(v_reuseFailAlloc_2976_, 12, v_occurs_2957_);
lean_ctor_set(v_reuseFailAlloc_2976_, 13, v_assignment_2958_);
lean_ctor_set(v_reuseFailAlloc_2976_, 14, v_nextCnstrId_2959_);
lean_ctor_set(v_reuseFailAlloc_2976_, 15, v_conflict_x3f_2961_);
lean_ctor_set(v_reuseFailAlloc_2976_, 16, v_diseqSplits_2962_);
lean_ctor_set(v_reuseFailAlloc_2976_, 17, v_divMod_2963_);
lean_ctor_set(v_reuseFailAlloc_2976_, 18, v_toIntIds_2964_);
lean_ctor_set(v_reuseFailAlloc_2976_, 19, v_toIntInfos_2965_);
lean_ctor_set(v_reuseFailAlloc_2976_, 20, v_toIntTermMap_2966_);
lean_ctor_set(v_reuseFailAlloc_2976_, 21, v_toIntVarMap_2967_);
lean_ctor_set(v_reuseFailAlloc_2976_, 22, v_nonlinearOccs_2969_);
lean_ctor_set_uint8(v_reuseFailAlloc_2976_, sizeof(void*)*23, v_caseSplits_2960_);
lean_ctor_set_uint8(v_reuseFailAlloc_2976_, sizeof(void*)*23 + 1, v_usedCommRing_2968_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0___boxed(lean_object* v_a_2978_, lean_object* v_v_2979_, lean_object* v_s_2980_){
_start:
{
lean_object* v_res_2981_; 
v_res_2981_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0(v_a_2978_, v_v_2979_, v_s_2980_);
lean_dec(v_v_2979_);
return v_res_2981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1(lean_object* v_a_2982_, lean_object* v_v_2983_, lean_object* v_s_2984_){
_start:
{
lean_object* v_vars_2985_; lean_object* v_varMap_2986_; lean_object* v_vars_x27_2987_; lean_object* v_varMap_x27_2988_; lean_object* v_natToIntMap_2989_; lean_object* v_natDef_2990_; lean_object* v_dvds_2991_; lean_object* v_lowers_2992_; lean_object* v_uppers_2993_; lean_object* v_diseqs_2994_; lean_object* v_elimEqs_2995_; lean_object* v_elimStack_2996_; lean_object* v_occurs_2997_; lean_object* v_assignment_2998_; lean_object* v_nextCnstrId_2999_; uint8_t v_caseSplits_3000_; lean_object* v_conflict_x3f_3001_; lean_object* v_diseqSplits_3002_; lean_object* v_divMod_3003_; lean_object* v_toIntIds_3004_; lean_object* v_toIntInfos_3005_; lean_object* v_toIntTermMap_3006_; lean_object* v_toIntVarMap_3007_; uint8_t v_usedCommRing_3008_; lean_object* v_nonlinearOccs_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3017_; 
v_vars_2985_ = lean_ctor_get(v_s_2984_, 0);
v_varMap_2986_ = lean_ctor_get(v_s_2984_, 1);
v_vars_x27_2987_ = lean_ctor_get(v_s_2984_, 2);
v_varMap_x27_2988_ = lean_ctor_get(v_s_2984_, 3);
v_natToIntMap_2989_ = lean_ctor_get(v_s_2984_, 4);
v_natDef_2990_ = lean_ctor_get(v_s_2984_, 5);
v_dvds_2991_ = lean_ctor_get(v_s_2984_, 6);
v_lowers_2992_ = lean_ctor_get(v_s_2984_, 7);
v_uppers_2993_ = lean_ctor_get(v_s_2984_, 8);
v_diseqs_2994_ = lean_ctor_get(v_s_2984_, 9);
v_elimEqs_2995_ = lean_ctor_get(v_s_2984_, 10);
v_elimStack_2996_ = lean_ctor_get(v_s_2984_, 11);
v_occurs_2997_ = lean_ctor_get(v_s_2984_, 12);
v_assignment_2998_ = lean_ctor_get(v_s_2984_, 13);
v_nextCnstrId_2999_ = lean_ctor_get(v_s_2984_, 14);
v_caseSplits_3000_ = lean_ctor_get_uint8(v_s_2984_, sizeof(void*)*23);
v_conflict_x3f_3001_ = lean_ctor_get(v_s_2984_, 15);
v_diseqSplits_3002_ = lean_ctor_get(v_s_2984_, 16);
v_divMod_3003_ = lean_ctor_get(v_s_2984_, 17);
v_toIntIds_3004_ = lean_ctor_get(v_s_2984_, 18);
v_toIntInfos_3005_ = lean_ctor_get(v_s_2984_, 19);
v_toIntTermMap_3006_ = lean_ctor_get(v_s_2984_, 20);
v_toIntVarMap_3007_ = lean_ctor_get(v_s_2984_, 21);
v_usedCommRing_3008_ = lean_ctor_get_uint8(v_s_2984_, sizeof(void*)*23 + 1);
v_nonlinearOccs_3009_ = lean_ctor_get(v_s_2984_, 22);
v_isSharedCheck_3017_ = !lean_is_exclusive(v_s_2984_);
if (v_isSharedCheck_3017_ == 0)
{
v___x_3011_ = v_s_2984_;
v_isShared_3012_ = v_isSharedCheck_3017_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_nonlinearOccs_3009_);
lean_inc(v_toIntVarMap_3007_);
lean_inc(v_toIntTermMap_3006_);
lean_inc(v_toIntInfos_3005_);
lean_inc(v_toIntIds_3004_);
lean_inc(v_divMod_3003_);
lean_inc(v_diseqSplits_3002_);
lean_inc(v_conflict_x3f_3001_);
lean_inc(v_nextCnstrId_2999_);
lean_inc(v_assignment_2998_);
lean_inc(v_occurs_2997_);
lean_inc(v_elimStack_2996_);
lean_inc(v_elimEqs_2995_);
lean_inc(v_diseqs_2994_);
lean_inc(v_uppers_2993_);
lean_inc(v_lowers_2992_);
lean_inc(v_dvds_2991_);
lean_inc(v_natDef_2990_);
lean_inc(v_natToIntMap_2989_);
lean_inc(v_varMap_x27_2988_);
lean_inc(v_vars_x27_2987_);
lean_inc(v_varMap_2986_);
lean_inc(v_vars_2985_);
lean_dec(v_s_2984_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3017_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v___x_3013_; lean_object* v___x_3015_; 
v___x_3013_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(v_a_2982_, v_uppers_2993_, v_v_2983_);
if (v_isShared_3012_ == 0)
{
lean_ctor_set(v___x_3011_, 8, v___x_3013_);
v___x_3015_ = v___x_3011_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3016_; 
v_reuseFailAlloc_3016_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_3016_, 0, v_vars_2985_);
lean_ctor_set(v_reuseFailAlloc_3016_, 1, v_varMap_2986_);
lean_ctor_set(v_reuseFailAlloc_3016_, 2, v_vars_x27_2987_);
lean_ctor_set(v_reuseFailAlloc_3016_, 3, v_varMap_x27_2988_);
lean_ctor_set(v_reuseFailAlloc_3016_, 4, v_natToIntMap_2989_);
lean_ctor_set(v_reuseFailAlloc_3016_, 5, v_natDef_2990_);
lean_ctor_set(v_reuseFailAlloc_3016_, 6, v_dvds_2991_);
lean_ctor_set(v_reuseFailAlloc_3016_, 7, v_lowers_2992_);
lean_ctor_set(v_reuseFailAlloc_3016_, 8, v___x_3013_);
lean_ctor_set(v_reuseFailAlloc_3016_, 9, v_diseqs_2994_);
lean_ctor_set(v_reuseFailAlloc_3016_, 10, v_elimEqs_2995_);
lean_ctor_set(v_reuseFailAlloc_3016_, 11, v_elimStack_2996_);
lean_ctor_set(v_reuseFailAlloc_3016_, 12, v_occurs_2997_);
lean_ctor_set(v_reuseFailAlloc_3016_, 13, v_assignment_2998_);
lean_ctor_set(v_reuseFailAlloc_3016_, 14, v_nextCnstrId_2999_);
lean_ctor_set(v_reuseFailAlloc_3016_, 15, v_conflict_x3f_3001_);
lean_ctor_set(v_reuseFailAlloc_3016_, 16, v_diseqSplits_3002_);
lean_ctor_set(v_reuseFailAlloc_3016_, 17, v_divMod_3003_);
lean_ctor_set(v_reuseFailAlloc_3016_, 18, v_toIntIds_3004_);
lean_ctor_set(v_reuseFailAlloc_3016_, 19, v_toIntInfos_3005_);
lean_ctor_set(v_reuseFailAlloc_3016_, 20, v_toIntTermMap_3006_);
lean_ctor_set(v_reuseFailAlloc_3016_, 21, v_toIntVarMap_3007_);
lean_ctor_set(v_reuseFailAlloc_3016_, 22, v_nonlinearOccs_3009_);
lean_ctor_set_uint8(v_reuseFailAlloc_3016_, sizeof(void*)*23, v_caseSplits_3000_);
lean_ctor_set_uint8(v_reuseFailAlloc_3016_, sizeof(void*)*23 + 1, v_usedCommRing_3008_);
v___x_3015_ = v_reuseFailAlloc_3016_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
return v___x_3015_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1___boxed(lean_object* v_a_3018_, lean_object* v_v_3019_, lean_object* v_s_3020_){
_start:
{
lean_object* v_res_3021_; 
v_res_3021_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1(v_a_3018_, v_v_3019_, v_s_3020_);
lean_dec(v_v_3019_);
return v_res_3021_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3(void){
_start:
{
lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; 
v___x_3029_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2));
v___x_3030_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_3031_ = l_Lean_Name_append(v___x_3030_, v___x_3029_);
return v___x_3031_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6(void){
_start:
{
lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; 
v___x_3038_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5));
v___x_3039_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_3040_ = l_Lean_Name_append(v___x_3039_, v___x_3038_);
return v___x_3040_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9(void){
_start:
{
lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; 
v___x_3047_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__8));
v___x_3048_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_3049_ = l_Lean_Name_append(v___x_3048_, v___x_3047_);
return v___x_3049_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11(void){
_start:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3054_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__10));
v___x_3055_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_3056_ = l_Lean_Name_append(v___x_3055_, v___x_3054_);
return v___x_3056_;
}
}
LEAN_EXPORT lean_object* lean_grind_cutsat_assert_le(lean_object* v_c_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_){
_start:
{
lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3108_; lean_object* v___y_3109_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___x_3141_; 
v___x_3141_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_3058_, v_a_3066_);
if (lean_obj_tag(v___x_3141_) == 0)
{
lean_object* v_a_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3278_; 
v_a_3142_ = lean_ctor_get(v___x_3141_, 0);
v_isSharedCheck_3278_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3278_ == 0)
{
v___x_3144_ = v___x_3141_;
v_isShared_3145_ = v_isSharedCheck_3278_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_a_3142_);
lean_dec(v___x_3141_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3278_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
uint8_t v___x_3146_; 
v___x_3146_ = lean_unbox(v_a_3142_);
lean_dec(v_a_3142_);
if (v___x_3146_ == 0)
{
lean_object* v_options_3147_; lean_object* v_inheritedTraceOptions_3148_; uint8_t v_hasTrace_3149_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; 
lean_del_object(v___x_3144_);
v_options_3147_ = lean_ctor_get(v_a_3066_, 2);
v_inheritedTraceOptions_3148_ = lean_ctor_get(v_a_3066_, 13);
v_hasTrace_3149_ = lean_ctor_get_uint8(v_options_3147_, sizeof(void*)*1);
if (v_hasTrace_3149_ == 0)
{
v___y_3151_ = v_a_3058_;
v___y_3152_ = v_a_3059_;
v___y_3153_ = v_a_3060_;
v___y_3154_ = v_a_3061_;
v___y_3155_ = v_a_3062_;
v___y_3156_ = v_a_3063_;
v___y_3157_ = v_a_3064_;
v___y_3158_ = v_a_3065_;
v___y_3159_ = v_a_3066_;
v___y_3160_ = v_a_3067_;
goto v___jp_3150_;
}
else
{
lean_object* v___x_3260_; lean_object* v___x_3261_; uint8_t v___x_3262_; 
v___x_3260_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__10));
v___x_3261_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11);
v___x_3262_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3148_, v_options_3147_, v___x_3261_);
if (v___x_3262_ == 0)
{
v___y_3151_ = v_a_3058_;
v___y_3152_ = v_a_3059_;
v___y_3153_ = v_a_3060_;
v___y_3154_ = v_a_3061_;
v___y_3155_ = v_a_3062_;
v___y_3156_ = v_a_3063_;
v___y_3157_ = v_a_3064_;
v___y_3158_ = v_a_3065_;
v___y_3159_ = v_a_3066_;
v___y_3160_ = v_a_3067_;
goto v___jp_3150_;
}
else
{
lean_object* v___x_3263_; 
lean_inc_ref(v_c_3057_);
v___x_3263_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_3057_, v_a_3058_, v_a_3066_);
if (lean_obj_tag(v___x_3263_) == 0)
{
lean_object* v_a_3264_; lean_object* v___x_3265_; 
v_a_3264_ = lean_ctor_get(v___x_3263_, 0);
lean_inc(v_a_3264_);
lean_dec_ref(v___x_3263_);
v___x_3265_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3260_, v_a_3264_, v_a_3064_, v_a_3065_, v_a_3066_, v_a_3067_);
if (lean_obj_tag(v___x_3265_) == 0)
{
lean_dec_ref(v___x_3265_);
v___y_3151_ = v_a_3058_;
v___y_3152_ = v_a_3059_;
v___y_3153_ = v_a_3060_;
v___y_3154_ = v_a_3061_;
v___y_3155_ = v_a_3062_;
v___y_3156_ = v_a_3063_;
v___y_3157_ = v_a_3064_;
v___y_3158_ = v_a_3065_;
v___y_3159_ = v_a_3066_;
v___y_3160_ = v_a_3067_;
goto v___jp_3150_;
}
else
{
lean_dec(v_a_3067_);
lean_dec_ref(v_a_3066_);
lean_dec(v_a_3065_);
lean_dec_ref(v_a_3064_);
lean_dec(v_a_3063_);
lean_dec_ref(v_a_3062_);
lean_dec(v_a_3061_);
lean_dec_ref(v_a_3060_);
lean_dec(v_a_3059_);
lean_dec(v_a_3058_);
lean_dec_ref(v_c_3057_);
return v___x_3265_;
}
}
else
{
lean_object* v_a_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3273_; 
lean_dec(v_a_3067_);
lean_dec_ref(v_a_3066_);
lean_dec(v_a_3065_);
lean_dec_ref(v_a_3064_);
lean_dec(v_a_3063_);
lean_dec_ref(v_a_3062_);
lean_dec(v_a_3061_);
lean_dec_ref(v_a_3060_);
lean_dec(v_a_3059_);
lean_dec(v_a_3058_);
lean_dec_ref(v_c_3057_);
v_a_3266_ = lean_ctor_get(v___x_3263_, 0);
v_isSharedCheck_3273_ = !lean_is_exclusive(v___x_3263_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3268_ = v___x_3263_;
v_isShared_3269_ = v_isSharedCheck_3273_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_a_3266_);
lean_dec(v___x_3263_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3273_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
lean_object* v___x_3271_; 
if (v_isShared_3269_ == 0)
{
v___x_3271_ = v___x_3268_;
goto v_reusejp_3270_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_a_3266_);
v___x_3271_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3270_;
}
v_reusejp_3270_:
{
return v___x_3271_;
}
}
}
}
}
v___jp_3150_:
{
lean_object* v___x_3161_; lean_object* v___x_3162_; 
v___x_3161_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_norm(v_c_3057_);
lean_inc_ref(v___y_3159_);
v___x_3162_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts(v___x_3161_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
if (lean_obj_tag(v___x_3162_) == 0)
{
lean_object* v_a_3163_; lean_object* v_p_3164_; uint8_t v___x_3165_; 
v_a_3163_ = lean_ctor_get(v___x_3162_, 0);
lean_inc(v_a_3163_);
lean_dec_ref(v___x_3162_);
v_p_3164_ = lean_ctor_get(v_a_3163_, 0);
v___x_3165_ = l_Int_Linear_Poly_isUnsatLe(v_p_3164_);
if (v___x_3165_ == 0)
{
uint8_t v___x_3166_; 
v___x_3166_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(v_a_3163_);
if (v___x_3166_ == 0)
{
if (lean_obj_tag(v_p_3164_) == 1)
{
lean_object* v_k_3167_; lean_object* v_v_3168_; lean_object* v___x_3169_; 
v_k_3167_ = lean_ctor_get(v_p_3164_, 0);
lean_inc(v_k_3167_);
v_v_3168_ = lean_ctor_get(v_p_3164_, 1);
lean_inc(v_v_3168_);
lean_inc(v_a_3163_);
v___x_3169_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq(v_a_3163_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
if (lean_obj_tag(v___x_3169_) == 0)
{
lean_object* v_a_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3208_; 
v_a_3170_ = lean_ctor_get(v___x_3169_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v___x_3169_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3172_ = v___x_3169_;
v_isShared_3173_ = v_isSharedCheck_3208_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_a_3170_);
lean_dec(v___x_3169_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3208_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
uint8_t v___x_3174_; 
v___x_3174_ = lean_unbox(v_a_3170_);
lean_dec(v_a_3170_);
if (v___x_3174_ == 0)
{
lean_object* v___x_3175_; 
lean_del_object(v___x_3172_);
v___x_3175_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(v_a_3163_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3152_);
if (lean_obj_tag(v___x_3175_) == 0)
{
lean_object* v_options_3176_; lean_object* v_a_3177_; lean_object* v_inheritedTraceOptions_3178_; uint8_t v_hasTrace_3179_; lean_object* v___f_3180_; lean_object* v___f_3181_; 
v_options_3176_ = lean_ctor_get(v___y_3159_, 2);
v_a_3177_ = lean_ctor_get(v___x_3175_, 0);
lean_inc_n(v_a_3177_, 3);
lean_dec_ref(v___x_3175_);
v_inheritedTraceOptions_3178_ = lean_ctor_get(v___y_3159_, 13);
v_hasTrace_3179_ = lean_ctor_get_uint8(v_options_3176_, sizeof(void*)*1);
lean_inc_n(v_v_3168_, 2);
v___f_3180_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3180_, 0, v_a_3177_);
lean_closure_set(v___f_3180_, 1, v_v_3168_);
v___f_3181_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3181_, 0, v_a_3177_);
lean_closure_set(v___f_3181_, 1, v_v_3168_);
if (v_hasTrace_3179_ == 0)
{
v___y_3100_ = v_v_3168_;
v___y_3101_ = v_k_3167_;
v___y_3102_ = v_a_3177_;
v___y_3103_ = v___f_3180_;
v___y_3104_ = v___f_3181_;
v___y_3105_ = v___y_3151_;
v___y_3106_ = v___y_3157_;
v___y_3107_ = v___y_3158_;
v___y_3108_ = v___y_3159_;
v___y_3109_ = v___y_3160_;
goto v___jp_3099_;
}
else
{
lean_object* v___x_3182_; lean_object* v___x_3183_; uint8_t v___x_3184_; 
v___x_3182_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2));
v___x_3183_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3);
v___x_3184_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3178_, v_options_3176_, v___x_3183_);
if (v___x_3184_ == 0)
{
v___y_3100_ = v_v_3168_;
v___y_3101_ = v_k_3167_;
v___y_3102_ = v_a_3177_;
v___y_3103_ = v___f_3180_;
v___y_3104_ = v___f_3181_;
v___y_3105_ = v___y_3151_;
v___y_3106_ = v___y_3157_;
v___y_3107_ = v___y_3158_;
v___y_3108_ = v___y_3159_;
v___y_3109_ = v___y_3160_;
goto v___jp_3099_;
}
else
{
lean_object* v___x_3185_; 
lean_inc(v_a_3177_);
v___x_3185_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_a_3177_, v___y_3151_, v___y_3159_);
if (lean_obj_tag(v___x_3185_) == 0)
{
lean_object* v_a_3186_; lean_object* v___x_3187_; 
v_a_3186_ = lean_ctor_get(v___x_3185_, 0);
lean_inc(v_a_3186_);
lean_dec_ref(v___x_3185_);
v___x_3187_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3182_, v_a_3186_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
if (lean_obj_tag(v___x_3187_) == 0)
{
lean_dec_ref(v___x_3187_);
v___y_3100_ = v_v_3168_;
v___y_3101_ = v_k_3167_;
v___y_3102_ = v_a_3177_;
v___y_3103_ = v___f_3180_;
v___y_3104_ = v___f_3181_;
v___y_3105_ = v___y_3151_;
v___y_3106_ = v___y_3157_;
v___y_3107_ = v___y_3158_;
v___y_3108_ = v___y_3159_;
v___y_3109_ = v___y_3160_;
goto v___jp_3099_;
}
else
{
lean_dec_ref(v___f_3181_);
lean_dec_ref(v___f_3180_);
lean_dec(v_a_3177_);
lean_dec(v_v_3168_);
lean_dec(v_k_3167_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3151_);
return v___x_3187_;
}
}
else
{
lean_object* v_a_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3195_; 
lean_dec_ref(v___f_3181_);
lean_dec_ref(v___f_3180_);
lean_dec(v_a_3177_);
lean_dec(v_v_3168_);
lean_dec(v_k_3167_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3151_);
v_a_3188_ = lean_ctor_get(v___x_3185_, 0);
v_isSharedCheck_3195_ = !lean_is_exclusive(v___x_3185_);
if (v_isSharedCheck_3195_ == 0)
{
v___x_3190_ = v___x_3185_;
v_isShared_3191_ = v_isSharedCheck_3195_;
goto v_resetjp_3189_;
}
else
{
lean_inc(v_a_3188_);
lean_dec(v___x_3185_);
v___x_3190_ = lean_box(0);
v_isShared_3191_ = v_isSharedCheck_3195_;
goto v_resetjp_3189_;
}
v_resetjp_3189_:
{
lean_object* v___x_3193_; 
if (v_isShared_3191_ == 0)
{
v___x_3193_ = v___x_3190_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v_a_3188_);
v___x_3193_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
return v___x_3193_;
}
}
}
}
}
}
else
{
lean_object* v_a_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3203_; 
lean_dec(v_v_3168_);
lean_dec(v_k_3167_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3151_);
v_a_3196_ = lean_ctor_get(v___x_3175_, 0);
v_isSharedCheck_3203_ = !lean_is_exclusive(v___x_3175_);
if (v_isSharedCheck_3203_ == 0)
{
v___x_3198_ = v___x_3175_;
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
else
{
lean_inc(v_a_3196_);
lean_dec(v___x_3175_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3203_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v___x_3201_; 
if (v_isShared_3199_ == 0)
{
v___x_3201_ = v___x_3198_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v_a_3196_);
v___x_3201_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
return v___x_3201_;
}
}
}
}
else
{
lean_object* v___x_3204_; lean_object* v___x_3206_; 
lean_dec(v_v_3168_);
lean_dec(v_k_3167_);
lean_dec(v_a_3163_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3152_);
lean_dec(v___y_3151_);
v___x_3204_ = lean_box(0);
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 0, v___x_3204_);
v___x_3206_ = v___x_3172_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v___x_3204_);
v___x_3206_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
return v___x_3206_;
}
}
}
}
else
{
lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3216_; 
lean_dec(v_v_3168_);
lean_dec(v_k_3167_);
lean_dec(v_a_3163_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3152_);
lean_dec(v___y_3151_);
v_a_3209_ = lean_ctor_get(v___x_3169_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_3169_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3211_ = v___x_3169_;
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___x_3169_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3214_; 
if (v_isShared_3212_ == 0)
{
v___x_3214_ = v___x_3211_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_a_3209_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
return v___x_3214_;
}
}
}
}
else
{
lean_object* v___x_3217_; 
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3152_);
v___x_3217_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_a_3163_, v___y_3151_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3151_);
return v___x_3217_;
}
}
else
{
lean_object* v_options_3218_; uint8_t v_hasTrace_3219_; 
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3152_);
v_options_3218_ = lean_ctor_get(v___y_3159_, 2);
v_hasTrace_3219_ = lean_ctor_get_uint8(v_options_3218_, sizeof(void*)*1);
if (v_hasTrace_3219_ == 0)
{
lean_dec(v_a_3163_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3151_);
goto v___jp_3069_;
}
else
{
lean_object* v_inheritedTraceOptions_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; uint8_t v___x_3223_; 
v_inheritedTraceOptions_3220_ = lean_ctor_get(v___y_3159_, 13);
v___x_3221_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5));
v___x_3222_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6);
v___x_3223_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3220_, v_options_3218_, v___x_3222_);
if (v___x_3223_ == 0)
{
lean_dec(v_a_3163_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3151_);
goto v___jp_3069_;
}
else
{
lean_object* v___x_3224_; 
v___x_3224_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_a_3163_, v___y_3151_, v___y_3159_);
lean_dec(v___y_3151_);
if (lean_obj_tag(v___x_3224_) == 0)
{
lean_object* v_a_3225_; lean_object* v___x_3226_; 
v_a_3225_ = lean_ctor_get(v___x_3224_, 0);
lean_inc(v_a_3225_);
lean_dec_ref(v___x_3224_);
v___x_3226_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3221_, v_a_3225_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
if (lean_obj_tag(v___x_3226_) == 0)
{
lean_dec_ref(v___x_3226_);
goto v___jp_3069_;
}
else
{
return v___x_3226_;
}
}
else
{
lean_object* v_a_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3234_; 
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
v_a_3227_ = lean_ctor_get(v___x_3224_, 0);
v_isSharedCheck_3234_ = !lean_is_exclusive(v___x_3224_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3229_ = v___x_3224_;
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_a_3227_);
lean_dec(v___x_3224_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v___x_3232_; 
if (v_isShared_3230_ == 0)
{
v___x_3232_ = v___x_3229_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v_a_3227_);
v___x_3232_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
return v___x_3232_;
}
}
}
}
}
}
}
else
{
lean_object* v_options_3235_; uint8_t v_hasTrace_3236_; 
v_options_3235_ = lean_ctor_get(v___y_3159_, 2);
v_hasTrace_3236_ = lean_ctor_get_uint8(v_options_3235_, sizeof(void*)*1);
if (v_hasTrace_3236_ == 0)
{
v___y_3119_ = v_a_3163_;
v___y_3120_ = v___y_3151_;
v___y_3121_ = v___y_3152_;
v___y_3122_ = v___y_3153_;
v___y_3123_ = v___y_3154_;
v___y_3124_ = v___y_3155_;
v___y_3125_ = v___y_3156_;
v___y_3126_ = v___y_3157_;
v___y_3127_ = v___y_3158_;
v___y_3128_ = v___y_3159_;
v___y_3129_ = v___y_3160_;
goto v___jp_3118_;
}
else
{
lean_object* v_inheritedTraceOptions_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; uint8_t v___x_3240_; 
v_inheritedTraceOptions_3237_ = lean_ctor_get(v___y_3159_, 13);
v___x_3238_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__8));
v___x_3239_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9);
v___x_3240_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3237_, v_options_3235_, v___x_3239_);
if (v___x_3240_ == 0)
{
v___y_3119_ = v_a_3163_;
v___y_3120_ = v___y_3151_;
v___y_3121_ = v___y_3152_;
v___y_3122_ = v___y_3153_;
v___y_3123_ = v___y_3154_;
v___y_3124_ = v___y_3155_;
v___y_3125_ = v___y_3156_;
v___y_3126_ = v___y_3157_;
v___y_3127_ = v___y_3158_;
v___y_3128_ = v___y_3159_;
v___y_3129_ = v___y_3160_;
goto v___jp_3118_;
}
else
{
lean_object* v___x_3241_; 
lean_inc(v_a_3163_);
v___x_3241_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_a_3163_, v___y_3151_, v___y_3159_);
if (lean_obj_tag(v___x_3241_) == 0)
{
lean_object* v_a_3242_; lean_object* v___x_3243_; 
v_a_3242_ = lean_ctor_get(v___x_3241_, 0);
lean_inc(v_a_3242_);
lean_dec_ref(v___x_3241_);
v___x_3243_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3238_, v_a_3242_, v___y_3157_, v___y_3158_, v___y_3159_, v___y_3160_);
if (lean_obj_tag(v___x_3243_) == 0)
{
lean_dec_ref(v___x_3243_);
v___y_3119_ = v_a_3163_;
v___y_3120_ = v___y_3151_;
v___y_3121_ = v___y_3152_;
v___y_3122_ = v___y_3153_;
v___y_3123_ = v___y_3154_;
v___y_3124_ = v___y_3155_;
v___y_3125_ = v___y_3156_;
v___y_3126_ = v___y_3157_;
v___y_3127_ = v___y_3158_;
v___y_3128_ = v___y_3159_;
v___y_3129_ = v___y_3160_;
goto v___jp_3118_;
}
else
{
lean_dec(v_a_3163_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3152_);
lean_dec(v___y_3151_);
return v___x_3243_;
}
}
else
{
lean_object* v_a_3244_; lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3251_; 
lean_dec(v_a_3163_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3152_);
lean_dec(v___y_3151_);
v_a_3244_ = lean_ctor_get(v___x_3241_, 0);
v_isSharedCheck_3251_ = !lean_is_exclusive(v___x_3241_);
if (v_isSharedCheck_3251_ == 0)
{
v___x_3246_ = v___x_3241_;
v_isShared_3247_ = v_isSharedCheck_3251_;
goto v_resetjp_3245_;
}
else
{
lean_inc(v_a_3244_);
lean_dec(v___x_3241_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3251_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v___x_3249_; 
if (v_isShared_3247_ == 0)
{
v___x_3249_ = v___x_3246_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v_a_3244_);
v___x_3249_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
return v___x_3249_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3259_; 
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
lean_dec(v___y_3158_);
lean_dec_ref(v___y_3157_);
lean_dec(v___y_3156_);
lean_dec_ref(v___y_3155_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3152_);
lean_dec(v___y_3151_);
v_a_3252_ = lean_ctor_get(v___x_3162_, 0);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___x_3162_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3254_ = v___x_3162_;
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_a_3252_);
lean_dec(v___x_3162_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___x_3257_; 
if (v_isShared_3255_ == 0)
{
v___x_3257_ = v___x_3254_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v_a_3252_);
v___x_3257_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
return v___x_3257_;
}
}
}
}
}
else
{
lean_object* v___x_3274_; lean_object* v___x_3276_; 
lean_dec(v_a_3067_);
lean_dec_ref(v_a_3066_);
lean_dec(v_a_3065_);
lean_dec_ref(v_a_3064_);
lean_dec(v_a_3063_);
lean_dec_ref(v_a_3062_);
lean_dec(v_a_3061_);
lean_dec_ref(v_a_3060_);
lean_dec(v_a_3059_);
lean_dec(v_a_3058_);
lean_dec_ref(v_c_3057_);
v___x_3274_ = lean_box(0);
if (v_isShared_3145_ == 0)
{
lean_ctor_set(v___x_3144_, 0, v___x_3274_);
v___x_3276_ = v___x_3144_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v___x_3274_);
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
else
{
lean_object* v_a_3279_; lean_object* v___x_3281_; uint8_t v_isShared_3282_; uint8_t v_isSharedCheck_3286_; 
lean_dec(v_a_3067_);
lean_dec_ref(v_a_3066_);
lean_dec(v_a_3065_);
lean_dec_ref(v_a_3064_);
lean_dec(v_a_3063_);
lean_dec_ref(v_a_3062_);
lean_dec(v_a_3061_);
lean_dec_ref(v_a_3060_);
lean_dec(v_a_3059_);
lean_dec(v_a_3058_);
lean_dec_ref(v_c_3057_);
v_a_3279_ = lean_ctor_get(v___x_3141_, 0);
v_isSharedCheck_3286_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3286_ == 0)
{
v___x_3281_ = v___x_3141_;
v_isShared_3282_ = v_isSharedCheck_3286_;
goto v_resetjp_3280_;
}
else
{
lean_inc(v_a_3279_);
lean_dec(v___x_3141_);
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
v___jp_3069_:
{
lean_object* v___x_3070_; lean_object* v___x_3071_; 
v___x_3070_ = lean_box(0);
v___x_3071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3071_, 0, v___x_3070_);
return v___x_3071_;
}
v___jp_3072_:
{
lean_object* v___x_3077_; 
v___x_3077_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(v___y_3074_, v___y_3075_, v___y_3076_);
lean_dec_ref(v___y_3076_);
if (lean_obj_tag(v___x_3077_) == 0)
{
lean_object* v_a_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3090_; 
v_a_3078_ = lean_ctor_get(v___x_3077_, 0);
v_isSharedCheck_3090_ = !lean_is_exclusive(v___x_3077_);
if (v_isSharedCheck_3090_ == 0)
{
v___x_3080_ = v___x_3077_;
v_isShared_3081_ = v_isSharedCheck_3090_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_a_3078_);
lean_dec(v___x_3077_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3090_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
uint8_t v___x_3082_; uint8_t v___x_3083_; uint8_t v___x_3084_; 
v___x_3082_ = 0;
v___x_3083_ = lean_unbox(v_a_3078_);
lean_dec(v_a_3078_);
v___x_3084_ = l_Lean_instBEqLBool_beq(v___x_3083_, v___x_3082_);
if (v___x_3084_ == 0)
{
lean_object* v___x_3085_; lean_object* v___x_3087_; 
lean_dec(v___y_3075_);
lean_dec(v___y_3073_);
v___x_3085_ = lean_box(0);
if (v_isShared_3081_ == 0)
{
lean_ctor_set(v___x_3080_, 0, v___x_3085_);
v___x_3087_ = v___x_3080_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v___x_3085_);
v___x_3087_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
return v___x_3087_;
}
}
else
{
lean_object* v___x_3089_; 
lean_del_object(v___x_3080_);
v___x_3089_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v___y_3073_, v___y_3075_);
lean_dec(v___y_3075_);
return v___x_3089_;
}
}
}
else
{
lean_object* v_a_3091_; lean_object* v___x_3093_; uint8_t v_isShared_3094_; uint8_t v_isSharedCheck_3098_; 
lean_dec(v___y_3075_);
lean_dec(v___y_3073_);
v_a_3091_ = lean_ctor_get(v___x_3077_, 0);
v_isSharedCheck_3098_ = !lean_is_exclusive(v___x_3077_);
if (v_isSharedCheck_3098_ == 0)
{
v___x_3093_ = v___x_3077_;
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
else
{
lean_inc(v_a_3091_);
lean_dec(v___x_3077_);
v___x_3093_ = lean_box(0);
v_isShared_3094_ = v_isSharedCheck_3098_;
goto v_resetjp_3092_;
}
v_resetjp_3092_:
{
lean_object* v___x_3096_; 
if (v_isShared_3094_ == 0)
{
v___x_3096_ = v___x_3093_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3097_; 
v_reuseFailAlloc_3097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3097_, 0, v_a_3091_);
v___x_3096_ = v_reuseFailAlloc_3097_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
return v___x_3096_;
}
}
}
}
v___jp_3099_:
{
lean_object* v_p_3110_; lean_object* v___x_3111_; 
v_p_3110_ = lean_ctor_get(v___y_3102_, 0);
lean_inc_ref(v_p_3110_);
v___x_3111_ = l_Int_Linear_Poly_updateOccs___redArg(v_p_3110_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_);
lean_dec(v___y_3109_);
lean_dec(v___y_3107_);
lean_dec_ref(v___y_3106_);
if (lean_obj_tag(v___x_3111_) == 0)
{
lean_object* v___x_3112_; uint8_t v___x_3113_; 
lean_dec_ref(v___x_3111_);
v___x_3112_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9);
v___x_3113_ = lean_int_dec_lt(v___y_3101_, v___x_3112_);
lean_dec(v___y_3101_);
if (v___x_3113_ == 0)
{
lean_object* v___x_3114_; lean_object* v___x_3115_; 
lean_dec_ref(v___y_3103_);
v___x_3114_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_3115_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3114_, v___y_3104_, v___y_3105_);
if (lean_obj_tag(v___x_3115_) == 0)
{
lean_dec_ref(v___x_3115_);
v___y_3073_ = v___y_3100_;
v___y_3074_ = v___y_3102_;
v___y_3075_ = v___y_3105_;
v___y_3076_ = v___y_3108_;
goto v___jp_3072_;
}
else
{
lean_dec_ref(v___y_3108_);
lean_dec(v___y_3105_);
lean_dec_ref(v___y_3102_);
lean_dec(v___y_3100_);
return v___x_3115_;
}
}
else
{
lean_object* v___x_3116_; lean_object* v___x_3117_; 
lean_dec_ref(v___y_3104_);
v___x_3116_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_3117_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3116_, v___y_3103_, v___y_3105_);
if (lean_obj_tag(v___x_3117_) == 0)
{
lean_dec_ref(v___x_3117_);
v___y_3073_ = v___y_3100_;
v___y_3074_ = v___y_3102_;
v___y_3075_ = v___y_3105_;
v___y_3076_ = v___y_3108_;
goto v___jp_3072_;
}
else
{
lean_dec_ref(v___y_3108_);
lean_dec(v___y_3105_);
lean_dec_ref(v___y_3102_);
lean_dec(v___y_3100_);
return v___x_3117_;
}
}
}
else
{
lean_dec_ref(v___y_3108_);
lean_dec(v___y_3105_);
lean_dec_ref(v___y_3104_);
lean_dec_ref(v___y_3103_);
lean_dec_ref(v___y_3102_);
lean_dec(v___y_3101_);
lean_dec(v___y_3100_);
return v___x_3111_;
}
}
v___jp_3118_:
{
lean_object* v___x_3130_; lean_object* v___x_3131_; 
v___x_3130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3130_, 0, v___y_3119_);
v___x_3131_ = l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(v___x_3130_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_);
lean_dec(v___y_3129_);
lean_dec_ref(v___y_3128_);
lean_dec(v___y_3127_);
lean_dec_ref(v___y_3126_);
lean_dec(v___y_3125_);
lean_dec_ref(v___y_3124_);
lean_dec(v___y_3123_);
lean_dec_ref(v___y_3122_);
lean_dec(v___y_3121_);
lean_dec(v___y_3120_);
if (lean_obj_tag(v___x_3131_) == 0)
{
lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3139_; 
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3131_);
if (v_isSharedCheck_3139_ == 0)
{
lean_object* v_unused_3140_; 
v_unused_3140_ = lean_ctor_get(v___x_3131_, 0);
lean_dec(v_unused_3140_);
v___x_3133_ = v___x_3131_;
v_isShared_3134_ = v_isSharedCheck_3139_;
goto v_resetjp_3132_;
}
else
{
lean_dec(v___x_3131_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3139_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3135_; lean_object* v___x_3137_; 
v___x_3135_ = lean_box(0);
if (v_isShared_3134_ == 0)
{
lean_ctor_set(v___x_3133_, 0, v___x_3135_);
v___x_3137_ = v___x_3133_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v___x_3135_);
v___x_3137_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
return v___x_3137_;
}
}
}
else
{
return v___x_3131_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___boxed(lean_object* v_c_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_){
_start:
{
lean_object* v_res_3299_; 
v_res_3299_ = lean_grind_cutsat_assert_le(v_c_3287_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_, v_a_3295_, v_a_3296_, v_a_3297_);
return v_res_3299_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1(void){
_start:
{
lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3301_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__0));
v___x_3302_ = l_Lean_stringToMessageData(v___x_3301_);
return v___x_3302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(lean_object* v_e_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_){
_start:
{
lean_object* v___x_3311_; 
v___x_3311_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_3304_);
if (lean_obj_tag(v___x_3311_) == 0)
{
lean_object* v_a_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3325_; 
v_a_3312_ = lean_ctor_get(v___x_3311_, 0);
v_isSharedCheck_3325_ = !lean_is_exclusive(v___x_3311_);
if (v_isSharedCheck_3325_ == 0)
{
v___x_3314_ = v___x_3311_;
v_isShared_3315_ = v_isSharedCheck_3325_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_a_3312_);
lean_dec(v___x_3311_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3325_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
uint8_t v___x_3316_; 
v___x_3316_ = lean_unbox(v_a_3312_);
lean_dec(v_a_3312_);
if (v___x_3316_ == 0)
{
lean_object* v___x_3317_; lean_object* v___x_3319_; 
lean_dec_ref(v_e_3303_);
v___x_3317_ = lean_box(0);
if (v_isShared_3315_ == 0)
{
lean_ctor_set(v___x_3314_, 0, v___x_3317_);
v___x_3319_ = v___x_3314_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v___x_3317_);
v___x_3319_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
return v___x_3319_;
}
}
else
{
lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; 
lean_del_object(v___x_3314_);
v___x_3321_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1);
v___x_3322_ = l_Lean_indentExpr(v_e_3303_);
v___x_3323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3323_, 0, v___x_3321_);
lean_ctor_set(v___x_3323_, 1, v___x_3322_);
v___x_3324_ = l_Lean_Meta_Sym_reportIssue(v___x_3323_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_);
return v___x_3324_;
}
}
}
else
{
lean_object* v_a_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3333_; 
lean_dec_ref(v_e_3303_);
v_a_3326_ = lean_ctor_get(v___x_3311_, 0);
v_isSharedCheck_3333_ = !lean_is_exclusive(v___x_3311_);
if (v_isSharedCheck_3333_ == 0)
{
v___x_3328_ = v___x_3311_;
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_a_3326_);
lean_dec(v___x_3311_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v___x_3331_; 
if (v_isShared_3329_ == 0)
{
v___x_3331_ = v___x_3328_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3332_; 
v_reuseFailAlloc_3332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3332_, 0, v_a_3326_);
v___x_3331_ = v_reuseFailAlloc_3332_;
goto v_reusejp_3330_;
}
v_reusejp_3330_:
{
return v___x_3331_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___boxed(lean_object* v_e_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_){
_start:
{
lean_object* v_res_3342_; 
v_res_3342_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(v_e_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_);
lean_dec(v_a_3340_);
lean_dec_ref(v_a_3339_);
lean_dec(v_a_3338_);
lean_dec_ref(v_a_3337_);
lean_dec(v_a_3336_);
lean_dec_ref(v_a_3335_);
return v_res_3342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized(lean_object* v_e_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_){
_start:
{
lean_object* v___x_3355_; 
v___x_3355_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(v_e_3343_, v_a_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_);
return v___x_3355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___boxed(lean_object* v_e_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_){
_start:
{
lean_object* v_res_3368_; 
v_res_3368_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized(v_e_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_);
lean_dec(v_a_3366_);
lean_dec_ref(v_a_3365_);
lean_dec(v_a_3364_);
lean_dec_ref(v_a_3363_);
lean_dec(v_a_3362_);
lean_dec_ref(v_a_3361_);
lean_dec(v_a_3360_);
lean_dec_ref(v_a_3359_);
lean_dec(v_a_3358_);
lean_dec(v_a_3357_);
return v_res_3368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f(lean_object* v_e_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_){
_start:
{
lean_object* v___x_3386_; 
lean_inc_ref(v_e_3374_);
v___x_3386_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3374_, v_a_3382_);
if (lean_obj_tag(v___x_3386_) == 0)
{
lean_object* v_a_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3502_; 
v_a_3387_ = lean_ctor_get(v___x_3386_, 0);
v_isSharedCheck_3502_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3502_ == 0)
{
v___x_3389_ = v___x_3386_;
v_isShared_3390_ = v_isSharedCheck_3502_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_a_3387_);
lean_dec(v___x_3386_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3502_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v___x_3396_; uint8_t v___x_3397_; 
v___x_3396_ = l_Lean_Expr_cleanupAnnotations(v_a_3387_);
v___x_3397_ = l_Lean_Expr_isApp(v___x_3396_);
if (v___x_3397_ == 0)
{
lean_dec_ref(v___x_3396_);
lean_dec_ref(v_e_3374_);
goto v___jp_3391_;
}
else
{
lean_object* v_arg_3398_; lean_object* v___x_3399_; uint8_t v___x_3400_; 
v_arg_3398_ = lean_ctor_get(v___x_3396_, 1);
lean_inc_ref(v_arg_3398_);
v___x_3399_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3396_);
v___x_3400_ = l_Lean_Expr_isApp(v___x_3399_);
if (v___x_3400_ == 0)
{
lean_dec_ref(v___x_3399_);
lean_dec_ref(v_arg_3398_);
lean_dec_ref(v_e_3374_);
goto v___jp_3391_;
}
else
{
lean_object* v_arg_3401_; lean_object* v___x_3402_; uint8_t v___x_3403_; 
v_arg_3401_ = lean_ctor_get(v___x_3399_, 1);
lean_inc_ref(v_arg_3401_);
v___x_3402_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3399_);
v___x_3403_ = l_Lean_Expr_isApp(v___x_3402_);
if (v___x_3403_ == 0)
{
lean_dec_ref(v___x_3402_);
lean_dec_ref(v_arg_3401_);
lean_dec_ref(v_arg_3398_);
lean_dec_ref(v_e_3374_);
goto v___jp_3391_;
}
else
{
lean_object* v_arg_3404_; lean_object* v___x_3405_; uint8_t v___x_3406_; 
v_arg_3404_ = lean_ctor_get(v___x_3402_, 1);
lean_inc_ref(v_arg_3404_);
v___x_3405_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3402_);
v___x_3406_ = l_Lean_Expr_isApp(v___x_3405_);
if (v___x_3406_ == 0)
{
lean_dec_ref(v___x_3405_);
lean_dec_ref(v_arg_3404_);
lean_dec_ref(v_arg_3401_);
lean_dec_ref(v_arg_3398_);
lean_dec_ref(v_e_3374_);
goto v___jp_3391_;
}
else
{
lean_object* v___x_3407_; lean_object* v___x_3408_; uint8_t v___x_3409_; 
v___x_3407_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3405_);
v___x_3408_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2));
v___x_3409_ = l_Lean_Expr_isConstOf(v___x_3407_, v___x_3408_);
lean_dec_ref(v___x_3407_);
if (v___x_3409_ == 0)
{
lean_dec_ref(v_arg_3404_);
lean_dec_ref(v_arg_3401_);
lean_dec_ref(v_arg_3398_);
lean_dec_ref(v_e_3374_);
goto v___jp_3391_;
}
else
{
lean_object* v___x_3410_; 
lean_del_object(v___x_3389_);
v___x_3410_ = l_Lean_Meta_Structural_isInstLEInt___redArg(v_arg_3404_, v_a_3382_);
if (lean_obj_tag(v___x_3410_) == 0)
{
lean_object* v_a_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3493_; 
v_a_3411_ = lean_ctor_get(v___x_3410_, 0);
v_isSharedCheck_3493_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3493_ == 0)
{
v___x_3413_ = v___x_3410_;
v_isShared_3414_ = v_isSharedCheck_3493_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_a_3411_);
lean_dec(v___x_3410_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3493_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
uint8_t v___x_3415_; 
v___x_3415_ = lean_unbox(v_a_3411_);
lean_dec(v_a_3411_);
if (v___x_3415_ == 0)
{
lean_object* v___x_3416_; lean_object* v___x_3418_; 
lean_dec_ref(v_arg_3401_);
lean_dec_ref(v_arg_3398_);
lean_dec_ref(v_e_3374_);
v___x_3416_ = lean_box(0);
if (v_isShared_3414_ == 0)
{
lean_ctor_set(v___x_3413_, 0, v___x_3416_);
v___x_3418_ = v___x_3413_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v___x_3416_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
return v___x_3418_;
}
}
else
{
lean_object* v___x_3420_; 
lean_del_object(v___x_3413_);
v___x_3420_ = l_Lean_Meta_getIntValue_x3f(v_arg_3398_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_);
if (lean_obj_tag(v___x_3420_) == 0)
{
lean_object* v_a_3421_; 
v_a_3421_ = lean_ctor_get(v___x_3420_, 0);
lean_inc(v_a_3421_);
lean_dec_ref(v___x_3420_);
if (lean_obj_tag(v_a_3421_) == 1)
{
lean_object* v_val_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3466_; 
v_val_3422_ = lean_ctor_get(v_a_3421_, 0);
v_isSharedCheck_3466_ = !lean_is_exclusive(v_a_3421_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3424_ = v_a_3421_;
v_isShared_3425_ = v_isSharedCheck_3466_;
goto v_resetjp_3423_;
}
else
{
lean_inc(v_val_3422_);
lean_dec(v_a_3421_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3466_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v___x_3426_; uint8_t v___x_3427_; 
v___x_3426_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9);
v___x_3427_ = lean_int_dec_eq(v_val_3422_, v___x_3426_);
lean_dec(v_val_3422_);
if (v___x_3427_ == 0)
{
lean_object* v___x_3428_; 
lean_del_object(v___x_3424_);
lean_dec_ref(v_arg_3401_);
v___x_3428_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(v_e_3374_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_);
if (lean_obj_tag(v___x_3428_) == 0)
{
lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3436_; 
v_isSharedCheck_3436_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3436_ == 0)
{
lean_object* v_unused_3437_; 
v_unused_3437_ = lean_ctor_get(v___x_3428_, 0);
lean_dec(v_unused_3437_);
v___x_3430_ = v___x_3428_;
v_isShared_3431_ = v_isSharedCheck_3436_;
goto v_resetjp_3429_;
}
else
{
lean_dec(v___x_3428_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3436_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v___x_3432_; lean_object* v___x_3434_; 
v___x_3432_ = lean_box(0);
if (v_isShared_3431_ == 0)
{
lean_ctor_set(v___x_3430_, 0, v___x_3432_);
v___x_3434_ = v___x_3430_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3435_; 
v_reuseFailAlloc_3435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3435_, 0, v___x_3432_);
v___x_3434_ = v_reuseFailAlloc_3435_;
goto v_reusejp_3433_;
}
v_reusejp_3433_:
{
return v___x_3434_;
}
}
}
else
{
lean_object* v_a_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3445_; 
v_a_3438_ = lean_ctor_get(v___x_3428_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3440_ = v___x_3428_;
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_a_3438_);
lean_dec(v___x_3428_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v___x_3443_; 
if (v_isShared_3441_ == 0)
{
v___x_3443_ = v___x_3440_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v_a_3438_);
v___x_3443_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
return v___x_3443_;
}
}
}
}
else
{
lean_object* v___x_3446_; 
lean_dec_ref(v_e_3374_);
v___x_3446_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(v_arg_3401_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_);
if (lean_obj_tag(v___x_3446_) == 0)
{
lean_object* v_a_3447_; lean_object* v___x_3449_; uint8_t v_isShared_3450_; uint8_t v_isSharedCheck_3457_; 
v_a_3447_ = lean_ctor_get(v___x_3446_, 0);
v_isSharedCheck_3457_ = !lean_is_exclusive(v___x_3446_);
if (v_isSharedCheck_3457_ == 0)
{
v___x_3449_ = v___x_3446_;
v_isShared_3450_ = v_isSharedCheck_3457_;
goto v_resetjp_3448_;
}
else
{
lean_inc(v_a_3447_);
lean_dec(v___x_3446_);
v___x_3449_ = lean_box(0);
v_isShared_3450_ = v_isSharedCheck_3457_;
goto v_resetjp_3448_;
}
v_resetjp_3448_:
{
lean_object* v___x_3452_; 
if (v_isShared_3425_ == 0)
{
lean_ctor_set(v___x_3424_, 0, v_a_3447_);
v___x_3452_ = v___x_3424_;
goto v_reusejp_3451_;
}
else
{
lean_object* v_reuseFailAlloc_3456_; 
v_reuseFailAlloc_3456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3456_, 0, v_a_3447_);
v___x_3452_ = v_reuseFailAlloc_3456_;
goto v_reusejp_3451_;
}
v_reusejp_3451_:
{
lean_object* v___x_3454_; 
if (v_isShared_3450_ == 0)
{
lean_ctor_set(v___x_3449_, 0, v___x_3452_);
v___x_3454_ = v___x_3449_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v___x_3452_);
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
lean_object* v_a_3458_; lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3465_; 
lean_del_object(v___x_3424_);
v_a_3458_ = lean_ctor_get(v___x_3446_, 0);
v_isSharedCheck_3465_ = !lean_is_exclusive(v___x_3446_);
if (v_isSharedCheck_3465_ == 0)
{
v___x_3460_ = v___x_3446_;
v_isShared_3461_ = v_isSharedCheck_3465_;
goto v_resetjp_3459_;
}
else
{
lean_inc(v_a_3458_);
lean_dec(v___x_3446_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3465_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
lean_object* v___x_3463_; 
if (v_isShared_3461_ == 0)
{
v___x_3463_ = v___x_3460_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_a_3458_);
v___x_3463_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
return v___x_3463_;
}
}
}
}
}
}
else
{
lean_object* v___x_3467_; 
lean_dec(v_a_3421_);
lean_dec_ref(v_arg_3401_);
v___x_3467_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(v_e_3374_, v_a_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_, v_a_3384_);
if (lean_obj_tag(v___x_3467_) == 0)
{
lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3475_; 
v_isSharedCheck_3475_ = !lean_is_exclusive(v___x_3467_);
if (v_isSharedCheck_3475_ == 0)
{
lean_object* v_unused_3476_; 
v_unused_3476_ = lean_ctor_get(v___x_3467_, 0);
lean_dec(v_unused_3476_);
v___x_3469_ = v___x_3467_;
v_isShared_3470_ = v_isSharedCheck_3475_;
goto v_resetjp_3468_;
}
else
{
lean_dec(v___x_3467_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3475_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v___x_3471_; lean_object* v___x_3473_; 
v___x_3471_ = lean_box(0);
if (v_isShared_3470_ == 0)
{
lean_ctor_set(v___x_3469_, 0, v___x_3471_);
v___x_3473_ = v___x_3469_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v___x_3471_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
return v___x_3473_;
}
}
}
else
{
lean_object* v_a_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3484_; 
v_a_3477_ = lean_ctor_get(v___x_3467_, 0);
v_isSharedCheck_3484_ = !lean_is_exclusive(v___x_3467_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3479_ = v___x_3467_;
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_a_3477_);
lean_dec(v___x_3467_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
lean_object* v___x_3482_; 
if (v_isShared_3480_ == 0)
{
v___x_3482_ = v___x_3479_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_a_3477_);
v___x_3482_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
return v___x_3482_;
}
}
}
}
}
else
{
lean_object* v_a_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3492_; 
lean_dec_ref(v_arg_3401_);
lean_dec_ref(v_e_3374_);
v_a_3485_ = lean_ctor_get(v___x_3420_, 0);
v_isSharedCheck_3492_ = !lean_is_exclusive(v___x_3420_);
if (v_isSharedCheck_3492_ == 0)
{
v___x_3487_ = v___x_3420_;
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_a_3485_);
lean_dec(v___x_3420_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v___x_3490_; 
if (v_isShared_3488_ == 0)
{
v___x_3490_ = v___x_3487_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v_a_3485_);
v___x_3490_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
return v___x_3490_;
}
}
}
}
}
}
else
{
lean_object* v_a_3494_; lean_object* v___x_3496_; uint8_t v_isShared_3497_; uint8_t v_isSharedCheck_3501_; 
lean_dec_ref(v_arg_3401_);
lean_dec_ref(v_arg_3398_);
lean_dec_ref(v_e_3374_);
v_a_3494_ = lean_ctor_get(v___x_3410_, 0);
v_isSharedCheck_3501_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3501_ == 0)
{
v___x_3496_ = v___x_3410_;
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
else
{
lean_inc(v_a_3494_);
lean_dec(v___x_3410_);
v___x_3496_ = lean_box(0);
v_isShared_3497_ = v_isSharedCheck_3501_;
goto v_resetjp_3495_;
}
v_resetjp_3495_:
{
lean_object* v___x_3499_; 
if (v_isShared_3497_ == 0)
{
v___x_3499_ = v___x_3496_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v_a_3494_);
v___x_3499_ = v_reuseFailAlloc_3500_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
return v___x_3499_;
}
}
}
}
}
}
}
}
v___jp_3391_:
{
lean_object* v___x_3392_; lean_object* v___x_3394_; 
v___x_3392_ = lean_box(0);
if (v_isShared_3390_ == 0)
{
lean_ctor_set(v___x_3389_, 0, v___x_3392_);
v___x_3394_ = v___x_3389_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v___x_3392_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
}
}
else
{
lean_object* v_a_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3510_; 
lean_dec_ref(v_e_3374_);
v_a_3503_ = lean_ctor_get(v___x_3386_, 0);
v_isSharedCheck_3510_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3505_ = v___x_3386_;
v_isShared_3506_ = v_isSharedCheck_3510_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_a_3503_);
lean_dec(v___x_3386_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3510_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
lean_object* v___x_3508_; 
if (v_isShared_3506_ == 0)
{
v___x_3508_ = v___x_3505_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v_a_3503_);
v___x_3508_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
return v___x_3508_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___boxed(lean_object* v_e_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_){
_start:
{
lean_object* v_res_3523_; 
v_res_3523_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f(v_e_3511_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_, v_a_3519_, v_a_3520_, v_a_3521_);
lean_dec(v_a_3521_);
lean_dec_ref(v_a_3520_);
lean_dec(v_a_3519_);
lean_dec_ref(v_a_3518_);
lean_dec(v_a_3517_);
lean_dec_ref(v_a_3516_);
lean_dec(v_a_3515_);
lean_dec_ref(v_a_3514_);
lean_dec(v_a_3513_);
lean_dec(v_a_3512_);
return v_res_3523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(lean_object* v_c_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_){
_start:
{
lean_object* v_p_3536_; lean_object* v___x_3537_; 
v_p_3536_ = lean_ctor_get(v_c_3524_, 0);
lean_inc_ref(v_p_3536_);
v___x_3537_ = l_Int_Linear_Poly_normCommRing_x3f(v_p_3536_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_);
if (lean_obj_tag(v___x_3537_) == 0)
{
lean_object* v_a_3538_; 
v_a_3538_ = lean_ctor_get(v___x_3537_, 0);
lean_inc(v_a_3538_);
lean_dec_ref(v___x_3537_);
if (lean_obj_tag(v_a_3538_) == 1)
{
lean_object* v_val_3539_; lean_object* v_snd_3540_; lean_object* v_fst_3541_; lean_object* v_fst_3542_; lean_object* v_snd_3543_; lean_object* v___x_3545_; uint8_t v_isShared_3546_; uint8_t v_isSharedCheck_3552_; 
v_val_3539_ = lean_ctor_get(v_a_3538_, 0);
lean_inc(v_val_3539_);
lean_dec_ref(v_a_3538_);
v_snd_3540_ = lean_ctor_get(v_val_3539_, 1);
lean_inc(v_snd_3540_);
v_fst_3541_ = lean_ctor_get(v_val_3539_, 0);
lean_inc(v_fst_3541_);
lean_dec(v_val_3539_);
v_fst_3542_ = lean_ctor_get(v_snd_3540_, 0);
v_snd_3543_ = lean_ctor_get(v_snd_3540_, 1);
v_isSharedCheck_3552_ = !lean_is_exclusive(v_snd_3540_);
if (v_isSharedCheck_3552_ == 0)
{
v___x_3545_ = v_snd_3540_;
v_isShared_3546_ = v_isSharedCheck_3552_;
goto v_resetjp_3544_;
}
else
{
lean_inc(v_snd_3543_);
lean_inc(v_fst_3542_);
lean_dec(v_snd_3540_);
v___x_3545_ = lean_box(0);
v_isShared_3546_ = v_isSharedCheck_3552_;
goto v_resetjp_3544_;
}
v_resetjp_3544_:
{
lean_object* v___x_3547_; lean_object* v___x_3549_; 
v___x_3547_ = lean_alloc_ctor(17, 3, 0);
lean_ctor_set(v___x_3547_, 0, v_c_3524_);
lean_ctor_set(v___x_3547_, 1, v_fst_3541_);
lean_ctor_set(v___x_3547_, 2, v_fst_3542_);
if (v_isShared_3546_ == 0)
{
lean_ctor_set(v___x_3545_, 1, v___x_3547_);
lean_ctor_set(v___x_3545_, 0, v_snd_3543_);
v___x_3549_ = v___x_3545_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v_snd_3543_);
lean_ctor_set(v_reuseFailAlloc_3551_, 1, v___x_3547_);
v___x_3549_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
lean_object* v___x_3550_; 
lean_inc(v_a_3534_);
lean_inc_ref(v_a_3533_);
lean_inc(v_a_3532_);
lean_inc_ref(v_a_3531_);
lean_inc(v_a_3530_);
lean_inc_ref(v_a_3529_);
lean_inc(v_a_3528_);
lean_inc_ref(v_a_3527_);
lean_inc(v_a_3526_);
lean_inc(v_a_3525_);
v___x_3550_ = lean_grind_cutsat_assert_le(v___x_3549_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_);
return v___x_3550_;
}
}
}
else
{
lean_object* v___x_3553_; 
lean_dec(v_a_3538_);
lean_inc(v_a_3534_);
lean_inc_ref(v_a_3533_);
lean_inc(v_a_3532_);
lean_inc_ref(v_a_3531_);
lean_inc(v_a_3530_);
lean_inc_ref(v_a_3529_);
lean_inc(v_a_3528_);
lean_inc_ref(v_a_3527_);
lean_inc(v_a_3526_);
lean_inc(v_a_3525_);
v___x_3553_ = lean_grind_cutsat_assert_le(v_c_3524_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_);
return v___x_3553_;
}
}
else
{
lean_object* v_a_3554_; lean_object* v___x_3556_; uint8_t v_isShared_3557_; uint8_t v_isSharedCheck_3561_; 
lean_dec_ref(v_c_3524_);
v_a_3554_ = lean_ctor_get(v___x_3537_, 0);
v_isSharedCheck_3561_ = !lean_is_exclusive(v___x_3537_);
if (v_isSharedCheck_3561_ == 0)
{
v___x_3556_ = v___x_3537_;
v_isShared_3557_ = v_isSharedCheck_3561_;
goto v_resetjp_3555_;
}
else
{
lean_inc(v_a_3554_);
lean_dec(v___x_3537_);
v___x_3556_ = lean_box(0);
v_isShared_3557_ = v_isSharedCheck_3561_;
goto v_resetjp_3555_;
}
v_resetjp_3555_:
{
lean_object* v___x_3559_; 
if (v_isShared_3557_ == 0)
{
v___x_3559_ = v___x_3556_;
goto v_reusejp_3558_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v_a_3554_);
v___x_3559_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3558_;
}
v_reusejp_3558_:
{
return v___x_3559_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore___boxed(lean_object* v_c_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_){
_start:
{
lean_object* v_res_3574_; 
v_res_3574_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v_c_3562_, v_a_3563_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_, v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_, v_a_3572_);
lean_dec(v_a_3572_);
lean_dec_ref(v_a_3571_);
lean_dec(v_a_3570_);
lean_dec_ref(v_a_3569_);
lean_dec(v_a_3568_);
lean_dec_ref(v_a_3567_);
lean_dec(v_a_3566_);
lean_dec_ref(v_a_3565_);
lean_dec(v_a_3564_);
lean_dec(v_a_3563_);
return v_res_3574_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0(void){
_start:
{
lean_object* v___x_3575_; lean_object* v___x_3576_; 
v___x_3575_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
v___x_3576_ = lean_int_neg(v___x_3575_);
return v___x_3576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe(lean_object* v_e_3577_, uint8_t v_eqTrue_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_, lean_object* v_a_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_){
_start:
{
lean_object* v___x_3590_; 
lean_inc_ref(v_e_3577_);
v___x_3590_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f(v_e_3577_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_, v_a_3585_, v_a_3586_, v_a_3587_, v_a_3588_);
if (lean_obj_tag(v___x_3590_) == 0)
{
lean_object* v_a_3591_; lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3617_; 
v_a_3591_ = lean_ctor_get(v___x_3590_, 0);
v_isSharedCheck_3617_ = !lean_is_exclusive(v___x_3590_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3593_ = v___x_3590_;
v_isShared_3594_ = v_isSharedCheck_3617_;
goto v_resetjp_3592_;
}
else
{
lean_inc(v_a_3591_);
lean_dec(v___x_3590_);
v___x_3593_ = lean_box(0);
v_isShared_3594_ = v_isSharedCheck_3617_;
goto v_resetjp_3592_;
}
v_resetjp_3592_:
{
if (lean_obj_tag(v_a_3591_) == 1)
{
lean_del_object(v___x_3593_);
if (v_eqTrue_3578_ == 0)
{
lean_object* v_val_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; 
v_val_3595_ = lean_ctor_get(v_a_3591_, 0);
lean_inc_n(v_val_3595_, 2);
lean_dec_ref(v_a_3591_);
v___x_3596_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
v___x_3597_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0);
v___x_3598_ = l_Int_Linear_Poly_mul(v_val_3595_, v___x_3597_);
v___x_3599_ = l_Int_Linear_Poly_addConst(v___x_3598_, v___x_3596_);
v___x_3600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3600_, 0, v_e_3577_);
lean_ctor_set(v___x_3600_, 1, v_val_3595_);
v___x_3601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3601_, 0, v___x_3599_);
lean_ctor_set(v___x_3601_, 1, v___x_3600_);
v___x_3602_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v___x_3601_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_, v_a_3585_, v_a_3586_, v_a_3587_, v_a_3588_);
return v___x_3602_;
}
else
{
lean_object* v_val_3603_; lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3612_; 
v_val_3603_ = lean_ctor_get(v_a_3591_, 0);
v_isSharedCheck_3612_ = !lean_is_exclusive(v_a_3591_);
if (v_isSharedCheck_3612_ == 0)
{
v___x_3605_ = v_a_3591_;
v_isShared_3606_ = v_isSharedCheck_3612_;
goto v_resetjp_3604_;
}
else
{
lean_inc(v_val_3603_);
lean_dec(v_a_3591_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3612_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
lean_object* v___x_3608_; 
if (v_isShared_3606_ == 0)
{
lean_ctor_set_tag(v___x_3605_, 0);
lean_ctor_set(v___x_3605_, 0, v_e_3577_);
v___x_3608_ = v___x_3605_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v_e_3577_);
v___x_3608_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
lean_object* v___x_3609_; lean_object* v___x_3610_; 
v___x_3609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3609_, 0, v_val_3603_);
lean_ctor_set(v___x_3609_, 1, v___x_3608_);
v___x_3610_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v___x_3609_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_, v_a_3585_, v_a_3586_, v_a_3587_, v_a_3588_);
return v___x_3610_;
}
}
}
}
else
{
lean_object* v___x_3613_; lean_object* v___x_3615_; 
lean_dec(v_a_3591_);
lean_dec_ref(v_e_3577_);
v___x_3613_ = lean_box(0);
if (v_isShared_3594_ == 0)
{
lean_ctor_set(v___x_3593_, 0, v___x_3613_);
v___x_3615_ = v___x_3593_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v___x_3613_);
v___x_3615_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
return v___x_3615_;
}
}
}
}
else
{
lean_object* v_a_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3625_; 
lean_dec_ref(v_e_3577_);
v_a_3618_ = lean_ctor_get(v___x_3590_, 0);
v_isSharedCheck_3625_ = !lean_is_exclusive(v___x_3590_);
if (v_isSharedCheck_3625_ == 0)
{
v___x_3620_ = v___x_3590_;
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_a_3618_);
lean_dec(v___x_3590_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v___x_3623_; 
if (v_isShared_3621_ == 0)
{
v___x_3623_ = v___x_3620_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v_a_3618_);
v___x_3623_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
return v___x_3623_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___boxed(lean_object* v_e_3626_, lean_object* v_eqTrue_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_, lean_object* v_a_3636_, lean_object* v_a_3637_, lean_object* v_a_3638_){
_start:
{
uint8_t v_eqTrue_boxed_3639_; lean_object* v_res_3640_; 
v_eqTrue_boxed_3639_ = lean_unbox(v_eqTrue_3627_);
v_res_3640_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe(v_e_3626_, v_eqTrue_boxed_3639_, v_a_3628_, v_a_3629_, v_a_3630_, v_a_3631_, v_a_3632_, v_a_3633_, v_a_3634_, v_a_3635_, v_a_3636_, v_a_3637_);
lean_dec(v_a_3637_);
lean_dec_ref(v_a_3636_);
lean_dec(v_a_3635_);
lean_dec_ref(v_a_3634_);
lean_dec(v_a_3633_);
lean_dec_ref(v_a_3632_);
lean_dec(v_a_3631_);
lean_dec_ref(v_a_3630_);
lean_dec(v_a_3629_);
lean_dec(v_a_3628_);
return v_res_3640_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0(void){
_start:
{
lean_object* v___x_3641_; lean_object* v___x_3642_; 
v___x_3641_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
v___x_3642_ = l_Lean_mkIntLit(v___x_3641_);
return v___x_3642_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5(void){
_start:
{
lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; 
v___x_3650_ = lean_box(0);
v___x_3651_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__4));
v___x_3652_ = l_Lean_mkConst(v___x_3651_, v___x_3650_);
return v___x_3652_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8(void){
_start:
{
lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; 
v___x_3658_ = lean_box(0);
v___x_3659_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__7));
v___x_3660_ = l_Lean_mkConst(v___x_3659_, v___x_3658_);
return v___x_3660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe(lean_object* v_e_3661_, uint8_t v_eqTrue_3662_, lean_object* v_a_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_){
_start:
{
lean_object* v___y_3675_; lean_object* v___y_3676_; lean_object* v_fst_3677_; lean_object* v_snd_3678_; lean_object* v___x_3707_; uint8_t v___x_3708_; 
lean_inc_ref(v_e_3661_);
v___x_3707_ = l_Lean_Expr_cleanupAnnotations(v_e_3661_);
v___x_3708_ = l_Lean_Expr_isApp(v___x_3707_);
if (v___x_3708_ == 0)
{
lean_dec_ref(v___x_3707_);
lean_dec_ref(v_e_3661_);
goto v___jp_3704_;
}
else
{
lean_object* v_arg_3709_; lean_object* v___x_3710_; uint8_t v___x_3711_; 
v_arg_3709_ = lean_ctor_get(v___x_3707_, 1);
lean_inc_ref(v_arg_3709_);
v___x_3710_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3707_);
v___x_3711_ = l_Lean_Expr_isApp(v___x_3710_);
if (v___x_3711_ == 0)
{
lean_dec_ref(v___x_3710_);
lean_dec_ref(v_arg_3709_);
lean_dec_ref(v_e_3661_);
goto v___jp_3704_;
}
else
{
lean_object* v_arg_3712_; lean_object* v___y_3714_; lean_object* v___x_3752_; uint8_t v___x_3753_; 
v_arg_3712_ = lean_ctor_get(v___x_3710_, 1);
lean_inc_ref(v_arg_3712_);
v___x_3752_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3710_);
v___x_3753_ = l_Lean_Expr_isApp(v___x_3752_);
if (v___x_3753_ == 0)
{
lean_dec_ref(v___x_3752_);
lean_dec_ref(v_arg_3712_);
lean_dec_ref(v_arg_3709_);
lean_dec_ref(v_e_3661_);
goto v___jp_3704_;
}
else
{
lean_object* v___x_3754_; uint8_t v___x_3755_; 
v___x_3754_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3752_);
v___x_3755_ = l_Lean_Expr_isApp(v___x_3754_);
if (v___x_3755_ == 0)
{
lean_dec_ref(v___x_3754_);
lean_dec_ref(v_arg_3712_);
lean_dec_ref(v_arg_3709_);
lean_dec_ref(v_e_3661_);
goto v___jp_3704_;
}
else
{
lean_object* v___x_3756_; lean_object* v___x_3757_; uint8_t v___x_3758_; 
v___x_3756_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3754_);
v___x_3757_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2));
v___x_3758_ = l_Lean_Expr_isConstOf(v___x_3756_, v___x_3757_);
lean_dec_ref(v___x_3756_);
if (v___x_3758_ == 0)
{
lean_dec_ref(v_arg_3712_);
lean_dec_ref(v_arg_3709_);
lean_dec_ref(v_e_3661_);
goto v___jp_3704_;
}
else
{
if (v_eqTrue_3662_ == 0)
{
lean_object* v___x_3759_; 
v___x_3759_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5);
v___y_3714_ = v___x_3759_;
goto v___jp_3713_;
}
else
{
lean_object* v___x_3760_; 
v___x_3760_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8);
v___y_3714_ = v___x_3760_;
goto v___jp_3713_;
}
}
}
}
v___jp_3713_:
{
lean_object* v___x_3715_; 
v___x_3715_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_3661_, v_a_3663_);
if (lean_obj_tag(v___x_3715_) == 0)
{
lean_object* v_a_3716_; lean_object* v___x_3717_; 
v_a_3716_ = lean_ctor_get(v___x_3715_, 0);
lean_inc(v_a_3716_);
lean_dec_ref(v___x_3715_);
lean_inc_ref(v_arg_3712_);
v___x_3717_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_3712_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_);
if (lean_obj_tag(v___x_3717_) == 0)
{
lean_object* v_a_3718_; lean_object* v_fst_3719_; lean_object* v_snd_3720_; lean_object* v___x_3721_; 
v_a_3718_ = lean_ctor_get(v___x_3717_, 0);
lean_inc(v_a_3718_);
lean_dec_ref(v___x_3717_);
v_fst_3719_ = lean_ctor_get(v_a_3718_, 0);
lean_inc(v_fst_3719_);
v_snd_3720_ = lean_ctor_get(v_a_3718_, 1);
lean_inc(v_snd_3720_);
lean_dec(v_a_3718_);
lean_inc_ref(v_arg_3709_);
v___x_3721_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_3709_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_);
if (lean_obj_tag(v___x_3721_) == 0)
{
lean_object* v_a_3722_; lean_object* v_fst_3723_; lean_object* v_snd_3724_; lean_object* v___x_3725_; 
v_a_3722_ = lean_ctor_get(v___x_3721_, 0);
lean_inc(v_a_3722_);
lean_dec_ref(v___x_3721_);
v_fst_3723_ = lean_ctor_get(v_a_3722_, 0);
lean_inc_n(v_fst_3723_, 2);
v_snd_3724_ = lean_ctor_get(v_a_3722_, 1);
lean_inc(v_snd_3724_);
lean_dec(v_a_3722_);
lean_inc(v_fst_3719_);
lean_inc_ref(v___y_3714_);
v___x_3725_ = l_Lean_mkApp6(v___y_3714_, v_arg_3712_, v_arg_3709_, v_fst_3719_, v_fst_3723_, v_snd_3720_, v_snd_3724_);
if (v_eqTrue_3662_ == 0)
{
lean_object* v___x_3726_; lean_object* v___x_3727_; 
v___x_3726_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0);
v___x_3727_ = l_Lean_mkIntAdd(v_fst_3723_, v___x_3726_);
v___y_3675_ = v_a_3716_;
v___y_3676_ = v___x_3725_;
v_fst_3677_ = v___x_3727_;
v_snd_3678_ = v_fst_3719_;
goto v___jp_3674_;
}
else
{
v___y_3675_ = v_a_3716_;
v___y_3676_ = v___x_3725_;
v_fst_3677_ = v_fst_3719_;
v_snd_3678_ = v_fst_3723_;
goto v___jp_3674_;
}
}
else
{
lean_object* v_a_3728_; lean_object* v___x_3730_; uint8_t v_isShared_3731_; uint8_t v_isSharedCheck_3735_; 
lean_dec(v_snd_3720_);
lean_dec(v_fst_3719_);
lean_dec(v_a_3716_);
lean_dec_ref(v_arg_3712_);
lean_dec_ref(v_arg_3709_);
lean_dec_ref(v_e_3661_);
v_a_3728_ = lean_ctor_get(v___x_3721_, 0);
v_isSharedCheck_3735_ = !lean_is_exclusive(v___x_3721_);
if (v_isSharedCheck_3735_ == 0)
{
v___x_3730_ = v___x_3721_;
v_isShared_3731_ = v_isSharedCheck_3735_;
goto v_resetjp_3729_;
}
else
{
lean_inc(v_a_3728_);
lean_dec(v___x_3721_);
v___x_3730_ = lean_box(0);
v_isShared_3731_ = v_isSharedCheck_3735_;
goto v_resetjp_3729_;
}
v_resetjp_3729_:
{
lean_object* v___x_3733_; 
if (v_isShared_3731_ == 0)
{
v___x_3733_ = v___x_3730_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v_a_3728_);
v___x_3733_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
return v___x_3733_;
}
}
}
}
else
{
lean_object* v_a_3736_; lean_object* v___x_3738_; uint8_t v_isShared_3739_; uint8_t v_isSharedCheck_3743_; 
lean_dec(v_a_3716_);
lean_dec_ref(v_arg_3712_);
lean_dec_ref(v_arg_3709_);
lean_dec_ref(v_e_3661_);
v_a_3736_ = lean_ctor_get(v___x_3717_, 0);
v_isSharedCheck_3743_ = !lean_is_exclusive(v___x_3717_);
if (v_isSharedCheck_3743_ == 0)
{
v___x_3738_ = v___x_3717_;
v_isShared_3739_ = v_isSharedCheck_3743_;
goto v_resetjp_3737_;
}
else
{
lean_inc(v_a_3736_);
lean_dec(v___x_3717_);
v___x_3738_ = lean_box(0);
v_isShared_3739_ = v_isSharedCheck_3743_;
goto v_resetjp_3737_;
}
v_resetjp_3737_:
{
lean_object* v___x_3741_; 
if (v_isShared_3739_ == 0)
{
v___x_3741_ = v___x_3738_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v_a_3736_);
v___x_3741_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
return v___x_3741_;
}
}
}
}
else
{
lean_object* v_a_3744_; lean_object* v___x_3746_; uint8_t v_isShared_3747_; uint8_t v_isSharedCheck_3751_; 
lean_dec_ref(v_arg_3712_);
lean_dec_ref(v_arg_3709_);
lean_dec_ref(v_e_3661_);
v_a_3744_ = lean_ctor_get(v___x_3715_, 0);
v_isSharedCheck_3751_ = !lean_is_exclusive(v___x_3715_);
if (v_isSharedCheck_3751_ == 0)
{
v___x_3746_ = v___x_3715_;
v_isShared_3747_ = v_isSharedCheck_3751_;
goto v_resetjp_3745_;
}
else
{
lean_inc(v_a_3744_);
lean_dec(v___x_3715_);
v___x_3746_ = lean_box(0);
v_isShared_3747_ = v_isSharedCheck_3751_;
goto v_resetjp_3745_;
}
v_resetjp_3745_:
{
lean_object* v___x_3749_; 
if (v_isShared_3747_ == 0)
{
v___x_3749_ = v___x_3746_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v_a_3744_);
v___x_3749_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
return v___x_3749_;
}
}
}
}
}
}
v___jp_3674_:
{
lean_object* v___x_3679_; 
lean_inc(v___y_3675_);
v___x_3679_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_3677_, v___y_3675_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_);
if (lean_obj_tag(v___x_3679_) == 0)
{
lean_object* v_a_3680_; lean_object* v___x_3681_; 
v_a_3680_ = lean_ctor_get(v___x_3679_, 0);
lean_inc(v_a_3680_);
lean_dec_ref(v___x_3679_);
v___x_3681_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_snd_3678_, v___y_3675_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_);
if (lean_obj_tag(v___x_3681_) == 0)
{
lean_object* v_a_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; 
v_a_3682_ = lean_ctor_get(v___x_3681_, 0);
lean_inc_n(v_a_3682_, 2);
lean_dec_ref(v___x_3681_);
lean_inc(v_a_3680_);
v___x_3683_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3683_, 0, v_a_3680_);
lean_ctor_set(v___x_3683_, 1, v_a_3682_);
v___x_3684_ = l_Int_Linear_Expr_norm(v___x_3683_);
lean_dec_ref(v___x_3683_);
v___x_3685_ = lean_alloc_ctor(2, 4, 1);
lean_ctor_set(v___x_3685_, 0, v_e_3661_);
lean_ctor_set(v___x_3685_, 1, v___y_3676_);
lean_ctor_set(v___x_3685_, 2, v_a_3680_);
lean_ctor_set(v___x_3685_, 3, v_a_3682_);
lean_ctor_set_uint8(v___x_3685_, sizeof(void*)*4, v_eqTrue_3662_);
v___x_3686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3686_, 0, v___x_3684_);
lean_ctor_set(v___x_3686_, 1, v___x_3685_);
v___x_3687_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v___x_3686_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_);
return v___x_3687_;
}
else
{
lean_object* v_a_3688_; lean_object* v___x_3690_; uint8_t v_isShared_3691_; uint8_t v_isSharedCheck_3695_; 
lean_dec(v_a_3680_);
lean_dec_ref(v___y_3676_);
lean_dec_ref(v_e_3661_);
v_a_3688_ = lean_ctor_get(v___x_3681_, 0);
v_isSharedCheck_3695_ = !lean_is_exclusive(v___x_3681_);
if (v_isSharedCheck_3695_ == 0)
{
v___x_3690_ = v___x_3681_;
v_isShared_3691_ = v_isSharedCheck_3695_;
goto v_resetjp_3689_;
}
else
{
lean_inc(v_a_3688_);
lean_dec(v___x_3681_);
v___x_3690_ = lean_box(0);
v_isShared_3691_ = v_isSharedCheck_3695_;
goto v_resetjp_3689_;
}
v_resetjp_3689_:
{
lean_object* v___x_3693_; 
if (v_isShared_3691_ == 0)
{
v___x_3693_ = v___x_3690_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v_a_3688_);
v___x_3693_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
return v___x_3693_;
}
}
}
}
else
{
lean_object* v_a_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3703_; 
lean_dec_ref(v_snd_3678_);
lean_dec_ref(v___y_3676_);
lean_dec(v___y_3675_);
lean_dec_ref(v_e_3661_);
v_a_3696_ = lean_ctor_get(v___x_3679_, 0);
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3679_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3698_ = v___x_3679_;
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_a_3696_);
lean_dec(v___x_3679_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v___x_3701_; 
if (v_isShared_3699_ == 0)
{
v___x_3701_ = v___x_3698_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v_a_3696_);
v___x_3701_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
return v___x_3701_;
}
}
}
}
v___jp_3704_:
{
lean_object* v___x_3705_; lean_object* v___x_3706_; 
v___x_3705_ = lean_box(0);
v___x_3706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3706_, 0, v___x_3705_);
return v___x_3706_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___boxed(lean_object* v_e_3761_, lean_object* v_eqTrue_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_){
_start:
{
uint8_t v_eqTrue_boxed_3774_; lean_object* v_res_3775_; 
v_eqTrue_boxed_3774_ = lean_unbox(v_eqTrue_3762_);
v_res_3775_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe(v_e_3761_, v_eqTrue_boxed_3774_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_, v_a_3770_, v_a_3771_, v_a_3772_);
lean_dec(v_a_3772_);
lean_dec_ref(v_a_3771_);
lean_dec(v_a_3770_);
lean_dec_ref(v_a_3769_);
lean_dec(v_a_3768_);
lean_dec_ref(v_a_3767_);
lean_dec(v_a_3766_);
lean_dec_ref(v_a_3765_);
lean_dec(v_a_3764_);
lean_dec(v_a_3763_);
return v_res_3775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe(lean_object* v_e_3776_, uint8_t v_eqTrue_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_, lean_object* v_a_3783_, lean_object* v_a_3784_, lean_object* v_a_3785_, lean_object* v_a_3786_, lean_object* v_a_3787_, lean_object* v_a_3788_){
_start:
{
lean_object* v___y_3794_; lean_object* v___y_3795_; lean_object* v___y_3796_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v___y_3803_; lean_object* v___y_3804_; lean_object* v___y_3805_; lean_object* v_fst_3806_; lean_object* v_snd_3807_; lean_object* v_____x_3834_; lean_object* v___y_3835_; lean_object* v___y_3836_; lean_object* v___y_3837_; lean_object* v___y_3838_; lean_object* v___y_3839_; lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; 
if (v_eqTrue_3777_ == 0)
{
lean_object* v___x_3899_; 
v___x_3899_ = l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLE_x3f___redArg(v_a_3778_, v_a_3779_, v_a_3785_, v_a_3786_, v_a_3787_, v_a_3788_);
if (lean_obj_tag(v___x_3899_) == 0)
{
lean_object* v_a_3900_; 
v_a_3900_ = lean_ctor_get(v___x_3899_, 0);
lean_inc(v_a_3900_);
lean_dec_ref(v___x_3899_);
v_____x_3834_ = v_a_3900_;
v___y_3835_ = v_a_3778_;
v___y_3836_ = v_a_3779_;
v___y_3837_ = v_a_3780_;
v___y_3838_ = v_a_3781_;
v___y_3839_ = v_a_3782_;
v___y_3840_ = v_a_3783_;
v___y_3841_ = v_a_3784_;
v___y_3842_ = v_a_3785_;
v___y_3843_ = v_a_3786_;
v___y_3844_ = v_a_3787_;
v___y_3845_ = v_a_3788_;
goto v___jp_3833_;
}
else
{
lean_object* v_a_3901_; lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_3908_; 
lean_dec_ref(v_e_3776_);
v_a_3901_ = lean_ctor_get(v___x_3899_, 0);
v_isSharedCheck_3908_ = !lean_is_exclusive(v___x_3899_);
if (v_isSharedCheck_3908_ == 0)
{
v___x_3903_ = v___x_3899_;
v_isShared_3904_ = v_isSharedCheck_3908_;
goto v_resetjp_3902_;
}
else
{
lean_inc(v_a_3901_);
lean_dec(v___x_3899_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_3908_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
lean_object* v___x_3906_; 
if (v_isShared_3904_ == 0)
{
v___x_3906_ = v___x_3903_;
goto v_reusejp_3905_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v_a_3901_);
v___x_3906_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3905_;
}
v_reusejp_3905_:
{
return v___x_3906_;
}
}
}
}
else
{
lean_object* v___x_3909_; 
v___x_3909_ = l_Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f___redArg(v_a_3778_, v_a_3779_, v_a_3785_, v_a_3786_, v_a_3787_, v_a_3788_);
if (lean_obj_tag(v___x_3909_) == 0)
{
lean_object* v_a_3910_; 
v_a_3910_ = lean_ctor_get(v___x_3909_, 0);
lean_inc(v_a_3910_);
lean_dec_ref(v___x_3909_);
v_____x_3834_ = v_a_3910_;
v___y_3835_ = v_a_3778_;
v___y_3836_ = v_a_3779_;
v___y_3837_ = v_a_3780_;
v___y_3838_ = v_a_3781_;
v___y_3839_ = v_a_3782_;
v___y_3840_ = v_a_3783_;
v___y_3841_ = v_a_3784_;
v___y_3842_ = v_a_3785_;
v___y_3843_ = v_a_3786_;
v___y_3844_ = v_a_3787_;
v___y_3845_ = v_a_3788_;
goto v___jp_3833_;
}
else
{
lean_object* v_a_3911_; lean_object* v___x_3913_; uint8_t v_isShared_3914_; uint8_t v_isSharedCheck_3918_; 
lean_dec_ref(v_e_3776_);
v_a_3911_ = lean_ctor_get(v___x_3909_, 0);
v_isSharedCheck_3918_ = !lean_is_exclusive(v___x_3909_);
if (v_isSharedCheck_3918_ == 0)
{
v___x_3913_ = v___x_3909_;
v_isShared_3914_ = v_isSharedCheck_3918_;
goto v_resetjp_3912_;
}
else
{
lean_inc(v_a_3911_);
lean_dec(v___x_3909_);
v___x_3913_ = lean_box(0);
v_isShared_3914_ = v_isSharedCheck_3918_;
goto v_resetjp_3912_;
}
v_resetjp_3912_:
{
lean_object* v___x_3916_; 
if (v_isShared_3914_ == 0)
{
v___x_3916_ = v___x_3913_;
goto v_reusejp_3915_;
}
else
{
lean_object* v_reuseFailAlloc_3917_; 
v_reuseFailAlloc_3917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3917_, 0, v_a_3911_);
v___x_3916_ = v_reuseFailAlloc_3917_;
goto v_reusejp_3915_;
}
v_reusejp_3915_:
{
return v___x_3916_;
}
}
}
}
v___jp_3790_:
{
lean_object* v___x_3791_; lean_object* v___x_3792_; 
v___x_3791_ = lean_box(0);
v___x_3792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3792_, 0, v___x_3791_);
return v___x_3792_;
}
v___jp_3793_:
{
lean_object* v___x_3808_; 
lean_inc(v___y_3799_);
v___x_3808_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_3806_, v___y_3799_, v___y_3798_, v___y_3795_, v___y_3800_, v___y_3796_, v___y_3802_, v___y_3794_, v___y_3801_, v___y_3797_, v___y_3803_, v___y_3805_);
if (lean_obj_tag(v___x_3808_) == 0)
{
lean_object* v_a_3809_; lean_object* v___x_3810_; 
v_a_3809_ = lean_ctor_get(v___x_3808_, 0);
lean_inc(v_a_3809_);
lean_dec_ref(v___x_3808_);
v___x_3810_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_snd_3807_, v___y_3799_, v___y_3798_, v___y_3795_, v___y_3800_, v___y_3796_, v___y_3802_, v___y_3794_, v___y_3801_, v___y_3797_, v___y_3803_, v___y_3805_);
if (lean_obj_tag(v___x_3810_) == 0)
{
lean_object* v_a_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; 
v_a_3811_ = lean_ctor_get(v___x_3810_, 0);
lean_inc_n(v_a_3811_, 2);
lean_dec_ref(v___x_3810_);
lean_inc(v_a_3809_);
v___x_3812_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3812_, 0, v_a_3809_);
lean_ctor_set(v___x_3812_, 1, v_a_3811_);
v___x_3813_ = l_Int_Linear_Expr_norm(v___x_3812_);
lean_dec_ref(v___x_3812_);
v___x_3814_ = lean_alloc_ctor(2, 4, 1);
lean_ctor_set(v___x_3814_, 0, v_e_3776_);
lean_ctor_set(v___x_3814_, 1, v___y_3804_);
lean_ctor_set(v___x_3814_, 2, v_a_3809_);
lean_ctor_set(v___x_3814_, 3, v_a_3811_);
lean_ctor_set_uint8(v___x_3814_, sizeof(void*)*4, v_eqTrue_3777_);
v___x_3815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3815_, 0, v___x_3813_);
lean_ctor_set(v___x_3815_, 1, v___x_3814_);
v___x_3816_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v___x_3815_, v___y_3798_, v___y_3795_, v___y_3800_, v___y_3796_, v___y_3802_, v___y_3794_, v___y_3801_, v___y_3797_, v___y_3803_, v___y_3805_);
return v___x_3816_;
}
else
{
lean_object* v_a_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3824_; 
lean_dec(v_a_3809_);
lean_dec_ref(v___y_3804_);
lean_dec_ref(v_e_3776_);
v_a_3817_ = lean_ctor_get(v___x_3810_, 0);
v_isSharedCheck_3824_ = !lean_is_exclusive(v___x_3810_);
if (v_isSharedCheck_3824_ == 0)
{
v___x_3819_ = v___x_3810_;
v_isShared_3820_ = v_isSharedCheck_3824_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_a_3817_);
lean_dec(v___x_3810_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3824_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
lean_object* v___x_3822_; 
if (v_isShared_3820_ == 0)
{
v___x_3822_ = v___x_3819_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v_a_3817_);
v___x_3822_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
return v___x_3822_;
}
}
}
}
else
{
lean_object* v_a_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3832_; 
lean_dec_ref(v_snd_3807_);
lean_dec_ref(v___y_3804_);
lean_dec(v___y_3799_);
lean_dec_ref(v_e_3776_);
v_a_3825_ = lean_ctor_get(v___x_3808_, 0);
v_isSharedCheck_3832_ = !lean_is_exclusive(v___x_3808_);
if (v_isSharedCheck_3832_ == 0)
{
v___x_3827_ = v___x_3808_;
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_a_3825_);
lean_dec(v___x_3808_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3830_; 
if (v_isShared_3828_ == 0)
{
v___x_3830_ = v___x_3827_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_a_3825_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
}
}
v___jp_3833_:
{
if (lean_obj_tag(v_____x_3834_) == 1)
{
lean_object* v_val_3846_; lean_object* v___x_3847_; uint8_t v___x_3848_; 
v_val_3846_ = lean_ctor_get(v_____x_3834_, 0);
lean_inc(v_val_3846_);
lean_dec_ref(v_____x_3834_);
lean_inc_ref(v_e_3776_);
v___x_3847_ = l_Lean_Expr_cleanupAnnotations(v_e_3776_);
v___x_3848_ = l_Lean_Expr_isApp(v___x_3847_);
if (v___x_3848_ == 0)
{
lean_dec_ref(v___x_3847_);
lean_dec(v_val_3846_);
lean_dec_ref(v_e_3776_);
goto v___jp_3790_;
}
else
{
lean_object* v_arg_3849_; lean_object* v___x_3850_; uint8_t v___x_3851_; 
v_arg_3849_ = lean_ctor_get(v___x_3847_, 1);
lean_inc_ref(v_arg_3849_);
v___x_3850_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3847_);
v___x_3851_ = l_Lean_Expr_isApp(v___x_3850_);
if (v___x_3851_ == 0)
{
lean_dec_ref(v___x_3850_);
lean_dec_ref(v_arg_3849_);
lean_dec(v_val_3846_);
lean_dec_ref(v_e_3776_);
goto v___jp_3790_;
}
else
{
lean_object* v_arg_3852_; lean_object* v___x_3853_; uint8_t v___x_3854_; 
v_arg_3852_ = lean_ctor_get(v___x_3850_, 1);
lean_inc_ref(v_arg_3852_);
v___x_3853_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3850_);
v___x_3854_ = l_Lean_Expr_isApp(v___x_3853_);
if (v___x_3854_ == 0)
{
lean_dec_ref(v___x_3853_);
lean_dec_ref(v_arg_3852_);
lean_dec_ref(v_arg_3849_);
lean_dec(v_val_3846_);
lean_dec_ref(v_e_3776_);
goto v___jp_3790_;
}
else
{
lean_object* v___x_3855_; uint8_t v___x_3856_; 
v___x_3855_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3853_);
v___x_3856_ = l_Lean_Expr_isApp(v___x_3855_);
if (v___x_3856_ == 0)
{
lean_dec_ref(v___x_3855_);
lean_dec_ref(v_arg_3852_);
lean_dec_ref(v_arg_3849_);
lean_dec(v_val_3846_);
lean_dec_ref(v_e_3776_);
goto v___jp_3790_;
}
else
{
lean_object* v___x_3857_; lean_object* v___x_3858_; uint8_t v___x_3859_; 
v___x_3857_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3855_);
v___x_3858_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2));
v___x_3859_ = l_Lean_Expr_isConstOf(v___x_3857_, v___x_3858_);
lean_dec_ref(v___x_3857_);
if (v___x_3859_ == 0)
{
lean_dec_ref(v_arg_3852_);
lean_dec_ref(v_arg_3849_);
lean_dec(v_val_3846_);
lean_dec_ref(v_e_3776_);
goto v___jp_3790_;
}
else
{
lean_object* v___x_3860_; 
v___x_3860_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_3776_, v___y_3836_);
if (lean_obj_tag(v___x_3860_) == 0)
{
lean_object* v_a_3861_; lean_object* v___x_3862_; 
v_a_3861_ = lean_ctor_get(v___x_3860_, 0);
lean_inc(v_a_3861_);
lean_dec_ref(v___x_3860_);
lean_inc_ref(v_arg_3852_);
v___x_3862_ = l_Lean_Meta_Grind_Arith_Cutsat_toInt(v_arg_3852_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_);
if (lean_obj_tag(v___x_3862_) == 0)
{
lean_object* v_a_3863_; lean_object* v_fst_3864_; lean_object* v_snd_3865_; lean_object* v___x_3866_; 
v_a_3863_ = lean_ctor_get(v___x_3862_, 0);
lean_inc(v_a_3863_);
lean_dec_ref(v___x_3862_);
v_fst_3864_ = lean_ctor_get(v_a_3863_, 0);
lean_inc(v_fst_3864_);
v_snd_3865_ = lean_ctor_get(v_a_3863_, 1);
lean_inc(v_snd_3865_);
lean_dec(v_a_3863_);
lean_inc_ref(v_arg_3849_);
v___x_3866_ = l_Lean_Meta_Grind_Arith_Cutsat_toInt(v_arg_3849_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_);
if (lean_obj_tag(v___x_3866_) == 0)
{
lean_object* v_a_3867_; lean_object* v_fst_3868_; lean_object* v_snd_3869_; lean_object* v___x_3870_; 
v_a_3867_ = lean_ctor_get(v___x_3866_, 0);
lean_inc(v_a_3867_);
lean_dec_ref(v___x_3866_);
v_fst_3868_ = lean_ctor_get(v_a_3867_, 0);
lean_inc_n(v_fst_3868_, 2);
v_snd_3869_ = lean_ctor_get(v_a_3867_, 1);
lean_inc(v_snd_3869_);
lean_dec(v_a_3867_);
lean_inc(v_fst_3864_);
v___x_3870_ = l_Lean_mkApp6(v_val_3846_, v_arg_3852_, v_arg_3849_, v_fst_3864_, v_fst_3868_, v_snd_3865_, v_snd_3869_);
if (v_eqTrue_3777_ == 0)
{
lean_object* v___x_3871_; lean_object* v___x_3872_; 
v___x_3871_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0);
v___x_3872_ = l_Lean_mkIntAdd(v_fst_3868_, v___x_3871_);
v___y_3794_ = v___y_3841_;
v___y_3795_ = v___y_3837_;
v___y_3796_ = v___y_3839_;
v___y_3797_ = v___y_3843_;
v___y_3798_ = v___y_3836_;
v___y_3799_ = v_a_3861_;
v___y_3800_ = v___y_3838_;
v___y_3801_ = v___y_3842_;
v___y_3802_ = v___y_3840_;
v___y_3803_ = v___y_3844_;
v___y_3804_ = v___x_3870_;
v___y_3805_ = v___y_3845_;
v_fst_3806_ = v___x_3872_;
v_snd_3807_ = v_fst_3864_;
goto v___jp_3793_;
}
else
{
v___y_3794_ = v___y_3841_;
v___y_3795_ = v___y_3837_;
v___y_3796_ = v___y_3839_;
v___y_3797_ = v___y_3843_;
v___y_3798_ = v___y_3836_;
v___y_3799_ = v_a_3861_;
v___y_3800_ = v___y_3838_;
v___y_3801_ = v___y_3842_;
v___y_3802_ = v___y_3840_;
v___y_3803_ = v___y_3844_;
v___y_3804_ = v___x_3870_;
v___y_3805_ = v___y_3845_;
v_fst_3806_ = v_fst_3864_;
v_snd_3807_ = v_fst_3868_;
goto v___jp_3793_;
}
}
else
{
lean_object* v_a_3873_; lean_object* v___x_3875_; uint8_t v_isShared_3876_; uint8_t v_isSharedCheck_3880_; 
lean_dec(v_snd_3865_);
lean_dec(v_fst_3864_);
lean_dec(v_a_3861_);
lean_dec_ref(v_arg_3852_);
lean_dec_ref(v_arg_3849_);
lean_dec(v_val_3846_);
lean_dec_ref(v_e_3776_);
v_a_3873_ = lean_ctor_get(v___x_3866_, 0);
v_isSharedCheck_3880_ = !lean_is_exclusive(v___x_3866_);
if (v_isSharedCheck_3880_ == 0)
{
v___x_3875_ = v___x_3866_;
v_isShared_3876_ = v_isSharedCheck_3880_;
goto v_resetjp_3874_;
}
else
{
lean_inc(v_a_3873_);
lean_dec(v___x_3866_);
v___x_3875_ = lean_box(0);
v_isShared_3876_ = v_isSharedCheck_3880_;
goto v_resetjp_3874_;
}
v_resetjp_3874_:
{
lean_object* v___x_3878_; 
if (v_isShared_3876_ == 0)
{
v___x_3878_ = v___x_3875_;
goto v_reusejp_3877_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v_a_3873_);
v___x_3878_ = v_reuseFailAlloc_3879_;
goto v_reusejp_3877_;
}
v_reusejp_3877_:
{
return v___x_3878_;
}
}
}
}
else
{
lean_object* v_a_3881_; lean_object* v___x_3883_; uint8_t v_isShared_3884_; uint8_t v_isSharedCheck_3888_; 
lean_dec(v_a_3861_);
lean_dec_ref(v_arg_3852_);
lean_dec_ref(v_arg_3849_);
lean_dec(v_val_3846_);
lean_dec_ref(v_e_3776_);
v_a_3881_ = lean_ctor_get(v___x_3862_, 0);
v_isSharedCheck_3888_ = !lean_is_exclusive(v___x_3862_);
if (v_isSharedCheck_3888_ == 0)
{
v___x_3883_ = v___x_3862_;
v_isShared_3884_ = v_isSharedCheck_3888_;
goto v_resetjp_3882_;
}
else
{
lean_inc(v_a_3881_);
lean_dec(v___x_3862_);
v___x_3883_ = lean_box(0);
v_isShared_3884_ = v_isSharedCheck_3888_;
goto v_resetjp_3882_;
}
v_resetjp_3882_:
{
lean_object* v___x_3886_; 
if (v_isShared_3884_ == 0)
{
v___x_3886_ = v___x_3883_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3887_; 
v_reuseFailAlloc_3887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3887_, 0, v_a_3881_);
v___x_3886_ = v_reuseFailAlloc_3887_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
return v___x_3886_;
}
}
}
}
else
{
lean_object* v_a_3889_; lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3896_; 
lean_dec_ref(v_arg_3852_);
lean_dec_ref(v_arg_3849_);
lean_dec(v_val_3846_);
lean_dec_ref(v_e_3776_);
v_a_3889_ = lean_ctor_get(v___x_3860_, 0);
v_isSharedCheck_3896_ = !lean_is_exclusive(v___x_3860_);
if (v_isSharedCheck_3896_ == 0)
{
v___x_3891_ = v___x_3860_;
v_isShared_3892_ = v_isSharedCheck_3896_;
goto v_resetjp_3890_;
}
else
{
lean_inc(v_a_3889_);
lean_dec(v___x_3860_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3896_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
lean_object* v___x_3894_; 
if (v_isShared_3892_ == 0)
{
v___x_3894_ = v___x_3891_;
goto v_reusejp_3893_;
}
else
{
lean_object* v_reuseFailAlloc_3895_; 
v_reuseFailAlloc_3895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3895_, 0, v_a_3889_);
v___x_3894_ = v_reuseFailAlloc_3895_;
goto v_reusejp_3893_;
}
v_reusejp_3893_:
{
return v___x_3894_;
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
lean_object* v___x_3897_; lean_object* v___x_3898_; 
lean_dec(v_____x_3834_);
lean_dec_ref(v_e_3776_);
v___x_3897_ = lean_box(0);
v___x_3898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3898_, 0, v___x_3897_);
return v___x_3898_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe___boxed(lean_object* v_e_3919_, lean_object* v_eqTrue_3920_, lean_object* v_a_3921_, lean_object* v_a_3922_, lean_object* v_a_3923_, lean_object* v_a_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_, lean_object* v_a_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_){
_start:
{
uint8_t v_eqTrue_boxed_3933_; lean_object* v_res_3934_; 
v_eqTrue_boxed_3933_ = lean_unbox(v_eqTrue_3920_);
v_res_3934_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe(v_e_3919_, v_eqTrue_boxed_3933_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_, v_a_3931_);
lean_dec(v_a_3931_);
lean_dec_ref(v_a_3930_);
lean_dec(v_a_3929_);
lean_dec_ref(v_a_3928_);
lean_dec(v_a_3927_);
lean_dec_ref(v_a_3926_);
lean_dec(v_a_3925_);
lean_dec_ref(v_a_3924_);
lean_dec(v_a_3923_);
lean_dec(v_a_3922_);
lean_dec(v_a_3921_);
return v_res_3934_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe(lean_object* v_e_3940_, uint8_t v_eqTrue_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_){
_start:
{
lean_object* v___x_3956_; 
v___x_3956_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3944_);
if (lean_obj_tag(v___x_3956_) == 0)
{
lean_object* v_a_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3987_; 
v_a_3957_ = lean_ctor_get(v___x_3956_, 0);
v_isSharedCheck_3987_ = !lean_is_exclusive(v___x_3956_);
if (v_isSharedCheck_3987_ == 0)
{
v___x_3959_ = v___x_3956_;
v_isShared_3960_ = v_isSharedCheck_3987_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_a_3957_);
lean_dec(v___x_3956_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_3987_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
uint8_t v_lia_3961_; 
v_lia_3961_ = lean_ctor_get_uint8(v_a_3957_, sizeof(void*)*11 + 23);
lean_dec(v_a_3957_);
if (v_lia_3961_ == 0)
{
lean_object* v___x_3962_; lean_object* v___x_3964_; 
lean_dec_ref(v_e_3940_);
v___x_3962_ = lean_box(0);
if (v_isShared_3960_ == 0)
{
lean_ctor_set(v___x_3959_, 0, v___x_3962_);
v___x_3964_ = v___x_3959_;
goto v_reusejp_3963_;
}
else
{
lean_object* v_reuseFailAlloc_3965_; 
v_reuseFailAlloc_3965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3965_, 0, v___x_3962_);
v___x_3964_ = v_reuseFailAlloc_3965_;
goto v_reusejp_3963_;
}
v_reusejp_3963_:
{
return v___x_3964_;
}
}
else
{
lean_object* v___x_3966_; uint8_t v___x_3967_; 
lean_del_object(v___x_3959_);
lean_inc_ref(v_e_3940_);
v___x_3966_ = l_Lean_Expr_cleanupAnnotations(v_e_3940_);
v___x_3967_ = l_Lean_Expr_isApp(v___x_3966_);
if (v___x_3967_ == 0)
{
lean_dec_ref(v___x_3966_);
lean_dec_ref(v_e_3940_);
goto v___jp_3953_;
}
else
{
lean_object* v___x_3968_; uint8_t v___x_3969_; 
v___x_3968_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3966_);
v___x_3969_ = l_Lean_Expr_isApp(v___x_3968_);
if (v___x_3969_ == 0)
{
lean_dec_ref(v___x_3968_);
lean_dec_ref(v_e_3940_);
goto v___jp_3953_;
}
else
{
lean_object* v___x_3970_; uint8_t v___x_3971_; 
v___x_3970_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3968_);
v___x_3971_ = l_Lean_Expr_isApp(v___x_3970_);
if (v___x_3971_ == 0)
{
lean_dec_ref(v___x_3970_);
lean_dec_ref(v_e_3940_);
goto v___jp_3953_;
}
else
{
lean_object* v___x_3972_; uint8_t v___x_3973_; 
v___x_3972_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3970_);
v___x_3973_ = l_Lean_Expr_isApp(v___x_3972_);
if (v___x_3973_ == 0)
{
lean_dec_ref(v___x_3972_);
lean_dec_ref(v_e_3940_);
goto v___jp_3953_;
}
else
{
lean_object* v_arg_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; uint8_t v___x_3977_; 
v_arg_3974_ = lean_ctor_get(v___x_3972_, 1);
lean_inc_ref(v_arg_3974_);
v___x_3975_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3972_);
v___x_3976_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2));
v___x_3977_ = l_Lean_Expr_isConstOf(v___x_3975_, v___x_3976_);
lean_dec_ref(v___x_3975_);
if (v___x_3977_ == 0)
{
lean_dec_ref(v_arg_3974_);
lean_dec_ref(v_e_3940_);
goto v___jp_3953_;
}
else
{
lean_object* v___x_3978_; uint8_t v___x_3979_; 
v___x_3978_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__0));
v___x_3979_ = l_Lean_Expr_isConstOf(v_arg_3974_, v___x_3978_);
if (v___x_3979_ == 0)
{
lean_object* v___x_3980_; uint8_t v___x_3981_; 
v___x_3980_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__2));
v___x_3981_ = l_Lean_Expr_isConstOf(v_arg_3974_, v___x_3980_);
if (v___x_3981_ == 0)
{
lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; 
v___x_3982_ = lean_box(v_eqTrue_3941_);
v___x_3983_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe___boxed), 14, 2);
lean_closure_set(v___x_3983_, 0, v_e_3940_);
lean_closure_set(v___x_3983_, 1, v___x_3982_);
v___x_3984_ = l_Lean_Meta_Grind_Arith_Cutsat_ToIntM_run(v_arg_3974_, v___x_3983_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_);
return v___x_3984_;
}
else
{
lean_object* v___x_3985_; 
lean_dec_ref(v_arg_3974_);
v___x_3985_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe(v_e_3940_, v_eqTrue_3941_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_);
return v___x_3985_;
}
}
else
{
lean_object* v___x_3986_; 
lean_dec_ref(v_arg_3974_);
v___x_3986_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe(v_e_3940_, v_eqTrue_3941_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_);
return v___x_3986_;
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
lean_object* v_a_3988_; lean_object* v___x_3990_; uint8_t v_isShared_3991_; uint8_t v_isSharedCheck_3995_; 
lean_dec_ref(v_e_3940_);
v_a_3988_ = lean_ctor_get(v___x_3956_, 0);
v_isSharedCheck_3995_ = !lean_is_exclusive(v___x_3956_);
if (v_isSharedCheck_3995_ == 0)
{
v___x_3990_ = v___x_3956_;
v_isShared_3991_ = v_isSharedCheck_3995_;
goto v_resetjp_3989_;
}
else
{
lean_inc(v_a_3988_);
lean_dec(v___x_3956_);
v___x_3990_ = lean_box(0);
v_isShared_3991_ = v_isSharedCheck_3995_;
goto v_resetjp_3989_;
}
v_resetjp_3989_:
{
lean_object* v___x_3993_; 
if (v_isShared_3991_ == 0)
{
v___x_3993_ = v___x_3990_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v_a_3988_);
v___x_3993_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
return v___x_3993_;
}
}
}
v___jp_3953_:
{
lean_object* v___x_3954_; lean_object* v___x_3955_; 
v___x_3954_ = lean_box(0);
v___x_3955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3955_, 0, v___x_3954_);
return v___x_3955_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___boxed(lean_object* v_e_3996_, lean_object* v_eqTrue_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_){
_start:
{
uint8_t v_eqTrue_boxed_4009_; lean_object* v_res_4010_; 
v_eqTrue_boxed_4009_ = lean_unbox(v_eqTrue_3997_);
v_res_4010_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLe(v_e_3996_, v_eqTrue_boxed_4009_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_, v_a_4004_, v_a_4005_, v_a_4006_, v_a_4007_);
lean_dec(v_a_4007_);
lean_dec_ref(v_a_4006_);
lean_dec(v_a_4005_);
lean_dec_ref(v_a_4004_);
lean_dec(v_a_4003_);
lean_dec_ref(v_a_4002_);
lean_dec(v_a_4001_);
lean_dec_ref(v_a_4000_);
lean_dec(v_a_3999_);
lean_dec(v_a_3998_);
return v_res_4010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__0(lean_object* v_e_4011_, lean_object* v_arg_4012_, lean_object* v_arg_4013_, uint8_t v_eqTrue_4014_, lean_object* v_____x_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_){
_start:
{
if (lean_obj_tag(v_____x_4015_) == 1)
{
lean_object* v_val_4028_; lean_object* v___x_4029_; 
v_val_4028_ = lean_ctor_get(v_____x_4015_, 0);
lean_inc(v_val_4028_);
lean_dec_ref(v_____x_4015_);
v___x_4029_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_4011_, v___y_4017_);
if (lean_obj_tag(v___x_4029_) == 0)
{
lean_object* v_a_4030_; lean_object* v___x_4031_; 
v_a_4030_ = lean_ctor_get(v___x_4029_, 0);
lean_inc(v_a_4030_);
lean_dec_ref(v___x_4029_);
lean_inc_ref(v_arg_4012_);
v___x_4031_ = l_Lean_Meta_Grind_Arith_Cutsat_toInt(v_arg_4012_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_);
if (lean_obj_tag(v___x_4031_) == 0)
{
lean_object* v_a_4032_; lean_object* v_fst_4033_; lean_object* v_snd_4034_; lean_object* v___x_4036_; uint8_t v_isShared_4037_; uint8_t v_isSharedCheck_4089_; 
v_a_4032_ = lean_ctor_get(v___x_4031_, 0);
lean_inc(v_a_4032_);
lean_dec_ref(v___x_4031_);
v_fst_4033_ = lean_ctor_get(v_a_4032_, 0);
v_snd_4034_ = lean_ctor_get(v_a_4032_, 1);
v_isSharedCheck_4089_ = !lean_is_exclusive(v_a_4032_);
if (v_isSharedCheck_4089_ == 0)
{
v___x_4036_ = v_a_4032_;
v_isShared_4037_ = v_isSharedCheck_4089_;
goto v_resetjp_4035_;
}
else
{
lean_inc(v_snd_4034_);
lean_inc(v_fst_4033_);
lean_dec(v_a_4032_);
v___x_4036_ = lean_box(0);
v_isShared_4037_ = v_isSharedCheck_4089_;
goto v_resetjp_4035_;
}
v_resetjp_4035_:
{
lean_object* v___x_4038_; 
lean_inc_ref(v_arg_4013_);
v___x_4038_ = l_Lean_Meta_Grind_Arith_Cutsat_toInt(v_arg_4013_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_);
if (lean_obj_tag(v___x_4038_) == 0)
{
lean_object* v_a_4039_; lean_object* v_fst_4040_; lean_object* v_snd_4041_; lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4080_; 
v_a_4039_ = lean_ctor_get(v___x_4038_, 0);
lean_inc(v_a_4039_);
lean_dec_ref(v___x_4038_);
v_fst_4040_ = lean_ctor_get(v_a_4039_, 0);
v_snd_4041_ = lean_ctor_get(v_a_4039_, 1);
v_isSharedCheck_4080_ = !lean_is_exclusive(v_a_4039_);
if (v_isSharedCheck_4080_ == 0)
{
v___x_4043_ = v_a_4039_;
v_isShared_4044_ = v_isSharedCheck_4080_;
goto v_resetjp_4042_;
}
else
{
lean_inc(v_snd_4041_);
lean_inc(v_fst_4040_);
lean_dec(v_a_4039_);
v___x_4043_ = lean_box(0);
v_isShared_4044_ = v_isSharedCheck_4080_;
goto v_resetjp_4042_;
}
v_resetjp_4042_:
{
lean_object* v___x_4045_; lean_object* v_fst_4047_; lean_object* v_snd_4048_; 
lean_inc(v_fst_4040_);
lean_inc(v_fst_4033_);
v___x_4045_ = l_Lean_mkApp6(v_val_4028_, v_arg_4012_, v_arg_4013_, v_fst_4033_, v_fst_4040_, v_snd_4034_, v_snd_4041_);
if (v_eqTrue_4014_ == 0)
{
v_fst_4047_ = v_fst_4040_;
v_snd_4048_ = v_fst_4033_;
goto v___jp_4046_;
}
else
{
lean_object* v___x_4078_; lean_object* v___x_4079_; 
v___x_4078_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0);
v___x_4079_ = l_Lean_mkIntAdd(v_fst_4033_, v___x_4078_);
v_fst_4047_ = v___x_4079_;
v_snd_4048_ = v_fst_4040_;
goto v___jp_4046_;
}
v___jp_4046_:
{
lean_object* v___x_4049_; 
lean_inc(v_a_4030_);
v___x_4049_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_4047_, v_a_4030_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_);
if (lean_obj_tag(v___x_4049_) == 0)
{
lean_object* v_a_4050_; lean_object* v___x_4051_; 
v_a_4050_ = lean_ctor_get(v___x_4049_, 0);
lean_inc(v_a_4050_);
lean_dec_ref(v___x_4049_);
v___x_4051_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_snd_4048_, v_a_4030_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_);
if (lean_obj_tag(v___x_4051_) == 0)
{
lean_object* v_a_4052_; lean_object* v___x_4054_; 
v_a_4052_ = lean_ctor_get(v___x_4051_, 0);
lean_inc_n(v_a_4052_, 2);
lean_dec_ref(v___x_4051_);
lean_inc(v_a_4050_);
if (v_isShared_4044_ == 0)
{
lean_ctor_set_tag(v___x_4043_, 3);
lean_ctor_set(v___x_4043_, 1, v_a_4052_);
lean_ctor_set(v___x_4043_, 0, v_a_4050_);
v___x_4054_ = v___x_4043_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4061_; 
v_reuseFailAlloc_4061_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4061_, 0, v_a_4050_);
lean_ctor_set(v_reuseFailAlloc_4061_, 1, v_a_4052_);
v___x_4054_ = v_reuseFailAlloc_4061_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4058_; 
v___x_4055_ = l_Int_Linear_Expr_norm(v___x_4054_);
lean_dec_ref(v___x_4054_);
v___x_4056_ = lean_alloc_ctor(2, 4, 1);
lean_ctor_set(v___x_4056_, 0, v_e_4011_);
lean_ctor_set(v___x_4056_, 1, v___x_4045_);
lean_ctor_set(v___x_4056_, 2, v_a_4050_);
lean_ctor_set(v___x_4056_, 3, v_a_4052_);
lean_ctor_set_uint8(v___x_4056_, sizeof(void*)*4, v_eqTrue_4014_);
if (v_isShared_4037_ == 0)
{
lean_ctor_set(v___x_4036_, 1, v___x_4056_);
lean_ctor_set(v___x_4036_, 0, v___x_4055_);
v___x_4058_ = v___x_4036_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v___x_4055_);
lean_ctor_set(v_reuseFailAlloc_4060_, 1, v___x_4056_);
v___x_4058_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4057_;
}
v_reusejp_4057_:
{
lean_object* v___x_4059_; 
lean_inc(v___y_4026_);
lean_inc_ref(v___y_4025_);
lean_inc(v___y_4024_);
lean_inc_ref(v___y_4023_);
lean_inc(v___y_4022_);
lean_inc_ref(v___y_4021_);
lean_inc(v___y_4020_);
lean_inc_ref(v___y_4019_);
lean_inc(v___y_4018_);
lean_inc(v___y_4017_);
v___x_4059_ = lean_grind_cutsat_assert_le(v___x_4058_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_);
return v___x_4059_;
}
}
}
else
{
lean_object* v_a_4062_; lean_object* v___x_4064_; uint8_t v_isShared_4065_; uint8_t v_isSharedCheck_4069_; 
lean_dec(v_a_4050_);
lean_dec_ref(v___x_4045_);
lean_del_object(v___x_4043_);
lean_del_object(v___x_4036_);
lean_dec_ref(v_e_4011_);
v_a_4062_ = lean_ctor_get(v___x_4051_, 0);
v_isSharedCheck_4069_ = !lean_is_exclusive(v___x_4051_);
if (v_isSharedCheck_4069_ == 0)
{
v___x_4064_ = v___x_4051_;
v_isShared_4065_ = v_isSharedCheck_4069_;
goto v_resetjp_4063_;
}
else
{
lean_inc(v_a_4062_);
lean_dec(v___x_4051_);
v___x_4064_ = lean_box(0);
v_isShared_4065_ = v_isSharedCheck_4069_;
goto v_resetjp_4063_;
}
v_resetjp_4063_:
{
lean_object* v___x_4067_; 
if (v_isShared_4065_ == 0)
{
v___x_4067_ = v___x_4064_;
goto v_reusejp_4066_;
}
else
{
lean_object* v_reuseFailAlloc_4068_; 
v_reuseFailAlloc_4068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4068_, 0, v_a_4062_);
v___x_4067_ = v_reuseFailAlloc_4068_;
goto v_reusejp_4066_;
}
v_reusejp_4066_:
{
return v___x_4067_;
}
}
}
}
else
{
lean_object* v_a_4070_; lean_object* v___x_4072_; uint8_t v_isShared_4073_; uint8_t v_isSharedCheck_4077_; 
lean_dec_ref(v_snd_4048_);
lean_dec_ref(v___x_4045_);
lean_del_object(v___x_4043_);
lean_del_object(v___x_4036_);
lean_dec(v_a_4030_);
lean_dec_ref(v_e_4011_);
v_a_4070_ = lean_ctor_get(v___x_4049_, 0);
v_isSharedCheck_4077_ = !lean_is_exclusive(v___x_4049_);
if (v_isSharedCheck_4077_ == 0)
{
v___x_4072_ = v___x_4049_;
v_isShared_4073_ = v_isSharedCheck_4077_;
goto v_resetjp_4071_;
}
else
{
lean_inc(v_a_4070_);
lean_dec(v___x_4049_);
v___x_4072_ = lean_box(0);
v_isShared_4073_ = v_isSharedCheck_4077_;
goto v_resetjp_4071_;
}
v_resetjp_4071_:
{
lean_object* v___x_4075_; 
if (v_isShared_4073_ == 0)
{
v___x_4075_ = v___x_4072_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v_a_4070_);
v___x_4075_ = v_reuseFailAlloc_4076_;
goto v_reusejp_4074_;
}
v_reusejp_4074_:
{
return v___x_4075_;
}
}
}
}
}
}
else
{
lean_object* v_a_4081_; lean_object* v___x_4083_; uint8_t v_isShared_4084_; uint8_t v_isSharedCheck_4088_; 
lean_del_object(v___x_4036_);
lean_dec(v_snd_4034_);
lean_dec(v_fst_4033_);
lean_dec(v_a_4030_);
lean_dec(v_val_4028_);
lean_dec_ref(v_arg_4013_);
lean_dec_ref(v_arg_4012_);
lean_dec_ref(v_e_4011_);
v_a_4081_ = lean_ctor_get(v___x_4038_, 0);
v_isSharedCheck_4088_ = !lean_is_exclusive(v___x_4038_);
if (v_isSharedCheck_4088_ == 0)
{
v___x_4083_ = v___x_4038_;
v_isShared_4084_ = v_isSharedCheck_4088_;
goto v_resetjp_4082_;
}
else
{
lean_inc(v_a_4081_);
lean_dec(v___x_4038_);
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
else
{
lean_object* v_a_4090_; lean_object* v___x_4092_; uint8_t v_isShared_4093_; uint8_t v_isSharedCheck_4097_; 
lean_dec(v_a_4030_);
lean_dec(v_val_4028_);
lean_dec_ref(v_arg_4013_);
lean_dec_ref(v_arg_4012_);
lean_dec_ref(v_e_4011_);
v_a_4090_ = lean_ctor_get(v___x_4031_, 0);
v_isSharedCheck_4097_ = !lean_is_exclusive(v___x_4031_);
if (v_isSharedCheck_4097_ == 0)
{
v___x_4092_ = v___x_4031_;
v_isShared_4093_ = v_isSharedCheck_4097_;
goto v_resetjp_4091_;
}
else
{
lean_inc(v_a_4090_);
lean_dec(v___x_4031_);
v___x_4092_ = lean_box(0);
v_isShared_4093_ = v_isSharedCheck_4097_;
goto v_resetjp_4091_;
}
v_resetjp_4091_:
{
lean_object* v___x_4095_; 
if (v_isShared_4093_ == 0)
{
v___x_4095_ = v___x_4092_;
goto v_reusejp_4094_;
}
else
{
lean_object* v_reuseFailAlloc_4096_; 
v_reuseFailAlloc_4096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4096_, 0, v_a_4090_);
v___x_4095_ = v_reuseFailAlloc_4096_;
goto v_reusejp_4094_;
}
v_reusejp_4094_:
{
return v___x_4095_;
}
}
}
}
else
{
lean_object* v_a_4098_; lean_object* v___x_4100_; uint8_t v_isShared_4101_; uint8_t v_isSharedCheck_4105_; 
lean_dec(v_val_4028_);
lean_dec_ref(v_arg_4013_);
lean_dec_ref(v_arg_4012_);
lean_dec_ref(v_e_4011_);
v_a_4098_ = lean_ctor_get(v___x_4029_, 0);
v_isSharedCheck_4105_ = !lean_is_exclusive(v___x_4029_);
if (v_isSharedCheck_4105_ == 0)
{
v___x_4100_ = v___x_4029_;
v_isShared_4101_ = v_isSharedCheck_4105_;
goto v_resetjp_4099_;
}
else
{
lean_inc(v_a_4098_);
lean_dec(v___x_4029_);
v___x_4100_ = lean_box(0);
v_isShared_4101_ = v_isSharedCheck_4105_;
goto v_resetjp_4099_;
}
v_resetjp_4099_:
{
lean_object* v___x_4103_; 
if (v_isShared_4101_ == 0)
{
v___x_4103_ = v___x_4100_;
goto v_reusejp_4102_;
}
else
{
lean_object* v_reuseFailAlloc_4104_; 
v_reuseFailAlloc_4104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4104_, 0, v_a_4098_);
v___x_4103_ = v_reuseFailAlloc_4104_;
goto v_reusejp_4102_;
}
v_reusejp_4102_:
{
return v___x_4103_;
}
}
}
}
else
{
lean_object* v___x_4106_; lean_object* v___x_4107_; 
lean_dec(v_____x_4015_);
lean_dec_ref(v_arg_4013_);
lean_dec_ref(v_arg_4012_);
lean_dec_ref(v_e_4011_);
v___x_4106_ = lean_box(0);
v___x_4107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4107_, 0, v___x_4106_);
return v___x_4107_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__0___boxed(lean_object** _args){
lean_object* v_e_4108_ = _args[0];
lean_object* v_arg_4109_ = _args[1];
lean_object* v_arg_4110_ = _args[2];
lean_object* v_eqTrue_4111_ = _args[3];
lean_object* v_____x_4112_ = _args[4];
lean_object* v___y_4113_ = _args[5];
lean_object* v___y_4114_ = _args[6];
lean_object* v___y_4115_ = _args[7];
lean_object* v___y_4116_ = _args[8];
lean_object* v___y_4117_ = _args[9];
lean_object* v___y_4118_ = _args[10];
lean_object* v___y_4119_ = _args[11];
lean_object* v___y_4120_ = _args[12];
lean_object* v___y_4121_ = _args[13];
lean_object* v___y_4122_ = _args[14];
lean_object* v___y_4123_ = _args[15];
lean_object* v___y_4124_ = _args[16];
_start:
{
uint8_t v_eqTrue_boxed_4125_; lean_object* v_res_4126_; 
v_eqTrue_boxed_4125_ = lean_unbox(v_eqTrue_4111_);
v_res_4126_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__0(v_e_4108_, v_arg_4109_, v_arg_4110_, v_eqTrue_boxed_4125_, v_____x_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_);
lean_dec(v___y_4123_);
lean_dec_ref(v___y_4122_);
lean_dec(v___y_4121_);
lean_dec_ref(v___y_4120_);
lean_dec(v___y_4119_);
lean_dec_ref(v___y_4118_);
lean_dec(v___y_4117_);
lean_dec_ref(v___y_4116_);
lean_dec(v___y_4115_);
lean_dec(v___y_4114_);
lean_dec(v___y_4113_);
return v_res_4126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__1(uint8_t v_eqTrue_4127_, lean_object* v___f_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_){
_start:
{
if (v_eqTrue_4127_ == 0)
{
lean_object* v___x_4141_; 
v___x_4141_ = l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLT_x3f___redArg(v___y_4129_, v___y_4130_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_);
if (lean_obj_tag(v___x_4141_) == 0)
{
lean_object* v_a_4142_; lean_object* v___x_4143_; 
v_a_4142_ = lean_ctor_get(v___x_4141_, 0);
lean_inc(v_a_4142_);
lean_dec_ref(v___x_4141_);
lean_inc(v___y_4139_);
lean_inc_ref(v___y_4138_);
lean_inc(v___y_4137_);
lean_inc_ref(v___y_4136_);
lean_inc(v___y_4135_);
lean_inc_ref(v___y_4134_);
lean_inc(v___y_4133_);
lean_inc_ref(v___y_4132_);
lean_inc(v___y_4131_);
lean_inc(v___y_4130_);
lean_inc(v___y_4129_);
v___x_4143_ = lean_apply_13(v___f_4128_, v_a_4142_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_, lean_box(0));
return v___x_4143_;
}
else
{
lean_object* v_a_4144_; lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4151_; 
lean_dec_ref(v___f_4128_);
v_a_4144_ = lean_ctor_get(v___x_4141_, 0);
v_isSharedCheck_4151_ = !lean_is_exclusive(v___x_4141_);
if (v_isSharedCheck_4151_ == 0)
{
v___x_4146_ = v___x_4141_;
v_isShared_4147_ = v_isSharedCheck_4151_;
goto v_resetjp_4145_;
}
else
{
lean_inc(v_a_4144_);
lean_dec(v___x_4141_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4151_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
lean_object* v___x_4149_; 
if (v_isShared_4147_ == 0)
{
v___x_4149_ = v___x_4146_;
goto v_reusejp_4148_;
}
else
{
lean_object* v_reuseFailAlloc_4150_; 
v_reuseFailAlloc_4150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4150_, 0, v_a_4144_);
v___x_4149_ = v_reuseFailAlloc_4150_;
goto v_reusejp_4148_;
}
v_reusejp_4148_:
{
return v___x_4149_;
}
}
}
}
else
{
lean_object* v___x_4152_; 
v___x_4152_ = l_Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f___redArg(v___y_4129_, v___y_4130_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_);
if (lean_obj_tag(v___x_4152_) == 0)
{
lean_object* v_a_4153_; lean_object* v___x_4154_; 
v_a_4153_ = lean_ctor_get(v___x_4152_, 0);
lean_inc(v_a_4153_);
lean_dec_ref(v___x_4152_);
lean_inc(v___y_4139_);
lean_inc_ref(v___y_4138_);
lean_inc(v___y_4137_);
lean_inc_ref(v___y_4136_);
lean_inc(v___y_4135_);
lean_inc_ref(v___y_4134_);
lean_inc(v___y_4133_);
lean_inc_ref(v___y_4132_);
lean_inc(v___y_4131_);
lean_inc(v___y_4130_);
lean_inc(v___y_4129_);
v___x_4154_ = lean_apply_13(v___f_4128_, v_a_4153_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_, lean_box(0));
return v___x_4154_;
}
else
{
lean_object* v_a_4155_; lean_object* v___x_4157_; uint8_t v_isShared_4158_; uint8_t v_isSharedCheck_4162_; 
lean_dec_ref(v___f_4128_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__1___boxed(lean_object* v_eqTrue_4163_, lean_object* v___f_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_){
_start:
{
uint8_t v_eqTrue_boxed_4177_; lean_object* v_res_4178_; 
v_eqTrue_boxed_4177_ = lean_unbox(v_eqTrue_4163_);
v_res_4178_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__1(v_eqTrue_boxed_4177_, v___f_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_);
lean_dec(v___y_4175_);
lean_dec_ref(v___y_4174_);
lean_dec(v___y_4173_);
lean_dec_ref(v___y_4172_);
lean_dec(v___y_4171_);
lean_dec_ref(v___y_4170_);
lean_dec(v___y_4169_);
lean_dec_ref(v___y_4168_);
lean_dec(v___y_4167_);
lean_dec(v___y_4166_);
lean_dec(v___y_4165_);
return v_res_4178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt(lean_object* v_e_4184_, uint8_t v_eqTrue_4185_, lean_object* v_a_4186_, lean_object* v_a_4187_, lean_object* v_a_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_){
_start:
{
lean_object* v___x_4200_; 
v___x_4200_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_4188_);
if (lean_obj_tag(v___x_4200_) == 0)
{
lean_object* v_a_4201_; lean_object* v___x_4203_; uint8_t v_isShared_4204_; uint8_t v_isSharedCheck_4229_; 
v_a_4201_ = lean_ctor_get(v___x_4200_, 0);
v_isSharedCheck_4229_ = !lean_is_exclusive(v___x_4200_);
if (v_isSharedCheck_4229_ == 0)
{
v___x_4203_ = v___x_4200_;
v_isShared_4204_ = v_isSharedCheck_4229_;
goto v_resetjp_4202_;
}
else
{
lean_inc(v_a_4201_);
lean_dec(v___x_4200_);
v___x_4203_ = lean_box(0);
v_isShared_4204_ = v_isSharedCheck_4229_;
goto v_resetjp_4202_;
}
v_resetjp_4202_:
{
uint8_t v_lia_4205_; 
v_lia_4205_ = lean_ctor_get_uint8(v_a_4201_, sizeof(void*)*11 + 23);
lean_dec(v_a_4201_);
if (v_lia_4205_ == 0)
{
lean_object* v___x_4206_; lean_object* v___x_4208_; 
lean_dec_ref(v_e_4184_);
v___x_4206_ = lean_box(0);
if (v_isShared_4204_ == 0)
{
lean_ctor_set(v___x_4203_, 0, v___x_4206_);
v___x_4208_ = v___x_4203_;
goto v_reusejp_4207_;
}
else
{
lean_object* v_reuseFailAlloc_4209_; 
v_reuseFailAlloc_4209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4209_, 0, v___x_4206_);
v___x_4208_ = v_reuseFailAlloc_4209_;
goto v_reusejp_4207_;
}
v_reusejp_4207_:
{
return v___x_4208_;
}
}
else
{
lean_object* v___x_4210_; uint8_t v___x_4211_; 
lean_del_object(v___x_4203_);
lean_inc_ref(v_e_4184_);
v___x_4210_ = l_Lean_Expr_cleanupAnnotations(v_e_4184_);
v___x_4211_ = l_Lean_Expr_isApp(v___x_4210_);
if (v___x_4211_ == 0)
{
lean_dec_ref(v___x_4210_);
lean_dec_ref(v_e_4184_);
goto v___jp_4197_;
}
else
{
lean_object* v_arg_4212_; lean_object* v___x_4213_; uint8_t v___x_4214_; 
v_arg_4212_ = lean_ctor_get(v___x_4210_, 1);
lean_inc_ref(v_arg_4212_);
v___x_4213_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4210_);
v___x_4214_ = l_Lean_Expr_isApp(v___x_4213_);
if (v___x_4214_ == 0)
{
lean_dec_ref(v___x_4213_);
lean_dec_ref(v_arg_4212_);
lean_dec_ref(v_e_4184_);
goto v___jp_4197_;
}
else
{
lean_object* v_arg_4215_; lean_object* v___x_4216_; uint8_t v___x_4217_; 
v_arg_4215_ = lean_ctor_get(v___x_4213_, 1);
lean_inc_ref(v_arg_4215_);
v___x_4216_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4213_);
v___x_4217_ = l_Lean_Expr_isApp(v___x_4216_);
if (v___x_4217_ == 0)
{
lean_dec_ref(v___x_4216_);
lean_dec_ref(v_arg_4215_);
lean_dec_ref(v_arg_4212_);
lean_dec_ref(v_e_4184_);
goto v___jp_4197_;
}
else
{
lean_object* v___x_4218_; uint8_t v___x_4219_; 
v___x_4218_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4216_);
v___x_4219_ = l_Lean_Expr_isApp(v___x_4218_);
if (v___x_4219_ == 0)
{
lean_dec_ref(v___x_4218_);
lean_dec_ref(v_arg_4215_);
lean_dec_ref(v_arg_4212_);
lean_dec_ref(v_e_4184_);
goto v___jp_4197_;
}
else
{
lean_object* v_arg_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; uint8_t v___x_4223_; 
v_arg_4220_ = lean_ctor_get(v___x_4218_, 1);
lean_inc_ref(v_arg_4220_);
v___x_4221_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4218_);
v___x_4222_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__2));
v___x_4223_ = l_Lean_Expr_isConstOf(v___x_4221_, v___x_4222_);
lean_dec_ref(v___x_4221_);
if (v___x_4223_ == 0)
{
lean_dec_ref(v_arg_4220_);
lean_dec_ref(v_arg_4215_);
lean_dec_ref(v_arg_4212_);
lean_dec_ref(v_e_4184_);
goto v___jp_4197_;
}
else
{
lean_object* v___x_4224_; lean_object* v___f_4225_; lean_object* v___x_4226_; lean_object* v___y_4227_; lean_object* v___x_4228_; 
v___x_4224_ = lean_box(v_eqTrue_4185_);
v___f_4225_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__0___boxed), 17, 4);
lean_closure_set(v___f_4225_, 0, v_e_4184_);
lean_closure_set(v___f_4225_, 1, v_arg_4215_);
lean_closure_set(v___f_4225_, 2, v_arg_4212_);
lean_closure_set(v___f_4225_, 3, v___x_4224_);
v___x_4226_ = lean_box(v_eqTrue_4185_);
v___y_4227_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__1___boxed), 14, 2);
lean_closure_set(v___y_4227_, 0, v___x_4226_);
lean_closure_set(v___y_4227_, 1, v___f_4225_);
v___x_4228_ = l_Lean_Meta_Grind_Arith_Cutsat_ToIntM_run(v_arg_4220_, v___y_4227_, v_a_4186_, v_a_4187_, v_a_4188_, v_a_4189_, v_a_4190_, v_a_4191_, v_a_4192_, v_a_4193_, v_a_4194_, v_a_4195_);
return v___x_4228_;
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
lean_object* v_a_4230_; lean_object* v___x_4232_; uint8_t v_isShared_4233_; uint8_t v_isSharedCheck_4237_; 
lean_dec_ref(v_e_4184_);
v_a_4230_ = lean_ctor_get(v___x_4200_, 0);
v_isSharedCheck_4237_ = !lean_is_exclusive(v___x_4200_);
if (v_isSharedCheck_4237_ == 0)
{
v___x_4232_ = v___x_4200_;
v_isShared_4233_ = v_isSharedCheck_4237_;
goto v_resetjp_4231_;
}
else
{
lean_inc(v_a_4230_);
lean_dec(v___x_4200_);
v___x_4232_ = lean_box(0);
v_isShared_4233_ = v_isSharedCheck_4237_;
goto v_resetjp_4231_;
}
v_resetjp_4231_:
{
lean_object* v___x_4235_; 
if (v_isShared_4233_ == 0)
{
v___x_4235_ = v___x_4232_;
goto v_reusejp_4234_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v_a_4230_);
v___x_4235_ = v_reuseFailAlloc_4236_;
goto v_reusejp_4234_;
}
v_reusejp_4234_:
{
return v___x_4235_;
}
}
}
v___jp_4197_:
{
lean_object* v___x_4198_; lean_object* v___x_4199_; 
v___x_4198_ = lean_box(0);
v___x_4199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4199_, 0, v___x_4198_);
return v___x_4199_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___boxed(lean_object* v_e_4238_, lean_object* v_eqTrue_4239_, lean_object* v_a_4240_, lean_object* v_a_4241_, lean_object* v_a_4242_, lean_object* v_a_4243_, lean_object* v_a_4244_, lean_object* v_a_4245_, lean_object* v_a_4246_, lean_object* v_a_4247_, lean_object* v_a_4248_, lean_object* v_a_4249_, lean_object* v_a_4250_){
_start:
{
uint8_t v_eqTrue_boxed_4251_; lean_object* v_res_4252_; 
v_eqTrue_boxed_4251_ = lean_unbox(v_eqTrue_4239_);
v_res_4252_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLt(v_e_4238_, v_eqTrue_boxed_4251_, v_a_4240_, v_a_4241_, v_a_4242_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_, v_a_4247_, v_a_4248_, v_a_4249_);
lean_dec(v_a_4249_);
lean_dec_ref(v_a_4248_);
lean_dec(v_a_4247_);
lean_dec_ref(v_a_4246_);
lean_dec(v_a_4245_);
lean_dec_ref(v_a_4244_);
lean_dec(v_a_4243_);
lean_dec_ref(v_a_4242_);
lean_dec(v_a_4241_);
lean_dec(v_a_4240_);
return v_res_4252_;
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
