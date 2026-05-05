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
lean_object* v_cs_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; size_t v_sz_1108_; size_t v___x_1109_; lean_object* v___x_1110_; 
v_cs_1105_ = lean_ctor_get(v_n_1092_, 0);
v___x_1106_ = lean_box(0);
v___x_1107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1106_);
lean_ctor_set(v___x_1107_, 1, v_b_1093_);
v_sz_1108_ = lean_array_size(v_cs_1105_);
v___x_1109_ = ((size_t)0ULL);
v___x_1110_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(v_init_1089_, v___x_1090_, v_c_1091_, v_cs_1105_, v_sz_1108_, v___x_1109_, v___x_1107_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1125_; 
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1113_ = v___x_1110_;
v_isShared_1114_ = v_isSharedCheck_1125_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1110_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1125_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v_fst_1115_; 
v_fst_1115_ = lean_ctor_get(v_a_1111_, 0);
if (lean_obj_tag(v_fst_1115_) == 0)
{
lean_object* v_snd_1116_; lean_object* v___x_1117_; lean_object* v___x_1119_; 
v_snd_1116_ = lean_ctor_get(v_a_1111_, 1);
lean_inc(v_snd_1116_);
lean_dec(v_a_1111_);
v___x_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1117_, 0, v_snd_1116_);
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 0, v___x_1117_);
v___x_1119_ = v___x_1113_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v___x_1117_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
else
{
lean_object* v_val_1121_; lean_object* v___x_1123_; 
lean_inc_ref(v_fst_1115_);
lean_dec(v_a_1111_);
v_val_1121_ = lean_ctor_get(v_fst_1115_, 0);
lean_inc(v_val_1121_);
lean_dec_ref(v_fst_1115_);
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 0, v_val_1121_);
v___x_1123_ = v___x_1113_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_val_1121_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
}
else
{
lean_object* v_a_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1133_; 
v_a_1126_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1133_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1133_ == 0)
{
v___x_1128_ = v___x_1110_;
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_a_1126_);
lean_dec(v___x_1110_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1133_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1131_; 
if (v_isShared_1129_ == 0)
{
v___x_1131_ = v___x_1128_;
goto v_reusejp_1130_;
}
else
{
lean_object* v_reuseFailAlloc_1132_; 
v_reuseFailAlloc_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1132_, 0, v_a_1126_);
v___x_1131_ = v_reuseFailAlloc_1132_;
goto v_reusejp_1130_;
}
v_reusejp_1130_:
{
return v___x_1131_;
}
}
}
}
else
{
lean_object* v_vs_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; size_t v_sz_1137_; size_t v___x_1138_; lean_object* v___x_1139_; 
v_vs_1134_ = lean_ctor_get(v_n_1092_, 0);
v___x_1135_ = lean_box(0);
v___x_1136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1135_);
lean_ctor_set(v___x_1136_, 1, v_b_1093_);
v_sz_1137_ = lean_array_size(v_vs_1134_);
v___x_1138_ = ((size_t)0ULL);
v___x_1139_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2(v___x_1090_, v_c_1091_, v_vs_1134_, v_sz_1137_, v___x_1138_, v___x_1136_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1154_; 
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1142_ = v___x_1139_;
v_isShared_1143_ = v_isSharedCheck_1154_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_a_1140_);
lean_dec(v___x_1139_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1154_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v_fst_1144_; 
v_fst_1144_ = lean_ctor_get(v_a_1140_, 0);
if (lean_obj_tag(v_fst_1144_) == 0)
{
lean_object* v_snd_1145_; lean_object* v___x_1146_; lean_object* v___x_1148_; 
v_snd_1145_ = lean_ctor_get(v_a_1140_, 1);
lean_inc(v_snd_1145_);
lean_dec(v_a_1140_);
v___x_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1146_, 0, v_snd_1145_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 0, v___x_1146_);
v___x_1148_ = v___x_1142_;
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
lean_object* v_val_1150_; lean_object* v___x_1152_; 
lean_inc_ref(v_fst_1144_);
lean_dec(v_a_1140_);
v_val_1150_ = lean_ctor_get(v_fst_1144_, 0);
lean_inc(v_val_1150_);
lean_dec_ref(v_fst_1144_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 0, v_val_1150_);
v___x_1152_ = v___x_1142_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_val_1150_);
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
else
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1162_; 
v_a_1155_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1157_ = v___x_1139_;
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1139_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1160_; 
if (v_isShared_1158_ == 0)
{
v___x_1160_ = v___x_1157_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_a_1155_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(lean_object* v_init_1163_, lean_object* v___x_1164_, lean_object* v_c_1165_, lean_object* v_as_1166_, size_t v_sz_1167_, size_t v_i_1168_, lean_object* v_b_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_){
_start:
{
uint8_t v___x_1181_; 
v___x_1181_ = lean_usize_dec_lt(v_i_1168_, v_sz_1167_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1182_; 
lean_dec_ref(v_c_1165_);
lean_dec_ref(v___x_1164_);
v___x_1182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1182_, 0, v_b_1169_);
return v___x_1182_;
}
else
{
lean_object* v_snd_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1217_; 
v_snd_1183_ = lean_ctor_get(v_b_1169_, 1);
v_isSharedCheck_1217_ = !lean_is_exclusive(v_b_1169_);
if (v_isSharedCheck_1217_ == 0)
{
lean_object* v_unused_1218_; 
v_unused_1218_ = lean_ctor_get(v_b_1169_, 0);
lean_dec(v_unused_1218_);
v___x_1185_ = v_b_1169_;
v_isShared_1186_ = v_isSharedCheck_1217_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_snd_1183_);
lean_dec(v_b_1169_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1217_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v_a_1187_; lean_object* v___x_1188_; 
v_a_1187_ = lean_array_uget_borrowed(v_as_1166_, v_i_1168_);
lean_inc(v_snd_1183_);
lean_inc_ref(v_c_1165_);
lean_inc_ref(v___x_1164_);
v___x_1188_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(v_init_1163_, v___x_1164_, v_c_1165_, v_a_1187_, v_snd_1183_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_);
if (lean_obj_tag(v___x_1188_) == 0)
{
lean_object* v_a_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1208_; 
v_a_1189_ = lean_ctor_get(v___x_1188_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1191_ = v___x_1188_;
v_isShared_1192_ = v_isSharedCheck_1208_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_a_1189_);
lean_dec(v___x_1188_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1208_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
if (lean_obj_tag(v_a_1189_) == 0)
{
lean_object* v___x_1193_; lean_object* v___x_1195_; 
lean_dec_ref(v_c_1165_);
lean_dec_ref(v___x_1164_);
v___x_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1193_, 0, v_a_1189_);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 0, v___x_1193_);
v___x_1195_ = v___x_1185_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1193_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v_snd_1183_);
v___x_1195_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
lean_object* v___x_1197_; 
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 0, v___x_1195_);
v___x_1197_ = v___x_1191_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v___x_1195_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
else
{
lean_object* v_a_1200_; lean_object* v___x_1201_; lean_object* v___x_1203_; 
lean_del_object(v___x_1191_);
lean_dec(v_snd_1183_);
v_a_1200_ = lean_ctor_get(v_a_1189_, 0);
lean_inc(v_a_1200_);
lean_dec_ref(v_a_1189_);
v___x_1201_ = lean_box(0);
if (v_isShared_1186_ == 0)
{
lean_ctor_set(v___x_1185_, 1, v_a_1200_);
lean_ctor_set(v___x_1185_, 0, v___x_1201_);
v___x_1203_ = v___x_1185_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1201_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v_a_1200_);
v___x_1203_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
size_t v___x_1204_; size_t v___x_1205_; 
v___x_1204_ = ((size_t)1ULL);
v___x_1205_ = lean_usize_add(v_i_1168_, v___x_1204_);
v_i_1168_ = v___x_1205_;
v_b_1169_ = v___x_1203_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
lean_del_object(v___x_1185_);
lean_dec(v_snd_1183_);
lean_dec_ref(v_c_1165_);
lean_dec_ref(v___x_1164_);
v_a_1209_ = lean_ctor_get(v___x_1188_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1211_ = v___x_1188_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1188_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_init_1219_ = _args[0];
lean_object* v___x_1220_ = _args[1];
lean_object* v_c_1221_ = _args[2];
lean_object* v_as_1222_ = _args[3];
lean_object* v_sz_1223_ = _args[4];
lean_object* v_i_1224_ = _args[5];
lean_object* v_b_1225_ = _args[6];
lean_object* v___y_1226_ = _args[7];
lean_object* v___y_1227_ = _args[8];
lean_object* v___y_1228_ = _args[9];
lean_object* v___y_1229_ = _args[10];
lean_object* v___y_1230_ = _args[11];
lean_object* v___y_1231_ = _args[12];
lean_object* v___y_1232_ = _args[13];
lean_object* v___y_1233_ = _args[14];
lean_object* v___y_1234_ = _args[15];
lean_object* v___y_1235_ = _args[16];
lean_object* v___y_1236_ = _args[17];
_start:
{
size_t v_sz_boxed_1237_; size_t v_i_boxed_1238_; lean_object* v_res_1239_; 
v_sz_boxed_1237_ = lean_unbox_usize(v_sz_1223_);
lean_dec(v_sz_1223_);
v_i_boxed_1238_ = lean_unbox_usize(v_i_1224_);
lean_dec(v_i_1224_);
v_res_1239_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(v_init_1219_, v___x_1220_, v_c_1221_, v_as_1222_, v_sz_boxed_1237_, v_i_boxed_1238_, v_b_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v_as_1222_);
lean_dec_ref(v_init_1219_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___boxed(lean_object* v_init_1240_, lean_object* v___x_1241_, lean_object* v_c_1242_, lean_object* v_n_1243_, lean_object* v_b_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(v_init_1240_, v___x_1241_, v_c_1242_, v_n_1243_, v_b_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec_ref(v___y_1251_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec(v___y_1245_);
lean_dec_ref(v_n_1243_);
lean_dec_ref(v_init_1240_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4(lean_object* v___x_1263_, lean_object* v_c_1264_, lean_object* v_as_1265_, size_t v_sz_1266_, size_t v_i_1267_, lean_object* v_b_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_){
_start:
{
uint8_t v___x_1280_; 
v___x_1280_ = lean_usize_dec_lt(v_i_1267_, v_sz_1266_);
if (v___x_1280_ == 0)
{
lean_object* v___x_1281_; 
lean_dec_ref(v_c_1264_);
lean_dec_ref(v___x_1263_);
v___x_1281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1281_, 0, v_b_1268_);
return v___x_1281_;
}
else
{
lean_object* v_snd_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1367_; 
v_snd_1282_ = lean_ctor_get(v_b_1268_, 1);
v_isSharedCheck_1367_ = !lean_is_exclusive(v_b_1268_);
if (v_isSharedCheck_1367_ == 0)
{
lean_object* v_unused_1368_; 
v_unused_1368_ = lean_ctor_get(v_b_1268_, 0);
lean_dec(v_unused_1368_);
v___x_1284_ = v_b_1268_;
v_isShared_1285_ = v_isSharedCheck_1367_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_snd_1282_);
lean_dec(v_b_1268_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1367_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v_a_1286_; lean_object* v_p_1287_; lean_object* v___x_1288_; uint8_t v___x_1289_; 
v_a_1286_ = lean_array_uget_borrowed(v_as_1265_, v_i_1267_);
v_p_1287_ = lean_ctor_get(v_a_1286_, 0);
v___x_1288_ = lean_box(0);
v___x_1289_ = l_Int_Linear_Poly_isNegEq(v___x_1263_, v_p_1287_);
if (v___x_1289_ == 0)
{
lean_object* v___x_1290_; size_t v___x_1291_; size_t v___x_1292_; 
lean_del_object(v___x_1284_);
lean_dec(v_snd_1282_);
v___x_1290_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___closed__1));
v___x_1291_ = ((size_t)1ULL);
v___x_1292_ = lean_usize_add(v_i_1267_, v___x_1291_);
v_i_1267_ = v___x_1292_;
v_b_1268_ = v___x_1290_;
goto _start;
}
else
{
lean_object* v___x_1294_; 
lean_inc(v_a_1286_);
v___x_1294_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_1286_, v___y_1269_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
if (lean_obj_tag(v___x_1294_) == 0)
{
lean_object* v_options_1295_; lean_object* v_inheritedTraceOptions_1296_; uint8_t v_hasTrace_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___y_1301_; lean_object* v___y_1302_; lean_object* v___y_1303_; lean_object* v___y_1304_; lean_object* v___y_1305_; lean_object* v___y_1306_; lean_object* v___y_1307_; lean_object* v___y_1308_; lean_object* v___y_1309_; lean_object* v___y_1310_; 
lean_dec_ref(v___x_1294_);
v_options_1295_ = lean_ctor_get(v___y_1277_, 2);
v_inheritedTraceOptions_1296_ = lean_ctor_get(v___y_1277_, 13);
v_hasTrace_1297_ = lean_ctor_get_uint8(v_options_1295_, sizeof(void*)*1);
lean_inc(v_a_1286_);
v___x_1298_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1298_, 0, v_c_1264_);
lean_ctor_set(v___x_1298_, 1, v_a_1286_);
v___x_1299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1263_);
lean_ctor_set(v___x_1299_, 1, v___x_1298_);
if (v_hasTrace_1297_ == 0)
{
v___y_1301_ = v___y_1269_;
v___y_1302_ = v___y_1270_;
v___y_1303_ = v___y_1271_;
v___y_1304_ = v___y_1272_;
v___y_1305_ = v___y_1273_;
v___y_1306_ = v___y_1274_;
v___y_1307_ = v___y_1275_;
v___y_1308_ = v___y_1276_;
v___y_1309_ = v___y_1277_;
v___y_1310_ = v___y_1278_;
goto v___jp_1300_;
}
else
{
lean_object* v___x_1335_; lean_object* v___x_1336_; uint8_t v___x_1337_; 
v___x_1335_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_1336_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5);
v___x_1337_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1296_, v_options_1295_, v___x_1336_);
if (v___x_1337_ == 0)
{
v___y_1301_ = v___y_1269_;
v___y_1302_ = v___y_1270_;
v___y_1303_ = v___y_1271_;
v___y_1304_ = v___y_1272_;
v___y_1305_ = v___y_1273_;
v___y_1306_ = v___y_1274_;
v___y_1307_ = v___y_1275_;
v___y_1308_ = v___y_1276_;
v___y_1309_ = v___y_1277_;
v___y_1310_ = v___y_1278_;
goto v___jp_1300_;
}
else
{
lean_object* v___x_1338_; 
lean_inc_ref(v___x_1299_);
v___x_1338_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_1299_, v___y_1269_, v___y_1277_);
if (lean_obj_tag(v___x_1338_) == 0)
{
lean_object* v_a_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v_a_1339_ = lean_ctor_get(v___x_1338_, 0);
lean_inc(v_a_1339_);
lean_dec_ref(v___x_1338_);
v___x_1340_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7);
v___x_1341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1340_);
lean_ctor_set(v___x_1341_, 1, v_a_1339_);
v___x_1342_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_1335_, v___x_1341_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_dec_ref(v___x_1342_);
v___y_1301_ = v___y_1269_;
v___y_1302_ = v___y_1270_;
v___y_1303_ = v___y_1271_;
v___y_1304_ = v___y_1272_;
v___y_1305_ = v___y_1273_;
v___y_1306_ = v___y_1274_;
v___y_1307_ = v___y_1275_;
v___y_1308_ = v___y_1276_;
v___y_1309_ = v___y_1277_;
v___y_1310_ = v___y_1278_;
goto v___jp_1300_;
}
else
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1350_; 
lean_dec_ref(v___x_1299_);
lean_del_object(v___x_1284_);
lean_dec(v_snd_1282_);
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1345_ = v___x_1342_;
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1342_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1348_; 
if (v_isShared_1346_ == 0)
{
v___x_1348_ = v___x_1345_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_a_1343_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
else
{
lean_object* v_a_1351_; lean_object* v___x_1353_; uint8_t v_isShared_1354_; uint8_t v_isSharedCheck_1358_; 
lean_dec_ref(v___x_1299_);
lean_del_object(v___x_1284_);
lean_dec(v_snd_1282_);
v_a_1351_ = lean_ctor_get(v___x_1338_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1353_ = v___x_1338_;
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
else
{
lean_inc(v_a_1351_);
lean_dec(v___x_1338_);
v___x_1353_ = lean_box(0);
v_isShared_1354_ = v_isSharedCheck_1358_;
goto v_resetjp_1352_;
}
v_resetjp_1352_:
{
lean_object* v___x_1356_; 
if (v_isShared_1354_ == 0)
{
v___x_1356_ = v___x_1353_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_a_1351_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
}
v___jp_1300_:
{
lean_object* v___x_1311_; 
lean_inc(v___y_1310_);
lean_inc_ref(v___y_1309_);
lean_inc(v___y_1308_);
lean_inc_ref(v___y_1307_);
lean_inc(v___y_1306_);
lean_inc_ref(v___y_1305_);
lean_inc(v___y_1304_);
lean_inc_ref(v___y_1303_);
lean_inc(v___y_1302_);
lean_inc(v___y_1301_);
v___x_1311_ = lean_grind_cutsat_assert_eq(v___x_1299_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1325_; 
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1325_ == 0)
{
lean_object* v_unused_1326_; 
v_unused_1326_ = lean_ctor_get(v___x_1311_, 0);
lean_dec(v_unused_1326_);
v___x_1313_ = v___x_1311_;
v_isShared_1314_ = v_isSharedCheck_1325_;
goto v_resetjp_1312_;
}
else
{
lean_dec(v___x_1311_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1325_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1318_; 
v___x_1315_ = lean_box(v___x_1289_);
v___x_1316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1315_);
if (v_isShared_1285_ == 0)
{
lean_ctor_set(v___x_1284_, 1, v___x_1288_);
lean_ctor_set(v___x_1284_, 0, v___x_1316_);
v___x_1318_ = v___x_1284_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v___x_1316_);
lean_ctor_set(v_reuseFailAlloc_1324_, 1, v___x_1288_);
v___x_1318_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1322_; 
v___x_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1318_);
v___x_1320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
lean_ctor_set(v___x_1320_, 1, v_snd_1282_);
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 0, v___x_1320_);
v___x_1322_ = v___x_1313_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1320_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
else
{
lean_object* v_a_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1334_; 
lean_del_object(v___x_1284_);
lean_dec(v_snd_1282_);
v_a_1327_ = lean_ctor_get(v___x_1311_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1329_ = v___x_1311_;
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_a_1327_);
lean_dec(v___x_1311_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1334_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1332_; 
if (v_isShared_1330_ == 0)
{
v___x_1332_ = v___x_1329_;
goto v_reusejp_1331_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v_a_1327_);
v___x_1332_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1331_;
}
v_reusejp_1331_:
{
return v___x_1332_;
}
}
}
}
}
else
{
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1366_; 
lean_del_object(v___x_1284_);
lean_dec(v_snd_1282_);
lean_dec_ref(v_c_1264_);
lean_dec_ref(v___x_1263_);
v_a_1359_ = lean_ctor_get(v___x_1294_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1361_ = v___x_1294_;
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v___x_1294_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1364_; 
if (v_isShared_1362_ == 0)
{
v___x_1364_ = v___x_1361_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_a_1359_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v___x_1369_ = _args[0];
lean_object* v_c_1370_ = _args[1];
lean_object* v_as_1371_ = _args[2];
lean_object* v_sz_1372_ = _args[3];
lean_object* v_i_1373_ = _args[4];
lean_object* v_b_1374_ = _args[5];
lean_object* v___y_1375_ = _args[6];
lean_object* v___y_1376_ = _args[7];
lean_object* v___y_1377_ = _args[8];
lean_object* v___y_1378_ = _args[9];
lean_object* v___y_1379_ = _args[10];
lean_object* v___y_1380_ = _args[11];
lean_object* v___y_1381_ = _args[12];
lean_object* v___y_1382_ = _args[13];
lean_object* v___y_1383_ = _args[14];
lean_object* v___y_1384_ = _args[15];
lean_object* v___y_1385_ = _args[16];
_start:
{
size_t v_sz_boxed_1386_; size_t v_i_boxed_1387_; lean_object* v_res_1388_; 
v_sz_boxed_1386_ = lean_unbox_usize(v_sz_1372_);
lean_dec(v_sz_1372_);
v_i_boxed_1387_ = lean_unbox_usize(v_i_1373_);
lean_dec(v_i_1373_);
v_res_1388_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4(v___x_1369_, v_c_1370_, v_as_1371_, v_sz_boxed_1386_, v_i_boxed_1387_, v_b_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
lean_dec(v___y_1378_);
lean_dec_ref(v___y_1377_);
lean_dec(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec_ref(v_as_1371_);
return v_res_1388_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1(lean_object* v___x_1392_, lean_object* v_c_1393_, lean_object* v_as_1394_, size_t v_sz_1395_, size_t v_i_1396_, lean_object* v_b_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
uint8_t v___x_1409_; 
v___x_1409_ = lean_usize_dec_lt(v_i_1396_, v_sz_1395_);
if (v___x_1409_ == 0)
{
lean_object* v___x_1410_; 
lean_dec_ref(v_c_1393_);
lean_dec_ref(v___x_1392_);
v___x_1410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1410_, 0, v_b_1397_);
return v___x_1410_;
}
else
{
lean_object* v_snd_1411_; lean_object* v___x_1413_; uint8_t v_isShared_1414_; uint8_t v_isSharedCheck_1496_; 
v_snd_1411_ = lean_ctor_get(v_b_1397_, 1);
v_isSharedCheck_1496_ = !lean_is_exclusive(v_b_1397_);
if (v_isSharedCheck_1496_ == 0)
{
lean_object* v_unused_1497_; 
v_unused_1497_ = lean_ctor_get(v_b_1397_, 0);
lean_dec(v_unused_1497_);
v___x_1413_ = v_b_1397_;
v_isShared_1414_ = v_isSharedCheck_1496_;
goto v_resetjp_1412_;
}
else
{
lean_inc(v_snd_1411_);
lean_dec(v_b_1397_);
v___x_1413_ = lean_box(0);
v_isShared_1414_ = v_isSharedCheck_1496_;
goto v_resetjp_1412_;
}
v_resetjp_1412_:
{
lean_object* v_a_1415_; lean_object* v_p_1416_; lean_object* v___x_1417_; uint8_t v___x_1418_; 
v_a_1415_ = lean_array_uget_borrowed(v_as_1394_, v_i_1396_);
v_p_1416_ = lean_ctor_get(v_a_1415_, 0);
v___x_1417_ = lean_box(0);
v___x_1418_ = l_Int_Linear_Poly_isNegEq(v___x_1392_, v_p_1416_);
if (v___x_1418_ == 0)
{
lean_object* v___x_1419_; size_t v___x_1420_; size_t v___x_1421_; lean_object* v___x_1422_; 
lean_del_object(v___x_1413_);
lean_dec(v_snd_1411_);
v___x_1419_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1___closed__0));
v___x_1420_ = ((size_t)1ULL);
v___x_1421_ = lean_usize_add(v_i_1396_, v___x_1420_);
v___x_1422_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4(v___x_1392_, v_c_1393_, v_as_1394_, v_sz_1395_, v___x_1421_, v___x_1419_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
return v___x_1422_;
}
else
{
lean_object* v___x_1423_; 
lean_inc(v_a_1415_);
v___x_1423_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_1415_, v___y_1398_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v_options_1424_; lean_object* v_inheritedTraceOptions_1425_; uint8_t v_hasTrace_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___y_1430_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; 
lean_dec_ref(v___x_1423_);
v_options_1424_ = lean_ctor_get(v___y_1406_, 2);
v_inheritedTraceOptions_1425_ = lean_ctor_get(v___y_1406_, 13);
v_hasTrace_1426_ = lean_ctor_get_uint8(v_options_1424_, sizeof(void*)*1);
lean_inc(v_a_1415_);
v___x_1427_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1427_, 0, v_c_1393_);
lean_ctor_set(v___x_1427_, 1, v_a_1415_);
v___x_1428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1428_, 0, v___x_1392_);
lean_ctor_set(v___x_1428_, 1, v___x_1427_);
if (v_hasTrace_1426_ == 0)
{
v___y_1430_ = v___y_1398_;
v___y_1431_ = v___y_1399_;
v___y_1432_ = v___y_1400_;
v___y_1433_ = v___y_1401_;
v___y_1434_ = v___y_1402_;
v___y_1435_ = v___y_1403_;
v___y_1436_ = v___y_1404_;
v___y_1437_ = v___y_1405_;
v___y_1438_ = v___y_1406_;
v___y_1439_ = v___y_1407_;
goto v___jp_1429_;
}
else
{
lean_object* v___x_1464_; lean_object* v___x_1465_; uint8_t v___x_1466_; 
v___x_1464_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_1465_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5);
v___x_1466_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1425_, v_options_1424_, v___x_1465_);
if (v___x_1466_ == 0)
{
v___y_1430_ = v___y_1398_;
v___y_1431_ = v___y_1399_;
v___y_1432_ = v___y_1400_;
v___y_1433_ = v___y_1401_;
v___y_1434_ = v___y_1402_;
v___y_1435_ = v___y_1403_;
v___y_1436_ = v___y_1404_;
v___y_1437_ = v___y_1405_;
v___y_1438_ = v___y_1406_;
v___y_1439_ = v___y_1407_;
goto v___jp_1429_;
}
else
{
lean_object* v___x_1467_; 
lean_inc_ref(v___x_1428_);
v___x_1467_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_1428_, v___y_1398_, v___y_1406_);
if (lean_obj_tag(v___x_1467_) == 0)
{
lean_object* v_a_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v_a_1468_ = lean_ctor_get(v___x_1467_, 0);
lean_inc(v_a_1468_);
lean_dec_ref(v___x_1467_);
v___x_1469_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7);
v___x_1470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1470_, 0, v___x_1469_);
lean_ctor_set(v___x_1470_, 1, v_a_1468_);
v___x_1471_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_1464_, v___x_1470_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_dec_ref(v___x_1471_);
v___y_1430_ = v___y_1398_;
v___y_1431_ = v___y_1399_;
v___y_1432_ = v___y_1400_;
v___y_1433_ = v___y_1401_;
v___y_1434_ = v___y_1402_;
v___y_1435_ = v___y_1403_;
v___y_1436_ = v___y_1404_;
v___y_1437_ = v___y_1405_;
v___y_1438_ = v___y_1406_;
v___y_1439_ = v___y_1407_;
goto v___jp_1429_;
}
else
{
lean_object* v_a_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1479_; 
lean_dec_ref(v___x_1428_);
lean_del_object(v___x_1413_);
lean_dec(v_snd_1411_);
v_a_1472_ = lean_ctor_get(v___x_1471_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1471_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1474_ = v___x_1471_;
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_dec(v___x_1471_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1477_; 
if (v_isShared_1475_ == 0)
{
v___x_1477_ = v___x_1474_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_a_1472_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
else
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1487_; 
lean_dec_ref(v___x_1428_);
lean_del_object(v___x_1413_);
lean_dec(v_snd_1411_);
v_a_1480_ = lean_ctor_get(v___x_1467_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1467_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1467_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1467_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1480_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
}
}
v___jp_1429_:
{
lean_object* v___x_1440_; 
lean_inc(v___y_1439_);
lean_inc_ref(v___y_1438_);
lean_inc(v___y_1437_);
lean_inc_ref(v___y_1436_);
lean_inc(v___y_1435_);
lean_inc_ref(v___y_1434_);
lean_inc(v___y_1433_);
lean_inc_ref(v___y_1432_);
lean_inc(v___y_1431_);
lean_inc(v___y_1430_);
v___x_1440_ = lean_grind_cutsat_assert_eq(v___x_1428_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1454_; 
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1454_ == 0)
{
lean_object* v_unused_1455_; 
v_unused_1455_ = lean_ctor_get(v___x_1440_, 0);
lean_dec(v_unused_1455_);
v___x_1442_ = v___x_1440_;
v_isShared_1443_ = v_isSharedCheck_1454_;
goto v_resetjp_1441_;
}
else
{
lean_dec(v___x_1440_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1454_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1447_; 
v___x_1444_ = lean_box(v___x_1418_);
v___x_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1444_);
if (v_isShared_1414_ == 0)
{
lean_ctor_set(v___x_1413_, 1, v___x_1417_);
lean_ctor_set(v___x_1413_, 0, v___x_1445_);
v___x_1447_ = v___x_1413_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1445_);
lean_ctor_set(v_reuseFailAlloc_1453_, 1, v___x_1417_);
v___x_1447_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1451_; 
v___x_1448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1447_);
v___x_1449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1448_);
lean_ctor_set(v___x_1449_, 1, v_snd_1411_);
if (v_isShared_1443_ == 0)
{
lean_ctor_set(v___x_1442_, 0, v___x_1449_);
v___x_1451_ = v___x_1442_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1452_; 
v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1449_);
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
else
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1463_; 
lean_del_object(v___x_1413_);
lean_dec(v_snd_1411_);
v_a_1456_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1458_ = v___x_1440_;
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1440_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1461_; 
if (v_isShared_1459_ == 0)
{
v___x_1461_ = v___x_1458_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_a_1456_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
}
}
else
{
lean_object* v_a_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1495_; 
lean_del_object(v___x_1413_);
lean_dec(v_snd_1411_);
lean_dec_ref(v_c_1393_);
lean_dec_ref(v___x_1392_);
v_a_1488_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1490_ = v___x_1423_;
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_a_1488_);
lean_dec(v___x_1423_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1493_; 
if (v_isShared_1491_ == 0)
{
v___x_1493_ = v___x_1490_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_a_1488_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v___x_1498_ = _args[0];
lean_object* v_c_1499_ = _args[1];
lean_object* v_as_1500_ = _args[2];
lean_object* v_sz_1501_ = _args[3];
lean_object* v_i_1502_ = _args[4];
lean_object* v_b_1503_ = _args[5];
lean_object* v___y_1504_ = _args[6];
lean_object* v___y_1505_ = _args[7];
lean_object* v___y_1506_ = _args[8];
lean_object* v___y_1507_ = _args[9];
lean_object* v___y_1508_ = _args[10];
lean_object* v___y_1509_ = _args[11];
lean_object* v___y_1510_ = _args[12];
lean_object* v___y_1511_ = _args[13];
lean_object* v___y_1512_ = _args[14];
lean_object* v___y_1513_ = _args[15];
lean_object* v___y_1514_ = _args[16];
_start:
{
size_t v_sz_boxed_1515_; size_t v_i_boxed_1516_; lean_object* v_res_1517_; 
v_sz_boxed_1515_ = lean_unbox_usize(v_sz_1501_);
lean_dec(v_sz_1501_);
v_i_boxed_1516_ = lean_unbox_usize(v_i_1502_);
lean_dec(v_i_1502_);
v_res_1517_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1(v___x_1498_, v_c_1499_, v_as_1500_, v_sz_boxed_1515_, v_i_boxed_1516_, v_b_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v___y_1505_);
lean_dec(v___y_1504_);
lean_dec_ref(v_as_1500_);
return v_res_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0(lean_object* v___x_1518_, lean_object* v_c_1519_, lean_object* v_t_1520_, lean_object* v_init_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
lean_object* v_root_1533_; lean_object* v_tail_1534_; lean_object* v___x_1535_; 
v_root_1533_ = lean_ctor_get(v_t_1520_, 0);
v_tail_1534_ = lean_ctor_get(v_t_1520_, 1);
lean_inc_ref(v_c_1519_);
lean_inc_ref(v___x_1518_);
lean_inc_ref(v_init_1521_);
v___x_1535_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(v_init_1521_, v___x_1518_, v_c_1519_, v_root_1533_, v_init_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
lean_dec_ref(v_init_1521_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v_a_1536_; lean_object* v___x_1538_; uint8_t v_isShared_1539_; uint8_t v_isSharedCheck_1572_; 
v_a_1536_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1538_ = v___x_1535_;
v_isShared_1539_ = v_isSharedCheck_1572_;
goto v_resetjp_1537_;
}
else
{
lean_inc(v_a_1536_);
lean_dec(v___x_1535_);
v___x_1538_ = lean_box(0);
v_isShared_1539_ = v_isSharedCheck_1572_;
goto v_resetjp_1537_;
}
v_resetjp_1537_:
{
if (lean_obj_tag(v_a_1536_) == 0)
{
lean_object* v_a_1540_; lean_object* v___x_1542_; 
lean_dec_ref(v_c_1519_);
lean_dec_ref(v___x_1518_);
v_a_1540_ = lean_ctor_get(v_a_1536_, 0);
lean_inc(v_a_1540_);
lean_dec_ref(v_a_1536_);
if (v_isShared_1539_ == 0)
{
lean_ctor_set(v___x_1538_, 0, v_a_1540_);
v___x_1542_ = v___x_1538_;
goto v_reusejp_1541_;
}
else
{
lean_object* v_reuseFailAlloc_1543_; 
v_reuseFailAlloc_1543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1543_, 0, v_a_1540_);
v___x_1542_ = v_reuseFailAlloc_1543_;
goto v_reusejp_1541_;
}
v_reusejp_1541_:
{
return v___x_1542_;
}
}
else
{
lean_object* v_a_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; size_t v_sz_1547_; size_t v___x_1548_; lean_object* v___x_1549_; 
lean_del_object(v___x_1538_);
v_a_1544_ = lean_ctor_get(v_a_1536_, 0);
lean_inc(v_a_1544_);
lean_dec_ref(v_a_1536_);
v___x_1545_ = lean_box(0);
v___x_1546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1545_);
lean_ctor_set(v___x_1546_, 1, v_a_1544_);
v_sz_1547_ = lean_array_size(v_tail_1534_);
v___x_1548_ = ((size_t)0ULL);
v___x_1549_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1(v___x_1518_, v_c_1519_, v_tail_1534_, v_sz_1547_, v___x_1548_, v___x_1546_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_);
if (lean_obj_tag(v___x_1549_) == 0)
{
lean_object* v_a_1550_; lean_object* v___x_1552_; uint8_t v_isShared_1553_; uint8_t v_isSharedCheck_1563_; 
v_a_1550_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1563_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1563_ == 0)
{
v___x_1552_ = v___x_1549_;
v_isShared_1553_ = v_isSharedCheck_1563_;
goto v_resetjp_1551_;
}
else
{
lean_inc(v_a_1550_);
lean_dec(v___x_1549_);
v___x_1552_ = lean_box(0);
v_isShared_1553_ = v_isSharedCheck_1563_;
goto v_resetjp_1551_;
}
v_resetjp_1551_:
{
lean_object* v_fst_1554_; 
v_fst_1554_ = lean_ctor_get(v_a_1550_, 0);
if (lean_obj_tag(v_fst_1554_) == 0)
{
lean_object* v_snd_1555_; lean_object* v___x_1557_; 
v_snd_1555_ = lean_ctor_get(v_a_1550_, 1);
lean_inc(v_snd_1555_);
lean_dec(v_a_1550_);
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 0, v_snd_1555_);
v___x_1557_ = v___x_1552_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_snd_1555_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
else
{
lean_object* v_val_1559_; lean_object* v___x_1561_; 
lean_inc_ref(v_fst_1554_);
lean_dec(v_a_1550_);
v_val_1559_ = lean_ctor_get(v_fst_1554_, 0);
lean_inc(v_val_1559_);
lean_dec_ref(v_fst_1554_);
if (v_isShared_1553_ == 0)
{
lean_ctor_set(v___x_1552_, 0, v_val_1559_);
v___x_1561_ = v___x_1552_;
goto v_reusejp_1560_;
}
else
{
lean_object* v_reuseFailAlloc_1562_; 
v_reuseFailAlloc_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1562_, 0, v_val_1559_);
v___x_1561_ = v_reuseFailAlloc_1562_;
goto v_reusejp_1560_;
}
v_reusejp_1560_:
{
return v___x_1561_;
}
}
}
}
else
{
lean_object* v_a_1564_; lean_object* v___x_1566_; uint8_t v_isShared_1567_; uint8_t v_isSharedCheck_1571_; 
v_a_1564_ = lean_ctor_get(v___x_1549_, 0);
v_isSharedCheck_1571_ = !lean_is_exclusive(v___x_1549_);
if (v_isSharedCheck_1571_ == 0)
{
v___x_1566_ = v___x_1549_;
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
else
{
lean_inc(v_a_1564_);
lean_dec(v___x_1549_);
v___x_1566_ = lean_box(0);
v_isShared_1567_ = v_isSharedCheck_1571_;
goto v_resetjp_1565_;
}
v_resetjp_1565_:
{
lean_object* v___x_1569_; 
if (v_isShared_1567_ == 0)
{
v___x_1569_ = v___x_1566_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v_a_1564_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
}
}
else
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1580_; 
lean_dec_ref(v_c_1519_);
lean_dec_ref(v___x_1518_);
v_a_1573_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1575_ = v___x_1535_;
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1535_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0___boxed(lean_object* v___x_1581_, lean_object* v_c_1582_, lean_object* v_t_1583_, lean_object* v_init_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0(v___x_1581_, v_c_1582_, v_t_1583_, v_init_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_);
lean_dec(v___y_1594_);
lean_dec_ref(v___y_1593_);
lean_dec(v___y_1592_);
lean_dec_ref(v___y_1591_);
lean_dec(v___y_1590_);
lean_dec_ref(v___y_1589_);
lean_dec(v___y_1588_);
lean_dec_ref(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec(v___y_1585_);
lean_dec_ref(v_t_1583_);
return v_res_1596_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0(void){
_start:
{
lean_object* v___x_1597_; 
v___x_1597_ = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq(lean_object* v_c_1598_, lean_object* v_a_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_){
_start:
{
lean_object* v_p_1610_; 
v_p_1610_ = lean_ctor_get(v_c_1598_, 0);
if (lean_obj_tag(v_p_1610_) == 1)
{
lean_object* v_k_1611_; lean_object* v_v_1612_; lean_object* v___x_1613_; 
lean_inc_ref(v_p_1610_);
v_k_1611_ = lean_ctor_get(v_p_1610_, 0);
v_v_1612_ = lean_ctor_get(v_p_1610_, 1);
v___x_1613_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1599_, v_a_1607_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v_a_1614_; lean_object* v___y_1616_; lean_object* v___x_1642_; uint8_t v___x_1643_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
lean_inc(v_a_1614_);
lean_dec_ref(v___x_1613_);
v___x_1642_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9);
v___x_1643_ = lean_int_dec_lt(v_k_1611_, v___x_1642_);
if (v___x_1643_ == 0)
{
lean_object* v_lowers_1644_; lean_object* v_size_1645_; lean_object* v___x_1646_; uint8_t v___x_1647_; 
v_lowers_1644_ = lean_ctor_get(v_a_1614_, 7);
lean_inc_ref(v_lowers_1644_);
lean_dec(v_a_1614_);
v_size_1645_ = lean_ctor_get(v_lowers_1644_, 2);
v___x_1646_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0);
v___x_1647_ = lean_nat_dec_lt(v_v_1612_, v_size_1645_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; 
lean_dec_ref(v_lowers_1644_);
v___x_1648_ = l_outOfBounds___redArg(v___x_1646_);
v___y_1616_ = v___x_1648_;
goto v___jp_1615_;
}
else
{
lean_object* v___x_1649_; 
v___x_1649_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1646_, v_lowers_1644_, v_v_1612_);
lean_dec_ref(v_lowers_1644_);
v___y_1616_ = v___x_1649_;
goto v___jp_1615_;
}
}
else
{
lean_object* v_uppers_1650_; lean_object* v_size_1651_; lean_object* v___x_1652_; uint8_t v___x_1653_; 
v_uppers_1650_ = lean_ctor_get(v_a_1614_, 8);
lean_inc_ref(v_uppers_1650_);
lean_dec(v_a_1614_);
v_size_1651_ = lean_ctor_get(v_uppers_1650_, 2);
v___x_1652_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0);
v___x_1653_ = lean_nat_dec_lt(v_v_1612_, v_size_1651_);
if (v___x_1653_ == 0)
{
lean_object* v___x_1654_; 
lean_dec_ref(v_uppers_1650_);
v___x_1654_ = l_outOfBounds___redArg(v___x_1652_);
v___y_1616_ = v___x_1654_;
goto v___jp_1615_;
}
else
{
lean_object* v___x_1655_; 
v___x_1655_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1652_, v_uppers_1650_, v_v_1612_);
lean_dec_ref(v_uppers_1650_);
v___y_1616_ = v___x_1655_;
goto v___jp_1615_;
}
}
v___jp_1615_:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; 
v___x_1617_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__0));
v___x_1618_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0(v_p_1610_, v_c_1598_, v___y_1616_, v___x_1617_, v_a_1599_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_);
lean_dec_ref(v___y_1616_);
if (lean_obj_tag(v___x_1618_) == 0)
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1633_; 
v_a_1619_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1633_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1633_ == 0)
{
v___x_1621_ = v___x_1618_;
v_isShared_1622_ = v_isSharedCheck_1633_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1618_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1633_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v_fst_1623_; 
v_fst_1623_ = lean_ctor_get(v_a_1619_, 0);
lean_inc(v_fst_1623_);
lean_dec(v_a_1619_);
if (lean_obj_tag(v_fst_1623_) == 0)
{
uint8_t v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1627_; 
v___x_1624_ = 0;
v___x_1625_ = lean_box(v___x_1624_);
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 0, v___x_1625_);
v___x_1627_ = v___x_1621_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v___x_1625_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
else
{
lean_object* v_val_1629_; lean_object* v___x_1631_; 
v_val_1629_ = lean_ctor_get(v_fst_1623_, 0);
lean_inc(v_val_1629_);
lean_dec_ref(v_fst_1623_);
if (v_isShared_1622_ == 0)
{
lean_ctor_set(v___x_1621_, 0, v_val_1629_);
v___x_1631_ = v___x_1621_;
goto v_reusejp_1630_;
}
else
{
lean_object* v_reuseFailAlloc_1632_; 
v_reuseFailAlloc_1632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1632_, 0, v_val_1629_);
v___x_1631_ = v_reuseFailAlloc_1632_;
goto v_reusejp_1630_;
}
v_reusejp_1630_:
{
return v___x_1631_;
}
}
}
}
else
{
lean_object* v_a_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1641_; 
v_a_1634_ = lean_ctor_get(v___x_1618_, 0);
v_isSharedCheck_1641_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1641_ == 0)
{
v___x_1636_ = v___x_1618_;
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
else
{
lean_inc(v_a_1634_);
lean_dec(v___x_1618_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1641_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1639_; 
if (v_isShared_1637_ == 0)
{
v___x_1639_ = v___x_1636_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1640_; 
v_reuseFailAlloc_1640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1640_, 0, v_a_1634_);
v___x_1639_ = v_reuseFailAlloc_1640_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
return v___x_1639_;
}
}
}
}
}
else
{
lean_object* v_a_1656_; lean_object* v___x_1658_; uint8_t v_isShared_1659_; uint8_t v_isSharedCheck_1663_; 
lean_dec_ref(v_p_1610_);
lean_dec_ref(v_c_1598_);
v_a_1656_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1658_ = v___x_1613_;
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
else
{
lean_inc(v_a_1656_);
lean_dec(v___x_1613_);
v___x_1658_ = lean_box(0);
v_isShared_1659_ = v_isSharedCheck_1663_;
goto v_resetjp_1657_;
}
v_resetjp_1657_:
{
lean_object* v___x_1661_; 
if (v_isShared_1659_ == 0)
{
v___x_1661_ = v___x_1658_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_a_1656_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
}
else
{
lean_object* v___x_1664_; 
v___x_1664_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_1598_, v_a_1599_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_);
return v___x_1664_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___boxed(lean_object* v_c_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_){
_start:
{
lean_object* v_res_1677_; 
v_res_1677_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq(v_c_1665_, v_a_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_);
lean_dec(v_a_1675_);
lean_dec_ref(v_a_1674_);
lean_dec(v_a_1673_);
lean_dec_ref(v_a_1672_);
lean_dec(v_a_1671_);
lean_dec_ref(v_a_1670_);
lean_dec(v_a_1669_);
lean_dec_ref(v_a_1668_);
lean_dec(v_a_1667_);
lean_dec(v_a_1666_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(lean_object* v___x_1678_, lean_object* v_as_1679_, size_t v_i_1680_, size_t v_stop_1681_, lean_object* v_b_1682_){
_start:
{
lean_object* v___y_1684_; uint8_t v___x_1688_; 
v___x_1688_ = lean_usize_dec_eq(v_i_1680_, v_stop_1681_);
if (v___x_1688_ == 0)
{
lean_object* v___x_1689_; lean_object* v_p_1690_; uint8_t v___x_1691_; 
v___x_1689_ = lean_array_uget_borrowed(v_as_1679_, v_i_1680_);
v_p_1690_ = lean_ctor_get(v___x_1689_, 0);
v___x_1691_ = l_Int_Linear_instBEqPoly_beq(v_p_1690_, v___x_1678_);
if (v___x_1691_ == 0)
{
lean_object* v___x_1692_; 
lean_inc(v___x_1689_);
v___x_1692_ = l_Lean_PersistentArray_push___redArg(v_b_1682_, v___x_1689_);
v___y_1684_ = v___x_1692_;
goto v___jp_1683_;
}
else
{
v___y_1684_ = v_b_1682_;
goto v___jp_1683_;
}
}
else
{
return v_b_1682_;
}
v___jp_1683_:
{
size_t v___x_1685_; size_t v___x_1686_; 
v___x_1685_ = ((size_t)1ULL);
v___x_1686_ = lean_usize_add(v_i_1680_, v___x_1685_);
v_i_1680_ = v___x_1686_;
v_b_1682_ = v___y_1684_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1___boxed(lean_object* v___x_1693_, lean_object* v_as_1694_, lean_object* v_i_1695_, lean_object* v_stop_1696_, lean_object* v_b_1697_){
_start:
{
size_t v_i_boxed_1698_; size_t v_stop_boxed_1699_; lean_object* v_res_1700_; 
v_i_boxed_1698_ = lean_unbox_usize(v_i_1695_);
lean_dec(v_i_1695_);
v_stop_boxed_1699_ = lean_unbox_usize(v_stop_1696_);
lean_dec(v_stop_1696_);
v_res_1700_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1693_, v_as_1694_, v_i_boxed_1698_, v_stop_boxed_1699_, v_b_1697_);
lean_dec_ref(v_as_1694_);
lean_dec_ref(v___x_1693_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(lean_object* v___x_1701_, lean_object* v_x_1702_, lean_object* v_x_1703_){
_start:
{
if (lean_obj_tag(v_x_1702_) == 0)
{
lean_object* v_cs_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; uint8_t v___x_1707_; 
v_cs_1704_ = lean_ctor_get(v_x_1702_, 0);
v___x_1705_ = lean_unsigned_to_nat(0u);
v___x_1706_ = lean_array_get_size(v_cs_1704_);
v___x_1707_ = lean_nat_dec_lt(v___x_1705_, v___x_1706_);
if (v___x_1707_ == 0)
{
return v_x_1703_;
}
else
{
uint8_t v___x_1708_; 
v___x_1708_ = lean_nat_dec_le(v___x_1706_, v___x_1706_);
if (v___x_1708_ == 0)
{
if (v___x_1707_ == 0)
{
return v_x_1703_;
}
else
{
size_t v___x_1709_; size_t v___x_1710_; lean_object* v___x_1711_; 
v___x_1709_ = ((size_t)0ULL);
v___x_1710_ = lean_usize_of_nat(v___x_1706_);
v___x_1711_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1701_, v_cs_1704_, v___x_1709_, v___x_1710_, v_x_1703_);
return v___x_1711_;
}
}
else
{
size_t v___x_1712_; size_t v___x_1713_; lean_object* v___x_1714_; 
v___x_1712_ = ((size_t)0ULL);
v___x_1713_ = lean_usize_of_nat(v___x_1706_);
v___x_1714_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1701_, v_cs_1704_, v___x_1712_, v___x_1713_, v_x_1703_);
return v___x_1714_;
}
}
}
else
{
lean_object* v_vs_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; uint8_t v___x_1718_; 
v_vs_1715_ = lean_ctor_get(v_x_1702_, 0);
v___x_1716_ = lean_unsigned_to_nat(0u);
v___x_1717_ = lean_array_get_size(v_vs_1715_);
v___x_1718_ = lean_nat_dec_lt(v___x_1716_, v___x_1717_);
if (v___x_1718_ == 0)
{
return v_x_1703_;
}
else
{
uint8_t v___x_1719_; 
v___x_1719_ = lean_nat_dec_le(v___x_1717_, v___x_1717_);
if (v___x_1719_ == 0)
{
if (v___x_1718_ == 0)
{
return v_x_1703_;
}
else
{
size_t v___x_1720_; size_t v___x_1721_; lean_object* v___x_1722_; 
v___x_1720_ = ((size_t)0ULL);
v___x_1721_ = lean_usize_of_nat(v___x_1717_);
v___x_1722_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1701_, v_vs_1715_, v___x_1720_, v___x_1721_, v_x_1703_);
return v___x_1722_;
}
}
else
{
size_t v___x_1723_; size_t v___x_1724_; lean_object* v___x_1725_; 
v___x_1723_ = ((size_t)0ULL);
v___x_1724_ = lean_usize_of_nat(v___x_1717_);
v___x_1725_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1701_, v_vs_1715_, v___x_1723_, v___x_1724_, v_x_1703_);
return v___x_1725_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(lean_object* v___x_1726_, lean_object* v_as_1727_, size_t v_i_1728_, size_t v_stop_1729_, lean_object* v_b_1730_){
_start:
{
uint8_t v___x_1731_; 
v___x_1731_ = lean_usize_dec_eq(v_i_1728_, v_stop_1729_);
if (v___x_1731_ == 0)
{
lean_object* v___x_1732_; lean_object* v___x_1733_; size_t v___x_1734_; size_t v___x_1735_; 
v___x_1732_ = lean_array_uget_borrowed(v_as_1727_, v_i_1728_);
v___x_1733_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(v___x_1726_, v___x_1732_, v_b_1730_);
v___x_1734_ = ((size_t)1ULL);
v___x_1735_ = lean_usize_add(v_i_1728_, v___x_1734_);
v_i_1728_ = v___x_1735_;
v_b_1730_ = v___x_1733_;
goto _start;
}
else
{
return v_b_1730_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v___x_1737_, lean_object* v_as_1738_, lean_object* v_i_1739_, lean_object* v_stop_1740_, lean_object* v_b_1741_){
_start:
{
size_t v_i_boxed_1742_; size_t v_stop_boxed_1743_; lean_object* v_res_1744_; 
v_i_boxed_1742_ = lean_unbox_usize(v_i_1739_);
lean_dec(v_i_1739_);
v_stop_boxed_1743_ = lean_unbox_usize(v_stop_1740_);
lean_dec(v_stop_1740_);
v_res_1744_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1737_, v_as_1738_, v_i_boxed_1742_, v_stop_boxed_1743_, v_b_1741_);
lean_dec_ref(v_as_1738_);
lean_dec_ref(v___x_1737_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2___boxed(lean_object* v___x_1745_, lean_object* v_x_1746_, lean_object* v_x_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(v___x_1745_, v_x_1746_, v_x_1747_);
lean_dec_ref(v_x_1746_);
lean_dec_ref(v___x_1745_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(lean_object* v___x_1749_, lean_object* v_x_1750_, size_t v_x_1751_, size_t v_x_1752_, lean_object* v_x_1753_){
_start:
{
if (lean_obj_tag(v_x_1750_) == 0)
{
lean_object* v_cs_1754_; lean_object* v___x_1755_; size_t v___x_1756_; lean_object* v_j_1757_; lean_object* v___x_1758_; size_t v___x_1759_; size_t v___x_1760_; size_t v___x_1761_; size_t v___x_1762_; size_t v___x_1763_; size_t v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; uint8_t v___x_1769_; 
v_cs_1754_ = lean_ctor_get(v_x_1750_, 0);
v___x_1755_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0);
v___x_1756_ = lean_usize_shift_right(v_x_1751_, v_x_1752_);
v_j_1757_ = lean_usize_to_nat(v___x_1756_);
v___x_1758_ = lean_array_get_borrowed(v___x_1755_, v_cs_1754_, v_j_1757_);
v___x_1759_ = ((size_t)1ULL);
v___x_1760_ = lean_usize_shift_left(v___x_1759_, v_x_1752_);
v___x_1761_ = lean_usize_sub(v___x_1760_, v___x_1759_);
v___x_1762_ = lean_usize_land(v_x_1751_, v___x_1761_);
v___x_1763_ = ((size_t)5ULL);
v___x_1764_ = lean_usize_sub(v_x_1752_, v___x_1763_);
v___x_1765_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(v___x_1749_, v___x_1758_, v___x_1762_, v___x_1764_, v_x_1753_);
v___x_1766_ = lean_unsigned_to_nat(1u);
v___x_1767_ = lean_nat_add(v_j_1757_, v___x_1766_);
lean_dec(v_j_1757_);
v___x_1768_ = lean_array_get_size(v_cs_1754_);
v___x_1769_ = lean_nat_dec_lt(v___x_1767_, v___x_1768_);
if (v___x_1769_ == 0)
{
lean_dec(v___x_1767_);
return v___x_1765_;
}
else
{
uint8_t v___x_1770_; 
v___x_1770_ = lean_nat_dec_le(v___x_1768_, v___x_1768_);
if (v___x_1770_ == 0)
{
if (v___x_1769_ == 0)
{
lean_dec(v___x_1767_);
return v___x_1765_;
}
else
{
size_t v___x_1771_; size_t v___x_1772_; lean_object* v___x_1773_; 
v___x_1771_ = lean_usize_of_nat(v___x_1767_);
lean_dec(v___x_1767_);
v___x_1772_ = lean_usize_of_nat(v___x_1768_);
v___x_1773_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1749_, v_cs_1754_, v___x_1771_, v___x_1772_, v___x_1765_);
return v___x_1773_;
}
}
else
{
size_t v___x_1774_; size_t v___x_1775_; lean_object* v___x_1776_; 
v___x_1774_ = lean_usize_of_nat(v___x_1767_);
lean_dec(v___x_1767_);
v___x_1775_ = lean_usize_of_nat(v___x_1768_);
v___x_1776_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1749_, v_cs_1754_, v___x_1774_, v___x_1775_, v___x_1765_);
return v___x_1776_;
}
}
}
else
{
lean_object* v_vs_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; uint8_t v___x_1780_; 
v_vs_1777_ = lean_ctor_get(v_x_1750_, 0);
v___x_1778_ = lean_usize_to_nat(v_x_1751_);
v___x_1779_ = lean_array_get_size(v_vs_1777_);
v___x_1780_ = lean_nat_dec_lt(v___x_1778_, v___x_1779_);
if (v___x_1780_ == 0)
{
lean_dec(v___x_1778_);
return v_x_1753_;
}
else
{
uint8_t v___x_1781_; 
v___x_1781_ = lean_nat_dec_le(v___x_1779_, v___x_1779_);
if (v___x_1781_ == 0)
{
if (v___x_1780_ == 0)
{
lean_dec(v___x_1778_);
return v_x_1753_;
}
else
{
size_t v___x_1782_; size_t v___x_1783_; lean_object* v___x_1784_; 
v___x_1782_ = lean_usize_of_nat(v___x_1778_);
lean_dec(v___x_1778_);
v___x_1783_ = lean_usize_of_nat(v___x_1779_);
v___x_1784_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1749_, v_vs_1777_, v___x_1782_, v___x_1783_, v_x_1753_);
return v___x_1784_;
}
}
else
{
size_t v___x_1785_; size_t v___x_1786_; lean_object* v___x_1787_; 
v___x_1785_ = lean_usize_of_nat(v___x_1778_);
lean_dec(v___x_1778_);
v___x_1786_ = lean_usize_of_nat(v___x_1779_);
v___x_1787_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1749_, v_vs_1777_, v___x_1785_, v___x_1786_, v_x_1753_);
return v___x_1787_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0___boxed(lean_object* v___x_1788_, lean_object* v_x_1789_, lean_object* v_x_1790_, lean_object* v_x_1791_, lean_object* v_x_1792_){
_start:
{
size_t v_x_21627__boxed_1793_; size_t v_x_21628__boxed_1794_; lean_object* v_res_1795_; 
v_x_21627__boxed_1793_ = lean_unbox_usize(v_x_1790_);
lean_dec(v_x_1790_);
v_x_21628__boxed_1794_ = lean_unbox_usize(v_x_1791_);
lean_dec(v_x_1791_);
v_res_1795_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(v___x_1788_, v_x_1789_, v_x_21627__boxed_1793_, v_x_21628__boxed_1794_, v_x_1792_);
lean_dec_ref(v_x_1789_);
lean_dec_ref(v___x_1788_);
return v_res_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(lean_object* v___x_1796_, lean_object* v_t_1797_, lean_object* v_init_1798_, lean_object* v_start_1799_){
_start:
{
lean_object* v___x_1800_; uint8_t v___x_1801_; 
v___x_1800_ = lean_unsigned_to_nat(0u);
v___x_1801_ = lean_nat_dec_eq(v_start_1799_, v___x_1800_);
if (v___x_1801_ == 0)
{
lean_object* v_root_1802_; lean_object* v_tail_1803_; size_t v_shift_1804_; lean_object* v_tailOff_1805_; uint8_t v___x_1806_; 
v_root_1802_ = lean_ctor_get(v_t_1797_, 0);
v_tail_1803_ = lean_ctor_get(v_t_1797_, 1);
v_shift_1804_ = lean_ctor_get_usize(v_t_1797_, 4);
v_tailOff_1805_ = lean_ctor_get(v_t_1797_, 3);
v___x_1806_ = lean_nat_dec_le(v_tailOff_1805_, v_start_1799_);
if (v___x_1806_ == 0)
{
size_t v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; uint8_t v___x_1810_; 
v___x_1807_ = lean_usize_of_nat(v_start_1799_);
v___x_1808_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(v___x_1796_, v_root_1802_, v___x_1807_, v_shift_1804_, v_init_1798_);
v___x_1809_ = lean_array_get_size(v_tail_1803_);
v___x_1810_ = lean_nat_dec_lt(v___x_1800_, v___x_1809_);
if (v___x_1810_ == 0)
{
return v___x_1808_;
}
else
{
uint8_t v___x_1811_; 
v___x_1811_ = lean_nat_dec_le(v___x_1809_, v___x_1809_);
if (v___x_1811_ == 0)
{
if (v___x_1810_ == 0)
{
return v___x_1808_;
}
else
{
size_t v___x_1812_; size_t v___x_1813_; lean_object* v___x_1814_; 
v___x_1812_ = ((size_t)0ULL);
v___x_1813_ = lean_usize_of_nat(v___x_1809_);
v___x_1814_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1796_, v_tail_1803_, v___x_1812_, v___x_1813_, v___x_1808_);
return v___x_1814_;
}
}
else
{
size_t v___x_1815_; size_t v___x_1816_; lean_object* v___x_1817_; 
v___x_1815_ = ((size_t)0ULL);
v___x_1816_ = lean_usize_of_nat(v___x_1809_);
v___x_1817_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1796_, v_tail_1803_, v___x_1815_, v___x_1816_, v___x_1808_);
return v___x_1817_;
}
}
}
else
{
lean_object* v___x_1818_; lean_object* v___x_1819_; uint8_t v___x_1820_; 
v___x_1818_ = lean_nat_sub(v_start_1799_, v_tailOff_1805_);
v___x_1819_ = lean_array_get_size(v_tail_1803_);
v___x_1820_ = lean_nat_dec_lt(v___x_1818_, v___x_1819_);
if (v___x_1820_ == 0)
{
lean_dec(v___x_1818_);
return v_init_1798_;
}
else
{
uint8_t v___x_1821_; 
v___x_1821_ = lean_nat_dec_le(v___x_1819_, v___x_1819_);
if (v___x_1821_ == 0)
{
if (v___x_1820_ == 0)
{
lean_dec(v___x_1818_);
return v_init_1798_;
}
else
{
size_t v___x_1822_; size_t v___x_1823_; lean_object* v___x_1824_; 
v___x_1822_ = lean_usize_of_nat(v___x_1818_);
lean_dec(v___x_1818_);
v___x_1823_ = lean_usize_of_nat(v___x_1819_);
v___x_1824_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1796_, v_tail_1803_, v___x_1822_, v___x_1823_, v_init_1798_);
return v___x_1824_;
}
}
else
{
size_t v___x_1825_; size_t v___x_1826_; lean_object* v___x_1827_; 
v___x_1825_ = lean_usize_of_nat(v___x_1818_);
lean_dec(v___x_1818_);
v___x_1826_ = lean_usize_of_nat(v___x_1819_);
v___x_1827_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1796_, v_tail_1803_, v___x_1825_, v___x_1826_, v_init_1798_);
return v___x_1827_;
}
}
}
}
else
{
lean_object* v_root_1828_; lean_object* v_tail_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; uint8_t v___x_1832_; 
v_root_1828_ = lean_ctor_get(v_t_1797_, 0);
v_tail_1829_ = lean_ctor_get(v_t_1797_, 1);
v___x_1830_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(v___x_1796_, v_root_1828_, v_init_1798_);
v___x_1831_ = lean_array_get_size(v_tail_1829_);
v___x_1832_ = lean_nat_dec_lt(v___x_1800_, v___x_1831_);
if (v___x_1832_ == 0)
{
return v___x_1830_;
}
else
{
uint8_t v___x_1833_; 
v___x_1833_ = lean_nat_dec_le(v___x_1831_, v___x_1831_);
if (v___x_1833_ == 0)
{
if (v___x_1832_ == 0)
{
return v___x_1830_;
}
else
{
size_t v___x_1834_; size_t v___x_1835_; lean_object* v___x_1836_; 
v___x_1834_ = ((size_t)0ULL);
v___x_1835_ = lean_usize_of_nat(v___x_1831_);
v___x_1836_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1796_, v_tail_1829_, v___x_1834_, v___x_1835_, v___x_1830_);
return v___x_1836_;
}
}
else
{
size_t v___x_1837_; size_t v___x_1838_; lean_object* v___x_1839_; 
v___x_1837_ = ((size_t)0ULL);
v___x_1838_ = lean_usize_of_nat(v___x_1831_);
v___x_1839_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1796_, v_tail_1829_, v___x_1837_, v___x_1838_, v___x_1830_);
return v___x_1839_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0___boxed(lean_object* v___x_1840_, lean_object* v_t_1841_, lean_object* v_init_1842_, lean_object* v_start_1843_){
_start:
{
lean_object* v_res_1844_; 
v_res_1844_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(v___x_1840_, v_t_1841_, v_init_1842_, v_start_1843_);
lean_dec(v_start_1843_);
lean_dec_ref(v_t_1841_);
lean_dec_ref(v___x_1840_);
return v_res_1844_;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1845_ = lean_unsigned_to_nat(32u);
v___x_1846_ = lean_mk_empty_array_with_capacity(v___x_1845_);
v___x_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1846_);
return v___x_1847_;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1(void){
_start:
{
size_t v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1848_ = ((size_t)5ULL);
v___x_1849_ = lean_unsigned_to_nat(0u);
v___x_1850_ = lean_unsigned_to_nat(32u);
v___x_1851_ = lean_mk_empty_array_with_capacity(v___x_1850_);
v___x_1852_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0);
v___x_1853_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1853_, 0, v___x_1852_);
lean_ctor_set(v___x_1853_, 1, v___x_1851_);
lean_ctor_set(v___x_1853_, 2, v___x_1849_);
lean_ctor_set(v___x_1853_, 3, v___x_1849_);
lean_ctor_set_usize(v___x_1853_, 4, v___x_1848_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(lean_object* v___x_1854_, lean_object* v_x_1855_, size_t v_x_1856_, size_t v_x_1857_){
_start:
{
if (lean_obj_tag(v_x_1855_) == 0)
{
lean_object* v_cs_1858_; size_t v_j_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; uint8_t v___x_1862_; 
v_cs_1858_ = lean_ctor_get(v_x_1855_, 0);
v_j_1859_ = lean_usize_shift_right(v_x_1856_, v_x_1857_);
v___x_1860_ = lean_usize_to_nat(v_j_1859_);
v___x_1861_ = lean_array_get_size(v_cs_1858_);
v___x_1862_ = lean_nat_dec_lt(v___x_1860_, v___x_1861_);
if (v___x_1862_ == 0)
{
lean_dec(v___x_1860_);
return v_x_1855_;
}
else
{
lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1880_; 
lean_inc_ref(v_cs_1858_);
v_isSharedCheck_1880_ = !lean_is_exclusive(v_x_1855_);
if (v_isSharedCheck_1880_ == 0)
{
lean_object* v_unused_1881_; 
v_unused_1881_ = lean_ctor_get(v_x_1855_, 0);
lean_dec(v_unused_1881_);
v___x_1864_ = v_x_1855_;
v_isShared_1865_ = v_isSharedCheck_1880_;
goto v_resetjp_1863_;
}
else
{
lean_dec(v_x_1855_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1880_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
size_t v___x_1866_; size_t v___x_1867_; size_t v___x_1868_; size_t v_i_1869_; size_t v___x_1870_; size_t v_shift_1871_; lean_object* v_v_1872_; lean_object* v___x_1873_; lean_object* v_xs_x27_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1878_; 
v___x_1866_ = ((size_t)1ULL);
v___x_1867_ = lean_usize_shift_left(v___x_1866_, v_x_1857_);
v___x_1868_ = lean_usize_sub(v___x_1867_, v___x_1866_);
v_i_1869_ = lean_usize_land(v_x_1856_, v___x_1868_);
v___x_1870_ = ((size_t)5ULL);
v_shift_1871_ = lean_usize_sub(v_x_1857_, v___x_1870_);
v_v_1872_ = lean_array_fget(v_cs_1858_, v___x_1860_);
v___x_1873_ = lean_box(0);
v_xs_x27_1874_ = lean_array_fset(v_cs_1858_, v___x_1860_, v___x_1873_);
v___x_1875_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(v___x_1854_, v_v_1872_, v_i_1869_, v_shift_1871_);
v___x_1876_ = lean_array_fset(v_xs_x27_1874_, v___x_1860_, v___x_1875_);
lean_dec(v___x_1860_);
if (v_isShared_1865_ == 0)
{
lean_ctor_set(v___x_1864_, 0, v___x_1876_);
v___x_1878_ = v___x_1864_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v___x_1876_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
else
{
lean_object* v_vs_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; uint8_t v___x_1885_; 
v_vs_1882_ = lean_ctor_get(v_x_1855_, 0);
v___x_1883_ = lean_usize_to_nat(v_x_1856_);
v___x_1884_ = lean_array_get_size(v_vs_1882_);
v___x_1885_ = lean_nat_dec_lt(v___x_1883_, v___x_1884_);
if (v___x_1885_ == 0)
{
lean_dec(v___x_1883_);
return v_x_1855_;
}
else
{
lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1899_; 
lean_inc_ref(v_vs_1882_);
v_isSharedCheck_1899_ = !lean_is_exclusive(v_x_1855_);
if (v_isSharedCheck_1899_ == 0)
{
lean_object* v_unused_1900_; 
v_unused_1900_ = lean_ctor_get(v_x_1855_, 0);
lean_dec(v_unused_1900_);
v___x_1887_ = v_x_1855_;
v_isShared_1888_ = v_isSharedCheck_1899_;
goto v_resetjp_1886_;
}
else
{
lean_dec(v_x_1855_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1899_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v_v_1889_; lean_object* v___x_1890_; lean_object* v_xs_x27_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1897_; 
v_v_1889_ = lean_array_fget(v_vs_1882_, v___x_1883_);
v___x_1890_ = lean_box(0);
v_xs_x27_1891_ = lean_array_fset(v_vs_1882_, v___x_1883_, v___x_1890_);
v___x_1892_ = lean_unsigned_to_nat(0u);
v___x_1893_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1);
v___x_1894_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(v___x_1854_, v_v_1889_, v___x_1893_, v___x_1892_);
lean_dec(v_v_1889_);
v___x_1895_ = lean_array_fset(v_xs_x27_1891_, v___x_1883_, v___x_1894_);
lean_dec(v___x_1883_);
if (v_isShared_1888_ == 0)
{
lean_ctor_set(v___x_1887_, 0, v___x_1895_);
v___x_1897_ = v___x_1887_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v___x_1895_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
return v___x_1897_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___boxed(lean_object* v___x_1901_, lean_object* v_x_1902_, lean_object* v_x_1903_, lean_object* v_x_1904_){
_start:
{
size_t v_x_21799__boxed_1905_; size_t v_x_21800__boxed_1906_; lean_object* v_res_1907_; 
v_x_21799__boxed_1905_ = lean_unbox_usize(v_x_1903_);
lean_dec(v_x_1903_);
v_x_21800__boxed_1906_ = lean_unbox_usize(v_x_1904_);
lean_dec(v_x_1904_);
v_res_1907_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(v___x_1901_, v_x_1902_, v_x_21799__boxed_1905_, v_x_21800__boxed_1906_);
lean_dec_ref(v___x_1901_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1(lean_object* v___x_1908_, lean_object* v_t_1909_, lean_object* v_i_1910_){
_start:
{
lean_object* v_root_1911_; lean_object* v_tail_1912_; lean_object* v_size_1913_; size_t v_shift_1914_; lean_object* v_tailOff_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1943_; 
v_root_1911_ = lean_ctor_get(v_t_1909_, 0);
v_tail_1912_ = lean_ctor_get(v_t_1909_, 1);
v_size_1913_ = lean_ctor_get(v_t_1909_, 2);
v_shift_1914_ = lean_ctor_get_usize(v_t_1909_, 4);
v_tailOff_1915_ = lean_ctor_get(v_t_1909_, 3);
v_isSharedCheck_1943_ = !lean_is_exclusive(v_t_1909_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1917_ = v_t_1909_;
v_isShared_1918_ = v_isSharedCheck_1943_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_tailOff_1915_);
lean_inc(v_size_1913_);
lean_inc(v_tail_1912_);
lean_inc(v_root_1911_);
lean_dec(v_t_1909_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1943_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
uint8_t v___x_1919_; 
v___x_1919_ = lean_nat_dec_le(v_tailOff_1915_, v_i_1910_);
if (v___x_1919_ == 0)
{
size_t v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1923_; 
v___x_1920_ = lean_usize_of_nat(v_i_1910_);
v___x_1921_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(v___x_1908_, v_root_1911_, v___x_1920_, v_shift_1914_);
if (v_isShared_1918_ == 0)
{
lean_ctor_set(v___x_1917_, 0, v___x_1921_);
v___x_1923_ = v___x_1917_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v___x_1921_);
lean_ctor_set(v_reuseFailAlloc_1924_, 1, v_tail_1912_);
lean_ctor_set(v_reuseFailAlloc_1924_, 2, v_size_1913_);
lean_ctor_set(v_reuseFailAlloc_1924_, 3, v_tailOff_1915_);
lean_ctor_set_usize(v_reuseFailAlloc_1924_, 4, v_shift_1914_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
else
{
lean_object* v___x_1925_; lean_object* v___x_1926_; uint8_t v___x_1927_; 
v___x_1925_ = lean_nat_sub(v_i_1910_, v_tailOff_1915_);
v___x_1926_ = lean_array_get_size(v_tail_1912_);
v___x_1927_ = lean_nat_dec_lt(v___x_1925_, v___x_1926_);
if (v___x_1927_ == 0)
{
lean_object* v___x_1929_; 
lean_dec(v___x_1925_);
if (v_isShared_1918_ == 0)
{
v___x_1929_ = v___x_1917_;
goto v_reusejp_1928_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_root_1911_);
lean_ctor_set(v_reuseFailAlloc_1930_, 1, v_tail_1912_);
lean_ctor_set(v_reuseFailAlloc_1930_, 2, v_size_1913_);
lean_ctor_set(v_reuseFailAlloc_1930_, 3, v_tailOff_1915_);
lean_ctor_set_usize(v_reuseFailAlloc_1930_, 4, v_shift_1914_);
v___x_1929_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1928_;
}
v_reusejp_1928_:
{
return v___x_1929_;
}
}
else
{
lean_object* v_v_1931_; lean_object* v___x_1932_; lean_object* v_xs_x27_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1941_; 
v_v_1931_ = lean_array_fget(v_tail_1912_, v___x_1925_);
v___x_1932_ = lean_box(0);
v_xs_x27_1933_ = lean_array_fset(v_tail_1912_, v___x_1925_, v___x_1932_);
v___x_1934_ = lean_unsigned_to_nat(32u);
v___x_1935_ = lean_mk_empty_array_with_capacity(v___x_1934_);
lean_dec_ref(v___x_1935_);
v___x_1936_ = lean_unsigned_to_nat(0u);
v___x_1937_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1);
v___x_1938_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(v___x_1908_, v_v_1931_, v___x_1937_, v___x_1936_);
lean_dec(v_v_1931_);
v___x_1939_ = lean_array_fset(v_xs_x27_1933_, v___x_1925_, v___x_1938_);
lean_dec(v___x_1925_);
if (v_isShared_1918_ == 0)
{
lean_ctor_set(v___x_1917_, 1, v___x_1939_);
v___x_1941_ = v___x_1917_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_root_1911_);
lean_ctor_set(v_reuseFailAlloc_1942_, 1, v___x_1939_);
lean_ctor_set(v_reuseFailAlloc_1942_, 2, v_size_1913_);
lean_ctor_set(v_reuseFailAlloc_1942_, 3, v_tailOff_1915_);
lean_ctor_set_usize(v_reuseFailAlloc_1942_, 4, v_shift_1914_);
v___x_1941_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
return v___x_1941_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1___boxed(lean_object* v___x_1944_, lean_object* v_t_1945_, lean_object* v_i_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1(v___x_1944_, v_t_1945_, v_i_1946_);
lean_dec(v_i_1946_);
lean_dec_ref(v___x_1944_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0(lean_object* v_p_1948_, lean_object* v_x_1949_, lean_object* v_s_1950_){
_start:
{
lean_object* v_vars_1951_; lean_object* v_varMap_1952_; lean_object* v_vars_x27_1953_; lean_object* v_varMap_x27_1954_; lean_object* v_natToIntMap_1955_; lean_object* v_natDef_1956_; lean_object* v_dvds_1957_; lean_object* v_lowers_1958_; lean_object* v_uppers_1959_; lean_object* v_diseqs_1960_; lean_object* v_elimEqs_1961_; lean_object* v_elimStack_1962_; lean_object* v_occurs_1963_; lean_object* v_assignment_1964_; lean_object* v_nextCnstrId_1965_; uint8_t v_caseSplits_1966_; lean_object* v_conflict_x3f_1967_; lean_object* v_diseqSplits_1968_; lean_object* v_divMod_1969_; lean_object* v_toIntIds_1970_; lean_object* v_toIntInfos_1971_; lean_object* v_toIntTermMap_1972_; lean_object* v_toIntVarMap_1973_; uint8_t v_usedCommRing_1974_; lean_object* v_nonlinearOccs_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1983_; 
v_vars_1951_ = lean_ctor_get(v_s_1950_, 0);
v_varMap_1952_ = lean_ctor_get(v_s_1950_, 1);
v_vars_x27_1953_ = lean_ctor_get(v_s_1950_, 2);
v_varMap_x27_1954_ = lean_ctor_get(v_s_1950_, 3);
v_natToIntMap_1955_ = lean_ctor_get(v_s_1950_, 4);
v_natDef_1956_ = lean_ctor_get(v_s_1950_, 5);
v_dvds_1957_ = lean_ctor_get(v_s_1950_, 6);
v_lowers_1958_ = lean_ctor_get(v_s_1950_, 7);
v_uppers_1959_ = lean_ctor_get(v_s_1950_, 8);
v_diseqs_1960_ = lean_ctor_get(v_s_1950_, 9);
v_elimEqs_1961_ = lean_ctor_get(v_s_1950_, 10);
v_elimStack_1962_ = lean_ctor_get(v_s_1950_, 11);
v_occurs_1963_ = lean_ctor_get(v_s_1950_, 12);
v_assignment_1964_ = lean_ctor_get(v_s_1950_, 13);
v_nextCnstrId_1965_ = lean_ctor_get(v_s_1950_, 14);
v_caseSplits_1966_ = lean_ctor_get_uint8(v_s_1950_, sizeof(void*)*23);
v_conflict_x3f_1967_ = lean_ctor_get(v_s_1950_, 15);
v_diseqSplits_1968_ = lean_ctor_get(v_s_1950_, 16);
v_divMod_1969_ = lean_ctor_get(v_s_1950_, 17);
v_toIntIds_1970_ = lean_ctor_get(v_s_1950_, 18);
v_toIntInfos_1971_ = lean_ctor_get(v_s_1950_, 19);
v_toIntTermMap_1972_ = lean_ctor_get(v_s_1950_, 20);
v_toIntVarMap_1973_ = lean_ctor_get(v_s_1950_, 21);
v_usedCommRing_1974_ = lean_ctor_get_uint8(v_s_1950_, sizeof(void*)*23 + 1);
v_nonlinearOccs_1975_ = lean_ctor_get(v_s_1950_, 22);
v_isSharedCheck_1983_ = !lean_is_exclusive(v_s_1950_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1977_ = v_s_1950_;
v_isShared_1978_ = v_isSharedCheck_1983_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_nonlinearOccs_1975_);
lean_inc(v_toIntVarMap_1973_);
lean_inc(v_toIntTermMap_1972_);
lean_inc(v_toIntInfos_1971_);
lean_inc(v_toIntIds_1970_);
lean_inc(v_divMod_1969_);
lean_inc(v_diseqSplits_1968_);
lean_inc(v_conflict_x3f_1967_);
lean_inc(v_nextCnstrId_1965_);
lean_inc(v_assignment_1964_);
lean_inc(v_occurs_1963_);
lean_inc(v_elimStack_1962_);
lean_inc(v_elimEqs_1961_);
lean_inc(v_diseqs_1960_);
lean_inc(v_uppers_1959_);
lean_inc(v_lowers_1958_);
lean_inc(v_dvds_1957_);
lean_inc(v_natDef_1956_);
lean_inc(v_natToIntMap_1955_);
lean_inc(v_varMap_x27_1954_);
lean_inc(v_vars_x27_1953_);
lean_inc(v_varMap_1952_);
lean_inc(v_vars_1951_);
lean_dec(v_s_1950_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1983_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1979_; lean_object* v___x_1981_; 
v___x_1979_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1(v_p_1948_, v_diseqs_1960_, v_x_1949_);
if (v_isShared_1978_ == 0)
{
lean_ctor_set(v___x_1977_, 9, v___x_1979_);
v___x_1981_ = v___x_1977_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v_vars_1951_);
lean_ctor_set(v_reuseFailAlloc_1982_, 1, v_varMap_1952_);
lean_ctor_set(v_reuseFailAlloc_1982_, 2, v_vars_x27_1953_);
lean_ctor_set(v_reuseFailAlloc_1982_, 3, v_varMap_x27_1954_);
lean_ctor_set(v_reuseFailAlloc_1982_, 4, v_natToIntMap_1955_);
lean_ctor_set(v_reuseFailAlloc_1982_, 5, v_natDef_1956_);
lean_ctor_set(v_reuseFailAlloc_1982_, 6, v_dvds_1957_);
lean_ctor_set(v_reuseFailAlloc_1982_, 7, v_lowers_1958_);
lean_ctor_set(v_reuseFailAlloc_1982_, 8, v_uppers_1959_);
lean_ctor_set(v_reuseFailAlloc_1982_, 9, v___x_1979_);
lean_ctor_set(v_reuseFailAlloc_1982_, 10, v_elimEqs_1961_);
lean_ctor_set(v_reuseFailAlloc_1982_, 11, v_elimStack_1962_);
lean_ctor_set(v_reuseFailAlloc_1982_, 12, v_occurs_1963_);
lean_ctor_set(v_reuseFailAlloc_1982_, 13, v_assignment_1964_);
lean_ctor_set(v_reuseFailAlloc_1982_, 14, v_nextCnstrId_1965_);
lean_ctor_set(v_reuseFailAlloc_1982_, 15, v_conflict_x3f_1967_);
lean_ctor_set(v_reuseFailAlloc_1982_, 16, v_diseqSplits_1968_);
lean_ctor_set(v_reuseFailAlloc_1982_, 17, v_divMod_1969_);
lean_ctor_set(v_reuseFailAlloc_1982_, 18, v_toIntIds_1970_);
lean_ctor_set(v_reuseFailAlloc_1982_, 19, v_toIntInfos_1971_);
lean_ctor_set(v_reuseFailAlloc_1982_, 20, v_toIntTermMap_1972_);
lean_ctor_set(v_reuseFailAlloc_1982_, 21, v_toIntVarMap_1973_);
lean_ctor_set(v_reuseFailAlloc_1982_, 22, v_nonlinearOccs_1975_);
lean_ctor_set_uint8(v_reuseFailAlloc_1982_, sizeof(void*)*23, v_caseSplits_1966_);
lean_ctor_set_uint8(v_reuseFailAlloc_1982_, sizeof(void*)*23 + 1, v_usedCommRing_1974_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed(lean_object* v_p_1984_, lean_object* v_x_1985_, lean_object* v_s_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0(v_p_1984_, v_x_1985_, v_s_1986_);
lean_dec(v_x_1985_);
lean_dec_ref(v_p_1984_);
return v_res_1987_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; 
v___x_1994_ = lean_unsigned_to_nat(1u);
v___x_1995_ = lean_nat_to_int(v___x_1994_);
return v___x_1995_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(lean_object* v_c_1996_, lean_object* v_x_1997_, lean_object* v_as_1998_, size_t v_sz_1999_, size_t v_i_2000_, lean_object* v_b_2001_, lean_object* v___y_2002_){
_start:
{
uint8_t v___x_2004_; 
v___x_2004_ = lean_usize_dec_lt(v_i_2000_, v_sz_1999_);
if (v___x_2004_ == 0)
{
lean_object* v___x_2005_; 
lean_dec(v_x_1997_);
lean_dec_ref(v_c_1996_);
v___x_2005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2005_, 0, v_b_2001_);
return v___x_2005_;
}
else
{
lean_object* v_snd_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2052_; 
v_snd_2006_ = lean_ctor_get(v_b_2001_, 1);
v_isSharedCheck_2052_ = !lean_is_exclusive(v_b_2001_);
if (v_isSharedCheck_2052_ == 0)
{
lean_object* v_unused_2053_; 
v_unused_2053_ = lean_ctor_get(v_b_2001_, 0);
lean_dec(v_unused_2053_);
v___x_2008_ = v_b_2001_;
v_isShared_2009_ = v_isSharedCheck_2052_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_snd_2006_);
lean_dec(v_b_2001_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2052_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v_p_2010_; lean_object* v_a_2011_; lean_object* v_p_2012_; lean_object* v___x_2013_; lean_object* v___f_2014_; uint8_t v___y_2016_; uint8_t v___x_2050_; 
v_p_2010_ = lean_ctor_get(v_c_1996_, 0);
v_a_2011_ = lean_array_uget_borrowed(v_as_1998_, v_i_2000_);
v_p_2012_ = lean_ctor_get(v_a_2011_, 0);
v___x_2013_ = lean_box(0);
lean_inc(v_x_1997_);
lean_inc_ref(v_p_2012_);
v___f_2014_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2014_, 0, v_p_2012_);
lean_closure_set(v___f_2014_, 1, v_x_1997_);
v___x_2050_ = l_Int_Linear_instBEqPoly_beq(v_p_2010_, v_p_2012_);
if (v___x_2050_ == 0)
{
uint8_t v___x_2051_; 
v___x_2051_ = l_Int_Linear_Poly_isNegEq(v_p_2010_, v_p_2012_);
v___y_2016_ = v___x_2051_;
goto v___jp_2015_;
}
else
{
v___y_2016_ = v___x_2050_;
goto v___jp_2015_;
}
v___jp_2015_:
{
if (v___y_2016_ == 0)
{
lean_object* v___x_2017_; size_t v___x_2018_; size_t v___x_2019_; 
lean_dec_ref(v___f_2014_);
lean_del_object(v___x_2008_);
lean_dec(v_snd_2006_);
v___x_2017_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__1));
v___x_2018_ = ((size_t)1ULL);
v___x_2019_ = lean_usize_add(v_i_2000_, v___x_2018_);
v_i_2000_ = v___x_2019_;
v_b_2001_ = v___x_2017_;
goto _start;
}
else
{
lean_object* v___x_2021_; lean_object* v___x_2022_; 
lean_dec(v_x_1997_);
v___x_2021_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2022_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2021_, v___f_2014_, v___y_2002_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v___x_2024_; uint8_t v_isShared_2025_; uint8_t v_isSharedCheck_2040_; 
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2040_ == 0)
{
lean_object* v_unused_2041_; 
v_unused_2041_ = lean_ctor_get(v___x_2022_, 0);
lean_dec(v_unused_2041_);
v___x_2024_ = v___x_2022_;
v_isShared_2025_ = v_isSharedCheck_2040_;
goto v_resetjp_2023_;
}
else
{
lean_dec(v___x_2022_);
v___x_2024_ = lean_box(0);
v_isShared_2025_ = v_isSharedCheck_2040_;
goto v_resetjp_2023_;
}
v_resetjp_2023_:
{
lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2033_; 
v___x_2026_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
lean_inc_ref(v_p_2010_);
v___x_2027_ = l_Int_Linear_Poly_addConst(v_p_2010_, v___x_2026_);
lean_inc(v_a_2011_);
v___x_2028_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_2028_, 0, v_c_1996_);
lean_ctor_set(v___x_2028_, 1, v_a_2011_);
v___x_2029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2029_, 0, v___x_2027_);
lean_ctor_set(v___x_2029_, 1, v___x_2028_);
v___x_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2029_);
v___x_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2031_, 0, v___x_2030_);
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 1, v___x_2013_);
lean_ctor_set(v___x_2008_, 0, v___x_2031_);
v___x_2033_ = v___x_2008_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v___x_2031_);
lean_ctor_set(v_reuseFailAlloc_2039_, 1, v___x_2013_);
v___x_2033_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2037_; 
v___x_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2033_);
v___x_2035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2034_);
lean_ctor_set(v___x_2035_, 1, v_snd_2006_);
if (v_isShared_2025_ == 0)
{
lean_ctor_set(v___x_2024_, 0, v___x_2035_);
v___x_2037_ = v___x_2024_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v___x_2035_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
}
else
{
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2049_; 
lean_del_object(v___x_2008_);
lean_dec(v_snd_2006_);
lean_dec_ref(v_c_1996_);
v_a_2042_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2044_ = v___x_2022_;
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_2022_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2047_; 
if (v_isShared_2045_ == 0)
{
v___x_2047_ = v___x_2044_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_a_2042_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___boxed(lean_object* v_c_2054_, lean_object* v_x_2055_, lean_object* v_as_2056_, lean_object* v_sz_2057_, lean_object* v_i_2058_, lean_object* v_b_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_){
_start:
{
size_t v_sz_boxed_2062_; size_t v_i_boxed_2063_; lean_object* v_res_2064_; 
v_sz_boxed_2062_ = lean_unbox_usize(v_sz_2057_);
lean_dec(v_sz_2057_);
v_i_boxed_2063_ = lean_unbox_usize(v_i_2058_);
lean_dec(v_i_2058_);
v_res_2064_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(v_c_2054_, v_x_2055_, v_as_2056_, v_sz_boxed_2062_, v_i_boxed_2063_, v_b_2059_, v___y_2060_);
lean_dec(v___y_2060_);
lean_dec_ref(v_as_2056_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7(lean_object* v_c_2071_, lean_object* v_x_2072_, lean_object* v_as_2073_, size_t v_sz_2074_, size_t v_i_2075_, lean_object* v_b_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_){
_start:
{
uint8_t v___x_2088_; 
v___x_2088_ = lean_usize_dec_lt(v_i_2075_, v_sz_2074_);
if (v___x_2088_ == 0)
{
lean_object* v___x_2089_; 
lean_dec(v_x_2072_);
lean_dec_ref(v_c_2071_);
v___x_2089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2089_, 0, v_b_2076_);
return v___x_2089_;
}
else
{
lean_object* v_snd_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2136_; 
v_snd_2090_ = lean_ctor_get(v_b_2076_, 1);
v_isSharedCheck_2136_ = !lean_is_exclusive(v_b_2076_);
if (v_isSharedCheck_2136_ == 0)
{
lean_object* v_unused_2137_; 
v_unused_2137_ = lean_ctor_get(v_b_2076_, 0);
lean_dec(v_unused_2137_);
v___x_2092_ = v_b_2076_;
v_isShared_2093_ = v_isSharedCheck_2136_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_snd_2090_);
lean_dec(v_b_2076_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2136_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v_p_2094_; lean_object* v_a_2095_; lean_object* v_p_2096_; lean_object* v___x_2097_; lean_object* v___f_2098_; uint8_t v___y_2100_; uint8_t v___x_2134_; 
v_p_2094_ = lean_ctor_get(v_c_2071_, 0);
v_a_2095_ = lean_array_uget_borrowed(v_as_2073_, v_i_2075_);
v_p_2096_ = lean_ctor_get(v_a_2095_, 0);
v___x_2097_ = lean_box(0);
lean_inc(v_x_2072_);
lean_inc_ref(v_p_2096_);
v___f_2098_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2098_, 0, v_p_2096_);
lean_closure_set(v___f_2098_, 1, v_x_2072_);
v___x_2134_ = l_Int_Linear_instBEqPoly_beq(v_p_2094_, v_p_2096_);
if (v___x_2134_ == 0)
{
uint8_t v___x_2135_; 
v___x_2135_ = l_Int_Linear_Poly_isNegEq(v_p_2094_, v_p_2096_);
v___y_2100_ = v___x_2135_;
goto v___jp_2099_;
}
else
{
v___y_2100_ = v___x_2134_;
goto v___jp_2099_;
}
v___jp_2099_:
{
if (v___y_2100_ == 0)
{
lean_object* v___x_2101_; size_t v___x_2102_; size_t v___x_2103_; lean_object* v___x_2104_; 
lean_dec_ref(v___f_2098_);
lean_del_object(v___x_2092_);
lean_dec(v_snd_2090_);
v___x_2101_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___closed__1));
v___x_2102_ = ((size_t)1ULL);
v___x_2103_ = lean_usize_add(v_i_2075_, v___x_2102_);
v___x_2104_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(v_c_2071_, v_x_2072_, v_as_2073_, v_sz_2074_, v___x_2103_, v___x_2101_, v___y_2077_);
return v___x_2104_;
}
else
{
lean_object* v___x_2105_; lean_object* v___x_2106_; 
lean_dec(v_x_2072_);
v___x_2105_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2106_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2105_, v___f_2098_, v___y_2077_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v___x_2108_; uint8_t v_isShared_2109_; uint8_t v_isSharedCheck_2124_; 
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2124_ == 0)
{
lean_object* v_unused_2125_; 
v_unused_2125_ = lean_ctor_get(v___x_2106_, 0);
lean_dec(v_unused_2125_);
v___x_2108_ = v___x_2106_;
v_isShared_2109_ = v_isSharedCheck_2124_;
goto v_resetjp_2107_;
}
else
{
lean_dec(v___x_2106_);
v___x_2108_ = lean_box(0);
v_isShared_2109_ = v_isSharedCheck_2124_;
goto v_resetjp_2107_;
}
v_resetjp_2107_:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2117_; 
v___x_2110_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
lean_inc_ref(v_p_2094_);
v___x_2111_ = l_Int_Linear_Poly_addConst(v_p_2094_, v___x_2110_);
lean_inc(v_a_2095_);
v___x_2112_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_2112_, 0, v_c_2071_);
lean_ctor_set(v___x_2112_, 1, v_a_2095_);
v___x_2113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2111_);
lean_ctor_set(v___x_2113_, 1, v___x_2112_);
v___x_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2113_);
v___x_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 1, v___x_2097_);
lean_ctor_set(v___x_2092_, 0, v___x_2115_);
v___x_2117_ = v___x_2092_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v___x_2115_);
lean_ctor_set(v_reuseFailAlloc_2123_, 1, v___x_2097_);
v___x_2117_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2121_; 
v___x_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
v___x_2119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2118_);
lean_ctor_set(v___x_2119_, 1, v_snd_2090_);
if (v_isShared_2109_ == 0)
{
lean_ctor_set(v___x_2108_, 0, v___x_2119_);
v___x_2121_ = v___x_2108_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v___x_2119_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
}
else
{
lean_object* v_a_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2133_; 
lean_del_object(v___x_2092_);
lean_dec(v_snd_2090_);
lean_dec_ref(v_c_2071_);
v_a_2126_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2128_ = v___x_2106_;
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_a_2126_);
lean_dec(v___x_2106_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2131_; 
if (v_isShared_2129_ == 0)
{
v___x_2131_ = v___x_2128_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_a_2126_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
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
lean_object* v_c_2138_ = _args[0];
lean_object* v_x_2139_ = _args[1];
lean_object* v_as_2140_ = _args[2];
lean_object* v_sz_2141_ = _args[3];
lean_object* v_i_2142_ = _args[4];
lean_object* v_b_2143_ = _args[5];
lean_object* v___y_2144_ = _args[6];
lean_object* v___y_2145_ = _args[7];
lean_object* v___y_2146_ = _args[8];
lean_object* v___y_2147_ = _args[9];
lean_object* v___y_2148_ = _args[10];
lean_object* v___y_2149_ = _args[11];
lean_object* v___y_2150_ = _args[12];
lean_object* v___y_2151_ = _args[13];
lean_object* v___y_2152_ = _args[14];
lean_object* v___y_2153_ = _args[15];
lean_object* v___y_2154_ = _args[16];
_start:
{
size_t v_sz_boxed_2155_; size_t v_i_boxed_2156_; lean_object* v_res_2157_; 
v_sz_boxed_2155_ = lean_unbox_usize(v_sz_2141_);
lean_dec(v_sz_2141_);
v_i_boxed_2156_ = lean_unbox_usize(v_i_2142_);
lean_dec(v_i_2142_);
v_res_2157_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7(v_c_2138_, v_x_2139_, v_as_2140_, v_sz_boxed_2155_, v_i_boxed_2156_, v_b_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_);
lean_dec(v___y_2153_);
lean_dec_ref(v___y_2152_);
lean_dec(v___y_2151_);
lean_dec_ref(v___y_2150_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
lean_dec(v___y_2147_);
lean_dec_ref(v___y_2146_);
lean_dec(v___y_2145_);
lean_dec(v___y_2144_);
lean_dec_ref(v_as_2140_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(lean_object* v_c_2164_, lean_object* v_x_2165_, lean_object* v_as_2166_, size_t v_sz_2167_, size_t v_i_2168_, lean_object* v_b_2169_, lean_object* v___y_2170_){
_start:
{
uint8_t v___x_2172_; 
v___x_2172_ = lean_usize_dec_lt(v_i_2168_, v_sz_2167_);
if (v___x_2172_ == 0)
{
lean_object* v___x_2173_; 
lean_dec(v_x_2165_);
lean_dec_ref(v_c_2164_);
v___x_2173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2173_, 0, v_b_2169_);
return v___x_2173_;
}
else
{
lean_object* v_snd_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2221_; 
v_snd_2174_ = lean_ctor_get(v_b_2169_, 1);
v_isSharedCheck_2221_ = !lean_is_exclusive(v_b_2169_);
if (v_isSharedCheck_2221_ == 0)
{
lean_object* v_unused_2222_; 
v_unused_2222_ = lean_ctor_get(v_b_2169_, 0);
lean_dec(v_unused_2222_);
v___x_2176_ = v_b_2169_;
v_isShared_2177_ = v_isSharedCheck_2221_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_snd_2174_);
lean_dec(v_b_2169_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2221_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v_p_2178_; lean_object* v_a_2179_; lean_object* v_p_2180_; lean_object* v___x_2181_; lean_object* v___f_2182_; uint8_t v___y_2184_; uint8_t v___x_2219_; 
v_p_2178_ = lean_ctor_get(v_c_2164_, 0);
v_a_2179_ = lean_array_uget_borrowed(v_as_2166_, v_i_2168_);
v_p_2180_ = lean_ctor_get(v_a_2179_, 0);
v___x_2181_ = lean_box(0);
lean_inc(v_x_2165_);
lean_inc_ref(v_p_2180_);
v___f_2182_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2182_, 0, v_p_2180_);
lean_closure_set(v___f_2182_, 1, v_x_2165_);
v___x_2219_ = l_Int_Linear_instBEqPoly_beq(v_p_2178_, v_p_2180_);
if (v___x_2219_ == 0)
{
uint8_t v___x_2220_; 
v___x_2220_ = l_Int_Linear_Poly_isNegEq(v_p_2178_, v_p_2180_);
v___y_2184_ = v___x_2220_;
goto v___jp_2183_;
}
else
{
v___y_2184_ = v___x_2219_;
goto v___jp_2183_;
}
v___jp_2183_:
{
if (v___y_2184_ == 0)
{
lean_object* v___x_2185_; size_t v___x_2186_; size_t v___x_2187_; 
lean_dec_ref(v___f_2182_);
lean_del_object(v___x_2176_);
lean_dec(v_snd_2174_);
v___x_2185_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg___closed__1));
v___x_2186_ = ((size_t)1ULL);
v___x_2187_ = lean_usize_add(v_i_2168_, v___x_2186_);
v_i_2168_ = v___x_2187_;
v_b_2169_ = v___x_2185_;
goto _start;
}
else
{
lean_object* v___x_2189_; lean_object* v___x_2190_; 
lean_dec(v_x_2165_);
v___x_2189_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2190_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2189_, v___f_2182_, v___y_2170_);
if (lean_obj_tag(v___x_2190_) == 0)
{
lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2209_; 
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2209_ == 0)
{
lean_object* v_unused_2210_; 
v_unused_2210_ = lean_ctor_get(v___x_2190_, 0);
lean_dec(v_unused_2210_);
v___x_2192_ = v___x_2190_;
v_isShared_2193_ = v_isSharedCheck_2209_;
goto v_resetjp_2191_;
}
else
{
lean_dec(v___x_2190_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2209_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2201_; 
v___x_2194_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
lean_inc_ref(v_p_2178_);
v___x_2195_ = l_Int_Linear_Poly_addConst(v_p_2178_, v___x_2194_);
lean_inc(v_a_2179_);
v___x_2196_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_2196_, 0, v_c_2164_);
lean_ctor_set(v___x_2196_, 1, v_a_2179_);
v___x_2197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2195_);
lean_ctor_set(v___x_2197_, 1, v___x_2196_);
v___x_2198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2198_, 0, v___x_2197_);
v___x_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2198_);
if (v_isShared_2177_ == 0)
{
lean_ctor_set(v___x_2176_, 1, v___x_2181_);
lean_ctor_set(v___x_2176_, 0, v___x_2199_);
v___x_2201_ = v___x_2176_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v___x_2199_);
lean_ctor_set(v_reuseFailAlloc_2208_, 1, v___x_2181_);
v___x_2201_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2206_; 
v___x_2202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2201_);
v___x_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2202_);
v___x_2204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2203_);
lean_ctor_set(v___x_2204_, 1, v_snd_2174_);
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 0, v___x_2204_);
v___x_2206_ = v___x_2192_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v___x_2204_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
}
else
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2218_; 
lean_del_object(v___x_2176_);
lean_dec(v_snd_2174_);
lean_dec_ref(v_c_2164_);
v_a_2211_ = lean_ctor_get(v___x_2190_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___x_2190_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2213_ = v___x_2190_;
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v___x_2190_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2216_; 
if (v_isShared_2214_ == 0)
{
v___x_2216_ = v___x_2213_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_a_2211_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg___boxed(lean_object* v_c_2223_, lean_object* v_x_2224_, lean_object* v_as_2225_, lean_object* v_sz_2226_, lean_object* v_i_2227_, lean_object* v_b_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
size_t v_sz_boxed_2231_; size_t v_i_boxed_2232_; lean_object* v_res_2233_; 
v_sz_boxed_2231_ = lean_unbox_usize(v_sz_2226_);
lean_dec(v_sz_2226_);
v_i_boxed_2232_ = lean_unbox_usize(v_i_2227_);
lean_dec(v_i_2227_);
v_res_2233_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(v_c_2223_, v_x_2224_, v_as_2225_, v_sz_boxed_2231_, v_i_boxed_2232_, v_b_2228_, v___y_2229_);
lean_dec(v___y_2229_);
lean_dec_ref(v_as_2225_);
return v_res_2233_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9(lean_object* v_c_2237_, lean_object* v_x_2238_, lean_object* v_as_2239_, size_t v_sz_2240_, size_t v_i_2241_, lean_object* v_b_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_){
_start:
{
uint8_t v___x_2254_; 
v___x_2254_ = lean_usize_dec_lt(v_i_2241_, v_sz_2240_);
if (v___x_2254_ == 0)
{
lean_object* v___x_2255_; 
lean_dec(v_x_2238_);
lean_dec_ref(v_c_2237_);
v___x_2255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2255_, 0, v_b_2242_);
return v___x_2255_;
}
else
{
lean_object* v_snd_2256_; lean_object* v___x_2258_; uint8_t v_isShared_2259_; uint8_t v_isSharedCheck_2303_; 
v_snd_2256_ = lean_ctor_get(v_b_2242_, 1);
v_isSharedCheck_2303_ = !lean_is_exclusive(v_b_2242_);
if (v_isSharedCheck_2303_ == 0)
{
lean_object* v_unused_2304_; 
v_unused_2304_ = lean_ctor_get(v_b_2242_, 0);
lean_dec(v_unused_2304_);
v___x_2258_ = v_b_2242_;
v_isShared_2259_ = v_isSharedCheck_2303_;
goto v_resetjp_2257_;
}
else
{
lean_inc(v_snd_2256_);
lean_dec(v_b_2242_);
v___x_2258_ = lean_box(0);
v_isShared_2259_ = v_isSharedCheck_2303_;
goto v_resetjp_2257_;
}
v_resetjp_2257_:
{
lean_object* v_p_2260_; lean_object* v_a_2261_; lean_object* v_p_2262_; lean_object* v___x_2263_; lean_object* v___f_2264_; uint8_t v___y_2266_; uint8_t v___x_2301_; 
v_p_2260_ = lean_ctor_get(v_c_2237_, 0);
v_a_2261_ = lean_array_uget_borrowed(v_as_2239_, v_i_2241_);
v_p_2262_ = lean_ctor_get(v_a_2261_, 0);
v___x_2263_ = lean_box(0);
lean_inc(v_x_2238_);
lean_inc_ref(v_p_2262_);
v___f_2264_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2264_, 0, v_p_2262_);
lean_closure_set(v___f_2264_, 1, v_x_2238_);
v___x_2301_ = l_Int_Linear_instBEqPoly_beq(v_p_2260_, v_p_2262_);
if (v___x_2301_ == 0)
{
uint8_t v___x_2302_; 
v___x_2302_ = l_Int_Linear_Poly_isNegEq(v_p_2260_, v_p_2262_);
v___y_2266_ = v___x_2302_;
goto v___jp_2265_;
}
else
{
v___y_2266_ = v___x_2301_;
goto v___jp_2265_;
}
v___jp_2265_:
{
if (v___y_2266_ == 0)
{
lean_object* v___x_2267_; size_t v___x_2268_; size_t v___x_2269_; lean_object* v___x_2270_; 
lean_dec_ref(v___f_2264_);
lean_del_object(v___x_2258_);
lean_dec(v_snd_2256_);
v___x_2267_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9___closed__0));
v___x_2268_ = ((size_t)1ULL);
v___x_2269_ = lean_usize_add(v_i_2241_, v___x_2268_);
v___x_2270_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(v_c_2237_, v_x_2238_, v_as_2239_, v_sz_2240_, v___x_2269_, v___x_2267_, v___y_2243_);
return v___x_2270_;
}
else
{
lean_object* v___x_2271_; lean_object* v___x_2272_; 
lean_dec(v_x_2238_);
v___x_2271_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2272_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2271_, v___f_2264_, v___y_2243_);
if (lean_obj_tag(v___x_2272_) == 0)
{
lean_object* v___x_2274_; uint8_t v_isShared_2275_; uint8_t v_isSharedCheck_2291_; 
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2291_ == 0)
{
lean_object* v_unused_2292_; 
v_unused_2292_ = lean_ctor_get(v___x_2272_, 0);
lean_dec(v_unused_2292_);
v___x_2274_ = v___x_2272_;
v_isShared_2275_ = v_isSharedCheck_2291_;
goto v_resetjp_2273_;
}
else
{
lean_dec(v___x_2272_);
v___x_2274_ = lean_box(0);
v_isShared_2275_ = v_isSharedCheck_2291_;
goto v_resetjp_2273_;
}
v_resetjp_2273_:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2283_; 
v___x_2276_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
lean_inc_ref(v_p_2260_);
v___x_2277_ = l_Int_Linear_Poly_addConst(v_p_2260_, v___x_2276_);
lean_inc(v_a_2261_);
v___x_2278_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_2278_, 0, v_c_2237_);
lean_ctor_set(v___x_2278_, 1, v_a_2261_);
v___x_2279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2279_, 0, v___x_2277_);
lean_ctor_set(v___x_2279_, 1, v___x_2278_);
v___x_2280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2279_);
v___x_2281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2280_);
if (v_isShared_2259_ == 0)
{
lean_ctor_set(v___x_2258_, 1, v___x_2263_);
lean_ctor_set(v___x_2258_, 0, v___x_2281_);
v___x_2283_ = v___x_2258_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v___x_2281_);
lean_ctor_set(v_reuseFailAlloc_2290_, 1, v___x_2263_);
v___x_2283_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2288_; 
v___x_2284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2283_);
v___x_2285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2284_);
v___x_2286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2285_);
lean_ctor_set(v___x_2286_, 1, v_snd_2256_);
if (v_isShared_2275_ == 0)
{
lean_ctor_set(v___x_2274_, 0, v___x_2286_);
v___x_2288_ = v___x_2274_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v___x_2286_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
}
else
{
lean_object* v_a_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2300_; 
lean_del_object(v___x_2258_);
lean_dec(v_snd_2256_);
lean_dec_ref(v_c_2237_);
v_a_2293_ = lean_ctor_get(v___x_2272_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2295_ = v___x_2272_;
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_a_2293_);
lean_dec(v___x_2272_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2298_; 
if (v_isShared_2296_ == 0)
{
v___x_2298_ = v___x_2295_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_a_2293_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
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
lean_object* v_c_2305_ = _args[0];
lean_object* v_x_2306_ = _args[1];
lean_object* v_as_2307_ = _args[2];
lean_object* v_sz_2308_ = _args[3];
lean_object* v_i_2309_ = _args[4];
lean_object* v_b_2310_ = _args[5];
lean_object* v___y_2311_ = _args[6];
lean_object* v___y_2312_ = _args[7];
lean_object* v___y_2313_ = _args[8];
lean_object* v___y_2314_ = _args[9];
lean_object* v___y_2315_ = _args[10];
lean_object* v___y_2316_ = _args[11];
lean_object* v___y_2317_ = _args[12];
lean_object* v___y_2318_ = _args[13];
lean_object* v___y_2319_ = _args[14];
lean_object* v___y_2320_ = _args[15];
lean_object* v___y_2321_ = _args[16];
_start:
{
size_t v_sz_boxed_2322_; size_t v_i_boxed_2323_; lean_object* v_res_2324_; 
v_sz_boxed_2322_ = lean_unbox_usize(v_sz_2308_);
lean_dec(v_sz_2308_);
v_i_boxed_2323_ = lean_unbox_usize(v_i_2309_);
lean_dec(v_i_2309_);
v_res_2324_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9(v_c_2305_, v_x_2306_, v_as_2307_, v_sz_boxed_2322_, v_i_boxed_2323_, v_b_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_);
lean_dec(v___y_2320_);
lean_dec_ref(v___y_2319_);
lean_dec(v___y_2318_);
lean_dec_ref(v___y_2317_);
lean_dec(v___y_2316_);
lean_dec_ref(v___y_2315_);
lean_dec(v___y_2314_);
lean_dec_ref(v___y_2313_);
lean_dec(v___y_2312_);
lean_dec(v___y_2311_);
lean_dec_ref(v_as_2307_);
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(lean_object* v_init_2325_, lean_object* v_c_2326_, lean_object* v_x_2327_, lean_object* v_n_2328_, lean_object* v_b_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_){
_start:
{
if (lean_obj_tag(v_n_2328_) == 0)
{
lean_object* v_cs_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; size_t v_sz_2344_; size_t v___x_2345_; lean_object* v___x_2346_; 
v_cs_2341_ = lean_ctor_get(v_n_2328_, 0);
v___x_2342_ = lean_box(0);
v___x_2343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2342_);
lean_ctor_set(v___x_2343_, 1, v_b_2329_);
v_sz_2344_ = lean_array_size(v_cs_2341_);
v___x_2345_ = ((size_t)0ULL);
v___x_2346_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8(v_init_2325_, v_c_2326_, v_x_2327_, v_cs_2341_, v_sz_2344_, v___x_2345_, v___x_2343_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_);
if (lean_obj_tag(v___x_2346_) == 0)
{
lean_object* v_a_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2361_; 
v_a_2347_ = lean_ctor_get(v___x_2346_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2346_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2349_ = v___x_2346_;
v_isShared_2350_ = v_isSharedCheck_2361_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_a_2347_);
lean_dec(v___x_2346_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2361_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v_fst_2351_; 
v_fst_2351_ = lean_ctor_get(v_a_2347_, 0);
if (lean_obj_tag(v_fst_2351_) == 0)
{
lean_object* v_snd_2352_; lean_object* v___x_2353_; lean_object* v___x_2355_; 
v_snd_2352_ = lean_ctor_get(v_a_2347_, 1);
lean_inc(v_snd_2352_);
lean_dec(v_a_2347_);
v___x_2353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2353_, 0, v_snd_2352_);
if (v_isShared_2350_ == 0)
{
lean_ctor_set(v___x_2349_, 0, v___x_2353_);
v___x_2355_ = v___x_2349_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v___x_2353_);
v___x_2355_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
return v___x_2355_;
}
}
else
{
lean_object* v_val_2357_; lean_object* v___x_2359_; 
lean_inc_ref(v_fst_2351_);
lean_dec(v_a_2347_);
v_val_2357_ = lean_ctor_get(v_fst_2351_, 0);
lean_inc(v_val_2357_);
lean_dec_ref(v_fst_2351_);
if (v_isShared_2350_ == 0)
{
lean_ctor_set(v___x_2349_, 0, v_val_2357_);
v___x_2359_ = v___x_2349_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_val_2357_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
}
else
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2369_; 
v_a_2362_ = lean_ctor_get(v___x_2346_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2346_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2364_ = v___x_2346_;
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2346_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2367_; 
if (v_isShared_2365_ == 0)
{
v___x_2367_ = v___x_2364_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_a_2362_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
}
else
{
lean_object* v_vs_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; size_t v_sz_2373_; size_t v___x_2374_; lean_object* v___x_2375_; 
v_vs_2370_ = lean_ctor_get(v_n_2328_, 0);
v___x_2371_ = lean_box(0);
v___x_2372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2371_);
lean_ctor_set(v___x_2372_, 1, v_b_2329_);
v_sz_2373_ = lean_array_size(v_vs_2370_);
v___x_2374_ = ((size_t)0ULL);
v___x_2375_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9(v_c_2326_, v_x_2327_, v_vs_2370_, v_sz_2373_, v___x_2374_, v___x_2372_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_);
if (lean_obj_tag(v___x_2375_) == 0)
{
lean_object* v_a_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2390_; 
v_a_2376_ = lean_ctor_get(v___x_2375_, 0);
v_isSharedCheck_2390_ = !lean_is_exclusive(v___x_2375_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2378_ = v___x_2375_;
v_isShared_2379_ = v_isSharedCheck_2390_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_dec(v___x_2375_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2390_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v_fst_2380_; 
v_fst_2380_ = lean_ctor_get(v_a_2376_, 0);
if (lean_obj_tag(v_fst_2380_) == 0)
{
lean_object* v_snd_2381_; lean_object* v___x_2382_; lean_object* v___x_2384_; 
v_snd_2381_ = lean_ctor_get(v_a_2376_, 1);
lean_inc(v_snd_2381_);
lean_dec(v_a_2376_);
v___x_2382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2382_, 0, v_snd_2381_);
if (v_isShared_2379_ == 0)
{
lean_ctor_set(v___x_2378_, 0, v___x_2382_);
v___x_2384_ = v___x_2378_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v___x_2382_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
return v___x_2384_;
}
}
else
{
lean_object* v_val_2386_; lean_object* v___x_2388_; 
lean_inc_ref(v_fst_2380_);
lean_dec(v_a_2376_);
v_val_2386_ = lean_ctor_get(v_fst_2380_, 0);
lean_inc(v_val_2386_);
lean_dec_ref(v_fst_2380_);
if (v_isShared_2379_ == 0)
{
lean_ctor_set(v___x_2378_, 0, v_val_2386_);
v___x_2388_ = v___x_2378_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v_val_2386_);
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
lean_object* v_a_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2398_; 
v_a_2391_ = lean_ctor_get(v___x_2375_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2375_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2393_ = v___x_2375_;
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_a_2391_);
lean_dec(v___x_2375_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2398_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2396_; 
if (v_isShared_2394_ == 0)
{
v___x_2396_ = v___x_2393_;
goto v_reusejp_2395_;
}
else
{
lean_object* v_reuseFailAlloc_2397_; 
v_reuseFailAlloc_2397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2397_, 0, v_a_2391_);
v___x_2396_ = v_reuseFailAlloc_2397_;
goto v_reusejp_2395_;
}
v_reusejp_2395_:
{
return v___x_2396_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8(lean_object* v_init_2399_, lean_object* v_c_2400_, lean_object* v_x_2401_, lean_object* v_as_2402_, size_t v_sz_2403_, size_t v_i_2404_, lean_object* v_b_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_){
_start:
{
uint8_t v___x_2417_; 
v___x_2417_ = lean_usize_dec_lt(v_i_2404_, v_sz_2403_);
if (v___x_2417_ == 0)
{
lean_object* v___x_2418_; 
lean_dec(v_x_2401_);
lean_dec_ref(v_c_2400_);
v___x_2418_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2418_, 0, v_b_2405_);
return v___x_2418_;
}
else
{
lean_object* v_snd_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2453_; 
v_snd_2419_ = lean_ctor_get(v_b_2405_, 1);
v_isSharedCheck_2453_ = !lean_is_exclusive(v_b_2405_);
if (v_isSharedCheck_2453_ == 0)
{
lean_object* v_unused_2454_; 
v_unused_2454_ = lean_ctor_get(v_b_2405_, 0);
lean_dec(v_unused_2454_);
v___x_2421_ = v_b_2405_;
v_isShared_2422_ = v_isSharedCheck_2453_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_snd_2419_);
lean_dec(v_b_2405_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2453_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v_a_2423_; lean_object* v___x_2424_; 
v_a_2423_ = lean_array_uget_borrowed(v_as_2402_, v_i_2404_);
lean_inc(v_snd_2419_);
lean_inc(v_x_2401_);
lean_inc_ref(v_c_2400_);
v___x_2424_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(v_init_2399_, v_c_2400_, v_x_2401_, v_a_2423_, v_snd_2419_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
if (lean_obj_tag(v___x_2424_) == 0)
{
lean_object* v_a_2425_; lean_object* v___x_2427_; uint8_t v_isShared_2428_; uint8_t v_isSharedCheck_2444_; 
v_a_2425_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2427_ = v___x_2424_;
v_isShared_2428_ = v_isSharedCheck_2444_;
goto v_resetjp_2426_;
}
else
{
lean_inc(v_a_2425_);
lean_dec(v___x_2424_);
v___x_2427_ = lean_box(0);
v_isShared_2428_ = v_isSharedCheck_2444_;
goto v_resetjp_2426_;
}
v_resetjp_2426_:
{
if (lean_obj_tag(v_a_2425_) == 0)
{
lean_object* v___x_2429_; lean_object* v___x_2431_; 
lean_dec(v_x_2401_);
lean_dec_ref(v_c_2400_);
v___x_2429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2429_, 0, v_a_2425_);
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 0, v___x_2429_);
v___x_2431_ = v___x_2421_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v___x_2429_);
lean_ctor_set(v_reuseFailAlloc_2435_, 1, v_snd_2419_);
v___x_2431_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
lean_object* v___x_2433_; 
if (v_isShared_2428_ == 0)
{
lean_ctor_set(v___x_2427_, 0, v___x_2431_);
v___x_2433_ = v___x_2427_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v___x_2431_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
}
else
{
lean_object* v_a_2436_; lean_object* v___x_2437_; lean_object* v___x_2439_; 
lean_del_object(v___x_2427_);
lean_dec(v_snd_2419_);
v_a_2436_ = lean_ctor_get(v_a_2425_, 0);
lean_inc(v_a_2436_);
lean_dec_ref(v_a_2425_);
v___x_2437_ = lean_box(0);
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 1, v_a_2436_);
lean_ctor_set(v___x_2421_, 0, v___x_2437_);
v___x_2439_ = v___x_2421_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v___x_2437_);
lean_ctor_set(v_reuseFailAlloc_2443_, 1, v_a_2436_);
v___x_2439_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
size_t v___x_2440_; size_t v___x_2441_; 
v___x_2440_ = ((size_t)1ULL);
v___x_2441_ = lean_usize_add(v_i_2404_, v___x_2440_);
v_i_2404_ = v___x_2441_;
v_b_2405_ = v___x_2439_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2452_; 
lean_del_object(v___x_2421_);
lean_dec(v_snd_2419_);
lean_dec(v_x_2401_);
lean_dec_ref(v_c_2400_);
v_a_2445_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2447_ = v___x_2424_;
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_a_2445_);
lean_dec(v___x_2424_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___x_2450_; 
if (v_isShared_2448_ == 0)
{
v___x_2450_ = v___x_2447_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v_a_2445_);
v___x_2450_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
return v___x_2450_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8___boxed(lean_object** _args){
lean_object* v_init_2455_ = _args[0];
lean_object* v_c_2456_ = _args[1];
lean_object* v_x_2457_ = _args[2];
lean_object* v_as_2458_ = _args[3];
lean_object* v_sz_2459_ = _args[4];
lean_object* v_i_2460_ = _args[5];
lean_object* v_b_2461_ = _args[6];
lean_object* v___y_2462_ = _args[7];
lean_object* v___y_2463_ = _args[8];
lean_object* v___y_2464_ = _args[9];
lean_object* v___y_2465_ = _args[10];
lean_object* v___y_2466_ = _args[11];
lean_object* v___y_2467_ = _args[12];
lean_object* v___y_2468_ = _args[13];
lean_object* v___y_2469_ = _args[14];
lean_object* v___y_2470_ = _args[15];
lean_object* v___y_2471_ = _args[16];
lean_object* v___y_2472_ = _args[17];
_start:
{
size_t v_sz_boxed_2473_; size_t v_i_boxed_2474_; lean_object* v_res_2475_; 
v_sz_boxed_2473_ = lean_unbox_usize(v_sz_2459_);
lean_dec(v_sz_2459_);
v_i_boxed_2474_ = lean_unbox_usize(v_i_2460_);
lean_dec(v_i_2460_);
v_res_2475_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8(v_init_2455_, v_c_2456_, v_x_2457_, v_as_2458_, v_sz_boxed_2473_, v_i_boxed_2474_, v_b_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_);
lean_dec(v___y_2471_);
lean_dec_ref(v___y_2470_);
lean_dec(v___y_2469_);
lean_dec_ref(v___y_2468_);
lean_dec(v___y_2467_);
lean_dec_ref(v___y_2466_);
lean_dec(v___y_2465_);
lean_dec_ref(v___y_2464_);
lean_dec(v___y_2463_);
lean_dec(v___y_2462_);
lean_dec_ref(v_as_2458_);
lean_dec_ref(v_init_2455_);
return v_res_2475_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6___boxed(lean_object* v_init_2476_, lean_object* v_c_2477_, lean_object* v_x_2478_, lean_object* v_n_2479_, lean_object* v_b_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_){
_start:
{
lean_object* v_res_2492_; 
v_res_2492_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(v_init_2476_, v_c_2477_, v_x_2478_, v_n_2479_, v_b_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec(v___y_2488_);
lean_dec_ref(v___y_2487_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec(v___y_2482_);
lean_dec(v___y_2481_);
lean_dec_ref(v_n_2479_);
lean_dec_ref(v_init_2476_);
return v_res_2492_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2(lean_object* v_c_2493_, lean_object* v_x_2494_, lean_object* v_t_2495_, lean_object* v_init_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_){
_start:
{
lean_object* v_root_2508_; lean_object* v_tail_2509_; lean_object* v___x_2510_; 
v_root_2508_ = lean_ctor_get(v_t_2495_, 0);
v_tail_2509_ = lean_ctor_get(v_t_2495_, 1);
lean_inc(v_x_2494_);
lean_inc_ref(v_c_2493_);
lean_inc_ref(v_init_2496_);
v___x_2510_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(v_init_2496_, v_c_2493_, v_x_2494_, v_root_2508_, v_init_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_);
lean_dec_ref(v_init_2496_);
if (lean_obj_tag(v___x_2510_) == 0)
{
lean_object* v_a_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2547_; 
v_a_2511_ = lean_ctor_get(v___x_2510_, 0);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2510_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2513_ = v___x_2510_;
v_isShared_2514_ = v_isSharedCheck_2547_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_a_2511_);
lean_dec(v___x_2510_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2547_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
if (lean_obj_tag(v_a_2511_) == 0)
{
lean_object* v_a_2515_; lean_object* v___x_2517_; 
lean_dec(v_x_2494_);
lean_dec_ref(v_c_2493_);
v_a_2515_ = lean_ctor_get(v_a_2511_, 0);
lean_inc(v_a_2515_);
lean_dec_ref(v_a_2511_);
if (v_isShared_2514_ == 0)
{
lean_ctor_set(v___x_2513_, 0, v_a_2515_);
v___x_2517_ = v___x_2513_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_a_2515_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
else
{
lean_object* v_a_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; size_t v_sz_2522_; size_t v___x_2523_; lean_object* v___x_2524_; 
lean_del_object(v___x_2513_);
v_a_2519_ = lean_ctor_get(v_a_2511_, 0);
lean_inc(v_a_2519_);
lean_dec_ref(v_a_2511_);
v___x_2520_ = lean_box(0);
v___x_2521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2520_);
lean_ctor_set(v___x_2521_, 1, v_a_2519_);
v_sz_2522_ = lean_array_size(v_tail_2509_);
v___x_2523_ = ((size_t)0ULL);
v___x_2524_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7(v_c_2493_, v_x_2494_, v_tail_2509_, v_sz_2522_, v___x_2523_, v___x_2521_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_);
if (lean_obj_tag(v___x_2524_) == 0)
{
lean_object* v_a_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2538_; 
v_a_2525_ = lean_ctor_get(v___x_2524_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2527_ = v___x_2524_;
v_isShared_2528_ = v_isSharedCheck_2538_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_a_2525_);
lean_dec(v___x_2524_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2538_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v_fst_2529_; 
v_fst_2529_ = lean_ctor_get(v_a_2525_, 0);
if (lean_obj_tag(v_fst_2529_) == 0)
{
lean_object* v_snd_2530_; lean_object* v___x_2532_; 
v_snd_2530_ = lean_ctor_get(v_a_2525_, 1);
lean_inc(v_snd_2530_);
lean_dec(v_a_2525_);
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 0, v_snd_2530_);
v___x_2532_ = v___x_2527_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_snd_2530_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
else
{
lean_object* v_val_2534_; lean_object* v___x_2536_; 
lean_inc_ref(v_fst_2529_);
lean_dec(v_a_2525_);
v_val_2534_ = lean_ctor_get(v_fst_2529_, 0);
lean_inc(v_val_2534_);
lean_dec_ref(v_fst_2529_);
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 0, v_val_2534_);
v___x_2536_ = v___x_2527_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_val_2534_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
}
}
else
{
lean_object* v_a_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2546_; 
v_a_2539_ = lean_ctor_get(v___x_2524_, 0);
v_isSharedCheck_2546_ = !lean_is_exclusive(v___x_2524_);
if (v_isSharedCheck_2546_ == 0)
{
v___x_2541_ = v___x_2524_;
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_a_2539_);
lean_dec(v___x_2524_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v___x_2544_; 
if (v_isShared_2542_ == 0)
{
v___x_2544_ = v___x_2541_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v_a_2539_);
v___x_2544_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
return v___x_2544_;
}
}
}
}
}
}
else
{
lean_object* v_a_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2555_; 
lean_dec(v_x_2494_);
lean_dec_ref(v_c_2493_);
v_a_2548_ = lean_ctor_get(v___x_2510_, 0);
v_isSharedCheck_2555_ = !lean_is_exclusive(v___x_2510_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2550_ = v___x_2510_;
v_isShared_2551_ = v_isSharedCheck_2555_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_a_2548_);
lean_dec(v___x_2510_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2555_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v___x_2553_; 
if (v_isShared_2551_ == 0)
{
v___x_2553_ = v___x_2550_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_a_2548_);
v___x_2553_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
return v___x_2553_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2___boxed(lean_object* v_c_2556_, lean_object* v_x_2557_, lean_object* v_t_2558_, lean_object* v_init_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_){
_start:
{
lean_object* v_res_2571_; 
v_res_2571_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2(v_c_2556_, v_x_2557_, v_t_2558_, v_init_2559_, v___y_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_);
lean_dec(v___y_2569_);
lean_dec_ref(v___y_2568_);
lean_dec(v___y_2567_);
lean_dec_ref(v___y_2566_);
lean_dec(v___y_2565_);
lean_dec_ref(v___y_2564_);
lean_dec(v___y_2563_);
lean_dec_ref(v___y_2562_);
lean_dec(v___y_2561_);
lean_dec(v___y_2560_);
lean_dec_ref(v_t_2558_);
return v_res_2571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(lean_object* v_x_2572_, lean_object* v_c_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_){
_start:
{
lean_object* v___x_2585_; 
v___x_2585_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2574_, v_a_2582_);
if (lean_obj_tag(v___x_2585_) == 0)
{
lean_object* v_a_2586_; lean_object* v___y_2588_; lean_object* v_diseqs_2613_; lean_object* v_size_2614_; lean_object* v___x_2615_; uint8_t v___x_2616_; 
v_a_2586_ = lean_ctor_get(v___x_2585_, 0);
lean_inc(v_a_2586_);
lean_dec_ref(v___x_2585_);
v_diseqs_2613_ = lean_ctor_get(v_a_2586_, 9);
lean_inc_ref(v_diseqs_2613_);
lean_dec(v_a_2586_);
v_size_2614_ = lean_ctor_get(v_diseqs_2613_, 2);
v___x_2615_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0);
v___x_2616_ = lean_nat_dec_lt(v_x_2572_, v_size_2614_);
if (v___x_2616_ == 0)
{
lean_object* v___x_2617_; 
lean_dec_ref(v_diseqs_2613_);
v___x_2617_ = l_outOfBounds___redArg(v___x_2615_);
v___y_2588_ = v___x_2617_;
goto v___jp_2587_;
}
else
{
lean_object* v___x_2618_; 
v___x_2618_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2615_, v_diseqs_2613_, v_x_2572_);
lean_dec_ref(v_diseqs_2613_);
v___y_2588_ = v___x_2618_;
goto v___jp_2587_;
}
v___jp_2587_:
{
lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2589_ = lean_box(0);
v___x_2590_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___closed__0));
v___x_2591_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2(v_c_2573_, v_x_2572_, v___y_2588_, v___x_2590_, v_a_2574_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_);
lean_dec_ref(v___y_2588_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2604_; 
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2594_ = v___x_2591_;
v_isShared_2595_ = v_isSharedCheck_2604_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2591_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2604_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v_fst_2596_; 
v_fst_2596_ = lean_ctor_get(v_a_2592_, 0);
lean_inc(v_fst_2596_);
lean_dec(v_a_2592_);
if (lean_obj_tag(v_fst_2596_) == 0)
{
lean_object* v___x_2598_; 
if (v_isShared_2595_ == 0)
{
lean_ctor_set(v___x_2594_, 0, v___x_2589_);
v___x_2598_ = v___x_2594_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v___x_2589_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
else
{
lean_object* v_val_2600_; lean_object* v___x_2602_; 
v_val_2600_ = lean_ctor_get(v_fst_2596_, 0);
lean_inc(v_val_2600_);
lean_dec_ref(v_fst_2596_);
if (v_isShared_2595_ == 0)
{
lean_ctor_set(v___x_2594_, 0, v_val_2600_);
v___x_2602_ = v___x_2594_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v_val_2600_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
}
else
{
lean_object* v_a_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2612_; 
v_a_2605_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2607_ = v___x_2591_;
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_a_2605_);
lean_dec(v___x_2591_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2610_; 
if (v_isShared_2608_ == 0)
{
v___x_2610_ = v___x_2607_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_a_2605_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
}
}
else
{
lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2626_; 
lean_dec_ref(v_c_2573_);
lean_dec(v_x_2572_);
v_a_2619_ = lean_ctor_get(v___x_2585_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2621_ = v___x_2585_;
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2585_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2624_; 
if (v_isShared_2622_ == 0)
{
v___x_2624_ = v___x_2621_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_a_2619_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f___boxed(lean_object* v_x_2627_, lean_object* v_c_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_){
_start:
{
lean_object* v_res_2640_; 
v_res_2640_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(v_x_2627_, v_c_2628_, v_a_2629_, v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_, v_a_2634_, v_a_2635_, v_a_2636_, v_a_2637_, v_a_2638_);
lean_dec(v_a_2638_);
lean_dec_ref(v_a_2637_);
lean_dec(v_a_2636_);
lean_dec_ref(v_a_2635_);
lean_dec(v_a_2634_);
lean_dec_ref(v_a_2633_);
lean_dec(v_a_2632_);
lean_dec_ref(v_a_2631_);
lean_dec(v_a_2630_);
lean_dec(v_a_2629_);
return v_res_2640_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11(lean_object* v_c_2641_, lean_object* v_x_2642_, lean_object* v_as_2643_, size_t v_sz_2644_, size_t v_i_2645_, lean_object* v_b_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_){
_start:
{
lean_object* v___x_2658_; 
v___x_2658_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(v_c_2641_, v_x_2642_, v_as_2643_, v_sz_2644_, v_i_2645_, v_b_2646_, v___y_2647_);
return v___x_2658_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___boxed(lean_object** _args){
lean_object* v_c_2659_ = _args[0];
lean_object* v_x_2660_ = _args[1];
lean_object* v_as_2661_ = _args[2];
lean_object* v_sz_2662_ = _args[3];
lean_object* v_i_2663_ = _args[4];
lean_object* v_b_2664_ = _args[5];
lean_object* v___y_2665_ = _args[6];
lean_object* v___y_2666_ = _args[7];
lean_object* v___y_2667_ = _args[8];
lean_object* v___y_2668_ = _args[9];
lean_object* v___y_2669_ = _args[10];
lean_object* v___y_2670_ = _args[11];
lean_object* v___y_2671_ = _args[12];
lean_object* v___y_2672_ = _args[13];
lean_object* v___y_2673_ = _args[14];
lean_object* v___y_2674_ = _args[15];
lean_object* v___y_2675_ = _args[16];
_start:
{
size_t v_sz_boxed_2676_; size_t v_i_boxed_2677_; lean_object* v_res_2678_; 
v_sz_boxed_2676_ = lean_unbox_usize(v_sz_2662_);
lean_dec(v_sz_2662_);
v_i_boxed_2677_ = lean_unbox_usize(v_i_2663_);
lean_dec(v_i_2663_);
v_res_2678_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11(v_c_2659_, v_x_2660_, v_as_2661_, v_sz_boxed_2676_, v_i_boxed_2677_, v_b_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
lean_dec(v___y_2672_);
lean_dec_ref(v___y_2671_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
lean_dec(v___y_2666_);
lean_dec(v___y_2665_);
lean_dec_ref(v_as_2661_);
return v_res_2678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10(lean_object* v_c_2679_, lean_object* v_x_2680_, lean_object* v_as_2681_, size_t v_sz_2682_, size_t v_i_2683_, lean_object* v_b_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_){
_start:
{
lean_object* v___x_2696_; 
v___x_2696_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(v_c_2679_, v_x_2680_, v_as_2681_, v_sz_2682_, v_i_2683_, v_b_2684_, v___y_2685_);
return v___x_2696_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___boxed(lean_object** _args){
lean_object* v_c_2697_ = _args[0];
lean_object* v_x_2698_ = _args[1];
lean_object* v_as_2699_ = _args[2];
lean_object* v_sz_2700_ = _args[3];
lean_object* v_i_2701_ = _args[4];
lean_object* v_b_2702_ = _args[5];
lean_object* v___y_2703_ = _args[6];
lean_object* v___y_2704_ = _args[7];
lean_object* v___y_2705_ = _args[8];
lean_object* v___y_2706_ = _args[9];
lean_object* v___y_2707_ = _args[10];
lean_object* v___y_2708_ = _args[11];
lean_object* v___y_2709_ = _args[12];
lean_object* v___y_2710_ = _args[13];
lean_object* v___y_2711_ = _args[14];
lean_object* v___y_2712_ = _args[15];
lean_object* v___y_2713_ = _args[16];
_start:
{
size_t v_sz_boxed_2714_; size_t v_i_boxed_2715_; lean_object* v_res_2716_; 
v_sz_boxed_2714_ = lean_unbox_usize(v_sz_2700_);
lean_dec(v_sz_2700_);
v_i_boxed_2715_ = lean_unbox_usize(v_i_2701_);
lean_dec(v_i_2701_);
v_res_2716_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10(v_c_2697_, v_x_2698_, v_as_2699_, v_sz_boxed_2714_, v_i_boxed_2715_, v_b_2702_, v___y_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_);
lean_dec(v___y_2712_);
lean_dec_ref(v___y_2711_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
lean_dec(v___y_2706_);
lean_dec_ref(v___y_2705_);
lean_dec(v___y_2704_);
lean_dec(v___y_2703_);
lean_dec_ref(v_as_2699_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0(lean_object* v_v_2717_, lean_object* v_b_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_){
_start:
{
lean_object* v_snd_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2761_; 
v_snd_2730_ = lean_ctor_get(v_b_2718_, 1);
v_isSharedCheck_2761_ = !lean_is_exclusive(v_b_2718_);
if (v_isSharedCheck_2761_ == 0)
{
lean_object* v_unused_2762_; 
v_unused_2762_ = lean_ctor_get(v_b_2718_, 0);
lean_dec(v_unused_2762_);
v___x_2732_ = v_b_2718_;
v_isShared_2733_ = v_isSharedCheck_2761_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_snd_2730_);
lean_dec(v_b_2718_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2761_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2734_; 
lean_inc(v_snd_2730_);
lean_inc(v_v_2717_);
v___x_2734_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(v_v_2717_, v_snd_2730_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_);
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_object* v_a_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2752_; 
v_a_2735_ = lean_ctor_get(v___x_2734_, 0);
v_isSharedCheck_2752_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2737_ = v___x_2734_;
v_isShared_2738_ = v_isSharedCheck_2752_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_a_2735_);
lean_dec(v___x_2734_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2752_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
if (lean_obj_tag(v_a_2735_) == 1)
{
lean_object* v_val_2739_; lean_object* v___x_2740_; lean_object* v___x_2742_; 
lean_del_object(v___x_2737_);
lean_dec(v_snd_2730_);
v_val_2739_ = lean_ctor_get(v_a_2735_, 0);
lean_inc(v_val_2739_);
lean_dec_ref(v_a_2735_);
v___x_2740_ = lean_box(0);
if (v_isShared_2733_ == 0)
{
lean_ctor_set(v___x_2732_, 1, v_val_2739_);
lean_ctor_set(v___x_2732_, 0, v___x_2740_);
v___x_2742_ = v___x_2732_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v___x_2740_);
lean_ctor_set(v_reuseFailAlloc_2744_, 1, v_val_2739_);
v___x_2742_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
v_b_2718_ = v___x_2742_;
goto _start;
}
}
else
{
lean_object* v___x_2745_; lean_object* v___x_2747_; 
lean_dec(v_a_2735_);
lean_dec(v_v_2717_);
lean_inc(v_snd_2730_);
v___x_2745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2745_, 0, v_snd_2730_);
if (v_isShared_2733_ == 0)
{
lean_ctor_set(v___x_2732_, 0, v___x_2745_);
v___x_2747_ = v___x_2732_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v___x_2745_);
lean_ctor_set(v_reuseFailAlloc_2751_, 1, v_snd_2730_);
v___x_2747_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
lean_object* v___x_2749_; 
if (v_isShared_2738_ == 0)
{
lean_ctor_set(v___x_2737_, 0, v___x_2747_);
v___x_2749_ = v___x_2737_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2750_; 
v_reuseFailAlloc_2750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2750_, 0, v___x_2747_);
v___x_2749_ = v_reuseFailAlloc_2750_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
return v___x_2749_;
}
}
}
}
}
else
{
lean_object* v_a_2753_; lean_object* v___x_2755_; uint8_t v_isShared_2756_; uint8_t v_isSharedCheck_2760_; 
lean_del_object(v___x_2732_);
lean_dec(v_snd_2730_);
lean_dec(v_v_2717_);
v_a_2753_ = lean_ctor_get(v___x_2734_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2755_ = v___x_2734_;
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
else
{
lean_inc(v_a_2753_);
lean_dec(v___x_2734_);
v___x_2755_ = lean_box(0);
v_isShared_2756_ = v_isSharedCheck_2760_;
goto v_resetjp_2754_;
}
v_resetjp_2754_:
{
lean_object* v___x_2758_; 
if (v_isShared_2756_ == 0)
{
v___x_2758_ = v___x_2755_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_a_2753_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___boxed(lean_object* v_v_2763_, lean_object* v_b_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_){
_start:
{
lean_object* v_res_2776_; 
v_res_2776_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0(v_v_2763_, v_b_2764_, v___y_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
lean_dec(v___y_2772_);
lean_dec_ref(v___y_2771_);
lean_dec(v___y_2770_);
lean_dec_ref(v___y_2769_);
lean_dec(v___y_2768_);
lean_dec_ref(v___y_2767_);
lean_dec(v___y_2766_);
lean_dec(v___y_2765_);
return v_res_2776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(lean_object* v_c_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_){
_start:
{
lean_object* v_p_2789_; 
v_p_2789_ = lean_ctor_get(v_c_2777_, 0);
if (lean_obj_tag(v_p_2789_) == 1)
{
lean_object* v_v_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
v_v_2790_ = lean_ctor_get(v_p_2789_, 1);
lean_inc(v_v_2790_);
v___x_2791_ = lean_box(0);
v___x_2792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2792_, 0, v___x_2791_);
lean_ctor_set(v___x_2792_, 1, v_c_2777_);
v___x_2793_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0(v_v_2790_, v___x_2792_, v_a_2778_, v_a_2779_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_);
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_object* v_a_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2807_; 
v_a_2794_ = lean_ctor_get(v___x_2793_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2796_ = v___x_2793_;
v_isShared_2797_ = v_isSharedCheck_2807_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_a_2794_);
lean_dec(v___x_2793_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2807_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v_fst_2798_; 
v_fst_2798_ = lean_ctor_get(v_a_2794_, 0);
if (lean_obj_tag(v_fst_2798_) == 0)
{
lean_object* v_snd_2799_; lean_object* v___x_2801_; 
v_snd_2799_ = lean_ctor_get(v_a_2794_, 1);
lean_inc(v_snd_2799_);
lean_dec(v_a_2794_);
if (v_isShared_2797_ == 0)
{
lean_ctor_set(v___x_2796_, 0, v_snd_2799_);
v___x_2801_ = v___x_2796_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_snd_2799_);
v___x_2801_ = v_reuseFailAlloc_2802_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
return v___x_2801_;
}
}
else
{
lean_object* v_val_2803_; lean_object* v___x_2805_; 
lean_inc_ref(v_fst_2798_);
lean_dec(v_a_2794_);
v_val_2803_ = lean_ctor_get(v_fst_2798_, 0);
lean_inc(v_val_2803_);
lean_dec_ref(v_fst_2798_);
if (v_isShared_2797_ == 0)
{
lean_ctor_set(v___x_2796_, 0, v_val_2803_);
v___x_2805_ = v___x_2796_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_val_2803_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
}
else
{
lean_object* v_a_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2815_; 
v_a_2808_ = lean_ctor_get(v___x_2793_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2810_ = v___x_2793_;
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v___x_2793_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___x_2813_; 
if (v_isShared_2811_ == 0)
{
v___x_2813_ = v___x_2810_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_a_2808_);
v___x_2813_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
return v___x_2813_;
}
}
}
}
else
{
lean_object* v___x_2816_; 
v___x_2816_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_2777_, v_a_2778_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_);
return v___x_2816_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq___boxed(lean_object* v_c_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_){
_start:
{
lean_object* v_res_2829_; 
v_res_2829_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(v_c_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_);
lean_dec(v_a_2827_);
lean_dec_ref(v_a_2826_);
lean_dec(v_a_2825_);
lean_dec_ref(v_a_2824_);
lean_dec(v_a_2823_);
lean_dec_ref(v_a_2822_);
lean_dec(v_a_2821_);
lean_dec_ref(v_a_2820_);
lean_dec(v_a_2819_);
lean_dec(v_a_2818_);
return v_res_2829_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(lean_object* v_a_2830_, lean_object* v_x_2831_, size_t v_x_2832_, size_t v_x_2833_){
_start:
{
if (lean_obj_tag(v_x_2831_) == 0)
{
lean_object* v_cs_2834_; size_t v_j_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; uint8_t v___x_2838_; 
v_cs_2834_ = lean_ctor_get(v_x_2831_, 0);
v_j_2835_ = lean_usize_shift_right(v_x_2832_, v_x_2833_);
v___x_2836_ = lean_usize_to_nat(v_j_2835_);
v___x_2837_ = lean_array_get_size(v_cs_2834_);
v___x_2838_ = lean_nat_dec_lt(v___x_2836_, v___x_2837_);
if (v___x_2838_ == 0)
{
lean_dec(v___x_2836_);
lean_dec_ref(v_a_2830_);
return v_x_2831_;
}
else
{
lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2856_; 
lean_inc_ref(v_cs_2834_);
v_isSharedCheck_2856_ = !lean_is_exclusive(v_x_2831_);
if (v_isSharedCheck_2856_ == 0)
{
lean_object* v_unused_2857_; 
v_unused_2857_ = lean_ctor_get(v_x_2831_, 0);
lean_dec(v_unused_2857_);
v___x_2840_ = v_x_2831_;
v_isShared_2841_ = v_isSharedCheck_2856_;
goto v_resetjp_2839_;
}
else
{
lean_dec(v_x_2831_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2856_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
size_t v___x_2842_; size_t v___x_2843_; size_t v___x_2844_; size_t v_i_2845_; size_t v___x_2846_; size_t v_shift_2847_; lean_object* v_v_2848_; lean_object* v___x_2849_; lean_object* v_xs_x27_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2854_; 
v___x_2842_ = ((size_t)1ULL);
v___x_2843_ = lean_usize_shift_left(v___x_2842_, v_x_2833_);
v___x_2844_ = lean_usize_sub(v___x_2843_, v___x_2842_);
v_i_2845_ = lean_usize_land(v_x_2832_, v___x_2844_);
v___x_2846_ = ((size_t)5ULL);
v_shift_2847_ = lean_usize_sub(v_x_2833_, v___x_2846_);
v_v_2848_ = lean_array_fget(v_cs_2834_, v___x_2836_);
v___x_2849_ = lean_box(0);
v_xs_x27_2850_ = lean_array_fset(v_cs_2834_, v___x_2836_, v___x_2849_);
v___x_2851_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(v_a_2830_, v_v_2848_, v_i_2845_, v_shift_2847_);
v___x_2852_ = lean_array_fset(v_xs_x27_2850_, v___x_2836_, v___x_2851_);
lean_dec(v___x_2836_);
if (v_isShared_2841_ == 0)
{
lean_ctor_set(v___x_2840_, 0, v___x_2852_);
v___x_2854_ = v___x_2840_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v___x_2852_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
return v___x_2854_;
}
}
}
}
else
{
lean_object* v_vs_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; uint8_t v___x_2861_; 
v_vs_2858_ = lean_ctor_get(v_x_2831_, 0);
v___x_2859_ = lean_usize_to_nat(v_x_2832_);
v___x_2860_ = lean_array_get_size(v_vs_2858_);
v___x_2861_ = lean_nat_dec_lt(v___x_2859_, v___x_2860_);
if (v___x_2861_ == 0)
{
lean_dec(v___x_2859_);
lean_dec_ref(v_a_2830_);
return v_x_2831_;
}
else
{
lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2873_; 
lean_inc_ref(v_vs_2858_);
v_isSharedCheck_2873_ = !lean_is_exclusive(v_x_2831_);
if (v_isSharedCheck_2873_ == 0)
{
lean_object* v_unused_2874_; 
v_unused_2874_ = lean_ctor_get(v_x_2831_, 0);
lean_dec(v_unused_2874_);
v___x_2863_ = v_x_2831_;
v_isShared_2864_ = v_isSharedCheck_2873_;
goto v_resetjp_2862_;
}
else
{
lean_dec(v_x_2831_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2873_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v_v_2865_; lean_object* v___x_2866_; lean_object* v_xs_x27_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2871_; 
v_v_2865_ = lean_array_fget(v_vs_2858_, v___x_2859_);
v___x_2866_ = lean_box(0);
v_xs_x27_2867_ = lean_array_fset(v_vs_2858_, v___x_2859_, v___x_2866_);
v___x_2868_ = l_Lean_PersistentArray_push___redArg(v_v_2865_, v_a_2830_);
v___x_2869_ = lean_array_fset(v_xs_x27_2867_, v___x_2859_, v___x_2868_);
lean_dec(v___x_2859_);
if (v_isShared_2864_ == 0)
{
lean_ctor_set(v___x_2863_, 0, v___x_2869_);
v___x_2871_ = v___x_2863_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v___x_2869_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0___boxed(lean_object* v_a_2875_, lean_object* v_x_2876_, lean_object* v_x_2877_, lean_object* v_x_2878_){
_start:
{
size_t v_x_93924__boxed_2879_; size_t v_x_93925__boxed_2880_; lean_object* v_res_2881_; 
v_x_93924__boxed_2879_ = lean_unbox_usize(v_x_2877_);
lean_dec(v_x_2877_);
v_x_93925__boxed_2880_ = lean_unbox_usize(v_x_2878_);
lean_dec(v_x_2878_);
v_res_2881_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(v_a_2875_, v_x_2876_, v_x_93924__boxed_2879_, v_x_93925__boxed_2880_);
return v_res_2881_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(lean_object* v_a_2882_, lean_object* v_t_2883_, lean_object* v_i_2884_){
_start:
{
lean_object* v_root_2885_; lean_object* v_tail_2886_; lean_object* v_size_2887_; size_t v_shift_2888_; lean_object* v_tailOff_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2913_; 
v_root_2885_ = lean_ctor_get(v_t_2883_, 0);
v_tail_2886_ = lean_ctor_get(v_t_2883_, 1);
v_size_2887_ = lean_ctor_get(v_t_2883_, 2);
v_shift_2888_ = lean_ctor_get_usize(v_t_2883_, 4);
v_tailOff_2889_ = lean_ctor_get(v_t_2883_, 3);
v_isSharedCheck_2913_ = !lean_is_exclusive(v_t_2883_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2891_ = v_t_2883_;
v_isShared_2892_ = v_isSharedCheck_2913_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_tailOff_2889_);
lean_inc(v_size_2887_);
lean_inc(v_tail_2886_);
lean_inc(v_root_2885_);
lean_dec(v_t_2883_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2913_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
uint8_t v___x_2893_; 
v___x_2893_ = lean_nat_dec_le(v_tailOff_2889_, v_i_2884_);
if (v___x_2893_ == 0)
{
size_t v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2897_; 
v___x_2894_ = lean_usize_of_nat(v_i_2884_);
v___x_2895_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(v_a_2882_, v_root_2885_, v___x_2894_, v_shift_2888_);
if (v_isShared_2892_ == 0)
{
lean_ctor_set(v___x_2891_, 0, v___x_2895_);
v___x_2897_ = v___x_2891_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v___x_2895_);
lean_ctor_set(v_reuseFailAlloc_2898_, 1, v_tail_2886_);
lean_ctor_set(v_reuseFailAlloc_2898_, 2, v_size_2887_);
lean_ctor_set(v_reuseFailAlloc_2898_, 3, v_tailOff_2889_);
lean_ctor_set_usize(v_reuseFailAlloc_2898_, 4, v_shift_2888_);
v___x_2897_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
return v___x_2897_;
}
}
else
{
lean_object* v___x_2899_; lean_object* v___x_2900_; uint8_t v___x_2901_; 
v___x_2899_ = lean_nat_sub(v_i_2884_, v_tailOff_2889_);
v___x_2900_ = lean_array_get_size(v_tail_2886_);
v___x_2901_ = lean_nat_dec_lt(v___x_2899_, v___x_2900_);
if (v___x_2901_ == 0)
{
lean_object* v___x_2903_; 
lean_dec(v___x_2899_);
lean_dec_ref(v_a_2882_);
if (v_isShared_2892_ == 0)
{
v___x_2903_ = v___x_2891_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_root_2885_);
lean_ctor_set(v_reuseFailAlloc_2904_, 1, v_tail_2886_);
lean_ctor_set(v_reuseFailAlloc_2904_, 2, v_size_2887_);
lean_ctor_set(v_reuseFailAlloc_2904_, 3, v_tailOff_2889_);
lean_ctor_set_usize(v_reuseFailAlloc_2904_, 4, v_shift_2888_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
else
{
lean_object* v_v_2905_; lean_object* v___x_2906_; lean_object* v_xs_x27_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2911_; 
v_v_2905_ = lean_array_fget(v_tail_2886_, v___x_2899_);
v___x_2906_ = lean_box(0);
v_xs_x27_2907_ = lean_array_fset(v_tail_2886_, v___x_2899_, v___x_2906_);
v___x_2908_ = l_Lean_PersistentArray_push___redArg(v_v_2905_, v_a_2882_);
v___x_2909_ = lean_array_fset(v_xs_x27_2907_, v___x_2899_, v___x_2908_);
lean_dec(v___x_2899_);
if (v_isShared_2892_ == 0)
{
lean_ctor_set(v___x_2891_, 1, v___x_2909_);
v___x_2911_ = v___x_2891_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_root_2885_);
lean_ctor_set(v_reuseFailAlloc_2912_, 1, v___x_2909_);
lean_ctor_set(v_reuseFailAlloc_2912_, 2, v_size_2887_);
lean_ctor_set(v_reuseFailAlloc_2912_, 3, v_tailOff_2889_);
lean_ctor_set_usize(v_reuseFailAlloc_2912_, 4, v_shift_2888_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0___boxed(lean_object* v_a_2914_, lean_object* v_t_2915_, lean_object* v_i_2916_){
_start:
{
lean_object* v_res_2917_; 
v_res_2917_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(v_a_2914_, v_t_2915_, v_i_2916_);
lean_dec(v_i_2916_);
return v_res_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0(lean_object* v_a_2918_, lean_object* v_v_2919_, lean_object* v_s_2920_){
_start:
{
lean_object* v_vars_2921_; lean_object* v_varMap_2922_; lean_object* v_vars_x27_2923_; lean_object* v_varMap_x27_2924_; lean_object* v_natToIntMap_2925_; lean_object* v_natDef_2926_; lean_object* v_dvds_2927_; lean_object* v_lowers_2928_; lean_object* v_uppers_2929_; lean_object* v_diseqs_2930_; lean_object* v_elimEqs_2931_; lean_object* v_elimStack_2932_; lean_object* v_occurs_2933_; lean_object* v_assignment_2934_; lean_object* v_nextCnstrId_2935_; uint8_t v_caseSplits_2936_; lean_object* v_conflict_x3f_2937_; lean_object* v_diseqSplits_2938_; lean_object* v_divMod_2939_; lean_object* v_toIntIds_2940_; lean_object* v_toIntInfos_2941_; lean_object* v_toIntTermMap_2942_; lean_object* v_toIntVarMap_2943_; uint8_t v_usedCommRing_2944_; lean_object* v_nonlinearOccs_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2953_; 
v_vars_2921_ = lean_ctor_get(v_s_2920_, 0);
v_varMap_2922_ = lean_ctor_get(v_s_2920_, 1);
v_vars_x27_2923_ = lean_ctor_get(v_s_2920_, 2);
v_varMap_x27_2924_ = lean_ctor_get(v_s_2920_, 3);
v_natToIntMap_2925_ = lean_ctor_get(v_s_2920_, 4);
v_natDef_2926_ = lean_ctor_get(v_s_2920_, 5);
v_dvds_2927_ = lean_ctor_get(v_s_2920_, 6);
v_lowers_2928_ = lean_ctor_get(v_s_2920_, 7);
v_uppers_2929_ = lean_ctor_get(v_s_2920_, 8);
v_diseqs_2930_ = lean_ctor_get(v_s_2920_, 9);
v_elimEqs_2931_ = lean_ctor_get(v_s_2920_, 10);
v_elimStack_2932_ = lean_ctor_get(v_s_2920_, 11);
v_occurs_2933_ = lean_ctor_get(v_s_2920_, 12);
v_assignment_2934_ = lean_ctor_get(v_s_2920_, 13);
v_nextCnstrId_2935_ = lean_ctor_get(v_s_2920_, 14);
v_caseSplits_2936_ = lean_ctor_get_uint8(v_s_2920_, sizeof(void*)*23);
v_conflict_x3f_2937_ = lean_ctor_get(v_s_2920_, 15);
v_diseqSplits_2938_ = lean_ctor_get(v_s_2920_, 16);
v_divMod_2939_ = lean_ctor_get(v_s_2920_, 17);
v_toIntIds_2940_ = lean_ctor_get(v_s_2920_, 18);
v_toIntInfos_2941_ = lean_ctor_get(v_s_2920_, 19);
v_toIntTermMap_2942_ = lean_ctor_get(v_s_2920_, 20);
v_toIntVarMap_2943_ = lean_ctor_get(v_s_2920_, 21);
v_usedCommRing_2944_ = lean_ctor_get_uint8(v_s_2920_, sizeof(void*)*23 + 1);
v_nonlinearOccs_2945_ = lean_ctor_get(v_s_2920_, 22);
v_isSharedCheck_2953_ = !lean_is_exclusive(v_s_2920_);
if (v_isSharedCheck_2953_ == 0)
{
v___x_2947_ = v_s_2920_;
v_isShared_2948_ = v_isSharedCheck_2953_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_nonlinearOccs_2945_);
lean_inc(v_toIntVarMap_2943_);
lean_inc(v_toIntTermMap_2942_);
lean_inc(v_toIntInfos_2941_);
lean_inc(v_toIntIds_2940_);
lean_inc(v_divMod_2939_);
lean_inc(v_diseqSplits_2938_);
lean_inc(v_conflict_x3f_2937_);
lean_inc(v_nextCnstrId_2935_);
lean_inc(v_assignment_2934_);
lean_inc(v_occurs_2933_);
lean_inc(v_elimStack_2932_);
lean_inc(v_elimEqs_2931_);
lean_inc(v_diseqs_2930_);
lean_inc(v_uppers_2929_);
lean_inc(v_lowers_2928_);
lean_inc(v_dvds_2927_);
lean_inc(v_natDef_2926_);
lean_inc(v_natToIntMap_2925_);
lean_inc(v_varMap_x27_2924_);
lean_inc(v_vars_x27_2923_);
lean_inc(v_varMap_2922_);
lean_inc(v_vars_2921_);
lean_dec(v_s_2920_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2953_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2949_; lean_object* v___x_2951_; 
v___x_2949_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(v_a_2918_, v_lowers_2928_, v_v_2919_);
if (v_isShared_2948_ == 0)
{
lean_ctor_set(v___x_2947_, 7, v___x_2949_);
v___x_2951_ = v___x_2947_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_vars_2921_);
lean_ctor_set(v_reuseFailAlloc_2952_, 1, v_varMap_2922_);
lean_ctor_set(v_reuseFailAlloc_2952_, 2, v_vars_x27_2923_);
lean_ctor_set(v_reuseFailAlloc_2952_, 3, v_varMap_x27_2924_);
lean_ctor_set(v_reuseFailAlloc_2952_, 4, v_natToIntMap_2925_);
lean_ctor_set(v_reuseFailAlloc_2952_, 5, v_natDef_2926_);
lean_ctor_set(v_reuseFailAlloc_2952_, 6, v_dvds_2927_);
lean_ctor_set(v_reuseFailAlloc_2952_, 7, v___x_2949_);
lean_ctor_set(v_reuseFailAlloc_2952_, 8, v_uppers_2929_);
lean_ctor_set(v_reuseFailAlloc_2952_, 9, v_diseqs_2930_);
lean_ctor_set(v_reuseFailAlloc_2952_, 10, v_elimEqs_2931_);
lean_ctor_set(v_reuseFailAlloc_2952_, 11, v_elimStack_2932_);
lean_ctor_set(v_reuseFailAlloc_2952_, 12, v_occurs_2933_);
lean_ctor_set(v_reuseFailAlloc_2952_, 13, v_assignment_2934_);
lean_ctor_set(v_reuseFailAlloc_2952_, 14, v_nextCnstrId_2935_);
lean_ctor_set(v_reuseFailAlloc_2952_, 15, v_conflict_x3f_2937_);
lean_ctor_set(v_reuseFailAlloc_2952_, 16, v_diseqSplits_2938_);
lean_ctor_set(v_reuseFailAlloc_2952_, 17, v_divMod_2939_);
lean_ctor_set(v_reuseFailAlloc_2952_, 18, v_toIntIds_2940_);
lean_ctor_set(v_reuseFailAlloc_2952_, 19, v_toIntInfos_2941_);
lean_ctor_set(v_reuseFailAlloc_2952_, 20, v_toIntTermMap_2942_);
lean_ctor_set(v_reuseFailAlloc_2952_, 21, v_toIntVarMap_2943_);
lean_ctor_set(v_reuseFailAlloc_2952_, 22, v_nonlinearOccs_2945_);
lean_ctor_set_uint8(v_reuseFailAlloc_2952_, sizeof(void*)*23, v_caseSplits_2936_);
lean_ctor_set_uint8(v_reuseFailAlloc_2952_, sizeof(void*)*23 + 1, v_usedCommRing_2944_);
v___x_2951_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
return v___x_2951_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0___boxed(lean_object* v_a_2954_, lean_object* v_v_2955_, lean_object* v_s_2956_){
_start:
{
lean_object* v_res_2957_; 
v_res_2957_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0(v_a_2954_, v_v_2955_, v_s_2956_);
lean_dec(v_v_2955_);
return v_res_2957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1(lean_object* v_a_2958_, lean_object* v_v_2959_, lean_object* v_s_2960_){
_start:
{
lean_object* v_vars_2961_; lean_object* v_varMap_2962_; lean_object* v_vars_x27_2963_; lean_object* v_varMap_x27_2964_; lean_object* v_natToIntMap_2965_; lean_object* v_natDef_2966_; lean_object* v_dvds_2967_; lean_object* v_lowers_2968_; lean_object* v_uppers_2969_; lean_object* v_diseqs_2970_; lean_object* v_elimEqs_2971_; lean_object* v_elimStack_2972_; lean_object* v_occurs_2973_; lean_object* v_assignment_2974_; lean_object* v_nextCnstrId_2975_; uint8_t v_caseSplits_2976_; lean_object* v_conflict_x3f_2977_; lean_object* v_diseqSplits_2978_; lean_object* v_divMod_2979_; lean_object* v_toIntIds_2980_; lean_object* v_toIntInfos_2981_; lean_object* v_toIntTermMap_2982_; lean_object* v_toIntVarMap_2983_; uint8_t v_usedCommRing_2984_; lean_object* v_nonlinearOccs_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_2993_; 
v_vars_2961_ = lean_ctor_get(v_s_2960_, 0);
v_varMap_2962_ = lean_ctor_get(v_s_2960_, 1);
v_vars_x27_2963_ = lean_ctor_get(v_s_2960_, 2);
v_varMap_x27_2964_ = lean_ctor_get(v_s_2960_, 3);
v_natToIntMap_2965_ = lean_ctor_get(v_s_2960_, 4);
v_natDef_2966_ = lean_ctor_get(v_s_2960_, 5);
v_dvds_2967_ = lean_ctor_get(v_s_2960_, 6);
v_lowers_2968_ = lean_ctor_get(v_s_2960_, 7);
v_uppers_2969_ = lean_ctor_get(v_s_2960_, 8);
v_diseqs_2970_ = lean_ctor_get(v_s_2960_, 9);
v_elimEqs_2971_ = lean_ctor_get(v_s_2960_, 10);
v_elimStack_2972_ = lean_ctor_get(v_s_2960_, 11);
v_occurs_2973_ = lean_ctor_get(v_s_2960_, 12);
v_assignment_2974_ = lean_ctor_get(v_s_2960_, 13);
v_nextCnstrId_2975_ = lean_ctor_get(v_s_2960_, 14);
v_caseSplits_2976_ = lean_ctor_get_uint8(v_s_2960_, sizeof(void*)*23);
v_conflict_x3f_2977_ = lean_ctor_get(v_s_2960_, 15);
v_diseqSplits_2978_ = lean_ctor_get(v_s_2960_, 16);
v_divMod_2979_ = lean_ctor_get(v_s_2960_, 17);
v_toIntIds_2980_ = lean_ctor_get(v_s_2960_, 18);
v_toIntInfos_2981_ = lean_ctor_get(v_s_2960_, 19);
v_toIntTermMap_2982_ = lean_ctor_get(v_s_2960_, 20);
v_toIntVarMap_2983_ = lean_ctor_get(v_s_2960_, 21);
v_usedCommRing_2984_ = lean_ctor_get_uint8(v_s_2960_, sizeof(void*)*23 + 1);
v_nonlinearOccs_2985_ = lean_ctor_get(v_s_2960_, 22);
v_isSharedCheck_2993_ = !lean_is_exclusive(v_s_2960_);
if (v_isSharedCheck_2993_ == 0)
{
v___x_2987_ = v_s_2960_;
v_isShared_2988_ = v_isSharedCheck_2993_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_nonlinearOccs_2985_);
lean_inc(v_toIntVarMap_2983_);
lean_inc(v_toIntTermMap_2982_);
lean_inc(v_toIntInfos_2981_);
lean_inc(v_toIntIds_2980_);
lean_inc(v_divMod_2979_);
lean_inc(v_diseqSplits_2978_);
lean_inc(v_conflict_x3f_2977_);
lean_inc(v_nextCnstrId_2975_);
lean_inc(v_assignment_2974_);
lean_inc(v_occurs_2973_);
lean_inc(v_elimStack_2972_);
lean_inc(v_elimEqs_2971_);
lean_inc(v_diseqs_2970_);
lean_inc(v_uppers_2969_);
lean_inc(v_lowers_2968_);
lean_inc(v_dvds_2967_);
lean_inc(v_natDef_2966_);
lean_inc(v_natToIntMap_2965_);
lean_inc(v_varMap_x27_2964_);
lean_inc(v_vars_x27_2963_);
lean_inc(v_varMap_2962_);
lean_inc(v_vars_2961_);
lean_dec(v_s_2960_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_2993_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
lean_object* v___x_2989_; lean_object* v___x_2991_; 
v___x_2989_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(v_a_2958_, v_uppers_2969_, v_v_2959_);
if (v_isShared_2988_ == 0)
{
lean_ctor_set(v___x_2987_, 8, v___x_2989_);
v___x_2991_ = v___x_2987_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v_vars_2961_);
lean_ctor_set(v_reuseFailAlloc_2992_, 1, v_varMap_2962_);
lean_ctor_set(v_reuseFailAlloc_2992_, 2, v_vars_x27_2963_);
lean_ctor_set(v_reuseFailAlloc_2992_, 3, v_varMap_x27_2964_);
lean_ctor_set(v_reuseFailAlloc_2992_, 4, v_natToIntMap_2965_);
lean_ctor_set(v_reuseFailAlloc_2992_, 5, v_natDef_2966_);
lean_ctor_set(v_reuseFailAlloc_2992_, 6, v_dvds_2967_);
lean_ctor_set(v_reuseFailAlloc_2992_, 7, v_lowers_2968_);
lean_ctor_set(v_reuseFailAlloc_2992_, 8, v___x_2989_);
lean_ctor_set(v_reuseFailAlloc_2992_, 9, v_diseqs_2970_);
lean_ctor_set(v_reuseFailAlloc_2992_, 10, v_elimEqs_2971_);
lean_ctor_set(v_reuseFailAlloc_2992_, 11, v_elimStack_2972_);
lean_ctor_set(v_reuseFailAlloc_2992_, 12, v_occurs_2973_);
lean_ctor_set(v_reuseFailAlloc_2992_, 13, v_assignment_2974_);
lean_ctor_set(v_reuseFailAlloc_2992_, 14, v_nextCnstrId_2975_);
lean_ctor_set(v_reuseFailAlloc_2992_, 15, v_conflict_x3f_2977_);
lean_ctor_set(v_reuseFailAlloc_2992_, 16, v_diseqSplits_2978_);
lean_ctor_set(v_reuseFailAlloc_2992_, 17, v_divMod_2979_);
lean_ctor_set(v_reuseFailAlloc_2992_, 18, v_toIntIds_2980_);
lean_ctor_set(v_reuseFailAlloc_2992_, 19, v_toIntInfos_2981_);
lean_ctor_set(v_reuseFailAlloc_2992_, 20, v_toIntTermMap_2982_);
lean_ctor_set(v_reuseFailAlloc_2992_, 21, v_toIntVarMap_2983_);
lean_ctor_set(v_reuseFailAlloc_2992_, 22, v_nonlinearOccs_2985_);
lean_ctor_set_uint8(v_reuseFailAlloc_2992_, sizeof(void*)*23, v_caseSplits_2976_);
lean_ctor_set_uint8(v_reuseFailAlloc_2992_, sizeof(void*)*23 + 1, v_usedCommRing_2984_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1___boxed(lean_object* v_a_2994_, lean_object* v_v_2995_, lean_object* v_s_2996_){
_start:
{
lean_object* v_res_2997_; 
v_res_2997_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1(v_a_2994_, v_v_2995_, v_s_2996_);
lean_dec(v_v_2995_);
return v_res_2997_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3(void){
_start:
{
lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; 
v___x_3005_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2));
v___x_3006_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_3007_ = l_Lean_Name_append(v___x_3006_, v___x_3005_);
return v___x_3007_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6(void){
_start:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; 
v___x_3014_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5));
v___x_3015_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_3016_ = l_Lean_Name_append(v___x_3015_, v___x_3014_);
return v___x_3016_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9(void){
_start:
{
lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; 
v___x_3023_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__8));
v___x_3024_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_3025_ = l_Lean_Name_append(v___x_3024_, v___x_3023_);
return v___x_3025_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11(void){
_start:
{
lean_object* v___x_3030_; lean_object* v___x_3031_; lean_object* v___x_3032_; 
v___x_3030_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__10));
v___x_3031_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_3032_ = l_Lean_Name_append(v___x_3031_, v___x_3030_);
return v___x_3032_;
}
}
LEAN_EXPORT lean_object* lean_grind_cutsat_assert_le(lean_object* v_c_3033_, lean_object* v_a_3034_, lean_object* v_a_3035_, lean_object* v_a_3036_, lean_object* v_a_3037_, lean_object* v_a_3038_, lean_object* v_a_3039_, lean_object* v_a_3040_, lean_object* v_a_3041_, lean_object* v_a_3042_, lean_object* v_a_3043_){
_start:
{
lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v___x_3117_; 
v___x_3117_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_3034_, v_a_3042_);
if (lean_obj_tag(v___x_3117_) == 0)
{
lean_object* v_a_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3254_; 
v_a_3118_ = lean_ctor_get(v___x_3117_, 0);
v_isSharedCheck_3254_ = !lean_is_exclusive(v___x_3117_);
if (v_isSharedCheck_3254_ == 0)
{
v___x_3120_ = v___x_3117_;
v_isShared_3121_ = v_isSharedCheck_3254_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_a_3118_);
lean_dec(v___x_3117_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3254_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
uint8_t v___x_3122_; 
v___x_3122_ = lean_unbox(v_a_3118_);
lean_dec(v_a_3118_);
if (v___x_3122_ == 0)
{
lean_object* v_options_3123_; lean_object* v_inheritedTraceOptions_3124_; uint8_t v_hasTrace_3125_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; 
lean_del_object(v___x_3120_);
v_options_3123_ = lean_ctor_get(v_a_3042_, 2);
v_inheritedTraceOptions_3124_ = lean_ctor_get(v_a_3042_, 13);
v_hasTrace_3125_ = lean_ctor_get_uint8(v_options_3123_, sizeof(void*)*1);
if (v_hasTrace_3125_ == 0)
{
v___y_3127_ = v_a_3034_;
v___y_3128_ = v_a_3035_;
v___y_3129_ = v_a_3036_;
v___y_3130_ = v_a_3037_;
v___y_3131_ = v_a_3038_;
v___y_3132_ = v_a_3039_;
v___y_3133_ = v_a_3040_;
v___y_3134_ = v_a_3041_;
v___y_3135_ = v_a_3042_;
v___y_3136_ = v_a_3043_;
goto v___jp_3126_;
}
else
{
lean_object* v___x_3236_; lean_object* v___x_3237_; uint8_t v___x_3238_; 
v___x_3236_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__10));
v___x_3237_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11);
v___x_3238_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3124_, v_options_3123_, v___x_3237_);
if (v___x_3238_ == 0)
{
v___y_3127_ = v_a_3034_;
v___y_3128_ = v_a_3035_;
v___y_3129_ = v_a_3036_;
v___y_3130_ = v_a_3037_;
v___y_3131_ = v_a_3038_;
v___y_3132_ = v_a_3039_;
v___y_3133_ = v_a_3040_;
v___y_3134_ = v_a_3041_;
v___y_3135_ = v_a_3042_;
v___y_3136_ = v_a_3043_;
goto v___jp_3126_;
}
else
{
lean_object* v___x_3239_; 
lean_inc_ref(v_c_3033_);
v___x_3239_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_3033_, v_a_3034_, v_a_3042_);
if (lean_obj_tag(v___x_3239_) == 0)
{
lean_object* v_a_3240_; lean_object* v___x_3241_; 
v_a_3240_ = lean_ctor_get(v___x_3239_, 0);
lean_inc(v_a_3240_);
lean_dec_ref(v___x_3239_);
v___x_3241_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3236_, v_a_3240_, v_a_3040_, v_a_3041_, v_a_3042_, v_a_3043_);
if (lean_obj_tag(v___x_3241_) == 0)
{
lean_dec_ref(v___x_3241_);
v___y_3127_ = v_a_3034_;
v___y_3128_ = v_a_3035_;
v___y_3129_ = v_a_3036_;
v___y_3130_ = v_a_3037_;
v___y_3131_ = v_a_3038_;
v___y_3132_ = v_a_3039_;
v___y_3133_ = v_a_3040_;
v___y_3134_ = v_a_3041_;
v___y_3135_ = v_a_3042_;
v___y_3136_ = v_a_3043_;
goto v___jp_3126_;
}
else
{
lean_dec(v_a_3043_);
lean_dec_ref(v_a_3042_);
lean_dec(v_a_3041_);
lean_dec_ref(v_a_3040_);
lean_dec(v_a_3039_);
lean_dec_ref(v_a_3038_);
lean_dec(v_a_3037_);
lean_dec_ref(v_a_3036_);
lean_dec(v_a_3035_);
lean_dec(v_a_3034_);
lean_dec_ref(v_c_3033_);
return v___x_3241_;
}
}
else
{
lean_object* v_a_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3249_; 
lean_dec(v_a_3043_);
lean_dec_ref(v_a_3042_);
lean_dec(v_a_3041_);
lean_dec_ref(v_a_3040_);
lean_dec(v_a_3039_);
lean_dec_ref(v_a_3038_);
lean_dec(v_a_3037_);
lean_dec_ref(v_a_3036_);
lean_dec(v_a_3035_);
lean_dec(v_a_3034_);
lean_dec_ref(v_c_3033_);
v_a_3242_ = lean_ctor_get(v___x_3239_, 0);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3239_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3244_ = v___x_3239_;
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_a_3242_);
lean_dec(v___x_3239_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3247_; 
if (v_isShared_3245_ == 0)
{
v___x_3247_ = v___x_3244_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v_a_3242_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
return v___x_3247_;
}
}
}
}
}
v___jp_3126_:
{
lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3137_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_norm(v_c_3033_);
lean_inc_ref(v___y_3135_);
v___x_3138_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts(v___x_3137_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_);
if (lean_obj_tag(v___x_3138_) == 0)
{
lean_object* v_a_3139_; lean_object* v_p_3140_; uint8_t v___x_3141_; 
v_a_3139_ = lean_ctor_get(v___x_3138_, 0);
lean_inc(v_a_3139_);
lean_dec_ref(v___x_3138_);
v_p_3140_ = lean_ctor_get(v_a_3139_, 0);
v___x_3141_ = l_Int_Linear_Poly_isUnsatLe(v_p_3140_);
if (v___x_3141_ == 0)
{
uint8_t v___x_3142_; 
v___x_3142_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(v_a_3139_);
if (v___x_3142_ == 0)
{
if (lean_obj_tag(v_p_3140_) == 1)
{
lean_object* v_k_3143_; lean_object* v_v_3144_; lean_object* v___x_3145_; 
v_k_3143_ = lean_ctor_get(v_p_3140_, 0);
lean_inc(v_k_3143_);
v_v_3144_ = lean_ctor_get(v_p_3140_, 1);
lean_inc(v_v_3144_);
lean_inc(v_a_3139_);
v___x_3145_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq(v_a_3139_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_);
if (lean_obj_tag(v___x_3145_) == 0)
{
lean_object* v_a_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3184_; 
v_a_3146_ = lean_ctor_get(v___x_3145_, 0);
v_isSharedCheck_3184_ = !lean_is_exclusive(v___x_3145_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3148_ = v___x_3145_;
v_isShared_3149_ = v_isSharedCheck_3184_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_a_3146_);
lean_dec(v___x_3145_);
v___x_3148_ = lean_box(0);
v_isShared_3149_ = v_isSharedCheck_3184_;
goto v_resetjp_3147_;
}
v_resetjp_3147_:
{
uint8_t v___x_3150_; 
v___x_3150_ = lean_unbox(v_a_3146_);
lean_dec(v_a_3146_);
if (v___x_3150_ == 0)
{
lean_object* v___x_3151_; 
lean_del_object(v___x_3148_);
v___x_3151_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(v_a_3139_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
lean_dec_ref(v___y_3129_);
lean_dec(v___y_3128_);
if (lean_obj_tag(v___x_3151_) == 0)
{
lean_object* v_options_3152_; lean_object* v_a_3153_; lean_object* v_inheritedTraceOptions_3154_; uint8_t v_hasTrace_3155_; lean_object* v___f_3156_; lean_object* v___f_3157_; 
v_options_3152_ = lean_ctor_get(v___y_3135_, 2);
v_a_3153_ = lean_ctor_get(v___x_3151_, 0);
lean_inc_n(v_a_3153_, 3);
lean_dec_ref(v___x_3151_);
v_inheritedTraceOptions_3154_ = lean_ctor_get(v___y_3135_, 13);
v_hasTrace_3155_ = lean_ctor_get_uint8(v_options_3152_, sizeof(void*)*1);
lean_inc_n(v_v_3144_, 2);
v___f_3156_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3156_, 0, v_a_3153_);
lean_closure_set(v___f_3156_, 1, v_v_3144_);
v___f_3157_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3157_, 0, v_a_3153_);
lean_closure_set(v___f_3157_, 1, v_v_3144_);
if (v_hasTrace_3155_ == 0)
{
v___y_3076_ = v___f_3156_;
v___y_3077_ = v_a_3153_;
v___y_3078_ = v_k_3143_;
v___y_3079_ = v___f_3157_;
v___y_3080_ = v_v_3144_;
v___y_3081_ = v___y_3127_;
v___y_3082_ = v___y_3133_;
v___y_3083_ = v___y_3134_;
v___y_3084_ = v___y_3135_;
v___y_3085_ = v___y_3136_;
goto v___jp_3075_;
}
else
{
lean_object* v___x_3158_; lean_object* v___x_3159_; uint8_t v___x_3160_; 
v___x_3158_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2));
v___x_3159_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3);
v___x_3160_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3154_, v_options_3152_, v___x_3159_);
if (v___x_3160_ == 0)
{
v___y_3076_ = v___f_3156_;
v___y_3077_ = v_a_3153_;
v___y_3078_ = v_k_3143_;
v___y_3079_ = v___f_3157_;
v___y_3080_ = v_v_3144_;
v___y_3081_ = v___y_3127_;
v___y_3082_ = v___y_3133_;
v___y_3083_ = v___y_3134_;
v___y_3084_ = v___y_3135_;
v___y_3085_ = v___y_3136_;
goto v___jp_3075_;
}
else
{
lean_object* v___x_3161_; 
lean_inc(v_a_3153_);
v___x_3161_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_a_3153_, v___y_3127_, v___y_3135_);
if (lean_obj_tag(v___x_3161_) == 0)
{
lean_object* v_a_3162_; lean_object* v___x_3163_; 
v_a_3162_ = lean_ctor_get(v___x_3161_, 0);
lean_inc(v_a_3162_);
lean_dec_ref(v___x_3161_);
v___x_3163_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3158_, v_a_3162_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_);
if (lean_obj_tag(v___x_3163_) == 0)
{
lean_dec_ref(v___x_3163_);
v___y_3076_ = v___f_3156_;
v___y_3077_ = v_a_3153_;
v___y_3078_ = v_k_3143_;
v___y_3079_ = v___f_3157_;
v___y_3080_ = v_v_3144_;
v___y_3081_ = v___y_3127_;
v___y_3082_ = v___y_3133_;
v___y_3083_ = v___y_3134_;
v___y_3084_ = v___y_3135_;
v___y_3085_ = v___y_3136_;
goto v___jp_3075_;
}
else
{
lean_dec_ref(v___f_3157_);
lean_dec_ref(v___f_3156_);
lean_dec(v_a_3153_);
lean_dec(v_v_3144_);
lean_dec(v_k_3143_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3127_);
return v___x_3163_;
}
}
else
{
lean_object* v_a_3164_; lean_object* v___x_3166_; uint8_t v_isShared_3167_; uint8_t v_isSharedCheck_3171_; 
lean_dec_ref(v___f_3157_);
lean_dec_ref(v___f_3156_);
lean_dec(v_a_3153_);
lean_dec(v_v_3144_);
lean_dec(v_k_3143_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3127_);
v_a_3164_ = lean_ctor_get(v___x_3161_, 0);
v_isSharedCheck_3171_ = !lean_is_exclusive(v___x_3161_);
if (v_isSharedCheck_3171_ == 0)
{
v___x_3166_ = v___x_3161_;
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
else
{
lean_inc(v_a_3164_);
lean_dec(v___x_3161_);
v___x_3166_ = lean_box(0);
v_isShared_3167_ = v_isSharedCheck_3171_;
goto v_resetjp_3165_;
}
v_resetjp_3165_:
{
lean_object* v___x_3169_; 
if (v_isShared_3167_ == 0)
{
v___x_3169_ = v___x_3166_;
goto v_reusejp_3168_;
}
else
{
lean_object* v_reuseFailAlloc_3170_; 
v_reuseFailAlloc_3170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3170_, 0, v_a_3164_);
v___x_3169_ = v_reuseFailAlloc_3170_;
goto v_reusejp_3168_;
}
v_reusejp_3168_:
{
return v___x_3169_;
}
}
}
}
}
}
else
{
lean_object* v_a_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3179_; 
lean_dec(v_v_3144_);
lean_dec(v_k_3143_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3127_);
v_a_3172_ = lean_ctor_get(v___x_3151_, 0);
v_isSharedCheck_3179_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3179_ == 0)
{
v___x_3174_ = v___x_3151_;
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_a_3172_);
lean_dec(v___x_3151_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3177_; 
if (v_isShared_3175_ == 0)
{
v___x_3177_ = v___x_3174_;
goto v_reusejp_3176_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v_a_3172_);
v___x_3177_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3176_;
}
v_reusejp_3176_:
{
return v___x_3177_;
}
}
}
}
else
{
lean_object* v___x_3180_; lean_object* v___x_3182_; 
lean_dec(v_v_3144_);
lean_dec(v_k_3143_);
lean_dec(v_a_3139_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
lean_dec_ref(v___y_3129_);
lean_dec(v___y_3128_);
lean_dec(v___y_3127_);
v___x_3180_ = lean_box(0);
if (v_isShared_3149_ == 0)
{
lean_ctor_set(v___x_3148_, 0, v___x_3180_);
v___x_3182_ = v___x_3148_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v___x_3180_);
v___x_3182_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
return v___x_3182_;
}
}
}
}
else
{
lean_object* v_a_3185_; lean_object* v___x_3187_; uint8_t v_isShared_3188_; uint8_t v_isSharedCheck_3192_; 
lean_dec(v_v_3144_);
lean_dec(v_k_3143_);
lean_dec(v_a_3139_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
lean_dec_ref(v___y_3129_);
lean_dec(v___y_3128_);
lean_dec(v___y_3127_);
v_a_3185_ = lean_ctor_get(v___x_3145_, 0);
v_isSharedCheck_3192_ = !lean_is_exclusive(v___x_3145_);
if (v_isSharedCheck_3192_ == 0)
{
v___x_3187_ = v___x_3145_;
v_isShared_3188_ = v_isSharedCheck_3192_;
goto v_resetjp_3186_;
}
else
{
lean_inc(v_a_3185_);
lean_dec(v___x_3145_);
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
else
{
lean_object* v___x_3193_; 
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
lean_dec_ref(v___y_3129_);
lean_dec(v___y_3128_);
v___x_3193_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_a_3139_, v___y_3127_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3127_);
return v___x_3193_;
}
}
else
{
lean_object* v_options_3194_; uint8_t v_hasTrace_3195_; 
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
lean_dec_ref(v___y_3129_);
lean_dec(v___y_3128_);
v_options_3194_ = lean_ctor_get(v___y_3135_, 2);
v_hasTrace_3195_ = lean_ctor_get_uint8(v_options_3194_, sizeof(void*)*1);
if (v_hasTrace_3195_ == 0)
{
lean_dec(v_a_3139_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3127_);
goto v___jp_3045_;
}
else
{
lean_object* v_inheritedTraceOptions_3196_; lean_object* v___x_3197_; lean_object* v___x_3198_; uint8_t v___x_3199_; 
v_inheritedTraceOptions_3196_ = lean_ctor_get(v___y_3135_, 13);
v___x_3197_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5));
v___x_3198_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6);
v___x_3199_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3196_, v_options_3194_, v___x_3198_);
if (v___x_3199_ == 0)
{
lean_dec(v_a_3139_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3127_);
goto v___jp_3045_;
}
else
{
lean_object* v___x_3200_; 
v___x_3200_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_a_3139_, v___y_3127_, v___y_3135_);
lean_dec(v___y_3127_);
if (lean_obj_tag(v___x_3200_) == 0)
{
lean_object* v_a_3201_; lean_object* v___x_3202_; 
v_a_3201_ = lean_ctor_get(v___x_3200_, 0);
lean_inc(v_a_3201_);
lean_dec_ref(v___x_3200_);
v___x_3202_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3197_, v_a_3201_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
if (lean_obj_tag(v___x_3202_) == 0)
{
lean_dec_ref(v___x_3202_);
goto v___jp_3045_;
}
else
{
return v___x_3202_;
}
}
else
{
lean_object* v_a_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3210_; 
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
v_a_3203_ = lean_ctor_get(v___x_3200_, 0);
v_isSharedCheck_3210_ = !lean_is_exclusive(v___x_3200_);
if (v_isSharedCheck_3210_ == 0)
{
v___x_3205_ = v___x_3200_;
v_isShared_3206_ = v_isSharedCheck_3210_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_a_3203_);
lean_dec(v___x_3200_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3210_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
lean_object* v___x_3208_; 
if (v_isShared_3206_ == 0)
{
v___x_3208_ = v___x_3205_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v_a_3203_);
v___x_3208_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
return v___x_3208_;
}
}
}
}
}
}
}
else
{
lean_object* v_options_3211_; uint8_t v_hasTrace_3212_; 
v_options_3211_ = lean_ctor_get(v___y_3135_, 2);
v_hasTrace_3212_ = lean_ctor_get_uint8(v_options_3211_, sizeof(void*)*1);
if (v_hasTrace_3212_ == 0)
{
v___y_3095_ = v_a_3139_;
v___y_3096_ = v___y_3127_;
v___y_3097_ = v___y_3128_;
v___y_3098_ = v___y_3129_;
v___y_3099_ = v___y_3130_;
v___y_3100_ = v___y_3131_;
v___y_3101_ = v___y_3132_;
v___y_3102_ = v___y_3133_;
v___y_3103_ = v___y_3134_;
v___y_3104_ = v___y_3135_;
v___y_3105_ = v___y_3136_;
goto v___jp_3094_;
}
else
{
lean_object* v_inheritedTraceOptions_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; uint8_t v___x_3216_; 
v_inheritedTraceOptions_3213_ = lean_ctor_get(v___y_3135_, 13);
v___x_3214_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__8));
v___x_3215_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9);
v___x_3216_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3213_, v_options_3211_, v___x_3215_);
if (v___x_3216_ == 0)
{
v___y_3095_ = v_a_3139_;
v___y_3096_ = v___y_3127_;
v___y_3097_ = v___y_3128_;
v___y_3098_ = v___y_3129_;
v___y_3099_ = v___y_3130_;
v___y_3100_ = v___y_3131_;
v___y_3101_ = v___y_3132_;
v___y_3102_ = v___y_3133_;
v___y_3103_ = v___y_3134_;
v___y_3104_ = v___y_3135_;
v___y_3105_ = v___y_3136_;
goto v___jp_3094_;
}
else
{
lean_object* v___x_3217_; 
lean_inc(v_a_3139_);
v___x_3217_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_a_3139_, v___y_3127_, v___y_3135_);
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_object* v_a_3218_; lean_object* v___x_3219_; 
v_a_3218_ = lean_ctor_get(v___x_3217_, 0);
lean_inc(v_a_3218_);
lean_dec_ref(v___x_3217_);
v___x_3219_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3214_, v_a_3218_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_);
if (lean_obj_tag(v___x_3219_) == 0)
{
lean_dec_ref(v___x_3219_);
v___y_3095_ = v_a_3139_;
v___y_3096_ = v___y_3127_;
v___y_3097_ = v___y_3128_;
v___y_3098_ = v___y_3129_;
v___y_3099_ = v___y_3130_;
v___y_3100_ = v___y_3131_;
v___y_3101_ = v___y_3132_;
v___y_3102_ = v___y_3133_;
v___y_3103_ = v___y_3134_;
v___y_3104_ = v___y_3135_;
v___y_3105_ = v___y_3136_;
goto v___jp_3094_;
}
else
{
lean_dec(v_a_3139_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
lean_dec_ref(v___y_3129_);
lean_dec(v___y_3128_);
lean_dec(v___y_3127_);
return v___x_3219_;
}
}
else
{
lean_object* v_a_3220_; lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3227_; 
lean_dec(v_a_3139_);
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
lean_dec_ref(v___y_3129_);
lean_dec(v___y_3128_);
lean_dec(v___y_3127_);
v_a_3220_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3227_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3227_ == 0)
{
v___x_3222_ = v___x_3217_;
v_isShared_3223_ = v_isSharedCheck_3227_;
goto v_resetjp_3221_;
}
else
{
lean_inc(v_a_3220_);
lean_dec(v___x_3217_);
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
}
}
}
else
{
lean_object* v_a_3228_; lean_object* v___x_3230_; uint8_t v_isShared_3231_; uint8_t v_isSharedCheck_3235_; 
lean_dec(v___y_3136_);
lean_dec_ref(v___y_3135_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
lean_dec_ref(v___y_3129_);
lean_dec(v___y_3128_);
lean_dec(v___y_3127_);
v_a_3228_ = lean_ctor_get(v___x_3138_, 0);
v_isSharedCheck_3235_ = !lean_is_exclusive(v___x_3138_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3230_ = v___x_3138_;
v_isShared_3231_ = v_isSharedCheck_3235_;
goto v_resetjp_3229_;
}
else
{
lean_inc(v_a_3228_);
lean_dec(v___x_3138_);
v___x_3230_ = lean_box(0);
v_isShared_3231_ = v_isSharedCheck_3235_;
goto v_resetjp_3229_;
}
v_resetjp_3229_:
{
lean_object* v___x_3233_; 
if (v_isShared_3231_ == 0)
{
v___x_3233_ = v___x_3230_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v_a_3228_);
v___x_3233_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
return v___x_3233_;
}
}
}
}
}
else
{
lean_object* v___x_3250_; lean_object* v___x_3252_; 
lean_dec(v_a_3043_);
lean_dec_ref(v_a_3042_);
lean_dec(v_a_3041_);
lean_dec_ref(v_a_3040_);
lean_dec(v_a_3039_);
lean_dec_ref(v_a_3038_);
lean_dec(v_a_3037_);
lean_dec_ref(v_a_3036_);
lean_dec(v_a_3035_);
lean_dec(v_a_3034_);
lean_dec_ref(v_c_3033_);
v___x_3250_ = lean_box(0);
if (v_isShared_3121_ == 0)
{
lean_ctor_set(v___x_3120_, 0, v___x_3250_);
v___x_3252_ = v___x_3120_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v___x_3250_);
v___x_3252_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
return v___x_3252_;
}
}
}
}
else
{
lean_object* v_a_3255_; lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3262_; 
lean_dec(v_a_3043_);
lean_dec_ref(v_a_3042_);
lean_dec(v_a_3041_);
lean_dec_ref(v_a_3040_);
lean_dec(v_a_3039_);
lean_dec_ref(v_a_3038_);
lean_dec(v_a_3037_);
lean_dec_ref(v_a_3036_);
lean_dec(v_a_3035_);
lean_dec(v_a_3034_);
lean_dec_ref(v_c_3033_);
v_a_3255_ = lean_ctor_get(v___x_3117_, 0);
v_isSharedCheck_3262_ = !lean_is_exclusive(v___x_3117_);
if (v_isSharedCheck_3262_ == 0)
{
v___x_3257_ = v___x_3117_;
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
else
{
lean_inc(v_a_3255_);
lean_dec(v___x_3117_);
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
v___jp_3045_:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3046_ = lean_box(0);
v___x_3047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3047_, 0, v___x_3046_);
return v___x_3047_;
}
v___jp_3048_:
{
lean_object* v___x_3053_; 
v___x_3053_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(v___y_3049_, v___y_3051_, v___y_3052_);
lean_dec_ref(v___y_3052_);
if (lean_obj_tag(v___x_3053_) == 0)
{
lean_object* v_a_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3066_; 
v_a_3054_ = lean_ctor_get(v___x_3053_, 0);
v_isSharedCheck_3066_ = !lean_is_exclusive(v___x_3053_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3056_ = v___x_3053_;
v_isShared_3057_ = v_isSharedCheck_3066_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_a_3054_);
lean_dec(v___x_3053_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3066_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
uint8_t v___x_3058_; uint8_t v___x_3059_; uint8_t v___x_3060_; 
v___x_3058_ = 0;
v___x_3059_ = lean_unbox(v_a_3054_);
lean_dec(v_a_3054_);
v___x_3060_ = l_Lean_instBEqLBool_beq(v___x_3059_, v___x_3058_);
if (v___x_3060_ == 0)
{
lean_object* v___x_3061_; lean_object* v___x_3063_; 
lean_dec(v___y_3051_);
lean_dec(v___y_3050_);
v___x_3061_ = lean_box(0);
if (v_isShared_3057_ == 0)
{
lean_ctor_set(v___x_3056_, 0, v___x_3061_);
v___x_3063_ = v___x_3056_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v___x_3061_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
else
{
lean_object* v___x_3065_; 
lean_del_object(v___x_3056_);
v___x_3065_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v___y_3050_, v___y_3051_);
lean_dec(v___y_3051_);
return v___x_3065_;
}
}
}
else
{
lean_object* v_a_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3074_; 
lean_dec(v___y_3051_);
lean_dec(v___y_3050_);
v_a_3067_ = lean_ctor_get(v___x_3053_, 0);
v_isSharedCheck_3074_ = !lean_is_exclusive(v___x_3053_);
if (v_isSharedCheck_3074_ == 0)
{
v___x_3069_ = v___x_3053_;
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_a_3067_);
lean_dec(v___x_3053_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3072_; 
if (v_isShared_3070_ == 0)
{
v___x_3072_ = v___x_3069_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_a_3067_);
v___x_3072_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
return v___x_3072_;
}
}
}
}
v___jp_3075_:
{
lean_object* v_p_3086_; lean_object* v___x_3087_; 
v_p_3086_ = lean_ctor_get(v___y_3077_, 0);
lean_inc_ref(v_p_3086_);
v___x_3087_ = l_Int_Linear_Poly_updateOccs___redArg(v_p_3086_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_);
lean_dec(v___y_3085_);
lean_dec(v___y_3083_);
lean_dec_ref(v___y_3082_);
if (lean_obj_tag(v___x_3087_) == 0)
{
lean_object* v___x_3088_; uint8_t v___x_3089_; 
lean_dec_ref(v___x_3087_);
v___x_3088_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9);
v___x_3089_ = lean_int_dec_lt(v___y_3078_, v___x_3088_);
lean_dec(v___y_3078_);
if (v___x_3089_ == 0)
{
lean_object* v___x_3090_; lean_object* v___x_3091_; 
lean_dec_ref(v___y_3076_);
v___x_3090_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_3091_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3090_, v___y_3079_, v___y_3081_);
if (lean_obj_tag(v___x_3091_) == 0)
{
lean_dec_ref(v___x_3091_);
v___y_3049_ = v___y_3077_;
v___y_3050_ = v___y_3080_;
v___y_3051_ = v___y_3081_;
v___y_3052_ = v___y_3084_;
goto v___jp_3048_;
}
else
{
lean_dec_ref(v___y_3084_);
lean_dec(v___y_3081_);
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3077_);
return v___x_3091_;
}
}
else
{
lean_object* v___x_3092_; lean_object* v___x_3093_; 
lean_dec_ref(v___y_3079_);
v___x_3092_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_3093_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3092_, v___y_3076_, v___y_3081_);
if (lean_obj_tag(v___x_3093_) == 0)
{
lean_dec_ref(v___x_3093_);
v___y_3049_ = v___y_3077_;
v___y_3050_ = v___y_3080_;
v___y_3051_ = v___y_3081_;
v___y_3052_ = v___y_3084_;
goto v___jp_3048_;
}
else
{
lean_dec_ref(v___y_3084_);
lean_dec(v___y_3081_);
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3077_);
return v___x_3093_;
}
}
}
else
{
lean_dec_ref(v___y_3084_);
lean_dec(v___y_3081_);
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3079_);
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec_ref(v___y_3076_);
return v___x_3087_;
}
}
v___jp_3094_:
{
lean_object* v___x_3106_; lean_object* v___x_3107_; 
v___x_3106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3106_, 0, v___y_3095_);
v___x_3107_ = l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(v___x_3106_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_);
lean_dec(v___y_3105_);
lean_dec_ref(v___y_3104_);
lean_dec(v___y_3103_);
lean_dec_ref(v___y_3102_);
lean_dec(v___y_3101_);
lean_dec_ref(v___y_3100_);
lean_dec(v___y_3099_);
lean_dec_ref(v___y_3098_);
lean_dec(v___y_3097_);
lean_dec(v___y_3096_);
if (lean_obj_tag(v___x_3107_) == 0)
{
lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3115_; 
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3115_ == 0)
{
lean_object* v_unused_3116_; 
v_unused_3116_ = lean_ctor_get(v___x_3107_, 0);
lean_dec(v_unused_3116_);
v___x_3109_ = v___x_3107_;
v_isShared_3110_ = v_isSharedCheck_3115_;
goto v_resetjp_3108_;
}
else
{
lean_dec(v___x_3107_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3115_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v___x_3111_; lean_object* v___x_3113_; 
v___x_3111_ = lean_box(0);
if (v_isShared_3110_ == 0)
{
lean_ctor_set(v___x_3109_, 0, v___x_3111_);
v___x_3113_ = v___x_3109_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v___x_3111_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
}
else
{
return v___x_3107_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___boxed(lean_object* v_c_3263_, lean_object* v_a_3264_, lean_object* v_a_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_, lean_object* v_a_3272_, lean_object* v_a_3273_, lean_object* v_a_3274_){
_start:
{
lean_object* v_res_3275_; 
v_res_3275_ = lean_grind_cutsat_assert_le(v_c_3263_, v_a_3264_, v_a_3265_, v_a_3266_, v_a_3267_, v_a_3268_, v_a_3269_, v_a_3270_, v_a_3271_, v_a_3272_, v_a_3273_);
return v_res_3275_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1(void){
_start:
{
lean_object* v___x_3277_; lean_object* v___x_3278_; 
v___x_3277_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__0));
v___x_3278_ = l_Lean_stringToMessageData(v___x_3277_);
return v___x_3278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(lean_object* v_e_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_){
_start:
{
lean_object* v___x_3287_; 
v___x_3287_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_3280_);
if (lean_obj_tag(v___x_3287_) == 0)
{
lean_object* v_a_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3301_; 
v_a_3288_ = lean_ctor_get(v___x_3287_, 0);
v_isSharedCheck_3301_ = !lean_is_exclusive(v___x_3287_);
if (v_isSharedCheck_3301_ == 0)
{
v___x_3290_ = v___x_3287_;
v_isShared_3291_ = v_isSharedCheck_3301_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_a_3288_);
lean_dec(v___x_3287_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3301_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
uint8_t v___x_3292_; 
v___x_3292_ = lean_unbox(v_a_3288_);
lean_dec(v_a_3288_);
if (v___x_3292_ == 0)
{
lean_object* v___x_3293_; lean_object* v___x_3295_; 
lean_dec_ref(v_e_3279_);
v___x_3293_ = lean_box(0);
if (v_isShared_3291_ == 0)
{
lean_ctor_set(v___x_3290_, 0, v___x_3293_);
v___x_3295_ = v___x_3290_;
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
else
{
lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; 
lean_del_object(v___x_3290_);
v___x_3297_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1);
v___x_3298_ = l_Lean_indentExpr(v_e_3279_);
v___x_3299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3299_, 0, v___x_3297_);
lean_ctor_set(v___x_3299_, 1, v___x_3298_);
v___x_3300_ = l_Lean_Meta_Sym_reportIssue(v___x_3299_, v_a_3280_, v_a_3281_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_);
return v___x_3300_;
}
}
}
else
{
lean_object* v_a_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3309_; 
lean_dec_ref(v_e_3279_);
v_a_3302_ = lean_ctor_get(v___x_3287_, 0);
v_isSharedCheck_3309_ = !lean_is_exclusive(v___x_3287_);
if (v_isSharedCheck_3309_ == 0)
{
v___x_3304_ = v___x_3287_;
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_a_3302_);
lean_dec(v___x_3287_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3309_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___x_3307_; 
if (v_isShared_3305_ == 0)
{
v___x_3307_ = v___x_3304_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3308_; 
v_reuseFailAlloc_3308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3308_, 0, v_a_3302_);
v___x_3307_ = v_reuseFailAlloc_3308_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
return v___x_3307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___boxed(lean_object* v_e_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_){
_start:
{
lean_object* v_res_3318_; 
v_res_3318_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(v_e_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_);
lean_dec(v_a_3316_);
lean_dec_ref(v_a_3315_);
lean_dec(v_a_3314_);
lean_dec_ref(v_a_3313_);
lean_dec(v_a_3312_);
lean_dec_ref(v_a_3311_);
return v_res_3318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized(lean_object* v_e_3319_, lean_object* v_a_3320_, lean_object* v_a_3321_, lean_object* v_a_3322_, lean_object* v_a_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_){
_start:
{
lean_object* v___x_3331_; 
v___x_3331_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(v_e_3319_, v_a_3324_, v_a_3325_, v_a_3326_, v_a_3327_, v_a_3328_, v_a_3329_);
return v___x_3331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___boxed(lean_object* v_e_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_, lean_object* v_a_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_){
_start:
{
lean_object* v_res_3344_; 
v_res_3344_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized(v_e_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_, v_a_3338_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_);
lean_dec(v_a_3342_);
lean_dec_ref(v_a_3341_);
lean_dec(v_a_3340_);
lean_dec_ref(v_a_3339_);
lean_dec(v_a_3338_);
lean_dec_ref(v_a_3337_);
lean_dec(v_a_3336_);
lean_dec_ref(v_a_3335_);
lean_dec(v_a_3334_);
lean_dec(v_a_3333_);
return v_res_3344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f(lean_object* v_e_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_){
_start:
{
lean_object* v___x_3362_; 
lean_inc_ref(v_e_3350_);
v___x_3362_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3350_, v_a_3358_);
if (lean_obj_tag(v___x_3362_) == 0)
{
lean_object* v_a_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3478_; 
v_a_3363_ = lean_ctor_get(v___x_3362_, 0);
v_isSharedCheck_3478_ = !lean_is_exclusive(v___x_3362_);
if (v_isSharedCheck_3478_ == 0)
{
v___x_3365_ = v___x_3362_;
v_isShared_3366_ = v_isSharedCheck_3478_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_a_3363_);
lean_dec(v___x_3362_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3478_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
lean_object* v___x_3372_; uint8_t v___x_3373_; 
v___x_3372_ = l_Lean_Expr_cleanupAnnotations(v_a_3363_);
v___x_3373_ = l_Lean_Expr_isApp(v___x_3372_);
if (v___x_3373_ == 0)
{
lean_dec_ref(v___x_3372_);
lean_dec_ref(v_e_3350_);
goto v___jp_3367_;
}
else
{
lean_object* v_arg_3374_; lean_object* v___x_3375_; uint8_t v___x_3376_; 
v_arg_3374_ = lean_ctor_get(v___x_3372_, 1);
lean_inc_ref(v_arg_3374_);
v___x_3375_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3372_);
v___x_3376_ = l_Lean_Expr_isApp(v___x_3375_);
if (v___x_3376_ == 0)
{
lean_dec_ref(v___x_3375_);
lean_dec_ref(v_arg_3374_);
lean_dec_ref(v_e_3350_);
goto v___jp_3367_;
}
else
{
lean_object* v_arg_3377_; lean_object* v___x_3378_; uint8_t v___x_3379_; 
v_arg_3377_ = lean_ctor_get(v___x_3375_, 1);
lean_inc_ref(v_arg_3377_);
v___x_3378_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3375_);
v___x_3379_ = l_Lean_Expr_isApp(v___x_3378_);
if (v___x_3379_ == 0)
{
lean_dec_ref(v___x_3378_);
lean_dec_ref(v_arg_3377_);
lean_dec_ref(v_arg_3374_);
lean_dec_ref(v_e_3350_);
goto v___jp_3367_;
}
else
{
lean_object* v_arg_3380_; lean_object* v___x_3381_; uint8_t v___x_3382_; 
v_arg_3380_ = lean_ctor_get(v___x_3378_, 1);
lean_inc_ref(v_arg_3380_);
v___x_3381_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3378_);
v___x_3382_ = l_Lean_Expr_isApp(v___x_3381_);
if (v___x_3382_ == 0)
{
lean_dec_ref(v___x_3381_);
lean_dec_ref(v_arg_3380_);
lean_dec_ref(v_arg_3377_);
lean_dec_ref(v_arg_3374_);
lean_dec_ref(v_e_3350_);
goto v___jp_3367_;
}
else
{
lean_object* v___x_3383_; lean_object* v___x_3384_; uint8_t v___x_3385_; 
v___x_3383_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3381_);
v___x_3384_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2));
v___x_3385_ = l_Lean_Expr_isConstOf(v___x_3383_, v___x_3384_);
lean_dec_ref(v___x_3383_);
if (v___x_3385_ == 0)
{
lean_dec_ref(v_arg_3380_);
lean_dec_ref(v_arg_3377_);
lean_dec_ref(v_arg_3374_);
lean_dec_ref(v_e_3350_);
goto v___jp_3367_;
}
else
{
lean_object* v___x_3386_; 
lean_del_object(v___x_3365_);
v___x_3386_ = l_Lean_Meta_Structural_isInstLEInt___redArg(v_arg_3380_, v_a_3358_);
if (lean_obj_tag(v___x_3386_) == 0)
{
lean_object* v_a_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3469_; 
v_a_3387_ = lean_ctor_get(v___x_3386_, 0);
v_isSharedCheck_3469_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3469_ == 0)
{
v___x_3389_ = v___x_3386_;
v_isShared_3390_ = v_isSharedCheck_3469_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_a_3387_);
lean_dec(v___x_3386_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3469_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
uint8_t v___x_3391_; 
v___x_3391_ = lean_unbox(v_a_3387_);
lean_dec(v_a_3387_);
if (v___x_3391_ == 0)
{
lean_object* v___x_3392_; lean_object* v___x_3394_; 
lean_dec_ref(v_arg_3377_);
lean_dec_ref(v_arg_3374_);
lean_dec_ref(v_e_3350_);
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
else
{
lean_object* v___x_3396_; 
lean_del_object(v___x_3389_);
v___x_3396_ = l_Lean_Meta_getIntValue_x3f(v_arg_3374_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_);
if (lean_obj_tag(v___x_3396_) == 0)
{
lean_object* v_a_3397_; 
v_a_3397_ = lean_ctor_get(v___x_3396_, 0);
lean_inc(v_a_3397_);
lean_dec_ref(v___x_3396_);
if (lean_obj_tag(v_a_3397_) == 1)
{
lean_object* v_val_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3442_; 
v_val_3398_ = lean_ctor_get(v_a_3397_, 0);
v_isSharedCheck_3442_ = !lean_is_exclusive(v_a_3397_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3400_ = v_a_3397_;
v_isShared_3401_ = v_isSharedCheck_3442_;
goto v_resetjp_3399_;
}
else
{
lean_inc(v_val_3398_);
lean_dec(v_a_3397_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3442_;
goto v_resetjp_3399_;
}
v_resetjp_3399_:
{
lean_object* v___x_3402_; uint8_t v___x_3403_; 
v___x_3402_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9);
v___x_3403_ = lean_int_dec_eq(v_val_3398_, v___x_3402_);
lean_dec(v_val_3398_);
if (v___x_3403_ == 0)
{
lean_object* v___x_3404_; 
lean_del_object(v___x_3400_);
lean_dec_ref(v_arg_3377_);
v___x_3404_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(v_e_3350_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_);
if (lean_obj_tag(v___x_3404_) == 0)
{
lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3412_; 
v_isSharedCheck_3412_ = !lean_is_exclusive(v___x_3404_);
if (v_isSharedCheck_3412_ == 0)
{
lean_object* v_unused_3413_; 
v_unused_3413_ = lean_ctor_get(v___x_3404_, 0);
lean_dec(v_unused_3413_);
v___x_3406_ = v___x_3404_;
v_isShared_3407_ = v_isSharedCheck_3412_;
goto v_resetjp_3405_;
}
else
{
lean_dec(v___x_3404_);
v___x_3406_ = lean_box(0);
v_isShared_3407_ = v_isSharedCheck_3412_;
goto v_resetjp_3405_;
}
v_resetjp_3405_:
{
lean_object* v___x_3408_; lean_object* v___x_3410_; 
v___x_3408_ = lean_box(0);
if (v_isShared_3407_ == 0)
{
lean_ctor_set(v___x_3406_, 0, v___x_3408_);
v___x_3410_ = v___x_3406_;
goto v_reusejp_3409_;
}
else
{
lean_object* v_reuseFailAlloc_3411_; 
v_reuseFailAlloc_3411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3411_, 0, v___x_3408_);
v___x_3410_ = v_reuseFailAlloc_3411_;
goto v_reusejp_3409_;
}
v_reusejp_3409_:
{
return v___x_3410_;
}
}
}
else
{
lean_object* v_a_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3421_; 
v_a_3414_ = lean_ctor_get(v___x_3404_, 0);
v_isSharedCheck_3421_ = !lean_is_exclusive(v___x_3404_);
if (v_isSharedCheck_3421_ == 0)
{
v___x_3416_ = v___x_3404_;
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
else
{
lean_inc(v_a_3414_);
lean_dec(v___x_3404_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3421_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v___x_3419_; 
if (v_isShared_3417_ == 0)
{
v___x_3419_ = v___x_3416_;
goto v_reusejp_3418_;
}
else
{
lean_object* v_reuseFailAlloc_3420_; 
v_reuseFailAlloc_3420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3420_, 0, v_a_3414_);
v___x_3419_ = v_reuseFailAlloc_3420_;
goto v_reusejp_3418_;
}
v_reusejp_3418_:
{
return v___x_3419_;
}
}
}
}
else
{
lean_object* v___x_3422_; 
lean_dec_ref(v_e_3350_);
v___x_3422_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(v_arg_3377_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_);
if (lean_obj_tag(v___x_3422_) == 0)
{
lean_object* v_a_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3433_; 
v_a_3423_ = lean_ctor_get(v___x_3422_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v___x_3422_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3425_ = v___x_3422_;
v_isShared_3426_ = v_isSharedCheck_3433_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_a_3423_);
lean_dec(v___x_3422_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3433_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v___x_3428_; 
if (v_isShared_3401_ == 0)
{
lean_ctor_set(v___x_3400_, 0, v_a_3423_);
v___x_3428_ = v___x_3400_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v_a_3423_);
v___x_3428_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
lean_object* v___x_3430_; 
if (v_isShared_3426_ == 0)
{
lean_ctor_set(v___x_3425_, 0, v___x_3428_);
v___x_3430_ = v___x_3425_;
goto v_reusejp_3429_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v___x_3428_);
v___x_3430_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3429_;
}
v_reusejp_3429_:
{
return v___x_3430_;
}
}
}
}
else
{
lean_object* v_a_3434_; lean_object* v___x_3436_; uint8_t v_isShared_3437_; uint8_t v_isSharedCheck_3441_; 
lean_del_object(v___x_3400_);
v_a_3434_ = lean_ctor_get(v___x_3422_, 0);
v_isSharedCheck_3441_ = !lean_is_exclusive(v___x_3422_);
if (v_isSharedCheck_3441_ == 0)
{
v___x_3436_ = v___x_3422_;
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
else
{
lean_inc(v_a_3434_);
lean_dec(v___x_3422_);
v___x_3436_ = lean_box(0);
v_isShared_3437_ = v_isSharedCheck_3441_;
goto v_resetjp_3435_;
}
v_resetjp_3435_:
{
lean_object* v___x_3439_; 
if (v_isShared_3437_ == 0)
{
v___x_3439_ = v___x_3436_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3440_; 
v_reuseFailAlloc_3440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3440_, 0, v_a_3434_);
v___x_3439_ = v_reuseFailAlloc_3440_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
return v___x_3439_;
}
}
}
}
}
}
else
{
lean_object* v___x_3443_; 
lean_dec(v_a_3397_);
lean_dec_ref(v_arg_3377_);
v___x_3443_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(v_e_3350_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_);
if (lean_obj_tag(v___x_3443_) == 0)
{
lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3451_; 
v_isSharedCheck_3451_ = !lean_is_exclusive(v___x_3443_);
if (v_isSharedCheck_3451_ == 0)
{
lean_object* v_unused_3452_; 
v_unused_3452_ = lean_ctor_get(v___x_3443_, 0);
lean_dec(v_unused_3452_);
v___x_3445_ = v___x_3443_;
v_isShared_3446_ = v_isSharedCheck_3451_;
goto v_resetjp_3444_;
}
else
{
lean_dec(v___x_3443_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3451_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
lean_object* v___x_3447_; lean_object* v___x_3449_; 
v___x_3447_ = lean_box(0);
if (v_isShared_3446_ == 0)
{
lean_ctor_set(v___x_3445_, 0, v___x_3447_);
v___x_3449_ = v___x_3445_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v___x_3447_);
v___x_3449_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
return v___x_3449_;
}
}
}
else
{
lean_object* v_a_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3460_; 
v_a_3453_ = lean_ctor_get(v___x_3443_, 0);
v_isSharedCheck_3460_ = !lean_is_exclusive(v___x_3443_);
if (v_isSharedCheck_3460_ == 0)
{
v___x_3455_ = v___x_3443_;
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_a_3453_);
lean_dec(v___x_3443_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3460_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3458_; 
if (v_isShared_3456_ == 0)
{
v___x_3458_ = v___x_3455_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v_a_3453_);
v___x_3458_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
return v___x_3458_;
}
}
}
}
}
else
{
lean_object* v_a_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3468_; 
lean_dec_ref(v_arg_3377_);
lean_dec_ref(v_e_3350_);
v_a_3461_ = lean_ctor_get(v___x_3396_, 0);
v_isSharedCheck_3468_ = !lean_is_exclusive(v___x_3396_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3463_ = v___x_3396_;
v_isShared_3464_ = v_isSharedCheck_3468_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_a_3461_);
lean_dec(v___x_3396_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3468_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v___x_3466_; 
if (v_isShared_3464_ == 0)
{
v___x_3466_ = v___x_3463_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_a_3461_);
v___x_3466_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
return v___x_3466_;
}
}
}
}
}
}
else
{
lean_object* v_a_3470_; lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3477_; 
lean_dec_ref(v_arg_3377_);
lean_dec_ref(v_arg_3374_);
lean_dec_ref(v_e_3350_);
v_a_3470_ = lean_ctor_get(v___x_3386_, 0);
v_isSharedCheck_3477_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3477_ == 0)
{
v___x_3472_ = v___x_3386_;
v_isShared_3473_ = v_isSharedCheck_3477_;
goto v_resetjp_3471_;
}
else
{
lean_inc(v_a_3470_);
lean_dec(v___x_3386_);
v___x_3472_ = lean_box(0);
v_isShared_3473_ = v_isSharedCheck_3477_;
goto v_resetjp_3471_;
}
v_resetjp_3471_:
{
lean_object* v___x_3475_; 
if (v_isShared_3473_ == 0)
{
v___x_3475_ = v___x_3472_;
goto v_reusejp_3474_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v_a_3470_);
v___x_3475_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3474_;
}
v_reusejp_3474_:
{
return v___x_3475_;
}
}
}
}
}
}
}
}
v___jp_3367_:
{
lean_object* v___x_3368_; lean_object* v___x_3370_; 
v___x_3368_ = lean_box(0);
if (v_isShared_3366_ == 0)
{
lean_ctor_set(v___x_3365_, 0, v___x_3368_);
v___x_3370_ = v___x_3365_;
goto v_reusejp_3369_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v___x_3368_);
v___x_3370_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3369_;
}
v_reusejp_3369_:
{
return v___x_3370_;
}
}
}
}
else
{
lean_object* v_a_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3486_; 
lean_dec_ref(v_e_3350_);
v_a_3479_ = lean_ctor_get(v___x_3362_, 0);
v_isSharedCheck_3486_ = !lean_is_exclusive(v___x_3362_);
if (v_isSharedCheck_3486_ == 0)
{
v___x_3481_ = v___x_3362_;
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_a_3479_);
lean_dec(v___x_3362_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3486_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v___x_3484_; 
if (v_isShared_3482_ == 0)
{
v___x_3484_ = v___x_3481_;
goto v_reusejp_3483_;
}
else
{
lean_object* v_reuseFailAlloc_3485_; 
v_reuseFailAlloc_3485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3485_, 0, v_a_3479_);
v___x_3484_ = v_reuseFailAlloc_3485_;
goto v_reusejp_3483_;
}
v_reusejp_3483_:
{
return v___x_3484_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___boxed(lean_object* v_e_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_, lean_object* v_a_3496_, lean_object* v_a_3497_, lean_object* v_a_3498_){
_start:
{
lean_object* v_res_3499_; 
v_res_3499_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f(v_e_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_, v_a_3496_, v_a_3497_);
lean_dec(v_a_3497_);
lean_dec_ref(v_a_3496_);
lean_dec(v_a_3495_);
lean_dec_ref(v_a_3494_);
lean_dec(v_a_3493_);
lean_dec_ref(v_a_3492_);
lean_dec(v_a_3491_);
lean_dec_ref(v_a_3490_);
lean_dec(v_a_3489_);
lean_dec(v_a_3488_);
return v_res_3499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(lean_object* v_c_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_, lean_object* v_a_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_){
_start:
{
lean_object* v_p_3512_; lean_object* v___x_3513_; 
v_p_3512_ = lean_ctor_get(v_c_3500_, 0);
lean_inc_ref(v_p_3512_);
v___x_3513_ = l_Int_Linear_Poly_normCommRing_x3f(v_p_3512_, v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_, v_a_3508_, v_a_3509_, v_a_3510_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v_a_3514_; 
v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
lean_inc(v_a_3514_);
lean_dec_ref(v___x_3513_);
if (lean_obj_tag(v_a_3514_) == 1)
{
lean_object* v_val_3515_; lean_object* v_snd_3516_; lean_object* v_fst_3517_; lean_object* v_fst_3518_; lean_object* v_snd_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3528_; 
v_val_3515_ = lean_ctor_get(v_a_3514_, 0);
lean_inc(v_val_3515_);
lean_dec_ref(v_a_3514_);
v_snd_3516_ = lean_ctor_get(v_val_3515_, 1);
lean_inc(v_snd_3516_);
v_fst_3517_ = lean_ctor_get(v_val_3515_, 0);
lean_inc(v_fst_3517_);
lean_dec(v_val_3515_);
v_fst_3518_ = lean_ctor_get(v_snd_3516_, 0);
v_snd_3519_ = lean_ctor_get(v_snd_3516_, 1);
v_isSharedCheck_3528_ = !lean_is_exclusive(v_snd_3516_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3521_ = v_snd_3516_;
v_isShared_3522_ = v_isSharedCheck_3528_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_snd_3519_);
lean_inc(v_fst_3518_);
lean_dec(v_snd_3516_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3528_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
lean_object* v___x_3523_; lean_object* v___x_3525_; 
v___x_3523_ = lean_alloc_ctor(17, 3, 0);
lean_ctor_set(v___x_3523_, 0, v_c_3500_);
lean_ctor_set(v___x_3523_, 1, v_fst_3517_);
lean_ctor_set(v___x_3523_, 2, v_fst_3518_);
if (v_isShared_3522_ == 0)
{
lean_ctor_set(v___x_3521_, 1, v___x_3523_);
lean_ctor_set(v___x_3521_, 0, v_snd_3519_);
v___x_3525_ = v___x_3521_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v_snd_3519_);
lean_ctor_set(v_reuseFailAlloc_3527_, 1, v___x_3523_);
v___x_3525_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
lean_object* v___x_3526_; 
lean_inc(v_a_3510_);
lean_inc_ref(v_a_3509_);
lean_inc(v_a_3508_);
lean_inc_ref(v_a_3507_);
lean_inc(v_a_3506_);
lean_inc_ref(v_a_3505_);
lean_inc(v_a_3504_);
lean_inc_ref(v_a_3503_);
lean_inc(v_a_3502_);
lean_inc(v_a_3501_);
v___x_3526_ = lean_grind_cutsat_assert_le(v___x_3525_, v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_, v_a_3508_, v_a_3509_, v_a_3510_);
return v___x_3526_;
}
}
}
else
{
lean_object* v___x_3529_; 
lean_dec(v_a_3514_);
lean_inc(v_a_3510_);
lean_inc_ref(v_a_3509_);
lean_inc(v_a_3508_);
lean_inc_ref(v_a_3507_);
lean_inc(v_a_3506_);
lean_inc_ref(v_a_3505_);
lean_inc(v_a_3504_);
lean_inc_ref(v_a_3503_);
lean_inc(v_a_3502_);
lean_inc(v_a_3501_);
v___x_3529_ = lean_grind_cutsat_assert_le(v_c_3500_, v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_, v_a_3506_, v_a_3507_, v_a_3508_, v_a_3509_, v_a_3510_);
return v___x_3529_;
}
}
else
{
lean_object* v_a_3530_; lean_object* v___x_3532_; uint8_t v_isShared_3533_; uint8_t v_isSharedCheck_3537_; 
lean_dec_ref(v_c_3500_);
v_a_3530_ = lean_ctor_get(v___x_3513_, 0);
v_isSharedCheck_3537_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3537_ == 0)
{
v___x_3532_ = v___x_3513_;
v_isShared_3533_ = v_isSharedCheck_3537_;
goto v_resetjp_3531_;
}
else
{
lean_inc(v_a_3530_);
lean_dec(v___x_3513_);
v___x_3532_ = lean_box(0);
v_isShared_3533_ = v_isSharedCheck_3537_;
goto v_resetjp_3531_;
}
v_resetjp_3531_:
{
lean_object* v___x_3535_; 
if (v_isShared_3533_ == 0)
{
v___x_3535_ = v___x_3532_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v_a_3530_);
v___x_3535_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
return v___x_3535_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore___boxed(lean_object* v_c_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_){
_start:
{
lean_object* v_res_3550_; 
v_res_3550_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v_c_3538_, v_a_3539_, v_a_3540_, v_a_3541_, v_a_3542_, v_a_3543_, v_a_3544_, v_a_3545_, v_a_3546_, v_a_3547_, v_a_3548_);
lean_dec(v_a_3548_);
lean_dec_ref(v_a_3547_);
lean_dec(v_a_3546_);
lean_dec_ref(v_a_3545_);
lean_dec(v_a_3544_);
lean_dec_ref(v_a_3543_);
lean_dec(v_a_3542_);
lean_dec_ref(v_a_3541_);
lean_dec(v_a_3540_);
lean_dec(v_a_3539_);
return v_res_3550_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0(void){
_start:
{
lean_object* v___x_3551_; lean_object* v___x_3552_; 
v___x_3551_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
v___x_3552_ = lean_int_neg(v___x_3551_);
return v___x_3552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe(lean_object* v_e_3553_, uint8_t v_eqTrue_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_){
_start:
{
lean_object* v___x_3566_; 
lean_inc_ref(v_e_3553_);
v___x_3566_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f(v_e_3553_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_, v_a_3562_, v_a_3563_, v_a_3564_);
if (lean_obj_tag(v___x_3566_) == 0)
{
lean_object* v_a_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3593_; 
v_a_3567_ = lean_ctor_get(v___x_3566_, 0);
v_isSharedCheck_3593_ = !lean_is_exclusive(v___x_3566_);
if (v_isSharedCheck_3593_ == 0)
{
v___x_3569_ = v___x_3566_;
v_isShared_3570_ = v_isSharedCheck_3593_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_a_3567_);
lean_dec(v___x_3566_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3593_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
if (lean_obj_tag(v_a_3567_) == 1)
{
lean_del_object(v___x_3569_);
if (v_eqTrue_3554_ == 0)
{
lean_object* v_val_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; 
v_val_3571_ = lean_ctor_get(v_a_3567_, 0);
lean_inc_n(v_val_3571_, 2);
lean_dec_ref(v_a_3567_);
v___x_3572_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
v___x_3573_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0);
v___x_3574_ = l_Int_Linear_Poly_mul(v_val_3571_, v___x_3573_);
v___x_3575_ = l_Int_Linear_Poly_addConst(v___x_3574_, v___x_3572_);
v___x_3576_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3576_, 0, v_e_3553_);
lean_ctor_set(v___x_3576_, 1, v_val_3571_);
v___x_3577_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3577_, 0, v___x_3575_);
lean_ctor_set(v___x_3577_, 1, v___x_3576_);
v___x_3578_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v___x_3577_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_, v_a_3562_, v_a_3563_, v_a_3564_);
return v___x_3578_;
}
else
{
lean_object* v_val_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3588_; 
v_val_3579_ = lean_ctor_get(v_a_3567_, 0);
v_isSharedCheck_3588_ = !lean_is_exclusive(v_a_3567_);
if (v_isSharedCheck_3588_ == 0)
{
v___x_3581_ = v_a_3567_;
v_isShared_3582_ = v_isSharedCheck_3588_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_val_3579_);
lean_dec(v_a_3567_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3588_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v___x_3584_; 
if (v_isShared_3582_ == 0)
{
lean_ctor_set_tag(v___x_3581_, 0);
lean_ctor_set(v___x_3581_, 0, v_e_3553_);
v___x_3584_ = v___x_3581_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3587_; 
v_reuseFailAlloc_3587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3587_, 0, v_e_3553_);
v___x_3584_ = v_reuseFailAlloc_3587_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
lean_object* v___x_3585_; lean_object* v___x_3586_; 
v___x_3585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3585_, 0, v_val_3579_);
lean_ctor_set(v___x_3585_, 1, v___x_3584_);
v___x_3586_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v___x_3585_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_, v_a_3561_, v_a_3562_, v_a_3563_, v_a_3564_);
return v___x_3586_;
}
}
}
}
else
{
lean_object* v___x_3589_; lean_object* v___x_3591_; 
lean_dec(v_a_3567_);
lean_dec_ref(v_e_3553_);
v___x_3589_ = lean_box(0);
if (v_isShared_3570_ == 0)
{
lean_ctor_set(v___x_3569_, 0, v___x_3589_);
v___x_3591_ = v___x_3569_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v___x_3589_);
v___x_3591_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
return v___x_3591_;
}
}
}
}
else
{
lean_object* v_a_3594_; lean_object* v___x_3596_; uint8_t v_isShared_3597_; uint8_t v_isSharedCheck_3601_; 
lean_dec_ref(v_e_3553_);
v_a_3594_ = lean_ctor_get(v___x_3566_, 0);
v_isSharedCheck_3601_ = !lean_is_exclusive(v___x_3566_);
if (v_isSharedCheck_3601_ == 0)
{
v___x_3596_ = v___x_3566_;
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
else
{
lean_inc(v_a_3594_);
lean_dec(v___x_3566_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___boxed(lean_object* v_e_3602_, lean_object* v_eqTrue_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_, lean_object* v_a_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_, lean_object* v_a_3614_){
_start:
{
uint8_t v_eqTrue_boxed_3615_; lean_object* v_res_3616_; 
v_eqTrue_boxed_3615_ = lean_unbox(v_eqTrue_3603_);
v_res_3616_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe(v_e_3602_, v_eqTrue_boxed_3615_, v_a_3604_, v_a_3605_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_, v_a_3612_, v_a_3613_);
lean_dec(v_a_3613_);
lean_dec_ref(v_a_3612_);
lean_dec(v_a_3611_);
lean_dec_ref(v_a_3610_);
lean_dec(v_a_3609_);
lean_dec_ref(v_a_3608_);
lean_dec(v_a_3607_);
lean_dec_ref(v_a_3606_);
lean_dec(v_a_3605_);
lean_dec(v_a_3604_);
return v_res_3616_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0(void){
_start:
{
lean_object* v___x_3617_; lean_object* v___x_3618_; 
v___x_3617_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
v___x_3618_ = l_Lean_mkIntLit(v___x_3617_);
return v___x_3618_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5(void){
_start:
{
lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; 
v___x_3626_ = lean_box(0);
v___x_3627_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__4));
v___x_3628_ = l_Lean_mkConst(v___x_3627_, v___x_3626_);
return v___x_3628_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8(void){
_start:
{
lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; 
v___x_3634_ = lean_box(0);
v___x_3635_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__7));
v___x_3636_ = l_Lean_mkConst(v___x_3635_, v___x_3634_);
return v___x_3636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe(lean_object* v_e_3637_, uint8_t v_eqTrue_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_, lean_object* v_a_3648_){
_start:
{
lean_object* v___y_3651_; lean_object* v___y_3652_; lean_object* v_fst_3653_; lean_object* v_snd_3654_; lean_object* v___x_3683_; uint8_t v___x_3684_; 
lean_inc_ref(v_e_3637_);
v___x_3683_ = l_Lean_Expr_cleanupAnnotations(v_e_3637_);
v___x_3684_ = l_Lean_Expr_isApp(v___x_3683_);
if (v___x_3684_ == 0)
{
lean_dec_ref(v___x_3683_);
lean_dec_ref(v_e_3637_);
goto v___jp_3680_;
}
else
{
lean_object* v_arg_3685_; lean_object* v___x_3686_; uint8_t v___x_3687_; 
v_arg_3685_ = lean_ctor_get(v___x_3683_, 1);
lean_inc_ref(v_arg_3685_);
v___x_3686_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3683_);
v___x_3687_ = l_Lean_Expr_isApp(v___x_3686_);
if (v___x_3687_ == 0)
{
lean_dec_ref(v___x_3686_);
lean_dec_ref(v_arg_3685_);
lean_dec_ref(v_e_3637_);
goto v___jp_3680_;
}
else
{
lean_object* v_arg_3688_; lean_object* v___y_3690_; lean_object* v___x_3728_; uint8_t v___x_3729_; 
v_arg_3688_ = lean_ctor_get(v___x_3686_, 1);
lean_inc_ref(v_arg_3688_);
v___x_3728_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3686_);
v___x_3729_ = l_Lean_Expr_isApp(v___x_3728_);
if (v___x_3729_ == 0)
{
lean_dec_ref(v___x_3728_);
lean_dec_ref(v_arg_3688_);
lean_dec_ref(v_arg_3685_);
lean_dec_ref(v_e_3637_);
goto v___jp_3680_;
}
else
{
lean_object* v___x_3730_; uint8_t v___x_3731_; 
v___x_3730_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3728_);
v___x_3731_ = l_Lean_Expr_isApp(v___x_3730_);
if (v___x_3731_ == 0)
{
lean_dec_ref(v___x_3730_);
lean_dec_ref(v_arg_3688_);
lean_dec_ref(v_arg_3685_);
lean_dec_ref(v_e_3637_);
goto v___jp_3680_;
}
else
{
lean_object* v___x_3732_; lean_object* v___x_3733_; uint8_t v___x_3734_; 
v___x_3732_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3730_);
v___x_3733_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2));
v___x_3734_ = l_Lean_Expr_isConstOf(v___x_3732_, v___x_3733_);
lean_dec_ref(v___x_3732_);
if (v___x_3734_ == 0)
{
lean_dec_ref(v_arg_3688_);
lean_dec_ref(v_arg_3685_);
lean_dec_ref(v_e_3637_);
goto v___jp_3680_;
}
else
{
if (v_eqTrue_3638_ == 0)
{
lean_object* v___x_3735_; 
v___x_3735_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5);
v___y_3690_ = v___x_3735_;
goto v___jp_3689_;
}
else
{
lean_object* v___x_3736_; 
v___x_3736_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8);
v___y_3690_ = v___x_3736_;
goto v___jp_3689_;
}
}
}
}
v___jp_3689_:
{
lean_object* v___x_3691_; 
v___x_3691_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_3637_, v_a_3639_);
if (lean_obj_tag(v___x_3691_) == 0)
{
lean_object* v_a_3692_; lean_object* v___x_3693_; 
v_a_3692_ = lean_ctor_get(v___x_3691_, 0);
lean_inc(v_a_3692_);
lean_dec_ref(v___x_3691_);
lean_inc_ref(v_arg_3688_);
v___x_3693_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_3688_, v_a_3639_, v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_, v_a_3645_, v_a_3646_, v_a_3647_, v_a_3648_);
if (lean_obj_tag(v___x_3693_) == 0)
{
lean_object* v_a_3694_; lean_object* v_fst_3695_; lean_object* v_snd_3696_; lean_object* v___x_3697_; 
v_a_3694_ = lean_ctor_get(v___x_3693_, 0);
lean_inc(v_a_3694_);
lean_dec_ref(v___x_3693_);
v_fst_3695_ = lean_ctor_get(v_a_3694_, 0);
lean_inc(v_fst_3695_);
v_snd_3696_ = lean_ctor_get(v_a_3694_, 1);
lean_inc(v_snd_3696_);
lean_dec(v_a_3694_);
lean_inc_ref(v_arg_3685_);
v___x_3697_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_3685_, v_a_3639_, v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_, v_a_3645_, v_a_3646_, v_a_3647_, v_a_3648_);
if (lean_obj_tag(v___x_3697_) == 0)
{
lean_object* v_a_3698_; lean_object* v_fst_3699_; lean_object* v_snd_3700_; lean_object* v___x_3701_; 
v_a_3698_ = lean_ctor_get(v___x_3697_, 0);
lean_inc(v_a_3698_);
lean_dec_ref(v___x_3697_);
v_fst_3699_ = lean_ctor_get(v_a_3698_, 0);
lean_inc_n(v_fst_3699_, 2);
v_snd_3700_ = lean_ctor_get(v_a_3698_, 1);
lean_inc(v_snd_3700_);
lean_dec(v_a_3698_);
lean_inc(v_fst_3695_);
lean_inc_ref(v___y_3690_);
v___x_3701_ = l_Lean_mkApp6(v___y_3690_, v_arg_3688_, v_arg_3685_, v_fst_3695_, v_fst_3699_, v_snd_3696_, v_snd_3700_);
if (v_eqTrue_3638_ == 0)
{
lean_object* v___x_3702_; lean_object* v___x_3703_; 
v___x_3702_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0);
v___x_3703_ = l_Lean_mkIntAdd(v_fst_3699_, v___x_3702_);
v___y_3651_ = v_a_3692_;
v___y_3652_ = v___x_3701_;
v_fst_3653_ = v___x_3703_;
v_snd_3654_ = v_fst_3695_;
goto v___jp_3650_;
}
else
{
v___y_3651_ = v_a_3692_;
v___y_3652_ = v___x_3701_;
v_fst_3653_ = v_fst_3695_;
v_snd_3654_ = v_fst_3699_;
goto v___jp_3650_;
}
}
else
{
lean_object* v_a_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3711_; 
lean_dec(v_snd_3696_);
lean_dec(v_fst_3695_);
lean_dec(v_a_3692_);
lean_dec_ref(v_arg_3688_);
lean_dec_ref(v_arg_3685_);
lean_dec_ref(v_e_3637_);
v_a_3704_ = lean_ctor_get(v___x_3697_, 0);
v_isSharedCheck_3711_ = !lean_is_exclusive(v___x_3697_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3706_ = v___x_3697_;
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_a_3704_);
lean_dec(v___x_3697_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
lean_object* v___x_3709_; 
if (v_isShared_3707_ == 0)
{
v___x_3709_ = v___x_3706_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v_a_3704_);
v___x_3709_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
return v___x_3709_;
}
}
}
}
else
{
lean_object* v_a_3712_; lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3719_; 
lean_dec(v_a_3692_);
lean_dec_ref(v_arg_3688_);
lean_dec_ref(v_arg_3685_);
lean_dec_ref(v_e_3637_);
v_a_3712_ = lean_ctor_get(v___x_3693_, 0);
v_isSharedCheck_3719_ = !lean_is_exclusive(v___x_3693_);
if (v_isSharedCheck_3719_ == 0)
{
v___x_3714_ = v___x_3693_;
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
else
{
lean_inc(v_a_3712_);
lean_dec(v___x_3693_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
lean_object* v___x_3717_; 
if (v_isShared_3715_ == 0)
{
v___x_3717_ = v___x_3714_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v_a_3712_);
v___x_3717_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
return v___x_3717_;
}
}
}
}
else
{
lean_object* v_a_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3727_; 
lean_dec_ref(v_arg_3688_);
lean_dec_ref(v_arg_3685_);
lean_dec_ref(v_e_3637_);
v_a_3720_ = lean_ctor_get(v___x_3691_, 0);
v_isSharedCheck_3727_ = !lean_is_exclusive(v___x_3691_);
if (v_isSharedCheck_3727_ == 0)
{
v___x_3722_ = v___x_3691_;
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_a_3720_);
lean_dec(v___x_3691_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3727_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v___x_3725_; 
if (v_isShared_3723_ == 0)
{
v___x_3725_ = v___x_3722_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v_a_3720_);
v___x_3725_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
return v___x_3725_;
}
}
}
}
}
}
v___jp_3650_:
{
lean_object* v___x_3655_; 
lean_inc(v___y_3651_);
v___x_3655_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_3653_, v___y_3651_, v_a_3639_, v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_, v_a_3645_, v_a_3646_, v_a_3647_, v_a_3648_);
if (lean_obj_tag(v___x_3655_) == 0)
{
lean_object* v_a_3656_; lean_object* v___x_3657_; 
v_a_3656_ = lean_ctor_get(v___x_3655_, 0);
lean_inc(v_a_3656_);
lean_dec_ref(v___x_3655_);
v___x_3657_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_snd_3654_, v___y_3651_, v_a_3639_, v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_, v_a_3645_, v_a_3646_, v_a_3647_, v_a_3648_);
if (lean_obj_tag(v___x_3657_) == 0)
{
lean_object* v_a_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; 
v_a_3658_ = lean_ctor_get(v___x_3657_, 0);
lean_inc_n(v_a_3658_, 2);
lean_dec_ref(v___x_3657_);
lean_inc(v_a_3656_);
v___x_3659_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3659_, 0, v_a_3656_);
lean_ctor_set(v___x_3659_, 1, v_a_3658_);
v___x_3660_ = l_Int_Linear_Expr_norm(v___x_3659_);
lean_dec_ref(v___x_3659_);
v___x_3661_ = lean_alloc_ctor(2, 4, 1);
lean_ctor_set(v___x_3661_, 0, v_e_3637_);
lean_ctor_set(v___x_3661_, 1, v___y_3652_);
lean_ctor_set(v___x_3661_, 2, v_a_3656_);
lean_ctor_set(v___x_3661_, 3, v_a_3658_);
lean_ctor_set_uint8(v___x_3661_, sizeof(void*)*4, v_eqTrue_3638_);
v___x_3662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3662_, 0, v___x_3660_);
lean_ctor_set(v___x_3662_, 1, v___x_3661_);
v___x_3663_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v___x_3662_, v_a_3639_, v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_, v_a_3645_, v_a_3646_, v_a_3647_, v_a_3648_);
return v___x_3663_;
}
else
{
lean_object* v_a_3664_; lean_object* v___x_3666_; uint8_t v_isShared_3667_; uint8_t v_isSharedCheck_3671_; 
lean_dec(v_a_3656_);
lean_dec_ref(v___y_3652_);
lean_dec_ref(v_e_3637_);
v_a_3664_ = lean_ctor_get(v___x_3657_, 0);
v_isSharedCheck_3671_ = !lean_is_exclusive(v___x_3657_);
if (v_isSharedCheck_3671_ == 0)
{
v___x_3666_ = v___x_3657_;
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
else
{
lean_inc(v_a_3664_);
lean_dec(v___x_3657_);
v___x_3666_ = lean_box(0);
v_isShared_3667_ = v_isSharedCheck_3671_;
goto v_resetjp_3665_;
}
v_resetjp_3665_:
{
lean_object* v___x_3669_; 
if (v_isShared_3667_ == 0)
{
v___x_3669_ = v___x_3666_;
goto v_reusejp_3668_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v_a_3664_);
v___x_3669_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3668_;
}
v_reusejp_3668_:
{
return v___x_3669_;
}
}
}
}
else
{
lean_object* v_a_3672_; lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3679_; 
lean_dec_ref(v_snd_3654_);
lean_dec_ref(v___y_3652_);
lean_dec(v___y_3651_);
lean_dec_ref(v_e_3637_);
v_a_3672_ = lean_ctor_get(v___x_3655_, 0);
v_isSharedCheck_3679_ = !lean_is_exclusive(v___x_3655_);
if (v_isSharedCheck_3679_ == 0)
{
v___x_3674_ = v___x_3655_;
v_isShared_3675_ = v_isSharedCheck_3679_;
goto v_resetjp_3673_;
}
else
{
lean_inc(v_a_3672_);
lean_dec(v___x_3655_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3679_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
lean_object* v___x_3677_; 
if (v_isShared_3675_ == 0)
{
v___x_3677_ = v___x_3674_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v_a_3672_);
v___x_3677_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
return v___x_3677_;
}
}
}
}
v___jp_3680_:
{
lean_object* v___x_3681_; lean_object* v___x_3682_; 
v___x_3681_ = lean_box(0);
v___x_3682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3682_, 0, v___x_3681_);
return v___x_3682_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___boxed(lean_object* v_e_3737_, lean_object* v_eqTrue_3738_, lean_object* v_a_3739_, lean_object* v_a_3740_, lean_object* v_a_3741_, lean_object* v_a_3742_, lean_object* v_a_3743_, lean_object* v_a_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_){
_start:
{
uint8_t v_eqTrue_boxed_3750_; lean_object* v_res_3751_; 
v_eqTrue_boxed_3750_ = lean_unbox(v_eqTrue_3738_);
v_res_3751_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe(v_e_3737_, v_eqTrue_boxed_3750_, v_a_3739_, v_a_3740_, v_a_3741_, v_a_3742_, v_a_3743_, v_a_3744_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_);
lean_dec(v_a_3748_);
lean_dec_ref(v_a_3747_);
lean_dec(v_a_3746_);
lean_dec_ref(v_a_3745_);
lean_dec(v_a_3744_);
lean_dec_ref(v_a_3743_);
lean_dec(v_a_3742_);
lean_dec_ref(v_a_3741_);
lean_dec(v_a_3740_);
lean_dec(v_a_3739_);
return v_res_3751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe(lean_object* v_e_3752_, uint8_t v_eqTrue_3753_, lean_object* v_a_3754_, lean_object* v_a_3755_, lean_object* v_a_3756_, lean_object* v_a_3757_, lean_object* v_a_3758_, lean_object* v_a_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_){
_start:
{
lean_object* v___y_3770_; lean_object* v___y_3771_; lean_object* v___y_3772_; lean_object* v___y_3773_; lean_object* v___y_3774_; lean_object* v___y_3775_; lean_object* v___y_3776_; lean_object* v___y_3777_; lean_object* v___y_3778_; lean_object* v___y_3779_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v_fst_3782_; lean_object* v_snd_3783_; lean_object* v_____x_3810_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3814_; lean_object* v___y_3815_; lean_object* v___y_3816_; lean_object* v___y_3817_; lean_object* v___y_3818_; lean_object* v___y_3819_; lean_object* v___y_3820_; lean_object* v___y_3821_; 
if (v_eqTrue_3753_ == 0)
{
lean_object* v___x_3875_; 
v___x_3875_ = l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLE_x3f___redArg(v_a_3754_, v_a_3755_, v_a_3761_, v_a_3762_, v_a_3763_, v_a_3764_);
if (lean_obj_tag(v___x_3875_) == 0)
{
lean_object* v_a_3876_; 
v_a_3876_ = lean_ctor_get(v___x_3875_, 0);
lean_inc(v_a_3876_);
lean_dec_ref(v___x_3875_);
v_____x_3810_ = v_a_3876_;
v___y_3811_ = v_a_3754_;
v___y_3812_ = v_a_3755_;
v___y_3813_ = v_a_3756_;
v___y_3814_ = v_a_3757_;
v___y_3815_ = v_a_3758_;
v___y_3816_ = v_a_3759_;
v___y_3817_ = v_a_3760_;
v___y_3818_ = v_a_3761_;
v___y_3819_ = v_a_3762_;
v___y_3820_ = v_a_3763_;
v___y_3821_ = v_a_3764_;
goto v___jp_3809_;
}
else
{
lean_object* v_a_3877_; lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3884_; 
lean_dec_ref(v_e_3752_);
v_a_3877_ = lean_ctor_get(v___x_3875_, 0);
v_isSharedCheck_3884_ = !lean_is_exclusive(v___x_3875_);
if (v_isSharedCheck_3884_ == 0)
{
v___x_3879_ = v___x_3875_;
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
else
{
lean_inc(v_a_3877_);
lean_dec(v___x_3875_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_3884_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
lean_object* v___x_3882_; 
if (v_isShared_3880_ == 0)
{
v___x_3882_ = v___x_3879_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v_a_3877_);
v___x_3882_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
return v___x_3882_;
}
}
}
}
else
{
lean_object* v___x_3885_; 
v___x_3885_ = l_Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f___redArg(v_a_3754_, v_a_3755_, v_a_3761_, v_a_3762_, v_a_3763_, v_a_3764_);
if (lean_obj_tag(v___x_3885_) == 0)
{
lean_object* v_a_3886_; 
v_a_3886_ = lean_ctor_get(v___x_3885_, 0);
lean_inc(v_a_3886_);
lean_dec_ref(v___x_3885_);
v_____x_3810_ = v_a_3886_;
v___y_3811_ = v_a_3754_;
v___y_3812_ = v_a_3755_;
v___y_3813_ = v_a_3756_;
v___y_3814_ = v_a_3757_;
v___y_3815_ = v_a_3758_;
v___y_3816_ = v_a_3759_;
v___y_3817_ = v_a_3760_;
v___y_3818_ = v_a_3761_;
v___y_3819_ = v_a_3762_;
v___y_3820_ = v_a_3763_;
v___y_3821_ = v_a_3764_;
goto v___jp_3809_;
}
else
{
lean_object* v_a_3887_; lean_object* v___x_3889_; uint8_t v_isShared_3890_; uint8_t v_isSharedCheck_3894_; 
lean_dec_ref(v_e_3752_);
v_a_3887_ = lean_ctor_get(v___x_3885_, 0);
v_isSharedCheck_3894_ = !lean_is_exclusive(v___x_3885_);
if (v_isSharedCheck_3894_ == 0)
{
v___x_3889_ = v___x_3885_;
v_isShared_3890_ = v_isSharedCheck_3894_;
goto v_resetjp_3888_;
}
else
{
lean_inc(v_a_3887_);
lean_dec(v___x_3885_);
v___x_3889_ = lean_box(0);
v_isShared_3890_ = v_isSharedCheck_3894_;
goto v_resetjp_3888_;
}
v_resetjp_3888_:
{
lean_object* v___x_3892_; 
if (v_isShared_3890_ == 0)
{
v___x_3892_ = v___x_3889_;
goto v_reusejp_3891_;
}
else
{
lean_object* v_reuseFailAlloc_3893_; 
v_reuseFailAlloc_3893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3893_, 0, v_a_3887_);
v___x_3892_ = v_reuseFailAlloc_3893_;
goto v_reusejp_3891_;
}
v_reusejp_3891_:
{
return v___x_3892_;
}
}
}
}
v___jp_3766_:
{
lean_object* v___x_3767_; lean_object* v___x_3768_; 
v___x_3767_ = lean_box(0);
v___x_3768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3768_, 0, v___x_3767_);
return v___x_3768_;
}
v___jp_3769_:
{
lean_object* v___x_3784_; 
lean_inc(v___y_3770_);
v___x_3784_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_3782_, v___y_3770_, v___y_3777_, v___y_3775_, v___y_3772_, v___y_3774_, v___y_3773_, v___y_3778_, v___y_3776_, v___y_3779_, v___y_3771_, v___y_3781_);
if (lean_obj_tag(v___x_3784_) == 0)
{
lean_object* v_a_3785_; lean_object* v___x_3786_; 
v_a_3785_ = lean_ctor_get(v___x_3784_, 0);
lean_inc(v_a_3785_);
lean_dec_ref(v___x_3784_);
v___x_3786_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_snd_3783_, v___y_3770_, v___y_3777_, v___y_3775_, v___y_3772_, v___y_3774_, v___y_3773_, v___y_3778_, v___y_3776_, v___y_3779_, v___y_3771_, v___y_3781_);
if (lean_obj_tag(v___x_3786_) == 0)
{
lean_object* v_a_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; 
v_a_3787_ = lean_ctor_get(v___x_3786_, 0);
lean_inc_n(v_a_3787_, 2);
lean_dec_ref(v___x_3786_);
lean_inc(v_a_3785_);
v___x_3788_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3788_, 0, v_a_3785_);
lean_ctor_set(v___x_3788_, 1, v_a_3787_);
v___x_3789_ = l_Int_Linear_Expr_norm(v___x_3788_);
lean_dec_ref(v___x_3788_);
v___x_3790_ = lean_alloc_ctor(2, 4, 1);
lean_ctor_set(v___x_3790_, 0, v_e_3752_);
lean_ctor_set(v___x_3790_, 1, v___y_3780_);
lean_ctor_set(v___x_3790_, 2, v_a_3785_);
lean_ctor_set(v___x_3790_, 3, v_a_3787_);
lean_ctor_set_uint8(v___x_3790_, sizeof(void*)*4, v_eqTrue_3753_);
v___x_3791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3791_, 0, v___x_3789_);
lean_ctor_set(v___x_3791_, 1, v___x_3790_);
v___x_3792_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v___x_3791_, v___y_3777_, v___y_3775_, v___y_3772_, v___y_3774_, v___y_3773_, v___y_3778_, v___y_3776_, v___y_3779_, v___y_3771_, v___y_3781_);
return v___x_3792_;
}
else
{
lean_object* v_a_3793_; lean_object* v___x_3795_; uint8_t v_isShared_3796_; uint8_t v_isSharedCheck_3800_; 
lean_dec(v_a_3785_);
lean_dec_ref(v___y_3780_);
lean_dec_ref(v_e_3752_);
v_a_3793_ = lean_ctor_get(v___x_3786_, 0);
v_isSharedCheck_3800_ = !lean_is_exclusive(v___x_3786_);
if (v_isSharedCheck_3800_ == 0)
{
v___x_3795_ = v___x_3786_;
v_isShared_3796_ = v_isSharedCheck_3800_;
goto v_resetjp_3794_;
}
else
{
lean_inc(v_a_3793_);
lean_dec(v___x_3786_);
v___x_3795_ = lean_box(0);
v_isShared_3796_ = v_isSharedCheck_3800_;
goto v_resetjp_3794_;
}
v_resetjp_3794_:
{
lean_object* v___x_3798_; 
if (v_isShared_3796_ == 0)
{
v___x_3798_ = v___x_3795_;
goto v_reusejp_3797_;
}
else
{
lean_object* v_reuseFailAlloc_3799_; 
v_reuseFailAlloc_3799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3799_, 0, v_a_3793_);
v___x_3798_ = v_reuseFailAlloc_3799_;
goto v_reusejp_3797_;
}
v_reusejp_3797_:
{
return v___x_3798_;
}
}
}
}
else
{
lean_object* v_a_3801_; lean_object* v___x_3803_; uint8_t v_isShared_3804_; uint8_t v_isSharedCheck_3808_; 
lean_dec_ref(v_snd_3783_);
lean_dec_ref(v___y_3780_);
lean_dec(v___y_3770_);
lean_dec_ref(v_e_3752_);
v_a_3801_ = lean_ctor_get(v___x_3784_, 0);
v_isSharedCheck_3808_ = !lean_is_exclusive(v___x_3784_);
if (v_isSharedCheck_3808_ == 0)
{
v___x_3803_ = v___x_3784_;
v_isShared_3804_ = v_isSharedCheck_3808_;
goto v_resetjp_3802_;
}
else
{
lean_inc(v_a_3801_);
lean_dec(v___x_3784_);
v___x_3803_ = lean_box(0);
v_isShared_3804_ = v_isSharedCheck_3808_;
goto v_resetjp_3802_;
}
v_resetjp_3802_:
{
lean_object* v___x_3806_; 
if (v_isShared_3804_ == 0)
{
v___x_3806_ = v___x_3803_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v_a_3801_);
v___x_3806_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3805_;
}
v_reusejp_3805_:
{
return v___x_3806_;
}
}
}
}
v___jp_3809_:
{
if (lean_obj_tag(v_____x_3810_) == 1)
{
lean_object* v_val_3822_; lean_object* v___x_3823_; uint8_t v___x_3824_; 
v_val_3822_ = lean_ctor_get(v_____x_3810_, 0);
lean_inc(v_val_3822_);
lean_dec_ref(v_____x_3810_);
lean_inc_ref(v_e_3752_);
v___x_3823_ = l_Lean_Expr_cleanupAnnotations(v_e_3752_);
v___x_3824_ = l_Lean_Expr_isApp(v___x_3823_);
if (v___x_3824_ == 0)
{
lean_dec_ref(v___x_3823_);
lean_dec(v_val_3822_);
lean_dec_ref(v_e_3752_);
goto v___jp_3766_;
}
else
{
lean_object* v_arg_3825_; lean_object* v___x_3826_; uint8_t v___x_3827_; 
v_arg_3825_ = lean_ctor_get(v___x_3823_, 1);
lean_inc_ref(v_arg_3825_);
v___x_3826_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3823_);
v___x_3827_ = l_Lean_Expr_isApp(v___x_3826_);
if (v___x_3827_ == 0)
{
lean_dec_ref(v___x_3826_);
lean_dec_ref(v_arg_3825_);
lean_dec(v_val_3822_);
lean_dec_ref(v_e_3752_);
goto v___jp_3766_;
}
else
{
lean_object* v_arg_3828_; lean_object* v___x_3829_; uint8_t v___x_3830_; 
v_arg_3828_ = lean_ctor_get(v___x_3826_, 1);
lean_inc_ref(v_arg_3828_);
v___x_3829_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3826_);
v___x_3830_ = l_Lean_Expr_isApp(v___x_3829_);
if (v___x_3830_ == 0)
{
lean_dec_ref(v___x_3829_);
lean_dec_ref(v_arg_3828_);
lean_dec_ref(v_arg_3825_);
lean_dec(v_val_3822_);
lean_dec_ref(v_e_3752_);
goto v___jp_3766_;
}
else
{
lean_object* v___x_3831_; uint8_t v___x_3832_; 
v___x_3831_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3829_);
v___x_3832_ = l_Lean_Expr_isApp(v___x_3831_);
if (v___x_3832_ == 0)
{
lean_dec_ref(v___x_3831_);
lean_dec_ref(v_arg_3828_);
lean_dec_ref(v_arg_3825_);
lean_dec(v_val_3822_);
lean_dec_ref(v_e_3752_);
goto v___jp_3766_;
}
else
{
lean_object* v___x_3833_; lean_object* v___x_3834_; uint8_t v___x_3835_; 
v___x_3833_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3831_);
v___x_3834_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2));
v___x_3835_ = l_Lean_Expr_isConstOf(v___x_3833_, v___x_3834_);
lean_dec_ref(v___x_3833_);
if (v___x_3835_ == 0)
{
lean_dec_ref(v_arg_3828_);
lean_dec_ref(v_arg_3825_);
lean_dec(v_val_3822_);
lean_dec_ref(v_e_3752_);
goto v___jp_3766_;
}
else
{
lean_object* v___x_3836_; 
v___x_3836_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_3752_, v___y_3812_);
if (lean_obj_tag(v___x_3836_) == 0)
{
lean_object* v_a_3837_; lean_object* v___x_3838_; 
v_a_3837_ = lean_ctor_get(v___x_3836_, 0);
lean_inc(v_a_3837_);
lean_dec_ref(v___x_3836_);
lean_inc_ref(v_arg_3828_);
v___x_3838_ = l_Lean_Meta_Grind_Arith_Cutsat_toInt(v_arg_3828_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
if (lean_obj_tag(v___x_3838_) == 0)
{
lean_object* v_a_3839_; lean_object* v_fst_3840_; lean_object* v_snd_3841_; lean_object* v___x_3842_; 
v_a_3839_ = lean_ctor_get(v___x_3838_, 0);
lean_inc(v_a_3839_);
lean_dec_ref(v___x_3838_);
v_fst_3840_ = lean_ctor_get(v_a_3839_, 0);
lean_inc(v_fst_3840_);
v_snd_3841_ = lean_ctor_get(v_a_3839_, 1);
lean_inc(v_snd_3841_);
lean_dec(v_a_3839_);
lean_inc_ref(v_arg_3825_);
v___x_3842_ = l_Lean_Meta_Grind_Arith_Cutsat_toInt(v_arg_3825_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
if (lean_obj_tag(v___x_3842_) == 0)
{
lean_object* v_a_3843_; lean_object* v_fst_3844_; lean_object* v_snd_3845_; lean_object* v___x_3846_; 
v_a_3843_ = lean_ctor_get(v___x_3842_, 0);
lean_inc(v_a_3843_);
lean_dec_ref(v___x_3842_);
v_fst_3844_ = lean_ctor_get(v_a_3843_, 0);
lean_inc_n(v_fst_3844_, 2);
v_snd_3845_ = lean_ctor_get(v_a_3843_, 1);
lean_inc(v_snd_3845_);
lean_dec(v_a_3843_);
lean_inc(v_fst_3840_);
v___x_3846_ = l_Lean_mkApp6(v_val_3822_, v_arg_3828_, v_arg_3825_, v_fst_3840_, v_fst_3844_, v_snd_3841_, v_snd_3845_);
if (v_eqTrue_3753_ == 0)
{
lean_object* v___x_3847_; lean_object* v___x_3848_; 
v___x_3847_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0);
v___x_3848_ = l_Lean_mkIntAdd(v_fst_3844_, v___x_3847_);
v___y_3770_ = v_a_3837_;
v___y_3771_ = v___y_3820_;
v___y_3772_ = v___y_3814_;
v___y_3773_ = v___y_3816_;
v___y_3774_ = v___y_3815_;
v___y_3775_ = v___y_3813_;
v___y_3776_ = v___y_3818_;
v___y_3777_ = v___y_3812_;
v___y_3778_ = v___y_3817_;
v___y_3779_ = v___y_3819_;
v___y_3780_ = v___x_3846_;
v___y_3781_ = v___y_3821_;
v_fst_3782_ = v___x_3848_;
v_snd_3783_ = v_fst_3840_;
goto v___jp_3769_;
}
else
{
v___y_3770_ = v_a_3837_;
v___y_3771_ = v___y_3820_;
v___y_3772_ = v___y_3814_;
v___y_3773_ = v___y_3816_;
v___y_3774_ = v___y_3815_;
v___y_3775_ = v___y_3813_;
v___y_3776_ = v___y_3818_;
v___y_3777_ = v___y_3812_;
v___y_3778_ = v___y_3817_;
v___y_3779_ = v___y_3819_;
v___y_3780_ = v___x_3846_;
v___y_3781_ = v___y_3821_;
v_fst_3782_ = v_fst_3840_;
v_snd_3783_ = v_fst_3844_;
goto v___jp_3769_;
}
}
else
{
lean_object* v_a_3849_; lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3856_; 
lean_dec(v_snd_3841_);
lean_dec(v_fst_3840_);
lean_dec(v_a_3837_);
lean_dec_ref(v_arg_3828_);
lean_dec_ref(v_arg_3825_);
lean_dec(v_val_3822_);
lean_dec_ref(v_e_3752_);
v_a_3849_ = lean_ctor_get(v___x_3842_, 0);
v_isSharedCheck_3856_ = !lean_is_exclusive(v___x_3842_);
if (v_isSharedCheck_3856_ == 0)
{
v___x_3851_ = v___x_3842_;
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
else
{
lean_inc(v_a_3849_);
lean_dec(v___x_3842_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
lean_object* v___x_3854_; 
if (v_isShared_3852_ == 0)
{
v___x_3854_ = v___x_3851_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v_a_3849_);
v___x_3854_ = v_reuseFailAlloc_3855_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
return v___x_3854_;
}
}
}
}
else
{
lean_object* v_a_3857_; lean_object* v___x_3859_; uint8_t v_isShared_3860_; uint8_t v_isSharedCheck_3864_; 
lean_dec(v_a_3837_);
lean_dec_ref(v_arg_3828_);
lean_dec_ref(v_arg_3825_);
lean_dec(v_val_3822_);
lean_dec_ref(v_e_3752_);
v_a_3857_ = lean_ctor_get(v___x_3838_, 0);
v_isSharedCheck_3864_ = !lean_is_exclusive(v___x_3838_);
if (v_isSharedCheck_3864_ == 0)
{
v___x_3859_ = v___x_3838_;
v_isShared_3860_ = v_isSharedCheck_3864_;
goto v_resetjp_3858_;
}
else
{
lean_inc(v_a_3857_);
lean_dec(v___x_3838_);
v___x_3859_ = lean_box(0);
v_isShared_3860_ = v_isSharedCheck_3864_;
goto v_resetjp_3858_;
}
v_resetjp_3858_:
{
lean_object* v___x_3862_; 
if (v_isShared_3860_ == 0)
{
v___x_3862_ = v___x_3859_;
goto v_reusejp_3861_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v_a_3857_);
v___x_3862_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3861_;
}
v_reusejp_3861_:
{
return v___x_3862_;
}
}
}
}
else
{
lean_object* v_a_3865_; lean_object* v___x_3867_; uint8_t v_isShared_3868_; uint8_t v_isSharedCheck_3872_; 
lean_dec_ref(v_arg_3828_);
lean_dec_ref(v_arg_3825_);
lean_dec(v_val_3822_);
lean_dec_ref(v_e_3752_);
v_a_3865_ = lean_ctor_get(v___x_3836_, 0);
v_isSharedCheck_3872_ = !lean_is_exclusive(v___x_3836_);
if (v_isSharedCheck_3872_ == 0)
{
v___x_3867_ = v___x_3836_;
v_isShared_3868_ = v_isSharedCheck_3872_;
goto v_resetjp_3866_;
}
else
{
lean_inc(v_a_3865_);
lean_dec(v___x_3836_);
v___x_3867_ = lean_box(0);
v_isShared_3868_ = v_isSharedCheck_3872_;
goto v_resetjp_3866_;
}
v_resetjp_3866_:
{
lean_object* v___x_3870_; 
if (v_isShared_3868_ == 0)
{
v___x_3870_ = v___x_3867_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3871_; 
v_reuseFailAlloc_3871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3871_, 0, v_a_3865_);
v___x_3870_ = v_reuseFailAlloc_3871_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
return v___x_3870_;
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
lean_object* v___x_3873_; lean_object* v___x_3874_; 
lean_dec(v_____x_3810_);
lean_dec_ref(v_e_3752_);
v___x_3873_ = lean_box(0);
v___x_3874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3874_, 0, v___x_3873_);
return v___x_3874_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe___boxed(lean_object* v_e_3895_, lean_object* v_eqTrue_3896_, lean_object* v_a_3897_, lean_object* v_a_3898_, lean_object* v_a_3899_, lean_object* v_a_3900_, lean_object* v_a_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_, lean_object* v_a_3908_){
_start:
{
uint8_t v_eqTrue_boxed_3909_; lean_object* v_res_3910_; 
v_eqTrue_boxed_3909_ = lean_unbox(v_eqTrue_3896_);
v_res_3910_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe(v_e_3895_, v_eqTrue_boxed_3909_, v_a_3897_, v_a_3898_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_, v_a_3907_);
lean_dec(v_a_3907_);
lean_dec_ref(v_a_3906_);
lean_dec(v_a_3905_);
lean_dec_ref(v_a_3904_);
lean_dec(v_a_3903_);
lean_dec_ref(v_a_3902_);
lean_dec(v_a_3901_);
lean_dec_ref(v_a_3900_);
lean_dec(v_a_3899_);
lean_dec(v_a_3898_);
lean_dec(v_a_3897_);
return v_res_3910_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe(lean_object* v_e_3916_, uint8_t v_eqTrue_3917_, lean_object* v_a_3918_, lean_object* v_a_3919_, lean_object* v_a_3920_, lean_object* v_a_3921_, lean_object* v_a_3922_, lean_object* v_a_3923_, lean_object* v_a_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_, lean_object* v_a_3927_){
_start:
{
lean_object* v___x_3932_; 
v___x_3932_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3920_);
if (lean_obj_tag(v___x_3932_) == 0)
{
lean_object* v_a_3933_; lean_object* v___x_3935_; uint8_t v_isShared_3936_; uint8_t v_isSharedCheck_3963_; 
v_a_3933_ = lean_ctor_get(v___x_3932_, 0);
v_isSharedCheck_3963_ = !lean_is_exclusive(v___x_3932_);
if (v_isSharedCheck_3963_ == 0)
{
v___x_3935_ = v___x_3932_;
v_isShared_3936_ = v_isSharedCheck_3963_;
goto v_resetjp_3934_;
}
else
{
lean_inc(v_a_3933_);
lean_dec(v___x_3932_);
v___x_3935_ = lean_box(0);
v_isShared_3936_ = v_isSharedCheck_3963_;
goto v_resetjp_3934_;
}
v_resetjp_3934_:
{
uint8_t v_lia_3937_; 
v_lia_3937_ = lean_ctor_get_uint8(v_a_3933_, sizeof(void*)*12 + 23);
lean_dec(v_a_3933_);
if (v_lia_3937_ == 0)
{
lean_object* v___x_3938_; lean_object* v___x_3940_; 
lean_dec_ref(v_e_3916_);
v___x_3938_ = lean_box(0);
if (v_isShared_3936_ == 0)
{
lean_ctor_set(v___x_3935_, 0, v___x_3938_);
v___x_3940_ = v___x_3935_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v___x_3938_);
v___x_3940_ = v_reuseFailAlloc_3941_;
goto v_reusejp_3939_;
}
v_reusejp_3939_:
{
return v___x_3940_;
}
}
else
{
lean_object* v___x_3942_; uint8_t v___x_3943_; 
lean_del_object(v___x_3935_);
lean_inc_ref(v_e_3916_);
v___x_3942_ = l_Lean_Expr_cleanupAnnotations(v_e_3916_);
v___x_3943_ = l_Lean_Expr_isApp(v___x_3942_);
if (v___x_3943_ == 0)
{
lean_dec_ref(v___x_3942_);
lean_dec_ref(v_e_3916_);
goto v___jp_3929_;
}
else
{
lean_object* v___x_3944_; uint8_t v___x_3945_; 
v___x_3944_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3942_);
v___x_3945_ = l_Lean_Expr_isApp(v___x_3944_);
if (v___x_3945_ == 0)
{
lean_dec_ref(v___x_3944_);
lean_dec_ref(v_e_3916_);
goto v___jp_3929_;
}
else
{
lean_object* v___x_3946_; uint8_t v___x_3947_; 
v___x_3946_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3944_);
v___x_3947_ = l_Lean_Expr_isApp(v___x_3946_);
if (v___x_3947_ == 0)
{
lean_dec_ref(v___x_3946_);
lean_dec_ref(v_e_3916_);
goto v___jp_3929_;
}
else
{
lean_object* v___x_3948_; uint8_t v___x_3949_; 
v___x_3948_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3946_);
v___x_3949_ = l_Lean_Expr_isApp(v___x_3948_);
if (v___x_3949_ == 0)
{
lean_dec_ref(v___x_3948_);
lean_dec_ref(v_e_3916_);
goto v___jp_3929_;
}
else
{
lean_object* v_arg_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; uint8_t v___x_3953_; 
v_arg_3950_ = lean_ctor_get(v___x_3948_, 1);
lean_inc_ref(v_arg_3950_);
v___x_3951_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3948_);
v___x_3952_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2));
v___x_3953_ = l_Lean_Expr_isConstOf(v___x_3951_, v___x_3952_);
lean_dec_ref(v___x_3951_);
if (v___x_3953_ == 0)
{
lean_dec_ref(v_arg_3950_);
lean_dec_ref(v_e_3916_);
goto v___jp_3929_;
}
else
{
lean_object* v___x_3954_; uint8_t v___x_3955_; 
v___x_3954_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__0));
v___x_3955_ = l_Lean_Expr_isConstOf(v_arg_3950_, v___x_3954_);
if (v___x_3955_ == 0)
{
lean_object* v___x_3956_; uint8_t v___x_3957_; 
v___x_3956_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__2));
v___x_3957_ = l_Lean_Expr_isConstOf(v_arg_3950_, v___x_3956_);
if (v___x_3957_ == 0)
{
lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; 
v___x_3958_ = lean_box(v_eqTrue_3917_);
v___x_3959_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe___boxed), 14, 2);
lean_closure_set(v___x_3959_, 0, v_e_3916_);
lean_closure_set(v___x_3959_, 1, v___x_3958_);
v___x_3960_ = l_Lean_Meta_Grind_Arith_Cutsat_ToIntM_run(v_arg_3950_, v___x_3959_, v_a_3918_, v_a_3919_, v_a_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_, v_a_3927_);
return v___x_3960_;
}
else
{
lean_object* v___x_3961_; 
lean_dec_ref(v_arg_3950_);
v___x_3961_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe(v_e_3916_, v_eqTrue_3917_, v_a_3918_, v_a_3919_, v_a_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_, v_a_3927_);
return v___x_3961_;
}
}
else
{
lean_object* v___x_3962_; 
lean_dec_ref(v_arg_3950_);
v___x_3962_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe(v_e_3916_, v_eqTrue_3917_, v_a_3918_, v_a_3919_, v_a_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_, v_a_3927_);
return v___x_3962_;
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
lean_object* v_a_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_3971_; 
lean_dec_ref(v_e_3916_);
v_a_3964_ = lean_ctor_get(v___x_3932_, 0);
v_isSharedCheck_3971_ = !lean_is_exclusive(v___x_3932_);
if (v_isSharedCheck_3971_ == 0)
{
v___x_3966_ = v___x_3932_;
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_a_3964_);
lean_dec(v___x_3932_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
lean_object* v___x_3969_; 
if (v_isShared_3967_ == 0)
{
v___x_3969_ = v___x_3966_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v_a_3964_);
v___x_3969_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
return v___x_3969_;
}
}
}
v___jp_3929_:
{
lean_object* v___x_3930_; lean_object* v___x_3931_; 
v___x_3930_ = lean_box(0);
v___x_3931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3931_, 0, v___x_3930_);
return v___x_3931_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___boxed(lean_object* v_e_3972_, lean_object* v_eqTrue_3973_, lean_object* v_a_3974_, lean_object* v_a_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_){
_start:
{
uint8_t v_eqTrue_boxed_3985_; lean_object* v_res_3986_; 
v_eqTrue_boxed_3985_ = lean_unbox(v_eqTrue_3973_);
v_res_3986_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLe(v_e_3972_, v_eqTrue_boxed_3985_, v_a_3974_, v_a_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_);
lean_dec(v_a_3983_);
lean_dec_ref(v_a_3982_);
lean_dec(v_a_3981_);
lean_dec_ref(v_a_3980_);
lean_dec(v_a_3979_);
lean_dec_ref(v_a_3978_);
lean_dec(v_a_3977_);
lean_dec_ref(v_a_3976_);
lean_dec(v_a_3975_);
lean_dec(v_a_3974_);
return v_res_3986_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__0(lean_object* v_e_3987_, lean_object* v_arg_3988_, lean_object* v_arg_3989_, uint8_t v_eqTrue_3990_, lean_object* v_____x_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_){
_start:
{
if (lean_obj_tag(v_____x_3991_) == 1)
{
lean_object* v_val_4004_; lean_object* v___x_4005_; 
v_val_4004_ = lean_ctor_get(v_____x_3991_, 0);
lean_inc(v_val_4004_);
lean_dec_ref(v_____x_3991_);
v___x_4005_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_3987_, v___y_3993_);
if (lean_obj_tag(v___x_4005_) == 0)
{
lean_object* v_a_4006_; lean_object* v___x_4007_; 
v_a_4006_ = lean_ctor_get(v___x_4005_, 0);
lean_inc(v_a_4006_);
lean_dec_ref(v___x_4005_);
lean_inc_ref(v_arg_3988_);
v___x_4007_ = l_Lean_Meta_Grind_Arith_Cutsat_toInt(v_arg_3988_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_);
if (lean_obj_tag(v___x_4007_) == 0)
{
lean_object* v_a_4008_; lean_object* v_fst_4009_; lean_object* v_snd_4010_; lean_object* v___x_4012_; uint8_t v_isShared_4013_; uint8_t v_isSharedCheck_4065_; 
v_a_4008_ = lean_ctor_get(v___x_4007_, 0);
lean_inc(v_a_4008_);
lean_dec_ref(v___x_4007_);
v_fst_4009_ = lean_ctor_get(v_a_4008_, 0);
v_snd_4010_ = lean_ctor_get(v_a_4008_, 1);
v_isSharedCheck_4065_ = !lean_is_exclusive(v_a_4008_);
if (v_isSharedCheck_4065_ == 0)
{
v___x_4012_ = v_a_4008_;
v_isShared_4013_ = v_isSharedCheck_4065_;
goto v_resetjp_4011_;
}
else
{
lean_inc(v_snd_4010_);
lean_inc(v_fst_4009_);
lean_dec(v_a_4008_);
v___x_4012_ = lean_box(0);
v_isShared_4013_ = v_isSharedCheck_4065_;
goto v_resetjp_4011_;
}
v_resetjp_4011_:
{
lean_object* v___x_4014_; 
lean_inc_ref(v_arg_3989_);
v___x_4014_ = l_Lean_Meta_Grind_Arith_Cutsat_toInt(v_arg_3989_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_);
if (lean_obj_tag(v___x_4014_) == 0)
{
lean_object* v_a_4015_; lean_object* v_fst_4016_; lean_object* v_snd_4017_; lean_object* v___x_4019_; uint8_t v_isShared_4020_; uint8_t v_isSharedCheck_4056_; 
v_a_4015_ = lean_ctor_get(v___x_4014_, 0);
lean_inc(v_a_4015_);
lean_dec_ref(v___x_4014_);
v_fst_4016_ = lean_ctor_get(v_a_4015_, 0);
v_snd_4017_ = lean_ctor_get(v_a_4015_, 1);
v_isSharedCheck_4056_ = !lean_is_exclusive(v_a_4015_);
if (v_isSharedCheck_4056_ == 0)
{
v___x_4019_ = v_a_4015_;
v_isShared_4020_ = v_isSharedCheck_4056_;
goto v_resetjp_4018_;
}
else
{
lean_inc(v_snd_4017_);
lean_inc(v_fst_4016_);
lean_dec(v_a_4015_);
v___x_4019_ = lean_box(0);
v_isShared_4020_ = v_isSharedCheck_4056_;
goto v_resetjp_4018_;
}
v_resetjp_4018_:
{
lean_object* v___x_4021_; lean_object* v_fst_4023_; lean_object* v_snd_4024_; 
lean_inc(v_fst_4016_);
lean_inc(v_fst_4009_);
v___x_4021_ = l_Lean_mkApp6(v_val_4004_, v_arg_3988_, v_arg_3989_, v_fst_4009_, v_fst_4016_, v_snd_4010_, v_snd_4017_);
if (v_eqTrue_3990_ == 0)
{
v_fst_4023_ = v_fst_4016_;
v_snd_4024_ = v_fst_4009_;
goto v___jp_4022_;
}
else
{
lean_object* v___x_4054_; lean_object* v___x_4055_; 
v___x_4054_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0);
v___x_4055_ = l_Lean_mkIntAdd(v_fst_4009_, v___x_4054_);
v_fst_4023_ = v___x_4055_;
v_snd_4024_ = v_fst_4016_;
goto v___jp_4022_;
}
v___jp_4022_:
{
lean_object* v___x_4025_; 
lean_inc(v_a_4006_);
v___x_4025_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_4023_, v_a_4006_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_);
if (lean_obj_tag(v___x_4025_) == 0)
{
lean_object* v_a_4026_; lean_object* v___x_4027_; 
v_a_4026_ = lean_ctor_get(v___x_4025_, 0);
lean_inc(v_a_4026_);
lean_dec_ref(v___x_4025_);
v___x_4027_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_snd_4024_, v_a_4006_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_);
if (lean_obj_tag(v___x_4027_) == 0)
{
lean_object* v_a_4028_; lean_object* v___x_4030_; 
v_a_4028_ = lean_ctor_get(v___x_4027_, 0);
lean_inc_n(v_a_4028_, 2);
lean_dec_ref(v___x_4027_);
lean_inc(v_a_4026_);
if (v_isShared_4020_ == 0)
{
lean_ctor_set_tag(v___x_4019_, 3);
lean_ctor_set(v___x_4019_, 1, v_a_4028_);
lean_ctor_set(v___x_4019_, 0, v_a_4026_);
v___x_4030_ = v___x_4019_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4037_; 
v_reuseFailAlloc_4037_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4037_, 0, v_a_4026_);
lean_ctor_set(v_reuseFailAlloc_4037_, 1, v_a_4028_);
v___x_4030_ = v_reuseFailAlloc_4037_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4034_; 
v___x_4031_ = l_Int_Linear_Expr_norm(v___x_4030_);
lean_dec_ref(v___x_4030_);
v___x_4032_ = lean_alloc_ctor(2, 4, 1);
lean_ctor_set(v___x_4032_, 0, v_e_3987_);
lean_ctor_set(v___x_4032_, 1, v___x_4021_);
lean_ctor_set(v___x_4032_, 2, v_a_4026_);
lean_ctor_set(v___x_4032_, 3, v_a_4028_);
lean_ctor_set_uint8(v___x_4032_, sizeof(void*)*4, v_eqTrue_3990_);
if (v_isShared_4013_ == 0)
{
lean_ctor_set(v___x_4012_, 1, v___x_4032_);
lean_ctor_set(v___x_4012_, 0, v___x_4031_);
v___x_4034_ = v___x_4012_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4036_; 
v_reuseFailAlloc_4036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4036_, 0, v___x_4031_);
lean_ctor_set(v_reuseFailAlloc_4036_, 1, v___x_4032_);
v___x_4034_ = v_reuseFailAlloc_4036_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
lean_object* v___x_4035_; 
lean_inc(v___y_4002_);
lean_inc_ref(v___y_4001_);
lean_inc(v___y_4000_);
lean_inc_ref(v___y_3999_);
lean_inc(v___y_3998_);
lean_inc_ref(v___y_3997_);
lean_inc(v___y_3996_);
lean_inc_ref(v___y_3995_);
lean_inc(v___y_3994_);
lean_inc(v___y_3993_);
v___x_4035_ = lean_grind_cutsat_assert_le(v___x_4034_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_);
return v___x_4035_;
}
}
}
else
{
lean_object* v_a_4038_; lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4045_; 
lean_dec(v_a_4026_);
lean_dec_ref(v___x_4021_);
lean_del_object(v___x_4019_);
lean_del_object(v___x_4012_);
lean_dec_ref(v_e_3987_);
v_a_4038_ = lean_ctor_get(v___x_4027_, 0);
v_isSharedCheck_4045_ = !lean_is_exclusive(v___x_4027_);
if (v_isSharedCheck_4045_ == 0)
{
v___x_4040_ = v___x_4027_;
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
else
{
lean_inc(v_a_4038_);
lean_dec(v___x_4027_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
lean_object* v___x_4043_; 
if (v_isShared_4041_ == 0)
{
v___x_4043_ = v___x_4040_;
goto v_reusejp_4042_;
}
else
{
lean_object* v_reuseFailAlloc_4044_; 
v_reuseFailAlloc_4044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4044_, 0, v_a_4038_);
v___x_4043_ = v_reuseFailAlloc_4044_;
goto v_reusejp_4042_;
}
v_reusejp_4042_:
{
return v___x_4043_;
}
}
}
}
else
{
lean_object* v_a_4046_; lean_object* v___x_4048_; uint8_t v_isShared_4049_; uint8_t v_isSharedCheck_4053_; 
lean_dec_ref(v_snd_4024_);
lean_dec_ref(v___x_4021_);
lean_del_object(v___x_4019_);
lean_del_object(v___x_4012_);
lean_dec(v_a_4006_);
lean_dec_ref(v_e_3987_);
v_a_4046_ = lean_ctor_get(v___x_4025_, 0);
v_isSharedCheck_4053_ = !lean_is_exclusive(v___x_4025_);
if (v_isSharedCheck_4053_ == 0)
{
v___x_4048_ = v___x_4025_;
v_isShared_4049_ = v_isSharedCheck_4053_;
goto v_resetjp_4047_;
}
else
{
lean_inc(v_a_4046_);
lean_dec(v___x_4025_);
v___x_4048_ = lean_box(0);
v_isShared_4049_ = v_isSharedCheck_4053_;
goto v_resetjp_4047_;
}
v_resetjp_4047_:
{
lean_object* v___x_4051_; 
if (v_isShared_4049_ == 0)
{
v___x_4051_ = v___x_4048_;
goto v_reusejp_4050_;
}
else
{
lean_object* v_reuseFailAlloc_4052_; 
v_reuseFailAlloc_4052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4052_, 0, v_a_4046_);
v___x_4051_ = v_reuseFailAlloc_4052_;
goto v_reusejp_4050_;
}
v_reusejp_4050_:
{
return v___x_4051_;
}
}
}
}
}
}
else
{
lean_object* v_a_4057_; lean_object* v___x_4059_; uint8_t v_isShared_4060_; uint8_t v_isSharedCheck_4064_; 
lean_del_object(v___x_4012_);
lean_dec(v_snd_4010_);
lean_dec(v_fst_4009_);
lean_dec(v_a_4006_);
lean_dec(v_val_4004_);
lean_dec_ref(v_arg_3989_);
lean_dec_ref(v_arg_3988_);
lean_dec_ref(v_e_3987_);
v_a_4057_ = lean_ctor_get(v___x_4014_, 0);
v_isSharedCheck_4064_ = !lean_is_exclusive(v___x_4014_);
if (v_isSharedCheck_4064_ == 0)
{
v___x_4059_ = v___x_4014_;
v_isShared_4060_ = v_isSharedCheck_4064_;
goto v_resetjp_4058_;
}
else
{
lean_inc(v_a_4057_);
lean_dec(v___x_4014_);
v___x_4059_ = lean_box(0);
v_isShared_4060_ = v_isSharedCheck_4064_;
goto v_resetjp_4058_;
}
v_resetjp_4058_:
{
lean_object* v___x_4062_; 
if (v_isShared_4060_ == 0)
{
v___x_4062_ = v___x_4059_;
goto v_reusejp_4061_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v_a_4057_);
v___x_4062_ = v_reuseFailAlloc_4063_;
goto v_reusejp_4061_;
}
v_reusejp_4061_:
{
return v___x_4062_;
}
}
}
}
}
else
{
lean_object* v_a_4066_; lean_object* v___x_4068_; uint8_t v_isShared_4069_; uint8_t v_isSharedCheck_4073_; 
lean_dec(v_a_4006_);
lean_dec(v_val_4004_);
lean_dec_ref(v_arg_3989_);
lean_dec_ref(v_arg_3988_);
lean_dec_ref(v_e_3987_);
v_a_4066_ = lean_ctor_get(v___x_4007_, 0);
v_isSharedCheck_4073_ = !lean_is_exclusive(v___x_4007_);
if (v_isSharedCheck_4073_ == 0)
{
v___x_4068_ = v___x_4007_;
v_isShared_4069_ = v_isSharedCheck_4073_;
goto v_resetjp_4067_;
}
else
{
lean_inc(v_a_4066_);
lean_dec(v___x_4007_);
v___x_4068_ = lean_box(0);
v_isShared_4069_ = v_isSharedCheck_4073_;
goto v_resetjp_4067_;
}
v_resetjp_4067_:
{
lean_object* v___x_4071_; 
if (v_isShared_4069_ == 0)
{
v___x_4071_ = v___x_4068_;
goto v_reusejp_4070_;
}
else
{
lean_object* v_reuseFailAlloc_4072_; 
v_reuseFailAlloc_4072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4072_, 0, v_a_4066_);
v___x_4071_ = v_reuseFailAlloc_4072_;
goto v_reusejp_4070_;
}
v_reusejp_4070_:
{
return v___x_4071_;
}
}
}
}
else
{
lean_object* v_a_4074_; lean_object* v___x_4076_; uint8_t v_isShared_4077_; uint8_t v_isSharedCheck_4081_; 
lean_dec(v_val_4004_);
lean_dec_ref(v_arg_3989_);
lean_dec_ref(v_arg_3988_);
lean_dec_ref(v_e_3987_);
v_a_4074_ = lean_ctor_get(v___x_4005_, 0);
v_isSharedCheck_4081_ = !lean_is_exclusive(v___x_4005_);
if (v_isSharedCheck_4081_ == 0)
{
v___x_4076_ = v___x_4005_;
v_isShared_4077_ = v_isSharedCheck_4081_;
goto v_resetjp_4075_;
}
else
{
lean_inc(v_a_4074_);
lean_dec(v___x_4005_);
v___x_4076_ = lean_box(0);
v_isShared_4077_ = v_isSharedCheck_4081_;
goto v_resetjp_4075_;
}
v_resetjp_4075_:
{
lean_object* v___x_4079_; 
if (v_isShared_4077_ == 0)
{
v___x_4079_ = v___x_4076_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v_a_4074_);
v___x_4079_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4078_;
}
v_reusejp_4078_:
{
return v___x_4079_;
}
}
}
}
else
{
lean_object* v___x_4082_; lean_object* v___x_4083_; 
lean_dec(v_____x_3991_);
lean_dec_ref(v_arg_3989_);
lean_dec_ref(v_arg_3988_);
lean_dec_ref(v_e_3987_);
v___x_4082_ = lean_box(0);
v___x_4083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4083_, 0, v___x_4082_);
return v___x_4083_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__0___boxed(lean_object** _args){
lean_object* v_e_4084_ = _args[0];
lean_object* v_arg_4085_ = _args[1];
lean_object* v_arg_4086_ = _args[2];
lean_object* v_eqTrue_4087_ = _args[3];
lean_object* v_____x_4088_ = _args[4];
lean_object* v___y_4089_ = _args[5];
lean_object* v___y_4090_ = _args[6];
lean_object* v___y_4091_ = _args[7];
lean_object* v___y_4092_ = _args[8];
lean_object* v___y_4093_ = _args[9];
lean_object* v___y_4094_ = _args[10];
lean_object* v___y_4095_ = _args[11];
lean_object* v___y_4096_ = _args[12];
lean_object* v___y_4097_ = _args[13];
lean_object* v___y_4098_ = _args[14];
lean_object* v___y_4099_ = _args[15];
lean_object* v___y_4100_ = _args[16];
_start:
{
uint8_t v_eqTrue_boxed_4101_; lean_object* v_res_4102_; 
v_eqTrue_boxed_4101_ = lean_unbox(v_eqTrue_4087_);
v_res_4102_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__0(v_e_4084_, v_arg_4085_, v_arg_4086_, v_eqTrue_boxed_4101_, v_____x_4088_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_);
lean_dec(v___y_4099_);
lean_dec_ref(v___y_4098_);
lean_dec(v___y_4097_);
lean_dec_ref(v___y_4096_);
lean_dec(v___y_4095_);
lean_dec_ref(v___y_4094_);
lean_dec(v___y_4093_);
lean_dec_ref(v___y_4092_);
lean_dec(v___y_4091_);
lean_dec(v___y_4090_);
lean_dec(v___y_4089_);
return v_res_4102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__1(uint8_t v_eqTrue_4103_, lean_object* v___f_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_){
_start:
{
if (v_eqTrue_4103_ == 0)
{
lean_object* v___x_4117_; 
v___x_4117_ = l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLT_x3f___redArg(v___y_4105_, v___y_4106_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_);
if (lean_obj_tag(v___x_4117_) == 0)
{
lean_object* v_a_4118_; lean_object* v___x_4119_; 
v_a_4118_ = lean_ctor_get(v___x_4117_, 0);
lean_inc(v_a_4118_);
lean_dec_ref(v___x_4117_);
lean_inc(v___y_4115_);
lean_inc_ref(v___y_4114_);
lean_inc(v___y_4113_);
lean_inc_ref(v___y_4112_);
lean_inc(v___y_4111_);
lean_inc_ref(v___y_4110_);
lean_inc(v___y_4109_);
lean_inc_ref(v___y_4108_);
lean_inc(v___y_4107_);
lean_inc(v___y_4106_);
lean_inc(v___y_4105_);
v___x_4119_ = lean_apply_13(v___f_4104_, v_a_4118_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, lean_box(0));
return v___x_4119_;
}
else
{
lean_object* v_a_4120_; lean_object* v___x_4122_; uint8_t v_isShared_4123_; uint8_t v_isSharedCheck_4127_; 
lean_dec_ref(v___f_4104_);
v_a_4120_ = lean_ctor_get(v___x_4117_, 0);
v_isSharedCheck_4127_ = !lean_is_exclusive(v___x_4117_);
if (v_isSharedCheck_4127_ == 0)
{
v___x_4122_ = v___x_4117_;
v_isShared_4123_ = v_isSharedCheck_4127_;
goto v_resetjp_4121_;
}
else
{
lean_inc(v_a_4120_);
lean_dec(v___x_4117_);
v___x_4122_ = lean_box(0);
v_isShared_4123_ = v_isSharedCheck_4127_;
goto v_resetjp_4121_;
}
v_resetjp_4121_:
{
lean_object* v___x_4125_; 
if (v_isShared_4123_ == 0)
{
v___x_4125_ = v___x_4122_;
goto v_reusejp_4124_;
}
else
{
lean_object* v_reuseFailAlloc_4126_; 
v_reuseFailAlloc_4126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4126_, 0, v_a_4120_);
v___x_4125_ = v_reuseFailAlloc_4126_;
goto v_reusejp_4124_;
}
v_reusejp_4124_:
{
return v___x_4125_;
}
}
}
}
else
{
lean_object* v___x_4128_; 
v___x_4128_ = l_Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f___redArg(v___y_4105_, v___y_4106_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_);
if (lean_obj_tag(v___x_4128_) == 0)
{
lean_object* v_a_4129_; lean_object* v___x_4130_; 
v_a_4129_ = lean_ctor_get(v___x_4128_, 0);
lean_inc(v_a_4129_);
lean_dec_ref(v___x_4128_);
lean_inc(v___y_4115_);
lean_inc_ref(v___y_4114_);
lean_inc(v___y_4113_);
lean_inc_ref(v___y_4112_);
lean_inc(v___y_4111_);
lean_inc_ref(v___y_4110_);
lean_inc(v___y_4109_);
lean_inc_ref(v___y_4108_);
lean_inc(v___y_4107_);
lean_inc(v___y_4106_);
lean_inc(v___y_4105_);
v___x_4130_ = lean_apply_13(v___f_4104_, v_a_4129_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, lean_box(0));
return v___x_4130_;
}
else
{
lean_object* v_a_4131_; lean_object* v___x_4133_; uint8_t v_isShared_4134_; uint8_t v_isSharedCheck_4138_; 
lean_dec_ref(v___f_4104_);
v_a_4131_ = lean_ctor_get(v___x_4128_, 0);
v_isSharedCheck_4138_ = !lean_is_exclusive(v___x_4128_);
if (v_isSharedCheck_4138_ == 0)
{
v___x_4133_ = v___x_4128_;
v_isShared_4134_ = v_isSharedCheck_4138_;
goto v_resetjp_4132_;
}
else
{
lean_inc(v_a_4131_);
lean_dec(v___x_4128_);
v___x_4133_ = lean_box(0);
v_isShared_4134_ = v_isSharedCheck_4138_;
goto v_resetjp_4132_;
}
v_resetjp_4132_:
{
lean_object* v___x_4136_; 
if (v_isShared_4134_ == 0)
{
v___x_4136_ = v___x_4133_;
goto v_reusejp_4135_;
}
else
{
lean_object* v_reuseFailAlloc_4137_; 
v_reuseFailAlloc_4137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4137_, 0, v_a_4131_);
v___x_4136_ = v_reuseFailAlloc_4137_;
goto v_reusejp_4135_;
}
v_reusejp_4135_:
{
return v___x_4136_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__1___boxed(lean_object* v_eqTrue_4139_, lean_object* v___f_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_){
_start:
{
uint8_t v_eqTrue_boxed_4153_; lean_object* v_res_4154_; 
v_eqTrue_boxed_4153_ = lean_unbox(v_eqTrue_4139_);
v_res_4154_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__1(v_eqTrue_boxed_4153_, v___f_4140_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_, v___y_4151_);
lean_dec(v___y_4151_);
lean_dec_ref(v___y_4150_);
lean_dec(v___y_4149_);
lean_dec_ref(v___y_4148_);
lean_dec(v___y_4147_);
lean_dec_ref(v___y_4146_);
lean_dec(v___y_4145_);
lean_dec_ref(v___y_4144_);
lean_dec(v___y_4143_);
lean_dec(v___y_4142_);
lean_dec(v___y_4141_);
return v_res_4154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt(lean_object* v_e_4160_, uint8_t v_eqTrue_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_, lean_object* v_a_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_){
_start:
{
lean_object* v___x_4176_; 
v___x_4176_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_4164_);
if (lean_obj_tag(v___x_4176_) == 0)
{
lean_object* v_a_4177_; lean_object* v___x_4179_; uint8_t v_isShared_4180_; uint8_t v_isSharedCheck_4205_; 
v_a_4177_ = lean_ctor_get(v___x_4176_, 0);
v_isSharedCheck_4205_ = !lean_is_exclusive(v___x_4176_);
if (v_isSharedCheck_4205_ == 0)
{
v___x_4179_ = v___x_4176_;
v_isShared_4180_ = v_isSharedCheck_4205_;
goto v_resetjp_4178_;
}
else
{
lean_inc(v_a_4177_);
lean_dec(v___x_4176_);
v___x_4179_ = lean_box(0);
v_isShared_4180_ = v_isSharedCheck_4205_;
goto v_resetjp_4178_;
}
v_resetjp_4178_:
{
uint8_t v_lia_4181_; 
v_lia_4181_ = lean_ctor_get_uint8(v_a_4177_, sizeof(void*)*12 + 23);
lean_dec(v_a_4177_);
if (v_lia_4181_ == 0)
{
lean_object* v___x_4182_; lean_object* v___x_4184_; 
lean_dec_ref(v_e_4160_);
v___x_4182_ = lean_box(0);
if (v_isShared_4180_ == 0)
{
lean_ctor_set(v___x_4179_, 0, v___x_4182_);
v___x_4184_ = v___x_4179_;
goto v_reusejp_4183_;
}
else
{
lean_object* v_reuseFailAlloc_4185_; 
v_reuseFailAlloc_4185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4185_, 0, v___x_4182_);
v___x_4184_ = v_reuseFailAlloc_4185_;
goto v_reusejp_4183_;
}
v_reusejp_4183_:
{
return v___x_4184_;
}
}
else
{
lean_object* v___x_4186_; uint8_t v___x_4187_; 
lean_del_object(v___x_4179_);
lean_inc_ref(v_e_4160_);
v___x_4186_ = l_Lean_Expr_cleanupAnnotations(v_e_4160_);
v___x_4187_ = l_Lean_Expr_isApp(v___x_4186_);
if (v___x_4187_ == 0)
{
lean_dec_ref(v___x_4186_);
lean_dec_ref(v_e_4160_);
goto v___jp_4173_;
}
else
{
lean_object* v_arg_4188_; lean_object* v___x_4189_; uint8_t v___x_4190_; 
v_arg_4188_ = lean_ctor_get(v___x_4186_, 1);
lean_inc_ref(v_arg_4188_);
v___x_4189_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4186_);
v___x_4190_ = l_Lean_Expr_isApp(v___x_4189_);
if (v___x_4190_ == 0)
{
lean_dec_ref(v___x_4189_);
lean_dec_ref(v_arg_4188_);
lean_dec_ref(v_e_4160_);
goto v___jp_4173_;
}
else
{
lean_object* v_arg_4191_; lean_object* v___x_4192_; uint8_t v___x_4193_; 
v_arg_4191_ = lean_ctor_get(v___x_4189_, 1);
lean_inc_ref(v_arg_4191_);
v___x_4192_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4189_);
v___x_4193_ = l_Lean_Expr_isApp(v___x_4192_);
if (v___x_4193_ == 0)
{
lean_dec_ref(v___x_4192_);
lean_dec_ref(v_arg_4191_);
lean_dec_ref(v_arg_4188_);
lean_dec_ref(v_e_4160_);
goto v___jp_4173_;
}
else
{
lean_object* v___x_4194_; uint8_t v___x_4195_; 
v___x_4194_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4192_);
v___x_4195_ = l_Lean_Expr_isApp(v___x_4194_);
if (v___x_4195_ == 0)
{
lean_dec_ref(v___x_4194_);
lean_dec_ref(v_arg_4191_);
lean_dec_ref(v_arg_4188_);
lean_dec_ref(v_e_4160_);
goto v___jp_4173_;
}
else
{
lean_object* v_arg_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; uint8_t v___x_4199_; 
v_arg_4196_ = lean_ctor_get(v___x_4194_, 1);
lean_inc_ref(v_arg_4196_);
v___x_4197_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4194_);
v___x_4198_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__2));
v___x_4199_ = l_Lean_Expr_isConstOf(v___x_4197_, v___x_4198_);
lean_dec_ref(v___x_4197_);
if (v___x_4199_ == 0)
{
lean_dec_ref(v_arg_4196_);
lean_dec_ref(v_arg_4191_);
lean_dec_ref(v_arg_4188_);
lean_dec_ref(v_e_4160_);
goto v___jp_4173_;
}
else
{
lean_object* v___x_4200_; lean_object* v___f_4201_; lean_object* v___x_4202_; lean_object* v___y_4203_; lean_object* v___x_4204_; 
v___x_4200_ = lean_box(v_eqTrue_4161_);
v___f_4201_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__0___boxed), 17, 4);
lean_closure_set(v___f_4201_, 0, v_e_4160_);
lean_closure_set(v___f_4201_, 1, v_arg_4191_);
lean_closure_set(v___f_4201_, 2, v_arg_4188_);
lean_closure_set(v___f_4201_, 3, v___x_4200_);
v___x_4202_ = lean_box(v_eqTrue_4161_);
v___y_4203_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__1___boxed), 14, 2);
lean_closure_set(v___y_4203_, 0, v___x_4202_);
lean_closure_set(v___y_4203_, 1, v___f_4201_);
v___x_4204_ = l_Lean_Meta_Grind_Arith_Cutsat_ToIntM_run(v_arg_4196_, v___y_4203_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_, v_a_4169_, v_a_4170_, v_a_4171_);
return v___x_4204_;
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
lean_object* v_a_4206_; lean_object* v___x_4208_; uint8_t v_isShared_4209_; uint8_t v_isSharedCheck_4213_; 
lean_dec_ref(v_e_4160_);
v_a_4206_ = lean_ctor_get(v___x_4176_, 0);
v_isSharedCheck_4213_ = !lean_is_exclusive(v___x_4176_);
if (v_isSharedCheck_4213_ == 0)
{
v___x_4208_ = v___x_4176_;
v_isShared_4209_ = v_isSharedCheck_4213_;
goto v_resetjp_4207_;
}
else
{
lean_inc(v_a_4206_);
lean_dec(v___x_4176_);
v___x_4208_ = lean_box(0);
v_isShared_4209_ = v_isSharedCheck_4213_;
goto v_resetjp_4207_;
}
v_resetjp_4207_:
{
lean_object* v___x_4211_; 
if (v_isShared_4209_ == 0)
{
v___x_4211_ = v___x_4208_;
goto v_reusejp_4210_;
}
else
{
lean_object* v_reuseFailAlloc_4212_; 
v_reuseFailAlloc_4212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4212_, 0, v_a_4206_);
v___x_4211_ = v_reuseFailAlloc_4212_;
goto v_reusejp_4210_;
}
v_reusejp_4210_:
{
return v___x_4211_;
}
}
}
v___jp_4173_:
{
lean_object* v___x_4174_; lean_object* v___x_4175_; 
v___x_4174_ = lean_box(0);
v___x_4175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4175_, 0, v___x_4174_);
return v___x_4175_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___boxed(lean_object* v_e_4214_, lean_object* v_eqTrue_4215_, lean_object* v_a_4216_, lean_object* v_a_4217_, lean_object* v_a_4218_, lean_object* v_a_4219_, lean_object* v_a_4220_, lean_object* v_a_4221_, lean_object* v_a_4222_, lean_object* v_a_4223_, lean_object* v_a_4224_, lean_object* v_a_4225_, lean_object* v_a_4226_){
_start:
{
uint8_t v_eqTrue_boxed_4227_; lean_object* v_res_4228_; 
v_eqTrue_boxed_4227_ = lean_unbox(v_eqTrue_4215_);
v_res_4228_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLt(v_e_4214_, v_eqTrue_boxed_4227_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_, v_a_4220_, v_a_4221_, v_a_4222_, v_a_4223_, v_a_4224_, v_a_4225_);
lean_dec(v_a_4225_);
lean_dec_ref(v_a_4224_);
lean_dec(v_a_4223_);
lean_dec_ref(v_a_4222_);
lean_dec(v_a_4221_);
lean_dec_ref(v_a_4220_);
lean_dec(v_a_4219_);
lean_dec_ref(v_a_4218_);
lean_dec(v_a_4217_);
lean_dec(v_a_4216_);
return v_res_4228_;
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
