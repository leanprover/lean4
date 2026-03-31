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
lean_object* v_fileName_317_; lean_object* v_fileMap_318_; lean_object* v_options_319_; lean_object* v_currRecDepth_320_; lean_object* v_maxRecDepth_321_; lean_object* v_ref_322_; lean_object* v_currNamespace_323_; lean_object* v_openDecls_324_; lean_object* v_initHeartbeats_325_; lean_object* v_maxHeartbeats_326_; lean_object* v_quotContext_327_; lean_object* v_currMacroScope_328_; uint8_t v_diag_329_; lean_object* v_cancelTk_x3f_330_; uint8_t v_suppressElabErrors_331_; lean_object* v_inheritedTraceOptions_332_; uint8_t v___x_333_; 
v_fileName_317_ = lean_ctor_get(v_a_314_, 0);
lean_inc_ref(v_fileName_317_);
v_fileMap_318_ = lean_ctor_get(v_a_314_, 1);
lean_inc_ref(v_fileMap_318_);
v_options_319_ = lean_ctor_get(v_a_314_, 2);
lean_inc_ref(v_options_319_);
v_currRecDepth_320_ = lean_ctor_get(v_a_314_, 3);
lean_inc(v_currRecDepth_320_);
v_maxRecDepth_321_ = lean_ctor_get(v_a_314_, 4);
lean_inc(v_maxRecDepth_321_);
v_ref_322_ = lean_ctor_get(v_a_314_, 5);
lean_inc(v_ref_322_);
v_currNamespace_323_ = lean_ctor_get(v_a_314_, 6);
lean_inc(v_currNamespace_323_);
v_openDecls_324_ = lean_ctor_get(v_a_314_, 7);
lean_inc(v_openDecls_324_);
v_initHeartbeats_325_ = lean_ctor_get(v_a_314_, 8);
lean_inc(v_initHeartbeats_325_);
v_maxHeartbeats_326_ = lean_ctor_get(v_a_314_, 9);
lean_inc(v_maxHeartbeats_326_);
v_quotContext_327_ = lean_ctor_get(v_a_314_, 10);
lean_inc(v_quotContext_327_);
v_currMacroScope_328_ = lean_ctor_get(v_a_314_, 11);
lean_inc(v_currMacroScope_328_);
v_diag_329_ = lean_ctor_get_uint8(v_a_314_, sizeof(void*)*14);
v_cancelTk_x3f_330_ = lean_ctor_get(v_a_314_, 12);
lean_inc(v_cancelTk_x3f_330_);
v_suppressElabErrors_331_ = lean_ctor_get_uint8(v_a_314_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_332_ = lean_ctor_get(v_a_314_, 13);
lean_inc_ref(v_inheritedTraceOptions_332_);
lean_dec_ref(v_a_314_);
v___x_333_ = lean_nat_dec_eq(v_currRecDepth_320_, v_maxRecDepth_321_);
if (v___x_333_ == 0)
{
lean_object* v_p_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; 
v_p_334_ = lean_ctor_get(v_c_305_, 0);
v___x_335_ = lean_unsigned_to_nat(1u);
v___x_336_ = lean_nat_add(v_currRecDepth_320_, v___x_335_);
lean_dec(v_currRecDepth_320_);
v___x_337_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_337_, 0, v_fileName_317_);
lean_ctor_set(v___x_337_, 1, v_fileMap_318_);
lean_ctor_set(v___x_337_, 2, v_options_319_);
lean_ctor_set(v___x_337_, 3, v___x_336_);
lean_ctor_set(v___x_337_, 4, v_maxRecDepth_321_);
lean_ctor_set(v___x_337_, 5, v_ref_322_);
lean_ctor_set(v___x_337_, 6, v_currNamespace_323_);
lean_ctor_set(v___x_337_, 7, v_openDecls_324_);
lean_ctor_set(v___x_337_, 8, v_initHeartbeats_325_);
lean_ctor_set(v___x_337_, 9, v_maxHeartbeats_326_);
lean_ctor_set(v___x_337_, 10, v_quotContext_327_);
lean_ctor_set(v___x_337_, 11, v_currMacroScope_328_);
lean_ctor_set(v___x_337_, 12, v_cancelTk_x3f_330_);
lean_ctor_set(v___x_337_, 13, v_inheritedTraceOptions_332_);
lean_ctor_set_uint8(v___x_337_, sizeof(void*)*14, v_diag_329_);
lean_ctor_set_uint8(v___x_337_, sizeof(void*)*14 + 1, v_suppressElabErrors_331_);
lean_inc_ref(v_p_334_);
v___x_338_ = l_Int_Linear_Poly_findVarToSubst___redArg(v_p_334_, v_a_306_, v___x_337_);
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
else
{
lean_object* v___x_365_; 
lean_dec_ref(v_inheritedTraceOptions_332_);
lean_dec(v_cancelTk_x3f_330_);
lean_dec(v_currMacroScope_328_);
lean_dec(v_quotContext_327_);
lean_dec(v_maxHeartbeats_326_);
lean_dec(v_initHeartbeats_325_);
lean_dec(v_openDecls_324_);
lean_dec(v_currNamespace_323_);
lean_dec(v_maxRecDepth_321_);
lean_dec(v_currRecDepth_320_);
lean_dec_ref(v_options_319_);
lean_dec_ref(v_fileMap_318_);
lean_dec_ref(v_fileName_317_);
lean_dec_ref(v_c_305_);
v___x_365_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg(v_ref_322_);
return v___x_365_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts___boxed(lean_object* v_c_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts(v_c_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_);
lean_dec(v_a_376_);
lean_dec(v_a_374_);
lean_dec_ref(v_a_373_);
lean_dec(v_a_372_);
lean_dec_ref(v_a_371_);
lean_dec(v_a_370_);
lean_dec_ref(v_a_369_);
lean_dec(v_a_368_);
lean_dec(v_a_367_);
return v_res_378_;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_Poly_isNegEq(lean_object* v_p_u2081_379_, lean_object* v_p_u2082_380_){
_start:
{
if (lean_obj_tag(v_p_u2081_379_) == 0)
{
if (lean_obj_tag(v_p_u2082_380_) == 0)
{
lean_object* v_k_381_; lean_object* v_k_382_; lean_object* v___x_383_; uint8_t v___x_384_; 
v_k_381_ = lean_ctor_get(v_p_u2081_379_, 0);
v_k_382_ = lean_ctor_get(v_p_u2082_380_, 0);
v___x_383_ = lean_int_neg(v_k_382_);
v___x_384_ = lean_int_dec_eq(v_k_381_, v___x_383_);
lean_dec(v___x_383_);
return v___x_384_;
}
else
{
uint8_t v___x_385_; 
v___x_385_ = 0;
return v___x_385_;
}
}
else
{
if (lean_obj_tag(v_p_u2082_380_) == 1)
{
lean_object* v_k_386_; lean_object* v_v_387_; lean_object* v_p_388_; lean_object* v_k_389_; lean_object* v_v_390_; lean_object* v_p_391_; uint8_t v___y_393_; lean_object* v___x_395_; uint8_t v___x_396_; 
v_k_386_ = lean_ctor_get(v_p_u2081_379_, 0);
v_v_387_ = lean_ctor_get(v_p_u2081_379_, 1);
v_p_388_ = lean_ctor_get(v_p_u2081_379_, 2);
v_k_389_ = lean_ctor_get(v_p_u2082_380_, 0);
v_v_390_ = lean_ctor_get(v_p_u2082_380_, 1);
v_p_391_ = lean_ctor_get(v_p_u2082_380_, 2);
v___x_395_ = lean_int_neg(v_k_389_);
v___x_396_ = lean_int_dec_eq(v_k_386_, v___x_395_);
lean_dec(v___x_395_);
if (v___x_396_ == 0)
{
v___y_393_ = v___x_396_;
goto v___jp_392_;
}
else
{
uint8_t v___x_397_; 
v___x_397_ = lean_nat_dec_eq(v_v_387_, v_v_390_);
v___y_393_ = v___x_397_;
goto v___jp_392_;
}
v___jp_392_:
{
if (v___y_393_ == 0)
{
return v___y_393_;
}
else
{
v_p_u2081_379_ = v_p_388_;
v_p_u2082_380_ = v_p_391_;
goto _start;
}
}
}
else
{
uint8_t v___x_398_; 
v___x_398_ = 0;
return v___x_398_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isNegEq___boxed(lean_object* v_p_u2081_399_, lean_object* v_p_u2082_400_){
_start:
{
uint8_t v_res_401_; lean_object* v_r_402_; 
v_res_401_ = l_Int_Linear_Poly_isNegEq(v_p_u2081_399_, v_p_u2082_400_);
lean_dec_ref(v_p_u2082_400_);
lean_dec_ref(v_p_u2081_399_);
v_r_402_ = lean_box(v_res_401_);
return v_r_402_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(lean_object* v___x_403_, lean_object* v_as_404_, size_t v_i_405_, size_t v_stop_406_, lean_object* v_b_407_){
_start:
{
lean_object* v___y_409_; uint8_t v___x_413_; 
v___x_413_ = lean_usize_dec_eq(v_i_405_, v_stop_406_);
if (v___x_413_ == 0)
{
lean_object* v___x_414_; lean_object* v_p_415_; uint8_t v___x_416_; 
v___x_414_ = lean_array_uget_borrowed(v_as_404_, v_i_405_);
v_p_415_ = lean_ctor_get(v___x_414_, 0);
v___x_416_ = l_Int_Linear_instBEqPoly_beq(v_p_415_, v___x_403_);
if (v___x_416_ == 0)
{
lean_object* v___x_417_; 
lean_inc(v___x_414_);
v___x_417_ = l_Lean_PersistentArray_push___redArg(v_b_407_, v___x_414_);
v___y_409_ = v___x_417_;
goto v___jp_408_;
}
else
{
v___y_409_ = v_b_407_;
goto v___jp_408_;
}
}
else
{
return v_b_407_;
}
v___jp_408_:
{
size_t v___x_410_; size_t v___x_411_; 
v___x_410_ = ((size_t)1ULL);
v___x_411_ = lean_usize_add(v_i_405_, v___x_410_);
v_i_405_ = v___x_411_;
v_b_407_ = v___y_409_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1___boxed(lean_object* v___x_418_, lean_object* v_as_419_, lean_object* v_i_420_, lean_object* v_stop_421_, lean_object* v_b_422_){
_start:
{
size_t v_i_boxed_423_; size_t v_stop_boxed_424_; lean_object* v_res_425_; 
v_i_boxed_423_ = lean_unbox_usize(v_i_420_);
lean_dec(v_i_420_);
v_stop_boxed_424_ = lean_unbox_usize(v_stop_421_);
lean_dec(v_stop_421_);
v_res_425_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_418_, v_as_419_, v_i_boxed_423_, v_stop_boxed_424_, v_b_422_);
lean_dec_ref(v_as_419_);
lean_dec_ref(v___x_418_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2(lean_object* v___x_426_, lean_object* v_x_427_, lean_object* v_x_428_){
_start:
{
if (lean_obj_tag(v_x_427_) == 0)
{
lean_object* v_cs_429_; lean_object* v___x_430_; lean_object* v___x_431_; uint8_t v___x_432_; 
v_cs_429_ = lean_ctor_get(v_x_427_, 0);
v___x_430_ = lean_unsigned_to_nat(0u);
v___x_431_ = lean_array_get_size(v_cs_429_);
v___x_432_ = lean_nat_dec_lt(v___x_430_, v___x_431_);
if (v___x_432_ == 0)
{
return v_x_428_;
}
else
{
uint8_t v___x_433_; 
v___x_433_ = lean_nat_dec_le(v___x_431_, v___x_431_);
if (v___x_433_ == 0)
{
if (v___x_432_ == 0)
{
return v_x_428_;
}
else
{
size_t v___x_434_; size_t v___x_435_; lean_object* v___x_436_; 
v___x_434_ = ((size_t)0ULL);
v___x_435_ = lean_usize_of_nat(v___x_431_);
v___x_436_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v___x_426_, v_cs_429_, v___x_434_, v___x_435_, v_x_428_);
return v___x_436_;
}
}
else
{
size_t v___x_437_; size_t v___x_438_; lean_object* v___x_439_; 
v___x_437_ = ((size_t)0ULL);
v___x_438_ = lean_usize_of_nat(v___x_431_);
v___x_439_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v___x_426_, v_cs_429_, v___x_437_, v___x_438_, v_x_428_);
return v___x_439_;
}
}
}
else
{
lean_object* v_vs_440_; lean_object* v___x_441_; lean_object* v___x_442_; uint8_t v___x_443_; 
v_vs_440_ = lean_ctor_get(v_x_427_, 0);
v___x_441_ = lean_unsigned_to_nat(0u);
v___x_442_ = lean_array_get_size(v_vs_440_);
v___x_443_ = lean_nat_dec_lt(v___x_441_, v___x_442_);
if (v___x_443_ == 0)
{
return v_x_428_;
}
else
{
uint8_t v___x_444_; 
v___x_444_ = lean_nat_dec_le(v___x_442_, v___x_442_);
if (v___x_444_ == 0)
{
if (v___x_443_ == 0)
{
return v_x_428_;
}
else
{
size_t v___x_445_; size_t v___x_446_; lean_object* v___x_447_; 
v___x_445_ = ((size_t)0ULL);
v___x_446_ = lean_usize_of_nat(v___x_442_);
v___x_447_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_426_, v_vs_440_, v___x_445_, v___x_446_, v_x_428_);
return v___x_447_;
}
}
else
{
size_t v___x_448_; size_t v___x_449_; lean_object* v___x_450_; 
v___x_448_ = ((size_t)0ULL);
v___x_449_ = lean_usize_of_nat(v___x_442_);
v___x_450_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_426_, v_vs_440_, v___x_448_, v___x_449_, v_x_428_);
return v___x_450_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(lean_object* v___x_451_, lean_object* v_as_452_, size_t v_i_453_, size_t v_stop_454_, lean_object* v_b_455_){
_start:
{
uint8_t v___x_456_; 
v___x_456_ = lean_usize_dec_eq(v_i_453_, v_stop_454_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; lean_object* v___x_458_; size_t v___x_459_; size_t v___x_460_; 
v___x_457_ = lean_array_uget_borrowed(v_as_452_, v_i_453_);
v___x_458_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2(v___x_451_, v___x_457_, v_b_455_);
v___x_459_ = ((size_t)1ULL);
v___x_460_ = lean_usize_add(v_i_453_, v___x_459_);
v_i_453_ = v___x_460_;
v_b_455_ = v___x_458_;
goto _start;
}
else
{
return v_b_455_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1___boxed(lean_object* v___x_462_, lean_object* v_as_463_, lean_object* v_i_464_, lean_object* v_stop_465_, lean_object* v_b_466_){
_start:
{
size_t v_i_boxed_467_; size_t v_stop_boxed_468_; lean_object* v_res_469_; 
v_i_boxed_467_ = lean_unbox_usize(v_i_464_);
lean_dec(v_i_464_);
v_stop_boxed_468_ = lean_unbox_usize(v_stop_465_);
lean_dec(v_stop_465_);
v_res_469_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v___x_462_, v_as_463_, v_i_boxed_467_, v_stop_boxed_468_, v_b_466_);
lean_dec_ref(v_as_463_);
lean_dec_ref(v___x_462_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2___boxed(lean_object* v___x_470_, lean_object* v_x_471_, lean_object* v_x_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2(v___x_470_, v_x_471_, v_x_472_);
lean_dec_ref(v_x_471_);
lean_dec_ref(v___x_470_);
return v_res_473_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(lean_object* v___x_475_, lean_object* v_x_476_, size_t v_x_477_, size_t v_x_478_, lean_object* v_x_479_){
_start:
{
if (lean_obj_tag(v_x_476_) == 0)
{
lean_object* v_cs_480_; lean_object* v___x_481_; size_t v___x_482_; lean_object* v_j_483_; lean_object* v___x_484_; size_t v___x_485_; size_t v___x_486_; size_t v___x_487_; size_t v___x_488_; size_t v___x_489_; size_t v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; uint8_t v___x_495_; 
v_cs_480_ = lean_ctor_get(v_x_476_, 0);
v___x_481_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0);
v___x_482_ = lean_usize_shift_right(v_x_477_, v_x_478_);
v_j_483_ = lean_usize_to_nat(v___x_482_);
v___x_484_ = lean_array_get_borrowed(v___x_481_, v_cs_480_, v_j_483_);
v___x_485_ = ((size_t)1ULL);
v___x_486_ = lean_usize_shift_left(v___x_485_, v_x_478_);
v___x_487_ = lean_usize_sub(v___x_486_, v___x_485_);
v___x_488_ = lean_usize_land(v_x_477_, v___x_487_);
v___x_489_ = ((size_t)5ULL);
v___x_490_ = lean_usize_sub(v_x_478_, v___x_489_);
v___x_491_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(v___x_475_, v___x_484_, v___x_488_, v___x_490_, v_x_479_);
v___x_492_ = lean_unsigned_to_nat(1u);
v___x_493_ = lean_nat_add(v_j_483_, v___x_492_);
lean_dec(v_j_483_);
v___x_494_ = lean_array_get_size(v_cs_480_);
v___x_495_ = lean_nat_dec_lt(v___x_493_, v___x_494_);
if (v___x_495_ == 0)
{
lean_dec(v___x_493_);
return v___x_491_;
}
else
{
uint8_t v___x_496_; 
v___x_496_ = lean_nat_dec_le(v___x_494_, v___x_494_);
if (v___x_496_ == 0)
{
if (v___x_495_ == 0)
{
lean_dec(v___x_493_);
return v___x_491_;
}
else
{
size_t v___x_497_; size_t v___x_498_; lean_object* v___x_499_; 
v___x_497_ = lean_usize_of_nat(v___x_493_);
lean_dec(v___x_493_);
v___x_498_ = lean_usize_of_nat(v___x_494_);
v___x_499_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v___x_475_, v_cs_480_, v___x_497_, v___x_498_, v___x_491_);
return v___x_499_;
}
}
else
{
size_t v___x_500_; size_t v___x_501_; lean_object* v___x_502_; 
v___x_500_ = lean_usize_of_nat(v___x_493_);
lean_dec(v___x_493_);
v___x_501_ = lean_usize_of_nat(v___x_494_);
v___x_502_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v___x_475_, v_cs_480_, v___x_500_, v___x_501_, v___x_491_);
return v___x_502_;
}
}
}
else
{
lean_object* v_vs_503_; lean_object* v___x_504_; lean_object* v___x_505_; uint8_t v___x_506_; 
v_vs_503_ = lean_ctor_get(v_x_476_, 0);
v___x_504_ = lean_usize_to_nat(v_x_477_);
v___x_505_ = lean_array_get_size(v_vs_503_);
v___x_506_ = lean_nat_dec_lt(v___x_504_, v___x_505_);
if (v___x_506_ == 0)
{
lean_dec(v___x_504_);
return v_x_479_;
}
else
{
uint8_t v___x_507_; 
v___x_507_ = lean_nat_dec_le(v___x_505_, v___x_505_);
if (v___x_507_ == 0)
{
if (v___x_506_ == 0)
{
lean_dec(v___x_504_);
return v_x_479_;
}
else
{
size_t v___x_508_; size_t v___x_509_; lean_object* v___x_510_; 
v___x_508_ = lean_usize_of_nat(v___x_504_);
lean_dec(v___x_504_);
v___x_509_ = lean_usize_of_nat(v___x_505_);
v___x_510_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_475_, v_vs_503_, v___x_508_, v___x_509_, v_x_479_);
return v___x_510_;
}
}
else
{
size_t v___x_511_; size_t v___x_512_; lean_object* v___x_513_; 
v___x_511_ = lean_usize_of_nat(v___x_504_);
lean_dec(v___x_504_);
v___x_512_ = lean_usize_of_nat(v___x_505_);
v___x_513_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_475_, v_vs_503_, v___x_511_, v___x_512_, v_x_479_);
return v___x_513_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___boxed(lean_object* v___x_514_, lean_object* v_x_515_, lean_object* v_x_516_, lean_object* v_x_517_, lean_object* v_x_518_){
_start:
{
size_t v_x_2065__boxed_519_; size_t v_x_2066__boxed_520_; lean_object* v_res_521_; 
v_x_2065__boxed_519_ = lean_unbox_usize(v_x_516_);
lean_dec(v_x_516_);
v_x_2066__boxed_520_ = lean_unbox_usize(v_x_517_);
lean_dec(v_x_517_);
v_res_521_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(v___x_514_, v_x_515_, v_x_2065__boxed_519_, v_x_2066__boxed_520_, v_x_518_);
lean_dec_ref(v_x_515_);
lean_dec_ref(v___x_514_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(lean_object* v___x_522_, lean_object* v_t_523_, lean_object* v_init_524_, lean_object* v_start_525_){
_start:
{
lean_object* v___x_526_; uint8_t v___x_527_; 
v___x_526_ = lean_unsigned_to_nat(0u);
v___x_527_ = lean_nat_dec_eq(v_start_525_, v___x_526_);
if (v___x_527_ == 0)
{
lean_object* v_root_528_; lean_object* v_tail_529_; size_t v_shift_530_; lean_object* v_tailOff_531_; uint8_t v___x_532_; 
v_root_528_ = lean_ctor_get(v_t_523_, 0);
v_tail_529_ = lean_ctor_get(v_t_523_, 1);
v_shift_530_ = lean_ctor_get_usize(v_t_523_, 4);
v_tailOff_531_ = lean_ctor_get(v_t_523_, 3);
v___x_532_ = lean_nat_dec_le(v_tailOff_531_, v_start_525_);
if (v___x_532_ == 0)
{
size_t v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; uint8_t v___x_536_; 
v___x_533_ = lean_usize_of_nat(v_start_525_);
v___x_534_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(v___x_522_, v_root_528_, v___x_533_, v_shift_530_, v_init_524_);
v___x_535_ = lean_array_get_size(v_tail_529_);
v___x_536_ = lean_nat_dec_lt(v___x_526_, v___x_535_);
if (v___x_536_ == 0)
{
return v___x_534_;
}
else
{
uint8_t v___x_537_; 
v___x_537_ = lean_nat_dec_le(v___x_535_, v___x_535_);
if (v___x_537_ == 0)
{
if (v___x_536_ == 0)
{
return v___x_534_;
}
else
{
size_t v___x_538_; size_t v___x_539_; lean_object* v___x_540_; 
v___x_538_ = ((size_t)0ULL);
v___x_539_ = lean_usize_of_nat(v___x_535_);
v___x_540_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_522_, v_tail_529_, v___x_538_, v___x_539_, v___x_534_);
return v___x_540_;
}
}
else
{
size_t v___x_541_; size_t v___x_542_; lean_object* v___x_543_; 
v___x_541_ = ((size_t)0ULL);
v___x_542_ = lean_usize_of_nat(v___x_535_);
v___x_543_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_522_, v_tail_529_, v___x_541_, v___x_542_, v___x_534_);
return v___x_543_;
}
}
}
else
{
lean_object* v___x_544_; lean_object* v___x_545_; uint8_t v___x_546_; 
v___x_544_ = lean_nat_sub(v_start_525_, v_tailOff_531_);
v___x_545_ = lean_array_get_size(v_tail_529_);
v___x_546_ = lean_nat_dec_lt(v___x_544_, v___x_545_);
if (v___x_546_ == 0)
{
lean_dec(v___x_544_);
return v_init_524_;
}
else
{
uint8_t v___x_547_; 
v___x_547_ = lean_nat_dec_le(v___x_545_, v___x_545_);
if (v___x_547_ == 0)
{
if (v___x_546_ == 0)
{
lean_dec(v___x_544_);
return v_init_524_;
}
else
{
size_t v___x_548_; size_t v___x_549_; lean_object* v___x_550_; 
v___x_548_ = lean_usize_of_nat(v___x_544_);
lean_dec(v___x_544_);
v___x_549_ = lean_usize_of_nat(v___x_545_);
v___x_550_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_522_, v_tail_529_, v___x_548_, v___x_549_, v_init_524_);
return v___x_550_;
}
}
else
{
size_t v___x_551_; size_t v___x_552_; lean_object* v___x_553_; 
v___x_551_ = lean_usize_of_nat(v___x_544_);
lean_dec(v___x_544_);
v___x_552_ = lean_usize_of_nat(v___x_545_);
v___x_553_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_522_, v_tail_529_, v___x_551_, v___x_552_, v_init_524_);
return v___x_553_;
}
}
}
}
else
{
lean_object* v_root_554_; lean_object* v_tail_555_; lean_object* v___x_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v_root_554_ = lean_ctor_get(v_t_523_, 0);
v_tail_555_ = lean_ctor_get(v_t_523_, 1);
v___x_556_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2(v___x_522_, v_root_554_, v_init_524_);
v___x_557_ = lean_array_get_size(v_tail_555_);
v___x_558_ = lean_nat_dec_lt(v___x_526_, v___x_557_);
if (v___x_558_ == 0)
{
return v___x_556_;
}
else
{
uint8_t v___x_559_; 
v___x_559_ = lean_nat_dec_le(v___x_557_, v___x_557_);
if (v___x_559_ == 0)
{
if (v___x_558_ == 0)
{
return v___x_556_;
}
else
{
size_t v___x_560_; size_t v___x_561_; lean_object* v___x_562_; 
v___x_560_ = ((size_t)0ULL);
v___x_561_ = lean_usize_of_nat(v___x_557_);
v___x_562_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_522_, v_tail_555_, v___x_560_, v___x_561_, v___x_556_);
return v___x_562_;
}
}
else
{
size_t v___x_563_; size_t v___x_564_; lean_object* v___x_565_; 
v___x_563_ = ((size_t)0ULL);
v___x_564_ = lean_usize_of_nat(v___x_557_);
v___x_565_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_522_, v_tail_555_, v___x_563_, v___x_564_, v___x_556_);
return v___x_565_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0___boxed(lean_object* v___x_566_, lean_object* v_t_567_, lean_object* v_init_568_, lean_object* v_start_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(v___x_566_, v_t_567_, v_init_568_, v_start_569_);
lean_dec(v_start_569_);
lean_dec_ref(v_t_567_);
lean_dec_ref(v___x_566_);
return v_res_570_;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_571_ = lean_unsigned_to_nat(32u);
v___x_572_ = lean_mk_empty_array_with_capacity(v___x_571_);
v___x_573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
return v___x_573_;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1(void){
_start:
{
size_t v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_574_ = ((size_t)5ULL);
v___x_575_ = lean_unsigned_to_nat(0u);
v___x_576_ = lean_unsigned_to_nat(32u);
v___x_577_ = lean_mk_empty_array_with_capacity(v___x_576_);
v___x_578_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__0, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__0_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__0);
v___x_579_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_579_, 0, v___x_578_);
lean_ctor_set(v___x_579_, 1, v___x_577_);
lean_ctor_set(v___x_579_, 2, v___x_575_);
lean_ctor_set(v___x_579_, 3, v___x_575_);
lean_ctor_set_usize(v___x_579_, 4, v___x_574_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4(lean_object* v___x_580_, lean_object* v_x_581_, size_t v_x_582_, size_t v_x_583_){
_start:
{
if (lean_obj_tag(v_x_581_) == 0)
{
lean_object* v_cs_584_; size_t v_j_585_; lean_object* v___x_586_; lean_object* v___x_587_; uint8_t v___x_588_; 
v_cs_584_ = lean_ctor_get(v_x_581_, 0);
v_j_585_ = lean_usize_shift_right(v_x_582_, v_x_583_);
v___x_586_ = lean_usize_to_nat(v_j_585_);
v___x_587_ = lean_array_get_size(v_cs_584_);
v___x_588_ = lean_nat_dec_lt(v___x_586_, v___x_587_);
if (v___x_588_ == 0)
{
lean_dec(v___x_586_);
return v_x_581_;
}
else
{
lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_606_; 
lean_inc_ref(v_cs_584_);
v_isSharedCheck_606_ = !lean_is_exclusive(v_x_581_);
if (v_isSharedCheck_606_ == 0)
{
lean_object* v_unused_607_; 
v_unused_607_ = lean_ctor_get(v_x_581_, 0);
lean_dec(v_unused_607_);
v___x_590_ = v_x_581_;
v_isShared_591_ = v_isSharedCheck_606_;
goto v_resetjp_589_;
}
else
{
lean_dec(v_x_581_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_606_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
size_t v___x_592_; size_t v___x_593_; size_t v___x_594_; size_t v_i_595_; size_t v___x_596_; size_t v_shift_597_; lean_object* v_v_598_; lean_object* v___x_599_; lean_object* v_xs_x27_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_604_; 
v___x_592_ = ((size_t)1ULL);
v___x_593_ = lean_usize_shift_left(v___x_592_, v_x_583_);
v___x_594_ = lean_usize_sub(v___x_593_, v___x_592_);
v_i_595_ = lean_usize_land(v_x_582_, v___x_594_);
v___x_596_ = ((size_t)5ULL);
v_shift_597_ = lean_usize_sub(v_x_583_, v___x_596_);
v_v_598_ = lean_array_fget(v_cs_584_, v___x_586_);
v___x_599_ = lean_box(0);
v_xs_x27_600_ = lean_array_fset(v_cs_584_, v___x_586_, v___x_599_);
v___x_601_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4(v___x_580_, v_v_598_, v_i_595_, v_shift_597_);
v___x_602_ = lean_array_fset(v_xs_x27_600_, v___x_586_, v___x_601_);
lean_dec(v___x_586_);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 0, v___x_602_);
v___x_604_ = v___x_590_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_602_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
}
else
{
lean_object* v_vs_608_; lean_object* v___x_609_; lean_object* v___x_610_; uint8_t v___x_611_; 
v_vs_608_ = lean_ctor_get(v_x_581_, 0);
v___x_609_ = lean_usize_to_nat(v_x_582_);
v___x_610_ = lean_array_get_size(v_vs_608_);
v___x_611_ = lean_nat_dec_lt(v___x_609_, v___x_610_);
if (v___x_611_ == 0)
{
lean_dec(v___x_609_);
return v_x_581_;
}
else
{
lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_625_; 
lean_inc_ref(v_vs_608_);
v_isSharedCheck_625_ = !lean_is_exclusive(v_x_581_);
if (v_isSharedCheck_625_ == 0)
{
lean_object* v_unused_626_; 
v_unused_626_ = lean_ctor_get(v_x_581_, 0);
lean_dec(v_unused_626_);
v___x_613_ = v_x_581_;
v_isShared_614_ = v_isSharedCheck_625_;
goto v_resetjp_612_;
}
else
{
lean_dec(v_x_581_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_625_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v_v_615_; lean_object* v___x_616_; lean_object* v_xs_x27_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_623_; 
v_v_615_ = lean_array_fget(v_vs_608_, v___x_609_);
v___x_616_ = lean_box(0);
v_xs_x27_617_ = lean_array_fset(v_vs_608_, v___x_609_, v___x_616_);
v___x_618_ = lean_unsigned_to_nat(0u);
v___x_619_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1);
v___x_620_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(v___x_580_, v_v_615_, v___x_619_, v___x_618_);
lean_dec(v_v_615_);
v___x_621_ = lean_array_fset(v_xs_x27_617_, v___x_609_, v___x_620_);
lean_dec(v___x_609_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v___x_621_);
v___x_623_ = v___x_613_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v___x_621_);
v___x_623_ = v_reuseFailAlloc_624_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
return v___x_623_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___boxed(lean_object* v___x_627_, lean_object* v_x_628_, lean_object* v_x_629_, lean_object* v_x_630_){
_start:
{
size_t v_x_2238__boxed_631_; size_t v_x_2239__boxed_632_; lean_object* v_res_633_; 
v_x_2238__boxed_631_ = lean_unbox_usize(v_x_629_);
lean_dec(v_x_629_);
v_x_2239__boxed_632_ = lean_unbox_usize(v_x_630_);
lean_dec(v_x_630_);
v_res_633_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4(v___x_627_, v_x_628_, v_x_2238__boxed_631_, v_x_2239__boxed_632_);
lean_dec_ref(v___x_627_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(lean_object* v___x_634_, lean_object* v_t_635_, lean_object* v_i_636_){
_start:
{
lean_object* v_root_637_; lean_object* v_tail_638_; lean_object* v_size_639_; size_t v_shift_640_; lean_object* v_tailOff_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_669_; 
v_root_637_ = lean_ctor_get(v_t_635_, 0);
v_tail_638_ = lean_ctor_get(v_t_635_, 1);
v_size_639_ = lean_ctor_get(v_t_635_, 2);
v_shift_640_ = lean_ctor_get_usize(v_t_635_, 4);
v_tailOff_641_ = lean_ctor_get(v_t_635_, 3);
v_isSharedCheck_669_ = !lean_is_exclusive(v_t_635_);
if (v_isSharedCheck_669_ == 0)
{
v___x_643_ = v_t_635_;
v_isShared_644_ = v_isSharedCheck_669_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_tailOff_641_);
lean_inc(v_size_639_);
lean_inc(v_tail_638_);
lean_inc(v_root_637_);
lean_dec(v_t_635_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_669_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
uint8_t v___x_645_; 
v___x_645_ = lean_nat_dec_le(v_tailOff_641_, v_i_636_);
if (v___x_645_ == 0)
{
size_t v___x_646_; lean_object* v___x_647_; lean_object* v___x_649_; 
v___x_646_ = lean_usize_of_nat(v_i_636_);
v___x_647_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4(v___x_634_, v_root_637_, v___x_646_, v_shift_640_);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 0, v___x_647_);
v___x_649_ = v___x_643_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_647_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v_tail_638_);
lean_ctor_set(v_reuseFailAlloc_650_, 2, v_size_639_);
lean_ctor_set(v_reuseFailAlloc_650_, 3, v_tailOff_641_);
lean_ctor_set_usize(v_reuseFailAlloc_650_, 4, v_shift_640_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
else
{
lean_object* v___x_651_; lean_object* v___x_652_; uint8_t v___x_653_; 
v___x_651_ = lean_nat_sub(v_i_636_, v_tailOff_641_);
v___x_652_ = lean_array_get_size(v_tail_638_);
v___x_653_ = lean_nat_dec_lt(v___x_651_, v___x_652_);
if (v___x_653_ == 0)
{
lean_object* v___x_655_; 
lean_dec(v___x_651_);
if (v_isShared_644_ == 0)
{
v___x_655_ = v___x_643_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v_root_637_);
lean_ctor_set(v_reuseFailAlloc_656_, 1, v_tail_638_);
lean_ctor_set(v_reuseFailAlloc_656_, 2, v_size_639_);
lean_ctor_set(v_reuseFailAlloc_656_, 3, v_tailOff_641_);
lean_ctor_set_usize(v_reuseFailAlloc_656_, 4, v_shift_640_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
else
{
lean_object* v_v_657_; lean_object* v___x_658_; lean_object* v_xs_x27_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_667_; 
v_v_657_ = lean_array_fget(v_tail_638_, v___x_651_);
v___x_658_ = lean_box(0);
v_xs_x27_659_ = lean_array_fset(v_tail_638_, v___x_651_, v___x_658_);
v___x_660_ = lean_unsigned_to_nat(32u);
v___x_661_ = lean_mk_empty_array_with_capacity(v___x_660_);
lean_dec_ref(v___x_661_);
v___x_662_ = lean_unsigned_to_nat(0u);
v___x_663_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1);
v___x_664_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(v___x_634_, v_v_657_, v___x_663_, v___x_662_);
lean_dec(v_v_657_);
v___x_665_ = lean_array_fset(v_xs_x27_659_, v___x_651_, v___x_664_);
lean_dec(v___x_651_);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 1, v___x_665_);
v___x_667_ = v___x_643_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_root_637_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v___x_665_);
lean_ctor_set(v_reuseFailAlloc_668_, 2, v_size_639_);
lean_ctor_set(v_reuseFailAlloc_668_, 3, v_tailOff_641_);
lean_ctor_set_usize(v_reuseFailAlloc_668_, 4, v_shift_640_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1___boxed(lean_object* v___x_670_, lean_object* v_t_671_, lean_object* v_i_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(v___x_670_, v_t_671_, v_i_672_);
lean_dec(v_i_672_);
lean_dec_ref(v___x_670_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0(lean_object* v_p_674_, lean_object* v_v_675_, lean_object* v_s_676_){
_start:
{
lean_object* v_vars_677_; lean_object* v_varMap_678_; lean_object* v_vars_x27_679_; lean_object* v_varMap_x27_680_; lean_object* v_natToIntMap_681_; lean_object* v_natDef_682_; lean_object* v_dvds_683_; lean_object* v_lowers_684_; lean_object* v_uppers_685_; lean_object* v_diseqs_686_; lean_object* v_elimEqs_687_; lean_object* v_elimStack_688_; lean_object* v_occurs_689_; lean_object* v_assignment_690_; lean_object* v_nextCnstrId_691_; uint8_t v_caseSplits_692_; lean_object* v_conflict_x3f_693_; lean_object* v_diseqSplits_694_; lean_object* v_divMod_695_; lean_object* v_toIntIds_696_; lean_object* v_toIntInfos_697_; lean_object* v_toIntTermMap_698_; lean_object* v_toIntVarMap_699_; uint8_t v_usedCommRing_700_; lean_object* v_nonlinearOccs_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_709_; 
v_vars_677_ = lean_ctor_get(v_s_676_, 0);
v_varMap_678_ = lean_ctor_get(v_s_676_, 1);
v_vars_x27_679_ = lean_ctor_get(v_s_676_, 2);
v_varMap_x27_680_ = lean_ctor_get(v_s_676_, 3);
v_natToIntMap_681_ = lean_ctor_get(v_s_676_, 4);
v_natDef_682_ = lean_ctor_get(v_s_676_, 5);
v_dvds_683_ = lean_ctor_get(v_s_676_, 6);
v_lowers_684_ = lean_ctor_get(v_s_676_, 7);
v_uppers_685_ = lean_ctor_get(v_s_676_, 8);
v_diseqs_686_ = lean_ctor_get(v_s_676_, 9);
v_elimEqs_687_ = lean_ctor_get(v_s_676_, 10);
v_elimStack_688_ = lean_ctor_get(v_s_676_, 11);
v_occurs_689_ = lean_ctor_get(v_s_676_, 12);
v_assignment_690_ = lean_ctor_get(v_s_676_, 13);
v_nextCnstrId_691_ = lean_ctor_get(v_s_676_, 14);
v_caseSplits_692_ = lean_ctor_get_uint8(v_s_676_, sizeof(void*)*23);
v_conflict_x3f_693_ = lean_ctor_get(v_s_676_, 15);
v_diseqSplits_694_ = lean_ctor_get(v_s_676_, 16);
v_divMod_695_ = lean_ctor_get(v_s_676_, 17);
v_toIntIds_696_ = lean_ctor_get(v_s_676_, 18);
v_toIntInfos_697_ = lean_ctor_get(v_s_676_, 19);
v_toIntTermMap_698_ = lean_ctor_get(v_s_676_, 20);
v_toIntVarMap_699_ = lean_ctor_get(v_s_676_, 21);
v_usedCommRing_700_ = lean_ctor_get_uint8(v_s_676_, sizeof(void*)*23 + 1);
v_nonlinearOccs_701_ = lean_ctor_get(v_s_676_, 22);
v_isSharedCheck_709_ = !lean_is_exclusive(v_s_676_);
if (v_isSharedCheck_709_ == 0)
{
v___x_703_ = v_s_676_;
v_isShared_704_ = v_isSharedCheck_709_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_nonlinearOccs_701_);
lean_inc(v_toIntVarMap_699_);
lean_inc(v_toIntTermMap_698_);
lean_inc(v_toIntInfos_697_);
lean_inc(v_toIntIds_696_);
lean_inc(v_divMod_695_);
lean_inc(v_diseqSplits_694_);
lean_inc(v_conflict_x3f_693_);
lean_inc(v_nextCnstrId_691_);
lean_inc(v_assignment_690_);
lean_inc(v_occurs_689_);
lean_inc(v_elimStack_688_);
lean_inc(v_elimEqs_687_);
lean_inc(v_diseqs_686_);
lean_inc(v_uppers_685_);
lean_inc(v_lowers_684_);
lean_inc(v_dvds_683_);
lean_inc(v_natDef_682_);
lean_inc(v_natToIntMap_681_);
lean_inc(v_varMap_x27_680_);
lean_inc(v_vars_x27_679_);
lean_inc(v_varMap_678_);
lean_inc(v_vars_677_);
lean_dec(v_s_676_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_709_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v___x_705_; lean_object* v___x_707_; 
v___x_705_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(v_p_674_, v_uppers_685_, v_v_675_);
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 8, v___x_705_);
v___x_707_ = v___x_703_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_vars_677_);
lean_ctor_set(v_reuseFailAlloc_708_, 1, v_varMap_678_);
lean_ctor_set(v_reuseFailAlloc_708_, 2, v_vars_x27_679_);
lean_ctor_set(v_reuseFailAlloc_708_, 3, v_varMap_x27_680_);
lean_ctor_set(v_reuseFailAlloc_708_, 4, v_natToIntMap_681_);
lean_ctor_set(v_reuseFailAlloc_708_, 5, v_natDef_682_);
lean_ctor_set(v_reuseFailAlloc_708_, 6, v_dvds_683_);
lean_ctor_set(v_reuseFailAlloc_708_, 7, v_lowers_684_);
lean_ctor_set(v_reuseFailAlloc_708_, 8, v___x_705_);
lean_ctor_set(v_reuseFailAlloc_708_, 9, v_diseqs_686_);
lean_ctor_set(v_reuseFailAlloc_708_, 10, v_elimEqs_687_);
lean_ctor_set(v_reuseFailAlloc_708_, 11, v_elimStack_688_);
lean_ctor_set(v_reuseFailAlloc_708_, 12, v_occurs_689_);
lean_ctor_set(v_reuseFailAlloc_708_, 13, v_assignment_690_);
lean_ctor_set(v_reuseFailAlloc_708_, 14, v_nextCnstrId_691_);
lean_ctor_set(v_reuseFailAlloc_708_, 15, v_conflict_x3f_693_);
lean_ctor_set(v_reuseFailAlloc_708_, 16, v_diseqSplits_694_);
lean_ctor_set(v_reuseFailAlloc_708_, 17, v_divMod_695_);
lean_ctor_set(v_reuseFailAlloc_708_, 18, v_toIntIds_696_);
lean_ctor_set(v_reuseFailAlloc_708_, 19, v_toIntInfos_697_);
lean_ctor_set(v_reuseFailAlloc_708_, 20, v_toIntTermMap_698_);
lean_ctor_set(v_reuseFailAlloc_708_, 21, v_toIntVarMap_699_);
lean_ctor_set(v_reuseFailAlloc_708_, 22, v_nonlinearOccs_701_);
lean_ctor_set_uint8(v_reuseFailAlloc_708_, sizeof(void*)*23, v_caseSplits_692_);
lean_ctor_set_uint8(v_reuseFailAlloc_708_, sizeof(void*)*23 + 1, v_usedCommRing_700_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___boxed(lean_object* v_p_710_, lean_object* v_v_711_, lean_object* v_s_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0(v_p_710_, v_v_711_, v_s_712_);
lean_dec(v_v_711_);
lean_dec_ref(v_p_710_);
return v_res_713_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1(lean_object* v_p_714_, lean_object* v_v_715_, lean_object* v_s_716_){
_start:
{
lean_object* v_vars_717_; lean_object* v_varMap_718_; lean_object* v_vars_x27_719_; lean_object* v_varMap_x27_720_; lean_object* v_natToIntMap_721_; lean_object* v_natDef_722_; lean_object* v_dvds_723_; lean_object* v_lowers_724_; lean_object* v_uppers_725_; lean_object* v_diseqs_726_; lean_object* v_elimEqs_727_; lean_object* v_elimStack_728_; lean_object* v_occurs_729_; lean_object* v_assignment_730_; lean_object* v_nextCnstrId_731_; uint8_t v_caseSplits_732_; lean_object* v_conflict_x3f_733_; lean_object* v_diseqSplits_734_; lean_object* v_divMod_735_; lean_object* v_toIntIds_736_; lean_object* v_toIntInfos_737_; lean_object* v_toIntTermMap_738_; lean_object* v_toIntVarMap_739_; uint8_t v_usedCommRing_740_; lean_object* v_nonlinearOccs_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_749_; 
v_vars_717_ = lean_ctor_get(v_s_716_, 0);
v_varMap_718_ = lean_ctor_get(v_s_716_, 1);
v_vars_x27_719_ = lean_ctor_get(v_s_716_, 2);
v_varMap_x27_720_ = lean_ctor_get(v_s_716_, 3);
v_natToIntMap_721_ = lean_ctor_get(v_s_716_, 4);
v_natDef_722_ = lean_ctor_get(v_s_716_, 5);
v_dvds_723_ = lean_ctor_get(v_s_716_, 6);
v_lowers_724_ = lean_ctor_get(v_s_716_, 7);
v_uppers_725_ = lean_ctor_get(v_s_716_, 8);
v_diseqs_726_ = lean_ctor_get(v_s_716_, 9);
v_elimEqs_727_ = lean_ctor_get(v_s_716_, 10);
v_elimStack_728_ = lean_ctor_get(v_s_716_, 11);
v_occurs_729_ = lean_ctor_get(v_s_716_, 12);
v_assignment_730_ = lean_ctor_get(v_s_716_, 13);
v_nextCnstrId_731_ = lean_ctor_get(v_s_716_, 14);
v_caseSplits_732_ = lean_ctor_get_uint8(v_s_716_, sizeof(void*)*23);
v_conflict_x3f_733_ = lean_ctor_get(v_s_716_, 15);
v_diseqSplits_734_ = lean_ctor_get(v_s_716_, 16);
v_divMod_735_ = lean_ctor_get(v_s_716_, 17);
v_toIntIds_736_ = lean_ctor_get(v_s_716_, 18);
v_toIntInfos_737_ = lean_ctor_get(v_s_716_, 19);
v_toIntTermMap_738_ = lean_ctor_get(v_s_716_, 20);
v_toIntVarMap_739_ = lean_ctor_get(v_s_716_, 21);
v_usedCommRing_740_ = lean_ctor_get_uint8(v_s_716_, sizeof(void*)*23 + 1);
v_nonlinearOccs_741_ = lean_ctor_get(v_s_716_, 22);
v_isSharedCheck_749_ = !lean_is_exclusive(v_s_716_);
if (v_isSharedCheck_749_ == 0)
{
v___x_743_ = v_s_716_;
v_isShared_744_ = v_isSharedCheck_749_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_nonlinearOccs_741_);
lean_inc(v_toIntVarMap_739_);
lean_inc(v_toIntTermMap_738_);
lean_inc(v_toIntInfos_737_);
lean_inc(v_toIntIds_736_);
lean_inc(v_divMod_735_);
lean_inc(v_diseqSplits_734_);
lean_inc(v_conflict_x3f_733_);
lean_inc(v_nextCnstrId_731_);
lean_inc(v_assignment_730_);
lean_inc(v_occurs_729_);
lean_inc(v_elimStack_728_);
lean_inc(v_elimEqs_727_);
lean_inc(v_diseqs_726_);
lean_inc(v_uppers_725_);
lean_inc(v_lowers_724_);
lean_inc(v_dvds_723_);
lean_inc(v_natDef_722_);
lean_inc(v_natToIntMap_721_);
lean_inc(v_varMap_x27_720_);
lean_inc(v_vars_x27_719_);
lean_inc(v_varMap_718_);
lean_inc(v_vars_717_);
lean_dec(v_s_716_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_749_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_745_; lean_object* v___x_747_; 
v___x_745_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(v_p_714_, v_lowers_724_, v_v_715_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 7, v___x_745_);
v___x_747_ = v___x_743_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_vars_717_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v_varMap_718_);
lean_ctor_set(v_reuseFailAlloc_748_, 2, v_vars_x27_719_);
lean_ctor_set(v_reuseFailAlloc_748_, 3, v_varMap_x27_720_);
lean_ctor_set(v_reuseFailAlloc_748_, 4, v_natToIntMap_721_);
lean_ctor_set(v_reuseFailAlloc_748_, 5, v_natDef_722_);
lean_ctor_set(v_reuseFailAlloc_748_, 6, v_dvds_723_);
lean_ctor_set(v_reuseFailAlloc_748_, 7, v___x_745_);
lean_ctor_set(v_reuseFailAlloc_748_, 8, v_uppers_725_);
lean_ctor_set(v_reuseFailAlloc_748_, 9, v_diseqs_726_);
lean_ctor_set(v_reuseFailAlloc_748_, 10, v_elimEqs_727_);
lean_ctor_set(v_reuseFailAlloc_748_, 11, v_elimStack_728_);
lean_ctor_set(v_reuseFailAlloc_748_, 12, v_occurs_729_);
lean_ctor_set(v_reuseFailAlloc_748_, 13, v_assignment_730_);
lean_ctor_set(v_reuseFailAlloc_748_, 14, v_nextCnstrId_731_);
lean_ctor_set(v_reuseFailAlloc_748_, 15, v_conflict_x3f_733_);
lean_ctor_set(v_reuseFailAlloc_748_, 16, v_diseqSplits_734_);
lean_ctor_set(v_reuseFailAlloc_748_, 17, v_divMod_735_);
lean_ctor_set(v_reuseFailAlloc_748_, 18, v_toIntIds_736_);
lean_ctor_set(v_reuseFailAlloc_748_, 19, v_toIntInfos_737_);
lean_ctor_set(v_reuseFailAlloc_748_, 20, v_toIntTermMap_738_);
lean_ctor_set(v_reuseFailAlloc_748_, 21, v_toIntVarMap_739_);
lean_ctor_set(v_reuseFailAlloc_748_, 22, v_nonlinearOccs_741_);
lean_ctor_set_uint8(v_reuseFailAlloc_748_, sizeof(void*)*23, v_caseSplits_732_);
lean_ctor_set_uint8(v_reuseFailAlloc_748_, sizeof(void*)*23 + 1, v_usedCommRing_740_);
v___x_747_ = v_reuseFailAlloc_748_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
return v___x_747_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1___boxed(lean_object* v_p_750_, lean_object* v_v_751_, lean_object* v_s_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1(v_p_750_, v_v_751_, v_s_752_);
lean_dec(v_v_751_);
lean_dec_ref(v_p_750_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(lean_object* v_c_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_){
_start:
{
lean_object* v_p_761_; 
v_p_761_ = lean_ctor_get(v_c_754_, 0);
if (lean_obj_tag(v_p_761_) == 1)
{
lean_object* v_k_762_; lean_object* v_v_763_; lean_object* v___x_764_; uint8_t v___x_765_; 
lean_inc_ref(v_p_761_);
lean_dec_ref(v_c_754_);
v_k_762_ = lean_ctor_get(v_p_761_, 0);
v_v_763_ = lean_ctor_get(v_p_761_, 1);
lean_inc(v_v_763_);
v___x_764_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9);
v___x_765_ = lean_int_dec_lt(v_k_762_, v___x_764_);
if (v___x_765_ == 0)
{
lean_object* v___f_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___f_766_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_766_, 0, v_p_761_);
lean_closure_set(v___f_766_, 1, v_v_763_);
v___x_767_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_768_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_767_, v___f_766_, v_a_755_);
return v___x_768_;
}
else
{
lean_object* v___f_769_; lean_object* v___x_770_; lean_object* v___x_771_; 
v___f_769_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_769_, 0, v_p_761_);
lean_closure_set(v___f_769_, 1, v_v_763_);
v___x_770_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_771_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_770_, v___f_769_, v_a_755_);
return v___x_771_;
}
}
else
{
lean_object* v___x_772_; 
v___x_772_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_);
return v___x_772_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___boxed(lean_object* v_c_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_){
_start:
{
lean_object* v_res_780_; 
v_res_780_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_c_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_);
lean_dec(v_a_778_);
lean_dec_ref(v_a_777_);
lean_dec(v_a_776_);
lean_dec_ref(v_a_775_);
lean_dec(v_a_774_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase(lean_object* v_c_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_){
_start:
{
lean_object* v___x_793_; 
v___x_793_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_c_781_, v_a_782_, v_a_788_, v_a_789_, v_a_790_, v_a_791_);
return v___x_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___boxed(lean_object* v_c_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase(v_c_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
lean_dec(v_a_800_);
lean_dec_ref(v_a_799_);
lean_dec(v_a_798_);
lean_dec_ref(v_a_797_);
lean_dec(v_a_796_);
lean_dec(v_a_795_);
return v_res_806_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5(void){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_820_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_821_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_822_ = l_Lean_Name_append(v___x_821_, v___x_820_);
return v___x_822_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7(void){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_824_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__6));
v___x_825_ = l_Lean_stringToMessageData(v___x_824_);
return v___x_825_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3(lean_object* v___x_826_, lean_object* v_c_827_, lean_object* v_as_828_, size_t v_sz_829_, size_t v_i_830_, lean_object* v_b_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_){
_start:
{
uint8_t v___x_843_; 
v___x_843_ = lean_usize_dec_lt(v_i_830_, v_sz_829_);
if (v___x_843_ == 0)
{
lean_object* v___x_844_; 
lean_dec_ref(v_c_827_);
lean_dec_ref(v___x_826_);
v___x_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_844_, 0, v_b_831_);
return v___x_844_;
}
else
{
lean_object* v_snd_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_931_; 
v_snd_845_ = lean_ctor_get(v_b_831_, 1);
v_isSharedCheck_931_ = !lean_is_exclusive(v_b_831_);
if (v_isSharedCheck_931_ == 0)
{
lean_object* v_unused_932_; 
v_unused_932_ = lean_ctor_get(v_b_831_, 0);
lean_dec(v_unused_932_);
v___x_847_ = v_b_831_;
v_isShared_848_ = v_isSharedCheck_931_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_snd_845_);
lean_dec(v_b_831_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_931_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v_a_849_; lean_object* v_p_850_; lean_object* v___x_851_; uint8_t v___x_852_; 
v_a_849_ = lean_array_uget_borrowed(v_as_828_, v_i_830_);
v_p_850_ = lean_ctor_get(v_a_849_, 0);
v___x_851_ = lean_box(0);
v___x_852_ = l_Int_Linear_Poly_isNegEq(v___x_826_, v_p_850_);
if (v___x_852_ == 0)
{
lean_object* v___x_853_; size_t v___x_854_; size_t v___x_855_; 
lean_del_object(v___x_847_);
lean_dec(v_snd_845_);
v___x_853_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__1));
v___x_854_ = ((size_t)1ULL);
v___x_855_ = lean_usize_add(v_i_830_, v___x_854_);
v_i_830_ = v___x_855_;
v_b_831_ = v___x_853_;
goto _start;
}
else
{
lean_object* v___x_857_; 
lean_inc(v_a_849_);
v___x_857_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_849_, v___y_832_, v___y_838_, v___y_839_, v___y_840_, v___y_841_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_options_858_; lean_object* v_inheritedTraceOptions_859_; uint8_t v_hasTrace_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___y_864_; lean_object* v___y_865_; lean_object* v___y_866_; lean_object* v___y_867_; lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___y_872_; lean_object* v___y_873_; 
lean_dec_ref(v___x_857_);
v_options_858_ = lean_ctor_get(v___y_840_, 2);
v_inheritedTraceOptions_859_ = lean_ctor_get(v___y_840_, 13);
v_hasTrace_860_ = lean_ctor_get_uint8(v_options_858_, sizeof(void*)*1);
lean_inc(v_a_849_);
v___x_861_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_861_, 0, v_c_827_);
lean_ctor_set(v___x_861_, 1, v_a_849_);
v___x_862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_862_, 0, v___x_826_);
lean_ctor_set(v___x_862_, 1, v___x_861_);
if (v_hasTrace_860_ == 0)
{
v___y_864_ = v___y_832_;
v___y_865_ = v___y_833_;
v___y_866_ = v___y_834_;
v___y_867_ = v___y_835_;
v___y_868_ = v___y_836_;
v___y_869_ = v___y_837_;
v___y_870_ = v___y_838_;
v___y_871_ = v___y_839_;
v___y_872_ = v___y_840_;
v___y_873_ = v___y_841_;
goto v___jp_863_;
}
else
{
lean_object* v___x_899_; lean_object* v___x_900_; uint8_t v___x_901_; 
v___x_899_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_900_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5);
v___x_901_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_859_, v_options_858_, v___x_900_);
if (v___x_901_ == 0)
{
v___y_864_ = v___y_832_;
v___y_865_ = v___y_833_;
v___y_866_ = v___y_834_;
v___y_867_ = v___y_835_;
v___y_868_ = v___y_836_;
v___y_869_ = v___y_837_;
v___y_870_ = v___y_838_;
v___y_871_ = v___y_839_;
v___y_872_ = v___y_840_;
v___y_873_ = v___y_841_;
goto v___jp_863_;
}
else
{
lean_object* v___x_902_; 
lean_inc_ref(v___x_862_);
v___x_902_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_862_, v___y_832_, v___y_840_);
if (lean_obj_tag(v___x_902_) == 0)
{
lean_object* v_a_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v_a_903_ = lean_ctor_get(v___x_902_, 0);
lean_inc(v_a_903_);
lean_dec_ref(v___x_902_);
v___x_904_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7);
v___x_905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
lean_ctor_set(v___x_905_, 1, v_a_903_);
v___x_906_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_899_, v___x_905_, v___y_838_, v___y_839_, v___y_840_, v___y_841_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_dec_ref(v___x_906_);
v___y_864_ = v___y_832_;
v___y_865_ = v___y_833_;
v___y_866_ = v___y_834_;
v___y_867_ = v___y_835_;
v___y_868_ = v___y_836_;
v___y_869_ = v___y_837_;
v___y_870_ = v___y_838_;
v___y_871_ = v___y_839_;
v___y_872_ = v___y_840_;
v___y_873_ = v___y_841_;
goto v___jp_863_;
}
else
{
lean_object* v_a_907_; lean_object* v___x_909_; uint8_t v_isShared_910_; uint8_t v_isSharedCheck_914_; 
lean_dec_ref(v___x_862_);
lean_del_object(v___x_847_);
lean_dec(v_snd_845_);
v_a_907_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_914_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_914_ == 0)
{
v___x_909_ = v___x_906_;
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
else
{
lean_inc(v_a_907_);
lean_dec(v___x_906_);
v___x_909_ = lean_box(0);
v_isShared_910_ = v_isSharedCheck_914_;
goto v_resetjp_908_;
}
v_resetjp_908_:
{
lean_object* v___x_912_; 
if (v_isShared_910_ == 0)
{
v___x_912_ = v___x_909_;
goto v_reusejp_911_;
}
else
{
lean_object* v_reuseFailAlloc_913_; 
v_reuseFailAlloc_913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_913_, 0, v_a_907_);
v___x_912_ = v_reuseFailAlloc_913_;
goto v_reusejp_911_;
}
v_reusejp_911_:
{
return v___x_912_;
}
}
}
}
else
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
lean_dec_ref(v___x_862_);
lean_del_object(v___x_847_);
lean_dec(v_snd_845_);
v_a_915_ = lean_ctor_get(v___x_902_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_902_);
if (v_isSharedCheck_922_ == 0)
{
v___x_917_ = v___x_902_;
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_902_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_915_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
}
v___jp_863_:
{
lean_object* v___x_874_; 
lean_inc(v___y_873_);
lean_inc_ref(v___y_872_);
lean_inc(v___y_871_);
lean_inc_ref(v___y_870_);
lean_inc(v___y_869_);
lean_inc_ref(v___y_868_);
lean_inc(v___y_867_);
lean_inc_ref(v___y_866_);
lean_inc(v___y_865_);
lean_inc(v___y_864_);
v___x_874_ = lean_grind_cutsat_assert_eq(v___x_862_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_889_; 
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_889_ == 0)
{
lean_object* v_unused_890_; 
v_unused_890_ = lean_ctor_get(v___x_874_, 0);
lean_dec(v_unused_890_);
v___x_876_ = v___x_874_;
v_isShared_877_ = v_isSharedCheck_889_;
goto v_resetjp_875_;
}
else
{
lean_dec(v___x_874_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_889_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_881_; 
v___x_878_ = lean_box(v___x_852_);
v___x_879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 1, v___x_851_);
lean_ctor_set(v___x_847_, 0, v___x_879_);
v___x_881_ = v___x_847_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_879_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v___x_851_);
v___x_881_ = v_reuseFailAlloc_888_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_886_; 
v___x_882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
v___x_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_883_, 0, v___x_882_);
v___x_884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_884_, 0, v___x_883_);
lean_ctor_set(v___x_884_, 1, v_snd_845_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 0, v___x_884_);
v___x_886_ = v___x_876_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_884_);
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
else
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_898_; 
lean_del_object(v___x_847_);
lean_dec(v_snd_845_);
v_a_891_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_898_ == 0)
{
v___x_893_ = v___x_874_;
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v___x_874_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_896_; 
if (v_isShared_894_ == 0)
{
v___x_896_ = v___x_893_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_a_891_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
}
else
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_930_; 
lean_del_object(v___x_847_);
lean_dec(v_snd_845_);
lean_dec_ref(v_c_827_);
lean_dec_ref(v___x_826_);
v_a_923_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_930_ == 0)
{
v___x_925_ = v___x_857_;
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_857_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
v___x_928_ = v___x_925_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_923_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___boxed(lean_object** _args){
lean_object* v___x_933_ = _args[0];
lean_object* v_c_934_ = _args[1];
lean_object* v_as_935_ = _args[2];
lean_object* v_sz_936_ = _args[3];
lean_object* v_i_937_ = _args[4];
lean_object* v_b_938_ = _args[5];
lean_object* v___y_939_ = _args[6];
lean_object* v___y_940_ = _args[7];
lean_object* v___y_941_ = _args[8];
lean_object* v___y_942_ = _args[9];
lean_object* v___y_943_ = _args[10];
lean_object* v___y_944_ = _args[11];
lean_object* v___y_945_ = _args[12];
lean_object* v___y_946_ = _args[13];
lean_object* v___y_947_ = _args[14];
lean_object* v___y_948_ = _args[15];
lean_object* v___y_949_ = _args[16];
_start:
{
size_t v_sz_boxed_950_; size_t v_i_boxed_951_; lean_object* v_res_952_; 
v_sz_boxed_950_ = lean_unbox_usize(v_sz_936_);
lean_dec(v_sz_936_);
v_i_boxed_951_ = lean_unbox_usize(v_i_937_);
lean_dec(v_i_937_);
v_res_952_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3(v___x_933_, v_c_934_, v_as_935_, v_sz_boxed_950_, v_i_boxed_951_, v_b_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec(v___y_944_);
lean_dec_ref(v___y_943_);
lean_dec(v___y_942_);
lean_dec_ref(v___y_941_);
lean_dec(v___y_940_);
lean_dec(v___y_939_);
lean_dec_ref(v_as_935_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2(lean_object* v___x_959_, lean_object* v_c_960_, lean_object* v_as_961_, size_t v_sz_962_, size_t v_i_963_, lean_object* v_b_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
uint8_t v___x_976_; 
v___x_976_ = lean_usize_dec_lt(v_i_963_, v_sz_962_);
if (v___x_976_ == 0)
{
lean_object* v___x_977_; 
lean_dec_ref(v_c_960_);
lean_dec_ref(v___x_959_);
v___x_977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_977_, 0, v_b_964_);
return v___x_977_;
}
else
{
lean_object* v_snd_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_1064_; 
v_snd_978_ = lean_ctor_get(v_b_964_, 1);
v_isSharedCheck_1064_ = !lean_is_exclusive(v_b_964_);
if (v_isSharedCheck_1064_ == 0)
{
lean_object* v_unused_1065_; 
v_unused_1065_ = lean_ctor_get(v_b_964_, 0);
lean_dec(v_unused_1065_);
v___x_980_ = v_b_964_;
v_isShared_981_ = v_isSharedCheck_1064_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_snd_978_);
lean_dec(v_b_964_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_1064_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v_a_982_; lean_object* v_p_983_; lean_object* v___x_984_; uint8_t v___x_985_; 
v_a_982_ = lean_array_uget_borrowed(v_as_961_, v_i_963_);
v_p_983_ = lean_ctor_get(v_a_982_, 0);
v___x_984_ = lean_box(0);
v___x_985_ = l_Int_Linear_Poly_isNegEq(v___x_959_, v_p_983_);
if (v___x_985_ == 0)
{
lean_object* v___x_986_; size_t v___x_987_; size_t v___x_988_; lean_object* v___x_989_; 
lean_del_object(v___x_980_);
lean_dec(v_snd_978_);
v___x_986_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__1));
v___x_987_ = ((size_t)1ULL);
v___x_988_ = lean_usize_add(v_i_963_, v___x_987_);
v___x_989_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3(v___x_959_, v_c_960_, v_as_961_, v_sz_962_, v___x_988_, v___x_986_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
return v___x_989_;
}
else
{
lean_object* v___x_990_; 
lean_inc(v_a_982_);
v___x_990_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_982_, v___y_965_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v_options_991_; lean_object* v_inheritedTraceOptions_992_; uint8_t v_hasTrace_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___y_997_; lean_object* v___y_998_; lean_object* v___y_999_; lean_object* v___y_1000_; lean_object* v___y_1001_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v___y_1006_; 
lean_dec_ref(v___x_990_);
v_options_991_ = lean_ctor_get(v___y_973_, 2);
v_inheritedTraceOptions_992_ = lean_ctor_get(v___y_973_, 13);
v_hasTrace_993_ = lean_ctor_get_uint8(v_options_991_, sizeof(void*)*1);
lean_inc(v_a_982_);
v___x_994_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_994_, 0, v_c_960_);
lean_ctor_set(v___x_994_, 1, v_a_982_);
v___x_995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_959_);
lean_ctor_set(v___x_995_, 1, v___x_994_);
if (v_hasTrace_993_ == 0)
{
v___y_997_ = v___y_965_;
v___y_998_ = v___y_966_;
v___y_999_ = v___y_967_;
v___y_1000_ = v___y_968_;
v___y_1001_ = v___y_969_;
v___y_1002_ = v___y_970_;
v___y_1003_ = v___y_971_;
v___y_1004_ = v___y_972_;
v___y_1005_ = v___y_973_;
v___y_1006_ = v___y_974_;
goto v___jp_996_;
}
else
{
lean_object* v___x_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; 
v___x_1032_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_1033_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5);
v___x_1034_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_992_, v_options_991_, v___x_1033_);
if (v___x_1034_ == 0)
{
v___y_997_ = v___y_965_;
v___y_998_ = v___y_966_;
v___y_999_ = v___y_967_;
v___y_1000_ = v___y_968_;
v___y_1001_ = v___y_969_;
v___y_1002_ = v___y_970_;
v___y_1003_ = v___y_971_;
v___y_1004_ = v___y_972_;
v___y_1005_ = v___y_973_;
v___y_1006_ = v___y_974_;
goto v___jp_996_;
}
else
{
lean_object* v___x_1035_; 
lean_inc_ref(v___x_995_);
v___x_1035_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_995_, v___y_965_, v___y_973_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v_a_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v_a_1036_ = lean_ctor_get(v___x_1035_, 0);
lean_inc(v_a_1036_);
lean_dec_ref(v___x_1035_);
v___x_1037_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7);
v___x_1038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1037_);
lean_ctor_set(v___x_1038_, 1, v_a_1036_);
v___x_1039_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_1032_, v___x_1038_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_dec_ref(v___x_1039_);
v___y_997_ = v___y_965_;
v___y_998_ = v___y_966_;
v___y_999_ = v___y_967_;
v___y_1000_ = v___y_968_;
v___y_1001_ = v___y_969_;
v___y_1002_ = v___y_970_;
v___y_1003_ = v___y_971_;
v___y_1004_ = v___y_972_;
v___y_1005_ = v___y_973_;
v___y_1006_ = v___y_974_;
goto v___jp_996_;
}
else
{
lean_object* v_a_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1047_; 
lean_dec_ref(v___x_995_);
lean_del_object(v___x_980_);
lean_dec(v_snd_978_);
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1047_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1042_ = v___x_1039_;
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_a_1040_);
lean_dec(v___x_1039_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1047_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1045_; 
if (v_isShared_1043_ == 0)
{
v___x_1045_ = v___x_1042_;
goto v_reusejp_1044_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_a_1040_);
v___x_1045_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1044_;
}
v_reusejp_1044_:
{
return v___x_1045_;
}
}
}
}
else
{
lean_object* v_a_1048_; lean_object* v___x_1050_; uint8_t v_isShared_1051_; uint8_t v_isSharedCheck_1055_; 
lean_dec_ref(v___x_995_);
lean_del_object(v___x_980_);
lean_dec(v_snd_978_);
v_a_1048_ = lean_ctor_get(v___x_1035_, 0);
v_isSharedCheck_1055_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1055_ == 0)
{
v___x_1050_ = v___x_1035_;
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
else
{
lean_inc(v_a_1048_);
lean_dec(v___x_1035_);
v___x_1050_ = lean_box(0);
v_isShared_1051_ = v_isSharedCheck_1055_;
goto v_resetjp_1049_;
}
v_resetjp_1049_:
{
lean_object* v___x_1053_; 
if (v_isShared_1051_ == 0)
{
v___x_1053_ = v___x_1050_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1054_; 
v_reuseFailAlloc_1054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1054_, 0, v_a_1048_);
v___x_1053_ = v_reuseFailAlloc_1054_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
return v___x_1053_;
}
}
}
}
}
v___jp_996_:
{
lean_object* v___x_1007_; 
lean_inc(v___y_1006_);
lean_inc_ref(v___y_1005_);
lean_inc(v___y_1004_);
lean_inc_ref(v___y_1003_);
lean_inc(v___y_1002_);
lean_inc_ref(v___y_1001_);
lean_inc(v___y_1000_);
lean_inc_ref(v___y_999_);
lean_inc(v___y_998_);
lean_inc(v___y_997_);
v___x_1007_ = lean_grind_cutsat_assert_eq(v___x_995_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1022_; 
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1022_ == 0)
{
lean_object* v_unused_1023_; 
v_unused_1023_ = lean_ctor_get(v___x_1007_, 0);
lean_dec(v_unused_1023_);
v___x_1009_ = v___x_1007_;
v_isShared_1010_ = v_isSharedCheck_1022_;
goto v_resetjp_1008_;
}
else
{
lean_dec(v___x_1007_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1022_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1014_; 
v___x_1011_ = lean_box(v___x_985_);
v___x_1012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
if (v_isShared_981_ == 0)
{
lean_ctor_set(v___x_980_, 1, v___x_984_);
lean_ctor_set(v___x_980_, 0, v___x_1012_);
v___x_1014_ = v___x_980_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_1012_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v___x_984_);
v___x_1014_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1019_; 
v___x_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1015_, 0, v___x_1014_);
v___x_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
v___x_1017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1017_, 0, v___x_1016_);
lean_ctor_set(v___x_1017_, 1, v_snd_978_);
if (v_isShared_1010_ == 0)
{
lean_ctor_set(v___x_1009_, 0, v___x_1017_);
v___x_1019_ = v___x_1009_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v___x_1017_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
lean_del_object(v___x_980_);
lean_dec(v_snd_978_);
v_a_1024_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_1007_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_1007_);
v___x_1026_ = lean_box(0);
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
v_resetjp_1025_:
{
lean_object* v___x_1029_; 
if (v_isShared_1027_ == 0)
{
v___x_1029_ = v___x_1026_;
goto v_reusejp_1028_;
}
else
{
lean_object* v_reuseFailAlloc_1030_; 
v_reuseFailAlloc_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1030_, 0, v_a_1024_);
v___x_1029_ = v_reuseFailAlloc_1030_;
goto v_reusejp_1028_;
}
v_reusejp_1028_:
{
return v___x_1029_;
}
}
}
}
}
else
{
lean_object* v_a_1056_; lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1063_; 
lean_del_object(v___x_980_);
lean_dec(v_snd_978_);
lean_dec_ref(v_c_960_);
lean_dec_ref(v___x_959_);
v_a_1056_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1063_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1063_ == 0)
{
v___x_1058_ = v___x_990_;
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
else
{
lean_inc(v_a_1056_);
lean_dec(v___x_990_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1063_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1061_; 
if (v_isShared_1059_ == 0)
{
v___x_1061_ = v___x_1058_;
goto v_reusejp_1060_;
}
else
{
lean_object* v_reuseFailAlloc_1062_; 
v_reuseFailAlloc_1062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1056_);
v___x_1061_ = v_reuseFailAlloc_1062_;
goto v_reusejp_1060_;
}
v_reusejp_1060_:
{
return v___x_1061_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___boxed(lean_object** _args){
lean_object* v___x_1066_ = _args[0];
lean_object* v_c_1067_ = _args[1];
lean_object* v_as_1068_ = _args[2];
lean_object* v_sz_1069_ = _args[3];
lean_object* v_i_1070_ = _args[4];
lean_object* v_b_1071_ = _args[5];
lean_object* v___y_1072_ = _args[6];
lean_object* v___y_1073_ = _args[7];
lean_object* v___y_1074_ = _args[8];
lean_object* v___y_1075_ = _args[9];
lean_object* v___y_1076_ = _args[10];
lean_object* v___y_1077_ = _args[11];
lean_object* v___y_1078_ = _args[12];
lean_object* v___y_1079_ = _args[13];
lean_object* v___y_1080_ = _args[14];
lean_object* v___y_1081_ = _args[15];
lean_object* v___y_1082_ = _args[16];
_start:
{
size_t v_sz_boxed_1083_; size_t v_i_boxed_1084_; lean_object* v_res_1085_; 
v_sz_boxed_1083_ = lean_unbox_usize(v_sz_1069_);
lean_dec(v_sz_1069_);
v_i_boxed_1084_ = lean_unbox_usize(v_i_1070_);
lean_dec(v_i_1070_);
v_res_1085_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2(v___x_1066_, v_c_1067_, v_as_1068_, v_sz_boxed_1083_, v_i_boxed_1084_, v_b_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v_as_1068_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(lean_object* v_init_1086_, lean_object* v___x_1087_, lean_object* v_c_1088_, lean_object* v_n_1089_, lean_object* v_b_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_){
_start:
{
if (lean_obj_tag(v_n_1089_) == 0)
{
lean_object* v_cs_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1136_; 
v_cs_1102_ = lean_ctor_get(v_n_1089_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v_n_1089_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1104_ = v_n_1089_;
v_isShared_1105_ = v_isSharedCheck_1136_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_cs_1102_);
lean_dec(v_n_1089_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1136_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1106_; lean_object* v___x_1107_; size_t v_sz_1108_; size_t v___x_1109_; lean_object* v___x_1110_; 
v___x_1106_ = lean_box(0);
v___x_1107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1107_, 0, v___x_1106_);
lean_ctor_set(v___x_1107_, 1, v_b_1090_);
v_sz_1108_ = lean_array_size(v_cs_1102_);
v___x_1109_ = ((size_t)0ULL);
v___x_1110_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(v_init_1086_, v___x_1087_, v_c_1088_, v_cs_1102_, v_sz_1108_, v___x_1109_, v___x_1107_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
lean_dec_ref(v_cs_1102_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v_a_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1127_; 
v_a_1111_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1113_ = v___x_1110_;
v_isShared_1114_ = v_isSharedCheck_1127_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_a_1111_);
lean_dec(v___x_1110_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1127_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v_fst_1115_; 
v_fst_1115_ = lean_ctor_get(v_a_1111_, 0);
if (lean_obj_tag(v_fst_1115_) == 0)
{
lean_object* v_snd_1116_; lean_object* v___x_1118_; 
v_snd_1116_ = lean_ctor_get(v_a_1111_, 1);
lean_inc(v_snd_1116_);
lean_dec(v_a_1111_);
if (v_isShared_1105_ == 0)
{
lean_ctor_set_tag(v___x_1104_, 1);
lean_ctor_set(v___x_1104_, 0, v_snd_1116_);
v___x_1118_ = v___x_1104_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1122_; 
v_reuseFailAlloc_1122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1122_, 0, v_snd_1116_);
v___x_1118_ = v_reuseFailAlloc_1122_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
lean_object* v___x_1120_; 
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 0, v___x_1118_);
v___x_1120_ = v___x_1113_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___x_1118_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
else
{
lean_object* v_val_1123_; lean_object* v___x_1125_; 
lean_inc_ref(v_fst_1115_);
lean_dec(v_a_1111_);
lean_del_object(v___x_1104_);
v_val_1123_ = lean_ctor_get(v_fst_1115_, 0);
lean_inc(v_val_1123_);
lean_dec_ref(v_fst_1115_);
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 0, v_val_1123_);
v___x_1125_ = v___x_1113_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_val_1123_);
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
lean_del_object(v___x_1104_);
v_a_1128_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1110_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1110_);
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
else
{
lean_object* v_vs_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1171_; 
v_vs_1137_ = lean_ctor_get(v_n_1089_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v_n_1089_);
if (v_isSharedCheck_1171_ == 0)
{
v___x_1139_ = v_n_1089_;
v_isShared_1140_ = v_isSharedCheck_1171_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_vs_1137_);
lean_dec(v_n_1089_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1171_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1141_; lean_object* v___x_1142_; size_t v_sz_1143_; size_t v___x_1144_; lean_object* v___x_1145_; 
v___x_1141_ = lean_box(0);
v___x_1142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1142_, 0, v___x_1141_);
lean_ctor_set(v___x_1142_, 1, v_b_1090_);
v_sz_1143_ = lean_array_size(v_vs_1137_);
v___x_1144_ = ((size_t)0ULL);
v___x_1145_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2(v___x_1087_, v_c_1088_, v_vs_1137_, v_sz_1143_, v___x_1144_, v___x_1142_, v___y_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
lean_dec_ref(v_vs_1137_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1162_; 
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1148_ = v___x_1145_;
v_isShared_1149_ = v_isSharedCheck_1162_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_a_1146_);
lean_dec(v___x_1145_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1162_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v_fst_1150_; 
v_fst_1150_ = lean_ctor_get(v_a_1146_, 0);
if (lean_obj_tag(v_fst_1150_) == 0)
{
lean_object* v_snd_1151_; lean_object* v___x_1153_; 
v_snd_1151_ = lean_ctor_get(v_a_1146_, 1);
lean_inc(v_snd_1151_);
lean_dec(v_a_1146_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 0, v_snd_1151_);
v___x_1153_ = v___x_1139_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_snd_1151_);
v___x_1153_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
lean_object* v___x_1155_; 
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v___x_1153_);
v___x_1155_ = v___x_1148_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1153_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
else
{
lean_object* v_val_1158_; lean_object* v___x_1160_; 
lean_inc_ref(v_fst_1150_);
lean_dec(v_a_1146_);
lean_del_object(v___x_1139_);
v_val_1158_ = lean_ctor_get(v_fst_1150_, 0);
lean_inc(v_val_1158_);
lean_dec_ref(v_fst_1150_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v_val_1158_);
v___x_1160_ = v___x_1148_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_val_1158_);
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
else
{
lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1170_; 
lean_del_object(v___x_1139_);
v_a_1163_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1165_ = v___x_1145_;
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___x_1145_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1170_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1168_; 
if (v_isShared_1166_ == 0)
{
v___x_1168_ = v___x_1165_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_a_1163_);
v___x_1168_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
return v___x_1168_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(lean_object* v_init_1172_, lean_object* v___x_1173_, lean_object* v_c_1174_, lean_object* v_as_1175_, size_t v_sz_1176_, size_t v_i_1177_, lean_object* v_b_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
uint8_t v___x_1190_; 
v___x_1190_ = lean_usize_dec_lt(v_i_1177_, v_sz_1176_);
if (v___x_1190_ == 0)
{
lean_object* v___x_1191_; 
lean_dec_ref(v_c_1174_);
lean_dec_ref(v___x_1173_);
v___x_1191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1191_, 0, v_b_1178_);
return v___x_1191_;
}
else
{
lean_object* v_snd_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1226_; 
v_snd_1192_ = lean_ctor_get(v_b_1178_, 1);
v_isSharedCheck_1226_ = !lean_is_exclusive(v_b_1178_);
if (v_isSharedCheck_1226_ == 0)
{
lean_object* v_unused_1227_; 
v_unused_1227_ = lean_ctor_get(v_b_1178_, 0);
lean_dec(v_unused_1227_);
v___x_1194_ = v_b_1178_;
v_isShared_1195_ = v_isSharedCheck_1226_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_snd_1192_);
lean_dec(v_b_1178_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1226_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v_a_1196_; lean_object* v___x_1197_; 
v_a_1196_ = lean_array_uget_borrowed(v_as_1175_, v_i_1177_);
lean_inc(v_snd_1192_);
lean_inc(v_a_1196_);
lean_inc_ref(v_c_1174_);
lean_inc_ref(v___x_1173_);
v___x_1197_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(v_init_1172_, v___x_1173_, v_c_1174_, v_a_1196_, v_snd_1192_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_);
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1217_; 
v_a_1198_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1200_ = v___x_1197_;
v_isShared_1201_ = v_isSharedCheck_1217_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_dec(v___x_1197_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1217_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
if (lean_obj_tag(v_a_1198_) == 0)
{
lean_object* v___x_1202_; lean_object* v___x_1204_; 
lean_dec_ref(v_c_1174_);
lean_dec_ref(v___x_1173_);
v___x_1202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1202_, 0, v_a_1198_);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 0, v___x_1202_);
v___x_1204_ = v___x_1194_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v___x_1202_);
lean_ctor_set(v_reuseFailAlloc_1208_, 1, v_snd_1192_);
v___x_1204_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
lean_object* v___x_1206_; 
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 0, v___x_1204_);
v___x_1206_ = v___x_1200_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1204_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
else
{
lean_object* v_a_1209_; lean_object* v___x_1210_; lean_object* v___x_1212_; 
lean_del_object(v___x_1200_);
lean_dec(v_snd_1192_);
v_a_1209_ = lean_ctor_get(v_a_1198_, 0);
lean_inc(v_a_1209_);
lean_dec_ref(v_a_1198_);
v___x_1210_ = lean_box(0);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 1, v_a_1209_);
lean_ctor_set(v___x_1194_, 0, v___x_1210_);
v___x_1212_ = v___x_1194_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v___x_1210_);
lean_ctor_set(v_reuseFailAlloc_1216_, 1, v_a_1209_);
v___x_1212_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
size_t v___x_1213_; size_t v___x_1214_; 
v___x_1213_ = ((size_t)1ULL);
v___x_1214_ = lean_usize_add(v_i_1177_, v___x_1213_);
v_i_1177_ = v___x_1214_;
v_b_1178_ = v___x_1212_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1225_; 
lean_del_object(v___x_1194_);
lean_dec(v_snd_1192_);
lean_dec_ref(v_c_1174_);
lean_dec_ref(v___x_1173_);
v_a_1218_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1220_ = v___x_1197_;
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1197_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_init_1228_ = _args[0];
lean_object* v___x_1229_ = _args[1];
lean_object* v_c_1230_ = _args[2];
lean_object* v_as_1231_ = _args[3];
lean_object* v_sz_1232_ = _args[4];
lean_object* v_i_1233_ = _args[5];
lean_object* v_b_1234_ = _args[6];
lean_object* v___y_1235_ = _args[7];
lean_object* v___y_1236_ = _args[8];
lean_object* v___y_1237_ = _args[9];
lean_object* v___y_1238_ = _args[10];
lean_object* v___y_1239_ = _args[11];
lean_object* v___y_1240_ = _args[12];
lean_object* v___y_1241_ = _args[13];
lean_object* v___y_1242_ = _args[14];
lean_object* v___y_1243_ = _args[15];
lean_object* v___y_1244_ = _args[16];
lean_object* v___y_1245_ = _args[17];
_start:
{
size_t v_sz_boxed_1246_; size_t v_i_boxed_1247_; lean_object* v_res_1248_; 
v_sz_boxed_1246_ = lean_unbox_usize(v_sz_1232_);
lean_dec(v_sz_1232_);
v_i_boxed_1247_ = lean_unbox_usize(v_i_1233_);
lean_dec(v_i_1233_);
v_res_1248_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(v_init_1228_, v___x_1229_, v_c_1230_, v_as_1231_, v_sz_boxed_1246_, v_i_boxed_1247_, v_b_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec(v___y_1236_);
lean_dec(v___y_1235_);
lean_dec_ref(v_as_1231_);
lean_dec_ref(v_init_1228_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___boxed(lean_object* v_init_1249_, lean_object* v___x_1250_, lean_object* v_c_1251_, lean_object* v_n_1252_, lean_object* v_b_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(v_init_1249_, v___x_1250_, v_c_1251_, v_n_1252_, v_b_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
lean_dec(v___y_1263_);
lean_dec_ref(v___y_1262_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec_ref(v_init_1249_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4(lean_object* v___x_1272_, lean_object* v_c_1273_, lean_object* v_as_1274_, size_t v_sz_1275_, size_t v_i_1276_, lean_object* v_b_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_, lean_object* v___y_1281_, lean_object* v___y_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_, lean_object* v___y_1285_, lean_object* v___y_1286_, lean_object* v___y_1287_){
_start:
{
uint8_t v___x_1289_; 
v___x_1289_ = lean_usize_dec_lt(v_i_1276_, v_sz_1275_);
if (v___x_1289_ == 0)
{
lean_object* v___x_1290_; 
lean_dec_ref(v_c_1273_);
lean_dec_ref(v___x_1272_);
v___x_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1290_, 0, v_b_1277_);
return v___x_1290_;
}
else
{
lean_object* v_snd_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1376_; 
v_snd_1291_ = lean_ctor_get(v_b_1277_, 1);
v_isSharedCheck_1376_ = !lean_is_exclusive(v_b_1277_);
if (v_isSharedCheck_1376_ == 0)
{
lean_object* v_unused_1377_; 
v_unused_1377_ = lean_ctor_get(v_b_1277_, 0);
lean_dec(v_unused_1377_);
v___x_1293_ = v_b_1277_;
v_isShared_1294_ = v_isSharedCheck_1376_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_snd_1291_);
lean_dec(v_b_1277_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1376_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v_a_1295_; lean_object* v_p_1296_; lean_object* v___x_1297_; uint8_t v___x_1298_; 
v_a_1295_ = lean_array_uget_borrowed(v_as_1274_, v_i_1276_);
v_p_1296_ = lean_ctor_get(v_a_1295_, 0);
v___x_1297_ = lean_box(0);
v___x_1298_ = l_Int_Linear_Poly_isNegEq(v___x_1272_, v_p_1296_);
if (v___x_1298_ == 0)
{
lean_object* v___x_1299_; size_t v___x_1300_; size_t v___x_1301_; 
lean_del_object(v___x_1293_);
lean_dec(v_snd_1291_);
v___x_1299_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___closed__1));
v___x_1300_ = ((size_t)1ULL);
v___x_1301_ = lean_usize_add(v_i_1276_, v___x_1300_);
v_i_1276_ = v___x_1301_;
v_b_1277_ = v___x_1299_;
goto _start;
}
else
{
lean_object* v___x_1303_; 
lean_inc(v_a_1295_);
v___x_1303_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_1295_, v___y_1278_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_object* v_options_1304_; lean_object* v_inheritedTraceOptions_1305_; uint8_t v_hasTrace_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___y_1310_; lean_object* v___y_1311_; lean_object* v___y_1312_; lean_object* v___y_1313_; lean_object* v___y_1314_; lean_object* v___y_1315_; lean_object* v___y_1316_; lean_object* v___y_1317_; lean_object* v___y_1318_; lean_object* v___y_1319_; 
lean_dec_ref(v___x_1303_);
v_options_1304_ = lean_ctor_get(v___y_1286_, 2);
v_inheritedTraceOptions_1305_ = lean_ctor_get(v___y_1286_, 13);
v_hasTrace_1306_ = lean_ctor_get_uint8(v_options_1304_, sizeof(void*)*1);
lean_inc(v_a_1295_);
v___x_1307_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1307_, 0, v_c_1273_);
lean_ctor_set(v___x_1307_, 1, v_a_1295_);
v___x_1308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1272_);
lean_ctor_set(v___x_1308_, 1, v___x_1307_);
if (v_hasTrace_1306_ == 0)
{
v___y_1310_ = v___y_1278_;
v___y_1311_ = v___y_1279_;
v___y_1312_ = v___y_1280_;
v___y_1313_ = v___y_1281_;
v___y_1314_ = v___y_1282_;
v___y_1315_ = v___y_1283_;
v___y_1316_ = v___y_1284_;
v___y_1317_ = v___y_1285_;
v___y_1318_ = v___y_1286_;
v___y_1319_ = v___y_1287_;
goto v___jp_1309_;
}
else
{
lean_object* v___x_1344_; lean_object* v___x_1345_; uint8_t v___x_1346_; 
v___x_1344_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_1345_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5);
v___x_1346_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1305_, v_options_1304_, v___x_1345_);
if (v___x_1346_ == 0)
{
v___y_1310_ = v___y_1278_;
v___y_1311_ = v___y_1279_;
v___y_1312_ = v___y_1280_;
v___y_1313_ = v___y_1281_;
v___y_1314_ = v___y_1282_;
v___y_1315_ = v___y_1283_;
v___y_1316_ = v___y_1284_;
v___y_1317_ = v___y_1285_;
v___y_1318_ = v___y_1286_;
v___y_1319_ = v___y_1287_;
goto v___jp_1309_;
}
else
{
lean_object* v___x_1347_; 
lean_inc_ref(v___x_1308_);
v___x_1347_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_1308_, v___y_1278_, v___y_1286_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v_a_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
lean_inc(v_a_1348_);
lean_dec_ref(v___x_1347_);
v___x_1349_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7);
v___x_1350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1349_);
lean_ctor_set(v___x_1350_, 1, v_a_1348_);
v___x_1351_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_1344_, v___x_1350_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_dec_ref(v___x_1351_);
v___y_1310_ = v___y_1278_;
v___y_1311_ = v___y_1279_;
v___y_1312_ = v___y_1280_;
v___y_1313_ = v___y_1281_;
v___y_1314_ = v___y_1282_;
v___y_1315_ = v___y_1283_;
v___y_1316_ = v___y_1284_;
v___y_1317_ = v___y_1285_;
v___y_1318_ = v___y_1286_;
v___y_1319_ = v___y_1287_;
goto v___jp_1309_;
}
else
{
lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1359_; 
lean_dec_ref(v___x_1308_);
lean_del_object(v___x_1293_);
lean_dec(v_snd_1291_);
v_a_1352_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1354_ = v___x_1351_;
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1351_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1357_; 
if (v_isShared_1355_ == 0)
{
v___x_1357_ = v___x_1354_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_a_1352_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
lean_dec_ref(v___x_1308_);
lean_del_object(v___x_1293_);
lean_dec(v_snd_1291_);
v_a_1360_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___x_1347_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1347_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1360_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
}
v___jp_1309_:
{
lean_object* v___x_1320_; 
lean_inc(v___y_1319_);
lean_inc_ref(v___y_1318_);
lean_inc(v___y_1317_);
lean_inc_ref(v___y_1316_);
lean_inc(v___y_1315_);
lean_inc_ref(v___y_1314_);
lean_inc(v___y_1313_);
lean_inc_ref(v___y_1312_);
lean_inc(v___y_1311_);
lean_inc(v___y_1310_);
v___x_1320_ = lean_grind_cutsat_assert_eq(v___x_1308_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_);
if (lean_obj_tag(v___x_1320_) == 0)
{
lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1334_; 
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1334_ == 0)
{
lean_object* v_unused_1335_; 
v_unused_1335_ = lean_ctor_get(v___x_1320_, 0);
lean_dec(v_unused_1335_);
v___x_1322_ = v___x_1320_;
v_isShared_1323_ = v_isSharedCheck_1334_;
goto v_resetjp_1321_;
}
else
{
lean_dec(v___x_1320_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1334_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1327_; 
v___x_1324_ = lean_box(v___x_1298_);
v___x_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1324_);
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 1, v___x_1297_);
lean_ctor_set(v___x_1293_, 0, v___x_1325_);
v___x_1327_ = v___x_1293_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1333_; 
v_reuseFailAlloc_1333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1333_, 0, v___x_1325_);
lean_ctor_set(v_reuseFailAlloc_1333_, 1, v___x_1297_);
v___x_1327_ = v_reuseFailAlloc_1333_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1331_; 
v___x_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1327_);
v___x_1329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1328_);
lean_ctor_set(v___x_1329_, 1, v_snd_1291_);
if (v_isShared_1323_ == 0)
{
lean_ctor_set(v___x_1322_, 0, v___x_1329_);
v___x_1331_ = v___x_1322_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v___x_1329_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
else
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1343_; 
lean_del_object(v___x_1293_);
lean_dec(v_snd_1291_);
v_a_1336_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1338_ = v___x_1320_;
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1320_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1341_; 
if (v_isShared_1339_ == 0)
{
v___x_1341_ = v___x_1338_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_a_1336_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
}
}
else
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
lean_del_object(v___x_1293_);
lean_dec(v_snd_1291_);
lean_dec_ref(v_c_1273_);
lean_dec_ref(v___x_1272_);
v_a_1368_ = lean_ctor_get(v___x_1303_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1303_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1303_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v___x_1378_ = _args[0];
lean_object* v_c_1379_ = _args[1];
lean_object* v_as_1380_ = _args[2];
lean_object* v_sz_1381_ = _args[3];
lean_object* v_i_1382_ = _args[4];
lean_object* v_b_1383_ = _args[5];
lean_object* v___y_1384_ = _args[6];
lean_object* v___y_1385_ = _args[7];
lean_object* v___y_1386_ = _args[8];
lean_object* v___y_1387_ = _args[9];
lean_object* v___y_1388_ = _args[10];
lean_object* v___y_1389_ = _args[11];
lean_object* v___y_1390_ = _args[12];
lean_object* v___y_1391_ = _args[13];
lean_object* v___y_1392_ = _args[14];
lean_object* v___y_1393_ = _args[15];
lean_object* v___y_1394_ = _args[16];
_start:
{
size_t v_sz_boxed_1395_; size_t v_i_boxed_1396_; lean_object* v_res_1397_; 
v_sz_boxed_1395_ = lean_unbox_usize(v_sz_1381_);
lean_dec(v_sz_1381_);
v_i_boxed_1396_ = lean_unbox_usize(v_i_1382_);
lean_dec(v_i_1382_);
v_res_1397_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4(v___x_1378_, v_c_1379_, v_as_1380_, v_sz_boxed_1395_, v_i_boxed_1396_, v_b_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
lean_dec(v___y_1385_);
lean_dec(v___y_1384_);
lean_dec_ref(v_as_1380_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1(lean_object* v___x_1401_, lean_object* v_c_1402_, lean_object* v_as_1403_, size_t v_sz_1404_, size_t v_i_1405_, lean_object* v_b_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
uint8_t v___x_1418_; 
v___x_1418_ = lean_usize_dec_lt(v_i_1405_, v_sz_1404_);
if (v___x_1418_ == 0)
{
lean_object* v___x_1419_; 
lean_dec_ref(v_c_1402_);
lean_dec_ref(v___x_1401_);
v___x_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1419_, 0, v_b_1406_);
return v___x_1419_;
}
else
{
lean_object* v_snd_1420_; lean_object* v___x_1422_; uint8_t v_isShared_1423_; uint8_t v_isSharedCheck_1505_; 
v_snd_1420_ = lean_ctor_get(v_b_1406_, 1);
v_isSharedCheck_1505_ = !lean_is_exclusive(v_b_1406_);
if (v_isSharedCheck_1505_ == 0)
{
lean_object* v_unused_1506_; 
v_unused_1506_ = lean_ctor_get(v_b_1406_, 0);
lean_dec(v_unused_1506_);
v___x_1422_ = v_b_1406_;
v_isShared_1423_ = v_isSharedCheck_1505_;
goto v_resetjp_1421_;
}
else
{
lean_inc(v_snd_1420_);
lean_dec(v_b_1406_);
v___x_1422_ = lean_box(0);
v_isShared_1423_ = v_isSharedCheck_1505_;
goto v_resetjp_1421_;
}
v_resetjp_1421_:
{
lean_object* v_a_1424_; lean_object* v_p_1425_; lean_object* v___x_1426_; uint8_t v___x_1427_; 
v_a_1424_ = lean_array_uget_borrowed(v_as_1403_, v_i_1405_);
v_p_1425_ = lean_ctor_get(v_a_1424_, 0);
v___x_1426_ = lean_box(0);
v___x_1427_ = l_Int_Linear_Poly_isNegEq(v___x_1401_, v_p_1425_);
if (v___x_1427_ == 0)
{
lean_object* v___x_1428_; size_t v___x_1429_; size_t v___x_1430_; lean_object* v___x_1431_; 
lean_del_object(v___x_1422_);
lean_dec(v_snd_1420_);
v___x_1428_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1___closed__0));
v___x_1429_ = ((size_t)1ULL);
v___x_1430_ = lean_usize_add(v_i_1405_, v___x_1429_);
v___x_1431_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4(v___x_1401_, v_c_1402_, v_as_1403_, v_sz_1404_, v___x_1430_, v___x_1428_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
return v___x_1431_;
}
else
{
lean_object* v___x_1432_; 
lean_inc(v_a_1424_);
v___x_1432_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_1424_, v___y_1407_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_object* v_options_1433_; lean_object* v_inheritedTraceOptions_1434_; uint8_t v_hasTrace_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1442_; lean_object* v___y_1443_; lean_object* v___y_1444_; lean_object* v___y_1445_; lean_object* v___y_1446_; lean_object* v___y_1447_; lean_object* v___y_1448_; 
lean_dec_ref(v___x_1432_);
v_options_1433_ = lean_ctor_get(v___y_1415_, 2);
v_inheritedTraceOptions_1434_ = lean_ctor_get(v___y_1415_, 13);
v_hasTrace_1435_ = lean_ctor_get_uint8(v_options_1433_, sizeof(void*)*1);
lean_inc(v_a_1424_);
v___x_1436_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1436_, 0, v_c_1402_);
lean_ctor_set(v___x_1436_, 1, v_a_1424_);
v___x_1437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1401_);
lean_ctor_set(v___x_1437_, 1, v___x_1436_);
if (v_hasTrace_1435_ == 0)
{
v___y_1439_ = v___y_1407_;
v___y_1440_ = v___y_1408_;
v___y_1441_ = v___y_1409_;
v___y_1442_ = v___y_1410_;
v___y_1443_ = v___y_1411_;
v___y_1444_ = v___y_1412_;
v___y_1445_ = v___y_1413_;
v___y_1446_ = v___y_1414_;
v___y_1447_ = v___y_1415_;
v___y_1448_ = v___y_1416_;
goto v___jp_1438_;
}
else
{
lean_object* v___x_1473_; lean_object* v___x_1474_; uint8_t v___x_1475_; 
v___x_1473_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_1474_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5);
v___x_1475_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1434_, v_options_1433_, v___x_1474_);
if (v___x_1475_ == 0)
{
v___y_1439_ = v___y_1407_;
v___y_1440_ = v___y_1408_;
v___y_1441_ = v___y_1409_;
v___y_1442_ = v___y_1410_;
v___y_1443_ = v___y_1411_;
v___y_1444_ = v___y_1412_;
v___y_1445_ = v___y_1413_;
v___y_1446_ = v___y_1414_;
v___y_1447_ = v___y_1415_;
v___y_1448_ = v___y_1416_;
goto v___jp_1438_;
}
else
{
lean_object* v___x_1476_; 
lean_inc_ref(v___x_1437_);
v___x_1476_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_1437_, v___y_1407_, v___y_1415_);
if (lean_obj_tag(v___x_1476_) == 0)
{
lean_object* v_a_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
v_a_1477_ = lean_ctor_get(v___x_1476_, 0);
lean_inc(v_a_1477_);
lean_dec_ref(v___x_1476_);
v___x_1478_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7);
v___x_1479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1478_);
lean_ctor_set(v___x_1479_, 1, v_a_1477_);
v___x_1480_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_1473_, v___x_1479_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_dec_ref(v___x_1480_);
v___y_1439_ = v___y_1407_;
v___y_1440_ = v___y_1408_;
v___y_1441_ = v___y_1409_;
v___y_1442_ = v___y_1410_;
v___y_1443_ = v___y_1411_;
v___y_1444_ = v___y_1412_;
v___y_1445_ = v___y_1413_;
v___y_1446_ = v___y_1414_;
v___y_1447_ = v___y_1415_;
v___y_1448_ = v___y_1416_;
goto v___jp_1438_;
}
else
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
lean_dec_ref(v___x_1437_);
lean_del_object(v___x_1422_);
lean_dec(v_snd_1420_);
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___x_1480_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1480_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1481_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
}
else
{
lean_object* v_a_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1496_; 
lean_dec_ref(v___x_1437_);
lean_del_object(v___x_1422_);
lean_dec(v_snd_1420_);
v_a_1489_ = lean_ctor_get(v___x_1476_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1476_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1491_ = v___x_1476_;
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_a_1489_);
lean_dec(v___x_1476_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1494_; 
if (v_isShared_1492_ == 0)
{
v___x_1494_ = v___x_1491_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_a_1489_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
}
}
v___jp_1438_:
{
lean_object* v___x_1449_; 
lean_inc(v___y_1448_);
lean_inc_ref(v___y_1447_);
lean_inc(v___y_1446_);
lean_inc_ref(v___y_1445_);
lean_inc(v___y_1444_);
lean_inc_ref(v___y_1443_);
lean_inc(v___y_1442_);
lean_inc_ref(v___y_1441_);
lean_inc(v___y_1440_);
lean_inc(v___y_1439_);
v___x_1449_ = lean_grind_cutsat_assert_eq(v___x_1437_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
if (lean_obj_tag(v___x_1449_) == 0)
{
lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1463_; 
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1463_ == 0)
{
lean_object* v_unused_1464_; 
v_unused_1464_ = lean_ctor_get(v___x_1449_, 0);
lean_dec(v_unused_1464_);
v___x_1451_ = v___x_1449_;
v_isShared_1452_ = v_isSharedCheck_1463_;
goto v_resetjp_1450_;
}
else
{
lean_dec(v___x_1449_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1463_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1456_; 
v___x_1453_ = lean_box(v___x_1427_);
v___x_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1453_);
if (v_isShared_1423_ == 0)
{
lean_ctor_set(v___x_1422_, 1, v___x_1426_);
lean_ctor_set(v___x_1422_, 0, v___x_1454_);
v___x_1456_ = v___x_1422_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v___x_1454_);
lean_ctor_set(v_reuseFailAlloc_1462_, 1, v___x_1426_);
v___x_1456_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1460_; 
v___x_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1457_, 0, v___x_1456_);
v___x_1458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1457_);
lean_ctor_set(v___x_1458_, 1, v_snd_1420_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 0, v___x_1458_);
v___x_1460_ = v___x_1451_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1458_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
}
else
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1472_; 
lean_del_object(v___x_1422_);
lean_dec(v_snd_1420_);
v_a_1465_ = lean_ctor_get(v___x_1449_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1449_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1467_ = v___x_1449_;
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1449_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1470_; 
if (v_isShared_1468_ == 0)
{
v___x_1470_ = v___x_1467_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_a_1465_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
}
else
{
lean_object* v_a_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1504_; 
lean_del_object(v___x_1422_);
lean_dec(v_snd_1420_);
lean_dec_ref(v_c_1402_);
lean_dec_ref(v___x_1401_);
v_a_1497_ = lean_ctor_get(v___x_1432_, 0);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1499_ = v___x_1432_;
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_a_1497_);
lean_dec(v___x_1432_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1502_; 
if (v_isShared_1500_ == 0)
{
v___x_1502_ = v___x_1499_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_a_1497_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v___x_1507_ = _args[0];
lean_object* v_c_1508_ = _args[1];
lean_object* v_as_1509_ = _args[2];
lean_object* v_sz_1510_ = _args[3];
lean_object* v_i_1511_ = _args[4];
lean_object* v_b_1512_ = _args[5];
lean_object* v___y_1513_ = _args[6];
lean_object* v___y_1514_ = _args[7];
lean_object* v___y_1515_ = _args[8];
lean_object* v___y_1516_ = _args[9];
lean_object* v___y_1517_ = _args[10];
lean_object* v___y_1518_ = _args[11];
lean_object* v___y_1519_ = _args[12];
lean_object* v___y_1520_ = _args[13];
lean_object* v___y_1521_ = _args[14];
lean_object* v___y_1522_ = _args[15];
lean_object* v___y_1523_ = _args[16];
_start:
{
size_t v_sz_boxed_1524_; size_t v_i_boxed_1525_; lean_object* v_res_1526_; 
v_sz_boxed_1524_ = lean_unbox_usize(v_sz_1510_);
lean_dec(v_sz_1510_);
v_i_boxed_1525_ = lean_unbox_usize(v_i_1511_);
lean_dec(v_i_1511_);
v_res_1526_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1(v___x_1507_, v_c_1508_, v_as_1509_, v_sz_boxed_1524_, v_i_boxed_1525_, v_b_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
lean_dec(v___y_1518_);
lean_dec_ref(v___y_1517_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec(v___y_1513_);
lean_dec_ref(v_as_1509_);
return v_res_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0(lean_object* v___x_1527_, lean_object* v_c_1528_, lean_object* v_t_1529_, lean_object* v_init_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_){
_start:
{
lean_object* v_root_1542_; lean_object* v_tail_1543_; lean_object* v___x_1544_; 
v_root_1542_ = lean_ctor_get(v_t_1529_, 0);
lean_inc_ref(v_root_1542_);
v_tail_1543_ = lean_ctor_get(v_t_1529_, 1);
lean_inc_ref(v_tail_1543_);
lean_dec_ref(v_t_1529_);
lean_inc_ref(v_c_1528_);
lean_inc_ref(v___x_1527_);
lean_inc_ref(v_init_1530_);
v___x_1544_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(v_init_1530_, v___x_1527_, v_c_1528_, v_root_1542_, v_init_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
lean_dec_ref(v_init_1530_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v_a_1545_; lean_object* v___x_1547_; uint8_t v_isShared_1548_; uint8_t v_isSharedCheck_1581_; 
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1547_ = v___x_1544_;
v_isShared_1548_ = v_isSharedCheck_1581_;
goto v_resetjp_1546_;
}
else
{
lean_inc(v_a_1545_);
lean_dec(v___x_1544_);
v___x_1547_ = lean_box(0);
v_isShared_1548_ = v_isSharedCheck_1581_;
goto v_resetjp_1546_;
}
v_resetjp_1546_:
{
if (lean_obj_tag(v_a_1545_) == 0)
{
lean_object* v_a_1549_; lean_object* v___x_1551_; 
lean_dec_ref(v_tail_1543_);
lean_dec_ref(v_c_1528_);
lean_dec_ref(v___x_1527_);
v_a_1549_ = lean_ctor_get(v_a_1545_, 0);
lean_inc(v_a_1549_);
lean_dec_ref(v_a_1545_);
if (v_isShared_1548_ == 0)
{
lean_ctor_set(v___x_1547_, 0, v_a_1549_);
v___x_1551_ = v___x_1547_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_a_1549_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
else
{
lean_object* v_a_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; size_t v_sz_1556_; size_t v___x_1557_; lean_object* v___x_1558_; 
lean_del_object(v___x_1547_);
v_a_1553_ = lean_ctor_get(v_a_1545_, 0);
lean_inc(v_a_1553_);
lean_dec_ref(v_a_1545_);
v___x_1554_ = lean_box(0);
v___x_1555_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1554_);
lean_ctor_set(v___x_1555_, 1, v_a_1553_);
v_sz_1556_ = lean_array_size(v_tail_1543_);
v___x_1557_ = ((size_t)0ULL);
v___x_1558_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1(v___x_1527_, v_c_1528_, v_tail_1543_, v_sz_1556_, v___x_1557_, v___x_1555_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_);
lean_dec_ref(v_tail_1543_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v_a_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1572_; 
v_a_1559_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1561_ = v___x_1558_;
v_isShared_1562_ = v_isSharedCheck_1572_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_a_1559_);
lean_dec(v___x_1558_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1572_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v_fst_1563_; 
v_fst_1563_ = lean_ctor_get(v_a_1559_, 0);
if (lean_obj_tag(v_fst_1563_) == 0)
{
lean_object* v_snd_1564_; lean_object* v___x_1566_; 
v_snd_1564_ = lean_ctor_get(v_a_1559_, 1);
lean_inc(v_snd_1564_);
lean_dec(v_a_1559_);
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 0, v_snd_1564_);
v___x_1566_ = v___x_1561_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_snd_1564_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
else
{
lean_object* v_val_1568_; lean_object* v___x_1570_; 
lean_inc_ref(v_fst_1563_);
lean_dec(v_a_1559_);
v_val_1568_ = lean_ctor_get(v_fst_1563_, 0);
lean_inc(v_val_1568_);
lean_dec_ref(v_fst_1563_);
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 0, v_val_1568_);
v___x_1570_ = v___x_1561_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_val_1568_);
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
else
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1580_; 
v_a_1573_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1580_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1580_ == 0)
{
v___x_1575_ = v___x_1558_;
v_isShared_1576_ = v_isSharedCheck_1580_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1558_);
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
}
else
{
lean_object* v_a_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1589_; 
lean_dec_ref(v_tail_1543_);
lean_dec_ref(v_c_1528_);
lean_dec_ref(v___x_1527_);
v_a_1582_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1589_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1589_ == 0)
{
v___x_1584_ = v___x_1544_;
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_a_1582_);
lean_dec(v___x_1544_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1589_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1587_; 
if (v_isShared_1585_ == 0)
{
v___x_1587_ = v___x_1584_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_a_1582_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0___boxed(lean_object* v___x_1590_, lean_object* v_c_1591_, lean_object* v_t_1592_, lean_object* v_init_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_){
_start:
{
lean_object* v_res_1605_; 
v_res_1605_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0(v___x_1590_, v_c_1591_, v_t_1592_, v_init_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
lean_dec(v___y_1595_);
lean_dec(v___y_1594_);
return v_res_1605_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0(void){
_start:
{
lean_object* v___x_1606_; 
v___x_1606_ = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq(lean_object* v_c_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_, lean_object* v_a_1616_, lean_object* v_a_1617_){
_start:
{
lean_object* v_p_1619_; 
v_p_1619_ = lean_ctor_get(v_c_1607_, 0);
if (lean_obj_tag(v_p_1619_) == 1)
{
lean_object* v_k_1620_; lean_object* v_v_1621_; lean_object* v___x_1622_; 
lean_inc_ref(v_p_1619_);
v_k_1620_ = lean_ctor_get(v_p_1619_, 0);
v_v_1621_ = lean_ctor_get(v_p_1619_, 1);
v___x_1622_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1608_, v_a_1616_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v_a_1623_; lean_object* v___y_1625_; lean_object* v___x_1651_; uint8_t v___x_1652_; 
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
lean_inc(v_a_1623_);
lean_dec_ref(v___x_1622_);
v___x_1651_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9);
v___x_1652_ = lean_int_dec_lt(v_k_1620_, v___x_1651_);
if (v___x_1652_ == 0)
{
lean_object* v_lowers_1653_; lean_object* v_size_1654_; lean_object* v___x_1655_; uint8_t v___x_1656_; 
v_lowers_1653_ = lean_ctor_get(v_a_1623_, 7);
lean_inc_ref(v_lowers_1653_);
lean_dec(v_a_1623_);
v_size_1654_ = lean_ctor_get(v_lowers_1653_, 2);
v___x_1655_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0);
v___x_1656_ = lean_nat_dec_lt(v_v_1621_, v_size_1654_);
if (v___x_1656_ == 0)
{
lean_object* v___x_1657_; 
lean_dec_ref(v_lowers_1653_);
v___x_1657_ = l_outOfBounds___redArg(v___x_1655_);
v___y_1625_ = v___x_1657_;
goto v___jp_1624_;
}
else
{
lean_object* v___x_1658_; 
v___x_1658_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1655_, v_lowers_1653_, v_v_1621_);
lean_dec_ref(v_lowers_1653_);
v___y_1625_ = v___x_1658_;
goto v___jp_1624_;
}
}
else
{
lean_object* v_uppers_1659_; lean_object* v_size_1660_; lean_object* v___x_1661_; uint8_t v___x_1662_; 
v_uppers_1659_ = lean_ctor_get(v_a_1623_, 8);
lean_inc_ref(v_uppers_1659_);
lean_dec(v_a_1623_);
v_size_1660_ = lean_ctor_get(v_uppers_1659_, 2);
v___x_1661_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0);
v___x_1662_ = lean_nat_dec_lt(v_v_1621_, v_size_1660_);
if (v___x_1662_ == 0)
{
lean_object* v___x_1663_; 
lean_dec_ref(v_uppers_1659_);
v___x_1663_ = l_outOfBounds___redArg(v___x_1661_);
v___y_1625_ = v___x_1663_;
goto v___jp_1624_;
}
else
{
lean_object* v___x_1664_; 
v___x_1664_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1661_, v_uppers_1659_, v_v_1621_);
lean_dec_ref(v_uppers_1659_);
v___y_1625_ = v___x_1664_;
goto v___jp_1624_;
}
}
v___jp_1624_:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; 
v___x_1626_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__0));
v___x_1627_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0(v_p_1619_, v_c_1607_, v___y_1625_, v___x_1626_, v_a_1608_, v_a_1609_, v_a_1610_, v_a_1611_, v_a_1612_, v_a_1613_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1642_; 
v_a_1628_ = lean_ctor_get(v___x_1627_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1630_ = v___x_1627_;
v_isShared_1631_ = v_isSharedCheck_1642_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_a_1628_);
lean_dec(v___x_1627_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1642_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v_fst_1632_; 
v_fst_1632_ = lean_ctor_get(v_a_1628_, 0);
lean_inc(v_fst_1632_);
lean_dec(v_a_1628_);
if (lean_obj_tag(v_fst_1632_) == 0)
{
uint8_t v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1636_; 
v___x_1633_ = 0;
v___x_1634_ = lean_box(v___x_1633_);
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 0, v___x_1634_);
v___x_1636_ = v___x_1630_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v___x_1634_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
else
{
lean_object* v_val_1638_; lean_object* v___x_1640_; 
v_val_1638_ = lean_ctor_get(v_fst_1632_, 0);
lean_inc(v_val_1638_);
lean_dec_ref(v_fst_1632_);
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 0, v_val_1638_);
v___x_1640_ = v___x_1630_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_val_1638_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
}
}
}
}
else
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1650_; 
v_a_1643_ = lean_ctor_get(v___x_1627_, 0);
v_isSharedCheck_1650_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1650_ == 0)
{
v___x_1645_ = v___x_1627_;
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1627_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1650_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1648_; 
if (v_isShared_1646_ == 0)
{
v___x_1648_ = v___x_1645_;
goto v_reusejp_1647_;
}
else
{
lean_object* v_reuseFailAlloc_1649_; 
v_reuseFailAlloc_1649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1649_, 0, v_a_1643_);
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
}
else
{
lean_object* v_a_1665_; lean_object* v___x_1667_; uint8_t v_isShared_1668_; uint8_t v_isSharedCheck_1672_; 
lean_dec_ref(v_p_1619_);
lean_dec_ref(v_c_1607_);
v_a_1665_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1672_ == 0)
{
v___x_1667_ = v___x_1622_;
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
else
{
lean_inc(v_a_1665_);
lean_dec(v___x_1622_);
v___x_1667_ = lean_box(0);
v_isShared_1668_ = v_isSharedCheck_1672_;
goto v_resetjp_1666_;
}
v_resetjp_1666_:
{
lean_object* v___x_1670_; 
if (v_isShared_1668_ == 0)
{
v___x_1670_ = v___x_1667_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v_a_1665_);
v___x_1670_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
return v___x_1670_;
}
}
}
}
else
{
lean_object* v___x_1673_; 
v___x_1673_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_1607_, v_a_1608_, v_a_1614_, v_a_1615_, v_a_1616_, v_a_1617_);
return v___x_1673_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___boxed(lean_object* v_c_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_, lean_object* v_a_1678_, lean_object* v_a_1679_, lean_object* v_a_1680_, lean_object* v_a_1681_, lean_object* v_a_1682_, lean_object* v_a_1683_, lean_object* v_a_1684_, lean_object* v_a_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq(v_c_1674_, v_a_1675_, v_a_1676_, v_a_1677_, v_a_1678_, v_a_1679_, v_a_1680_, v_a_1681_, v_a_1682_, v_a_1683_, v_a_1684_);
lean_dec(v_a_1684_);
lean_dec_ref(v_a_1683_);
lean_dec(v_a_1682_);
lean_dec_ref(v_a_1681_);
lean_dec(v_a_1680_);
lean_dec_ref(v_a_1679_);
lean_dec(v_a_1678_);
lean_dec_ref(v_a_1677_);
lean_dec(v_a_1676_);
lean_dec(v_a_1675_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(lean_object* v___x_1687_, lean_object* v_as_1688_, size_t v_i_1689_, size_t v_stop_1690_, lean_object* v_b_1691_){
_start:
{
lean_object* v___y_1693_; uint8_t v___x_1697_; 
v___x_1697_ = lean_usize_dec_eq(v_i_1689_, v_stop_1690_);
if (v___x_1697_ == 0)
{
lean_object* v___x_1698_; lean_object* v_p_1699_; uint8_t v___x_1700_; 
v___x_1698_ = lean_array_uget_borrowed(v_as_1688_, v_i_1689_);
v_p_1699_ = lean_ctor_get(v___x_1698_, 0);
v___x_1700_ = l_Int_Linear_instBEqPoly_beq(v_p_1699_, v___x_1687_);
if (v___x_1700_ == 0)
{
lean_object* v___x_1701_; 
lean_inc(v___x_1698_);
v___x_1701_ = l_Lean_PersistentArray_push___redArg(v_b_1691_, v___x_1698_);
v___y_1693_ = v___x_1701_;
goto v___jp_1692_;
}
else
{
v___y_1693_ = v_b_1691_;
goto v___jp_1692_;
}
}
else
{
return v_b_1691_;
}
v___jp_1692_:
{
size_t v___x_1694_; size_t v___x_1695_; 
v___x_1694_ = ((size_t)1ULL);
v___x_1695_ = lean_usize_add(v_i_1689_, v___x_1694_);
v_i_1689_ = v___x_1695_;
v_b_1691_ = v___y_1693_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1___boxed(lean_object* v___x_1702_, lean_object* v_as_1703_, lean_object* v_i_1704_, lean_object* v_stop_1705_, lean_object* v_b_1706_){
_start:
{
size_t v_i_boxed_1707_; size_t v_stop_boxed_1708_; lean_object* v_res_1709_; 
v_i_boxed_1707_ = lean_unbox_usize(v_i_1704_);
lean_dec(v_i_1704_);
v_stop_boxed_1708_ = lean_unbox_usize(v_stop_1705_);
lean_dec(v_stop_1705_);
v_res_1709_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1702_, v_as_1703_, v_i_boxed_1707_, v_stop_boxed_1708_, v_b_1706_);
lean_dec_ref(v_as_1703_);
lean_dec_ref(v___x_1702_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(lean_object* v___x_1710_, lean_object* v_x_1711_, lean_object* v_x_1712_){
_start:
{
if (lean_obj_tag(v_x_1711_) == 0)
{
lean_object* v_cs_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; uint8_t v___x_1716_; 
v_cs_1713_ = lean_ctor_get(v_x_1711_, 0);
v___x_1714_ = lean_unsigned_to_nat(0u);
v___x_1715_ = lean_array_get_size(v_cs_1713_);
v___x_1716_ = lean_nat_dec_lt(v___x_1714_, v___x_1715_);
if (v___x_1716_ == 0)
{
return v_x_1712_;
}
else
{
uint8_t v___x_1717_; 
v___x_1717_ = lean_nat_dec_le(v___x_1715_, v___x_1715_);
if (v___x_1717_ == 0)
{
if (v___x_1716_ == 0)
{
return v_x_1712_;
}
else
{
size_t v___x_1718_; size_t v___x_1719_; lean_object* v___x_1720_; 
v___x_1718_ = ((size_t)0ULL);
v___x_1719_ = lean_usize_of_nat(v___x_1715_);
v___x_1720_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1710_, v_cs_1713_, v___x_1718_, v___x_1719_, v_x_1712_);
return v___x_1720_;
}
}
else
{
size_t v___x_1721_; size_t v___x_1722_; lean_object* v___x_1723_; 
v___x_1721_ = ((size_t)0ULL);
v___x_1722_ = lean_usize_of_nat(v___x_1715_);
v___x_1723_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1710_, v_cs_1713_, v___x_1721_, v___x_1722_, v_x_1712_);
return v___x_1723_;
}
}
}
else
{
lean_object* v_vs_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; uint8_t v___x_1727_; 
v_vs_1724_ = lean_ctor_get(v_x_1711_, 0);
v___x_1725_ = lean_unsigned_to_nat(0u);
v___x_1726_ = lean_array_get_size(v_vs_1724_);
v___x_1727_ = lean_nat_dec_lt(v___x_1725_, v___x_1726_);
if (v___x_1727_ == 0)
{
return v_x_1712_;
}
else
{
uint8_t v___x_1728_; 
v___x_1728_ = lean_nat_dec_le(v___x_1726_, v___x_1726_);
if (v___x_1728_ == 0)
{
if (v___x_1727_ == 0)
{
return v_x_1712_;
}
else
{
size_t v___x_1729_; size_t v___x_1730_; lean_object* v___x_1731_; 
v___x_1729_ = ((size_t)0ULL);
v___x_1730_ = lean_usize_of_nat(v___x_1726_);
v___x_1731_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1710_, v_vs_1724_, v___x_1729_, v___x_1730_, v_x_1712_);
return v___x_1731_;
}
}
else
{
size_t v___x_1732_; size_t v___x_1733_; lean_object* v___x_1734_; 
v___x_1732_ = ((size_t)0ULL);
v___x_1733_ = lean_usize_of_nat(v___x_1726_);
v___x_1734_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1710_, v_vs_1724_, v___x_1732_, v___x_1733_, v_x_1712_);
return v___x_1734_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(lean_object* v___x_1735_, lean_object* v_as_1736_, size_t v_i_1737_, size_t v_stop_1738_, lean_object* v_b_1739_){
_start:
{
uint8_t v___x_1740_; 
v___x_1740_ = lean_usize_dec_eq(v_i_1737_, v_stop_1738_);
if (v___x_1740_ == 0)
{
lean_object* v___x_1741_; lean_object* v___x_1742_; size_t v___x_1743_; size_t v___x_1744_; 
v___x_1741_ = lean_array_uget_borrowed(v_as_1736_, v_i_1737_);
v___x_1742_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(v___x_1735_, v___x_1741_, v_b_1739_);
v___x_1743_ = ((size_t)1ULL);
v___x_1744_ = lean_usize_add(v_i_1737_, v___x_1743_);
v_i_1737_ = v___x_1744_;
v_b_1739_ = v___x_1742_;
goto _start;
}
else
{
return v_b_1739_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v___x_1746_, lean_object* v_as_1747_, lean_object* v_i_1748_, lean_object* v_stop_1749_, lean_object* v_b_1750_){
_start:
{
size_t v_i_boxed_1751_; size_t v_stop_boxed_1752_; lean_object* v_res_1753_; 
v_i_boxed_1751_ = lean_unbox_usize(v_i_1748_);
lean_dec(v_i_1748_);
v_stop_boxed_1752_ = lean_unbox_usize(v_stop_1749_);
lean_dec(v_stop_1749_);
v_res_1753_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1746_, v_as_1747_, v_i_boxed_1751_, v_stop_boxed_1752_, v_b_1750_);
lean_dec_ref(v_as_1747_);
lean_dec_ref(v___x_1746_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2___boxed(lean_object* v___x_1754_, lean_object* v_x_1755_, lean_object* v_x_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(v___x_1754_, v_x_1755_, v_x_1756_);
lean_dec_ref(v_x_1755_);
lean_dec_ref(v___x_1754_);
return v_res_1757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(lean_object* v___x_1758_, lean_object* v_x_1759_, size_t v_x_1760_, size_t v_x_1761_, lean_object* v_x_1762_){
_start:
{
if (lean_obj_tag(v_x_1759_) == 0)
{
lean_object* v_cs_1763_; lean_object* v___x_1764_; size_t v___x_1765_; lean_object* v_j_1766_; lean_object* v___x_1767_; size_t v___x_1768_; size_t v___x_1769_; size_t v___x_1770_; size_t v___x_1771_; size_t v___x_1772_; size_t v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; uint8_t v___x_1778_; 
v_cs_1763_ = lean_ctor_get(v_x_1759_, 0);
v___x_1764_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0);
v___x_1765_ = lean_usize_shift_right(v_x_1760_, v_x_1761_);
v_j_1766_ = lean_usize_to_nat(v___x_1765_);
v___x_1767_ = lean_array_get_borrowed(v___x_1764_, v_cs_1763_, v_j_1766_);
v___x_1768_ = ((size_t)1ULL);
v___x_1769_ = lean_usize_shift_left(v___x_1768_, v_x_1761_);
v___x_1770_ = lean_usize_sub(v___x_1769_, v___x_1768_);
v___x_1771_ = lean_usize_land(v_x_1760_, v___x_1770_);
v___x_1772_ = ((size_t)5ULL);
v___x_1773_ = lean_usize_sub(v_x_1761_, v___x_1772_);
v___x_1774_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(v___x_1758_, v___x_1767_, v___x_1771_, v___x_1773_, v_x_1762_);
v___x_1775_ = lean_unsigned_to_nat(1u);
v___x_1776_ = lean_nat_add(v_j_1766_, v___x_1775_);
lean_dec(v_j_1766_);
v___x_1777_ = lean_array_get_size(v_cs_1763_);
v___x_1778_ = lean_nat_dec_lt(v___x_1776_, v___x_1777_);
if (v___x_1778_ == 0)
{
lean_dec(v___x_1776_);
return v___x_1774_;
}
else
{
uint8_t v___x_1779_; 
v___x_1779_ = lean_nat_dec_le(v___x_1777_, v___x_1777_);
if (v___x_1779_ == 0)
{
if (v___x_1778_ == 0)
{
lean_dec(v___x_1776_);
return v___x_1774_;
}
else
{
size_t v___x_1780_; size_t v___x_1781_; lean_object* v___x_1782_; 
v___x_1780_ = lean_usize_of_nat(v___x_1776_);
lean_dec(v___x_1776_);
v___x_1781_ = lean_usize_of_nat(v___x_1777_);
v___x_1782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1758_, v_cs_1763_, v___x_1780_, v___x_1781_, v___x_1774_);
return v___x_1782_;
}
}
else
{
size_t v___x_1783_; size_t v___x_1784_; lean_object* v___x_1785_; 
v___x_1783_ = lean_usize_of_nat(v___x_1776_);
lean_dec(v___x_1776_);
v___x_1784_ = lean_usize_of_nat(v___x_1777_);
v___x_1785_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1758_, v_cs_1763_, v___x_1783_, v___x_1784_, v___x_1774_);
return v___x_1785_;
}
}
}
else
{
lean_object* v_vs_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; uint8_t v___x_1789_; 
v_vs_1786_ = lean_ctor_get(v_x_1759_, 0);
v___x_1787_ = lean_usize_to_nat(v_x_1760_);
v___x_1788_ = lean_array_get_size(v_vs_1786_);
v___x_1789_ = lean_nat_dec_lt(v___x_1787_, v___x_1788_);
if (v___x_1789_ == 0)
{
lean_dec(v___x_1787_);
return v_x_1762_;
}
else
{
uint8_t v___x_1790_; 
v___x_1790_ = lean_nat_dec_le(v___x_1788_, v___x_1788_);
if (v___x_1790_ == 0)
{
if (v___x_1789_ == 0)
{
lean_dec(v___x_1787_);
return v_x_1762_;
}
else
{
size_t v___x_1791_; size_t v___x_1792_; lean_object* v___x_1793_; 
v___x_1791_ = lean_usize_of_nat(v___x_1787_);
lean_dec(v___x_1787_);
v___x_1792_ = lean_usize_of_nat(v___x_1788_);
v___x_1793_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1758_, v_vs_1786_, v___x_1791_, v___x_1792_, v_x_1762_);
return v___x_1793_;
}
}
else
{
size_t v___x_1794_; size_t v___x_1795_; lean_object* v___x_1796_; 
v___x_1794_ = lean_usize_of_nat(v___x_1787_);
lean_dec(v___x_1787_);
v___x_1795_ = lean_usize_of_nat(v___x_1788_);
v___x_1796_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1758_, v_vs_1786_, v___x_1794_, v___x_1795_, v_x_1762_);
return v___x_1796_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0___boxed(lean_object* v___x_1797_, lean_object* v_x_1798_, lean_object* v_x_1799_, lean_object* v_x_1800_, lean_object* v_x_1801_){
_start:
{
size_t v_x_21627__boxed_1802_; size_t v_x_21628__boxed_1803_; lean_object* v_res_1804_; 
v_x_21627__boxed_1802_ = lean_unbox_usize(v_x_1799_);
lean_dec(v_x_1799_);
v_x_21628__boxed_1803_ = lean_unbox_usize(v_x_1800_);
lean_dec(v_x_1800_);
v_res_1804_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(v___x_1797_, v_x_1798_, v_x_21627__boxed_1802_, v_x_21628__boxed_1803_, v_x_1801_);
lean_dec_ref(v_x_1798_);
lean_dec_ref(v___x_1797_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(lean_object* v___x_1805_, lean_object* v_t_1806_, lean_object* v_init_1807_, lean_object* v_start_1808_){
_start:
{
lean_object* v___x_1809_; uint8_t v___x_1810_; 
v___x_1809_ = lean_unsigned_to_nat(0u);
v___x_1810_ = lean_nat_dec_eq(v_start_1808_, v___x_1809_);
if (v___x_1810_ == 0)
{
lean_object* v_root_1811_; lean_object* v_tail_1812_; size_t v_shift_1813_; lean_object* v_tailOff_1814_; uint8_t v___x_1815_; 
v_root_1811_ = lean_ctor_get(v_t_1806_, 0);
v_tail_1812_ = lean_ctor_get(v_t_1806_, 1);
v_shift_1813_ = lean_ctor_get_usize(v_t_1806_, 4);
v_tailOff_1814_ = lean_ctor_get(v_t_1806_, 3);
v___x_1815_ = lean_nat_dec_le(v_tailOff_1814_, v_start_1808_);
if (v___x_1815_ == 0)
{
size_t v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; uint8_t v___x_1819_; 
v___x_1816_ = lean_usize_of_nat(v_start_1808_);
v___x_1817_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(v___x_1805_, v_root_1811_, v___x_1816_, v_shift_1813_, v_init_1807_);
v___x_1818_ = lean_array_get_size(v_tail_1812_);
v___x_1819_ = lean_nat_dec_lt(v___x_1809_, v___x_1818_);
if (v___x_1819_ == 0)
{
return v___x_1817_;
}
else
{
uint8_t v___x_1820_; 
v___x_1820_ = lean_nat_dec_le(v___x_1818_, v___x_1818_);
if (v___x_1820_ == 0)
{
if (v___x_1819_ == 0)
{
return v___x_1817_;
}
else
{
size_t v___x_1821_; size_t v___x_1822_; lean_object* v___x_1823_; 
v___x_1821_ = ((size_t)0ULL);
v___x_1822_ = lean_usize_of_nat(v___x_1818_);
v___x_1823_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1805_, v_tail_1812_, v___x_1821_, v___x_1822_, v___x_1817_);
return v___x_1823_;
}
}
else
{
size_t v___x_1824_; size_t v___x_1825_; lean_object* v___x_1826_; 
v___x_1824_ = ((size_t)0ULL);
v___x_1825_ = lean_usize_of_nat(v___x_1818_);
v___x_1826_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1805_, v_tail_1812_, v___x_1824_, v___x_1825_, v___x_1817_);
return v___x_1826_;
}
}
}
else
{
lean_object* v___x_1827_; lean_object* v___x_1828_; uint8_t v___x_1829_; 
v___x_1827_ = lean_nat_sub(v_start_1808_, v_tailOff_1814_);
v___x_1828_ = lean_array_get_size(v_tail_1812_);
v___x_1829_ = lean_nat_dec_lt(v___x_1827_, v___x_1828_);
if (v___x_1829_ == 0)
{
lean_dec(v___x_1827_);
return v_init_1807_;
}
else
{
uint8_t v___x_1830_; 
v___x_1830_ = lean_nat_dec_le(v___x_1828_, v___x_1828_);
if (v___x_1830_ == 0)
{
if (v___x_1829_ == 0)
{
lean_dec(v___x_1827_);
return v_init_1807_;
}
else
{
size_t v___x_1831_; size_t v___x_1832_; lean_object* v___x_1833_; 
v___x_1831_ = lean_usize_of_nat(v___x_1827_);
lean_dec(v___x_1827_);
v___x_1832_ = lean_usize_of_nat(v___x_1828_);
v___x_1833_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1805_, v_tail_1812_, v___x_1831_, v___x_1832_, v_init_1807_);
return v___x_1833_;
}
}
else
{
size_t v___x_1834_; size_t v___x_1835_; lean_object* v___x_1836_; 
v___x_1834_ = lean_usize_of_nat(v___x_1827_);
lean_dec(v___x_1827_);
v___x_1835_ = lean_usize_of_nat(v___x_1828_);
v___x_1836_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1805_, v_tail_1812_, v___x_1834_, v___x_1835_, v_init_1807_);
return v___x_1836_;
}
}
}
}
else
{
lean_object* v_root_1837_; lean_object* v_tail_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; uint8_t v___x_1841_; 
v_root_1837_ = lean_ctor_get(v_t_1806_, 0);
v_tail_1838_ = lean_ctor_get(v_t_1806_, 1);
v___x_1839_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(v___x_1805_, v_root_1837_, v_init_1807_);
v___x_1840_ = lean_array_get_size(v_tail_1838_);
v___x_1841_ = lean_nat_dec_lt(v___x_1809_, v___x_1840_);
if (v___x_1841_ == 0)
{
return v___x_1839_;
}
else
{
uint8_t v___x_1842_; 
v___x_1842_ = lean_nat_dec_le(v___x_1840_, v___x_1840_);
if (v___x_1842_ == 0)
{
if (v___x_1841_ == 0)
{
return v___x_1839_;
}
else
{
size_t v___x_1843_; size_t v___x_1844_; lean_object* v___x_1845_; 
v___x_1843_ = ((size_t)0ULL);
v___x_1844_ = lean_usize_of_nat(v___x_1840_);
v___x_1845_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1805_, v_tail_1838_, v___x_1843_, v___x_1844_, v___x_1839_);
return v___x_1845_;
}
}
else
{
size_t v___x_1846_; size_t v___x_1847_; lean_object* v___x_1848_; 
v___x_1846_ = ((size_t)0ULL);
v___x_1847_ = lean_usize_of_nat(v___x_1840_);
v___x_1848_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1805_, v_tail_1838_, v___x_1846_, v___x_1847_, v___x_1839_);
return v___x_1848_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0___boxed(lean_object* v___x_1849_, lean_object* v_t_1850_, lean_object* v_init_1851_, lean_object* v_start_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(v___x_1849_, v_t_1850_, v_init_1851_, v_start_1852_);
lean_dec(v_start_1852_);
lean_dec_ref(v_t_1850_);
lean_dec_ref(v___x_1849_);
return v_res_1853_;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1854_ = lean_unsigned_to_nat(32u);
v___x_1855_ = lean_mk_empty_array_with_capacity(v___x_1854_);
v___x_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
return v___x_1856_;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1(void){
_start:
{
size_t v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1857_ = ((size_t)5ULL);
v___x_1858_ = lean_unsigned_to_nat(0u);
v___x_1859_ = lean_unsigned_to_nat(32u);
v___x_1860_ = lean_mk_empty_array_with_capacity(v___x_1859_);
v___x_1861_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0);
v___x_1862_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1862_, 0, v___x_1861_);
lean_ctor_set(v___x_1862_, 1, v___x_1860_);
lean_ctor_set(v___x_1862_, 2, v___x_1858_);
lean_ctor_set(v___x_1862_, 3, v___x_1858_);
lean_ctor_set_usize(v___x_1862_, 4, v___x_1857_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(lean_object* v___x_1863_, lean_object* v_x_1864_, size_t v_x_1865_, size_t v_x_1866_){
_start:
{
if (lean_obj_tag(v_x_1864_) == 0)
{
lean_object* v_cs_1867_; size_t v_j_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; uint8_t v___x_1871_; 
v_cs_1867_ = lean_ctor_get(v_x_1864_, 0);
v_j_1868_ = lean_usize_shift_right(v_x_1865_, v_x_1866_);
v___x_1869_ = lean_usize_to_nat(v_j_1868_);
v___x_1870_ = lean_array_get_size(v_cs_1867_);
v___x_1871_ = lean_nat_dec_lt(v___x_1869_, v___x_1870_);
if (v___x_1871_ == 0)
{
lean_dec(v___x_1869_);
return v_x_1864_;
}
else
{
lean_object* v___x_1873_; uint8_t v_isShared_1874_; uint8_t v_isSharedCheck_1889_; 
lean_inc_ref(v_cs_1867_);
v_isSharedCheck_1889_ = !lean_is_exclusive(v_x_1864_);
if (v_isSharedCheck_1889_ == 0)
{
lean_object* v_unused_1890_; 
v_unused_1890_ = lean_ctor_get(v_x_1864_, 0);
lean_dec(v_unused_1890_);
v___x_1873_ = v_x_1864_;
v_isShared_1874_ = v_isSharedCheck_1889_;
goto v_resetjp_1872_;
}
else
{
lean_dec(v_x_1864_);
v___x_1873_ = lean_box(0);
v_isShared_1874_ = v_isSharedCheck_1889_;
goto v_resetjp_1872_;
}
v_resetjp_1872_:
{
size_t v___x_1875_; size_t v___x_1876_; size_t v___x_1877_; size_t v_i_1878_; size_t v___x_1879_; size_t v_shift_1880_; lean_object* v_v_1881_; lean_object* v___x_1882_; lean_object* v_xs_x27_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1887_; 
v___x_1875_ = ((size_t)1ULL);
v___x_1876_ = lean_usize_shift_left(v___x_1875_, v_x_1866_);
v___x_1877_ = lean_usize_sub(v___x_1876_, v___x_1875_);
v_i_1878_ = lean_usize_land(v_x_1865_, v___x_1877_);
v___x_1879_ = ((size_t)5ULL);
v_shift_1880_ = lean_usize_sub(v_x_1866_, v___x_1879_);
v_v_1881_ = lean_array_fget(v_cs_1867_, v___x_1869_);
v___x_1882_ = lean_box(0);
v_xs_x27_1883_ = lean_array_fset(v_cs_1867_, v___x_1869_, v___x_1882_);
v___x_1884_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(v___x_1863_, v_v_1881_, v_i_1878_, v_shift_1880_);
v___x_1885_ = lean_array_fset(v_xs_x27_1883_, v___x_1869_, v___x_1884_);
lean_dec(v___x_1869_);
if (v_isShared_1874_ == 0)
{
lean_ctor_set(v___x_1873_, 0, v___x_1885_);
v___x_1887_ = v___x_1873_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v___x_1885_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
return v___x_1887_;
}
}
}
}
else
{
lean_object* v_vs_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; uint8_t v___x_1894_; 
v_vs_1891_ = lean_ctor_get(v_x_1864_, 0);
v___x_1892_ = lean_usize_to_nat(v_x_1865_);
v___x_1893_ = lean_array_get_size(v_vs_1891_);
v___x_1894_ = lean_nat_dec_lt(v___x_1892_, v___x_1893_);
if (v___x_1894_ == 0)
{
lean_dec(v___x_1892_);
return v_x_1864_;
}
else
{
lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1908_; 
lean_inc_ref(v_vs_1891_);
v_isSharedCheck_1908_ = !lean_is_exclusive(v_x_1864_);
if (v_isSharedCheck_1908_ == 0)
{
lean_object* v_unused_1909_; 
v_unused_1909_ = lean_ctor_get(v_x_1864_, 0);
lean_dec(v_unused_1909_);
v___x_1896_ = v_x_1864_;
v_isShared_1897_ = v_isSharedCheck_1908_;
goto v_resetjp_1895_;
}
else
{
lean_dec(v_x_1864_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1908_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v_v_1898_; lean_object* v___x_1899_; lean_object* v_xs_x27_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1906_; 
v_v_1898_ = lean_array_fget(v_vs_1891_, v___x_1892_);
v___x_1899_ = lean_box(0);
v_xs_x27_1900_ = lean_array_fset(v_vs_1891_, v___x_1892_, v___x_1899_);
v___x_1901_ = lean_unsigned_to_nat(0u);
v___x_1902_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1);
v___x_1903_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(v___x_1863_, v_v_1898_, v___x_1902_, v___x_1901_);
lean_dec(v_v_1898_);
v___x_1904_ = lean_array_fset(v_xs_x27_1900_, v___x_1892_, v___x_1903_);
lean_dec(v___x_1892_);
if (v_isShared_1897_ == 0)
{
lean_ctor_set(v___x_1896_, 0, v___x_1904_);
v___x_1906_ = v___x_1896_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1907_; 
v_reuseFailAlloc_1907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1907_, 0, v___x_1904_);
v___x_1906_ = v_reuseFailAlloc_1907_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
return v___x_1906_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___boxed(lean_object* v___x_1910_, lean_object* v_x_1911_, lean_object* v_x_1912_, lean_object* v_x_1913_){
_start:
{
size_t v_x_21799__boxed_1914_; size_t v_x_21800__boxed_1915_; lean_object* v_res_1916_; 
v_x_21799__boxed_1914_ = lean_unbox_usize(v_x_1912_);
lean_dec(v_x_1912_);
v_x_21800__boxed_1915_ = lean_unbox_usize(v_x_1913_);
lean_dec(v_x_1913_);
v_res_1916_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(v___x_1910_, v_x_1911_, v_x_21799__boxed_1914_, v_x_21800__boxed_1915_);
lean_dec_ref(v___x_1910_);
return v_res_1916_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1(lean_object* v___x_1917_, lean_object* v_t_1918_, lean_object* v_i_1919_){
_start:
{
lean_object* v_root_1920_; lean_object* v_tail_1921_; lean_object* v_size_1922_; size_t v_shift_1923_; lean_object* v_tailOff_1924_; lean_object* v___x_1926_; uint8_t v_isShared_1927_; uint8_t v_isSharedCheck_1952_; 
v_root_1920_ = lean_ctor_get(v_t_1918_, 0);
v_tail_1921_ = lean_ctor_get(v_t_1918_, 1);
v_size_1922_ = lean_ctor_get(v_t_1918_, 2);
v_shift_1923_ = lean_ctor_get_usize(v_t_1918_, 4);
v_tailOff_1924_ = lean_ctor_get(v_t_1918_, 3);
v_isSharedCheck_1952_ = !lean_is_exclusive(v_t_1918_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1926_ = v_t_1918_;
v_isShared_1927_ = v_isSharedCheck_1952_;
goto v_resetjp_1925_;
}
else
{
lean_inc(v_tailOff_1924_);
lean_inc(v_size_1922_);
lean_inc(v_tail_1921_);
lean_inc(v_root_1920_);
lean_dec(v_t_1918_);
v___x_1926_ = lean_box(0);
v_isShared_1927_ = v_isSharedCheck_1952_;
goto v_resetjp_1925_;
}
v_resetjp_1925_:
{
uint8_t v___x_1928_; 
v___x_1928_ = lean_nat_dec_le(v_tailOff_1924_, v_i_1919_);
if (v___x_1928_ == 0)
{
size_t v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1932_; 
v___x_1929_ = lean_usize_of_nat(v_i_1919_);
v___x_1930_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(v___x_1917_, v_root_1920_, v___x_1929_, v_shift_1923_);
if (v_isShared_1927_ == 0)
{
lean_ctor_set(v___x_1926_, 0, v___x_1930_);
v___x_1932_ = v___x_1926_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v___x_1930_);
lean_ctor_set(v_reuseFailAlloc_1933_, 1, v_tail_1921_);
lean_ctor_set(v_reuseFailAlloc_1933_, 2, v_size_1922_);
lean_ctor_set(v_reuseFailAlloc_1933_, 3, v_tailOff_1924_);
lean_ctor_set_usize(v_reuseFailAlloc_1933_, 4, v_shift_1923_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
}
}
else
{
lean_object* v___x_1934_; lean_object* v___x_1935_; uint8_t v___x_1936_; 
v___x_1934_ = lean_nat_sub(v_i_1919_, v_tailOff_1924_);
v___x_1935_ = lean_array_get_size(v_tail_1921_);
v___x_1936_ = lean_nat_dec_lt(v___x_1934_, v___x_1935_);
if (v___x_1936_ == 0)
{
lean_object* v___x_1938_; 
lean_dec(v___x_1934_);
if (v_isShared_1927_ == 0)
{
v___x_1938_ = v___x_1926_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_root_1920_);
lean_ctor_set(v_reuseFailAlloc_1939_, 1, v_tail_1921_);
lean_ctor_set(v_reuseFailAlloc_1939_, 2, v_size_1922_);
lean_ctor_set(v_reuseFailAlloc_1939_, 3, v_tailOff_1924_);
lean_ctor_set_usize(v_reuseFailAlloc_1939_, 4, v_shift_1923_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
else
{
lean_object* v_v_1940_; lean_object* v___x_1941_; lean_object* v_xs_x27_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1950_; 
v_v_1940_ = lean_array_fget(v_tail_1921_, v___x_1934_);
v___x_1941_ = lean_box(0);
v_xs_x27_1942_ = lean_array_fset(v_tail_1921_, v___x_1934_, v___x_1941_);
v___x_1943_ = lean_unsigned_to_nat(32u);
v___x_1944_ = lean_mk_empty_array_with_capacity(v___x_1943_);
lean_dec_ref(v___x_1944_);
v___x_1945_ = lean_unsigned_to_nat(0u);
v___x_1946_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1);
v___x_1947_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(v___x_1917_, v_v_1940_, v___x_1946_, v___x_1945_);
lean_dec(v_v_1940_);
v___x_1948_ = lean_array_fset(v_xs_x27_1942_, v___x_1934_, v___x_1947_);
lean_dec(v___x_1934_);
if (v_isShared_1927_ == 0)
{
lean_ctor_set(v___x_1926_, 1, v___x_1948_);
v___x_1950_ = v___x_1926_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_root_1920_);
lean_ctor_set(v_reuseFailAlloc_1951_, 1, v___x_1948_);
lean_ctor_set(v_reuseFailAlloc_1951_, 2, v_size_1922_);
lean_ctor_set(v_reuseFailAlloc_1951_, 3, v_tailOff_1924_);
lean_ctor_set_usize(v_reuseFailAlloc_1951_, 4, v_shift_1923_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1___boxed(lean_object* v___x_1953_, lean_object* v_t_1954_, lean_object* v_i_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1(v___x_1953_, v_t_1954_, v_i_1955_);
lean_dec(v_i_1955_);
lean_dec_ref(v___x_1953_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0(lean_object* v_p_1957_, lean_object* v_x_1958_, lean_object* v_s_1959_){
_start:
{
lean_object* v_vars_1960_; lean_object* v_varMap_1961_; lean_object* v_vars_x27_1962_; lean_object* v_varMap_x27_1963_; lean_object* v_natToIntMap_1964_; lean_object* v_natDef_1965_; lean_object* v_dvds_1966_; lean_object* v_lowers_1967_; lean_object* v_uppers_1968_; lean_object* v_diseqs_1969_; lean_object* v_elimEqs_1970_; lean_object* v_elimStack_1971_; lean_object* v_occurs_1972_; lean_object* v_assignment_1973_; lean_object* v_nextCnstrId_1974_; uint8_t v_caseSplits_1975_; lean_object* v_conflict_x3f_1976_; lean_object* v_diseqSplits_1977_; lean_object* v_divMod_1978_; lean_object* v_toIntIds_1979_; lean_object* v_toIntInfos_1980_; lean_object* v_toIntTermMap_1981_; lean_object* v_toIntVarMap_1982_; uint8_t v_usedCommRing_1983_; lean_object* v_nonlinearOccs_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1992_; 
v_vars_1960_ = lean_ctor_get(v_s_1959_, 0);
v_varMap_1961_ = lean_ctor_get(v_s_1959_, 1);
v_vars_x27_1962_ = lean_ctor_get(v_s_1959_, 2);
v_varMap_x27_1963_ = lean_ctor_get(v_s_1959_, 3);
v_natToIntMap_1964_ = lean_ctor_get(v_s_1959_, 4);
v_natDef_1965_ = lean_ctor_get(v_s_1959_, 5);
v_dvds_1966_ = lean_ctor_get(v_s_1959_, 6);
v_lowers_1967_ = lean_ctor_get(v_s_1959_, 7);
v_uppers_1968_ = lean_ctor_get(v_s_1959_, 8);
v_diseqs_1969_ = lean_ctor_get(v_s_1959_, 9);
v_elimEqs_1970_ = lean_ctor_get(v_s_1959_, 10);
v_elimStack_1971_ = lean_ctor_get(v_s_1959_, 11);
v_occurs_1972_ = lean_ctor_get(v_s_1959_, 12);
v_assignment_1973_ = lean_ctor_get(v_s_1959_, 13);
v_nextCnstrId_1974_ = lean_ctor_get(v_s_1959_, 14);
v_caseSplits_1975_ = lean_ctor_get_uint8(v_s_1959_, sizeof(void*)*23);
v_conflict_x3f_1976_ = lean_ctor_get(v_s_1959_, 15);
v_diseqSplits_1977_ = lean_ctor_get(v_s_1959_, 16);
v_divMod_1978_ = lean_ctor_get(v_s_1959_, 17);
v_toIntIds_1979_ = lean_ctor_get(v_s_1959_, 18);
v_toIntInfos_1980_ = lean_ctor_get(v_s_1959_, 19);
v_toIntTermMap_1981_ = lean_ctor_get(v_s_1959_, 20);
v_toIntVarMap_1982_ = lean_ctor_get(v_s_1959_, 21);
v_usedCommRing_1983_ = lean_ctor_get_uint8(v_s_1959_, sizeof(void*)*23 + 1);
v_nonlinearOccs_1984_ = lean_ctor_get(v_s_1959_, 22);
v_isSharedCheck_1992_ = !lean_is_exclusive(v_s_1959_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1986_ = v_s_1959_;
v_isShared_1987_ = v_isSharedCheck_1992_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_nonlinearOccs_1984_);
lean_inc(v_toIntVarMap_1982_);
lean_inc(v_toIntTermMap_1981_);
lean_inc(v_toIntInfos_1980_);
lean_inc(v_toIntIds_1979_);
lean_inc(v_divMod_1978_);
lean_inc(v_diseqSplits_1977_);
lean_inc(v_conflict_x3f_1976_);
lean_inc(v_nextCnstrId_1974_);
lean_inc(v_assignment_1973_);
lean_inc(v_occurs_1972_);
lean_inc(v_elimStack_1971_);
lean_inc(v_elimEqs_1970_);
lean_inc(v_diseqs_1969_);
lean_inc(v_uppers_1968_);
lean_inc(v_lowers_1967_);
lean_inc(v_dvds_1966_);
lean_inc(v_natDef_1965_);
lean_inc(v_natToIntMap_1964_);
lean_inc(v_varMap_x27_1963_);
lean_inc(v_vars_x27_1962_);
lean_inc(v_varMap_1961_);
lean_inc(v_vars_1960_);
lean_dec(v_s_1959_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1992_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1988_; lean_object* v___x_1990_; 
v___x_1988_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1(v_p_1957_, v_diseqs_1969_, v_x_1958_);
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 9, v___x_1988_);
v___x_1990_ = v___x_1986_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_vars_1960_);
lean_ctor_set(v_reuseFailAlloc_1991_, 1, v_varMap_1961_);
lean_ctor_set(v_reuseFailAlloc_1991_, 2, v_vars_x27_1962_);
lean_ctor_set(v_reuseFailAlloc_1991_, 3, v_varMap_x27_1963_);
lean_ctor_set(v_reuseFailAlloc_1991_, 4, v_natToIntMap_1964_);
lean_ctor_set(v_reuseFailAlloc_1991_, 5, v_natDef_1965_);
lean_ctor_set(v_reuseFailAlloc_1991_, 6, v_dvds_1966_);
lean_ctor_set(v_reuseFailAlloc_1991_, 7, v_lowers_1967_);
lean_ctor_set(v_reuseFailAlloc_1991_, 8, v_uppers_1968_);
lean_ctor_set(v_reuseFailAlloc_1991_, 9, v___x_1988_);
lean_ctor_set(v_reuseFailAlloc_1991_, 10, v_elimEqs_1970_);
lean_ctor_set(v_reuseFailAlloc_1991_, 11, v_elimStack_1971_);
lean_ctor_set(v_reuseFailAlloc_1991_, 12, v_occurs_1972_);
lean_ctor_set(v_reuseFailAlloc_1991_, 13, v_assignment_1973_);
lean_ctor_set(v_reuseFailAlloc_1991_, 14, v_nextCnstrId_1974_);
lean_ctor_set(v_reuseFailAlloc_1991_, 15, v_conflict_x3f_1976_);
lean_ctor_set(v_reuseFailAlloc_1991_, 16, v_diseqSplits_1977_);
lean_ctor_set(v_reuseFailAlloc_1991_, 17, v_divMod_1978_);
lean_ctor_set(v_reuseFailAlloc_1991_, 18, v_toIntIds_1979_);
lean_ctor_set(v_reuseFailAlloc_1991_, 19, v_toIntInfos_1980_);
lean_ctor_set(v_reuseFailAlloc_1991_, 20, v_toIntTermMap_1981_);
lean_ctor_set(v_reuseFailAlloc_1991_, 21, v_toIntVarMap_1982_);
lean_ctor_set(v_reuseFailAlloc_1991_, 22, v_nonlinearOccs_1984_);
lean_ctor_set_uint8(v_reuseFailAlloc_1991_, sizeof(void*)*23, v_caseSplits_1975_);
lean_ctor_set_uint8(v_reuseFailAlloc_1991_, sizeof(void*)*23 + 1, v_usedCommRing_1983_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed(lean_object* v_p_1993_, lean_object* v_x_1994_, lean_object* v_s_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0(v_p_1993_, v_x_1994_, v_s_1995_);
lean_dec(v_x_1994_);
lean_dec_ref(v_p_1993_);
return v_res_1996_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_2003_; lean_object* v___x_2004_; 
v___x_2003_ = lean_unsigned_to_nat(1u);
v___x_2004_ = lean_nat_to_int(v___x_2003_);
return v___x_2004_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(lean_object* v_c_2005_, lean_object* v_x_2006_, lean_object* v_as_2007_, size_t v_sz_2008_, size_t v_i_2009_, lean_object* v_b_2010_, lean_object* v___y_2011_){
_start:
{
uint8_t v___x_2013_; 
v___x_2013_ = lean_usize_dec_lt(v_i_2009_, v_sz_2008_);
if (v___x_2013_ == 0)
{
lean_object* v___x_2014_; 
lean_dec(v_x_2006_);
lean_dec_ref(v_c_2005_);
v___x_2014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2014_, 0, v_b_2010_);
return v___x_2014_;
}
else
{
lean_object* v_snd_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2061_; 
v_snd_2015_ = lean_ctor_get(v_b_2010_, 1);
v_isSharedCheck_2061_ = !lean_is_exclusive(v_b_2010_);
if (v_isSharedCheck_2061_ == 0)
{
lean_object* v_unused_2062_; 
v_unused_2062_ = lean_ctor_get(v_b_2010_, 0);
lean_dec(v_unused_2062_);
v___x_2017_ = v_b_2010_;
v_isShared_2018_ = v_isSharedCheck_2061_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_snd_2015_);
lean_dec(v_b_2010_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2061_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v_p_2019_; lean_object* v_a_2020_; lean_object* v_p_2021_; lean_object* v___x_2022_; lean_object* v___f_2023_; uint8_t v___y_2025_; uint8_t v___x_2059_; 
v_p_2019_ = lean_ctor_get(v_c_2005_, 0);
v_a_2020_ = lean_array_uget_borrowed(v_as_2007_, v_i_2009_);
v_p_2021_ = lean_ctor_get(v_a_2020_, 0);
v___x_2022_ = lean_box(0);
lean_inc(v_x_2006_);
lean_inc_ref(v_p_2021_);
v___f_2023_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2023_, 0, v_p_2021_);
lean_closure_set(v___f_2023_, 1, v_x_2006_);
v___x_2059_ = l_Int_Linear_instBEqPoly_beq(v_p_2019_, v_p_2021_);
if (v___x_2059_ == 0)
{
uint8_t v___x_2060_; 
v___x_2060_ = l_Int_Linear_Poly_isNegEq(v_p_2019_, v_p_2021_);
v___y_2025_ = v___x_2060_;
goto v___jp_2024_;
}
else
{
v___y_2025_ = v___x_2059_;
goto v___jp_2024_;
}
v___jp_2024_:
{
if (v___y_2025_ == 0)
{
lean_object* v___x_2026_; size_t v___x_2027_; size_t v___x_2028_; 
lean_dec_ref(v___f_2023_);
lean_del_object(v___x_2017_);
lean_dec(v_snd_2015_);
v___x_2026_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__1));
v___x_2027_ = ((size_t)1ULL);
v___x_2028_ = lean_usize_add(v_i_2009_, v___x_2027_);
v_i_2009_ = v___x_2028_;
v_b_2010_ = v___x_2026_;
goto _start;
}
else
{
lean_object* v___x_2030_; lean_object* v___x_2031_; 
lean_dec(v_x_2006_);
v___x_2030_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2031_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2030_, v___f_2023_, v___y_2011_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2049_; 
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2049_ == 0)
{
lean_object* v_unused_2050_; 
v_unused_2050_ = lean_ctor_get(v___x_2031_, 0);
lean_dec(v_unused_2050_);
v___x_2033_ = v___x_2031_;
v_isShared_2034_ = v_isSharedCheck_2049_;
goto v_resetjp_2032_;
}
else
{
lean_dec(v___x_2031_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2049_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2042_; 
v___x_2035_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
lean_inc_ref(v_p_2019_);
v___x_2036_ = l_Int_Linear_Poly_addConst(v_p_2019_, v___x_2035_);
lean_inc(v_a_2020_);
v___x_2037_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_2037_, 0, v_c_2005_);
lean_ctor_set(v___x_2037_, 1, v_a_2020_);
v___x_2038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2036_);
lean_ctor_set(v___x_2038_, 1, v___x_2037_);
v___x_2039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2038_);
v___x_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2039_);
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 1, v___x_2022_);
lean_ctor_set(v___x_2017_, 0, v___x_2040_);
v___x_2042_ = v___x_2017_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2040_);
lean_ctor_set(v_reuseFailAlloc_2048_, 1, v___x_2022_);
v___x_2042_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2046_; 
v___x_2043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2043_, 0, v___x_2042_);
v___x_2044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2043_);
lean_ctor_set(v___x_2044_, 1, v_snd_2015_);
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 0, v___x_2044_);
v___x_2046_ = v___x_2033_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v___x_2044_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
lean_del_object(v___x_2017_);
lean_dec(v_snd_2015_);
lean_dec_ref(v_c_2005_);
v_a_2051_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_2031_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2031_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___boxed(lean_object* v_c_2063_, lean_object* v_x_2064_, lean_object* v_as_2065_, lean_object* v_sz_2066_, lean_object* v_i_2067_, lean_object* v_b_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_){
_start:
{
size_t v_sz_boxed_2071_; size_t v_i_boxed_2072_; lean_object* v_res_2073_; 
v_sz_boxed_2071_ = lean_unbox_usize(v_sz_2066_);
lean_dec(v_sz_2066_);
v_i_boxed_2072_ = lean_unbox_usize(v_i_2067_);
lean_dec(v_i_2067_);
v_res_2073_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(v_c_2063_, v_x_2064_, v_as_2065_, v_sz_boxed_2071_, v_i_boxed_2072_, v_b_2068_, v___y_2069_);
lean_dec(v___y_2069_);
lean_dec_ref(v_as_2065_);
return v_res_2073_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7(lean_object* v_c_2080_, lean_object* v_x_2081_, lean_object* v_as_2082_, size_t v_sz_2083_, size_t v_i_2084_, lean_object* v_b_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_){
_start:
{
uint8_t v___x_2097_; 
v___x_2097_ = lean_usize_dec_lt(v_i_2084_, v_sz_2083_);
if (v___x_2097_ == 0)
{
lean_object* v___x_2098_; 
lean_dec(v_x_2081_);
lean_dec_ref(v_c_2080_);
v___x_2098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2098_, 0, v_b_2085_);
return v___x_2098_;
}
else
{
lean_object* v_snd_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2145_; 
v_snd_2099_ = lean_ctor_get(v_b_2085_, 1);
v_isSharedCheck_2145_ = !lean_is_exclusive(v_b_2085_);
if (v_isSharedCheck_2145_ == 0)
{
lean_object* v_unused_2146_; 
v_unused_2146_ = lean_ctor_get(v_b_2085_, 0);
lean_dec(v_unused_2146_);
v___x_2101_ = v_b_2085_;
v_isShared_2102_ = v_isSharedCheck_2145_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_snd_2099_);
lean_dec(v_b_2085_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2145_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v_p_2103_; lean_object* v_a_2104_; lean_object* v_p_2105_; lean_object* v___x_2106_; lean_object* v___f_2107_; uint8_t v___y_2109_; uint8_t v___x_2143_; 
v_p_2103_ = lean_ctor_get(v_c_2080_, 0);
v_a_2104_ = lean_array_uget_borrowed(v_as_2082_, v_i_2084_);
v_p_2105_ = lean_ctor_get(v_a_2104_, 0);
v___x_2106_ = lean_box(0);
lean_inc(v_x_2081_);
lean_inc_ref(v_p_2105_);
v___f_2107_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2107_, 0, v_p_2105_);
lean_closure_set(v___f_2107_, 1, v_x_2081_);
v___x_2143_ = l_Int_Linear_instBEqPoly_beq(v_p_2103_, v_p_2105_);
if (v___x_2143_ == 0)
{
uint8_t v___x_2144_; 
v___x_2144_ = l_Int_Linear_Poly_isNegEq(v_p_2103_, v_p_2105_);
v___y_2109_ = v___x_2144_;
goto v___jp_2108_;
}
else
{
v___y_2109_ = v___x_2143_;
goto v___jp_2108_;
}
v___jp_2108_:
{
if (v___y_2109_ == 0)
{
lean_object* v___x_2110_; size_t v___x_2111_; size_t v___x_2112_; lean_object* v___x_2113_; 
lean_dec_ref(v___f_2107_);
lean_del_object(v___x_2101_);
lean_dec(v_snd_2099_);
v___x_2110_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___closed__1));
v___x_2111_ = ((size_t)1ULL);
v___x_2112_ = lean_usize_add(v_i_2084_, v___x_2111_);
v___x_2113_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(v_c_2080_, v_x_2081_, v_as_2082_, v_sz_2083_, v___x_2112_, v___x_2110_, v___y_2086_);
return v___x_2113_;
}
else
{
lean_object* v___x_2114_; lean_object* v___x_2115_; 
lean_dec(v_x_2081_);
v___x_2114_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2115_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2114_, v___f_2107_, v___y_2086_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v___x_2117_; uint8_t v_isShared_2118_; uint8_t v_isSharedCheck_2133_; 
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2133_ == 0)
{
lean_object* v_unused_2134_; 
v_unused_2134_ = lean_ctor_get(v___x_2115_, 0);
lean_dec(v_unused_2134_);
v___x_2117_ = v___x_2115_;
v_isShared_2118_ = v_isSharedCheck_2133_;
goto v_resetjp_2116_;
}
else
{
lean_dec(v___x_2115_);
v___x_2117_ = lean_box(0);
v_isShared_2118_ = v_isSharedCheck_2133_;
goto v_resetjp_2116_;
}
v_resetjp_2116_:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2126_; 
v___x_2119_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
lean_inc_ref(v_p_2103_);
v___x_2120_ = l_Int_Linear_Poly_addConst(v_p_2103_, v___x_2119_);
lean_inc(v_a_2104_);
v___x_2121_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_2121_, 0, v_c_2080_);
lean_ctor_set(v___x_2121_, 1, v_a_2104_);
v___x_2122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2120_);
lean_ctor_set(v___x_2122_, 1, v___x_2121_);
v___x_2123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2122_);
v___x_2124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2123_);
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 1, v___x_2106_);
lean_ctor_set(v___x_2101_, 0, v___x_2124_);
v___x_2126_ = v___x_2101_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v___x_2124_);
lean_ctor_set(v_reuseFailAlloc_2132_, 1, v___x_2106_);
v___x_2126_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2130_; 
v___x_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2126_);
v___x_2128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2128_, 0, v___x_2127_);
lean_ctor_set(v___x_2128_, 1, v_snd_2099_);
if (v_isShared_2118_ == 0)
{
lean_ctor_set(v___x_2117_, 0, v___x_2128_);
v___x_2130_ = v___x_2117_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v___x_2128_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
}
}
else
{
lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2142_; 
lean_del_object(v___x_2101_);
lean_dec(v_snd_2099_);
lean_dec_ref(v_c_2080_);
v_a_2135_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2137_ = v___x_2115_;
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2115_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2140_; 
if (v_isShared_2138_ == 0)
{
v___x_2140_ = v___x_2137_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_a_2135_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
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
lean_object* v_c_2147_ = _args[0];
lean_object* v_x_2148_ = _args[1];
lean_object* v_as_2149_ = _args[2];
lean_object* v_sz_2150_ = _args[3];
lean_object* v_i_2151_ = _args[4];
lean_object* v_b_2152_ = _args[5];
lean_object* v___y_2153_ = _args[6];
lean_object* v___y_2154_ = _args[7];
lean_object* v___y_2155_ = _args[8];
lean_object* v___y_2156_ = _args[9];
lean_object* v___y_2157_ = _args[10];
lean_object* v___y_2158_ = _args[11];
lean_object* v___y_2159_ = _args[12];
lean_object* v___y_2160_ = _args[13];
lean_object* v___y_2161_ = _args[14];
lean_object* v___y_2162_ = _args[15];
lean_object* v___y_2163_ = _args[16];
_start:
{
size_t v_sz_boxed_2164_; size_t v_i_boxed_2165_; lean_object* v_res_2166_; 
v_sz_boxed_2164_ = lean_unbox_usize(v_sz_2150_);
lean_dec(v_sz_2150_);
v_i_boxed_2165_ = lean_unbox_usize(v_i_2151_);
lean_dec(v_i_2151_);
v_res_2166_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7(v_c_2147_, v_x_2148_, v_as_2149_, v_sz_boxed_2164_, v_i_boxed_2165_, v_b_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_, v___y_2161_, v___y_2162_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec(v___y_2154_);
lean_dec(v___y_2153_);
lean_dec_ref(v_as_2149_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(lean_object* v_c_2173_, lean_object* v_x_2174_, lean_object* v_as_2175_, size_t v_sz_2176_, size_t v_i_2177_, lean_object* v_b_2178_, lean_object* v___y_2179_){
_start:
{
uint8_t v___x_2181_; 
v___x_2181_ = lean_usize_dec_lt(v_i_2177_, v_sz_2176_);
if (v___x_2181_ == 0)
{
lean_object* v___x_2182_; 
lean_dec(v_x_2174_);
lean_dec_ref(v_c_2173_);
v___x_2182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2182_, 0, v_b_2178_);
return v___x_2182_;
}
else
{
lean_object* v_snd_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2230_; 
v_snd_2183_ = lean_ctor_get(v_b_2178_, 1);
v_isSharedCheck_2230_ = !lean_is_exclusive(v_b_2178_);
if (v_isSharedCheck_2230_ == 0)
{
lean_object* v_unused_2231_; 
v_unused_2231_ = lean_ctor_get(v_b_2178_, 0);
lean_dec(v_unused_2231_);
v___x_2185_ = v_b_2178_;
v_isShared_2186_ = v_isSharedCheck_2230_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_snd_2183_);
lean_dec(v_b_2178_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2230_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v_p_2187_; lean_object* v_a_2188_; lean_object* v_p_2189_; lean_object* v___x_2190_; lean_object* v___f_2191_; uint8_t v___y_2193_; uint8_t v___x_2228_; 
v_p_2187_ = lean_ctor_get(v_c_2173_, 0);
v_a_2188_ = lean_array_uget_borrowed(v_as_2175_, v_i_2177_);
v_p_2189_ = lean_ctor_get(v_a_2188_, 0);
v___x_2190_ = lean_box(0);
lean_inc(v_x_2174_);
lean_inc_ref(v_p_2189_);
v___f_2191_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2191_, 0, v_p_2189_);
lean_closure_set(v___f_2191_, 1, v_x_2174_);
v___x_2228_ = l_Int_Linear_instBEqPoly_beq(v_p_2187_, v_p_2189_);
if (v___x_2228_ == 0)
{
uint8_t v___x_2229_; 
v___x_2229_ = l_Int_Linear_Poly_isNegEq(v_p_2187_, v_p_2189_);
v___y_2193_ = v___x_2229_;
goto v___jp_2192_;
}
else
{
v___y_2193_ = v___x_2228_;
goto v___jp_2192_;
}
v___jp_2192_:
{
if (v___y_2193_ == 0)
{
lean_object* v___x_2194_; size_t v___x_2195_; size_t v___x_2196_; 
lean_dec_ref(v___f_2191_);
lean_del_object(v___x_2185_);
lean_dec(v_snd_2183_);
v___x_2194_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg___closed__1));
v___x_2195_ = ((size_t)1ULL);
v___x_2196_ = lean_usize_add(v_i_2177_, v___x_2195_);
v_i_2177_ = v___x_2196_;
v_b_2178_ = v___x_2194_;
goto _start;
}
else
{
lean_object* v___x_2198_; lean_object* v___x_2199_; 
lean_dec(v_x_2174_);
v___x_2198_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2199_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2198_, v___f_2191_, v___y_2179_);
if (lean_obj_tag(v___x_2199_) == 0)
{
lean_object* v___x_2201_; uint8_t v_isShared_2202_; uint8_t v_isSharedCheck_2218_; 
v_isSharedCheck_2218_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2218_ == 0)
{
lean_object* v_unused_2219_; 
v_unused_2219_ = lean_ctor_get(v___x_2199_, 0);
lean_dec(v_unused_2219_);
v___x_2201_ = v___x_2199_;
v_isShared_2202_ = v_isSharedCheck_2218_;
goto v_resetjp_2200_;
}
else
{
lean_dec(v___x_2199_);
v___x_2201_ = lean_box(0);
v_isShared_2202_ = v_isSharedCheck_2218_;
goto v_resetjp_2200_;
}
v_resetjp_2200_:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2210_; 
v___x_2203_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
lean_inc_ref(v_p_2187_);
v___x_2204_ = l_Int_Linear_Poly_addConst(v_p_2187_, v___x_2203_);
lean_inc(v_a_2188_);
v___x_2205_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_2205_, 0, v_c_2173_);
lean_ctor_set(v___x_2205_, 1, v_a_2188_);
v___x_2206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2204_);
lean_ctor_set(v___x_2206_, 1, v___x_2205_);
v___x_2207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2206_);
v___x_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
if (v_isShared_2186_ == 0)
{
lean_ctor_set(v___x_2185_, 1, v___x_2190_);
lean_ctor_set(v___x_2185_, 0, v___x_2208_);
v___x_2210_ = v___x_2185_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v___x_2208_);
lean_ctor_set(v_reuseFailAlloc_2217_, 1, v___x_2190_);
v___x_2210_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2215_; 
v___x_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2210_);
v___x_2212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2212_, 0, v___x_2211_);
v___x_2213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2212_);
lean_ctor_set(v___x_2213_, 1, v_snd_2183_);
if (v_isShared_2202_ == 0)
{
lean_ctor_set(v___x_2201_, 0, v___x_2213_);
v___x_2215_ = v___x_2201_;
goto v_reusejp_2214_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v___x_2213_);
v___x_2215_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2214_;
}
v_reusejp_2214_:
{
return v___x_2215_;
}
}
}
}
else
{
lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2227_; 
lean_del_object(v___x_2185_);
lean_dec(v_snd_2183_);
lean_dec_ref(v_c_2173_);
v_a_2220_ = lean_ctor_get(v___x_2199_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2199_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2222_ = v___x_2199_;
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___x_2199_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2225_; 
if (v_isShared_2223_ == 0)
{
v___x_2225_ = v___x_2222_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_a_2220_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg___boxed(lean_object* v_c_2232_, lean_object* v_x_2233_, lean_object* v_as_2234_, lean_object* v_sz_2235_, lean_object* v_i_2236_, lean_object* v_b_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_){
_start:
{
size_t v_sz_boxed_2240_; size_t v_i_boxed_2241_; lean_object* v_res_2242_; 
v_sz_boxed_2240_ = lean_unbox_usize(v_sz_2235_);
lean_dec(v_sz_2235_);
v_i_boxed_2241_ = lean_unbox_usize(v_i_2236_);
lean_dec(v_i_2236_);
v_res_2242_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(v_c_2232_, v_x_2233_, v_as_2234_, v_sz_boxed_2240_, v_i_boxed_2241_, v_b_2237_, v___y_2238_);
lean_dec(v___y_2238_);
lean_dec_ref(v_as_2234_);
return v_res_2242_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9(lean_object* v_c_2246_, lean_object* v_x_2247_, lean_object* v_as_2248_, size_t v_sz_2249_, size_t v_i_2250_, lean_object* v_b_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_){
_start:
{
uint8_t v___x_2263_; 
v___x_2263_ = lean_usize_dec_lt(v_i_2250_, v_sz_2249_);
if (v___x_2263_ == 0)
{
lean_object* v___x_2264_; 
lean_dec(v_x_2247_);
lean_dec_ref(v_c_2246_);
v___x_2264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2264_, 0, v_b_2251_);
return v___x_2264_;
}
else
{
lean_object* v_snd_2265_; lean_object* v___x_2267_; uint8_t v_isShared_2268_; uint8_t v_isSharedCheck_2312_; 
v_snd_2265_ = lean_ctor_get(v_b_2251_, 1);
v_isSharedCheck_2312_ = !lean_is_exclusive(v_b_2251_);
if (v_isSharedCheck_2312_ == 0)
{
lean_object* v_unused_2313_; 
v_unused_2313_ = lean_ctor_get(v_b_2251_, 0);
lean_dec(v_unused_2313_);
v___x_2267_ = v_b_2251_;
v_isShared_2268_ = v_isSharedCheck_2312_;
goto v_resetjp_2266_;
}
else
{
lean_inc(v_snd_2265_);
lean_dec(v_b_2251_);
v___x_2267_ = lean_box(0);
v_isShared_2268_ = v_isSharedCheck_2312_;
goto v_resetjp_2266_;
}
v_resetjp_2266_:
{
lean_object* v_p_2269_; lean_object* v_a_2270_; lean_object* v_p_2271_; lean_object* v___x_2272_; lean_object* v___f_2273_; uint8_t v___y_2275_; uint8_t v___x_2310_; 
v_p_2269_ = lean_ctor_get(v_c_2246_, 0);
v_a_2270_ = lean_array_uget_borrowed(v_as_2248_, v_i_2250_);
v_p_2271_ = lean_ctor_get(v_a_2270_, 0);
v___x_2272_ = lean_box(0);
lean_inc(v_x_2247_);
lean_inc_ref(v_p_2271_);
v___f_2273_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2273_, 0, v_p_2271_);
lean_closure_set(v___f_2273_, 1, v_x_2247_);
v___x_2310_ = l_Int_Linear_instBEqPoly_beq(v_p_2269_, v_p_2271_);
if (v___x_2310_ == 0)
{
uint8_t v___x_2311_; 
v___x_2311_ = l_Int_Linear_Poly_isNegEq(v_p_2269_, v_p_2271_);
v___y_2275_ = v___x_2311_;
goto v___jp_2274_;
}
else
{
v___y_2275_ = v___x_2310_;
goto v___jp_2274_;
}
v___jp_2274_:
{
if (v___y_2275_ == 0)
{
lean_object* v___x_2276_; size_t v___x_2277_; size_t v___x_2278_; lean_object* v___x_2279_; 
lean_dec_ref(v___f_2273_);
lean_del_object(v___x_2267_);
lean_dec(v_snd_2265_);
v___x_2276_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9___closed__0));
v___x_2277_ = ((size_t)1ULL);
v___x_2278_ = lean_usize_add(v_i_2250_, v___x_2277_);
v___x_2279_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(v_c_2246_, v_x_2247_, v_as_2248_, v_sz_2249_, v___x_2278_, v___x_2276_, v___y_2252_);
return v___x_2279_;
}
else
{
lean_object* v___x_2280_; lean_object* v___x_2281_; 
lean_dec(v_x_2247_);
v___x_2280_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2281_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2280_, v___f_2273_, v___y_2252_);
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_object* v___x_2283_; uint8_t v_isShared_2284_; uint8_t v_isSharedCheck_2300_; 
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2281_);
if (v_isSharedCheck_2300_ == 0)
{
lean_object* v_unused_2301_; 
v_unused_2301_ = lean_ctor_get(v___x_2281_, 0);
lean_dec(v_unused_2301_);
v___x_2283_ = v___x_2281_;
v_isShared_2284_ = v_isSharedCheck_2300_;
goto v_resetjp_2282_;
}
else
{
lean_dec(v___x_2281_);
v___x_2283_ = lean_box(0);
v_isShared_2284_ = v_isSharedCheck_2300_;
goto v_resetjp_2282_;
}
v_resetjp_2282_:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2292_; 
v___x_2285_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
lean_inc_ref(v_p_2269_);
v___x_2286_ = l_Int_Linear_Poly_addConst(v_p_2269_, v___x_2285_);
lean_inc(v_a_2270_);
v___x_2287_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_2287_, 0, v_c_2246_);
lean_ctor_set(v___x_2287_, 1, v_a_2270_);
v___x_2288_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2286_);
lean_ctor_set(v___x_2288_, 1, v___x_2287_);
v___x_2289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2288_);
v___x_2290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2289_);
if (v_isShared_2268_ == 0)
{
lean_ctor_set(v___x_2267_, 1, v___x_2272_);
lean_ctor_set(v___x_2267_, 0, v___x_2290_);
v___x_2292_ = v___x_2267_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v___x_2290_);
lean_ctor_set(v_reuseFailAlloc_2299_, 1, v___x_2272_);
v___x_2292_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2297_; 
v___x_2293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2292_);
v___x_2294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2293_);
v___x_2295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2294_);
lean_ctor_set(v___x_2295_, 1, v_snd_2265_);
if (v_isShared_2284_ == 0)
{
lean_ctor_set(v___x_2283_, 0, v___x_2295_);
v___x_2297_ = v___x_2283_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v___x_2295_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
}
}
else
{
lean_object* v_a_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2309_; 
lean_del_object(v___x_2267_);
lean_dec(v_snd_2265_);
lean_dec_ref(v_c_2246_);
v_a_2302_ = lean_ctor_get(v___x_2281_, 0);
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2281_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2304_ = v___x_2281_;
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_a_2302_);
lean_dec(v___x_2281_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2309_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v___x_2307_; 
if (v_isShared_2305_ == 0)
{
v___x_2307_ = v___x_2304_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_a_2302_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
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
lean_object* v_c_2314_ = _args[0];
lean_object* v_x_2315_ = _args[1];
lean_object* v_as_2316_ = _args[2];
lean_object* v_sz_2317_ = _args[3];
lean_object* v_i_2318_ = _args[4];
lean_object* v_b_2319_ = _args[5];
lean_object* v___y_2320_ = _args[6];
lean_object* v___y_2321_ = _args[7];
lean_object* v___y_2322_ = _args[8];
lean_object* v___y_2323_ = _args[9];
lean_object* v___y_2324_ = _args[10];
lean_object* v___y_2325_ = _args[11];
lean_object* v___y_2326_ = _args[12];
lean_object* v___y_2327_ = _args[13];
lean_object* v___y_2328_ = _args[14];
lean_object* v___y_2329_ = _args[15];
lean_object* v___y_2330_ = _args[16];
_start:
{
size_t v_sz_boxed_2331_; size_t v_i_boxed_2332_; lean_object* v_res_2333_; 
v_sz_boxed_2331_ = lean_unbox_usize(v_sz_2317_);
lean_dec(v_sz_2317_);
v_i_boxed_2332_ = lean_unbox_usize(v_i_2318_);
lean_dec(v_i_2318_);
v_res_2333_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9(v_c_2314_, v_x_2315_, v_as_2316_, v_sz_boxed_2331_, v_i_boxed_2332_, v_b_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
lean_dec(v___y_2327_);
lean_dec_ref(v___y_2326_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
lean_dec(v___y_2323_);
lean_dec_ref(v___y_2322_);
lean_dec(v___y_2321_);
lean_dec(v___y_2320_);
lean_dec_ref(v_as_2316_);
return v_res_2333_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(lean_object* v_init_2334_, lean_object* v_c_2335_, lean_object* v_x_2336_, lean_object* v_n_2337_, lean_object* v_b_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_){
_start:
{
if (lean_obj_tag(v_n_2337_) == 0)
{
lean_object* v_cs_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2384_; 
v_cs_2350_ = lean_ctor_get(v_n_2337_, 0);
v_isSharedCheck_2384_ = !lean_is_exclusive(v_n_2337_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2352_ = v_n_2337_;
v_isShared_2353_ = v_isSharedCheck_2384_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_cs_2350_);
lean_dec(v_n_2337_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2384_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; size_t v_sz_2356_; size_t v___x_2357_; lean_object* v___x_2358_; 
v___x_2354_ = lean_box(0);
v___x_2355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2355_, 0, v___x_2354_);
lean_ctor_set(v___x_2355_, 1, v_b_2338_);
v_sz_2356_ = lean_array_size(v_cs_2350_);
v___x_2357_ = ((size_t)0ULL);
v___x_2358_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8(v_init_2334_, v_c_2335_, v_x_2336_, v_cs_2350_, v_sz_2356_, v___x_2357_, v___x_2355_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
lean_dec_ref(v_cs_2350_);
if (lean_obj_tag(v___x_2358_) == 0)
{
lean_object* v_a_2359_; lean_object* v___x_2361_; uint8_t v_isShared_2362_; uint8_t v_isSharedCheck_2375_; 
v_a_2359_ = lean_ctor_get(v___x_2358_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2361_ = v___x_2358_;
v_isShared_2362_ = v_isSharedCheck_2375_;
goto v_resetjp_2360_;
}
else
{
lean_inc(v_a_2359_);
lean_dec(v___x_2358_);
v___x_2361_ = lean_box(0);
v_isShared_2362_ = v_isSharedCheck_2375_;
goto v_resetjp_2360_;
}
v_resetjp_2360_:
{
lean_object* v_fst_2363_; 
v_fst_2363_ = lean_ctor_get(v_a_2359_, 0);
if (lean_obj_tag(v_fst_2363_) == 0)
{
lean_object* v_snd_2364_; lean_object* v___x_2366_; 
v_snd_2364_ = lean_ctor_get(v_a_2359_, 1);
lean_inc(v_snd_2364_);
lean_dec(v_a_2359_);
if (v_isShared_2353_ == 0)
{
lean_ctor_set_tag(v___x_2352_, 1);
lean_ctor_set(v___x_2352_, 0, v_snd_2364_);
v___x_2366_ = v___x_2352_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_snd_2364_);
v___x_2366_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
lean_object* v___x_2368_; 
if (v_isShared_2362_ == 0)
{
lean_ctor_set(v___x_2361_, 0, v___x_2366_);
v___x_2368_ = v___x_2361_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v___x_2366_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
else
{
lean_object* v_val_2371_; lean_object* v___x_2373_; 
lean_inc_ref(v_fst_2363_);
lean_dec(v_a_2359_);
lean_del_object(v___x_2352_);
v_val_2371_ = lean_ctor_get(v_fst_2363_, 0);
lean_inc(v_val_2371_);
lean_dec_ref(v_fst_2363_);
if (v_isShared_2362_ == 0)
{
lean_ctor_set(v___x_2361_, 0, v_val_2371_);
v___x_2373_ = v___x_2361_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_val_2371_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
else
{
lean_object* v_a_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2383_; 
lean_del_object(v___x_2352_);
v_a_2376_ = lean_ctor_get(v___x_2358_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2358_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2378_ = v___x_2358_;
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_dec(v___x_2358_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2381_; 
if (v_isShared_2379_ == 0)
{
v___x_2381_ = v___x_2378_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_a_2376_);
v___x_2381_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
return v___x_2381_;
}
}
}
}
}
else
{
lean_object* v_vs_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2419_; 
v_vs_2385_ = lean_ctor_get(v_n_2337_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v_n_2337_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2387_ = v_n_2337_;
v_isShared_2388_ = v_isSharedCheck_2419_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_vs_2385_);
lean_dec(v_n_2337_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2419_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___x_2389_; lean_object* v___x_2390_; size_t v_sz_2391_; size_t v___x_2392_; lean_object* v___x_2393_; 
v___x_2389_ = lean_box(0);
v___x_2390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2390_, 0, v___x_2389_);
lean_ctor_set(v___x_2390_, 1, v_b_2338_);
v_sz_2391_ = lean_array_size(v_vs_2385_);
v___x_2392_ = ((size_t)0ULL);
v___x_2393_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9(v_c_2335_, v_x_2336_, v_vs_2385_, v_sz_2391_, v___x_2392_, v___x_2390_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
lean_dec_ref(v_vs_2385_);
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_object* v_a_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2410_; 
v_a_2394_ = lean_ctor_get(v___x_2393_, 0);
v_isSharedCheck_2410_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2410_ == 0)
{
v___x_2396_ = v___x_2393_;
v_isShared_2397_ = v_isSharedCheck_2410_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_a_2394_);
lean_dec(v___x_2393_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2410_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v_fst_2398_; 
v_fst_2398_ = lean_ctor_get(v_a_2394_, 0);
if (lean_obj_tag(v_fst_2398_) == 0)
{
lean_object* v_snd_2399_; lean_object* v___x_2401_; 
v_snd_2399_ = lean_ctor_get(v_a_2394_, 1);
lean_inc(v_snd_2399_);
lean_dec(v_a_2394_);
if (v_isShared_2388_ == 0)
{
lean_ctor_set(v___x_2387_, 0, v_snd_2399_);
v___x_2401_ = v___x_2387_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_snd_2399_);
v___x_2401_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
lean_object* v___x_2403_; 
if (v_isShared_2397_ == 0)
{
lean_ctor_set(v___x_2396_, 0, v___x_2401_);
v___x_2403_ = v___x_2396_;
goto v_reusejp_2402_;
}
else
{
lean_object* v_reuseFailAlloc_2404_; 
v_reuseFailAlloc_2404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2404_, 0, v___x_2401_);
v___x_2403_ = v_reuseFailAlloc_2404_;
goto v_reusejp_2402_;
}
v_reusejp_2402_:
{
return v___x_2403_;
}
}
}
else
{
lean_object* v_val_2406_; lean_object* v___x_2408_; 
lean_inc_ref(v_fst_2398_);
lean_dec(v_a_2394_);
lean_del_object(v___x_2387_);
v_val_2406_ = lean_ctor_get(v_fst_2398_, 0);
lean_inc(v_val_2406_);
lean_dec_ref(v_fst_2398_);
if (v_isShared_2397_ == 0)
{
lean_ctor_set(v___x_2396_, 0, v_val_2406_);
v___x_2408_ = v___x_2396_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v_val_2406_);
v___x_2408_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
return v___x_2408_;
}
}
}
}
else
{
lean_object* v_a_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2418_; 
lean_del_object(v___x_2387_);
v_a_2411_ = lean_ctor_get(v___x_2393_, 0);
v_isSharedCheck_2418_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2413_ = v___x_2393_;
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_a_2411_);
lean_dec(v___x_2393_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2416_; 
if (v_isShared_2414_ == 0)
{
v___x_2416_ = v___x_2413_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v_a_2411_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
return v___x_2416_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8(lean_object* v_init_2420_, lean_object* v_c_2421_, lean_object* v_x_2422_, lean_object* v_as_2423_, size_t v_sz_2424_, size_t v_i_2425_, lean_object* v_b_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_){
_start:
{
uint8_t v___x_2438_; 
v___x_2438_ = lean_usize_dec_lt(v_i_2425_, v_sz_2424_);
if (v___x_2438_ == 0)
{
lean_object* v___x_2439_; 
lean_dec(v_x_2422_);
lean_dec_ref(v_c_2421_);
v___x_2439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2439_, 0, v_b_2426_);
return v___x_2439_;
}
else
{
lean_object* v_snd_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2474_; 
v_snd_2440_ = lean_ctor_get(v_b_2426_, 1);
v_isSharedCheck_2474_ = !lean_is_exclusive(v_b_2426_);
if (v_isSharedCheck_2474_ == 0)
{
lean_object* v_unused_2475_; 
v_unused_2475_ = lean_ctor_get(v_b_2426_, 0);
lean_dec(v_unused_2475_);
v___x_2442_ = v_b_2426_;
v_isShared_2443_ = v_isSharedCheck_2474_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_snd_2440_);
lean_dec(v_b_2426_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2474_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v_a_2444_; lean_object* v___x_2445_; 
v_a_2444_ = lean_array_uget_borrowed(v_as_2423_, v_i_2425_);
lean_inc(v_snd_2440_);
lean_inc(v_a_2444_);
lean_inc(v_x_2422_);
lean_inc_ref(v_c_2421_);
v___x_2445_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(v_init_2420_, v_c_2421_, v_x_2422_, v_a_2444_, v_snd_2440_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
if (lean_obj_tag(v___x_2445_) == 0)
{
lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2465_; 
v_a_2446_ = lean_ctor_get(v___x_2445_, 0);
v_isSharedCheck_2465_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2448_ = v___x_2445_;
v_isShared_2449_ = v_isSharedCheck_2465_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_dec(v___x_2445_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2465_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
if (lean_obj_tag(v_a_2446_) == 0)
{
lean_object* v___x_2450_; lean_object* v___x_2452_; 
lean_dec(v_x_2422_);
lean_dec_ref(v_c_2421_);
v___x_2450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2450_, 0, v_a_2446_);
if (v_isShared_2443_ == 0)
{
lean_ctor_set(v___x_2442_, 0, v___x_2450_);
v___x_2452_ = v___x_2442_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v___x_2450_);
lean_ctor_set(v_reuseFailAlloc_2456_, 1, v_snd_2440_);
v___x_2452_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
lean_object* v___x_2454_; 
if (v_isShared_2449_ == 0)
{
lean_ctor_set(v___x_2448_, 0, v___x_2452_);
v___x_2454_ = v___x_2448_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v___x_2452_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
return v___x_2454_;
}
}
}
else
{
lean_object* v_a_2457_; lean_object* v___x_2458_; lean_object* v___x_2460_; 
lean_del_object(v___x_2448_);
lean_dec(v_snd_2440_);
v_a_2457_ = lean_ctor_get(v_a_2446_, 0);
lean_inc(v_a_2457_);
lean_dec_ref(v_a_2446_);
v___x_2458_ = lean_box(0);
if (v_isShared_2443_ == 0)
{
lean_ctor_set(v___x_2442_, 1, v_a_2457_);
lean_ctor_set(v___x_2442_, 0, v___x_2458_);
v___x_2460_ = v___x_2442_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v___x_2458_);
lean_ctor_set(v_reuseFailAlloc_2464_, 1, v_a_2457_);
v___x_2460_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
size_t v___x_2461_; size_t v___x_2462_; 
v___x_2461_ = ((size_t)1ULL);
v___x_2462_ = lean_usize_add(v_i_2425_, v___x_2461_);
v_i_2425_ = v___x_2462_;
v_b_2426_ = v___x_2460_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2473_; 
lean_del_object(v___x_2442_);
lean_dec(v_snd_2440_);
lean_dec(v_x_2422_);
lean_dec_ref(v_c_2421_);
v_a_2466_ = lean_ctor_get(v___x_2445_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2468_ = v___x_2445_;
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_dec(v___x_2445_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2471_; 
if (v_isShared_2469_ == 0)
{
v___x_2471_ = v___x_2468_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_a_2466_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8___boxed(lean_object** _args){
lean_object* v_init_2476_ = _args[0];
lean_object* v_c_2477_ = _args[1];
lean_object* v_x_2478_ = _args[2];
lean_object* v_as_2479_ = _args[3];
lean_object* v_sz_2480_ = _args[4];
lean_object* v_i_2481_ = _args[5];
lean_object* v_b_2482_ = _args[6];
lean_object* v___y_2483_ = _args[7];
lean_object* v___y_2484_ = _args[8];
lean_object* v___y_2485_ = _args[9];
lean_object* v___y_2486_ = _args[10];
lean_object* v___y_2487_ = _args[11];
lean_object* v___y_2488_ = _args[12];
lean_object* v___y_2489_ = _args[13];
lean_object* v___y_2490_ = _args[14];
lean_object* v___y_2491_ = _args[15];
lean_object* v___y_2492_ = _args[16];
lean_object* v___y_2493_ = _args[17];
_start:
{
size_t v_sz_boxed_2494_; size_t v_i_boxed_2495_; lean_object* v_res_2496_; 
v_sz_boxed_2494_ = lean_unbox_usize(v_sz_2480_);
lean_dec(v_sz_2480_);
v_i_boxed_2495_ = lean_unbox_usize(v_i_2481_);
lean_dec(v_i_2481_);
v_res_2496_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8(v_init_2476_, v_c_2477_, v_x_2478_, v_as_2479_, v_sz_boxed_2494_, v_i_boxed_2495_, v_b_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_);
lean_dec(v___y_2492_);
lean_dec_ref(v___y_2491_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec(v___y_2488_);
lean_dec_ref(v___y_2487_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
lean_dec(v___y_2484_);
lean_dec(v___y_2483_);
lean_dec_ref(v_as_2479_);
lean_dec_ref(v_init_2476_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6___boxed(lean_object* v_init_2497_, lean_object* v_c_2498_, lean_object* v_x_2499_, lean_object* v_n_2500_, lean_object* v_b_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_){
_start:
{
lean_object* v_res_2513_; 
v_res_2513_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(v_init_2497_, v_c_2498_, v_x_2499_, v_n_2500_, v_b_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
lean_dec(v___y_2511_);
lean_dec_ref(v___y_2510_);
lean_dec(v___y_2509_);
lean_dec_ref(v___y_2508_);
lean_dec(v___y_2507_);
lean_dec_ref(v___y_2506_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
lean_dec(v___y_2503_);
lean_dec(v___y_2502_);
lean_dec_ref(v_init_2497_);
return v_res_2513_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2(lean_object* v_c_2514_, lean_object* v_x_2515_, lean_object* v_t_2516_, lean_object* v_init_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_){
_start:
{
lean_object* v_root_2529_; lean_object* v_tail_2530_; lean_object* v___x_2531_; 
v_root_2529_ = lean_ctor_get(v_t_2516_, 0);
lean_inc_ref(v_root_2529_);
v_tail_2530_ = lean_ctor_get(v_t_2516_, 1);
lean_inc_ref(v_tail_2530_);
lean_dec_ref(v_t_2516_);
lean_inc(v_x_2515_);
lean_inc_ref(v_c_2514_);
lean_inc_ref(v_init_2517_);
v___x_2531_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(v_init_2517_, v_c_2514_, v_x_2515_, v_root_2529_, v_init_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_);
lean_dec_ref(v_init_2517_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_object* v_a_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2568_; 
v_a_2532_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2568_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2534_ = v___x_2531_;
v_isShared_2535_ = v_isSharedCheck_2568_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_a_2532_);
lean_dec(v___x_2531_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2568_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
if (lean_obj_tag(v_a_2532_) == 0)
{
lean_object* v_a_2536_; lean_object* v___x_2538_; 
lean_dec_ref(v_tail_2530_);
lean_dec(v_x_2515_);
lean_dec_ref(v_c_2514_);
v_a_2536_ = lean_ctor_get(v_a_2532_, 0);
lean_inc(v_a_2536_);
lean_dec_ref(v_a_2532_);
if (v_isShared_2535_ == 0)
{
lean_ctor_set(v___x_2534_, 0, v_a_2536_);
v___x_2538_ = v___x_2534_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_a_2536_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
else
{
lean_object* v_a_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; size_t v_sz_2543_; size_t v___x_2544_; lean_object* v___x_2545_; 
lean_del_object(v___x_2534_);
v_a_2540_ = lean_ctor_get(v_a_2532_, 0);
lean_inc(v_a_2540_);
lean_dec_ref(v_a_2532_);
v___x_2541_ = lean_box(0);
v___x_2542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2542_, 0, v___x_2541_);
lean_ctor_set(v___x_2542_, 1, v_a_2540_);
v_sz_2543_ = lean_array_size(v_tail_2530_);
v___x_2544_ = ((size_t)0ULL);
v___x_2545_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7(v_c_2514_, v_x_2515_, v_tail_2530_, v_sz_2543_, v___x_2544_, v___x_2542_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_);
lean_dec_ref(v_tail_2530_);
if (lean_obj_tag(v___x_2545_) == 0)
{
lean_object* v_a_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2559_; 
v_a_2546_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2548_ = v___x_2545_;
v_isShared_2549_ = v_isSharedCheck_2559_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_a_2546_);
lean_dec(v___x_2545_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2559_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v_fst_2550_; 
v_fst_2550_ = lean_ctor_get(v_a_2546_, 0);
if (lean_obj_tag(v_fst_2550_) == 0)
{
lean_object* v_snd_2551_; lean_object* v___x_2553_; 
v_snd_2551_ = lean_ctor_get(v_a_2546_, 1);
lean_inc(v_snd_2551_);
lean_dec(v_a_2546_);
if (v_isShared_2549_ == 0)
{
lean_ctor_set(v___x_2548_, 0, v_snd_2551_);
v___x_2553_ = v___x_2548_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_snd_2551_);
v___x_2553_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
return v___x_2553_;
}
}
else
{
lean_object* v_val_2555_; lean_object* v___x_2557_; 
lean_inc_ref(v_fst_2550_);
lean_dec(v_a_2546_);
v_val_2555_ = lean_ctor_get(v_fst_2550_, 0);
lean_inc(v_val_2555_);
lean_dec_ref(v_fst_2550_);
if (v_isShared_2549_ == 0)
{
lean_ctor_set(v___x_2548_, 0, v_val_2555_);
v___x_2557_ = v___x_2548_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_val_2555_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
return v___x_2557_;
}
}
}
}
else
{
lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2567_; 
v_a_2560_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2562_ = v___x_2545_;
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___x_2545_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2565_; 
if (v_isShared_2563_ == 0)
{
v___x_2565_ = v___x_2562_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_a_2560_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
return v___x_2565_;
}
}
}
}
}
}
else
{
lean_object* v_a_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2576_; 
lean_dec_ref(v_tail_2530_);
lean_dec(v_x_2515_);
lean_dec_ref(v_c_2514_);
v_a_2569_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2571_ = v___x_2531_;
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_a_2569_);
lean_dec(v___x_2531_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2576_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2574_; 
if (v_isShared_2572_ == 0)
{
v___x_2574_ = v___x_2571_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_a_2569_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2___boxed(lean_object* v_c_2577_, lean_object* v_x_2578_, lean_object* v_t_2579_, lean_object* v_init_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_){
_start:
{
lean_object* v_res_2592_; 
v_res_2592_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2(v_c_2577_, v_x_2578_, v_t_2579_, v_init_2580_, v___y_2581_, v___y_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_);
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
lean_dec(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec(v___y_2584_);
lean_dec_ref(v___y_2583_);
lean_dec(v___y_2582_);
lean_dec(v___y_2581_);
return v_res_2592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(lean_object* v_x_2593_, lean_object* v_c_2594_, lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_){
_start:
{
lean_object* v___x_2606_; 
v___x_2606_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2595_, v_a_2603_);
if (lean_obj_tag(v___x_2606_) == 0)
{
lean_object* v_a_2607_; lean_object* v___y_2609_; lean_object* v_diseqs_2634_; lean_object* v_size_2635_; lean_object* v___x_2636_; uint8_t v___x_2637_; 
v_a_2607_ = lean_ctor_get(v___x_2606_, 0);
lean_inc(v_a_2607_);
lean_dec_ref(v___x_2606_);
v_diseqs_2634_ = lean_ctor_get(v_a_2607_, 9);
lean_inc_ref(v_diseqs_2634_);
lean_dec(v_a_2607_);
v_size_2635_ = lean_ctor_get(v_diseqs_2634_, 2);
v___x_2636_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0);
v___x_2637_ = lean_nat_dec_lt(v_x_2593_, v_size_2635_);
if (v___x_2637_ == 0)
{
lean_object* v___x_2638_; 
lean_dec_ref(v_diseqs_2634_);
v___x_2638_ = l_outOfBounds___redArg(v___x_2636_);
v___y_2609_ = v___x_2638_;
goto v___jp_2608_;
}
else
{
lean_object* v___x_2639_; 
v___x_2639_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2636_, v_diseqs_2634_, v_x_2593_);
lean_dec_ref(v_diseqs_2634_);
v___y_2609_ = v___x_2639_;
goto v___jp_2608_;
}
v___jp_2608_:
{
lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2610_ = lean_box(0);
v___x_2611_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___closed__0));
v___x_2612_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2(v_c_2594_, v_x_2593_, v___y_2609_, v___x_2611_, v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_, v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_);
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2625_; 
v_a_2613_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2625_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2625_ == 0)
{
v___x_2615_ = v___x_2612_;
v_isShared_2616_ = v_isSharedCheck_2625_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2612_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2625_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v_fst_2617_; 
v_fst_2617_ = lean_ctor_get(v_a_2613_, 0);
lean_inc(v_fst_2617_);
lean_dec(v_a_2613_);
if (lean_obj_tag(v_fst_2617_) == 0)
{
lean_object* v___x_2619_; 
if (v_isShared_2616_ == 0)
{
lean_ctor_set(v___x_2615_, 0, v___x_2610_);
v___x_2619_ = v___x_2615_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v___x_2610_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
else
{
lean_object* v_val_2621_; lean_object* v___x_2623_; 
v_val_2621_ = lean_ctor_get(v_fst_2617_, 0);
lean_inc(v_val_2621_);
lean_dec_ref(v_fst_2617_);
if (v_isShared_2616_ == 0)
{
lean_ctor_set(v___x_2615_, 0, v_val_2621_);
v___x_2623_ = v___x_2615_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_val_2621_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
}
}
else
{
lean_object* v_a_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2633_; 
v_a_2626_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2633_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2633_ == 0)
{
v___x_2628_ = v___x_2612_;
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_a_2626_);
lean_dec(v___x_2612_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2633_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v___x_2631_; 
if (v_isShared_2629_ == 0)
{
v___x_2631_ = v___x_2628_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2632_; 
v_reuseFailAlloc_2632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2632_, 0, v_a_2626_);
v___x_2631_ = v_reuseFailAlloc_2632_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
return v___x_2631_;
}
}
}
}
}
else
{
lean_object* v_a_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2647_; 
lean_dec_ref(v_c_2594_);
lean_dec(v_x_2593_);
v_a_2640_ = lean_ctor_get(v___x_2606_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v___x_2606_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2642_ = v___x_2606_;
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_a_2640_);
lean_dec(v___x_2606_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2645_; 
if (v_isShared_2643_ == 0)
{
v___x_2645_ = v___x_2642_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_a_2640_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f___boxed(lean_object* v_x_2648_, lean_object* v_c_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_){
_start:
{
lean_object* v_res_2661_; 
v_res_2661_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(v_x_2648_, v_c_2649_, v_a_2650_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_);
lean_dec(v_a_2659_);
lean_dec_ref(v_a_2658_);
lean_dec(v_a_2657_);
lean_dec_ref(v_a_2656_);
lean_dec(v_a_2655_);
lean_dec_ref(v_a_2654_);
lean_dec(v_a_2653_);
lean_dec_ref(v_a_2652_);
lean_dec(v_a_2651_);
lean_dec(v_a_2650_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11(lean_object* v_c_2662_, lean_object* v_x_2663_, lean_object* v_as_2664_, size_t v_sz_2665_, size_t v_i_2666_, lean_object* v_b_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_){
_start:
{
lean_object* v___x_2679_; 
v___x_2679_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(v_c_2662_, v_x_2663_, v_as_2664_, v_sz_2665_, v_i_2666_, v_b_2667_, v___y_2668_);
return v___x_2679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___boxed(lean_object** _args){
lean_object* v_c_2680_ = _args[0];
lean_object* v_x_2681_ = _args[1];
lean_object* v_as_2682_ = _args[2];
lean_object* v_sz_2683_ = _args[3];
lean_object* v_i_2684_ = _args[4];
lean_object* v_b_2685_ = _args[5];
lean_object* v___y_2686_ = _args[6];
lean_object* v___y_2687_ = _args[7];
lean_object* v___y_2688_ = _args[8];
lean_object* v___y_2689_ = _args[9];
lean_object* v___y_2690_ = _args[10];
lean_object* v___y_2691_ = _args[11];
lean_object* v___y_2692_ = _args[12];
lean_object* v___y_2693_ = _args[13];
lean_object* v___y_2694_ = _args[14];
lean_object* v___y_2695_ = _args[15];
lean_object* v___y_2696_ = _args[16];
_start:
{
size_t v_sz_boxed_2697_; size_t v_i_boxed_2698_; lean_object* v_res_2699_; 
v_sz_boxed_2697_ = lean_unbox_usize(v_sz_2683_);
lean_dec(v_sz_2683_);
v_i_boxed_2698_ = lean_unbox_usize(v_i_2684_);
lean_dec(v_i_2684_);
v_res_2699_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11(v_c_2680_, v_x_2681_, v_as_2682_, v_sz_boxed_2697_, v_i_boxed_2698_, v_b_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
lean_dec(v___y_2691_);
lean_dec_ref(v___y_2690_);
lean_dec(v___y_2689_);
lean_dec_ref(v___y_2688_);
lean_dec(v___y_2687_);
lean_dec(v___y_2686_);
lean_dec_ref(v_as_2682_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10(lean_object* v_c_2700_, lean_object* v_x_2701_, lean_object* v_as_2702_, size_t v_sz_2703_, size_t v_i_2704_, lean_object* v_b_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
lean_object* v___x_2717_; 
v___x_2717_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(v_c_2700_, v_x_2701_, v_as_2702_, v_sz_2703_, v_i_2704_, v_b_2705_, v___y_2706_);
return v___x_2717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___boxed(lean_object** _args){
lean_object* v_c_2718_ = _args[0];
lean_object* v_x_2719_ = _args[1];
lean_object* v_as_2720_ = _args[2];
lean_object* v_sz_2721_ = _args[3];
lean_object* v_i_2722_ = _args[4];
lean_object* v_b_2723_ = _args[5];
lean_object* v___y_2724_ = _args[6];
lean_object* v___y_2725_ = _args[7];
lean_object* v___y_2726_ = _args[8];
lean_object* v___y_2727_ = _args[9];
lean_object* v___y_2728_ = _args[10];
lean_object* v___y_2729_ = _args[11];
lean_object* v___y_2730_ = _args[12];
lean_object* v___y_2731_ = _args[13];
lean_object* v___y_2732_ = _args[14];
lean_object* v___y_2733_ = _args[15];
lean_object* v___y_2734_ = _args[16];
_start:
{
size_t v_sz_boxed_2735_; size_t v_i_boxed_2736_; lean_object* v_res_2737_; 
v_sz_boxed_2735_ = lean_unbox_usize(v_sz_2721_);
lean_dec(v_sz_2721_);
v_i_boxed_2736_ = lean_unbox_usize(v_i_2722_);
lean_dec(v_i_2722_);
v_res_2737_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10(v_c_2718_, v_x_2719_, v_as_2720_, v_sz_boxed_2735_, v_i_boxed_2736_, v_b_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec(v___y_2724_);
lean_dec_ref(v_as_2720_);
return v_res_2737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0(lean_object* v_v_2738_, lean_object* v_b_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_){
_start:
{
lean_object* v_snd_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2782_; 
v_snd_2751_ = lean_ctor_get(v_b_2739_, 1);
v_isSharedCheck_2782_ = !lean_is_exclusive(v_b_2739_);
if (v_isSharedCheck_2782_ == 0)
{
lean_object* v_unused_2783_; 
v_unused_2783_ = lean_ctor_get(v_b_2739_, 0);
lean_dec(v_unused_2783_);
v___x_2753_ = v_b_2739_;
v_isShared_2754_ = v_isSharedCheck_2782_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_snd_2751_);
lean_dec(v_b_2739_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2782_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2755_; 
lean_inc(v_snd_2751_);
lean_inc(v_v_2738_);
v___x_2755_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(v_v_2738_, v_snd_2751_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
if (lean_obj_tag(v___x_2755_) == 0)
{
lean_object* v_a_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2773_; 
v_a_2756_ = lean_ctor_get(v___x_2755_, 0);
v_isSharedCheck_2773_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2773_ == 0)
{
v___x_2758_ = v___x_2755_;
v_isShared_2759_ = v_isSharedCheck_2773_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_a_2756_);
lean_dec(v___x_2755_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2773_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
if (lean_obj_tag(v_a_2756_) == 1)
{
lean_object* v_val_2760_; lean_object* v___x_2761_; lean_object* v___x_2763_; 
lean_del_object(v___x_2758_);
lean_dec(v_snd_2751_);
v_val_2760_ = lean_ctor_get(v_a_2756_, 0);
lean_inc(v_val_2760_);
lean_dec_ref(v_a_2756_);
v___x_2761_ = lean_box(0);
if (v_isShared_2754_ == 0)
{
lean_ctor_set(v___x_2753_, 1, v_val_2760_);
lean_ctor_set(v___x_2753_, 0, v___x_2761_);
v___x_2763_ = v___x_2753_;
goto v_reusejp_2762_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v___x_2761_);
lean_ctor_set(v_reuseFailAlloc_2765_, 1, v_val_2760_);
v___x_2763_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2762_;
}
v_reusejp_2762_:
{
v_b_2739_ = v___x_2763_;
goto _start;
}
}
else
{
lean_object* v___x_2766_; lean_object* v___x_2768_; 
lean_dec(v_a_2756_);
lean_dec(v_v_2738_);
lean_inc(v_snd_2751_);
v___x_2766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2766_, 0, v_snd_2751_);
if (v_isShared_2754_ == 0)
{
lean_ctor_set(v___x_2753_, 0, v___x_2766_);
v___x_2768_ = v___x_2753_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2772_; 
v_reuseFailAlloc_2772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2772_, 0, v___x_2766_);
lean_ctor_set(v_reuseFailAlloc_2772_, 1, v_snd_2751_);
v___x_2768_ = v_reuseFailAlloc_2772_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
lean_object* v___x_2770_; 
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 0, v___x_2768_);
v___x_2770_ = v___x_2758_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v___x_2768_);
v___x_2770_ = v_reuseFailAlloc_2771_;
goto v_reusejp_2769_;
}
v_reusejp_2769_:
{
return v___x_2770_;
}
}
}
}
}
else
{
lean_object* v_a_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2781_; 
lean_del_object(v___x_2753_);
lean_dec(v_snd_2751_);
lean_dec(v_v_2738_);
v_a_2774_ = lean_ctor_get(v___x_2755_, 0);
v_isSharedCheck_2781_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2781_ == 0)
{
v___x_2776_ = v___x_2755_;
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_a_2774_);
lean_dec(v___x_2755_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2781_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2779_; 
if (v_isShared_2777_ == 0)
{
v___x_2779_ = v___x_2776_;
goto v_reusejp_2778_;
}
else
{
lean_object* v_reuseFailAlloc_2780_; 
v_reuseFailAlloc_2780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_a_2774_);
v___x_2779_ = v_reuseFailAlloc_2780_;
goto v_reusejp_2778_;
}
v_reusejp_2778_:
{
return v___x_2779_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___boxed(lean_object* v_v_2784_, lean_object* v_b_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_){
_start:
{
lean_object* v_res_2797_; 
v_res_2797_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0(v_v_2784_, v_b_2785_, v___y_2786_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_);
lean_dec(v___y_2795_);
lean_dec_ref(v___y_2794_);
lean_dec(v___y_2793_);
lean_dec_ref(v___y_2792_);
lean_dec(v___y_2791_);
lean_dec_ref(v___y_2790_);
lean_dec(v___y_2789_);
lean_dec_ref(v___y_2788_);
lean_dec(v___y_2787_);
lean_dec(v___y_2786_);
return v_res_2797_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(lean_object* v_c_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_, lean_object* v_a_2804_, lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_){
_start:
{
lean_object* v_p_2810_; 
v_p_2810_ = lean_ctor_get(v_c_2798_, 0);
if (lean_obj_tag(v_p_2810_) == 1)
{
lean_object* v_v_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v_v_2811_ = lean_ctor_get(v_p_2810_, 1);
lean_inc(v_v_2811_);
v___x_2812_ = lean_box(0);
v___x_2813_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2813_, 0, v___x_2812_);
lean_ctor_set(v___x_2813_, 1, v_c_2798_);
v___x_2814_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0(v_v_2811_, v___x_2813_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v_a_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2828_; 
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
v_isSharedCheck_2828_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2828_ == 0)
{
v___x_2817_ = v___x_2814_;
v_isShared_2818_ = v_isSharedCheck_2828_;
goto v_resetjp_2816_;
}
else
{
lean_inc(v_a_2815_);
lean_dec(v___x_2814_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2828_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v_fst_2819_; 
v_fst_2819_ = lean_ctor_get(v_a_2815_, 0);
if (lean_obj_tag(v_fst_2819_) == 0)
{
lean_object* v_snd_2820_; lean_object* v___x_2822_; 
v_snd_2820_ = lean_ctor_get(v_a_2815_, 1);
lean_inc(v_snd_2820_);
lean_dec(v_a_2815_);
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 0, v_snd_2820_);
v___x_2822_ = v___x_2817_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_snd_2820_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
else
{
lean_object* v_val_2824_; lean_object* v___x_2826_; 
lean_inc_ref(v_fst_2819_);
lean_dec(v_a_2815_);
v_val_2824_ = lean_ctor_get(v_fst_2819_, 0);
lean_inc(v_val_2824_);
lean_dec_ref(v_fst_2819_);
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 0, v_val_2824_);
v___x_2826_ = v___x_2817_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_val_2824_);
v___x_2826_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
return v___x_2826_;
}
}
}
}
else
{
lean_object* v_a_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2836_; 
v_a_2829_ = lean_ctor_get(v___x_2814_, 0);
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2831_ = v___x_2814_;
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_a_2829_);
lean_dec(v___x_2814_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v___x_2834_; 
if (v_isShared_2832_ == 0)
{
v___x_2834_ = v___x_2831_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_a_2829_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
}
}
else
{
lean_object* v___x_2837_; 
v___x_2837_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_2798_, v_a_2799_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_);
return v___x_2837_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq___boxed(lean_object* v_c_2838_, lean_object* v_a_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_a_2842_, lean_object* v_a_2843_, lean_object* v_a_2844_, lean_object* v_a_2845_, lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_){
_start:
{
lean_object* v_res_2850_; 
v_res_2850_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(v_c_2838_, v_a_2839_, v_a_2840_, v_a_2841_, v_a_2842_, v_a_2843_, v_a_2844_, v_a_2845_, v_a_2846_, v_a_2847_, v_a_2848_);
lean_dec(v_a_2848_);
lean_dec_ref(v_a_2847_);
lean_dec(v_a_2846_);
lean_dec_ref(v_a_2845_);
lean_dec(v_a_2844_);
lean_dec_ref(v_a_2843_);
lean_dec(v_a_2842_);
lean_dec_ref(v_a_2841_);
lean_dec(v_a_2840_);
lean_dec(v_a_2839_);
return v_res_2850_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(lean_object* v_a_2851_, lean_object* v_x_2852_, size_t v_x_2853_, size_t v_x_2854_){
_start:
{
if (lean_obj_tag(v_x_2852_) == 0)
{
lean_object* v_cs_2855_; size_t v_j_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; uint8_t v___x_2859_; 
v_cs_2855_ = lean_ctor_get(v_x_2852_, 0);
v_j_2856_ = lean_usize_shift_right(v_x_2853_, v_x_2854_);
v___x_2857_ = lean_usize_to_nat(v_j_2856_);
v___x_2858_ = lean_array_get_size(v_cs_2855_);
v___x_2859_ = lean_nat_dec_lt(v___x_2857_, v___x_2858_);
if (v___x_2859_ == 0)
{
lean_dec(v___x_2857_);
lean_dec_ref(v_a_2851_);
return v_x_2852_;
}
else
{
lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2877_; 
lean_inc_ref(v_cs_2855_);
v_isSharedCheck_2877_ = !lean_is_exclusive(v_x_2852_);
if (v_isSharedCheck_2877_ == 0)
{
lean_object* v_unused_2878_; 
v_unused_2878_ = lean_ctor_get(v_x_2852_, 0);
lean_dec(v_unused_2878_);
v___x_2861_ = v_x_2852_;
v_isShared_2862_ = v_isSharedCheck_2877_;
goto v_resetjp_2860_;
}
else
{
lean_dec(v_x_2852_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2877_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
size_t v___x_2863_; size_t v___x_2864_; size_t v___x_2865_; size_t v_i_2866_; size_t v___x_2867_; size_t v_shift_2868_; lean_object* v_v_2869_; lean_object* v___x_2870_; lean_object* v_xs_x27_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2875_; 
v___x_2863_ = ((size_t)1ULL);
v___x_2864_ = lean_usize_shift_left(v___x_2863_, v_x_2854_);
v___x_2865_ = lean_usize_sub(v___x_2864_, v___x_2863_);
v_i_2866_ = lean_usize_land(v_x_2853_, v___x_2865_);
v___x_2867_ = ((size_t)5ULL);
v_shift_2868_ = lean_usize_sub(v_x_2854_, v___x_2867_);
v_v_2869_ = lean_array_fget(v_cs_2855_, v___x_2857_);
v___x_2870_ = lean_box(0);
v_xs_x27_2871_ = lean_array_fset(v_cs_2855_, v___x_2857_, v___x_2870_);
v___x_2872_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(v_a_2851_, v_v_2869_, v_i_2866_, v_shift_2868_);
v___x_2873_ = lean_array_fset(v_xs_x27_2871_, v___x_2857_, v___x_2872_);
lean_dec(v___x_2857_);
if (v_isShared_2862_ == 0)
{
lean_ctor_set(v___x_2861_, 0, v___x_2873_);
v___x_2875_ = v___x_2861_;
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
else
{
lean_object* v_vs_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; uint8_t v___x_2882_; 
v_vs_2879_ = lean_ctor_get(v_x_2852_, 0);
v___x_2880_ = lean_usize_to_nat(v_x_2853_);
v___x_2881_ = lean_array_get_size(v_vs_2879_);
v___x_2882_ = lean_nat_dec_lt(v___x_2880_, v___x_2881_);
if (v___x_2882_ == 0)
{
lean_dec(v___x_2880_);
lean_dec_ref(v_a_2851_);
return v_x_2852_;
}
else
{
lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2894_; 
lean_inc_ref(v_vs_2879_);
v_isSharedCheck_2894_ = !lean_is_exclusive(v_x_2852_);
if (v_isSharedCheck_2894_ == 0)
{
lean_object* v_unused_2895_; 
v_unused_2895_ = lean_ctor_get(v_x_2852_, 0);
lean_dec(v_unused_2895_);
v___x_2884_ = v_x_2852_;
v_isShared_2885_ = v_isSharedCheck_2894_;
goto v_resetjp_2883_;
}
else
{
lean_dec(v_x_2852_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2894_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v_v_2886_; lean_object* v___x_2887_; lean_object* v_xs_x27_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2892_; 
v_v_2886_ = lean_array_fget(v_vs_2879_, v___x_2880_);
v___x_2887_ = lean_box(0);
v_xs_x27_2888_ = lean_array_fset(v_vs_2879_, v___x_2880_, v___x_2887_);
v___x_2889_ = l_Lean_PersistentArray_push___redArg(v_v_2886_, v_a_2851_);
v___x_2890_ = lean_array_fset(v_xs_x27_2888_, v___x_2880_, v___x_2889_);
lean_dec(v___x_2880_);
if (v_isShared_2885_ == 0)
{
lean_ctor_set(v___x_2884_, 0, v___x_2890_);
v___x_2892_ = v___x_2884_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v___x_2890_);
v___x_2892_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
return v___x_2892_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0___boxed(lean_object* v_a_2896_, lean_object* v_x_2897_, lean_object* v_x_2898_, lean_object* v_x_2899_){
_start:
{
size_t v_x_93919__boxed_2900_; size_t v_x_93920__boxed_2901_; lean_object* v_res_2902_; 
v_x_93919__boxed_2900_ = lean_unbox_usize(v_x_2898_);
lean_dec(v_x_2898_);
v_x_93920__boxed_2901_ = lean_unbox_usize(v_x_2899_);
lean_dec(v_x_2899_);
v_res_2902_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(v_a_2896_, v_x_2897_, v_x_93919__boxed_2900_, v_x_93920__boxed_2901_);
return v_res_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(lean_object* v_a_2903_, lean_object* v_t_2904_, lean_object* v_i_2905_){
_start:
{
lean_object* v_root_2906_; lean_object* v_tail_2907_; lean_object* v_size_2908_; size_t v_shift_2909_; lean_object* v_tailOff_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2934_; 
v_root_2906_ = lean_ctor_get(v_t_2904_, 0);
v_tail_2907_ = lean_ctor_get(v_t_2904_, 1);
v_size_2908_ = lean_ctor_get(v_t_2904_, 2);
v_shift_2909_ = lean_ctor_get_usize(v_t_2904_, 4);
v_tailOff_2910_ = lean_ctor_get(v_t_2904_, 3);
v_isSharedCheck_2934_ = !lean_is_exclusive(v_t_2904_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2912_ = v_t_2904_;
v_isShared_2913_ = v_isSharedCheck_2934_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_tailOff_2910_);
lean_inc(v_size_2908_);
lean_inc(v_tail_2907_);
lean_inc(v_root_2906_);
lean_dec(v_t_2904_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2934_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
uint8_t v___x_2914_; 
v___x_2914_ = lean_nat_dec_le(v_tailOff_2910_, v_i_2905_);
if (v___x_2914_ == 0)
{
size_t v___x_2915_; lean_object* v___x_2916_; lean_object* v___x_2918_; 
v___x_2915_ = lean_usize_of_nat(v_i_2905_);
v___x_2916_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(v_a_2903_, v_root_2906_, v___x_2915_, v_shift_2909_);
if (v_isShared_2913_ == 0)
{
lean_ctor_set(v___x_2912_, 0, v___x_2916_);
v___x_2918_ = v___x_2912_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v___x_2916_);
lean_ctor_set(v_reuseFailAlloc_2919_, 1, v_tail_2907_);
lean_ctor_set(v_reuseFailAlloc_2919_, 2, v_size_2908_);
lean_ctor_set(v_reuseFailAlloc_2919_, 3, v_tailOff_2910_);
lean_ctor_set_usize(v_reuseFailAlloc_2919_, 4, v_shift_2909_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
else
{
lean_object* v___x_2920_; lean_object* v___x_2921_; uint8_t v___x_2922_; 
v___x_2920_ = lean_nat_sub(v_i_2905_, v_tailOff_2910_);
v___x_2921_ = lean_array_get_size(v_tail_2907_);
v___x_2922_ = lean_nat_dec_lt(v___x_2920_, v___x_2921_);
if (v___x_2922_ == 0)
{
lean_object* v___x_2924_; 
lean_dec(v___x_2920_);
lean_dec_ref(v_a_2903_);
if (v_isShared_2913_ == 0)
{
v___x_2924_ = v___x_2912_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_root_2906_);
lean_ctor_set(v_reuseFailAlloc_2925_, 1, v_tail_2907_);
lean_ctor_set(v_reuseFailAlloc_2925_, 2, v_size_2908_);
lean_ctor_set(v_reuseFailAlloc_2925_, 3, v_tailOff_2910_);
lean_ctor_set_usize(v_reuseFailAlloc_2925_, 4, v_shift_2909_);
v___x_2924_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
return v___x_2924_;
}
}
else
{
lean_object* v_v_2926_; lean_object* v___x_2927_; lean_object* v_xs_x27_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2932_; 
v_v_2926_ = lean_array_fget(v_tail_2907_, v___x_2920_);
v___x_2927_ = lean_box(0);
v_xs_x27_2928_ = lean_array_fset(v_tail_2907_, v___x_2920_, v___x_2927_);
v___x_2929_ = l_Lean_PersistentArray_push___redArg(v_v_2926_, v_a_2903_);
v___x_2930_ = lean_array_fset(v_xs_x27_2928_, v___x_2920_, v___x_2929_);
lean_dec(v___x_2920_);
if (v_isShared_2913_ == 0)
{
lean_ctor_set(v___x_2912_, 1, v___x_2930_);
v___x_2932_ = v___x_2912_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_root_2906_);
lean_ctor_set(v_reuseFailAlloc_2933_, 1, v___x_2930_);
lean_ctor_set(v_reuseFailAlloc_2933_, 2, v_size_2908_);
lean_ctor_set(v_reuseFailAlloc_2933_, 3, v_tailOff_2910_);
lean_ctor_set_usize(v_reuseFailAlloc_2933_, 4, v_shift_2909_);
v___x_2932_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
return v___x_2932_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0___boxed(lean_object* v_a_2935_, lean_object* v_t_2936_, lean_object* v_i_2937_){
_start:
{
lean_object* v_res_2938_; 
v_res_2938_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(v_a_2935_, v_t_2936_, v_i_2937_);
lean_dec(v_i_2937_);
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0(lean_object* v_a_2939_, lean_object* v_v_2940_, lean_object* v_s_2941_){
_start:
{
lean_object* v_vars_2942_; lean_object* v_varMap_2943_; lean_object* v_vars_x27_2944_; lean_object* v_varMap_x27_2945_; lean_object* v_natToIntMap_2946_; lean_object* v_natDef_2947_; lean_object* v_dvds_2948_; lean_object* v_lowers_2949_; lean_object* v_uppers_2950_; lean_object* v_diseqs_2951_; lean_object* v_elimEqs_2952_; lean_object* v_elimStack_2953_; lean_object* v_occurs_2954_; lean_object* v_assignment_2955_; lean_object* v_nextCnstrId_2956_; uint8_t v_caseSplits_2957_; lean_object* v_conflict_x3f_2958_; lean_object* v_diseqSplits_2959_; lean_object* v_divMod_2960_; lean_object* v_toIntIds_2961_; lean_object* v_toIntInfos_2962_; lean_object* v_toIntTermMap_2963_; lean_object* v_toIntVarMap_2964_; uint8_t v_usedCommRing_2965_; lean_object* v_nonlinearOccs_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2974_; 
v_vars_2942_ = lean_ctor_get(v_s_2941_, 0);
v_varMap_2943_ = lean_ctor_get(v_s_2941_, 1);
v_vars_x27_2944_ = lean_ctor_get(v_s_2941_, 2);
v_varMap_x27_2945_ = lean_ctor_get(v_s_2941_, 3);
v_natToIntMap_2946_ = lean_ctor_get(v_s_2941_, 4);
v_natDef_2947_ = lean_ctor_get(v_s_2941_, 5);
v_dvds_2948_ = lean_ctor_get(v_s_2941_, 6);
v_lowers_2949_ = lean_ctor_get(v_s_2941_, 7);
v_uppers_2950_ = lean_ctor_get(v_s_2941_, 8);
v_diseqs_2951_ = lean_ctor_get(v_s_2941_, 9);
v_elimEqs_2952_ = lean_ctor_get(v_s_2941_, 10);
v_elimStack_2953_ = lean_ctor_get(v_s_2941_, 11);
v_occurs_2954_ = lean_ctor_get(v_s_2941_, 12);
v_assignment_2955_ = lean_ctor_get(v_s_2941_, 13);
v_nextCnstrId_2956_ = lean_ctor_get(v_s_2941_, 14);
v_caseSplits_2957_ = lean_ctor_get_uint8(v_s_2941_, sizeof(void*)*23);
v_conflict_x3f_2958_ = lean_ctor_get(v_s_2941_, 15);
v_diseqSplits_2959_ = lean_ctor_get(v_s_2941_, 16);
v_divMod_2960_ = lean_ctor_get(v_s_2941_, 17);
v_toIntIds_2961_ = lean_ctor_get(v_s_2941_, 18);
v_toIntInfos_2962_ = lean_ctor_get(v_s_2941_, 19);
v_toIntTermMap_2963_ = lean_ctor_get(v_s_2941_, 20);
v_toIntVarMap_2964_ = lean_ctor_get(v_s_2941_, 21);
v_usedCommRing_2965_ = lean_ctor_get_uint8(v_s_2941_, sizeof(void*)*23 + 1);
v_nonlinearOccs_2966_ = lean_ctor_get(v_s_2941_, 22);
v_isSharedCheck_2974_ = !lean_is_exclusive(v_s_2941_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2968_ = v_s_2941_;
v_isShared_2969_ = v_isSharedCheck_2974_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_nonlinearOccs_2966_);
lean_inc(v_toIntVarMap_2964_);
lean_inc(v_toIntTermMap_2963_);
lean_inc(v_toIntInfos_2962_);
lean_inc(v_toIntIds_2961_);
lean_inc(v_divMod_2960_);
lean_inc(v_diseqSplits_2959_);
lean_inc(v_conflict_x3f_2958_);
lean_inc(v_nextCnstrId_2956_);
lean_inc(v_assignment_2955_);
lean_inc(v_occurs_2954_);
lean_inc(v_elimStack_2953_);
lean_inc(v_elimEqs_2952_);
lean_inc(v_diseqs_2951_);
lean_inc(v_uppers_2950_);
lean_inc(v_lowers_2949_);
lean_inc(v_dvds_2948_);
lean_inc(v_natDef_2947_);
lean_inc(v_natToIntMap_2946_);
lean_inc(v_varMap_x27_2945_);
lean_inc(v_vars_x27_2944_);
lean_inc(v_varMap_2943_);
lean_inc(v_vars_2942_);
lean_dec(v_s_2941_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2974_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___x_2970_; lean_object* v___x_2972_; 
v___x_2970_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(v_a_2939_, v_lowers_2949_, v_v_2940_);
if (v_isShared_2969_ == 0)
{
lean_ctor_set(v___x_2968_, 7, v___x_2970_);
v___x_2972_ = v___x_2968_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_vars_2942_);
lean_ctor_set(v_reuseFailAlloc_2973_, 1, v_varMap_2943_);
lean_ctor_set(v_reuseFailAlloc_2973_, 2, v_vars_x27_2944_);
lean_ctor_set(v_reuseFailAlloc_2973_, 3, v_varMap_x27_2945_);
lean_ctor_set(v_reuseFailAlloc_2973_, 4, v_natToIntMap_2946_);
lean_ctor_set(v_reuseFailAlloc_2973_, 5, v_natDef_2947_);
lean_ctor_set(v_reuseFailAlloc_2973_, 6, v_dvds_2948_);
lean_ctor_set(v_reuseFailAlloc_2973_, 7, v___x_2970_);
lean_ctor_set(v_reuseFailAlloc_2973_, 8, v_uppers_2950_);
lean_ctor_set(v_reuseFailAlloc_2973_, 9, v_diseqs_2951_);
lean_ctor_set(v_reuseFailAlloc_2973_, 10, v_elimEqs_2952_);
lean_ctor_set(v_reuseFailAlloc_2973_, 11, v_elimStack_2953_);
lean_ctor_set(v_reuseFailAlloc_2973_, 12, v_occurs_2954_);
lean_ctor_set(v_reuseFailAlloc_2973_, 13, v_assignment_2955_);
lean_ctor_set(v_reuseFailAlloc_2973_, 14, v_nextCnstrId_2956_);
lean_ctor_set(v_reuseFailAlloc_2973_, 15, v_conflict_x3f_2958_);
lean_ctor_set(v_reuseFailAlloc_2973_, 16, v_diseqSplits_2959_);
lean_ctor_set(v_reuseFailAlloc_2973_, 17, v_divMod_2960_);
lean_ctor_set(v_reuseFailAlloc_2973_, 18, v_toIntIds_2961_);
lean_ctor_set(v_reuseFailAlloc_2973_, 19, v_toIntInfos_2962_);
lean_ctor_set(v_reuseFailAlloc_2973_, 20, v_toIntTermMap_2963_);
lean_ctor_set(v_reuseFailAlloc_2973_, 21, v_toIntVarMap_2964_);
lean_ctor_set(v_reuseFailAlloc_2973_, 22, v_nonlinearOccs_2966_);
lean_ctor_set_uint8(v_reuseFailAlloc_2973_, sizeof(void*)*23, v_caseSplits_2957_);
lean_ctor_set_uint8(v_reuseFailAlloc_2973_, sizeof(void*)*23 + 1, v_usedCommRing_2965_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
return v___x_2972_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0___boxed(lean_object* v_a_2975_, lean_object* v_v_2976_, lean_object* v_s_2977_){
_start:
{
lean_object* v_res_2978_; 
v_res_2978_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0(v_a_2975_, v_v_2976_, v_s_2977_);
lean_dec(v_v_2976_);
return v_res_2978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1(lean_object* v_a_2979_, lean_object* v_v_2980_, lean_object* v_s_2981_){
_start:
{
lean_object* v_vars_2982_; lean_object* v_varMap_2983_; lean_object* v_vars_x27_2984_; lean_object* v_varMap_x27_2985_; lean_object* v_natToIntMap_2986_; lean_object* v_natDef_2987_; lean_object* v_dvds_2988_; lean_object* v_lowers_2989_; lean_object* v_uppers_2990_; lean_object* v_diseqs_2991_; lean_object* v_elimEqs_2992_; lean_object* v_elimStack_2993_; lean_object* v_occurs_2994_; lean_object* v_assignment_2995_; lean_object* v_nextCnstrId_2996_; uint8_t v_caseSplits_2997_; lean_object* v_conflict_x3f_2998_; lean_object* v_diseqSplits_2999_; lean_object* v_divMod_3000_; lean_object* v_toIntIds_3001_; lean_object* v_toIntInfos_3002_; lean_object* v_toIntTermMap_3003_; lean_object* v_toIntVarMap_3004_; uint8_t v_usedCommRing_3005_; lean_object* v_nonlinearOccs_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3014_; 
v_vars_2982_ = lean_ctor_get(v_s_2981_, 0);
v_varMap_2983_ = lean_ctor_get(v_s_2981_, 1);
v_vars_x27_2984_ = lean_ctor_get(v_s_2981_, 2);
v_varMap_x27_2985_ = lean_ctor_get(v_s_2981_, 3);
v_natToIntMap_2986_ = lean_ctor_get(v_s_2981_, 4);
v_natDef_2987_ = lean_ctor_get(v_s_2981_, 5);
v_dvds_2988_ = lean_ctor_get(v_s_2981_, 6);
v_lowers_2989_ = lean_ctor_get(v_s_2981_, 7);
v_uppers_2990_ = lean_ctor_get(v_s_2981_, 8);
v_diseqs_2991_ = lean_ctor_get(v_s_2981_, 9);
v_elimEqs_2992_ = lean_ctor_get(v_s_2981_, 10);
v_elimStack_2993_ = lean_ctor_get(v_s_2981_, 11);
v_occurs_2994_ = lean_ctor_get(v_s_2981_, 12);
v_assignment_2995_ = lean_ctor_get(v_s_2981_, 13);
v_nextCnstrId_2996_ = lean_ctor_get(v_s_2981_, 14);
v_caseSplits_2997_ = lean_ctor_get_uint8(v_s_2981_, sizeof(void*)*23);
v_conflict_x3f_2998_ = lean_ctor_get(v_s_2981_, 15);
v_diseqSplits_2999_ = lean_ctor_get(v_s_2981_, 16);
v_divMod_3000_ = lean_ctor_get(v_s_2981_, 17);
v_toIntIds_3001_ = lean_ctor_get(v_s_2981_, 18);
v_toIntInfos_3002_ = lean_ctor_get(v_s_2981_, 19);
v_toIntTermMap_3003_ = lean_ctor_get(v_s_2981_, 20);
v_toIntVarMap_3004_ = lean_ctor_get(v_s_2981_, 21);
v_usedCommRing_3005_ = lean_ctor_get_uint8(v_s_2981_, sizeof(void*)*23 + 1);
v_nonlinearOccs_3006_ = lean_ctor_get(v_s_2981_, 22);
v_isSharedCheck_3014_ = !lean_is_exclusive(v_s_2981_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_3008_ = v_s_2981_;
v_isShared_3009_ = v_isSharedCheck_3014_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_nonlinearOccs_3006_);
lean_inc(v_toIntVarMap_3004_);
lean_inc(v_toIntTermMap_3003_);
lean_inc(v_toIntInfos_3002_);
lean_inc(v_toIntIds_3001_);
lean_inc(v_divMod_3000_);
lean_inc(v_diseqSplits_2999_);
lean_inc(v_conflict_x3f_2998_);
lean_inc(v_nextCnstrId_2996_);
lean_inc(v_assignment_2995_);
lean_inc(v_occurs_2994_);
lean_inc(v_elimStack_2993_);
lean_inc(v_elimEqs_2992_);
lean_inc(v_diseqs_2991_);
lean_inc(v_uppers_2990_);
lean_inc(v_lowers_2989_);
lean_inc(v_dvds_2988_);
lean_inc(v_natDef_2987_);
lean_inc(v_natToIntMap_2986_);
lean_inc(v_varMap_x27_2985_);
lean_inc(v_vars_x27_2984_);
lean_inc(v_varMap_2983_);
lean_inc(v_vars_2982_);
lean_dec(v_s_2981_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3014_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v___x_3010_; lean_object* v___x_3012_; 
v___x_3010_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(v_a_2979_, v_uppers_2990_, v_v_2980_);
if (v_isShared_3009_ == 0)
{
lean_ctor_set(v___x_3008_, 8, v___x_3010_);
v___x_3012_ = v___x_3008_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_vars_2982_);
lean_ctor_set(v_reuseFailAlloc_3013_, 1, v_varMap_2983_);
lean_ctor_set(v_reuseFailAlloc_3013_, 2, v_vars_x27_2984_);
lean_ctor_set(v_reuseFailAlloc_3013_, 3, v_varMap_x27_2985_);
lean_ctor_set(v_reuseFailAlloc_3013_, 4, v_natToIntMap_2986_);
lean_ctor_set(v_reuseFailAlloc_3013_, 5, v_natDef_2987_);
lean_ctor_set(v_reuseFailAlloc_3013_, 6, v_dvds_2988_);
lean_ctor_set(v_reuseFailAlloc_3013_, 7, v_lowers_2989_);
lean_ctor_set(v_reuseFailAlloc_3013_, 8, v___x_3010_);
lean_ctor_set(v_reuseFailAlloc_3013_, 9, v_diseqs_2991_);
lean_ctor_set(v_reuseFailAlloc_3013_, 10, v_elimEqs_2992_);
lean_ctor_set(v_reuseFailAlloc_3013_, 11, v_elimStack_2993_);
lean_ctor_set(v_reuseFailAlloc_3013_, 12, v_occurs_2994_);
lean_ctor_set(v_reuseFailAlloc_3013_, 13, v_assignment_2995_);
lean_ctor_set(v_reuseFailAlloc_3013_, 14, v_nextCnstrId_2996_);
lean_ctor_set(v_reuseFailAlloc_3013_, 15, v_conflict_x3f_2998_);
lean_ctor_set(v_reuseFailAlloc_3013_, 16, v_diseqSplits_2999_);
lean_ctor_set(v_reuseFailAlloc_3013_, 17, v_divMod_3000_);
lean_ctor_set(v_reuseFailAlloc_3013_, 18, v_toIntIds_3001_);
lean_ctor_set(v_reuseFailAlloc_3013_, 19, v_toIntInfos_3002_);
lean_ctor_set(v_reuseFailAlloc_3013_, 20, v_toIntTermMap_3003_);
lean_ctor_set(v_reuseFailAlloc_3013_, 21, v_toIntVarMap_3004_);
lean_ctor_set(v_reuseFailAlloc_3013_, 22, v_nonlinearOccs_3006_);
lean_ctor_set_uint8(v_reuseFailAlloc_3013_, sizeof(void*)*23, v_caseSplits_2997_);
lean_ctor_set_uint8(v_reuseFailAlloc_3013_, sizeof(void*)*23 + 1, v_usedCommRing_3005_);
v___x_3012_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
return v___x_3012_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1___boxed(lean_object* v_a_3015_, lean_object* v_v_3016_, lean_object* v_s_3017_){
_start:
{
lean_object* v_res_3018_; 
v_res_3018_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1(v_a_3015_, v_v_3016_, v_s_3017_);
lean_dec(v_v_3016_);
return v_res_3018_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3(void){
_start:
{
lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; 
v___x_3026_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2));
v___x_3027_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_3028_ = l_Lean_Name_append(v___x_3027_, v___x_3026_);
return v___x_3028_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6(void){
_start:
{
lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; 
v___x_3035_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5));
v___x_3036_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_3037_ = l_Lean_Name_append(v___x_3036_, v___x_3035_);
return v___x_3037_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9(void){
_start:
{
lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; 
v___x_3044_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__8));
v___x_3045_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_3046_ = l_Lean_Name_append(v___x_3045_, v___x_3044_);
return v___x_3046_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11(void){
_start:
{
lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; 
v___x_3051_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__10));
v___x_3052_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_3053_ = l_Lean_Name_append(v___x_3052_, v___x_3051_);
return v___x_3053_;
}
}
LEAN_EXPORT lean_object* lean_grind_cutsat_assert_le(lean_object* v_c_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_){
_start:
{
lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v___y_3103_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___x_3138_; 
v___x_3138_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_3055_, v_a_3063_);
if (lean_obj_tag(v___x_3138_) == 0)
{
lean_object* v_a_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3275_; 
v_a_3139_ = lean_ctor_get(v___x_3138_, 0);
v_isSharedCheck_3275_ = !lean_is_exclusive(v___x_3138_);
if (v_isSharedCheck_3275_ == 0)
{
v___x_3141_ = v___x_3138_;
v_isShared_3142_ = v_isSharedCheck_3275_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_a_3139_);
lean_dec(v___x_3138_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3275_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
uint8_t v___x_3143_; 
v___x_3143_ = lean_unbox(v_a_3139_);
lean_dec(v_a_3139_);
if (v___x_3143_ == 0)
{
lean_object* v_options_3144_; lean_object* v_inheritedTraceOptions_3145_; uint8_t v_hasTrace_3146_; lean_object* v___y_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___y_3154_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; 
lean_del_object(v___x_3141_);
v_options_3144_ = lean_ctor_get(v_a_3063_, 2);
v_inheritedTraceOptions_3145_ = lean_ctor_get(v_a_3063_, 13);
v_hasTrace_3146_ = lean_ctor_get_uint8(v_options_3144_, sizeof(void*)*1);
if (v_hasTrace_3146_ == 0)
{
v___y_3148_ = v_a_3055_;
v___y_3149_ = v_a_3056_;
v___y_3150_ = v_a_3057_;
v___y_3151_ = v_a_3058_;
v___y_3152_ = v_a_3059_;
v___y_3153_ = v_a_3060_;
v___y_3154_ = v_a_3061_;
v___y_3155_ = v_a_3062_;
v___y_3156_ = v_a_3063_;
v___y_3157_ = v_a_3064_;
goto v___jp_3147_;
}
else
{
lean_object* v___x_3257_; lean_object* v___x_3258_; uint8_t v___x_3259_; 
v___x_3257_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__10));
v___x_3258_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11);
v___x_3259_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3145_, v_options_3144_, v___x_3258_);
if (v___x_3259_ == 0)
{
v___y_3148_ = v_a_3055_;
v___y_3149_ = v_a_3056_;
v___y_3150_ = v_a_3057_;
v___y_3151_ = v_a_3058_;
v___y_3152_ = v_a_3059_;
v___y_3153_ = v_a_3060_;
v___y_3154_ = v_a_3061_;
v___y_3155_ = v_a_3062_;
v___y_3156_ = v_a_3063_;
v___y_3157_ = v_a_3064_;
goto v___jp_3147_;
}
else
{
lean_object* v___x_3260_; 
lean_inc_ref(v_c_3054_);
v___x_3260_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_3054_, v_a_3055_, v_a_3063_);
if (lean_obj_tag(v___x_3260_) == 0)
{
lean_object* v_a_3261_; lean_object* v___x_3262_; 
v_a_3261_ = lean_ctor_get(v___x_3260_, 0);
lean_inc(v_a_3261_);
lean_dec_ref(v___x_3260_);
v___x_3262_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3257_, v_a_3261_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_);
if (lean_obj_tag(v___x_3262_) == 0)
{
lean_dec_ref(v___x_3262_);
v___y_3148_ = v_a_3055_;
v___y_3149_ = v_a_3056_;
v___y_3150_ = v_a_3057_;
v___y_3151_ = v_a_3058_;
v___y_3152_ = v_a_3059_;
v___y_3153_ = v_a_3060_;
v___y_3154_ = v_a_3061_;
v___y_3155_ = v_a_3062_;
v___y_3156_ = v_a_3063_;
v___y_3157_ = v_a_3064_;
goto v___jp_3147_;
}
else
{
lean_dec(v_a_3064_);
lean_dec_ref(v_a_3063_);
lean_dec(v_a_3062_);
lean_dec_ref(v_a_3061_);
lean_dec(v_a_3060_);
lean_dec_ref(v_a_3059_);
lean_dec(v_a_3058_);
lean_dec_ref(v_a_3057_);
lean_dec(v_a_3056_);
lean_dec(v_a_3055_);
lean_dec_ref(v_c_3054_);
return v___x_3262_;
}
}
else
{
lean_object* v_a_3263_; lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3270_; 
lean_dec(v_a_3064_);
lean_dec_ref(v_a_3063_);
lean_dec(v_a_3062_);
lean_dec_ref(v_a_3061_);
lean_dec(v_a_3060_);
lean_dec_ref(v_a_3059_);
lean_dec(v_a_3058_);
lean_dec_ref(v_a_3057_);
lean_dec(v_a_3056_);
lean_dec(v_a_3055_);
lean_dec_ref(v_c_3054_);
v_a_3263_ = lean_ctor_get(v___x_3260_, 0);
v_isSharedCheck_3270_ = !lean_is_exclusive(v___x_3260_);
if (v_isSharedCheck_3270_ == 0)
{
v___x_3265_ = v___x_3260_;
v_isShared_3266_ = v_isSharedCheck_3270_;
goto v_resetjp_3264_;
}
else
{
lean_inc(v_a_3263_);
lean_dec(v___x_3260_);
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
v___jp_3147_:
{
lean_object* v___x_3158_; lean_object* v___x_3159_; 
v___x_3158_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_norm(v_c_3054_);
lean_inc_ref(v___y_3156_);
v___x_3159_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts(v___x_3158_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_);
if (lean_obj_tag(v___x_3159_) == 0)
{
lean_object* v_a_3160_; lean_object* v_p_3161_; uint8_t v___x_3162_; 
v_a_3160_ = lean_ctor_get(v___x_3159_, 0);
lean_inc(v_a_3160_);
lean_dec_ref(v___x_3159_);
v_p_3161_ = lean_ctor_get(v_a_3160_, 0);
v___x_3162_ = l_Int_Linear_Poly_isUnsatLe(v_p_3161_);
if (v___x_3162_ == 0)
{
uint8_t v___x_3163_; 
v___x_3163_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(v_a_3160_);
if (v___x_3163_ == 0)
{
if (lean_obj_tag(v_p_3161_) == 1)
{
lean_object* v_k_3164_; lean_object* v_v_3165_; lean_object* v___x_3166_; 
v_k_3164_ = lean_ctor_get(v_p_3161_, 0);
lean_inc(v_k_3164_);
v_v_3165_ = lean_ctor_get(v_p_3161_, 1);
lean_inc(v_v_3165_);
lean_inc(v_a_3160_);
v___x_3166_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq(v_a_3160_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_);
if (lean_obj_tag(v___x_3166_) == 0)
{
lean_object* v_a_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3205_; 
v_a_3167_ = lean_ctor_get(v___x_3166_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_3166_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3169_ = v___x_3166_;
v_isShared_3170_ = v_isSharedCheck_3205_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_a_3167_);
lean_dec(v___x_3166_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3205_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
uint8_t v___x_3171_; 
v___x_3171_ = lean_unbox(v_a_3167_);
lean_dec(v_a_3167_);
if (v___x_3171_ == 0)
{
lean_object* v___x_3172_; 
lean_del_object(v___x_3169_);
v___x_3172_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(v_a_3160_, v___y_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
lean_dec(v___y_3149_);
if (lean_obj_tag(v___x_3172_) == 0)
{
lean_object* v_options_3173_; lean_object* v_a_3174_; lean_object* v_inheritedTraceOptions_3175_; uint8_t v_hasTrace_3176_; lean_object* v___f_3177_; lean_object* v___f_3178_; 
v_options_3173_ = lean_ctor_get(v___y_3156_, 2);
v_a_3174_ = lean_ctor_get(v___x_3172_, 0);
lean_inc_n(v_a_3174_, 3);
lean_dec_ref(v___x_3172_);
v_inheritedTraceOptions_3175_ = lean_ctor_get(v___y_3156_, 13);
v_hasTrace_3176_ = lean_ctor_get_uint8(v_options_3173_, sizeof(void*)*1);
lean_inc_n(v_v_3165_, 2);
v___f_3177_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3177_, 0, v_a_3174_);
lean_closure_set(v___f_3177_, 1, v_v_3165_);
v___f_3178_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3178_, 0, v_a_3174_);
lean_closure_set(v___f_3178_, 1, v_v_3165_);
if (v_hasTrace_3176_ == 0)
{
v___y_3097_ = v_v_3165_;
v___y_3098_ = v_k_3164_;
v___y_3099_ = v_a_3174_;
v___y_3100_ = v___f_3177_;
v___y_3101_ = v___f_3178_;
v___y_3102_ = v___y_3148_;
v___y_3103_ = v___y_3154_;
v___y_3104_ = v___y_3155_;
v___y_3105_ = v___y_3156_;
v___y_3106_ = v___y_3157_;
goto v___jp_3096_;
}
else
{
lean_object* v___x_3179_; lean_object* v___x_3180_; uint8_t v___x_3181_; 
v___x_3179_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2));
v___x_3180_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3);
v___x_3181_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3175_, v_options_3173_, v___x_3180_);
if (v___x_3181_ == 0)
{
v___y_3097_ = v_v_3165_;
v___y_3098_ = v_k_3164_;
v___y_3099_ = v_a_3174_;
v___y_3100_ = v___f_3177_;
v___y_3101_ = v___f_3178_;
v___y_3102_ = v___y_3148_;
v___y_3103_ = v___y_3154_;
v___y_3104_ = v___y_3155_;
v___y_3105_ = v___y_3156_;
v___y_3106_ = v___y_3157_;
goto v___jp_3096_;
}
else
{
lean_object* v___x_3182_; 
lean_inc(v_a_3174_);
v___x_3182_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_a_3174_, v___y_3148_, v___y_3156_);
if (lean_obj_tag(v___x_3182_) == 0)
{
lean_object* v_a_3183_; lean_object* v___x_3184_; 
v_a_3183_ = lean_ctor_get(v___x_3182_, 0);
lean_inc(v_a_3183_);
lean_dec_ref(v___x_3182_);
v___x_3184_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3179_, v_a_3183_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_);
if (lean_obj_tag(v___x_3184_) == 0)
{
lean_dec_ref(v___x_3184_);
v___y_3097_ = v_v_3165_;
v___y_3098_ = v_k_3164_;
v___y_3099_ = v_a_3174_;
v___y_3100_ = v___f_3177_;
v___y_3101_ = v___f_3178_;
v___y_3102_ = v___y_3148_;
v___y_3103_ = v___y_3154_;
v___y_3104_ = v___y_3155_;
v___y_3105_ = v___y_3156_;
v___y_3106_ = v___y_3157_;
goto v___jp_3096_;
}
else
{
lean_dec_ref(v___f_3178_);
lean_dec_ref(v___f_3177_);
lean_dec(v_a_3174_);
lean_dec(v_v_3165_);
lean_dec(v_k_3164_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
lean_dec(v___y_3148_);
return v___x_3184_;
}
}
else
{
lean_object* v_a_3185_; lean_object* v___x_3187_; uint8_t v_isShared_3188_; uint8_t v_isSharedCheck_3192_; 
lean_dec_ref(v___f_3178_);
lean_dec_ref(v___f_3177_);
lean_dec(v_a_3174_);
lean_dec(v_v_3165_);
lean_dec(v_k_3164_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
lean_dec(v___y_3148_);
v_a_3185_ = lean_ctor_get(v___x_3182_, 0);
v_isSharedCheck_3192_ = !lean_is_exclusive(v___x_3182_);
if (v_isSharedCheck_3192_ == 0)
{
v___x_3187_ = v___x_3182_;
v_isShared_3188_ = v_isSharedCheck_3192_;
goto v_resetjp_3186_;
}
else
{
lean_inc(v_a_3185_);
lean_dec(v___x_3182_);
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
}
}
else
{
lean_object* v_a_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3200_; 
lean_dec(v_v_3165_);
lean_dec(v_k_3164_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
lean_dec(v___y_3148_);
v_a_3193_ = lean_ctor_get(v___x_3172_, 0);
v_isSharedCheck_3200_ = !lean_is_exclusive(v___x_3172_);
if (v_isSharedCheck_3200_ == 0)
{
v___x_3195_ = v___x_3172_;
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_a_3193_);
lean_dec(v___x_3172_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v___x_3198_; 
if (v_isShared_3196_ == 0)
{
v___x_3198_ = v___x_3195_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v_a_3193_);
v___x_3198_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
return v___x_3198_;
}
}
}
}
else
{
lean_object* v___x_3201_; lean_object* v___x_3203_; 
lean_dec(v_v_3165_);
lean_dec(v_k_3164_);
lean_dec(v_a_3160_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
lean_dec(v___y_3149_);
lean_dec(v___y_3148_);
v___x_3201_ = lean_box(0);
if (v_isShared_3170_ == 0)
{
lean_ctor_set(v___x_3169_, 0, v___x_3201_);
v___x_3203_ = v___x_3169_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v___x_3201_);
v___x_3203_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
return v___x_3203_;
}
}
}
}
else
{
lean_object* v_a_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3213_; 
lean_dec(v_v_3165_);
lean_dec(v_k_3164_);
lean_dec(v_a_3160_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
lean_dec(v___y_3149_);
lean_dec(v___y_3148_);
v_a_3206_ = lean_ctor_get(v___x_3166_, 0);
v_isSharedCheck_3213_ = !lean_is_exclusive(v___x_3166_);
if (v_isSharedCheck_3213_ == 0)
{
v___x_3208_ = v___x_3166_;
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_a_3206_);
lean_dec(v___x_3166_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3211_; 
if (v_isShared_3209_ == 0)
{
v___x_3211_ = v___x_3208_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v_a_3206_);
v___x_3211_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
return v___x_3211_;
}
}
}
}
else
{
lean_object* v___x_3214_; 
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
lean_dec(v___y_3149_);
v___x_3214_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_a_3160_, v___y_3148_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
lean_dec(v___y_3148_);
return v___x_3214_;
}
}
else
{
lean_object* v_options_3215_; uint8_t v_hasTrace_3216_; 
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
lean_dec(v___y_3149_);
v_options_3215_ = lean_ctor_get(v___y_3156_, 2);
v_hasTrace_3216_ = lean_ctor_get_uint8(v_options_3215_, sizeof(void*)*1);
if (v_hasTrace_3216_ == 0)
{
lean_dec(v_a_3160_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
lean_dec(v___y_3148_);
goto v___jp_3066_;
}
else
{
lean_object* v_inheritedTraceOptions_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; uint8_t v___x_3220_; 
v_inheritedTraceOptions_3217_ = lean_ctor_get(v___y_3156_, 13);
v___x_3218_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5));
v___x_3219_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6);
v___x_3220_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3217_, v_options_3215_, v___x_3219_);
if (v___x_3220_ == 0)
{
lean_dec(v_a_3160_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
lean_dec(v___y_3148_);
goto v___jp_3066_;
}
else
{
lean_object* v___x_3221_; 
v___x_3221_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_a_3160_, v___y_3148_, v___y_3156_);
lean_dec(v___y_3148_);
if (lean_obj_tag(v___x_3221_) == 0)
{
lean_object* v_a_3222_; lean_object* v___x_3223_; 
v_a_3222_ = lean_ctor_get(v___x_3221_, 0);
lean_inc(v_a_3222_);
lean_dec_ref(v___x_3221_);
v___x_3223_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3218_, v_a_3222_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
if (lean_obj_tag(v___x_3223_) == 0)
{
lean_dec_ref(v___x_3223_);
goto v___jp_3066_;
}
else
{
return v___x_3223_;
}
}
else
{
lean_object* v_a_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3231_; 
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
v_a_3224_ = lean_ctor_get(v___x_3221_, 0);
v_isSharedCheck_3231_ = !lean_is_exclusive(v___x_3221_);
if (v_isSharedCheck_3231_ == 0)
{
v___x_3226_ = v___x_3221_;
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_a_3224_);
lean_dec(v___x_3221_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3231_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3229_; 
if (v_isShared_3227_ == 0)
{
v___x_3229_ = v___x_3226_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v_a_3224_);
v___x_3229_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
return v___x_3229_;
}
}
}
}
}
}
}
else
{
lean_object* v_options_3232_; uint8_t v_hasTrace_3233_; 
v_options_3232_ = lean_ctor_get(v___y_3156_, 2);
v_hasTrace_3233_ = lean_ctor_get_uint8(v_options_3232_, sizeof(void*)*1);
if (v_hasTrace_3233_ == 0)
{
v___y_3116_ = v_a_3160_;
v___y_3117_ = v___y_3148_;
v___y_3118_ = v___y_3149_;
v___y_3119_ = v___y_3150_;
v___y_3120_ = v___y_3151_;
v___y_3121_ = v___y_3152_;
v___y_3122_ = v___y_3153_;
v___y_3123_ = v___y_3154_;
v___y_3124_ = v___y_3155_;
v___y_3125_ = v___y_3156_;
v___y_3126_ = v___y_3157_;
goto v___jp_3115_;
}
else
{
lean_object* v_inheritedTraceOptions_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; uint8_t v___x_3237_; 
v_inheritedTraceOptions_3234_ = lean_ctor_get(v___y_3156_, 13);
v___x_3235_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__8));
v___x_3236_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9);
v___x_3237_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3234_, v_options_3232_, v___x_3236_);
if (v___x_3237_ == 0)
{
v___y_3116_ = v_a_3160_;
v___y_3117_ = v___y_3148_;
v___y_3118_ = v___y_3149_;
v___y_3119_ = v___y_3150_;
v___y_3120_ = v___y_3151_;
v___y_3121_ = v___y_3152_;
v___y_3122_ = v___y_3153_;
v___y_3123_ = v___y_3154_;
v___y_3124_ = v___y_3155_;
v___y_3125_ = v___y_3156_;
v___y_3126_ = v___y_3157_;
goto v___jp_3115_;
}
else
{
lean_object* v___x_3238_; 
lean_inc(v_a_3160_);
v___x_3238_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_a_3160_, v___y_3148_, v___y_3156_);
if (lean_obj_tag(v___x_3238_) == 0)
{
lean_object* v_a_3239_; lean_object* v___x_3240_; 
v_a_3239_ = lean_ctor_get(v___x_3238_, 0);
lean_inc(v_a_3239_);
lean_dec_ref(v___x_3238_);
v___x_3240_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3235_, v_a_3239_, v___y_3154_, v___y_3155_, v___y_3156_, v___y_3157_);
if (lean_obj_tag(v___x_3240_) == 0)
{
lean_dec_ref(v___x_3240_);
v___y_3116_ = v_a_3160_;
v___y_3117_ = v___y_3148_;
v___y_3118_ = v___y_3149_;
v___y_3119_ = v___y_3150_;
v___y_3120_ = v___y_3151_;
v___y_3121_ = v___y_3152_;
v___y_3122_ = v___y_3153_;
v___y_3123_ = v___y_3154_;
v___y_3124_ = v___y_3155_;
v___y_3125_ = v___y_3156_;
v___y_3126_ = v___y_3157_;
goto v___jp_3115_;
}
else
{
lean_dec(v_a_3160_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
lean_dec(v___y_3149_);
lean_dec(v___y_3148_);
return v___x_3240_;
}
}
else
{
lean_object* v_a_3241_; lean_object* v___x_3243_; uint8_t v_isShared_3244_; uint8_t v_isSharedCheck_3248_; 
lean_dec(v_a_3160_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
lean_dec(v___y_3149_);
lean_dec(v___y_3148_);
v_a_3241_ = lean_ctor_get(v___x_3238_, 0);
v_isSharedCheck_3248_ = !lean_is_exclusive(v___x_3238_);
if (v_isSharedCheck_3248_ == 0)
{
v___x_3243_ = v___x_3238_;
v_isShared_3244_ = v_isSharedCheck_3248_;
goto v_resetjp_3242_;
}
else
{
lean_inc(v_a_3241_);
lean_dec(v___x_3238_);
v___x_3243_ = lean_box(0);
v_isShared_3244_ = v_isSharedCheck_3248_;
goto v_resetjp_3242_;
}
v_resetjp_3242_:
{
lean_object* v___x_3246_; 
if (v_isShared_3244_ == 0)
{
v___x_3246_ = v___x_3243_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3247_; 
v_reuseFailAlloc_3247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3247_, 0, v_a_3241_);
v___x_3246_ = v_reuseFailAlloc_3247_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
return v___x_3246_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3249_; lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3256_; 
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
lean_dec(v___y_3155_);
lean_dec_ref(v___y_3154_);
lean_dec(v___y_3153_);
lean_dec_ref(v___y_3152_);
lean_dec(v___y_3151_);
lean_dec_ref(v___y_3150_);
lean_dec(v___y_3149_);
lean_dec(v___y_3148_);
v_a_3249_ = lean_ctor_get(v___x_3159_, 0);
v_isSharedCheck_3256_ = !lean_is_exclusive(v___x_3159_);
if (v_isSharedCheck_3256_ == 0)
{
v___x_3251_ = v___x_3159_;
v_isShared_3252_ = v_isSharedCheck_3256_;
goto v_resetjp_3250_;
}
else
{
lean_inc(v_a_3249_);
lean_dec(v___x_3159_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3256_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v___x_3254_; 
if (v_isShared_3252_ == 0)
{
v___x_3254_ = v___x_3251_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v_a_3249_);
v___x_3254_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
return v___x_3254_;
}
}
}
}
}
else
{
lean_object* v___x_3271_; lean_object* v___x_3273_; 
lean_dec(v_a_3064_);
lean_dec_ref(v_a_3063_);
lean_dec(v_a_3062_);
lean_dec_ref(v_a_3061_);
lean_dec(v_a_3060_);
lean_dec_ref(v_a_3059_);
lean_dec(v_a_3058_);
lean_dec_ref(v_a_3057_);
lean_dec(v_a_3056_);
lean_dec(v_a_3055_);
lean_dec_ref(v_c_3054_);
v___x_3271_ = lean_box(0);
if (v_isShared_3142_ == 0)
{
lean_ctor_set(v___x_3141_, 0, v___x_3271_);
v___x_3273_ = v___x_3141_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v___x_3271_);
v___x_3273_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
return v___x_3273_;
}
}
}
}
else
{
lean_object* v_a_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3283_; 
lean_dec(v_a_3064_);
lean_dec_ref(v_a_3063_);
lean_dec(v_a_3062_);
lean_dec_ref(v_a_3061_);
lean_dec(v_a_3060_);
lean_dec_ref(v_a_3059_);
lean_dec(v_a_3058_);
lean_dec_ref(v_a_3057_);
lean_dec(v_a_3056_);
lean_dec(v_a_3055_);
lean_dec_ref(v_c_3054_);
v_a_3276_ = lean_ctor_get(v___x_3138_, 0);
v_isSharedCheck_3283_ = !lean_is_exclusive(v___x_3138_);
if (v_isSharedCheck_3283_ == 0)
{
v___x_3278_ = v___x_3138_;
v_isShared_3279_ = v_isSharedCheck_3283_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_a_3276_);
lean_dec(v___x_3138_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3283_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
lean_object* v___x_3281_; 
if (v_isShared_3279_ == 0)
{
v___x_3281_ = v___x_3278_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3282_; 
v_reuseFailAlloc_3282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3282_, 0, v_a_3276_);
v___x_3281_ = v_reuseFailAlloc_3282_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
return v___x_3281_;
}
}
}
v___jp_3066_:
{
lean_object* v___x_3067_; lean_object* v___x_3068_; 
v___x_3067_ = lean_box(0);
v___x_3068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3067_);
return v___x_3068_;
}
v___jp_3069_:
{
lean_object* v___x_3074_; 
v___x_3074_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(v___y_3071_, v___y_3072_, v___y_3073_);
lean_dec_ref(v___y_3073_);
if (lean_obj_tag(v___x_3074_) == 0)
{
lean_object* v_a_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3087_; 
v_a_3075_ = lean_ctor_get(v___x_3074_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3074_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3077_ = v___x_3074_;
v_isShared_3078_ = v_isSharedCheck_3087_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_a_3075_);
lean_dec(v___x_3074_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3087_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
uint8_t v___x_3079_; uint8_t v___x_3080_; uint8_t v___x_3081_; 
v___x_3079_ = 0;
v___x_3080_ = lean_unbox(v_a_3075_);
lean_dec(v_a_3075_);
v___x_3081_ = l_Lean_instBEqLBool_beq(v___x_3080_, v___x_3079_);
if (v___x_3081_ == 0)
{
lean_object* v___x_3082_; lean_object* v___x_3084_; 
lean_dec(v___y_3072_);
lean_dec(v___y_3070_);
v___x_3082_ = lean_box(0);
if (v_isShared_3078_ == 0)
{
lean_ctor_set(v___x_3077_, 0, v___x_3082_);
v___x_3084_ = v___x_3077_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v___x_3082_);
v___x_3084_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
return v___x_3084_;
}
}
else
{
lean_object* v___x_3086_; 
lean_del_object(v___x_3077_);
v___x_3086_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v___y_3070_, v___y_3072_);
lean_dec(v___y_3072_);
return v___x_3086_;
}
}
}
else
{
lean_object* v_a_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3095_; 
lean_dec(v___y_3072_);
lean_dec(v___y_3070_);
v_a_3088_ = lean_ctor_get(v___x_3074_, 0);
v_isSharedCheck_3095_ = !lean_is_exclusive(v___x_3074_);
if (v_isSharedCheck_3095_ == 0)
{
v___x_3090_ = v___x_3074_;
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_a_3088_);
lean_dec(v___x_3074_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3095_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
lean_object* v___x_3093_; 
if (v_isShared_3091_ == 0)
{
v___x_3093_ = v___x_3090_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v_a_3088_);
v___x_3093_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
return v___x_3093_;
}
}
}
}
v___jp_3096_:
{
lean_object* v_p_3107_; lean_object* v___x_3108_; 
v_p_3107_ = lean_ctor_get(v___y_3099_, 0);
lean_inc_ref(v_p_3107_);
v___x_3108_ = l_Int_Linear_Poly_updateOccs___redArg(v_p_3107_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_);
lean_dec(v___y_3106_);
lean_dec(v___y_3104_);
lean_dec_ref(v___y_3103_);
if (lean_obj_tag(v___x_3108_) == 0)
{
lean_object* v___x_3109_; uint8_t v___x_3110_; 
lean_dec_ref(v___x_3108_);
v___x_3109_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9);
v___x_3110_ = lean_int_dec_lt(v___y_3098_, v___x_3109_);
lean_dec(v___y_3098_);
if (v___x_3110_ == 0)
{
lean_object* v___x_3111_; lean_object* v___x_3112_; 
lean_dec_ref(v___y_3100_);
v___x_3111_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_3112_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3111_, v___y_3101_, v___y_3102_);
if (lean_obj_tag(v___x_3112_) == 0)
{
lean_dec_ref(v___x_3112_);
v___y_3070_ = v___y_3097_;
v___y_3071_ = v___y_3099_;
v___y_3072_ = v___y_3102_;
v___y_3073_ = v___y_3105_;
goto v___jp_3069_;
}
else
{
lean_dec_ref(v___y_3105_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3099_);
lean_dec(v___y_3097_);
return v___x_3112_;
}
}
else
{
lean_object* v___x_3113_; lean_object* v___x_3114_; 
lean_dec_ref(v___y_3101_);
v___x_3113_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_3114_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3113_, v___y_3100_, v___y_3102_);
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_dec_ref(v___x_3114_);
v___y_3070_ = v___y_3097_;
v___y_3071_ = v___y_3099_;
v___y_3072_ = v___y_3102_;
v___y_3073_ = v___y_3105_;
goto v___jp_3069_;
}
else
{
lean_dec_ref(v___y_3105_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3099_);
lean_dec(v___y_3097_);
return v___x_3114_;
}
}
}
else
{
lean_dec_ref(v___y_3105_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec_ref(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec(v___y_3098_);
lean_dec(v___y_3097_);
return v___x_3108_;
}
}
v___jp_3115_:
{
lean_object* v___x_3127_; lean_object* v___x_3128_; 
v___x_3127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3127_, 0, v___y_3116_);
v___x_3128_ = l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(v___x_3127_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_);
lean_dec(v___y_3126_);
lean_dec_ref(v___y_3125_);
lean_dec(v___y_3124_);
lean_dec_ref(v___y_3123_);
lean_dec(v___y_3122_);
lean_dec_ref(v___y_3121_);
lean_dec(v___y_3120_);
lean_dec_ref(v___y_3119_);
lean_dec(v___y_3118_);
lean_dec(v___y_3117_);
if (lean_obj_tag(v___x_3128_) == 0)
{
lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3136_; 
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_3128_);
if (v_isSharedCheck_3136_ == 0)
{
lean_object* v_unused_3137_; 
v_unused_3137_ = lean_ctor_get(v___x_3128_, 0);
lean_dec(v_unused_3137_);
v___x_3130_ = v___x_3128_;
v_isShared_3131_ = v_isSharedCheck_3136_;
goto v_resetjp_3129_;
}
else
{
lean_dec(v___x_3128_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3136_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3132_; lean_object* v___x_3134_; 
v___x_3132_ = lean_box(0);
if (v_isShared_3131_ == 0)
{
lean_ctor_set(v___x_3130_, 0, v___x_3132_);
v___x_3134_ = v___x_3130_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v___x_3132_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
return v___x_3134_;
}
}
}
else
{
return v___x_3128_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___boxed(lean_object* v_c_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_){
_start:
{
lean_object* v_res_3296_; 
v_res_3296_ = lean_grind_cutsat_assert_le(v_c_3284_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_);
return v_res_3296_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1(void){
_start:
{
lean_object* v___x_3298_; lean_object* v___x_3299_; 
v___x_3298_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__0));
v___x_3299_ = l_Lean_stringToMessageData(v___x_3298_);
return v___x_3299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(lean_object* v_e_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_){
_start:
{
lean_object* v___x_3308_; 
v___x_3308_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_3301_);
if (lean_obj_tag(v___x_3308_) == 0)
{
lean_object* v_a_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3322_; 
v_a_3309_ = lean_ctor_get(v___x_3308_, 0);
v_isSharedCheck_3322_ = !lean_is_exclusive(v___x_3308_);
if (v_isSharedCheck_3322_ == 0)
{
v___x_3311_ = v___x_3308_;
v_isShared_3312_ = v_isSharedCheck_3322_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_a_3309_);
lean_dec(v___x_3308_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3322_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
uint8_t v___x_3313_; 
v___x_3313_ = lean_unbox(v_a_3309_);
lean_dec(v_a_3309_);
if (v___x_3313_ == 0)
{
lean_object* v___x_3314_; lean_object* v___x_3316_; 
lean_dec_ref(v_e_3300_);
v___x_3314_ = lean_box(0);
if (v_isShared_3312_ == 0)
{
lean_ctor_set(v___x_3311_, 0, v___x_3314_);
v___x_3316_ = v___x_3311_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v___x_3314_);
v___x_3316_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
return v___x_3316_;
}
}
else
{
lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; 
lean_del_object(v___x_3311_);
v___x_3318_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1);
v___x_3319_ = l_Lean_indentExpr(v_e_3300_);
v___x_3320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3320_, 0, v___x_3318_);
lean_ctor_set(v___x_3320_, 1, v___x_3319_);
v___x_3321_ = l_Lean_Meta_Sym_reportIssue(v___x_3320_, v_a_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_);
return v___x_3321_;
}
}
}
else
{
lean_object* v_a_3323_; lean_object* v___x_3325_; uint8_t v_isShared_3326_; uint8_t v_isSharedCheck_3330_; 
lean_dec_ref(v_e_3300_);
v_a_3323_ = lean_ctor_get(v___x_3308_, 0);
v_isSharedCheck_3330_ = !lean_is_exclusive(v___x_3308_);
if (v_isSharedCheck_3330_ == 0)
{
v___x_3325_ = v___x_3308_;
v_isShared_3326_ = v_isSharedCheck_3330_;
goto v_resetjp_3324_;
}
else
{
lean_inc(v_a_3323_);
lean_dec(v___x_3308_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___boxed(lean_object* v_e_3331_, lean_object* v_a_3332_, lean_object* v_a_3333_, lean_object* v_a_3334_, lean_object* v_a_3335_, lean_object* v_a_3336_, lean_object* v_a_3337_, lean_object* v_a_3338_){
_start:
{
lean_object* v_res_3339_; 
v_res_3339_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(v_e_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_, v_a_3336_, v_a_3337_);
lean_dec(v_a_3337_);
lean_dec_ref(v_a_3336_);
lean_dec(v_a_3335_);
lean_dec_ref(v_a_3334_);
lean_dec(v_a_3333_);
lean_dec_ref(v_a_3332_);
return v_res_3339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized(lean_object* v_e_3340_, lean_object* v_a_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_, lean_object* v_a_3350_){
_start:
{
lean_object* v___x_3352_; 
v___x_3352_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(v_e_3340_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_, v_a_3350_);
return v___x_3352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___boxed(lean_object* v_e_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_, lean_object* v_a_3361_, lean_object* v_a_3362_, lean_object* v_a_3363_, lean_object* v_a_3364_){
_start:
{
lean_object* v_res_3365_; 
v_res_3365_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized(v_e_3353_, v_a_3354_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_, v_a_3361_, v_a_3362_, v_a_3363_);
lean_dec(v_a_3363_);
lean_dec_ref(v_a_3362_);
lean_dec(v_a_3361_);
lean_dec_ref(v_a_3360_);
lean_dec(v_a_3359_);
lean_dec_ref(v_a_3358_);
lean_dec(v_a_3357_);
lean_dec_ref(v_a_3356_);
lean_dec(v_a_3355_);
lean_dec(v_a_3354_);
return v_res_3365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f(lean_object* v_e_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_, lean_object* v_a_3375_, lean_object* v_a_3376_, lean_object* v_a_3377_, lean_object* v_a_3378_, lean_object* v_a_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_){
_start:
{
lean_object* v___x_3383_; 
lean_inc_ref(v_e_3371_);
v___x_3383_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3371_, v_a_3379_);
if (lean_obj_tag(v___x_3383_) == 0)
{
lean_object* v_a_3384_; lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3499_; 
v_a_3384_ = lean_ctor_get(v___x_3383_, 0);
v_isSharedCheck_3499_ = !lean_is_exclusive(v___x_3383_);
if (v_isSharedCheck_3499_ == 0)
{
v___x_3386_ = v___x_3383_;
v_isShared_3387_ = v_isSharedCheck_3499_;
goto v_resetjp_3385_;
}
else
{
lean_inc(v_a_3384_);
lean_dec(v___x_3383_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3499_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
lean_object* v___x_3393_; uint8_t v___x_3394_; 
v___x_3393_ = l_Lean_Expr_cleanupAnnotations(v_a_3384_);
v___x_3394_ = l_Lean_Expr_isApp(v___x_3393_);
if (v___x_3394_ == 0)
{
lean_dec_ref(v___x_3393_);
lean_dec_ref(v_e_3371_);
goto v___jp_3388_;
}
else
{
lean_object* v_arg_3395_; lean_object* v___x_3396_; uint8_t v___x_3397_; 
v_arg_3395_ = lean_ctor_get(v___x_3393_, 1);
lean_inc_ref(v_arg_3395_);
v___x_3396_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3393_);
v___x_3397_ = l_Lean_Expr_isApp(v___x_3396_);
if (v___x_3397_ == 0)
{
lean_dec_ref(v___x_3396_);
lean_dec_ref(v_arg_3395_);
lean_dec_ref(v_e_3371_);
goto v___jp_3388_;
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
lean_dec_ref(v_arg_3395_);
lean_dec_ref(v_e_3371_);
goto v___jp_3388_;
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
lean_dec_ref(v_arg_3395_);
lean_dec_ref(v_e_3371_);
goto v___jp_3388_;
}
else
{
lean_object* v___x_3404_; lean_object* v___x_3405_; uint8_t v___x_3406_; 
v___x_3404_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3402_);
v___x_3405_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2));
v___x_3406_ = l_Lean_Expr_isConstOf(v___x_3404_, v___x_3405_);
lean_dec_ref(v___x_3404_);
if (v___x_3406_ == 0)
{
lean_dec_ref(v_arg_3401_);
lean_dec_ref(v_arg_3398_);
lean_dec_ref(v_arg_3395_);
lean_dec_ref(v_e_3371_);
goto v___jp_3388_;
}
else
{
lean_object* v___x_3407_; 
lean_del_object(v___x_3386_);
v___x_3407_ = l_Lean_Meta_Structural_isInstLEInt___redArg(v_arg_3401_, v_a_3379_);
if (lean_obj_tag(v___x_3407_) == 0)
{
lean_object* v_a_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3490_; 
v_a_3408_ = lean_ctor_get(v___x_3407_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3410_ = v___x_3407_;
v_isShared_3411_ = v_isSharedCheck_3490_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_a_3408_);
lean_dec(v___x_3407_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3490_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
uint8_t v___x_3412_; 
v___x_3412_ = lean_unbox(v_a_3408_);
lean_dec(v_a_3408_);
if (v___x_3412_ == 0)
{
lean_object* v___x_3413_; lean_object* v___x_3415_; 
lean_dec_ref(v_arg_3398_);
lean_dec_ref(v_arg_3395_);
lean_dec_ref(v_e_3371_);
v___x_3413_ = lean_box(0);
if (v_isShared_3411_ == 0)
{
lean_ctor_set(v___x_3410_, 0, v___x_3413_);
v___x_3415_ = v___x_3410_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v___x_3413_);
v___x_3415_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
return v___x_3415_;
}
}
else
{
lean_object* v___x_3417_; 
lean_del_object(v___x_3410_);
v___x_3417_ = l_Lean_Meta_getIntValue_x3f(v_arg_3395_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_);
if (lean_obj_tag(v___x_3417_) == 0)
{
lean_object* v_a_3418_; 
v_a_3418_ = lean_ctor_get(v___x_3417_, 0);
lean_inc(v_a_3418_);
lean_dec_ref(v___x_3417_);
if (lean_obj_tag(v_a_3418_) == 1)
{
lean_object* v_val_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3463_; 
v_val_3419_ = lean_ctor_get(v_a_3418_, 0);
v_isSharedCheck_3463_ = !lean_is_exclusive(v_a_3418_);
if (v_isSharedCheck_3463_ == 0)
{
v___x_3421_ = v_a_3418_;
v_isShared_3422_ = v_isSharedCheck_3463_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_val_3419_);
lean_dec(v_a_3418_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3463_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v___x_3423_; uint8_t v___x_3424_; 
v___x_3423_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9);
v___x_3424_ = lean_int_dec_eq(v_val_3419_, v___x_3423_);
lean_dec(v_val_3419_);
if (v___x_3424_ == 0)
{
lean_object* v___x_3425_; 
lean_del_object(v___x_3421_);
lean_dec_ref(v_arg_3398_);
v___x_3425_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(v_e_3371_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_);
if (lean_obj_tag(v___x_3425_) == 0)
{
lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3433_; 
v_isSharedCheck_3433_ = !lean_is_exclusive(v___x_3425_);
if (v_isSharedCheck_3433_ == 0)
{
lean_object* v_unused_3434_; 
v_unused_3434_ = lean_ctor_get(v___x_3425_, 0);
lean_dec(v_unused_3434_);
v___x_3427_ = v___x_3425_;
v_isShared_3428_ = v_isSharedCheck_3433_;
goto v_resetjp_3426_;
}
else
{
lean_dec(v___x_3425_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3433_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
lean_object* v___x_3429_; lean_object* v___x_3431_; 
v___x_3429_ = lean_box(0);
if (v_isShared_3428_ == 0)
{
lean_ctor_set(v___x_3427_, 0, v___x_3429_);
v___x_3431_ = v___x_3427_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v___x_3429_);
v___x_3431_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
return v___x_3431_;
}
}
}
else
{
lean_object* v_a_3435_; lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3442_; 
v_a_3435_ = lean_ctor_get(v___x_3425_, 0);
v_isSharedCheck_3442_ = !lean_is_exclusive(v___x_3425_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3437_ = v___x_3425_;
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
else
{
lean_inc(v_a_3435_);
lean_dec(v___x_3425_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3442_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v___x_3440_; 
if (v_isShared_3438_ == 0)
{
v___x_3440_ = v___x_3437_;
goto v_reusejp_3439_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_a_3435_);
v___x_3440_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3439_;
}
v_reusejp_3439_:
{
return v___x_3440_;
}
}
}
}
else
{
lean_object* v___x_3443_; 
lean_dec_ref(v_e_3371_);
v___x_3443_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(v_arg_3398_, v_a_3372_, v_a_3373_, v_a_3374_, v_a_3375_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_);
if (lean_obj_tag(v___x_3443_) == 0)
{
lean_object* v_a_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3454_; 
v_a_3444_ = lean_ctor_get(v___x_3443_, 0);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3443_);
if (v_isSharedCheck_3454_ == 0)
{
v___x_3446_ = v___x_3443_;
v_isShared_3447_ = v_isSharedCheck_3454_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_a_3444_);
lean_dec(v___x_3443_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3454_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v___x_3449_; 
if (v_isShared_3422_ == 0)
{
lean_ctor_set(v___x_3421_, 0, v_a_3444_);
v___x_3449_ = v___x_3421_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v_a_3444_);
v___x_3449_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
lean_object* v___x_3451_; 
if (v_isShared_3447_ == 0)
{
lean_ctor_set(v___x_3446_, 0, v___x_3449_);
v___x_3451_ = v___x_3446_;
goto v_reusejp_3450_;
}
else
{
lean_object* v_reuseFailAlloc_3452_; 
v_reuseFailAlloc_3452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3452_, 0, v___x_3449_);
v___x_3451_ = v_reuseFailAlloc_3452_;
goto v_reusejp_3450_;
}
v_reusejp_3450_:
{
return v___x_3451_;
}
}
}
}
else
{
lean_object* v_a_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3462_; 
lean_del_object(v___x_3421_);
v_a_3455_ = lean_ctor_get(v___x_3443_, 0);
v_isSharedCheck_3462_ = !lean_is_exclusive(v___x_3443_);
if (v_isSharedCheck_3462_ == 0)
{
v___x_3457_ = v___x_3443_;
v_isShared_3458_ = v_isSharedCheck_3462_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_a_3455_);
lean_dec(v___x_3443_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3462_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v___x_3460_; 
if (v_isShared_3458_ == 0)
{
v___x_3460_ = v___x_3457_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_a_3455_);
v___x_3460_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
return v___x_3460_;
}
}
}
}
}
}
else
{
lean_object* v___x_3464_; 
lean_dec(v_a_3418_);
lean_dec_ref(v_arg_3398_);
v___x_3464_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(v_e_3371_, v_a_3376_, v_a_3377_, v_a_3378_, v_a_3379_, v_a_3380_, v_a_3381_);
if (lean_obj_tag(v___x_3464_) == 0)
{
lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3472_; 
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3472_ == 0)
{
lean_object* v_unused_3473_; 
v_unused_3473_ = lean_ctor_get(v___x_3464_, 0);
lean_dec(v_unused_3473_);
v___x_3466_ = v___x_3464_;
v_isShared_3467_ = v_isSharedCheck_3472_;
goto v_resetjp_3465_;
}
else
{
lean_dec(v___x_3464_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3472_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3468_; lean_object* v___x_3470_; 
v___x_3468_ = lean_box(0);
if (v_isShared_3467_ == 0)
{
lean_ctor_set(v___x_3466_, 0, v___x_3468_);
v___x_3470_ = v___x_3466_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v___x_3468_);
v___x_3470_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
return v___x_3470_;
}
}
}
else
{
lean_object* v_a_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3481_; 
v_a_3474_ = lean_ctor_get(v___x_3464_, 0);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3464_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3476_ = v___x_3464_;
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_a_3474_);
lean_dec(v___x_3464_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
lean_object* v___x_3479_; 
if (v_isShared_3477_ == 0)
{
v___x_3479_ = v___x_3476_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_a_3474_);
v___x_3479_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
return v___x_3479_;
}
}
}
}
}
else
{
lean_object* v_a_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3489_; 
lean_dec_ref(v_arg_3398_);
lean_dec_ref(v_e_3371_);
v_a_3482_ = lean_ctor_get(v___x_3417_, 0);
v_isSharedCheck_3489_ = !lean_is_exclusive(v___x_3417_);
if (v_isSharedCheck_3489_ == 0)
{
v___x_3484_ = v___x_3417_;
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_a_3482_);
lean_dec(v___x_3417_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v___x_3487_; 
if (v_isShared_3485_ == 0)
{
v___x_3487_ = v___x_3484_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v_a_3482_);
v___x_3487_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3486_;
}
v_reusejp_3486_:
{
return v___x_3487_;
}
}
}
}
}
}
else
{
lean_object* v_a_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3498_; 
lean_dec_ref(v_arg_3398_);
lean_dec_ref(v_arg_3395_);
lean_dec_ref(v_e_3371_);
v_a_3491_ = lean_ctor_get(v___x_3407_, 0);
v_isSharedCheck_3498_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3498_ == 0)
{
v___x_3493_ = v___x_3407_;
v_isShared_3494_ = v_isSharedCheck_3498_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_a_3491_);
lean_dec(v___x_3407_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3498_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___x_3496_; 
if (v_isShared_3494_ == 0)
{
v___x_3496_ = v___x_3493_;
goto v_reusejp_3495_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v_a_3491_);
v___x_3496_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3495_;
}
v_reusejp_3495_:
{
return v___x_3496_;
}
}
}
}
}
}
}
}
v___jp_3388_:
{
lean_object* v___x_3389_; lean_object* v___x_3391_; 
v___x_3389_ = lean_box(0);
if (v_isShared_3387_ == 0)
{
lean_ctor_set(v___x_3386_, 0, v___x_3389_);
v___x_3391_ = v___x_3386_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v___x_3389_);
v___x_3391_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
return v___x_3391_;
}
}
}
}
else
{
lean_object* v_a_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3507_; 
lean_dec_ref(v_e_3371_);
v_a_3500_ = lean_ctor_get(v___x_3383_, 0);
v_isSharedCheck_3507_ = !lean_is_exclusive(v___x_3383_);
if (v_isSharedCheck_3507_ == 0)
{
v___x_3502_ = v___x_3383_;
v_isShared_3503_ = v_isSharedCheck_3507_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_a_3500_);
lean_dec(v___x_3383_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3507_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v___x_3505_; 
if (v_isShared_3503_ == 0)
{
v___x_3505_ = v___x_3502_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3506_; 
v_reuseFailAlloc_3506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3506_, 0, v_a_3500_);
v___x_3505_ = v_reuseFailAlloc_3506_;
goto v_reusejp_3504_;
}
v_reusejp_3504_:
{
return v___x_3505_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___boxed(lean_object* v_e_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_){
_start:
{
lean_object* v_res_3520_; 
v_res_3520_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f(v_e_3508_, v_a_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_);
lean_dec(v_a_3518_);
lean_dec_ref(v_a_3517_);
lean_dec(v_a_3516_);
lean_dec_ref(v_a_3515_);
lean_dec(v_a_3514_);
lean_dec_ref(v_a_3513_);
lean_dec(v_a_3512_);
lean_dec_ref(v_a_3511_);
lean_dec(v_a_3510_);
lean_dec(v_a_3509_);
return v_res_3520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(lean_object* v_c_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_){
_start:
{
lean_object* v_p_3533_; lean_object* v___x_3534_; 
v_p_3533_ = lean_ctor_get(v_c_3521_, 0);
lean_inc_ref(v_p_3533_);
v___x_3534_ = l_Int_Linear_Poly_normCommRing_x3f(v_p_3533_, v_a_3522_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_, v_a_3531_);
if (lean_obj_tag(v___x_3534_) == 0)
{
lean_object* v_a_3535_; 
v_a_3535_ = lean_ctor_get(v___x_3534_, 0);
lean_inc(v_a_3535_);
lean_dec_ref(v___x_3534_);
if (lean_obj_tag(v_a_3535_) == 1)
{
lean_object* v_val_3536_; lean_object* v_snd_3537_; lean_object* v_fst_3538_; lean_object* v_fst_3539_; lean_object* v_snd_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3549_; 
v_val_3536_ = lean_ctor_get(v_a_3535_, 0);
lean_inc(v_val_3536_);
lean_dec_ref(v_a_3535_);
v_snd_3537_ = lean_ctor_get(v_val_3536_, 1);
lean_inc(v_snd_3537_);
v_fst_3538_ = lean_ctor_get(v_val_3536_, 0);
lean_inc(v_fst_3538_);
lean_dec(v_val_3536_);
v_fst_3539_ = lean_ctor_get(v_snd_3537_, 0);
v_snd_3540_ = lean_ctor_get(v_snd_3537_, 1);
v_isSharedCheck_3549_ = !lean_is_exclusive(v_snd_3537_);
if (v_isSharedCheck_3549_ == 0)
{
v___x_3542_ = v_snd_3537_;
v_isShared_3543_ = v_isSharedCheck_3549_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_snd_3540_);
lean_inc(v_fst_3539_);
lean_dec(v_snd_3537_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3549_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3544_; lean_object* v___x_3546_; 
v___x_3544_ = lean_alloc_ctor(17, 3, 0);
lean_ctor_set(v___x_3544_, 0, v_c_3521_);
lean_ctor_set(v___x_3544_, 1, v_fst_3538_);
lean_ctor_set(v___x_3544_, 2, v_fst_3539_);
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 1, v___x_3544_);
lean_ctor_set(v___x_3542_, 0, v_snd_3540_);
v___x_3546_ = v___x_3542_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v_snd_3540_);
lean_ctor_set(v_reuseFailAlloc_3548_, 1, v___x_3544_);
v___x_3546_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
lean_object* v___x_3547_; 
lean_inc(v_a_3531_);
lean_inc_ref(v_a_3530_);
lean_inc(v_a_3529_);
lean_inc_ref(v_a_3528_);
lean_inc(v_a_3527_);
lean_inc_ref(v_a_3526_);
lean_inc(v_a_3525_);
lean_inc_ref(v_a_3524_);
lean_inc(v_a_3523_);
lean_inc(v_a_3522_);
v___x_3547_ = lean_grind_cutsat_assert_le(v___x_3546_, v_a_3522_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_, v_a_3531_);
return v___x_3547_;
}
}
}
else
{
lean_object* v___x_3550_; 
lean_dec(v_a_3535_);
lean_inc(v_a_3531_);
lean_inc_ref(v_a_3530_);
lean_inc(v_a_3529_);
lean_inc_ref(v_a_3528_);
lean_inc(v_a_3527_);
lean_inc_ref(v_a_3526_);
lean_inc(v_a_3525_);
lean_inc_ref(v_a_3524_);
lean_inc(v_a_3523_);
lean_inc(v_a_3522_);
v___x_3550_ = lean_grind_cutsat_assert_le(v_c_3521_, v_a_3522_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_, v_a_3531_);
return v___x_3550_;
}
}
else
{
lean_object* v_a_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3558_; 
lean_dec_ref(v_c_3521_);
v_a_3551_ = lean_ctor_get(v___x_3534_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v___x_3534_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3553_ = v___x_3534_;
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_a_3551_);
lean_dec(v___x_3534_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3558_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v___x_3556_; 
if (v_isShared_3554_ == 0)
{
v___x_3556_ = v___x_3553_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v_a_3551_);
v___x_3556_ = v_reuseFailAlloc_3557_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
return v___x_3556_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore___boxed(lean_object* v_c_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_){
_start:
{
lean_object* v_res_3571_; 
v_res_3571_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v_c_3559_, v_a_3560_, v_a_3561_, v_a_3562_, v_a_3563_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_, v_a_3568_, v_a_3569_);
lean_dec(v_a_3569_);
lean_dec_ref(v_a_3568_);
lean_dec(v_a_3567_);
lean_dec_ref(v_a_3566_);
lean_dec(v_a_3565_);
lean_dec_ref(v_a_3564_);
lean_dec(v_a_3563_);
lean_dec_ref(v_a_3562_);
lean_dec(v_a_3561_);
lean_dec(v_a_3560_);
return v_res_3571_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0(void){
_start:
{
lean_object* v___x_3572_; lean_object* v___x_3573_; 
v___x_3572_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
v___x_3573_ = lean_int_neg(v___x_3572_);
return v___x_3573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe(lean_object* v_e_3574_, uint8_t v_eqTrue_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_){
_start:
{
lean_object* v___x_3587_; 
lean_inc_ref(v_e_3574_);
v___x_3587_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f(v_e_3574_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_, v_a_3585_);
if (lean_obj_tag(v___x_3587_) == 0)
{
lean_object* v_a_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3614_; 
v_a_3588_ = lean_ctor_get(v___x_3587_, 0);
v_isSharedCheck_3614_ = !lean_is_exclusive(v___x_3587_);
if (v_isSharedCheck_3614_ == 0)
{
v___x_3590_ = v___x_3587_;
v_isShared_3591_ = v_isSharedCheck_3614_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_a_3588_);
lean_dec(v___x_3587_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3614_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
if (lean_obj_tag(v_a_3588_) == 1)
{
lean_del_object(v___x_3590_);
if (v_eqTrue_3575_ == 0)
{
lean_object* v_val_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; 
v_val_3592_ = lean_ctor_get(v_a_3588_, 0);
lean_inc_n(v_val_3592_, 2);
lean_dec_ref(v_a_3588_);
v___x_3593_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
v___x_3594_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0);
v___x_3595_ = l_Int_Linear_Poly_mul(v_val_3592_, v___x_3594_);
v___x_3596_ = l_Int_Linear_Poly_addConst(v___x_3595_, v___x_3593_);
v___x_3597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3597_, 0, v_e_3574_);
lean_ctor_set(v___x_3597_, 1, v_val_3592_);
v___x_3598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3598_, 0, v___x_3596_);
lean_ctor_set(v___x_3598_, 1, v___x_3597_);
v___x_3599_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v___x_3598_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_, v_a_3585_);
return v___x_3599_;
}
else
{
lean_object* v_val_3600_; lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3609_; 
v_val_3600_ = lean_ctor_get(v_a_3588_, 0);
v_isSharedCheck_3609_ = !lean_is_exclusive(v_a_3588_);
if (v_isSharedCheck_3609_ == 0)
{
v___x_3602_ = v_a_3588_;
v_isShared_3603_ = v_isSharedCheck_3609_;
goto v_resetjp_3601_;
}
else
{
lean_inc(v_val_3600_);
lean_dec(v_a_3588_);
v___x_3602_ = lean_box(0);
v_isShared_3603_ = v_isSharedCheck_3609_;
goto v_resetjp_3601_;
}
v_resetjp_3601_:
{
lean_object* v___x_3605_; 
if (v_isShared_3603_ == 0)
{
lean_ctor_set_tag(v___x_3602_, 0);
lean_ctor_set(v___x_3602_, 0, v_e_3574_);
v___x_3605_ = v___x_3602_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v_e_3574_);
v___x_3605_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
lean_object* v___x_3606_; lean_object* v___x_3607_; 
v___x_3606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3606_, 0, v_val_3600_);
lean_ctor_set(v___x_3606_, 1, v___x_3605_);
v___x_3607_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v___x_3606_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_, v_a_3585_);
return v___x_3607_;
}
}
}
}
else
{
lean_object* v___x_3610_; lean_object* v___x_3612_; 
lean_dec(v_a_3588_);
lean_dec_ref(v_e_3574_);
v___x_3610_ = lean_box(0);
if (v_isShared_3591_ == 0)
{
lean_ctor_set(v___x_3590_, 0, v___x_3610_);
v___x_3612_ = v___x_3590_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v___x_3610_);
v___x_3612_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
return v___x_3612_;
}
}
}
}
else
{
lean_object* v_a_3615_; lean_object* v___x_3617_; uint8_t v_isShared_3618_; uint8_t v_isSharedCheck_3622_; 
lean_dec_ref(v_e_3574_);
v_a_3615_ = lean_ctor_get(v___x_3587_, 0);
v_isSharedCheck_3622_ = !lean_is_exclusive(v___x_3587_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3617_ = v___x_3587_;
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
else
{
lean_inc(v_a_3615_);
lean_dec(v___x_3587_);
v___x_3617_ = lean_box(0);
v_isShared_3618_ = v_isSharedCheck_3622_;
goto v_resetjp_3616_;
}
v_resetjp_3616_:
{
lean_object* v___x_3620_; 
if (v_isShared_3618_ == 0)
{
v___x_3620_ = v___x_3617_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_a_3615_);
v___x_3620_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
return v___x_3620_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___boxed(lean_object* v_e_3623_, lean_object* v_eqTrue_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_, lean_object* v_a_3635_){
_start:
{
uint8_t v_eqTrue_boxed_3636_; lean_object* v_res_3637_; 
v_eqTrue_boxed_3636_ = lean_unbox(v_eqTrue_3624_);
v_res_3637_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe(v_e_3623_, v_eqTrue_boxed_3636_, v_a_3625_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_, v_a_3630_, v_a_3631_, v_a_3632_, v_a_3633_, v_a_3634_);
lean_dec(v_a_3634_);
lean_dec_ref(v_a_3633_);
lean_dec(v_a_3632_);
lean_dec_ref(v_a_3631_);
lean_dec(v_a_3630_);
lean_dec_ref(v_a_3629_);
lean_dec(v_a_3628_);
lean_dec_ref(v_a_3627_);
lean_dec(v_a_3626_);
lean_dec(v_a_3625_);
return v_res_3637_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0(void){
_start:
{
lean_object* v___x_3638_; lean_object* v___x_3639_; 
v___x_3638_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
v___x_3639_ = l_Lean_mkIntLit(v___x_3638_);
return v___x_3639_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5(void){
_start:
{
lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; 
v___x_3647_ = lean_box(0);
v___x_3648_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__4));
v___x_3649_ = l_Lean_mkConst(v___x_3648_, v___x_3647_);
return v___x_3649_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8(void){
_start:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; 
v___x_3655_ = lean_box(0);
v___x_3656_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__7));
v___x_3657_ = l_Lean_mkConst(v___x_3656_, v___x_3655_);
return v___x_3657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe(lean_object* v_e_3658_, uint8_t v_eqTrue_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_, lean_object* v_a_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_, lean_object* v_a_3669_){
_start:
{
lean_object* v___y_3672_; lean_object* v___y_3673_; lean_object* v_fst_3674_; lean_object* v_snd_3675_; lean_object* v___x_3704_; uint8_t v___x_3705_; 
lean_inc_ref(v_e_3658_);
v___x_3704_ = l_Lean_Expr_cleanupAnnotations(v_e_3658_);
v___x_3705_ = l_Lean_Expr_isApp(v___x_3704_);
if (v___x_3705_ == 0)
{
lean_dec_ref(v___x_3704_);
lean_dec_ref(v_e_3658_);
goto v___jp_3701_;
}
else
{
lean_object* v_arg_3706_; lean_object* v___x_3707_; uint8_t v___x_3708_; 
v_arg_3706_ = lean_ctor_get(v___x_3704_, 1);
lean_inc_ref(v_arg_3706_);
v___x_3707_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3704_);
v___x_3708_ = l_Lean_Expr_isApp(v___x_3707_);
if (v___x_3708_ == 0)
{
lean_dec_ref(v___x_3707_);
lean_dec_ref(v_arg_3706_);
lean_dec_ref(v_e_3658_);
goto v___jp_3701_;
}
else
{
lean_object* v_arg_3709_; lean_object* v___y_3711_; lean_object* v___x_3749_; uint8_t v___x_3750_; 
v_arg_3709_ = lean_ctor_get(v___x_3707_, 1);
lean_inc_ref(v_arg_3709_);
v___x_3749_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3707_);
v___x_3750_ = l_Lean_Expr_isApp(v___x_3749_);
if (v___x_3750_ == 0)
{
lean_dec_ref(v___x_3749_);
lean_dec_ref(v_arg_3709_);
lean_dec_ref(v_arg_3706_);
lean_dec_ref(v_e_3658_);
goto v___jp_3701_;
}
else
{
lean_object* v___x_3751_; uint8_t v___x_3752_; 
v___x_3751_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3749_);
v___x_3752_ = l_Lean_Expr_isApp(v___x_3751_);
if (v___x_3752_ == 0)
{
lean_dec_ref(v___x_3751_);
lean_dec_ref(v_arg_3709_);
lean_dec_ref(v_arg_3706_);
lean_dec_ref(v_e_3658_);
goto v___jp_3701_;
}
else
{
lean_object* v___x_3753_; lean_object* v___x_3754_; uint8_t v___x_3755_; 
v___x_3753_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3751_);
v___x_3754_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2));
v___x_3755_ = l_Lean_Expr_isConstOf(v___x_3753_, v___x_3754_);
lean_dec_ref(v___x_3753_);
if (v___x_3755_ == 0)
{
lean_dec_ref(v_arg_3709_);
lean_dec_ref(v_arg_3706_);
lean_dec_ref(v_e_3658_);
goto v___jp_3701_;
}
else
{
if (v_eqTrue_3659_ == 0)
{
lean_object* v___x_3756_; 
v___x_3756_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5);
v___y_3711_ = v___x_3756_;
goto v___jp_3710_;
}
else
{
lean_object* v___x_3757_; 
v___x_3757_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8);
v___y_3711_ = v___x_3757_;
goto v___jp_3710_;
}
}
}
}
v___jp_3710_:
{
lean_object* v___x_3712_; 
v___x_3712_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_3658_, v_a_3660_);
if (lean_obj_tag(v___x_3712_) == 0)
{
lean_object* v_a_3713_; lean_object* v___x_3714_; 
v_a_3713_ = lean_ctor_get(v___x_3712_, 0);
lean_inc(v_a_3713_);
lean_dec_ref(v___x_3712_);
lean_inc_ref(v_arg_3709_);
v___x_3714_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_3709_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_);
if (lean_obj_tag(v___x_3714_) == 0)
{
lean_object* v_a_3715_; lean_object* v_fst_3716_; lean_object* v_snd_3717_; lean_object* v___x_3718_; 
v_a_3715_ = lean_ctor_get(v___x_3714_, 0);
lean_inc(v_a_3715_);
lean_dec_ref(v___x_3714_);
v_fst_3716_ = lean_ctor_get(v_a_3715_, 0);
lean_inc(v_fst_3716_);
v_snd_3717_ = lean_ctor_get(v_a_3715_, 1);
lean_inc(v_snd_3717_);
lean_dec(v_a_3715_);
lean_inc_ref(v_arg_3706_);
v___x_3718_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_3706_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_);
if (lean_obj_tag(v___x_3718_) == 0)
{
lean_object* v_a_3719_; lean_object* v_fst_3720_; lean_object* v_snd_3721_; lean_object* v___x_3722_; 
v_a_3719_ = lean_ctor_get(v___x_3718_, 0);
lean_inc(v_a_3719_);
lean_dec_ref(v___x_3718_);
v_fst_3720_ = lean_ctor_get(v_a_3719_, 0);
lean_inc_n(v_fst_3720_, 2);
v_snd_3721_ = lean_ctor_get(v_a_3719_, 1);
lean_inc(v_snd_3721_);
lean_dec(v_a_3719_);
lean_inc(v_fst_3716_);
lean_inc_ref(v___y_3711_);
v___x_3722_ = l_Lean_mkApp6(v___y_3711_, v_arg_3709_, v_arg_3706_, v_fst_3716_, v_fst_3720_, v_snd_3717_, v_snd_3721_);
if (v_eqTrue_3659_ == 0)
{
lean_object* v___x_3723_; lean_object* v___x_3724_; 
v___x_3723_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0);
v___x_3724_ = l_Lean_mkIntAdd(v_fst_3720_, v___x_3723_);
v___y_3672_ = v_a_3713_;
v___y_3673_ = v___x_3722_;
v_fst_3674_ = v___x_3724_;
v_snd_3675_ = v_fst_3716_;
goto v___jp_3671_;
}
else
{
v___y_3672_ = v_a_3713_;
v___y_3673_ = v___x_3722_;
v_fst_3674_ = v_fst_3716_;
v_snd_3675_ = v_fst_3720_;
goto v___jp_3671_;
}
}
else
{
lean_object* v_a_3725_; lean_object* v___x_3727_; uint8_t v_isShared_3728_; uint8_t v_isSharedCheck_3732_; 
lean_dec(v_snd_3717_);
lean_dec(v_fst_3716_);
lean_dec(v_a_3713_);
lean_dec_ref(v_arg_3709_);
lean_dec_ref(v_arg_3706_);
lean_dec_ref(v_e_3658_);
v_a_3725_ = lean_ctor_get(v___x_3718_, 0);
v_isSharedCheck_3732_ = !lean_is_exclusive(v___x_3718_);
if (v_isSharedCheck_3732_ == 0)
{
v___x_3727_ = v___x_3718_;
v_isShared_3728_ = v_isSharedCheck_3732_;
goto v_resetjp_3726_;
}
else
{
lean_inc(v_a_3725_);
lean_dec(v___x_3718_);
v___x_3727_ = lean_box(0);
v_isShared_3728_ = v_isSharedCheck_3732_;
goto v_resetjp_3726_;
}
v_resetjp_3726_:
{
lean_object* v___x_3730_; 
if (v_isShared_3728_ == 0)
{
v___x_3730_ = v___x_3727_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v_a_3725_);
v___x_3730_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
return v___x_3730_;
}
}
}
}
else
{
lean_object* v_a_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3740_; 
lean_dec(v_a_3713_);
lean_dec_ref(v_arg_3709_);
lean_dec_ref(v_arg_3706_);
lean_dec_ref(v_e_3658_);
v_a_3733_ = lean_ctor_get(v___x_3714_, 0);
v_isSharedCheck_3740_ = !lean_is_exclusive(v___x_3714_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3735_ = v___x_3714_;
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_a_3733_);
lean_dec(v___x_3714_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
lean_object* v___x_3738_; 
if (v_isShared_3736_ == 0)
{
v___x_3738_ = v___x_3735_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v_a_3733_);
v___x_3738_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
return v___x_3738_;
}
}
}
}
else
{
lean_object* v_a_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3748_; 
lean_dec_ref(v_arg_3709_);
lean_dec_ref(v_arg_3706_);
lean_dec_ref(v_e_3658_);
v_a_3741_ = lean_ctor_get(v___x_3712_, 0);
v_isSharedCheck_3748_ = !lean_is_exclusive(v___x_3712_);
if (v_isSharedCheck_3748_ == 0)
{
v___x_3743_ = v___x_3712_;
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
else
{
lean_inc(v_a_3741_);
lean_dec(v___x_3712_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3748_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v___x_3746_; 
if (v_isShared_3744_ == 0)
{
v___x_3746_ = v___x_3743_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v_a_3741_);
v___x_3746_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
return v___x_3746_;
}
}
}
}
}
}
v___jp_3671_:
{
lean_object* v___x_3676_; 
lean_inc(v___y_3672_);
v___x_3676_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_3674_, v___y_3672_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_);
if (lean_obj_tag(v___x_3676_) == 0)
{
lean_object* v_a_3677_; lean_object* v___x_3678_; 
v_a_3677_ = lean_ctor_get(v___x_3676_, 0);
lean_inc(v_a_3677_);
lean_dec_ref(v___x_3676_);
v___x_3678_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_snd_3675_, v___y_3672_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_);
if (lean_obj_tag(v___x_3678_) == 0)
{
lean_object* v_a_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; 
v_a_3679_ = lean_ctor_get(v___x_3678_, 0);
lean_inc_n(v_a_3679_, 2);
lean_dec_ref(v___x_3678_);
lean_inc(v_a_3677_);
v___x_3680_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3680_, 0, v_a_3677_);
lean_ctor_set(v___x_3680_, 1, v_a_3679_);
v___x_3681_ = l_Int_Linear_Expr_norm(v___x_3680_);
lean_dec_ref(v___x_3680_);
v___x_3682_ = lean_alloc_ctor(2, 4, 1);
lean_ctor_set(v___x_3682_, 0, v_e_3658_);
lean_ctor_set(v___x_3682_, 1, v___y_3673_);
lean_ctor_set(v___x_3682_, 2, v_a_3677_);
lean_ctor_set(v___x_3682_, 3, v_a_3679_);
lean_ctor_set_uint8(v___x_3682_, sizeof(void*)*4, v_eqTrue_3659_);
v___x_3683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3683_, 0, v___x_3681_);
lean_ctor_set(v___x_3683_, 1, v___x_3682_);
v___x_3684_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v___x_3683_, v_a_3660_, v_a_3661_, v_a_3662_, v_a_3663_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_);
return v___x_3684_;
}
else
{
lean_object* v_a_3685_; lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3692_; 
lean_dec(v_a_3677_);
lean_dec_ref(v___y_3673_);
lean_dec_ref(v_e_3658_);
v_a_3685_ = lean_ctor_get(v___x_3678_, 0);
v_isSharedCheck_3692_ = !lean_is_exclusive(v___x_3678_);
if (v_isSharedCheck_3692_ == 0)
{
v___x_3687_ = v___x_3678_;
v_isShared_3688_ = v_isSharedCheck_3692_;
goto v_resetjp_3686_;
}
else
{
lean_inc(v_a_3685_);
lean_dec(v___x_3678_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3692_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
lean_object* v___x_3690_; 
if (v_isShared_3688_ == 0)
{
v___x_3690_ = v___x_3687_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v_a_3685_);
v___x_3690_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
return v___x_3690_;
}
}
}
}
else
{
lean_object* v_a_3693_; lean_object* v___x_3695_; uint8_t v_isShared_3696_; uint8_t v_isSharedCheck_3700_; 
lean_dec_ref(v_snd_3675_);
lean_dec_ref(v___y_3673_);
lean_dec(v___y_3672_);
lean_dec_ref(v_e_3658_);
v_a_3693_ = lean_ctor_get(v___x_3676_, 0);
v_isSharedCheck_3700_ = !lean_is_exclusive(v___x_3676_);
if (v_isSharedCheck_3700_ == 0)
{
v___x_3695_ = v___x_3676_;
v_isShared_3696_ = v_isSharedCheck_3700_;
goto v_resetjp_3694_;
}
else
{
lean_inc(v_a_3693_);
lean_dec(v___x_3676_);
v___x_3695_ = lean_box(0);
v_isShared_3696_ = v_isSharedCheck_3700_;
goto v_resetjp_3694_;
}
v_resetjp_3694_:
{
lean_object* v___x_3698_; 
if (v_isShared_3696_ == 0)
{
v___x_3698_ = v___x_3695_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3699_; 
v_reuseFailAlloc_3699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3699_, 0, v_a_3693_);
v___x_3698_ = v_reuseFailAlloc_3699_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
return v___x_3698_;
}
}
}
}
v___jp_3701_:
{
lean_object* v___x_3702_; lean_object* v___x_3703_; 
v___x_3702_ = lean_box(0);
v___x_3703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3703_, 0, v___x_3702_);
return v___x_3703_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___boxed(lean_object* v_e_3758_, lean_object* v_eqTrue_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_, lean_object* v_a_3770_){
_start:
{
uint8_t v_eqTrue_boxed_3771_; lean_object* v_res_3772_; 
v_eqTrue_boxed_3771_ = lean_unbox(v_eqTrue_3759_);
v_res_3772_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe(v_e_3758_, v_eqTrue_boxed_3771_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_, v_a_3769_);
lean_dec(v_a_3769_);
lean_dec_ref(v_a_3768_);
lean_dec(v_a_3767_);
lean_dec_ref(v_a_3766_);
lean_dec(v_a_3765_);
lean_dec_ref(v_a_3764_);
lean_dec(v_a_3763_);
lean_dec_ref(v_a_3762_);
lean_dec(v_a_3761_);
lean_dec(v_a_3760_);
return v_res_3772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe(lean_object* v_e_3773_, uint8_t v_eqTrue_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_, lean_object* v_a_3783_, lean_object* v_a_3784_, lean_object* v_a_3785_){
_start:
{
lean_object* v___y_3791_; lean_object* v___y_3792_; lean_object* v___y_3793_; lean_object* v___y_3794_; lean_object* v___y_3795_; lean_object* v___y_3796_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v_fst_3803_; lean_object* v_snd_3804_; lean_object* v_____x_3831_; lean_object* v___y_3832_; lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v___y_3835_; lean_object* v___y_3836_; lean_object* v___y_3837_; lean_object* v___y_3838_; lean_object* v___y_3839_; lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v___y_3842_; 
if (v_eqTrue_3774_ == 0)
{
lean_object* v___x_3896_; 
v___x_3896_ = l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLE_x3f___redArg(v_a_3775_, v_a_3776_, v_a_3782_, v_a_3783_, v_a_3784_, v_a_3785_);
if (lean_obj_tag(v___x_3896_) == 0)
{
lean_object* v_a_3897_; 
v_a_3897_ = lean_ctor_get(v___x_3896_, 0);
lean_inc(v_a_3897_);
lean_dec_ref(v___x_3896_);
v_____x_3831_ = v_a_3897_;
v___y_3832_ = v_a_3775_;
v___y_3833_ = v_a_3776_;
v___y_3834_ = v_a_3777_;
v___y_3835_ = v_a_3778_;
v___y_3836_ = v_a_3779_;
v___y_3837_ = v_a_3780_;
v___y_3838_ = v_a_3781_;
v___y_3839_ = v_a_3782_;
v___y_3840_ = v_a_3783_;
v___y_3841_ = v_a_3784_;
v___y_3842_ = v_a_3785_;
goto v___jp_3830_;
}
else
{
lean_object* v_a_3898_; lean_object* v___x_3900_; uint8_t v_isShared_3901_; uint8_t v_isSharedCheck_3905_; 
lean_dec_ref(v_e_3773_);
v_a_3898_ = lean_ctor_get(v___x_3896_, 0);
v_isSharedCheck_3905_ = !lean_is_exclusive(v___x_3896_);
if (v_isSharedCheck_3905_ == 0)
{
v___x_3900_ = v___x_3896_;
v_isShared_3901_ = v_isSharedCheck_3905_;
goto v_resetjp_3899_;
}
else
{
lean_inc(v_a_3898_);
lean_dec(v___x_3896_);
v___x_3900_ = lean_box(0);
v_isShared_3901_ = v_isSharedCheck_3905_;
goto v_resetjp_3899_;
}
v_resetjp_3899_:
{
lean_object* v___x_3903_; 
if (v_isShared_3901_ == 0)
{
v___x_3903_ = v___x_3900_;
goto v_reusejp_3902_;
}
else
{
lean_object* v_reuseFailAlloc_3904_; 
v_reuseFailAlloc_3904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3904_, 0, v_a_3898_);
v___x_3903_ = v_reuseFailAlloc_3904_;
goto v_reusejp_3902_;
}
v_reusejp_3902_:
{
return v___x_3903_;
}
}
}
}
else
{
lean_object* v___x_3906_; 
v___x_3906_ = l_Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f___redArg(v_a_3775_, v_a_3776_, v_a_3782_, v_a_3783_, v_a_3784_, v_a_3785_);
if (lean_obj_tag(v___x_3906_) == 0)
{
lean_object* v_a_3907_; 
v_a_3907_ = lean_ctor_get(v___x_3906_, 0);
lean_inc(v_a_3907_);
lean_dec_ref(v___x_3906_);
v_____x_3831_ = v_a_3907_;
v___y_3832_ = v_a_3775_;
v___y_3833_ = v_a_3776_;
v___y_3834_ = v_a_3777_;
v___y_3835_ = v_a_3778_;
v___y_3836_ = v_a_3779_;
v___y_3837_ = v_a_3780_;
v___y_3838_ = v_a_3781_;
v___y_3839_ = v_a_3782_;
v___y_3840_ = v_a_3783_;
v___y_3841_ = v_a_3784_;
v___y_3842_ = v_a_3785_;
goto v___jp_3830_;
}
else
{
lean_object* v_a_3908_; lean_object* v___x_3910_; uint8_t v_isShared_3911_; uint8_t v_isSharedCheck_3915_; 
lean_dec_ref(v_e_3773_);
v_a_3908_ = lean_ctor_get(v___x_3906_, 0);
v_isSharedCheck_3915_ = !lean_is_exclusive(v___x_3906_);
if (v_isSharedCheck_3915_ == 0)
{
v___x_3910_ = v___x_3906_;
v_isShared_3911_ = v_isSharedCheck_3915_;
goto v_resetjp_3909_;
}
else
{
lean_inc(v_a_3908_);
lean_dec(v___x_3906_);
v___x_3910_ = lean_box(0);
v_isShared_3911_ = v_isSharedCheck_3915_;
goto v_resetjp_3909_;
}
v_resetjp_3909_:
{
lean_object* v___x_3913_; 
if (v_isShared_3911_ == 0)
{
v___x_3913_ = v___x_3910_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v_a_3908_);
v___x_3913_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
return v___x_3913_;
}
}
}
}
v___jp_3787_:
{
lean_object* v___x_3788_; lean_object* v___x_3789_; 
v___x_3788_ = lean_box(0);
v___x_3789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3789_, 0, v___x_3788_);
return v___x_3789_;
}
v___jp_3790_:
{
lean_object* v___x_3805_; 
lean_inc(v___y_3796_);
v___x_3805_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_3803_, v___y_3796_, v___y_3795_, v___y_3792_, v___y_3797_, v___y_3793_, v___y_3799_, v___y_3791_, v___y_3798_, v___y_3794_, v___y_3800_, v___y_3802_);
if (lean_obj_tag(v___x_3805_) == 0)
{
lean_object* v_a_3806_; lean_object* v___x_3807_; 
v_a_3806_ = lean_ctor_get(v___x_3805_, 0);
lean_inc(v_a_3806_);
lean_dec_ref(v___x_3805_);
v___x_3807_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_snd_3804_, v___y_3796_, v___y_3795_, v___y_3792_, v___y_3797_, v___y_3793_, v___y_3799_, v___y_3791_, v___y_3798_, v___y_3794_, v___y_3800_, v___y_3802_);
if (lean_obj_tag(v___x_3807_) == 0)
{
lean_object* v_a_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; 
v_a_3808_ = lean_ctor_get(v___x_3807_, 0);
lean_inc_n(v_a_3808_, 2);
lean_dec_ref(v___x_3807_);
lean_inc(v_a_3806_);
v___x_3809_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3809_, 0, v_a_3806_);
lean_ctor_set(v___x_3809_, 1, v_a_3808_);
v___x_3810_ = l_Int_Linear_Expr_norm(v___x_3809_);
lean_dec_ref(v___x_3809_);
v___x_3811_ = lean_alloc_ctor(2, 4, 1);
lean_ctor_set(v___x_3811_, 0, v_e_3773_);
lean_ctor_set(v___x_3811_, 1, v___y_3801_);
lean_ctor_set(v___x_3811_, 2, v_a_3806_);
lean_ctor_set(v___x_3811_, 3, v_a_3808_);
lean_ctor_set_uint8(v___x_3811_, sizeof(void*)*4, v_eqTrue_3774_);
v___x_3812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3812_, 0, v___x_3810_);
lean_ctor_set(v___x_3812_, 1, v___x_3811_);
v___x_3813_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v___x_3812_, v___y_3795_, v___y_3792_, v___y_3797_, v___y_3793_, v___y_3799_, v___y_3791_, v___y_3798_, v___y_3794_, v___y_3800_, v___y_3802_);
return v___x_3813_;
}
else
{
lean_object* v_a_3814_; lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3821_; 
lean_dec(v_a_3806_);
lean_dec_ref(v___y_3801_);
lean_dec_ref(v_e_3773_);
v_a_3814_ = lean_ctor_get(v___x_3807_, 0);
v_isSharedCheck_3821_ = !lean_is_exclusive(v___x_3807_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3816_ = v___x_3807_;
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
else
{
lean_inc(v_a_3814_);
lean_dec(v___x_3807_);
v___x_3816_ = lean_box(0);
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
v_resetjp_3815_:
{
lean_object* v___x_3819_; 
if (v_isShared_3817_ == 0)
{
v___x_3819_ = v___x_3816_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v_a_3814_);
v___x_3819_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
return v___x_3819_;
}
}
}
}
else
{
lean_object* v_a_3822_; lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3829_; 
lean_dec_ref(v_snd_3804_);
lean_dec_ref(v___y_3801_);
lean_dec(v___y_3796_);
lean_dec_ref(v_e_3773_);
v_a_3822_ = lean_ctor_get(v___x_3805_, 0);
v_isSharedCheck_3829_ = !lean_is_exclusive(v___x_3805_);
if (v_isSharedCheck_3829_ == 0)
{
v___x_3824_ = v___x_3805_;
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
else
{
lean_inc(v_a_3822_);
lean_dec(v___x_3805_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
lean_object* v___x_3827_; 
if (v_isShared_3825_ == 0)
{
v___x_3827_ = v___x_3824_;
goto v_reusejp_3826_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v_a_3822_);
v___x_3827_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3826_;
}
v_reusejp_3826_:
{
return v___x_3827_;
}
}
}
}
v___jp_3830_:
{
if (lean_obj_tag(v_____x_3831_) == 1)
{
lean_object* v_val_3843_; lean_object* v___x_3844_; uint8_t v___x_3845_; 
v_val_3843_ = lean_ctor_get(v_____x_3831_, 0);
lean_inc(v_val_3843_);
lean_dec_ref(v_____x_3831_);
lean_inc_ref(v_e_3773_);
v___x_3844_ = l_Lean_Expr_cleanupAnnotations(v_e_3773_);
v___x_3845_ = l_Lean_Expr_isApp(v___x_3844_);
if (v___x_3845_ == 0)
{
lean_dec_ref(v___x_3844_);
lean_dec(v_val_3843_);
lean_dec_ref(v_e_3773_);
goto v___jp_3787_;
}
else
{
lean_object* v_arg_3846_; lean_object* v___x_3847_; uint8_t v___x_3848_; 
v_arg_3846_ = lean_ctor_get(v___x_3844_, 1);
lean_inc_ref(v_arg_3846_);
v___x_3847_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3844_);
v___x_3848_ = l_Lean_Expr_isApp(v___x_3847_);
if (v___x_3848_ == 0)
{
lean_dec_ref(v___x_3847_);
lean_dec_ref(v_arg_3846_);
lean_dec(v_val_3843_);
lean_dec_ref(v_e_3773_);
goto v___jp_3787_;
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
lean_dec_ref(v_arg_3846_);
lean_dec(v_val_3843_);
lean_dec_ref(v_e_3773_);
goto v___jp_3787_;
}
else
{
lean_object* v___x_3852_; uint8_t v___x_3853_; 
v___x_3852_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3850_);
v___x_3853_ = l_Lean_Expr_isApp(v___x_3852_);
if (v___x_3853_ == 0)
{
lean_dec_ref(v___x_3852_);
lean_dec_ref(v_arg_3849_);
lean_dec_ref(v_arg_3846_);
lean_dec(v_val_3843_);
lean_dec_ref(v_e_3773_);
goto v___jp_3787_;
}
else
{
lean_object* v___x_3854_; lean_object* v___x_3855_; uint8_t v___x_3856_; 
v___x_3854_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3852_);
v___x_3855_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2));
v___x_3856_ = l_Lean_Expr_isConstOf(v___x_3854_, v___x_3855_);
lean_dec_ref(v___x_3854_);
if (v___x_3856_ == 0)
{
lean_dec_ref(v_arg_3849_);
lean_dec_ref(v_arg_3846_);
lean_dec(v_val_3843_);
lean_dec_ref(v_e_3773_);
goto v___jp_3787_;
}
else
{
lean_object* v___x_3857_; 
v___x_3857_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_3773_, v___y_3833_);
if (lean_obj_tag(v___x_3857_) == 0)
{
lean_object* v_a_3858_; lean_object* v___x_3859_; 
v_a_3858_ = lean_ctor_get(v___x_3857_, 0);
lean_inc(v_a_3858_);
lean_dec_ref(v___x_3857_);
lean_inc_ref(v_arg_3849_);
v___x_3859_ = l_Lean_Meta_Grind_Arith_Cutsat_toInt(v_arg_3849_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_);
if (lean_obj_tag(v___x_3859_) == 0)
{
lean_object* v_a_3860_; lean_object* v_fst_3861_; lean_object* v_snd_3862_; lean_object* v___x_3863_; 
v_a_3860_ = lean_ctor_get(v___x_3859_, 0);
lean_inc(v_a_3860_);
lean_dec_ref(v___x_3859_);
v_fst_3861_ = lean_ctor_get(v_a_3860_, 0);
lean_inc(v_fst_3861_);
v_snd_3862_ = lean_ctor_get(v_a_3860_, 1);
lean_inc(v_snd_3862_);
lean_dec(v_a_3860_);
lean_inc_ref(v_arg_3846_);
v___x_3863_ = l_Lean_Meta_Grind_Arith_Cutsat_toInt(v_arg_3846_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_);
if (lean_obj_tag(v___x_3863_) == 0)
{
lean_object* v_a_3864_; lean_object* v_fst_3865_; lean_object* v_snd_3866_; lean_object* v___x_3867_; 
v_a_3864_ = lean_ctor_get(v___x_3863_, 0);
lean_inc(v_a_3864_);
lean_dec_ref(v___x_3863_);
v_fst_3865_ = lean_ctor_get(v_a_3864_, 0);
lean_inc_n(v_fst_3865_, 2);
v_snd_3866_ = lean_ctor_get(v_a_3864_, 1);
lean_inc(v_snd_3866_);
lean_dec(v_a_3864_);
lean_inc(v_fst_3861_);
v___x_3867_ = l_Lean_mkApp6(v_val_3843_, v_arg_3849_, v_arg_3846_, v_fst_3861_, v_fst_3865_, v_snd_3862_, v_snd_3866_);
if (v_eqTrue_3774_ == 0)
{
lean_object* v___x_3868_; lean_object* v___x_3869_; 
v___x_3868_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0);
v___x_3869_ = l_Lean_mkIntAdd(v_fst_3865_, v___x_3868_);
v___y_3791_ = v___y_3838_;
v___y_3792_ = v___y_3834_;
v___y_3793_ = v___y_3836_;
v___y_3794_ = v___y_3840_;
v___y_3795_ = v___y_3833_;
v___y_3796_ = v_a_3858_;
v___y_3797_ = v___y_3835_;
v___y_3798_ = v___y_3839_;
v___y_3799_ = v___y_3837_;
v___y_3800_ = v___y_3841_;
v___y_3801_ = v___x_3867_;
v___y_3802_ = v___y_3842_;
v_fst_3803_ = v___x_3869_;
v_snd_3804_ = v_fst_3861_;
goto v___jp_3790_;
}
else
{
v___y_3791_ = v___y_3838_;
v___y_3792_ = v___y_3834_;
v___y_3793_ = v___y_3836_;
v___y_3794_ = v___y_3840_;
v___y_3795_ = v___y_3833_;
v___y_3796_ = v_a_3858_;
v___y_3797_ = v___y_3835_;
v___y_3798_ = v___y_3839_;
v___y_3799_ = v___y_3837_;
v___y_3800_ = v___y_3841_;
v___y_3801_ = v___x_3867_;
v___y_3802_ = v___y_3842_;
v_fst_3803_ = v_fst_3861_;
v_snd_3804_ = v_fst_3865_;
goto v___jp_3790_;
}
}
else
{
lean_object* v_a_3870_; lean_object* v___x_3872_; uint8_t v_isShared_3873_; uint8_t v_isSharedCheck_3877_; 
lean_dec(v_snd_3862_);
lean_dec(v_fst_3861_);
lean_dec(v_a_3858_);
lean_dec_ref(v_arg_3849_);
lean_dec_ref(v_arg_3846_);
lean_dec(v_val_3843_);
lean_dec_ref(v_e_3773_);
v_a_3870_ = lean_ctor_get(v___x_3863_, 0);
v_isSharedCheck_3877_ = !lean_is_exclusive(v___x_3863_);
if (v_isSharedCheck_3877_ == 0)
{
v___x_3872_ = v___x_3863_;
v_isShared_3873_ = v_isSharedCheck_3877_;
goto v_resetjp_3871_;
}
else
{
lean_inc(v_a_3870_);
lean_dec(v___x_3863_);
v___x_3872_ = lean_box(0);
v_isShared_3873_ = v_isSharedCheck_3877_;
goto v_resetjp_3871_;
}
v_resetjp_3871_:
{
lean_object* v___x_3875_; 
if (v_isShared_3873_ == 0)
{
v___x_3875_ = v___x_3872_;
goto v_reusejp_3874_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v_a_3870_);
v___x_3875_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3874_;
}
v_reusejp_3874_:
{
return v___x_3875_;
}
}
}
}
else
{
lean_object* v_a_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3885_; 
lean_dec(v_a_3858_);
lean_dec_ref(v_arg_3849_);
lean_dec_ref(v_arg_3846_);
lean_dec(v_val_3843_);
lean_dec_ref(v_e_3773_);
v_a_3878_ = lean_ctor_get(v___x_3859_, 0);
v_isSharedCheck_3885_ = !lean_is_exclusive(v___x_3859_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3880_ = v___x_3859_;
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_a_3878_);
lean_dec(v___x_3859_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3883_; 
if (v_isShared_3881_ == 0)
{
v___x_3883_ = v___x_3880_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v_a_3878_);
v___x_3883_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3882_;
}
v_reusejp_3882_:
{
return v___x_3883_;
}
}
}
}
else
{
lean_object* v_a_3886_; lean_object* v___x_3888_; uint8_t v_isShared_3889_; uint8_t v_isSharedCheck_3893_; 
lean_dec_ref(v_arg_3849_);
lean_dec_ref(v_arg_3846_);
lean_dec(v_val_3843_);
lean_dec_ref(v_e_3773_);
v_a_3886_ = lean_ctor_get(v___x_3857_, 0);
v_isSharedCheck_3893_ = !lean_is_exclusive(v___x_3857_);
if (v_isSharedCheck_3893_ == 0)
{
v___x_3888_ = v___x_3857_;
v_isShared_3889_ = v_isSharedCheck_3893_;
goto v_resetjp_3887_;
}
else
{
lean_inc(v_a_3886_);
lean_dec(v___x_3857_);
v___x_3888_ = lean_box(0);
v_isShared_3889_ = v_isSharedCheck_3893_;
goto v_resetjp_3887_;
}
v_resetjp_3887_:
{
lean_object* v___x_3891_; 
if (v_isShared_3889_ == 0)
{
v___x_3891_ = v___x_3888_;
goto v_reusejp_3890_;
}
else
{
lean_object* v_reuseFailAlloc_3892_; 
v_reuseFailAlloc_3892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3892_, 0, v_a_3886_);
v___x_3891_ = v_reuseFailAlloc_3892_;
goto v_reusejp_3890_;
}
v_reusejp_3890_:
{
return v___x_3891_;
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
lean_object* v___x_3894_; lean_object* v___x_3895_; 
lean_dec(v_____x_3831_);
lean_dec_ref(v_e_3773_);
v___x_3894_ = lean_box(0);
v___x_3895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3895_, 0, v___x_3894_);
return v___x_3895_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe___boxed(lean_object* v_e_3916_, lean_object* v_eqTrue_3917_, lean_object* v_a_3918_, lean_object* v_a_3919_, lean_object* v_a_3920_, lean_object* v_a_3921_, lean_object* v_a_3922_, lean_object* v_a_3923_, lean_object* v_a_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_, lean_object* v_a_3929_){
_start:
{
uint8_t v_eqTrue_boxed_3930_; lean_object* v_res_3931_; 
v_eqTrue_boxed_3930_ = lean_unbox(v_eqTrue_3917_);
v_res_3931_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe(v_e_3916_, v_eqTrue_boxed_3930_, v_a_3918_, v_a_3919_, v_a_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_, v_a_3925_, v_a_3926_, v_a_3927_, v_a_3928_);
lean_dec(v_a_3928_);
lean_dec_ref(v_a_3927_);
lean_dec(v_a_3926_);
lean_dec_ref(v_a_3925_);
lean_dec(v_a_3924_);
lean_dec_ref(v_a_3923_);
lean_dec(v_a_3922_);
lean_dec_ref(v_a_3921_);
lean_dec(v_a_3920_);
lean_dec(v_a_3919_);
lean_dec(v_a_3918_);
return v_res_3931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe(lean_object* v_e_3937_, uint8_t v_eqTrue_3938_, lean_object* v_a_3939_, lean_object* v_a_3940_, lean_object* v_a_3941_, lean_object* v_a_3942_, lean_object* v_a_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_){
_start:
{
lean_object* v___x_3953_; 
v___x_3953_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3941_);
if (lean_obj_tag(v___x_3953_) == 0)
{
lean_object* v_a_3954_; lean_object* v___x_3956_; uint8_t v_isShared_3957_; uint8_t v_isSharedCheck_3984_; 
v_a_3954_ = lean_ctor_get(v___x_3953_, 0);
v_isSharedCheck_3984_ = !lean_is_exclusive(v___x_3953_);
if (v_isSharedCheck_3984_ == 0)
{
v___x_3956_ = v___x_3953_;
v_isShared_3957_ = v_isSharedCheck_3984_;
goto v_resetjp_3955_;
}
else
{
lean_inc(v_a_3954_);
lean_dec(v___x_3953_);
v___x_3956_ = lean_box(0);
v_isShared_3957_ = v_isSharedCheck_3984_;
goto v_resetjp_3955_;
}
v_resetjp_3955_:
{
uint8_t v_lia_3958_; 
v_lia_3958_ = lean_ctor_get_uint8(v_a_3954_, sizeof(void*)*11 + 23);
lean_dec(v_a_3954_);
if (v_lia_3958_ == 0)
{
lean_object* v___x_3959_; lean_object* v___x_3961_; 
lean_dec_ref(v_e_3937_);
v___x_3959_ = lean_box(0);
if (v_isShared_3957_ == 0)
{
lean_ctor_set(v___x_3956_, 0, v___x_3959_);
v___x_3961_ = v___x_3956_;
goto v_reusejp_3960_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v___x_3959_);
v___x_3961_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3960_;
}
v_reusejp_3960_:
{
return v___x_3961_;
}
}
else
{
lean_object* v___x_3963_; uint8_t v___x_3964_; 
lean_del_object(v___x_3956_);
lean_inc_ref(v_e_3937_);
v___x_3963_ = l_Lean_Expr_cleanupAnnotations(v_e_3937_);
v___x_3964_ = l_Lean_Expr_isApp(v___x_3963_);
if (v___x_3964_ == 0)
{
lean_dec_ref(v___x_3963_);
lean_dec_ref(v_e_3937_);
goto v___jp_3950_;
}
else
{
lean_object* v___x_3965_; uint8_t v___x_3966_; 
v___x_3965_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3963_);
v___x_3966_ = l_Lean_Expr_isApp(v___x_3965_);
if (v___x_3966_ == 0)
{
lean_dec_ref(v___x_3965_);
lean_dec_ref(v_e_3937_);
goto v___jp_3950_;
}
else
{
lean_object* v___x_3967_; uint8_t v___x_3968_; 
v___x_3967_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3965_);
v___x_3968_ = l_Lean_Expr_isApp(v___x_3967_);
if (v___x_3968_ == 0)
{
lean_dec_ref(v___x_3967_);
lean_dec_ref(v_e_3937_);
goto v___jp_3950_;
}
else
{
lean_object* v___x_3969_; uint8_t v___x_3970_; 
v___x_3969_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3967_);
v___x_3970_ = l_Lean_Expr_isApp(v___x_3969_);
if (v___x_3970_ == 0)
{
lean_dec_ref(v___x_3969_);
lean_dec_ref(v_e_3937_);
goto v___jp_3950_;
}
else
{
lean_object* v_arg_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; uint8_t v___x_3974_; 
v_arg_3971_ = lean_ctor_get(v___x_3969_, 1);
lean_inc_ref(v_arg_3971_);
v___x_3972_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3969_);
v___x_3973_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2));
v___x_3974_ = l_Lean_Expr_isConstOf(v___x_3972_, v___x_3973_);
lean_dec_ref(v___x_3972_);
if (v___x_3974_ == 0)
{
lean_dec_ref(v_arg_3971_);
lean_dec_ref(v_e_3937_);
goto v___jp_3950_;
}
else
{
lean_object* v___x_3975_; uint8_t v___x_3976_; 
v___x_3975_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__0));
v___x_3976_ = l_Lean_Expr_isConstOf(v_arg_3971_, v___x_3975_);
if (v___x_3976_ == 0)
{
lean_object* v___x_3977_; uint8_t v___x_3978_; 
v___x_3977_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__2));
v___x_3978_ = l_Lean_Expr_isConstOf(v_arg_3971_, v___x_3977_);
if (v___x_3978_ == 0)
{
lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; 
v___x_3979_ = lean_box(v_eqTrue_3938_);
v___x_3980_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe___boxed), 14, 2);
lean_closure_set(v___x_3980_, 0, v_e_3937_);
lean_closure_set(v___x_3980_, 1, v___x_3979_);
v___x_3981_ = l_Lean_Meta_Grind_Arith_Cutsat_ToIntM_run(v_arg_3971_, v___x_3980_, v_a_3939_, v_a_3940_, v_a_3941_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_);
return v___x_3981_;
}
else
{
lean_object* v___x_3982_; 
lean_dec_ref(v_arg_3971_);
v___x_3982_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe(v_e_3937_, v_eqTrue_3938_, v_a_3939_, v_a_3940_, v_a_3941_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_);
return v___x_3982_;
}
}
else
{
lean_object* v___x_3983_; 
lean_dec_ref(v_arg_3971_);
v___x_3983_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe(v_e_3937_, v_eqTrue_3938_, v_a_3939_, v_a_3940_, v_a_3941_, v_a_3942_, v_a_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_);
return v___x_3983_;
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
lean_object* v_a_3985_; lean_object* v___x_3987_; uint8_t v_isShared_3988_; uint8_t v_isSharedCheck_3992_; 
lean_dec_ref(v_e_3937_);
v_a_3985_ = lean_ctor_get(v___x_3953_, 0);
v_isSharedCheck_3992_ = !lean_is_exclusive(v___x_3953_);
if (v_isSharedCheck_3992_ == 0)
{
v___x_3987_ = v___x_3953_;
v_isShared_3988_ = v_isSharedCheck_3992_;
goto v_resetjp_3986_;
}
else
{
lean_inc(v_a_3985_);
lean_dec(v___x_3953_);
v___x_3987_ = lean_box(0);
v_isShared_3988_ = v_isSharedCheck_3992_;
goto v_resetjp_3986_;
}
v_resetjp_3986_:
{
lean_object* v___x_3990_; 
if (v_isShared_3988_ == 0)
{
v___x_3990_ = v___x_3987_;
goto v_reusejp_3989_;
}
else
{
lean_object* v_reuseFailAlloc_3991_; 
v_reuseFailAlloc_3991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3991_, 0, v_a_3985_);
v___x_3990_ = v_reuseFailAlloc_3991_;
goto v_reusejp_3989_;
}
v_reusejp_3989_:
{
return v___x_3990_;
}
}
}
v___jp_3950_:
{
lean_object* v___x_3951_; lean_object* v___x_3952_; 
v___x_3951_ = lean_box(0);
v___x_3952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3952_, 0, v___x_3951_);
return v___x_3952_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___boxed(lean_object* v_e_3993_, lean_object* v_eqTrue_3994_, lean_object* v_a_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_){
_start:
{
uint8_t v_eqTrue_boxed_4006_; lean_object* v_res_4007_; 
v_eqTrue_boxed_4006_ = lean_unbox(v_eqTrue_3994_);
v_res_4007_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLe(v_e_3993_, v_eqTrue_boxed_4006_, v_a_3995_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_, v_a_4004_);
lean_dec(v_a_4004_);
lean_dec_ref(v_a_4003_);
lean_dec(v_a_4002_);
lean_dec_ref(v_a_4001_);
lean_dec(v_a_4000_);
lean_dec_ref(v_a_3999_);
lean_dec(v_a_3998_);
lean_dec_ref(v_a_3997_);
lean_dec(v_a_3996_);
lean_dec(v_a_3995_);
return v_res_4007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__0(lean_object* v_e_4008_, lean_object* v_arg_4009_, lean_object* v_arg_4010_, uint8_t v_eqTrue_4011_, lean_object* v_____x_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_){
_start:
{
if (lean_obj_tag(v_____x_4012_) == 1)
{
lean_object* v_val_4025_; lean_object* v___x_4026_; 
v_val_4025_ = lean_ctor_get(v_____x_4012_, 0);
lean_inc(v_val_4025_);
lean_dec_ref(v_____x_4012_);
v___x_4026_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_4008_, v___y_4014_);
if (lean_obj_tag(v___x_4026_) == 0)
{
lean_object* v_a_4027_; lean_object* v___x_4028_; 
v_a_4027_ = lean_ctor_get(v___x_4026_, 0);
lean_inc(v_a_4027_);
lean_dec_ref(v___x_4026_);
lean_inc_ref(v_arg_4009_);
v___x_4028_ = l_Lean_Meta_Grind_Arith_Cutsat_toInt(v_arg_4009_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_);
if (lean_obj_tag(v___x_4028_) == 0)
{
lean_object* v_a_4029_; lean_object* v_fst_4030_; lean_object* v_snd_4031_; lean_object* v___x_4033_; uint8_t v_isShared_4034_; uint8_t v_isSharedCheck_4086_; 
v_a_4029_ = lean_ctor_get(v___x_4028_, 0);
lean_inc(v_a_4029_);
lean_dec_ref(v___x_4028_);
v_fst_4030_ = lean_ctor_get(v_a_4029_, 0);
v_snd_4031_ = lean_ctor_get(v_a_4029_, 1);
v_isSharedCheck_4086_ = !lean_is_exclusive(v_a_4029_);
if (v_isSharedCheck_4086_ == 0)
{
v___x_4033_ = v_a_4029_;
v_isShared_4034_ = v_isSharedCheck_4086_;
goto v_resetjp_4032_;
}
else
{
lean_inc(v_snd_4031_);
lean_inc(v_fst_4030_);
lean_dec(v_a_4029_);
v___x_4033_ = lean_box(0);
v_isShared_4034_ = v_isSharedCheck_4086_;
goto v_resetjp_4032_;
}
v_resetjp_4032_:
{
lean_object* v___x_4035_; 
lean_inc_ref(v_arg_4010_);
v___x_4035_ = l_Lean_Meta_Grind_Arith_Cutsat_toInt(v_arg_4010_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_);
if (lean_obj_tag(v___x_4035_) == 0)
{
lean_object* v_a_4036_; lean_object* v_fst_4037_; lean_object* v_snd_4038_; lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4077_; 
v_a_4036_ = lean_ctor_get(v___x_4035_, 0);
lean_inc(v_a_4036_);
lean_dec_ref(v___x_4035_);
v_fst_4037_ = lean_ctor_get(v_a_4036_, 0);
v_snd_4038_ = lean_ctor_get(v_a_4036_, 1);
v_isSharedCheck_4077_ = !lean_is_exclusive(v_a_4036_);
if (v_isSharedCheck_4077_ == 0)
{
v___x_4040_ = v_a_4036_;
v_isShared_4041_ = v_isSharedCheck_4077_;
goto v_resetjp_4039_;
}
else
{
lean_inc(v_snd_4038_);
lean_inc(v_fst_4037_);
lean_dec(v_a_4036_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4077_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
lean_object* v___x_4042_; lean_object* v_fst_4044_; lean_object* v_snd_4045_; 
lean_inc(v_fst_4037_);
lean_inc(v_fst_4030_);
v___x_4042_ = l_Lean_mkApp6(v_val_4025_, v_arg_4009_, v_arg_4010_, v_fst_4030_, v_fst_4037_, v_snd_4031_, v_snd_4038_);
if (v_eqTrue_4011_ == 0)
{
v_fst_4044_ = v_fst_4037_;
v_snd_4045_ = v_fst_4030_;
goto v___jp_4043_;
}
else
{
lean_object* v___x_4075_; lean_object* v___x_4076_; 
v___x_4075_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0);
v___x_4076_ = l_Lean_mkIntAdd(v_fst_4030_, v___x_4075_);
v_fst_4044_ = v___x_4076_;
v_snd_4045_ = v_fst_4037_;
goto v___jp_4043_;
}
v___jp_4043_:
{
lean_object* v___x_4046_; 
lean_inc(v_a_4027_);
v___x_4046_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_4044_, v_a_4027_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_);
if (lean_obj_tag(v___x_4046_) == 0)
{
lean_object* v_a_4047_; lean_object* v___x_4048_; 
v_a_4047_ = lean_ctor_get(v___x_4046_, 0);
lean_inc(v_a_4047_);
lean_dec_ref(v___x_4046_);
v___x_4048_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_snd_4045_, v_a_4027_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_);
if (lean_obj_tag(v___x_4048_) == 0)
{
lean_object* v_a_4049_; lean_object* v___x_4051_; 
v_a_4049_ = lean_ctor_get(v___x_4048_, 0);
lean_inc_n(v_a_4049_, 2);
lean_dec_ref(v___x_4048_);
lean_inc(v_a_4047_);
if (v_isShared_4041_ == 0)
{
lean_ctor_set_tag(v___x_4040_, 3);
lean_ctor_set(v___x_4040_, 1, v_a_4049_);
lean_ctor_set(v___x_4040_, 0, v_a_4047_);
v___x_4051_ = v___x_4040_;
goto v_reusejp_4050_;
}
else
{
lean_object* v_reuseFailAlloc_4058_; 
v_reuseFailAlloc_4058_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4058_, 0, v_a_4047_);
lean_ctor_set(v_reuseFailAlloc_4058_, 1, v_a_4049_);
v___x_4051_ = v_reuseFailAlloc_4058_;
goto v_reusejp_4050_;
}
v_reusejp_4050_:
{
lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4055_; 
v___x_4052_ = l_Int_Linear_Expr_norm(v___x_4051_);
lean_dec_ref(v___x_4051_);
v___x_4053_ = lean_alloc_ctor(2, 4, 1);
lean_ctor_set(v___x_4053_, 0, v_e_4008_);
lean_ctor_set(v___x_4053_, 1, v___x_4042_);
lean_ctor_set(v___x_4053_, 2, v_a_4047_);
lean_ctor_set(v___x_4053_, 3, v_a_4049_);
lean_ctor_set_uint8(v___x_4053_, sizeof(void*)*4, v_eqTrue_4011_);
if (v_isShared_4034_ == 0)
{
lean_ctor_set(v___x_4033_, 1, v___x_4053_);
lean_ctor_set(v___x_4033_, 0, v___x_4052_);
v___x_4055_ = v___x_4033_;
goto v_reusejp_4054_;
}
else
{
lean_object* v_reuseFailAlloc_4057_; 
v_reuseFailAlloc_4057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4057_, 0, v___x_4052_);
lean_ctor_set(v_reuseFailAlloc_4057_, 1, v___x_4053_);
v___x_4055_ = v_reuseFailAlloc_4057_;
goto v_reusejp_4054_;
}
v_reusejp_4054_:
{
lean_object* v___x_4056_; 
lean_inc(v___y_4023_);
lean_inc_ref(v___y_4022_);
lean_inc(v___y_4021_);
lean_inc_ref(v___y_4020_);
lean_inc(v___y_4019_);
lean_inc_ref(v___y_4018_);
lean_inc(v___y_4017_);
lean_inc_ref(v___y_4016_);
lean_inc(v___y_4015_);
lean_inc(v___y_4014_);
v___x_4056_ = lean_grind_cutsat_assert_le(v___x_4055_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_);
return v___x_4056_;
}
}
}
else
{
lean_object* v_a_4059_; lean_object* v___x_4061_; uint8_t v_isShared_4062_; uint8_t v_isSharedCheck_4066_; 
lean_dec(v_a_4047_);
lean_dec_ref(v___x_4042_);
lean_del_object(v___x_4040_);
lean_del_object(v___x_4033_);
lean_dec_ref(v_e_4008_);
v_a_4059_ = lean_ctor_get(v___x_4048_, 0);
v_isSharedCheck_4066_ = !lean_is_exclusive(v___x_4048_);
if (v_isSharedCheck_4066_ == 0)
{
v___x_4061_ = v___x_4048_;
v_isShared_4062_ = v_isSharedCheck_4066_;
goto v_resetjp_4060_;
}
else
{
lean_inc(v_a_4059_);
lean_dec(v___x_4048_);
v___x_4061_ = lean_box(0);
v_isShared_4062_ = v_isSharedCheck_4066_;
goto v_resetjp_4060_;
}
v_resetjp_4060_:
{
lean_object* v___x_4064_; 
if (v_isShared_4062_ == 0)
{
v___x_4064_ = v___x_4061_;
goto v_reusejp_4063_;
}
else
{
lean_object* v_reuseFailAlloc_4065_; 
v_reuseFailAlloc_4065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4065_, 0, v_a_4059_);
v___x_4064_ = v_reuseFailAlloc_4065_;
goto v_reusejp_4063_;
}
v_reusejp_4063_:
{
return v___x_4064_;
}
}
}
}
else
{
lean_object* v_a_4067_; lean_object* v___x_4069_; uint8_t v_isShared_4070_; uint8_t v_isSharedCheck_4074_; 
lean_dec_ref(v_snd_4045_);
lean_dec_ref(v___x_4042_);
lean_del_object(v___x_4040_);
lean_del_object(v___x_4033_);
lean_dec(v_a_4027_);
lean_dec_ref(v_e_4008_);
v_a_4067_ = lean_ctor_get(v___x_4046_, 0);
v_isSharedCheck_4074_ = !lean_is_exclusive(v___x_4046_);
if (v_isSharedCheck_4074_ == 0)
{
v___x_4069_ = v___x_4046_;
v_isShared_4070_ = v_isSharedCheck_4074_;
goto v_resetjp_4068_;
}
else
{
lean_inc(v_a_4067_);
lean_dec(v___x_4046_);
v___x_4069_ = lean_box(0);
v_isShared_4070_ = v_isSharedCheck_4074_;
goto v_resetjp_4068_;
}
v_resetjp_4068_:
{
lean_object* v___x_4072_; 
if (v_isShared_4070_ == 0)
{
v___x_4072_ = v___x_4069_;
goto v_reusejp_4071_;
}
else
{
lean_object* v_reuseFailAlloc_4073_; 
v_reuseFailAlloc_4073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4073_, 0, v_a_4067_);
v___x_4072_ = v_reuseFailAlloc_4073_;
goto v_reusejp_4071_;
}
v_reusejp_4071_:
{
return v___x_4072_;
}
}
}
}
}
}
else
{
lean_object* v_a_4078_; lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4085_; 
lean_del_object(v___x_4033_);
lean_dec(v_snd_4031_);
lean_dec(v_fst_4030_);
lean_dec(v_a_4027_);
lean_dec(v_val_4025_);
lean_dec_ref(v_arg_4010_);
lean_dec_ref(v_arg_4009_);
lean_dec_ref(v_e_4008_);
v_a_4078_ = lean_ctor_get(v___x_4035_, 0);
v_isSharedCheck_4085_ = !lean_is_exclusive(v___x_4035_);
if (v_isSharedCheck_4085_ == 0)
{
v___x_4080_ = v___x_4035_;
v_isShared_4081_ = v_isSharedCheck_4085_;
goto v_resetjp_4079_;
}
else
{
lean_inc(v_a_4078_);
lean_dec(v___x_4035_);
v___x_4080_ = lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4085_;
goto v_resetjp_4079_;
}
v_resetjp_4079_:
{
lean_object* v___x_4083_; 
if (v_isShared_4081_ == 0)
{
v___x_4083_ = v___x_4080_;
goto v_reusejp_4082_;
}
else
{
lean_object* v_reuseFailAlloc_4084_; 
v_reuseFailAlloc_4084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4084_, 0, v_a_4078_);
v___x_4083_ = v_reuseFailAlloc_4084_;
goto v_reusejp_4082_;
}
v_reusejp_4082_:
{
return v___x_4083_;
}
}
}
}
}
else
{
lean_object* v_a_4087_; lean_object* v___x_4089_; uint8_t v_isShared_4090_; uint8_t v_isSharedCheck_4094_; 
lean_dec(v_a_4027_);
lean_dec(v_val_4025_);
lean_dec_ref(v_arg_4010_);
lean_dec_ref(v_arg_4009_);
lean_dec_ref(v_e_4008_);
v_a_4087_ = lean_ctor_get(v___x_4028_, 0);
v_isSharedCheck_4094_ = !lean_is_exclusive(v___x_4028_);
if (v_isSharedCheck_4094_ == 0)
{
v___x_4089_ = v___x_4028_;
v_isShared_4090_ = v_isSharedCheck_4094_;
goto v_resetjp_4088_;
}
else
{
lean_inc(v_a_4087_);
lean_dec(v___x_4028_);
v___x_4089_ = lean_box(0);
v_isShared_4090_ = v_isSharedCheck_4094_;
goto v_resetjp_4088_;
}
v_resetjp_4088_:
{
lean_object* v___x_4092_; 
if (v_isShared_4090_ == 0)
{
v___x_4092_ = v___x_4089_;
goto v_reusejp_4091_;
}
else
{
lean_object* v_reuseFailAlloc_4093_; 
v_reuseFailAlloc_4093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4093_, 0, v_a_4087_);
v___x_4092_ = v_reuseFailAlloc_4093_;
goto v_reusejp_4091_;
}
v_reusejp_4091_:
{
return v___x_4092_;
}
}
}
}
else
{
lean_object* v_a_4095_; lean_object* v___x_4097_; uint8_t v_isShared_4098_; uint8_t v_isSharedCheck_4102_; 
lean_dec(v_val_4025_);
lean_dec_ref(v_arg_4010_);
lean_dec_ref(v_arg_4009_);
lean_dec_ref(v_e_4008_);
v_a_4095_ = lean_ctor_get(v___x_4026_, 0);
v_isSharedCheck_4102_ = !lean_is_exclusive(v___x_4026_);
if (v_isSharedCheck_4102_ == 0)
{
v___x_4097_ = v___x_4026_;
v_isShared_4098_ = v_isSharedCheck_4102_;
goto v_resetjp_4096_;
}
else
{
lean_inc(v_a_4095_);
lean_dec(v___x_4026_);
v___x_4097_ = lean_box(0);
v_isShared_4098_ = v_isSharedCheck_4102_;
goto v_resetjp_4096_;
}
v_resetjp_4096_:
{
lean_object* v___x_4100_; 
if (v_isShared_4098_ == 0)
{
v___x_4100_ = v___x_4097_;
goto v_reusejp_4099_;
}
else
{
lean_object* v_reuseFailAlloc_4101_; 
v_reuseFailAlloc_4101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4101_, 0, v_a_4095_);
v___x_4100_ = v_reuseFailAlloc_4101_;
goto v_reusejp_4099_;
}
v_reusejp_4099_:
{
return v___x_4100_;
}
}
}
}
else
{
lean_object* v___x_4103_; lean_object* v___x_4104_; 
lean_dec(v_____x_4012_);
lean_dec_ref(v_arg_4010_);
lean_dec_ref(v_arg_4009_);
lean_dec_ref(v_e_4008_);
v___x_4103_ = lean_box(0);
v___x_4104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4104_, 0, v___x_4103_);
return v___x_4104_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__0___boxed(lean_object** _args){
lean_object* v_e_4105_ = _args[0];
lean_object* v_arg_4106_ = _args[1];
lean_object* v_arg_4107_ = _args[2];
lean_object* v_eqTrue_4108_ = _args[3];
lean_object* v_____x_4109_ = _args[4];
lean_object* v___y_4110_ = _args[5];
lean_object* v___y_4111_ = _args[6];
lean_object* v___y_4112_ = _args[7];
lean_object* v___y_4113_ = _args[8];
lean_object* v___y_4114_ = _args[9];
lean_object* v___y_4115_ = _args[10];
lean_object* v___y_4116_ = _args[11];
lean_object* v___y_4117_ = _args[12];
lean_object* v___y_4118_ = _args[13];
lean_object* v___y_4119_ = _args[14];
lean_object* v___y_4120_ = _args[15];
lean_object* v___y_4121_ = _args[16];
_start:
{
uint8_t v_eqTrue_boxed_4122_; lean_object* v_res_4123_; 
v_eqTrue_boxed_4122_ = lean_unbox(v_eqTrue_4108_);
v_res_4123_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__0(v_e_4105_, v_arg_4106_, v_arg_4107_, v_eqTrue_boxed_4122_, v_____x_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_);
lean_dec(v___y_4120_);
lean_dec_ref(v___y_4119_);
lean_dec(v___y_4118_);
lean_dec_ref(v___y_4117_);
lean_dec(v___y_4116_);
lean_dec_ref(v___y_4115_);
lean_dec(v___y_4114_);
lean_dec_ref(v___y_4113_);
lean_dec(v___y_4112_);
lean_dec(v___y_4111_);
lean_dec(v___y_4110_);
return v_res_4123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__1(uint8_t v_eqTrue_4124_, lean_object* v___f_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_){
_start:
{
if (v_eqTrue_4124_ == 0)
{
lean_object* v___x_4138_; 
v___x_4138_ = l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLT_x3f___redArg(v___y_4126_, v___y_4127_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_);
if (lean_obj_tag(v___x_4138_) == 0)
{
lean_object* v_a_4139_; lean_object* v___x_4140_; 
v_a_4139_ = lean_ctor_get(v___x_4138_, 0);
lean_inc(v_a_4139_);
lean_dec_ref(v___x_4138_);
lean_inc(v___y_4136_);
lean_inc_ref(v___y_4135_);
lean_inc(v___y_4134_);
lean_inc_ref(v___y_4133_);
lean_inc(v___y_4132_);
lean_inc_ref(v___y_4131_);
lean_inc(v___y_4130_);
lean_inc_ref(v___y_4129_);
lean_inc(v___y_4128_);
lean_inc(v___y_4127_);
lean_inc(v___y_4126_);
v___x_4140_ = lean_apply_13(v___f_4125_, v_a_4139_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_, lean_box(0));
return v___x_4140_;
}
else
{
lean_object* v_a_4141_; lean_object* v___x_4143_; uint8_t v_isShared_4144_; uint8_t v_isSharedCheck_4148_; 
lean_dec_ref(v___f_4125_);
v_a_4141_ = lean_ctor_get(v___x_4138_, 0);
v_isSharedCheck_4148_ = !lean_is_exclusive(v___x_4138_);
if (v_isSharedCheck_4148_ == 0)
{
v___x_4143_ = v___x_4138_;
v_isShared_4144_ = v_isSharedCheck_4148_;
goto v_resetjp_4142_;
}
else
{
lean_inc(v_a_4141_);
lean_dec(v___x_4138_);
v___x_4143_ = lean_box(0);
v_isShared_4144_ = v_isSharedCheck_4148_;
goto v_resetjp_4142_;
}
v_resetjp_4142_:
{
lean_object* v___x_4146_; 
if (v_isShared_4144_ == 0)
{
v___x_4146_ = v___x_4143_;
goto v_reusejp_4145_;
}
else
{
lean_object* v_reuseFailAlloc_4147_; 
v_reuseFailAlloc_4147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4147_, 0, v_a_4141_);
v___x_4146_ = v_reuseFailAlloc_4147_;
goto v_reusejp_4145_;
}
v_reusejp_4145_:
{
return v___x_4146_;
}
}
}
}
else
{
lean_object* v___x_4149_; 
v___x_4149_ = l_Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f___redArg(v___y_4126_, v___y_4127_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_);
if (lean_obj_tag(v___x_4149_) == 0)
{
lean_object* v_a_4150_; lean_object* v___x_4151_; 
v_a_4150_ = lean_ctor_get(v___x_4149_, 0);
lean_inc(v_a_4150_);
lean_dec_ref(v___x_4149_);
lean_inc(v___y_4136_);
lean_inc_ref(v___y_4135_);
lean_inc(v___y_4134_);
lean_inc_ref(v___y_4133_);
lean_inc(v___y_4132_);
lean_inc_ref(v___y_4131_);
lean_inc(v___y_4130_);
lean_inc_ref(v___y_4129_);
lean_inc(v___y_4128_);
lean_inc(v___y_4127_);
lean_inc(v___y_4126_);
v___x_4151_ = lean_apply_13(v___f_4125_, v_a_4150_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_, lean_box(0));
return v___x_4151_;
}
else
{
lean_object* v_a_4152_; lean_object* v___x_4154_; uint8_t v_isShared_4155_; uint8_t v_isSharedCheck_4159_; 
lean_dec_ref(v___f_4125_);
v_a_4152_ = lean_ctor_get(v___x_4149_, 0);
v_isSharedCheck_4159_ = !lean_is_exclusive(v___x_4149_);
if (v_isSharedCheck_4159_ == 0)
{
v___x_4154_ = v___x_4149_;
v_isShared_4155_ = v_isSharedCheck_4159_;
goto v_resetjp_4153_;
}
else
{
lean_inc(v_a_4152_);
lean_dec(v___x_4149_);
v___x_4154_ = lean_box(0);
v_isShared_4155_ = v_isSharedCheck_4159_;
goto v_resetjp_4153_;
}
v_resetjp_4153_:
{
lean_object* v___x_4157_; 
if (v_isShared_4155_ == 0)
{
v___x_4157_ = v___x_4154_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4158_; 
v_reuseFailAlloc_4158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4158_, 0, v_a_4152_);
v___x_4157_ = v_reuseFailAlloc_4158_;
goto v_reusejp_4156_;
}
v_reusejp_4156_:
{
return v___x_4157_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__1___boxed(lean_object* v_eqTrue_4160_, lean_object* v___f_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_){
_start:
{
uint8_t v_eqTrue_boxed_4174_; lean_object* v_res_4175_; 
v_eqTrue_boxed_4174_ = lean_unbox(v_eqTrue_4160_);
v_res_4175_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__1(v_eqTrue_boxed_4174_, v___f_4161_, v___y_4162_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_);
lean_dec(v___y_4172_);
lean_dec_ref(v___y_4171_);
lean_dec(v___y_4170_);
lean_dec_ref(v___y_4169_);
lean_dec(v___y_4168_);
lean_dec_ref(v___y_4167_);
lean_dec(v___y_4166_);
lean_dec_ref(v___y_4165_);
lean_dec(v___y_4164_);
lean_dec(v___y_4163_);
lean_dec(v___y_4162_);
return v_res_4175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt(lean_object* v_e_4181_, uint8_t v_eqTrue_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_, lean_object* v_a_4186_, lean_object* v_a_4187_, lean_object* v_a_4188_, lean_object* v_a_4189_, lean_object* v_a_4190_, lean_object* v_a_4191_, lean_object* v_a_4192_){
_start:
{
lean_object* v___x_4197_; 
v___x_4197_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_4185_);
if (lean_obj_tag(v___x_4197_) == 0)
{
lean_object* v_a_4198_; lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4226_; 
v_a_4198_ = lean_ctor_get(v___x_4197_, 0);
v_isSharedCheck_4226_ = !lean_is_exclusive(v___x_4197_);
if (v_isSharedCheck_4226_ == 0)
{
v___x_4200_ = v___x_4197_;
v_isShared_4201_ = v_isSharedCheck_4226_;
goto v_resetjp_4199_;
}
else
{
lean_inc(v_a_4198_);
lean_dec(v___x_4197_);
v___x_4200_ = lean_box(0);
v_isShared_4201_ = v_isSharedCheck_4226_;
goto v_resetjp_4199_;
}
v_resetjp_4199_:
{
uint8_t v_lia_4202_; 
v_lia_4202_ = lean_ctor_get_uint8(v_a_4198_, sizeof(void*)*11 + 23);
lean_dec(v_a_4198_);
if (v_lia_4202_ == 0)
{
lean_object* v___x_4203_; lean_object* v___x_4205_; 
lean_dec_ref(v_e_4181_);
v___x_4203_ = lean_box(0);
if (v_isShared_4201_ == 0)
{
lean_ctor_set(v___x_4200_, 0, v___x_4203_);
v___x_4205_ = v___x_4200_;
goto v_reusejp_4204_;
}
else
{
lean_object* v_reuseFailAlloc_4206_; 
v_reuseFailAlloc_4206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4206_, 0, v___x_4203_);
v___x_4205_ = v_reuseFailAlloc_4206_;
goto v_reusejp_4204_;
}
v_reusejp_4204_:
{
return v___x_4205_;
}
}
else
{
lean_object* v___x_4207_; uint8_t v___x_4208_; 
lean_del_object(v___x_4200_);
lean_inc_ref(v_e_4181_);
v___x_4207_ = l_Lean_Expr_cleanupAnnotations(v_e_4181_);
v___x_4208_ = l_Lean_Expr_isApp(v___x_4207_);
if (v___x_4208_ == 0)
{
lean_dec_ref(v___x_4207_);
lean_dec_ref(v_e_4181_);
goto v___jp_4194_;
}
else
{
lean_object* v_arg_4209_; lean_object* v___x_4210_; uint8_t v___x_4211_; 
v_arg_4209_ = lean_ctor_get(v___x_4207_, 1);
lean_inc_ref(v_arg_4209_);
v___x_4210_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4207_);
v___x_4211_ = l_Lean_Expr_isApp(v___x_4210_);
if (v___x_4211_ == 0)
{
lean_dec_ref(v___x_4210_);
lean_dec_ref(v_arg_4209_);
lean_dec_ref(v_e_4181_);
goto v___jp_4194_;
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
lean_dec_ref(v_arg_4209_);
lean_dec_ref(v_e_4181_);
goto v___jp_4194_;
}
else
{
lean_object* v___x_4215_; uint8_t v___x_4216_; 
v___x_4215_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4213_);
v___x_4216_ = l_Lean_Expr_isApp(v___x_4215_);
if (v___x_4216_ == 0)
{
lean_dec_ref(v___x_4215_);
lean_dec_ref(v_arg_4212_);
lean_dec_ref(v_arg_4209_);
lean_dec_ref(v_e_4181_);
goto v___jp_4194_;
}
else
{
lean_object* v_arg_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; uint8_t v___x_4220_; 
v_arg_4217_ = lean_ctor_get(v___x_4215_, 1);
lean_inc_ref(v_arg_4217_);
v___x_4218_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4215_);
v___x_4219_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__2));
v___x_4220_ = l_Lean_Expr_isConstOf(v___x_4218_, v___x_4219_);
lean_dec_ref(v___x_4218_);
if (v___x_4220_ == 0)
{
lean_dec_ref(v_arg_4217_);
lean_dec_ref(v_arg_4212_);
lean_dec_ref(v_arg_4209_);
lean_dec_ref(v_e_4181_);
goto v___jp_4194_;
}
else
{
lean_object* v___x_4221_; lean_object* v___f_4222_; lean_object* v___x_4223_; lean_object* v___y_4224_; lean_object* v___x_4225_; 
v___x_4221_ = lean_box(v_eqTrue_4182_);
v___f_4222_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__0___boxed), 17, 4);
lean_closure_set(v___f_4222_, 0, v_e_4181_);
lean_closure_set(v___f_4222_, 1, v_arg_4212_);
lean_closure_set(v___f_4222_, 2, v_arg_4209_);
lean_closure_set(v___f_4222_, 3, v___x_4221_);
v___x_4223_ = lean_box(v_eqTrue_4182_);
v___y_4224_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__1___boxed), 14, 2);
lean_closure_set(v___y_4224_, 0, v___x_4223_);
lean_closure_set(v___y_4224_, 1, v___f_4222_);
v___x_4225_ = l_Lean_Meta_Grind_Arith_Cutsat_ToIntM_run(v_arg_4217_, v___y_4224_, v_a_4183_, v_a_4184_, v_a_4185_, v_a_4186_, v_a_4187_, v_a_4188_, v_a_4189_, v_a_4190_, v_a_4191_, v_a_4192_);
return v___x_4225_;
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
lean_object* v_a_4227_; lean_object* v___x_4229_; uint8_t v_isShared_4230_; uint8_t v_isSharedCheck_4234_; 
lean_dec_ref(v_e_4181_);
v_a_4227_ = lean_ctor_get(v___x_4197_, 0);
v_isSharedCheck_4234_ = !lean_is_exclusive(v___x_4197_);
if (v_isSharedCheck_4234_ == 0)
{
v___x_4229_ = v___x_4197_;
v_isShared_4230_ = v_isSharedCheck_4234_;
goto v_resetjp_4228_;
}
else
{
lean_inc(v_a_4227_);
lean_dec(v___x_4197_);
v___x_4229_ = lean_box(0);
v_isShared_4230_ = v_isSharedCheck_4234_;
goto v_resetjp_4228_;
}
v_resetjp_4228_:
{
lean_object* v___x_4232_; 
if (v_isShared_4230_ == 0)
{
v___x_4232_ = v___x_4229_;
goto v_reusejp_4231_;
}
else
{
lean_object* v_reuseFailAlloc_4233_; 
v_reuseFailAlloc_4233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4233_, 0, v_a_4227_);
v___x_4232_ = v_reuseFailAlloc_4233_;
goto v_reusejp_4231_;
}
v_reusejp_4231_:
{
return v___x_4232_;
}
}
}
v___jp_4194_:
{
lean_object* v___x_4195_; lean_object* v___x_4196_; 
v___x_4195_ = lean_box(0);
v___x_4196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4196_, 0, v___x_4195_);
return v___x_4196_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___boxed(lean_object* v_e_4235_, lean_object* v_eqTrue_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_, lean_object* v_a_4239_, lean_object* v_a_4240_, lean_object* v_a_4241_, lean_object* v_a_4242_, lean_object* v_a_4243_, lean_object* v_a_4244_, lean_object* v_a_4245_, lean_object* v_a_4246_, lean_object* v_a_4247_){
_start:
{
uint8_t v_eqTrue_boxed_4248_; lean_object* v_res_4249_; 
v_eqTrue_boxed_4248_ = lean_unbox(v_eqTrue_4236_);
v_res_4249_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLt(v_e_4235_, v_eqTrue_boxed_4248_, v_a_4237_, v_a_4238_, v_a_4239_, v_a_4240_, v_a_4241_, v_a_4242_, v_a_4243_, v_a_4244_, v_a_4245_, v_a_4246_);
lean_dec(v_a_4246_);
lean_dec_ref(v_a_4245_);
lean_dec(v_a_4244_);
lean_dec_ref(v_a_4243_);
lean_dec(v_a_4242_);
lean_dec_ref(v_a_4241_);
lean_dec(v_a_4240_);
lean_dec_ref(v_a_4239_);
lean_dec(v_a_4238_);
lean_dec(v_a_4237_);
return v_res_4249_;
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
