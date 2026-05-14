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
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v_ref_53_; lean_object* v___x_54_; lean_object* v_a_55_; lean_object* v___x_57_; uint8_t v_isShared_58_; uint8_t v_isSharedCheck_100_; 
v_ref_53_ = lean_ctor_get(v___y_50_, 5);
v___x_54_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0_spec__0(v_msg_47_, v___y_48_, v___y_49_, v___y_50_, v___y_51_);
v_a_55_ = lean_ctor_get(v___x_54_, 0);
v_isSharedCheck_100_ = !lean_is_exclusive(v___x_54_);
if (v_isSharedCheck_100_ == 0)
{
v___x_57_ = v___x_54_;
v_isShared_58_ = v_isSharedCheck_100_;
goto v_resetjp_56_;
}
else
{
lean_inc(v_a_55_);
lean_dec(v___x_54_);
v___x_57_ = lean_box(0);
v_isShared_58_ = v_isSharedCheck_100_;
goto v_resetjp_56_;
}
v_resetjp_56_:
{
lean_object* v___x_59_; lean_object* v_traceState_60_; lean_object* v_env_61_; lean_object* v_nextMacroScope_62_; lean_object* v_ngen_63_; lean_object* v_auxDeclNGen_64_; lean_object* v_cache_65_; lean_object* v_messages_66_; lean_object* v_infoState_67_; lean_object* v_snapshotTasks_68_; lean_object* v_newDecls_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_99_; 
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
v_newDecls_69_ = lean_ctor_get(v___x_59_, 9);
v_isSharedCheck_99_ = !lean_is_exclusive(v___x_59_);
if (v_isSharedCheck_99_ == 0)
{
v___x_71_ = v___x_59_;
v_isShared_72_ = v_isSharedCheck_99_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_newDecls_69_);
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
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_99_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
uint64_t v_tid_73_; lean_object* v_traces_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_98_; 
v_tid_73_ = lean_ctor_get_uint64(v_traceState_60_, sizeof(void*)*1);
v_traces_74_ = lean_ctor_get(v_traceState_60_, 0);
v_isSharedCheck_98_ = !lean_is_exclusive(v_traceState_60_);
if (v_isSharedCheck_98_ == 0)
{
v___x_76_ = v_traceState_60_;
v_isShared_77_ = v_isSharedCheck_98_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_traces_74_);
lean_dec(v_traceState_60_);
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
lean_ctor_set(v___x_82_, 0, v_cls_46_);
lean_ctor_set(v___x_82_, 1, v___x_78_);
lean_ctor_set(v___x_82_, 2, v___x_81_);
lean_ctor_set_float(v___x_82_, sizeof(void*)*3, v___x_79_);
lean_ctor_set_float(v___x_82_, sizeof(void*)*3 + 8, v___x_79_);
lean_ctor_set_uint8(v___x_82_, sizeof(void*)*3 + 16, v___x_80_);
v___x_83_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__2));
v___x_84_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_84_, 0, v___x_82_);
lean_ctor_set(v___x_84_, 1, v_a_55_);
lean_ctor_set(v___x_84_, 2, v___x_83_);
lean_inc(v_ref_53_);
v___x_85_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_85_, 0, v_ref_53_);
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
v_reuseFailAlloc_96_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v_env_61_);
lean_ctor_set(v_reuseFailAlloc_96_, 1, v_nextMacroScope_62_);
lean_ctor_set(v_reuseFailAlloc_96_, 2, v_ngen_63_);
lean_ctor_set(v_reuseFailAlloc_96_, 3, v_auxDeclNGen_64_);
lean_ctor_set(v_reuseFailAlloc_96_, 4, v___x_88_);
lean_ctor_set(v_reuseFailAlloc_96_, 5, v_cache_65_);
lean_ctor_set(v_reuseFailAlloc_96_, 6, v_messages_66_);
lean_ctor_set(v_reuseFailAlloc_96_, 7, v_infoState_67_);
lean_ctor_set(v_reuseFailAlloc_96_, 8, v_snapshotTasks_68_);
lean_ctor_set(v_reuseFailAlloc_96_, 9, v_newDecls_69_);
v___x_90_ = v_reuseFailAlloc_96_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_94_; 
v___x_91_ = lean_st_ref_set(v___y_51_, v___x_90_);
v___x_92_ = lean_box(0);
if (v_isShared_58_ == 0)
{
lean_ctor_set(v___x_57_, 0, v___x_92_);
v___x_94_ = v___x_57_;
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
v___x_205_ = l_Int_Linear_Poly_mul(v_p_201_, v_b_130_);
v___x_206_ = lean_int_neg(v_a_127_);
lean_inc_ref(v_p_202_);
v___x_207_ = l_Int_Linear_Poly_mul(v_p_202_, v___x_206_);
lean_dec(v___x_206_);
v___x_208_ = l_Int_Linear_Poly_combine(v___x_205_, v___x_207_);
v___y_149_ = v___x_208_;
goto v___jp_148_;
}
else
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
lean_inc_ref(v_p_202_);
v___x_209_ = l_Int_Linear_Poly_mul(v_p_202_, v_a_127_);
v___x_210_ = lean_int_neg(v_b_130_);
lean_inc_ref(v_p_201_);
v___x_211_ = l_Int_Linear_Poly_mul(v_p_201_, v___x_210_);
lean_dec(v___x_210_);
v___x_212_ = l_Int_Linear_Poly_combine(v___x_209_, v___x_211_);
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
lean_dec_ref(v___x_156_);
lean_inc_ref(v_c_u2081_129_);
v___x_158_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_u2081_129_, v_a_132_, v_a_140_);
if (lean_obj_tag(v___x_158_) == 0)
{
lean_object* v_a_159_; lean_object* v___x_160_; 
v_a_159_ = lean_ctor_get(v___x_158_, 0);
lean_inc(v_a_159_);
lean_dec_ref(v___x_158_);
lean_inc_ref(v_c_u2082_131_);
v___x_160_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2082_131_, v_a_132_, v_a_140_);
if (lean_obj_tag(v___x_160_) == 0)
{
lean_object* v_a_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v_a_161_ = lean_ctor_get(v___x_160_, 0);
lean_inc(v_a_161_);
lean_dec_ref(v___x_160_);
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
lean_dec_ref(v___x_168_);
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
lean_object* v_p_318_; lean_object* v_fileName_319_; lean_object* v_fileMap_320_; lean_object* v_options_321_; lean_object* v_currRecDepth_322_; lean_object* v_maxRecDepth_323_; lean_object* v_ref_324_; lean_object* v_currNamespace_325_; lean_object* v_openDecls_326_; lean_object* v_initHeartbeats_327_; lean_object* v_maxHeartbeats_328_; lean_object* v_quotContext_329_; lean_object* v_currMacroScope_330_; uint8_t v_diag_331_; lean_object* v_cancelTk_x3f_332_; uint8_t v_suppressElabErrors_333_; lean_object* v_inheritedTraceOptions_334_; lean_object* v___x_366_; uint8_t v___x_367_; 
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
v___x_366_ = lean_unsigned_to_nat(0u);
v___x_367_ = lean_nat_dec_eq(v_maxRecDepth_323_, v___x_366_);
if (v___x_367_ == 0)
{
uint8_t v___x_368_; 
v___x_368_ = lean_nat_dec_eq(v_currRecDepth_322_, v_maxRecDepth_323_);
if (v___x_368_ == 0)
{
goto v___jp_335_;
}
else
{
lean_object* v___x_369_; 
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
v___x_369_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg(v_ref_324_);
return v___x_369_;
}
}
else
{
goto v___jp_335_;
}
v___jp_335_:
{
lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_336_ = lean_unsigned_to_nat(1u);
v___x_337_ = lean_nat_add(v_currRecDepth_322_, v___x_336_);
lean_dec(v_currRecDepth_322_);
v___x_338_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_338_, 0, v_fileName_319_);
lean_ctor_set(v___x_338_, 1, v_fileMap_320_);
lean_ctor_set(v___x_338_, 2, v_options_321_);
lean_ctor_set(v___x_338_, 3, v___x_337_);
lean_ctor_set(v___x_338_, 4, v_maxRecDepth_323_);
lean_ctor_set(v___x_338_, 5, v_ref_324_);
lean_ctor_set(v___x_338_, 6, v_currNamespace_325_);
lean_ctor_set(v___x_338_, 7, v_openDecls_326_);
lean_ctor_set(v___x_338_, 8, v_initHeartbeats_327_);
lean_ctor_set(v___x_338_, 9, v_maxHeartbeats_328_);
lean_ctor_set(v___x_338_, 10, v_quotContext_329_);
lean_ctor_set(v___x_338_, 11, v_currMacroScope_330_);
lean_ctor_set(v___x_338_, 12, v_cancelTk_x3f_332_);
lean_ctor_set(v___x_338_, 13, v_inheritedTraceOptions_334_);
lean_ctor_set_uint8(v___x_338_, sizeof(void*)*14, v_diag_331_);
lean_ctor_set_uint8(v___x_338_, sizeof(void*)*14 + 1, v_suppressElabErrors_333_);
lean_inc_ref(v_p_318_);
v___x_339_ = l_Int_Linear_Poly_findVarToSubst___redArg(v_p_318_, v_a_307_, v___x_338_);
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v_a_340_; lean_object* v___x_342_; uint8_t v_isShared_343_; uint8_t v_isSharedCheck_357_; 
v_a_340_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_357_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_357_ == 0)
{
v___x_342_ = v___x_339_;
v_isShared_343_ = v_isSharedCheck_357_;
goto v_resetjp_341_;
}
else
{
lean_inc(v_a_340_);
lean_dec(v___x_339_);
v___x_342_ = lean_box(0);
v_isShared_343_ = v_isSharedCheck_357_;
goto v_resetjp_341_;
}
v_resetjp_341_:
{
if (lean_obj_tag(v_a_340_) == 1)
{
lean_object* v_val_344_; lean_object* v_snd_345_; lean_object* v_snd_346_; lean_object* v_fst_347_; lean_object* v_fst_348_; lean_object* v_p_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
lean_del_object(v___x_342_);
v_val_344_ = lean_ctor_get(v_a_340_, 0);
lean_inc(v_val_344_);
lean_dec_ref(v_a_340_);
v_snd_345_ = lean_ctor_get(v_val_344_, 1);
lean_inc(v_snd_345_);
v_snd_346_ = lean_ctor_get(v_snd_345_, 1);
lean_inc(v_snd_346_);
v_fst_347_ = lean_ctor_get(v_val_344_, 0);
lean_inc(v_fst_347_);
lean_dec(v_val_344_);
v_fst_348_ = lean_ctor_get(v_snd_345_, 0);
lean_inc(v_fst_348_);
lean_dec(v_snd_345_);
v_p_349_ = lean_ctor_get(v_snd_346_, 0);
v___x_350_ = l_Int_Linear_Poly_coeff(v_p_349_, v_fst_348_);
v___x_351_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq(v___x_350_, v_fst_348_, v_snd_346_, v_fst_347_, v_c_306_, v_a_307_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_, v___x_338_, v_a_316_);
lean_dec(v_fst_347_);
lean_dec(v___x_350_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v_a_352_; 
v_a_352_ = lean_ctor_get(v___x_351_, 0);
lean_inc(v_a_352_);
lean_dec_ref(v___x_351_);
v_c_306_ = v_a_352_;
v_a_315_ = v___x_338_;
goto _start;
}
else
{
lean_dec_ref(v___x_338_);
return v___x_351_;
}
}
else
{
lean_object* v___x_355_; 
lean_dec(v_a_340_);
lean_dec_ref(v___x_338_);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 0, v_c_306_);
v___x_355_ = v___x_342_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_c_306_);
v___x_355_ = v_reuseFailAlloc_356_;
goto v_reusejp_354_;
}
v_reusejp_354_:
{
return v___x_355_;
}
}
}
}
else
{
lean_object* v_a_358_; lean_object* v___x_360_; uint8_t v_isShared_361_; uint8_t v_isSharedCheck_365_; 
lean_dec_ref(v___x_338_);
lean_dec_ref(v_c_306_);
v_a_358_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_365_ == 0)
{
v___x_360_ = v___x_339_;
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
else
{
lean_inc(v_a_358_);
lean_dec(v___x_339_);
v___x_360_ = lean_box(0);
v_isShared_361_ = v_isSharedCheck_365_;
goto v_resetjp_359_;
}
v_resetjp_359_:
{
lean_object* v___x_363_; 
if (v_isShared_361_ == 0)
{
v___x_363_ = v___x_360_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_a_358_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts___boxed(lean_object* v_c_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_){
_start:
{
lean_object* v_res_382_; 
v_res_382_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts(v_c_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_, v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_);
lean_dec(v_a_380_);
lean_dec(v_a_378_);
lean_dec_ref(v_a_377_);
lean_dec(v_a_376_);
lean_dec_ref(v_a_375_);
lean_dec(v_a_374_);
lean_dec_ref(v_a_373_);
lean_dec(v_a_372_);
lean_dec(v_a_371_);
return v_res_382_;
}
}
LEAN_EXPORT uint8_t l_Int_Linear_Poly_isNegEq(lean_object* v_p_u2081_383_, lean_object* v_p_u2082_384_){
_start:
{
if (lean_obj_tag(v_p_u2081_383_) == 0)
{
if (lean_obj_tag(v_p_u2082_384_) == 0)
{
lean_object* v_k_385_; lean_object* v_k_386_; lean_object* v___x_387_; uint8_t v___x_388_; 
v_k_385_ = lean_ctor_get(v_p_u2081_383_, 0);
v_k_386_ = lean_ctor_get(v_p_u2082_384_, 0);
v___x_387_ = lean_int_neg(v_k_386_);
v___x_388_ = lean_int_dec_eq(v_k_385_, v___x_387_);
lean_dec(v___x_387_);
return v___x_388_;
}
else
{
uint8_t v___x_389_; 
v___x_389_ = 0;
return v___x_389_;
}
}
else
{
if (lean_obj_tag(v_p_u2082_384_) == 1)
{
lean_object* v_k_390_; lean_object* v_v_391_; lean_object* v_p_392_; lean_object* v_k_393_; lean_object* v_v_394_; lean_object* v_p_395_; uint8_t v___y_397_; lean_object* v___x_399_; uint8_t v___x_400_; 
v_k_390_ = lean_ctor_get(v_p_u2081_383_, 0);
v_v_391_ = lean_ctor_get(v_p_u2081_383_, 1);
v_p_392_ = lean_ctor_get(v_p_u2081_383_, 2);
v_k_393_ = lean_ctor_get(v_p_u2082_384_, 0);
v_v_394_ = lean_ctor_get(v_p_u2082_384_, 1);
v_p_395_ = lean_ctor_get(v_p_u2082_384_, 2);
v___x_399_ = lean_int_neg(v_k_393_);
v___x_400_ = lean_int_dec_eq(v_k_390_, v___x_399_);
lean_dec(v___x_399_);
if (v___x_400_ == 0)
{
v___y_397_ = v___x_400_;
goto v___jp_396_;
}
else
{
uint8_t v___x_401_; 
v___x_401_ = lean_nat_dec_eq(v_v_391_, v_v_394_);
v___y_397_ = v___x_401_;
goto v___jp_396_;
}
v___jp_396_:
{
if (v___y_397_ == 0)
{
return v___y_397_;
}
else
{
v_p_u2081_383_ = v_p_392_;
v_p_u2082_384_ = v_p_395_;
goto _start;
}
}
}
else
{
uint8_t v___x_402_; 
v___x_402_ = 0;
return v___x_402_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_isNegEq___boxed(lean_object* v_p_u2081_403_, lean_object* v_p_u2082_404_){
_start:
{
uint8_t v_res_405_; lean_object* v_r_406_; 
v_res_405_ = l_Int_Linear_Poly_isNegEq(v_p_u2081_403_, v_p_u2082_404_);
lean_dec_ref(v_p_u2082_404_);
lean_dec_ref(v_p_u2081_403_);
v_r_406_ = lean_box(v_res_405_);
return v_r_406_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(lean_object* v___x_407_, lean_object* v_as_408_, size_t v_i_409_, size_t v_stop_410_, lean_object* v_b_411_){
_start:
{
lean_object* v___y_413_; uint8_t v___x_417_; 
v___x_417_ = lean_usize_dec_eq(v_i_409_, v_stop_410_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; lean_object* v_p_419_; uint8_t v___x_420_; 
v___x_418_ = lean_array_uget_borrowed(v_as_408_, v_i_409_);
v_p_419_ = lean_ctor_get(v___x_418_, 0);
v___x_420_ = l_Int_Linear_instBEqPoly_beq(v_p_419_, v___x_407_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; 
lean_inc(v___x_418_);
v___x_421_ = l_Lean_PersistentArray_push___redArg(v_b_411_, v___x_418_);
v___y_413_ = v___x_421_;
goto v___jp_412_;
}
else
{
v___y_413_ = v_b_411_;
goto v___jp_412_;
}
}
else
{
return v_b_411_;
}
v___jp_412_:
{
size_t v___x_414_; size_t v___x_415_; 
v___x_414_ = ((size_t)1ULL);
v___x_415_ = lean_usize_add(v_i_409_, v___x_414_);
v_i_409_ = v___x_415_;
v_b_411_ = v___y_413_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1___boxed(lean_object* v___x_422_, lean_object* v_as_423_, lean_object* v_i_424_, lean_object* v_stop_425_, lean_object* v_b_426_){
_start:
{
size_t v_i_boxed_427_; size_t v_stop_boxed_428_; lean_object* v_res_429_; 
v_i_boxed_427_ = lean_unbox_usize(v_i_424_);
lean_dec(v_i_424_);
v_stop_boxed_428_ = lean_unbox_usize(v_stop_425_);
lean_dec(v_stop_425_);
v_res_429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_422_, v_as_423_, v_i_boxed_427_, v_stop_boxed_428_, v_b_426_);
lean_dec_ref(v_as_423_);
lean_dec_ref(v___x_422_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2(lean_object* v___x_430_, lean_object* v_x_431_, lean_object* v_x_432_){
_start:
{
if (lean_obj_tag(v_x_431_) == 0)
{
lean_object* v_cs_433_; lean_object* v___x_434_; lean_object* v___x_435_; uint8_t v___x_436_; 
v_cs_433_ = lean_ctor_get(v_x_431_, 0);
v___x_434_ = lean_unsigned_to_nat(0u);
v___x_435_ = lean_array_get_size(v_cs_433_);
v___x_436_ = lean_nat_dec_lt(v___x_434_, v___x_435_);
if (v___x_436_ == 0)
{
return v_x_432_;
}
else
{
uint8_t v___x_437_; 
v___x_437_ = lean_nat_dec_le(v___x_435_, v___x_435_);
if (v___x_437_ == 0)
{
if (v___x_436_ == 0)
{
return v_x_432_;
}
else
{
size_t v___x_438_; size_t v___x_439_; lean_object* v___x_440_; 
v___x_438_ = ((size_t)0ULL);
v___x_439_ = lean_usize_of_nat(v___x_435_);
v___x_440_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v___x_430_, v_cs_433_, v___x_438_, v___x_439_, v_x_432_);
return v___x_440_;
}
}
else
{
size_t v___x_441_; size_t v___x_442_; lean_object* v___x_443_; 
v___x_441_ = ((size_t)0ULL);
v___x_442_ = lean_usize_of_nat(v___x_435_);
v___x_443_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v___x_430_, v_cs_433_, v___x_441_, v___x_442_, v_x_432_);
return v___x_443_;
}
}
}
else
{
lean_object* v_vs_444_; lean_object* v___x_445_; lean_object* v___x_446_; uint8_t v___x_447_; 
v_vs_444_ = lean_ctor_get(v_x_431_, 0);
v___x_445_ = lean_unsigned_to_nat(0u);
v___x_446_ = lean_array_get_size(v_vs_444_);
v___x_447_ = lean_nat_dec_lt(v___x_445_, v___x_446_);
if (v___x_447_ == 0)
{
return v_x_432_;
}
else
{
uint8_t v___x_448_; 
v___x_448_ = lean_nat_dec_le(v___x_446_, v___x_446_);
if (v___x_448_ == 0)
{
if (v___x_447_ == 0)
{
return v_x_432_;
}
else
{
size_t v___x_449_; size_t v___x_450_; lean_object* v___x_451_; 
v___x_449_ = ((size_t)0ULL);
v___x_450_ = lean_usize_of_nat(v___x_446_);
v___x_451_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_430_, v_vs_444_, v___x_449_, v___x_450_, v_x_432_);
return v___x_451_;
}
}
else
{
size_t v___x_452_; size_t v___x_453_; lean_object* v___x_454_; 
v___x_452_ = ((size_t)0ULL);
v___x_453_ = lean_usize_of_nat(v___x_446_);
v___x_454_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_430_, v_vs_444_, v___x_452_, v___x_453_, v_x_432_);
return v___x_454_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(lean_object* v___x_455_, lean_object* v_as_456_, size_t v_i_457_, size_t v_stop_458_, lean_object* v_b_459_){
_start:
{
uint8_t v___x_460_; 
v___x_460_ = lean_usize_dec_eq(v_i_457_, v_stop_458_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; lean_object* v___x_462_; size_t v___x_463_; size_t v___x_464_; 
v___x_461_ = lean_array_uget_borrowed(v_as_456_, v_i_457_);
v___x_462_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2(v___x_455_, v___x_461_, v_b_459_);
v___x_463_ = ((size_t)1ULL);
v___x_464_ = lean_usize_add(v_i_457_, v___x_463_);
v_i_457_ = v___x_464_;
v_b_459_ = v___x_462_;
goto _start;
}
else
{
return v_b_459_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1___boxed(lean_object* v___x_466_, lean_object* v_as_467_, lean_object* v_i_468_, lean_object* v_stop_469_, lean_object* v_b_470_){
_start:
{
size_t v_i_boxed_471_; size_t v_stop_boxed_472_; lean_object* v_res_473_; 
v_i_boxed_471_ = lean_unbox_usize(v_i_468_);
lean_dec(v_i_468_);
v_stop_boxed_472_ = lean_unbox_usize(v_stop_469_);
lean_dec(v_stop_469_);
v_res_473_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v___x_466_, v_as_467_, v_i_boxed_471_, v_stop_boxed_472_, v_b_470_);
lean_dec_ref(v_as_467_);
lean_dec_ref(v___x_466_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2___boxed(lean_object* v___x_474_, lean_object* v_x_475_, lean_object* v_x_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2(v___x_474_, v_x_475_, v_x_476_);
lean_dec_ref(v_x_475_);
lean_dec_ref(v___x_474_);
return v_res_477_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_478_; 
v___x_478_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(lean_object* v___x_479_, lean_object* v_x_480_, size_t v_x_481_, size_t v_x_482_, lean_object* v_x_483_){
_start:
{
if (lean_obj_tag(v_x_480_) == 0)
{
lean_object* v_cs_484_; lean_object* v___x_485_; size_t v___x_486_; lean_object* v_j_487_; lean_object* v___x_488_; size_t v___x_489_; size_t v___x_490_; size_t v___x_491_; size_t v___x_492_; size_t v___x_493_; size_t v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_497_; lean_object* v___x_498_; uint8_t v___x_499_; 
v_cs_484_ = lean_ctor_get(v_x_480_, 0);
v___x_485_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0);
v___x_486_ = lean_usize_shift_right(v_x_481_, v_x_482_);
v_j_487_ = lean_usize_to_nat(v___x_486_);
v___x_488_ = lean_array_get_borrowed(v___x_485_, v_cs_484_, v_j_487_);
v___x_489_ = ((size_t)1ULL);
v___x_490_ = lean_usize_shift_left(v___x_489_, v_x_482_);
v___x_491_ = lean_usize_sub(v___x_490_, v___x_489_);
v___x_492_ = lean_usize_land(v_x_481_, v___x_491_);
v___x_493_ = ((size_t)5ULL);
v___x_494_ = lean_usize_sub(v_x_482_, v___x_493_);
v___x_495_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(v___x_479_, v___x_488_, v___x_492_, v___x_494_, v_x_483_);
v___x_496_ = lean_unsigned_to_nat(1u);
v___x_497_ = lean_nat_add(v_j_487_, v___x_496_);
lean_dec(v_j_487_);
v___x_498_ = lean_array_get_size(v_cs_484_);
v___x_499_ = lean_nat_dec_lt(v___x_497_, v___x_498_);
if (v___x_499_ == 0)
{
lean_dec(v___x_497_);
return v___x_495_;
}
else
{
uint8_t v___x_500_; 
v___x_500_ = lean_nat_dec_le(v___x_498_, v___x_498_);
if (v___x_500_ == 0)
{
if (v___x_499_ == 0)
{
lean_dec(v___x_497_);
return v___x_495_;
}
else
{
size_t v___x_501_; size_t v___x_502_; lean_object* v___x_503_; 
v___x_501_ = lean_usize_of_nat(v___x_497_);
lean_dec(v___x_497_);
v___x_502_ = lean_usize_of_nat(v___x_498_);
v___x_503_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v___x_479_, v_cs_484_, v___x_501_, v___x_502_, v___x_495_);
return v___x_503_;
}
}
else
{
size_t v___x_504_; size_t v___x_505_; lean_object* v___x_506_; 
v___x_504_ = lean_usize_of_nat(v___x_497_);
lean_dec(v___x_497_);
v___x_505_ = lean_usize_of_nat(v___x_498_);
v___x_506_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v___x_479_, v_cs_484_, v___x_504_, v___x_505_, v___x_495_);
return v___x_506_;
}
}
}
else
{
lean_object* v_vs_507_; lean_object* v___x_508_; lean_object* v___x_509_; uint8_t v___x_510_; 
v_vs_507_ = lean_ctor_get(v_x_480_, 0);
v___x_508_ = lean_usize_to_nat(v_x_481_);
v___x_509_ = lean_array_get_size(v_vs_507_);
v___x_510_ = lean_nat_dec_lt(v___x_508_, v___x_509_);
if (v___x_510_ == 0)
{
lean_dec(v___x_508_);
return v_x_483_;
}
else
{
uint8_t v___x_511_; 
v___x_511_ = lean_nat_dec_le(v___x_509_, v___x_509_);
if (v___x_511_ == 0)
{
if (v___x_510_ == 0)
{
lean_dec(v___x_508_);
return v_x_483_;
}
else
{
size_t v___x_512_; size_t v___x_513_; lean_object* v___x_514_; 
v___x_512_ = lean_usize_of_nat(v___x_508_);
lean_dec(v___x_508_);
v___x_513_ = lean_usize_of_nat(v___x_509_);
v___x_514_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_479_, v_vs_507_, v___x_512_, v___x_513_, v_x_483_);
return v___x_514_;
}
}
else
{
size_t v___x_515_; size_t v___x_516_; lean_object* v___x_517_; 
v___x_515_ = lean_usize_of_nat(v___x_508_);
lean_dec(v___x_508_);
v___x_516_ = lean_usize_of_nat(v___x_509_);
v___x_517_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_479_, v_vs_507_, v___x_515_, v___x_516_, v_x_483_);
return v___x_517_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___boxed(lean_object* v___x_518_, lean_object* v_x_519_, lean_object* v_x_520_, lean_object* v_x_521_, lean_object* v_x_522_){
_start:
{
size_t v_x_2065__boxed_523_; size_t v_x_2066__boxed_524_; lean_object* v_res_525_; 
v_x_2065__boxed_523_ = lean_unbox_usize(v_x_520_);
lean_dec(v_x_520_);
v_x_2066__boxed_524_ = lean_unbox_usize(v_x_521_);
lean_dec(v_x_521_);
v_res_525_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(v___x_518_, v_x_519_, v_x_2065__boxed_523_, v_x_2066__boxed_524_, v_x_522_);
lean_dec_ref(v_x_519_);
lean_dec_ref(v___x_518_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(lean_object* v___x_526_, lean_object* v_t_527_, lean_object* v_init_528_, lean_object* v_start_529_){
_start:
{
lean_object* v___x_530_; uint8_t v___x_531_; 
v___x_530_ = lean_unsigned_to_nat(0u);
v___x_531_ = lean_nat_dec_eq(v_start_529_, v___x_530_);
if (v___x_531_ == 0)
{
lean_object* v_root_532_; lean_object* v_tail_533_; size_t v_shift_534_; lean_object* v_tailOff_535_; uint8_t v___x_536_; 
v_root_532_ = lean_ctor_get(v_t_527_, 0);
v_tail_533_ = lean_ctor_get(v_t_527_, 1);
v_shift_534_ = lean_ctor_get_usize(v_t_527_, 4);
v_tailOff_535_ = lean_ctor_get(v_t_527_, 3);
v___x_536_ = lean_nat_dec_le(v_tailOff_535_, v_start_529_);
if (v___x_536_ == 0)
{
size_t v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; uint8_t v___x_540_; 
v___x_537_ = lean_usize_of_nat(v_start_529_);
v___x_538_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(v___x_526_, v_root_532_, v___x_537_, v_shift_534_, v_init_528_);
v___x_539_ = lean_array_get_size(v_tail_533_);
v___x_540_ = lean_nat_dec_lt(v___x_530_, v___x_539_);
if (v___x_540_ == 0)
{
return v___x_538_;
}
else
{
uint8_t v___x_541_; 
v___x_541_ = lean_nat_dec_le(v___x_539_, v___x_539_);
if (v___x_541_ == 0)
{
if (v___x_540_ == 0)
{
return v___x_538_;
}
else
{
size_t v___x_542_; size_t v___x_543_; lean_object* v___x_544_; 
v___x_542_ = ((size_t)0ULL);
v___x_543_ = lean_usize_of_nat(v___x_539_);
v___x_544_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_526_, v_tail_533_, v___x_542_, v___x_543_, v___x_538_);
return v___x_544_;
}
}
else
{
size_t v___x_545_; size_t v___x_546_; lean_object* v___x_547_; 
v___x_545_ = ((size_t)0ULL);
v___x_546_ = lean_usize_of_nat(v___x_539_);
v___x_547_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_526_, v_tail_533_, v___x_545_, v___x_546_, v___x_538_);
return v___x_547_;
}
}
}
else
{
lean_object* v___x_548_; lean_object* v___x_549_; uint8_t v___x_550_; 
v___x_548_ = lean_nat_sub(v_start_529_, v_tailOff_535_);
v___x_549_ = lean_array_get_size(v_tail_533_);
v___x_550_ = lean_nat_dec_lt(v___x_548_, v___x_549_);
if (v___x_550_ == 0)
{
lean_dec(v___x_548_);
return v_init_528_;
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
return v_init_528_;
}
else
{
size_t v___x_552_; size_t v___x_553_; lean_object* v___x_554_; 
v___x_552_ = lean_usize_of_nat(v___x_548_);
lean_dec(v___x_548_);
v___x_553_ = lean_usize_of_nat(v___x_549_);
v___x_554_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_526_, v_tail_533_, v___x_552_, v___x_553_, v_init_528_);
return v___x_554_;
}
}
else
{
size_t v___x_555_; size_t v___x_556_; lean_object* v___x_557_; 
v___x_555_ = lean_usize_of_nat(v___x_548_);
lean_dec(v___x_548_);
v___x_556_ = lean_usize_of_nat(v___x_549_);
v___x_557_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_526_, v_tail_533_, v___x_555_, v___x_556_, v_init_528_);
return v___x_557_;
}
}
}
}
else
{
lean_object* v_root_558_; lean_object* v_tail_559_; lean_object* v___x_560_; lean_object* v___x_561_; uint8_t v___x_562_; 
v_root_558_ = lean_ctor_get(v_t_527_, 0);
v_tail_559_ = lean_ctor_get(v_t_527_, 1);
v___x_560_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2(v___x_526_, v_root_558_, v_init_528_);
v___x_561_ = lean_array_get_size(v_tail_559_);
v___x_562_ = lean_nat_dec_lt(v___x_530_, v___x_561_);
if (v___x_562_ == 0)
{
return v___x_560_;
}
else
{
uint8_t v___x_563_; 
v___x_563_ = lean_nat_dec_le(v___x_561_, v___x_561_);
if (v___x_563_ == 0)
{
if (v___x_562_ == 0)
{
return v___x_560_;
}
else
{
size_t v___x_564_; size_t v___x_565_; lean_object* v___x_566_; 
v___x_564_ = ((size_t)0ULL);
v___x_565_ = lean_usize_of_nat(v___x_561_);
v___x_566_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_526_, v_tail_559_, v___x_564_, v___x_565_, v___x_560_);
return v___x_566_;
}
}
else
{
size_t v___x_567_; size_t v___x_568_; lean_object* v___x_569_; 
v___x_567_ = ((size_t)0ULL);
v___x_568_ = lean_usize_of_nat(v___x_561_);
v___x_569_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v___x_526_, v_tail_559_, v___x_567_, v___x_568_, v___x_560_);
return v___x_569_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0___boxed(lean_object* v___x_570_, lean_object* v_t_571_, lean_object* v_init_572_, lean_object* v_start_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(v___x_570_, v_t_571_, v_init_572_, v_start_573_);
lean_dec(v_start_573_);
lean_dec_ref(v_t_571_);
lean_dec_ref(v___x_570_);
return v_res_574_;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_575_ = lean_unsigned_to_nat(32u);
v___x_576_ = lean_mk_empty_array_with_capacity(v___x_575_);
v___x_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
return v___x_577_;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1(void){
_start:
{
size_t v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; 
v___x_578_ = ((size_t)5ULL);
v___x_579_ = lean_unsigned_to_nat(0u);
v___x_580_ = lean_unsigned_to_nat(32u);
v___x_581_ = lean_mk_empty_array_with_capacity(v___x_580_);
v___x_582_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__0, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__0_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__0);
v___x_583_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_583_, 0, v___x_582_);
lean_ctor_set(v___x_583_, 1, v___x_581_);
lean_ctor_set(v___x_583_, 2, v___x_579_);
lean_ctor_set(v___x_583_, 3, v___x_579_);
lean_ctor_set_usize(v___x_583_, 4, v___x_578_);
return v___x_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4(lean_object* v___x_584_, lean_object* v_x_585_, size_t v_x_586_, size_t v_x_587_){
_start:
{
if (lean_obj_tag(v_x_585_) == 0)
{
lean_object* v_cs_588_; size_t v_j_589_; lean_object* v___x_590_; lean_object* v___x_591_; uint8_t v___x_592_; 
v_cs_588_ = lean_ctor_get(v_x_585_, 0);
v_j_589_ = lean_usize_shift_right(v_x_586_, v_x_587_);
v___x_590_ = lean_usize_to_nat(v_j_589_);
v___x_591_ = lean_array_get_size(v_cs_588_);
v___x_592_ = lean_nat_dec_lt(v___x_590_, v___x_591_);
if (v___x_592_ == 0)
{
lean_dec(v___x_590_);
return v_x_585_;
}
else
{
lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_610_; 
lean_inc_ref(v_cs_588_);
v_isSharedCheck_610_ = !lean_is_exclusive(v_x_585_);
if (v_isSharedCheck_610_ == 0)
{
lean_object* v_unused_611_; 
v_unused_611_ = lean_ctor_get(v_x_585_, 0);
lean_dec(v_unused_611_);
v___x_594_ = v_x_585_;
v_isShared_595_ = v_isSharedCheck_610_;
goto v_resetjp_593_;
}
else
{
lean_dec(v_x_585_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_610_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
size_t v___x_596_; size_t v___x_597_; size_t v___x_598_; size_t v_i_599_; size_t v___x_600_; size_t v_shift_601_; lean_object* v_v_602_; lean_object* v___x_603_; lean_object* v_xs_x27_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_608_; 
v___x_596_ = ((size_t)1ULL);
v___x_597_ = lean_usize_shift_left(v___x_596_, v_x_587_);
v___x_598_ = lean_usize_sub(v___x_597_, v___x_596_);
v_i_599_ = lean_usize_land(v_x_586_, v___x_598_);
v___x_600_ = ((size_t)5ULL);
v_shift_601_ = lean_usize_sub(v_x_587_, v___x_600_);
v_v_602_ = lean_array_fget(v_cs_588_, v___x_590_);
v___x_603_ = lean_box(0);
v_xs_x27_604_ = lean_array_fset(v_cs_588_, v___x_590_, v___x_603_);
v___x_605_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4(v___x_584_, v_v_602_, v_i_599_, v_shift_601_);
v___x_606_ = lean_array_fset(v_xs_x27_604_, v___x_590_, v___x_605_);
lean_dec(v___x_590_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v___x_606_);
v___x_608_ = v___x_594_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v___x_606_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
else
{
lean_object* v_vs_612_; lean_object* v___x_613_; lean_object* v___x_614_; uint8_t v___x_615_; 
v_vs_612_ = lean_ctor_get(v_x_585_, 0);
v___x_613_ = lean_usize_to_nat(v_x_586_);
v___x_614_ = lean_array_get_size(v_vs_612_);
v___x_615_ = lean_nat_dec_lt(v___x_613_, v___x_614_);
if (v___x_615_ == 0)
{
lean_dec(v___x_613_);
return v_x_585_;
}
else
{
lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_629_; 
lean_inc_ref(v_vs_612_);
v_isSharedCheck_629_ = !lean_is_exclusive(v_x_585_);
if (v_isSharedCheck_629_ == 0)
{
lean_object* v_unused_630_; 
v_unused_630_ = lean_ctor_get(v_x_585_, 0);
lean_dec(v_unused_630_);
v___x_617_ = v_x_585_;
v_isShared_618_ = v_isSharedCheck_629_;
goto v_resetjp_616_;
}
else
{
lean_dec(v_x_585_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_629_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
lean_object* v_v_619_; lean_object* v___x_620_; lean_object* v_xs_x27_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_627_; 
v_v_619_ = lean_array_fget(v_vs_612_, v___x_613_);
v___x_620_ = lean_box(0);
v_xs_x27_621_ = lean_array_fset(v_vs_612_, v___x_613_, v___x_620_);
v___x_622_ = lean_unsigned_to_nat(0u);
v___x_623_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1);
v___x_624_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(v___x_584_, v_v_619_, v___x_623_, v___x_622_);
lean_dec(v_v_619_);
v___x_625_ = lean_array_fset(v_xs_x27_621_, v___x_613_, v___x_624_);
lean_dec(v___x_613_);
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 0, v___x_625_);
v___x_627_ = v___x_617_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_628_; 
v_reuseFailAlloc_628_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___boxed(lean_object* v___x_631_, lean_object* v_x_632_, lean_object* v_x_633_, lean_object* v_x_634_){
_start:
{
size_t v_x_2238__boxed_635_; size_t v_x_2239__boxed_636_; lean_object* v_res_637_; 
v_x_2238__boxed_635_ = lean_unbox_usize(v_x_633_);
lean_dec(v_x_633_);
v_x_2239__boxed_636_ = lean_unbox_usize(v_x_634_);
lean_dec(v_x_634_);
v_res_637_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4(v___x_631_, v_x_632_, v_x_2238__boxed_635_, v_x_2239__boxed_636_);
lean_dec_ref(v___x_631_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(lean_object* v___x_638_, lean_object* v_t_639_, lean_object* v_i_640_){
_start:
{
lean_object* v_root_641_; lean_object* v_tail_642_; lean_object* v_size_643_; size_t v_shift_644_; lean_object* v_tailOff_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_673_; 
v_root_641_ = lean_ctor_get(v_t_639_, 0);
v_tail_642_ = lean_ctor_get(v_t_639_, 1);
v_size_643_ = lean_ctor_get(v_t_639_, 2);
v_shift_644_ = lean_ctor_get_usize(v_t_639_, 4);
v_tailOff_645_ = lean_ctor_get(v_t_639_, 3);
v_isSharedCheck_673_ = !lean_is_exclusive(v_t_639_);
if (v_isSharedCheck_673_ == 0)
{
v___x_647_ = v_t_639_;
v_isShared_648_ = v_isSharedCheck_673_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_tailOff_645_);
lean_inc(v_size_643_);
lean_inc(v_tail_642_);
lean_inc(v_root_641_);
lean_dec(v_t_639_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_673_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
uint8_t v___x_649_; 
v___x_649_ = lean_nat_dec_le(v_tailOff_645_, v_i_640_);
if (v___x_649_ == 0)
{
size_t v___x_650_; lean_object* v___x_651_; lean_object* v___x_653_; 
v___x_650_ = lean_usize_of_nat(v_i_640_);
v___x_651_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4(v___x_638_, v_root_641_, v___x_650_, v_shift_644_);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 0, v___x_651_);
v___x_653_ = v___x_647_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v___x_651_);
lean_ctor_set(v_reuseFailAlloc_654_, 1, v_tail_642_);
lean_ctor_set(v_reuseFailAlloc_654_, 2, v_size_643_);
lean_ctor_set(v_reuseFailAlloc_654_, 3, v_tailOff_645_);
lean_ctor_set_usize(v_reuseFailAlloc_654_, 4, v_shift_644_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
else
{
lean_object* v___x_655_; lean_object* v___x_656_; uint8_t v___x_657_; 
v___x_655_ = lean_nat_sub(v_i_640_, v_tailOff_645_);
v___x_656_ = lean_array_get_size(v_tail_642_);
v___x_657_ = lean_nat_dec_lt(v___x_655_, v___x_656_);
if (v___x_657_ == 0)
{
lean_object* v___x_659_; 
lean_dec(v___x_655_);
if (v_isShared_648_ == 0)
{
v___x_659_ = v___x_647_;
goto v_reusejp_658_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_root_641_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v_tail_642_);
lean_ctor_set(v_reuseFailAlloc_660_, 2, v_size_643_);
lean_ctor_set(v_reuseFailAlloc_660_, 3, v_tailOff_645_);
lean_ctor_set_usize(v_reuseFailAlloc_660_, 4, v_shift_644_);
v___x_659_ = v_reuseFailAlloc_660_;
goto v_reusejp_658_;
}
v_reusejp_658_:
{
return v___x_659_;
}
}
else
{
lean_object* v_v_661_; lean_object* v___x_662_; lean_object* v_xs_x27_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_671_; 
v_v_661_ = lean_array_fget(v_tail_642_, v___x_655_);
v___x_662_ = lean_box(0);
v_xs_x27_663_ = lean_array_fset(v_tail_642_, v___x_655_, v___x_662_);
v___x_664_ = lean_unsigned_to_nat(32u);
v___x_665_ = lean_mk_empty_array_with_capacity(v___x_664_);
lean_dec_ref(v___x_665_);
v___x_666_ = lean_unsigned_to_nat(0u);
v___x_667_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1);
v___x_668_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(v___x_638_, v_v_661_, v___x_667_, v___x_666_);
lean_dec(v_v_661_);
v___x_669_ = lean_array_fset(v_xs_x27_663_, v___x_655_, v___x_668_);
lean_dec(v___x_655_);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 1, v___x_669_);
v___x_671_ = v___x_647_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_root_641_);
lean_ctor_set(v_reuseFailAlloc_672_, 1, v___x_669_);
lean_ctor_set(v_reuseFailAlloc_672_, 2, v_size_643_);
lean_ctor_set(v_reuseFailAlloc_672_, 3, v_tailOff_645_);
lean_ctor_set_usize(v_reuseFailAlloc_672_, 4, v_shift_644_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1___boxed(lean_object* v___x_674_, lean_object* v_t_675_, lean_object* v_i_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(v___x_674_, v_t_675_, v_i_676_);
lean_dec(v_i_676_);
lean_dec_ref(v___x_674_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0(lean_object* v_p_678_, lean_object* v_v_679_, lean_object* v_s_680_){
_start:
{
lean_object* v_vars_681_; lean_object* v_varMap_682_; lean_object* v_vars_x27_683_; lean_object* v_varMap_x27_684_; lean_object* v_natToIntMap_685_; lean_object* v_natDef_686_; lean_object* v_dvds_687_; lean_object* v_lowers_688_; lean_object* v_uppers_689_; lean_object* v_diseqs_690_; lean_object* v_elimEqs_691_; lean_object* v_elimStack_692_; lean_object* v_occurs_693_; lean_object* v_assignment_694_; lean_object* v_nextCnstrId_695_; uint8_t v_caseSplits_696_; lean_object* v_conflict_x3f_697_; lean_object* v_diseqSplits_698_; lean_object* v_divMod_699_; lean_object* v_toIntIds_700_; lean_object* v_toIntInfos_701_; lean_object* v_toIntTermMap_702_; lean_object* v_toIntVarMap_703_; uint8_t v_usedCommRing_704_; lean_object* v_nonlinearOccs_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_713_; 
v_vars_681_ = lean_ctor_get(v_s_680_, 0);
v_varMap_682_ = lean_ctor_get(v_s_680_, 1);
v_vars_x27_683_ = lean_ctor_get(v_s_680_, 2);
v_varMap_x27_684_ = lean_ctor_get(v_s_680_, 3);
v_natToIntMap_685_ = lean_ctor_get(v_s_680_, 4);
v_natDef_686_ = lean_ctor_get(v_s_680_, 5);
v_dvds_687_ = lean_ctor_get(v_s_680_, 6);
v_lowers_688_ = lean_ctor_get(v_s_680_, 7);
v_uppers_689_ = lean_ctor_get(v_s_680_, 8);
v_diseqs_690_ = lean_ctor_get(v_s_680_, 9);
v_elimEqs_691_ = lean_ctor_get(v_s_680_, 10);
v_elimStack_692_ = lean_ctor_get(v_s_680_, 11);
v_occurs_693_ = lean_ctor_get(v_s_680_, 12);
v_assignment_694_ = lean_ctor_get(v_s_680_, 13);
v_nextCnstrId_695_ = lean_ctor_get(v_s_680_, 14);
v_caseSplits_696_ = lean_ctor_get_uint8(v_s_680_, sizeof(void*)*23);
v_conflict_x3f_697_ = lean_ctor_get(v_s_680_, 15);
v_diseqSplits_698_ = lean_ctor_get(v_s_680_, 16);
v_divMod_699_ = lean_ctor_get(v_s_680_, 17);
v_toIntIds_700_ = lean_ctor_get(v_s_680_, 18);
v_toIntInfos_701_ = lean_ctor_get(v_s_680_, 19);
v_toIntTermMap_702_ = lean_ctor_get(v_s_680_, 20);
v_toIntVarMap_703_ = lean_ctor_get(v_s_680_, 21);
v_usedCommRing_704_ = lean_ctor_get_uint8(v_s_680_, sizeof(void*)*23 + 1);
v_nonlinearOccs_705_ = lean_ctor_get(v_s_680_, 22);
v_isSharedCheck_713_ = !lean_is_exclusive(v_s_680_);
if (v_isSharedCheck_713_ == 0)
{
v___x_707_ = v_s_680_;
v_isShared_708_ = v_isSharedCheck_713_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_nonlinearOccs_705_);
lean_inc(v_toIntVarMap_703_);
lean_inc(v_toIntTermMap_702_);
lean_inc(v_toIntInfos_701_);
lean_inc(v_toIntIds_700_);
lean_inc(v_divMod_699_);
lean_inc(v_diseqSplits_698_);
lean_inc(v_conflict_x3f_697_);
lean_inc(v_nextCnstrId_695_);
lean_inc(v_assignment_694_);
lean_inc(v_occurs_693_);
lean_inc(v_elimStack_692_);
lean_inc(v_elimEqs_691_);
lean_inc(v_diseqs_690_);
lean_inc(v_uppers_689_);
lean_inc(v_lowers_688_);
lean_inc(v_dvds_687_);
lean_inc(v_natDef_686_);
lean_inc(v_natToIntMap_685_);
lean_inc(v_varMap_x27_684_);
lean_inc(v_vars_x27_683_);
lean_inc(v_varMap_682_);
lean_inc(v_vars_681_);
lean_dec(v_s_680_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_713_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_709_; lean_object* v___x_711_; 
v___x_709_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(v_p_678_, v_uppers_689_, v_v_679_);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 8, v___x_709_);
v___x_711_ = v___x_707_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_vars_681_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v_varMap_682_);
lean_ctor_set(v_reuseFailAlloc_712_, 2, v_vars_x27_683_);
lean_ctor_set(v_reuseFailAlloc_712_, 3, v_varMap_x27_684_);
lean_ctor_set(v_reuseFailAlloc_712_, 4, v_natToIntMap_685_);
lean_ctor_set(v_reuseFailAlloc_712_, 5, v_natDef_686_);
lean_ctor_set(v_reuseFailAlloc_712_, 6, v_dvds_687_);
lean_ctor_set(v_reuseFailAlloc_712_, 7, v_lowers_688_);
lean_ctor_set(v_reuseFailAlloc_712_, 8, v___x_709_);
lean_ctor_set(v_reuseFailAlloc_712_, 9, v_diseqs_690_);
lean_ctor_set(v_reuseFailAlloc_712_, 10, v_elimEqs_691_);
lean_ctor_set(v_reuseFailAlloc_712_, 11, v_elimStack_692_);
lean_ctor_set(v_reuseFailAlloc_712_, 12, v_occurs_693_);
lean_ctor_set(v_reuseFailAlloc_712_, 13, v_assignment_694_);
lean_ctor_set(v_reuseFailAlloc_712_, 14, v_nextCnstrId_695_);
lean_ctor_set(v_reuseFailAlloc_712_, 15, v_conflict_x3f_697_);
lean_ctor_set(v_reuseFailAlloc_712_, 16, v_diseqSplits_698_);
lean_ctor_set(v_reuseFailAlloc_712_, 17, v_divMod_699_);
lean_ctor_set(v_reuseFailAlloc_712_, 18, v_toIntIds_700_);
lean_ctor_set(v_reuseFailAlloc_712_, 19, v_toIntInfos_701_);
lean_ctor_set(v_reuseFailAlloc_712_, 20, v_toIntTermMap_702_);
lean_ctor_set(v_reuseFailAlloc_712_, 21, v_toIntVarMap_703_);
lean_ctor_set(v_reuseFailAlloc_712_, 22, v_nonlinearOccs_705_);
lean_ctor_set_uint8(v_reuseFailAlloc_712_, sizeof(void*)*23, v_caseSplits_696_);
lean_ctor_set_uint8(v_reuseFailAlloc_712_, sizeof(void*)*23 + 1, v_usedCommRing_704_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___boxed(lean_object* v_p_714_, lean_object* v_v_715_, lean_object* v_s_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0(v_p_714_, v_v_715_, v_s_716_);
lean_dec(v_v_715_);
lean_dec_ref(v_p_714_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1(lean_object* v_p_718_, lean_object* v_v_719_, lean_object* v_s_720_){
_start:
{
lean_object* v_vars_721_; lean_object* v_varMap_722_; lean_object* v_vars_x27_723_; lean_object* v_varMap_x27_724_; lean_object* v_natToIntMap_725_; lean_object* v_natDef_726_; lean_object* v_dvds_727_; lean_object* v_lowers_728_; lean_object* v_uppers_729_; lean_object* v_diseqs_730_; lean_object* v_elimEqs_731_; lean_object* v_elimStack_732_; lean_object* v_occurs_733_; lean_object* v_assignment_734_; lean_object* v_nextCnstrId_735_; uint8_t v_caseSplits_736_; lean_object* v_conflict_x3f_737_; lean_object* v_diseqSplits_738_; lean_object* v_divMod_739_; lean_object* v_toIntIds_740_; lean_object* v_toIntInfos_741_; lean_object* v_toIntTermMap_742_; lean_object* v_toIntVarMap_743_; uint8_t v_usedCommRing_744_; lean_object* v_nonlinearOccs_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_753_; 
v_vars_721_ = lean_ctor_get(v_s_720_, 0);
v_varMap_722_ = lean_ctor_get(v_s_720_, 1);
v_vars_x27_723_ = lean_ctor_get(v_s_720_, 2);
v_varMap_x27_724_ = lean_ctor_get(v_s_720_, 3);
v_natToIntMap_725_ = lean_ctor_get(v_s_720_, 4);
v_natDef_726_ = lean_ctor_get(v_s_720_, 5);
v_dvds_727_ = lean_ctor_get(v_s_720_, 6);
v_lowers_728_ = lean_ctor_get(v_s_720_, 7);
v_uppers_729_ = lean_ctor_get(v_s_720_, 8);
v_diseqs_730_ = lean_ctor_get(v_s_720_, 9);
v_elimEqs_731_ = lean_ctor_get(v_s_720_, 10);
v_elimStack_732_ = lean_ctor_get(v_s_720_, 11);
v_occurs_733_ = lean_ctor_get(v_s_720_, 12);
v_assignment_734_ = lean_ctor_get(v_s_720_, 13);
v_nextCnstrId_735_ = lean_ctor_get(v_s_720_, 14);
v_caseSplits_736_ = lean_ctor_get_uint8(v_s_720_, sizeof(void*)*23);
v_conflict_x3f_737_ = lean_ctor_get(v_s_720_, 15);
v_diseqSplits_738_ = lean_ctor_get(v_s_720_, 16);
v_divMod_739_ = lean_ctor_get(v_s_720_, 17);
v_toIntIds_740_ = lean_ctor_get(v_s_720_, 18);
v_toIntInfos_741_ = lean_ctor_get(v_s_720_, 19);
v_toIntTermMap_742_ = lean_ctor_get(v_s_720_, 20);
v_toIntVarMap_743_ = lean_ctor_get(v_s_720_, 21);
v_usedCommRing_744_ = lean_ctor_get_uint8(v_s_720_, sizeof(void*)*23 + 1);
v_nonlinearOccs_745_ = lean_ctor_get(v_s_720_, 22);
v_isSharedCheck_753_ = !lean_is_exclusive(v_s_720_);
if (v_isSharedCheck_753_ == 0)
{
v___x_747_ = v_s_720_;
v_isShared_748_ = v_isSharedCheck_753_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_nonlinearOccs_745_);
lean_inc(v_toIntVarMap_743_);
lean_inc(v_toIntTermMap_742_);
lean_inc(v_toIntInfos_741_);
lean_inc(v_toIntIds_740_);
lean_inc(v_divMod_739_);
lean_inc(v_diseqSplits_738_);
lean_inc(v_conflict_x3f_737_);
lean_inc(v_nextCnstrId_735_);
lean_inc(v_assignment_734_);
lean_inc(v_occurs_733_);
lean_inc(v_elimStack_732_);
lean_inc(v_elimEqs_731_);
lean_inc(v_diseqs_730_);
lean_inc(v_uppers_729_);
lean_inc(v_lowers_728_);
lean_inc(v_dvds_727_);
lean_inc(v_natDef_726_);
lean_inc(v_natToIntMap_725_);
lean_inc(v_varMap_x27_724_);
lean_inc(v_vars_x27_723_);
lean_inc(v_varMap_722_);
lean_inc(v_vars_721_);
lean_dec(v_s_720_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_753_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_749_; lean_object* v___x_751_; 
v___x_749_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(v_p_718_, v_lowers_728_, v_v_719_);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 7, v___x_749_);
v___x_751_ = v___x_747_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_vars_721_);
lean_ctor_set(v_reuseFailAlloc_752_, 1, v_varMap_722_);
lean_ctor_set(v_reuseFailAlloc_752_, 2, v_vars_x27_723_);
lean_ctor_set(v_reuseFailAlloc_752_, 3, v_varMap_x27_724_);
lean_ctor_set(v_reuseFailAlloc_752_, 4, v_natToIntMap_725_);
lean_ctor_set(v_reuseFailAlloc_752_, 5, v_natDef_726_);
lean_ctor_set(v_reuseFailAlloc_752_, 6, v_dvds_727_);
lean_ctor_set(v_reuseFailAlloc_752_, 7, v___x_749_);
lean_ctor_set(v_reuseFailAlloc_752_, 8, v_uppers_729_);
lean_ctor_set(v_reuseFailAlloc_752_, 9, v_diseqs_730_);
lean_ctor_set(v_reuseFailAlloc_752_, 10, v_elimEqs_731_);
lean_ctor_set(v_reuseFailAlloc_752_, 11, v_elimStack_732_);
lean_ctor_set(v_reuseFailAlloc_752_, 12, v_occurs_733_);
lean_ctor_set(v_reuseFailAlloc_752_, 13, v_assignment_734_);
lean_ctor_set(v_reuseFailAlloc_752_, 14, v_nextCnstrId_735_);
lean_ctor_set(v_reuseFailAlloc_752_, 15, v_conflict_x3f_737_);
lean_ctor_set(v_reuseFailAlloc_752_, 16, v_diseqSplits_738_);
lean_ctor_set(v_reuseFailAlloc_752_, 17, v_divMod_739_);
lean_ctor_set(v_reuseFailAlloc_752_, 18, v_toIntIds_740_);
lean_ctor_set(v_reuseFailAlloc_752_, 19, v_toIntInfos_741_);
lean_ctor_set(v_reuseFailAlloc_752_, 20, v_toIntTermMap_742_);
lean_ctor_set(v_reuseFailAlloc_752_, 21, v_toIntVarMap_743_);
lean_ctor_set(v_reuseFailAlloc_752_, 22, v_nonlinearOccs_745_);
lean_ctor_set_uint8(v_reuseFailAlloc_752_, sizeof(void*)*23, v_caseSplits_736_);
lean_ctor_set_uint8(v_reuseFailAlloc_752_, sizeof(void*)*23 + 1, v_usedCommRing_744_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1___boxed(lean_object* v_p_754_, lean_object* v_v_755_, lean_object* v_s_756_){
_start:
{
lean_object* v_res_757_; 
v_res_757_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1(v_p_754_, v_v_755_, v_s_756_);
lean_dec(v_v_755_);
lean_dec_ref(v_p_754_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(lean_object* v_c_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_){
_start:
{
lean_object* v_p_765_; 
v_p_765_ = lean_ctor_get(v_c_758_, 0);
if (lean_obj_tag(v_p_765_) == 1)
{
lean_object* v_k_766_; lean_object* v_v_767_; lean_object* v___x_768_; uint8_t v___x_769_; 
lean_inc_ref(v_p_765_);
lean_dec_ref(v_c_758_);
v_k_766_ = lean_ctor_get(v_p_765_, 0);
v_v_767_ = lean_ctor_get(v_p_765_, 1);
lean_inc(v_v_767_);
v___x_768_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9);
v___x_769_ = lean_int_dec_lt(v_k_766_, v___x_768_);
if (v___x_769_ == 0)
{
lean_object* v___f_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v___f_770_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_770_, 0, v_p_765_);
lean_closure_set(v___f_770_, 1, v_v_767_);
v___x_771_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_772_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_771_, v___f_770_, v_a_759_);
return v___x_772_;
}
else
{
lean_object* v___f_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___f_773_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_773_, 0, v_p_765_);
lean_closure_set(v___f_773_, 1, v_v_767_);
v___x_774_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_775_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_774_, v___f_773_, v_a_759_);
return v___x_775_;
}
}
else
{
lean_object* v___x_776_; 
v___x_776_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_);
return v___x_776_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___boxed(lean_object* v_c_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_){
_start:
{
lean_object* v_res_784_; 
v_res_784_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_c_777_, v_a_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_);
lean_dec(v_a_782_);
lean_dec_ref(v_a_781_);
lean_dec(v_a_780_);
lean_dec_ref(v_a_779_);
lean_dec(v_a_778_);
return v_res_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase(lean_object* v_c_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_){
_start:
{
lean_object* v___x_797_; 
v___x_797_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_c_785_, v_a_786_, v_a_792_, v_a_793_, v_a_794_, v_a_795_);
return v___x_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___boxed(lean_object* v_c_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase(v_c_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_);
lean_dec(v_a_808_);
lean_dec_ref(v_a_807_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_a_804_);
lean_dec_ref(v_a_803_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
lean_dec(v_a_800_);
lean_dec(v_a_799_);
return v_res_810_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5(void){
_start:
{
lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_824_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_825_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_826_ = l_Lean_Name_append(v___x_825_, v___x_824_);
return v___x_826_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7(void){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_828_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__6));
v___x_829_ = l_Lean_stringToMessageData(v___x_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3(lean_object* v___x_830_, lean_object* v_c_831_, lean_object* v_as_832_, size_t v_sz_833_, size_t v_i_834_, lean_object* v_b_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
uint8_t v___x_847_; 
v___x_847_ = lean_usize_dec_lt(v_i_834_, v_sz_833_);
if (v___x_847_ == 0)
{
lean_object* v___x_848_; 
lean_dec_ref(v_c_831_);
lean_dec_ref(v___x_830_);
v___x_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_848_, 0, v_b_835_);
return v___x_848_;
}
else
{
lean_object* v_snd_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_935_; 
v_snd_849_ = lean_ctor_get(v_b_835_, 1);
v_isSharedCheck_935_ = !lean_is_exclusive(v_b_835_);
if (v_isSharedCheck_935_ == 0)
{
lean_object* v_unused_936_; 
v_unused_936_ = lean_ctor_get(v_b_835_, 0);
lean_dec(v_unused_936_);
v___x_851_ = v_b_835_;
v_isShared_852_ = v_isSharedCheck_935_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_snd_849_);
lean_dec(v_b_835_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_935_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v_a_853_; lean_object* v_p_854_; lean_object* v___x_855_; uint8_t v___x_856_; 
v_a_853_ = lean_array_uget_borrowed(v_as_832_, v_i_834_);
v_p_854_ = lean_ctor_get(v_a_853_, 0);
v___x_855_ = lean_box(0);
v___x_856_ = l_Int_Linear_Poly_isNegEq(v___x_830_, v_p_854_);
if (v___x_856_ == 0)
{
lean_object* v___x_857_; size_t v___x_858_; size_t v___x_859_; 
lean_del_object(v___x_851_);
lean_dec(v_snd_849_);
v___x_857_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__1));
v___x_858_ = ((size_t)1ULL);
v___x_859_ = lean_usize_add(v_i_834_, v___x_858_);
v_i_834_ = v___x_859_;
v_b_835_ = v___x_857_;
goto _start;
}
else
{
lean_object* v___x_861_; 
lean_inc(v_a_853_);
v___x_861_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_853_, v___y_836_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v_options_862_; lean_object* v_inheritedTraceOptions_863_; uint8_t v_hasTrace_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___y_868_; lean_object* v___y_869_; lean_object* v___y_870_; lean_object* v___y_871_; lean_object* v___y_872_; lean_object* v___y_873_; lean_object* v___y_874_; lean_object* v___y_875_; lean_object* v___y_876_; lean_object* v___y_877_; 
lean_dec_ref(v___x_861_);
v_options_862_ = lean_ctor_get(v___y_844_, 2);
v_inheritedTraceOptions_863_ = lean_ctor_get(v___y_844_, 13);
v_hasTrace_864_ = lean_ctor_get_uint8(v_options_862_, sizeof(void*)*1);
lean_inc(v_a_853_);
v___x_865_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_865_, 0, v_c_831_);
lean_ctor_set(v___x_865_, 1, v_a_853_);
v___x_866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_830_);
lean_ctor_set(v___x_866_, 1, v___x_865_);
if (v_hasTrace_864_ == 0)
{
v___y_868_ = v___y_836_;
v___y_869_ = v___y_837_;
v___y_870_ = v___y_838_;
v___y_871_ = v___y_839_;
v___y_872_ = v___y_840_;
v___y_873_ = v___y_841_;
v___y_874_ = v___y_842_;
v___y_875_ = v___y_843_;
v___y_876_ = v___y_844_;
v___y_877_ = v___y_845_;
goto v___jp_867_;
}
else
{
lean_object* v___x_903_; lean_object* v___x_904_; uint8_t v___x_905_; 
v___x_903_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_904_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5);
v___x_905_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_863_, v_options_862_, v___x_904_);
if (v___x_905_ == 0)
{
v___y_868_ = v___y_836_;
v___y_869_ = v___y_837_;
v___y_870_ = v___y_838_;
v___y_871_ = v___y_839_;
v___y_872_ = v___y_840_;
v___y_873_ = v___y_841_;
v___y_874_ = v___y_842_;
v___y_875_ = v___y_843_;
v___y_876_ = v___y_844_;
v___y_877_ = v___y_845_;
goto v___jp_867_;
}
else
{
lean_object* v___x_906_; 
lean_inc_ref(v___x_866_);
v___x_906_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_866_, v___y_836_, v___y_844_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_object* v_a_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; 
v_a_907_ = lean_ctor_get(v___x_906_, 0);
lean_inc(v_a_907_);
lean_dec_ref(v___x_906_);
v___x_908_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7);
v___x_909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_908_);
lean_ctor_set(v___x_909_, 1, v_a_907_);
v___x_910_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_903_, v___x_909_, v___y_842_, v___y_843_, v___y_844_, v___y_845_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_dec_ref(v___x_910_);
v___y_868_ = v___y_836_;
v___y_869_ = v___y_837_;
v___y_870_ = v___y_838_;
v___y_871_ = v___y_839_;
v___y_872_ = v___y_840_;
v___y_873_ = v___y_841_;
v___y_874_ = v___y_842_;
v___y_875_ = v___y_843_;
v___y_876_ = v___y_844_;
v___y_877_ = v___y_845_;
goto v___jp_867_;
}
else
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_918_; 
lean_dec_ref(v___x_866_);
lean_del_object(v___x_851_);
lean_dec(v_snd_849_);
v_a_911_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_918_ == 0)
{
v___x_913_ = v___x_910_;
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_910_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
if (v_isShared_914_ == 0)
{
v___x_916_ = v___x_913_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_a_911_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
else
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_926_; 
lean_dec_ref(v___x_866_);
lean_del_object(v___x_851_);
lean_dec(v_snd_849_);
v_a_919_ = lean_ctor_get(v___x_906_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_906_);
if (v_isSharedCheck_926_ == 0)
{
v___x_921_ = v___x_906_;
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_906_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_924_; 
if (v_isShared_922_ == 0)
{
v___x_924_ = v___x_921_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_a_919_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
}
}
v___jp_867_:
{
lean_object* v___x_878_; 
lean_inc(v___y_877_);
lean_inc_ref(v___y_876_);
lean_inc(v___y_875_);
lean_inc_ref(v___y_874_);
lean_inc(v___y_873_);
lean_inc_ref(v___y_872_);
lean_inc(v___y_871_);
lean_inc_ref(v___y_870_);
lean_inc(v___y_869_);
lean_inc(v___y_868_);
v___x_878_ = lean_grind_cutsat_assert_eq(v___x_866_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_893_; 
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_893_ == 0)
{
lean_object* v_unused_894_; 
v_unused_894_ = lean_ctor_get(v___x_878_, 0);
lean_dec(v_unused_894_);
v___x_880_ = v___x_878_;
v_isShared_881_ = v_isSharedCheck_893_;
goto v_resetjp_879_;
}
else
{
lean_dec(v___x_878_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_893_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_885_; 
v___x_882_ = lean_box(v___x_856_);
v___x_883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_883_, 0, v___x_882_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 1, v___x_855_);
lean_ctor_set(v___x_851_, 0, v___x_883_);
v___x_885_ = v___x_851_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_883_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v___x_855_);
v___x_885_ = v_reuseFailAlloc_892_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_890_; 
v___x_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_886_, 0, v___x_885_);
v___x_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_887_, 0, v___x_886_);
v___x_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_887_);
lean_ctor_set(v___x_888_, 1, v_snd_849_);
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 0, v___x_888_);
v___x_890_ = v___x_880_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_888_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
else
{
lean_object* v_a_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_902_; 
lean_del_object(v___x_851_);
lean_dec(v_snd_849_);
v_a_895_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_902_ == 0)
{
v___x_897_ = v___x_878_;
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_a_895_);
lean_dec(v___x_878_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_902_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_900_; 
if (v_isShared_898_ == 0)
{
v___x_900_ = v___x_897_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v_a_895_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
}
}
else
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_934_; 
lean_del_object(v___x_851_);
lean_dec(v_snd_849_);
lean_dec_ref(v_c_831_);
lean_dec_ref(v___x_830_);
v_a_927_ = lean_ctor_get(v___x_861_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_861_);
if (v_isSharedCheck_934_ == 0)
{
v___x_929_ = v___x_861_;
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_861_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_932_; 
if (v_isShared_930_ == 0)
{
v___x_932_ = v___x_929_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_a_927_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___boxed(lean_object** _args){
lean_object* v___x_937_ = _args[0];
lean_object* v_c_938_ = _args[1];
lean_object* v_as_939_ = _args[2];
lean_object* v_sz_940_ = _args[3];
lean_object* v_i_941_ = _args[4];
lean_object* v_b_942_ = _args[5];
lean_object* v___y_943_ = _args[6];
lean_object* v___y_944_ = _args[7];
lean_object* v___y_945_ = _args[8];
lean_object* v___y_946_ = _args[9];
lean_object* v___y_947_ = _args[10];
lean_object* v___y_948_ = _args[11];
lean_object* v___y_949_ = _args[12];
lean_object* v___y_950_ = _args[13];
lean_object* v___y_951_ = _args[14];
lean_object* v___y_952_ = _args[15];
lean_object* v___y_953_ = _args[16];
_start:
{
size_t v_sz_boxed_954_; size_t v_i_boxed_955_; lean_object* v_res_956_; 
v_sz_boxed_954_ = lean_unbox_usize(v_sz_940_);
lean_dec(v_sz_940_);
v_i_boxed_955_ = lean_unbox_usize(v_i_941_);
lean_dec(v_i_941_);
v_res_956_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3(v___x_937_, v_c_938_, v_as_939_, v_sz_boxed_954_, v_i_boxed_955_, v_b_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
lean_dec(v___y_946_);
lean_dec_ref(v___y_945_);
lean_dec(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v_as_939_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2(lean_object* v___x_963_, lean_object* v_c_964_, lean_object* v_as_965_, size_t v_sz_966_, size_t v_i_967_, lean_object* v_b_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
uint8_t v___x_980_; 
v___x_980_ = lean_usize_dec_lt(v_i_967_, v_sz_966_);
if (v___x_980_ == 0)
{
lean_object* v___x_981_; 
lean_dec_ref(v_c_964_);
lean_dec_ref(v___x_963_);
v___x_981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_981_, 0, v_b_968_);
return v___x_981_;
}
else
{
lean_object* v_snd_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_1068_; 
v_snd_982_ = lean_ctor_get(v_b_968_, 1);
v_isSharedCheck_1068_ = !lean_is_exclusive(v_b_968_);
if (v_isSharedCheck_1068_ == 0)
{
lean_object* v_unused_1069_; 
v_unused_1069_ = lean_ctor_get(v_b_968_, 0);
lean_dec(v_unused_1069_);
v___x_984_ = v_b_968_;
v_isShared_985_ = v_isSharedCheck_1068_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_snd_982_);
lean_dec(v_b_968_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_1068_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v_a_986_; lean_object* v_p_987_; lean_object* v___x_988_; uint8_t v___x_989_; 
v_a_986_ = lean_array_uget_borrowed(v_as_965_, v_i_967_);
v_p_987_ = lean_ctor_get(v_a_986_, 0);
v___x_988_ = lean_box(0);
v___x_989_ = l_Int_Linear_Poly_isNegEq(v___x_963_, v_p_987_);
if (v___x_989_ == 0)
{
lean_object* v___x_990_; size_t v___x_991_; size_t v___x_992_; lean_object* v___x_993_; 
lean_del_object(v___x_984_);
lean_dec(v_snd_982_);
v___x_990_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__1));
v___x_991_ = ((size_t)1ULL);
v___x_992_ = lean_usize_add(v_i_967_, v___x_991_);
v___x_993_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3(v___x_963_, v_c_964_, v_as_965_, v_sz_966_, v___x_992_, v___x_990_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_);
return v___x_993_;
}
else
{
lean_object* v___x_994_; 
lean_inc(v_a_986_);
v___x_994_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_986_, v___y_969_, v___y_975_, v___y_976_, v___y_977_, v___y_978_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v_options_995_; lean_object* v_inheritedTraceOptions_996_; uint8_t v_hasTrace_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___y_1001_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v___y_1006_; lean_object* v___y_1007_; lean_object* v___y_1008_; lean_object* v___y_1009_; lean_object* v___y_1010_; 
lean_dec_ref(v___x_994_);
v_options_995_ = lean_ctor_get(v___y_977_, 2);
v_inheritedTraceOptions_996_ = lean_ctor_get(v___y_977_, 13);
v_hasTrace_997_ = lean_ctor_get_uint8(v_options_995_, sizeof(void*)*1);
lean_inc(v_a_986_);
v___x_998_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_998_, 0, v_c_964_);
lean_ctor_set(v___x_998_, 1, v_a_986_);
v___x_999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_999_, 0, v___x_963_);
lean_ctor_set(v___x_999_, 1, v___x_998_);
if (v_hasTrace_997_ == 0)
{
v___y_1001_ = v___y_969_;
v___y_1002_ = v___y_970_;
v___y_1003_ = v___y_971_;
v___y_1004_ = v___y_972_;
v___y_1005_ = v___y_973_;
v___y_1006_ = v___y_974_;
v___y_1007_ = v___y_975_;
v___y_1008_ = v___y_976_;
v___y_1009_ = v___y_977_;
v___y_1010_ = v___y_978_;
goto v___jp_1000_;
}
else
{
lean_object* v___x_1036_; lean_object* v___x_1037_; uint8_t v___x_1038_; 
v___x_1036_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_1037_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5);
v___x_1038_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_996_, v_options_995_, v___x_1037_);
if (v___x_1038_ == 0)
{
v___y_1001_ = v___y_969_;
v___y_1002_ = v___y_970_;
v___y_1003_ = v___y_971_;
v___y_1004_ = v___y_972_;
v___y_1005_ = v___y_973_;
v___y_1006_ = v___y_974_;
v___y_1007_ = v___y_975_;
v___y_1008_ = v___y_976_;
v___y_1009_ = v___y_977_;
v___y_1010_ = v___y_978_;
goto v___jp_1000_;
}
else
{
lean_object* v___x_1039_; 
lean_inc_ref(v___x_999_);
v___x_1039_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_999_, v___y_969_, v___y_977_);
if (lean_obj_tag(v___x_1039_) == 0)
{
lean_object* v_a_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
v_a_1040_ = lean_ctor_get(v___x_1039_, 0);
lean_inc(v_a_1040_);
lean_dec_ref(v___x_1039_);
v___x_1041_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7);
v___x_1042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
lean_ctor_set(v___x_1042_, 1, v_a_1040_);
v___x_1043_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_1036_, v___x_1042_, v___y_975_, v___y_976_, v___y_977_, v___y_978_);
if (lean_obj_tag(v___x_1043_) == 0)
{
lean_dec_ref(v___x_1043_);
v___y_1001_ = v___y_969_;
v___y_1002_ = v___y_970_;
v___y_1003_ = v___y_971_;
v___y_1004_ = v___y_972_;
v___y_1005_ = v___y_973_;
v___y_1006_ = v___y_974_;
v___y_1007_ = v___y_975_;
v___y_1008_ = v___y_976_;
v___y_1009_ = v___y_977_;
v___y_1010_ = v___y_978_;
goto v___jp_1000_;
}
else
{
lean_object* v_a_1044_; lean_object* v___x_1046_; uint8_t v_isShared_1047_; uint8_t v_isSharedCheck_1051_; 
lean_dec_ref(v___x_999_);
lean_del_object(v___x_984_);
lean_dec(v_snd_982_);
v_a_1044_ = lean_ctor_get(v___x_1043_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v___x_1043_);
if (v_isSharedCheck_1051_ == 0)
{
v___x_1046_ = v___x_1043_;
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
else
{
lean_inc(v_a_1044_);
lean_dec(v___x_1043_);
v___x_1046_ = lean_box(0);
v_isShared_1047_ = v_isSharedCheck_1051_;
goto v_resetjp_1045_;
}
v_resetjp_1045_:
{
lean_object* v___x_1049_; 
if (v_isShared_1047_ == 0)
{
v___x_1049_ = v___x_1046_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_a_1044_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
}
else
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
lean_dec_ref(v___x_999_);
lean_del_object(v___x_984_);
lean_dec(v_snd_982_);
v_a_1052_ = lean_ctor_get(v___x_1039_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1039_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___x_1039_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1039_);
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
v___jp_1000_:
{
lean_object* v___x_1011_; 
lean_inc(v___y_1010_);
lean_inc_ref(v___y_1009_);
lean_inc(v___y_1008_);
lean_inc_ref(v___y_1007_);
lean_inc(v___y_1006_);
lean_inc_ref(v___y_1005_);
lean_inc(v___y_1004_);
lean_inc_ref(v___y_1003_);
lean_inc(v___y_1002_);
lean_inc(v___y_1001_);
v___x_1011_ = lean_grind_cutsat_assert_eq(v___x_999_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_);
if (lean_obj_tag(v___x_1011_) == 0)
{
lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1026_; 
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1026_ == 0)
{
lean_object* v_unused_1027_; 
v_unused_1027_ = lean_ctor_get(v___x_1011_, 0);
lean_dec(v_unused_1027_);
v___x_1013_ = v___x_1011_;
v_isShared_1014_ = v_isSharedCheck_1026_;
goto v_resetjp_1012_;
}
else
{
lean_dec(v___x_1011_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1026_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1018_; 
v___x_1015_ = lean_box(v___x_989_);
v___x_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 1, v___x_988_);
lean_ctor_set(v___x_984_, 0, v___x_1016_);
v___x_1018_ = v___x_984_;
goto v_reusejp_1017_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v___x_1016_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v___x_988_);
v___x_1018_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1017_;
}
v_reusejp_1017_:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1023_; 
v___x_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1018_);
v___x_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1020_, 0, v___x_1019_);
v___x_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1021_, 0, v___x_1020_);
lean_ctor_set(v___x_1021_, 1, v_snd_982_);
if (v_isShared_1014_ == 0)
{
lean_ctor_set(v___x_1013_, 0, v___x_1021_);
v___x_1023_ = v___x_1013_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v___x_1021_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
}
else
{
lean_object* v_a_1028_; lean_object* v___x_1030_; uint8_t v_isShared_1031_; uint8_t v_isSharedCheck_1035_; 
lean_del_object(v___x_984_);
lean_dec(v_snd_982_);
v_a_1028_ = lean_ctor_get(v___x_1011_, 0);
v_isSharedCheck_1035_ = !lean_is_exclusive(v___x_1011_);
if (v_isSharedCheck_1035_ == 0)
{
v___x_1030_ = v___x_1011_;
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
else
{
lean_inc(v_a_1028_);
lean_dec(v___x_1011_);
v___x_1030_ = lean_box(0);
v_isShared_1031_ = v_isSharedCheck_1035_;
goto v_resetjp_1029_;
}
v_resetjp_1029_:
{
lean_object* v___x_1033_; 
if (v_isShared_1031_ == 0)
{
v___x_1033_ = v___x_1030_;
goto v_reusejp_1032_;
}
else
{
lean_object* v_reuseFailAlloc_1034_; 
v_reuseFailAlloc_1034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1034_, 0, v_a_1028_);
v___x_1033_ = v_reuseFailAlloc_1034_;
goto v_reusejp_1032_;
}
v_reusejp_1032_:
{
return v___x_1033_;
}
}
}
}
}
else
{
lean_object* v_a_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1067_; 
lean_del_object(v___x_984_);
lean_dec(v_snd_982_);
lean_dec_ref(v_c_964_);
lean_dec_ref(v___x_963_);
v_a_1060_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1067_ == 0)
{
v___x_1062_ = v___x_994_;
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_a_1060_);
lean_dec(v___x_994_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1067_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___x_1065_; 
if (v_isShared_1063_ == 0)
{
v___x_1065_ = v___x_1062_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_a_1060_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___boxed(lean_object** _args){
lean_object* v___x_1070_ = _args[0];
lean_object* v_c_1071_ = _args[1];
lean_object* v_as_1072_ = _args[2];
lean_object* v_sz_1073_ = _args[3];
lean_object* v_i_1074_ = _args[4];
lean_object* v_b_1075_ = _args[5];
lean_object* v___y_1076_ = _args[6];
lean_object* v___y_1077_ = _args[7];
lean_object* v___y_1078_ = _args[8];
lean_object* v___y_1079_ = _args[9];
lean_object* v___y_1080_ = _args[10];
lean_object* v___y_1081_ = _args[11];
lean_object* v___y_1082_ = _args[12];
lean_object* v___y_1083_ = _args[13];
lean_object* v___y_1084_ = _args[14];
lean_object* v___y_1085_ = _args[15];
lean_object* v___y_1086_ = _args[16];
_start:
{
size_t v_sz_boxed_1087_; size_t v_i_boxed_1088_; lean_object* v_res_1089_; 
v_sz_boxed_1087_ = lean_unbox_usize(v_sz_1073_);
lean_dec(v_sz_1073_);
v_i_boxed_1088_ = lean_unbox_usize(v_i_1074_);
lean_dec(v_i_1074_);
v_res_1089_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2(v___x_1070_, v_c_1071_, v_as_1072_, v_sz_boxed_1087_, v_i_boxed_1088_, v_b_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v_as_1072_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(lean_object* v_init_1090_, lean_object* v___x_1091_, lean_object* v_c_1092_, lean_object* v_n_1093_, lean_object* v_b_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
if (lean_obj_tag(v_n_1093_) == 0)
{
lean_object* v_cs_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; size_t v_sz_1109_; size_t v___x_1110_; lean_object* v___x_1111_; 
v_cs_1106_ = lean_ctor_get(v_n_1093_, 0);
v___x_1107_ = lean_box(0);
v___x_1108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1107_);
lean_ctor_set(v___x_1108_, 1, v_b_1094_);
v_sz_1109_ = lean_array_size(v_cs_1106_);
v___x_1110_ = ((size_t)0ULL);
v___x_1111_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(v_init_1090_, v___x_1091_, v_c_1092_, v_cs_1106_, v_sz_1109_, v___x_1110_, v___x_1108_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1126_; 
v_a_1112_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1114_ = v___x_1111_;
v_isShared_1115_ = v_isSharedCheck_1126_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1111_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1126_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v_fst_1116_; 
v_fst_1116_ = lean_ctor_get(v_a_1112_, 0);
if (lean_obj_tag(v_fst_1116_) == 0)
{
lean_object* v_snd_1117_; lean_object* v___x_1118_; lean_object* v___x_1120_; 
v_snd_1117_ = lean_ctor_get(v_a_1112_, 1);
lean_inc(v_snd_1117_);
lean_dec(v_a_1112_);
v___x_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1118_, 0, v_snd_1117_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 0, v___x_1118_);
v___x_1120_ = v___x_1114_;
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
else
{
lean_object* v_val_1122_; lean_object* v___x_1124_; 
lean_inc_ref(v_fst_1116_);
lean_dec(v_a_1112_);
v_val_1122_ = lean_ctor_get(v_fst_1116_, 0);
lean_inc(v_val_1122_);
lean_dec_ref(v_fst_1116_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 0, v_val_1122_);
v___x_1124_ = v___x_1114_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_val_1122_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
}
else
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1134_; 
v_a_1127_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1129_ = v___x_1111_;
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1111_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
if (v_isShared_1130_ == 0)
{
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1127_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
return v___x_1132_;
}
}
}
}
else
{
lean_object* v_vs_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; size_t v_sz_1138_; size_t v___x_1139_; lean_object* v___x_1140_; 
v_vs_1135_ = lean_ctor_get(v_n_1093_, 0);
v___x_1136_ = lean_box(0);
v___x_1137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
lean_ctor_set(v___x_1137_, 1, v_b_1094_);
v_sz_1138_ = lean_array_size(v_vs_1135_);
v___x_1139_ = ((size_t)0ULL);
v___x_1140_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2(v___x_1091_, v_c_1092_, v_vs_1135_, v_sz_1138_, v___x_1139_, v___x_1137_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_, v___y_1101_, v___y_1102_, v___y_1103_, v___y_1104_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v_a_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1155_; 
v_a_1141_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1143_ = v___x_1140_;
v_isShared_1144_ = v_isSharedCheck_1155_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_a_1141_);
lean_dec(v___x_1140_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1155_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v_fst_1145_; 
v_fst_1145_ = lean_ctor_get(v_a_1141_, 0);
if (lean_obj_tag(v_fst_1145_) == 0)
{
lean_object* v_snd_1146_; lean_object* v___x_1147_; lean_object* v___x_1149_; 
v_snd_1146_ = lean_ctor_get(v_a_1141_, 1);
lean_inc(v_snd_1146_);
lean_dec(v_a_1141_);
v___x_1147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1147_, 0, v_snd_1146_);
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 0, v___x_1147_);
v___x_1149_ = v___x_1143_;
goto v_reusejp_1148_;
}
else
{
lean_object* v_reuseFailAlloc_1150_; 
v_reuseFailAlloc_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1150_, 0, v___x_1147_);
v___x_1149_ = v_reuseFailAlloc_1150_;
goto v_reusejp_1148_;
}
v_reusejp_1148_:
{
return v___x_1149_;
}
}
else
{
lean_object* v_val_1151_; lean_object* v___x_1153_; 
lean_inc_ref(v_fst_1145_);
lean_dec(v_a_1141_);
v_val_1151_ = lean_ctor_get(v_fst_1145_, 0);
lean_inc(v_val_1151_);
lean_dec_ref(v_fst_1145_);
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 0, v_val_1151_);
v___x_1153_ = v___x_1143_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_val_1151_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
}
}
else
{
lean_object* v_a_1156_; lean_object* v___x_1158_; uint8_t v_isShared_1159_; uint8_t v_isSharedCheck_1163_; 
v_a_1156_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1163_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1158_ = v___x_1140_;
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
else
{
lean_inc(v_a_1156_);
lean_dec(v___x_1140_);
v___x_1158_ = lean_box(0);
v_isShared_1159_ = v_isSharedCheck_1163_;
goto v_resetjp_1157_;
}
v_resetjp_1157_:
{
lean_object* v___x_1161_; 
if (v_isShared_1159_ == 0)
{
v___x_1161_ = v___x_1158_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1156_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(lean_object* v_init_1164_, lean_object* v___x_1165_, lean_object* v_c_1166_, lean_object* v_as_1167_, size_t v_sz_1168_, size_t v_i_1169_, lean_object* v_b_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_){
_start:
{
uint8_t v___x_1182_; 
v___x_1182_ = lean_usize_dec_lt(v_i_1169_, v_sz_1168_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1183_; 
lean_dec_ref(v_c_1166_);
lean_dec_ref(v___x_1165_);
v___x_1183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1183_, 0, v_b_1170_);
return v___x_1183_;
}
else
{
lean_object* v_snd_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1218_; 
v_snd_1184_ = lean_ctor_get(v_b_1170_, 1);
v_isSharedCheck_1218_ = !lean_is_exclusive(v_b_1170_);
if (v_isSharedCheck_1218_ == 0)
{
lean_object* v_unused_1219_; 
v_unused_1219_ = lean_ctor_get(v_b_1170_, 0);
lean_dec(v_unused_1219_);
v___x_1186_ = v_b_1170_;
v_isShared_1187_ = v_isSharedCheck_1218_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_snd_1184_);
lean_dec(v_b_1170_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1218_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v_a_1188_; lean_object* v___x_1189_; 
v_a_1188_ = lean_array_uget_borrowed(v_as_1167_, v_i_1169_);
lean_inc(v_snd_1184_);
lean_inc_ref(v_c_1166_);
lean_inc_ref(v___x_1165_);
v___x_1189_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(v_init_1164_, v___x_1165_, v_c_1166_, v_a_1188_, v_snd_1184_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_, v___y_1175_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
if (lean_obj_tag(v___x_1189_) == 0)
{
lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1209_; 
v_a_1190_ = lean_ctor_get(v___x_1189_, 0);
v_isSharedCheck_1209_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1209_ == 0)
{
v___x_1192_ = v___x_1189_;
v_isShared_1193_ = v_isSharedCheck_1209_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_dec(v___x_1189_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1209_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
if (lean_obj_tag(v_a_1190_) == 0)
{
lean_object* v___x_1194_; lean_object* v___x_1196_; 
lean_dec_ref(v_c_1166_);
lean_dec_ref(v___x_1165_);
v___x_1194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1194_, 0, v_a_1190_);
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 0, v___x_1194_);
v___x_1196_ = v___x_1186_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v___x_1194_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v_snd_1184_);
v___x_1196_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
lean_object* v___x_1198_; 
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 0, v___x_1196_);
v___x_1198_ = v___x_1192_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v___x_1196_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
else
{
lean_object* v_a_1201_; lean_object* v___x_1202_; lean_object* v___x_1204_; 
lean_del_object(v___x_1192_);
lean_dec(v_snd_1184_);
v_a_1201_ = lean_ctor_get(v_a_1190_, 0);
lean_inc(v_a_1201_);
lean_dec_ref(v_a_1190_);
v___x_1202_ = lean_box(0);
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 1, v_a_1201_);
lean_ctor_set(v___x_1186_, 0, v___x_1202_);
v___x_1204_ = v___x_1186_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v___x_1202_);
lean_ctor_set(v_reuseFailAlloc_1208_, 1, v_a_1201_);
v___x_1204_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
size_t v___x_1205_; size_t v___x_1206_; 
v___x_1205_ = ((size_t)1ULL);
v___x_1206_ = lean_usize_add(v_i_1169_, v___x_1205_);
v_i_1169_ = v___x_1206_;
v_b_1170_ = v___x_1204_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1217_; 
lean_del_object(v___x_1186_);
lean_dec(v_snd_1184_);
lean_dec_ref(v_c_1166_);
lean_dec_ref(v___x_1165_);
v_a_1210_ = lean_ctor_get(v___x_1189_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1212_ = v___x_1189_;
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1189_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_init_1220_ = _args[0];
lean_object* v___x_1221_ = _args[1];
lean_object* v_c_1222_ = _args[2];
lean_object* v_as_1223_ = _args[3];
lean_object* v_sz_1224_ = _args[4];
lean_object* v_i_1225_ = _args[5];
lean_object* v_b_1226_ = _args[6];
lean_object* v___y_1227_ = _args[7];
lean_object* v___y_1228_ = _args[8];
lean_object* v___y_1229_ = _args[9];
lean_object* v___y_1230_ = _args[10];
lean_object* v___y_1231_ = _args[11];
lean_object* v___y_1232_ = _args[12];
lean_object* v___y_1233_ = _args[13];
lean_object* v___y_1234_ = _args[14];
lean_object* v___y_1235_ = _args[15];
lean_object* v___y_1236_ = _args[16];
lean_object* v___y_1237_ = _args[17];
_start:
{
size_t v_sz_boxed_1238_; size_t v_i_boxed_1239_; lean_object* v_res_1240_; 
v_sz_boxed_1238_ = lean_unbox_usize(v_sz_1224_);
lean_dec(v_sz_1224_);
v_i_boxed_1239_ = lean_unbox_usize(v_i_1225_);
lean_dec(v_i_1225_);
v_res_1240_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(v_init_1220_, v___x_1221_, v_c_1222_, v_as_1223_, v_sz_boxed_1238_, v_i_boxed_1239_, v_b_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v_as_1223_);
lean_dec_ref(v_init_1220_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___boxed(lean_object* v_init_1241_, lean_object* v___x_1242_, lean_object* v_c_1243_, lean_object* v_n_1244_, lean_object* v_b_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(v_init_1241_, v___x_1242_, v_c_1243_, v_n_1244_, v_b_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec_ref(v___y_1250_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec_ref(v_n_1244_);
lean_dec_ref(v_init_1241_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4(lean_object* v___x_1264_, lean_object* v_c_1265_, lean_object* v_as_1266_, size_t v_sz_1267_, size_t v_i_1268_, lean_object* v_b_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_, lean_object* v___y_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
uint8_t v___x_1281_; 
v___x_1281_ = lean_usize_dec_lt(v_i_1268_, v_sz_1267_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; 
lean_dec_ref(v_c_1265_);
lean_dec_ref(v___x_1264_);
v___x_1282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1282_, 0, v_b_1269_);
return v___x_1282_;
}
else
{
lean_object* v_snd_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1368_; 
v_snd_1283_ = lean_ctor_get(v_b_1269_, 1);
v_isSharedCheck_1368_ = !lean_is_exclusive(v_b_1269_);
if (v_isSharedCheck_1368_ == 0)
{
lean_object* v_unused_1369_; 
v_unused_1369_ = lean_ctor_get(v_b_1269_, 0);
lean_dec(v_unused_1369_);
v___x_1285_ = v_b_1269_;
v_isShared_1286_ = v_isSharedCheck_1368_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_snd_1283_);
lean_dec(v_b_1269_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1368_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v_a_1287_; lean_object* v_p_1288_; lean_object* v___x_1289_; uint8_t v___x_1290_; 
v_a_1287_ = lean_array_uget_borrowed(v_as_1266_, v_i_1268_);
v_p_1288_ = lean_ctor_get(v_a_1287_, 0);
v___x_1289_ = lean_box(0);
v___x_1290_ = l_Int_Linear_Poly_isNegEq(v___x_1264_, v_p_1288_);
if (v___x_1290_ == 0)
{
lean_object* v___x_1291_; size_t v___x_1292_; size_t v___x_1293_; 
lean_del_object(v___x_1285_);
lean_dec(v_snd_1283_);
v___x_1291_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___closed__1));
v___x_1292_ = ((size_t)1ULL);
v___x_1293_ = lean_usize_add(v_i_1268_, v___x_1292_);
v_i_1268_ = v___x_1293_;
v_b_1269_ = v___x_1291_;
goto _start;
}
else
{
lean_object* v___x_1295_; 
lean_inc(v_a_1287_);
v___x_1295_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_1287_, v___y_1270_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
if (lean_obj_tag(v___x_1295_) == 0)
{
lean_object* v_options_1296_; lean_object* v_inheritedTraceOptions_1297_; uint8_t v_hasTrace_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___y_1302_; lean_object* v___y_1303_; lean_object* v___y_1304_; lean_object* v___y_1305_; lean_object* v___y_1306_; lean_object* v___y_1307_; lean_object* v___y_1308_; lean_object* v___y_1309_; lean_object* v___y_1310_; lean_object* v___y_1311_; 
lean_dec_ref(v___x_1295_);
v_options_1296_ = lean_ctor_get(v___y_1278_, 2);
v_inheritedTraceOptions_1297_ = lean_ctor_get(v___y_1278_, 13);
v_hasTrace_1298_ = lean_ctor_get_uint8(v_options_1296_, sizeof(void*)*1);
lean_inc(v_a_1287_);
v___x_1299_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1299_, 0, v_c_1265_);
lean_ctor_set(v___x_1299_, 1, v_a_1287_);
v___x_1300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1300_, 0, v___x_1264_);
lean_ctor_set(v___x_1300_, 1, v___x_1299_);
if (v_hasTrace_1298_ == 0)
{
v___y_1302_ = v___y_1270_;
v___y_1303_ = v___y_1271_;
v___y_1304_ = v___y_1272_;
v___y_1305_ = v___y_1273_;
v___y_1306_ = v___y_1274_;
v___y_1307_ = v___y_1275_;
v___y_1308_ = v___y_1276_;
v___y_1309_ = v___y_1277_;
v___y_1310_ = v___y_1278_;
v___y_1311_ = v___y_1279_;
goto v___jp_1301_;
}
else
{
lean_object* v___x_1336_; lean_object* v___x_1337_; uint8_t v___x_1338_; 
v___x_1336_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_1337_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5);
v___x_1338_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1297_, v_options_1296_, v___x_1337_);
if (v___x_1338_ == 0)
{
v___y_1302_ = v___y_1270_;
v___y_1303_ = v___y_1271_;
v___y_1304_ = v___y_1272_;
v___y_1305_ = v___y_1273_;
v___y_1306_ = v___y_1274_;
v___y_1307_ = v___y_1275_;
v___y_1308_ = v___y_1276_;
v___y_1309_ = v___y_1277_;
v___y_1310_ = v___y_1278_;
v___y_1311_ = v___y_1279_;
goto v___jp_1301_;
}
else
{
lean_object* v___x_1339_; 
lean_inc_ref(v___x_1300_);
v___x_1339_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_1300_, v___y_1270_, v___y_1278_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v_a_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v_a_1340_ = lean_ctor_get(v___x_1339_, 0);
lean_inc(v_a_1340_);
lean_dec_ref(v___x_1339_);
v___x_1341_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7);
v___x_1342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1341_);
lean_ctor_set(v___x_1342_, 1, v_a_1340_);
v___x_1343_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_1336_, v___x_1342_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_dec_ref(v___x_1343_);
v___y_1302_ = v___y_1270_;
v___y_1303_ = v___y_1271_;
v___y_1304_ = v___y_1272_;
v___y_1305_ = v___y_1273_;
v___y_1306_ = v___y_1274_;
v___y_1307_ = v___y_1275_;
v___y_1308_ = v___y_1276_;
v___y_1309_ = v___y_1277_;
v___y_1310_ = v___y_1278_;
v___y_1311_ = v___y_1279_;
goto v___jp_1301_;
}
else
{
lean_object* v_a_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1351_; 
lean_dec_ref(v___x_1300_);
lean_del_object(v___x_1285_);
lean_dec(v_snd_1283_);
v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1351_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1351_ == 0)
{
v___x_1346_ = v___x_1343_;
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_a_1344_);
lean_dec(v___x_1343_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1351_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1349_; 
if (v_isShared_1347_ == 0)
{
v___x_1349_ = v___x_1346_;
goto v_reusejp_1348_;
}
else
{
lean_object* v_reuseFailAlloc_1350_; 
v_reuseFailAlloc_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1350_, 0, v_a_1344_);
v___x_1349_ = v_reuseFailAlloc_1350_;
goto v_reusejp_1348_;
}
v_reusejp_1348_:
{
return v___x_1349_;
}
}
}
}
else
{
lean_object* v_a_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1359_; 
lean_dec_ref(v___x_1300_);
lean_del_object(v___x_1285_);
lean_dec(v_snd_1283_);
v_a_1352_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1354_ = v___x_1339_;
v_isShared_1355_ = v_isSharedCheck_1359_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_a_1352_);
lean_dec(v___x_1339_);
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
}
v___jp_1301_:
{
lean_object* v___x_1312_; 
lean_inc(v___y_1311_);
lean_inc_ref(v___y_1310_);
lean_inc(v___y_1309_);
lean_inc_ref(v___y_1308_);
lean_inc(v___y_1307_);
lean_inc_ref(v___y_1306_);
lean_inc(v___y_1305_);
lean_inc_ref(v___y_1304_);
lean_inc(v___y_1303_);
lean_inc(v___y_1302_);
v___x_1312_ = lean_grind_cutsat_assert_eq(v___x_1300_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1326_; 
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1326_ == 0)
{
lean_object* v_unused_1327_; 
v_unused_1327_ = lean_ctor_get(v___x_1312_, 0);
lean_dec(v_unused_1327_);
v___x_1314_ = v___x_1312_;
v_isShared_1315_ = v_isSharedCheck_1326_;
goto v_resetjp_1313_;
}
else
{
lean_dec(v___x_1312_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1326_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1319_; 
v___x_1316_ = lean_box(v___x_1290_);
v___x_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1316_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 1, v___x_1289_);
lean_ctor_set(v___x_1285_, 0, v___x_1317_);
v___x_1319_ = v___x_1285_;
goto v_reusejp_1318_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v___x_1317_);
lean_ctor_set(v_reuseFailAlloc_1325_, 1, v___x_1289_);
v___x_1319_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1318_;
}
v_reusejp_1318_:
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1323_; 
v___x_1320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
v___x_1321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1320_);
lean_ctor_set(v___x_1321_, 1, v_snd_1283_);
if (v_isShared_1315_ == 0)
{
lean_ctor_set(v___x_1314_, 0, v___x_1321_);
v___x_1323_ = v___x_1314_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v___x_1321_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
else
{
lean_object* v_a_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
lean_del_object(v___x_1285_);
lean_dec(v_snd_1283_);
v_a_1328_ = lean_ctor_get(v___x_1312_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1330_ = v___x_1312_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_inc(v_a_1328_);
lean_dec(v___x_1312_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_a_1328_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
lean_del_object(v___x_1285_);
lean_dec(v_snd_1283_);
lean_dec_ref(v_c_1265_);
lean_dec_ref(v___x_1264_);
v_a_1360_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___x_1295_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1295_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___boxed(lean_object** _args){
lean_object* v___x_1370_ = _args[0];
lean_object* v_c_1371_ = _args[1];
lean_object* v_as_1372_ = _args[2];
lean_object* v_sz_1373_ = _args[3];
lean_object* v_i_1374_ = _args[4];
lean_object* v_b_1375_ = _args[5];
lean_object* v___y_1376_ = _args[6];
lean_object* v___y_1377_ = _args[7];
lean_object* v___y_1378_ = _args[8];
lean_object* v___y_1379_ = _args[9];
lean_object* v___y_1380_ = _args[10];
lean_object* v___y_1381_ = _args[11];
lean_object* v___y_1382_ = _args[12];
lean_object* v___y_1383_ = _args[13];
lean_object* v___y_1384_ = _args[14];
lean_object* v___y_1385_ = _args[15];
lean_object* v___y_1386_ = _args[16];
_start:
{
size_t v_sz_boxed_1387_; size_t v_i_boxed_1388_; lean_object* v_res_1389_; 
v_sz_boxed_1387_ = lean_unbox_usize(v_sz_1373_);
lean_dec(v_sz_1373_);
v_i_boxed_1388_ = lean_unbox_usize(v_i_1374_);
lean_dec(v_i_1374_);
v_res_1389_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4(v___x_1370_, v_c_1371_, v_as_1372_, v_sz_boxed_1387_, v_i_boxed_1388_, v_b_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec(v___y_1377_);
lean_dec(v___y_1376_);
lean_dec_ref(v_as_1372_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1(lean_object* v___x_1393_, lean_object* v_c_1394_, lean_object* v_as_1395_, size_t v_sz_1396_, size_t v_i_1397_, lean_object* v_b_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
uint8_t v___x_1410_; 
v___x_1410_ = lean_usize_dec_lt(v_i_1397_, v_sz_1396_);
if (v___x_1410_ == 0)
{
lean_object* v___x_1411_; 
lean_dec_ref(v_c_1394_);
lean_dec_ref(v___x_1393_);
v___x_1411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1411_, 0, v_b_1398_);
return v___x_1411_;
}
else
{
lean_object* v_snd_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1497_; 
v_snd_1412_ = lean_ctor_get(v_b_1398_, 1);
v_isSharedCheck_1497_ = !lean_is_exclusive(v_b_1398_);
if (v_isSharedCheck_1497_ == 0)
{
lean_object* v_unused_1498_; 
v_unused_1498_ = lean_ctor_get(v_b_1398_, 0);
lean_dec(v_unused_1498_);
v___x_1414_ = v_b_1398_;
v_isShared_1415_ = v_isSharedCheck_1497_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_snd_1412_);
lean_dec(v_b_1398_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1497_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v_a_1416_; lean_object* v_p_1417_; lean_object* v___x_1418_; uint8_t v___x_1419_; 
v_a_1416_ = lean_array_uget_borrowed(v_as_1395_, v_i_1397_);
v_p_1417_ = lean_ctor_get(v_a_1416_, 0);
v___x_1418_ = lean_box(0);
v___x_1419_ = l_Int_Linear_Poly_isNegEq(v___x_1393_, v_p_1417_);
if (v___x_1419_ == 0)
{
lean_object* v___x_1420_; size_t v___x_1421_; size_t v___x_1422_; lean_object* v___x_1423_; 
lean_del_object(v___x_1414_);
lean_dec(v_snd_1412_);
v___x_1420_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1___closed__0));
v___x_1421_ = ((size_t)1ULL);
v___x_1422_ = lean_usize_add(v_i_1397_, v___x_1421_);
v___x_1423_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4(v___x_1393_, v_c_1394_, v_as_1395_, v_sz_1396_, v___x_1422_, v___x_1420_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
return v___x_1423_;
}
else
{
lean_object* v___x_1424_; 
lean_inc(v_a_1416_);
v___x_1424_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_1416_, v___y_1399_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v_options_1425_; lean_object* v_inheritedTraceOptions_1426_; uint8_t v_hasTrace_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___y_1431_; lean_object* v___y_1432_; lean_object* v___y_1433_; lean_object* v___y_1434_; lean_object* v___y_1435_; lean_object* v___y_1436_; lean_object* v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; 
lean_dec_ref(v___x_1424_);
v_options_1425_ = lean_ctor_get(v___y_1407_, 2);
v_inheritedTraceOptions_1426_ = lean_ctor_get(v___y_1407_, 13);
v_hasTrace_1427_ = lean_ctor_get_uint8(v_options_1425_, sizeof(void*)*1);
lean_inc(v_a_1416_);
v___x_1428_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1428_, 0, v_c_1394_);
lean_ctor_set(v___x_1428_, 1, v_a_1416_);
v___x_1429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1393_);
lean_ctor_set(v___x_1429_, 1, v___x_1428_);
if (v_hasTrace_1427_ == 0)
{
v___y_1431_ = v___y_1399_;
v___y_1432_ = v___y_1400_;
v___y_1433_ = v___y_1401_;
v___y_1434_ = v___y_1402_;
v___y_1435_ = v___y_1403_;
v___y_1436_ = v___y_1404_;
v___y_1437_ = v___y_1405_;
v___y_1438_ = v___y_1406_;
v___y_1439_ = v___y_1407_;
v___y_1440_ = v___y_1408_;
goto v___jp_1430_;
}
else
{
lean_object* v___x_1465_; lean_object* v___x_1466_; uint8_t v___x_1467_; 
v___x_1465_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_1466_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5);
v___x_1467_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1426_, v_options_1425_, v___x_1466_);
if (v___x_1467_ == 0)
{
v___y_1431_ = v___y_1399_;
v___y_1432_ = v___y_1400_;
v___y_1433_ = v___y_1401_;
v___y_1434_ = v___y_1402_;
v___y_1435_ = v___y_1403_;
v___y_1436_ = v___y_1404_;
v___y_1437_ = v___y_1405_;
v___y_1438_ = v___y_1406_;
v___y_1439_ = v___y_1407_;
v___y_1440_ = v___y_1408_;
goto v___jp_1430_;
}
else
{
lean_object* v___x_1468_; 
lean_inc_ref(v___x_1429_);
v___x_1468_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_1429_, v___y_1399_, v___y_1407_);
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_object* v_a_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v_a_1469_ = lean_ctor_get(v___x_1468_, 0);
lean_inc(v_a_1469_);
lean_dec_ref(v___x_1468_);
v___x_1470_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7);
v___x_1471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1471_, 0, v___x_1470_);
lean_ctor_set(v___x_1471_, 1, v_a_1469_);
v___x_1472_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_1465_, v___x_1471_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_dec_ref(v___x_1472_);
v___y_1431_ = v___y_1399_;
v___y_1432_ = v___y_1400_;
v___y_1433_ = v___y_1401_;
v___y_1434_ = v___y_1402_;
v___y_1435_ = v___y_1403_;
v___y_1436_ = v___y_1404_;
v___y_1437_ = v___y_1405_;
v___y_1438_ = v___y_1406_;
v___y_1439_ = v___y_1407_;
v___y_1440_ = v___y_1408_;
goto v___jp_1430_;
}
else
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
lean_dec_ref(v___x_1429_);
lean_del_object(v___x_1414_);
lean_dec(v_snd_1412_);
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1475_ = v___x_1472_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1472_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1473_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
else
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
lean_dec_ref(v___x_1429_);
lean_del_object(v___x_1414_);
lean_dec(v_snd_1412_);
v_a_1481_ = lean_ctor_get(v___x_1468_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___x_1468_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1468_);
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
}
v___jp_1430_:
{
lean_object* v___x_1441_; 
lean_inc(v___y_1440_);
lean_inc_ref(v___y_1439_);
lean_inc(v___y_1438_);
lean_inc_ref(v___y_1437_);
lean_inc(v___y_1436_);
lean_inc_ref(v___y_1435_);
lean_inc(v___y_1434_);
lean_inc_ref(v___y_1433_);
lean_inc(v___y_1432_);
lean_inc(v___y_1431_);
v___x_1441_ = lean_grind_cutsat_assert_eq(v___x_1429_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_);
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1455_; 
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1455_ == 0)
{
lean_object* v_unused_1456_; 
v_unused_1456_ = lean_ctor_get(v___x_1441_, 0);
lean_dec(v_unused_1456_);
v___x_1443_ = v___x_1441_;
v_isShared_1444_ = v_isSharedCheck_1455_;
goto v_resetjp_1442_;
}
else
{
lean_dec(v___x_1441_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1455_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1448_; 
v___x_1445_ = lean_box(v___x_1419_);
v___x_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1446_, 0, v___x_1445_);
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 1, v___x_1418_);
lean_ctor_set(v___x_1414_, 0, v___x_1446_);
v___x_1448_ = v___x_1414_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1446_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v___x_1418_);
v___x_1448_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1452_; 
v___x_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1448_);
v___x_1450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1450_, 0, v___x_1449_);
lean_ctor_set(v___x_1450_, 1, v_snd_1412_);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 0, v___x_1450_);
v___x_1452_ = v___x_1443_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1450_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
else
{
lean_object* v_a_1457_; lean_object* v___x_1459_; uint8_t v_isShared_1460_; uint8_t v_isSharedCheck_1464_; 
lean_del_object(v___x_1414_);
lean_dec(v_snd_1412_);
v_a_1457_ = lean_ctor_get(v___x_1441_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1441_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1459_ = v___x_1441_;
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
else
{
lean_inc(v_a_1457_);
lean_dec(v___x_1441_);
v___x_1459_ = lean_box(0);
v_isShared_1460_ = v_isSharedCheck_1464_;
goto v_resetjp_1458_;
}
v_resetjp_1458_:
{
lean_object* v___x_1462_; 
if (v_isShared_1460_ == 0)
{
v___x_1462_ = v___x_1459_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v_a_1457_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
}
}
else
{
lean_object* v_a_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1496_; 
lean_del_object(v___x_1414_);
lean_dec(v_snd_1412_);
lean_dec_ref(v_c_1394_);
lean_dec_ref(v___x_1393_);
v_a_1489_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1491_ = v___x_1424_;
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_a_1489_);
lean_dec(v___x_1424_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v___x_1499_ = _args[0];
lean_object* v_c_1500_ = _args[1];
lean_object* v_as_1501_ = _args[2];
lean_object* v_sz_1502_ = _args[3];
lean_object* v_i_1503_ = _args[4];
lean_object* v_b_1504_ = _args[5];
lean_object* v___y_1505_ = _args[6];
lean_object* v___y_1506_ = _args[7];
lean_object* v___y_1507_ = _args[8];
lean_object* v___y_1508_ = _args[9];
lean_object* v___y_1509_ = _args[10];
lean_object* v___y_1510_ = _args[11];
lean_object* v___y_1511_ = _args[12];
lean_object* v___y_1512_ = _args[13];
lean_object* v___y_1513_ = _args[14];
lean_object* v___y_1514_ = _args[15];
lean_object* v___y_1515_ = _args[16];
_start:
{
size_t v_sz_boxed_1516_; size_t v_i_boxed_1517_; lean_object* v_res_1518_; 
v_sz_boxed_1516_ = lean_unbox_usize(v_sz_1502_);
lean_dec(v_sz_1502_);
v_i_boxed_1517_ = lean_unbox_usize(v_i_1503_);
lean_dec(v_i_1503_);
v_res_1518_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1(v___x_1499_, v_c_1500_, v_as_1501_, v_sz_boxed_1516_, v_i_boxed_1517_, v_b_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
lean_dec(v___y_1506_);
lean_dec(v___y_1505_);
lean_dec_ref(v_as_1501_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0(lean_object* v___x_1519_, lean_object* v_c_1520_, lean_object* v_t_1521_, lean_object* v_init_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
lean_object* v_root_1534_; lean_object* v_tail_1535_; lean_object* v___x_1536_; 
v_root_1534_ = lean_ctor_get(v_t_1521_, 0);
v_tail_1535_ = lean_ctor_get(v_t_1521_, 1);
lean_inc_ref(v_c_1520_);
lean_inc_ref(v___x_1519_);
lean_inc_ref(v_init_1522_);
v___x_1536_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(v_init_1522_, v___x_1519_, v_c_1520_, v_root_1534_, v_init_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
lean_dec_ref(v_init_1522_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_a_1537_; lean_object* v___x_1539_; uint8_t v_isShared_1540_; uint8_t v_isSharedCheck_1573_; 
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1573_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1573_ == 0)
{
v___x_1539_ = v___x_1536_;
v_isShared_1540_ = v_isSharedCheck_1573_;
goto v_resetjp_1538_;
}
else
{
lean_inc(v_a_1537_);
lean_dec(v___x_1536_);
v___x_1539_ = lean_box(0);
v_isShared_1540_ = v_isSharedCheck_1573_;
goto v_resetjp_1538_;
}
v_resetjp_1538_:
{
if (lean_obj_tag(v_a_1537_) == 0)
{
lean_object* v_a_1541_; lean_object* v___x_1543_; 
lean_dec_ref(v_c_1520_);
lean_dec_ref(v___x_1519_);
v_a_1541_ = lean_ctor_get(v_a_1537_, 0);
lean_inc(v_a_1541_);
lean_dec_ref(v_a_1537_);
if (v_isShared_1540_ == 0)
{
lean_ctor_set(v___x_1539_, 0, v_a_1541_);
v___x_1543_ = v___x_1539_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1541_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
else
{
lean_object* v_a_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; size_t v_sz_1548_; size_t v___x_1549_; lean_object* v___x_1550_; 
lean_del_object(v___x_1539_);
v_a_1545_ = lean_ctor_get(v_a_1537_, 0);
lean_inc(v_a_1545_);
lean_dec_ref(v_a_1537_);
v___x_1546_ = lean_box(0);
v___x_1547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1546_);
lean_ctor_set(v___x_1547_, 1, v_a_1545_);
v_sz_1548_ = lean_array_size(v_tail_1535_);
v___x_1549_ = ((size_t)0ULL);
v___x_1550_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1(v___x_1519_, v_c_1520_, v_tail_1535_, v_sz_1548_, v___x_1549_, v___x_1547_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
if (lean_obj_tag(v___x_1550_) == 0)
{
lean_object* v_a_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1564_; 
v_a_1551_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1564_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1564_ == 0)
{
v___x_1553_ = v___x_1550_;
v_isShared_1554_ = v_isSharedCheck_1564_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_a_1551_);
lean_dec(v___x_1550_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1564_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v_fst_1555_; 
v_fst_1555_ = lean_ctor_get(v_a_1551_, 0);
if (lean_obj_tag(v_fst_1555_) == 0)
{
lean_object* v_snd_1556_; lean_object* v___x_1558_; 
v_snd_1556_ = lean_ctor_get(v_a_1551_, 1);
lean_inc(v_snd_1556_);
lean_dec(v_a_1551_);
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 0, v_snd_1556_);
v___x_1558_ = v___x_1553_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_snd_1556_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
else
{
lean_object* v_val_1560_; lean_object* v___x_1562_; 
lean_inc_ref(v_fst_1555_);
lean_dec(v_a_1551_);
v_val_1560_ = lean_ctor_get(v_fst_1555_, 0);
lean_inc(v_val_1560_);
lean_dec_ref(v_fst_1555_);
if (v_isShared_1554_ == 0)
{
lean_ctor_set(v___x_1553_, 0, v_val_1560_);
v___x_1562_ = v___x_1553_;
goto v_reusejp_1561_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v_val_1560_);
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
v_a_1565_ = lean_ctor_get(v___x_1550_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1550_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1567_ = v___x_1550_;
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_a_1565_);
lean_dec(v___x_1550_);
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
}
}
else
{
lean_object* v_a_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1581_; 
lean_dec_ref(v_c_1520_);
lean_dec_ref(v___x_1519_);
v_a_1574_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1581_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1581_ == 0)
{
v___x_1576_ = v___x_1536_;
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_a_1574_);
lean_dec(v___x_1536_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1581_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1579_; 
if (v_isShared_1577_ == 0)
{
v___x_1579_ = v___x_1576_;
goto v_reusejp_1578_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_a_1574_);
v___x_1579_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1578_;
}
v_reusejp_1578_:
{
return v___x_1579_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0___boxed(lean_object* v___x_1582_, lean_object* v_c_1583_, lean_object* v_t_1584_, lean_object* v_init_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_){
_start:
{
lean_object* v_res_1597_; 
v_res_1597_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0(v___x_1582_, v_c_1583_, v_t_1584_, v_init_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
lean_dec(v___y_1595_);
lean_dec_ref(v___y_1594_);
lean_dec(v___y_1593_);
lean_dec_ref(v___y_1592_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec(v___y_1586_);
lean_dec_ref(v_t_1584_);
return v_res_1597_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0(void){
_start:
{
lean_object* v___x_1598_; 
v___x_1598_ = l_Lean_instInhabitedPersistentArray_default(lean_box(0));
return v___x_1598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq(lean_object* v_c_1599_, lean_object* v_a_1600_, lean_object* v_a_1601_, lean_object* v_a_1602_, lean_object* v_a_1603_, lean_object* v_a_1604_, lean_object* v_a_1605_, lean_object* v_a_1606_, lean_object* v_a_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_){
_start:
{
lean_object* v_p_1611_; 
v_p_1611_ = lean_ctor_get(v_c_1599_, 0);
if (lean_obj_tag(v_p_1611_) == 1)
{
lean_object* v_k_1612_; lean_object* v_v_1613_; lean_object* v___x_1614_; 
lean_inc_ref(v_p_1611_);
v_k_1612_ = lean_ctor_get(v_p_1611_, 0);
v_v_1613_ = lean_ctor_get(v_p_1611_, 1);
v___x_1614_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1600_, v_a_1608_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v_a_1615_; lean_object* v___y_1617_; lean_object* v___x_1643_; uint8_t v___x_1644_; 
v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
lean_inc(v_a_1615_);
lean_dec_ref(v___x_1614_);
v___x_1643_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9);
v___x_1644_ = lean_int_dec_lt(v_k_1612_, v___x_1643_);
if (v___x_1644_ == 0)
{
lean_object* v_lowers_1645_; lean_object* v_size_1646_; lean_object* v___x_1647_; uint8_t v___x_1648_; 
v_lowers_1645_ = lean_ctor_get(v_a_1615_, 7);
lean_inc_ref(v_lowers_1645_);
lean_dec(v_a_1615_);
v_size_1646_ = lean_ctor_get(v_lowers_1645_, 2);
v___x_1647_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0);
v___x_1648_ = lean_nat_dec_lt(v_v_1613_, v_size_1646_);
if (v___x_1648_ == 0)
{
lean_object* v___x_1649_; 
lean_dec_ref(v_lowers_1645_);
v___x_1649_ = l_outOfBounds___redArg(v___x_1647_);
v___y_1617_ = v___x_1649_;
goto v___jp_1616_;
}
else
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1647_, v_lowers_1645_, v_v_1613_);
lean_dec_ref(v_lowers_1645_);
v___y_1617_ = v___x_1650_;
goto v___jp_1616_;
}
}
else
{
lean_object* v_uppers_1651_; lean_object* v_size_1652_; lean_object* v___x_1653_; uint8_t v___x_1654_; 
v_uppers_1651_ = lean_ctor_get(v_a_1615_, 8);
lean_inc_ref(v_uppers_1651_);
lean_dec(v_a_1615_);
v_size_1652_ = lean_ctor_get(v_uppers_1651_, 2);
v___x_1653_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0);
v___x_1654_ = lean_nat_dec_lt(v_v_1613_, v_size_1652_);
if (v___x_1654_ == 0)
{
lean_object* v___x_1655_; 
lean_dec_ref(v_uppers_1651_);
v___x_1655_ = l_outOfBounds___redArg(v___x_1653_);
v___y_1617_ = v___x_1655_;
goto v___jp_1616_;
}
else
{
lean_object* v___x_1656_; 
v___x_1656_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1653_, v_uppers_1651_, v_v_1613_);
lean_dec_ref(v_uppers_1651_);
v___y_1617_ = v___x_1656_;
goto v___jp_1616_;
}
}
v___jp_1616_:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1618_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__0));
v___x_1619_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0(v_p_1611_, v_c_1599_, v___y_1617_, v___x_1618_, v_a_1600_, v_a_1601_, v_a_1602_, v_a_1603_, v_a_1604_, v_a_1605_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_);
lean_dec_ref(v___y_1617_);
if (lean_obj_tag(v___x_1619_) == 0)
{
lean_object* v_a_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1634_; 
v_a_1620_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1622_ = v___x_1619_;
v_isShared_1623_ = v_isSharedCheck_1634_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_a_1620_);
lean_dec(v___x_1619_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1634_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
lean_object* v_fst_1624_; 
v_fst_1624_ = lean_ctor_get(v_a_1620_, 0);
lean_inc(v_fst_1624_);
lean_dec(v_a_1620_);
if (lean_obj_tag(v_fst_1624_) == 0)
{
uint8_t v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1628_; 
v___x_1625_ = 0;
v___x_1626_ = lean_box(v___x_1625_);
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 0, v___x_1626_);
v___x_1628_ = v___x_1622_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v___x_1626_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
else
{
lean_object* v_val_1630_; lean_object* v___x_1632_; 
v_val_1630_ = lean_ctor_get(v_fst_1624_, 0);
lean_inc(v_val_1630_);
lean_dec_ref(v_fst_1624_);
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 0, v_val_1630_);
v___x_1632_ = v___x_1622_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_val_1630_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
}
else
{
lean_object* v_a_1635_; lean_object* v___x_1637_; uint8_t v_isShared_1638_; uint8_t v_isSharedCheck_1642_; 
v_a_1635_ = lean_ctor_get(v___x_1619_, 0);
v_isSharedCheck_1642_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1637_ = v___x_1619_;
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
else
{
lean_inc(v_a_1635_);
lean_dec(v___x_1619_);
v___x_1637_ = lean_box(0);
v_isShared_1638_ = v_isSharedCheck_1642_;
goto v_resetjp_1636_;
}
v_resetjp_1636_:
{
lean_object* v___x_1640_; 
if (v_isShared_1638_ == 0)
{
v___x_1640_ = v___x_1637_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_a_1635_);
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
}
else
{
lean_object* v_a_1657_; lean_object* v___x_1659_; uint8_t v_isShared_1660_; uint8_t v_isSharedCheck_1664_; 
lean_dec_ref(v_p_1611_);
lean_dec_ref(v_c_1599_);
v_a_1657_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1664_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1659_ = v___x_1614_;
v_isShared_1660_ = v_isSharedCheck_1664_;
goto v_resetjp_1658_;
}
else
{
lean_inc(v_a_1657_);
lean_dec(v___x_1614_);
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
else
{
lean_object* v___x_1665_; 
v___x_1665_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_1599_, v_a_1600_, v_a_1606_, v_a_1607_, v_a_1608_, v_a_1609_);
return v___x_1665_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___boxed(lean_object* v_c_1666_, lean_object* v_a_1667_, lean_object* v_a_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_, lean_object* v_a_1676_, lean_object* v_a_1677_){
_start:
{
lean_object* v_res_1678_; 
v_res_1678_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq(v_c_1666_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_, v_a_1675_, v_a_1676_);
lean_dec(v_a_1676_);
lean_dec_ref(v_a_1675_);
lean_dec(v_a_1674_);
lean_dec_ref(v_a_1673_);
lean_dec(v_a_1672_);
lean_dec_ref(v_a_1671_);
lean_dec(v_a_1670_);
lean_dec_ref(v_a_1669_);
lean_dec(v_a_1668_);
lean_dec(v_a_1667_);
return v_res_1678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(lean_object* v___x_1679_, lean_object* v_as_1680_, size_t v_i_1681_, size_t v_stop_1682_, lean_object* v_b_1683_){
_start:
{
lean_object* v___y_1685_; uint8_t v___x_1689_; 
v___x_1689_ = lean_usize_dec_eq(v_i_1681_, v_stop_1682_);
if (v___x_1689_ == 0)
{
lean_object* v___x_1690_; lean_object* v_p_1691_; uint8_t v___x_1692_; 
v___x_1690_ = lean_array_uget_borrowed(v_as_1680_, v_i_1681_);
v_p_1691_ = lean_ctor_get(v___x_1690_, 0);
v___x_1692_ = l_Int_Linear_instBEqPoly_beq(v_p_1691_, v___x_1679_);
if (v___x_1692_ == 0)
{
lean_object* v___x_1693_; 
lean_inc(v___x_1690_);
v___x_1693_ = l_Lean_PersistentArray_push___redArg(v_b_1683_, v___x_1690_);
v___y_1685_ = v___x_1693_;
goto v___jp_1684_;
}
else
{
v___y_1685_ = v_b_1683_;
goto v___jp_1684_;
}
}
else
{
return v_b_1683_;
}
v___jp_1684_:
{
size_t v___x_1686_; size_t v___x_1687_; 
v___x_1686_ = ((size_t)1ULL);
v___x_1687_ = lean_usize_add(v_i_1681_, v___x_1686_);
v_i_1681_ = v___x_1687_;
v_b_1683_ = v___y_1685_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1___boxed(lean_object* v___x_1694_, lean_object* v_as_1695_, lean_object* v_i_1696_, lean_object* v_stop_1697_, lean_object* v_b_1698_){
_start:
{
size_t v_i_boxed_1699_; size_t v_stop_boxed_1700_; lean_object* v_res_1701_; 
v_i_boxed_1699_ = lean_unbox_usize(v_i_1696_);
lean_dec(v_i_1696_);
v_stop_boxed_1700_ = lean_unbox_usize(v_stop_1697_);
lean_dec(v_stop_1697_);
v_res_1701_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1694_, v_as_1695_, v_i_boxed_1699_, v_stop_boxed_1700_, v_b_1698_);
lean_dec_ref(v_as_1695_);
lean_dec_ref(v___x_1694_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(lean_object* v___x_1702_, lean_object* v_x_1703_, lean_object* v_x_1704_){
_start:
{
if (lean_obj_tag(v_x_1703_) == 0)
{
lean_object* v_cs_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; uint8_t v___x_1708_; 
v_cs_1705_ = lean_ctor_get(v_x_1703_, 0);
v___x_1706_ = lean_unsigned_to_nat(0u);
v___x_1707_ = lean_array_get_size(v_cs_1705_);
v___x_1708_ = lean_nat_dec_lt(v___x_1706_, v___x_1707_);
if (v___x_1708_ == 0)
{
return v_x_1704_;
}
else
{
uint8_t v___x_1709_; 
v___x_1709_ = lean_nat_dec_le(v___x_1707_, v___x_1707_);
if (v___x_1709_ == 0)
{
if (v___x_1708_ == 0)
{
return v_x_1704_;
}
else
{
size_t v___x_1710_; size_t v___x_1711_; lean_object* v___x_1712_; 
v___x_1710_ = ((size_t)0ULL);
v___x_1711_ = lean_usize_of_nat(v___x_1707_);
v___x_1712_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1702_, v_cs_1705_, v___x_1710_, v___x_1711_, v_x_1704_);
return v___x_1712_;
}
}
else
{
size_t v___x_1713_; size_t v___x_1714_; lean_object* v___x_1715_; 
v___x_1713_ = ((size_t)0ULL);
v___x_1714_ = lean_usize_of_nat(v___x_1707_);
v___x_1715_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1702_, v_cs_1705_, v___x_1713_, v___x_1714_, v_x_1704_);
return v___x_1715_;
}
}
}
else
{
lean_object* v_vs_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; uint8_t v___x_1719_; 
v_vs_1716_ = lean_ctor_get(v_x_1703_, 0);
v___x_1717_ = lean_unsigned_to_nat(0u);
v___x_1718_ = lean_array_get_size(v_vs_1716_);
v___x_1719_ = lean_nat_dec_lt(v___x_1717_, v___x_1718_);
if (v___x_1719_ == 0)
{
return v_x_1704_;
}
else
{
uint8_t v___x_1720_; 
v___x_1720_ = lean_nat_dec_le(v___x_1718_, v___x_1718_);
if (v___x_1720_ == 0)
{
if (v___x_1719_ == 0)
{
return v_x_1704_;
}
else
{
size_t v___x_1721_; size_t v___x_1722_; lean_object* v___x_1723_; 
v___x_1721_ = ((size_t)0ULL);
v___x_1722_ = lean_usize_of_nat(v___x_1718_);
v___x_1723_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1702_, v_vs_1716_, v___x_1721_, v___x_1722_, v_x_1704_);
return v___x_1723_;
}
}
else
{
size_t v___x_1724_; size_t v___x_1725_; lean_object* v___x_1726_; 
v___x_1724_ = ((size_t)0ULL);
v___x_1725_ = lean_usize_of_nat(v___x_1718_);
v___x_1726_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1702_, v_vs_1716_, v___x_1724_, v___x_1725_, v_x_1704_);
return v___x_1726_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(lean_object* v___x_1727_, lean_object* v_as_1728_, size_t v_i_1729_, size_t v_stop_1730_, lean_object* v_b_1731_){
_start:
{
uint8_t v___x_1732_; 
v___x_1732_ = lean_usize_dec_eq(v_i_1729_, v_stop_1730_);
if (v___x_1732_ == 0)
{
lean_object* v___x_1733_; lean_object* v___x_1734_; size_t v___x_1735_; size_t v___x_1736_; 
v___x_1733_ = lean_array_uget_borrowed(v_as_1728_, v_i_1729_);
v___x_1734_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(v___x_1727_, v___x_1733_, v_b_1731_);
v___x_1735_ = ((size_t)1ULL);
v___x_1736_ = lean_usize_add(v_i_1729_, v___x_1735_);
v_i_1729_ = v___x_1736_;
v_b_1731_ = v___x_1734_;
goto _start;
}
else
{
return v_b_1731_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v___x_1738_, lean_object* v_as_1739_, lean_object* v_i_1740_, lean_object* v_stop_1741_, lean_object* v_b_1742_){
_start:
{
size_t v_i_boxed_1743_; size_t v_stop_boxed_1744_; lean_object* v_res_1745_; 
v_i_boxed_1743_ = lean_unbox_usize(v_i_1740_);
lean_dec(v_i_1740_);
v_stop_boxed_1744_ = lean_unbox_usize(v_stop_1741_);
lean_dec(v_stop_1741_);
v_res_1745_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1738_, v_as_1739_, v_i_boxed_1743_, v_stop_boxed_1744_, v_b_1742_);
lean_dec_ref(v_as_1739_);
lean_dec_ref(v___x_1738_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2___boxed(lean_object* v___x_1746_, lean_object* v_x_1747_, lean_object* v_x_1748_){
_start:
{
lean_object* v_res_1749_; 
v_res_1749_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(v___x_1746_, v_x_1747_, v_x_1748_);
lean_dec_ref(v_x_1747_);
lean_dec_ref(v___x_1746_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(lean_object* v___x_1750_, lean_object* v_x_1751_, size_t v_x_1752_, size_t v_x_1753_, lean_object* v_x_1754_){
_start:
{
if (lean_obj_tag(v_x_1751_) == 0)
{
lean_object* v_cs_1755_; lean_object* v___x_1756_; size_t v___x_1757_; lean_object* v_j_1758_; lean_object* v___x_1759_; size_t v___x_1760_; size_t v___x_1761_; size_t v___x_1762_; size_t v___x_1763_; size_t v___x_1764_; size_t v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; uint8_t v___x_1770_; 
v_cs_1755_ = lean_ctor_get(v_x_1751_, 0);
v___x_1756_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0);
v___x_1757_ = lean_usize_shift_right(v_x_1752_, v_x_1753_);
v_j_1758_ = lean_usize_to_nat(v___x_1757_);
v___x_1759_ = lean_array_get_borrowed(v___x_1756_, v_cs_1755_, v_j_1758_);
v___x_1760_ = ((size_t)1ULL);
v___x_1761_ = lean_usize_shift_left(v___x_1760_, v_x_1753_);
v___x_1762_ = lean_usize_sub(v___x_1761_, v___x_1760_);
v___x_1763_ = lean_usize_land(v_x_1752_, v___x_1762_);
v___x_1764_ = ((size_t)5ULL);
v___x_1765_ = lean_usize_sub(v_x_1753_, v___x_1764_);
v___x_1766_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(v___x_1750_, v___x_1759_, v___x_1763_, v___x_1765_, v_x_1754_);
v___x_1767_ = lean_unsigned_to_nat(1u);
v___x_1768_ = lean_nat_add(v_j_1758_, v___x_1767_);
lean_dec(v_j_1758_);
v___x_1769_ = lean_array_get_size(v_cs_1755_);
v___x_1770_ = lean_nat_dec_lt(v___x_1768_, v___x_1769_);
if (v___x_1770_ == 0)
{
lean_dec(v___x_1768_);
return v___x_1766_;
}
else
{
uint8_t v___x_1771_; 
v___x_1771_ = lean_nat_dec_le(v___x_1769_, v___x_1769_);
if (v___x_1771_ == 0)
{
if (v___x_1770_ == 0)
{
lean_dec(v___x_1768_);
return v___x_1766_;
}
else
{
size_t v___x_1772_; size_t v___x_1773_; lean_object* v___x_1774_; 
v___x_1772_ = lean_usize_of_nat(v___x_1768_);
lean_dec(v___x_1768_);
v___x_1773_ = lean_usize_of_nat(v___x_1769_);
v___x_1774_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1750_, v_cs_1755_, v___x_1772_, v___x_1773_, v___x_1766_);
return v___x_1774_;
}
}
else
{
size_t v___x_1775_; size_t v___x_1776_; lean_object* v___x_1777_; 
v___x_1775_ = lean_usize_of_nat(v___x_1768_);
lean_dec(v___x_1768_);
v___x_1776_ = lean_usize_of_nat(v___x_1769_);
v___x_1777_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1750_, v_cs_1755_, v___x_1775_, v___x_1776_, v___x_1766_);
return v___x_1777_;
}
}
}
else
{
lean_object* v_vs_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; uint8_t v___x_1781_; 
v_vs_1778_ = lean_ctor_get(v_x_1751_, 0);
v___x_1779_ = lean_usize_to_nat(v_x_1752_);
v___x_1780_ = lean_array_get_size(v_vs_1778_);
v___x_1781_ = lean_nat_dec_lt(v___x_1779_, v___x_1780_);
if (v___x_1781_ == 0)
{
lean_dec(v___x_1779_);
return v_x_1754_;
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
return v_x_1754_;
}
else
{
size_t v___x_1783_; size_t v___x_1784_; lean_object* v___x_1785_; 
v___x_1783_ = lean_usize_of_nat(v___x_1779_);
lean_dec(v___x_1779_);
v___x_1784_ = lean_usize_of_nat(v___x_1780_);
v___x_1785_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1750_, v_vs_1778_, v___x_1783_, v___x_1784_, v_x_1754_);
return v___x_1785_;
}
}
else
{
size_t v___x_1786_; size_t v___x_1787_; lean_object* v___x_1788_; 
v___x_1786_ = lean_usize_of_nat(v___x_1779_);
lean_dec(v___x_1779_);
v___x_1787_ = lean_usize_of_nat(v___x_1780_);
v___x_1788_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1750_, v_vs_1778_, v___x_1786_, v___x_1787_, v_x_1754_);
return v___x_1788_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0___boxed(lean_object* v___x_1789_, lean_object* v_x_1790_, lean_object* v_x_1791_, lean_object* v_x_1792_, lean_object* v_x_1793_){
_start:
{
size_t v_x_21627__boxed_1794_; size_t v_x_21628__boxed_1795_; lean_object* v_res_1796_; 
v_x_21627__boxed_1794_ = lean_unbox_usize(v_x_1791_);
lean_dec(v_x_1791_);
v_x_21628__boxed_1795_ = lean_unbox_usize(v_x_1792_);
lean_dec(v_x_1792_);
v_res_1796_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(v___x_1789_, v_x_1790_, v_x_21627__boxed_1794_, v_x_21628__boxed_1795_, v_x_1793_);
lean_dec_ref(v_x_1790_);
lean_dec_ref(v___x_1789_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(lean_object* v___x_1797_, lean_object* v_t_1798_, lean_object* v_init_1799_, lean_object* v_start_1800_){
_start:
{
lean_object* v___x_1801_; uint8_t v___x_1802_; 
v___x_1801_ = lean_unsigned_to_nat(0u);
v___x_1802_ = lean_nat_dec_eq(v_start_1800_, v___x_1801_);
if (v___x_1802_ == 0)
{
lean_object* v_root_1803_; lean_object* v_tail_1804_; size_t v_shift_1805_; lean_object* v_tailOff_1806_; uint8_t v___x_1807_; 
v_root_1803_ = lean_ctor_get(v_t_1798_, 0);
v_tail_1804_ = lean_ctor_get(v_t_1798_, 1);
v_shift_1805_ = lean_ctor_get_usize(v_t_1798_, 4);
v_tailOff_1806_ = lean_ctor_get(v_t_1798_, 3);
v___x_1807_ = lean_nat_dec_le(v_tailOff_1806_, v_start_1800_);
if (v___x_1807_ == 0)
{
size_t v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; uint8_t v___x_1811_; 
v___x_1808_ = lean_usize_of_nat(v_start_1800_);
v___x_1809_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(v___x_1797_, v_root_1803_, v___x_1808_, v_shift_1805_, v_init_1799_);
v___x_1810_ = lean_array_get_size(v_tail_1804_);
v___x_1811_ = lean_nat_dec_lt(v___x_1801_, v___x_1810_);
if (v___x_1811_ == 0)
{
return v___x_1809_;
}
else
{
uint8_t v___x_1812_; 
v___x_1812_ = lean_nat_dec_le(v___x_1810_, v___x_1810_);
if (v___x_1812_ == 0)
{
if (v___x_1811_ == 0)
{
return v___x_1809_;
}
else
{
size_t v___x_1813_; size_t v___x_1814_; lean_object* v___x_1815_; 
v___x_1813_ = ((size_t)0ULL);
v___x_1814_ = lean_usize_of_nat(v___x_1810_);
v___x_1815_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1797_, v_tail_1804_, v___x_1813_, v___x_1814_, v___x_1809_);
return v___x_1815_;
}
}
else
{
size_t v___x_1816_; size_t v___x_1817_; lean_object* v___x_1818_; 
v___x_1816_ = ((size_t)0ULL);
v___x_1817_ = lean_usize_of_nat(v___x_1810_);
v___x_1818_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1797_, v_tail_1804_, v___x_1816_, v___x_1817_, v___x_1809_);
return v___x_1818_;
}
}
}
else
{
lean_object* v___x_1819_; lean_object* v___x_1820_; uint8_t v___x_1821_; 
v___x_1819_ = lean_nat_sub(v_start_1800_, v_tailOff_1806_);
v___x_1820_ = lean_array_get_size(v_tail_1804_);
v___x_1821_ = lean_nat_dec_lt(v___x_1819_, v___x_1820_);
if (v___x_1821_ == 0)
{
lean_dec(v___x_1819_);
return v_init_1799_;
}
else
{
uint8_t v___x_1822_; 
v___x_1822_ = lean_nat_dec_le(v___x_1820_, v___x_1820_);
if (v___x_1822_ == 0)
{
if (v___x_1821_ == 0)
{
lean_dec(v___x_1819_);
return v_init_1799_;
}
else
{
size_t v___x_1823_; size_t v___x_1824_; lean_object* v___x_1825_; 
v___x_1823_ = lean_usize_of_nat(v___x_1819_);
lean_dec(v___x_1819_);
v___x_1824_ = lean_usize_of_nat(v___x_1820_);
v___x_1825_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1797_, v_tail_1804_, v___x_1823_, v___x_1824_, v_init_1799_);
return v___x_1825_;
}
}
else
{
size_t v___x_1826_; size_t v___x_1827_; lean_object* v___x_1828_; 
v___x_1826_ = lean_usize_of_nat(v___x_1819_);
lean_dec(v___x_1819_);
v___x_1827_ = lean_usize_of_nat(v___x_1820_);
v___x_1828_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1797_, v_tail_1804_, v___x_1826_, v___x_1827_, v_init_1799_);
return v___x_1828_;
}
}
}
}
else
{
lean_object* v_root_1829_; lean_object* v_tail_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; uint8_t v___x_1833_; 
v_root_1829_ = lean_ctor_get(v_t_1798_, 0);
v_tail_1830_ = lean_ctor_get(v_t_1798_, 1);
v___x_1831_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(v___x_1797_, v_root_1829_, v_init_1799_);
v___x_1832_ = lean_array_get_size(v_tail_1830_);
v___x_1833_ = lean_nat_dec_lt(v___x_1801_, v___x_1832_);
if (v___x_1833_ == 0)
{
return v___x_1831_;
}
else
{
uint8_t v___x_1834_; 
v___x_1834_ = lean_nat_dec_le(v___x_1832_, v___x_1832_);
if (v___x_1834_ == 0)
{
if (v___x_1833_ == 0)
{
return v___x_1831_;
}
else
{
size_t v___x_1835_; size_t v___x_1836_; lean_object* v___x_1837_; 
v___x_1835_ = ((size_t)0ULL);
v___x_1836_ = lean_usize_of_nat(v___x_1832_);
v___x_1837_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1797_, v_tail_1830_, v___x_1835_, v___x_1836_, v___x_1831_);
return v___x_1837_;
}
}
else
{
size_t v___x_1838_; size_t v___x_1839_; lean_object* v___x_1840_; 
v___x_1838_ = ((size_t)0ULL);
v___x_1839_ = lean_usize_of_nat(v___x_1832_);
v___x_1840_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1797_, v_tail_1830_, v___x_1838_, v___x_1839_, v___x_1831_);
return v___x_1840_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0___boxed(lean_object* v___x_1841_, lean_object* v_t_1842_, lean_object* v_init_1843_, lean_object* v_start_1844_){
_start:
{
lean_object* v_res_1845_; 
v_res_1845_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(v___x_1841_, v_t_1842_, v_init_1843_, v_start_1844_);
lean_dec(v_start_1844_);
lean_dec_ref(v_t_1842_);
lean_dec_ref(v___x_1841_);
return v_res_1845_;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1846_ = lean_unsigned_to_nat(32u);
v___x_1847_ = lean_mk_empty_array_with_capacity(v___x_1846_);
v___x_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1847_);
return v___x_1848_;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1(void){
_start:
{
size_t v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1849_ = ((size_t)5ULL);
v___x_1850_ = lean_unsigned_to_nat(0u);
v___x_1851_ = lean_unsigned_to_nat(32u);
v___x_1852_ = lean_mk_empty_array_with_capacity(v___x_1851_);
v___x_1853_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0);
v___x_1854_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1854_, 0, v___x_1853_);
lean_ctor_set(v___x_1854_, 1, v___x_1852_);
lean_ctor_set(v___x_1854_, 2, v___x_1850_);
lean_ctor_set(v___x_1854_, 3, v___x_1850_);
lean_ctor_set_usize(v___x_1854_, 4, v___x_1849_);
return v___x_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(lean_object* v___x_1855_, lean_object* v_x_1856_, size_t v_x_1857_, size_t v_x_1858_){
_start:
{
if (lean_obj_tag(v_x_1856_) == 0)
{
lean_object* v_cs_1859_; size_t v_j_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; uint8_t v___x_1863_; 
v_cs_1859_ = lean_ctor_get(v_x_1856_, 0);
v_j_1860_ = lean_usize_shift_right(v_x_1857_, v_x_1858_);
v___x_1861_ = lean_usize_to_nat(v_j_1860_);
v___x_1862_ = lean_array_get_size(v_cs_1859_);
v___x_1863_ = lean_nat_dec_lt(v___x_1861_, v___x_1862_);
if (v___x_1863_ == 0)
{
lean_dec(v___x_1861_);
return v_x_1856_;
}
else
{
lean_object* v___x_1865_; uint8_t v_isShared_1866_; uint8_t v_isSharedCheck_1881_; 
lean_inc_ref(v_cs_1859_);
v_isSharedCheck_1881_ = !lean_is_exclusive(v_x_1856_);
if (v_isSharedCheck_1881_ == 0)
{
lean_object* v_unused_1882_; 
v_unused_1882_ = lean_ctor_get(v_x_1856_, 0);
lean_dec(v_unused_1882_);
v___x_1865_ = v_x_1856_;
v_isShared_1866_ = v_isSharedCheck_1881_;
goto v_resetjp_1864_;
}
else
{
lean_dec(v_x_1856_);
v___x_1865_ = lean_box(0);
v_isShared_1866_ = v_isSharedCheck_1881_;
goto v_resetjp_1864_;
}
v_resetjp_1864_:
{
size_t v___x_1867_; size_t v___x_1868_; size_t v___x_1869_; size_t v_i_1870_; size_t v___x_1871_; size_t v_shift_1872_; lean_object* v_v_1873_; lean_object* v___x_1874_; lean_object* v_xs_x27_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1879_; 
v___x_1867_ = ((size_t)1ULL);
v___x_1868_ = lean_usize_shift_left(v___x_1867_, v_x_1858_);
v___x_1869_ = lean_usize_sub(v___x_1868_, v___x_1867_);
v_i_1870_ = lean_usize_land(v_x_1857_, v___x_1869_);
v___x_1871_ = ((size_t)5ULL);
v_shift_1872_ = lean_usize_sub(v_x_1858_, v___x_1871_);
v_v_1873_ = lean_array_fget(v_cs_1859_, v___x_1861_);
v___x_1874_ = lean_box(0);
v_xs_x27_1875_ = lean_array_fset(v_cs_1859_, v___x_1861_, v___x_1874_);
v___x_1876_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(v___x_1855_, v_v_1873_, v_i_1870_, v_shift_1872_);
v___x_1877_ = lean_array_fset(v_xs_x27_1875_, v___x_1861_, v___x_1876_);
lean_dec(v___x_1861_);
if (v_isShared_1866_ == 0)
{
lean_ctor_set(v___x_1865_, 0, v___x_1877_);
v___x_1879_ = v___x_1865_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v___x_1877_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
}
else
{
lean_object* v_vs_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; uint8_t v___x_1886_; 
v_vs_1883_ = lean_ctor_get(v_x_1856_, 0);
v___x_1884_ = lean_usize_to_nat(v_x_1857_);
v___x_1885_ = lean_array_get_size(v_vs_1883_);
v___x_1886_ = lean_nat_dec_lt(v___x_1884_, v___x_1885_);
if (v___x_1886_ == 0)
{
lean_dec(v___x_1884_);
return v_x_1856_;
}
else
{
lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1900_; 
lean_inc_ref(v_vs_1883_);
v_isSharedCheck_1900_ = !lean_is_exclusive(v_x_1856_);
if (v_isSharedCheck_1900_ == 0)
{
lean_object* v_unused_1901_; 
v_unused_1901_ = lean_ctor_get(v_x_1856_, 0);
lean_dec(v_unused_1901_);
v___x_1888_ = v_x_1856_;
v_isShared_1889_ = v_isSharedCheck_1900_;
goto v_resetjp_1887_;
}
else
{
lean_dec(v_x_1856_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1900_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v_v_1890_; lean_object* v___x_1891_; lean_object* v_xs_x27_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1898_; 
v_v_1890_ = lean_array_fget(v_vs_1883_, v___x_1884_);
v___x_1891_ = lean_box(0);
v_xs_x27_1892_ = lean_array_fset(v_vs_1883_, v___x_1884_, v___x_1891_);
v___x_1893_ = lean_unsigned_to_nat(0u);
v___x_1894_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1);
v___x_1895_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(v___x_1855_, v_v_1890_, v___x_1894_, v___x_1893_);
lean_dec(v_v_1890_);
v___x_1896_ = lean_array_fset(v_xs_x27_1892_, v___x_1884_, v___x_1895_);
lean_dec(v___x_1884_);
if (v_isShared_1889_ == 0)
{
lean_ctor_set(v___x_1888_, 0, v___x_1896_);
v___x_1898_ = v___x_1888_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v___x_1896_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___boxed(lean_object* v___x_1902_, lean_object* v_x_1903_, lean_object* v_x_1904_, lean_object* v_x_1905_){
_start:
{
size_t v_x_21799__boxed_1906_; size_t v_x_21800__boxed_1907_; lean_object* v_res_1908_; 
v_x_21799__boxed_1906_ = lean_unbox_usize(v_x_1904_);
lean_dec(v_x_1904_);
v_x_21800__boxed_1907_ = lean_unbox_usize(v_x_1905_);
lean_dec(v_x_1905_);
v_res_1908_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(v___x_1902_, v_x_1903_, v_x_21799__boxed_1906_, v_x_21800__boxed_1907_);
lean_dec_ref(v___x_1902_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1(lean_object* v___x_1909_, lean_object* v_t_1910_, lean_object* v_i_1911_){
_start:
{
lean_object* v_root_1912_; lean_object* v_tail_1913_; lean_object* v_size_1914_; size_t v_shift_1915_; lean_object* v_tailOff_1916_; lean_object* v___x_1918_; uint8_t v_isShared_1919_; uint8_t v_isSharedCheck_1944_; 
v_root_1912_ = lean_ctor_get(v_t_1910_, 0);
v_tail_1913_ = lean_ctor_get(v_t_1910_, 1);
v_size_1914_ = lean_ctor_get(v_t_1910_, 2);
v_shift_1915_ = lean_ctor_get_usize(v_t_1910_, 4);
v_tailOff_1916_ = lean_ctor_get(v_t_1910_, 3);
v_isSharedCheck_1944_ = !lean_is_exclusive(v_t_1910_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1918_ = v_t_1910_;
v_isShared_1919_ = v_isSharedCheck_1944_;
goto v_resetjp_1917_;
}
else
{
lean_inc(v_tailOff_1916_);
lean_inc(v_size_1914_);
lean_inc(v_tail_1913_);
lean_inc(v_root_1912_);
lean_dec(v_t_1910_);
v___x_1918_ = lean_box(0);
v_isShared_1919_ = v_isSharedCheck_1944_;
goto v_resetjp_1917_;
}
v_resetjp_1917_:
{
uint8_t v___x_1920_; 
v___x_1920_ = lean_nat_dec_le(v_tailOff_1916_, v_i_1911_);
if (v___x_1920_ == 0)
{
size_t v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1924_; 
v___x_1921_ = lean_usize_of_nat(v_i_1911_);
v___x_1922_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(v___x_1909_, v_root_1912_, v___x_1921_, v_shift_1915_);
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 0, v___x_1922_);
v___x_1924_ = v___x_1918_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v___x_1922_);
lean_ctor_set(v_reuseFailAlloc_1925_, 1, v_tail_1913_);
lean_ctor_set(v_reuseFailAlloc_1925_, 2, v_size_1914_);
lean_ctor_set(v_reuseFailAlloc_1925_, 3, v_tailOff_1916_);
lean_ctor_set_usize(v_reuseFailAlloc_1925_, 4, v_shift_1915_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
else
{
lean_object* v___x_1926_; lean_object* v___x_1927_; uint8_t v___x_1928_; 
v___x_1926_ = lean_nat_sub(v_i_1911_, v_tailOff_1916_);
v___x_1927_ = lean_array_get_size(v_tail_1913_);
v___x_1928_ = lean_nat_dec_lt(v___x_1926_, v___x_1927_);
if (v___x_1928_ == 0)
{
lean_object* v___x_1930_; 
lean_dec(v___x_1926_);
if (v_isShared_1919_ == 0)
{
v___x_1930_ = v___x_1918_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_root_1912_);
lean_ctor_set(v_reuseFailAlloc_1931_, 1, v_tail_1913_);
lean_ctor_set(v_reuseFailAlloc_1931_, 2, v_size_1914_);
lean_ctor_set(v_reuseFailAlloc_1931_, 3, v_tailOff_1916_);
lean_ctor_set_usize(v_reuseFailAlloc_1931_, 4, v_shift_1915_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
else
{
lean_object* v_v_1932_; lean_object* v___x_1933_; lean_object* v_xs_x27_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1942_; 
v_v_1932_ = lean_array_fget(v_tail_1913_, v___x_1926_);
v___x_1933_ = lean_box(0);
v_xs_x27_1934_ = lean_array_fset(v_tail_1913_, v___x_1926_, v___x_1933_);
v___x_1935_ = lean_unsigned_to_nat(32u);
v___x_1936_ = lean_mk_empty_array_with_capacity(v___x_1935_);
lean_dec_ref(v___x_1936_);
v___x_1937_ = lean_unsigned_to_nat(0u);
v___x_1938_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1);
v___x_1939_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(v___x_1909_, v_v_1932_, v___x_1938_, v___x_1937_);
lean_dec(v_v_1932_);
v___x_1940_ = lean_array_fset(v_xs_x27_1934_, v___x_1926_, v___x_1939_);
lean_dec(v___x_1926_);
if (v_isShared_1919_ == 0)
{
lean_ctor_set(v___x_1918_, 1, v___x_1940_);
v___x_1942_ = v___x_1918_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_root_1912_);
lean_ctor_set(v_reuseFailAlloc_1943_, 1, v___x_1940_);
lean_ctor_set(v_reuseFailAlloc_1943_, 2, v_size_1914_);
lean_ctor_set(v_reuseFailAlloc_1943_, 3, v_tailOff_1916_);
lean_ctor_set_usize(v_reuseFailAlloc_1943_, 4, v_shift_1915_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1___boxed(lean_object* v___x_1945_, lean_object* v_t_1946_, lean_object* v_i_1947_){
_start:
{
lean_object* v_res_1948_; 
v_res_1948_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1(v___x_1945_, v_t_1946_, v_i_1947_);
lean_dec(v_i_1947_);
lean_dec_ref(v___x_1945_);
return v_res_1948_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0(lean_object* v_p_1949_, lean_object* v_x_1950_, lean_object* v_s_1951_){
_start:
{
lean_object* v_vars_1952_; lean_object* v_varMap_1953_; lean_object* v_vars_x27_1954_; lean_object* v_varMap_x27_1955_; lean_object* v_natToIntMap_1956_; lean_object* v_natDef_1957_; lean_object* v_dvds_1958_; lean_object* v_lowers_1959_; lean_object* v_uppers_1960_; lean_object* v_diseqs_1961_; lean_object* v_elimEqs_1962_; lean_object* v_elimStack_1963_; lean_object* v_occurs_1964_; lean_object* v_assignment_1965_; lean_object* v_nextCnstrId_1966_; uint8_t v_caseSplits_1967_; lean_object* v_conflict_x3f_1968_; lean_object* v_diseqSplits_1969_; lean_object* v_divMod_1970_; lean_object* v_toIntIds_1971_; lean_object* v_toIntInfos_1972_; lean_object* v_toIntTermMap_1973_; lean_object* v_toIntVarMap_1974_; uint8_t v_usedCommRing_1975_; lean_object* v_nonlinearOccs_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_1984_; 
v_vars_1952_ = lean_ctor_get(v_s_1951_, 0);
v_varMap_1953_ = lean_ctor_get(v_s_1951_, 1);
v_vars_x27_1954_ = lean_ctor_get(v_s_1951_, 2);
v_varMap_x27_1955_ = lean_ctor_get(v_s_1951_, 3);
v_natToIntMap_1956_ = lean_ctor_get(v_s_1951_, 4);
v_natDef_1957_ = lean_ctor_get(v_s_1951_, 5);
v_dvds_1958_ = lean_ctor_get(v_s_1951_, 6);
v_lowers_1959_ = lean_ctor_get(v_s_1951_, 7);
v_uppers_1960_ = lean_ctor_get(v_s_1951_, 8);
v_diseqs_1961_ = lean_ctor_get(v_s_1951_, 9);
v_elimEqs_1962_ = lean_ctor_get(v_s_1951_, 10);
v_elimStack_1963_ = lean_ctor_get(v_s_1951_, 11);
v_occurs_1964_ = lean_ctor_get(v_s_1951_, 12);
v_assignment_1965_ = lean_ctor_get(v_s_1951_, 13);
v_nextCnstrId_1966_ = lean_ctor_get(v_s_1951_, 14);
v_caseSplits_1967_ = lean_ctor_get_uint8(v_s_1951_, sizeof(void*)*23);
v_conflict_x3f_1968_ = lean_ctor_get(v_s_1951_, 15);
v_diseqSplits_1969_ = lean_ctor_get(v_s_1951_, 16);
v_divMod_1970_ = lean_ctor_get(v_s_1951_, 17);
v_toIntIds_1971_ = lean_ctor_get(v_s_1951_, 18);
v_toIntInfos_1972_ = lean_ctor_get(v_s_1951_, 19);
v_toIntTermMap_1973_ = lean_ctor_get(v_s_1951_, 20);
v_toIntVarMap_1974_ = lean_ctor_get(v_s_1951_, 21);
v_usedCommRing_1975_ = lean_ctor_get_uint8(v_s_1951_, sizeof(void*)*23 + 1);
v_nonlinearOccs_1976_ = lean_ctor_get(v_s_1951_, 22);
v_isSharedCheck_1984_ = !lean_is_exclusive(v_s_1951_);
if (v_isSharedCheck_1984_ == 0)
{
v___x_1978_ = v_s_1951_;
v_isShared_1979_ = v_isSharedCheck_1984_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_nonlinearOccs_1976_);
lean_inc(v_toIntVarMap_1974_);
lean_inc(v_toIntTermMap_1973_);
lean_inc(v_toIntInfos_1972_);
lean_inc(v_toIntIds_1971_);
lean_inc(v_divMod_1970_);
lean_inc(v_diseqSplits_1969_);
lean_inc(v_conflict_x3f_1968_);
lean_inc(v_nextCnstrId_1966_);
lean_inc(v_assignment_1965_);
lean_inc(v_occurs_1964_);
lean_inc(v_elimStack_1963_);
lean_inc(v_elimEqs_1962_);
lean_inc(v_diseqs_1961_);
lean_inc(v_uppers_1960_);
lean_inc(v_lowers_1959_);
lean_inc(v_dvds_1958_);
lean_inc(v_natDef_1957_);
lean_inc(v_natToIntMap_1956_);
lean_inc(v_varMap_x27_1955_);
lean_inc(v_vars_x27_1954_);
lean_inc(v_varMap_1953_);
lean_inc(v_vars_1952_);
lean_dec(v_s_1951_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_1984_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
lean_object* v___x_1980_; lean_object* v___x_1982_; 
v___x_1980_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1(v_p_1949_, v_diseqs_1961_, v_x_1950_);
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 9, v___x_1980_);
v___x_1982_ = v___x_1978_;
goto v_reusejp_1981_;
}
else
{
lean_object* v_reuseFailAlloc_1983_; 
v_reuseFailAlloc_1983_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_1983_, 0, v_vars_1952_);
lean_ctor_set(v_reuseFailAlloc_1983_, 1, v_varMap_1953_);
lean_ctor_set(v_reuseFailAlloc_1983_, 2, v_vars_x27_1954_);
lean_ctor_set(v_reuseFailAlloc_1983_, 3, v_varMap_x27_1955_);
lean_ctor_set(v_reuseFailAlloc_1983_, 4, v_natToIntMap_1956_);
lean_ctor_set(v_reuseFailAlloc_1983_, 5, v_natDef_1957_);
lean_ctor_set(v_reuseFailAlloc_1983_, 6, v_dvds_1958_);
lean_ctor_set(v_reuseFailAlloc_1983_, 7, v_lowers_1959_);
lean_ctor_set(v_reuseFailAlloc_1983_, 8, v_uppers_1960_);
lean_ctor_set(v_reuseFailAlloc_1983_, 9, v___x_1980_);
lean_ctor_set(v_reuseFailAlloc_1983_, 10, v_elimEqs_1962_);
lean_ctor_set(v_reuseFailAlloc_1983_, 11, v_elimStack_1963_);
lean_ctor_set(v_reuseFailAlloc_1983_, 12, v_occurs_1964_);
lean_ctor_set(v_reuseFailAlloc_1983_, 13, v_assignment_1965_);
lean_ctor_set(v_reuseFailAlloc_1983_, 14, v_nextCnstrId_1966_);
lean_ctor_set(v_reuseFailAlloc_1983_, 15, v_conflict_x3f_1968_);
lean_ctor_set(v_reuseFailAlloc_1983_, 16, v_diseqSplits_1969_);
lean_ctor_set(v_reuseFailAlloc_1983_, 17, v_divMod_1970_);
lean_ctor_set(v_reuseFailAlloc_1983_, 18, v_toIntIds_1971_);
lean_ctor_set(v_reuseFailAlloc_1983_, 19, v_toIntInfos_1972_);
lean_ctor_set(v_reuseFailAlloc_1983_, 20, v_toIntTermMap_1973_);
lean_ctor_set(v_reuseFailAlloc_1983_, 21, v_toIntVarMap_1974_);
lean_ctor_set(v_reuseFailAlloc_1983_, 22, v_nonlinearOccs_1976_);
lean_ctor_set_uint8(v_reuseFailAlloc_1983_, sizeof(void*)*23, v_caseSplits_1967_);
lean_ctor_set_uint8(v_reuseFailAlloc_1983_, sizeof(void*)*23 + 1, v_usedCommRing_1975_);
v___x_1982_ = v_reuseFailAlloc_1983_;
goto v_reusejp_1981_;
}
v_reusejp_1981_:
{
return v___x_1982_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed(lean_object* v_p_1985_, lean_object* v_x_1986_, lean_object* v_s_1987_){
_start:
{
lean_object* v_res_1988_; 
v_res_1988_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0(v_p_1985_, v_x_1986_, v_s_1987_);
lean_dec(v_x_1986_);
lean_dec_ref(v_p_1985_);
return v_res_1988_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1995_ = lean_unsigned_to_nat(1u);
v___x_1996_ = lean_nat_to_int(v___x_1995_);
return v___x_1996_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(lean_object* v_c_1997_, lean_object* v_x_1998_, lean_object* v_as_1999_, size_t v_sz_2000_, size_t v_i_2001_, lean_object* v_b_2002_, lean_object* v___y_2003_){
_start:
{
uint8_t v___x_2005_; 
v___x_2005_ = lean_usize_dec_lt(v_i_2001_, v_sz_2000_);
if (v___x_2005_ == 0)
{
lean_object* v___x_2006_; 
lean_dec(v_x_1998_);
lean_dec_ref(v_c_1997_);
v___x_2006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2006_, 0, v_b_2002_);
return v___x_2006_;
}
else
{
lean_object* v_snd_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2053_; 
v_snd_2007_ = lean_ctor_get(v_b_2002_, 1);
v_isSharedCheck_2053_ = !lean_is_exclusive(v_b_2002_);
if (v_isSharedCheck_2053_ == 0)
{
lean_object* v_unused_2054_; 
v_unused_2054_ = lean_ctor_get(v_b_2002_, 0);
lean_dec(v_unused_2054_);
v___x_2009_ = v_b_2002_;
v_isShared_2010_ = v_isSharedCheck_2053_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_snd_2007_);
lean_dec(v_b_2002_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2053_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v_p_2011_; lean_object* v_a_2012_; lean_object* v_p_2013_; lean_object* v___x_2014_; lean_object* v___f_2015_; uint8_t v___y_2017_; uint8_t v___x_2051_; 
v_p_2011_ = lean_ctor_get(v_c_1997_, 0);
v_a_2012_ = lean_array_uget_borrowed(v_as_1999_, v_i_2001_);
v_p_2013_ = lean_ctor_get(v_a_2012_, 0);
v___x_2014_ = lean_box(0);
lean_inc(v_x_1998_);
lean_inc_ref(v_p_2013_);
v___f_2015_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2015_, 0, v_p_2013_);
lean_closure_set(v___f_2015_, 1, v_x_1998_);
v___x_2051_ = l_Int_Linear_instBEqPoly_beq(v_p_2011_, v_p_2013_);
if (v___x_2051_ == 0)
{
uint8_t v___x_2052_; 
v___x_2052_ = l_Int_Linear_Poly_isNegEq(v_p_2011_, v_p_2013_);
v___y_2017_ = v___x_2052_;
goto v___jp_2016_;
}
else
{
v___y_2017_ = v___x_2051_;
goto v___jp_2016_;
}
v___jp_2016_:
{
if (v___y_2017_ == 0)
{
lean_object* v___x_2018_; size_t v___x_2019_; size_t v___x_2020_; 
lean_dec_ref(v___f_2015_);
lean_del_object(v___x_2009_);
lean_dec(v_snd_2007_);
v___x_2018_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__1));
v___x_2019_ = ((size_t)1ULL);
v___x_2020_ = lean_usize_add(v_i_2001_, v___x_2019_);
v_i_2001_ = v___x_2020_;
v_b_2002_ = v___x_2018_;
goto _start;
}
else
{
lean_object* v___x_2022_; lean_object* v___x_2023_; 
lean_dec(v_x_1998_);
v___x_2022_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2023_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2022_, v___f_2015_, v___y_2003_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2041_; 
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2041_ == 0)
{
lean_object* v_unused_2042_; 
v_unused_2042_ = lean_ctor_get(v___x_2023_, 0);
lean_dec(v_unused_2042_);
v___x_2025_ = v___x_2023_;
v_isShared_2026_ = v_isSharedCheck_2041_;
goto v_resetjp_2024_;
}
else
{
lean_dec(v___x_2023_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2041_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2034_; 
v___x_2027_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
lean_inc_ref(v_p_2011_);
v___x_2028_ = l_Int_Linear_Poly_addConst(v_p_2011_, v___x_2027_);
lean_inc(v_a_2012_);
v___x_2029_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_2029_, 0, v_c_1997_);
lean_ctor_set(v___x_2029_, 1, v_a_2012_);
v___x_2030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2028_);
lean_ctor_set(v___x_2030_, 1, v___x_2029_);
v___x_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2031_, 0, v___x_2030_);
v___x_2032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2031_);
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 1, v___x_2014_);
lean_ctor_set(v___x_2009_, 0, v___x_2032_);
v___x_2034_ = v___x_2009_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2032_);
lean_ctor_set(v_reuseFailAlloc_2040_, 1, v___x_2014_);
v___x_2034_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2038_; 
v___x_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2034_);
v___x_2036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2035_);
lean_ctor_set(v___x_2036_, 1, v_snd_2007_);
if (v_isShared_2026_ == 0)
{
lean_ctor_set(v___x_2025_, 0, v___x_2036_);
v___x_2038_ = v___x_2025_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v___x_2036_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
}
}
}
}
else
{
lean_object* v_a_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2050_; 
lean_del_object(v___x_2009_);
lean_dec(v_snd_2007_);
lean_dec_ref(v_c_1997_);
v_a_2043_ = lean_ctor_get(v___x_2023_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2023_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2045_ = v___x_2023_;
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_a_2043_);
lean_dec(v___x_2023_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2048_; 
if (v_isShared_2046_ == 0)
{
v___x_2048_ = v___x_2045_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_a_2043_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___boxed(lean_object* v_c_2055_, lean_object* v_x_2056_, lean_object* v_as_2057_, lean_object* v_sz_2058_, lean_object* v_i_2059_, lean_object* v_b_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_){
_start:
{
size_t v_sz_boxed_2063_; size_t v_i_boxed_2064_; lean_object* v_res_2065_; 
v_sz_boxed_2063_ = lean_unbox_usize(v_sz_2058_);
lean_dec(v_sz_2058_);
v_i_boxed_2064_ = lean_unbox_usize(v_i_2059_);
lean_dec(v_i_2059_);
v_res_2065_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(v_c_2055_, v_x_2056_, v_as_2057_, v_sz_boxed_2063_, v_i_boxed_2064_, v_b_2060_, v___y_2061_);
lean_dec(v___y_2061_);
lean_dec_ref(v_as_2057_);
return v_res_2065_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7(lean_object* v_c_2072_, lean_object* v_x_2073_, lean_object* v_as_2074_, size_t v_sz_2075_, size_t v_i_2076_, lean_object* v_b_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_){
_start:
{
uint8_t v___x_2089_; 
v___x_2089_ = lean_usize_dec_lt(v_i_2076_, v_sz_2075_);
if (v___x_2089_ == 0)
{
lean_object* v___x_2090_; 
lean_dec(v_x_2073_);
lean_dec_ref(v_c_2072_);
v___x_2090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2090_, 0, v_b_2077_);
return v___x_2090_;
}
else
{
lean_object* v_snd_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2137_; 
v_snd_2091_ = lean_ctor_get(v_b_2077_, 1);
v_isSharedCheck_2137_ = !lean_is_exclusive(v_b_2077_);
if (v_isSharedCheck_2137_ == 0)
{
lean_object* v_unused_2138_; 
v_unused_2138_ = lean_ctor_get(v_b_2077_, 0);
lean_dec(v_unused_2138_);
v___x_2093_ = v_b_2077_;
v_isShared_2094_ = v_isSharedCheck_2137_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_snd_2091_);
lean_dec(v_b_2077_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2137_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v_p_2095_; lean_object* v_a_2096_; lean_object* v_p_2097_; lean_object* v___x_2098_; lean_object* v___f_2099_; uint8_t v___y_2101_; uint8_t v___x_2135_; 
v_p_2095_ = lean_ctor_get(v_c_2072_, 0);
v_a_2096_ = lean_array_uget_borrowed(v_as_2074_, v_i_2076_);
v_p_2097_ = lean_ctor_get(v_a_2096_, 0);
v___x_2098_ = lean_box(0);
lean_inc(v_x_2073_);
lean_inc_ref(v_p_2097_);
v___f_2099_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2099_, 0, v_p_2097_);
lean_closure_set(v___f_2099_, 1, v_x_2073_);
v___x_2135_ = l_Int_Linear_instBEqPoly_beq(v_p_2095_, v_p_2097_);
if (v___x_2135_ == 0)
{
uint8_t v___x_2136_; 
v___x_2136_ = l_Int_Linear_Poly_isNegEq(v_p_2095_, v_p_2097_);
v___y_2101_ = v___x_2136_;
goto v___jp_2100_;
}
else
{
v___y_2101_ = v___x_2135_;
goto v___jp_2100_;
}
v___jp_2100_:
{
if (v___y_2101_ == 0)
{
lean_object* v___x_2102_; size_t v___x_2103_; size_t v___x_2104_; lean_object* v___x_2105_; 
lean_dec_ref(v___f_2099_);
lean_del_object(v___x_2093_);
lean_dec(v_snd_2091_);
v___x_2102_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___closed__1));
v___x_2103_ = ((size_t)1ULL);
v___x_2104_ = lean_usize_add(v_i_2076_, v___x_2103_);
v___x_2105_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(v_c_2072_, v_x_2073_, v_as_2074_, v_sz_2075_, v___x_2104_, v___x_2102_, v___y_2078_);
return v___x_2105_;
}
else
{
lean_object* v___x_2106_; lean_object* v___x_2107_; 
lean_dec(v_x_2073_);
v___x_2106_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2107_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2106_, v___f_2099_, v___y_2078_);
if (lean_obj_tag(v___x_2107_) == 0)
{
lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2125_; 
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2107_);
if (v_isSharedCheck_2125_ == 0)
{
lean_object* v_unused_2126_; 
v_unused_2126_ = lean_ctor_get(v___x_2107_, 0);
lean_dec(v_unused_2126_);
v___x_2109_ = v___x_2107_;
v_isShared_2110_ = v_isSharedCheck_2125_;
goto v_resetjp_2108_;
}
else
{
lean_dec(v___x_2107_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2125_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2118_; 
v___x_2111_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
lean_inc_ref(v_p_2095_);
v___x_2112_ = l_Int_Linear_Poly_addConst(v_p_2095_, v___x_2111_);
lean_inc(v_a_2096_);
v___x_2113_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_2113_, 0, v_c_2072_);
lean_ctor_set(v___x_2113_, 1, v_a_2096_);
v___x_2114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2112_);
lean_ctor_set(v___x_2114_, 1, v___x_2113_);
v___x_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
v___x_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2115_);
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 1, v___x_2098_);
lean_ctor_set(v___x_2093_, 0, v___x_2116_);
v___x_2118_ = v___x_2093_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v___x_2116_);
lean_ctor_set(v_reuseFailAlloc_2124_, 1, v___x_2098_);
v___x_2118_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2122_; 
v___x_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2118_);
v___x_2120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2119_);
lean_ctor_set(v___x_2120_, 1, v_snd_2091_);
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 0, v___x_2120_);
v___x_2122_ = v___x_2109_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v___x_2120_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
}
else
{
lean_object* v_a_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2134_; 
lean_del_object(v___x_2093_);
lean_dec(v_snd_2091_);
lean_dec_ref(v_c_2072_);
v_a_2127_ = lean_ctor_get(v___x_2107_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2107_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2129_ = v___x_2107_;
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_a_2127_);
lean_dec(v___x_2107_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2132_; 
if (v_isShared_2130_ == 0)
{
v___x_2132_ = v___x_2129_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_a_2127_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
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
lean_object* v_c_2139_ = _args[0];
lean_object* v_x_2140_ = _args[1];
lean_object* v_as_2141_ = _args[2];
lean_object* v_sz_2142_ = _args[3];
lean_object* v_i_2143_ = _args[4];
lean_object* v_b_2144_ = _args[5];
lean_object* v___y_2145_ = _args[6];
lean_object* v___y_2146_ = _args[7];
lean_object* v___y_2147_ = _args[8];
lean_object* v___y_2148_ = _args[9];
lean_object* v___y_2149_ = _args[10];
lean_object* v___y_2150_ = _args[11];
lean_object* v___y_2151_ = _args[12];
lean_object* v___y_2152_ = _args[13];
lean_object* v___y_2153_ = _args[14];
lean_object* v___y_2154_ = _args[15];
lean_object* v___y_2155_ = _args[16];
_start:
{
size_t v_sz_boxed_2156_; size_t v_i_boxed_2157_; lean_object* v_res_2158_; 
v_sz_boxed_2156_ = lean_unbox_usize(v_sz_2142_);
lean_dec(v_sz_2142_);
v_i_boxed_2157_ = lean_unbox_usize(v_i_2143_);
lean_dec(v_i_2143_);
v_res_2158_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7(v_c_2139_, v_x_2140_, v_as_2141_, v_sz_boxed_2156_, v_i_boxed_2157_, v_b_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
lean_dec(v___y_2154_);
lean_dec_ref(v___y_2153_);
lean_dec(v___y_2152_);
lean_dec_ref(v___y_2151_);
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
lean_dec(v___y_2146_);
lean_dec(v___y_2145_);
lean_dec_ref(v_as_2141_);
return v_res_2158_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(lean_object* v_c_2165_, lean_object* v_x_2166_, lean_object* v_as_2167_, size_t v_sz_2168_, size_t v_i_2169_, lean_object* v_b_2170_, lean_object* v___y_2171_){
_start:
{
uint8_t v___x_2173_; 
v___x_2173_ = lean_usize_dec_lt(v_i_2169_, v_sz_2168_);
if (v___x_2173_ == 0)
{
lean_object* v___x_2174_; 
lean_dec(v_x_2166_);
lean_dec_ref(v_c_2165_);
v___x_2174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2174_, 0, v_b_2170_);
return v___x_2174_;
}
else
{
lean_object* v_snd_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2222_; 
v_snd_2175_ = lean_ctor_get(v_b_2170_, 1);
v_isSharedCheck_2222_ = !lean_is_exclusive(v_b_2170_);
if (v_isSharedCheck_2222_ == 0)
{
lean_object* v_unused_2223_; 
v_unused_2223_ = lean_ctor_get(v_b_2170_, 0);
lean_dec(v_unused_2223_);
v___x_2177_ = v_b_2170_;
v_isShared_2178_ = v_isSharedCheck_2222_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_snd_2175_);
lean_dec(v_b_2170_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2222_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v_p_2179_; lean_object* v_a_2180_; lean_object* v_p_2181_; lean_object* v___x_2182_; lean_object* v___f_2183_; uint8_t v___y_2185_; uint8_t v___x_2220_; 
v_p_2179_ = lean_ctor_get(v_c_2165_, 0);
v_a_2180_ = lean_array_uget_borrowed(v_as_2167_, v_i_2169_);
v_p_2181_ = lean_ctor_get(v_a_2180_, 0);
v___x_2182_ = lean_box(0);
lean_inc(v_x_2166_);
lean_inc_ref(v_p_2181_);
v___f_2183_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2183_, 0, v_p_2181_);
lean_closure_set(v___f_2183_, 1, v_x_2166_);
v___x_2220_ = l_Int_Linear_instBEqPoly_beq(v_p_2179_, v_p_2181_);
if (v___x_2220_ == 0)
{
uint8_t v___x_2221_; 
v___x_2221_ = l_Int_Linear_Poly_isNegEq(v_p_2179_, v_p_2181_);
v___y_2185_ = v___x_2221_;
goto v___jp_2184_;
}
else
{
v___y_2185_ = v___x_2220_;
goto v___jp_2184_;
}
v___jp_2184_:
{
if (v___y_2185_ == 0)
{
lean_object* v___x_2186_; size_t v___x_2187_; size_t v___x_2188_; 
lean_dec_ref(v___f_2183_);
lean_del_object(v___x_2177_);
lean_dec(v_snd_2175_);
v___x_2186_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg___closed__1));
v___x_2187_ = ((size_t)1ULL);
v___x_2188_ = lean_usize_add(v_i_2169_, v___x_2187_);
v_i_2169_ = v___x_2188_;
v_b_2170_ = v___x_2186_;
goto _start;
}
else
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
lean_dec(v_x_2166_);
v___x_2190_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2191_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2190_, v___f_2183_, v___y_2171_);
if (lean_obj_tag(v___x_2191_) == 0)
{
lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2210_; 
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2210_ == 0)
{
lean_object* v_unused_2211_; 
v_unused_2211_ = lean_ctor_get(v___x_2191_, 0);
lean_dec(v_unused_2211_);
v___x_2193_ = v___x_2191_;
v_isShared_2194_ = v_isSharedCheck_2210_;
goto v_resetjp_2192_;
}
else
{
lean_dec(v___x_2191_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2210_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2202_; 
v___x_2195_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
lean_inc_ref(v_p_2179_);
v___x_2196_ = l_Int_Linear_Poly_addConst(v_p_2179_, v___x_2195_);
lean_inc(v_a_2180_);
v___x_2197_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_2197_, 0, v_c_2165_);
lean_ctor_set(v___x_2197_, 1, v_a_2180_);
v___x_2198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2198_, 0, v___x_2196_);
lean_ctor_set(v___x_2198_, 1, v___x_2197_);
v___x_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2198_);
v___x_2200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2199_);
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 1, v___x_2182_);
lean_ctor_set(v___x_2177_, 0, v___x_2200_);
v___x_2202_ = v___x_2177_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v___x_2200_);
lean_ctor_set(v_reuseFailAlloc_2209_, 1, v___x_2182_);
v___x_2202_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2207_; 
v___x_2203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2202_);
v___x_2204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2203_);
v___x_2205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2204_);
lean_ctor_set(v___x_2205_, 1, v_snd_2175_);
if (v_isShared_2194_ == 0)
{
lean_ctor_set(v___x_2193_, 0, v___x_2205_);
v___x_2207_ = v___x_2193_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v___x_2205_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
}
else
{
lean_object* v_a_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2219_; 
lean_del_object(v___x_2177_);
lean_dec(v_snd_2175_);
lean_dec_ref(v_c_2165_);
v_a_2212_ = lean_ctor_get(v___x_2191_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2191_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2214_ = v___x_2191_;
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_a_2212_);
lean_dec(v___x_2191_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2219_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2217_; 
if (v_isShared_2215_ == 0)
{
v___x_2217_ = v___x_2214_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_a_2212_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg___boxed(lean_object* v_c_2224_, lean_object* v_x_2225_, lean_object* v_as_2226_, lean_object* v_sz_2227_, lean_object* v_i_2228_, lean_object* v_b_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
size_t v_sz_boxed_2232_; size_t v_i_boxed_2233_; lean_object* v_res_2234_; 
v_sz_boxed_2232_ = lean_unbox_usize(v_sz_2227_);
lean_dec(v_sz_2227_);
v_i_boxed_2233_ = lean_unbox_usize(v_i_2228_);
lean_dec(v_i_2228_);
v_res_2234_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(v_c_2224_, v_x_2225_, v_as_2226_, v_sz_boxed_2232_, v_i_boxed_2233_, v_b_2229_, v___y_2230_);
lean_dec(v___y_2230_);
lean_dec_ref(v_as_2226_);
return v_res_2234_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9(lean_object* v_c_2238_, lean_object* v_x_2239_, lean_object* v_as_2240_, size_t v_sz_2241_, size_t v_i_2242_, lean_object* v_b_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_){
_start:
{
uint8_t v___x_2255_; 
v___x_2255_ = lean_usize_dec_lt(v_i_2242_, v_sz_2241_);
if (v___x_2255_ == 0)
{
lean_object* v___x_2256_; 
lean_dec(v_x_2239_);
lean_dec_ref(v_c_2238_);
v___x_2256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2256_, 0, v_b_2243_);
return v___x_2256_;
}
else
{
lean_object* v_snd_2257_; lean_object* v___x_2259_; uint8_t v_isShared_2260_; uint8_t v_isSharedCheck_2304_; 
v_snd_2257_ = lean_ctor_get(v_b_2243_, 1);
v_isSharedCheck_2304_ = !lean_is_exclusive(v_b_2243_);
if (v_isSharedCheck_2304_ == 0)
{
lean_object* v_unused_2305_; 
v_unused_2305_ = lean_ctor_get(v_b_2243_, 0);
lean_dec(v_unused_2305_);
v___x_2259_ = v_b_2243_;
v_isShared_2260_ = v_isSharedCheck_2304_;
goto v_resetjp_2258_;
}
else
{
lean_inc(v_snd_2257_);
lean_dec(v_b_2243_);
v___x_2259_ = lean_box(0);
v_isShared_2260_ = v_isSharedCheck_2304_;
goto v_resetjp_2258_;
}
v_resetjp_2258_:
{
lean_object* v_p_2261_; lean_object* v_a_2262_; lean_object* v_p_2263_; lean_object* v___x_2264_; lean_object* v___f_2265_; uint8_t v___y_2267_; uint8_t v___x_2302_; 
v_p_2261_ = lean_ctor_get(v_c_2238_, 0);
v_a_2262_ = lean_array_uget_borrowed(v_as_2240_, v_i_2242_);
v_p_2263_ = lean_ctor_get(v_a_2262_, 0);
v___x_2264_ = lean_box(0);
lean_inc(v_x_2239_);
lean_inc_ref(v_p_2263_);
v___f_2265_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2265_, 0, v_p_2263_);
lean_closure_set(v___f_2265_, 1, v_x_2239_);
v___x_2302_ = l_Int_Linear_instBEqPoly_beq(v_p_2261_, v_p_2263_);
if (v___x_2302_ == 0)
{
uint8_t v___x_2303_; 
v___x_2303_ = l_Int_Linear_Poly_isNegEq(v_p_2261_, v_p_2263_);
v___y_2267_ = v___x_2303_;
goto v___jp_2266_;
}
else
{
v___y_2267_ = v___x_2302_;
goto v___jp_2266_;
}
v___jp_2266_:
{
if (v___y_2267_ == 0)
{
lean_object* v___x_2268_; size_t v___x_2269_; size_t v___x_2270_; lean_object* v___x_2271_; 
lean_dec_ref(v___f_2265_);
lean_del_object(v___x_2259_);
lean_dec(v_snd_2257_);
v___x_2268_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9___closed__0));
v___x_2269_ = ((size_t)1ULL);
v___x_2270_ = lean_usize_add(v_i_2242_, v___x_2269_);
v___x_2271_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(v_c_2238_, v_x_2239_, v_as_2240_, v_sz_2241_, v___x_2270_, v___x_2268_, v___y_2244_);
return v___x_2271_;
}
else
{
lean_object* v___x_2272_; lean_object* v___x_2273_; 
lean_dec(v_x_2239_);
v___x_2272_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2273_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2272_, v___f_2265_, v___y_2244_);
if (lean_obj_tag(v___x_2273_) == 0)
{
lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2292_; 
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2273_);
if (v_isSharedCheck_2292_ == 0)
{
lean_object* v_unused_2293_; 
v_unused_2293_ = lean_ctor_get(v___x_2273_, 0);
lean_dec(v_unused_2293_);
v___x_2275_ = v___x_2273_;
v_isShared_2276_ = v_isSharedCheck_2292_;
goto v_resetjp_2274_;
}
else
{
lean_dec(v___x_2273_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2292_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2284_; 
v___x_2277_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
lean_inc_ref(v_p_2261_);
v___x_2278_ = l_Int_Linear_Poly_addConst(v_p_2261_, v___x_2277_);
lean_inc(v_a_2262_);
v___x_2279_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_2279_, 0, v_c_2238_);
lean_ctor_set(v___x_2279_, 1, v_a_2262_);
v___x_2280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2278_);
lean_ctor_set(v___x_2280_, 1, v___x_2279_);
v___x_2281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2280_);
v___x_2282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2281_);
if (v_isShared_2260_ == 0)
{
lean_ctor_set(v___x_2259_, 1, v___x_2264_);
lean_ctor_set(v___x_2259_, 0, v___x_2282_);
v___x_2284_ = v___x_2259_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v___x_2282_);
lean_ctor_set(v_reuseFailAlloc_2291_, 1, v___x_2264_);
v___x_2284_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2289_; 
v___x_2285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2285_, 0, v___x_2284_);
v___x_2286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2285_);
v___x_2287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2287_, 0, v___x_2286_);
lean_ctor_set(v___x_2287_, 1, v_snd_2257_);
if (v_isShared_2276_ == 0)
{
lean_ctor_set(v___x_2275_, 0, v___x_2287_);
v___x_2289_ = v___x_2275_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v___x_2287_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
}
else
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2301_; 
lean_del_object(v___x_2259_);
lean_dec(v_snd_2257_);
lean_dec_ref(v_c_2238_);
v_a_2294_ = lean_ctor_get(v___x_2273_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2273_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2296_ = v___x_2273_;
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2273_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2299_; 
if (v_isShared_2297_ == 0)
{
v___x_2299_ = v___x_2296_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_a_2294_);
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
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9___boxed(lean_object** _args){
lean_object* v_c_2306_ = _args[0];
lean_object* v_x_2307_ = _args[1];
lean_object* v_as_2308_ = _args[2];
lean_object* v_sz_2309_ = _args[3];
lean_object* v_i_2310_ = _args[4];
lean_object* v_b_2311_ = _args[5];
lean_object* v___y_2312_ = _args[6];
lean_object* v___y_2313_ = _args[7];
lean_object* v___y_2314_ = _args[8];
lean_object* v___y_2315_ = _args[9];
lean_object* v___y_2316_ = _args[10];
lean_object* v___y_2317_ = _args[11];
lean_object* v___y_2318_ = _args[12];
lean_object* v___y_2319_ = _args[13];
lean_object* v___y_2320_ = _args[14];
lean_object* v___y_2321_ = _args[15];
lean_object* v___y_2322_ = _args[16];
_start:
{
size_t v_sz_boxed_2323_; size_t v_i_boxed_2324_; lean_object* v_res_2325_; 
v_sz_boxed_2323_ = lean_unbox_usize(v_sz_2309_);
lean_dec(v_sz_2309_);
v_i_boxed_2324_ = lean_unbox_usize(v_i_2310_);
lean_dec(v_i_2310_);
v_res_2325_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9(v_c_2306_, v_x_2307_, v_as_2308_, v_sz_boxed_2323_, v_i_boxed_2324_, v_b_2311_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
lean_dec(v___y_2321_);
lean_dec_ref(v___y_2320_);
lean_dec(v___y_2319_);
lean_dec_ref(v___y_2318_);
lean_dec(v___y_2317_);
lean_dec_ref(v___y_2316_);
lean_dec(v___y_2315_);
lean_dec_ref(v___y_2314_);
lean_dec(v___y_2313_);
lean_dec(v___y_2312_);
lean_dec_ref(v_as_2308_);
return v_res_2325_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(lean_object* v_init_2326_, lean_object* v_c_2327_, lean_object* v_x_2328_, lean_object* v_n_2329_, lean_object* v_b_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
if (lean_obj_tag(v_n_2329_) == 0)
{
lean_object* v_cs_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; size_t v_sz_2345_; size_t v___x_2346_; lean_object* v___x_2347_; 
v_cs_2342_ = lean_ctor_get(v_n_2329_, 0);
v___x_2343_ = lean_box(0);
v___x_2344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2343_);
lean_ctor_set(v___x_2344_, 1, v_b_2330_);
v_sz_2345_ = lean_array_size(v_cs_2342_);
v___x_2346_ = ((size_t)0ULL);
v___x_2347_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8(v_init_2326_, v_c_2327_, v_x_2328_, v_cs_2342_, v_sz_2345_, v___x_2346_, v___x_2344_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2362_; 
v_a_2348_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2350_ = v___x_2347_;
v_isShared_2351_ = v_isSharedCheck_2362_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___x_2347_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2362_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v_fst_2352_; 
v_fst_2352_ = lean_ctor_get(v_a_2348_, 0);
if (lean_obj_tag(v_fst_2352_) == 0)
{
lean_object* v_snd_2353_; lean_object* v___x_2354_; lean_object* v___x_2356_; 
v_snd_2353_ = lean_ctor_get(v_a_2348_, 1);
lean_inc(v_snd_2353_);
lean_dec(v_a_2348_);
v___x_2354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2354_, 0, v_snd_2353_);
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 0, v___x_2354_);
v___x_2356_ = v___x_2350_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___x_2354_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
else
{
lean_object* v_val_2358_; lean_object* v___x_2360_; 
lean_inc_ref(v_fst_2352_);
lean_dec(v_a_2348_);
v_val_2358_ = lean_ctor_get(v_fst_2352_, 0);
lean_inc(v_val_2358_);
lean_dec_ref(v_fst_2352_);
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 0, v_val_2358_);
v___x_2360_ = v___x_2350_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_val_2358_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
}
else
{
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2370_; 
v_a_2363_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2365_ = v___x_2347_;
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2347_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2368_; 
if (v_isShared_2366_ == 0)
{
v___x_2368_ = v___x_2365_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_a_2363_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
}
else
{
lean_object* v_vs_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; size_t v_sz_2374_; size_t v___x_2375_; lean_object* v___x_2376_; 
v_vs_2371_ = lean_ctor_get(v_n_2329_, 0);
v___x_2372_ = lean_box(0);
v___x_2373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2372_);
lean_ctor_set(v___x_2373_, 1, v_b_2330_);
v_sz_2374_ = lean_array_size(v_vs_2371_);
v___x_2375_ = ((size_t)0ULL);
v___x_2376_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9(v_c_2327_, v_x_2328_, v_vs_2371_, v_sz_2374_, v___x_2375_, v___x_2373_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
if (lean_obj_tag(v___x_2376_) == 0)
{
lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2391_; 
v_a_2377_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2379_ = v___x_2376_;
v_isShared_2380_ = v_isSharedCheck_2391_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_dec(v___x_2376_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2391_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v_fst_2381_; 
v_fst_2381_ = lean_ctor_get(v_a_2377_, 0);
if (lean_obj_tag(v_fst_2381_) == 0)
{
lean_object* v_snd_2382_; lean_object* v___x_2383_; lean_object* v___x_2385_; 
v_snd_2382_ = lean_ctor_get(v_a_2377_, 1);
lean_inc(v_snd_2382_);
lean_dec(v_a_2377_);
v___x_2383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2383_, 0, v_snd_2382_);
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 0, v___x_2383_);
v___x_2385_ = v___x_2379_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v___x_2383_);
v___x_2385_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
return v___x_2385_;
}
}
else
{
lean_object* v_val_2387_; lean_object* v___x_2389_; 
lean_inc_ref(v_fst_2381_);
lean_dec(v_a_2377_);
v_val_2387_ = lean_ctor_get(v_fst_2381_, 0);
lean_inc(v_val_2387_);
lean_dec_ref(v_fst_2381_);
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 0, v_val_2387_);
v___x_2389_ = v___x_2379_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_val_2387_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
}
}
else
{
lean_object* v_a_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2399_; 
v_a_2392_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2394_ = v___x_2376_;
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_a_2392_);
lean_dec(v___x_2376_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v___x_2397_; 
if (v_isShared_2395_ == 0)
{
v___x_2397_ = v___x_2394_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_a_2392_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8(lean_object* v_init_2400_, lean_object* v_c_2401_, lean_object* v_x_2402_, lean_object* v_as_2403_, size_t v_sz_2404_, size_t v_i_2405_, lean_object* v_b_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_){
_start:
{
uint8_t v___x_2418_; 
v___x_2418_ = lean_usize_dec_lt(v_i_2405_, v_sz_2404_);
if (v___x_2418_ == 0)
{
lean_object* v___x_2419_; 
lean_dec(v_x_2402_);
lean_dec_ref(v_c_2401_);
v___x_2419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2419_, 0, v_b_2406_);
return v___x_2419_;
}
else
{
lean_object* v_snd_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2454_; 
v_snd_2420_ = lean_ctor_get(v_b_2406_, 1);
v_isSharedCheck_2454_ = !lean_is_exclusive(v_b_2406_);
if (v_isSharedCheck_2454_ == 0)
{
lean_object* v_unused_2455_; 
v_unused_2455_ = lean_ctor_get(v_b_2406_, 0);
lean_dec(v_unused_2455_);
v___x_2422_ = v_b_2406_;
v_isShared_2423_ = v_isSharedCheck_2454_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_snd_2420_);
lean_dec(v_b_2406_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2454_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v_a_2424_; lean_object* v___x_2425_; 
v_a_2424_ = lean_array_uget_borrowed(v_as_2403_, v_i_2405_);
lean_inc(v_snd_2420_);
lean_inc(v_x_2402_);
lean_inc_ref(v_c_2401_);
v___x_2425_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(v_init_2400_, v_c_2401_, v_x_2402_, v_a_2424_, v_snd_2420_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2445_; 
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2445_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2428_ = v___x_2425_;
v_isShared_2429_ = v_isSharedCheck_2445_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2425_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2445_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
if (lean_obj_tag(v_a_2426_) == 0)
{
lean_object* v___x_2430_; lean_object* v___x_2432_; 
lean_dec(v_x_2402_);
lean_dec_ref(v_c_2401_);
v___x_2430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2430_, 0, v_a_2426_);
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 0, v___x_2430_);
v___x_2432_ = v___x_2422_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v___x_2430_);
lean_ctor_set(v_reuseFailAlloc_2436_, 1, v_snd_2420_);
v___x_2432_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
lean_object* v___x_2434_; 
if (v_isShared_2429_ == 0)
{
lean_ctor_set(v___x_2428_, 0, v___x_2432_);
v___x_2434_ = v___x_2428_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v___x_2432_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
}
else
{
lean_object* v_a_2437_; lean_object* v___x_2438_; lean_object* v___x_2440_; 
lean_del_object(v___x_2428_);
lean_dec(v_snd_2420_);
v_a_2437_ = lean_ctor_get(v_a_2426_, 0);
lean_inc(v_a_2437_);
lean_dec_ref(v_a_2426_);
v___x_2438_ = lean_box(0);
if (v_isShared_2423_ == 0)
{
lean_ctor_set(v___x_2422_, 1, v_a_2437_);
lean_ctor_set(v___x_2422_, 0, v___x_2438_);
v___x_2440_ = v___x_2422_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v___x_2438_);
lean_ctor_set(v_reuseFailAlloc_2444_, 1, v_a_2437_);
v___x_2440_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
size_t v___x_2441_; size_t v___x_2442_; 
v___x_2441_ = ((size_t)1ULL);
v___x_2442_ = lean_usize_add(v_i_2405_, v___x_2441_);
v_i_2405_ = v___x_2442_;
v_b_2406_ = v___x_2440_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2453_; 
lean_del_object(v___x_2422_);
lean_dec(v_snd_2420_);
lean_dec(v_x_2402_);
lean_dec_ref(v_c_2401_);
v_a_2446_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2448_ = v___x_2425_;
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_dec(v___x_2425_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2451_; 
if (v_isShared_2449_ == 0)
{
v___x_2451_ = v___x_2448_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_a_2446_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8___boxed(lean_object** _args){
lean_object* v_init_2456_ = _args[0];
lean_object* v_c_2457_ = _args[1];
lean_object* v_x_2458_ = _args[2];
lean_object* v_as_2459_ = _args[3];
lean_object* v_sz_2460_ = _args[4];
lean_object* v_i_2461_ = _args[5];
lean_object* v_b_2462_ = _args[6];
lean_object* v___y_2463_ = _args[7];
lean_object* v___y_2464_ = _args[8];
lean_object* v___y_2465_ = _args[9];
lean_object* v___y_2466_ = _args[10];
lean_object* v___y_2467_ = _args[11];
lean_object* v___y_2468_ = _args[12];
lean_object* v___y_2469_ = _args[13];
lean_object* v___y_2470_ = _args[14];
lean_object* v___y_2471_ = _args[15];
lean_object* v___y_2472_ = _args[16];
lean_object* v___y_2473_ = _args[17];
_start:
{
size_t v_sz_boxed_2474_; size_t v_i_boxed_2475_; lean_object* v_res_2476_; 
v_sz_boxed_2474_ = lean_unbox_usize(v_sz_2460_);
lean_dec(v_sz_2460_);
v_i_boxed_2475_ = lean_unbox_usize(v_i_2461_);
lean_dec(v_i_2461_);
v_res_2476_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8(v_init_2456_, v_c_2457_, v_x_2458_, v_as_2459_, v_sz_boxed_2474_, v_i_boxed_2475_, v_b_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
lean_dec(v___y_2468_);
lean_dec_ref(v___y_2467_);
lean_dec(v___y_2466_);
lean_dec_ref(v___y_2465_);
lean_dec(v___y_2464_);
lean_dec(v___y_2463_);
lean_dec_ref(v_as_2459_);
lean_dec_ref(v_init_2456_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6___boxed(lean_object* v_init_2477_, lean_object* v_c_2478_, lean_object* v_x_2479_, lean_object* v_n_2480_, lean_object* v_b_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_){
_start:
{
lean_object* v_res_2493_; 
v_res_2493_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(v_init_2477_, v_c_2478_, v_x_2479_, v_n_2480_, v_b_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec(v___y_2483_);
lean_dec(v___y_2482_);
lean_dec_ref(v_n_2480_);
lean_dec_ref(v_init_2477_);
return v_res_2493_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2(lean_object* v_c_2494_, lean_object* v_x_2495_, lean_object* v_t_2496_, lean_object* v_init_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_){
_start:
{
lean_object* v_root_2509_; lean_object* v_tail_2510_; lean_object* v___x_2511_; 
v_root_2509_ = lean_ctor_get(v_t_2496_, 0);
v_tail_2510_ = lean_ctor_get(v_t_2496_, 1);
lean_inc(v_x_2495_);
lean_inc_ref(v_c_2494_);
lean_inc_ref(v_init_2497_);
v___x_2511_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(v_init_2497_, v_c_2494_, v_x_2495_, v_root_2509_, v_init_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
lean_dec_ref(v_init_2497_);
if (lean_obj_tag(v___x_2511_) == 0)
{
lean_object* v_a_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2548_; 
v_a_2512_ = lean_ctor_get(v___x_2511_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2514_ = v___x_2511_;
v_isShared_2515_ = v_isSharedCheck_2548_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_a_2512_);
lean_dec(v___x_2511_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2548_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
if (lean_obj_tag(v_a_2512_) == 0)
{
lean_object* v_a_2516_; lean_object* v___x_2518_; 
lean_dec(v_x_2495_);
lean_dec_ref(v_c_2494_);
v_a_2516_ = lean_ctor_get(v_a_2512_, 0);
lean_inc(v_a_2516_);
lean_dec_ref(v_a_2512_);
if (v_isShared_2515_ == 0)
{
lean_ctor_set(v___x_2514_, 0, v_a_2516_);
v___x_2518_ = v___x_2514_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_a_2516_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
else
{
lean_object* v_a_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; size_t v_sz_2523_; size_t v___x_2524_; lean_object* v___x_2525_; 
lean_del_object(v___x_2514_);
v_a_2520_ = lean_ctor_get(v_a_2512_, 0);
lean_inc(v_a_2520_);
lean_dec_ref(v_a_2512_);
v___x_2521_ = lean_box(0);
v___x_2522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2521_);
lean_ctor_set(v___x_2522_, 1, v_a_2520_);
v_sz_2523_ = lean_array_size(v_tail_2510_);
v___x_2524_ = ((size_t)0ULL);
v___x_2525_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7(v_c_2494_, v_x_2495_, v_tail_2510_, v_sz_2523_, v___x_2524_, v___x_2522_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2539_; 
v_a_2526_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2528_ = v___x_2525_;
v_isShared_2529_ = v_isSharedCheck_2539_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2525_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2539_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v_fst_2530_; 
v_fst_2530_ = lean_ctor_get(v_a_2526_, 0);
if (lean_obj_tag(v_fst_2530_) == 0)
{
lean_object* v_snd_2531_; lean_object* v___x_2533_; 
v_snd_2531_ = lean_ctor_get(v_a_2526_, 1);
lean_inc(v_snd_2531_);
lean_dec(v_a_2526_);
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 0, v_snd_2531_);
v___x_2533_ = v___x_2528_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_snd_2531_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
return v___x_2533_;
}
}
else
{
lean_object* v_val_2535_; lean_object* v___x_2537_; 
lean_inc_ref(v_fst_2530_);
lean_dec(v_a_2526_);
v_val_2535_ = lean_ctor_get(v_fst_2530_, 0);
lean_inc(v_val_2535_);
lean_dec_ref(v_fst_2530_);
if (v_isShared_2529_ == 0)
{
lean_ctor_set(v___x_2528_, 0, v_val_2535_);
v___x_2537_ = v___x_2528_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_val_2535_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
}
}
else
{
lean_object* v_a_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2547_; 
v_a_2540_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2542_ = v___x_2525_;
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_a_2540_);
lean_dec(v___x_2525_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2545_; 
if (v_isShared_2543_ == 0)
{
v___x_2545_ = v___x_2542_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_a_2540_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
}
}
}
else
{
lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2556_; 
lean_dec(v_x_2495_);
lean_dec_ref(v_c_2494_);
v_a_2549_ = lean_ctor_get(v___x_2511_, 0);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2551_ = v___x_2511_;
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_dec(v___x_2511_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2554_; 
if (v_isShared_2552_ == 0)
{
v___x_2554_ = v___x_2551_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v_a_2549_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2___boxed(lean_object* v_c_2557_, lean_object* v_x_2558_, lean_object* v_t_2559_, lean_object* v_init_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_){
_start:
{
lean_object* v_res_2572_; 
v_res_2572_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2(v_c_2557_, v_x_2558_, v_t_2559_, v_init_2560_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_, v___y_2570_);
lean_dec(v___y_2570_);
lean_dec_ref(v___y_2569_);
lean_dec(v___y_2568_);
lean_dec_ref(v___y_2567_);
lean_dec(v___y_2566_);
lean_dec_ref(v___y_2565_);
lean_dec(v___y_2564_);
lean_dec_ref(v___y_2563_);
lean_dec(v___y_2562_);
lean_dec(v___y_2561_);
lean_dec_ref(v_t_2559_);
return v_res_2572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(lean_object* v_x_2573_, lean_object* v_c_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_, lean_object* v_a_2577_, lean_object* v_a_2578_, lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_){
_start:
{
lean_object* v___x_2586_; 
v___x_2586_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2575_, v_a_2583_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v_a_2587_; lean_object* v___y_2589_; lean_object* v_diseqs_2614_; lean_object* v_size_2615_; lean_object* v___x_2616_; uint8_t v___x_2617_; 
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
lean_inc(v_a_2587_);
lean_dec_ref(v___x_2586_);
v_diseqs_2614_ = lean_ctor_get(v_a_2587_, 9);
lean_inc_ref(v_diseqs_2614_);
lean_dec(v_a_2587_);
v_size_2615_ = lean_ctor_get(v_diseqs_2614_, 2);
v___x_2616_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0);
v___x_2617_ = lean_nat_dec_lt(v_x_2573_, v_size_2615_);
if (v___x_2617_ == 0)
{
lean_object* v___x_2618_; 
lean_dec_ref(v_diseqs_2614_);
v___x_2618_ = l_outOfBounds___redArg(v___x_2616_);
v___y_2589_ = v___x_2618_;
goto v___jp_2588_;
}
else
{
lean_object* v___x_2619_; 
v___x_2619_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2616_, v_diseqs_2614_, v_x_2573_);
lean_dec_ref(v_diseqs_2614_);
v___y_2589_ = v___x_2619_;
goto v___jp_2588_;
}
v___jp_2588_:
{
lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2590_ = lean_box(0);
v___x_2591_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___closed__0));
v___x_2592_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2(v_c_2574_, v_x_2573_, v___y_2589_, v___x_2591_, v_a_2575_, v_a_2576_, v_a_2577_, v_a_2578_, v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_);
lean_dec_ref(v___y_2589_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2605_; 
v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2595_ = v___x_2592_;
v_isShared_2596_ = v_isSharedCheck_2605_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_a_2593_);
lean_dec(v___x_2592_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2605_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v_fst_2597_; 
v_fst_2597_ = lean_ctor_get(v_a_2593_, 0);
lean_inc(v_fst_2597_);
lean_dec(v_a_2593_);
if (lean_obj_tag(v_fst_2597_) == 0)
{
lean_object* v___x_2599_; 
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 0, v___x_2590_);
v___x_2599_ = v___x_2595_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v___x_2590_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
else
{
lean_object* v_val_2601_; lean_object* v___x_2603_; 
v_val_2601_ = lean_ctor_get(v_fst_2597_, 0);
lean_inc(v_val_2601_);
lean_dec_ref(v_fst_2597_);
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 0, v_val_2601_);
v___x_2603_ = v___x_2595_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_val_2601_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
}
else
{
lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2613_; 
v_a_2606_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2608_ = v___x_2592_;
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2592_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2611_; 
if (v_isShared_2609_ == 0)
{
v___x_2611_ = v___x_2608_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_a_2606_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
}
}
}
else
{
lean_object* v_a_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2627_; 
lean_dec_ref(v_c_2574_);
lean_dec(v_x_2573_);
v_a_2620_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2627_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2627_ == 0)
{
v___x_2622_ = v___x_2586_;
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_a_2620_);
lean_dec(v___x_2586_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2627_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2625_; 
if (v_isShared_2623_ == 0)
{
v___x_2625_ = v___x_2622_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2626_; 
v_reuseFailAlloc_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_a_2620_);
v___x_2625_ = v_reuseFailAlloc_2626_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
return v___x_2625_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f___boxed(lean_object* v_x_2628_, lean_object* v_c_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_){
_start:
{
lean_object* v_res_2641_; 
v_res_2641_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(v_x_2628_, v_c_2629_, v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_, v_a_2634_, v_a_2635_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_);
lean_dec(v_a_2639_);
lean_dec_ref(v_a_2638_);
lean_dec(v_a_2637_);
lean_dec_ref(v_a_2636_);
lean_dec(v_a_2635_);
lean_dec_ref(v_a_2634_);
lean_dec(v_a_2633_);
lean_dec_ref(v_a_2632_);
lean_dec(v_a_2631_);
lean_dec(v_a_2630_);
return v_res_2641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11(lean_object* v_c_2642_, lean_object* v_x_2643_, lean_object* v_as_2644_, size_t v_sz_2645_, size_t v_i_2646_, lean_object* v_b_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_){
_start:
{
lean_object* v___x_2659_; 
v___x_2659_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(v_c_2642_, v_x_2643_, v_as_2644_, v_sz_2645_, v_i_2646_, v_b_2647_, v___y_2648_);
return v___x_2659_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___boxed(lean_object** _args){
lean_object* v_c_2660_ = _args[0];
lean_object* v_x_2661_ = _args[1];
lean_object* v_as_2662_ = _args[2];
lean_object* v_sz_2663_ = _args[3];
lean_object* v_i_2664_ = _args[4];
lean_object* v_b_2665_ = _args[5];
lean_object* v___y_2666_ = _args[6];
lean_object* v___y_2667_ = _args[7];
lean_object* v___y_2668_ = _args[8];
lean_object* v___y_2669_ = _args[9];
lean_object* v___y_2670_ = _args[10];
lean_object* v___y_2671_ = _args[11];
lean_object* v___y_2672_ = _args[12];
lean_object* v___y_2673_ = _args[13];
lean_object* v___y_2674_ = _args[14];
lean_object* v___y_2675_ = _args[15];
lean_object* v___y_2676_ = _args[16];
_start:
{
size_t v_sz_boxed_2677_; size_t v_i_boxed_2678_; lean_object* v_res_2679_; 
v_sz_boxed_2677_ = lean_unbox_usize(v_sz_2663_);
lean_dec(v_sz_2663_);
v_i_boxed_2678_ = lean_unbox_usize(v_i_2664_);
lean_dec(v_i_2664_);
v_res_2679_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11(v_c_2660_, v_x_2661_, v_as_2662_, v_sz_boxed_2677_, v_i_boxed_2678_, v_b_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_);
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
lean_dec_ref(v_as_2662_);
return v_res_2679_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10(lean_object* v_c_2680_, lean_object* v_x_2681_, lean_object* v_as_2682_, size_t v_sz_2683_, size_t v_i_2684_, lean_object* v_b_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_){
_start:
{
lean_object* v___x_2697_; 
v___x_2697_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(v_c_2680_, v_x_2681_, v_as_2682_, v_sz_2683_, v_i_2684_, v_b_2685_, v___y_2686_);
return v___x_2697_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___boxed(lean_object** _args){
lean_object* v_c_2698_ = _args[0];
lean_object* v_x_2699_ = _args[1];
lean_object* v_as_2700_ = _args[2];
lean_object* v_sz_2701_ = _args[3];
lean_object* v_i_2702_ = _args[4];
lean_object* v_b_2703_ = _args[5];
lean_object* v___y_2704_ = _args[6];
lean_object* v___y_2705_ = _args[7];
lean_object* v___y_2706_ = _args[8];
lean_object* v___y_2707_ = _args[9];
lean_object* v___y_2708_ = _args[10];
lean_object* v___y_2709_ = _args[11];
lean_object* v___y_2710_ = _args[12];
lean_object* v___y_2711_ = _args[13];
lean_object* v___y_2712_ = _args[14];
lean_object* v___y_2713_ = _args[15];
lean_object* v___y_2714_ = _args[16];
_start:
{
size_t v_sz_boxed_2715_; size_t v_i_boxed_2716_; lean_object* v_res_2717_; 
v_sz_boxed_2715_ = lean_unbox_usize(v_sz_2701_);
lean_dec(v_sz_2701_);
v_i_boxed_2716_ = lean_unbox_usize(v_i_2702_);
lean_dec(v_i_2702_);
v_res_2717_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10(v_c_2698_, v_x_2699_, v_as_2700_, v_sz_boxed_2715_, v_i_boxed_2716_, v_b_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_);
lean_dec(v___y_2713_);
lean_dec_ref(v___y_2712_);
lean_dec(v___y_2711_);
lean_dec_ref(v___y_2710_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
lean_dec(v___y_2705_);
lean_dec(v___y_2704_);
lean_dec_ref(v_as_2700_);
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg(lean_object* v_v_2718_, lean_object* v_a_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_){
_start:
{
lean_object* v_snd_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2762_; 
v_snd_2731_ = lean_ctor_get(v_a_2719_, 1);
v_isSharedCheck_2762_ = !lean_is_exclusive(v_a_2719_);
if (v_isSharedCheck_2762_ == 0)
{
lean_object* v_unused_2763_; 
v_unused_2763_ = lean_ctor_get(v_a_2719_, 0);
lean_dec(v_unused_2763_);
v___x_2733_ = v_a_2719_;
v_isShared_2734_ = v_isSharedCheck_2762_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_snd_2731_);
lean_dec(v_a_2719_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2762_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v___x_2735_; 
lean_inc(v_snd_2731_);
lean_inc(v_v_2718_);
v___x_2735_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(v_v_2718_, v_snd_2731_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_);
if (lean_obj_tag(v___x_2735_) == 0)
{
lean_object* v_a_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2753_; 
v_a_2736_ = lean_ctor_get(v___x_2735_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2738_ = v___x_2735_;
v_isShared_2739_ = v_isSharedCheck_2753_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_a_2736_);
lean_dec(v___x_2735_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2753_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
if (lean_obj_tag(v_a_2736_) == 1)
{
lean_object* v_val_2740_; lean_object* v___x_2741_; lean_object* v___x_2743_; 
lean_del_object(v___x_2738_);
lean_dec(v_snd_2731_);
v_val_2740_ = lean_ctor_get(v_a_2736_, 0);
lean_inc(v_val_2740_);
lean_dec_ref(v_a_2736_);
v___x_2741_ = lean_box(0);
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 1, v_val_2740_);
lean_ctor_set(v___x_2733_, 0, v___x_2741_);
v___x_2743_ = v___x_2733_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v___x_2741_);
lean_ctor_set(v_reuseFailAlloc_2745_, 1, v_val_2740_);
v___x_2743_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
v_a_2719_ = v___x_2743_;
goto _start;
}
}
else
{
lean_object* v___x_2746_; lean_object* v___x_2748_; 
lean_dec(v_a_2736_);
lean_dec(v_v_2718_);
lean_inc(v_snd_2731_);
v___x_2746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2746_, 0, v_snd_2731_);
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 0, v___x_2746_);
v___x_2748_ = v___x_2733_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v___x_2746_);
lean_ctor_set(v_reuseFailAlloc_2752_, 1, v_snd_2731_);
v___x_2748_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
lean_object* v___x_2750_; 
if (v_isShared_2739_ == 0)
{
lean_ctor_set(v___x_2738_, 0, v___x_2748_);
v___x_2750_ = v___x_2738_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v___x_2748_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
return v___x_2750_;
}
}
}
}
}
else
{
lean_object* v_a_2754_; lean_object* v___x_2756_; uint8_t v_isShared_2757_; uint8_t v_isSharedCheck_2761_; 
lean_del_object(v___x_2733_);
lean_dec(v_snd_2731_);
lean_dec(v_v_2718_);
v_a_2754_ = lean_ctor_get(v___x_2735_, 0);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2756_ = v___x_2735_;
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
else
{
lean_inc(v_a_2754_);
lean_dec(v___x_2735_);
v___x_2756_ = lean_box(0);
v_isShared_2757_ = v_isSharedCheck_2761_;
goto v_resetjp_2755_;
}
v_resetjp_2755_:
{
lean_object* v___x_2759_; 
if (v_isShared_2757_ == 0)
{
v___x_2759_ = v___x_2756_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v_a_2754_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
return v___x_2759_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg___boxed(lean_object* v_v_2764_, lean_object* v_a_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_){
_start:
{
lean_object* v_res_2777_; 
v_res_2777_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg(v_v_2764_, v_a_2765_, v___y_2766_, v___y_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_);
lean_dec(v___y_2775_);
lean_dec_ref(v___y_2774_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
lean_dec(v___y_2771_);
lean_dec_ref(v___y_2770_);
lean_dec(v___y_2769_);
lean_dec_ref(v___y_2768_);
lean_dec(v___y_2767_);
lean_dec(v___y_2766_);
return v_res_2777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(lean_object* v_c_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_){
_start:
{
lean_object* v_p_2790_; 
v_p_2790_ = lean_ctor_get(v_c_2778_, 0);
if (lean_obj_tag(v_p_2790_) == 1)
{
lean_object* v_v_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
v_v_2791_ = lean_ctor_get(v_p_2790_, 1);
lean_inc(v_v_2791_);
v___x_2792_ = lean_box(0);
v___x_2793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2792_);
lean_ctor_set(v___x_2793_, 1, v_c_2778_);
v___x_2794_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg(v_v_2791_, v___x_2793_, v_a_2779_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_object* v_a_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2808_; 
v_a_2795_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2797_ = v___x_2794_;
v_isShared_2798_ = v_isSharedCheck_2808_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_a_2795_);
lean_dec(v___x_2794_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2808_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v_fst_2799_; 
v_fst_2799_ = lean_ctor_get(v_a_2795_, 0);
if (lean_obj_tag(v_fst_2799_) == 0)
{
lean_object* v_snd_2800_; lean_object* v___x_2802_; 
v_snd_2800_ = lean_ctor_get(v_a_2795_, 1);
lean_inc(v_snd_2800_);
lean_dec(v_a_2795_);
if (v_isShared_2798_ == 0)
{
lean_ctor_set(v___x_2797_, 0, v_snd_2800_);
v___x_2802_ = v___x_2797_;
goto v_reusejp_2801_;
}
else
{
lean_object* v_reuseFailAlloc_2803_; 
v_reuseFailAlloc_2803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2803_, 0, v_snd_2800_);
v___x_2802_ = v_reuseFailAlloc_2803_;
goto v_reusejp_2801_;
}
v_reusejp_2801_:
{
return v___x_2802_;
}
}
else
{
lean_object* v_val_2804_; lean_object* v___x_2806_; 
lean_inc_ref(v_fst_2799_);
lean_dec(v_a_2795_);
v_val_2804_ = lean_ctor_get(v_fst_2799_, 0);
lean_inc(v_val_2804_);
lean_dec_ref(v_fst_2799_);
if (v_isShared_2798_ == 0)
{
lean_ctor_set(v___x_2797_, 0, v_val_2804_);
v___x_2806_ = v___x_2797_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_val_2804_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
return v___x_2806_;
}
}
}
}
else
{
lean_object* v_a_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2816_; 
v_a_2809_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2811_ = v___x_2794_;
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_a_2809_);
lean_dec(v___x_2794_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v___x_2814_; 
if (v_isShared_2812_ == 0)
{
v___x_2814_ = v___x_2811_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_a_2809_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
}
}
else
{
lean_object* v___x_2817_; 
v___x_2817_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_2778_, v_a_2779_, v_a_2785_, v_a_2786_, v_a_2787_, v_a_2788_);
return v___x_2817_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq___boxed(lean_object* v_c_2818_, lean_object* v_a_2819_, lean_object* v_a_2820_, lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_, lean_object* v_a_2827_, lean_object* v_a_2828_, lean_object* v_a_2829_){
_start:
{
lean_object* v_res_2830_; 
v_res_2830_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(v_c_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_, v_a_2825_, v_a_2826_, v_a_2827_, v_a_2828_);
lean_dec(v_a_2828_);
lean_dec_ref(v_a_2827_);
lean_dec(v_a_2826_);
lean_dec_ref(v_a_2825_);
lean_dec(v_a_2824_);
lean_dec_ref(v_a_2823_);
lean_dec(v_a_2822_);
lean_dec_ref(v_a_2821_);
lean_dec(v_a_2820_);
lean_dec(v_a_2819_);
return v_res_2830_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0(lean_object* v_v_2831_, lean_object* v_inst_2832_, lean_object* v_a_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_){
_start:
{
lean_object* v___x_2845_; 
v___x_2845_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg(v_v_2831_, v_a_2833_, v___y_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_);
return v___x_2845_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___boxed(lean_object* v_v_2846_, lean_object* v_inst_2847_, lean_object* v_a_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_, lean_object* v___y_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_){
_start:
{
lean_object* v_res_2860_; 
v_res_2860_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0(v_v_2846_, v_inst_2847_, v_a_2848_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_, v___y_2853_, v___y_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_);
lean_dec(v___y_2858_);
lean_dec_ref(v___y_2857_);
lean_dec(v___y_2856_);
lean_dec_ref(v___y_2855_);
lean_dec(v___y_2854_);
lean_dec_ref(v___y_2853_);
lean_dec(v___y_2852_);
lean_dec_ref(v___y_2851_);
lean_dec(v___y_2850_);
lean_dec(v___y_2849_);
return v_res_2860_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(lean_object* v_a_2861_, lean_object* v_x_2862_, size_t v_x_2863_, size_t v_x_2864_){
_start:
{
if (lean_obj_tag(v_x_2862_) == 0)
{
lean_object* v_cs_2865_; size_t v_j_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; uint8_t v___x_2869_; 
v_cs_2865_ = lean_ctor_get(v_x_2862_, 0);
v_j_2866_ = lean_usize_shift_right(v_x_2863_, v_x_2864_);
v___x_2867_ = lean_usize_to_nat(v_j_2866_);
v___x_2868_ = lean_array_get_size(v_cs_2865_);
v___x_2869_ = lean_nat_dec_lt(v___x_2867_, v___x_2868_);
if (v___x_2869_ == 0)
{
lean_dec(v___x_2867_);
lean_dec_ref(v_a_2861_);
return v_x_2862_;
}
else
{
lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2887_; 
lean_inc_ref(v_cs_2865_);
v_isSharedCheck_2887_ = !lean_is_exclusive(v_x_2862_);
if (v_isSharedCheck_2887_ == 0)
{
lean_object* v_unused_2888_; 
v_unused_2888_ = lean_ctor_get(v_x_2862_, 0);
lean_dec(v_unused_2888_);
v___x_2871_ = v_x_2862_;
v_isShared_2872_ = v_isSharedCheck_2887_;
goto v_resetjp_2870_;
}
else
{
lean_dec(v_x_2862_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2887_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
size_t v___x_2873_; size_t v___x_2874_; size_t v___x_2875_; size_t v_i_2876_; size_t v___x_2877_; size_t v_shift_2878_; lean_object* v_v_2879_; lean_object* v___x_2880_; lean_object* v_xs_x27_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2885_; 
v___x_2873_ = ((size_t)1ULL);
v___x_2874_ = lean_usize_shift_left(v___x_2873_, v_x_2864_);
v___x_2875_ = lean_usize_sub(v___x_2874_, v___x_2873_);
v_i_2876_ = lean_usize_land(v_x_2863_, v___x_2875_);
v___x_2877_ = ((size_t)5ULL);
v_shift_2878_ = lean_usize_sub(v_x_2864_, v___x_2877_);
v_v_2879_ = lean_array_fget(v_cs_2865_, v___x_2867_);
v___x_2880_ = lean_box(0);
v_xs_x27_2881_ = lean_array_fset(v_cs_2865_, v___x_2867_, v___x_2880_);
v___x_2882_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(v_a_2861_, v_v_2879_, v_i_2876_, v_shift_2878_);
v___x_2883_ = lean_array_fset(v_xs_x27_2881_, v___x_2867_, v___x_2882_);
lean_dec(v___x_2867_);
if (v_isShared_2872_ == 0)
{
lean_ctor_set(v___x_2871_, 0, v___x_2883_);
v___x_2885_ = v___x_2871_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v___x_2883_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
}
}
else
{
lean_object* v_vs_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; uint8_t v___x_2892_; 
v_vs_2889_ = lean_ctor_get(v_x_2862_, 0);
v___x_2890_ = lean_usize_to_nat(v_x_2863_);
v___x_2891_ = lean_array_get_size(v_vs_2889_);
v___x_2892_ = lean_nat_dec_lt(v___x_2890_, v___x_2891_);
if (v___x_2892_ == 0)
{
lean_dec(v___x_2890_);
lean_dec_ref(v_a_2861_);
return v_x_2862_;
}
else
{
lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2904_; 
lean_inc_ref(v_vs_2889_);
v_isSharedCheck_2904_ = !lean_is_exclusive(v_x_2862_);
if (v_isSharedCheck_2904_ == 0)
{
lean_object* v_unused_2905_; 
v_unused_2905_ = lean_ctor_get(v_x_2862_, 0);
lean_dec(v_unused_2905_);
v___x_2894_ = v_x_2862_;
v_isShared_2895_ = v_isSharedCheck_2904_;
goto v_resetjp_2893_;
}
else
{
lean_dec(v_x_2862_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2904_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v_v_2896_; lean_object* v___x_2897_; lean_object* v_xs_x27_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2902_; 
v_v_2896_ = lean_array_fget(v_vs_2889_, v___x_2890_);
v___x_2897_ = lean_box(0);
v_xs_x27_2898_ = lean_array_fset(v_vs_2889_, v___x_2890_, v___x_2897_);
v___x_2899_ = l_Lean_PersistentArray_push___redArg(v_v_2896_, v_a_2861_);
v___x_2900_ = lean_array_fset(v_xs_x27_2898_, v___x_2890_, v___x_2899_);
lean_dec(v___x_2890_);
if (v_isShared_2895_ == 0)
{
lean_ctor_set(v___x_2894_, 0, v___x_2900_);
v___x_2902_ = v___x_2894_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v___x_2900_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0___boxed(lean_object* v_a_2906_, lean_object* v_x_2907_, lean_object* v_x_2908_, lean_object* v_x_2909_){
_start:
{
size_t v_x_93928__boxed_2910_; size_t v_x_93929__boxed_2911_; lean_object* v_res_2912_; 
v_x_93928__boxed_2910_ = lean_unbox_usize(v_x_2908_);
lean_dec(v_x_2908_);
v_x_93929__boxed_2911_ = lean_unbox_usize(v_x_2909_);
lean_dec(v_x_2909_);
v_res_2912_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(v_a_2906_, v_x_2907_, v_x_93928__boxed_2910_, v_x_93929__boxed_2911_);
return v_res_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(lean_object* v_a_2913_, lean_object* v_t_2914_, lean_object* v_i_2915_){
_start:
{
lean_object* v_root_2916_; lean_object* v_tail_2917_; lean_object* v_size_2918_; size_t v_shift_2919_; lean_object* v_tailOff_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2944_; 
v_root_2916_ = lean_ctor_get(v_t_2914_, 0);
v_tail_2917_ = lean_ctor_get(v_t_2914_, 1);
v_size_2918_ = lean_ctor_get(v_t_2914_, 2);
v_shift_2919_ = lean_ctor_get_usize(v_t_2914_, 4);
v_tailOff_2920_ = lean_ctor_get(v_t_2914_, 3);
v_isSharedCheck_2944_ = !lean_is_exclusive(v_t_2914_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2922_ = v_t_2914_;
v_isShared_2923_ = v_isSharedCheck_2944_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_tailOff_2920_);
lean_inc(v_size_2918_);
lean_inc(v_tail_2917_);
lean_inc(v_root_2916_);
lean_dec(v_t_2914_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2944_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
uint8_t v___x_2924_; 
v___x_2924_ = lean_nat_dec_le(v_tailOff_2920_, v_i_2915_);
if (v___x_2924_ == 0)
{
size_t v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2928_; 
v___x_2925_ = lean_usize_of_nat(v_i_2915_);
v___x_2926_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(v_a_2913_, v_root_2916_, v___x_2925_, v_shift_2919_);
if (v_isShared_2923_ == 0)
{
lean_ctor_set(v___x_2922_, 0, v___x_2926_);
v___x_2928_ = v___x_2922_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v___x_2926_);
lean_ctor_set(v_reuseFailAlloc_2929_, 1, v_tail_2917_);
lean_ctor_set(v_reuseFailAlloc_2929_, 2, v_size_2918_);
lean_ctor_set(v_reuseFailAlloc_2929_, 3, v_tailOff_2920_);
lean_ctor_set_usize(v_reuseFailAlloc_2929_, 4, v_shift_2919_);
v___x_2928_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
return v___x_2928_;
}
}
else
{
lean_object* v___x_2930_; lean_object* v___x_2931_; uint8_t v___x_2932_; 
v___x_2930_ = lean_nat_sub(v_i_2915_, v_tailOff_2920_);
v___x_2931_ = lean_array_get_size(v_tail_2917_);
v___x_2932_ = lean_nat_dec_lt(v___x_2930_, v___x_2931_);
if (v___x_2932_ == 0)
{
lean_object* v___x_2934_; 
lean_dec(v___x_2930_);
lean_dec_ref(v_a_2913_);
if (v_isShared_2923_ == 0)
{
v___x_2934_ = v___x_2922_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v_root_2916_);
lean_ctor_set(v_reuseFailAlloc_2935_, 1, v_tail_2917_);
lean_ctor_set(v_reuseFailAlloc_2935_, 2, v_size_2918_);
lean_ctor_set(v_reuseFailAlloc_2935_, 3, v_tailOff_2920_);
lean_ctor_set_usize(v_reuseFailAlloc_2935_, 4, v_shift_2919_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
return v___x_2934_;
}
}
else
{
lean_object* v_v_2936_; lean_object* v___x_2937_; lean_object* v_xs_x27_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2942_; 
v_v_2936_ = lean_array_fget(v_tail_2917_, v___x_2930_);
v___x_2937_ = lean_box(0);
v_xs_x27_2938_ = lean_array_fset(v_tail_2917_, v___x_2930_, v___x_2937_);
v___x_2939_ = l_Lean_PersistentArray_push___redArg(v_v_2936_, v_a_2913_);
v___x_2940_ = lean_array_fset(v_xs_x27_2938_, v___x_2930_, v___x_2939_);
lean_dec(v___x_2930_);
if (v_isShared_2923_ == 0)
{
lean_ctor_set(v___x_2922_, 1, v___x_2940_);
v___x_2942_ = v___x_2922_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_root_2916_);
lean_ctor_set(v_reuseFailAlloc_2943_, 1, v___x_2940_);
lean_ctor_set(v_reuseFailAlloc_2943_, 2, v_size_2918_);
lean_ctor_set(v_reuseFailAlloc_2943_, 3, v_tailOff_2920_);
lean_ctor_set_usize(v_reuseFailAlloc_2943_, 4, v_shift_2919_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0___boxed(lean_object* v_a_2945_, lean_object* v_t_2946_, lean_object* v_i_2947_){
_start:
{
lean_object* v_res_2948_; 
v_res_2948_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(v_a_2945_, v_t_2946_, v_i_2947_);
lean_dec(v_i_2947_);
return v_res_2948_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0(lean_object* v_a_2949_, lean_object* v_v_2950_, lean_object* v_s_2951_){
_start:
{
lean_object* v_vars_2952_; lean_object* v_varMap_2953_; lean_object* v_vars_x27_2954_; lean_object* v_varMap_x27_2955_; lean_object* v_natToIntMap_2956_; lean_object* v_natDef_2957_; lean_object* v_dvds_2958_; lean_object* v_lowers_2959_; lean_object* v_uppers_2960_; lean_object* v_diseqs_2961_; lean_object* v_elimEqs_2962_; lean_object* v_elimStack_2963_; lean_object* v_occurs_2964_; lean_object* v_assignment_2965_; lean_object* v_nextCnstrId_2966_; uint8_t v_caseSplits_2967_; lean_object* v_conflict_x3f_2968_; lean_object* v_diseqSplits_2969_; lean_object* v_divMod_2970_; lean_object* v_toIntIds_2971_; lean_object* v_toIntInfos_2972_; lean_object* v_toIntTermMap_2973_; lean_object* v_toIntVarMap_2974_; uint8_t v_usedCommRing_2975_; lean_object* v_nonlinearOccs_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2984_; 
v_vars_2952_ = lean_ctor_get(v_s_2951_, 0);
v_varMap_2953_ = lean_ctor_get(v_s_2951_, 1);
v_vars_x27_2954_ = lean_ctor_get(v_s_2951_, 2);
v_varMap_x27_2955_ = lean_ctor_get(v_s_2951_, 3);
v_natToIntMap_2956_ = lean_ctor_get(v_s_2951_, 4);
v_natDef_2957_ = lean_ctor_get(v_s_2951_, 5);
v_dvds_2958_ = lean_ctor_get(v_s_2951_, 6);
v_lowers_2959_ = lean_ctor_get(v_s_2951_, 7);
v_uppers_2960_ = lean_ctor_get(v_s_2951_, 8);
v_diseqs_2961_ = lean_ctor_get(v_s_2951_, 9);
v_elimEqs_2962_ = lean_ctor_get(v_s_2951_, 10);
v_elimStack_2963_ = lean_ctor_get(v_s_2951_, 11);
v_occurs_2964_ = lean_ctor_get(v_s_2951_, 12);
v_assignment_2965_ = lean_ctor_get(v_s_2951_, 13);
v_nextCnstrId_2966_ = lean_ctor_get(v_s_2951_, 14);
v_caseSplits_2967_ = lean_ctor_get_uint8(v_s_2951_, sizeof(void*)*23);
v_conflict_x3f_2968_ = lean_ctor_get(v_s_2951_, 15);
v_diseqSplits_2969_ = lean_ctor_get(v_s_2951_, 16);
v_divMod_2970_ = lean_ctor_get(v_s_2951_, 17);
v_toIntIds_2971_ = lean_ctor_get(v_s_2951_, 18);
v_toIntInfos_2972_ = lean_ctor_get(v_s_2951_, 19);
v_toIntTermMap_2973_ = lean_ctor_get(v_s_2951_, 20);
v_toIntVarMap_2974_ = lean_ctor_get(v_s_2951_, 21);
v_usedCommRing_2975_ = lean_ctor_get_uint8(v_s_2951_, sizeof(void*)*23 + 1);
v_nonlinearOccs_2976_ = lean_ctor_get(v_s_2951_, 22);
v_isSharedCheck_2984_ = !lean_is_exclusive(v_s_2951_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2978_ = v_s_2951_;
v_isShared_2979_ = v_isSharedCheck_2984_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_nonlinearOccs_2976_);
lean_inc(v_toIntVarMap_2974_);
lean_inc(v_toIntTermMap_2973_);
lean_inc(v_toIntInfos_2972_);
lean_inc(v_toIntIds_2971_);
lean_inc(v_divMod_2970_);
lean_inc(v_diseqSplits_2969_);
lean_inc(v_conflict_x3f_2968_);
lean_inc(v_nextCnstrId_2966_);
lean_inc(v_assignment_2965_);
lean_inc(v_occurs_2964_);
lean_inc(v_elimStack_2963_);
lean_inc(v_elimEqs_2962_);
lean_inc(v_diseqs_2961_);
lean_inc(v_uppers_2960_);
lean_inc(v_lowers_2959_);
lean_inc(v_dvds_2958_);
lean_inc(v_natDef_2957_);
lean_inc(v_natToIntMap_2956_);
lean_inc(v_varMap_x27_2955_);
lean_inc(v_vars_x27_2954_);
lean_inc(v_varMap_2953_);
lean_inc(v_vars_2952_);
lean_dec(v_s_2951_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_2984_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2980_; lean_object* v___x_2982_; 
v___x_2980_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(v_a_2949_, v_lowers_2959_, v_v_2950_);
if (v_isShared_2979_ == 0)
{
lean_ctor_set(v___x_2978_, 7, v___x_2980_);
v___x_2982_ = v___x_2978_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v_vars_2952_);
lean_ctor_set(v_reuseFailAlloc_2983_, 1, v_varMap_2953_);
lean_ctor_set(v_reuseFailAlloc_2983_, 2, v_vars_x27_2954_);
lean_ctor_set(v_reuseFailAlloc_2983_, 3, v_varMap_x27_2955_);
lean_ctor_set(v_reuseFailAlloc_2983_, 4, v_natToIntMap_2956_);
lean_ctor_set(v_reuseFailAlloc_2983_, 5, v_natDef_2957_);
lean_ctor_set(v_reuseFailAlloc_2983_, 6, v_dvds_2958_);
lean_ctor_set(v_reuseFailAlloc_2983_, 7, v___x_2980_);
lean_ctor_set(v_reuseFailAlloc_2983_, 8, v_uppers_2960_);
lean_ctor_set(v_reuseFailAlloc_2983_, 9, v_diseqs_2961_);
lean_ctor_set(v_reuseFailAlloc_2983_, 10, v_elimEqs_2962_);
lean_ctor_set(v_reuseFailAlloc_2983_, 11, v_elimStack_2963_);
lean_ctor_set(v_reuseFailAlloc_2983_, 12, v_occurs_2964_);
lean_ctor_set(v_reuseFailAlloc_2983_, 13, v_assignment_2965_);
lean_ctor_set(v_reuseFailAlloc_2983_, 14, v_nextCnstrId_2966_);
lean_ctor_set(v_reuseFailAlloc_2983_, 15, v_conflict_x3f_2968_);
lean_ctor_set(v_reuseFailAlloc_2983_, 16, v_diseqSplits_2969_);
lean_ctor_set(v_reuseFailAlloc_2983_, 17, v_divMod_2970_);
lean_ctor_set(v_reuseFailAlloc_2983_, 18, v_toIntIds_2971_);
lean_ctor_set(v_reuseFailAlloc_2983_, 19, v_toIntInfos_2972_);
lean_ctor_set(v_reuseFailAlloc_2983_, 20, v_toIntTermMap_2973_);
lean_ctor_set(v_reuseFailAlloc_2983_, 21, v_toIntVarMap_2974_);
lean_ctor_set(v_reuseFailAlloc_2983_, 22, v_nonlinearOccs_2976_);
lean_ctor_set_uint8(v_reuseFailAlloc_2983_, sizeof(void*)*23, v_caseSplits_2967_);
lean_ctor_set_uint8(v_reuseFailAlloc_2983_, sizeof(void*)*23 + 1, v_usedCommRing_2975_);
v___x_2982_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
return v___x_2982_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0___boxed(lean_object* v_a_2985_, lean_object* v_v_2986_, lean_object* v_s_2987_){
_start:
{
lean_object* v_res_2988_; 
v_res_2988_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0(v_a_2985_, v_v_2986_, v_s_2987_);
lean_dec(v_v_2986_);
return v_res_2988_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1(lean_object* v_a_2989_, lean_object* v_v_2990_, lean_object* v_s_2991_){
_start:
{
lean_object* v_vars_2992_; lean_object* v_varMap_2993_; lean_object* v_vars_x27_2994_; lean_object* v_varMap_x27_2995_; lean_object* v_natToIntMap_2996_; lean_object* v_natDef_2997_; lean_object* v_dvds_2998_; lean_object* v_lowers_2999_; lean_object* v_uppers_3000_; lean_object* v_diseqs_3001_; lean_object* v_elimEqs_3002_; lean_object* v_elimStack_3003_; lean_object* v_occurs_3004_; lean_object* v_assignment_3005_; lean_object* v_nextCnstrId_3006_; uint8_t v_caseSplits_3007_; lean_object* v_conflict_x3f_3008_; lean_object* v_diseqSplits_3009_; lean_object* v_divMod_3010_; lean_object* v_toIntIds_3011_; lean_object* v_toIntInfos_3012_; lean_object* v_toIntTermMap_3013_; lean_object* v_toIntVarMap_3014_; uint8_t v_usedCommRing_3015_; lean_object* v_nonlinearOccs_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3024_; 
v_vars_2992_ = lean_ctor_get(v_s_2991_, 0);
v_varMap_2993_ = lean_ctor_get(v_s_2991_, 1);
v_vars_x27_2994_ = lean_ctor_get(v_s_2991_, 2);
v_varMap_x27_2995_ = lean_ctor_get(v_s_2991_, 3);
v_natToIntMap_2996_ = lean_ctor_get(v_s_2991_, 4);
v_natDef_2997_ = lean_ctor_get(v_s_2991_, 5);
v_dvds_2998_ = lean_ctor_get(v_s_2991_, 6);
v_lowers_2999_ = lean_ctor_get(v_s_2991_, 7);
v_uppers_3000_ = lean_ctor_get(v_s_2991_, 8);
v_diseqs_3001_ = lean_ctor_get(v_s_2991_, 9);
v_elimEqs_3002_ = lean_ctor_get(v_s_2991_, 10);
v_elimStack_3003_ = lean_ctor_get(v_s_2991_, 11);
v_occurs_3004_ = lean_ctor_get(v_s_2991_, 12);
v_assignment_3005_ = lean_ctor_get(v_s_2991_, 13);
v_nextCnstrId_3006_ = lean_ctor_get(v_s_2991_, 14);
v_caseSplits_3007_ = lean_ctor_get_uint8(v_s_2991_, sizeof(void*)*23);
v_conflict_x3f_3008_ = lean_ctor_get(v_s_2991_, 15);
v_diseqSplits_3009_ = lean_ctor_get(v_s_2991_, 16);
v_divMod_3010_ = lean_ctor_get(v_s_2991_, 17);
v_toIntIds_3011_ = lean_ctor_get(v_s_2991_, 18);
v_toIntInfos_3012_ = lean_ctor_get(v_s_2991_, 19);
v_toIntTermMap_3013_ = lean_ctor_get(v_s_2991_, 20);
v_toIntVarMap_3014_ = lean_ctor_get(v_s_2991_, 21);
v_usedCommRing_3015_ = lean_ctor_get_uint8(v_s_2991_, sizeof(void*)*23 + 1);
v_nonlinearOccs_3016_ = lean_ctor_get(v_s_2991_, 22);
v_isSharedCheck_3024_ = !lean_is_exclusive(v_s_2991_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_3018_ = v_s_2991_;
v_isShared_3019_ = v_isSharedCheck_3024_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_nonlinearOccs_3016_);
lean_inc(v_toIntVarMap_3014_);
lean_inc(v_toIntTermMap_3013_);
lean_inc(v_toIntInfos_3012_);
lean_inc(v_toIntIds_3011_);
lean_inc(v_divMod_3010_);
lean_inc(v_diseqSplits_3009_);
lean_inc(v_conflict_x3f_3008_);
lean_inc(v_nextCnstrId_3006_);
lean_inc(v_assignment_3005_);
lean_inc(v_occurs_3004_);
lean_inc(v_elimStack_3003_);
lean_inc(v_elimEqs_3002_);
lean_inc(v_diseqs_3001_);
lean_inc(v_uppers_3000_);
lean_inc(v_lowers_2999_);
lean_inc(v_dvds_2998_);
lean_inc(v_natDef_2997_);
lean_inc(v_natToIntMap_2996_);
lean_inc(v_varMap_x27_2995_);
lean_inc(v_vars_x27_2994_);
lean_inc(v_varMap_2993_);
lean_inc(v_vars_2992_);
lean_dec(v_s_2991_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3024_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v___x_3020_; lean_object* v___x_3022_; 
v___x_3020_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(v_a_2989_, v_uppers_3000_, v_v_2990_);
if (v_isShared_3019_ == 0)
{
lean_ctor_set(v___x_3018_, 8, v___x_3020_);
v___x_3022_ = v___x_3018_;
goto v_reusejp_3021_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(0, 23, 2);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v_vars_2992_);
lean_ctor_set(v_reuseFailAlloc_3023_, 1, v_varMap_2993_);
lean_ctor_set(v_reuseFailAlloc_3023_, 2, v_vars_x27_2994_);
lean_ctor_set(v_reuseFailAlloc_3023_, 3, v_varMap_x27_2995_);
lean_ctor_set(v_reuseFailAlloc_3023_, 4, v_natToIntMap_2996_);
lean_ctor_set(v_reuseFailAlloc_3023_, 5, v_natDef_2997_);
lean_ctor_set(v_reuseFailAlloc_3023_, 6, v_dvds_2998_);
lean_ctor_set(v_reuseFailAlloc_3023_, 7, v_lowers_2999_);
lean_ctor_set(v_reuseFailAlloc_3023_, 8, v___x_3020_);
lean_ctor_set(v_reuseFailAlloc_3023_, 9, v_diseqs_3001_);
lean_ctor_set(v_reuseFailAlloc_3023_, 10, v_elimEqs_3002_);
lean_ctor_set(v_reuseFailAlloc_3023_, 11, v_elimStack_3003_);
lean_ctor_set(v_reuseFailAlloc_3023_, 12, v_occurs_3004_);
lean_ctor_set(v_reuseFailAlloc_3023_, 13, v_assignment_3005_);
lean_ctor_set(v_reuseFailAlloc_3023_, 14, v_nextCnstrId_3006_);
lean_ctor_set(v_reuseFailAlloc_3023_, 15, v_conflict_x3f_3008_);
lean_ctor_set(v_reuseFailAlloc_3023_, 16, v_diseqSplits_3009_);
lean_ctor_set(v_reuseFailAlloc_3023_, 17, v_divMod_3010_);
lean_ctor_set(v_reuseFailAlloc_3023_, 18, v_toIntIds_3011_);
lean_ctor_set(v_reuseFailAlloc_3023_, 19, v_toIntInfos_3012_);
lean_ctor_set(v_reuseFailAlloc_3023_, 20, v_toIntTermMap_3013_);
lean_ctor_set(v_reuseFailAlloc_3023_, 21, v_toIntVarMap_3014_);
lean_ctor_set(v_reuseFailAlloc_3023_, 22, v_nonlinearOccs_3016_);
lean_ctor_set_uint8(v_reuseFailAlloc_3023_, sizeof(void*)*23, v_caseSplits_3007_);
lean_ctor_set_uint8(v_reuseFailAlloc_3023_, sizeof(void*)*23 + 1, v_usedCommRing_3015_);
v___x_3022_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3021_;
}
v_reusejp_3021_:
{
return v___x_3022_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1___boxed(lean_object* v_a_3025_, lean_object* v_v_3026_, lean_object* v_s_3027_){
_start:
{
lean_object* v_res_3028_; 
v_res_3028_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1(v_a_3025_, v_v_3026_, v_s_3027_);
lean_dec(v_v_3026_);
return v_res_3028_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3(void){
_start:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___x_3036_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2));
v___x_3037_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_3038_ = l_Lean_Name_append(v___x_3037_, v___x_3036_);
return v___x_3038_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6(void){
_start:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3045_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5));
v___x_3046_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_3047_ = l_Lean_Name_append(v___x_3046_, v___x_3045_);
return v___x_3047_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9(void){
_start:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3054_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__8));
v___x_3055_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_3056_ = l_Lean_Name_append(v___x_3055_, v___x_3054_);
return v___x_3056_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11(void){
_start:
{
lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; 
v___x_3061_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__10));
v___x_3062_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_3063_ = l_Lean_Name_append(v___x_3062_, v___x_3061_);
return v___x_3063_;
}
}
LEAN_EXPORT lean_object* lean_grind_cutsat_assert_le(lean_object* v_c_3064_, lean_object* v_a_3065_, lean_object* v_a_3066_, lean_object* v_a_3067_, lean_object* v_a_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_){
_start:
{
lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3107_; lean_object* v___y_3108_; lean_object* v___y_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3126_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___x_3148_; 
v___x_3148_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_3065_, v_a_3073_);
if (lean_obj_tag(v___x_3148_) == 0)
{
lean_object* v_a_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3285_; 
v_a_3149_ = lean_ctor_get(v___x_3148_, 0);
v_isSharedCheck_3285_ = !lean_is_exclusive(v___x_3148_);
if (v_isSharedCheck_3285_ == 0)
{
v___x_3151_ = v___x_3148_;
v_isShared_3152_ = v_isSharedCheck_3285_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_a_3149_);
lean_dec(v___x_3148_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3285_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
uint8_t v___x_3153_; 
v___x_3153_ = lean_unbox(v_a_3149_);
lean_dec(v_a_3149_);
if (v___x_3153_ == 0)
{
lean_object* v_options_3154_; lean_object* v_inheritedTraceOptions_3155_; uint8_t v_hasTrace_3156_; lean_object* v___y_3158_; lean_object* v___y_3159_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3162_; lean_object* v___y_3163_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___y_3167_; 
lean_del_object(v___x_3151_);
v_options_3154_ = lean_ctor_get(v_a_3073_, 2);
v_inheritedTraceOptions_3155_ = lean_ctor_get(v_a_3073_, 13);
v_hasTrace_3156_ = lean_ctor_get_uint8(v_options_3154_, sizeof(void*)*1);
if (v_hasTrace_3156_ == 0)
{
v___y_3158_ = v_a_3065_;
v___y_3159_ = v_a_3066_;
v___y_3160_ = v_a_3067_;
v___y_3161_ = v_a_3068_;
v___y_3162_ = v_a_3069_;
v___y_3163_ = v_a_3070_;
v___y_3164_ = v_a_3071_;
v___y_3165_ = v_a_3072_;
v___y_3166_ = v_a_3073_;
v___y_3167_ = v_a_3074_;
goto v___jp_3157_;
}
else
{
lean_object* v___x_3267_; lean_object* v___x_3268_; uint8_t v___x_3269_; 
v___x_3267_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__10));
v___x_3268_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11);
v___x_3269_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3155_, v_options_3154_, v___x_3268_);
if (v___x_3269_ == 0)
{
v___y_3158_ = v_a_3065_;
v___y_3159_ = v_a_3066_;
v___y_3160_ = v_a_3067_;
v___y_3161_ = v_a_3068_;
v___y_3162_ = v_a_3069_;
v___y_3163_ = v_a_3070_;
v___y_3164_ = v_a_3071_;
v___y_3165_ = v_a_3072_;
v___y_3166_ = v_a_3073_;
v___y_3167_ = v_a_3074_;
goto v___jp_3157_;
}
else
{
lean_object* v___x_3270_; 
lean_inc_ref(v_c_3064_);
v___x_3270_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_3064_, v_a_3065_, v_a_3073_);
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_object* v_a_3271_; lean_object* v___x_3272_; 
v_a_3271_ = lean_ctor_get(v___x_3270_, 0);
lean_inc(v_a_3271_);
lean_dec_ref(v___x_3270_);
v___x_3272_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3267_, v_a_3271_, v_a_3071_, v_a_3072_, v_a_3073_, v_a_3074_);
if (lean_obj_tag(v___x_3272_) == 0)
{
lean_dec_ref(v___x_3272_);
v___y_3158_ = v_a_3065_;
v___y_3159_ = v_a_3066_;
v___y_3160_ = v_a_3067_;
v___y_3161_ = v_a_3068_;
v___y_3162_ = v_a_3069_;
v___y_3163_ = v_a_3070_;
v___y_3164_ = v_a_3071_;
v___y_3165_ = v_a_3072_;
v___y_3166_ = v_a_3073_;
v___y_3167_ = v_a_3074_;
goto v___jp_3157_;
}
else
{
lean_dec(v_a_3074_);
lean_dec_ref(v_a_3073_);
lean_dec(v_a_3072_);
lean_dec_ref(v_a_3071_);
lean_dec(v_a_3070_);
lean_dec_ref(v_a_3069_);
lean_dec(v_a_3068_);
lean_dec_ref(v_a_3067_);
lean_dec(v_a_3066_);
lean_dec(v_a_3065_);
lean_dec_ref(v_c_3064_);
return v___x_3272_;
}
}
else
{
lean_object* v_a_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3280_; 
lean_dec(v_a_3074_);
lean_dec_ref(v_a_3073_);
lean_dec(v_a_3072_);
lean_dec_ref(v_a_3071_);
lean_dec(v_a_3070_);
lean_dec_ref(v_a_3069_);
lean_dec(v_a_3068_);
lean_dec_ref(v_a_3067_);
lean_dec(v_a_3066_);
lean_dec(v_a_3065_);
lean_dec_ref(v_c_3064_);
v_a_3273_ = lean_ctor_get(v___x_3270_, 0);
v_isSharedCheck_3280_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3280_ == 0)
{
v___x_3275_ = v___x_3270_;
v_isShared_3276_ = v_isSharedCheck_3280_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_a_3273_);
lean_dec(v___x_3270_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3280_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
lean_object* v___x_3278_; 
if (v_isShared_3276_ == 0)
{
v___x_3278_ = v___x_3275_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v_a_3273_);
v___x_3278_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
return v___x_3278_;
}
}
}
}
}
v___jp_3157_:
{
lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3168_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_norm(v_c_3064_);
lean_inc_ref(v___y_3166_);
v___x_3169_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts(v___x_3168_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
if (lean_obj_tag(v___x_3169_) == 0)
{
lean_object* v_a_3170_; lean_object* v_p_3171_; uint8_t v___x_3172_; 
v_a_3170_ = lean_ctor_get(v___x_3169_, 0);
lean_inc(v_a_3170_);
lean_dec_ref(v___x_3169_);
v_p_3171_ = lean_ctor_get(v_a_3170_, 0);
v___x_3172_ = l_Int_Linear_Poly_isUnsatLe(v_p_3171_);
if (v___x_3172_ == 0)
{
uint8_t v___x_3173_; 
v___x_3173_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(v_a_3170_);
if (v___x_3173_ == 0)
{
if (lean_obj_tag(v_p_3171_) == 1)
{
lean_object* v_k_3174_; lean_object* v_v_3175_; lean_object* v___x_3176_; 
v_k_3174_ = lean_ctor_get(v_p_3171_, 0);
lean_inc(v_k_3174_);
v_v_3175_ = lean_ctor_get(v_p_3171_, 1);
lean_inc(v_v_3175_);
lean_inc(v_a_3170_);
v___x_3176_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq(v_a_3170_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
if (lean_obj_tag(v___x_3176_) == 0)
{
lean_object* v_a_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3215_; 
v_a_3177_ = lean_ctor_get(v___x_3176_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___x_3176_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3179_ = v___x_3176_;
v_isShared_3180_ = v_isSharedCheck_3215_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_a_3177_);
lean_dec(v___x_3176_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3215_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
uint8_t v___x_3181_; 
v___x_3181_ = lean_unbox(v_a_3177_);
lean_dec(v_a_3177_);
if (v___x_3181_ == 0)
{
lean_object* v___x_3182_; 
lean_del_object(v___x_3179_);
v___x_3182_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(v_a_3170_, v___y_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
lean_dec(v___y_3163_);
lean_dec_ref(v___y_3162_);
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3160_);
lean_dec(v___y_3159_);
if (lean_obj_tag(v___x_3182_) == 0)
{
lean_object* v_options_3183_; lean_object* v_a_3184_; lean_object* v_inheritedTraceOptions_3185_; uint8_t v_hasTrace_3186_; lean_object* v___f_3187_; lean_object* v___f_3188_; 
v_options_3183_ = lean_ctor_get(v___y_3166_, 2);
v_a_3184_ = lean_ctor_get(v___x_3182_, 0);
lean_inc_n(v_a_3184_, 3);
lean_dec_ref(v___x_3182_);
v_inheritedTraceOptions_3185_ = lean_ctor_get(v___y_3166_, 13);
v_hasTrace_3186_ = lean_ctor_get_uint8(v_options_3183_, sizeof(void*)*1);
lean_inc_n(v_v_3175_, 2);
v___f_3187_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3187_, 0, v_a_3184_);
lean_closure_set(v___f_3187_, 1, v_v_3175_);
v___f_3188_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3188_, 0, v_a_3184_);
lean_closure_set(v___f_3188_, 1, v_v_3175_);
if (v_hasTrace_3186_ == 0)
{
v___y_3107_ = v___f_3187_;
v___y_3108_ = v_v_3175_;
v___y_3109_ = v_a_3184_;
v___y_3110_ = v___f_3188_;
v___y_3111_ = v_k_3174_;
v___y_3112_ = v___y_3158_;
v___y_3113_ = v___y_3164_;
v___y_3114_ = v___y_3165_;
v___y_3115_ = v___y_3166_;
v___y_3116_ = v___y_3167_;
goto v___jp_3106_;
}
else
{
lean_object* v___x_3189_; lean_object* v___x_3190_; uint8_t v___x_3191_; 
v___x_3189_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2));
v___x_3190_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3);
v___x_3191_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3185_, v_options_3183_, v___x_3190_);
if (v___x_3191_ == 0)
{
v___y_3107_ = v___f_3187_;
v___y_3108_ = v_v_3175_;
v___y_3109_ = v_a_3184_;
v___y_3110_ = v___f_3188_;
v___y_3111_ = v_k_3174_;
v___y_3112_ = v___y_3158_;
v___y_3113_ = v___y_3164_;
v___y_3114_ = v___y_3165_;
v___y_3115_ = v___y_3166_;
v___y_3116_ = v___y_3167_;
goto v___jp_3106_;
}
else
{
lean_object* v___x_3192_; 
lean_inc(v_a_3184_);
v___x_3192_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_a_3184_, v___y_3158_, v___y_3166_);
if (lean_obj_tag(v___x_3192_) == 0)
{
lean_object* v_a_3193_; lean_object* v___x_3194_; 
v_a_3193_ = lean_ctor_get(v___x_3192_, 0);
lean_inc(v_a_3193_);
lean_dec_ref(v___x_3192_);
v___x_3194_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3189_, v_a_3193_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
if (lean_obj_tag(v___x_3194_) == 0)
{
lean_dec_ref(v___x_3194_);
v___y_3107_ = v___f_3187_;
v___y_3108_ = v_v_3175_;
v___y_3109_ = v_a_3184_;
v___y_3110_ = v___f_3188_;
v___y_3111_ = v_k_3174_;
v___y_3112_ = v___y_3158_;
v___y_3113_ = v___y_3164_;
v___y_3114_ = v___y_3165_;
v___y_3115_ = v___y_3166_;
v___y_3116_ = v___y_3167_;
goto v___jp_3106_;
}
else
{
lean_dec_ref(v___f_3188_);
lean_dec_ref(v___f_3187_);
lean_dec(v_a_3184_);
lean_dec(v_v_3175_);
lean_dec(v_k_3174_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec(v___y_3158_);
return v___x_3194_;
}
}
else
{
lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3202_; 
lean_dec_ref(v___f_3188_);
lean_dec_ref(v___f_3187_);
lean_dec(v_a_3184_);
lean_dec(v_v_3175_);
lean_dec(v_k_3174_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec(v___y_3158_);
v_a_3195_ = lean_ctor_get(v___x_3192_, 0);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3192_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3197_ = v___x_3192_;
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_a_3195_);
lean_dec(v___x_3192_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v___x_3200_; 
if (v_isShared_3198_ == 0)
{
v___x_3200_ = v___x_3197_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3201_; 
v_reuseFailAlloc_3201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3201_, 0, v_a_3195_);
v___x_3200_ = v_reuseFailAlloc_3201_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
return v___x_3200_;
}
}
}
}
}
}
else
{
lean_object* v_a_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3210_; 
lean_dec(v_v_3175_);
lean_dec(v_k_3174_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec(v___y_3158_);
v_a_3203_ = lean_ctor_get(v___x_3182_, 0);
v_isSharedCheck_3210_ = !lean_is_exclusive(v___x_3182_);
if (v_isSharedCheck_3210_ == 0)
{
v___x_3205_ = v___x_3182_;
v_isShared_3206_ = v_isSharedCheck_3210_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_a_3203_);
lean_dec(v___x_3182_);
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
else
{
lean_object* v___x_3211_; lean_object* v___x_3213_; 
lean_dec(v_v_3175_);
lean_dec(v_k_3174_);
lean_dec(v_a_3170_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec(v___y_3163_);
lean_dec_ref(v___y_3162_);
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3160_);
lean_dec(v___y_3159_);
lean_dec(v___y_3158_);
v___x_3211_ = lean_box(0);
if (v_isShared_3180_ == 0)
{
lean_ctor_set(v___x_3179_, 0, v___x_3211_);
v___x_3213_ = v___x_3179_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v___x_3211_);
v___x_3213_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
return v___x_3213_;
}
}
}
}
else
{
lean_object* v_a_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3223_; 
lean_dec(v_v_3175_);
lean_dec(v_k_3174_);
lean_dec(v_a_3170_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec(v___y_3163_);
lean_dec_ref(v___y_3162_);
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3160_);
lean_dec(v___y_3159_);
lean_dec(v___y_3158_);
v_a_3216_ = lean_ctor_get(v___x_3176_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___x_3176_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3218_ = v___x_3176_;
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_a_3216_);
lean_dec(v___x_3176_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v___x_3221_; 
if (v_isShared_3219_ == 0)
{
v___x_3221_ = v___x_3218_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_a_3216_);
v___x_3221_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
return v___x_3221_;
}
}
}
}
else
{
lean_object* v___x_3224_; 
lean_dec(v___y_3163_);
lean_dec_ref(v___y_3162_);
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3160_);
lean_dec(v___y_3159_);
v___x_3224_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_a_3170_, v___y_3158_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec(v___y_3158_);
return v___x_3224_;
}
}
else
{
lean_object* v_options_3225_; uint8_t v_hasTrace_3226_; 
lean_dec(v___y_3163_);
lean_dec_ref(v___y_3162_);
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3160_);
lean_dec(v___y_3159_);
v_options_3225_ = lean_ctor_get(v___y_3166_, 2);
v_hasTrace_3226_ = lean_ctor_get_uint8(v_options_3225_, sizeof(void*)*1);
if (v_hasTrace_3226_ == 0)
{
lean_dec(v_a_3170_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec(v___y_3158_);
goto v___jp_3076_;
}
else
{
lean_object* v_inheritedTraceOptions_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; uint8_t v___x_3230_; 
v_inheritedTraceOptions_3227_ = lean_ctor_get(v___y_3166_, 13);
v___x_3228_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5));
v___x_3229_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6);
v___x_3230_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3227_, v_options_3225_, v___x_3229_);
if (v___x_3230_ == 0)
{
lean_dec(v_a_3170_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec(v___y_3158_);
goto v___jp_3076_;
}
else
{
lean_object* v___x_3231_; 
v___x_3231_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_a_3170_, v___y_3158_, v___y_3166_);
lean_dec(v___y_3158_);
if (lean_obj_tag(v___x_3231_) == 0)
{
lean_object* v_a_3232_; lean_object* v___x_3233_; 
v_a_3232_ = lean_ctor_get(v___x_3231_, 0);
lean_inc(v_a_3232_);
lean_dec_ref(v___x_3231_);
v___x_3233_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3228_, v_a_3232_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
if (lean_obj_tag(v___x_3233_) == 0)
{
lean_dec_ref(v___x_3233_);
goto v___jp_3076_;
}
else
{
return v___x_3233_;
}
}
else
{
lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3241_; 
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
v_a_3234_ = lean_ctor_get(v___x_3231_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3236_ = v___x_3231_;
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_a_3234_);
lean_dec(v___x_3231_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3239_; 
if (v_isShared_3237_ == 0)
{
v___x_3239_ = v___x_3236_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_a_3234_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
}
}
}
}
}
else
{
lean_object* v_options_3242_; uint8_t v_hasTrace_3243_; 
v_options_3242_ = lean_ctor_get(v___y_3166_, 2);
v_hasTrace_3243_ = lean_ctor_get_uint8(v_options_3242_, sizeof(void*)*1);
if (v_hasTrace_3243_ == 0)
{
v___y_3126_ = v_a_3170_;
v___y_3127_ = v___y_3158_;
v___y_3128_ = v___y_3159_;
v___y_3129_ = v___y_3160_;
v___y_3130_ = v___y_3161_;
v___y_3131_ = v___y_3162_;
v___y_3132_ = v___y_3163_;
v___y_3133_ = v___y_3164_;
v___y_3134_ = v___y_3165_;
v___y_3135_ = v___y_3166_;
v___y_3136_ = v___y_3167_;
goto v___jp_3125_;
}
else
{
lean_object* v_inheritedTraceOptions_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; uint8_t v___x_3247_; 
v_inheritedTraceOptions_3244_ = lean_ctor_get(v___y_3166_, 13);
v___x_3245_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__8));
v___x_3246_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9);
v___x_3247_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3244_, v_options_3242_, v___x_3246_);
if (v___x_3247_ == 0)
{
v___y_3126_ = v_a_3170_;
v___y_3127_ = v___y_3158_;
v___y_3128_ = v___y_3159_;
v___y_3129_ = v___y_3160_;
v___y_3130_ = v___y_3161_;
v___y_3131_ = v___y_3162_;
v___y_3132_ = v___y_3163_;
v___y_3133_ = v___y_3164_;
v___y_3134_ = v___y_3165_;
v___y_3135_ = v___y_3166_;
v___y_3136_ = v___y_3167_;
goto v___jp_3125_;
}
else
{
lean_object* v___x_3248_; 
lean_inc(v_a_3170_);
v___x_3248_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_a_3170_, v___y_3158_, v___y_3166_);
if (lean_obj_tag(v___x_3248_) == 0)
{
lean_object* v_a_3249_; lean_object* v___x_3250_; 
v_a_3249_ = lean_ctor_get(v___x_3248_, 0);
lean_inc(v_a_3249_);
lean_dec_ref(v___x_3248_);
v___x_3250_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3245_, v_a_3249_, v___y_3164_, v___y_3165_, v___y_3166_, v___y_3167_);
if (lean_obj_tag(v___x_3250_) == 0)
{
lean_dec_ref(v___x_3250_);
v___y_3126_ = v_a_3170_;
v___y_3127_ = v___y_3158_;
v___y_3128_ = v___y_3159_;
v___y_3129_ = v___y_3160_;
v___y_3130_ = v___y_3161_;
v___y_3131_ = v___y_3162_;
v___y_3132_ = v___y_3163_;
v___y_3133_ = v___y_3164_;
v___y_3134_ = v___y_3165_;
v___y_3135_ = v___y_3166_;
v___y_3136_ = v___y_3167_;
goto v___jp_3125_;
}
else
{
lean_dec(v_a_3170_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec(v___y_3163_);
lean_dec_ref(v___y_3162_);
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3160_);
lean_dec(v___y_3159_);
lean_dec(v___y_3158_);
return v___x_3250_;
}
}
else
{
lean_object* v_a_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3258_; 
lean_dec(v_a_3170_);
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec(v___y_3163_);
lean_dec_ref(v___y_3162_);
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3160_);
lean_dec(v___y_3159_);
lean_dec(v___y_3158_);
v_a_3251_ = lean_ctor_get(v___x_3248_, 0);
v_isSharedCheck_3258_ = !lean_is_exclusive(v___x_3248_);
if (v_isSharedCheck_3258_ == 0)
{
v___x_3253_ = v___x_3248_;
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_a_3251_);
lean_dec(v___x_3248_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v___x_3256_; 
if (v_isShared_3254_ == 0)
{
v___x_3256_ = v___x_3253_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v_a_3251_);
v___x_3256_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
return v___x_3256_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3259_; lean_object* v___x_3261_; uint8_t v_isShared_3262_; uint8_t v_isSharedCheck_3266_; 
lean_dec(v___y_3167_);
lean_dec_ref(v___y_3166_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec(v___y_3163_);
lean_dec_ref(v___y_3162_);
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3160_);
lean_dec(v___y_3159_);
lean_dec(v___y_3158_);
v_a_3259_ = lean_ctor_get(v___x_3169_, 0);
v_isSharedCheck_3266_ = !lean_is_exclusive(v___x_3169_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3261_ = v___x_3169_;
v_isShared_3262_ = v_isSharedCheck_3266_;
goto v_resetjp_3260_;
}
else
{
lean_inc(v_a_3259_);
lean_dec(v___x_3169_);
v___x_3261_ = lean_box(0);
v_isShared_3262_ = v_isSharedCheck_3266_;
goto v_resetjp_3260_;
}
v_resetjp_3260_:
{
lean_object* v___x_3264_; 
if (v_isShared_3262_ == 0)
{
v___x_3264_ = v___x_3261_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v_a_3259_);
v___x_3264_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
return v___x_3264_;
}
}
}
}
}
else
{
lean_object* v___x_3281_; lean_object* v___x_3283_; 
lean_dec(v_a_3074_);
lean_dec_ref(v_a_3073_);
lean_dec(v_a_3072_);
lean_dec_ref(v_a_3071_);
lean_dec(v_a_3070_);
lean_dec_ref(v_a_3069_);
lean_dec(v_a_3068_);
lean_dec_ref(v_a_3067_);
lean_dec(v_a_3066_);
lean_dec(v_a_3065_);
lean_dec_ref(v_c_3064_);
v___x_3281_ = lean_box(0);
if (v_isShared_3152_ == 0)
{
lean_ctor_set(v___x_3151_, 0, v___x_3281_);
v___x_3283_ = v___x_3151_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3284_; 
v_reuseFailAlloc_3284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3284_, 0, v___x_3281_);
v___x_3283_ = v_reuseFailAlloc_3284_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
return v___x_3283_;
}
}
}
}
else
{
lean_object* v_a_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3293_; 
lean_dec(v_a_3074_);
lean_dec_ref(v_a_3073_);
lean_dec(v_a_3072_);
lean_dec_ref(v_a_3071_);
lean_dec(v_a_3070_);
lean_dec_ref(v_a_3069_);
lean_dec(v_a_3068_);
lean_dec_ref(v_a_3067_);
lean_dec(v_a_3066_);
lean_dec(v_a_3065_);
lean_dec_ref(v_c_3064_);
v_a_3286_ = lean_ctor_get(v___x_3148_, 0);
v_isSharedCheck_3293_ = !lean_is_exclusive(v___x_3148_);
if (v_isSharedCheck_3293_ == 0)
{
v___x_3288_ = v___x_3148_;
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_a_3286_);
lean_dec(v___x_3148_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
lean_object* v___x_3291_; 
if (v_isShared_3289_ == 0)
{
v___x_3291_ = v___x_3288_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v_a_3286_);
v___x_3291_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
return v___x_3291_;
}
}
}
v___jp_3076_:
{
lean_object* v___x_3077_; lean_object* v___x_3078_; 
v___x_3077_ = lean_box(0);
v___x_3078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3078_, 0, v___x_3077_);
return v___x_3078_;
}
v___jp_3079_:
{
lean_object* v___x_3084_; 
v___x_3084_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(v___y_3081_, v___y_3082_, v___y_3083_);
lean_dec_ref(v___y_3083_);
if (lean_obj_tag(v___x_3084_) == 0)
{
lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3097_; 
v_a_3085_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3097_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3097_ == 0)
{
v___x_3087_ = v___x_3084_;
v_isShared_3088_ = v_isSharedCheck_3097_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_3084_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3097_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
uint8_t v___x_3089_; uint8_t v___x_3090_; uint8_t v___x_3091_; 
v___x_3089_ = 0;
v___x_3090_ = lean_unbox(v_a_3085_);
lean_dec(v_a_3085_);
v___x_3091_ = l_Lean_instBEqLBool_beq(v___x_3090_, v___x_3089_);
if (v___x_3091_ == 0)
{
lean_object* v___x_3092_; lean_object* v___x_3094_; 
lean_dec(v___y_3082_);
lean_dec(v___y_3080_);
v___x_3092_ = lean_box(0);
if (v_isShared_3088_ == 0)
{
lean_ctor_set(v___x_3087_, 0, v___x_3092_);
v___x_3094_ = v___x_3087_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v___x_3092_);
v___x_3094_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
return v___x_3094_;
}
}
else
{
lean_object* v___x_3096_; 
lean_del_object(v___x_3087_);
v___x_3096_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v___y_3080_, v___y_3082_);
lean_dec(v___y_3082_);
return v___x_3096_;
}
}
}
else
{
lean_object* v_a_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3105_; 
lean_dec(v___y_3082_);
lean_dec(v___y_3080_);
v_a_3098_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3105_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3100_ = v___x_3084_;
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_a_3098_);
lean_dec(v___x_3084_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___x_3103_; 
if (v_isShared_3101_ == 0)
{
v___x_3103_ = v___x_3100_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_a_3098_);
v___x_3103_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
return v___x_3103_;
}
}
}
}
v___jp_3106_:
{
lean_object* v_p_3117_; lean_object* v___x_3118_; 
v_p_3117_ = lean_ctor_get(v___y_3109_, 0);
lean_inc_ref(v_p_3117_);
v___x_3118_ = l_Int_Linear_Poly_updateOccs___redArg(v_p_3117_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_);
lean_dec(v___y_3116_);
lean_dec(v___y_3114_);
lean_dec_ref(v___y_3113_);
if (lean_obj_tag(v___x_3118_) == 0)
{
lean_object* v___x_3119_; uint8_t v___x_3120_; 
lean_dec_ref(v___x_3118_);
v___x_3119_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9);
v___x_3120_ = lean_int_dec_lt(v___y_3111_, v___x_3119_);
lean_dec(v___y_3111_);
if (v___x_3120_ == 0)
{
lean_object* v___x_3121_; lean_object* v___x_3122_; 
lean_dec_ref(v___y_3107_);
v___x_3121_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_3122_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3121_, v___y_3110_, v___y_3112_);
if (lean_obj_tag(v___x_3122_) == 0)
{
lean_dec_ref(v___x_3122_);
v___y_3080_ = v___y_3108_;
v___y_3081_ = v___y_3109_;
v___y_3082_ = v___y_3112_;
v___y_3083_ = v___y_3115_;
goto v___jp_3079_;
}
else
{
lean_dec_ref(v___y_3115_);
lean_dec(v___y_3112_);
lean_dec_ref(v___y_3109_);
lean_dec(v___y_3108_);
return v___x_3122_;
}
}
else
{
lean_object* v___x_3123_; lean_object* v___x_3124_; 
lean_dec_ref(v___y_3110_);
v___x_3123_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_3124_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3123_, v___y_3107_, v___y_3112_);
if (lean_obj_tag(v___x_3124_) == 0)
{
lean_dec_ref(v___x_3124_);
v___y_3080_ = v___y_3108_;
v___y_3081_ = v___y_3109_;
v___y_3082_ = v___y_3112_;
v___y_3083_ = v___y_3115_;
goto v___jp_3079_;
}
else
{
lean_dec_ref(v___y_3115_);
lean_dec(v___y_3112_);
lean_dec_ref(v___y_3109_);
lean_dec(v___y_3108_);
return v___x_3124_;
}
}
}
else
{
lean_dec_ref(v___y_3115_);
lean_dec(v___y_3112_);
lean_dec(v___y_3111_);
lean_dec_ref(v___y_3110_);
lean_dec_ref(v___y_3109_);
lean_dec(v___y_3108_);
lean_dec_ref(v___y_3107_);
return v___x_3118_;
}
}
v___jp_3125_:
{
lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3137_, 0, v___y_3126_);
v___x_3138_ = l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(v___x_3137_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_);
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
if (lean_obj_tag(v___x_3138_) == 0)
{
lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3146_; 
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3138_);
if (v_isSharedCheck_3146_ == 0)
{
lean_object* v_unused_3147_; 
v_unused_3147_ = lean_ctor_get(v___x_3138_, 0);
lean_dec(v_unused_3147_);
v___x_3140_ = v___x_3138_;
v_isShared_3141_ = v_isSharedCheck_3146_;
goto v_resetjp_3139_;
}
else
{
lean_dec(v___x_3138_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3146_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v___x_3142_; lean_object* v___x_3144_; 
v___x_3142_ = lean_box(0);
if (v_isShared_3141_ == 0)
{
lean_ctor_set(v___x_3140_, 0, v___x_3142_);
v___x_3144_ = v___x_3140_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v___x_3142_);
v___x_3144_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
return v___x_3144_;
}
}
}
else
{
return v___x_3138_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___boxed(lean_object* v_c_3294_, lean_object* v_a_3295_, lean_object* v_a_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_){
_start:
{
lean_object* v_res_3306_; 
v_res_3306_ = lean_grind_cutsat_assert_le(v_c_3294_, v_a_3295_, v_a_3296_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_, v_a_3303_, v_a_3304_);
return v_res_3306_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1(void){
_start:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; 
v___x_3308_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__0));
v___x_3309_ = l_Lean_stringToMessageData(v___x_3308_);
return v___x_3309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(lean_object* v_e_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_){
_start:
{
lean_object* v___x_3318_; 
v___x_3318_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_3311_);
if (lean_obj_tag(v___x_3318_) == 0)
{
lean_object* v_a_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3332_; 
v_a_3319_ = lean_ctor_get(v___x_3318_, 0);
v_isSharedCheck_3332_ = !lean_is_exclusive(v___x_3318_);
if (v_isSharedCheck_3332_ == 0)
{
v___x_3321_ = v___x_3318_;
v_isShared_3322_ = v_isSharedCheck_3332_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_a_3319_);
lean_dec(v___x_3318_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3332_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
uint8_t v___x_3323_; 
v___x_3323_ = lean_unbox(v_a_3319_);
lean_dec(v_a_3319_);
if (v___x_3323_ == 0)
{
lean_object* v___x_3324_; lean_object* v___x_3326_; 
lean_dec_ref(v_e_3310_);
v___x_3324_ = lean_box(0);
if (v_isShared_3322_ == 0)
{
lean_ctor_set(v___x_3321_, 0, v___x_3324_);
v___x_3326_ = v___x_3321_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3327_, 0, v___x_3324_);
v___x_3326_ = v_reuseFailAlloc_3327_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
return v___x_3326_;
}
}
else
{
lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; 
lean_del_object(v___x_3321_);
v___x_3328_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1);
v___x_3329_ = l_Lean_indentExpr(v_e_3310_);
v___x_3330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3330_, 0, v___x_3328_);
lean_ctor_set(v___x_3330_, 1, v___x_3329_);
v___x_3331_ = l_Lean_Meta_Sym_reportIssue(v___x_3330_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_);
return v___x_3331_;
}
}
}
else
{
lean_object* v_a_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3340_; 
lean_dec_ref(v_e_3310_);
v_a_3333_ = lean_ctor_get(v___x_3318_, 0);
v_isSharedCheck_3340_ = !lean_is_exclusive(v___x_3318_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3335_ = v___x_3318_;
v_isShared_3336_ = v_isSharedCheck_3340_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_a_3333_);
lean_dec(v___x_3318_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3340_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v___x_3338_; 
if (v_isShared_3336_ == 0)
{
v___x_3338_ = v___x_3335_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v_a_3333_);
v___x_3338_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
return v___x_3338_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___boxed(lean_object* v_e_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_){
_start:
{
lean_object* v_res_3349_; 
v_res_3349_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(v_e_3341_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_);
lean_dec(v_a_3347_);
lean_dec_ref(v_a_3346_);
lean_dec(v_a_3345_);
lean_dec_ref(v_a_3344_);
lean_dec(v_a_3343_);
lean_dec_ref(v_a_3342_);
return v_res_3349_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized(lean_object* v_e_3350_, lean_object* v_a_3351_, lean_object* v_a_3352_, lean_object* v_a_3353_, lean_object* v_a_3354_, lean_object* v_a_3355_, lean_object* v_a_3356_, lean_object* v_a_3357_, lean_object* v_a_3358_, lean_object* v_a_3359_, lean_object* v_a_3360_){
_start:
{
lean_object* v___x_3362_; 
v___x_3362_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(v_e_3350_, v_a_3355_, v_a_3356_, v_a_3357_, v_a_3358_, v_a_3359_, v_a_3360_);
return v___x_3362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___boxed(lean_object* v_e_3363_, lean_object* v_a_3364_, lean_object* v_a_3365_, lean_object* v_a_3366_, lean_object* v_a_3367_, lean_object* v_a_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_, lean_object* v_a_3374_){
_start:
{
lean_object* v_res_3375_; 
v_res_3375_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized(v_e_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_, v_a_3373_);
lean_dec(v_a_3373_);
lean_dec_ref(v_a_3372_);
lean_dec(v_a_3371_);
lean_dec_ref(v_a_3370_);
lean_dec(v_a_3369_);
lean_dec_ref(v_a_3368_);
lean_dec(v_a_3367_);
lean_dec_ref(v_a_3366_);
lean_dec(v_a_3365_);
lean_dec(v_a_3364_);
return v_res_3375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f(lean_object* v_e_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_, lean_object* v_a_3384_, lean_object* v_a_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_){
_start:
{
lean_object* v___x_3393_; 
lean_inc_ref(v_e_3381_);
v___x_3393_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3381_, v_a_3389_);
if (lean_obj_tag(v___x_3393_) == 0)
{
lean_object* v_a_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3509_; 
v_a_3394_ = lean_ctor_get(v___x_3393_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_3393_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3396_ = v___x_3393_;
v_isShared_3397_ = v_isSharedCheck_3509_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_a_3394_);
lean_dec(v___x_3393_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3509_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v___x_3403_; uint8_t v___x_3404_; 
v___x_3403_ = l_Lean_Expr_cleanupAnnotations(v_a_3394_);
v___x_3404_ = l_Lean_Expr_isApp(v___x_3403_);
if (v___x_3404_ == 0)
{
lean_dec_ref(v___x_3403_);
lean_dec_ref(v_e_3381_);
goto v___jp_3398_;
}
else
{
lean_object* v_arg_3405_; lean_object* v___x_3406_; uint8_t v___x_3407_; 
v_arg_3405_ = lean_ctor_get(v___x_3403_, 1);
lean_inc_ref(v_arg_3405_);
v___x_3406_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3403_);
v___x_3407_ = l_Lean_Expr_isApp(v___x_3406_);
if (v___x_3407_ == 0)
{
lean_dec_ref(v___x_3406_);
lean_dec_ref(v_arg_3405_);
lean_dec_ref(v_e_3381_);
goto v___jp_3398_;
}
else
{
lean_object* v_arg_3408_; lean_object* v___x_3409_; uint8_t v___x_3410_; 
v_arg_3408_ = lean_ctor_get(v___x_3406_, 1);
lean_inc_ref(v_arg_3408_);
v___x_3409_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3406_);
v___x_3410_ = l_Lean_Expr_isApp(v___x_3409_);
if (v___x_3410_ == 0)
{
lean_dec_ref(v___x_3409_);
lean_dec_ref(v_arg_3408_);
lean_dec_ref(v_arg_3405_);
lean_dec_ref(v_e_3381_);
goto v___jp_3398_;
}
else
{
lean_object* v_arg_3411_; lean_object* v___x_3412_; uint8_t v___x_3413_; 
v_arg_3411_ = lean_ctor_get(v___x_3409_, 1);
lean_inc_ref(v_arg_3411_);
v___x_3412_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3409_);
v___x_3413_ = l_Lean_Expr_isApp(v___x_3412_);
if (v___x_3413_ == 0)
{
lean_dec_ref(v___x_3412_);
lean_dec_ref(v_arg_3411_);
lean_dec_ref(v_arg_3408_);
lean_dec_ref(v_arg_3405_);
lean_dec_ref(v_e_3381_);
goto v___jp_3398_;
}
else
{
lean_object* v___x_3414_; lean_object* v___x_3415_; uint8_t v___x_3416_; 
v___x_3414_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3412_);
v___x_3415_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2));
v___x_3416_ = l_Lean_Expr_isConstOf(v___x_3414_, v___x_3415_);
lean_dec_ref(v___x_3414_);
if (v___x_3416_ == 0)
{
lean_dec_ref(v_arg_3411_);
lean_dec_ref(v_arg_3408_);
lean_dec_ref(v_arg_3405_);
lean_dec_ref(v_e_3381_);
goto v___jp_3398_;
}
else
{
lean_object* v___x_3417_; 
lean_del_object(v___x_3396_);
v___x_3417_ = l_Lean_Meta_Structural_isInstLEInt___redArg(v_arg_3411_, v_a_3389_);
if (lean_obj_tag(v___x_3417_) == 0)
{
lean_object* v_a_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3500_; 
v_a_3418_ = lean_ctor_get(v___x_3417_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3417_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3420_ = v___x_3417_;
v_isShared_3421_ = v_isSharedCheck_3500_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_a_3418_);
lean_dec(v___x_3417_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3500_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
uint8_t v___x_3422_; 
v___x_3422_ = lean_unbox(v_a_3418_);
lean_dec(v_a_3418_);
if (v___x_3422_ == 0)
{
lean_object* v___x_3423_; lean_object* v___x_3425_; 
lean_dec_ref(v_arg_3408_);
lean_dec_ref(v_arg_3405_);
lean_dec_ref(v_e_3381_);
v___x_3423_ = lean_box(0);
if (v_isShared_3421_ == 0)
{
lean_ctor_set(v___x_3420_, 0, v___x_3423_);
v___x_3425_ = v___x_3420_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v___x_3423_);
v___x_3425_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
return v___x_3425_;
}
}
else
{
lean_object* v___x_3427_; 
lean_del_object(v___x_3420_);
v___x_3427_ = l_Lean_Meta_getIntValue_x3f(v_arg_3405_, v_a_3388_, v_a_3389_, v_a_3390_, v_a_3391_);
if (lean_obj_tag(v___x_3427_) == 0)
{
lean_object* v_a_3428_; 
v_a_3428_ = lean_ctor_get(v___x_3427_, 0);
lean_inc(v_a_3428_);
lean_dec_ref(v___x_3427_);
if (lean_obj_tag(v_a_3428_) == 1)
{
lean_object* v_val_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3473_; 
v_val_3429_ = lean_ctor_get(v_a_3428_, 0);
v_isSharedCheck_3473_ = !lean_is_exclusive(v_a_3428_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3431_ = v_a_3428_;
v_isShared_3432_ = v_isSharedCheck_3473_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_val_3429_);
lean_dec(v_a_3428_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3473_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v___x_3433_; uint8_t v___x_3434_; 
v___x_3433_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9);
v___x_3434_ = lean_int_dec_eq(v_val_3429_, v___x_3433_);
lean_dec(v_val_3429_);
if (v___x_3434_ == 0)
{
lean_object* v___x_3435_; 
lean_del_object(v___x_3431_);
lean_dec_ref(v_arg_3408_);
v___x_3435_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(v_e_3381_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_, v_a_3390_, v_a_3391_);
if (lean_obj_tag(v___x_3435_) == 0)
{
lean_object* v___x_3437_; uint8_t v_isShared_3438_; uint8_t v_isSharedCheck_3443_; 
v_isSharedCheck_3443_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3443_ == 0)
{
lean_object* v_unused_3444_; 
v_unused_3444_ = lean_ctor_get(v___x_3435_, 0);
lean_dec(v_unused_3444_);
v___x_3437_ = v___x_3435_;
v_isShared_3438_ = v_isSharedCheck_3443_;
goto v_resetjp_3436_;
}
else
{
lean_dec(v___x_3435_);
v___x_3437_ = lean_box(0);
v_isShared_3438_ = v_isSharedCheck_3443_;
goto v_resetjp_3436_;
}
v_resetjp_3436_:
{
lean_object* v___x_3439_; lean_object* v___x_3441_; 
v___x_3439_ = lean_box(0);
if (v_isShared_3438_ == 0)
{
lean_ctor_set(v___x_3437_, 0, v___x_3439_);
v___x_3441_ = v___x_3437_;
goto v_reusejp_3440_;
}
else
{
lean_object* v_reuseFailAlloc_3442_; 
v_reuseFailAlloc_3442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3442_, 0, v___x_3439_);
v___x_3441_ = v_reuseFailAlloc_3442_;
goto v_reusejp_3440_;
}
v_reusejp_3440_:
{
return v___x_3441_;
}
}
}
else
{
lean_object* v_a_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3452_; 
v_a_3445_ = lean_ctor_get(v___x_3435_, 0);
v_isSharedCheck_3452_ = !lean_is_exclusive(v___x_3435_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3447_ = v___x_3435_;
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_a_3445_);
lean_dec(v___x_3435_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3450_; 
if (v_isShared_3448_ == 0)
{
v___x_3450_ = v___x_3447_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v_a_3445_);
v___x_3450_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
return v___x_3450_;
}
}
}
}
else
{
lean_object* v___x_3453_; 
lean_dec_ref(v_e_3381_);
v___x_3453_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(v_arg_3408_, v_a_3382_, v_a_3383_, v_a_3384_, v_a_3385_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_, v_a_3390_, v_a_3391_);
if (lean_obj_tag(v___x_3453_) == 0)
{
lean_object* v_a_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3464_; 
v_a_3454_ = lean_ctor_get(v___x_3453_, 0);
v_isSharedCheck_3464_ = !lean_is_exclusive(v___x_3453_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3456_ = v___x_3453_;
v_isShared_3457_ = v_isSharedCheck_3464_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_a_3454_);
lean_dec(v___x_3453_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3464_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
lean_object* v___x_3459_; 
if (v_isShared_3432_ == 0)
{
lean_ctor_set(v___x_3431_, 0, v_a_3454_);
v___x_3459_ = v___x_3431_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v_a_3454_);
v___x_3459_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
lean_object* v___x_3461_; 
if (v_isShared_3457_ == 0)
{
lean_ctor_set(v___x_3456_, 0, v___x_3459_);
v___x_3461_ = v___x_3456_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v___x_3459_);
v___x_3461_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
return v___x_3461_;
}
}
}
}
else
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3472_; 
lean_del_object(v___x_3431_);
v_a_3465_ = lean_ctor_get(v___x_3453_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3453_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3467_ = v___x_3453_;
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3453_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___x_3470_; 
if (v_isShared_3468_ == 0)
{
v___x_3470_ = v___x_3467_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_a_3465_);
v___x_3470_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
return v___x_3470_;
}
}
}
}
}
}
else
{
lean_object* v___x_3474_; 
lean_dec(v_a_3428_);
lean_dec_ref(v_arg_3408_);
v___x_3474_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(v_e_3381_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_, v_a_3390_, v_a_3391_);
if (lean_obj_tag(v___x_3474_) == 0)
{
lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3482_; 
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3474_);
if (v_isSharedCheck_3482_ == 0)
{
lean_object* v_unused_3483_; 
v_unused_3483_ = lean_ctor_get(v___x_3474_, 0);
lean_dec(v_unused_3483_);
v___x_3476_ = v___x_3474_;
v_isShared_3477_ = v_isSharedCheck_3482_;
goto v_resetjp_3475_;
}
else
{
lean_dec(v___x_3474_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3482_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
lean_object* v___x_3478_; lean_object* v___x_3480_; 
v___x_3478_ = lean_box(0);
if (v_isShared_3477_ == 0)
{
lean_ctor_set(v___x_3476_, 0, v___x_3478_);
v___x_3480_ = v___x_3476_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v___x_3478_);
v___x_3480_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
return v___x_3480_;
}
}
}
else
{
lean_object* v_a_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3491_; 
v_a_3484_ = lean_ctor_get(v___x_3474_, 0);
v_isSharedCheck_3491_ = !lean_is_exclusive(v___x_3474_);
if (v_isSharedCheck_3491_ == 0)
{
v___x_3486_ = v___x_3474_;
v_isShared_3487_ = v_isSharedCheck_3491_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_a_3484_);
lean_dec(v___x_3474_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3491_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v___x_3489_; 
if (v_isShared_3487_ == 0)
{
v___x_3489_ = v___x_3486_;
goto v_reusejp_3488_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v_a_3484_);
v___x_3489_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3488_;
}
v_reusejp_3488_:
{
return v___x_3489_;
}
}
}
}
}
else
{
lean_object* v_a_3492_; lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3499_; 
lean_dec_ref(v_arg_3408_);
lean_dec_ref(v_e_3381_);
v_a_3492_ = lean_ctor_get(v___x_3427_, 0);
v_isSharedCheck_3499_ = !lean_is_exclusive(v___x_3427_);
if (v_isSharedCheck_3499_ == 0)
{
v___x_3494_ = v___x_3427_;
v_isShared_3495_ = v_isSharedCheck_3499_;
goto v_resetjp_3493_;
}
else
{
lean_inc(v_a_3492_);
lean_dec(v___x_3427_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3499_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
lean_object* v___x_3497_; 
if (v_isShared_3495_ == 0)
{
v___x_3497_ = v___x_3494_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v_a_3492_);
v___x_3497_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
return v___x_3497_;
}
}
}
}
}
}
else
{
lean_object* v_a_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3508_; 
lean_dec_ref(v_arg_3408_);
lean_dec_ref(v_arg_3405_);
lean_dec_ref(v_e_3381_);
v_a_3501_ = lean_ctor_get(v___x_3417_, 0);
v_isSharedCheck_3508_ = !lean_is_exclusive(v___x_3417_);
if (v_isSharedCheck_3508_ == 0)
{
v___x_3503_ = v___x_3417_;
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_a_3501_);
lean_dec(v___x_3417_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3508_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
lean_object* v___x_3506_; 
if (v_isShared_3504_ == 0)
{
v___x_3506_ = v___x_3503_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v_a_3501_);
v___x_3506_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
return v___x_3506_;
}
}
}
}
}
}
}
}
v___jp_3398_:
{
lean_object* v___x_3399_; lean_object* v___x_3401_; 
v___x_3399_ = lean_box(0);
if (v_isShared_3397_ == 0)
{
lean_ctor_set(v___x_3396_, 0, v___x_3399_);
v___x_3401_ = v___x_3396_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v___x_3399_);
v___x_3401_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
return v___x_3401_;
}
}
}
}
else
{
lean_object* v_a_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3517_; 
lean_dec_ref(v_e_3381_);
v_a_3510_ = lean_ctor_get(v___x_3393_, 0);
v_isSharedCheck_3517_ = !lean_is_exclusive(v___x_3393_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3512_ = v___x_3393_;
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_a_3510_);
lean_dec(v___x_3393_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v___x_3515_; 
if (v_isShared_3513_ == 0)
{
v___x_3515_ = v___x_3512_;
goto v_reusejp_3514_;
}
else
{
lean_object* v_reuseFailAlloc_3516_; 
v_reuseFailAlloc_3516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_a_3510_);
v___x_3515_ = v_reuseFailAlloc_3516_;
goto v_reusejp_3514_;
}
v_reusejp_3514_:
{
return v___x_3515_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___boxed(lean_object* v_e_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_){
_start:
{
lean_object* v_res_3530_; 
v_res_3530_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f(v_e_3518_, v_a_3519_, v_a_3520_, v_a_3521_, v_a_3522_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_);
lean_dec(v_a_3528_);
lean_dec_ref(v_a_3527_);
lean_dec(v_a_3526_);
lean_dec_ref(v_a_3525_);
lean_dec(v_a_3524_);
lean_dec_ref(v_a_3523_);
lean_dec(v_a_3522_);
lean_dec_ref(v_a_3521_);
lean_dec(v_a_3520_);
lean_dec(v_a_3519_);
return v_res_3530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(lean_object* v_c_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_){
_start:
{
lean_object* v_p_3543_; lean_object* v___x_3544_; 
v_p_3543_ = lean_ctor_get(v_c_3531_, 0);
lean_inc_ref(v_p_3543_);
v___x_3544_ = l_Int_Linear_Poly_normCommRing_x3f(v_p_3543_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_);
if (lean_obj_tag(v___x_3544_) == 0)
{
lean_object* v_a_3545_; 
v_a_3545_ = lean_ctor_get(v___x_3544_, 0);
lean_inc(v_a_3545_);
lean_dec_ref(v___x_3544_);
if (lean_obj_tag(v_a_3545_) == 1)
{
lean_object* v_val_3546_; lean_object* v_snd_3547_; lean_object* v_fst_3548_; lean_object* v_fst_3549_; lean_object* v_snd_3550_; lean_object* v___x_3552_; uint8_t v_isShared_3553_; uint8_t v_isSharedCheck_3559_; 
v_val_3546_ = lean_ctor_get(v_a_3545_, 0);
lean_inc(v_val_3546_);
lean_dec_ref(v_a_3545_);
v_snd_3547_ = lean_ctor_get(v_val_3546_, 1);
lean_inc(v_snd_3547_);
v_fst_3548_ = lean_ctor_get(v_val_3546_, 0);
lean_inc(v_fst_3548_);
lean_dec(v_val_3546_);
v_fst_3549_ = lean_ctor_get(v_snd_3547_, 0);
v_snd_3550_ = lean_ctor_get(v_snd_3547_, 1);
v_isSharedCheck_3559_ = !lean_is_exclusive(v_snd_3547_);
if (v_isSharedCheck_3559_ == 0)
{
v___x_3552_ = v_snd_3547_;
v_isShared_3553_ = v_isSharedCheck_3559_;
goto v_resetjp_3551_;
}
else
{
lean_inc(v_snd_3550_);
lean_inc(v_fst_3549_);
lean_dec(v_snd_3547_);
v___x_3552_ = lean_box(0);
v_isShared_3553_ = v_isSharedCheck_3559_;
goto v_resetjp_3551_;
}
v_resetjp_3551_:
{
lean_object* v___x_3554_; lean_object* v___x_3556_; 
v___x_3554_ = lean_alloc_ctor(17, 3, 0);
lean_ctor_set(v___x_3554_, 0, v_c_3531_);
lean_ctor_set(v___x_3554_, 1, v_fst_3548_);
lean_ctor_set(v___x_3554_, 2, v_fst_3549_);
if (v_isShared_3553_ == 0)
{
lean_ctor_set(v___x_3552_, 1, v___x_3554_);
lean_ctor_set(v___x_3552_, 0, v_snd_3550_);
v___x_3556_ = v___x_3552_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3558_; 
v_reuseFailAlloc_3558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3558_, 0, v_snd_3550_);
lean_ctor_set(v_reuseFailAlloc_3558_, 1, v___x_3554_);
v___x_3556_ = v_reuseFailAlloc_3558_;
goto v_reusejp_3555_;
}
v_reusejp_3555_:
{
lean_object* v___x_3557_; 
lean_inc(v_a_3541_);
lean_inc_ref(v_a_3540_);
lean_inc(v_a_3539_);
lean_inc_ref(v_a_3538_);
lean_inc(v_a_3537_);
lean_inc_ref(v_a_3536_);
lean_inc(v_a_3535_);
lean_inc_ref(v_a_3534_);
lean_inc(v_a_3533_);
lean_inc(v_a_3532_);
v___x_3557_ = lean_grind_cutsat_assert_le(v___x_3556_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_);
return v___x_3557_;
}
}
}
else
{
lean_object* v___x_3560_; 
lean_dec(v_a_3545_);
lean_inc(v_a_3541_);
lean_inc_ref(v_a_3540_);
lean_inc(v_a_3539_);
lean_inc_ref(v_a_3538_);
lean_inc(v_a_3537_);
lean_inc_ref(v_a_3536_);
lean_inc(v_a_3535_);
lean_inc_ref(v_a_3534_);
lean_inc(v_a_3533_);
lean_inc(v_a_3532_);
v___x_3560_ = lean_grind_cutsat_assert_le(v_c_3531_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_);
return v___x_3560_;
}
}
else
{
lean_object* v_a_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3568_; 
lean_dec_ref(v_c_3531_);
v_a_3561_ = lean_ctor_get(v___x_3544_, 0);
v_isSharedCheck_3568_ = !lean_is_exclusive(v___x_3544_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3563_ = v___x_3544_;
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_a_3561_);
lean_dec(v___x_3544_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v___x_3566_; 
if (v_isShared_3564_ == 0)
{
v___x_3566_ = v___x_3563_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_a_3561_);
v___x_3566_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
return v___x_3566_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore___boxed(lean_object* v_c_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_){
_start:
{
lean_object* v_res_3581_; 
v_res_3581_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v_c_3569_, v_a_3570_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_);
lean_dec(v_a_3579_);
lean_dec_ref(v_a_3578_);
lean_dec(v_a_3577_);
lean_dec_ref(v_a_3576_);
lean_dec(v_a_3575_);
lean_dec_ref(v_a_3574_);
lean_dec(v_a_3573_);
lean_dec_ref(v_a_3572_);
lean_dec(v_a_3571_);
lean_dec(v_a_3570_);
return v_res_3581_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0(void){
_start:
{
lean_object* v___x_3582_; lean_object* v___x_3583_; 
v___x_3582_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
v___x_3583_ = lean_int_neg(v___x_3582_);
return v___x_3583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe(lean_object* v_e_3584_, uint8_t v_eqTrue_3585_, lean_object* v_a_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_){
_start:
{
lean_object* v___x_3597_; 
lean_inc_ref(v_e_3584_);
v___x_3597_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f(v_e_3584_, v_a_3586_, v_a_3587_, v_a_3588_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_);
if (lean_obj_tag(v___x_3597_) == 0)
{
lean_object* v_a_3598_; lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3624_; 
v_a_3598_ = lean_ctor_get(v___x_3597_, 0);
v_isSharedCheck_3624_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3624_ == 0)
{
v___x_3600_ = v___x_3597_;
v_isShared_3601_ = v_isSharedCheck_3624_;
goto v_resetjp_3599_;
}
else
{
lean_inc(v_a_3598_);
lean_dec(v___x_3597_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3624_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
if (lean_obj_tag(v_a_3598_) == 1)
{
lean_del_object(v___x_3600_);
if (v_eqTrue_3585_ == 0)
{
lean_object* v_val_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; 
v_val_3602_ = lean_ctor_get(v_a_3598_, 0);
lean_inc_n(v_val_3602_, 2);
lean_dec_ref(v_a_3598_);
v___x_3603_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
v___x_3604_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0);
v___x_3605_ = l_Int_Linear_Poly_mul(v_val_3602_, v___x_3604_);
v___x_3606_ = l_Int_Linear_Poly_addConst(v___x_3605_, v___x_3603_);
v___x_3607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3607_, 0, v_e_3584_);
lean_ctor_set(v___x_3607_, 1, v_val_3602_);
v___x_3608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3608_, 0, v___x_3606_);
lean_ctor_set(v___x_3608_, 1, v___x_3607_);
v___x_3609_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v___x_3608_, v_a_3586_, v_a_3587_, v_a_3588_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_);
return v___x_3609_;
}
else
{
lean_object* v_val_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3619_; 
v_val_3610_ = lean_ctor_get(v_a_3598_, 0);
v_isSharedCheck_3619_ = !lean_is_exclusive(v_a_3598_);
if (v_isSharedCheck_3619_ == 0)
{
v___x_3612_ = v_a_3598_;
v_isShared_3613_ = v_isSharedCheck_3619_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_val_3610_);
lean_dec(v_a_3598_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3619_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
lean_object* v___x_3615_; 
if (v_isShared_3613_ == 0)
{
lean_ctor_set_tag(v___x_3612_, 0);
lean_ctor_set(v___x_3612_, 0, v_e_3584_);
v___x_3615_ = v___x_3612_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v_e_3584_);
v___x_3615_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
lean_object* v___x_3616_; lean_object* v___x_3617_; 
v___x_3616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3616_, 0, v_val_3610_);
lean_ctor_set(v___x_3616_, 1, v___x_3615_);
v___x_3617_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v___x_3616_, v_a_3586_, v_a_3587_, v_a_3588_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_);
return v___x_3617_;
}
}
}
}
else
{
lean_object* v___x_3620_; lean_object* v___x_3622_; 
lean_dec(v_a_3598_);
lean_dec_ref(v_e_3584_);
v___x_3620_ = lean_box(0);
if (v_isShared_3601_ == 0)
{
lean_ctor_set(v___x_3600_, 0, v___x_3620_);
v___x_3622_ = v___x_3600_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v___x_3620_);
v___x_3622_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
return v___x_3622_;
}
}
}
}
else
{
lean_object* v_a_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3632_; 
lean_dec_ref(v_e_3584_);
v_a_3625_ = lean_ctor_get(v___x_3597_, 0);
v_isSharedCheck_3632_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3632_ == 0)
{
v___x_3627_ = v___x_3597_;
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_a_3625_);
lean_dec(v___x_3597_);
v___x_3627_ = lean_box(0);
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
v_resetjp_3626_:
{
lean_object* v___x_3630_; 
if (v_isShared_3628_ == 0)
{
v___x_3630_ = v___x_3627_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3631_, 0, v_a_3625_);
v___x_3630_ = v_reuseFailAlloc_3631_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
return v___x_3630_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___boxed(lean_object* v_e_3633_, lean_object* v_eqTrue_3634_, lean_object* v_a_3635_, lean_object* v_a_3636_, lean_object* v_a_3637_, lean_object* v_a_3638_, lean_object* v_a_3639_, lean_object* v_a_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_, lean_object* v_a_3645_){
_start:
{
uint8_t v_eqTrue_boxed_3646_; lean_object* v_res_3647_; 
v_eqTrue_boxed_3646_ = lean_unbox(v_eqTrue_3634_);
v_res_3647_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe(v_e_3633_, v_eqTrue_boxed_3646_, v_a_3635_, v_a_3636_, v_a_3637_, v_a_3638_, v_a_3639_, v_a_3640_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_);
lean_dec(v_a_3644_);
lean_dec_ref(v_a_3643_);
lean_dec(v_a_3642_);
lean_dec_ref(v_a_3641_);
lean_dec(v_a_3640_);
lean_dec_ref(v_a_3639_);
lean_dec(v_a_3638_);
lean_dec_ref(v_a_3637_);
lean_dec(v_a_3636_);
lean_dec(v_a_3635_);
return v_res_3647_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0(void){
_start:
{
lean_object* v___x_3648_; lean_object* v___x_3649_; 
v___x_3648_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
v___x_3649_ = l_Lean_mkIntLit(v___x_3648_);
return v___x_3649_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5(void){
_start:
{
lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; 
v___x_3657_ = lean_box(0);
v___x_3658_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__4));
v___x_3659_ = l_Lean_mkConst(v___x_3658_, v___x_3657_);
return v___x_3659_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8(void){
_start:
{
lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; 
v___x_3665_ = lean_box(0);
v___x_3666_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__7));
v___x_3667_ = l_Lean_mkConst(v___x_3666_, v___x_3665_);
return v___x_3667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe(lean_object* v_e_3668_, uint8_t v_eqTrue_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_, lean_object* v_a_3678_, lean_object* v_a_3679_){
_start:
{
lean_object* v___y_3682_; lean_object* v___y_3683_; lean_object* v_fst_3684_; lean_object* v_snd_3685_; lean_object* v___x_3714_; uint8_t v___x_3715_; 
lean_inc_ref(v_e_3668_);
v___x_3714_ = l_Lean_Expr_cleanupAnnotations(v_e_3668_);
v___x_3715_ = l_Lean_Expr_isApp(v___x_3714_);
if (v___x_3715_ == 0)
{
lean_dec_ref(v___x_3714_);
lean_dec_ref(v_e_3668_);
goto v___jp_3711_;
}
else
{
lean_object* v_arg_3716_; lean_object* v___x_3717_; uint8_t v___x_3718_; 
v_arg_3716_ = lean_ctor_get(v___x_3714_, 1);
lean_inc_ref(v_arg_3716_);
v___x_3717_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3714_);
v___x_3718_ = l_Lean_Expr_isApp(v___x_3717_);
if (v___x_3718_ == 0)
{
lean_dec_ref(v___x_3717_);
lean_dec_ref(v_arg_3716_);
lean_dec_ref(v_e_3668_);
goto v___jp_3711_;
}
else
{
lean_object* v_arg_3719_; lean_object* v___y_3721_; lean_object* v___x_3759_; uint8_t v___x_3760_; 
v_arg_3719_ = lean_ctor_get(v___x_3717_, 1);
lean_inc_ref(v_arg_3719_);
v___x_3759_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3717_);
v___x_3760_ = l_Lean_Expr_isApp(v___x_3759_);
if (v___x_3760_ == 0)
{
lean_dec_ref(v___x_3759_);
lean_dec_ref(v_arg_3719_);
lean_dec_ref(v_arg_3716_);
lean_dec_ref(v_e_3668_);
goto v___jp_3711_;
}
else
{
lean_object* v___x_3761_; uint8_t v___x_3762_; 
v___x_3761_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3759_);
v___x_3762_ = l_Lean_Expr_isApp(v___x_3761_);
if (v___x_3762_ == 0)
{
lean_dec_ref(v___x_3761_);
lean_dec_ref(v_arg_3719_);
lean_dec_ref(v_arg_3716_);
lean_dec_ref(v_e_3668_);
goto v___jp_3711_;
}
else
{
lean_object* v___x_3763_; lean_object* v___x_3764_; uint8_t v___x_3765_; 
v___x_3763_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3761_);
v___x_3764_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2));
v___x_3765_ = l_Lean_Expr_isConstOf(v___x_3763_, v___x_3764_);
lean_dec_ref(v___x_3763_);
if (v___x_3765_ == 0)
{
lean_dec_ref(v_arg_3719_);
lean_dec_ref(v_arg_3716_);
lean_dec_ref(v_e_3668_);
goto v___jp_3711_;
}
else
{
if (v_eqTrue_3669_ == 0)
{
lean_object* v___x_3766_; 
v___x_3766_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5);
v___y_3721_ = v___x_3766_;
goto v___jp_3720_;
}
else
{
lean_object* v___x_3767_; 
v___x_3767_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8);
v___y_3721_ = v___x_3767_;
goto v___jp_3720_;
}
}
}
}
v___jp_3720_:
{
lean_object* v___x_3722_; 
v___x_3722_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_3668_, v_a_3670_);
if (lean_obj_tag(v___x_3722_) == 0)
{
lean_object* v_a_3723_; lean_object* v___x_3724_; 
v_a_3723_ = lean_ctor_get(v___x_3722_, 0);
lean_inc(v_a_3723_);
lean_dec_ref(v___x_3722_);
lean_inc_ref(v_arg_3719_);
v___x_3724_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_3719_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_);
if (lean_obj_tag(v___x_3724_) == 0)
{
lean_object* v_a_3725_; lean_object* v_fst_3726_; lean_object* v_snd_3727_; lean_object* v___x_3728_; 
v_a_3725_ = lean_ctor_get(v___x_3724_, 0);
lean_inc(v_a_3725_);
lean_dec_ref(v___x_3724_);
v_fst_3726_ = lean_ctor_get(v_a_3725_, 0);
lean_inc(v_fst_3726_);
v_snd_3727_ = lean_ctor_get(v_a_3725_, 1);
lean_inc(v_snd_3727_);
lean_dec(v_a_3725_);
lean_inc_ref(v_arg_3716_);
v___x_3728_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_3716_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_);
if (lean_obj_tag(v___x_3728_) == 0)
{
lean_object* v_a_3729_; lean_object* v_fst_3730_; lean_object* v_snd_3731_; lean_object* v___x_3732_; 
v_a_3729_ = lean_ctor_get(v___x_3728_, 0);
lean_inc(v_a_3729_);
lean_dec_ref(v___x_3728_);
v_fst_3730_ = lean_ctor_get(v_a_3729_, 0);
lean_inc_n(v_fst_3730_, 2);
v_snd_3731_ = lean_ctor_get(v_a_3729_, 1);
lean_inc(v_snd_3731_);
lean_dec(v_a_3729_);
lean_inc(v_fst_3726_);
lean_inc_ref(v___y_3721_);
v___x_3732_ = l_Lean_mkApp6(v___y_3721_, v_arg_3719_, v_arg_3716_, v_fst_3726_, v_fst_3730_, v_snd_3727_, v_snd_3731_);
if (v_eqTrue_3669_ == 0)
{
lean_object* v___x_3733_; lean_object* v___x_3734_; 
v___x_3733_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0);
v___x_3734_ = l_Lean_mkIntAdd(v_fst_3730_, v___x_3733_);
v___y_3682_ = v_a_3723_;
v___y_3683_ = v___x_3732_;
v_fst_3684_ = v___x_3734_;
v_snd_3685_ = v_fst_3726_;
goto v___jp_3681_;
}
else
{
v___y_3682_ = v_a_3723_;
v___y_3683_ = v___x_3732_;
v_fst_3684_ = v_fst_3726_;
v_snd_3685_ = v_fst_3730_;
goto v___jp_3681_;
}
}
else
{
lean_object* v_a_3735_; lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3742_; 
lean_dec(v_snd_3727_);
lean_dec(v_fst_3726_);
lean_dec(v_a_3723_);
lean_dec_ref(v_arg_3719_);
lean_dec_ref(v_arg_3716_);
lean_dec_ref(v_e_3668_);
v_a_3735_ = lean_ctor_get(v___x_3728_, 0);
v_isSharedCheck_3742_ = !lean_is_exclusive(v___x_3728_);
if (v_isSharedCheck_3742_ == 0)
{
v___x_3737_ = v___x_3728_;
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
else
{
lean_inc(v_a_3735_);
lean_dec(v___x_3728_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
lean_object* v___x_3740_; 
if (v_isShared_3738_ == 0)
{
v___x_3740_ = v___x_3737_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_a_3735_);
v___x_3740_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
return v___x_3740_;
}
}
}
}
else
{
lean_object* v_a_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3750_; 
lean_dec(v_a_3723_);
lean_dec_ref(v_arg_3719_);
lean_dec_ref(v_arg_3716_);
lean_dec_ref(v_e_3668_);
v_a_3743_ = lean_ctor_get(v___x_3724_, 0);
v_isSharedCheck_3750_ = !lean_is_exclusive(v___x_3724_);
if (v_isSharedCheck_3750_ == 0)
{
v___x_3745_ = v___x_3724_;
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_a_3743_);
lean_dec(v___x_3724_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v___x_3748_; 
if (v_isShared_3746_ == 0)
{
v___x_3748_ = v___x_3745_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v_a_3743_);
v___x_3748_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
return v___x_3748_;
}
}
}
}
else
{
lean_object* v_a_3751_; lean_object* v___x_3753_; uint8_t v_isShared_3754_; uint8_t v_isSharedCheck_3758_; 
lean_dec_ref(v_arg_3719_);
lean_dec_ref(v_arg_3716_);
lean_dec_ref(v_e_3668_);
v_a_3751_ = lean_ctor_get(v___x_3722_, 0);
v_isSharedCheck_3758_ = !lean_is_exclusive(v___x_3722_);
if (v_isSharedCheck_3758_ == 0)
{
v___x_3753_ = v___x_3722_;
v_isShared_3754_ = v_isSharedCheck_3758_;
goto v_resetjp_3752_;
}
else
{
lean_inc(v_a_3751_);
lean_dec(v___x_3722_);
v___x_3753_ = lean_box(0);
v_isShared_3754_ = v_isSharedCheck_3758_;
goto v_resetjp_3752_;
}
v_resetjp_3752_:
{
lean_object* v___x_3756_; 
if (v_isShared_3754_ == 0)
{
v___x_3756_ = v___x_3753_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3757_; 
v_reuseFailAlloc_3757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3757_, 0, v_a_3751_);
v___x_3756_ = v_reuseFailAlloc_3757_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
return v___x_3756_;
}
}
}
}
}
}
v___jp_3681_:
{
lean_object* v___x_3686_; 
lean_inc(v___y_3682_);
v___x_3686_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_3684_, v___y_3682_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_);
if (lean_obj_tag(v___x_3686_) == 0)
{
lean_object* v_a_3687_; lean_object* v___x_3688_; 
v_a_3687_ = lean_ctor_get(v___x_3686_, 0);
lean_inc(v_a_3687_);
lean_dec_ref(v___x_3686_);
v___x_3688_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_snd_3685_, v___y_3682_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_);
if (lean_obj_tag(v___x_3688_) == 0)
{
lean_object* v_a_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; 
v_a_3689_ = lean_ctor_get(v___x_3688_, 0);
lean_inc_n(v_a_3689_, 2);
lean_dec_ref(v___x_3688_);
lean_inc(v_a_3687_);
v___x_3690_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3690_, 0, v_a_3687_);
lean_ctor_set(v___x_3690_, 1, v_a_3689_);
v___x_3691_ = l_Int_Linear_Expr_norm(v___x_3690_);
lean_dec_ref(v___x_3690_);
v___x_3692_ = lean_alloc_ctor(2, 4, 1);
lean_ctor_set(v___x_3692_, 0, v_e_3668_);
lean_ctor_set(v___x_3692_, 1, v___y_3683_);
lean_ctor_set(v___x_3692_, 2, v_a_3687_);
lean_ctor_set(v___x_3692_, 3, v_a_3689_);
lean_ctor_set_uint8(v___x_3692_, sizeof(void*)*4, v_eqTrue_3669_);
v___x_3693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3693_, 0, v___x_3691_);
lean_ctor_set(v___x_3693_, 1, v___x_3692_);
v___x_3694_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v___x_3693_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_, v_a_3678_, v_a_3679_);
return v___x_3694_;
}
else
{
lean_object* v_a_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3702_; 
lean_dec(v_a_3687_);
lean_dec_ref(v___y_3683_);
lean_dec_ref(v_e_3668_);
v_a_3695_ = lean_ctor_get(v___x_3688_, 0);
v_isSharedCheck_3702_ = !lean_is_exclusive(v___x_3688_);
if (v_isSharedCheck_3702_ == 0)
{
v___x_3697_ = v___x_3688_;
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_a_3695_);
lean_dec(v___x_3688_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
lean_object* v___x_3700_; 
if (v_isShared_3698_ == 0)
{
v___x_3700_ = v___x_3697_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_a_3695_);
v___x_3700_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
return v___x_3700_;
}
}
}
}
else
{
lean_object* v_a_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3710_; 
lean_dec_ref(v_snd_3685_);
lean_dec_ref(v___y_3683_);
lean_dec(v___y_3682_);
lean_dec_ref(v_e_3668_);
v_a_3703_ = lean_ctor_get(v___x_3686_, 0);
v_isSharedCheck_3710_ = !lean_is_exclusive(v___x_3686_);
if (v_isSharedCheck_3710_ == 0)
{
v___x_3705_ = v___x_3686_;
v_isShared_3706_ = v_isSharedCheck_3710_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_a_3703_);
lean_dec(v___x_3686_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3710_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
lean_object* v___x_3708_; 
if (v_isShared_3706_ == 0)
{
v___x_3708_ = v___x_3705_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v_a_3703_);
v___x_3708_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
return v___x_3708_;
}
}
}
}
v___jp_3711_:
{
lean_object* v___x_3712_; lean_object* v___x_3713_; 
v___x_3712_ = lean_box(0);
v___x_3713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3713_, 0, v___x_3712_);
return v___x_3713_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___boxed(lean_object* v_e_3768_, lean_object* v_eqTrue_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_){
_start:
{
uint8_t v_eqTrue_boxed_3781_; lean_object* v_res_3782_; 
v_eqTrue_boxed_3781_ = lean_unbox(v_eqTrue_3769_);
v_res_3782_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe(v_e_3768_, v_eqTrue_boxed_3781_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_, v_a_3779_);
lean_dec(v_a_3779_);
lean_dec_ref(v_a_3778_);
lean_dec(v_a_3777_);
lean_dec_ref(v_a_3776_);
lean_dec(v_a_3775_);
lean_dec_ref(v_a_3774_);
lean_dec(v_a_3773_);
lean_dec_ref(v_a_3772_);
lean_dec(v_a_3771_);
lean_dec(v_a_3770_);
return v_res_3782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe(lean_object* v_e_3783_, uint8_t v_eqTrue_3784_, lean_object* v_a_3785_, lean_object* v_a_3786_, lean_object* v_a_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_, lean_object* v_a_3792_, lean_object* v_a_3793_, lean_object* v_a_3794_, lean_object* v_a_3795_){
_start:
{
lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v___y_3803_; lean_object* v___y_3804_; lean_object* v___y_3805_; lean_object* v___y_3806_; lean_object* v___y_3807_; lean_object* v___y_3808_; lean_object* v___y_3809_; lean_object* v___y_3810_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v_fst_3813_; lean_object* v_snd_3814_; lean_object* v_____x_3841_; lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___y_3846_; lean_object* v___y_3847_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v___y_3850_; lean_object* v___y_3851_; lean_object* v___y_3852_; 
if (v_eqTrue_3784_ == 0)
{
lean_object* v___x_3906_; 
v___x_3906_ = l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLE_x3f___redArg(v_a_3785_, v_a_3786_, v_a_3792_, v_a_3793_, v_a_3794_, v_a_3795_);
if (lean_obj_tag(v___x_3906_) == 0)
{
lean_object* v_a_3907_; 
v_a_3907_ = lean_ctor_get(v___x_3906_, 0);
lean_inc(v_a_3907_);
lean_dec_ref(v___x_3906_);
v_____x_3841_ = v_a_3907_;
v___y_3842_ = v_a_3785_;
v___y_3843_ = v_a_3786_;
v___y_3844_ = v_a_3787_;
v___y_3845_ = v_a_3788_;
v___y_3846_ = v_a_3789_;
v___y_3847_ = v_a_3790_;
v___y_3848_ = v_a_3791_;
v___y_3849_ = v_a_3792_;
v___y_3850_ = v_a_3793_;
v___y_3851_ = v_a_3794_;
v___y_3852_ = v_a_3795_;
goto v___jp_3840_;
}
else
{
lean_object* v_a_3908_; lean_object* v___x_3910_; uint8_t v_isShared_3911_; uint8_t v_isSharedCheck_3915_; 
lean_dec_ref(v_e_3783_);
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
else
{
lean_object* v___x_3916_; 
v___x_3916_ = l_Lean_Meta_Grind_Arith_Cutsat_getOfLE_x3f___redArg(v_a_3785_, v_a_3786_, v_a_3792_, v_a_3793_, v_a_3794_, v_a_3795_);
if (lean_obj_tag(v___x_3916_) == 0)
{
lean_object* v_a_3917_; 
v_a_3917_ = lean_ctor_get(v___x_3916_, 0);
lean_inc(v_a_3917_);
lean_dec_ref(v___x_3916_);
v_____x_3841_ = v_a_3917_;
v___y_3842_ = v_a_3785_;
v___y_3843_ = v_a_3786_;
v___y_3844_ = v_a_3787_;
v___y_3845_ = v_a_3788_;
v___y_3846_ = v_a_3789_;
v___y_3847_ = v_a_3790_;
v___y_3848_ = v_a_3791_;
v___y_3849_ = v_a_3792_;
v___y_3850_ = v_a_3793_;
v___y_3851_ = v_a_3794_;
v___y_3852_ = v_a_3795_;
goto v___jp_3840_;
}
else
{
lean_object* v_a_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3925_; 
lean_dec_ref(v_e_3783_);
v_a_3918_ = lean_ctor_get(v___x_3916_, 0);
v_isSharedCheck_3925_ = !lean_is_exclusive(v___x_3916_);
if (v_isSharedCheck_3925_ == 0)
{
v___x_3920_ = v___x_3916_;
v_isShared_3921_ = v_isSharedCheck_3925_;
goto v_resetjp_3919_;
}
else
{
lean_inc(v_a_3918_);
lean_dec(v___x_3916_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3925_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
lean_object* v___x_3923_; 
if (v_isShared_3921_ == 0)
{
v___x_3923_ = v___x_3920_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v_a_3918_);
v___x_3923_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
return v___x_3923_;
}
}
}
}
v___jp_3797_:
{
lean_object* v___x_3798_; lean_object* v___x_3799_; 
v___x_3798_ = lean_box(0);
v___x_3799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3799_, 0, v___x_3798_);
return v___x_3799_;
}
v___jp_3800_:
{
lean_object* v___x_3815_; 
lean_inc(v___y_3801_);
v___x_3815_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_3813_, v___y_3801_, v___y_3808_, v___y_3806_, v___y_3803_, v___y_3805_, v___y_3804_, v___y_3809_, v___y_3807_, v___y_3810_, v___y_3802_, v___y_3812_);
if (lean_obj_tag(v___x_3815_) == 0)
{
lean_object* v_a_3816_; lean_object* v___x_3817_; 
v_a_3816_ = lean_ctor_get(v___x_3815_, 0);
lean_inc(v_a_3816_);
lean_dec_ref(v___x_3815_);
v___x_3817_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_snd_3814_, v___y_3801_, v___y_3808_, v___y_3806_, v___y_3803_, v___y_3805_, v___y_3804_, v___y_3809_, v___y_3807_, v___y_3810_, v___y_3802_, v___y_3812_);
if (lean_obj_tag(v___x_3817_) == 0)
{
lean_object* v_a_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; 
v_a_3818_ = lean_ctor_get(v___x_3817_, 0);
lean_inc_n(v_a_3818_, 2);
lean_dec_ref(v___x_3817_);
lean_inc(v_a_3816_);
v___x_3819_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3819_, 0, v_a_3816_);
lean_ctor_set(v___x_3819_, 1, v_a_3818_);
v___x_3820_ = l_Int_Linear_Expr_norm(v___x_3819_);
lean_dec_ref(v___x_3819_);
v___x_3821_ = lean_alloc_ctor(2, 4, 1);
lean_ctor_set(v___x_3821_, 0, v_e_3783_);
lean_ctor_set(v___x_3821_, 1, v___y_3811_);
lean_ctor_set(v___x_3821_, 2, v_a_3816_);
lean_ctor_set(v___x_3821_, 3, v_a_3818_);
lean_ctor_set_uint8(v___x_3821_, sizeof(void*)*4, v_eqTrue_3784_);
v___x_3822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3822_, 0, v___x_3820_);
lean_ctor_set(v___x_3822_, 1, v___x_3821_);
v___x_3823_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v___x_3822_, v___y_3808_, v___y_3806_, v___y_3803_, v___y_3805_, v___y_3804_, v___y_3809_, v___y_3807_, v___y_3810_, v___y_3802_, v___y_3812_);
return v___x_3823_;
}
else
{
lean_object* v_a_3824_; lean_object* v___x_3826_; uint8_t v_isShared_3827_; uint8_t v_isSharedCheck_3831_; 
lean_dec(v_a_3816_);
lean_dec_ref(v___y_3811_);
lean_dec_ref(v_e_3783_);
v_a_3824_ = lean_ctor_get(v___x_3817_, 0);
v_isSharedCheck_3831_ = !lean_is_exclusive(v___x_3817_);
if (v_isSharedCheck_3831_ == 0)
{
v___x_3826_ = v___x_3817_;
v_isShared_3827_ = v_isSharedCheck_3831_;
goto v_resetjp_3825_;
}
else
{
lean_inc(v_a_3824_);
lean_dec(v___x_3817_);
v___x_3826_ = lean_box(0);
v_isShared_3827_ = v_isSharedCheck_3831_;
goto v_resetjp_3825_;
}
v_resetjp_3825_:
{
lean_object* v___x_3829_; 
if (v_isShared_3827_ == 0)
{
v___x_3829_ = v___x_3826_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v_a_3824_);
v___x_3829_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
return v___x_3829_;
}
}
}
}
else
{
lean_object* v_a_3832_; lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3839_; 
lean_dec_ref(v_snd_3814_);
lean_dec_ref(v___y_3811_);
lean_dec(v___y_3801_);
lean_dec_ref(v_e_3783_);
v_a_3832_ = lean_ctor_get(v___x_3815_, 0);
v_isSharedCheck_3839_ = !lean_is_exclusive(v___x_3815_);
if (v_isSharedCheck_3839_ == 0)
{
v___x_3834_ = v___x_3815_;
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
else
{
lean_inc(v_a_3832_);
lean_dec(v___x_3815_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
lean_object* v___x_3837_; 
if (v_isShared_3835_ == 0)
{
v___x_3837_ = v___x_3834_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_a_3832_);
v___x_3837_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
return v___x_3837_;
}
}
}
}
v___jp_3840_:
{
if (lean_obj_tag(v_____x_3841_) == 1)
{
lean_object* v_val_3853_; lean_object* v___x_3854_; uint8_t v___x_3855_; 
v_val_3853_ = lean_ctor_get(v_____x_3841_, 0);
lean_inc(v_val_3853_);
lean_dec_ref(v_____x_3841_);
lean_inc_ref(v_e_3783_);
v___x_3854_ = l_Lean_Expr_cleanupAnnotations(v_e_3783_);
v___x_3855_ = l_Lean_Expr_isApp(v___x_3854_);
if (v___x_3855_ == 0)
{
lean_dec_ref(v___x_3854_);
lean_dec(v_val_3853_);
lean_dec_ref(v_e_3783_);
goto v___jp_3797_;
}
else
{
lean_object* v_arg_3856_; lean_object* v___x_3857_; uint8_t v___x_3858_; 
v_arg_3856_ = lean_ctor_get(v___x_3854_, 1);
lean_inc_ref(v_arg_3856_);
v___x_3857_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3854_);
v___x_3858_ = l_Lean_Expr_isApp(v___x_3857_);
if (v___x_3858_ == 0)
{
lean_dec_ref(v___x_3857_);
lean_dec_ref(v_arg_3856_);
lean_dec(v_val_3853_);
lean_dec_ref(v_e_3783_);
goto v___jp_3797_;
}
else
{
lean_object* v_arg_3859_; lean_object* v___x_3860_; uint8_t v___x_3861_; 
v_arg_3859_ = lean_ctor_get(v___x_3857_, 1);
lean_inc_ref(v_arg_3859_);
v___x_3860_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3857_);
v___x_3861_ = l_Lean_Expr_isApp(v___x_3860_);
if (v___x_3861_ == 0)
{
lean_dec_ref(v___x_3860_);
lean_dec_ref(v_arg_3859_);
lean_dec_ref(v_arg_3856_);
lean_dec(v_val_3853_);
lean_dec_ref(v_e_3783_);
goto v___jp_3797_;
}
else
{
lean_object* v___x_3862_; uint8_t v___x_3863_; 
v___x_3862_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3860_);
v___x_3863_ = l_Lean_Expr_isApp(v___x_3862_);
if (v___x_3863_ == 0)
{
lean_dec_ref(v___x_3862_);
lean_dec_ref(v_arg_3859_);
lean_dec_ref(v_arg_3856_);
lean_dec(v_val_3853_);
lean_dec_ref(v_e_3783_);
goto v___jp_3797_;
}
else
{
lean_object* v___x_3864_; lean_object* v___x_3865_; uint8_t v___x_3866_; 
v___x_3864_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3862_);
v___x_3865_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2));
v___x_3866_ = l_Lean_Expr_isConstOf(v___x_3864_, v___x_3865_);
lean_dec_ref(v___x_3864_);
if (v___x_3866_ == 0)
{
lean_dec_ref(v_arg_3859_);
lean_dec_ref(v_arg_3856_);
lean_dec(v_val_3853_);
lean_dec_ref(v_e_3783_);
goto v___jp_3797_;
}
else
{
lean_object* v___x_3867_; 
v___x_3867_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_3783_, v___y_3843_);
if (lean_obj_tag(v___x_3867_) == 0)
{
lean_object* v_a_3868_; lean_object* v___x_3869_; 
v_a_3868_ = lean_ctor_get(v___x_3867_, 0);
lean_inc(v_a_3868_);
lean_dec_ref(v___x_3867_);
lean_inc_ref(v_arg_3859_);
v___x_3869_ = l_Lean_Meta_Grind_Arith_Cutsat_toInt(v_arg_3859_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_);
if (lean_obj_tag(v___x_3869_) == 0)
{
lean_object* v_a_3870_; lean_object* v_fst_3871_; lean_object* v_snd_3872_; lean_object* v___x_3873_; 
v_a_3870_ = lean_ctor_get(v___x_3869_, 0);
lean_inc(v_a_3870_);
lean_dec_ref(v___x_3869_);
v_fst_3871_ = lean_ctor_get(v_a_3870_, 0);
lean_inc(v_fst_3871_);
v_snd_3872_ = lean_ctor_get(v_a_3870_, 1);
lean_inc(v_snd_3872_);
lean_dec(v_a_3870_);
lean_inc_ref(v_arg_3856_);
v___x_3873_ = l_Lean_Meta_Grind_Arith_Cutsat_toInt(v_arg_3856_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_, v___y_3852_);
if (lean_obj_tag(v___x_3873_) == 0)
{
lean_object* v_a_3874_; lean_object* v_fst_3875_; lean_object* v_snd_3876_; lean_object* v___x_3877_; 
v_a_3874_ = lean_ctor_get(v___x_3873_, 0);
lean_inc(v_a_3874_);
lean_dec_ref(v___x_3873_);
v_fst_3875_ = lean_ctor_get(v_a_3874_, 0);
lean_inc_n(v_fst_3875_, 2);
v_snd_3876_ = lean_ctor_get(v_a_3874_, 1);
lean_inc(v_snd_3876_);
lean_dec(v_a_3874_);
lean_inc(v_fst_3871_);
v___x_3877_ = l_Lean_mkApp6(v_val_3853_, v_arg_3859_, v_arg_3856_, v_fst_3871_, v_fst_3875_, v_snd_3872_, v_snd_3876_);
if (v_eqTrue_3784_ == 0)
{
lean_object* v___x_3878_; lean_object* v___x_3879_; 
v___x_3878_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0);
v___x_3879_ = l_Lean_mkIntAdd(v_fst_3875_, v___x_3878_);
v___y_3801_ = v_a_3868_;
v___y_3802_ = v___y_3851_;
v___y_3803_ = v___y_3845_;
v___y_3804_ = v___y_3847_;
v___y_3805_ = v___y_3846_;
v___y_3806_ = v___y_3844_;
v___y_3807_ = v___y_3849_;
v___y_3808_ = v___y_3843_;
v___y_3809_ = v___y_3848_;
v___y_3810_ = v___y_3850_;
v___y_3811_ = v___x_3877_;
v___y_3812_ = v___y_3852_;
v_fst_3813_ = v___x_3879_;
v_snd_3814_ = v_fst_3871_;
goto v___jp_3800_;
}
else
{
v___y_3801_ = v_a_3868_;
v___y_3802_ = v___y_3851_;
v___y_3803_ = v___y_3845_;
v___y_3804_ = v___y_3847_;
v___y_3805_ = v___y_3846_;
v___y_3806_ = v___y_3844_;
v___y_3807_ = v___y_3849_;
v___y_3808_ = v___y_3843_;
v___y_3809_ = v___y_3848_;
v___y_3810_ = v___y_3850_;
v___y_3811_ = v___x_3877_;
v___y_3812_ = v___y_3852_;
v_fst_3813_ = v_fst_3871_;
v_snd_3814_ = v_fst_3875_;
goto v___jp_3800_;
}
}
else
{
lean_object* v_a_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3887_; 
lean_dec(v_snd_3872_);
lean_dec(v_fst_3871_);
lean_dec(v_a_3868_);
lean_dec_ref(v_arg_3859_);
lean_dec_ref(v_arg_3856_);
lean_dec(v_val_3853_);
lean_dec_ref(v_e_3783_);
v_a_3880_ = lean_ctor_get(v___x_3873_, 0);
v_isSharedCheck_3887_ = !lean_is_exclusive(v___x_3873_);
if (v_isSharedCheck_3887_ == 0)
{
v___x_3882_ = v___x_3873_;
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_a_3880_);
lean_dec(v___x_3873_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___x_3885_; 
if (v_isShared_3883_ == 0)
{
v___x_3885_ = v___x_3882_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_a_3880_);
v___x_3885_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
return v___x_3885_;
}
}
}
}
else
{
lean_object* v_a_3888_; lean_object* v___x_3890_; uint8_t v_isShared_3891_; uint8_t v_isSharedCheck_3895_; 
lean_dec(v_a_3868_);
lean_dec_ref(v_arg_3859_);
lean_dec_ref(v_arg_3856_);
lean_dec(v_val_3853_);
lean_dec_ref(v_e_3783_);
v_a_3888_ = lean_ctor_get(v___x_3869_, 0);
v_isSharedCheck_3895_ = !lean_is_exclusive(v___x_3869_);
if (v_isSharedCheck_3895_ == 0)
{
v___x_3890_ = v___x_3869_;
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
else
{
lean_inc(v_a_3888_);
lean_dec(v___x_3869_);
v___x_3890_ = lean_box(0);
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
v_resetjp_3889_:
{
lean_object* v___x_3893_; 
if (v_isShared_3891_ == 0)
{
v___x_3893_ = v___x_3890_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3894_; 
v_reuseFailAlloc_3894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3894_, 0, v_a_3888_);
v___x_3893_ = v_reuseFailAlloc_3894_;
goto v_reusejp_3892_;
}
v_reusejp_3892_:
{
return v___x_3893_;
}
}
}
}
else
{
lean_object* v_a_3896_; lean_object* v___x_3898_; uint8_t v_isShared_3899_; uint8_t v_isSharedCheck_3903_; 
lean_dec_ref(v_arg_3859_);
lean_dec_ref(v_arg_3856_);
lean_dec(v_val_3853_);
lean_dec_ref(v_e_3783_);
v_a_3896_ = lean_ctor_get(v___x_3867_, 0);
v_isSharedCheck_3903_ = !lean_is_exclusive(v___x_3867_);
if (v_isSharedCheck_3903_ == 0)
{
v___x_3898_ = v___x_3867_;
v_isShared_3899_ = v_isSharedCheck_3903_;
goto v_resetjp_3897_;
}
else
{
lean_inc(v_a_3896_);
lean_dec(v___x_3867_);
v___x_3898_ = lean_box(0);
v_isShared_3899_ = v_isSharedCheck_3903_;
goto v_resetjp_3897_;
}
v_resetjp_3897_:
{
lean_object* v___x_3901_; 
if (v_isShared_3899_ == 0)
{
v___x_3901_ = v___x_3898_;
goto v_reusejp_3900_;
}
else
{
lean_object* v_reuseFailAlloc_3902_; 
v_reuseFailAlloc_3902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3902_, 0, v_a_3896_);
v___x_3901_ = v_reuseFailAlloc_3902_;
goto v_reusejp_3900_;
}
v_reusejp_3900_:
{
return v___x_3901_;
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
lean_object* v___x_3904_; lean_object* v___x_3905_; 
lean_dec(v_____x_3841_);
lean_dec_ref(v_e_3783_);
v___x_3904_ = lean_box(0);
v___x_3905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3905_, 0, v___x_3904_);
return v___x_3905_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe___boxed(lean_object* v_e_3926_, lean_object* v_eqTrue_3927_, lean_object* v_a_3928_, lean_object* v_a_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_, lean_object* v_a_3932_, lean_object* v_a_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_){
_start:
{
uint8_t v_eqTrue_boxed_3940_; lean_object* v_res_3941_; 
v_eqTrue_boxed_3940_ = lean_unbox(v_eqTrue_3927_);
v_res_3941_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe(v_e_3926_, v_eqTrue_boxed_3940_, v_a_3928_, v_a_3929_, v_a_3930_, v_a_3931_, v_a_3932_, v_a_3933_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_, v_a_3938_);
lean_dec(v_a_3938_);
lean_dec_ref(v_a_3937_);
lean_dec(v_a_3936_);
lean_dec_ref(v_a_3935_);
lean_dec(v_a_3934_);
lean_dec_ref(v_a_3933_);
lean_dec(v_a_3932_);
lean_dec_ref(v_a_3931_);
lean_dec(v_a_3930_);
lean_dec(v_a_3929_);
lean_dec(v_a_3928_);
return v_res_3941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe(lean_object* v_e_3947_, uint8_t v_eqTrue_3948_, lean_object* v_a_3949_, lean_object* v_a_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_){
_start:
{
lean_object* v___x_3963_; 
v___x_3963_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3951_);
if (lean_obj_tag(v___x_3963_) == 0)
{
lean_object* v_a_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_3994_; 
v_a_3964_ = lean_ctor_get(v___x_3963_, 0);
v_isSharedCheck_3994_ = !lean_is_exclusive(v___x_3963_);
if (v_isSharedCheck_3994_ == 0)
{
v___x_3966_ = v___x_3963_;
v_isShared_3967_ = v_isSharedCheck_3994_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_a_3964_);
lean_dec(v___x_3963_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_3994_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
uint8_t v_lia_3968_; 
v_lia_3968_ = lean_ctor_get_uint8(v_a_3964_, sizeof(void*)*13 + 23);
lean_dec(v_a_3964_);
if (v_lia_3968_ == 0)
{
lean_object* v___x_3969_; lean_object* v___x_3971_; 
lean_dec_ref(v_e_3947_);
v___x_3969_ = lean_box(0);
if (v_isShared_3967_ == 0)
{
lean_ctor_set(v___x_3966_, 0, v___x_3969_);
v___x_3971_ = v___x_3966_;
goto v_reusejp_3970_;
}
else
{
lean_object* v_reuseFailAlloc_3972_; 
v_reuseFailAlloc_3972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3972_, 0, v___x_3969_);
v___x_3971_ = v_reuseFailAlloc_3972_;
goto v_reusejp_3970_;
}
v_reusejp_3970_:
{
return v___x_3971_;
}
}
else
{
lean_object* v___x_3973_; uint8_t v___x_3974_; 
lean_del_object(v___x_3966_);
lean_inc_ref(v_e_3947_);
v___x_3973_ = l_Lean_Expr_cleanupAnnotations(v_e_3947_);
v___x_3974_ = l_Lean_Expr_isApp(v___x_3973_);
if (v___x_3974_ == 0)
{
lean_dec_ref(v___x_3973_);
lean_dec_ref(v_e_3947_);
goto v___jp_3960_;
}
else
{
lean_object* v___x_3975_; uint8_t v___x_3976_; 
v___x_3975_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3973_);
v___x_3976_ = l_Lean_Expr_isApp(v___x_3975_);
if (v___x_3976_ == 0)
{
lean_dec_ref(v___x_3975_);
lean_dec_ref(v_e_3947_);
goto v___jp_3960_;
}
else
{
lean_object* v___x_3977_; uint8_t v___x_3978_; 
v___x_3977_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3975_);
v___x_3978_ = l_Lean_Expr_isApp(v___x_3977_);
if (v___x_3978_ == 0)
{
lean_dec_ref(v___x_3977_);
lean_dec_ref(v_e_3947_);
goto v___jp_3960_;
}
else
{
lean_object* v___x_3979_; uint8_t v___x_3980_; 
v___x_3979_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3977_);
v___x_3980_ = l_Lean_Expr_isApp(v___x_3979_);
if (v___x_3980_ == 0)
{
lean_dec_ref(v___x_3979_);
lean_dec_ref(v_e_3947_);
goto v___jp_3960_;
}
else
{
lean_object* v_arg_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; uint8_t v___x_3984_; 
v_arg_3981_ = lean_ctor_get(v___x_3979_, 1);
lean_inc_ref(v_arg_3981_);
v___x_3982_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3979_);
v___x_3983_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2));
v___x_3984_ = l_Lean_Expr_isConstOf(v___x_3982_, v___x_3983_);
lean_dec_ref(v___x_3982_);
if (v___x_3984_ == 0)
{
lean_dec_ref(v_arg_3981_);
lean_dec_ref(v_e_3947_);
goto v___jp_3960_;
}
else
{
lean_object* v___x_3985_; uint8_t v___x_3986_; 
v___x_3985_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__0));
v___x_3986_ = l_Lean_Expr_isConstOf(v_arg_3981_, v___x_3985_);
if (v___x_3986_ == 0)
{
lean_object* v___x_3987_; uint8_t v___x_3988_; 
v___x_3987_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__2));
v___x_3988_ = l_Lean_Expr_isConstOf(v_arg_3981_, v___x_3987_);
if (v___x_3988_ == 0)
{
lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; 
v___x_3989_ = lean_box(v_eqTrue_3948_);
v___x_3990_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateToIntLe___boxed), 14, 2);
lean_closure_set(v___x_3990_, 0, v_e_3947_);
lean_closure_set(v___x_3990_, 1, v___x_3989_);
v___x_3991_ = l_Lean_Meta_Grind_Arith_Cutsat_ToIntM_run(v_arg_3981_, v___x_3990_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_);
return v___x_3991_;
}
else
{
lean_object* v___x_3992_; 
lean_dec_ref(v_arg_3981_);
v___x_3992_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe(v_e_3947_, v_eqTrue_3948_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_);
return v___x_3992_;
}
}
else
{
lean_object* v___x_3993_; 
lean_dec_ref(v_arg_3981_);
v___x_3993_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe(v_e_3947_, v_eqTrue_3948_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_);
return v___x_3993_;
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
lean_object* v_a_3995_; lean_object* v___x_3997_; uint8_t v_isShared_3998_; uint8_t v_isSharedCheck_4002_; 
lean_dec_ref(v_e_3947_);
v_a_3995_ = lean_ctor_get(v___x_3963_, 0);
v_isSharedCheck_4002_ = !lean_is_exclusive(v___x_3963_);
if (v_isSharedCheck_4002_ == 0)
{
v___x_3997_ = v___x_3963_;
v_isShared_3998_ = v_isSharedCheck_4002_;
goto v_resetjp_3996_;
}
else
{
lean_inc(v_a_3995_);
lean_dec(v___x_3963_);
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
v___jp_3960_:
{
lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___x_3961_ = lean_box(0);
v___x_3962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3962_, 0, v___x_3961_);
return v___x_3962_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___boxed(lean_object* v_e_4003_, lean_object* v_eqTrue_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_){
_start:
{
uint8_t v_eqTrue_boxed_4016_; lean_object* v_res_4017_; 
v_eqTrue_boxed_4016_ = lean_unbox(v_eqTrue_4004_);
v_res_4017_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLe(v_e_4003_, v_eqTrue_boxed_4016_, v_a_4005_, v_a_4006_, v_a_4007_, v_a_4008_, v_a_4009_, v_a_4010_, v_a_4011_, v_a_4012_, v_a_4013_, v_a_4014_);
lean_dec(v_a_4014_);
lean_dec_ref(v_a_4013_);
lean_dec(v_a_4012_);
lean_dec_ref(v_a_4011_);
lean_dec(v_a_4010_);
lean_dec_ref(v_a_4009_);
lean_dec(v_a_4008_);
lean_dec_ref(v_a_4007_);
lean_dec(v_a_4006_);
lean_dec(v_a_4005_);
return v_res_4017_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__0(lean_object* v_e_4018_, lean_object* v_arg_4019_, lean_object* v_arg_4020_, uint8_t v_eqTrue_4021_, lean_object* v_____x_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_){
_start:
{
if (lean_obj_tag(v_____x_4022_) == 1)
{
lean_object* v_val_4035_; lean_object* v___x_4036_; 
v_val_4035_ = lean_ctor_get(v_____x_4022_, 0);
lean_inc(v_val_4035_);
lean_dec_ref(v_____x_4022_);
v___x_4036_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_4018_, v___y_4024_);
if (lean_obj_tag(v___x_4036_) == 0)
{
lean_object* v_a_4037_; lean_object* v___x_4038_; 
v_a_4037_ = lean_ctor_get(v___x_4036_, 0);
lean_inc(v_a_4037_);
lean_dec_ref(v___x_4036_);
lean_inc_ref(v_arg_4019_);
v___x_4038_ = l_Lean_Meta_Grind_Arith_Cutsat_toInt(v_arg_4019_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_);
if (lean_obj_tag(v___x_4038_) == 0)
{
lean_object* v_a_4039_; lean_object* v_fst_4040_; lean_object* v_snd_4041_; lean_object* v___x_4043_; uint8_t v_isShared_4044_; uint8_t v_isSharedCheck_4096_; 
v_a_4039_ = lean_ctor_get(v___x_4038_, 0);
lean_inc(v_a_4039_);
lean_dec_ref(v___x_4038_);
v_fst_4040_ = lean_ctor_get(v_a_4039_, 0);
v_snd_4041_ = lean_ctor_get(v_a_4039_, 1);
v_isSharedCheck_4096_ = !lean_is_exclusive(v_a_4039_);
if (v_isSharedCheck_4096_ == 0)
{
v___x_4043_ = v_a_4039_;
v_isShared_4044_ = v_isSharedCheck_4096_;
goto v_resetjp_4042_;
}
else
{
lean_inc(v_snd_4041_);
lean_inc(v_fst_4040_);
lean_dec(v_a_4039_);
v___x_4043_ = lean_box(0);
v_isShared_4044_ = v_isSharedCheck_4096_;
goto v_resetjp_4042_;
}
v_resetjp_4042_:
{
lean_object* v___x_4045_; 
lean_inc_ref(v_arg_4020_);
v___x_4045_ = l_Lean_Meta_Grind_Arith_Cutsat_toInt(v_arg_4020_, v___y_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_);
if (lean_obj_tag(v___x_4045_) == 0)
{
lean_object* v_a_4046_; lean_object* v_fst_4047_; lean_object* v_snd_4048_; lean_object* v___x_4050_; uint8_t v_isShared_4051_; uint8_t v_isSharedCheck_4087_; 
v_a_4046_ = lean_ctor_get(v___x_4045_, 0);
lean_inc(v_a_4046_);
lean_dec_ref(v___x_4045_);
v_fst_4047_ = lean_ctor_get(v_a_4046_, 0);
v_snd_4048_ = lean_ctor_get(v_a_4046_, 1);
v_isSharedCheck_4087_ = !lean_is_exclusive(v_a_4046_);
if (v_isSharedCheck_4087_ == 0)
{
v___x_4050_ = v_a_4046_;
v_isShared_4051_ = v_isSharedCheck_4087_;
goto v_resetjp_4049_;
}
else
{
lean_inc(v_snd_4048_);
lean_inc(v_fst_4047_);
lean_dec(v_a_4046_);
v___x_4050_ = lean_box(0);
v_isShared_4051_ = v_isSharedCheck_4087_;
goto v_resetjp_4049_;
}
v_resetjp_4049_:
{
lean_object* v___x_4052_; lean_object* v_fst_4054_; lean_object* v_snd_4055_; 
lean_inc(v_fst_4047_);
lean_inc(v_fst_4040_);
v___x_4052_ = l_Lean_mkApp6(v_val_4035_, v_arg_4019_, v_arg_4020_, v_fst_4040_, v_fst_4047_, v_snd_4041_, v_snd_4048_);
if (v_eqTrue_4021_ == 0)
{
v_fst_4054_ = v_fst_4047_;
v_snd_4055_ = v_fst_4040_;
goto v___jp_4053_;
}
else
{
lean_object* v___x_4085_; lean_object* v___x_4086_; 
v___x_4085_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0);
v___x_4086_ = l_Lean_mkIntAdd(v_fst_4040_, v___x_4085_);
v_fst_4054_ = v___x_4086_;
v_snd_4055_ = v_fst_4047_;
goto v___jp_4053_;
}
v___jp_4053_:
{
lean_object* v___x_4056_; 
lean_inc(v_a_4037_);
v___x_4056_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_4054_, v_a_4037_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_);
if (lean_obj_tag(v___x_4056_) == 0)
{
lean_object* v_a_4057_; lean_object* v___x_4058_; 
v_a_4057_ = lean_ctor_get(v___x_4056_, 0);
lean_inc(v_a_4057_);
lean_dec_ref(v___x_4056_);
v___x_4058_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_snd_4055_, v_a_4037_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_);
if (lean_obj_tag(v___x_4058_) == 0)
{
lean_object* v_a_4059_; lean_object* v___x_4061_; 
v_a_4059_ = lean_ctor_get(v___x_4058_, 0);
lean_inc_n(v_a_4059_, 2);
lean_dec_ref(v___x_4058_);
lean_inc(v_a_4057_);
if (v_isShared_4051_ == 0)
{
lean_ctor_set_tag(v___x_4050_, 3);
lean_ctor_set(v___x_4050_, 1, v_a_4059_);
lean_ctor_set(v___x_4050_, 0, v_a_4057_);
v___x_4061_ = v___x_4050_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4068_; 
v_reuseFailAlloc_4068_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4068_, 0, v_a_4057_);
lean_ctor_set(v_reuseFailAlloc_4068_, 1, v_a_4059_);
v___x_4061_ = v_reuseFailAlloc_4068_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4065_; 
v___x_4062_ = l_Int_Linear_Expr_norm(v___x_4061_);
lean_dec_ref(v___x_4061_);
v___x_4063_ = lean_alloc_ctor(2, 4, 1);
lean_ctor_set(v___x_4063_, 0, v_e_4018_);
lean_ctor_set(v___x_4063_, 1, v___x_4052_);
lean_ctor_set(v___x_4063_, 2, v_a_4057_);
lean_ctor_set(v___x_4063_, 3, v_a_4059_);
lean_ctor_set_uint8(v___x_4063_, sizeof(void*)*4, v_eqTrue_4021_);
if (v_isShared_4044_ == 0)
{
lean_ctor_set(v___x_4043_, 1, v___x_4063_);
lean_ctor_set(v___x_4043_, 0, v___x_4062_);
v___x_4065_ = v___x_4043_;
goto v_reusejp_4064_;
}
else
{
lean_object* v_reuseFailAlloc_4067_; 
v_reuseFailAlloc_4067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4067_, 0, v___x_4062_);
lean_ctor_set(v_reuseFailAlloc_4067_, 1, v___x_4063_);
v___x_4065_ = v_reuseFailAlloc_4067_;
goto v_reusejp_4064_;
}
v_reusejp_4064_:
{
lean_object* v___x_4066_; 
lean_inc(v___y_4033_);
lean_inc_ref(v___y_4032_);
lean_inc(v___y_4031_);
lean_inc_ref(v___y_4030_);
lean_inc(v___y_4029_);
lean_inc_ref(v___y_4028_);
lean_inc(v___y_4027_);
lean_inc_ref(v___y_4026_);
lean_inc(v___y_4025_);
lean_inc(v___y_4024_);
v___x_4066_ = lean_grind_cutsat_assert_le(v___x_4065_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_);
return v___x_4066_;
}
}
}
else
{
lean_object* v_a_4069_; lean_object* v___x_4071_; uint8_t v_isShared_4072_; uint8_t v_isSharedCheck_4076_; 
lean_dec(v_a_4057_);
lean_dec_ref(v___x_4052_);
lean_del_object(v___x_4050_);
lean_del_object(v___x_4043_);
lean_dec_ref(v_e_4018_);
v_a_4069_ = lean_ctor_get(v___x_4058_, 0);
v_isSharedCheck_4076_ = !lean_is_exclusive(v___x_4058_);
if (v_isSharedCheck_4076_ == 0)
{
v___x_4071_ = v___x_4058_;
v_isShared_4072_ = v_isSharedCheck_4076_;
goto v_resetjp_4070_;
}
else
{
lean_inc(v_a_4069_);
lean_dec(v___x_4058_);
v___x_4071_ = lean_box(0);
v_isShared_4072_ = v_isSharedCheck_4076_;
goto v_resetjp_4070_;
}
v_resetjp_4070_:
{
lean_object* v___x_4074_; 
if (v_isShared_4072_ == 0)
{
v___x_4074_ = v___x_4071_;
goto v_reusejp_4073_;
}
else
{
lean_object* v_reuseFailAlloc_4075_; 
v_reuseFailAlloc_4075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4075_, 0, v_a_4069_);
v___x_4074_ = v_reuseFailAlloc_4075_;
goto v_reusejp_4073_;
}
v_reusejp_4073_:
{
return v___x_4074_;
}
}
}
}
else
{
lean_object* v_a_4077_; lean_object* v___x_4079_; uint8_t v_isShared_4080_; uint8_t v_isSharedCheck_4084_; 
lean_dec_ref(v_snd_4055_);
lean_dec_ref(v___x_4052_);
lean_del_object(v___x_4050_);
lean_del_object(v___x_4043_);
lean_dec(v_a_4037_);
lean_dec_ref(v_e_4018_);
v_a_4077_ = lean_ctor_get(v___x_4056_, 0);
v_isSharedCheck_4084_ = !lean_is_exclusive(v___x_4056_);
if (v_isSharedCheck_4084_ == 0)
{
v___x_4079_ = v___x_4056_;
v_isShared_4080_ = v_isSharedCheck_4084_;
goto v_resetjp_4078_;
}
else
{
lean_inc(v_a_4077_);
lean_dec(v___x_4056_);
v___x_4079_ = lean_box(0);
v_isShared_4080_ = v_isSharedCheck_4084_;
goto v_resetjp_4078_;
}
v_resetjp_4078_:
{
lean_object* v___x_4082_; 
if (v_isShared_4080_ == 0)
{
v___x_4082_ = v___x_4079_;
goto v_reusejp_4081_;
}
else
{
lean_object* v_reuseFailAlloc_4083_; 
v_reuseFailAlloc_4083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4083_, 0, v_a_4077_);
v___x_4082_ = v_reuseFailAlloc_4083_;
goto v_reusejp_4081_;
}
v_reusejp_4081_:
{
return v___x_4082_;
}
}
}
}
}
}
else
{
lean_object* v_a_4088_; lean_object* v___x_4090_; uint8_t v_isShared_4091_; uint8_t v_isSharedCheck_4095_; 
lean_del_object(v___x_4043_);
lean_dec(v_snd_4041_);
lean_dec(v_fst_4040_);
lean_dec(v_a_4037_);
lean_dec(v_val_4035_);
lean_dec_ref(v_arg_4020_);
lean_dec_ref(v_arg_4019_);
lean_dec_ref(v_e_4018_);
v_a_4088_ = lean_ctor_get(v___x_4045_, 0);
v_isSharedCheck_4095_ = !lean_is_exclusive(v___x_4045_);
if (v_isSharedCheck_4095_ == 0)
{
v___x_4090_ = v___x_4045_;
v_isShared_4091_ = v_isSharedCheck_4095_;
goto v_resetjp_4089_;
}
else
{
lean_inc(v_a_4088_);
lean_dec(v___x_4045_);
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
}
}
else
{
lean_object* v_a_4097_; lean_object* v___x_4099_; uint8_t v_isShared_4100_; uint8_t v_isSharedCheck_4104_; 
lean_dec(v_a_4037_);
lean_dec(v_val_4035_);
lean_dec_ref(v_arg_4020_);
lean_dec_ref(v_arg_4019_);
lean_dec_ref(v_e_4018_);
v_a_4097_ = lean_ctor_get(v___x_4038_, 0);
v_isSharedCheck_4104_ = !lean_is_exclusive(v___x_4038_);
if (v_isSharedCheck_4104_ == 0)
{
v___x_4099_ = v___x_4038_;
v_isShared_4100_ = v_isSharedCheck_4104_;
goto v_resetjp_4098_;
}
else
{
lean_inc(v_a_4097_);
lean_dec(v___x_4038_);
v___x_4099_ = lean_box(0);
v_isShared_4100_ = v_isSharedCheck_4104_;
goto v_resetjp_4098_;
}
v_resetjp_4098_:
{
lean_object* v___x_4102_; 
if (v_isShared_4100_ == 0)
{
v___x_4102_ = v___x_4099_;
goto v_reusejp_4101_;
}
else
{
lean_object* v_reuseFailAlloc_4103_; 
v_reuseFailAlloc_4103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4103_, 0, v_a_4097_);
v___x_4102_ = v_reuseFailAlloc_4103_;
goto v_reusejp_4101_;
}
v_reusejp_4101_:
{
return v___x_4102_;
}
}
}
}
else
{
lean_object* v_a_4105_; lean_object* v___x_4107_; uint8_t v_isShared_4108_; uint8_t v_isSharedCheck_4112_; 
lean_dec(v_val_4035_);
lean_dec_ref(v_arg_4020_);
lean_dec_ref(v_arg_4019_);
lean_dec_ref(v_e_4018_);
v_a_4105_ = lean_ctor_get(v___x_4036_, 0);
v_isSharedCheck_4112_ = !lean_is_exclusive(v___x_4036_);
if (v_isSharedCheck_4112_ == 0)
{
v___x_4107_ = v___x_4036_;
v_isShared_4108_ = v_isSharedCheck_4112_;
goto v_resetjp_4106_;
}
else
{
lean_inc(v_a_4105_);
lean_dec(v___x_4036_);
v___x_4107_ = lean_box(0);
v_isShared_4108_ = v_isSharedCheck_4112_;
goto v_resetjp_4106_;
}
v_resetjp_4106_:
{
lean_object* v___x_4110_; 
if (v_isShared_4108_ == 0)
{
v___x_4110_ = v___x_4107_;
goto v_reusejp_4109_;
}
else
{
lean_object* v_reuseFailAlloc_4111_; 
v_reuseFailAlloc_4111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4111_, 0, v_a_4105_);
v___x_4110_ = v_reuseFailAlloc_4111_;
goto v_reusejp_4109_;
}
v_reusejp_4109_:
{
return v___x_4110_;
}
}
}
}
else
{
lean_object* v___x_4113_; lean_object* v___x_4114_; 
lean_dec(v_____x_4022_);
lean_dec_ref(v_arg_4020_);
lean_dec_ref(v_arg_4019_);
lean_dec_ref(v_e_4018_);
v___x_4113_ = lean_box(0);
v___x_4114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4114_, 0, v___x_4113_);
return v___x_4114_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__0___boxed(lean_object** _args){
lean_object* v_e_4115_ = _args[0];
lean_object* v_arg_4116_ = _args[1];
lean_object* v_arg_4117_ = _args[2];
lean_object* v_eqTrue_4118_ = _args[3];
lean_object* v_____x_4119_ = _args[4];
lean_object* v___y_4120_ = _args[5];
lean_object* v___y_4121_ = _args[6];
lean_object* v___y_4122_ = _args[7];
lean_object* v___y_4123_ = _args[8];
lean_object* v___y_4124_ = _args[9];
lean_object* v___y_4125_ = _args[10];
lean_object* v___y_4126_ = _args[11];
lean_object* v___y_4127_ = _args[12];
lean_object* v___y_4128_ = _args[13];
lean_object* v___y_4129_ = _args[14];
lean_object* v___y_4130_ = _args[15];
lean_object* v___y_4131_ = _args[16];
_start:
{
uint8_t v_eqTrue_boxed_4132_; lean_object* v_res_4133_; 
v_eqTrue_boxed_4132_ = lean_unbox(v_eqTrue_4118_);
v_res_4133_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__0(v_e_4115_, v_arg_4116_, v_arg_4117_, v_eqTrue_boxed_4132_, v_____x_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_);
lean_dec(v___y_4130_);
lean_dec_ref(v___y_4129_);
lean_dec(v___y_4128_);
lean_dec_ref(v___y_4127_);
lean_dec(v___y_4126_);
lean_dec_ref(v___y_4125_);
lean_dec(v___y_4124_);
lean_dec_ref(v___y_4123_);
lean_dec(v___y_4122_);
lean_dec(v___y_4121_);
lean_dec(v___y_4120_);
return v_res_4133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__1(uint8_t v_eqTrue_4134_, lean_object* v___f_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_){
_start:
{
if (v_eqTrue_4134_ == 0)
{
lean_object* v___x_4148_; 
v___x_4148_ = l_Lean_Meta_Grind_Arith_Cutsat_getOfNotLT_x3f___redArg(v___y_4136_, v___y_4137_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_);
if (lean_obj_tag(v___x_4148_) == 0)
{
lean_object* v_a_4149_; lean_object* v___x_4150_; 
v_a_4149_ = lean_ctor_get(v___x_4148_, 0);
lean_inc(v_a_4149_);
lean_dec_ref(v___x_4148_);
lean_inc(v___y_4146_);
lean_inc_ref(v___y_4145_);
lean_inc(v___y_4144_);
lean_inc_ref(v___y_4143_);
lean_inc(v___y_4142_);
lean_inc_ref(v___y_4141_);
lean_inc(v___y_4140_);
lean_inc_ref(v___y_4139_);
lean_inc(v___y_4138_);
lean_inc(v___y_4137_);
lean_inc(v___y_4136_);
v___x_4150_ = lean_apply_13(v___f_4135_, v_a_4149_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_, lean_box(0));
return v___x_4150_;
}
else
{
lean_object* v_a_4151_; lean_object* v___x_4153_; uint8_t v_isShared_4154_; uint8_t v_isSharedCheck_4158_; 
lean_dec_ref(v___f_4135_);
v_a_4151_ = lean_ctor_get(v___x_4148_, 0);
v_isSharedCheck_4158_ = !lean_is_exclusive(v___x_4148_);
if (v_isSharedCheck_4158_ == 0)
{
v___x_4153_ = v___x_4148_;
v_isShared_4154_ = v_isSharedCheck_4158_;
goto v_resetjp_4152_;
}
else
{
lean_inc(v_a_4151_);
lean_dec(v___x_4148_);
v___x_4153_ = lean_box(0);
v_isShared_4154_ = v_isSharedCheck_4158_;
goto v_resetjp_4152_;
}
v_resetjp_4152_:
{
lean_object* v___x_4156_; 
if (v_isShared_4154_ == 0)
{
v___x_4156_ = v___x_4153_;
goto v_reusejp_4155_;
}
else
{
lean_object* v_reuseFailAlloc_4157_; 
v_reuseFailAlloc_4157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4157_, 0, v_a_4151_);
v___x_4156_ = v_reuseFailAlloc_4157_;
goto v_reusejp_4155_;
}
v_reusejp_4155_:
{
return v___x_4156_;
}
}
}
}
else
{
lean_object* v___x_4159_; 
v___x_4159_ = l_Lean_Meta_Grind_Arith_Cutsat_getOfLT_x3f___redArg(v___y_4136_, v___y_4137_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_);
if (lean_obj_tag(v___x_4159_) == 0)
{
lean_object* v_a_4160_; lean_object* v___x_4161_; 
v_a_4160_ = lean_ctor_get(v___x_4159_, 0);
lean_inc(v_a_4160_);
lean_dec_ref(v___x_4159_);
lean_inc(v___y_4146_);
lean_inc_ref(v___y_4145_);
lean_inc(v___y_4144_);
lean_inc_ref(v___y_4143_);
lean_inc(v___y_4142_);
lean_inc_ref(v___y_4141_);
lean_inc(v___y_4140_);
lean_inc_ref(v___y_4139_);
lean_inc(v___y_4138_);
lean_inc(v___y_4137_);
lean_inc(v___y_4136_);
v___x_4161_ = lean_apply_13(v___f_4135_, v_a_4160_, v___y_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_, lean_box(0));
return v___x_4161_;
}
else
{
lean_object* v_a_4162_; lean_object* v___x_4164_; uint8_t v_isShared_4165_; uint8_t v_isSharedCheck_4169_; 
lean_dec_ref(v___f_4135_);
v_a_4162_ = lean_ctor_get(v___x_4159_, 0);
v_isSharedCheck_4169_ = !lean_is_exclusive(v___x_4159_);
if (v_isSharedCheck_4169_ == 0)
{
v___x_4164_ = v___x_4159_;
v_isShared_4165_ = v_isSharedCheck_4169_;
goto v_resetjp_4163_;
}
else
{
lean_inc(v_a_4162_);
lean_dec(v___x_4159_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__1___boxed(lean_object* v_eqTrue_4170_, lean_object* v___f_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_){
_start:
{
uint8_t v_eqTrue_boxed_4184_; lean_object* v_res_4185_; 
v_eqTrue_boxed_4184_ = lean_unbox(v_eqTrue_4170_);
v_res_4185_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__1(v_eqTrue_boxed_4184_, v___f_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_);
lean_dec(v___y_4182_);
lean_dec_ref(v___y_4181_);
lean_dec(v___y_4180_);
lean_dec_ref(v___y_4179_);
lean_dec(v___y_4178_);
lean_dec_ref(v___y_4177_);
lean_dec(v___y_4176_);
lean_dec_ref(v___y_4175_);
lean_dec(v___y_4174_);
lean_dec(v___y_4173_);
lean_dec(v___y_4172_);
return v_res_4185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt(lean_object* v_e_4191_, uint8_t v_eqTrue_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_, lean_object* v_a_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_, lean_object* v_a_4202_){
_start:
{
lean_object* v___x_4207_; 
v___x_4207_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_4195_);
if (lean_obj_tag(v___x_4207_) == 0)
{
lean_object* v_a_4208_; lean_object* v___x_4210_; uint8_t v_isShared_4211_; uint8_t v_isSharedCheck_4236_; 
v_a_4208_ = lean_ctor_get(v___x_4207_, 0);
v_isSharedCheck_4236_ = !lean_is_exclusive(v___x_4207_);
if (v_isSharedCheck_4236_ == 0)
{
v___x_4210_ = v___x_4207_;
v_isShared_4211_ = v_isSharedCheck_4236_;
goto v_resetjp_4209_;
}
else
{
lean_inc(v_a_4208_);
lean_dec(v___x_4207_);
v___x_4210_ = lean_box(0);
v_isShared_4211_ = v_isSharedCheck_4236_;
goto v_resetjp_4209_;
}
v_resetjp_4209_:
{
uint8_t v_lia_4212_; 
v_lia_4212_ = lean_ctor_get_uint8(v_a_4208_, sizeof(void*)*13 + 23);
lean_dec(v_a_4208_);
if (v_lia_4212_ == 0)
{
lean_object* v___x_4213_; lean_object* v___x_4215_; 
lean_dec_ref(v_e_4191_);
v___x_4213_ = lean_box(0);
if (v_isShared_4211_ == 0)
{
lean_ctor_set(v___x_4210_, 0, v___x_4213_);
v___x_4215_ = v___x_4210_;
goto v_reusejp_4214_;
}
else
{
lean_object* v_reuseFailAlloc_4216_; 
v_reuseFailAlloc_4216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4216_, 0, v___x_4213_);
v___x_4215_ = v_reuseFailAlloc_4216_;
goto v_reusejp_4214_;
}
v_reusejp_4214_:
{
return v___x_4215_;
}
}
else
{
lean_object* v___x_4217_; uint8_t v___x_4218_; 
lean_del_object(v___x_4210_);
lean_inc_ref(v_e_4191_);
v___x_4217_ = l_Lean_Expr_cleanupAnnotations(v_e_4191_);
v___x_4218_ = l_Lean_Expr_isApp(v___x_4217_);
if (v___x_4218_ == 0)
{
lean_dec_ref(v___x_4217_);
lean_dec_ref(v_e_4191_);
goto v___jp_4204_;
}
else
{
lean_object* v_arg_4219_; lean_object* v___x_4220_; uint8_t v___x_4221_; 
v_arg_4219_ = lean_ctor_get(v___x_4217_, 1);
lean_inc_ref(v_arg_4219_);
v___x_4220_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4217_);
v___x_4221_ = l_Lean_Expr_isApp(v___x_4220_);
if (v___x_4221_ == 0)
{
lean_dec_ref(v___x_4220_);
lean_dec_ref(v_arg_4219_);
lean_dec_ref(v_e_4191_);
goto v___jp_4204_;
}
else
{
lean_object* v_arg_4222_; lean_object* v___x_4223_; uint8_t v___x_4224_; 
v_arg_4222_ = lean_ctor_get(v___x_4220_, 1);
lean_inc_ref(v_arg_4222_);
v___x_4223_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4220_);
v___x_4224_ = l_Lean_Expr_isApp(v___x_4223_);
if (v___x_4224_ == 0)
{
lean_dec_ref(v___x_4223_);
lean_dec_ref(v_arg_4222_);
lean_dec_ref(v_arg_4219_);
lean_dec_ref(v_e_4191_);
goto v___jp_4204_;
}
else
{
lean_object* v___x_4225_; uint8_t v___x_4226_; 
v___x_4225_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4223_);
v___x_4226_ = l_Lean_Expr_isApp(v___x_4225_);
if (v___x_4226_ == 0)
{
lean_dec_ref(v___x_4225_);
lean_dec_ref(v_arg_4222_);
lean_dec_ref(v_arg_4219_);
lean_dec_ref(v_e_4191_);
goto v___jp_4204_;
}
else
{
lean_object* v_arg_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; uint8_t v___x_4230_; 
v_arg_4227_ = lean_ctor_get(v___x_4225_, 1);
lean_inc_ref(v_arg_4227_);
v___x_4228_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4225_);
v___x_4229_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___closed__2));
v___x_4230_ = l_Lean_Expr_isConstOf(v___x_4228_, v___x_4229_);
lean_dec_ref(v___x_4228_);
if (v___x_4230_ == 0)
{
lean_dec_ref(v_arg_4227_);
lean_dec_ref(v_arg_4222_);
lean_dec_ref(v_arg_4219_);
lean_dec_ref(v_e_4191_);
goto v___jp_4204_;
}
else
{
lean_object* v___x_4231_; lean_object* v___f_4232_; lean_object* v___x_4233_; lean_object* v___y_4234_; lean_object* v___x_4235_; 
v___x_4231_ = lean_box(v_eqTrue_4192_);
v___f_4232_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__0___boxed), 17, 4);
lean_closure_set(v___f_4232_, 0, v_e_4191_);
lean_closure_set(v___f_4232_, 1, v_arg_4222_);
lean_closure_set(v___f_4232_, 2, v_arg_4219_);
lean_closure_set(v___f_4232_, 3, v___x_4231_);
v___x_4233_ = lean_box(v_eqTrue_4192_);
v___y_4234_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___lam__1___boxed), 14, 2);
lean_closure_set(v___y_4234_, 0, v___x_4233_);
lean_closure_set(v___y_4234_, 1, v___f_4232_);
v___x_4235_ = l_Lean_Meta_Grind_Arith_Cutsat_ToIntM_run(v_arg_4227_, v___y_4234_, v_a_4193_, v_a_4194_, v_a_4195_, v_a_4196_, v_a_4197_, v_a_4198_, v_a_4199_, v_a_4200_, v_a_4201_, v_a_4202_);
return v___x_4235_;
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
lean_object* v_a_4237_; lean_object* v___x_4239_; uint8_t v_isShared_4240_; uint8_t v_isSharedCheck_4244_; 
lean_dec_ref(v_e_4191_);
v_a_4237_ = lean_ctor_get(v___x_4207_, 0);
v_isSharedCheck_4244_ = !lean_is_exclusive(v___x_4207_);
if (v_isSharedCheck_4244_ == 0)
{
v___x_4239_ = v___x_4207_;
v_isShared_4240_ = v_isSharedCheck_4244_;
goto v_resetjp_4238_;
}
else
{
lean_inc(v_a_4237_);
lean_dec(v___x_4207_);
v___x_4239_ = lean_box(0);
v_isShared_4240_ = v_isSharedCheck_4244_;
goto v_resetjp_4238_;
}
v_resetjp_4238_:
{
lean_object* v___x_4242_; 
if (v_isShared_4240_ == 0)
{
v___x_4242_ = v___x_4239_;
goto v_reusejp_4241_;
}
else
{
lean_object* v_reuseFailAlloc_4243_; 
v_reuseFailAlloc_4243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4243_, 0, v_a_4237_);
v___x_4242_ = v_reuseFailAlloc_4243_;
goto v_reusejp_4241_;
}
v_reusejp_4241_:
{
return v___x_4242_;
}
}
}
v___jp_4204_:
{
lean_object* v___x_4205_; lean_object* v___x_4206_; 
v___x_4205_ = lean_box(0);
v___x_4206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4206_, 0, v___x_4205_);
return v___x_4206_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt___boxed(lean_object* v_e_4245_, lean_object* v_eqTrue_4246_, lean_object* v_a_4247_, lean_object* v_a_4248_, lean_object* v_a_4249_, lean_object* v_a_4250_, lean_object* v_a_4251_, lean_object* v_a_4252_, lean_object* v_a_4253_, lean_object* v_a_4254_, lean_object* v_a_4255_, lean_object* v_a_4256_, lean_object* v_a_4257_){
_start:
{
uint8_t v_eqTrue_boxed_4258_; lean_object* v_res_4259_; 
v_eqTrue_boxed_4258_ = lean_unbox(v_eqTrue_4246_);
v_res_4259_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLt(v_e_4245_, v_eqTrue_boxed_4258_, v_a_4247_, v_a_4248_, v_a_4249_, v_a_4250_, v_a_4251_, v_a_4252_, v_a_4253_, v_a_4254_, v_a_4255_, v_a_4256_);
lean_dec(v_a_4256_);
lean_dec_ref(v_a_4255_);
lean_dec(v_a_4254_);
lean_dec_ref(v_a_4253_);
lean_dec(v_a_4252_);
lean_dec_ref(v_a_4251_);
lean_dec(v_a_4250_);
lean_dec_ref(v_a_4249_);
lean_dec(v_a_4248_);
lean_dec(v_a_4247_);
return v_res_4259_;
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
