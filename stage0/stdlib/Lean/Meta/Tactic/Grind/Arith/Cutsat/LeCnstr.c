// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.LeCnstr
// Imports: public import Lean.Meta.Tactic.Grind.Arith.Cutsat.Util import Init.Data.Int.OfNat import Lean.Meta.Tactic.Simp.Arith.Int import Lean.Meta.Tactic.Grind.Arith.Cutsat.Var import Lean.Meta.Tactic.Grind.Arith.Cutsat.Proof import Lean.Meta.Tactic.Grind.Arith.Cutsat.Nat import Lean.Meta.Tactic.Grind.Arith.Cutsat.Norm import Lean.Meta.Tactic.Grind.Arith.Cutsat.CommRing
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
lean_object* l_Lean_instInhabitedPersistentArrayNode_default___redArg();
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
lean_object* l_Lean_instInhabitedPersistentArray_default___redArg();
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Structural_isInstLEInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_Sym_getConfig___redArg(lean_object*);
lean_object* l_Lean_Meta_Sym_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_mul(lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_addConst(lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_normCommRing_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_cutsat_assert_le(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Expr_norm(lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_natToInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntLit(lean_object*);
lean_object* l_Lean_mkIntAdd(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__0_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__1_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__1_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_15_ = l_Int_Internal_Linear_Poly_isSorted(v_p_14_);
if (v___x_15_ == 0)
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; 
lean_inc_ref(v_p_14_);
v___x_16_ = l_Int_Internal_Linear_Poly_norm(v_p_14_);
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
v_k_7_ = l_Int_Internal_Linear_Poly_gcdCoeffs_x27(v_p_6_);
v___x_8_ = lean_unsigned_to_nat(1u);
v___x_9_ = lean_nat_dec_eq(v_k_7_, v___x_8_);
if (v___x_9_ == 0)
{
lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_10_ = lean_nat_to_int(v_k_7_);
v___x_11_ = l_Int_Internal_Linear_Poly_div(v___x_10_, v_p_6_);
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
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0_spec__0(lean_object* v_msgData_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_){
_start:
{
lean_object* v___x_25_; lean_object* v_env_26_; uint8_t v___x_27_; lean_object* v_env_28_; lean_object* v___x_29_; lean_object* v_toCold_30_; lean_object* v_mctx_31_; lean_object* v_lctx_32_; lean_object* v_options_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_25_ = lean_st_ref_get(v___y_23_);
v_env_26_ = lean_ctor_get(v___x_25_, 0);
lean_inc_ref(v_env_26_);
lean_dec(v___x_25_);
v___x_27_ = 0;
v_env_28_ = l_Lean_Environment_setRecordingDeps(v_env_26_, v___x_27_);
v___x_29_ = lean_st_ref_get(v___y_21_);
v_toCold_30_ = lean_ctor_get(v___y_22_, 0);
v_mctx_31_ = lean_ctor_get(v___x_29_, 0);
lean_inc_ref(v_mctx_31_);
lean_dec(v___x_29_);
v_lctx_32_ = lean_ctor_get(v___y_20_, 2);
v_options_33_ = lean_ctor_get(v_toCold_30_, 2);
lean_inc_ref(v_options_33_);
lean_inc_ref(v_lctx_32_);
v___x_34_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_34_, 0, v_env_28_);
lean_ctor_set(v___x_34_, 1, v_mctx_31_);
lean_ctor_set(v___x_34_, 2, v_lctx_32_);
lean_ctor_set(v___x_34_, 3, v_options_33_);
v___x_35_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_35_, 0, v___x_34_);
lean_ctor_set(v___x_35_, 1, v_msgData_19_);
v___x_36_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_36_, 0, v___x_35_);
return v___x_36_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_19_ = stack[0].m_obj;
lean_object* v___y_20_ = stack[1].m_obj;
lean_object* v___y_21_ = stack[2].m_obj;
lean_object* v___y_22_ = stack[3].m_obj;
lean_object* v___y_23_ = stack[4].m_obj;
lean_object* v_res_37_;
v_res_37_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0_spec__0(v_msgData_19_, v___y_20_, v___y_21_, v___y_22_, v___y_23_);
stack->m_obj
 = v_res_37_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0_spec__0___boxed(lean_object* v_msgData_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0_spec__0(v_msgData_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_);
lean_dec(v___y_42_);
lean_dec_ref(v___y_41_);
lean_dec(v___y_40_);
lean_dec_ref(v___y_39_);
return v_res_44_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_45_; double v___x_46_; 
v___x_45_ = lean_unsigned_to_nat(0u);
v___x_46_ = lean_float_of_nat(v___x_45_);
return v___x_46_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(lean_object* v_cls_50_, lean_object* v_msg_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_){
_start:
{
lean_object* v_ref_57_; lean_object* v___x_58_; lean_object* v_a_59_; lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_104_; 
v_ref_57_ = lean_ctor_get(v___y_54_, 2);
v___x_58_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0_spec__0(v_msg_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
v_a_59_ = lean_ctor_get(v___x_58_, 0);
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_58_);
if (v_isSharedCheck_104_ == 0)
{
v___x_61_ = v___x_58_;
v_isShared_62_ = v_isSharedCheck_104_;
goto v_resetjp_60_;
}
else
{
lean_inc(v_a_59_);
lean_dec(v___x_58_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_104_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v___x_63_; lean_object* v_traceState_64_; lean_object* v_env_65_; lean_object* v_nextMacroScope_66_; lean_object* v_ngen_67_; lean_object* v_auxDeclNGen_68_; lean_object* v_cache_69_; lean_object* v_recordedDeps_70_; lean_object* v_messages_71_; lean_object* v_infoState_72_; lean_object* v_snapshotTasks_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_103_; 
v___x_63_ = lean_st_ref_take(v___y_55_);
v_traceState_64_ = lean_ctor_get(v___x_63_, 4);
v_env_65_ = lean_ctor_get(v___x_63_, 0);
v_nextMacroScope_66_ = lean_ctor_get(v___x_63_, 1);
v_ngen_67_ = lean_ctor_get(v___x_63_, 2);
v_auxDeclNGen_68_ = lean_ctor_get(v___x_63_, 3);
v_cache_69_ = lean_ctor_get(v___x_63_, 5);
v_recordedDeps_70_ = lean_ctor_get(v___x_63_, 6);
v_messages_71_ = lean_ctor_get(v___x_63_, 7);
v_infoState_72_ = lean_ctor_get(v___x_63_, 8);
v_snapshotTasks_73_ = lean_ctor_get(v___x_63_, 9);
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_63_);
if (v_isSharedCheck_103_ == 0)
{
v___x_75_ = v___x_63_;
v_isShared_76_ = v_isSharedCheck_103_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_snapshotTasks_73_);
lean_inc(v_infoState_72_);
lean_inc(v_messages_71_);
lean_inc(v_recordedDeps_70_);
lean_inc(v_cache_69_);
lean_inc(v_traceState_64_);
lean_inc(v_auxDeclNGen_68_);
lean_inc(v_ngen_67_);
lean_inc(v_nextMacroScope_66_);
lean_inc(v_env_65_);
lean_dec(v___x_63_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_103_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
uint64_t v_tid_77_; lean_object* v_traces_78_; lean_object* v___x_80_; uint8_t v_isShared_81_; uint8_t v_isSharedCheck_102_; 
v_tid_77_ = lean_ctor_get_uint64(v_traceState_64_, sizeof(void*)*1);
v_traces_78_ = lean_ctor_get(v_traceState_64_, 0);
v_isSharedCheck_102_ = !lean_is_exclusive(v_traceState_64_);
if (v_isSharedCheck_102_ == 0)
{
v___x_80_ = v_traceState_64_;
v_isShared_81_ = v_isSharedCheck_102_;
goto v_resetjp_79_;
}
else
{
lean_inc(v_traces_78_);
lean_dec(v_traceState_64_);
v___x_80_ = lean_box(0);
v_isShared_81_ = v_isSharedCheck_102_;
goto v_resetjp_79_;
}
v_resetjp_79_:
{
lean_object* v___x_82_; lean_object* v___x_83_; double v___x_84_; uint8_t v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_93_; 
v___x_82_ = lean_box(0);
v___x_83_ = lean_box(0);
v___x_84_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__0);
v___x_85_ = 0;
v___x_86_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__1));
v___x_87_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_87_, 0, v_cls_50_);
lean_ctor_set(v___x_87_, 1, v___x_83_);
lean_ctor_set(v___x_87_, 2, v___x_86_);
lean_ctor_set_float(v___x_87_, sizeof(void*)*3, v___x_84_);
lean_ctor_set_float(v___x_87_, sizeof(void*)*3 + 8, v___x_84_);
lean_ctor_set_uint8(v___x_87_, sizeof(void*)*3 + 16, v___x_85_);
v___x_88_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__2));
v___x_89_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_89_, 0, v___x_87_);
lean_ctor_set(v___x_89_, 1, v_a_59_);
lean_ctor_set(v___x_89_, 2, v___x_88_);
lean_inc(v_ref_57_);
v___x_90_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_90_, 0, v_ref_57_);
lean_ctor_set(v___x_90_, 1, v___x_89_);
v___x_91_ = l_Lean_PersistentArray_push___redArg(v_traces_78_, v___x_90_);
if (v_isShared_81_ == 0)
{
lean_ctor_set(v___x_80_, 0, v___x_91_);
v___x_93_ = v___x_80_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v___x_91_);
lean_ctor_set_uint64(v_reuseFailAlloc_101_, sizeof(void*)*1, v_tid_77_);
v___x_93_ = v_reuseFailAlloc_101_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
lean_object* v___x_95_; 
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 4, v___x_93_);
v___x_95_ = v___x_75_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_env_65_);
lean_ctor_set(v_reuseFailAlloc_100_, 1, v_nextMacroScope_66_);
lean_ctor_set(v_reuseFailAlloc_100_, 2, v_ngen_67_);
lean_ctor_set(v_reuseFailAlloc_100_, 3, v_auxDeclNGen_68_);
lean_ctor_set(v_reuseFailAlloc_100_, 4, v___x_93_);
lean_ctor_set(v_reuseFailAlloc_100_, 5, v_cache_69_);
lean_ctor_set(v_reuseFailAlloc_100_, 6, v_recordedDeps_70_);
lean_ctor_set(v_reuseFailAlloc_100_, 7, v_messages_71_);
lean_ctor_set(v_reuseFailAlloc_100_, 8, v_infoState_72_);
lean_ctor_set(v_reuseFailAlloc_100_, 9, v_snapshotTasks_73_);
v___x_95_ = v_reuseFailAlloc_100_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
lean_object* v___x_96_; lean_object* v___x_98_; 
v___x_96_ = lean_st_ref_put(v___y_55_, v___x_95_);
if (v_isShared_62_ == 0)
{
lean_ctor_set(v___x_61_, 0, v___x_82_);
v___x_98_ = v___x_61_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v___x_82_);
v___x_98_ = v_reuseFailAlloc_99_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
return v___x_98_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_50_ = stack[0].m_obj;
lean_object* v_msg_51_ = stack[1].m_obj;
lean_object* v___y_52_ = stack[2].m_obj;
lean_object* v___y_53_ = stack[3].m_obj;
lean_object* v___y_54_ = stack[4].m_obj;
lean_object* v___y_55_ = stack[5].m_obj;
lean_object* v_res_105_;
v_res_105_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v_cls_50_, v_msg_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
stack->m_obj
 = v_res_105_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___boxed(lean_object* v_cls_106_, lean_object* v_msg_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v_cls_106_, v_msg_107_, v___y_108_, v___y_109_, v___y_110_, v___y_111_);
lean_dec(v___y_111_);
lean_dec_ref(v___y_110_);
lean_dec(v___y_109_);
lean_dec_ref(v___y_108_);
return v_res_113_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6(void){
_start:
{
lean_object* v_cls_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v_cls_124_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__3));
v___x_125_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_126_ = l_Lean_Name_append(v___x_125_, v_cls_124_);
return v___x_126_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__8(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__7));
v___x_129_ = l_Lean_stringToMessageData(v___x_128_);
return v___x_129_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9(void){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = lean_unsigned_to_nat(0u);
v___x_131_ = lean_nat_to_int(v___x_130_);
return v___x_131_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq(lean_object* v_a_132_, lean_object* v_x_133_, lean_object* v_c_u2081_134_, lean_object* v_b_135_, lean_object* v_c_u2082_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_, lean_object* v_a_145_, lean_object* v_a_146_){
_start:
{
lean_object* v___y_149_; lean_object* v___y_154_; lean_object* v_p_207_; lean_object* v_p_208_; lean_object* v___x_209_; uint8_t v___x_210_; 
v_p_207_ = lean_ctor_get(v_c_u2081_134_, 0);
v_p_208_ = lean_ctor_get(v_c_u2082_136_, 0);
v___x_209_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9);
v___x_210_ = lean_int_dec_le(v___x_209_, v_a_132_);
if (v___x_210_ == 0)
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
lean_inc_ref(v_p_207_);
v___x_211_ = l_Int_Internal_Linear_Poly_mul(v_p_207_, v_b_135_);
v___x_212_ = lean_int_neg(v_a_132_);
lean_inc_ref(v_p_208_);
v___x_213_ = l_Int_Internal_Linear_Poly_mul(v_p_208_, v___x_212_);
lean_dec(v___x_212_);
v___x_214_ = l_Int_Internal_Linear_Poly_combine(v___x_211_, v___x_213_);
v___y_154_ = v___x_214_;
goto v___jp_153_;
}
else
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; 
lean_inc_ref(v_p_208_);
v___x_215_ = l_Int_Internal_Linear_Poly_mul(v_p_208_, v_a_132_);
v___x_216_ = lean_int_neg(v_b_135_);
lean_inc_ref(v_p_207_);
v___x_217_ = l_Int_Internal_Linear_Poly_mul(v_p_207_, v___x_216_);
lean_dec(v___x_216_);
v___x_218_ = l_Int_Internal_Linear_Poly_combine(v___x_215_, v___x_217_);
v___y_154_ = v___x_218_;
goto v___jp_153_;
}
v___jp_148_:
{
lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_150_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v___x_150_, 0, v_x_133_);
lean_ctor_set(v___x_150_, 1, v_c_u2081_134_);
lean_ctor_set(v___x_150_, 2, v_c_u2082_136_);
v___x_151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_151_, 0, v___y_149_);
lean_ctor_set(v___x_151_, 1, v___x_150_);
v___x_152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
return v___x_152_;
}
v___jp_153_:
{
lean_object* v_toCold_155_; lean_object* v_options_156_; uint8_t v_hasTrace_157_; 
v_toCold_155_ = lean_ctor_get(v_a_145_, 0);
v_options_156_ = lean_ctor_get(v_toCold_155_, 2);
v_hasTrace_157_ = lean_ctor_get_uint8(v_options_156_, sizeof(void*)*1);
if (v_hasTrace_157_ == 0)
{
v___y_149_ = v___y_154_;
goto v___jp_148_;
}
else
{
lean_object* v_inheritedTraceOptions_158_; lean_object* v_cls_159_; lean_object* v___x_160_; uint8_t v___x_161_; 
v_inheritedTraceOptions_158_ = lean_ctor_get(v_toCold_155_, 11);
v_cls_159_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__3));
v___x_160_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6);
v___x_161_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_158_, v_options_156_, v___x_160_);
if (v___x_161_ == 0)
{
v___y_149_ = v___y_154_;
goto v___jp_148_;
}
else
{
lean_object* v___x_162_; 
v___x_162_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_x_133_, v_a_137_, v_a_145_);
if (lean_obj_tag(v___x_162_) == 0)
{
lean_object* v_a_163_; lean_object* v___x_164_; 
v_a_163_ = lean_ctor_get(v___x_162_, 0);
lean_inc(v_a_163_);
lean_dec_ref_known(v___x_162_, 1);
lean_inc_ref(v_c_u2081_134_);
v___x_164_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_u2081_134_, v_a_137_, v_a_145_);
if (lean_obj_tag(v___x_164_) == 0)
{
lean_object* v_a_165_; lean_object* v___x_166_; 
v_a_165_ = lean_ctor_get(v___x_164_, 0);
lean_inc(v_a_165_);
lean_dec_ref_known(v___x_164_, 1);
lean_inc_ref(v_c_u2082_136_);
v___x_166_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2082_136_, v_a_137_, v_a_145_);
if (lean_obj_tag(v___x_166_) == 0)
{
lean_object* v_a_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v_a_167_ = lean_ctor_get(v___x_166_, 0);
lean_inc(v_a_167_);
lean_dec_ref_known(v___x_166_, 1);
v___x_168_ = l_Lean_MessageData_ofExpr(v_a_163_);
v___x_169_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__8);
v___x_170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_168_);
lean_ctor_set(v___x_170_, 1, v___x_169_);
v___x_171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
lean_ctor_set(v___x_171_, 1, v_a_165_);
v___x_172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
lean_ctor_set(v___x_172_, 1, v___x_169_);
v___x_173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
lean_ctor_set(v___x_173_, 1, v_a_167_);
v___x_174_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v_cls_159_, v___x_173_, v_a_143_, v_a_144_, v_a_145_, v_a_146_);
if (lean_obj_tag(v___x_174_) == 0)
{
lean_dec_ref_known(v___x_174_, 1);
v___y_149_ = v___y_154_;
goto v___jp_148_;
}
else
{
lean_object* v_a_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_182_; 
lean_dec_ref(v___y_154_);
lean_dec_ref(v_c_u2082_136_);
lean_dec_ref(v_c_u2081_134_);
lean_dec(v_x_133_);
v_a_175_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_182_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_182_ == 0)
{
v___x_177_ = v___x_174_;
v_isShared_178_ = v_isSharedCheck_182_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_a_175_);
lean_dec(v___x_174_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_182_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_180_; 
if (v_isShared_178_ == 0)
{
v___x_180_ = v___x_177_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_a_175_);
v___x_180_ = v_reuseFailAlloc_181_;
goto v_reusejp_179_;
}
v_reusejp_179_:
{
return v___x_180_;
}
}
}
}
else
{
lean_object* v_a_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_190_; 
lean_dec(v_a_165_);
lean_dec(v_a_163_);
lean_dec_ref(v___y_154_);
lean_dec_ref(v_c_u2082_136_);
lean_dec_ref(v_c_u2081_134_);
lean_dec(v_x_133_);
v_a_183_ = lean_ctor_get(v___x_166_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_190_ == 0)
{
v___x_185_ = v___x_166_;
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_a_183_);
lean_dec(v___x_166_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_190_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_188_; 
if (v_isShared_186_ == 0)
{
v___x_188_ = v___x_185_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_a_183_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
}
else
{
lean_object* v_a_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_198_; 
lean_dec(v_a_163_);
lean_dec_ref(v___y_154_);
lean_dec_ref(v_c_u2082_136_);
lean_dec_ref(v_c_u2081_134_);
lean_dec(v_x_133_);
v_a_191_ = lean_ctor_get(v___x_164_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_164_);
if (v_isSharedCheck_198_ == 0)
{
v___x_193_ = v___x_164_;
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_a_191_);
lean_dec(v___x_164_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_198_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
lean_object* v___x_196_; 
if (v_isShared_194_ == 0)
{
v___x_196_ = v___x_193_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v_a_191_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
}
else
{
lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_206_; 
lean_dec_ref(v___y_154_);
lean_dec_ref(v_c_u2082_136_);
lean_dec_ref(v_c_u2081_134_);
lean_dec(v_x_133_);
v_a_199_ = lean_ctor_get(v___x_162_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_206_ == 0)
{
v___x_201_ = v___x_162_;
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_162_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_204_; 
if (v_isShared_202_ == 0)
{
v___x_204_ = v___x_201_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_a_199_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_132_ = stack[0].m_obj;
lean_object* v_x_133_ = stack[1].m_obj;
lean_object* v_c_u2081_134_ = stack[2].m_obj;
lean_object* v_b_135_ = stack[3].m_obj;
lean_object* v_c_u2082_136_ = stack[4].m_obj;
lean_object* v_a_137_ = stack[5].m_obj;
lean_object* v_a_138_ = stack[6].m_obj;
lean_object* v_a_139_ = stack[7].m_obj;
lean_object* v_a_140_ = stack[8].m_obj;
lean_object* v_a_141_ = stack[9].m_obj;
lean_object* v_a_142_ = stack[10].m_obj;
lean_object* v_a_143_ = stack[11].m_obj;
lean_object* v_a_144_ = stack[12].m_obj;
lean_object* v_a_145_ = stack[13].m_obj;
lean_object* v_a_146_ = stack[14].m_obj;
lean_object* v_res_219_;
v_res_219_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq(v_a_132_, v_x_133_, v_c_u2081_134_, v_b_135_, v_c_u2082_136_, v_a_137_, v_a_138_, v_a_139_, v_a_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_, v_a_145_, v_a_146_);
stack->m_obj
 = v_res_219_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___boxed(lean_object* v_a_220_, lean_object* v_x_221_, lean_object* v_c_u2081_222_, lean_object* v_b_223_, lean_object* v_c_u2082_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq(v_a_220_, v_x_221_, v_c_u2081_222_, v_b_223_, v_c_u2082_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_);
lean_dec(v_a_234_);
lean_dec_ref(v_a_233_);
lean_dec(v_a_232_);
lean_dec_ref(v_a_231_);
lean_dec(v_a_230_);
lean_dec_ref(v_a_229_);
lean_dec(v_a_228_);
lean_dec_ref(v_a_227_);
lean_dec(v_a_226_);
lean_dec(v_a_225_);
lean_dec(v_b_223_);
lean_dec(v_a_220_);
return v_res_236_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0(lean_object* v_cls_237_, lean_object* v_msg_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v_cls_237_, v_msg_238_, v___y_245_, v___y_246_, v___y_247_, v___y_248_);
return v___x_250_;
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_237_ = stack[0].m_obj;
lean_object* v_msg_238_ = stack[1].m_obj;
lean_object* v___y_239_ = stack[2].m_obj;
lean_object* v___y_240_ = stack[3].m_obj;
lean_object* v___y_241_ = stack[4].m_obj;
lean_object* v___y_242_ = stack[5].m_obj;
lean_object* v___y_243_ = stack[6].m_obj;
lean_object* v___y_244_ = stack[7].m_obj;
lean_object* v___y_245_ = stack[8].m_obj;
lean_object* v___y_246_ = stack[9].m_obj;
lean_object* v___y_247_ = stack[10].m_obj;
lean_object* v___y_248_ = stack[11].m_obj;
lean_object* v_res_251_;
v_res_251_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0(v_cls_237_, v_msg_238_, v___y_239_, v___y_240_, v___y_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_);
stack->m_obj
 = v_res_251_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___boxed(lean_object* v_cls_252_, lean_object* v_msg_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0(v_cls_252_, v_msg_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, v___y_260_, v___y_261_, v___y_262_, v___y_263_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
lean_dec(v___y_261_);
lean_dec_ref(v___y_260_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v___y_255_);
lean_dec(v___y_254_);
return v_res_265_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = l_Lean_maxRecDepthErrorMessage;
v___x_272_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_272_, 0, v___x_271_);
return v___x_272_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__3);
v___x_274_ = l_Lean_MessageData_ofFormat(v___x_273_);
return v___x_274_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_275_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__4);
v___x_276_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__2));
v___x_277_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
lean_ctor_set(v___x_277_, 1, v___x_275_);
return v___x_277_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg(lean_object* v_ref_278_){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_280_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__5);
v___x_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_281_, 0, v_ref_278_);
lean_ctor_set(v___x_281_, 1, v___x_280_);
v___x_282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_282_, 0, v___x_281_);
return v___x_282_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_278_ = stack[0].m_obj;
lean_object* v_res_283_;
v_res_283_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg(v_ref_278_);
stack->m_obj
 = v_res_283_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___boxed(lean_object* v_ref_284_, lean_object* v___y_285_){
_start:
{
lean_object* v_res_286_; 
v_res_286_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg(v_ref_284_);
return v_res_286_;
}
}
lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0(lean_object* v_00_u03b1_287_, lean_object* v_ref_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg(v_ref_288_);
return v___x_300_;
}
}
LEAN_EXPORT void l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_288_ = stack[1].m_obj;
lean_object* v___y_289_ = stack[2].m_obj;
lean_object* v___y_290_ = stack[3].m_obj;
lean_object* v___y_291_ = stack[4].m_obj;
lean_object* v___y_292_ = stack[5].m_obj;
lean_object* v___y_293_ = stack[6].m_obj;
lean_object* v___y_294_ = stack[7].m_obj;
lean_object* v___y_295_ = stack[8].m_obj;
lean_object* v___y_296_ = stack[9].m_obj;
lean_object* v___y_297_ = stack[10].m_obj;
lean_object* v___y_298_ = stack[11].m_obj;
lean_object* v_res_301_;
v_res_301_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0(lean_box(0), v_ref_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_);
stack->m_obj
 = v_res_301_;
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___boxed(lean_object* v_00_u03b1_302_, lean_object* v_ref_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
lean_object* v_res_315_; 
v_res_315_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0(v_00_u03b1_302_, v_ref_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_);
lean_dec(v___y_313_);
lean_dec_ref(v___y_312_);
lean_dec(v___y_311_);
lean_dec_ref(v___y_310_);
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
lean_dec(v___y_305_);
lean_dec(v___y_304_);
return v_res_315_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts(lean_object* v_c_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_){
_start:
{
lean_object* v_p_328_; lean_object* v_toCold_329_; lean_object* v_currRecDepth_330_; lean_object* v_ref_331_; uint16_t v_optionFlags_332_; uint8_t v_suppressElabErrors_333_; uint8_t v_isRecordingDeps_334_; lean_object* v_maxRecDepth_366_; lean_object* v___x_367_; uint8_t v___x_368_; 
v_p_328_ = lean_ctor_get(v_c_316_, 0);
v_toCold_329_ = lean_ctor_get(v_a_325_, 0);
lean_inc_ref(v_toCold_329_);
v_currRecDepth_330_ = lean_ctor_get(v_a_325_, 1);
lean_inc(v_currRecDepth_330_);
v_ref_331_ = lean_ctor_get(v_a_325_, 2);
lean_inc(v_ref_331_);
v_optionFlags_332_ = lean_ctor_get_uint16(v_a_325_, sizeof(void*)*3);
v_suppressElabErrors_333_ = lean_ctor_get_uint8(v_a_325_, sizeof(void*)*3 + 2);
v_isRecordingDeps_334_ = lean_ctor_get_uint8(v_a_325_, sizeof(void*)*3 + 3);
lean_dec_ref(v_a_325_);
v_maxRecDepth_366_ = lean_ctor_get(v_toCold_329_, 3);
v___x_367_ = lean_unsigned_to_nat(0u);
v___x_368_ = lean_nat_dec_eq(v_maxRecDepth_366_, v___x_367_);
if (v___x_368_ == 0)
{
uint8_t v___x_369_; 
v___x_369_ = lean_nat_dec_eq(v_currRecDepth_330_, v_maxRecDepth_366_);
if (v___x_369_ == 0)
{
goto v___jp_335_;
}
else
{
lean_object* v___x_370_; 
lean_dec(v_currRecDepth_330_);
lean_dec_ref(v_toCold_329_);
lean_dec_ref(v_c_316_);
v___x_370_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg(v_ref_331_);
return v___x_370_;
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
v___x_337_ = lean_nat_add(v_currRecDepth_330_, v___x_336_);
lean_dec(v_currRecDepth_330_);
v___x_338_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_338_, 0, v_toCold_329_);
lean_ctor_set(v___x_338_, 1, v___x_337_);
lean_ctor_set(v___x_338_, 2, v_ref_331_);
lean_ctor_set_uint16(v___x_338_, sizeof(void*)*3, v_optionFlags_332_);
lean_ctor_set_uint8(v___x_338_, sizeof(void*)*3 + 2, v_suppressElabErrors_333_);
lean_ctor_set_uint8(v___x_338_, sizeof(void*)*3 + 3, v_isRecordingDeps_334_);
lean_inc_ref(v_p_328_);
v___x_339_ = l_Int_Internal_Linear_Poly_findVarToSubst___redArg(v_p_328_, v_a_317_, v___x_338_);
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
lean_dec_ref_known(v_a_340_, 1);
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
v___x_350_ = l_Int_Internal_Linear_Poly_coeff(v_p_349_, v_fst_348_);
v___x_351_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq(v___x_350_, v_fst_348_, v_snd_346_, v_fst_347_, v_c_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v___x_338_, v_a_326_);
lean_dec(v_fst_347_);
lean_dec(v___x_350_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v_a_352_; 
v_a_352_ = lean_ctor_get(v___x_351_, 0);
lean_inc(v_a_352_);
lean_dec_ref_known(v___x_351_, 1);
v_c_316_ = v_a_352_;
v_a_325_ = v___x_338_;
goto _start;
}
else
{
lean_dec_ref_known(v___x_338_, 3);
return v___x_351_;
}
}
else
{
lean_object* v___x_355_; 
lean_dec(v_a_340_);
lean_dec_ref_known(v___x_338_, 3);
if (v_isShared_343_ == 0)
{
lean_ctor_set(v___x_342_, 0, v_c_316_);
v___x_355_ = v___x_342_;
goto v_reusejp_354_;
}
else
{
lean_object* v_reuseFailAlloc_356_; 
v_reuseFailAlloc_356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_356_, 0, v_c_316_);
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
lean_dec_ref_known(v___x_338_, 3);
lean_dec_ref(v_c_316_);
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
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_316_ = stack[0].m_obj;
lean_object* v_a_317_ = stack[1].m_obj;
lean_object* v_a_318_ = stack[2].m_obj;
lean_object* v_a_319_ = stack[3].m_obj;
lean_object* v_a_320_ = stack[4].m_obj;
lean_object* v_a_321_ = stack[5].m_obj;
lean_object* v_a_322_ = stack[6].m_obj;
lean_object* v_a_323_ = stack[7].m_obj;
lean_object* v_a_324_ = stack[8].m_obj;
lean_object* v_a_325_ = stack[9].m_obj;
lean_object* v_a_326_ = stack[10].m_obj;
lean_object* v_res_371_;
v_res_371_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts(v_c_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
stack->m_obj
 = v_res_371_;
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
uint8_t l_Int_Internal_Linear_Poly_isNegEq(lean_object* v_p_u2081_385_, lean_object* v_p_u2082_386_){
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
lean_object* v_k_392_; lean_object* v_v_393_; lean_object* v_p_394_; lean_object* v_k_395_; lean_object* v_v_396_; lean_object* v_p_397_; lean_object* v___x_398_; uint8_t v___x_399_; 
v_k_392_ = lean_ctor_get(v_p_u2081_385_, 0);
v_v_393_ = lean_ctor_get(v_p_u2081_385_, 1);
v_p_394_ = lean_ctor_get(v_p_u2081_385_, 2);
v_k_395_ = lean_ctor_get(v_p_u2082_386_, 0);
v_v_396_ = lean_ctor_get(v_p_u2082_386_, 1);
v_p_397_ = lean_ctor_get(v_p_u2082_386_, 2);
v___x_398_ = lean_int_neg(v_k_395_);
v___x_399_ = lean_int_dec_eq(v_k_392_, v___x_398_);
lean_dec(v___x_398_);
if (v___x_399_ == 0)
{
return v___x_399_;
}
else
{
uint8_t v___x_400_; 
v___x_400_ = lean_nat_dec_eq(v_v_393_, v_v_396_);
if (v___x_400_ == 0)
{
return v___x_400_;
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
uint8_t v___x_402_; 
v___x_402_ = 0;
return v___x_402_;
}
}
}
}
LEAN_EXPORT void l_Int_Internal_Linear_Poly_isNegEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_p_u2081_385_ = stack[0].m_obj;
lean_object* v_p_u2082_386_ = stack[1].m_obj;
uint8_t v_res_403_;
v_res_403_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_u2081_385_, v_p_u2082_386_);
stack->m_num = v_res_403_;
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isNegEq___boxed(lean_object* v_p_u2081_404_, lean_object* v_p_u2082_405_){
_start:
{
uint8_t v_res_406_; lean_object* v_r_407_; 
v_res_406_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_u2081_404_, v_p_u2082_405_);
lean_dec_ref(v_p_u2082_405_);
lean_dec_ref(v_p_u2081_404_);
v_r_407_ = lean_box(v_res_406_);
return v_r_407_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(lean_object* v_c_408_, lean_object* v_as_409_, size_t v_i_410_, size_t v_stop_411_, lean_object* v_b_412_){
_start:
{
lean_object* v___y_414_; uint8_t v___x_418_; 
v___x_418_ = lean_usize_dec_eq(v_i_410_, v_stop_411_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; lean_object* v_p_420_; lean_object* v_p_421_; uint8_t v___x_422_; 
v___x_419_ = lean_array_uget_borrowed(v_as_409_, v_i_410_);
v_p_420_ = lean_ctor_get(v___x_419_, 0);
v_p_421_ = lean_ctor_get(v_c_408_, 0);
v___x_422_ = l_Int_Internal_Linear_instBEqPoly_beq(v_p_420_, v_p_421_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; 
lean_inc(v___x_419_);
v___x_423_ = l_Lean_PersistentArray_push___redArg(v_b_412_, v___x_419_);
v___y_414_ = v___x_423_;
goto v___jp_413_;
}
else
{
v___y_414_ = v_b_412_;
goto v___jp_413_;
}
}
else
{
return v_b_412_;
}
v___jp_413_:
{
size_t v___x_415_; size_t v___x_416_; 
v___x_415_ = ((size_t)1ULL);
v___x_416_ = lean_usize_add(v_i_410_, v___x_415_);
v_i_410_ = v___x_416_;
v_b_412_ = v___y_414_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_408_ = stack[0].m_obj;
lean_object* v_as_409_ = stack[1].m_obj;
size_t v_i_410_ = stack[2].m_num;
size_t v_stop_411_ = stack[3].m_num;
lean_object* v_b_412_ = stack[4].m_obj;
lean_object* v_res_424_;
v_res_424_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v_c_408_, v_as_409_, v_i_410_, v_stop_411_, v_b_412_);
stack->m_obj
 = v_res_424_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1___boxed(lean_object* v_c_425_, lean_object* v_as_426_, lean_object* v_i_427_, lean_object* v_stop_428_, lean_object* v_b_429_){
_start:
{
size_t v_i_boxed_430_; size_t v_stop_boxed_431_; lean_object* v_res_432_; 
v_i_boxed_430_ = lean_unbox_usize(v_i_427_);
lean_dec(v_i_427_);
v_stop_boxed_431_ = lean_unbox_usize(v_stop_428_);
lean_dec(v_stop_428_);
v_res_432_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v_c_425_, v_as_426_, v_i_boxed_430_, v_stop_boxed_431_, v_b_429_);
lean_dec_ref(v_as_426_);
lean_dec_ref(v_c_425_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2(lean_object* v_c_433_, lean_object* v_x_434_, lean_object* v_x_435_){
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
size_t v___x_440_; size_t v___x_441_; lean_object* v___x_442_; 
v___x_440_ = ((size_t)0ULL);
v___x_441_ = lean_usize_of_nat(v___x_438_);
v___x_442_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v_c_433_, v_cs_436_, v___x_440_, v___x_441_, v_x_435_);
return v___x_442_;
}
}
else
{
lean_object* v_vs_443_; lean_object* v___x_444_; lean_object* v___x_445_; uint8_t v___x_446_; 
v_vs_443_ = lean_ctor_get(v_x_434_, 0);
v___x_444_ = lean_unsigned_to_nat(0u);
v___x_445_ = lean_array_get_size(v_vs_443_);
v___x_446_ = lean_nat_dec_lt(v___x_444_, v___x_445_);
if (v___x_446_ == 0)
{
return v_x_435_;
}
else
{
size_t v___x_447_; size_t v___x_448_; lean_object* v___x_449_; 
v___x_447_ = ((size_t)0ULL);
v___x_448_ = lean_usize_of_nat(v___x_445_);
v___x_449_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v_c_433_, v_vs_443_, v___x_447_, v___x_448_, v_x_435_);
return v___x_449_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(lean_object* v_c_450_, lean_object* v_as_451_, size_t v_i_452_, size_t v_stop_453_, lean_object* v_b_454_){
_start:
{
uint8_t v___x_455_; 
v___x_455_ = lean_usize_dec_eq(v_i_452_, v_stop_453_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; lean_object* v___x_457_; size_t v___x_458_; size_t v___x_459_; 
v___x_456_ = lean_array_uget_borrowed(v_as_451_, v_i_452_);
v___x_457_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2(v_c_450_, v___x_456_, v_b_454_);
v___x_458_ = ((size_t)1ULL);
v___x_459_ = lean_usize_add(v_i_452_, v___x_458_);
v_i_452_ = v___x_459_;
v_b_454_ = v___x_457_;
goto _start;
}
else
{
return v_b_454_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_450_ = stack[0].m_obj;
lean_object* v_as_451_ = stack[1].m_obj;
size_t v_i_452_ = stack[2].m_num;
size_t v_stop_453_ = stack[3].m_num;
lean_object* v_b_454_ = stack[4].m_obj;
lean_object* v_res_461_;
v_res_461_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v_c_450_, v_as_451_, v_i_452_, v_stop_453_, v_b_454_);
stack->m_obj
 = v_res_461_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1___boxed(lean_object* v_c_462_, lean_object* v_as_463_, lean_object* v_i_464_, lean_object* v_stop_465_, lean_object* v_b_466_){
_start:
{
size_t v_i_boxed_467_; size_t v_stop_boxed_468_; lean_object* v_res_469_; 
v_i_boxed_467_ = lean_unbox_usize(v_i_464_);
lean_dec(v_i_464_);
v_stop_boxed_468_ = lean_unbox_usize(v_stop_465_);
lean_dec(v_stop_465_);
v_res_469_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v_c_462_, v_as_463_, v_i_boxed_467_, v_stop_boxed_468_, v_b_466_);
lean_dec_ref(v_as_463_);
lean_dec_ref(v_c_462_);
return v_res_469_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2___boxed(lean_object* v_c_470_, lean_object* v_x_471_, lean_object* v_x_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2(v_c_470_, v_x_471_, v_x_472_);
lean_dec_ref(v_x_471_);
lean_dec_ref(v_c_470_);
return v_res_473_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_474_; 
v___x_474_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_474_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(lean_object* v_c_475_, lean_object* v_x_476_, size_t v_x_477_, size_t v_x_478_, lean_object* v_x_479_){
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
v___x_491_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(v_c_475_, v___x_484_, v___x_488_, v___x_490_, v_x_479_);
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
size_t v___x_496_; size_t v___x_497_; lean_object* v___x_498_; 
v___x_496_ = lean_usize_of_nat(v___x_493_);
lean_dec(v___x_493_);
v___x_497_ = lean_usize_of_nat(v___x_494_);
v___x_498_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v_c_475_, v_cs_480_, v___x_496_, v___x_497_, v___x_491_);
return v___x_498_;
}
}
else
{
lean_object* v_vs_499_; lean_object* v___x_500_; lean_object* v___x_501_; uint8_t v___x_502_; 
v_vs_499_ = lean_ctor_get(v_x_476_, 0);
v___x_500_ = lean_usize_to_nat(v_x_477_);
v___x_501_ = lean_array_get_size(v_vs_499_);
v___x_502_ = lean_nat_dec_lt(v___x_500_, v___x_501_);
if (v___x_502_ == 0)
{
lean_dec(v___x_500_);
return v_x_479_;
}
else
{
size_t v___x_503_; size_t v___x_504_; lean_object* v___x_505_; 
v___x_503_ = lean_usize_of_nat(v___x_500_);
lean_dec(v___x_500_);
v___x_504_ = lean_usize_of_nat(v___x_501_);
v___x_505_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v_c_475_, v_vs_499_, v___x_503_, v___x_504_, v_x_479_);
return v___x_505_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_475_ = stack[0].m_obj;
lean_object* v_x_476_ = stack[1].m_obj;
size_t v_x_477_ = stack[2].m_num;
size_t v_x_478_ = stack[3].m_num;
lean_object* v_x_479_ = stack[4].m_obj;
lean_object* v_res_506_;
v_res_506_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(v_c_475_, v_x_476_, v_x_477_, v_x_478_, v_x_479_);
stack->m_obj
 = v_res_506_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___boxed(lean_object* v_c_507_, lean_object* v_x_508_, lean_object* v_x_509_, lean_object* v_x_510_, lean_object* v_x_511_){
_start:
{
size_t v_x_1598__boxed_512_; size_t v_x_1599__boxed_513_; lean_object* v_res_514_; 
v_x_1598__boxed_512_ = lean_unbox_usize(v_x_509_);
lean_dec(v_x_509_);
v_x_1599__boxed_513_ = lean_unbox_usize(v_x_510_);
lean_dec(v_x_510_);
v_res_514_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(v_c_507_, v_x_508_, v_x_1598__boxed_512_, v_x_1599__boxed_513_, v_x_511_);
lean_dec_ref(v_x_508_);
lean_dec_ref(v_c_507_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(lean_object* v_c_515_, lean_object* v_t_516_, lean_object* v_init_517_, lean_object* v_start_518_){
_start:
{
lean_object* v___x_519_; uint8_t v___x_520_; 
v___x_519_ = lean_unsigned_to_nat(0u);
v___x_520_ = lean_nat_dec_eq(v_start_518_, v___x_519_);
if (v___x_520_ == 0)
{
lean_object* v_root_521_; lean_object* v_tail_522_; size_t v_shift_523_; lean_object* v_tailOff_524_; uint8_t v___x_525_; 
v_root_521_ = lean_ctor_get(v_t_516_, 0);
v_tail_522_ = lean_ctor_get(v_t_516_, 1);
v_shift_523_ = lean_ctor_get_usize(v_t_516_, 4);
v_tailOff_524_ = lean_ctor_get(v_t_516_, 3);
v___x_525_ = lean_nat_dec_le(v_tailOff_524_, v_start_518_);
if (v___x_525_ == 0)
{
size_t v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; uint8_t v___x_529_; 
v___x_526_ = lean_usize_of_nat(v_start_518_);
v___x_527_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(v_c_515_, v_root_521_, v___x_526_, v_shift_523_, v_init_517_);
v___x_528_ = lean_array_get_size(v_tail_522_);
v___x_529_ = lean_nat_dec_lt(v___x_519_, v___x_528_);
if (v___x_529_ == 0)
{
return v___x_527_;
}
else
{
size_t v___x_530_; size_t v___x_531_; lean_object* v___x_532_; 
v___x_530_ = ((size_t)0ULL);
v___x_531_ = lean_usize_of_nat(v___x_528_);
v___x_532_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v_c_515_, v_tail_522_, v___x_530_, v___x_531_, v___x_527_);
return v___x_532_;
}
}
else
{
lean_object* v___x_533_; lean_object* v___x_534_; uint8_t v___x_535_; 
v___x_533_ = lean_nat_sub(v_start_518_, v_tailOff_524_);
v___x_534_ = lean_array_get_size(v_tail_522_);
v___x_535_ = lean_nat_dec_lt(v___x_533_, v___x_534_);
if (v___x_535_ == 0)
{
lean_dec(v___x_533_);
return v_init_517_;
}
else
{
size_t v___x_536_; size_t v___x_537_; lean_object* v___x_538_; 
v___x_536_ = lean_usize_of_nat(v___x_533_);
lean_dec(v___x_533_);
v___x_537_ = lean_usize_of_nat(v___x_534_);
v___x_538_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v_c_515_, v_tail_522_, v___x_536_, v___x_537_, v_init_517_);
return v___x_538_;
}
}
}
else
{
lean_object* v_root_539_; lean_object* v_tail_540_; lean_object* v___x_541_; lean_object* v___x_542_; uint8_t v___x_543_; 
v_root_539_ = lean_ctor_get(v_t_516_, 0);
v_tail_540_ = lean_ctor_get(v_t_516_, 1);
v___x_541_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2(v_c_515_, v_root_539_, v_init_517_);
v___x_542_ = lean_array_get_size(v_tail_540_);
v___x_543_ = lean_nat_dec_lt(v___x_519_, v___x_542_);
if (v___x_543_ == 0)
{
return v___x_541_;
}
else
{
size_t v___x_544_; size_t v___x_545_; lean_object* v___x_546_; 
v___x_544_ = ((size_t)0ULL);
v___x_545_ = lean_usize_of_nat(v___x_542_);
v___x_546_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v_c_515_, v_tail_540_, v___x_544_, v___x_545_, v___x_541_);
return v___x_546_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0___boxed(lean_object* v_c_547_, lean_object* v_t_548_, lean_object* v_init_549_, lean_object* v_start_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(v_c_547_, v_t_548_, v_init_549_, v_start_550_);
lean_dec(v_start_550_);
lean_dec_ref(v_t_548_);
lean_dec_ref(v_c_547_);
return v_res_551_;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; 
v___x_552_ = lean_unsigned_to_nat(32u);
v___x_553_ = lean_mk_empty_array_with_capacity(v___x_552_);
v___x_554_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
return v___x_554_;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1(void){
_start:
{
size_t v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_555_ = ((size_t)5ULL);
v___x_556_ = lean_unsigned_to_nat(0u);
v___x_557_ = lean_unsigned_to_nat(32u);
v___x_558_ = lean_mk_empty_array_with_capacity(v___x_557_);
v___x_559_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__0, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__0_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__0);
v___x_560_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_560_, 0, v___x_559_);
lean_ctor_set(v___x_560_, 1, v___x_558_);
lean_ctor_set(v___x_560_, 2, v___x_556_);
lean_ctor_set(v___x_560_, 3, v___x_556_);
lean_ctor_set_usize(v___x_560_, 4, v___x_555_);
return v___x_560_;
}
}
lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4(lean_object* v_c_561_, lean_object* v_x_562_, size_t v_x_563_, size_t v_x_564_){
_start:
{
if (lean_obj_tag(v_x_562_) == 0)
{
lean_object* v_cs_565_; size_t v_j_566_; lean_object* v___x_567_; lean_object* v___x_568_; uint8_t v___x_569_; 
v_cs_565_ = lean_ctor_get(v_x_562_, 0);
v_j_566_ = lean_usize_shift_right(v_x_563_, v_x_564_);
v___x_567_ = lean_usize_to_nat(v_j_566_);
v___x_568_ = lean_array_get_size(v_cs_565_);
v___x_569_ = lean_nat_dec_lt(v___x_567_, v___x_568_);
if (v___x_569_ == 0)
{
lean_dec(v___x_567_);
return v_x_562_;
}
else
{
lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_587_; 
lean_inc_ref(v_cs_565_);
v_isSharedCheck_587_ = !lean_is_exclusive(v_x_562_);
if (v_isSharedCheck_587_ == 0)
{
lean_object* v_unused_588_; 
v_unused_588_ = lean_ctor_get(v_x_562_, 0);
lean_dec(v_unused_588_);
v___x_571_ = v_x_562_;
v_isShared_572_ = v_isSharedCheck_587_;
goto v_resetjp_570_;
}
else
{
lean_dec(v_x_562_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_587_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
size_t v___x_573_; size_t v___x_574_; size_t v___x_575_; size_t v_i_576_; size_t v___x_577_; size_t v_shift_578_; lean_object* v_v_579_; lean_object* v___x_580_; lean_object* v_xs_x27_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_585_; 
v___x_573_ = ((size_t)1ULL);
v___x_574_ = lean_usize_shift_left(v___x_573_, v_x_564_);
v___x_575_ = lean_usize_sub(v___x_574_, v___x_573_);
v_i_576_ = lean_usize_land(v_x_563_, v___x_575_);
v___x_577_ = ((size_t)5ULL);
v_shift_578_ = lean_usize_sub(v_x_564_, v___x_577_);
v_v_579_ = lean_array_fget(v_cs_565_, v___x_567_);
v___x_580_ = lean_box(0);
v_xs_x27_581_ = lean_array_fset(v_cs_565_, v___x_567_, v___x_580_);
v___x_582_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4(v_c_561_, v_v_579_, v_i_576_, v_shift_578_);
v___x_583_ = lean_array_fset(v_xs_x27_581_, v___x_567_, v___x_582_);
lean_dec(v___x_567_);
if (v_isShared_572_ == 0)
{
lean_ctor_set(v___x_571_, 0, v___x_583_);
v___x_585_ = v___x_571_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_583_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
else
{
lean_object* v_vs_589_; lean_object* v___x_590_; lean_object* v___x_591_; uint8_t v___x_592_; 
v_vs_589_ = lean_ctor_get(v_x_562_, 0);
v___x_590_ = lean_usize_to_nat(v_x_563_);
v___x_591_ = lean_array_get_size(v_vs_589_);
v___x_592_ = lean_nat_dec_lt(v___x_590_, v___x_591_);
if (v___x_592_ == 0)
{
lean_dec(v___x_590_);
return v_x_562_;
}
else
{
lean_object* v___x_594_; uint8_t v_isShared_595_; uint8_t v_isSharedCheck_606_; 
lean_inc_ref(v_vs_589_);
v_isSharedCheck_606_ = !lean_is_exclusive(v_x_562_);
if (v_isSharedCheck_606_ == 0)
{
lean_object* v_unused_607_; 
v_unused_607_ = lean_ctor_get(v_x_562_, 0);
lean_dec(v_unused_607_);
v___x_594_ = v_x_562_;
v_isShared_595_ = v_isSharedCheck_606_;
goto v_resetjp_593_;
}
else
{
lean_dec(v_x_562_);
v___x_594_ = lean_box(0);
v_isShared_595_ = v_isSharedCheck_606_;
goto v_resetjp_593_;
}
v_resetjp_593_:
{
lean_object* v_v_596_; lean_object* v___x_597_; lean_object* v_xs_x27_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_604_; 
v_v_596_ = lean_array_fget(v_vs_589_, v___x_590_);
v___x_597_ = lean_box(0);
v_xs_x27_598_ = lean_array_fset(v_vs_589_, v___x_590_, v___x_597_);
v___x_599_ = lean_unsigned_to_nat(0u);
v___x_600_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1);
v___x_601_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(v_c_561_, v_v_596_, v___x_600_, v___x_599_);
lean_dec(v_v_596_);
v___x_602_ = lean_array_fset(v_xs_x27_598_, v___x_590_, v___x_601_);
lean_dec(v___x_590_);
if (v_isShared_595_ == 0)
{
lean_ctor_set(v___x_594_, 0, v___x_602_);
v___x_604_ = v___x_594_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT void l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_561_ = stack[0].m_obj;
lean_object* v_x_562_ = stack[1].m_obj;
size_t v_x_563_ = stack[2].m_num;
size_t v_x_564_ = stack[3].m_num;
lean_object* v_res_608_;
v_res_608_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4(v_c_561_, v_x_562_, v_x_563_, v_x_564_);
stack->m_obj
 = v_res_608_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___boxed(lean_object* v_c_609_, lean_object* v_x_610_, lean_object* v_x_611_, lean_object* v_x_612_){
_start:
{
size_t v_x_1781__boxed_613_; size_t v_x_1782__boxed_614_; lean_object* v_res_615_; 
v_x_1781__boxed_613_ = lean_unbox_usize(v_x_611_);
lean_dec(v_x_611_);
v_x_1782__boxed_614_ = lean_unbox_usize(v_x_612_);
lean_dec(v_x_612_);
v_res_615_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4(v_c_609_, v_x_610_, v_x_1781__boxed_613_, v_x_1782__boxed_614_);
lean_dec_ref(v_c_609_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(lean_object* v_c_616_, lean_object* v_t_617_, lean_object* v_i_618_){
_start:
{
lean_object* v_root_619_; lean_object* v_tail_620_; lean_object* v_size_621_; size_t v_shift_622_; lean_object* v_tailOff_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_651_; 
v_root_619_ = lean_ctor_get(v_t_617_, 0);
v_tail_620_ = lean_ctor_get(v_t_617_, 1);
v_size_621_ = lean_ctor_get(v_t_617_, 2);
v_shift_622_ = lean_ctor_get_usize(v_t_617_, 4);
v_tailOff_623_ = lean_ctor_get(v_t_617_, 3);
v_isSharedCheck_651_ = !lean_is_exclusive(v_t_617_);
if (v_isSharedCheck_651_ == 0)
{
v___x_625_ = v_t_617_;
v_isShared_626_ = v_isSharedCheck_651_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_tailOff_623_);
lean_inc(v_size_621_);
lean_inc(v_tail_620_);
lean_inc(v_root_619_);
lean_dec(v_t_617_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_651_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
uint8_t v___x_627_; 
v___x_627_ = lean_nat_dec_le(v_tailOff_623_, v_i_618_);
if (v___x_627_ == 0)
{
size_t v___x_628_; lean_object* v___x_629_; lean_object* v___x_631_; 
v___x_628_ = lean_usize_of_nat(v_i_618_);
v___x_629_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4(v_c_616_, v_root_619_, v___x_628_, v_shift_622_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 0, v___x_629_);
v___x_631_ = v___x_625_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v_tail_620_);
lean_ctor_set(v_reuseFailAlloc_632_, 2, v_size_621_);
lean_ctor_set(v_reuseFailAlloc_632_, 3, v_tailOff_623_);
lean_ctor_set_usize(v_reuseFailAlloc_632_, 4, v_shift_622_);
v___x_631_ = v_reuseFailAlloc_632_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
return v___x_631_;
}
}
else
{
lean_object* v___x_633_; lean_object* v___x_634_; uint8_t v___x_635_; 
v___x_633_ = lean_nat_sub(v_i_618_, v_tailOff_623_);
v___x_634_ = lean_array_get_size(v_tail_620_);
v___x_635_ = lean_nat_dec_lt(v___x_633_, v___x_634_);
if (v___x_635_ == 0)
{
lean_object* v___x_637_; 
lean_dec(v___x_633_);
if (v_isShared_626_ == 0)
{
v___x_637_ = v___x_625_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_root_619_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v_tail_620_);
lean_ctor_set(v_reuseFailAlloc_638_, 2, v_size_621_);
lean_ctor_set(v_reuseFailAlloc_638_, 3, v_tailOff_623_);
lean_ctor_set_usize(v_reuseFailAlloc_638_, 4, v_shift_622_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
else
{
lean_object* v_v_639_; lean_object* v___x_640_; lean_object* v_xs_x27_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_649_; 
v_v_639_ = lean_array_fget(v_tail_620_, v___x_633_);
v___x_640_ = lean_box(0);
v_xs_x27_641_ = lean_array_fset(v_tail_620_, v___x_633_, v___x_640_);
v___x_642_ = lean_unsigned_to_nat(32u);
v___x_643_ = lean_mk_empty_array_with_capacity(v___x_642_);
lean_dec_ref(v___x_643_);
v___x_644_ = lean_unsigned_to_nat(0u);
v___x_645_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1);
v___x_646_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(v_c_616_, v_v_639_, v___x_645_, v___x_644_);
lean_dec(v_v_639_);
v___x_647_ = lean_array_fset(v_xs_x27_641_, v___x_633_, v___x_646_);
lean_dec(v___x_633_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 1, v___x_647_);
v___x_649_ = v___x_625_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_root_619_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v___x_647_);
lean_ctor_set(v_reuseFailAlloc_650_, 2, v_size_621_);
lean_ctor_set(v_reuseFailAlloc_650_, 3, v_tailOff_623_);
lean_ctor_set_usize(v_reuseFailAlloc_650_, 4, v_shift_622_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1___boxed(lean_object* v_c_652_, lean_object* v_t_653_, lean_object* v_i_654_){
_start:
{
lean_object* v_res_655_; 
v_res_655_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(v_c_652_, v_t_653_, v_i_654_);
lean_dec(v_i_654_);
lean_dec_ref(v_c_652_);
return v_res_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0(lean_object* v_c_656_, lean_object* v_v_657_, lean_object* v_s_658_){
_start:
{
lean_object* v_vars_659_; lean_object* v_varMap_660_; lean_object* v_varsHistory_661_; lean_object* v_natToIntMap_662_; lean_object* v_natDef_663_; lean_object* v_dvds_664_; lean_object* v_lowers_665_; lean_object* v_uppers_666_; lean_object* v_diseqs_667_; lean_object* v_elimEqs_668_; lean_object* v_elimStack_669_; lean_object* v_occurs_670_; lean_object* v_assignment_671_; lean_object* v_nextCnstrId_672_; uint8_t v_caseSplits_673_; lean_object* v_steps_674_; lean_object* v_conflict_x3f_675_; lean_object* v_diseqSplits_676_; lean_object* v_divMod_677_; uint8_t v_usedCommRing_678_; lean_object* v_nonlinearOccs_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_687_; 
v_vars_659_ = lean_ctor_get(v_s_658_, 0);
v_varMap_660_ = lean_ctor_get(v_s_658_, 1);
v_varsHistory_661_ = lean_ctor_get(v_s_658_, 2);
v_natToIntMap_662_ = lean_ctor_get(v_s_658_, 3);
v_natDef_663_ = lean_ctor_get(v_s_658_, 4);
v_dvds_664_ = lean_ctor_get(v_s_658_, 5);
v_lowers_665_ = lean_ctor_get(v_s_658_, 6);
v_uppers_666_ = lean_ctor_get(v_s_658_, 7);
v_diseqs_667_ = lean_ctor_get(v_s_658_, 8);
v_elimEqs_668_ = lean_ctor_get(v_s_658_, 9);
v_elimStack_669_ = lean_ctor_get(v_s_658_, 10);
v_occurs_670_ = lean_ctor_get(v_s_658_, 11);
v_assignment_671_ = lean_ctor_get(v_s_658_, 12);
v_nextCnstrId_672_ = lean_ctor_get(v_s_658_, 13);
v_caseSplits_673_ = lean_ctor_get_uint8(v_s_658_, sizeof(void*)*19);
v_steps_674_ = lean_ctor_get(v_s_658_, 14);
v_conflict_x3f_675_ = lean_ctor_get(v_s_658_, 15);
v_diseqSplits_676_ = lean_ctor_get(v_s_658_, 16);
v_divMod_677_ = lean_ctor_get(v_s_658_, 17);
v_usedCommRing_678_ = lean_ctor_get_uint8(v_s_658_, sizeof(void*)*19 + 1);
v_nonlinearOccs_679_ = lean_ctor_get(v_s_658_, 18);
v_isSharedCheck_687_ = !lean_is_exclusive(v_s_658_);
if (v_isSharedCheck_687_ == 0)
{
v___x_681_ = v_s_658_;
v_isShared_682_ = v_isSharedCheck_687_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_nonlinearOccs_679_);
lean_inc(v_divMod_677_);
lean_inc(v_diseqSplits_676_);
lean_inc(v_conflict_x3f_675_);
lean_inc(v_steps_674_);
lean_inc(v_nextCnstrId_672_);
lean_inc(v_assignment_671_);
lean_inc(v_occurs_670_);
lean_inc(v_elimStack_669_);
lean_inc(v_elimEqs_668_);
lean_inc(v_diseqs_667_);
lean_inc(v_uppers_666_);
lean_inc(v_lowers_665_);
lean_inc(v_dvds_664_);
lean_inc(v_natDef_663_);
lean_inc(v_natToIntMap_662_);
lean_inc(v_varsHistory_661_);
lean_inc(v_varMap_660_);
lean_inc(v_vars_659_);
lean_dec(v_s_658_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_687_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___x_683_; lean_object* v___x_685_; 
v___x_683_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(v_c_656_, v_uppers_666_, v_v_657_);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 7, v___x_683_);
v___x_685_ = v___x_681_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v_vars_659_);
lean_ctor_set(v_reuseFailAlloc_686_, 1, v_varMap_660_);
lean_ctor_set(v_reuseFailAlloc_686_, 2, v_varsHistory_661_);
lean_ctor_set(v_reuseFailAlloc_686_, 3, v_natToIntMap_662_);
lean_ctor_set(v_reuseFailAlloc_686_, 4, v_natDef_663_);
lean_ctor_set(v_reuseFailAlloc_686_, 5, v_dvds_664_);
lean_ctor_set(v_reuseFailAlloc_686_, 6, v_lowers_665_);
lean_ctor_set(v_reuseFailAlloc_686_, 7, v___x_683_);
lean_ctor_set(v_reuseFailAlloc_686_, 8, v_diseqs_667_);
lean_ctor_set(v_reuseFailAlloc_686_, 9, v_elimEqs_668_);
lean_ctor_set(v_reuseFailAlloc_686_, 10, v_elimStack_669_);
lean_ctor_set(v_reuseFailAlloc_686_, 11, v_occurs_670_);
lean_ctor_set(v_reuseFailAlloc_686_, 12, v_assignment_671_);
lean_ctor_set(v_reuseFailAlloc_686_, 13, v_nextCnstrId_672_);
lean_ctor_set(v_reuseFailAlloc_686_, 14, v_steps_674_);
lean_ctor_set(v_reuseFailAlloc_686_, 15, v_conflict_x3f_675_);
lean_ctor_set(v_reuseFailAlloc_686_, 16, v_diseqSplits_676_);
lean_ctor_set(v_reuseFailAlloc_686_, 17, v_divMod_677_);
lean_ctor_set(v_reuseFailAlloc_686_, 18, v_nonlinearOccs_679_);
lean_ctor_set_uint8(v_reuseFailAlloc_686_, sizeof(void*)*19, v_caseSplits_673_);
lean_ctor_set_uint8(v_reuseFailAlloc_686_, sizeof(void*)*19 + 1, v_usedCommRing_678_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___boxed(lean_object* v_c_688_, lean_object* v_v_689_, lean_object* v_s_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0(v_c_688_, v_v_689_, v_s_690_);
lean_dec(v_v_689_);
lean_dec_ref(v_c_688_);
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1(lean_object* v_c_692_, lean_object* v_v_693_, lean_object* v_s_694_){
_start:
{
lean_object* v_vars_695_; lean_object* v_varMap_696_; lean_object* v_varsHistory_697_; lean_object* v_natToIntMap_698_; lean_object* v_natDef_699_; lean_object* v_dvds_700_; lean_object* v_lowers_701_; lean_object* v_uppers_702_; lean_object* v_diseqs_703_; lean_object* v_elimEqs_704_; lean_object* v_elimStack_705_; lean_object* v_occurs_706_; lean_object* v_assignment_707_; lean_object* v_nextCnstrId_708_; uint8_t v_caseSplits_709_; lean_object* v_steps_710_; lean_object* v_conflict_x3f_711_; lean_object* v_diseqSplits_712_; lean_object* v_divMod_713_; uint8_t v_usedCommRing_714_; lean_object* v_nonlinearOccs_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_723_; 
v_vars_695_ = lean_ctor_get(v_s_694_, 0);
v_varMap_696_ = lean_ctor_get(v_s_694_, 1);
v_varsHistory_697_ = lean_ctor_get(v_s_694_, 2);
v_natToIntMap_698_ = lean_ctor_get(v_s_694_, 3);
v_natDef_699_ = lean_ctor_get(v_s_694_, 4);
v_dvds_700_ = lean_ctor_get(v_s_694_, 5);
v_lowers_701_ = lean_ctor_get(v_s_694_, 6);
v_uppers_702_ = lean_ctor_get(v_s_694_, 7);
v_diseqs_703_ = lean_ctor_get(v_s_694_, 8);
v_elimEqs_704_ = lean_ctor_get(v_s_694_, 9);
v_elimStack_705_ = lean_ctor_get(v_s_694_, 10);
v_occurs_706_ = lean_ctor_get(v_s_694_, 11);
v_assignment_707_ = lean_ctor_get(v_s_694_, 12);
v_nextCnstrId_708_ = lean_ctor_get(v_s_694_, 13);
v_caseSplits_709_ = lean_ctor_get_uint8(v_s_694_, sizeof(void*)*19);
v_steps_710_ = lean_ctor_get(v_s_694_, 14);
v_conflict_x3f_711_ = lean_ctor_get(v_s_694_, 15);
v_diseqSplits_712_ = lean_ctor_get(v_s_694_, 16);
v_divMod_713_ = lean_ctor_get(v_s_694_, 17);
v_usedCommRing_714_ = lean_ctor_get_uint8(v_s_694_, sizeof(void*)*19 + 1);
v_nonlinearOccs_715_ = lean_ctor_get(v_s_694_, 18);
v_isSharedCheck_723_ = !lean_is_exclusive(v_s_694_);
if (v_isSharedCheck_723_ == 0)
{
v___x_717_ = v_s_694_;
v_isShared_718_ = v_isSharedCheck_723_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_nonlinearOccs_715_);
lean_inc(v_divMod_713_);
lean_inc(v_diseqSplits_712_);
lean_inc(v_conflict_x3f_711_);
lean_inc(v_steps_710_);
lean_inc(v_nextCnstrId_708_);
lean_inc(v_assignment_707_);
lean_inc(v_occurs_706_);
lean_inc(v_elimStack_705_);
lean_inc(v_elimEqs_704_);
lean_inc(v_diseqs_703_);
lean_inc(v_uppers_702_);
lean_inc(v_lowers_701_);
lean_inc(v_dvds_700_);
lean_inc(v_natDef_699_);
lean_inc(v_natToIntMap_698_);
lean_inc(v_varsHistory_697_);
lean_inc(v_varMap_696_);
lean_inc(v_vars_695_);
lean_dec(v_s_694_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_723_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_719_; lean_object* v___x_721_; 
v___x_719_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(v_c_692_, v_lowers_701_, v_v_693_);
if (v_isShared_718_ == 0)
{
lean_ctor_set(v___x_717_, 6, v___x_719_);
v___x_721_ = v___x_717_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_vars_695_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_varMap_696_);
lean_ctor_set(v_reuseFailAlloc_722_, 2, v_varsHistory_697_);
lean_ctor_set(v_reuseFailAlloc_722_, 3, v_natToIntMap_698_);
lean_ctor_set(v_reuseFailAlloc_722_, 4, v_natDef_699_);
lean_ctor_set(v_reuseFailAlloc_722_, 5, v_dvds_700_);
lean_ctor_set(v_reuseFailAlloc_722_, 6, v___x_719_);
lean_ctor_set(v_reuseFailAlloc_722_, 7, v_uppers_702_);
lean_ctor_set(v_reuseFailAlloc_722_, 8, v_diseqs_703_);
lean_ctor_set(v_reuseFailAlloc_722_, 9, v_elimEqs_704_);
lean_ctor_set(v_reuseFailAlloc_722_, 10, v_elimStack_705_);
lean_ctor_set(v_reuseFailAlloc_722_, 11, v_occurs_706_);
lean_ctor_set(v_reuseFailAlloc_722_, 12, v_assignment_707_);
lean_ctor_set(v_reuseFailAlloc_722_, 13, v_nextCnstrId_708_);
lean_ctor_set(v_reuseFailAlloc_722_, 14, v_steps_710_);
lean_ctor_set(v_reuseFailAlloc_722_, 15, v_conflict_x3f_711_);
lean_ctor_set(v_reuseFailAlloc_722_, 16, v_diseqSplits_712_);
lean_ctor_set(v_reuseFailAlloc_722_, 17, v_divMod_713_);
lean_ctor_set(v_reuseFailAlloc_722_, 18, v_nonlinearOccs_715_);
lean_ctor_set_uint8(v_reuseFailAlloc_722_, sizeof(void*)*19, v_caseSplits_709_);
lean_ctor_set_uint8(v_reuseFailAlloc_722_, sizeof(void*)*19 + 1, v_usedCommRing_714_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1___boxed(lean_object* v_c_724_, lean_object* v_v_725_, lean_object* v_s_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1(v_c_724_, v_v_725_, v_s_726_);
lean_dec(v_v_725_);
lean_dec_ref(v_c_724_);
return v_res_727_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(lean_object* v_c_728_, lean_object* v_a_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_){
_start:
{
lean_object* v_p_735_; 
v_p_735_ = lean_ctor_get(v_c_728_, 0);
if (lean_obj_tag(v_p_735_) == 1)
{
lean_object* v_k_736_; lean_object* v_v_737_; lean_object* v___x_738_; uint8_t v___x_739_; 
v_k_736_ = lean_ctor_get(v_p_735_, 0);
v_v_737_ = lean_ctor_get(v_p_735_, 1);
lean_inc(v_v_737_);
v___x_738_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9);
v___x_739_ = lean_int_dec_lt(v_k_736_, v___x_738_);
if (v___x_739_ == 0)
{
lean_object* v___f_740_; lean_object* v___x_741_; lean_object* v___x_742_; 
v___f_740_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_740_, 0, v_c_728_);
lean_closure_set(v___f_740_, 1, v_v_737_);
v___x_741_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_742_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_741_, v___f_740_, v_a_729_);
return v___x_742_;
}
else
{
lean_object* v___f_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___f_743_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_743_, 0, v_c_728_);
lean_closure_set(v___f_743_, 1, v_v_737_);
v___x_744_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_745_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_744_, v___f_743_, v_a_729_);
return v___x_745_;
}
}
else
{
lean_object* v___x_746_; 
v___x_746_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_);
return v___x_746_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_728_ = stack[0].m_obj;
lean_object* v_a_729_ = stack[1].m_obj;
lean_object* v_a_730_ = stack[2].m_obj;
lean_object* v_a_731_ = stack[3].m_obj;
lean_object* v_a_732_ = stack[4].m_obj;
lean_object* v_a_733_ = stack[5].m_obj;
lean_object* v_res_747_;
v_res_747_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_c_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_);
stack->m_obj
 = v_res_747_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___boxed(lean_object* v_c_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_c_748_, v_a_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_);
lean_dec(v_a_753_);
lean_dec_ref(v_a_752_);
lean_dec(v_a_751_);
lean_dec_ref(v_a_750_);
lean_dec(v_a_749_);
return v_res_755_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase(lean_object* v_c_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_c_756_, v_a_757_, v_a_763_, v_a_764_, v_a_765_, v_a_766_);
return v___x_768_;
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_756_ = stack[0].m_obj;
lean_object* v_a_757_ = stack[1].m_obj;
lean_object* v_a_758_ = stack[2].m_obj;
lean_object* v_a_759_ = stack[3].m_obj;
lean_object* v_a_760_ = stack[4].m_obj;
lean_object* v_a_761_ = stack[5].m_obj;
lean_object* v_a_762_ = stack[6].m_obj;
lean_object* v_a_763_ = stack[7].m_obj;
lean_object* v_a_764_ = stack[8].m_obj;
lean_object* v_a_765_ = stack[9].m_obj;
lean_object* v_a_766_ = stack[10].m_obj;
lean_object* v_res_769_;
v_res_769_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase(v_c_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_);
stack->m_obj
 = v_res_769_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___boxed(lean_object* v_c_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase(v_c_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_);
lean_dec(v_a_780_);
lean_dec_ref(v_a_779_);
lean_dec(v_a_778_);
lean_dec_ref(v_a_777_);
lean_dec(v_a_776_);
lean_dec_ref(v_a_775_);
lean_dec(v_a_774_);
lean_dec_ref(v_a_773_);
lean_dec(v_a_772_);
lean_dec(v_a_771_);
return v_res_782_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5(void){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; 
v___x_796_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_797_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_798_ = l_Lean_Name_append(v___x_797_, v___x_796_);
return v___x_798_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7(void){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; 
v___x_800_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__6));
v___x_801_ = l_Lean_stringToMessageData(v___x_800_);
return v___x_801_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3(lean_object* v_c_802_, lean_object* v_as_803_, size_t v_sz_804_, size_t v_i_805_, lean_object* v_b_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
uint8_t v___x_818_; 
v___x_818_ = lean_usize_dec_lt(v_i_805_, v_sz_804_);
if (v___x_818_ == 0)
{
lean_object* v___x_819_; 
lean_dec_ref(v_c_802_);
v___x_819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_819_, 0, v_b_806_);
return v___x_819_;
}
else
{
lean_object* v_snd_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_908_; 
v_snd_820_ = lean_ctor_get(v_b_806_, 1);
v_isSharedCheck_908_ = !lean_is_exclusive(v_b_806_);
if (v_isSharedCheck_908_ == 0)
{
lean_object* v_unused_909_; 
v_unused_909_ = lean_ctor_get(v_b_806_, 0);
lean_dec(v_unused_909_);
v___x_822_ = v_b_806_;
v_isShared_823_ = v_isSharedCheck_908_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_snd_820_);
lean_dec(v_b_806_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_908_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v_p_824_; lean_object* v_a_825_; lean_object* v_p_826_; lean_object* v___x_827_; uint8_t v___x_828_; 
v_p_824_ = lean_ctor_get(v_c_802_, 0);
v_a_825_ = lean_array_uget_borrowed(v_as_803_, v_i_805_);
v_p_826_ = lean_ctor_get(v_a_825_, 0);
v___x_827_ = lean_box(0);
v___x_828_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_824_, v_p_826_);
if (v___x_828_ == 0)
{
lean_object* v___x_829_; size_t v___x_830_; size_t v___x_831_; 
lean_del_object(v___x_822_);
lean_dec(v_snd_820_);
v___x_829_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__1));
v___x_830_ = ((size_t)1ULL);
v___x_831_ = lean_usize_add(v_i_805_, v___x_830_);
v_i_805_ = v___x_831_;
v_b_806_ = v___x_829_;
goto _start;
}
else
{
lean_object* v___x_833_; 
lean_inc_ref(v_p_824_);
lean_inc(v_a_825_);
v___x_833_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_825_, v___y_807_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_object* v_toCold_834_; lean_object* v_options_835_; lean_object* v_inheritedTraceOptions_836_; uint8_t v_hasTrace_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___y_844_; lean_object* v___y_845_; lean_object* v___y_846_; lean_object* v___y_847_; lean_object* v___y_848_; lean_object* v___y_849_; lean_object* v___y_850_; 
lean_dec_ref_known(v___x_833_, 1);
v_toCold_834_ = lean_ctor_get(v___y_815_, 0);
v_options_835_ = lean_ctor_get(v_toCold_834_, 2);
v_inheritedTraceOptions_836_ = lean_ctor_get(v_toCold_834_, 11);
v_hasTrace_837_ = lean_ctor_get_uint8(v_options_835_, sizeof(void*)*1);
lean_inc(v_a_825_);
v___x_838_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_838_, 0, v_c_802_);
lean_ctor_set(v___x_838_, 1, v_a_825_);
v___x_839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_839_, 0, v_p_824_);
lean_ctor_set(v___x_839_, 1, v___x_838_);
if (v_hasTrace_837_ == 0)
{
v___y_841_ = v___y_807_;
v___y_842_ = v___y_808_;
v___y_843_ = v___y_809_;
v___y_844_ = v___y_810_;
v___y_845_ = v___y_811_;
v___y_846_ = v___y_812_;
v___y_847_ = v___y_813_;
v___y_848_ = v___y_814_;
v___y_849_ = v___y_815_;
v___y_850_ = v___y_816_;
goto v___jp_840_;
}
else
{
lean_object* v___x_876_; lean_object* v___x_877_; uint8_t v___x_878_; 
v___x_876_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_877_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5);
v___x_878_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_836_, v_options_835_, v___x_877_);
if (v___x_878_ == 0)
{
v___y_841_ = v___y_807_;
v___y_842_ = v___y_808_;
v___y_843_ = v___y_809_;
v___y_844_ = v___y_810_;
v___y_845_ = v___y_811_;
v___y_846_ = v___y_812_;
v___y_847_ = v___y_813_;
v___y_848_ = v___y_814_;
v___y_849_ = v___y_815_;
v___y_850_ = v___y_816_;
goto v___jp_840_;
}
else
{
lean_object* v___x_879_; 
lean_inc_ref(v___x_839_);
v___x_879_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_839_, v___y_807_, v___y_815_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v_a_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; 
v_a_880_ = lean_ctor_get(v___x_879_, 0);
lean_inc(v_a_880_);
lean_dec_ref_known(v___x_879_, 1);
v___x_881_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7);
v___x_882_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
lean_ctor_set(v___x_882_, 1, v_a_880_);
v___x_883_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_876_, v___x_882_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_dec_ref_known(v___x_883_, 1);
v___y_841_ = v___y_807_;
v___y_842_ = v___y_808_;
v___y_843_ = v___y_809_;
v___y_844_ = v___y_810_;
v___y_845_ = v___y_811_;
v___y_846_ = v___y_812_;
v___y_847_ = v___y_813_;
v___y_848_ = v___y_814_;
v___y_849_ = v___y_815_;
v___y_850_ = v___y_816_;
goto v___jp_840_;
}
else
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_891_; 
lean_dec_ref_known(v___x_839_, 2);
lean_del_object(v___x_822_);
lean_dec(v_snd_820_);
v_a_884_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_891_ == 0)
{
v___x_886_ = v___x_883_;
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_883_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_889_; 
if (v_isShared_887_ == 0)
{
v___x_889_ = v___x_886_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_884_);
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
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
lean_dec_ref_known(v___x_839_, 2);
lean_del_object(v___x_822_);
lean_dec(v_snd_820_);
v_a_892_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_899_ == 0)
{
v___x_894_ = v___x_879_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_879_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_895_ == 0)
{
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_892_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
}
v___jp_840_:
{
lean_object* v___x_851_; 
lean_inc(v___y_850_);
lean_inc_ref(v___y_849_);
lean_inc(v___y_848_);
lean_inc_ref(v___y_847_);
lean_inc(v___y_846_);
lean_inc_ref(v___y_845_);
lean_inc(v___y_844_);
lean_inc_ref(v___y_843_);
lean_inc(v___y_842_);
lean_inc(v___y_841_);
v___x_851_ = lean_grind_cutsat_assert_eq(v___x_839_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_866_; 
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_866_ == 0)
{
lean_object* v_unused_867_; 
v_unused_867_ = lean_ctor_get(v___x_851_, 0);
lean_dec(v_unused_867_);
v___x_853_ = v___x_851_;
v_isShared_854_ = v_isSharedCheck_866_;
goto v_resetjp_852_;
}
else
{
lean_dec(v___x_851_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_866_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_858_; 
v___x_855_ = lean_box(v___x_828_);
v___x_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_856_, 0, v___x_855_);
if (v_isShared_823_ == 0)
{
lean_ctor_set(v___x_822_, 1, v___x_827_);
lean_ctor_set(v___x_822_, 0, v___x_856_);
v___x_858_ = v___x_822_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_856_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v___x_827_);
v___x_858_ = v_reuseFailAlloc_865_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_863_; 
v___x_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_859_, 0, v___x_858_);
v___x_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_860_, 0, v___x_859_);
v___x_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_861_, 0, v___x_860_);
lean_ctor_set(v___x_861_, 1, v_snd_820_);
if (v_isShared_854_ == 0)
{
lean_ctor_set(v___x_853_, 0, v___x_861_);
v___x_863_ = v___x_853_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_861_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
else
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_875_; 
lean_del_object(v___x_822_);
lean_dec(v_snd_820_);
v_a_868_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_875_ == 0)
{
v___x_870_ = v___x_851_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_851_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_873_; 
if (v_isShared_871_ == 0)
{
v___x_873_ = v___x_870_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_868_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
}
else
{
lean_object* v_a_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_907_; 
lean_dec_ref(v_p_824_);
lean_del_object(v___x_822_);
lean_dec(v_snd_820_);
lean_dec_ref(v_c_802_);
v_a_900_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_907_ == 0)
{
v___x_902_ = v___x_833_;
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_a_900_);
lean_dec(v___x_833_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_905_; 
if (v_isShared_903_ == 0)
{
v___x_905_ = v___x_902_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_a_900_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_802_ = stack[0].m_obj;
lean_object* v_as_803_ = stack[1].m_obj;
size_t v_sz_804_ = stack[2].m_num;
size_t v_i_805_ = stack[3].m_num;
lean_object* v_b_806_ = stack[4].m_obj;
lean_object* v___y_807_ = stack[5].m_obj;
lean_object* v___y_808_ = stack[6].m_obj;
lean_object* v___y_809_ = stack[7].m_obj;
lean_object* v___y_810_ = stack[8].m_obj;
lean_object* v___y_811_ = stack[9].m_obj;
lean_object* v___y_812_ = stack[10].m_obj;
lean_object* v___y_813_ = stack[11].m_obj;
lean_object* v___y_814_ = stack[12].m_obj;
lean_object* v___y_815_ = stack[13].m_obj;
lean_object* v___y_816_ = stack[14].m_obj;
lean_object* v_res_910_;
v_res_910_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3(v_c_802_, v_as_803_, v_sz_804_, v_i_805_, v_b_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
stack->m_obj
 = v_res_910_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_c_911_, lean_object* v_as_912_, lean_object* v_sz_913_, lean_object* v_i_914_, lean_object* v_b_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
size_t v_sz_boxed_927_; size_t v_i_boxed_928_; lean_object* v_res_929_; 
v_sz_boxed_927_ = lean_unbox_usize(v_sz_913_);
lean_dec(v_sz_913_);
v_i_boxed_928_ = lean_unbox_usize(v_i_914_);
lean_dec(v_i_914_);
v_res_929_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3(v_c_911_, v_as_912_, v_sz_boxed_927_, v_i_boxed_928_, v_b_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_);
lean_dec(v___y_925_);
lean_dec_ref(v___y_924_);
lean_dec(v___y_923_);
lean_dec_ref(v___y_922_);
lean_dec(v___y_921_);
lean_dec_ref(v___y_920_);
lean_dec(v___y_919_);
lean_dec_ref(v___y_918_);
lean_dec(v___y_917_);
lean_dec(v___y_916_);
lean_dec_ref(v_as_912_);
return v_res_929_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2(lean_object* v_c_936_, lean_object* v_as_937_, size_t v_sz_938_, size_t v_i_939_, lean_object* v_b_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
uint8_t v___x_952_; 
v___x_952_ = lean_usize_dec_lt(v_i_939_, v_sz_938_);
if (v___x_952_ == 0)
{
lean_object* v___x_953_; 
lean_dec_ref(v_c_936_);
v___x_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_953_, 0, v_b_940_);
return v___x_953_;
}
else
{
lean_object* v_snd_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_1042_; 
v_snd_954_ = lean_ctor_get(v_b_940_, 1);
v_isSharedCheck_1042_ = !lean_is_exclusive(v_b_940_);
if (v_isSharedCheck_1042_ == 0)
{
lean_object* v_unused_1043_; 
v_unused_1043_ = lean_ctor_get(v_b_940_, 0);
lean_dec(v_unused_1043_);
v___x_956_ = v_b_940_;
v_isShared_957_ = v_isSharedCheck_1042_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_snd_954_);
lean_dec(v_b_940_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_1042_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v_p_958_; lean_object* v_a_959_; lean_object* v_p_960_; lean_object* v___x_961_; uint8_t v___x_962_; 
v_p_958_ = lean_ctor_get(v_c_936_, 0);
v_a_959_ = lean_array_uget_borrowed(v_as_937_, v_i_939_);
v_p_960_ = lean_ctor_get(v_a_959_, 0);
v___x_961_ = lean_box(0);
v___x_962_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_958_, v_p_960_);
if (v___x_962_ == 0)
{
lean_object* v___x_963_; size_t v___x_964_; size_t v___x_965_; lean_object* v___x_966_; 
lean_del_object(v___x_956_);
lean_dec(v_snd_954_);
v___x_963_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__1));
v___x_964_ = ((size_t)1ULL);
v___x_965_ = lean_usize_add(v_i_939_, v___x_964_);
v___x_966_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3(v_c_936_, v_as_937_, v_sz_938_, v___x_965_, v___x_963_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_);
return v___x_966_;
}
else
{
lean_object* v___x_967_; 
lean_inc_ref(v_p_958_);
lean_inc(v_a_959_);
v___x_967_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_959_, v___y_941_, v___y_947_, v___y_948_, v___y_949_, v___y_950_);
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v_toCold_968_; lean_object* v_options_969_; lean_object* v_inheritedTraceOptions_970_; uint8_t v_hasTrace_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___y_975_; lean_object* v___y_976_; lean_object* v___y_977_; lean_object* v___y_978_; lean_object* v___y_979_; lean_object* v___y_980_; lean_object* v___y_981_; lean_object* v___y_982_; lean_object* v___y_983_; lean_object* v___y_984_; 
lean_dec_ref_known(v___x_967_, 1);
v_toCold_968_ = lean_ctor_get(v___y_949_, 0);
v_options_969_ = lean_ctor_get(v_toCold_968_, 2);
v_inheritedTraceOptions_970_ = lean_ctor_get(v_toCold_968_, 11);
v_hasTrace_971_ = lean_ctor_get_uint8(v_options_969_, sizeof(void*)*1);
lean_inc(v_a_959_);
v___x_972_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_972_, 0, v_c_936_);
lean_ctor_set(v___x_972_, 1, v_a_959_);
v___x_973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_973_, 0, v_p_958_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
if (v_hasTrace_971_ == 0)
{
v___y_975_ = v___y_941_;
v___y_976_ = v___y_942_;
v___y_977_ = v___y_943_;
v___y_978_ = v___y_944_;
v___y_979_ = v___y_945_;
v___y_980_ = v___y_946_;
v___y_981_ = v___y_947_;
v___y_982_ = v___y_948_;
v___y_983_ = v___y_949_;
v___y_984_ = v___y_950_;
goto v___jp_974_;
}
else
{
lean_object* v___x_1010_; lean_object* v___x_1011_; uint8_t v___x_1012_; 
v___x_1010_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_1011_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5);
v___x_1012_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_970_, v_options_969_, v___x_1011_);
if (v___x_1012_ == 0)
{
v___y_975_ = v___y_941_;
v___y_976_ = v___y_942_;
v___y_977_ = v___y_943_;
v___y_978_ = v___y_944_;
v___y_979_ = v___y_945_;
v___y_980_ = v___y_946_;
v___y_981_ = v___y_947_;
v___y_982_ = v___y_948_;
v___y_983_ = v___y_949_;
v___y_984_ = v___y_950_;
goto v___jp_974_;
}
else
{
lean_object* v___x_1013_; 
lean_inc_ref(v___x_973_);
v___x_1013_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_973_, v___y_941_, v___y_949_);
if (lean_obj_tag(v___x_1013_) == 0)
{
lean_object* v_a_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v_a_1014_ = lean_ctor_get(v___x_1013_, 0);
lean_inc(v_a_1014_);
lean_dec_ref_known(v___x_1013_, 1);
v___x_1015_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7);
v___x_1016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
lean_ctor_set(v___x_1016_, 1, v_a_1014_);
v___x_1017_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_1010_, v___x_1016_, v___y_947_, v___y_948_, v___y_949_, v___y_950_);
if (lean_obj_tag(v___x_1017_) == 0)
{
lean_dec_ref_known(v___x_1017_, 1);
v___y_975_ = v___y_941_;
v___y_976_ = v___y_942_;
v___y_977_ = v___y_943_;
v___y_978_ = v___y_944_;
v___y_979_ = v___y_945_;
v___y_980_ = v___y_946_;
v___y_981_ = v___y_947_;
v___y_982_ = v___y_948_;
v___y_983_ = v___y_949_;
v___y_984_ = v___y_950_;
goto v___jp_974_;
}
else
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
lean_dec_ref_known(v___x_973_, 2);
lean_del_object(v___x_956_);
lean_dec(v_snd_954_);
v_a_1018_ = lean_ctor_get(v___x_1017_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_1017_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___x_1017_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_1017_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1018_);
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
lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1033_; 
lean_dec_ref_known(v___x_973_, 2);
lean_del_object(v___x_956_);
lean_dec(v_snd_954_);
v_a_1026_ = lean_ctor_get(v___x_1013_, 0);
v_isSharedCheck_1033_ = !lean_is_exclusive(v___x_1013_);
if (v_isSharedCheck_1033_ == 0)
{
v___x_1028_ = v___x_1013_;
v_isShared_1029_ = v_isSharedCheck_1033_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1013_);
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
v___jp_974_:
{
lean_object* v___x_985_; 
lean_inc(v___y_984_);
lean_inc_ref(v___y_983_);
lean_inc(v___y_982_);
lean_inc_ref(v___y_981_);
lean_inc(v___y_980_);
lean_inc_ref(v___y_979_);
lean_inc(v___y_978_);
lean_inc_ref(v___y_977_);
lean_inc(v___y_976_);
lean_inc(v___y_975_);
v___x_985_ = lean_grind_cutsat_assert_eq(v___x_973_, v___y_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
if (lean_obj_tag(v___x_985_) == 0)
{
lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_1000_; 
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_1000_ == 0)
{
lean_object* v_unused_1001_; 
v_unused_1001_ = lean_ctor_get(v___x_985_, 0);
lean_dec(v_unused_1001_);
v___x_987_ = v___x_985_;
v_isShared_988_ = v_isSharedCheck_1000_;
goto v_resetjp_986_;
}
else
{
lean_dec(v___x_985_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_1000_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_992_; 
v___x_989_ = lean_box(v___x_962_);
v___x_990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 1, v___x_961_);
lean_ctor_set(v___x_956_, 0, v___x_990_);
v___x_992_ = v___x_956_;
goto v_reusejp_991_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_990_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v___x_961_);
v___x_992_ = v_reuseFailAlloc_999_;
goto v_reusejp_991_;
}
v_reusejp_991_:
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_997_; 
v___x_993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
v___x_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
v___x_995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
lean_ctor_set(v___x_995_, 1, v_snd_954_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 0, v___x_995_);
v___x_997_ = v___x_987_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v___x_995_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
}
else
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
lean_del_object(v___x_956_);
lean_dec(v_snd_954_);
v_a_1002_ = lean_ctor_get(v___x_985_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_985_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1004_ = v___x_985_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_985_);
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
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1041_; 
lean_dec_ref(v_p_958_);
lean_del_object(v___x_956_);
lean_dec(v_snd_954_);
lean_dec_ref(v_c_936_);
v_a_1034_ = lean_ctor_get(v___x_967_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_967_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1036_ = v___x_967_;
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_967_);
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
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_936_ = stack[0].m_obj;
lean_object* v_as_937_ = stack[1].m_obj;
size_t v_sz_938_ = stack[2].m_num;
size_t v_i_939_ = stack[3].m_num;
lean_object* v_b_940_ = stack[4].m_obj;
lean_object* v___y_941_ = stack[5].m_obj;
lean_object* v___y_942_ = stack[6].m_obj;
lean_object* v___y_943_ = stack[7].m_obj;
lean_object* v___y_944_ = stack[8].m_obj;
lean_object* v___y_945_ = stack[9].m_obj;
lean_object* v___y_946_ = stack[10].m_obj;
lean_object* v___y_947_ = stack[11].m_obj;
lean_object* v___y_948_ = stack[12].m_obj;
lean_object* v___y_949_ = stack[13].m_obj;
lean_object* v___y_950_ = stack[14].m_obj;
lean_object* v_res_1044_;
v_res_1044_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2(v_c_936_, v_as_937_, v_sz_938_, v_i_939_, v_b_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_);
stack->m_obj
 = v_res_1044_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___boxed(lean_object* v_c_1045_, lean_object* v_as_1046_, lean_object* v_sz_1047_, lean_object* v_i_1048_, lean_object* v_b_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_){
_start:
{
size_t v_sz_boxed_1061_; size_t v_i_boxed_1062_; lean_object* v_res_1063_; 
v_sz_boxed_1061_ = lean_unbox_usize(v_sz_1047_);
lean_dec(v_sz_1047_);
v_i_boxed_1062_ = lean_unbox_usize(v_i_1048_);
lean_dec(v_i_1048_);
v_res_1063_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2(v_c_1045_, v_as_1046_, v_sz_boxed_1061_, v_i_boxed_1062_, v_b_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
lean_dec(v___y_1059_);
lean_dec_ref(v___y_1058_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec(v___y_1053_);
lean_dec_ref(v___y_1052_);
lean_dec(v___y_1051_);
lean_dec(v___y_1050_);
lean_dec_ref(v_as_1046_);
return v_res_1063_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(lean_object* v_init_1064_, lean_object* v_c_1065_, lean_object* v_n_1066_, lean_object* v_b_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_){
_start:
{
if (lean_obj_tag(v_n_1066_) == 0)
{
lean_object* v_cs_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; size_t v_sz_1082_; size_t v___x_1083_; lean_object* v___x_1084_; 
v_cs_1079_ = lean_ctor_get(v_n_1066_, 0);
v___x_1080_ = lean_box(0);
v___x_1081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
lean_ctor_set(v___x_1081_, 1, v_b_1067_);
v_sz_1082_ = lean_array_size(v_cs_1079_);
v___x_1083_ = ((size_t)0ULL);
v___x_1084_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(v_init_1064_, v_c_1065_, v_cs_1079_, v_sz_1082_, v___x_1083_, v___x_1081_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1099_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1087_ = v___x_1084_;
v_isShared_1088_ = v_isSharedCheck_1099_;
goto v_resetjp_1086_;
}
else
{
lean_inc(v_a_1085_);
lean_dec(v___x_1084_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1099_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v_fst_1089_; 
v_fst_1089_ = lean_ctor_get(v_a_1085_, 0);
if (lean_obj_tag(v_fst_1089_) == 0)
{
lean_object* v_snd_1090_; lean_object* v___x_1091_; lean_object* v___x_1093_; 
v_snd_1090_ = lean_ctor_get(v_a_1085_, 1);
lean_inc(v_snd_1090_);
lean_dec(v_a_1085_);
v___x_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1091_, 0, v_snd_1090_);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 0, v___x_1091_);
v___x_1093_ = v___x_1087_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v___x_1091_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
else
{
lean_object* v_val_1095_; lean_object* v___x_1097_; 
lean_inc_ref(v_fst_1089_);
lean_dec(v_a_1085_);
v_val_1095_ = lean_ctor_get(v_fst_1089_, 0);
lean_inc(v_val_1095_);
lean_dec_ref_known(v_fst_1089_, 1);
if (v_isShared_1088_ == 0)
{
lean_ctor_set(v___x_1087_, 0, v_val_1095_);
v___x_1097_ = v___x_1087_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_val_1095_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
else
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
v_a_1100_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1084_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1084_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
else
{
lean_object* v_vs_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; size_t v_sz_1111_; size_t v___x_1112_; lean_object* v___x_1113_; 
v_vs_1108_ = lean_ctor_get(v_n_1066_, 0);
v___x_1109_ = lean_box(0);
v___x_1110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1110_, 0, v___x_1109_);
lean_ctor_set(v___x_1110_, 1, v_b_1067_);
v_sz_1111_ = lean_array_size(v_vs_1108_);
v___x_1112_ = ((size_t)0ULL);
v___x_1113_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2(v_c_1065_, v_vs_1108_, v_sz_1111_, v___x_1112_, v___x_1110_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1128_; 
v_a_1114_ = lean_ctor_get(v___x_1113_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1116_ = v___x_1113_;
v_isShared_1117_ = v_isSharedCheck_1128_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_1113_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1128_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v_fst_1118_; 
v_fst_1118_ = lean_ctor_get(v_a_1114_, 0);
if (lean_obj_tag(v_fst_1118_) == 0)
{
lean_object* v_snd_1119_; lean_object* v___x_1120_; lean_object* v___x_1122_; 
v_snd_1119_ = lean_ctor_get(v_a_1114_, 1);
lean_inc(v_snd_1119_);
lean_dec(v_a_1114_);
v___x_1120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1120_, 0, v_snd_1119_);
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 0, v___x_1120_);
v___x_1122_ = v___x_1116_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v___x_1120_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
else
{
lean_object* v_val_1124_; lean_object* v___x_1126_; 
lean_inc_ref(v_fst_1118_);
lean_dec(v_a_1114_);
v_val_1124_ = lean_ctor_get(v_fst_1118_, 0);
lean_inc(v_val_1124_);
lean_dec_ref_known(v_fst_1118_, 1);
if (v_isShared_1117_ == 0)
{
lean_ctor_set(v___x_1116_, 0, v_val_1124_);
v___x_1126_ = v___x_1116_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_val_1124_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
else
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1136_; 
v_a_1129_ = lean_ctor_get(v___x_1113_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1131_ = v___x_1113_;
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v___x_1113_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1134_; 
if (v_isShared_1132_ == 0)
{
v___x_1134_ = v___x_1131_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_a_1129_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_1064_ = stack[0].m_obj;
lean_object* v_c_1065_ = stack[1].m_obj;
lean_object* v_n_1066_ = stack[2].m_obj;
lean_object* v_b_1067_ = stack[3].m_obj;
lean_object* v___y_1068_ = stack[4].m_obj;
lean_object* v___y_1069_ = stack[5].m_obj;
lean_object* v___y_1070_ = stack[6].m_obj;
lean_object* v___y_1071_ = stack[7].m_obj;
lean_object* v___y_1072_ = stack[8].m_obj;
lean_object* v___y_1073_ = stack[9].m_obj;
lean_object* v___y_1074_ = stack[10].m_obj;
lean_object* v___y_1075_ = stack[11].m_obj;
lean_object* v___y_1076_ = stack[12].m_obj;
lean_object* v___y_1077_ = stack[13].m_obj;
lean_object* v_res_1137_;
v_res_1137_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(v_init_1064_, v_c_1065_, v_n_1066_, v_b_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
stack->m_obj
 = v_res_1137_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(lean_object* v_init_1138_, lean_object* v_c_1139_, lean_object* v_as_1140_, size_t v_sz_1141_, size_t v_i_1142_, lean_object* v_b_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_, lean_object* v___y_1152_, lean_object* v___y_1153_){
_start:
{
uint8_t v___x_1155_; 
v___x_1155_ = lean_usize_dec_lt(v_i_1142_, v_sz_1141_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; 
lean_dec_ref(v_c_1139_);
v___x_1156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1156_, 0, v_b_1143_);
return v___x_1156_;
}
else
{
lean_object* v_snd_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1191_; 
v_snd_1157_ = lean_ctor_get(v_b_1143_, 1);
v_isSharedCheck_1191_ = !lean_is_exclusive(v_b_1143_);
if (v_isSharedCheck_1191_ == 0)
{
lean_object* v_unused_1192_; 
v_unused_1192_ = lean_ctor_get(v_b_1143_, 0);
lean_dec(v_unused_1192_);
v___x_1159_ = v_b_1143_;
v_isShared_1160_ = v_isSharedCheck_1191_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_snd_1157_);
lean_dec(v_b_1143_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1191_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1161_; lean_object* v_a_1162_; lean_object* v___x_1163_; 
v___x_1161_ = lean_box(0);
v_a_1162_ = lean_array_uget_borrowed(v_as_1140_, v_i_1142_);
lean_inc(v_snd_1157_);
lean_inc_ref(v_c_1139_);
v___x_1163_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(v_init_1138_, v_c_1139_, v_a_1162_, v_snd_1157_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
if (lean_obj_tag(v___x_1163_) == 0)
{
lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1182_; 
v_a_1164_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1166_ = v___x_1163_;
v_isShared_1167_ = v_isSharedCheck_1182_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1163_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1182_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
if (lean_obj_tag(v_a_1164_) == 0)
{
lean_object* v___x_1168_; lean_object* v___x_1170_; 
lean_dec_ref(v_c_1139_);
v___x_1168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1168_, 0, v_a_1164_);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 0, v___x_1168_);
v___x_1170_ = v___x_1159_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v___x_1168_);
lean_ctor_set(v_reuseFailAlloc_1174_, 1, v_snd_1157_);
v___x_1170_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
lean_object* v___x_1172_; 
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 0, v___x_1170_);
v___x_1172_ = v___x_1166_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v___x_1170_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
else
{
lean_object* v_a_1175_; lean_object* v___x_1177_; 
lean_del_object(v___x_1166_);
lean_dec(v_snd_1157_);
v_a_1175_ = lean_ctor_get(v_a_1164_, 0);
lean_inc(v_a_1175_);
lean_dec_ref_known(v_a_1164_, 1);
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 1, v_a_1175_);
lean_ctor_set(v___x_1159_, 0, v___x_1161_);
v___x_1177_ = v___x_1159_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v___x_1161_);
lean_ctor_set(v_reuseFailAlloc_1181_, 1, v_a_1175_);
v___x_1177_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
size_t v___x_1178_; size_t v___x_1179_; 
v___x_1178_ = ((size_t)1ULL);
v___x_1179_ = lean_usize_add(v_i_1142_, v___x_1178_);
v_i_1142_ = v___x_1179_;
v_b_1143_ = v___x_1177_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1183_; lean_object* v___x_1185_; uint8_t v_isShared_1186_; uint8_t v_isSharedCheck_1190_; 
lean_del_object(v___x_1159_);
lean_dec(v_snd_1157_);
lean_dec_ref(v_c_1139_);
v_a_1183_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1190_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1190_ == 0)
{
v___x_1185_ = v___x_1163_;
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
else
{
lean_inc(v_a_1183_);
lean_dec(v___x_1163_);
v___x_1185_ = lean_box(0);
v_isShared_1186_ = v_isSharedCheck_1190_;
goto v_resetjp_1184_;
}
v_resetjp_1184_:
{
lean_object* v___x_1188_; 
if (v_isShared_1186_ == 0)
{
v___x_1188_ = v___x_1185_;
goto v_reusejp_1187_;
}
else
{
lean_object* v_reuseFailAlloc_1189_; 
v_reuseFailAlloc_1189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1189_, 0, v_a_1183_);
v___x_1188_ = v_reuseFailAlloc_1189_;
goto v_reusejp_1187_;
}
v_reusejp_1187_:
{
return v___x_1188_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_1138_ = stack[0].m_obj;
lean_object* v_c_1139_ = stack[1].m_obj;
lean_object* v_as_1140_ = stack[2].m_obj;
size_t v_sz_1141_ = stack[3].m_num;
size_t v_i_1142_ = stack[4].m_num;
lean_object* v_b_1143_ = stack[5].m_obj;
lean_object* v___y_1144_ = stack[6].m_obj;
lean_object* v___y_1145_ = stack[7].m_obj;
lean_object* v___y_1146_ = stack[8].m_obj;
lean_object* v___y_1147_ = stack[9].m_obj;
lean_object* v___y_1148_ = stack[10].m_obj;
lean_object* v___y_1149_ = stack[11].m_obj;
lean_object* v___y_1150_ = stack[12].m_obj;
lean_object* v___y_1151_ = stack[13].m_obj;
lean_object* v___y_1152_ = stack[14].m_obj;
lean_object* v___y_1153_ = stack[15].m_obj;
lean_object* v_res_1193_;
v_res_1193_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(v_init_1138_, v_c_1139_, v_as_1140_, v_sz_1141_, v_i_1142_, v_b_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_, v___y_1152_, v___y_1153_);
stack->m_obj
 = v_res_1193_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_init_1194_ = _args[0];
lean_object* v_c_1195_ = _args[1];
lean_object* v_as_1196_ = _args[2];
lean_object* v_sz_1197_ = _args[3];
lean_object* v_i_1198_ = _args[4];
lean_object* v_b_1199_ = _args[5];
lean_object* v___y_1200_ = _args[6];
lean_object* v___y_1201_ = _args[7];
lean_object* v___y_1202_ = _args[8];
lean_object* v___y_1203_ = _args[9];
lean_object* v___y_1204_ = _args[10];
lean_object* v___y_1205_ = _args[11];
lean_object* v___y_1206_ = _args[12];
lean_object* v___y_1207_ = _args[13];
lean_object* v___y_1208_ = _args[14];
lean_object* v___y_1209_ = _args[15];
lean_object* v___y_1210_ = _args[16];
_start:
{
size_t v_sz_boxed_1211_; size_t v_i_boxed_1212_; lean_object* v_res_1213_; 
v_sz_boxed_1211_ = lean_unbox_usize(v_sz_1197_);
lean_dec(v_sz_1197_);
v_i_boxed_1212_ = lean_unbox_usize(v_i_1198_);
lean_dec(v_i_1198_);
v_res_1213_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(v_init_1194_, v_c_1195_, v_as_1196_, v_sz_boxed_1211_, v_i_boxed_1212_, v_b_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v___y_1204_);
lean_dec(v___y_1203_);
lean_dec_ref(v___y_1202_);
lean_dec(v___y_1201_);
lean_dec(v___y_1200_);
lean_dec_ref(v_as_1196_);
lean_dec_ref(v_init_1194_);
return v_res_1213_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___boxed(lean_object* v_init_1214_, lean_object* v_c_1215_, lean_object* v_n_1216_, lean_object* v_b_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(v_init_1214_, v_c_1215_, v_n_1216_, v_b_1217_, v___y_1218_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v___y_1219_);
lean_dec(v___y_1218_);
lean_dec_ref(v_n_1216_);
lean_dec_ref(v_init_1214_);
return v_res_1229_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4(lean_object* v_c_1236_, lean_object* v_as_1237_, size_t v_sz_1238_, size_t v_i_1239_, lean_object* v_b_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
uint8_t v___x_1252_; 
v___x_1252_ = lean_usize_dec_lt(v_i_1239_, v_sz_1238_);
if (v___x_1252_ == 0)
{
lean_object* v___x_1253_; 
lean_dec_ref(v_c_1236_);
v___x_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1253_, 0, v_b_1240_);
return v___x_1253_;
}
else
{
lean_object* v_snd_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1341_; 
v_snd_1254_ = lean_ctor_get(v_b_1240_, 1);
v_isSharedCheck_1341_ = !lean_is_exclusive(v_b_1240_);
if (v_isSharedCheck_1341_ == 0)
{
lean_object* v_unused_1342_; 
v_unused_1342_ = lean_ctor_get(v_b_1240_, 0);
lean_dec(v_unused_1342_);
v___x_1256_ = v_b_1240_;
v_isShared_1257_ = v_isSharedCheck_1341_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_snd_1254_);
lean_dec(v_b_1240_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1341_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v_p_1258_; lean_object* v_a_1259_; lean_object* v_p_1260_; lean_object* v___x_1261_; uint8_t v___x_1262_; 
v_p_1258_ = lean_ctor_get(v_c_1236_, 0);
v_a_1259_ = lean_array_uget_borrowed(v_as_1237_, v_i_1239_);
v_p_1260_ = lean_ctor_get(v_a_1259_, 0);
v___x_1261_ = lean_box(0);
v___x_1262_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_1258_, v_p_1260_);
if (v___x_1262_ == 0)
{
lean_object* v___x_1263_; size_t v___x_1264_; size_t v___x_1265_; 
lean_del_object(v___x_1256_);
lean_dec(v_snd_1254_);
v___x_1263_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___closed__1));
v___x_1264_ = ((size_t)1ULL);
v___x_1265_ = lean_usize_add(v_i_1239_, v___x_1264_);
v_i_1239_ = v___x_1265_;
v_b_1240_ = v___x_1263_;
goto _start;
}
else
{
lean_object* v___x_1267_; 
lean_inc_ref(v_p_1258_);
lean_inc(v_a_1259_);
v___x_1267_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_1259_, v___y_1241_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v_toCold_1268_; lean_object* v_options_1269_; lean_object* v_inheritedTraceOptions_1270_; uint8_t v_hasTrace_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1277_; lean_object* v___y_1278_; lean_object* v___y_1279_; lean_object* v___y_1280_; lean_object* v___y_1281_; lean_object* v___y_1282_; lean_object* v___y_1283_; lean_object* v___y_1284_; 
lean_dec_ref_known(v___x_1267_, 1);
v_toCold_1268_ = lean_ctor_get(v___y_1249_, 0);
v_options_1269_ = lean_ctor_get(v_toCold_1268_, 2);
v_inheritedTraceOptions_1270_ = lean_ctor_get(v_toCold_1268_, 11);
v_hasTrace_1271_ = lean_ctor_get_uint8(v_options_1269_, sizeof(void*)*1);
lean_inc(v_a_1259_);
v___x_1272_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1272_, 0, v_c_1236_);
lean_ctor_set(v___x_1272_, 1, v_a_1259_);
v___x_1273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1273_, 0, v_p_1258_);
lean_ctor_set(v___x_1273_, 1, v___x_1272_);
if (v_hasTrace_1271_ == 0)
{
v___y_1275_ = v___y_1241_;
v___y_1276_ = v___y_1242_;
v___y_1277_ = v___y_1243_;
v___y_1278_ = v___y_1244_;
v___y_1279_ = v___y_1245_;
v___y_1280_ = v___y_1246_;
v___y_1281_ = v___y_1247_;
v___y_1282_ = v___y_1248_;
v___y_1283_ = v___y_1249_;
v___y_1284_ = v___y_1250_;
goto v___jp_1274_;
}
else
{
lean_object* v___x_1309_; lean_object* v___x_1310_; uint8_t v___x_1311_; 
v___x_1309_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_1310_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5);
v___x_1311_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1270_, v_options_1269_, v___x_1310_);
if (v___x_1311_ == 0)
{
v___y_1275_ = v___y_1241_;
v___y_1276_ = v___y_1242_;
v___y_1277_ = v___y_1243_;
v___y_1278_ = v___y_1244_;
v___y_1279_ = v___y_1245_;
v___y_1280_ = v___y_1246_;
v___y_1281_ = v___y_1247_;
v___y_1282_ = v___y_1248_;
v___y_1283_ = v___y_1249_;
v___y_1284_ = v___y_1250_;
goto v___jp_1274_;
}
else
{
lean_object* v___x_1312_; 
lean_inc_ref(v___x_1273_);
v___x_1312_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_1273_, v___y_1241_, v___y_1249_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_object* v_a_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
v_a_1313_ = lean_ctor_get(v___x_1312_, 0);
lean_inc(v_a_1313_);
lean_dec_ref_known(v___x_1312_, 1);
v___x_1314_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7);
v___x_1315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1314_);
lean_ctor_set(v___x_1315_, 1, v_a_1313_);
v___x_1316_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_1309_, v___x_1315_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_dec_ref_known(v___x_1316_, 1);
v___y_1275_ = v___y_1241_;
v___y_1276_ = v___y_1242_;
v___y_1277_ = v___y_1243_;
v___y_1278_ = v___y_1244_;
v___y_1279_ = v___y_1245_;
v___y_1280_ = v___y_1246_;
v___y_1281_ = v___y_1247_;
v___y_1282_ = v___y_1248_;
v___y_1283_ = v___y_1249_;
v___y_1284_ = v___y_1250_;
goto v___jp_1274_;
}
else
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1324_; 
lean_dec_ref_known(v___x_1273_, 2);
lean_del_object(v___x_1256_);
lean_dec(v_snd_1254_);
v_a_1317_ = lean_ctor_get(v___x_1316_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1316_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1319_ = v___x_1316_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1316_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_a_1317_);
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
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
lean_dec_ref_known(v___x_1273_, 2);
lean_del_object(v___x_1256_);
lean_dec(v_snd_1254_);
v_a_1325_ = lean_ctor_get(v___x_1312_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1312_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1312_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1325_);
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
}
v___jp_1274_:
{
lean_object* v___x_1285_; 
lean_inc(v___y_1284_);
lean_inc_ref(v___y_1283_);
lean_inc(v___y_1282_);
lean_inc_ref(v___y_1281_);
lean_inc(v___y_1280_);
lean_inc_ref(v___y_1279_);
lean_inc(v___y_1278_);
lean_inc_ref(v___y_1277_);
lean_inc(v___y_1276_);
lean_inc(v___y_1275_);
v___x_1285_ = lean_grind_cutsat_assert_eq(v___x_1273_, v___y_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1299_; 
v_isSharedCheck_1299_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1299_ == 0)
{
lean_object* v_unused_1300_; 
v_unused_1300_ = lean_ctor_get(v___x_1285_, 0);
lean_dec(v_unused_1300_);
v___x_1287_ = v___x_1285_;
v_isShared_1288_ = v_isSharedCheck_1299_;
goto v_resetjp_1286_;
}
else
{
lean_dec(v___x_1285_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1299_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1292_; 
v___x_1289_ = lean_box(v___x_1262_);
v___x_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1290_, 0, v___x_1289_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 1, v___x_1261_);
lean_ctor_set(v___x_1256_, 0, v___x_1290_);
v___x_1292_ = v___x_1256_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1298_; 
v_reuseFailAlloc_1298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1298_, 0, v___x_1290_);
lean_ctor_set(v_reuseFailAlloc_1298_, 1, v___x_1261_);
v___x_1292_ = v_reuseFailAlloc_1298_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1296_; 
v___x_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1293_, 0, v___x_1292_);
v___x_1294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1293_);
lean_ctor_set(v___x_1294_, 1, v_snd_1254_);
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 0, v___x_1294_);
v___x_1296_ = v___x_1287_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v___x_1294_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
else
{
lean_object* v_a_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1308_; 
lean_del_object(v___x_1256_);
lean_dec(v_snd_1254_);
v_a_1301_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1303_ = v___x_1285_;
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_a_1301_);
lean_dec(v___x_1285_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1306_; 
if (v_isShared_1304_ == 0)
{
v___x_1306_ = v___x_1303_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_a_1301_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
}
}
else
{
lean_object* v_a_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
lean_dec_ref(v_p_1258_);
lean_del_object(v___x_1256_);
lean_dec(v_snd_1254_);
lean_dec_ref(v_c_1236_);
v_a_1333_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1335_ = v___x_1267_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
else
{
lean_inc(v_a_1333_);
lean_dec(v___x_1267_);
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
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1236_ = stack[0].m_obj;
lean_object* v_as_1237_ = stack[1].m_obj;
size_t v_sz_1238_ = stack[2].m_num;
size_t v_i_1239_ = stack[3].m_num;
lean_object* v_b_1240_ = stack[4].m_obj;
lean_object* v___y_1241_ = stack[5].m_obj;
lean_object* v___y_1242_ = stack[6].m_obj;
lean_object* v___y_1243_ = stack[7].m_obj;
lean_object* v___y_1244_ = stack[8].m_obj;
lean_object* v___y_1245_ = stack[9].m_obj;
lean_object* v___y_1246_ = stack[10].m_obj;
lean_object* v___y_1247_ = stack[11].m_obj;
lean_object* v___y_1248_ = stack[12].m_obj;
lean_object* v___y_1249_ = stack[13].m_obj;
lean_object* v___y_1250_ = stack[14].m_obj;
lean_object* v_res_1343_;
v_res_1343_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4(v_c_1236_, v_as_1237_, v_sz_1238_, v_i_1239_, v_b_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_, v___y_1250_);
stack->m_obj
 = v_res_1343_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___boxed(lean_object* v_c_1344_, lean_object* v_as_1345_, lean_object* v_sz_1346_, lean_object* v_i_1347_, lean_object* v_b_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
size_t v_sz_boxed_1360_; size_t v_i_boxed_1361_; lean_object* v_res_1362_; 
v_sz_boxed_1360_ = lean_unbox_usize(v_sz_1346_);
lean_dec(v_sz_1346_);
v_i_boxed_1361_ = lean_unbox_usize(v_i_1347_);
lean_dec(v_i_1347_);
v_res_1362_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4(v_c_1344_, v_as_1345_, v_sz_boxed_1360_, v_i_boxed_1361_, v_b_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
lean_dec(v___y_1352_);
lean_dec_ref(v___y_1351_);
lean_dec(v___y_1350_);
lean_dec(v___y_1349_);
lean_dec_ref(v_as_1345_);
return v_res_1362_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1(lean_object* v_c_1366_, lean_object* v_as_1367_, size_t v_sz_1368_, size_t v_i_1369_, lean_object* v_b_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
uint8_t v___x_1382_; 
v___x_1382_ = lean_usize_dec_lt(v_i_1369_, v_sz_1368_);
if (v___x_1382_ == 0)
{
lean_object* v___x_1383_; 
lean_dec_ref(v_c_1366_);
v___x_1383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1383_, 0, v_b_1370_);
return v___x_1383_;
}
else
{
lean_object* v_snd_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1471_; 
v_snd_1384_ = lean_ctor_get(v_b_1370_, 1);
v_isSharedCheck_1471_ = !lean_is_exclusive(v_b_1370_);
if (v_isSharedCheck_1471_ == 0)
{
lean_object* v_unused_1472_; 
v_unused_1472_ = lean_ctor_get(v_b_1370_, 0);
lean_dec(v_unused_1472_);
v___x_1386_ = v_b_1370_;
v_isShared_1387_ = v_isSharedCheck_1471_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_snd_1384_);
lean_dec(v_b_1370_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1471_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v_p_1388_; lean_object* v_a_1389_; lean_object* v_p_1390_; lean_object* v___x_1391_; uint8_t v___x_1392_; 
v_p_1388_ = lean_ctor_get(v_c_1366_, 0);
v_a_1389_ = lean_array_uget_borrowed(v_as_1367_, v_i_1369_);
v_p_1390_ = lean_ctor_get(v_a_1389_, 0);
v___x_1391_ = lean_box(0);
v___x_1392_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_1388_, v_p_1390_);
if (v___x_1392_ == 0)
{
lean_object* v___x_1393_; size_t v___x_1394_; size_t v___x_1395_; lean_object* v___x_1396_; 
lean_del_object(v___x_1386_);
lean_dec(v_snd_1384_);
v___x_1393_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1___closed__0));
v___x_1394_ = ((size_t)1ULL);
v___x_1395_ = lean_usize_add(v_i_1369_, v___x_1394_);
v___x_1396_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4(v_c_1366_, v_as_1367_, v_sz_1368_, v___x_1395_, v___x_1393_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
return v___x_1396_;
}
else
{
lean_object* v___x_1397_; 
lean_inc_ref(v_p_1388_);
lean_inc(v_a_1389_);
v___x_1397_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_1389_, v___y_1371_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
if (lean_obj_tag(v___x_1397_) == 0)
{
lean_object* v_toCold_1398_; lean_object* v_options_1399_; lean_object* v_inheritedTraceOptions_1400_; uint8_t v_hasTrace_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___y_1405_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; 
lean_dec_ref_known(v___x_1397_, 1);
v_toCold_1398_ = lean_ctor_get(v___y_1379_, 0);
v_options_1399_ = lean_ctor_get(v_toCold_1398_, 2);
v_inheritedTraceOptions_1400_ = lean_ctor_get(v_toCold_1398_, 11);
v_hasTrace_1401_ = lean_ctor_get_uint8(v_options_1399_, sizeof(void*)*1);
lean_inc(v_a_1389_);
v___x_1402_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1402_, 0, v_c_1366_);
lean_ctor_set(v___x_1402_, 1, v_a_1389_);
v___x_1403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1403_, 0, v_p_1388_);
lean_ctor_set(v___x_1403_, 1, v___x_1402_);
if (v_hasTrace_1401_ == 0)
{
v___y_1405_ = v___y_1371_;
v___y_1406_ = v___y_1372_;
v___y_1407_ = v___y_1373_;
v___y_1408_ = v___y_1374_;
v___y_1409_ = v___y_1375_;
v___y_1410_ = v___y_1376_;
v___y_1411_ = v___y_1377_;
v___y_1412_ = v___y_1378_;
v___y_1413_ = v___y_1379_;
v___y_1414_ = v___y_1380_;
goto v___jp_1404_;
}
else
{
lean_object* v___x_1439_; lean_object* v___x_1440_; uint8_t v___x_1441_; 
v___x_1439_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_1440_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5);
v___x_1441_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1400_, v_options_1399_, v___x_1440_);
if (v___x_1441_ == 0)
{
v___y_1405_ = v___y_1371_;
v___y_1406_ = v___y_1372_;
v___y_1407_ = v___y_1373_;
v___y_1408_ = v___y_1374_;
v___y_1409_ = v___y_1375_;
v___y_1410_ = v___y_1376_;
v___y_1411_ = v___y_1377_;
v___y_1412_ = v___y_1378_;
v___y_1413_ = v___y_1379_;
v___y_1414_ = v___y_1380_;
goto v___jp_1404_;
}
else
{
lean_object* v___x_1442_; 
lean_inc_ref(v___x_1403_);
v___x_1442_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_1403_, v___y_1371_, v___y_1379_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_object* v_a_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; 
v_a_1443_ = lean_ctor_get(v___x_1442_, 0);
lean_inc(v_a_1443_);
lean_dec_ref_known(v___x_1442_, 1);
v___x_1444_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7);
v___x_1445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1444_);
lean_ctor_set(v___x_1445_, 1, v_a_1443_);
v___x_1446_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_1439_, v___x_1445_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
if (lean_obj_tag(v___x_1446_) == 0)
{
lean_dec_ref_known(v___x_1446_, 1);
v___y_1405_ = v___y_1371_;
v___y_1406_ = v___y_1372_;
v___y_1407_ = v___y_1373_;
v___y_1408_ = v___y_1374_;
v___y_1409_ = v___y_1375_;
v___y_1410_ = v___y_1376_;
v___y_1411_ = v___y_1377_;
v___y_1412_ = v___y_1378_;
v___y_1413_ = v___y_1379_;
v___y_1414_ = v___y_1380_;
goto v___jp_1404_;
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
lean_dec_ref_known(v___x_1403_, 2);
lean_del_object(v___x_1386_);
lean_dec(v_snd_1384_);
v_a_1447_ = lean_ctor_get(v___x_1446_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1446_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1446_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1446_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1447_);
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
lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1462_; 
lean_dec_ref_known(v___x_1403_, 2);
lean_del_object(v___x_1386_);
lean_dec(v_snd_1384_);
v_a_1455_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1457_ = v___x_1442_;
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1442_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1460_; 
if (v_isShared_1458_ == 0)
{
v___x_1460_ = v___x_1457_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_a_1455_);
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
}
v___jp_1404_:
{
lean_object* v___x_1415_; 
lean_inc(v___y_1414_);
lean_inc_ref(v___y_1413_);
lean_inc(v___y_1412_);
lean_inc_ref(v___y_1411_);
lean_inc(v___y_1410_);
lean_inc_ref(v___y_1409_);
lean_inc(v___y_1408_);
lean_inc_ref(v___y_1407_);
lean_inc(v___y_1406_);
lean_inc(v___y_1405_);
v___x_1415_ = lean_grind_cutsat_assert_eq(v___x_1403_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v___x_1417_; uint8_t v_isShared_1418_; uint8_t v_isSharedCheck_1429_; 
v_isSharedCheck_1429_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1429_ == 0)
{
lean_object* v_unused_1430_; 
v_unused_1430_ = lean_ctor_get(v___x_1415_, 0);
lean_dec(v_unused_1430_);
v___x_1417_ = v___x_1415_;
v_isShared_1418_ = v_isSharedCheck_1429_;
goto v_resetjp_1416_;
}
else
{
lean_dec(v___x_1415_);
v___x_1417_ = lean_box(0);
v_isShared_1418_ = v_isSharedCheck_1429_;
goto v_resetjp_1416_;
}
v_resetjp_1416_:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1422_; 
v___x_1419_ = lean_box(v___x_1392_);
v___x_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1419_);
if (v_isShared_1387_ == 0)
{
lean_ctor_set(v___x_1386_, 1, v___x_1391_);
lean_ctor_set(v___x_1386_, 0, v___x_1420_);
v___x_1422_ = v___x_1386_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v___x_1420_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v___x_1391_);
v___x_1422_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1426_; 
v___x_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1422_);
v___x_1424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1424_, 0, v___x_1423_);
lean_ctor_set(v___x_1424_, 1, v_snd_1384_);
if (v_isShared_1418_ == 0)
{
lean_ctor_set(v___x_1417_, 0, v___x_1424_);
v___x_1426_ = v___x_1417_;
goto v_reusejp_1425_;
}
else
{
lean_object* v_reuseFailAlloc_1427_; 
v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1427_, 0, v___x_1424_);
v___x_1426_ = v_reuseFailAlloc_1427_;
goto v_reusejp_1425_;
}
v_reusejp_1425_:
{
return v___x_1426_;
}
}
}
}
else
{
lean_object* v_a_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1438_; 
lean_del_object(v___x_1386_);
lean_dec(v_snd_1384_);
v_a_1431_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1438_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1438_ == 0)
{
v___x_1433_ = v___x_1415_;
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_a_1431_);
lean_dec(v___x_1415_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1438_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v___x_1436_; 
if (v_isShared_1434_ == 0)
{
v___x_1436_ = v___x_1433_;
goto v_reusejp_1435_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v_a_1431_);
v___x_1436_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1435_;
}
v_reusejp_1435_:
{
return v___x_1436_;
}
}
}
}
}
else
{
lean_object* v_a_1463_; lean_object* v___x_1465_; uint8_t v_isShared_1466_; uint8_t v_isSharedCheck_1470_; 
lean_dec_ref(v_p_1388_);
lean_del_object(v___x_1386_);
lean_dec(v_snd_1384_);
lean_dec_ref(v_c_1366_);
v_a_1463_ = lean_ctor_get(v___x_1397_, 0);
v_isSharedCheck_1470_ = !lean_is_exclusive(v___x_1397_);
if (v_isSharedCheck_1470_ == 0)
{
v___x_1465_ = v___x_1397_;
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
else
{
lean_inc(v_a_1463_);
lean_dec(v___x_1397_);
v___x_1465_ = lean_box(0);
v_isShared_1466_ = v_isSharedCheck_1470_;
goto v_resetjp_1464_;
}
v_resetjp_1464_:
{
lean_object* v___x_1468_; 
if (v_isShared_1466_ == 0)
{
v___x_1468_ = v___x_1465_;
goto v_reusejp_1467_;
}
else
{
lean_object* v_reuseFailAlloc_1469_; 
v_reuseFailAlloc_1469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1469_, 0, v_a_1463_);
v___x_1468_ = v_reuseFailAlloc_1469_;
goto v_reusejp_1467_;
}
v_reusejp_1467_:
{
return v___x_1468_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1366_ = stack[0].m_obj;
lean_object* v_as_1367_ = stack[1].m_obj;
size_t v_sz_1368_ = stack[2].m_num;
size_t v_i_1369_ = stack[3].m_num;
lean_object* v_b_1370_ = stack[4].m_obj;
lean_object* v___y_1371_ = stack[5].m_obj;
lean_object* v___y_1372_ = stack[6].m_obj;
lean_object* v___y_1373_ = stack[7].m_obj;
lean_object* v___y_1374_ = stack[8].m_obj;
lean_object* v___y_1375_ = stack[9].m_obj;
lean_object* v___y_1376_ = stack[10].m_obj;
lean_object* v___y_1377_ = stack[11].m_obj;
lean_object* v___y_1378_ = stack[12].m_obj;
lean_object* v___y_1379_ = stack[13].m_obj;
lean_object* v___y_1380_ = stack[14].m_obj;
lean_object* v_res_1473_;
v_res_1473_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1(v_c_1366_, v_as_1367_, v_sz_1368_, v_i_1369_, v_b_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_);
stack->m_obj
 = v_res_1473_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1___boxed(lean_object* v_c_1474_, lean_object* v_as_1475_, lean_object* v_sz_1476_, lean_object* v_i_1477_, lean_object* v_b_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
size_t v_sz_boxed_1490_; size_t v_i_boxed_1491_; lean_object* v_res_1492_; 
v_sz_boxed_1490_ = lean_unbox_usize(v_sz_1476_);
lean_dec(v_sz_1476_);
v_i_boxed_1491_ = lean_unbox_usize(v_i_1477_);
lean_dec(v_i_1477_);
v_res_1492_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1(v_c_1474_, v_as_1475_, v_sz_boxed_1490_, v_i_boxed_1491_, v_b_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v___y_1480_);
lean_dec(v___y_1479_);
lean_dec_ref(v_as_1475_);
return v_res_1492_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0(lean_object* v_c_1493_, lean_object* v_t_1494_, lean_object* v_init_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
lean_object* v_root_1507_; lean_object* v_tail_1508_; lean_object* v___x_1509_; 
v_root_1507_ = lean_ctor_get(v_t_1494_, 0);
v_tail_1508_ = lean_ctor_get(v_t_1494_, 1);
lean_inc_ref(v_c_1493_);
lean_inc_ref(v_init_1495_);
v___x_1509_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(v_init_1495_, v_c_1493_, v_root_1507_, v_init_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
lean_dec_ref(v_init_1495_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1546_; 
v_a_1510_ = lean_ctor_get(v___x_1509_, 0);
v_isSharedCheck_1546_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1546_ == 0)
{
v___x_1512_ = v___x_1509_;
v_isShared_1513_ = v_isSharedCheck_1546_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___x_1509_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1546_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
if (lean_obj_tag(v_a_1510_) == 0)
{
lean_object* v_a_1514_; lean_object* v___x_1516_; 
lean_dec_ref(v_c_1493_);
v_a_1514_ = lean_ctor_get(v_a_1510_, 0);
lean_inc(v_a_1514_);
lean_dec_ref_known(v_a_1510_, 1);
if (v_isShared_1513_ == 0)
{
lean_ctor_set(v___x_1512_, 0, v_a_1514_);
v___x_1516_ = v___x_1512_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_a_1514_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
else
{
lean_object* v_a_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; size_t v_sz_1521_; size_t v___x_1522_; lean_object* v___x_1523_; 
lean_del_object(v___x_1512_);
v_a_1518_ = lean_ctor_get(v_a_1510_, 0);
lean_inc(v_a_1518_);
lean_dec_ref_known(v_a_1510_, 1);
v___x_1519_ = lean_box(0);
v___x_1520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1519_);
lean_ctor_set(v___x_1520_, 1, v_a_1518_);
v_sz_1521_ = lean_array_size(v_tail_1508_);
v___x_1522_ = ((size_t)0ULL);
v___x_1523_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1(v_c_1493_, v_tail_1508_, v_sz_1521_, v___x_1522_, v___x_1520_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
if (lean_obj_tag(v___x_1523_) == 0)
{
lean_object* v_a_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1537_; 
v_a_1524_ = lean_ctor_get(v___x_1523_, 0);
v_isSharedCheck_1537_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1537_ == 0)
{
v___x_1526_ = v___x_1523_;
v_isShared_1527_ = v_isSharedCheck_1537_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_a_1524_);
lean_dec(v___x_1523_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1537_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
lean_object* v_fst_1528_; 
v_fst_1528_ = lean_ctor_get(v_a_1524_, 0);
if (lean_obj_tag(v_fst_1528_) == 0)
{
lean_object* v_snd_1529_; lean_object* v___x_1531_; 
v_snd_1529_ = lean_ctor_get(v_a_1524_, 1);
lean_inc(v_snd_1529_);
lean_dec(v_a_1524_);
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 0, v_snd_1529_);
v___x_1531_ = v___x_1526_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_snd_1529_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
else
{
lean_object* v_val_1533_; lean_object* v___x_1535_; 
lean_inc_ref(v_fst_1528_);
lean_dec(v_a_1524_);
v_val_1533_ = lean_ctor_get(v_fst_1528_, 0);
lean_inc(v_val_1533_);
lean_dec_ref_known(v_fst_1528_, 1);
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 0, v_val_1533_);
v___x_1535_ = v___x_1526_;
goto v_reusejp_1534_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_val_1533_);
v___x_1535_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1534_;
}
v_reusejp_1534_:
{
return v___x_1535_;
}
}
}
}
else
{
lean_object* v_a_1538_; lean_object* v___x_1540_; uint8_t v_isShared_1541_; uint8_t v_isSharedCheck_1545_; 
v_a_1538_ = lean_ctor_get(v___x_1523_, 0);
v_isSharedCheck_1545_ = !lean_is_exclusive(v___x_1523_);
if (v_isSharedCheck_1545_ == 0)
{
v___x_1540_ = v___x_1523_;
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
else
{
lean_inc(v_a_1538_);
lean_dec(v___x_1523_);
v___x_1540_ = lean_box(0);
v_isShared_1541_ = v_isSharedCheck_1545_;
goto v_resetjp_1539_;
}
v_resetjp_1539_:
{
lean_object* v___x_1543_; 
if (v_isShared_1541_ == 0)
{
v___x_1543_ = v___x_1540_;
goto v_reusejp_1542_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v_a_1538_);
v___x_1543_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1542_;
}
v_reusejp_1542_:
{
return v___x_1543_;
}
}
}
}
}
}
else
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1554_; 
lean_dec_ref(v_c_1493_);
v_a_1547_ = lean_ctor_get(v___x_1509_, 0);
v_isSharedCheck_1554_ = !lean_is_exclusive(v___x_1509_);
if (v_isSharedCheck_1554_ == 0)
{
v___x_1549_ = v___x_1509_;
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1509_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1554_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1552_; 
if (v_isShared_1550_ == 0)
{
v___x_1552_ = v___x_1549_;
goto v_reusejp_1551_;
}
else
{
lean_object* v_reuseFailAlloc_1553_; 
v_reuseFailAlloc_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1553_, 0, v_a_1547_);
v___x_1552_ = v_reuseFailAlloc_1553_;
goto v_reusejp_1551_;
}
v_reusejp_1551_:
{
return v___x_1552_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1493_ = stack[0].m_obj;
lean_object* v_t_1494_ = stack[1].m_obj;
lean_object* v_init_1495_ = stack[2].m_obj;
lean_object* v___y_1496_ = stack[3].m_obj;
lean_object* v___y_1497_ = stack[4].m_obj;
lean_object* v___y_1498_ = stack[5].m_obj;
lean_object* v___y_1499_ = stack[6].m_obj;
lean_object* v___y_1500_ = stack[7].m_obj;
lean_object* v___y_1501_ = stack[8].m_obj;
lean_object* v___y_1502_ = stack[9].m_obj;
lean_object* v___y_1503_ = stack[10].m_obj;
lean_object* v___y_1504_ = stack[11].m_obj;
lean_object* v___y_1505_ = stack[12].m_obj;
lean_object* v_res_1555_;
v_res_1555_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0(v_c_1493_, v_t_1494_, v_init_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_);
stack->m_obj
 = v_res_1555_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0___boxed(lean_object* v_c_1556_, lean_object* v_t_1557_, lean_object* v_init_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
lean_object* v_res_1570_; 
v_res_1570_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0(v_c_1556_, v_t_1557_, v_init_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec(v___y_1564_);
lean_dec_ref(v___y_1563_);
lean_dec(v___y_1562_);
lean_dec_ref(v___y_1561_);
lean_dec(v___y_1560_);
lean_dec(v___y_1559_);
lean_dec_ref(v_t_1557_);
return v_res_1570_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0(void){
_start:
{
lean_object* v___x_1571_; 
v___x_1571_ = l_Lean_instInhabitedPersistentArray_default___redArg();
return v___x_1571_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq(lean_object* v_c_1572_, lean_object* v_a_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_, lean_object* v_a_1576_, lean_object* v_a_1577_, lean_object* v_a_1578_, lean_object* v_a_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_){
_start:
{
lean_object* v_p_1584_; 
v_p_1584_ = lean_ctor_get(v_c_1572_, 0);
if (lean_obj_tag(v_p_1584_) == 1)
{
lean_object* v_k_1585_; lean_object* v_v_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v_k_1585_ = lean_ctor_get(v_p_1584_, 0);
v_v_1586_ = lean_ctor_get(v_p_1584_, 1);
v___x_1587_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0);
v___x_1588_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1573_, v_a_1581_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v_a_1589_; lean_object* v___y_1591_; lean_object* v___x_1617_; uint8_t v___x_1618_; 
v_a_1589_ = lean_ctor_get(v___x_1588_, 0);
lean_inc(v_a_1589_);
lean_dec_ref_known(v___x_1588_, 1);
v___x_1617_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9);
v___x_1618_ = lean_int_dec_lt(v_k_1585_, v___x_1617_);
if (v___x_1618_ == 0)
{
lean_object* v_lowers_1619_; lean_object* v_size_1620_; uint8_t v___x_1621_; 
v_lowers_1619_ = lean_ctor_get(v_a_1589_, 6);
lean_inc_ref(v_lowers_1619_);
lean_dec(v_a_1589_);
v_size_1620_ = lean_ctor_get(v_lowers_1619_, 2);
v___x_1621_ = lean_nat_dec_lt(v_v_1586_, v_size_1620_);
if (v___x_1621_ == 0)
{
lean_object* v___x_1622_; 
lean_dec_ref(v_lowers_1619_);
v___x_1622_ = l_outOfBounds___redArg(v___x_1587_);
v___y_1591_ = v___x_1622_;
goto v___jp_1590_;
}
else
{
lean_object* v___x_1623_; 
v___x_1623_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1587_, v_lowers_1619_, v_v_1586_);
lean_dec_ref(v_lowers_1619_);
v___y_1591_ = v___x_1623_;
goto v___jp_1590_;
}
}
else
{
lean_object* v_uppers_1624_; lean_object* v_size_1625_; uint8_t v___x_1626_; 
v_uppers_1624_ = lean_ctor_get(v_a_1589_, 7);
lean_inc_ref(v_uppers_1624_);
lean_dec(v_a_1589_);
v_size_1625_ = lean_ctor_get(v_uppers_1624_, 2);
v___x_1626_ = lean_nat_dec_lt(v_v_1586_, v_size_1625_);
if (v___x_1626_ == 0)
{
lean_object* v___x_1627_; 
lean_dec_ref(v_uppers_1624_);
v___x_1627_ = l_outOfBounds___redArg(v___x_1587_);
v___y_1591_ = v___x_1627_;
goto v___jp_1590_;
}
else
{
lean_object* v___x_1628_; 
v___x_1628_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1587_, v_uppers_1624_, v_v_1586_);
lean_dec_ref(v_uppers_1624_);
v___y_1591_ = v___x_1628_;
goto v___jp_1590_;
}
}
v___jp_1590_:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1592_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__0));
v___x_1593_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0(v_c_1572_, v___y_1591_, v___x_1592_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_);
lean_dec_ref(v___y_1591_);
if (lean_obj_tag(v___x_1593_) == 0)
{
lean_object* v_a_1594_; lean_object* v___x_1596_; uint8_t v_isShared_1597_; uint8_t v_isSharedCheck_1608_; 
v_a_1594_ = lean_ctor_get(v___x_1593_, 0);
v_isSharedCheck_1608_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1608_ == 0)
{
v___x_1596_ = v___x_1593_;
v_isShared_1597_ = v_isSharedCheck_1608_;
goto v_resetjp_1595_;
}
else
{
lean_inc(v_a_1594_);
lean_dec(v___x_1593_);
v___x_1596_ = lean_box(0);
v_isShared_1597_ = v_isSharedCheck_1608_;
goto v_resetjp_1595_;
}
v_resetjp_1595_:
{
lean_object* v_fst_1598_; 
v_fst_1598_ = lean_ctor_get(v_a_1594_, 0);
lean_inc(v_fst_1598_);
lean_dec(v_a_1594_);
if (lean_obj_tag(v_fst_1598_) == 0)
{
uint8_t v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1602_; 
v___x_1599_ = 0;
v___x_1600_ = lean_box(v___x_1599_);
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 0, v___x_1600_);
v___x_1602_ = v___x_1596_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v___x_1600_);
v___x_1602_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
return v___x_1602_;
}
}
else
{
lean_object* v_val_1604_; lean_object* v___x_1606_; 
v_val_1604_ = lean_ctor_get(v_fst_1598_, 0);
lean_inc(v_val_1604_);
lean_dec_ref_known(v_fst_1598_, 1);
if (v_isShared_1597_ == 0)
{
lean_ctor_set(v___x_1596_, 0, v_val_1604_);
v___x_1606_ = v___x_1596_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_val_1604_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
else
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1616_; 
v_a_1609_ = lean_ctor_get(v___x_1593_, 0);
v_isSharedCheck_1616_ = !lean_is_exclusive(v___x_1593_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1611_ = v___x_1593_;
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1593_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1616_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1614_; 
if (v_isShared_1612_ == 0)
{
v___x_1614_ = v___x_1611_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_a_1609_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
}
}
}
}
}
else
{
lean_object* v_a_1629_; lean_object* v___x_1631_; uint8_t v_isShared_1632_; uint8_t v_isSharedCheck_1636_; 
lean_dec_ref(v_c_1572_);
v_a_1629_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1636_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1636_ == 0)
{
v___x_1631_ = v___x_1588_;
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
else
{
lean_inc(v_a_1629_);
lean_dec(v___x_1588_);
v___x_1631_ = lean_box(0);
v_isShared_1632_ = v_isSharedCheck_1636_;
goto v_resetjp_1630_;
}
v_resetjp_1630_:
{
lean_object* v___x_1634_; 
if (v_isShared_1632_ == 0)
{
v___x_1634_ = v___x_1631_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1635_; 
v_reuseFailAlloc_1635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1635_, 0, v_a_1629_);
v___x_1634_ = v_reuseFailAlloc_1635_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
return v___x_1634_;
}
}
}
}
else
{
lean_object* v___x_1637_; 
v___x_1637_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_1572_, v_a_1573_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_);
return v___x_1637_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1572_ = stack[0].m_obj;
lean_object* v_a_1573_ = stack[1].m_obj;
lean_object* v_a_1574_ = stack[2].m_obj;
lean_object* v_a_1575_ = stack[3].m_obj;
lean_object* v_a_1576_ = stack[4].m_obj;
lean_object* v_a_1577_ = stack[5].m_obj;
lean_object* v_a_1578_ = stack[6].m_obj;
lean_object* v_a_1579_ = stack[7].m_obj;
lean_object* v_a_1580_ = stack[8].m_obj;
lean_object* v_a_1581_ = stack[9].m_obj;
lean_object* v_a_1582_ = stack[10].m_obj;
lean_object* v_res_1638_;
v_res_1638_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq(v_c_1572_, v_a_1573_, v_a_1574_, v_a_1575_, v_a_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_);
stack->m_obj
 = v_res_1638_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___boxed(lean_object* v_c_1639_, lean_object* v_a_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_){
_start:
{
lean_object* v_res_1651_; 
v_res_1651_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq(v_c_1639_, v_a_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_, v_a_1649_);
lean_dec(v_a_1649_);
lean_dec_ref(v_a_1648_);
lean_dec(v_a_1647_);
lean_dec_ref(v_a_1646_);
lean_dec(v_a_1645_);
lean_dec_ref(v_a_1644_);
lean_dec(v_a_1643_);
lean_dec_ref(v_a_1642_);
lean_dec(v_a_1641_);
lean_dec(v_a_1640_);
return v_res_1651_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(lean_object* v___x_1652_, lean_object* v_as_1653_, size_t v_i_1654_, size_t v_stop_1655_, lean_object* v_b_1656_){
_start:
{
lean_object* v___y_1658_; uint8_t v___x_1662_; 
v___x_1662_ = lean_usize_dec_eq(v_i_1654_, v_stop_1655_);
if (v___x_1662_ == 0)
{
lean_object* v___x_1663_; lean_object* v_p_1664_; uint8_t v___x_1665_; 
v___x_1663_ = lean_array_uget_borrowed(v_as_1653_, v_i_1654_);
v_p_1664_ = lean_ctor_get(v___x_1663_, 0);
v___x_1665_ = l_Int_Internal_Linear_instBEqPoly_beq(v_p_1664_, v___x_1652_);
if (v___x_1665_ == 0)
{
lean_object* v___x_1666_; 
lean_inc(v___x_1663_);
v___x_1666_ = l_Lean_PersistentArray_push___redArg(v_b_1656_, v___x_1663_);
v___y_1658_ = v___x_1666_;
goto v___jp_1657_;
}
else
{
v___y_1658_ = v_b_1656_;
goto v___jp_1657_;
}
}
else
{
return v_b_1656_;
}
v___jp_1657_:
{
size_t v___x_1659_; size_t v___x_1660_; 
v___x_1659_ = ((size_t)1ULL);
v___x_1660_ = lean_usize_add(v_i_1654_, v___x_1659_);
v_i_1654_ = v___x_1660_;
v_b_1656_ = v___y_1658_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1652_ = stack[0].m_obj;
lean_object* v_as_1653_ = stack[1].m_obj;
size_t v_i_1654_ = stack[2].m_num;
size_t v_stop_1655_ = stack[3].m_num;
lean_object* v_b_1656_ = stack[4].m_obj;
lean_object* v_res_1667_;
v_res_1667_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1652_, v_as_1653_, v_i_1654_, v_stop_1655_, v_b_1656_);
stack->m_obj
 = v_res_1667_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1___boxed(lean_object* v___x_1668_, lean_object* v_as_1669_, lean_object* v_i_1670_, lean_object* v_stop_1671_, lean_object* v_b_1672_){
_start:
{
size_t v_i_boxed_1673_; size_t v_stop_boxed_1674_; lean_object* v_res_1675_; 
v_i_boxed_1673_ = lean_unbox_usize(v_i_1670_);
lean_dec(v_i_1670_);
v_stop_boxed_1674_ = lean_unbox_usize(v_stop_1671_);
lean_dec(v_stop_1671_);
v_res_1675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1668_, v_as_1669_, v_i_boxed_1673_, v_stop_boxed_1674_, v_b_1672_);
lean_dec_ref(v_as_1669_);
lean_dec_ref(v___x_1668_);
return v_res_1675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(lean_object* v___x_1676_, lean_object* v_x_1677_, lean_object* v_x_1678_){
_start:
{
if (lean_obj_tag(v_x_1677_) == 0)
{
lean_object* v_cs_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; uint8_t v___x_1682_; 
v_cs_1679_ = lean_ctor_get(v_x_1677_, 0);
v___x_1680_ = lean_unsigned_to_nat(0u);
v___x_1681_ = lean_array_get_size(v_cs_1679_);
v___x_1682_ = lean_nat_dec_lt(v___x_1680_, v___x_1681_);
if (v___x_1682_ == 0)
{
return v_x_1678_;
}
else
{
size_t v___x_1683_; size_t v___x_1684_; lean_object* v___x_1685_; 
v___x_1683_ = ((size_t)0ULL);
v___x_1684_ = lean_usize_of_nat(v___x_1681_);
v___x_1685_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1676_, v_cs_1679_, v___x_1683_, v___x_1684_, v_x_1678_);
return v___x_1685_;
}
}
else
{
lean_object* v_vs_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; uint8_t v___x_1689_; 
v_vs_1686_ = lean_ctor_get(v_x_1677_, 0);
v___x_1687_ = lean_unsigned_to_nat(0u);
v___x_1688_ = lean_array_get_size(v_vs_1686_);
v___x_1689_ = lean_nat_dec_lt(v___x_1687_, v___x_1688_);
if (v___x_1689_ == 0)
{
return v_x_1678_;
}
else
{
size_t v___x_1690_; size_t v___x_1691_; lean_object* v___x_1692_; 
v___x_1690_ = ((size_t)0ULL);
v___x_1691_ = lean_usize_of_nat(v___x_1688_);
v___x_1692_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1676_, v_vs_1686_, v___x_1690_, v___x_1691_, v_x_1678_);
return v___x_1692_;
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(lean_object* v___x_1693_, lean_object* v_as_1694_, size_t v_i_1695_, size_t v_stop_1696_, lean_object* v_b_1697_){
_start:
{
uint8_t v___x_1698_; 
v___x_1698_ = lean_usize_dec_eq(v_i_1695_, v_stop_1696_);
if (v___x_1698_ == 0)
{
lean_object* v___x_1699_; lean_object* v___x_1700_; size_t v___x_1701_; size_t v___x_1702_; 
v___x_1699_ = lean_array_uget_borrowed(v_as_1694_, v_i_1695_);
v___x_1700_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(v___x_1693_, v___x_1699_, v_b_1697_);
v___x_1701_ = ((size_t)1ULL);
v___x_1702_ = lean_usize_add(v_i_1695_, v___x_1701_);
v_i_1695_ = v___x_1702_;
v_b_1697_ = v___x_1700_;
goto _start;
}
else
{
return v_b_1697_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1693_ = stack[0].m_obj;
lean_object* v_as_1694_ = stack[1].m_obj;
size_t v_i_1695_ = stack[2].m_num;
size_t v_stop_1696_ = stack[3].m_num;
lean_object* v_b_1697_ = stack[4].m_obj;
lean_object* v_res_1704_;
v_res_1704_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1693_, v_as_1694_, v_i_1695_, v_stop_1696_, v_b_1697_);
stack->m_obj
 = v_res_1704_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v___x_1705_, lean_object* v_as_1706_, lean_object* v_i_1707_, lean_object* v_stop_1708_, lean_object* v_b_1709_){
_start:
{
size_t v_i_boxed_1710_; size_t v_stop_boxed_1711_; lean_object* v_res_1712_; 
v_i_boxed_1710_ = lean_unbox_usize(v_i_1707_);
lean_dec(v_i_1707_);
v_stop_boxed_1711_ = lean_unbox_usize(v_stop_1708_);
lean_dec(v_stop_1708_);
v_res_1712_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1705_, v_as_1706_, v_i_boxed_1710_, v_stop_boxed_1711_, v_b_1709_);
lean_dec_ref(v_as_1706_);
lean_dec_ref(v___x_1705_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2___boxed(lean_object* v___x_1713_, lean_object* v_x_1714_, lean_object* v_x_1715_){
_start:
{
lean_object* v_res_1716_; 
v_res_1716_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(v___x_1713_, v_x_1714_, v_x_1715_);
lean_dec_ref(v_x_1714_);
lean_dec_ref(v___x_1713_);
return v_res_1716_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(lean_object* v___x_1717_, lean_object* v_x_1718_, size_t v_x_1719_, size_t v_x_1720_, lean_object* v_x_1721_){
_start:
{
if (lean_obj_tag(v_x_1718_) == 0)
{
lean_object* v_cs_1722_; lean_object* v___x_1723_; size_t v___x_1724_; lean_object* v_j_1725_; lean_object* v___x_1726_; size_t v___x_1727_; size_t v___x_1728_; size_t v___x_1729_; size_t v___x_1730_; size_t v___x_1731_; size_t v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; uint8_t v___x_1737_; 
v_cs_1722_ = lean_ctor_get(v_x_1718_, 0);
v___x_1723_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0);
v___x_1724_ = lean_usize_shift_right(v_x_1719_, v_x_1720_);
v_j_1725_ = lean_usize_to_nat(v___x_1724_);
v___x_1726_ = lean_array_get_borrowed(v___x_1723_, v_cs_1722_, v_j_1725_);
v___x_1727_ = ((size_t)1ULL);
v___x_1728_ = lean_usize_shift_left(v___x_1727_, v_x_1720_);
v___x_1729_ = lean_usize_sub(v___x_1728_, v___x_1727_);
v___x_1730_ = lean_usize_land(v_x_1719_, v___x_1729_);
v___x_1731_ = ((size_t)5ULL);
v___x_1732_ = lean_usize_sub(v_x_1720_, v___x_1731_);
v___x_1733_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(v___x_1717_, v___x_1726_, v___x_1730_, v___x_1732_, v_x_1721_);
v___x_1734_ = lean_unsigned_to_nat(1u);
v___x_1735_ = lean_nat_add(v_j_1725_, v___x_1734_);
lean_dec(v_j_1725_);
v___x_1736_ = lean_array_get_size(v_cs_1722_);
v___x_1737_ = lean_nat_dec_lt(v___x_1735_, v___x_1736_);
if (v___x_1737_ == 0)
{
lean_dec(v___x_1735_);
return v___x_1733_;
}
else
{
size_t v___x_1738_; size_t v___x_1739_; lean_object* v___x_1740_; 
v___x_1738_ = lean_usize_of_nat(v___x_1735_);
lean_dec(v___x_1735_);
v___x_1739_ = lean_usize_of_nat(v___x_1736_);
v___x_1740_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1717_, v_cs_1722_, v___x_1738_, v___x_1739_, v___x_1733_);
return v___x_1740_;
}
}
else
{
lean_object* v_vs_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; uint8_t v___x_1744_; 
v_vs_1741_ = lean_ctor_get(v_x_1718_, 0);
v___x_1742_ = lean_usize_to_nat(v_x_1719_);
v___x_1743_ = lean_array_get_size(v_vs_1741_);
v___x_1744_ = lean_nat_dec_lt(v___x_1742_, v___x_1743_);
if (v___x_1744_ == 0)
{
lean_dec(v___x_1742_);
return v_x_1721_;
}
else
{
size_t v___x_1745_; size_t v___x_1746_; lean_object* v___x_1747_; 
v___x_1745_ = lean_usize_of_nat(v___x_1742_);
lean_dec(v___x_1742_);
v___x_1746_ = lean_usize_of_nat(v___x_1743_);
v___x_1747_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1717_, v_vs_1741_, v___x_1745_, v___x_1746_, v_x_1721_);
return v___x_1747_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1717_ = stack[0].m_obj;
lean_object* v_x_1718_ = stack[1].m_obj;
size_t v_x_1719_ = stack[2].m_num;
size_t v_x_1720_ = stack[3].m_num;
lean_object* v_x_1721_ = stack[4].m_obj;
lean_object* v_res_1748_;
v_res_1748_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(v___x_1717_, v_x_1718_, v_x_1719_, v_x_1720_, v_x_1721_);
stack->m_obj
 = v_res_1748_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0___boxed(lean_object* v___x_1749_, lean_object* v_x_1750_, lean_object* v_x_1751_, lean_object* v_x_1752_, lean_object* v_x_1753_){
_start:
{
size_t v_x_20572__boxed_1754_; size_t v_x_20573__boxed_1755_; lean_object* v_res_1756_; 
v_x_20572__boxed_1754_ = lean_unbox_usize(v_x_1751_);
lean_dec(v_x_1751_);
v_x_20573__boxed_1755_ = lean_unbox_usize(v_x_1752_);
lean_dec(v_x_1752_);
v_res_1756_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(v___x_1749_, v_x_1750_, v_x_20572__boxed_1754_, v_x_20573__boxed_1755_, v_x_1753_);
lean_dec_ref(v_x_1750_);
lean_dec_ref(v___x_1749_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(lean_object* v___x_1757_, lean_object* v_t_1758_, lean_object* v_init_1759_, lean_object* v_start_1760_){
_start:
{
lean_object* v___x_1761_; uint8_t v___x_1762_; 
v___x_1761_ = lean_unsigned_to_nat(0u);
v___x_1762_ = lean_nat_dec_eq(v_start_1760_, v___x_1761_);
if (v___x_1762_ == 0)
{
lean_object* v_root_1763_; lean_object* v_tail_1764_; size_t v_shift_1765_; lean_object* v_tailOff_1766_; uint8_t v___x_1767_; 
v_root_1763_ = lean_ctor_get(v_t_1758_, 0);
v_tail_1764_ = lean_ctor_get(v_t_1758_, 1);
v_shift_1765_ = lean_ctor_get_usize(v_t_1758_, 4);
v_tailOff_1766_ = lean_ctor_get(v_t_1758_, 3);
v___x_1767_ = lean_nat_dec_le(v_tailOff_1766_, v_start_1760_);
if (v___x_1767_ == 0)
{
size_t v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; uint8_t v___x_1771_; 
v___x_1768_ = lean_usize_of_nat(v_start_1760_);
v___x_1769_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(v___x_1757_, v_root_1763_, v___x_1768_, v_shift_1765_, v_init_1759_);
v___x_1770_ = lean_array_get_size(v_tail_1764_);
v___x_1771_ = lean_nat_dec_lt(v___x_1761_, v___x_1770_);
if (v___x_1771_ == 0)
{
return v___x_1769_;
}
else
{
size_t v___x_1772_; size_t v___x_1773_; lean_object* v___x_1774_; 
v___x_1772_ = ((size_t)0ULL);
v___x_1773_ = lean_usize_of_nat(v___x_1770_);
v___x_1774_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1757_, v_tail_1764_, v___x_1772_, v___x_1773_, v___x_1769_);
return v___x_1774_;
}
}
else
{
lean_object* v___x_1775_; lean_object* v___x_1776_; uint8_t v___x_1777_; 
v___x_1775_ = lean_nat_sub(v_start_1760_, v_tailOff_1766_);
v___x_1776_ = lean_array_get_size(v_tail_1764_);
v___x_1777_ = lean_nat_dec_lt(v___x_1775_, v___x_1776_);
if (v___x_1777_ == 0)
{
lean_dec(v___x_1775_);
return v_init_1759_;
}
else
{
size_t v___x_1778_; size_t v___x_1779_; lean_object* v___x_1780_; 
v___x_1778_ = lean_usize_of_nat(v___x_1775_);
lean_dec(v___x_1775_);
v___x_1779_ = lean_usize_of_nat(v___x_1776_);
v___x_1780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1757_, v_tail_1764_, v___x_1778_, v___x_1779_, v_init_1759_);
return v___x_1780_;
}
}
}
else
{
lean_object* v_root_1781_; lean_object* v_tail_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; uint8_t v___x_1785_; 
v_root_1781_ = lean_ctor_get(v_t_1758_, 0);
v_tail_1782_ = lean_ctor_get(v_t_1758_, 1);
v___x_1783_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(v___x_1757_, v_root_1781_, v_init_1759_);
v___x_1784_ = lean_array_get_size(v_tail_1782_);
v___x_1785_ = lean_nat_dec_lt(v___x_1761_, v___x_1784_);
if (v___x_1785_ == 0)
{
return v___x_1783_;
}
else
{
size_t v___x_1786_; size_t v___x_1787_; lean_object* v___x_1788_; 
v___x_1786_ = ((size_t)0ULL);
v___x_1787_ = lean_usize_of_nat(v___x_1784_);
v___x_1788_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1757_, v_tail_1782_, v___x_1786_, v___x_1787_, v___x_1783_);
return v___x_1788_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0___boxed(lean_object* v___x_1789_, lean_object* v_t_1790_, lean_object* v_init_1791_, lean_object* v_start_1792_){
_start:
{
lean_object* v_res_1793_; 
v_res_1793_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(v___x_1789_, v_t_1790_, v_init_1791_, v_start_1792_);
lean_dec(v_start_1792_);
lean_dec_ref(v_t_1790_);
lean_dec_ref(v___x_1789_);
return v_res_1793_;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1794_ = lean_unsigned_to_nat(32u);
v___x_1795_ = lean_mk_empty_array_with_capacity(v___x_1794_);
v___x_1796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1795_);
return v___x_1796_;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1(void){
_start:
{
size_t v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1797_ = ((size_t)5ULL);
v___x_1798_ = lean_unsigned_to_nat(0u);
v___x_1799_ = lean_unsigned_to_nat(32u);
v___x_1800_ = lean_mk_empty_array_with_capacity(v___x_1799_);
v___x_1801_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0);
v___x_1802_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1802_, 0, v___x_1801_);
lean_ctor_set(v___x_1802_, 1, v___x_1800_);
lean_ctor_set(v___x_1802_, 2, v___x_1798_);
lean_ctor_set(v___x_1802_, 3, v___x_1798_);
lean_ctor_set_usize(v___x_1802_, 4, v___x_1797_);
return v___x_1802_;
}
}
lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(lean_object* v___x_1803_, lean_object* v_x_1804_, size_t v_x_1805_, size_t v_x_1806_){
_start:
{
if (lean_obj_tag(v_x_1804_) == 0)
{
lean_object* v_cs_1807_; size_t v_j_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; uint8_t v___x_1811_; 
v_cs_1807_ = lean_ctor_get(v_x_1804_, 0);
v_j_1808_ = lean_usize_shift_right(v_x_1805_, v_x_1806_);
v___x_1809_ = lean_usize_to_nat(v_j_1808_);
v___x_1810_ = lean_array_get_size(v_cs_1807_);
v___x_1811_ = lean_nat_dec_lt(v___x_1809_, v___x_1810_);
if (v___x_1811_ == 0)
{
lean_dec(v___x_1809_);
return v_x_1804_;
}
else
{
lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1829_; 
lean_inc_ref(v_cs_1807_);
v_isSharedCheck_1829_ = !lean_is_exclusive(v_x_1804_);
if (v_isSharedCheck_1829_ == 0)
{
lean_object* v_unused_1830_; 
v_unused_1830_ = lean_ctor_get(v_x_1804_, 0);
lean_dec(v_unused_1830_);
v___x_1813_ = v_x_1804_;
v_isShared_1814_ = v_isSharedCheck_1829_;
goto v_resetjp_1812_;
}
else
{
lean_dec(v_x_1804_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1829_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
size_t v___x_1815_; size_t v___x_1816_; size_t v___x_1817_; size_t v_i_1818_; size_t v___x_1819_; size_t v_shift_1820_; lean_object* v_v_1821_; lean_object* v___x_1822_; lean_object* v_xs_x27_1823_; lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1827_; 
v___x_1815_ = ((size_t)1ULL);
v___x_1816_ = lean_usize_shift_left(v___x_1815_, v_x_1806_);
v___x_1817_ = lean_usize_sub(v___x_1816_, v___x_1815_);
v_i_1818_ = lean_usize_land(v_x_1805_, v___x_1817_);
v___x_1819_ = ((size_t)5ULL);
v_shift_1820_ = lean_usize_sub(v_x_1806_, v___x_1819_);
v_v_1821_ = lean_array_fget(v_cs_1807_, v___x_1809_);
v___x_1822_ = lean_box(0);
v_xs_x27_1823_ = lean_array_fset(v_cs_1807_, v___x_1809_, v___x_1822_);
v___x_1824_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(v___x_1803_, v_v_1821_, v_i_1818_, v_shift_1820_);
v___x_1825_ = lean_array_fset(v_xs_x27_1823_, v___x_1809_, v___x_1824_);
lean_dec(v___x_1809_);
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 0, v___x_1825_);
v___x_1827_ = v___x_1813_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v___x_1825_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
}
else
{
lean_object* v_vs_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; uint8_t v___x_1834_; 
v_vs_1831_ = lean_ctor_get(v_x_1804_, 0);
v___x_1832_ = lean_usize_to_nat(v_x_1805_);
v___x_1833_ = lean_array_get_size(v_vs_1831_);
v___x_1834_ = lean_nat_dec_lt(v___x_1832_, v___x_1833_);
if (v___x_1834_ == 0)
{
lean_dec(v___x_1832_);
return v_x_1804_;
}
else
{
lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1848_; 
lean_inc_ref(v_vs_1831_);
v_isSharedCheck_1848_ = !lean_is_exclusive(v_x_1804_);
if (v_isSharedCheck_1848_ == 0)
{
lean_object* v_unused_1849_; 
v_unused_1849_ = lean_ctor_get(v_x_1804_, 0);
lean_dec(v_unused_1849_);
v___x_1836_ = v_x_1804_;
v_isShared_1837_ = v_isSharedCheck_1848_;
goto v_resetjp_1835_;
}
else
{
lean_dec(v_x_1804_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1848_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v_v_1838_; lean_object* v___x_1839_; lean_object* v_xs_x27_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1846_; 
v_v_1838_ = lean_array_fget(v_vs_1831_, v___x_1832_);
v___x_1839_ = lean_box(0);
v_xs_x27_1840_ = lean_array_fset(v_vs_1831_, v___x_1832_, v___x_1839_);
v___x_1841_ = lean_unsigned_to_nat(0u);
v___x_1842_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1);
v___x_1843_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(v___x_1803_, v_v_1838_, v___x_1842_, v___x_1841_);
lean_dec(v_v_1838_);
v___x_1844_ = lean_array_fset(v_xs_x27_1840_, v___x_1832_, v___x_1843_);
lean_dec(v___x_1832_);
if (v_isShared_1837_ == 0)
{
lean_ctor_set(v___x_1836_, 0, v___x_1844_);
v___x_1846_ = v___x_1836_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v___x_1844_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1803_ = stack[0].m_obj;
lean_object* v_x_1804_ = stack[1].m_obj;
size_t v_x_1805_ = stack[2].m_num;
size_t v_x_1806_ = stack[3].m_num;
lean_object* v_res_1850_;
v_res_1850_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(v___x_1803_, v_x_1804_, v_x_1805_, v_x_1806_);
stack->m_obj
 = v_res_1850_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___boxed(lean_object* v___x_1851_, lean_object* v_x_1852_, lean_object* v_x_1853_, lean_object* v_x_1854_){
_start:
{
size_t v_x_20763__boxed_1855_; size_t v_x_20764__boxed_1856_; lean_object* v_res_1857_; 
v_x_20763__boxed_1855_ = lean_unbox_usize(v_x_1853_);
lean_dec(v_x_1853_);
v_x_20764__boxed_1856_ = lean_unbox_usize(v_x_1854_);
lean_dec(v_x_1854_);
v_res_1857_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(v___x_1851_, v_x_1852_, v_x_20763__boxed_1855_, v_x_20764__boxed_1856_);
lean_dec_ref(v___x_1851_);
return v_res_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1(lean_object* v___x_1858_, lean_object* v_t_1859_, lean_object* v_i_1860_){
_start:
{
lean_object* v_root_1861_; lean_object* v_tail_1862_; lean_object* v_size_1863_; size_t v_shift_1864_; lean_object* v_tailOff_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1893_; 
v_root_1861_ = lean_ctor_get(v_t_1859_, 0);
v_tail_1862_ = lean_ctor_get(v_t_1859_, 1);
v_size_1863_ = lean_ctor_get(v_t_1859_, 2);
v_shift_1864_ = lean_ctor_get_usize(v_t_1859_, 4);
v_tailOff_1865_ = lean_ctor_get(v_t_1859_, 3);
v_isSharedCheck_1893_ = !lean_is_exclusive(v_t_1859_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1867_ = v_t_1859_;
v_isShared_1868_ = v_isSharedCheck_1893_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_tailOff_1865_);
lean_inc(v_size_1863_);
lean_inc(v_tail_1862_);
lean_inc(v_root_1861_);
lean_dec(v_t_1859_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1893_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
uint8_t v___x_1869_; 
v___x_1869_ = lean_nat_dec_le(v_tailOff_1865_, v_i_1860_);
if (v___x_1869_ == 0)
{
size_t v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1873_; 
v___x_1870_ = lean_usize_of_nat(v_i_1860_);
v___x_1871_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(v___x_1858_, v_root_1861_, v___x_1870_, v_shift_1864_);
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 0, v___x_1871_);
v___x_1873_ = v___x_1867_;
goto v_reusejp_1872_;
}
else
{
lean_object* v_reuseFailAlloc_1874_; 
v_reuseFailAlloc_1874_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_1874_, 0, v___x_1871_);
lean_ctor_set(v_reuseFailAlloc_1874_, 1, v_tail_1862_);
lean_ctor_set(v_reuseFailAlloc_1874_, 2, v_size_1863_);
lean_ctor_set(v_reuseFailAlloc_1874_, 3, v_tailOff_1865_);
lean_ctor_set_usize(v_reuseFailAlloc_1874_, 4, v_shift_1864_);
v___x_1873_ = v_reuseFailAlloc_1874_;
goto v_reusejp_1872_;
}
v_reusejp_1872_:
{
return v___x_1873_;
}
}
else
{
lean_object* v___x_1875_; lean_object* v___x_1876_; uint8_t v___x_1877_; 
v___x_1875_ = lean_nat_sub(v_i_1860_, v_tailOff_1865_);
v___x_1876_ = lean_array_get_size(v_tail_1862_);
v___x_1877_ = lean_nat_dec_lt(v___x_1875_, v___x_1876_);
if (v___x_1877_ == 0)
{
lean_object* v___x_1879_; 
lean_dec(v___x_1875_);
if (v_isShared_1868_ == 0)
{
v___x_1879_ = v___x_1867_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_root_1861_);
lean_ctor_set(v_reuseFailAlloc_1880_, 1, v_tail_1862_);
lean_ctor_set(v_reuseFailAlloc_1880_, 2, v_size_1863_);
lean_ctor_set(v_reuseFailAlloc_1880_, 3, v_tailOff_1865_);
lean_ctor_set_usize(v_reuseFailAlloc_1880_, 4, v_shift_1864_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
else
{
lean_object* v_v_1881_; lean_object* v___x_1882_; lean_object* v_xs_x27_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1891_; 
v_v_1881_ = lean_array_fget(v_tail_1862_, v___x_1875_);
v___x_1882_ = lean_box(0);
v_xs_x27_1883_ = lean_array_fset(v_tail_1862_, v___x_1875_, v___x_1882_);
v___x_1884_ = lean_unsigned_to_nat(32u);
v___x_1885_ = lean_mk_empty_array_with_capacity(v___x_1884_);
lean_dec_ref(v___x_1885_);
v___x_1886_ = lean_unsigned_to_nat(0u);
v___x_1887_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1);
v___x_1888_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(v___x_1858_, v_v_1881_, v___x_1887_, v___x_1886_);
lean_dec(v_v_1881_);
v___x_1889_ = lean_array_fset(v_xs_x27_1883_, v___x_1875_, v___x_1888_);
lean_dec(v___x_1875_);
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 1, v___x_1889_);
v___x_1891_ = v___x_1867_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_root_1861_);
lean_ctor_set(v_reuseFailAlloc_1892_, 1, v___x_1889_);
lean_ctor_set(v_reuseFailAlloc_1892_, 2, v_size_1863_);
lean_ctor_set(v_reuseFailAlloc_1892_, 3, v_tailOff_1865_);
lean_ctor_set_usize(v_reuseFailAlloc_1892_, 4, v_shift_1864_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1___boxed(lean_object* v___x_1894_, lean_object* v_t_1895_, lean_object* v_i_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1(v___x_1894_, v_t_1895_, v_i_1896_);
lean_dec(v_i_1896_);
lean_dec_ref(v___x_1894_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0(lean_object* v_p_1898_, lean_object* v_x_1899_, lean_object* v_s_1900_){
_start:
{
lean_object* v_vars_1901_; lean_object* v_varMap_1902_; lean_object* v_varsHistory_1903_; lean_object* v_natToIntMap_1904_; lean_object* v_natDef_1905_; lean_object* v_dvds_1906_; lean_object* v_lowers_1907_; lean_object* v_uppers_1908_; lean_object* v_diseqs_1909_; lean_object* v_elimEqs_1910_; lean_object* v_elimStack_1911_; lean_object* v_occurs_1912_; lean_object* v_assignment_1913_; lean_object* v_nextCnstrId_1914_; uint8_t v_caseSplits_1915_; lean_object* v_steps_1916_; lean_object* v_conflict_x3f_1917_; lean_object* v_diseqSplits_1918_; lean_object* v_divMod_1919_; uint8_t v_usedCommRing_1920_; lean_object* v_nonlinearOccs_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1929_; 
v_vars_1901_ = lean_ctor_get(v_s_1900_, 0);
v_varMap_1902_ = lean_ctor_get(v_s_1900_, 1);
v_varsHistory_1903_ = lean_ctor_get(v_s_1900_, 2);
v_natToIntMap_1904_ = lean_ctor_get(v_s_1900_, 3);
v_natDef_1905_ = lean_ctor_get(v_s_1900_, 4);
v_dvds_1906_ = lean_ctor_get(v_s_1900_, 5);
v_lowers_1907_ = lean_ctor_get(v_s_1900_, 6);
v_uppers_1908_ = lean_ctor_get(v_s_1900_, 7);
v_diseqs_1909_ = lean_ctor_get(v_s_1900_, 8);
v_elimEqs_1910_ = lean_ctor_get(v_s_1900_, 9);
v_elimStack_1911_ = lean_ctor_get(v_s_1900_, 10);
v_occurs_1912_ = lean_ctor_get(v_s_1900_, 11);
v_assignment_1913_ = lean_ctor_get(v_s_1900_, 12);
v_nextCnstrId_1914_ = lean_ctor_get(v_s_1900_, 13);
v_caseSplits_1915_ = lean_ctor_get_uint8(v_s_1900_, sizeof(void*)*19);
v_steps_1916_ = lean_ctor_get(v_s_1900_, 14);
v_conflict_x3f_1917_ = lean_ctor_get(v_s_1900_, 15);
v_diseqSplits_1918_ = lean_ctor_get(v_s_1900_, 16);
v_divMod_1919_ = lean_ctor_get(v_s_1900_, 17);
v_usedCommRing_1920_ = lean_ctor_get_uint8(v_s_1900_, sizeof(void*)*19 + 1);
v_nonlinearOccs_1921_ = lean_ctor_get(v_s_1900_, 18);
v_isSharedCheck_1929_ = !lean_is_exclusive(v_s_1900_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1923_ = v_s_1900_;
v_isShared_1924_ = v_isSharedCheck_1929_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_nonlinearOccs_1921_);
lean_inc(v_divMod_1919_);
lean_inc(v_diseqSplits_1918_);
lean_inc(v_conflict_x3f_1917_);
lean_inc(v_steps_1916_);
lean_inc(v_nextCnstrId_1914_);
lean_inc(v_assignment_1913_);
lean_inc(v_occurs_1912_);
lean_inc(v_elimStack_1911_);
lean_inc(v_elimEqs_1910_);
lean_inc(v_diseqs_1909_);
lean_inc(v_uppers_1908_);
lean_inc(v_lowers_1907_);
lean_inc(v_dvds_1906_);
lean_inc(v_natDef_1905_);
lean_inc(v_natToIntMap_1904_);
lean_inc(v_varsHistory_1903_);
lean_inc(v_varMap_1902_);
lean_inc(v_vars_1901_);
lean_dec(v_s_1900_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1929_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1925_; lean_object* v___x_1927_; 
v___x_1925_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1(v_p_1898_, v_diseqs_1909_, v_x_1899_);
if (v_isShared_1924_ == 0)
{
lean_ctor_set(v___x_1923_, 8, v___x_1925_);
v___x_1927_ = v___x_1923_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_vars_1901_);
lean_ctor_set(v_reuseFailAlloc_1928_, 1, v_varMap_1902_);
lean_ctor_set(v_reuseFailAlloc_1928_, 2, v_varsHistory_1903_);
lean_ctor_set(v_reuseFailAlloc_1928_, 3, v_natToIntMap_1904_);
lean_ctor_set(v_reuseFailAlloc_1928_, 4, v_natDef_1905_);
lean_ctor_set(v_reuseFailAlloc_1928_, 5, v_dvds_1906_);
lean_ctor_set(v_reuseFailAlloc_1928_, 6, v_lowers_1907_);
lean_ctor_set(v_reuseFailAlloc_1928_, 7, v_uppers_1908_);
lean_ctor_set(v_reuseFailAlloc_1928_, 8, v___x_1925_);
lean_ctor_set(v_reuseFailAlloc_1928_, 9, v_elimEqs_1910_);
lean_ctor_set(v_reuseFailAlloc_1928_, 10, v_elimStack_1911_);
lean_ctor_set(v_reuseFailAlloc_1928_, 11, v_occurs_1912_);
lean_ctor_set(v_reuseFailAlloc_1928_, 12, v_assignment_1913_);
lean_ctor_set(v_reuseFailAlloc_1928_, 13, v_nextCnstrId_1914_);
lean_ctor_set(v_reuseFailAlloc_1928_, 14, v_steps_1916_);
lean_ctor_set(v_reuseFailAlloc_1928_, 15, v_conflict_x3f_1917_);
lean_ctor_set(v_reuseFailAlloc_1928_, 16, v_diseqSplits_1918_);
lean_ctor_set(v_reuseFailAlloc_1928_, 17, v_divMod_1919_);
lean_ctor_set(v_reuseFailAlloc_1928_, 18, v_nonlinearOccs_1921_);
lean_ctor_set_uint8(v_reuseFailAlloc_1928_, sizeof(void*)*19, v_caseSplits_1915_);
lean_ctor_set_uint8(v_reuseFailAlloc_1928_, sizeof(void*)*19 + 1, v_usedCommRing_1920_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed(lean_object* v_p_1930_, lean_object* v_x_1931_, lean_object* v_s_1932_){
_start:
{
lean_object* v_res_1933_; 
v_res_1933_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0(v_p_1930_, v_x_1931_, v_s_1932_);
lean_dec(v_x_1931_);
lean_dec_ref(v_p_1930_);
return v_res_1933_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1940_ = lean_unsigned_to_nat(1u);
v___x_1941_ = lean_nat_to_int(v___x_1940_);
return v___x_1941_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(lean_object* v_c_1942_, lean_object* v_x_1943_, lean_object* v_as_1944_, size_t v_sz_1945_, size_t v_i_1946_, lean_object* v_b_1947_, lean_object* v___y_1948_){
_start:
{
uint8_t v___x_1950_; 
v___x_1950_ = lean_usize_dec_lt(v_i_1946_, v_sz_1945_);
if (v___x_1950_ == 0)
{
lean_object* v___x_1951_; 
lean_dec(v_x_1943_);
lean_dec_ref(v_c_1942_);
v___x_1951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1951_, 0, v_b_1947_);
return v___x_1951_;
}
else
{
lean_object* v_snd_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1998_; 
v_snd_1952_ = lean_ctor_get(v_b_1947_, 1);
v_isSharedCheck_1998_ = !lean_is_exclusive(v_b_1947_);
if (v_isSharedCheck_1998_ == 0)
{
lean_object* v_unused_1999_; 
v_unused_1999_ = lean_ctor_get(v_b_1947_, 0);
lean_dec(v_unused_1999_);
v___x_1954_ = v_b_1947_;
v_isShared_1955_ = v_isSharedCheck_1998_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_snd_1952_);
lean_dec(v_b_1947_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1998_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v_p_1956_; lean_object* v_a_1957_; lean_object* v_p_1958_; lean_object* v___x_1959_; lean_object* v___f_1960_; uint8_t v___y_1962_; uint8_t v___x_1996_; 
v_p_1956_ = lean_ctor_get(v_c_1942_, 0);
v_a_1957_ = lean_array_uget_borrowed(v_as_1944_, v_i_1946_);
v_p_1958_ = lean_ctor_get(v_a_1957_, 0);
v___x_1959_ = lean_box(0);
lean_inc(v_x_1943_);
lean_inc_ref(v_p_1958_);
v___f_1960_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1960_, 0, v_p_1958_);
lean_closure_set(v___f_1960_, 1, v_x_1943_);
v___x_1996_ = l_Int_Internal_Linear_instBEqPoly_beq(v_p_1956_, v_p_1958_);
if (v___x_1996_ == 0)
{
uint8_t v___x_1997_; 
v___x_1997_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_1956_, v_p_1958_);
v___y_1962_ = v___x_1997_;
goto v___jp_1961_;
}
else
{
v___y_1962_ = v___x_1996_;
goto v___jp_1961_;
}
v___jp_1961_:
{
if (v___y_1962_ == 0)
{
lean_object* v___x_1963_; size_t v___x_1964_; size_t v___x_1965_; 
lean_dec_ref(v___f_1960_);
lean_del_object(v___x_1954_);
lean_dec(v_snd_1952_);
v___x_1963_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__1));
v___x_1964_ = ((size_t)1ULL);
v___x_1965_ = lean_usize_add(v_i_1946_, v___x_1964_);
v_i_1946_ = v___x_1965_;
v_b_1947_ = v___x_1963_;
goto _start;
}
else
{
lean_object* v___x_1967_; lean_object* v___x_1968_; 
lean_dec(v_x_1943_);
v___x_1967_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_1968_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1967_, v___f_1960_, v___y_1948_);
if (lean_obj_tag(v___x_1968_) == 0)
{
lean_object* v___x_1970_; uint8_t v_isShared_1971_; uint8_t v_isSharedCheck_1986_; 
v_isSharedCheck_1986_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1986_ == 0)
{
lean_object* v_unused_1987_; 
v_unused_1987_ = lean_ctor_get(v___x_1968_, 0);
lean_dec(v_unused_1987_);
v___x_1970_ = v___x_1968_;
v_isShared_1971_ = v_isSharedCheck_1986_;
goto v_resetjp_1969_;
}
else
{
lean_dec(v___x_1968_);
v___x_1970_ = lean_box(0);
v_isShared_1971_ = v_isSharedCheck_1986_;
goto v_resetjp_1969_;
}
v_resetjp_1969_:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1979_; 
v___x_1972_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
lean_inc_ref(v_p_1956_);
v___x_1973_ = l_Int_Internal_Linear_Poly_addConst(v_p_1956_, v___x_1972_);
lean_inc(v_a_1957_);
v___x_1974_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_1974_, 0, v_c_1942_);
lean_ctor_set(v___x_1974_, 1, v_a_1957_);
v___x_1975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1973_);
lean_ctor_set(v___x_1975_, 1, v___x_1974_);
v___x_1976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1975_);
v___x_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1976_);
if (v_isShared_1955_ == 0)
{
lean_ctor_set(v___x_1954_, 1, v___x_1959_);
lean_ctor_set(v___x_1954_, 0, v___x_1977_);
v___x_1979_ = v___x_1954_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1985_; 
v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1985_, 0, v___x_1977_);
lean_ctor_set(v_reuseFailAlloc_1985_, 1, v___x_1959_);
v___x_1979_ = v_reuseFailAlloc_1985_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1983_; 
v___x_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1979_);
v___x_1981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1980_);
lean_ctor_set(v___x_1981_, 1, v_snd_1952_);
if (v_isShared_1971_ == 0)
{
lean_ctor_set(v___x_1970_, 0, v___x_1981_);
v___x_1983_ = v___x_1970_;
goto v_reusejp_1982_;
}
else
{
lean_object* v_reuseFailAlloc_1984_; 
v_reuseFailAlloc_1984_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
lean_del_object(v___x_1954_);
lean_dec(v_snd_1952_);
lean_dec_ref(v_c_1942_);
v_a_1988_ = lean_ctor_get(v___x_1968_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1968_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___x_1968_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1968_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_a_1988_);
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
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_1942_ = stack[0].m_obj;
lean_object* v_x_1943_ = stack[1].m_obj;
lean_object* v_as_1944_ = stack[2].m_obj;
size_t v_sz_1945_ = stack[3].m_num;
size_t v_i_1946_ = stack[4].m_num;
lean_object* v_b_1947_ = stack[5].m_obj;
lean_object* v___y_1948_ = stack[6].m_obj;
lean_object* v_res_2000_;
v_res_2000_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(v_c_1942_, v_x_1943_, v_as_1944_, v_sz_1945_, v_i_1946_, v_b_1947_, v___y_1948_);
stack->m_obj
 = v_res_2000_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___boxed(lean_object* v_c_2001_, lean_object* v_x_2002_, lean_object* v_as_2003_, lean_object* v_sz_2004_, lean_object* v_i_2005_, lean_object* v_b_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_){
_start:
{
size_t v_sz_boxed_2009_; size_t v_i_boxed_2010_; lean_object* v_res_2011_; 
v_sz_boxed_2009_ = lean_unbox_usize(v_sz_2004_);
lean_dec(v_sz_2004_);
v_i_boxed_2010_ = lean_unbox_usize(v_i_2005_);
lean_dec(v_i_2005_);
v_res_2011_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(v_c_2001_, v_x_2002_, v_as_2003_, v_sz_boxed_2009_, v_i_boxed_2010_, v_b_2006_, v___y_2007_);
lean_dec(v___y_2007_);
lean_dec_ref(v_as_2003_);
return v_res_2011_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7(lean_object* v_c_2018_, lean_object* v_x_2019_, lean_object* v_as_2020_, size_t v_sz_2021_, size_t v_i_2022_, lean_object* v_b_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_){
_start:
{
uint8_t v___x_2035_; 
v___x_2035_ = lean_usize_dec_lt(v_i_2022_, v_sz_2021_);
if (v___x_2035_ == 0)
{
lean_object* v___x_2036_; 
lean_dec(v_x_2019_);
lean_dec_ref(v_c_2018_);
v___x_2036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2036_, 0, v_b_2023_);
return v___x_2036_;
}
else
{
lean_object* v_snd_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2083_; 
v_snd_2037_ = lean_ctor_get(v_b_2023_, 1);
v_isSharedCheck_2083_ = !lean_is_exclusive(v_b_2023_);
if (v_isSharedCheck_2083_ == 0)
{
lean_object* v_unused_2084_; 
v_unused_2084_ = lean_ctor_get(v_b_2023_, 0);
lean_dec(v_unused_2084_);
v___x_2039_ = v_b_2023_;
v_isShared_2040_ = v_isSharedCheck_2083_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_snd_2037_);
lean_dec(v_b_2023_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2083_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v_p_2041_; lean_object* v_a_2042_; lean_object* v_p_2043_; lean_object* v___x_2044_; lean_object* v___f_2045_; uint8_t v___y_2047_; uint8_t v___x_2081_; 
v_p_2041_ = lean_ctor_get(v_c_2018_, 0);
v_a_2042_ = lean_array_uget_borrowed(v_as_2020_, v_i_2022_);
v_p_2043_ = lean_ctor_get(v_a_2042_, 0);
v___x_2044_ = lean_box(0);
lean_inc(v_x_2019_);
lean_inc_ref(v_p_2043_);
v___f_2045_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2045_, 0, v_p_2043_);
lean_closure_set(v___f_2045_, 1, v_x_2019_);
v___x_2081_ = l_Int_Internal_Linear_instBEqPoly_beq(v_p_2041_, v_p_2043_);
if (v___x_2081_ == 0)
{
uint8_t v___x_2082_; 
v___x_2082_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_2041_, v_p_2043_);
v___y_2047_ = v___x_2082_;
goto v___jp_2046_;
}
else
{
v___y_2047_ = v___x_2081_;
goto v___jp_2046_;
}
v___jp_2046_:
{
if (v___y_2047_ == 0)
{
lean_object* v___x_2048_; size_t v___x_2049_; size_t v___x_2050_; lean_object* v___x_2051_; 
lean_dec_ref(v___f_2045_);
lean_del_object(v___x_2039_);
lean_dec(v_snd_2037_);
v___x_2048_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___closed__1));
v___x_2049_ = ((size_t)1ULL);
v___x_2050_ = lean_usize_add(v_i_2022_, v___x_2049_);
v___x_2051_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(v_c_2018_, v_x_2019_, v_as_2020_, v_sz_2021_, v___x_2050_, v___x_2048_, v___y_2024_);
return v___x_2051_;
}
else
{
lean_object* v___x_2052_; lean_object* v___x_2053_; 
lean_dec(v_x_2019_);
v___x_2052_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2053_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2052_, v___f_2045_, v___y_2024_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2071_; 
v_isSharedCheck_2071_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2071_ == 0)
{
lean_object* v_unused_2072_; 
v_unused_2072_ = lean_ctor_get(v___x_2053_, 0);
lean_dec(v_unused_2072_);
v___x_2055_ = v___x_2053_;
v_isShared_2056_ = v_isSharedCheck_2071_;
goto v_resetjp_2054_;
}
else
{
lean_dec(v___x_2053_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2071_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2064_; 
v___x_2057_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
lean_inc_ref(v_p_2041_);
v___x_2058_ = l_Int_Internal_Linear_Poly_addConst(v_p_2041_, v___x_2057_);
lean_inc(v_a_2042_);
v___x_2059_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_2059_, 0, v_c_2018_);
lean_ctor_set(v___x_2059_, 1, v_a_2042_);
v___x_2060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2060_, 0, v___x_2058_);
lean_ctor_set(v___x_2060_, 1, v___x_2059_);
v___x_2061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2061_, 0, v___x_2060_);
v___x_2062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2062_, 0, v___x_2061_);
if (v_isShared_2040_ == 0)
{
lean_ctor_set(v___x_2039_, 1, v___x_2044_);
lean_ctor_set(v___x_2039_, 0, v___x_2062_);
v___x_2064_ = v___x_2039_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v___x_2062_);
lean_ctor_set(v_reuseFailAlloc_2070_, 1, v___x_2044_);
v___x_2064_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2068_; 
v___x_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2064_);
v___x_2066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2065_);
lean_ctor_set(v___x_2066_, 1, v_snd_2037_);
if (v_isShared_2056_ == 0)
{
lean_ctor_set(v___x_2055_, 0, v___x_2066_);
v___x_2068_ = v___x_2055_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_2066_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
}
else
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2080_; 
lean_del_object(v___x_2039_);
lean_dec(v_snd_2037_);
lean_dec_ref(v_c_2018_);
v_a_2073_ = lean_ctor_get(v___x_2053_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2053_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2075_ = v___x_2053_;
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2053_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2078_; 
if (v_isShared_2076_ == 0)
{
v___x_2078_ = v___x_2075_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_a_2073_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_2018_ = stack[0].m_obj;
lean_object* v_x_2019_ = stack[1].m_obj;
lean_object* v_as_2020_ = stack[2].m_obj;
size_t v_sz_2021_ = stack[3].m_num;
size_t v_i_2022_ = stack[4].m_num;
lean_object* v_b_2023_ = stack[5].m_obj;
lean_object* v___y_2024_ = stack[6].m_obj;
lean_object* v___y_2025_ = stack[7].m_obj;
lean_object* v___y_2026_ = stack[8].m_obj;
lean_object* v___y_2027_ = stack[9].m_obj;
lean_object* v___y_2028_ = stack[10].m_obj;
lean_object* v___y_2029_ = stack[11].m_obj;
lean_object* v___y_2030_ = stack[12].m_obj;
lean_object* v___y_2031_ = stack[13].m_obj;
lean_object* v___y_2032_ = stack[14].m_obj;
lean_object* v___y_2033_ = stack[15].m_obj;
lean_object* v_res_2085_;
v_res_2085_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7(v_c_2018_, v_x_2019_, v_as_2020_, v_sz_2021_, v_i_2022_, v_b_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
stack->m_obj
 = v_res_2085_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___boxed(lean_object** _args){
lean_object* v_c_2086_ = _args[0];
lean_object* v_x_2087_ = _args[1];
lean_object* v_as_2088_ = _args[2];
lean_object* v_sz_2089_ = _args[3];
lean_object* v_i_2090_ = _args[4];
lean_object* v_b_2091_ = _args[5];
lean_object* v___y_2092_ = _args[6];
lean_object* v___y_2093_ = _args[7];
lean_object* v___y_2094_ = _args[8];
lean_object* v___y_2095_ = _args[9];
lean_object* v___y_2096_ = _args[10];
lean_object* v___y_2097_ = _args[11];
lean_object* v___y_2098_ = _args[12];
lean_object* v___y_2099_ = _args[13];
lean_object* v___y_2100_ = _args[14];
lean_object* v___y_2101_ = _args[15];
lean_object* v___y_2102_ = _args[16];
_start:
{
size_t v_sz_boxed_2103_; size_t v_i_boxed_2104_; lean_object* v_res_2105_; 
v_sz_boxed_2103_ = lean_unbox_usize(v_sz_2089_);
lean_dec(v_sz_2089_);
v_i_boxed_2104_ = lean_unbox_usize(v_i_2090_);
lean_dec(v_i_2090_);
v_res_2105_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7(v_c_2086_, v_x_2087_, v_as_2088_, v_sz_boxed_2103_, v_i_boxed_2104_, v_b_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_);
lean_dec(v___y_2101_);
lean_dec_ref(v___y_2100_);
lean_dec(v___y_2099_);
lean_dec_ref(v___y_2098_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
lean_dec(v___y_2093_);
lean_dec(v___y_2092_);
lean_dec_ref(v_as_2088_);
return v_res_2105_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(lean_object* v_c_2112_, lean_object* v_x_2113_, lean_object* v_as_2114_, size_t v_sz_2115_, size_t v_i_2116_, lean_object* v_b_2117_, lean_object* v___y_2118_){
_start:
{
uint8_t v___x_2120_; 
v___x_2120_ = lean_usize_dec_lt(v_i_2116_, v_sz_2115_);
if (v___x_2120_ == 0)
{
lean_object* v___x_2121_; 
lean_dec(v_x_2113_);
lean_dec_ref(v_c_2112_);
v___x_2121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2121_, 0, v_b_2117_);
return v___x_2121_;
}
else
{
lean_object* v_snd_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2169_; 
v_snd_2122_ = lean_ctor_get(v_b_2117_, 1);
v_isSharedCheck_2169_ = !lean_is_exclusive(v_b_2117_);
if (v_isSharedCheck_2169_ == 0)
{
lean_object* v_unused_2170_; 
v_unused_2170_ = lean_ctor_get(v_b_2117_, 0);
lean_dec(v_unused_2170_);
v___x_2124_ = v_b_2117_;
v_isShared_2125_ = v_isSharedCheck_2169_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_snd_2122_);
lean_dec(v_b_2117_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2169_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v_p_2126_; lean_object* v_a_2127_; lean_object* v_p_2128_; lean_object* v___x_2129_; lean_object* v___f_2130_; uint8_t v___y_2132_; uint8_t v___x_2167_; 
v_p_2126_ = lean_ctor_get(v_c_2112_, 0);
v_a_2127_ = lean_array_uget_borrowed(v_as_2114_, v_i_2116_);
v_p_2128_ = lean_ctor_get(v_a_2127_, 0);
v___x_2129_ = lean_box(0);
lean_inc(v_x_2113_);
lean_inc_ref(v_p_2128_);
v___f_2130_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2130_, 0, v_p_2128_);
lean_closure_set(v___f_2130_, 1, v_x_2113_);
v___x_2167_ = l_Int_Internal_Linear_instBEqPoly_beq(v_p_2126_, v_p_2128_);
if (v___x_2167_ == 0)
{
uint8_t v___x_2168_; 
v___x_2168_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_2126_, v_p_2128_);
v___y_2132_ = v___x_2168_;
goto v___jp_2131_;
}
else
{
v___y_2132_ = v___x_2167_;
goto v___jp_2131_;
}
v___jp_2131_:
{
if (v___y_2132_ == 0)
{
lean_object* v___x_2133_; size_t v___x_2134_; size_t v___x_2135_; 
lean_dec_ref(v___f_2130_);
lean_del_object(v___x_2124_);
lean_dec(v_snd_2122_);
v___x_2133_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg___closed__1));
v___x_2134_ = ((size_t)1ULL);
v___x_2135_ = lean_usize_add(v_i_2116_, v___x_2134_);
v_i_2116_ = v___x_2135_;
v_b_2117_ = v___x_2133_;
goto _start;
}
else
{
lean_object* v___x_2137_; lean_object* v___x_2138_; 
lean_dec(v_x_2113_);
v___x_2137_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2138_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2137_, v___f_2130_, v___y_2118_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2157_; 
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2157_ == 0)
{
lean_object* v_unused_2158_; 
v_unused_2158_ = lean_ctor_get(v___x_2138_, 0);
lean_dec(v_unused_2158_);
v___x_2140_ = v___x_2138_;
v_isShared_2141_ = v_isSharedCheck_2157_;
goto v_resetjp_2139_;
}
else
{
lean_dec(v___x_2138_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2157_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2149_; 
v___x_2142_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
lean_inc_ref(v_p_2126_);
v___x_2143_ = l_Int_Internal_Linear_Poly_addConst(v_p_2126_, v___x_2142_);
lean_inc(v_a_2127_);
v___x_2144_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_2144_, 0, v_c_2112_);
lean_ctor_set(v___x_2144_, 1, v_a_2127_);
v___x_2145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2143_);
lean_ctor_set(v___x_2145_, 1, v___x_2144_);
v___x_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2146_, 0, v___x_2145_);
v___x_2147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2146_);
if (v_isShared_2125_ == 0)
{
lean_ctor_set(v___x_2124_, 1, v___x_2129_);
lean_ctor_set(v___x_2124_, 0, v___x_2147_);
v___x_2149_ = v___x_2124_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v___x_2147_);
lean_ctor_set(v_reuseFailAlloc_2156_, 1, v___x_2129_);
v___x_2149_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2154_; 
v___x_2150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2149_);
v___x_2151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2150_);
v___x_2152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2151_);
lean_ctor_set(v___x_2152_, 1, v_snd_2122_);
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 0, v___x_2152_);
v___x_2154_ = v___x_2140_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v___x_2152_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
}
}
else
{
lean_object* v_a_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2166_; 
lean_del_object(v___x_2124_);
lean_dec(v_snd_2122_);
lean_dec_ref(v_c_2112_);
v_a_2159_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2161_ = v___x_2138_;
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_a_2159_);
lean_dec(v___x_2138_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2164_; 
if (v_isShared_2162_ == 0)
{
v___x_2164_ = v___x_2161_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_a_2159_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_2112_ = stack[0].m_obj;
lean_object* v_x_2113_ = stack[1].m_obj;
lean_object* v_as_2114_ = stack[2].m_obj;
size_t v_sz_2115_ = stack[3].m_num;
size_t v_i_2116_ = stack[4].m_num;
lean_object* v_b_2117_ = stack[5].m_obj;
lean_object* v___y_2118_ = stack[6].m_obj;
lean_object* v_res_2171_;
v_res_2171_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(v_c_2112_, v_x_2113_, v_as_2114_, v_sz_2115_, v_i_2116_, v_b_2117_, v___y_2118_);
stack->m_obj
 = v_res_2171_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg___boxed(lean_object* v_c_2172_, lean_object* v_x_2173_, lean_object* v_as_2174_, lean_object* v_sz_2175_, lean_object* v_i_2176_, lean_object* v_b_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_){
_start:
{
size_t v_sz_boxed_2180_; size_t v_i_boxed_2181_; lean_object* v_res_2182_; 
v_sz_boxed_2180_ = lean_unbox_usize(v_sz_2175_);
lean_dec(v_sz_2175_);
v_i_boxed_2181_ = lean_unbox_usize(v_i_2176_);
lean_dec(v_i_2176_);
v_res_2182_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(v_c_2172_, v_x_2173_, v_as_2174_, v_sz_boxed_2180_, v_i_boxed_2181_, v_b_2177_, v___y_2178_);
lean_dec(v___y_2178_);
lean_dec_ref(v_as_2174_);
return v_res_2182_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9(lean_object* v_c_2186_, lean_object* v_x_2187_, lean_object* v_as_2188_, size_t v_sz_2189_, size_t v_i_2190_, lean_object* v_b_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_){
_start:
{
uint8_t v___x_2203_; 
v___x_2203_ = lean_usize_dec_lt(v_i_2190_, v_sz_2189_);
if (v___x_2203_ == 0)
{
lean_object* v___x_2204_; 
lean_dec(v_x_2187_);
lean_dec_ref(v_c_2186_);
v___x_2204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2204_, 0, v_b_2191_);
return v___x_2204_;
}
else
{
lean_object* v_snd_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2252_; 
v_snd_2205_ = lean_ctor_get(v_b_2191_, 1);
v_isSharedCheck_2252_ = !lean_is_exclusive(v_b_2191_);
if (v_isSharedCheck_2252_ == 0)
{
lean_object* v_unused_2253_; 
v_unused_2253_ = lean_ctor_get(v_b_2191_, 0);
lean_dec(v_unused_2253_);
v___x_2207_ = v_b_2191_;
v_isShared_2208_ = v_isSharedCheck_2252_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_snd_2205_);
lean_dec(v_b_2191_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2252_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v_p_2209_; lean_object* v_a_2210_; lean_object* v_p_2211_; lean_object* v___x_2212_; lean_object* v___f_2213_; uint8_t v___y_2215_; uint8_t v___x_2250_; 
v_p_2209_ = lean_ctor_get(v_c_2186_, 0);
v_a_2210_ = lean_array_uget_borrowed(v_as_2188_, v_i_2190_);
v_p_2211_ = lean_ctor_get(v_a_2210_, 0);
v___x_2212_ = lean_box(0);
lean_inc(v_x_2187_);
lean_inc_ref(v_p_2211_);
v___f_2213_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2213_, 0, v_p_2211_);
lean_closure_set(v___f_2213_, 1, v_x_2187_);
v___x_2250_ = l_Int_Internal_Linear_instBEqPoly_beq(v_p_2209_, v_p_2211_);
if (v___x_2250_ == 0)
{
uint8_t v___x_2251_; 
v___x_2251_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_2209_, v_p_2211_);
v___y_2215_ = v___x_2251_;
goto v___jp_2214_;
}
else
{
v___y_2215_ = v___x_2250_;
goto v___jp_2214_;
}
v___jp_2214_:
{
if (v___y_2215_ == 0)
{
lean_object* v___x_2216_; size_t v___x_2217_; size_t v___x_2218_; lean_object* v___x_2219_; 
lean_dec_ref(v___f_2213_);
lean_del_object(v___x_2207_);
lean_dec(v_snd_2205_);
v___x_2216_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9___closed__0));
v___x_2217_ = ((size_t)1ULL);
v___x_2218_ = lean_usize_add(v_i_2190_, v___x_2217_);
v___x_2219_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(v_c_2186_, v_x_2187_, v_as_2188_, v_sz_2189_, v___x_2218_, v___x_2216_, v___y_2192_);
return v___x_2219_;
}
else
{
lean_object* v___x_2220_; lean_object* v___x_2221_; 
lean_dec(v_x_2187_);
v___x_2220_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2221_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2220_, v___f_2213_, v___y_2192_);
if (lean_obj_tag(v___x_2221_) == 0)
{
lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2240_; 
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2240_ == 0)
{
lean_object* v_unused_2241_; 
v_unused_2241_ = lean_ctor_get(v___x_2221_, 0);
lean_dec(v_unused_2241_);
v___x_2223_ = v___x_2221_;
v_isShared_2224_ = v_isSharedCheck_2240_;
goto v_resetjp_2222_;
}
else
{
lean_dec(v___x_2221_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2240_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2232_; 
v___x_2225_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
lean_inc_ref(v_p_2209_);
v___x_2226_ = l_Int_Internal_Linear_Poly_addConst(v_p_2209_, v___x_2225_);
lean_inc(v_a_2210_);
v___x_2227_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_2227_, 0, v_c_2186_);
lean_ctor_set(v___x_2227_, 1, v_a_2210_);
v___x_2228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2226_);
lean_ctor_set(v___x_2228_, 1, v___x_2227_);
v___x_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2229_, 0, v___x_2228_);
v___x_2230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2229_);
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 1, v___x_2212_);
lean_ctor_set(v___x_2207_, 0, v___x_2230_);
v___x_2232_ = v___x_2207_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2239_; 
v_reuseFailAlloc_2239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2239_, 0, v___x_2230_);
lean_ctor_set(v_reuseFailAlloc_2239_, 1, v___x_2212_);
v___x_2232_ = v_reuseFailAlloc_2239_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2237_; 
v___x_2233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2233_, 0, v___x_2232_);
v___x_2234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2233_);
v___x_2235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2235_, 0, v___x_2234_);
lean_ctor_set(v___x_2235_, 1, v_snd_2205_);
if (v_isShared_2224_ == 0)
{
lean_ctor_set(v___x_2223_, 0, v___x_2235_);
v___x_2237_ = v___x_2223_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v___x_2235_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
}
else
{
lean_object* v_a_2242_; lean_object* v___x_2244_; uint8_t v_isShared_2245_; uint8_t v_isSharedCheck_2249_; 
lean_del_object(v___x_2207_);
lean_dec(v_snd_2205_);
lean_dec_ref(v_c_2186_);
v_a_2242_ = lean_ctor_get(v___x_2221_, 0);
v_isSharedCheck_2249_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2249_ == 0)
{
v___x_2244_ = v___x_2221_;
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
else
{
lean_inc(v_a_2242_);
lean_dec(v___x_2221_);
v___x_2244_ = lean_box(0);
v_isShared_2245_ = v_isSharedCheck_2249_;
goto v_resetjp_2243_;
}
v_resetjp_2243_:
{
lean_object* v___x_2247_; 
if (v_isShared_2245_ == 0)
{
v___x_2247_ = v___x_2244_;
goto v_reusejp_2246_;
}
else
{
lean_object* v_reuseFailAlloc_2248_; 
v_reuseFailAlloc_2248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_a_2242_);
v___x_2247_ = v_reuseFailAlloc_2248_;
goto v_reusejp_2246_;
}
v_reusejp_2246_:
{
return v___x_2247_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_2186_ = stack[0].m_obj;
lean_object* v_x_2187_ = stack[1].m_obj;
lean_object* v_as_2188_ = stack[2].m_obj;
size_t v_sz_2189_ = stack[3].m_num;
size_t v_i_2190_ = stack[4].m_num;
lean_object* v_b_2191_ = stack[5].m_obj;
lean_object* v___y_2192_ = stack[6].m_obj;
lean_object* v___y_2193_ = stack[7].m_obj;
lean_object* v___y_2194_ = stack[8].m_obj;
lean_object* v___y_2195_ = stack[9].m_obj;
lean_object* v___y_2196_ = stack[10].m_obj;
lean_object* v___y_2197_ = stack[11].m_obj;
lean_object* v___y_2198_ = stack[12].m_obj;
lean_object* v___y_2199_ = stack[13].m_obj;
lean_object* v___y_2200_ = stack[14].m_obj;
lean_object* v___y_2201_ = stack[15].m_obj;
lean_object* v_res_2254_;
v_res_2254_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9(v_c_2186_, v_x_2187_, v_as_2188_, v_sz_2189_, v_i_2190_, v_b_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_);
stack->m_obj
 = v_res_2254_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9___boxed(lean_object** _args){
lean_object* v_c_2255_ = _args[0];
lean_object* v_x_2256_ = _args[1];
lean_object* v_as_2257_ = _args[2];
lean_object* v_sz_2258_ = _args[3];
lean_object* v_i_2259_ = _args[4];
lean_object* v_b_2260_ = _args[5];
lean_object* v___y_2261_ = _args[6];
lean_object* v___y_2262_ = _args[7];
lean_object* v___y_2263_ = _args[8];
lean_object* v___y_2264_ = _args[9];
lean_object* v___y_2265_ = _args[10];
lean_object* v___y_2266_ = _args[11];
lean_object* v___y_2267_ = _args[12];
lean_object* v___y_2268_ = _args[13];
lean_object* v___y_2269_ = _args[14];
lean_object* v___y_2270_ = _args[15];
lean_object* v___y_2271_ = _args[16];
_start:
{
size_t v_sz_boxed_2272_; size_t v_i_boxed_2273_; lean_object* v_res_2274_; 
v_sz_boxed_2272_ = lean_unbox_usize(v_sz_2258_);
lean_dec(v_sz_2258_);
v_i_boxed_2273_ = lean_unbox_usize(v_i_2259_);
lean_dec(v_i_2259_);
v_res_2274_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9(v_c_2255_, v_x_2256_, v_as_2257_, v_sz_boxed_2272_, v_i_boxed_2273_, v_b_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec(v___y_2261_);
lean_dec_ref(v_as_2257_);
return v_res_2274_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(lean_object* v_init_2275_, lean_object* v_c_2276_, lean_object* v_x_2277_, lean_object* v_n_2278_, lean_object* v_b_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_){
_start:
{
if (lean_obj_tag(v_n_2278_) == 0)
{
lean_object* v_cs_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; size_t v_sz_2294_; size_t v___x_2295_; lean_object* v___x_2296_; 
v_cs_2291_ = lean_ctor_get(v_n_2278_, 0);
v___x_2292_ = lean_box(0);
v___x_2293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2292_);
lean_ctor_set(v___x_2293_, 1, v_b_2279_);
v_sz_2294_ = lean_array_size(v_cs_2291_);
v___x_2295_ = ((size_t)0ULL);
v___x_2296_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8(v_init_2275_, v_c_2276_, v_x_2277_, v_cs_2291_, v_sz_2294_, v___x_2295_, v___x_2293_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
if (lean_obj_tag(v___x_2296_) == 0)
{
lean_object* v_a_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2311_; 
v_a_2297_ = lean_ctor_get(v___x_2296_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2296_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2299_ = v___x_2296_;
v_isShared_2300_ = v_isSharedCheck_2311_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_a_2297_);
lean_dec(v___x_2296_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2311_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v_fst_2301_; 
v_fst_2301_ = lean_ctor_get(v_a_2297_, 0);
if (lean_obj_tag(v_fst_2301_) == 0)
{
lean_object* v_snd_2302_; lean_object* v___x_2303_; lean_object* v___x_2305_; 
v_snd_2302_ = lean_ctor_get(v_a_2297_, 1);
lean_inc(v_snd_2302_);
lean_dec(v_a_2297_);
v___x_2303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2303_, 0, v_snd_2302_);
if (v_isShared_2300_ == 0)
{
lean_ctor_set(v___x_2299_, 0, v___x_2303_);
v___x_2305_ = v___x_2299_;
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
else
{
lean_object* v_val_2307_; lean_object* v___x_2309_; 
lean_inc_ref(v_fst_2301_);
lean_dec(v_a_2297_);
v_val_2307_ = lean_ctor_get(v_fst_2301_, 0);
lean_inc(v_val_2307_);
lean_dec_ref_known(v_fst_2301_, 1);
if (v_isShared_2300_ == 0)
{
lean_ctor_set(v___x_2299_, 0, v_val_2307_);
v___x_2309_ = v___x_2299_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_val_2307_);
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
else
{
lean_object* v_a_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2319_; 
v_a_2312_ = lean_ctor_get(v___x_2296_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2296_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2314_ = v___x_2296_;
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_a_2312_);
lean_dec(v___x_2296_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2317_; 
if (v_isShared_2315_ == 0)
{
v___x_2317_ = v___x_2314_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_a_2312_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
}
}
}
}
else
{
lean_object* v_vs_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; size_t v_sz_2323_; size_t v___x_2324_; lean_object* v___x_2325_; 
v_vs_2320_ = lean_ctor_get(v_n_2278_, 0);
v___x_2321_ = lean_box(0);
v___x_2322_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2321_);
lean_ctor_set(v___x_2322_, 1, v_b_2279_);
v_sz_2323_ = lean_array_size(v_vs_2320_);
v___x_2324_ = ((size_t)0ULL);
v___x_2325_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9(v_c_2276_, v_x_2277_, v_vs_2320_, v_sz_2323_, v___x_2324_, v___x_2322_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2340_; 
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2328_ = v___x_2325_;
v_isShared_2329_ = v_isSharedCheck_2340_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_dec(v___x_2325_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2340_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v_fst_2330_; 
v_fst_2330_ = lean_ctor_get(v_a_2326_, 0);
if (lean_obj_tag(v_fst_2330_) == 0)
{
lean_object* v_snd_2331_; lean_object* v___x_2332_; lean_object* v___x_2334_; 
v_snd_2331_ = lean_ctor_get(v_a_2326_, 1);
lean_inc(v_snd_2331_);
lean_dec(v_a_2326_);
v___x_2332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2332_, 0, v_snd_2331_);
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 0, v___x_2332_);
v___x_2334_ = v___x_2328_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v___x_2332_);
v___x_2334_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
return v___x_2334_;
}
}
else
{
lean_object* v_val_2336_; lean_object* v___x_2338_; 
lean_inc_ref(v_fst_2330_);
lean_dec(v_a_2326_);
v_val_2336_ = lean_ctor_get(v_fst_2330_, 0);
lean_inc(v_val_2336_);
lean_dec_ref_known(v_fst_2330_, 1);
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 0, v_val_2336_);
v___x_2338_ = v___x_2328_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_val_2336_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
}
else
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2348_; 
v_a_2341_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2343_ = v___x_2325_;
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___x_2325_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___x_2346_; 
if (v_isShared_2344_ == 0)
{
v___x_2346_ = v___x_2343_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_a_2341_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
return v___x_2346_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_2275_ = stack[0].m_obj;
lean_object* v_c_2276_ = stack[1].m_obj;
lean_object* v_x_2277_ = stack[2].m_obj;
lean_object* v_n_2278_ = stack[3].m_obj;
lean_object* v_b_2279_ = stack[4].m_obj;
lean_object* v___y_2280_ = stack[5].m_obj;
lean_object* v___y_2281_ = stack[6].m_obj;
lean_object* v___y_2282_ = stack[7].m_obj;
lean_object* v___y_2283_ = stack[8].m_obj;
lean_object* v___y_2284_ = stack[9].m_obj;
lean_object* v___y_2285_ = stack[10].m_obj;
lean_object* v___y_2286_ = stack[11].m_obj;
lean_object* v___y_2287_ = stack[12].m_obj;
lean_object* v___y_2288_ = stack[13].m_obj;
lean_object* v___y_2289_ = stack[14].m_obj;
lean_object* v_res_2349_;
v_res_2349_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(v_init_2275_, v_c_2276_, v_x_2277_, v_n_2278_, v_b_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
stack->m_obj
 = v_res_2349_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8(lean_object* v_init_2350_, lean_object* v_c_2351_, lean_object* v_x_2352_, lean_object* v_as_2353_, size_t v_sz_2354_, size_t v_i_2355_, lean_object* v_b_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_){
_start:
{
uint8_t v___x_2368_; 
v___x_2368_ = lean_usize_dec_lt(v_i_2355_, v_sz_2354_);
if (v___x_2368_ == 0)
{
lean_object* v___x_2369_; 
lean_dec(v_x_2352_);
lean_dec_ref(v_c_2351_);
v___x_2369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2369_, 0, v_b_2356_);
return v___x_2369_;
}
else
{
lean_object* v_snd_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2404_; 
v_snd_2370_ = lean_ctor_get(v_b_2356_, 1);
v_isSharedCheck_2404_ = !lean_is_exclusive(v_b_2356_);
if (v_isSharedCheck_2404_ == 0)
{
lean_object* v_unused_2405_; 
v_unused_2405_ = lean_ctor_get(v_b_2356_, 0);
lean_dec(v_unused_2405_);
v___x_2372_ = v_b_2356_;
v_isShared_2373_ = v_isSharedCheck_2404_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_snd_2370_);
lean_dec(v_b_2356_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2404_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2374_; lean_object* v_a_2375_; lean_object* v___x_2376_; 
v___x_2374_ = lean_box(0);
v_a_2375_ = lean_array_uget_borrowed(v_as_2353_, v_i_2355_);
lean_inc(v_snd_2370_);
lean_inc(v_x_2352_);
lean_inc_ref(v_c_2351_);
v___x_2376_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(v_init_2350_, v_c_2351_, v_x_2352_, v_a_2375_, v_snd_2370_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_);
if (lean_obj_tag(v___x_2376_) == 0)
{
lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2395_; 
v_a_2377_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2395_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2379_ = v___x_2376_;
v_isShared_2380_ = v_isSharedCheck_2395_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_dec(v___x_2376_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2395_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
if (lean_obj_tag(v_a_2377_) == 0)
{
lean_object* v___x_2381_; lean_object* v___x_2383_; 
lean_dec(v_x_2352_);
lean_dec_ref(v_c_2351_);
v___x_2381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2381_, 0, v_a_2377_);
if (v_isShared_2373_ == 0)
{
lean_ctor_set(v___x_2372_, 0, v___x_2381_);
v___x_2383_ = v___x_2372_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v___x_2381_);
lean_ctor_set(v_reuseFailAlloc_2387_, 1, v_snd_2370_);
v___x_2383_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
lean_object* v___x_2385_; 
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
}
else
{
lean_object* v_a_2388_; lean_object* v___x_2390_; 
lean_del_object(v___x_2379_);
lean_dec(v_snd_2370_);
v_a_2388_ = lean_ctor_get(v_a_2377_, 0);
lean_inc(v_a_2388_);
lean_dec_ref_known(v_a_2377_, 1);
if (v_isShared_2373_ == 0)
{
lean_ctor_set(v___x_2372_, 1, v_a_2388_);
lean_ctor_set(v___x_2372_, 0, v___x_2374_);
v___x_2390_ = v___x_2372_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v___x_2374_);
lean_ctor_set(v_reuseFailAlloc_2394_, 1, v_a_2388_);
v___x_2390_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
size_t v___x_2391_; size_t v___x_2392_; 
v___x_2391_ = ((size_t)1ULL);
v___x_2392_ = lean_usize_add(v_i_2355_, v___x_2391_);
v_i_2355_ = v___x_2392_;
v_b_2356_ = v___x_2390_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2403_; 
lean_del_object(v___x_2372_);
lean_dec(v_snd_2370_);
lean_dec(v_x_2352_);
lean_dec_ref(v_c_2351_);
v_a_2396_ = lean_ctor_get(v___x_2376_, 0);
v_isSharedCheck_2403_ = !lean_is_exclusive(v___x_2376_);
if (v_isSharedCheck_2403_ == 0)
{
v___x_2398_ = v___x_2376_;
v_isShared_2399_ = v_isSharedCheck_2403_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_a_2396_);
lean_dec(v___x_2376_);
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
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_2350_ = stack[0].m_obj;
lean_object* v_c_2351_ = stack[1].m_obj;
lean_object* v_x_2352_ = stack[2].m_obj;
lean_object* v_as_2353_ = stack[3].m_obj;
size_t v_sz_2354_ = stack[4].m_num;
size_t v_i_2355_ = stack[5].m_num;
lean_object* v_b_2356_ = stack[6].m_obj;
lean_object* v___y_2357_ = stack[7].m_obj;
lean_object* v___y_2358_ = stack[8].m_obj;
lean_object* v___y_2359_ = stack[9].m_obj;
lean_object* v___y_2360_ = stack[10].m_obj;
lean_object* v___y_2361_ = stack[11].m_obj;
lean_object* v___y_2362_ = stack[12].m_obj;
lean_object* v___y_2363_ = stack[13].m_obj;
lean_object* v___y_2364_ = stack[14].m_obj;
lean_object* v___y_2365_ = stack[15].m_obj;
lean_object* v___y_2366_ = stack[16].m_obj;
lean_object* v_res_2406_;
v_res_2406_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8(v_init_2350_, v_c_2351_, v_x_2352_, v_as_2353_, v_sz_2354_, v_i_2355_, v_b_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_);
stack->m_obj
 = v_res_2406_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8___boxed(lean_object** _args){
lean_object* v_init_2407_ = _args[0];
lean_object* v_c_2408_ = _args[1];
lean_object* v_x_2409_ = _args[2];
lean_object* v_as_2410_ = _args[3];
lean_object* v_sz_2411_ = _args[4];
lean_object* v_i_2412_ = _args[5];
lean_object* v_b_2413_ = _args[6];
lean_object* v___y_2414_ = _args[7];
lean_object* v___y_2415_ = _args[8];
lean_object* v___y_2416_ = _args[9];
lean_object* v___y_2417_ = _args[10];
lean_object* v___y_2418_ = _args[11];
lean_object* v___y_2419_ = _args[12];
lean_object* v___y_2420_ = _args[13];
lean_object* v___y_2421_ = _args[14];
lean_object* v___y_2422_ = _args[15];
lean_object* v___y_2423_ = _args[16];
lean_object* v___y_2424_ = _args[17];
_start:
{
size_t v_sz_boxed_2425_; size_t v_i_boxed_2426_; lean_object* v_res_2427_; 
v_sz_boxed_2425_ = lean_unbox_usize(v_sz_2411_);
lean_dec(v_sz_2411_);
v_i_boxed_2426_ = lean_unbox_usize(v_i_2412_);
lean_dec(v_i_2412_);
v_res_2427_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8(v_init_2407_, v_c_2408_, v_x_2409_, v_as_2410_, v_sz_boxed_2425_, v_i_boxed_2426_, v_b_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec(v___y_2417_);
lean_dec_ref(v___y_2416_);
lean_dec(v___y_2415_);
lean_dec(v___y_2414_);
lean_dec_ref(v_as_2410_);
lean_dec_ref(v_init_2407_);
return v_res_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6___boxed(lean_object* v_init_2428_, lean_object* v_c_2429_, lean_object* v_x_2430_, lean_object* v_n_2431_, lean_object* v_b_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_){
_start:
{
lean_object* v_res_2444_; 
v_res_2444_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(v_init_2428_, v_c_2429_, v_x_2430_, v_n_2431_, v_b_2432_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_, v___y_2442_);
lean_dec(v___y_2442_);
lean_dec_ref(v___y_2441_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
lean_dec(v___y_2436_);
lean_dec_ref(v___y_2435_);
lean_dec(v___y_2434_);
lean_dec(v___y_2433_);
lean_dec_ref(v_n_2431_);
lean_dec_ref(v_init_2428_);
return v_res_2444_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2(lean_object* v_c_2445_, lean_object* v_x_2446_, lean_object* v_t_2447_, lean_object* v_init_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_){
_start:
{
lean_object* v_root_2460_; lean_object* v_tail_2461_; lean_object* v___x_2462_; 
v_root_2460_ = lean_ctor_get(v_t_2447_, 0);
v_tail_2461_ = lean_ctor_get(v_t_2447_, 1);
lean_inc(v_x_2446_);
lean_inc_ref(v_c_2445_);
lean_inc_ref(v_init_2448_);
v___x_2462_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(v_init_2448_, v_c_2445_, v_x_2446_, v_root_2460_, v_init_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
lean_dec_ref(v_init_2448_);
if (lean_obj_tag(v___x_2462_) == 0)
{
lean_object* v_a_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2499_; 
v_a_2463_ = lean_ctor_get(v___x_2462_, 0);
v_isSharedCheck_2499_ = !lean_is_exclusive(v___x_2462_);
if (v_isSharedCheck_2499_ == 0)
{
v___x_2465_ = v___x_2462_;
v_isShared_2466_ = v_isSharedCheck_2499_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_a_2463_);
lean_dec(v___x_2462_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2499_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
if (lean_obj_tag(v_a_2463_) == 0)
{
lean_object* v_a_2467_; lean_object* v___x_2469_; 
lean_dec(v_x_2446_);
lean_dec_ref(v_c_2445_);
v_a_2467_ = lean_ctor_get(v_a_2463_, 0);
lean_inc(v_a_2467_);
lean_dec_ref_known(v_a_2463_, 1);
if (v_isShared_2466_ == 0)
{
lean_ctor_set(v___x_2465_, 0, v_a_2467_);
v___x_2469_ = v___x_2465_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_a_2467_);
v___x_2469_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
return v___x_2469_;
}
}
else
{
lean_object* v_a_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; size_t v_sz_2474_; size_t v___x_2475_; lean_object* v___x_2476_; 
lean_del_object(v___x_2465_);
v_a_2471_ = lean_ctor_get(v_a_2463_, 0);
lean_inc(v_a_2471_);
lean_dec_ref_known(v_a_2463_, 1);
v___x_2472_ = lean_box(0);
v___x_2473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2473_, 0, v___x_2472_);
lean_ctor_set(v___x_2473_, 1, v_a_2471_);
v_sz_2474_ = lean_array_size(v_tail_2461_);
v___x_2475_ = ((size_t)0ULL);
v___x_2476_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7(v_c_2445_, v_x_2446_, v_tail_2461_, v_sz_2474_, v___x_2475_, v___x_2473_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
if (lean_obj_tag(v___x_2476_) == 0)
{
lean_object* v_a_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2490_; 
v_a_2477_ = lean_ctor_get(v___x_2476_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2479_ = v___x_2476_;
v_isShared_2480_ = v_isSharedCheck_2490_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_a_2477_);
lean_dec(v___x_2476_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2490_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v_fst_2481_; 
v_fst_2481_ = lean_ctor_get(v_a_2477_, 0);
if (lean_obj_tag(v_fst_2481_) == 0)
{
lean_object* v_snd_2482_; lean_object* v___x_2484_; 
v_snd_2482_ = lean_ctor_get(v_a_2477_, 1);
lean_inc(v_snd_2482_);
lean_dec(v_a_2477_);
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 0, v_snd_2482_);
v___x_2484_ = v___x_2479_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_snd_2482_);
v___x_2484_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
return v___x_2484_;
}
}
else
{
lean_object* v_val_2486_; lean_object* v___x_2488_; 
lean_inc_ref(v_fst_2481_);
lean_dec(v_a_2477_);
v_val_2486_ = lean_ctor_get(v_fst_2481_, 0);
lean_inc(v_val_2486_);
lean_dec_ref_known(v_fst_2481_, 1);
if (v_isShared_2480_ == 0)
{
lean_ctor_set(v___x_2479_, 0, v_val_2486_);
v___x_2488_ = v___x_2479_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_val_2486_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
}
else
{
lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2498_; 
v_a_2491_ = lean_ctor_get(v___x_2476_, 0);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2493_ = v___x_2476_;
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_dec(v___x_2476_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2496_; 
if (v_isShared_2494_ == 0)
{
v___x_2496_ = v___x_2493_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_a_2491_);
v___x_2496_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
return v___x_2496_;
}
}
}
}
}
}
else
{
lean_object* v_a_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2507_; 
lean_dec(v_x_2446_);
lean_dec_ref(v_c_2445_);
v_a_2500_ = lean_ctor_get(v___x_2462_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2462_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2502_ = v___x_2462_;
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_a_2500_);
lean_dec(v___x_2462_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2505_; 
if (v_isShared_2503_ == 0)
{
v___x_2505_ = v___x_2502_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_a_2500_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_2445_ = stack[0].m_obj;
lean_object* v_x_2446_ = stack[1].m_obj;
lean_object* v_t_2447_ = stack[2].m_obj;
lean_object* v_init_2448_ = stack[3].m_obj;
lean_object* v___y_2449_ = stack[4].m_obj;
lean_object* v___y_2450_ = stack[5].m_obj;
lean_object* v___y_2451_ = stack[6].m_obj;
lean_object* v___y_2452_ = stack[7].m_obj;
lean_object* v___y_2453_ = stack[8].m_obj;
lean_object* v___y_2454_ = stack[9].m_obj;
lean_object* v___y_2455_ = stack[10].m_obj;
lean_object* v___y_2456_ = stack[11].m_obj;
lean_object* v___y_2457_ = stack[12].m_obj;
lean_object* v___y_2458_ = stack[13].m_obj;
lean_object* v_res_2508_;
v_res_2508_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2(v_c_2445_, v_x_2446_, v_t_2447_, v_init_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
stack->m_obj
 = v_res_2508_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2___boxed(lean_object* v_c_2509_, lean_object* v_x_2510_, lean_object* v_t_2511_, lean_object* v_init_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_){
_start:
{
lean_object* v_res_2524_; 
v_res_2524_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2(v_c_2509_, v_x_2510_, v_t_2511_, v_init_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
lean_dec(v___y_2518_);
lean_dec_ref(v___y_2517_);
lean_dec(v___y_2516_);
lean_dec_ref(v___y_2515_);
lean_dec(v___y_2514_);
lean_dec(v___y_2513_);
lean_dec_ref(v_t_2511_);
return v_res_2524_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(lean_object* v_x_2525_, lean_object* v_c_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_){
_start:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2538_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0);
v___x_2539_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2527_, v_a_2535_);
if (lean_obj_tag(v___x_2539_) == 0)
{
lean_object* v_a_2540_; lean_object* v___y_2542_; lean_object* v_diseqs_2567_; lean_object* v_size_2568_; uint8_t v___x_2569_; 
v_a_2540_ = lean_ctor_get(v___x_2539_, 0);
lean_inc(v_a_2540_);
lean_dec_ref_known(v___x_2539_, 1);
v_diseqs_2567_ = lean_ctor_get(v_a_2540_, 8);
lean_inc_ref(v_diseqs_2567_);
lean_dec(v_a_2540_);
v_size_2568_ = lean_ctor_get(v_diseqs_2567_, 2);
v___x_2569_ = lean_nat_dec_lt(v_x_2525_, v_size_2568_);
if (v___x_2569_ == 0)
{
lean_object* v___x_2570_; 
lean_dec_ref(v_diseqs_2567_);
v___x_2570_ = l_outOfBounds___redArg(v___x_2538_);
v___y_2542_ = v___x_2570_;
goto v___jp_2541_;
}
else
{
lean_object* v___x_2571_; 
v___x_2571_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2538_, v_diseqs_2567_, v_x_2525_);
lean_dec_ref(v_diseqs_2567_);
v___y_2542_ = v___x_2571_;
goto v___jp_2541_;
}
v___jp_2541_:
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2543_ = lean_box(0);
v___x_2544_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___closed__0));
v___x_2545_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2(v_c_2526_, v_x_2525_, v___y_2542_, v___x_2544_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_);
lean_dec_ref(v___y_2542_);
if (lean_obj_tag(v___x_2545_) == 0)
{
lean_object* v_a_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2558_; 
v_a_2546_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2548_ = v___x_2545_;
v_isShared_2549_ = v_isSharedCheck_2558_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_a_2546_);
lean_dec(v___x_2545_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2558_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v_fst_2550_; 
v_fst_2550_ = lean_ctor_get(v_a_2546_, 0);
lean_inc(v_fst_2550_);
lean_dec(v_a_2546_);
if (lean_obj_tag(v_fst_2550_) == 0)
{
lean_object* v___x_2552_; 
if (v_isShared_2549_ == 0)
{
lean_ctor_set(v___x_2548_, 0, v___x_2543_);
v___x_2552_ = v___x_2548_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v___x_2543_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
else
{
lean_object* v_val_2554_; lean_object* v___x_2556_; 
v_val_2554_ = lean_ctor_get(v_fst_2550_, 0);
lean_inc(v_val_2554_);
lean_dec_ref_known(v_fst_2550_, 1);
if (v_isShared_2549_ == 0)
{
lean_ctor_set(v___x_2548_, 0, v_val_2554_);
v___x_2556_ = v___x_2548_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_val_2554_);
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
else
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2566_; 
v_a_2559_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2561_ = v___x_2545_;
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2545_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2564_; 
if (v_isShared_2562_ == 0)
{
v___x_2564_ = v___x_2561_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_a_2559_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
}
}
}
else
{
lean_object* v_a_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2579_; 
lean_dec_ref(v_c_2526_);
lean_dec(v_x_2525_);
v_a_2572_ = lean_ctor_get(v___x_2539_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2539_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2574_ = v___x_2539_;
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_a_2572_);
lean_dec(v___x_2539_);
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2525_ = stack[0].m_obj;
lean_object* v_c_2526_ = stack[1].m_obj;
lean_object* v_a_2527_ = stack[2].m_obj;
lean_object* v_a_2528_ = stack[3].m_obj;
lean_object* v_a_2529_ = stack[4].m_obj;
lean_object* v_a_2530_ = stack[5].m_obj;
lean_object* v_a_2531_ = stack[6].m_obj;
lean_object* v_a_2532_ = stack[7].m_obj;
lean_object* v_a_2533_ = stack[8].m_obj;
lean_object* v_a_2534_ = stack[9].m_obj;
lean_object* v_a_2535_ = stack[10].m_obj;
lean_object* v_a_2536_ = stack[11].m_obj;
lean_object* v_res_2580_;
v_res_2580_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(v_x_2525_, v_c_2526_, v_a_2527_, v_a_2528_, v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_, v_a_2536_);
stack->m_obj
 = v_res_2580_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f___boxed(lean_object* v_x_2581_, lean_object* v_c_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v_a_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_){
_start:
{
lean_object* v_res_2594_; 
v_res_2594_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(v_x_2581_, v_c_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_);
lean_dec(v_a_2592_);
lean_dec_ref(v_a_2591_);
lean_dec(v_a_2590_);
lean_dec_ref(v_a_2589_);
lean_dec(v_a_2588_);
lean_dec_ref(v_a_2587_);
lean_dec(v_a_2586_);
lean_dec_ref(v_a_2585_);
lean_dec(v_a_2584_);
lean_dec(v_a_2583_);
return v_res_2594_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11(lean_object* v_c_2595_, lean_object* v_x_2596_, lean_object* v_as_2597_, size_t v_sz_2598_, size_t v_i_2599_, lean_object* v_b_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_){
_start:
{
lean_object* v___x_2612_; 
v___x_2612_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(v_c_2595_, v_x_2596_, v_as_2597_, v_sz_2598_, v_i_2599_, v_b_2600_, v___y_2601_);
return v___x_2612_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_2595_ = stack[0].m_obj;
lean_object* v_x_2596_ = stack[1].m_obj;
lean_object* v_as_2597_ = stack[2].m_obj;
size_t v_sz_2598_ = stack[3].m_num;
size_t v_i_2599_ = stack[4].m_num;
lean_object* v_b_2600_ = stack[5].m_obj;
lean_object* v___y_2601_ = stack[6].m_obj;
lean_object* v___y_2602_ = stack[7].m_obj;
lean_object* v___y_2603_ = stack[8].m_obj;
lean_object* v___y_2604_ = stack[9].m_obj;
lean_object* v___y_2605_ = stack[10].m_obj;
lean_object* v___y_2606_ = stack[11].m_obj;
lean_object* v___y_2607_ = stack[12].m_obj;
lean_object* v___y_2608_ = stack[13].m_obj;
lean_object* v___y_2609_ = stack[14].m_obj;
lean_object* v___y_2610_ = stack[15].m_obj;
lean_object* v_res_2613_;
v_res_2613_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11(v_c_2595_, v_x_2596_, v_as_2597_, v_sz_2598_, v_i_2599_, v_b_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
stack->m_obj
 = v_res_2613_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___boxed(lean_object** _args){
lean_object* v_c_2614_ = _args[0];
lean_object* v_x_2615_ = _args[1];
lean_object* v_as_2616_ = _args[2];
lean_object* v_sz_2617_ = _args[3];
lean_object* v_i_2618_ = _args[4];
lean_object* v_b_2619_ = _args[5];
lean_object* v___y_2620_ = _args[6];
lean_object* v___y_2621_ = _args[7];
lean_object* v___y_2622_ = _args[8];
lean_object* v___y_2623_ = _args[9];
lean_object* v___y_2624_ = _args[10];
lean_object* v___y_2625_ = _args[11];
lean_object* v___y_2626_ = _args[12];
lean_object* v___y_2627_ = _args[13];
lean_object* v___y_2628_ = _args[14];
lean_object* v___y_2629_ = _args[15];
lean_object* v___y_2630_ = _args[16];
_start:
{
size_t v_sz_boxed_2631_; size_t v_i_boxed_2632_; lean_object* v_res_2633_; 
v_sz_boxed_2631_ = lean_unbox_usize(v_sz_2617_);
lean_dec(v_sz_2617_);
v_i_boxed_2632_ = lean_unbox_usize(v_i_2618_);
lean_dec(v_i_2618_);
v_res_2633_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11(v_c_2614_, v_x_2615_, v_as_2616_, v_sz_boxed_2631_, v_i_boxed_2632_, v_b_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec(v___y_2627_);
lean_dec_ref(v___y_2626_);
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
lean_dec(v___y_2623_);
lean_dec_ref(v___y_2622_);
lean_dec(v___y_2621_);
lean_dec(v___y_2620_);
lean_dec_ref(v_as_2616_);
return v_res_2633_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10(lean_object* v_c_2634_, lean_object* v_x_2635_, lean_object* v_as_2636_, size_t v_sz_2637_, size_t v_i_2638_, lean_object* v_b_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_){
_start:
{
lean_object* v___x_2651_; 
v___x_2651_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(v_c_2634_, v_x_2635_, v_as_2636_, v_sz_2637_, v_i_2638_, v_b_2639_, v___y_2640_);
return v___x_2651_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_2634_ = stack[0].m_obj;
lean_object* v_x_2635_ = stack[1].m_obj;
lean_object* v_as_2636_ = stack[2].m_obj;
size_t v_sz_2637_ = stack[3].m_num;
size_t v_i_2638_ = stack[4].m_num;
lean_object* v_b_2639_ = stack[5].m_obj;
lean_object* v___y_2640_ = stack[6].m_obj;
lean_object* v___y_2641_ = stack[7].m_obj;
lean_object* v___y_2642_ = stack[8].m_obj;
lean_object* v___y_2643_ = stack[9].m_obj;
lean_object* v___y_2644_ = stack[10].m_obj;
lean_object* v___y_2645_ = stack[11].m_obj;
lean_object* v___y_2646_ = stack[12].m_obj;
lean_object* v___y_2647_ = stack[13].m_obj;
lean_object* v___y_2648_ = stack[14].m_obj;
lean_object* v___y_2649_ = stack[15].m_obj;
lean_object* v_res_2652_;
v_res_2652_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10(v_c_2634_, v_x_2635_, v_as_2636_, v_sz_2637_, v_i_2638_, v_b_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
stack->m_obj
 = v_res_2652_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___boxed(lean_object** _args){
lean_object* v_c_2653_ = _args[0];
lean_object* v_x_2654_ = _args[1];
lean_object* v_as_2655_ = _args[2];
lean_object* v_sz_2656_ = _args[3];
lean_object* v_i_2657_ = _args[4];
lean_object* v_b_2658_ = _args[5];
lean_object* v___y_2659_ = _args[6];
lean_object* v___y_2660_ = _args[7];
lean_object* v___y_2661_ = _args[8];
lean_object* v___y_2662_ = _args[9];
lean_object* v___y_2663_ = _args[10];
lean_object* v___y_2664_ = _args[11];
lean_object* v___y_2665_ = _args[12];
lean_object* v___y_2666_ = _args[13];
lean_object* v___y_2667_ = _args[14];
lean_object* v___y_2668_ = _args[15];
lean_object* v___y_2669_ = _args[16];
_start:
{
size_t v_sz_boxed_2670_; size_t v_i_boxed_2671_; lean_object* v_res_2672_; 
v_sz_boxed_2670_ = lean_unbox_usize(v_sz_2656_);
lean_dec(v_sz_2656_);
v_i_boxed_2671_ = lean_unbox_usize(v_i_2657_);
lean_dec(v_i_2657_);
v_res_2672_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10(v_c_2653_, v_x_2654_, v_as_2655_, v_sz_boxed_2670_, v_i_boxed_2671_, v_b_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
lean_dec(v___y_2664_);
lean_dec_ref(v___y_2663_);
lean_dec(v___y_2662_);
lean_dec_ref(v___y_2661_);
lean_dec(v___y_2660_);
lean_dec(v___y_2659_);
lean_dec_ref(v_as_2655_);
return v_res_2672_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg(lean_object* v_v_2673_, lean_object* v_a_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_){
_start:
{
lean_object* v_snd_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2717_; 
v_snd_2686_ = lean_ctor_get(v_a_2674_, 1);
v_isSharedCheck_2717_ = !lean_is_exclusive(v_a_2674_);
if (v_isSharedCheck_2717_ == 0)
{
lean_object* v_unused_2718_; 
v_unused_2718_ = lean_ctor_get(v_a_2674_, 0);
lean_dec(v_unused_2718_);
v___x_2688_ = v_a_2674_;
v_isShared_2689_ = v_isSharedCheck_2717_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_snd_2686_);
lean_dec(v_a_2674_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2717_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; 
v___x_2690_ = lean_box(0);
lean_inc(v_snd_2686_);
lean_inc(v_v_2673_);
v___x_2691_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(v_v_2673_, v_snd_2686_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
if (lean_obj_tag(v___x_2691_) == 0)
{
lean_object* v_a_2692_; lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2708_; 
v_a_2692_ = lean_ctor_get(v___x_2691_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2691_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2694_ = v___x_2691_;
v_isShared_2695_ = v_isSharedCheck_2708_;
goto v_resetjp_2693_;
}
else
{
lean_inc(v_a_2692_);
lean_dec(v___x_2691_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2708_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
if (lean_obj_tag(v_a_2692_) == 1)
{
lean_object* v_val_2696_; lean_object* v___x_2698_; 
lean_del_object(v___x_2694_);
lean_dec(v_snd_2686_);
v_val_2696_ = lean_ctor_get(v_a_2692_, 0);
lean_inc(v_val_2696_);
lean_dec_ref_known(v_a_2692_, 1);
if (v_isShared_2689_ == 0)
{
lean_ctor_set(v___x_2688_, 1, v_val_2696_);
lean_ctor_set(v___x_2688_, 0, v___x_2690_);
v___x_2698_ = v___x_2688_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___x_2690_);
lean_ctor_set(v_reuseFailAlloc_2700_, 1, v_val_2696_);
v___x_2698_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
v_a_2674_ = v___x_2698_;
goto _start;
}
}
else
{
lean_object* v___x_2701_; lean_object* v___x_2703_; 
lean_dec(v_a_2692_);
lean_dec(v_v_2673_);
lean_inc(v_snd_2686_);
v___x_2701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2701_, 0, v_snd_2686_);
if (v_isShared_2689_ == 0)
{
lean_ctor_set(v___x_2688_, 0, v___x_2701_);
v___x_2703_ = v___x_2688_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v___x_2701_);
lean_ctor_set(v_reuseFailAlloc_2707_, 1, v_snd_2686_);
v___x_2703_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
lean_object* v___x_2705_; 
if (v_isShared_2695_ == 0)
{
lean_ctor_set(v___x_2694_, 0, v___x_2703_);
v___x_2705_ = v___x_2694_;
goto v_reusejp_2704_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___x_2703_);
v___x_2705_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2704_;
}
v_reusejp_2704_:
{
return v___x_2705_;
}
}
}
}
}
else
{
lean_object* v_a_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2716_; 
lean_del_object(v___x_2688_);
lean_dec(v_snd_2686_);
lean_dec(v_v_2673_);
v_a_2709_ = lean_ctor_get(v___x_2691_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2691_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2711_ = v___x_2691_;
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_a_2709_);
lean_dec(v___x_2691_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2714_; 
if (v_isShared_2712_ == 0)
{
v___x_2714_ = v___x_2711_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v_a_2709_);
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
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_2673_ = stack[0].m_obj;
lean_object* v_a_2674_ = stack[1].m_obj;
lean_object* v___y_2675_ = stack[2].m_obj;
lean_object* v___y_2676_ = stack[3].m_obj;
lean_object* v___y_2677_ = stack[4].m_obj;
lean_object* v___y_2678_ = stack[5].m_obj;
lean_object* v___y_2679_ = stack[6].m_obj;
lean_object* v___y_2680_ = stack[7].m_obj;
lean_object* v___y_2681_ = stack[8].m_obj;
lean_object* v___y_2682_ = stack[9].m_obj;
lean_object* v___y_2683_ = stack[10].m_obj;
lean_object* v___y_2684_ = stack[11].m_obj;
lean_object* v_res_2719_;
v_res_2719_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg(v_v_2673_, v_a_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_, v___y_2683_, v___y_2684_);
stack->m_obj
 = v_res_2719_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg___boxed(lean_object* v_v_2720_, lean_object* v_a_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_){
_start:
{
lean_object* v_res_2733_; 
v_res_2733_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg(v_v_2720_, v_a_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v___y_2723_);
lean_dec(v___y_2722_);
return v_res_2733_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(lean_object* v_c_2734_, lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_){
_start:
{
lean_object* v_p_2746_; 
v_p_2746_ = lean_ctor_get(v_c_2734_, 0);
if (lean_obj_tag(v_p_2746_) == 1)
{
lean_object* v_v_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; 
v_v_2747_ = lean_ctor_get(v_p_2746_, 1);
lean_inc(v_v_2747_);
v___x_2748_ = lean_box(0);
v___x_2749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2749_, 0, v___x_2748_);
lean_ctor_set(v___x_2749_, 1, v_c_2734_);
v___x_2750_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg(v_v_2747_, v___x_2749_, v_a_2735_, v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v_a_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2764_; 
v_a_2751_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2764_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2764_ == 0)
{
v___x_2753_ = v___x_2750_;
v_isShared_2754_ = v_isSharedCheck_2764_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_a_2751_);
lean_dec(v___x_2750_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2764_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v_fst_2755_; 
v_fst_2755_ = lean_ctor_get(v_a_2751_, 0);
if (lean_obj_tag(v_fst_2755_) == 0)
{
lean_object* v_snd_2756_; lean_object* v___x_2758_; 
v_snd_2756_ = lean_ctor_get(v_a_2751_, 1);
lean_inc(v_snd_2756_);
lean_dec(v_a_2751_);
if (v_isShared_2754_ == 0)
{
lean_ctor_set(v___x_2753_, 0, v_snd_2756_);
v___x_2758_ = v___x_2753_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_snd_2756_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
}
}
else
{
lean_object* v_val_2760_; lean_object* v___x_2762_; 
lean_inc_ref(v_fst_2755_);
lean_dec(v_a_2751_);
v_val_2760_ = lean_ctor_get(v_fst_2755_, 0);
lean_inc(v_val_2760_);
lean_dec_ref_known(v_fst_2755_, 1);
if (v_isShared_2754_ == 0)
{
lean_ctor_set(v___x_2753_, 0, v_val_2760_);
v___x_2762_ = v___x_2753_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v_val_2760_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
return v___x_2762_;
}
}
}
}
else
{
lean_object* v_a_2765_; lean_object* v___x_2767_; uint8_t v_isShared_2768_; uint8_t v_isSharedCheck_2772_; 
v_a_2765_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2772_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2772_ == 0)
{
v___x_2767_ = v___x_2750_;
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
else
{
lean_inc(v_a_2765_);
lean_dec(v___x_2750_);
v___x_2767_ = lean_box(0);
v_isShared_2768_ = v_isSharedCheck_2772_;
goto v_resetjp_2766_;
}
v_resetjp_2766_:
{
lean_object* v___x_2770_; 
if (v_isShared_2768_ == 0)
{
v___x_2770_ = v___x_2767_;
goto v_reusejp_2769_;
}
else
{
lean_object* v_reuseFailAlloc_2771_; 
v_reuseFailAlloc_2771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_a_2765_);
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
else
{
lean_object* v___x_2773_; 
v___x_2773_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_2734_, v_a_2735_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_);
return v___x_2773_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_2734_ = stack[0].m_obj;
lean_object* v_a_2735_ = stack[1].m_obj;
lean_object* v_a_2736_ = stack[2].m_obj;
lean_object* v_a_2737_ = stack[3].m_obj;
lean_object* v_a_2738_ = stack[4].m_obj;
lean_object* v_a_2739_ = stack[5].m_obj;
lean_object* v_a_2740_ = stack[6].m_obj;
lean_object* v_a_2741_ = stack[7].m_obj;
lean_object* v_a_2742_ = stack[8].m_obj;
lean_object* v_a_2743_ = stack[9].m_obj;
lean_object* v_a_2744_ = stack[10].m_obj;
lean_object* v_res_2774_;
v_res_2774_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(v_c_2734_, v_a_2735_, v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_);
stack->m_obj
 = v_res_2774_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq___boxed(lean_object* v_c_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_, lean_object* v_a_2786_){
_start:
{
lean_object* v_res_2787_; 
v_res_2787_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(v_c_2775_, v_a_2776_, v_a_2777_, v_a_2778_, v_a_2779_, v_a_2780_, v_a_2781_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_);
lean_dec(v_a_2785_);
lean_dec_ref(v_a_2784_);
lean_dec(v_a_2783_);
lean_dec_ref(v_a_2782_);
lean_dec(v_a_2781_);
lean_dec_ref(v_a_2780_);
lean_dec(v_a_2779_);
lean_dec_ref(v_a_2778_);
lean_dec(v_a_2777_);
lean_dec(v_a_2776_);
return v_res_2787_;
}
}
lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0(lean_object* v_v_2788_, lean_object* v_inst_2789_, lean_object* v_a_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_){
_start:
{
lean_object* v___x_2802_; 
v___x_2802_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg(v_v_2788_, v_a_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
return v___x_2802_;
}
}
LEAN_EXPORT void l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_v_2788_ = stack[0].m_obj;
lean_object* v_a_2790_ = stack[2].m_obj;
lean_object* v___y_2791_ = stack[3].m_obj;
lean_object* v___y_2792_ = stack[4].m_obj;
lean_object* v___y_2793_ = stack[5].m_obj;
lean_object* v___y_2794_ = stack[6].m_obj;
lean_object* v___y_2795_ = stack[7].m_obj;
lean_object* v___y_2796_ = stack[8].m_obj;
lean_object* v___y_2797_ = stack[9].m_obj;
lean_object* v___y_2798_ = stack[10].m_obj;
lean_object* v___y_2799_ = stack[11].m_obj;
lean_object* v___y_2800_ = stack[12].m_obj;
lean_object* v_res_2803_;
v_res_2803_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0(v_v_2788_, lean_box(0), v_a_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
stack->m_obj
 = v_res_2803_;
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___boxed(lean_object* v_v_2804_, lean_object* v_inst_2805_, lean_object* v_a_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_){
_start:
{
lean_object* v_res_2818_; 
v_res_2818_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0(v_v_2804_, v_inst_2805_, v_a_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_);
lean_dec(v___y_2816_);
lean_dec_ref(v___y_2815_);
lean_dec(v___y_2814_);
lean_dec_ref(v___y_2813_);
lean_dec(v___y_2812_);
lean_dec_ref(v___y_2811_);
lean_dec(v___y_2810_);
lean_dec_ref(v___y_2809_);
lean_dec(v___y_2808_);
lean_dec(v___y_2807_);
return v_res_2818_;
}
}
lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(lean_object* v_a_2819_, lean_object* v_x_2820_, size_t v_x_2821_, size_t v_x_2822_){
_start:
{
if (lean_obj_tag(v_x_2820_) == 0)
{
lean_object* v_cs_2823_; size_t v_j_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; uint8_t v___x_2827_; 
v_cs_2823_ = lean_ctor_get(v_x_2820_, 0);
v_j_2824_ = lean_usize_shift_right(v_x_2821_, v_x_2822_);
v___x_2825_ = lean_usize_to_nat(v_j_2824_);
v___x_2826_ = lean_array_get_size(v_cs_2823_);
v___x_2827_ = lean_nat_dec_lt(v___x_2825_, v___x_2826_);
if (v___x_2827_ == 0)
{
lean_dec(v___x_2825_);
lean_dec_ref(v_a_2819_);
return v_x_2820_;
}
else
{
lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2845_; 
lean_inc_ref(v_cs_2823_);
v_isSharedCheck_2845_ = !lean_is_exclusive(v_x_2820_);
if (v_isSharedCheck_2845_ == 0)
{
lean_object* v_unused_2846_; 
v_unused_2846_ = lean_ctor_get(v_x_2820_, 0);
lean_dec(v_unused_2846_);
v___x_2829_ = v_x_2820_;
v_isShared_2830_ = v_isSharedCheck_2845_;
goto v_resetjp_2828_;
}
else
{
lean_dec(v_x_2820_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2845_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
size_t v___x_2831_; size_t v___x_2832_; size_t v___x_2833_; size_t v_i_2834_; size_t v___x_2835_; size_t v_shift_2836_; lean_object* v_v_2837_; lean_object* v___x_2838_; lean_object* v_xs_x27_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2843_; 
v___x_2831_ = ((size_t)1ULL);
v___x_2832_ = lean_usize_shift_left(v___x_2831_, v_x_2822_);
v___x_2833_ = lean_usize_sub(v___x_2832_, v___x_2831_);
v_i_2834_ = lean_usize_land(v_x_2821_, v___x_2833_);
v___x_2835_ = ((size_t)5ULL);
v_shift_2836_ = lean_usize_sub(v_x_2822_, v___x_2835_);
v_v_2837_ = lean_array_fget(v_cs_2823_, v___x_2825_);
v___x_2838_ = lean_box(0);
v_xs_x27_2839_ = lean_array_fset(v_cs_2823_, v___x_2825_, v___x_2838_);
v___x_2840_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(v_a_2819_, v_v_2837_, v_i_2834_, v_shift_2836_);
v___x_2841_ = lean_array_fset(v_xs_x27_2839_, v___x_2825_, v___x_2840_);
lean_dec(v___x_2825_);
if (v_isShared_2830_ == 0)
{
lean_ctor_set(v___x_2829_, 0, v___x_2841_);
v___x_2843_ = v___x_2829_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v___x_2841_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
return v___x_2843_;
}
}
}
}
else
{
lean_object* v_vs_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; uint8_t v___x_2850_; 
v_vs_2847_ = lean_ctor_get(v_x_2820_, 0);
v___x_2848_ = lean_usize_to_nat(v_x_2821_);
v___x_2849_ = lean_array_get_size(v_vs_2847_);
v___x_2850_ = lean_nat_dec_lt(v___x_2848_, v___x_2849_);
if (v___x_2850_ == 0)
{
lean_dec(v___x_2848_);
lean_dec_ref(v_a_2819_);
return v_x_2820_;
}
else
{
lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2862_; 
lean_inc_ref(v_vs_2847_);
v_isSharedCheck_2862_ = !lean_is_exclusive(v_x_2820_);
if (v_isSharedCheck_2862_ == 0)
{
lean_object* v_unused_2863_; 
v_unused_2863_ = lean_ctor_get(v_x_2820_, 0);
lean_dec(v_unused_2863_);
v___x_2852_ = v_x_2820_;
v_isShared_2853_ = v_isSharedCheck_2862_;
goto v_resetjp_2851_;
}
else
{
lean_dec(v_x_2820_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2862_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v_v_2854_; lean_object* v___x_2855_; lean_object* v_xs_x27_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2860_; 
v_v_2854_ = lean_array_fget(v_vs_2847_, v___x_2848_);
v___x_2855_ = lean_box(0);
v_xs_x27_2856_ = lean_array_fset(v_vs_2847_, v___x_2848_, v___x_2855_);
v___x_2857_ = l_Lean_PersistentArray_push___redArg(v_v_2854_, v_a_2819_);
v___x_2858_ = lean_array_fset(v_xs_x27_2856_, v___x_2848_, v___x_2857_);
lean_dec(v___x_2848_);
if (v_isShared_2853_ == 0)
{
lean_ctor_set(v___x_2852_, 0, v___x_2858_);
v___x_2860_ = v___x_2852_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v___x_2858_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
return v___x_2860_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2819_ = stack[0].m_obj;
lean_object* v_x_2820_ = stack[1].m_obj;
size_t v_x_2821_ = stack[2].m_num;
size_t v_x_2822_ = stack[3].m_num;
lean_object* v_res_2864_;
v_res_2864_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(v_a_2819_, v_x_2820_, v_x_2821_, v_x_2822_);
stack->m_obj
 = v_res_2864_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0___boxed(lean_object* v_a_2865_, lean_object* v_x_2866_, lean_object* v_x_2867_, lean_object* v_x_2868_){
_start:
{
size_t v_x_62157__boxed_2869_; size_t v_x_62158__boxed_2870_; lean_object* v_res_2871_; 
v_x_62157__boxed_2869_ = lean_unbox_usize(v_x_2867_);
lean_dec(v_x_2867_);
v_x_62158__boxed_2870_ = lean_unbox_usize(v_x_2868_);
lean_dec(v_x_2868_);
v_res_2871_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(v_a_2865_, v_x_2866_, v_x_62157__boxed_2869_, v_x_62158__boxed_2870_);
return v_res_2871_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(lean_object* v_a_2872_, lean_object* v_t_2873_, lean_object* v_i_2874_){
_start:
{
lean_object* v_root_2875_; lean_object* v_tail_2876_; lean_object* v_size_2877_; size_t v_shift_2878_; lean_object* v_tailOff_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2903_; 
v_root_2875_ = lean_ctor_get(v_t_2873_, 0);
v_tail_2876_ = lean_ctor_get(v_t_2873_, 1);
v_size_2877_ = lean_ctor_get(v_t_2873_, 2);
v_shift_2878_ = lean_ctor_get_usize(v_t_2873_, 4);
v_tailOff_2879_ = lean_ctor_get(v_t_2873_, 3);
v_isSharedCheck_2903_ = !lean_is_exclusive(v_t_2873_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2881_ = v_t_2873_;
v_isShared_2882_ = v_isSharedCheck_2903_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_tailOff_2879_);
lean_inc(v_size_2877_);
lean_inc(v_tail_2876_);
lean_inc(v_root_2875_);
lean_dec(v_t_2873_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2903_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
uint8_t v___x_2883_; 
v___x_2883_ = lean_nat_dec_le(v_tailOff_2879_, v_i_2874_);
if (v___x_2883_ == 0)
{
size_t v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2887_; 
v___x_2884_ = lean_usize_of_nat(v_i_2874_);
v___x_2885_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(v_a_2872_, v_root_2875_, v___x_2884_, v_shift_2878_);
if (v_isShared_2882_ == 0)
{
lean_ctor_set(v___x_2881_, 0, v___x_2885_);
v___x_2887_ = v___x_2881_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v___x_2885_);
lean_ctor_set(v_reuseFailAlloc_2888_, 1, v_tail_2876_);
lean_ctor_set(v_reuseFailAlloc_2888_, 2, v_size_2877_);
lean_ctor_set(v_reuseFailAlloc_2888_, 3, v_tailOff_2879_);
lean_ctor_set_usize(v_reuseFailAlloc_2888_, 4, v_shift_2878_);
v___x_2887_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
return v___x_2887_;
}
}
else
{
lean_object* v___x_2889_; lean_object* v___x_2890_; uint8_t v___x_2891_; 
v___x_2889_ = lean_nat_sub(v_i_2874_, v_tailOff_2879_);
v___x_2890_ = lean_array_get_size(v_tail_2876_);
v___x_2891_ = lean_nat_dec_lt(v___x_2889_, v___x_2890_);
if (v___x_2891_ == 0)
{
lean_object* v___x_2893_; 
lean_dec(v___x_2889_);
lean_dec_ref(v_a_2872_);
if (v_isShared_2882_ == 0)
{
v___x_2893_ = v___x_2881_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_root_2875_);
lean_ctor_set(v_reuseFailAlloc_2894_, 1, v_tail_2876_);
lean_ctor_set(v_reuseFailAlloc_2894_, 2, v_size_2877_);
lean_ctor_set(v_reuseFailAlloc_2894_, 3, v_tailOff_2879_);
lean_ctor_set_usize(v_reuseFailAlloc_2894_, 4, v_shift_2878_);
v___x_2893_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
return v___x_2893_;
}
}
else
{
lean_object* v_v_2895_; lean_object* v___x_2896_; lean_object* v_xs_x27_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2901_; 
v_v_2895_ = lean_array_fget(v_tail_2876_, v___x_2889_);
v___x_2896_ = lean_box(0);
v_xs_x27_2897_ = lean_array_fset(v_tail_2876_, v___x_2889_, v___x_2896_);
v___x_2898_ = l_Lean_PersistentArray_push___redArg(v_v_2895_, v_a_2872_);
v___x_2899_ = lean_array_fset(v_xs_x27_2897_, v___x_2889_, v___x_2898_);
lean_dec(v___x_2889_);
if (v_isShared_2882_ == 0)
{
lean_ctor_set(v___x_2881_, 1, v___x_2899_);
v___x_2901_ = v___x_2881_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_root_2875_);
lean_ctor_set(v_reuseFailAlloc_2902_, 1, v___x_2899_);
lean_ctor_set(v_reuseFailAlloc_2902_, 2, v_size_2877_);
lean_ctor_set(v_reuseFailAlloc_2902_, 3, v_tailOff_2879_);
lean_ctor_set_usize(v_reuseFailAlloc_2902_, 4, v_shift_2878_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0___boxed(lean_object* v_a_2904_, lean_object* v_t_2905_, lean_object* v_i_2906_){
_start:
{
lean_object* v_res_2907_; 
v_res_2907_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(v_a_2904_, v_t_2905_, v_i_2906_);
lean_dec(v_i_2906_);
return v_res_2907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0(lean_object* v_a_2908_, lean_object* v_v_2909_, lean_object* v_s_2910_){
_start:
{
lean_object* v_vars_2911_; lean_object* v_varMap_2912_; lean_object* v_varsHistory_2913_; lean_object* v_natToIntMap_2914_; lean_object* v_natDef_2915_; lean_object* v_dvds_2916_; lean_object* v_lowers_2917_; lean_object* v_uppers_2918_; lean_object* v_diseqs_2919_; lean_object* v_elimEqs_2920_; lean_object* v_elimStack_2921_; lean_object* v_occurs_2922_; lean_object* v_assignment_2923_; lean_object* v_nextCnstrId_2924_; uint8_t v_caseSplits_2925_; lean_object* v_steps_2926_; lean_object* v_conflict_x3f_2927_; lean_object* v_diseqSplits_2928_; lean_object* v_divMod_2929_; uint8_t v_usedCommRing_2930_; lean_object* v_nonlinearOccs_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2939_; 
v_vars_2911_ = lean_ctor_get(v_s_2910_, 0);
v_varMap_2912_ = lean_ctor_get(v_s_2910_, 1);
v_varsHistory_2913_ = lean_ctor_get(v_s_2910_, 2);
v_natToIntMap_2914_ = lean_ctor_get(v_s_2910_, 3);
v_natDef_2915_ = lean_ctor_get(v_s_2910_, 4);
v_dvds_2916_ = lean_ctor_get(v_s_2910_, 5);
v_lowers_2917_ = lean_ctor_get(v_s_2910_, 6);
v_uppers_2918_ = lean_ctor_get(v_s_2910_, 7);
v_diseqs_2919_ = lean_ctor_get(v_s_2910_, 8);
v_elimEqs_2920_ = lean_ctor_get(v_s_2910_, 9);
v_elimStack_2921_ = lean_ctor_get(v_s_2910_, 10);
v_occurs_2922_ = lean_ctor_get(v_s_2910_, 11);
v_assignment_2923_ = lean_ctor_get(v_s_2910_, 12);
v_nextCnstrId_2924_ = lean_ctor_get(v_s_2910_, 13);
v_caseSplits_2925_ = lean_ctor_get_uint8(v_s_2910_, sizeof(void*)*19);
v_steps_2926_ = lean_ctor_get(v_s_2910_, 14);
v_conflict_x3f_2927_ = lean_ctor_get(v_s_2910_, 15);
v_diseqSplits_2928_ = lean_ctor_get(v_s_2910_, 16);
v_divMod_2929_ = lean_ctor_get(v_s_2910_, 17);
v_usedCommRing_2930_ = lean_ctor_get_uint8(v_s_2910_, sizeof(void*)*19 + 1);
v_nonlinearOccs_2931_ = lean_ctor_get(v_s_2910_, 18);
v_isSharedCheck_2939_ = !lean_is_exclusive(v_s_2910_);
if (v_isSharedCheck_2939_ == 0)
{
v___x_2933_ = v_s_2910_;
v_isShared_2934_ = v_isSharedCheck_2939_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_nonlinearOccs_2931_);
lean_inc(v_divMod_2929_);
lean_inc(v_diseqSplits_2928_);
lean_inc(v_conflict_x3f_2927_);
lean_inc(v_steps_2926_);
lean_inc(v_nextCnstrId_2924_);
lean_inc(v_assignment_2923_);
lean_inc(v_occurs_2922_);
lean_inc(v_elimStack_2921_);
lean_inc(v_elimEqs_2920_);
lean_inc(v_diseqs_2919_);
lean_inc(v_uppers_2918_);
lean_inc(v_lowers_2917_);
lean_inc(v_dvds_2916_);
lean_inc(v_natDef_2915_);
lean_inc(v_natToIntMap_2914_);
lean_inc(v_varsHistory_2913_);
lean_inc(v_varMap_2912_);
lean_inc(v_vars_2911_);
lean_dec(v_s_2910_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2939_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2935_; lean_object* v___x_2937_; 
v___x_2935_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(v_a_2908_, v_lowers_2917_, v_v_2909_);
if (v_isShared_2934_ == 0)
{
lean_ctor_set(v___x_2933_, 6, v___x_2935_);
v___x_2937_ = v___x_2933_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v_vars_2911_);
lean_ctor_set(v_reuseFailAlloc_2938_, 1, v_varMap_2912_);
lean_ctor_set(v_reuseFailAlloc_2938_, 2, v_varsHistory_2913_);
lean_ctor_set(v_reuseFailAlloc_2938_, 3, v_natToIntMap_2914_);
lean_ctor_set(v_reuseFailAlloc_2938_, 4, v_natDef_2915_);
lean_ctor_set(v_reuseFailAlloc_2938_, 5, v_dvds_2916_);
lean_ctor_set(v_reuseFailAlloc_2938_, 6, v___x_2935_);
lean_ctor_set(v_reuseFailAlloc_2938_, 7, v_uppers_2918_);
lean_ctor_set(v_reuseFailAlloc_2938_, 8, v_diseqs_2919_);
lean_ctor_set(v_reuseFailAlloc_2938_, 9, v_elimEqs_2920_);
lean_ctor_set(v_reuseFailAlloc_2938_, 10, v_elimStack_2921_);
lean_ctor_set(v_reuseFailAlloc_2938_, 11, v_occurs_2922_);
lean_ctor_set(v_reuseFailAlloc_2938_, 12, v_assignment_2923_);
lean_ctor_set(v_reuseFailAlloc_2938_, 13, v_nextCnstrId_2924_);
lean_ctor_set(v_reuseFailAlloc_2938_, 14, v_steps_2926_);
lean_ctor_set(v_reuseFailAlloc_2938_, 15, v_conflict_x3f_2927_);
lean_ctor_set(v_reuseFailAlloc_2938_, 16, v_diseqSplits_2928_);
lean_ctor_set(v_reuseFailAlloc_2938_, 17, v_divMod_2929_);
lean_ctor_set(v_reuseFailAlloc_2938_, 18, v_nonlinearOccs_2931_);
lean_ctor_set_uint8(v_reuseFailAlloc_2938_, sizeof(void*)*19, v_caseSplits_2925_);
lean_ctor_set_uint8(v_reuseFailAlloc_2938_, sizeof(void*)*19 + 1, v_usedCommRing_2930_);
v___x_2937_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
return v___x_2937_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0___boxed(lean_object* v_a_2940_, lean_object* v_v_2941_, lean_object* v_s_2942_){
_start:
{
lean_object* v_res_2943_; 
v_res_2943_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0(v_a_2940_, v_v_2941_, v_s_2942_);
lean_dec(v_v_2941_);
return v_res_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1(lean_object* v_a_2944_, lean_object* v_v_2945_, lean_object* v_s_2946_){
_start:
{
lean_object* v_vars_2947_; lean_object* v_varMap_2948_; lean_object* v_varsHistory_2949_; lean_object* v_natToIntMap_2950_; lean_object* v_natDef_2951_; lean_object* v_dvds_2952_; lean_object* v_lowers_2953_; lean_object* v_uppers_2954_; lean_object* v_diseqs_2955_; lean_object* v_elimEqs_2956_; lean_object* v_elimStack_2957_; lean_object* v_occurs_2958_; lean_object* v_assignment_2959_; lean_object* v_nextCnstrId_2960_; uint8_t v_caseSplits_2961_; lean_object* v_steps_2962_; lean_object* v_conflict_x3f_2963_; lean_object* v_diseqSplits_2964_; lean_object* v_divMod_2965_; uint8_t v_usedCommRing_2966_; lean_object* v_nonlinearOccs_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2975_; 
v_vars_2947_ = lean_ctor_get(v_s_2946_, 0);
v_varMap_2948_ = lean_ctor_get(v_s_2946_, 1);
v_varsHistory_2949_ = lean_ctor_get(v_s_2946_, 2);
v_natToIntMap_2950_ = lean_ctor_get(v_s_2946_, 3);
v_natDef_2951_ = lean_ctor_get(v_s_2946_, 4);
v_dvds_2952_ = lean_ctor_get(v_s_2946_, 5);
v_lowers_2953_ = lean_ctor_get(v_s_2946_, 6);
v_uppers_2954_ = lean_ctor_get(v_s_2946_, 7);
v_diseqs_2955_ = lean_ctor_get(v_s_2946_, 8);
v_elimEqs_2956_ = lean_ctor_get(v_s_2946_, 9);
v_elimStack_2957_ = lean_ctor_get(v_s_2946_, 10);
v_occurs_2958_ = lean_ctor_get(v_s_2946_, 11);
v_assignment_2959_ = lean_ctor_get(v_s_2946_, 12);
v_nextCnstrId_2960_ = lean_ctor_get(v_s_2946_, 13);
v_caseSplits_2961_ = lean_ctor_get_uint8(v_s_2946_, sizeof(void*)*19);
v_steps_2962_ = lean_ctor_get(v_s_2946_, 14);
v_conflict_x3f_2963_ = lean_ctor_get(v_s_2946_, 15);
v_diseqSplits_2964_ = lean_ctor_get(v_s_2946_, 16);
v_divMod_2965_ = lean_ctor_get(v_s_2946_, 17);
v_usedCommRing_2966_ = lean_ctor_get_uint8(v_s_2946_, sizeof(void*)*19 + 1);
v_nonlinearOccs_2967_ = lean_ctor_get(v_s_2946_, 18);
v_isSharedCheck_2975_ = !lean_is_exclusive(v_s_2946_);
if (v_isSharedCheck_2975_ == 0)
{
v___x_2969_ = v_s_2946_;
v_isShared_2970_ = v_isSharedCheck_2975_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_nonlinearOccs_2967_);
lean_inc(v_divMod_2965_);
lean_inc(v_diseqSplits_2964_);
lean_inc(v_conflict_x3f_2963_);
lean_inc(v_steps_2962_);
lean_inc(v_nextCnstrId_2960_);
lean_inc(v_assignment_2959_);
lean_inc(v_occurs_2958_);
lean_inc(v_elimStack_2957_);
lean_inc(v_elimEqs_2956_);
lean_inc(v_diseqs_2955_);
lean_inc(v_uppers_2954_);
lean_inc(v_lowers_2953_);
lean_inc(v_dvds_2952_);
lean_inc(v_natDef_2951_);
lean_inc(v_natToIntMap_2950_);
lean_inc(v_varsHistory_2949_);
lean_inc(v_varMap_2948_);
lean_inc(v_vars_2947_);
lean_dec(v_s_2946_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2975_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___x_2971_; lean_object* v___x_2973_; 
v___x_2971_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(v_a_2944_, v_uppers_2954_, v_v_2945_);
if (v_isShared_2970_ == 0)
{
lean_ctor_set(v___x_2969_, 7, v___x_2971_);
v___x_2973_ = v___x_2969_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v_vars_2947_);
lean_ctor_set(v_reuseFailAlloc_2974_, 1, v_varMap_2948_);
lean_ctor_set(v_reuseFailAlloc_2974_, 2, v_varsHistory_2949_);
lean_ctor_set(v_reuseFailAlloc_2974_, 3, v_natToIntMap_2950_);
lean_ctor_set(v_reuseFailAlloc_2974_, 4, v_natDef_2951_);
lean_ctor_set(v_reuseFailAlloc_2974_, 5, v_dvds_2952_);
lean_ctor_set(v_reuseFailAlloc_2974_, 6, v_lowers_2953_);
lean_ctor_set(v_reuseFailAlloc_2974_, 7, v___x_2971_);
lean_ctor_set(v_reuseFailAlloc_2974_, 8, v_diseqs_2955_);
lean_ctor_set(v_reuseFailAlloc_2974_, 9, v_elimEqs_2956_);
lean_ctor_set(v_reuseFailAlloc_2974_, 10, v_elimStack_2957_);
lean_ctor_set(v_reuseFailAlloc_2974_, 11, v_occurs_2958_);
lean_ctor_set(v_reuseFailAlloc_2974_, 12, v_assignment_2959_);
lean_ctor_set(v_reuseFailAlloc_2974_, 13, v_nextCnstrId_2960_);
lean_ctor_set(v_reuseFailAlloc_2974_, 14, v_steps_2962_);
lean_ctor_set(v_reuseFailAlloc_2974_, 15, v_conflict_x3f_2963_);
lean_ctor_set(v_reuseFailAlloc_2974_, 16, v_diseqSplits_2964_);
lean_ctor_set(v_reuseFailAlloc_2974_, 17, v_divMod_2965_);
lean_ctor_set(v_reuseFailAlloc_2974_, 18, v_nonlinearOccs_2967_);
lean_ctor_set_uint8(v_reuseFailAlloc_2974_, sizeof(void*)*19, v_caseSplits_2961_);
lean_ctor_set_uint8(v_reuseFailAlloc_2974_, sizeof(void*)*19 + 1, v_usedCommRing_2966_);
v___x_2973_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
return v___x_2973_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1___boxed(lean_object* v_a_2976_, lean_object* v_v_2977_, lean_object* v_s_2978_){
_start:
{
lean_object* v_res_2979_; 
v_res_2979_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1(v_a_2976_, v_v_2977_, v_s_2978_);
lean_dec(v_v_2977_);
return v_res_2979_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3(void){
_start:
{
lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2987_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2));
v___x_2988_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_2989_ = l_Lean_Name_append(v___x_2988_, v___x_2987_);
return v___x_2989_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6(void){
_start:
{
lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2996_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5));
v___x_2997_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_2998_ = l_Lean_Name_append(v___x_2997_, v___x_2996_);
return v___x_2998_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9(void){
_start:
{
lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; 
v___x_3005_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__8));
v___x_3006_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_3007_ = l_Lean_Name_append(v___x_3006_, v___x_3005_);
return v___x_3007_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11(void){
_start:
{
lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
v___x_3012_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__10));
v___x_3013_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_3014_ = l_Lean_Name_append(v___x_3013_, v___x_3012_);
return v___x_3014_;
}
}
lean_object* lean_grind_cutsat_assert_le(lean_object* v_c_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_, lean_object* v_a_3018_, lean_object* v_a_3019_, lean_object* v_a_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_, lean_object* v_a_3023_, lean_object* v_a_3024_, lean_object* v_a_3025_){
_start:
{
lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3058_; lean_object* v___y_3059_; lean_object* v___y_3060_; lean_object* v___y_3061_; lean_object* v___y_3062_; lean_object* v___y_3063_; lean_object* v___y_3064_; lean_object* v___y_3065_; lean_object* v___y_3066_; lean_object* v___y_3067_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; lean_object* v___y_3087_; lean_object* v___x_3099_; 
v___x_3099_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_3016_, v_a_3024_);
if (lean_obj_tag(v___x_3099_) == 0)
{
lean_object* v_a_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3240_; 
v_a_3100_ = lean_ctor_get(v___x_3099_, 0);
v_isSharedCheck_3240_ = !lean_is_exclusive(v___x_3099_);
if (v_isSharedCheck_3240_ == 0)
{
v___x_3102_ = v___x_3099_;
v_isShared_3103_ = v_isSharedCheck_3240_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_a_3100_);
lean_dec(v___x_3099_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3240_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
uint8_t v___x_3104_; 
v___x_3104_ = lean_unbox(v_a_3100_);
lean_dec(v_a_3100_);
if (v___x_3104_ == 0)
{
lean_object* v_toCold_3105_; lean_object* v_options_3106_; lean_object* v_inheritedTraceOptions_3107_; uint8_t v_hasTrace_3108_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; 
lean_del_object(v___x_3102_);
v_toCold_3105_ = lean_ctor_get(v_a_3024_, 0);
v_options_3106_ = lean_ctor_get(v_toCold_3105_, 2);
v_inheritedTraceOptions_3107_ = lean_ctor_get(v_toCold_3105_, 11);
v_hasTrace_3108_ = lean_ctor_get_uint8(v_options_3106_, sizeof(void*)*1);
if (v_hasTrace_3108_ == 0)
{
v___y_3110_ = v_a_3016_;
v___y_3111_ = v_a_3017_;
v___y_3112_ = v_a_3018_;
v___y_3113_ = v_a_3019_;
v___y_3114_ = v_a_3020_;
v___y_3115_ = v_a_3021_;
v___y_3116_ = v_a_3022_;
v___y_3117_ = v_a_3023_;
v___y_3118_ = v_a_3024_;
v___y_3119_ = v_a_3025_;
goto v___jp_3109_;
}
else
{
lean_object* v___x_3222_; lean_object* v___x_3223_; uint8_t v___x_3224_; 
v___x_3222_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__10));
v___x_3223_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11);
v___x_3224_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3107_, v_options_3106_, v___x_3223_);
if (v___x_3224_ == 0)
{
v___y_3110_ = v_a_3016_;
v___y_3111_ = v_a_3017_;
v___y_3112_ = v_a_3018_;
v___y_3113_ = v_a_3019_;
v___y_3114_ = v_a_3020_;
v___y_3115_ = v_a_3021_;
v___y_3116_ = v_a_3022_;
v___y_3117_ = v_a_3023_;
v___y_3118_ = v_a_3024_;
v___y_3119_ = v_a_3025_;
goto v___jp_3109_;
}
else
{
lean_object* v___x_3225_; 
lean_inc_ref(v_c_3015_);
v___x_3225_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_3015_, v_a_3016_, v_a_3024_);
if (lean_obj_tag(v___x_3225_) == 0)
{
lean_object* v_a_3226_; lean_object* v___x_3227_; 
v_a_3226_ = lean_ctor_get(v___x_3225_, 0);
lean_inc(v_a_3226_);
lean_dec_ref_known(v___x_3225_, 1);
v___x_3227_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3222_, v_a_3226_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_);
if (lean_obj_tag(v___x_3227_) == 0)
{
lean_dec_ref_known(v___x_3227_, 1);
v___y_3110_ = v_a_3016_;
v___y_3111_ = v_a_3017_;
v___y_3112_ = v_a_3018_;
v___y_3113_ = v_a_3019_;
v___y_3114_ = v_a_3020_;
v___y_3115_ = v_a_3021_;
v___y_3116_ = v_a_3022_;
v___y_3117_ = v_a_3023_;
v___y_3118_ = v_a_3024_;
v___y_3119_ = v_a_3025_;
goto v___jp_3109_;
}
else
{
lean_dec(v_a_3025_);
lean_dec_ref(v_a_3024_);
lean_dec(v_a_3023_);
lean_dec_ref(v_a_3022_);
lean_dec(v_a_3021_);
lean_dec_ref(v_a_3020_);
lean_dec(v_a_3019_);
lean_dec_ref(v_a_3018_);
lean_dec(v_a_3017_);
lean_dec(v_a_3016_);
lean_dec_ref(v_c_3015_);
return v___x_3227_;
}
}
else
{
lean_object* v_a_3228_; lean_object* v___x_3230_; uint8_t v_isShared_3231_; uint8_t v_isSharedCheck_3235_; 
lean_dec(v_a_3025_);
lean_dec_ref(v_a_3024_);
lean_dec(v_a_3023_);
lean_dec_ref(v_a_3022_);
lean_dec(v_a_3021_);
lean_dec_ref(v_a_3020_);
lean_dec(v_a_3019_);
lean_dec_ref(v_a_3018_);
lean_dec(v_a_3017_);
lean_dec(v_a_3016_);
lean_dec_ref(v_c_3015_);
v_a_3228_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3235_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3230_ = v___x_3225_;
v_isShared_3231_ = v_isSharedCheck_3235_;
goto v_resetjp_3229_;
}
else
{
lean_inc(v_a_3228_);
lean_dec(v___x_3225_);
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
v___jp_3109_:
{
lean_object* v___x_3120_; lean_object* v___x_3121_; 
v___x_3120_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_norm(v_c_3015_);
lean_inc_ref(v___y_3118_);
v___x_3121_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts(v___x_3120_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_);
if (lean_obj_tag(v___x_3121_) == 0)
{
lean_object* v_a_3122_; lean_object* v_p_3123_; uint8_t v___x_3124_; 
v_a_3122_ = lean_ctor_get(v___x_3121_, 0);
lean_inc(v_a_3122_);
lean_dec_ref_known(v___x_3121_, 1);
v_p_3123_ = lean_ctor_get(v_a_3122_, 0);
v___x_3124_ = l_Int_Internal_Linear_Poly_isUnsatLe(v_p_3123_);
if (v___x_3124_ == 0)
{
uint8_t v___x_3125_; 
v___x_3125_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(v_a_3122_);
if (v___x_3125_ == 0)
{
if (lean_obj_tag(v_p_3123_) == 1)
{
lean_object* v_k_3126_; lean_object* v_v_3127_; lean_object* v___x_3128_; 
v_k_3126_ = lean_ctor_get(v_p_3123_, 0);
lean_inc(v_k_3126_);
v_v_3127_ = lean_ctor_get(v_p_3123_, 1);
lean_inc(v_v_3127_);
lean_inc(v_a_3122_);
v___x_3128_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq(v_a_3122_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_);
if (lean_obj_tag(v___x_3128_) == 0)
{
lean_object* v_a_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3168_; 
v_a_3129_ = lean_ctor_get(v___x_3128_, 0);
v_isSharedCheck_3168_ = !lean_is_exclusive(v___x_3128_);
if (v_isSharedCheck_3168_ == 0)
{
v___x_3131_ = v___x_3128_;
v_isShared_3132_ = v_isSharedCheck_3168_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_a_3129_);
lean_dec(v___x_3128_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3168_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
uint8_t v___x_3133_; 
v___x_3133_ = lean_unbox(v_a_3129_);
lean_dec(v_a_3129_);
if (v___x_3133_ == 0)
{
lean_object* v___x_3134_; 
lean_del_object(v___x_3131_);
v___x_3134_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(v_a_3122_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_);
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec(v___y_3111_);
if (lean_obj_tag(v___x_3134_) == 0)
{
lean_object* v_toCold_3135_; lean_object* v_options_3136_; lean_object* v_a_3137_; lean_object* v_inheritedTraceOptions_3138_; uint8_t v_hasTrace_3139_; lean_object* v___f_3140_; lean_object* v___f_3141_; 
v_toCold_3135_ = lean_ctor_get(v___y_3118_, 0);
v_options_3136_ = lean_ctor_get(v_toCold_3135_, 2);
v_a_3137_ = lean_ctor_get(v___x_3134_, 0);
lean_inc_n(v_a_3137_, 3);
lean_dec_ref_known(v___x_3134_, 1);
v_inheritedTraceOptions_3138_ = lean_ctor_get(v_toCold_3135_, 11);
v_hasTrace_3139_ = lean_ctor_get_uint8(v_options_3136_, sizeof(void*)*1);
lean_inc_n(v_v_3127_, 2);
v___f_3140_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3140_, 0, v_a_3137_);
lean_closure_set(v___f_3140_, 1, v_v_3127_);
v___f_3141_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3141_, 0, v_a_3137_);
lean_closure_set(v___f_3141_, 1, v_v_3127_);
if (v_hasTrace_3139_ == 0)
{
v___y_3058_ = v___f_3141_;
v___y_3059_ = v___f_3140_;
v___y_3060_ = v_v_3127_;
v___y_3061_ = v_a_3137_;
v___y_3062_ = v_k_3126_;
v___y_3063_ = v___y_3110_;
v___y_3064_ = v___y_3116_;
v___y_3065_ = v___y_3117_;
v___y_3066_ = v___y_3118_;
v___y_3067_ = v___y_3119_;
goto v___jp_3057_;
}
else
{
lean_object* v___x_3142_; lean_object* v___x_3143_; uint8_t v___x_3144_; 
v___x_3142_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2));
v___x_3143_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3);
v___x_3144_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3138_, v_options_3136_, v___x_3143_);
if (v___x_3144_ == 0)
{
v___y_3058_ = v___f_3141_;
v___y_3059_ = v___f_3140_;
v___y_3060_ = v_v_3127_;
v___y_3061_ = v_a_3137_;
v___y_3062_ = v_k_3126_;
v___y_3063_ = v___y_3110_;
v___y_3064_ = v___y_3116_;
v___y_3065_ = v___y_3117_;
v___y_3066_ = v___y_3118_;
v___y_3067_ = v___y_3119_;
goto v___jp_3057_;
}
else
{
lean_object* v___x_3145_; 
lean_inc(v_a_3137_);
v___x_3145_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_a_3137_, v___y_3110_, v___y_3118_);
if (lean_obj_tag(v___x_3145_) == 0)
{
lean_object* v_a_3146_; lean_object* v___x_3147_; 
v_a_3146_ = lean_ctor_get(v___x_3145_, 0);
lean_inc(v_a_3146_);
lean_dec_ref_known(v___x_3145_, 1);
v___x_3147_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3142_, v_a_3146_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_);
if (lean_obj_tag(v___x_3147_) == 0)
{
lean_dec_ref_known(v___x_3147_, 1);
v___y_3058_ = v___f_3141_;
v___y_3059_ = v___f_3140_;
v___y_3060_ = v_v_3127_;
v___y_3061_ = v_a_3137_;
v___y_3062_ = v_k_3126_;
v___y_3063_ = v___y_3110_;
v___y_3064_ = v___y_3116_;
v___y_3065_ = v___y_3117_;
v___y_3066_ = v___y_3118_;
v___y_3067_ = v___y_3119_;
goto v___jp_3057_;
}
else
{
lean_dec_ref(v___f_3141_);
lean_dec_ref(v___f_3140_);
lean_dec(v_a_3137_);
lean_dec(v_v_3127_);
lean_dec(v_k_3126_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec(v___y_3110_);
return v___x_3147_;
}
}
else
{
lean_object* v_a_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3155_; 
lean_dec_ref(v___f_3141_);
lean_dec_ref(v___f_3140_);
lean_dec(v_a_3137_);
lean_dec(v_v_3127_);
lean_dec(v_k_3126_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec(v___y_3110_);
v_a_3148_ = lean_ctor_get(v___x_3145_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_3145_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3150_ = v___x_3145_;
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_a_3148_);
lean_dec(v___x_3145_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3153_; 
if (v_isShared_3151_ == 0)
{
v___x_3153_ = v___x_3150_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_a_3148_);
v___x_3153_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
return v___x_3153_;
}
}
}
}
}
}
else
{
lean_object* v_a_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3163_; 
lean_dec(v_v_3127_);
lean_dec(v_k_3126_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec(v___y_3110_);
v_a_3156_ = lean_ctor_get(v___x_3134_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3158_ = v___x_3134_;
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_a_3156_);
lean_dec(v___x_3134_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3161_; 
if (v_isShared_3159_ == 0)
{
v___x_3161_ = v___x_3158_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_a_3156_);
v___x_3161_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
return v___x_3161_;
}
}
}
}
else
{
lean_object* v___x_3164_; lean_object* v___x_3166_; 
lean_dec(v_v_3127_);
lean_dec(v_k_3126_);
lean_dec(v_a_3122_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec(v___y_3111_);
lean_dec(v___y_3110_);
v___x_3164_ = lean_box(0);
if (v_isShared_3132_ == 0)
{
lean_ctor_set(v___x_3131_, 0, v___x_3164_);
v___x_3166_ = v___x_3131_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v___x_3164_);
v___x_3166_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
return v___x_3166_;
}
}
}
}
else
{
lean_object* v_a_3169_; lean_object* v___x_3171_; uint8_t v_isShared_3172_; uint8_t v_isSharedCheck_3176_; 
lean_dec(v_v_3127_);
lean_dec(v_k_3126_);
lean_dec(v_a_3122_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec(v___y_3111_);
lean_dec(v___y_3110_);
v_a_3169_ = lean_ctor_get(v___x_3128_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3128_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3171_ = v___x_3128_;
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
else
{
lean_inc(v_a_3169_);
lean_dec(v___x_3128_);
v___x_3171_ = lean_box(0);
v_isShared_3172_ = v_isSharedCheck_3176_;
goto v_resetjp_3170_;
}
v_resetjp_3170_:
{
lean_object* v___x_3174_; 
if (v_isShared_3172_ == 0)
{
v___x_3174_ = v___x_3171_;
goto v_reusejp_3173_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v_a_3169_);
v___x_3174_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3173_;
}
v_reusejp_3173_:
{
return v___x_3174_;
}
}
}
}
else
{
lean_object* v___x_3177_; 
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec(v___y_3111_);
v___x_3177_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_a_3122_, v___y_3110_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec(v___y_3110_);
return v___x_3177_;
}
}
else
{
lean_object* v_toCold_3178_; lean_object* v_options_3179_; uint8_t v_hasTrace_3180_; 
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec(v___y_3111_);
v_toCold_3178_ = lean_ctor_get(v___y_3118_, 0);
v_options_3179_ = lean_ctor_get(v_toCold_3178_, 2);
v_hasTrace_3180_ = lean_ctor_get_uint8(v_options_3179_, sizeof(void*)*1);
if (v_hasTrace_3180_ == 0)
{
lean_dec(v_a_3122_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec(v___y_3110_);
goto v___jp_3027_;
}
else
{
lean_object* v_inheritedTraceOptions_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; uint8_t v___x_3184_; 
v_inheritedTraceOptions_3181_ = lean_ctor_get(v_toCold_3178_, 11);
v___x_3182_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5));
v___x_3183_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6);
v___x_3184_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3181_, v_options_3179_, v___x_3183_);
if (v___x_3184_ == 0)
{
lean_dec(v_a_3122_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec(v___y_3110_);
goto v___jp_3027_;
}
else
{
lean_object* v___x_3185_; 
v___x_3185_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_a_3122_, v___y_3110_, v___y_3118_);
lean_dec(v___y_3110_);
if (lean_obj_tag(v___x_3185_) == 0)
{
lean_object* v_a_3186_; lean_object* v___x_3187_; 
v_a_3186_ = lean_ctor_get(v___x_3185_, 0);
lean_inc(v_a_3186_);
lean_dec_ref_known(v___x_3185_, 1);
v___x_3187_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3182_, v_a_3186_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
if (lean_obj_tag(v___x_3187_) == 0)
{
lean_dec_ref_known(v___x_3187_, 1);
goto v___jp_3027_;
}
else
{
return v___x_3187_;
}
}
else
{
lean_object* v_a_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3195_; 
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
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
}
else
{
lean_object* v_toCold_3196_; lean_object* v_options_3197_; uint8_t v_hasTrace_3198_; 
v_toCold_3196_ = lean_ctor_get(v___y_3118_, 0);
v_options_3197_ = lean_ctor_get(v_toCold_3196_, 2);
v_hasTrace_3198_ = lean_ctor_get_uint8(v_options_3197_, sizeof(void*)*1);
if (v_hasTrace_3198_ == 0)
{
v___y_3077_ = v_a_3122_;
v___y_3078_ = v___y_3110_;
v___y_3079_ = v___y_3111_;
v___y_3080_ = v___y_3112_;
v___y_3081_ = v___y_3113_;
v___y_3082_ = v___y_3114_;
v___y_3083_ = v___y_3115_;
v___y_3084_ = v___y_3116_;
v___y_3085_ = v___y_3117_;
v___y_3086_ = v___y_3118_;
v___y_3087_ = v___y_3119_;
goto v___jp_3076_;
}
else
{
lean_object* v_inheritedTraceOptions_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; uint8_t v___x_3202_; 
v_inheritedTraceOptions_3199_ = lean_ctor_get(v_toCold_3196_, 11);
v___x_3200_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__8));
v___x_3201_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9);
v___x_3202_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3199_, v_options_3197_, v___x_3201_);
if (v___x_3202_ == 0)
{
v___y_3077_ = v_a_3122_;
v___y_3078_ = v___y_3110_;
v___y_3079_ = v___y_3111_;
v___y_3080_ = v___y_3112_;
v___y_3081_ = v___y_3113_;
v___y_3082_ = v___y_3114_;
v___y_3083_ = v___y_3115_;
v___y_3084_ = v___y_3116_;
v___y_3085_ = v___y_3117_;
v___y_3086_ = v___y_3118_;
v___y_3087_ = v___y_3119_;
goto v___jp_3076_;
}
else
{
lean_object* v___x_3203_; 
lean_inc(v_a_3122_);
v___x_3203_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_a_3122_, v___y_3110_, v___y_3118_);
if (lean_obj_tag(v___x_3203_) == 0)
{
lean_object* v_a_3204_; lean_object* v___x_3205_; 
v_a_3204_ = lean_ctor_get(v___x_3203_, 0);
lean_inc(v_a_3204_);
lean_dec_ref_known(v___x_3203_, 1);
v___x_3205_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3200_, v_a_3204_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_);
if (lean_obj_tag(v___x_3205_) == 0)
{
lean_dec_ref_known(v___x_3205_, 1);
v___y_3077_ = v_a_3122_;
v___y_3078_ = v___y_3110_;
v___y_3079_ = v___y_3111_;
v___y_3080_ = v___y_3112_;
v___y_3081_ = v___y_3113_;
v___y_3082_ = v___y_3114_;
v___y_3083_ = v___y_3115_;
v___y_3084_ = v___y_3116_;
v___y_3085_ = v___y_3117_;
v___y_3086_ = v___y_3118_;
v___y_3087_ = v___y_3119_;
goto v___jp_3076_;
}
else
{
lean_dec(v_a_3122_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec(v___y_3111_);
lean_dec(v___y_3110_);
return v___x_3205_;
}
}
else
{
lean_object* v_a_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3213_; 
lean_dec(v_a_3122_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec(v___y_3111_);
lean_dec(v___y_3110_);
v_a_3206_ = lean_ctor_get(v___x_3203_, 0);
v_isSharedCheck_3213_ = !lean_is_exclusive(v___x_3203_);
if (v_isSharedCheck_3213_ == 0)
{
v___x_3208_ = v___x_3203_;
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_a_3206_);
lean_dec(v___x_3203_);
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
}
}
}
else
{
lean_object* v_a_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3221_; 
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec(v___y_3117_);
lean_dec_ref(v___y_3116_);
lean_dec(v___y_3115_);
lean_dec_ref(v___y_3114_);
lean_dec(v___y_3113_);
lean_dec_ref(v___y_3112_);
lean_dec(v___y_3111_);
lean_dec(v___y_3110_);
v_a_3214_ = lean_ctor_get(v___x_3121_, 0);
v_isSharedCheck_3221_ = !lean_is_exclusive(v___x_3121_);
if (v_isSharedCheck_3221_ == 0)
{
v___x_3216_ = v___x_3121_;
v_isShared_3217_ = v_isSharedCheck_3221_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_a_3214_);
lean_dec(v___x_3121_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3221_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v___x_3219_; 
if (v_isShared_3217_ == 0)
{
v___x_3219_ = v___x_3216_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v_a_3214_);
v___x_3219_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
return v___x_3219_;
}
}
}
}
}
else
{
lean_object* v___x_3236_; lean_object* v___x_3238_; 
lean_dec(v_a_3025_);
lean_dec_ref(v_a_3024_);
lean_dec(v_a_3023_);
lean_dec_ref(v_a_3022_);
lean_dec(v_a_3021_);
lean_dec_ref(v_a_3020_);
lean_dec(v_a_3019_);
lean_dec_ref(v_a_3018_);
lean_dec(v_a_3017_);
lean_dec(v_a_3016_);
lean_dec_ref(v_c_3015_);
v___x_3236_ = lean_box(0);
if (v_isShared_3103_ == 0)
{
lean_ctor_set(v___x_3102_, 0, v___x_3236_);
v___x_3238_ = v___x_3102_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v___x_3236_);
v___x_3238_ = v_reuseFailAlloc_3239_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
return v___x_3238_;
}
}
}
}
else
{
lean_object* v_a_3241_; lean_object* v___x_3243_; uint8_t v_isShared_3244_; uint8_t v_isSharedCheck_3248_; 
lean_dec(v_a_3025_);
lean_dec_ref(v_a_3024_);
lean_dec(v_a_3023_);
lean_dec_ref(v_a_3022_);
lean_dec(v_a_3021_);
lean_dec_ref(v_a_3020_);
lean_dec(v_a_3019_);
lean_dec_ref(v_a_3018_);
lean_dec(v_a_3017_);
lean_dec(v_a_3016_);
lean_dec_ref(v_c_3015_);
v_a_3241_ = lean_ctor_get(v___x_3099_, 0);
v_isSharedCheck_3248_ = !lean_is_exclusive(v___x_3099_);
if (v_isSharedCheck_3248_ == 0)
{
v___x_3243_ = v___x_3099_;
v_isShared_3244_ = v_isSharedCheck_3248_;
goto v_resetjp_3242_;
}
else
{
lean_inc(v_a_3241_);
lean_dec(v___x_3099_);
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
v___jp_3027_:
{
lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3028_ = lean_box(0);
v___x_3029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3028_);
return v___x_3029_;
}
v___jp_3030_:
{
lean_object* v___x_3035_; 
v___x_3035_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(v___y_3032_, v___y_3033_, v___y_3034_);
lean_dec_ref(v___y_3034_);
if (lean_obj_tag(v___x_3035_) == 0)
{
lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3048_; 
v_a_3036_ = lean_ctor_get(v___x_3035_, 0);
v_isSharedCheck_3048_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3048_ == 0)
{
v___x_3038_ = v___x_3035_;
v_isShared_3039_ = v_isSharedCheck_3048_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v___x_3035_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3048_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
uint8_t v___x_3040_; uint8_t v___x_3041_; uint8_t v___x_3042_; 
v___x_3040_ = 0;
v___x_3041_ = lean_unbox(v_a_3036_);
lean_dec(v_a_3036_);
v___x_3042_ = l_Lean_instBEqLBool_beq(v___x_3041_, v___x_3040_);
if (v___x_3042_ == 0)
{
lean_object* v___x_3043_; lean_object* v___x_3045_; 
lean_dec(v___y_3033_);
lean_dec(v___y_3031_);
v___x_3043_ = lean_box(0);
if (v_isShared_3039_ == 0)
{
lean_ctor_set(v___x_3038_, 0, v___x_3043_);
v___x_3045_ = v___x_3038_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v___x_3043_);
v___x_3045_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
return v___x_3045_;
}
}
else
{
lean_object* v___x_3047_; 
lean_del_object(v___x_3038_);
v___x_3047_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v___y_3031_, v___y_3033_);
lean_dec(v___y_3033_);
return v___x_3047_;
}
}
}
else
{
lean_object* v_a_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3056_; 
lean_dec(v___y_3033_);
lean_dec(v___y_3031_);
v_a_3049_ = lean_ctor_get(v___x_3035_, 0);
v_isSharedCheck_3056_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_3051_ = v___x_3035_;
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_a_3049_);
lean_dec(v___x_3035_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3054_; 
if (v_isShared_3052_ == 0)
{
v___x_3054_ = v___x_3051_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_a_3049_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
}
}
}
}
v___jp_3057_:
{
lean_object* v_p_3068_; lean_object* v___x_3069_; 
v_p_3068_ = lean_ctor_get(v___y_3061_, 0);
lean_inc_ref(v_p_3068_);
v___x_3069_ = l_Int_Internal_Linear_Poly_updateOccs___redArg(v_p_3068_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_);
lean_dec(v___y_3067_);
lean_dec(v___y_3065_);
lean_dec_ref(v___y_3064_);
if (lean_obj_tag(v___x_3069_) == 0)
{
lean_object* v___x_3070_; uint8_t v___x_3071_; 
lean_dec_ref_known(v___x_3069_, 1);
v___x_3070_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9);
v___x_3071_ = lean_int_dec_lt(v___y_3062_, v___x_3070_);
lean_dec(v___y_3062_);
if (v___x_3071_ == 0)
{
lean_object* v___x_3072_; lean_object* v___x_3073_; 
lean_dec_ref(v___y_3059_);
v___x_3072_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_3073_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3072_, v___y_3058_, v___y_3063_);
if (lean_obj_tag(v___x_3073_) == 0)
{
lean_dec_ref_known(v___x_3073_, 1);
v___y_3031_ = v___y_3060_;
v___y_3032_ = v___y_3061_;
v___y_3033_ = v___y_3063_;
v___y_3034_ = v___y_3066_;
goto v___jp_3030_;
}
else
{
lean_dec_ref(v___y_3066_);
lean_dec(v___y_3063_);
lean_dec_ref(v___y_3061_);
lean_dec(v___y_3060_);
return v___x_3073_;
}
}
else
{
lean_object* v___x_3074_; lean_object* v___x_3075_; 
lean_dec_ref(v___y_3058_);
v___x_3074_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_3075_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3074_, v___y_3059_, v___y_3063_);
if (lean_obj_tag(v___x_3075_) == 0)
{
lean_dec_ref_known(v___x_3075_, 1);
v___y_3031_ = v___y_3060_;
v___y_3032_ = v___y_3061_;
v___y_3033_ = v___y_3063_;
v___y_3034_ = v___y_3066_;
goto v___jp_3030_;
}
else
{
lean_dec_ref(v___y_3066_);
lean_dec(v___y_3063_);
lean_dec_ref(v___y_3061_);
lean_dec(v___y_3060_);
return v___x_3075_;
}
}
}
else
{
lean_dec_ref(v___y_3066_);
lean_dec(v___y_3063_);
lean_dec(v___y_3062_);
lean_dec_ref(v___y_3061_);
lean_dec(v___y_3060_);
lean_dec_ref(v___y_3059_);
lean_dec_ref(v___y_3058_);
return v___x_3069_;
}
}
v___jp_3076_:
{
lean_object* v___x_3088_; lean_object* v___x_3089_; 
v___x_3088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3088_, 0, v___y_3077_);
v___x_3089_ = l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(v___x_3088_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_);
lean_dec(v___y_3087_);
lean_dec_ref(v___y_3086_);
lean_dec(v___y_3085_);
lean_dec_ref(v___y_3084_);
lean_dec(v___y_3083_);
lean_dec_ref(v___y_3082_);
lean_dec(v___y_3081_);
lean_dec_ref(v___y_3080_);
lean_dec(v___y_3079_);
lean_dec(v___y_3078_);
if (lean_obj_tag(v___x_3089_) == 0)
{
lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3097_; 
v_isSharedCheck_3097_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3097_ == 0)
{
lean_object* v_unused_3098_; 
v_unused_3098_ = lean_ctor_get(v___x_3089_, 0);
lean_dec(v_unused_3098_);
v___x_3091_ = v___x_3089_;
v_isShared_3092_ = v_isSharedCheck_3097_;
goto v_resetjp_3090_;
}
else
{
lean_dec(v___x_3089_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3097_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3093_; lean_object* v___x_3095_; 
v___x_3093_ = lean_box(0);
if (v_isShared_3092_ == 0)
{
lean_ctor_set(v___x_3091_, 0, v___x_3093_);
v___x_3095_ = v___x_3091_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v___x_3093_);
v___x_3095_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
return v___x_3095_;
}
}
}
else
{
return v___x_3089_;
}
}
}
}
LEAN_EXPORT void lean_grind_cutsat_assert_le_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_3015_ = stack[0].m_obj;
lean_object* v_a_3016_ = stack[1].m_obj;
lean_object* v_a_3017_ = stack[2].m_obj;
lean_object* v_a_3018_ = stack[3].m_obj;
lean_object* v_a_3019_ = stack[4].m_obj;
lean_object* v_a_3020_ = stack[5].m_obj;
lean_object* v_a_3021_ = stack[6].m_obj;
lean_object* v_a_3022_ = stack[7].m_obj;
lean_object* v_a_3023_ = stack[8].m_obj;
lean_object* v_a_3024_ = stack[9].m_obj;
lean_object* v_a_3025_ = stack[10].m_obj;
lean_object* v_res_3249_;
v_res_3249_ = lean_grind_cutsat_assert_le(v_c_3015_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_, v_a_3021_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_);
stack->m_obj
 = v_res_3249_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___boxed(lean_object* v_c_3250_, lean_object* v_a_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_, lean_object* v_a_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_){
_start:
{
lean_object* v_res_3262_; 
v_res_3262_ = lean_grind_cutsat_assert_le(v_c_3250_, v_a_3251_, v_a_3252_, v_a_3253_, v_a_3254_, v_a_3255_, v_a_3256_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_);
return v_res_3262_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1(void){
_start:
{
lean_object* v___x_3264_; lean_object* v___x_3265_; 
v___x_3264_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__0));
v___x_3265_ = l_Lean_stringToMessageData(v___x_3264_);
return v___x_3265_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(lean_object* v_e_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_, lean_object* v_a_3272_){
_start:
{
lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
v___x_3274_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1);
v___x_3275_ = l_Lean_indentExpr(v_e_3266_);
v___x_3276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3276_, 0, v___x_3274_);
lean_ctor_set(v___x_3276_, 1, v___x_3275_);
v___x_3277_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_3267_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_object* v_a_3278_; lean_object* v___x_3280_; uint8_t v_isShared_3281_; uint8_t v_isSharedCheck_3288_; 
v_a_3278_ = lean_ctor_get(v___x_3277_, 0);
v_isSharedCheck_3288_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3280_ = v___x_3277_;
v_isShared_3281_ = v_isSharedCheck_3288_;
goto v_resetjp_3279_;
}
else
{
lean_inc(v_a_3278_);
lean_dec(v___x_3277_);
v___x_3280_ = lean_box(0);
v_isShared_3281_ = v_isSharedCheck_3288_;
goto v_resetjp_3279_;
}
v_resetjp_3279_:
{
uint8_t v_verbose_3282_; 
v_verbose_3282_ = lean_ctor_get_uint8(v_a_3278_, 0);
lean_dec(v_a_3278_);
if (v_verbose_3282_ == 0)
{
lean_object* v___x_3283_; lean_object* v___x_3285_; 
lean_dec_ref_known(v___x_3276_, 2);
v___x_3283_ = lean_box(0);
if (v_isShared_3281_ == 0)
{
lean_ctor_set(v___x_3280_, 0, v___x_3283_);
v___x_3285_ = v___x_3280_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v___x_3283_);
v___x_3285_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
return v___x_3285_;
}
}
else
{
lean_object* v___x_3287_; 
lean_del_object(v___x_3280_);
v___x_3287_ = l_Lean_Meta_Sym_reportIssue(v___x_3276_, v_a_3267_, v_a_3268_, v_a_3269_, v_a_3270_, v_a_3271_, v_a_3272_);
return v___x_3287_;
}
}
}
else
{
lean_object* v_a_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3296_; 
lean_dec_ref_known(v___x_3276_, 2);
v_a_3289_ = lean_ctor_get(v___x_3277_, 0);
v_isSharedCheck_3296_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3296_ == 0)
{
v___x_3291_ = v___x_3277_;
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_a_3289_);
lean_dec(v___x_3277_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3294_; 
if (v_isShared_3292_ == 0)
{
v___x_3294_ = v___x_3291_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v_a_3289_);
v___x_3294_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
return v___x_3294_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3266_ = stack[0].m_obj;
lean_object* v_a_3267_ = stack[1].m_obj;
lean_object* v_a_3268_ = stack[2].m_obj;
lean_object* v_a_3269_ = stack[3].m_obj;
lean_object* v_a_3270_ = stack[4].m_obj;
lean_object* v_a_3271_ = stack[5].m_obj;
lean_object* v_a_3272_ = stack[6].m_obj;
lean_object* v_res_3297_;
v_res_3297_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(v_e_3266_, v_a_3267_, v_a_3268_, v_a_3269_, v_a_3270_, v_a_3271_, v_a_3272_);
stack->m_obj
 = v_res_3297_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___boxed(lean_object* v_e_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_){
_start:
{
lean_object* v_res_3306_; 
v_res_3306_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(v_e_3298_, v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_, v_a_3303_, v_a_3304_);
lean_dec(v_a_3304_);
lean_dec_ref(v_a_3303_);
lean_dec(v_a_3302_);
lean_dec_ref(v_a_3301_);
lean_dec(v_a_3300_);
lean_dec_ref(v_a_3299_);
return v_res_3306_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized(lean_object* v_e_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_, lean_object* v_a_3317_){
_start:
{
lean_object* v___x_3319_; 
v___x_3319_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(v_e_3307_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_);
return v___x_3319_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3307_ = stack[0].m_obj;
lean_object* v_a_3308_ = stack[1].m_obj;
lean_object* v_a_3309_ = stack[2].m_obj;
lean_object* v_a_3310_ = stack[3].m_obj;
lean_object* v_a_3311_ = stack[4].m_obj;
lean_object* v_a_3312_ = stack[5].m_obj;
lean_object* v_a_3313_ = stack[6].m_obj;
lean_object* v_a_3314_ = stack[7].m_obj;
lean_object* v_a_3315_ = stack[8].m_obj;
lean_object* v_a_3316_ = stack[9].m_obj;
lean_object* v_a_3317_ = stack[10].m_obj;
lean_object* v_res_3320_;
v_res_3320_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized(v_e_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_);
stack->m_obj
 = v_res_3320_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___boxed(lean_object* v_e_3321_, lean_object* v_a_3322_, lean_object* v_a_3323_, lean_object* v_a_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_, lean_object* v_a_3329_, lean_object* v_a_3330_, lean_object* v_a_3331_, lean_object* v_a_3332_){
_start:
{
lean_object* v_res_3333_; 
v_res_3333_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized(v_e_3321_, v_a_3322_, v_a_3323_, v_a_3324_, v_a_3325_, v_a_3326_, v_a_3327_, v_a_3328_, v_a_3329_, v_a_3330_, v_a_3331_);
lean_dec(v_a_3331_);
lean_dec_ref(v_a_3330_);
lean_dec(v_a_3329_);
lean_dec_ref(v_a_3328_);
lean_dec(v_a_3327_);
lean_dec_ref(v_a_3326_);
lean_dec(v_a_3325_);
lean_dec_ref(v_a_3324_);
lean_dec(v_a_3323_);
lean_dec(v_a_3322_);
return v_res_3333_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f(lean_object* v_e_3339_, lean_object* v_a_3340_, lean_object* v_a_3341_, lean_object* v_a_3342_, lean_object* v_a_3343_, lean_object* v_a_3344_, lean_object* v_a_3345_, lean_object* v_a_3346_, lean_object* v_a_3347_, lean_object* v_a_3348_, lean_object* v_a_3349_){
_start:
{
lean_object* v___x_3354_; 
lean_inc_ref(v_e_3339_);
v___x_3354_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3339_, v_a_3347_);
if (lean_obj_tag(v___x_3354_) == 0)
{
lean_object* v_a_3355_; lean_object* v___x_3356_; uint8_t v___x_3357_; 
v_a_3355_ = lean_ctor_get(v___x_3354_, 0);
lean_inc(v_a_3355_);
lean_dec_ref_known(v___x_3354_, 1);
v___x_3356_ = l_Lean_Expr_cleanupAnnotations(v_a_3355_);
v___x_3357_ = l_Lean_Expr_isApp(v___x_3356_);
if (v___x_3357_ == 0)
{
lean_dec_ref(v___x_3356_);
lean_dec_ref(v_e_3339_);
goto v___jp_3351_;
}
else
{
lean_object* v_arg_3358_; lean_object* v___x_3359_; uint8_t v___x_3360_; 
v_arg_3358_ = lean_ctor_get(v___x_3356_, 1);
lean_inc_ref(v_arg_3358_);
v___x_3359_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3356_);
v___x_3360_ = l_Lean_Expr_isApp(v___x_3359_);
if (v___x_3360_ == 0)
{
lean_dec_ref(v___x_3359_);
lean_dec_ref(v_arg_3358_);
lean_dec_ref(v_e_3339_);
goto v___jp_3351_;
}
else
{
lean_object* v_arg_3361_; lean_object* v___x_3362_; uint8_t v___x_3363_; 
v_arg_3361_ = lean_ctor_get(v___x_3359_, 1);
lean_inc_ref(v_arg_3361_);
v___x_3362_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3359_);
v___x_3363_ = l_Lean_Expr_isApp(v___x_3362_);
if (v___x_3363_ == 0)
{
lean_dec_ref(v___x_3362_);
lean_dec_ref(v_arg_3361_);
lean_dec_ref(v_arg_3358_);
lean_dec_ref(v_e_3339_);
goto v___jp_3351_;
}
else
{
lean_object* v_arg_3364_; lean_object* v___x_3365_; uint8_t v___x_3366_; 
v_arg_3364_ = lean_ctor_get(v___x_3362_, 1);
lean_inc_ref(v_arg_3364_);
v___x_3365_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3362_);
v___x_3366_ = l_Lean_Expr_isApp(v___x_3365_);
if (v___x_3366_ == 0)
{
lean_dec_ref(v___x_3365_);
lean_dec_ref(v_arg_3364_);
lean_dec_ref(v_arg_3361_);
lean_dec_ref(v_arg_3358_);
lean_dec_ref(v_e_3339_);
goto v___jp_3351_;
}
else
{
lean_object* v___x_3367_; lean_object* v___x_3368_; uint8_t v___x_3369_; 
v___x_3367_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3365_);
v___x_3368_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2));
v___x_3369_ = l_Lean_Expr_isConstOf(v___x_3367_, v___x_3368_);
lean_dec_ref(v___x_3367_);
if (v___x_3369_ == 0)
{
lean_dec_ref(v_arg_3364_);
lean_dec_ref(v_arg_3361_);
lean_dec_ref(v_arg_3358_);
lean_dec_ref(v_e_3339_);
goto v___jp_3351_;
}
else
{
lean_object* v___x_3370_; 
v___x_3370_ = l_Lean_Meta_Structural_isInstLEInt___redArg(v_arg_3364_, v_a_3347_);
if (lean_obj_tag(v___x_3370_) == 0)
{
lean_object* v_a_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3453_; 
v_a_3371_ = lean_ctor_get(v___x_3370_, 0);
v_isSharedCheck_3453_ = !lean_is_exclusive(v___x_3370_);
if (v_isSharedCheck_3453_ == 0)
{
v___x_3373_ = v___x_3370_;
v_isShared_3374_ = v_isSharedCheck_3453_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_a_3371_);
lean_dec(v___x_3370_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3453_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
uint8_t v___x_3375_; 
v___x_3375_ = lean_unbox(v_a_3371_);
lean_dec(v_a_3371_);
if (v___x_3375_ == 0)
{
lean_object* v___x_3376_; lean_object* v___x_3378_; 
lean_dec_ref(v_arg_3361_);
lean_dec_ref(v_arg_3358_);
lean_dec_ref(v_e_3339_);
v___x_3376_ = lean_box(0);
if (v_isShared_3374_ == 0)
{
lean_ctor_set(v___x_3373_, 0, v___x_3376_);
v___x_3378_ = v___x_3373_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v___x_3376_);
v___x_3378_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
return v___x_3378_;
}
}
else
{
lean_object* v___x_3380_; 
lean_del_object(v___x_3373_);
v___x_3380_ = l_Lean_Meta_getIntValue_x3f(v_arg_3358_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_);
if (lean_obj_tag(v___x_3380_) == 0)
{
lean_object* v_a_3381_; 
v_a_3381_ = lean_ctor_get(v___x_3380_, 0);
lean_inc(v_a_3381_);
lean_dec_ref_known(v___x_3380_, 1);
if (lean_obj_tag(v_a_3381_) == 1)
{
lean_object* v_val_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3426_; 
v_val_3382_ = lean_ctor_get(v_a_3381_, 0);
v_isSharedCheck_3426_ = !lean_is_exclusive(v_a_3381_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3384_ = v_a_3381_;
v_isShared_3385_ = v_isSharedCheck_3426_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_val_3382_);
lean_dec(v_a_3381_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3426_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v___x_3386_; uint8_t v___x_3387_; 
v___x_3386_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9);
v___x_3387_ = lean_int_dec_eq(v_val_3382_, v___x_3386_);
lean_dec(v_val_3382_);
if (v___x_3387_ == 0)
{
lean_object* v___x_3388_; 
lean_del_object(v___x_3384_);
lean_dec_ref(v_arg_3361_);
v___x_3388_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(v_e_3339_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_);
if (lean_obj_tag(v___x_3388_) == 0)
{
lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3396_; 
v_isSharedCheck_3396_ = !lean_is_exclusive(v___x_3388_);
if (v_isSharedCheck_3396_ == 0)
{
lean_object* v_unused_3397_; 
v_unused_3397_ = lean_ctor_get(v___x_3388_, 0);
lean_dec(v_unused_3397_);
v___x_3390_ = v___x_3388_;
v_isShared_3391_ = v_isSharedCheck_3396_;
goto v_resetjp_3389_;
}
else
{
lean_dec(v___x_3388_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3396_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v___x_3392_; lean_object* v___x_3394_; 
v___x_3392_ = lean_box(0);
if (v_isShared_3391_ == 0)
{
lean_ctor_set(v___x_3390_, 0, v___x_3392_);
v___x_3394_ = v___x_3390_;
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
else
{
lean_object* v_a_3398_; lean_object* v___x_3400_; uint8_t v_isShared_3401_; uint8_t v_isSharedCheck_3405_; 
v_a_3398_ = lean_ctor_get(v___x_3388_, 0);
v_isSharedCheck_3405_ = !lean_is_exclusive(v___x_3388_);
if (v_isSharedCheck_3405_ == 0)
{
v___x_3400_ = v___x_3388_;
v_isShared_3401_ = v_isSharedCheck_3405_;
goto v_resetjp_3399_;
}
else
{
lean_inc(v_a_3398_);
lean_dec(v___x_3388_);
v___x_3400_ = lean_box(0);
v_isShared_3401_ = v_isSharedCheck_3405_;
goto v_resetjp_3399_;
}
v_resetjp_3399_:
{
lean_object* v___x_3403_; 
if (v_isShared_3401_ == 0)
{
v___x_3403_ = v___x_3400_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3404_; 
v_reuseFailAlloc_3404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3404_, 0, v_a_3398_);
v___x_3403_ = v_reuseFailAlloc_3404_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
return v___x_3403_;
}
}
}
}
else
{
lean_object* v___x_3406_; 
lean_dec_ref(v_e_3339_);
v___x_3406_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(v_arg_3361_, v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_);
if (lean_obj_tag(v___x_3406_) == 0)
{
lean_object* v_a_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3417_; 
v_a_3407_ = lean_ctor_get(v___x_3406_, 0);
v_isSharedCheck_3417_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3409_ = v___x_3406_;
v_isShared_3410_ = v_isSharedCheck_3417_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_a_3407_);
lean_dec(v___x_3406_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3417_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v___x_3412_; 
if (v_isShared_3385_ == 0)
{
lean_ctor_set(v___x_3384_, 0, v_a_3407_);
v___x_3412_ = v___x_3384_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v_a_3407_);
v___x_3412_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
lean_object* v___x_3414_; 
if (v_isShared_3410_ == 0)
{
lean_ctor_set(v___x_3409_, 0, v___x_3412_);
v___x_3414_ = v___x_3409_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v___x_3412_);
v___x_3414_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
return v___x_3414_;
}
}
}
}
else
{
lean_object* v_a_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3425_; 
lean_del_object(v___x_3384_);
v_a_3418_ = lean_ctor_get(v___x_3406_, 0);
v_isSharedCheck_3425_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3425_ == 0)
{
v___x_3420_ = v___x_3406_;
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_a_3418_);
lean_dec(v___x_3406_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v___x_3423_; 
if (v_isShared_3421_ == 0)
{
v___x_3423_ = v___x_3420_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v_a_3418_);
v___x_3423_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
return v___x_3423_;
}
}
}
}
}
}
else
{
lean_object* v___x_3427_; 
lean_dec(v_a_3381_);
lean_dec_ref(v_arg_3361_);
v___x_3427_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(v_e_3339_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_);
if (lean_obj_tag(v___x_3427_) == 0)
{
lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3435_; 
v_isSharedCheck_3435_ = !lean_is_exclusive(v___x_3427_);
if (v_isSharedCheck_3435_ == 0)
{
lean_object* v_unused_3436_; 
v_unused_3436_ = lean_ctor_get(v___x_3427_, 0);
lean_dec(v_unused_3436_);
v___x_3429_ = v___x_3427_;
v_isShared_3430_ = v_isSharedCheck_3435_;
goto v_resetjp_3428_;
}
else
{
lean_dec(v___x_3427_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3435_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3431_; lean_object* v___x_3433_; 
v___x_3431_ = lean_box(0);
if (v_isShared_3430_ == 0)
{
lean_ctor_set(v___x_3429_, 0, v___x_3431_);
v___x_3433_ = v___x_3429_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v___x_3431_);
v___x_3433_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
return v___x_3433_;
}
}
}
else
{
lean_object* v_a_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3444_; 
v_a_3437_ = lean_ctor_get(v___x_3427_, 0);
v_isSharedCheck_3444_ = !lean_is_exclusive(v___x_3427_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3439_ = v___x_3427_;
v_isShared_3440_ = v_isSharedCheck_3444_;
goto v_resetjp_3438_;
}
else
{
lean_inc(v_a_3437_);
lean_dec(v___x_3427_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3444_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
lean_object* v___x_3442_; 
if (v_isShared_3440_ == 0)
{
v___x_3442_ = v___x_3439_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v_a_3437_);
v___x_3442_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
return v___x_3442_;
}
}
}
}
}
else
{
lean_object* v_a_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3452_; 
lean_dec_ref(v_arg_3361_);
lean_dec_ref(v_e_3339_);
v_a_3445_ = lean_ctor_get(v___x_3380_, 0);
v_isSharedCheck_3452_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3447_ = v___x_3380_;
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_a_3445_);
lean_dec(v___x_3380_);
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
}
}
else
{
lean_object* v_a_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3461_; 
lean_dec_ref(v_arg_3361_);
lean_dec_ref(v_arg_3358_);
lean_dec_ref(v_e_3339_);
v_a_3454_ = lean_ctor_get(v___x_3370_, 0);
v_isSharedCheck_3461_ = !lean_is_exclusive(v___x_3370_);
if (v_isSharedCheck_3461_ == 0)
{
v___x_3456_ = v___x_3370_;
v_isShared_3457_ = v_isSharedCheck_3461_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_a_3454_);
lean_dec(v___x_3370_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3461_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
lean_object* v___x_3459_; 
if (v_isShared_3457_ == 0)
{
v___x_3459_ = v___x_3456_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v_a_3454_);
v___x_3459_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
return v___x_3459_;
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
lean_object* v_a_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3469_; 
lean_dec_ref(v_e_3339_);
v_a_3462_ = lean_ctor_get(v___x_3354_, 0);
v_isSharedCheck_3469_ = !lean_is_exclusive(v___x_3354_);
if (v_isSharedCheck_3469_ == 0)
{
v___x_3464_ = v___x_3354_;
v_isShared_3465_ = v_isSharedCheck_3469_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_a_3462_);
lean_dec(v___x_3354_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3469_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v___x_3467_; 
if (v_isShared_3465_ == 0)
{
v___x_3467_ = v___x_3464_;
goto v_reusejp_3466_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v_a_3462_);
v___x_3467_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3466_;
}
v_reusejp_3466_:
{
return v___x_3467_;
}
}
}
v___jp_3351_:
{
lean_object* v___x_3352_; lean_object* v___x_3353_; 
v___x_3352_ = lean_box(0);
v___x_3353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3353_, 0, v___x_3352_);
return v___x_3353_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3339_ = stack[0].m_obj;
lean_object* v_a_3340_ = stack[1].m_obj;
lean_object* v_a_3341_ = stack[2].m_obj;
lean_object* v_a_3342_ = stack[3].m_obj;
lean_object* v_a_3343_ = stack[4].m_obj;
lean_object* v_a_3344_ = stack[5].m_obj;
lean_object* v_a_3345_ = stack[6].m_obj;
lean_object* v_a_3346_ = stack[7].m_obj;
lean_object* v_a_3347_ = stack[8].m_obj;
lean_object* v_a_3348_ = stack[9].m_obj;
lean_object* v_a_3349_ = stack[10].m_obj;
lean_object* v_res_3470_;
v_res_3470_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f(v_e_3339_, v_a_3340_, v_a_3341_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_, v_a_3346_, v_a_3347_, v_a_3348_, v_a_3349_);
stack->m_obj
 = v_res_3470_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___boxed(lean_object* v_e_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_){
_start:
{
lean_object* v_res_3483_; 
v_res_3483_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f(v_e_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_);
lean_dec(v_a_3481_);
lean_dec_ref(v_a_3480_);
lean_dec(v_a_3479_);
lean_dec_ref(v_a_3478_);
lean_dec(v_a_3477_);
lean_dec_ref(v_a_3476_);
lean_dec(v_a_3475_);
lean_dec_ref(v_a_3474_);
lean_dec(v_a_3473_);
lean_dec(v_a_3472_);
return v_res_3483_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(lean_object* v_c_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_){
_start:
{
lean_object* v_p_3496_; lean_object* v___x_3497_; 
v_p_3496_ = lean_ctor_get(v_c_3484_, 0);
lean_inc_ref(v_p_3496_);
v___x_3497_ = l_Int_Internal_Linear_Poly_normCommRing_x3f(v_p_3496_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_);
if (lean_obj_tag(v___x_3497_) == 0)
{
lean_object* v_a_3498_; 
v_a_3498_ = lean_ctor_get(v___x_3497_, 0);
lean_inc(v_a_3498_);
lean_dec_ref_known(v___x_3497_, 1);
if (lean_obj_tag(v_a_3498_) == 1)
{
lean_object* v_val_3499_; lean_object* v_snd_3500_; lean_object* v_fst_3501_; lean_object* v_fst_3502_; lean_object* v_snd_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3512_; 
v_val_3499_ = lean_ctor_get(v_a_3498_, 0);
lean_inc(v_val_3499_);
lean_dec_ref_known(v_a_3498_, 1);
v_snd_3500_ = lean_ctor_get(v_val_3499_, 1);
lean_inc(v_snd_3500_);
v_fst_3501_ = lean_ctor_get(v_val_3499_, 0);
lean_inc(v_fst_3501_);
lean_dec(v_val_3499_);
v_fst_3502_ = lean_ctor_get(v_snd_3500_, 0);
v_snd_3503_ = lean_ctor_get(v_snd_3500_, 1);
v_isSharedCheck_3512_ = !lean_is_exclusive(v_snd_3500_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3505_ = v_snd_3500_;
v_isShared_3506_ = v_isSharedCheck_3512_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_snd_3503_);
lean_inc(v_fst_3502_);
lean_dec(v_snd_3500_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3512_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
lean_object* v___x_3507_; lean_object* v___x_3509_; 
v___x_3507_ = lean_alloc_ctor(17, 3, 0);
lean_ctor_set(v___x_3507_, 0, v_c_3484_);
lean_ctor_set(v___x_3507_, 1, v_fst_3501_);
lean_ctor_set(v___x_3507_, 2, v_fst_3502_);
if (v_isShared_3506_ == 0)
{
lean_ctor_set(v___x_3505_, 1, v___x_3507_);
lean_ctor_set(v___x_3505_, 0, v_snd_3503_);
v___x_3509_ = v___x_3505_;
goto v_reusejp_3508_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_snd_3503_);
lean_ctor_set(v_reuseFailAlloc_3511_, 1, v___x_3507_);
v___x_3509_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3508_;
}
v_reusejp_3508_:
{
lean_object* v___x_3510_; 
lean_inc(v_a_3494_);
lean_inc_ref(v_a_3493_);
lean_inc(v_a_3492_);
lean_inc_ref(v_a_3491_);
lean_inc(v_a_3490_);
lean_inc_ref(v_a_3489_);
lean_inc(v_a_3488_);
lean_inc_ref(v_a_3487_);
lean_inc(v_a_3486_);
lean_inc(v_a_3485_);
v___x_3510_ = lean_grind_cutsat_assert_le(v___x_3509_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_);
return v___x_3510_;
}
}
}
else
{
lean_object* v___x_3513_; 
lean_dec(v_a_3498_);
lean_inc(v_a_3494_);
lean_inc_ref(v_a_3493_);
lean_inc(v_a_3492_);
lean_inc_ref(v_a_3491_);
lean_inc(v_a_3490_);
lean_inc_ref(v_a_3489_);
lean_inc(v_a_3488_);
lean_inc_ref(v_a_3487_);
lean_inc(v_a_3486_);
lean_inc(v_a_3485_);
v___x_3513_ = lean_grind_cutsat_assert_le(v_c_3484_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_);
return v___x_3513_;
}
}
else
{
lean_object* v_a_3514_; lean_object* v___x_3516_; uint8_t v_isShared_3517_; uint8_t v_isSharedCheck_3521_; 
lean_dec_ref(v_c_3484_);
v_a_3514_ = lean_ctor_get(v___x_3497_, 0);
v_isSharedCheck_3521_ = !lean_is_exclusive(v___x_3497_);
if (v_isSharedCheck_3521_ == 0)
{
v___x_3516_ = v___x_3497_;
v_isShared_3517_ = v_isSharedCheck_3521_;
goto v_resetjp_3515_;
}
else
{
lean_inc(v_a_3514_);
lean_dec(v___x_3497_);
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
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_c_3484_ = stack[0].m_obj;
lean_object* v_a_3485_ = stack[1].m_obj;
lean_object* v_a_3486_ = stack[2].m_obj;
lean_object* v_a_3487_ = stack[3].m_obj;
lean_object* v_a_3488_ = stack[4].m_obj;
lean_object* v_a_3489_ = stack[5].m_obj;
lean_object* v_a_3490_ = stack[6].m_obj;
lean_object* v_a_3491_ = stack[7].m_obj;
lean_object* v_a_3492_ = stack[8].m_obj;
lean_object* v_a_3493_ = stack[9].m_obj;
lean_object* v_a_3494_ = stack[10].m_obj;
lean_object* v_res_3522_;
v_res_3522_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v_c_3484_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_);
stack->m_obj
 = v_res_3522_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore___boxed(lean_object* v_c_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_){
_start:
{
lean_object* v_res_3535_; 
v_res_3535_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v_c_3523_, v_a_3524_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_);
lean_dec(v_a_3533_);
lean_dec_ref(v_a_3532_);
lean_dec(v_a_3531_);
lean_dec_ref(v_a_3530_);
lean_dec(v_a_3529_);
lean_dec_ref(v_a_3528_);
lean_dec(v_a_3527_);
lean_dec_ref(v_a_3526_);
lean_dec(v_a_3525_);
lean_dec(v_a_3524_);
return v_res_3535_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0(void){
_start:
{
lean_object* v___x_3536_; lean_object* v___x_3537_; 
v___x_3536_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
v___x_3537_ = lean_int_neg(v___x_3536_);
return v___x_3537_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe(lean_object* v_e_3538_, uint8_t v_eqTrue_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_){
_start:
{
lean_object* v___x_3551_; 
lean_inc_ref(v_e_3538_);
v___x_3551_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f(v_e_3538_, v_a_3540_, v_a_3541_, v_a_3542_, v_a_3543_, v_a_3544_, v_a_3545_, v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_);
if (lean_obj_tag(v___x_3551_) == 0)
{
lean_object* v_a_3552_; lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3578_; 
v_a_3552_ = lean_ctor_get(v___x_3551_, 0);
v_isSharedCheck_3578_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3578_ == 0)
{
v___x_3554_ = v___x_3551_;
v_isShared_3555_ = v_isSharedCheck_3578_;
goto v_resetjp_3553_;
}
else
{
lean_inc(v_a_3552_);
lean_dec(v___x_3551_);
v___x_3554_ = lean_box(0);
v_isShared_3555_ = v_isSharedCheck_3578_;
goto v_resetjp_3553_;
}
v_resetjp_3553_:
{
if (lean_obj_tag(v_a_3552_) == 1)
{
lean_del_object(v___x_3554_);
if (v_eqTrue_3539_ == 0)
{
lean_object* v_val_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; 
v_val_3556_ = lean_ctor_get(v_a_3552_, 0);
lean_inc_n(v_val_3556_, 2);
lean_dec_ref_known(v_a_3552_, 1);
v___x_3557_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
v___x_3558_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0);
v___x_3559_ = l_Int_Internal_Linear_Poly_mul(v_val_3556_, v___x_3558_);
v___x_3560_ = l_Int_Internal_Linear_Poly_addConst(v___x_3559_, v___x_3557_);
v___x_3561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3561_, 0, v_e_3538_);
lean_ctor_set(v___x_3561_, 1, v_val_3556_);
v___x_3562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3562_, 0, v___x_3560_);
lean_ctor_set(v___x_3562_, 1, v___x_3561_);
v___x_3563_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v___x_3562_, v_a_3540_, v_a_3541_, v_a_3542_, v_a_3543_, v_a_3544_, v_a_3545_, v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_);
return v___x_3563_;
}
else
{
lean_object* v_val_3564_; lean_object* v___x_3566_; uint8_t v_isShared_3567_; uint8_t v_isSharedCheck_3573_; 
v_val_3564_ = lean_ctor_get(v_a_3552_, 0);
v_isSharedCheck_3573_ = !lean_is_exclusive(v_a_3552_);
if (v_isSharedCheck_3573_ == 0)
{
v___x_3566_ = v_a_3552_;
v_isShared_3567_ = v_isSharedCheck_3573_;
goto v_resetjp_3565_;
}
else
{
lean_inc(v_val_3564_);
lean_dec(v_a_3552_);
v___x_3566_ = lean_box(0);
v_isShared_3567_ = v_isSharedCheck_3573_;
goto v_resetjp_3565_;
}
v_resetjp_3565_:
{
lean_object* v___x_3569_; 
if (v_isShared_3567_ == 0)
{
lean_ctor_set_tag(v___x_3566_, 0);
lean_ctor_set(v___x_3566_, 0, v_e_3538_);
v___x_3569_ = v___x_3566_;
goto v_reusejp_3568_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v_e_3538_);
v___x_3569_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3568_;
}
v_reusejp_3568_:
{
lean_object* v___x_3570_; lean_object* v___x_3571_; 
v___x_3570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3570_, 0, v_val_3564_);
lean_ctor_set(v___x_3570_, 1, v___x_3569_);
v___x_3571_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v___x_3570_, v_a_3540_, v_a_3541_, v_a_3542_, v_a_3543_, v_a_3544_, v_a_3545_, v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_);
return v___x_3571_;
}
}
}
}
else
{
lean_object* v___x_3574_; lean_object* v___x_3576_; 
lean_dec(v_a_3552_);
lean_dec_ref(v_e_3538_);
v___x_3574_ = lean_box(0);
if (v_isShared_3555_ == 0)
{
lean_ctor_set(v___x_3554_, 0, v___x_3574_);
v___x_3576_ = v___x_3554_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v___x_3574_);
v___x_3576_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
return v___x_3576_;
}
}
}
}
else
{
lean_object* v_a_3579_; lean_object* v___x_3581_; uint8_t v_isShared_3582_; uint8_t v_isSharedCheck_3586_; 
lean_dec_ref(v_e_3538_);
v_a_3579_ = lean_ctor_get(v___x_3551_, 0);
v_isSharedCheck_3586_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3586_ == 0)
{
v___x_3581_ = v___x_3551_;
v_isShared_3582_ = v_isSharedCheck_3586_;
goto v_resetjp_3580_;
}
else
{
lean_inc(v_a_3579_);
lean_dec(v___x_3551_);
v___x_3581_ = lean_box(0);
v_isShared_3582_ = v_isSharedCheck_3586_;
goto v_resetjp_3580_;
}
v_resetjp_3580_:
{
lean_object* v___x_3584_; 
if (v_isShared_3582_ == 0)
{
v___x_3584_ = v___x_3581_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3585_; 
v_reuseFailAlloc_3585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3585_, 0, v_a_3579_);
v___x_3584_ = v_reuseFailAlloc_3585_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
return v___x_3584_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3538_ = stack[0].m_obj;
uint8_t v_eqTrue_3539_ = stack[1].m_num;
lean_object* v_a_3540_ = stack[2].m_obj;
lean_object* v_a_3541_ = stack[3].m_obj;
lean_object* v_a_3542_ = stack[4].m_obj;
lean_object* v_a_3543_ = stack[5].m_obj;
lean_object* v_a_3544_ = stack[6].m_obj;
lean_object* v_a_3545_ = stack[7].m_obj;
lean_object* v_a_3546_ = stack[8].m_obj;
lean_object* v_a_3547_ = stack[9].m_obj;
lean_object* v_a_3548_ = stack[10].m_obj;
lean_object* v_a_3549_ = stack[11].m_obj;
lean_object* v_res_3587_;
v_res_3587_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe(v_e_3538_, v_eqTrue_3539_, v_a_3540_, v_a_3541_, v_a_3542_, v_a_3543_, v_a_3544_, v_a_3545_, v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_);
stack->m_obj
 = v_res_3587_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___boxed(lean_object* v_e_3588_, lean_object* v_eqTrue_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_){
_start:
{
uint8_t v_eqTrue_boxed_3601_; lean_object* v_res_3602_; 
v_eqTrue_boxed_3601_ = lean_unbox(v_eqTrue_3589_);
v_res_3602_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe(v_e_3588_, v_eqTrue_boxed_3601_, v_a_3590_, v_a_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_, v_a_3598_, v_a_3599_);
lean_dec(v_a_3599_);
lean_dec_ref(v_a_3598_);
lean_dec(v_a_3597_);
lean_dec_ref(v_a_3596_);
lean_dec(v_a_3595_);
lean_dec_ref(v_a_3594_);
lean_dec(v_a_3593_);
lean_dec_ref(v_a_3592_);
lean_dec(v_a_3591_);
lean_dec(v_a_3590_);
return v_res_3602_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0(void){
_start:
{
lean_object* v___x_3603_; lean_object* v___x_3604_; 
v___x_3603_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
v___x_3604_ = l_Lean_mkIntLit(v___x_3603_);
return v___x_3604_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5(void){
_start:
{
lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; 
v___x_3612_ = lean_box(0);
v___x_3613_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__4));
v___x_3614_ = l_Lean_mkConst(v___x_3613_, v___x_3612_);
return v___x_3614_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8(void){
_start:
{
lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; 
v___x_3620_ = lean_box(0);
v___x_3621_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__7));
v___x_3622_ = l_Lean_mkConst(v___x_3621_, v___x_3620_);
return v___x_3622_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe(lean_object* v_e_3623_, uint8_t v_eqTrue_3624_, lean_object* v_a_3625_, lean_object* v_a_3626_, lean_object* v_a_3627_, lean_object* v_a_3628_, lean_object* v_a_3629_, lean_object* v_a_3630_, lean_object* v_a_3631_, lean_object* v_a_3632_, lean_object* v_a_3633_, lean_object* v_a_3634_){
_start:
{
lean_object* v___y_3637_; lean_object* v___y_3638_; lean_object* v_fst_3639_; lean_object* v_snd_3640_; lean_object* v___x_3669_; uint8_t v___x_3670_; 
lean_inc_ref(v_e_3623_);
v___x_3669_ = l_Lean_Expr_cleanupAnnotations(v_e_3623_);
v___x_3670_ = l_Lean_Expr_isApp(v___x_3669_);
if (v___x_3670_ == 0)
{
lean_dec_ref(v___x_3669_);
lean_dec_ref(v_e_3623_);
goto v___jp_3666_;
}
else
{
lean_object* v_arg_3671_; lean_object* v___x_3672_; uint8_t v___x_3673_; 
v_arg_3671_ = lean_ctor_get(v___x_3669_, 1);
lean_inc_ref(v_arg_3671_);
v___x_3672_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3669_);
v___x_3673_ = l_Lean_Expr_isApp(v___x_3672_);
if (v___x_3673_ == 0)
{
lean_dec_ref(v___x_3672_);
lean_dec_ref(v_arg_3671_);
lean_dec_ref(v_e_3623_);
goto v___jp_3666_;
}
else
{
lean_object* v_arg_3674_; lean_object* v___y_3676_; lean_object* v___x_3714_; uint8_t v___x_3715_; 
v_arg_3674_ = lean_ctor_get(v___x_3672_, 1);
lean_inc_ref(v_arg_3674_);
v___x_3714_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3672_);
v___x_3715_ = l_Lean_Expr_isApp(v___x_3714_);
if (v___x_3715_ == 0)
{
lean_dec_ref(v___x_3714_);
lean_dec_ref(v_arg_3674_);
lean_dec_ref(v_arg_3671_);
lean_dec_ref(v_e_3623_);
goto v___jp_3666_;
}
else
{
lean_object* v___x_3716_; uint8_t v___x_3717_; 
v___x_3716_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3714_);
v___x_3717_ = l_Lean_Expr_isApp(v___x_3716_);
if (v___x_3717_ == 0)
{
lean_dec_ref(v___x_3716_);
lean_dec_ref(v_arg_3674_);
lean_dec_ref(v_arg_3671_);
lean_dec_ref(v_e_3623_);
goto v___jp_3666_;
}
else
{
lean_object* v___x_3718_; lean_object* v___x_3719_; uint8_t v___x_3720_; 
v___x_3718_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3716_);
v___x_3719_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2));
v___x_3720_ = l_Lean_Expr_isConstOf(v___x_3718_, v___x_3719_);
lean_dec_ref(v___x_3718_);
if (v___x_3720_ == 0)
{
lean_dec_ref(v_arg_3674_);
lean_dec_ref(v_arg_3671_);
lean_dec_ref(v_e_3623_);
goto v___jp_3666_;
}
else
{
if (v_eqTrue_3624_ == 0)
{
lean_object* v___x_3721_; 
v___x_3721_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5);
v___y_3676_ = v___x_3721_;
goto v___jp_3675_;
}
else
{
lean_object* v___x_3722_; 
v___x_3722_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8);
v___y_3676_ = v___x_3722_;
goto v___jp_3675_;
}
}
}
}
v___jp_3675_:
{
lean_object* v___x_3677_; 
v___x_3677_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_3623_, v_a_3625_);
if (lean_obj_tag(v___x_3677_) == 0)
{
lean_object* v_a_3678_; lean_object* v___x_3679_; 
v_a_3678_ = lean_ctor_get(v___x_3677_, 0);
lean_inc(v_a_3678_);
lean_dec_ref_known(v___x_3677_, 1);
lean_inc_ref(v_arg_3674_);
v___x_3679_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_3674_, v_a_3625_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_, v_a_3630_, v_a_3631_, v_a_3632_, v_a_3633_, v_a_3634_);
if (lean_obj_tag(v___x_3679_) == 0)
{
lean_object* v_a_3680_; lean_object* v_fst_3681_; lean_object* v_snd_3682_; lean_object* v___x_3683_; 
v_a_3680_ = lean_ctor_get(v___x_3679_, 0);
lean_inc(v_a_3680_);
lean_dec_ref_known(v___x_3679_, 1);
v_fst_3681_ = lean_ctor_get(v_a_3680_, 0);
lean_inc(v_fst_3681_);
v_snd_3682_ = lean_ctor_get(v_a_3680_, 1);
lean_inc(v_snd_3682_);
lean_dec(v_a_3680_);
lean_inc_ref(v_arg_3671_);
v___x_3683_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_3671_, v_a_3625_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_, v_a_3630_, v_a_3631_, v_a_3632_, v_a_3633_, v_a_3634_);
if (lean_obj_tag(v___x_3683_) == 0)
{
lean_object* v_a_3684_; lean_object* v_fst_3685_; lean_object* v_snd_3686_; lean_object* v___x_3687_; 
v_a_3684_ = lean_ctor_get(v___x_3683_, 0);
lean_inc(v_a_3684_);
lean_dec_ref_known(v___x_3683_, 1);
v_fst_3685_ = lean_ctor_get(v_a_3684_, 0);
lean_inc_n(v_fst_3685_, 2);
v_snd_3686_ = lean_ctor_get(v_a_3684_, 1);
lean_inc(v_snd_3686_);
lean_dec(v_a_3684_);
lean_inc(v_fst_3681_);
lean_inc_ref(v___y_3676_);
v___x_3687_ = l_Lean_mkApp6(v___y_3676_, v_arg_3674_, v_arg_3671_, v_fst_3681_, v_fst_3685_, v_snd_3682_, v_snd_3686_);
if (v_eqTrue_3624_ == 0)
{
lean_object* v___x_3688_; lean_object* v___x_3689_; 
v___x_3688_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0);
v___x_3689_ = l_Lean_mkIntAdd(v_fst_3685_, v___x_3688_);
v___y_3637_ = v___x_3687_;
v___y_3638_ = v_a_3678_;
v_fst_3639_ = v___x_3689_;
v_snd_3640_ = v_fst_3681_;
goto v___jp_3636_;
}
else
{
v___y_3637_ = v___x_3687_;
v___y_3638_ = v_a_3678_;
v_fst_3639_ = v_fst_3681_;
v_snd_3640_ = v_fst_3685_;
goto v___jp_3636_;
}
}
else
{
lean_object* v_a_3690_; lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3697_; 
lean_dec(v_snd_3682_);
lean_dec(v_fst_3681_);
lean_dec(v_a_3678_);
lean_dec_ref(v_arg_3674_);
lean_dec_ref(v_arg_3671_);
lean_dec_ref(v_e_3623_);
v_a_3690_ = lean_ctor_get(v___x_3683_, 0);
v_isSharedCheck_3697_ = !lean_is_exclusive(v___x_3683_);
if (v_isSharedCheck_3697_ == 0)
{
v___x_3692_ = v___x_3683_;
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
else
{
lean_inc(v_a_3690_);
lean_dec(v___x_3683_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
lean_object* v___x_3695_; 
if (v_isShared_3693_ == 0)
{
v___x_3695_ = v___x_3692_;
goto v_reusejp_3694_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v_a_3690_);
v___x_3695_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3694_;
}
v_reusejp_3694_:
{
return v___x_3695_;
}
}
}
}
else
{
lean_object* v_a_3698_; lean_object* v___x_3700_; uint8_t v_isShared_3701_; uint8_t v_isSharedCheck_3705_; 
lean_dec(v_a_3678_);
lean_dec_ref(v_arg_3674_);
lean_dec_ref(v_arg_3671_);
lean_dec_ref(v_e_3623_);
v_a_3698_ = lean_ctor_get(v___x_3679_, 0);
v_isSharedCheck_3705_ = !lean_is_exclusive(v___x_3679_);
if (v_isSharedCheck_3705_ == 0)
{
v___x_3700_ = v___x_3679_;
v_isShared_3701_ = v_isSharedCheck_3705_;
goto v_resetjp_3699_;
}
else
{
lean_inc(v_a_3698_);
lean_dec(v___x_3679_);
v___x_3700_ = lean_box(0);
v_isShared_3701_ = v_isSharedCheck_3705_;
goto v_resetjp_3699_;
}
v_resetjp_3699_:
{
lean_object* v___x_3703_; 
if (v_isShared_3701_ == 0)
{
v___x_3703_ = v___x_3700_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v_a_3698_);
v___x_3703_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
return v___x_3703_;
}
}
}
}
else
{
lean_object* v_a_3706_; lean_object* v___x_3708_; uint8_t v_isShared_3709_; uint8_t v_isSharedCheck_3713_; 
lean_dec_ref(v_arg_3674_);
lean_dec_ref(v_arg_3671_);
lean_dec_ref(v_e_3623_);
v_a_3706_ = lean_ctor_get(v___x_3677_, 0);
v_isSharedCheck_3713_ = !lean_is_exclusive(v___x_3677_);
if (v_isSharedCheck_3713_ == 0)
{
v___x_3708_ = v___x_3677_;
v_isShared_3709_ = v_isSharedCheck_3713_;
goto v_resetjp_3707_;
}
else
{
lean_inc(v_a_3706_);
lean_dec(v___x_3677_);
v___x_3708_ = lean_box(0);
v_isShared_3709_ = v_isSharedCheck_3713_;
goto v_resetjp_3707_;
}
v_resetjp_3707_:
{
lean_object* v___x_3711_; 
if (v_isShared_3709_ == 0)
{
v___x_3711_ = v___x_3708_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3712_; 
v_reuseFailAlloc_3712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3712_, 0, v_a_3706_);
v___x_3711_ = v_reuseFailAlloc_3712_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
return v___x_3711_;
}
}
}
}
}
}
v___jp_3636_:
{
lean_object* v___x_3641_; 
lean_inc(v___y_3638_);
v___x_3641_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_3639_, v___y_3638_, v_a_3625_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_, v_a_3630_, v_a_3631_, v_a_3632_, v_a_3633_, v_a_3634_);
if (lean_obj_tag(v___x_3641_) == 0)
{
lean_object* v_a_3642_; lean_object* v___x_3643_; 
v_a_3642_ = lean_ctor_get(v___x_3641_, 0);
lean_inc(v_a_3642_);
lean_dec_ref_known(v___x_3641_, 1);
v___x_3643_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_snd_3640_, v___y_3638_, v_a_3625_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_, v_a_3630_, v_a_3631_, v_a_3632_, v_a_3633_, v_a_3634_);
if (lean_obj_tag(v___x_3643_) == 0)
{
lean_object* v_a_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; 
v_a_3644_ = lean_ctor_get(v___x_3643_, 0);
lean_inc_n(v_a_3644_, 2);
lean_dec_ref_known(v___x_3643_, 1);
lean_inc(v_a_3642_);
v___x_3645_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3645_, 0, v_a_3642_);
lean_ctor_set(v___x_3645_, 1, v_a_3644_);
v___x_3646_ = l_Int_Internal_Linear_Expr_norm(v___x_3645_);
lean_dec_ref_known(v___x_3645_, 2);
v___x_3647_ = lean_alloc_ctor(2, 4, 1);
lean_ctor_set(v___x_3647_, 0, v_e_3623_);
lean_ctor_set(v___x_3647_, 1, v___y_3637_);
lean_ctor_set(v___x_3647_, 2, v_a_3642_);
lean_ctor_set(v___x_3647_, 3, v_a_3644_);
lean_ctor_set_uint8(v___x_3647_, sizeof(void*)*4, v_eqTrue_3624_);
v___x_3648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3648_, 0, v___x_3646_);
lean_ctor_set(v___x_3648_, 1, v___x_3647_);
v___x_3649_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v___x_3648_, v_a_3625_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_, v_a_3630_, v_a_3631_, v_a_3632_, v_a_3633_, v_a_3634_);
return v___x_3649_;
}
else
{
lean_object* v_a_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3657_; 
lean_dec(v_a_3642_);
lean_dec_ref(v___y_3637_);
lean_dec_ref(v_e_3623_);
v_a_3650_ = lean_ctor_get(v___x_3643_, 0);
v_isSharedCheck_3657_ = !lean_is_exclusive(v___x_3643_);
if (v_isSharedCheck_3657_ == 0)
{
v___x_3652_ = v___x_3643_;
v_isShared_3653_ = v_isSharedCheck_3657_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_a_3650_);
lean_dec(v___x_3643_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3657_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v___x_3655_; 
if (v_isShared_3653_ == 0)
{
v___x_3655_ = v___x_3652_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v_a_3650_);
v___x_3655_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
return v___x_3655_;
}
}
}
}
else
{
lean_object* v_a_3658_; lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_3665_; 
lean_dec_ref(v_snd_3640_);
lean_dec(v___y_3638_);
lean_dec_ref(v___y_3637_);
lean_dec_ref(v_e_3623_);
v_a_3658_ = lean_ctor_get(v___x_3641_, 0);
v_isSharedCheck_3665_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3665_ == 0)
{
v___x_3660_ = v___x_3641_;
v_isShared_3661_ = v_isSharedCheck_3665_;
goto v_resetjp_3659_;
}
else
{
lean_inc(v_a_3658_);
lean_dec(v___x_3641_);
v___x_3660_ = lean_box(0);
v_isShared_3661_ = v_isSharedCheck_3665_;
goto v_resetjp_3659_;
}
v_resetjp_3659_:
{
lean_object* v___x_3663_; 
if (v_isShared_3661_ == 0)
{
v___x_3663_ = v___x_3660_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v_a_3658_);
v___x_3663_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
return v___x_3663_;
}
}
}
}
v___jp_3666_:
{
lean_object* v___x_3667_; lean_object* v___x_3668_; 
v___x_3667_ = lean_box(0);
v___x_3668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3668_, 0, v___x_3667_);
return v___x_3668_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3623_ = stack[0].m_obj;
uint8_t v_eqTrue_3624_ = stack[1].m_num;
lean_object* v_a_3625_ = stack[2].m_obj;
lean_object* v_a_3626_ = stack[3].m_obj;
lean_object* v_a_3627_ = stack[4].m_obj;
lean_object* v_a_3628_ = stack[5].m_obj;
lean_object* v_a_3629_ = stack[6].m_obj;
lean_object* v_a_3630_ = stack[7].m_obj;
lean_object* v_a_3631_ = stack[8].m_obj;
lean_object* v_a_3632_ = stack[9].m_obj;
lean_object* v_a_3633_ = stack[10].m_obj;
lean_object* v_a_3634_ = stack[11].m_obj;
lean_object* v_res_3723_;
v_res_3723_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe(v_e_3623_, v_eqTrue_3624_, v_a_3625_, v_a_3626_, v_a_3627_, v_a_3628_, v_a_3629_, v_a_3630_, v_a_3631_, v_a_3632_, v_a_3633_, v_a_3634_);
stack->m_obj
 = v_res_3723_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___boxed(lean_object* v_e_3724_, lean_object* v_eqTrue_3725_, lean_object* v_a_3726_, lean_object* v_a_3727_, lean_object* v_a_3728_, lean_object* v_a_3729_, lean_object* v_a_3730_, lean_object* v_a_3731_, lean_object* v_a_3732_, lean_object* v_a_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_, lean_object* v_a_3736_){
_start:
{
uint8_t v_eqTrue_boxed_3737_; lean_object* v_res_3738_; 
v_eqTrue_boxed_3737_ = lean_unbox(v_eqTrue_3725_);
v_res_3738_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe(v_e_3724_, v_eqTrue_boxed_3737_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_);
lean_dec(v_a_3735_);
lean_dec_ref(v_a_3734_);
lean_dec(v_a_3733_);
lean_dec_ref(v_a_3732_);
lean_dec(v_a_3731_);
lean_dec_ref(v_a_3730_);
lean_dec(v_a_3729_);
lean_dec_ref(v_a_3728_);
lean_dec(v_a_3727_);
lean_dec(v_a_3726_);
return v_res_3738_;
}
}
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe(lean_object* v_e_3744_, uint8_t v_eqTrue_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_, lean_object* v_a_3752_, lean_object* v_a_3753_, lean_object* v_a_3754_, lean_object* v_a_3755_){
_start:
{
lean_object* v___x_3760_; 
v___x_3760_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3748_);
if (lean_obj_tag(v___x_3760_) == 0)
{
lean_object* v_a_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3792_; 
v_a_3761_ = lean_ctor_get(v___x_3760_, 0);
v_isSharedCheck_3792_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3792_ == 0)
{
v___x_3763_ = v___x_3760_;
v_isShared_3764_ = v_isSharedCheck_3792_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_a_3761_);
lean_dec(v___x_3760_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3792_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
uint8_t v_lia_3765_; 
v_lia_3765_ = lean_ctor_get_uint8(v_a_3761_, sizeof(void*)*14 + 23);
lean_dec(v_a_3761_);
if (v_lia_3765_ == 0)
{
lean_object* v___x_3766_; lean_object* v___x_3768_; 
lean_dec_ref(v_e_3744_);
v___x_3766_ = lean_box(0);
if (v_isShared_3764_ == 0)
{
lean_ctor_set(v___x_3763_, 0, v___x_3766_);
v___x_3768_ = v___x_3763_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v___x_3766_);
v___x_3768_ = v_reuseFailAlloc_3769_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
return v___x_3768_;
}
}
else
{
lean_object* v___x_3770_; uint8_t v___x_3771_; 
lean_inc_ref(v_e_3744_);
v___x_3770_ = l_Lean_Expr_cleanupAnnotations(v_e_3744_);
v___x_3771_ = l_Lean_Expr_isApp(v___x_3770_);
if (v___x_3771_ == 0)
{
lean_dec_ref(v___x_3770_);
lean_del_object(v___x_3763_);
lean_dec_ref(v_e_3744_);
goto v___jp_3757_;
}
else
{
lean_object* v___x_3772_; uint8_t v___x_3773_; 
v___x_3772_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3770_);
v___x_3773_ = l_Lean_Expr_isApp(v___x_3772_);
if (v___x_3773_ == 0)
{
lean_dec_ref(v___x_3772_);
lean_del_object(v___x_3763_);
lean_dec_ref(v_e_3744_);
goto v___jp_3757_;
}
else
{
lean_object* v___x_3774_; uint8_t v___x_3775_; 
v___x_3774_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3772_);
v___x_3775_ = l_Lean_Expr_isApp(v___x_3774_);
if (v___x_3775_ == 0)
{
lean_dec_ref(v___x_3774_);
lean_del_object(v___x_3763_);
lean_dec_ref(v_e_3744_);
goto v___jp_3757_;
}
else
{
lean_object* v___x_3776_; uint8_t v___x_3777_; 
v___x_3776_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3774_);
v___x_3777_ = l_Lean_Expr_isApp(v___x_3776_);
if (v___x_3777_ == 0)
{
lean_dec_ref(v___x_3776_);
lean_del_object(v___x_3763_);
lean_dec_ref(v_e_3744_);
goto v___jp_3757_;
}
else
{
lean_object* v_arg_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; uint8_t v___x_3781_; 
v_arg_3778_ = lean_ctor_get(v___x_3776_, 1);
lean_inc_ref(v_arg_3778_);
v___x_3779_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3776_);
v___x_3780_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2));
v___x_3781_ = l_Lean_Expr_isConstOf(v___x_3779_, v___x_3780_);
lean_dec_ref(v___x_3779_);
if (v___x_3781_ == 0)
{
lean_dec_ref(v_arg_3778_);
lean_del_object(v___x_3763_);
lean_dec_ref(v_e_3744_);
goto v___jp_3757_;
}
else
{
lean_object* v___x_3782_; uint8_t v___x_3783_; 
v___x_3782_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__0));
v___x_3783_ = l_Lean_Expr_isConstOf(v_arg_3778_, v___x_3782_);
if (v___x_3783_ == 0)
{
lean_object* v___x_3784_; uint8_t v___x_3785_; 
v___x_3784_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__2));
v___x_3785_ = l_Lean_Expr_isConstOf(v_arg_3778_, v___x_3784_);
lean_dec_ref(v_arg_3778_);
if (v___x_3785_ == 0)
{
lean_object* v___x_3786_; lean_object* v___x_3788_; 
lean_dec_ref(v_e_3744_);
v___x_3786_ = lean_box(0);
if (v_isShared_3764_ == 0)
{
lean_ctor_set(v___x_3763_, 0, v___x_3786_);
v___x_3788_ = v___x_3763_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v___x_3786_);
v___x_3788_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
return v___x_3788_;
}
}
else
{
lean_object* v___x_3790_; 
lean_del_object(v___x_3763_);
v___x_3790_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe(v_e_3744_, v_eqTrue_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_, v_a_3753_, v_a_3754_, v_a_3755_);
return v___x_3790_;
}
}
else
{
lean_object* v___x_3791_; 
lean_dec_ref(v_arg_3778_);
lean_del_object(v___x_3763_);
v___x_3791_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe(v_e_3744_, v_eqTrue_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_, v_a_3753_, v_a_3754_, v_a_3755_);
return v___x_3791_;
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
lean_object* v_a_3793_; lean_object* v___x_3795_; uint8_t v_isShared_3796_; uint8_t v_isSharedCheck_3800_; 
lean_dec_ref(v_e_3744_);
v_a_3793_ = lean_ctor_get(v___x_3760_, 0);
v_isSharedCheck_3800_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3800_ == 0)
{
v___x_3795_ = v___x_3760_;
v_isShared_3796_ = v_isSharedCheck_3800_;
goto v_resetjp_3794_;
}
else
{
lean_inc(v_a_3793_);
lean_dec(v___x_3760_);
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
v___jp_3757_:
{
lean_object* v___x_3758_; lean_object* v___x_3759_; 
v___x_3758_ = lean_box(0);
v___x_3759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3759_, 0, v___x_3758_);
return v___x_3759_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_Grind_Arith_Cutsat_propagateLe_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_3744_ = stack[0].m_obj;
uint8_t v_eqTrue_3745_ = stack[1].m_num;
lean_object* v_a_3746_ = stack[2].m_obj;
lean_object* v_a_3747_ = stack[3].m_obj;
lean_object* v_a_3748_ = stack[4].m_obj;
lean_object* v_a_3749_ = stack[5].m_obj;
lean_object* v_a_3750_ = stack[6].m_obj;
lean_object* v_a_3751_ = stack[7].m_obj;
lean_object* v_a_3752_ = stack[8].m_obj;
lean_object* v_a_3753_ = stack[9].m_obj;
lean_object* v_a_3754_ = stack[10].m_obj;
lean_object* v_a_3755_ = stack[11].m_obj;
lean_object* v_res_3801_;
v_res_3801_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLe(v_e_3744_, v_eqTrue_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_, v_a_3753_, v_a_3754_, v_a_3755_);
stack->m_obj
 = v_res_3801_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___boxed(lean_object* v_e_3802_, lean_object* v_eqTrue_3803_, lean_object* v_a_3804_, lean_object* v_a_3805_, lean_object* v_a_3806_, lean_object* v_a_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_, lean_object* v_a_3811_, lean_object* v_a_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_){
_start:
{
uint8_t v_eqTrue_boxed_3815_; lean_object* v_res_3816_; 
v_eqTrue_boxed_3815_ = lean_unbox(v_eqTrue_3803_);
v_res_3816_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLe(v_e_3802_, v_eqTrue_boxed_3815_, v_a_3804_, v_a_3805_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_, v_a_3812_, v_a_3813_);
lean_dec(v_a_3813_);
lean_dec_ref(v_a_3812_);
lean_dec(v_a_3811_);
lean_dec_ref(v_a_3810_);
lean_dec(v_a_3809_);
lean_dec_ref(v_a_3808_);
lean_dec(v_a_3807_);
lean_dec_ref(v_a_3806_);
lean_dec(v_a_3805_);
lean_dec(v_a_3804_);
return v_res_3816_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_OfNat(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Proof(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Nat(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_CommRing(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
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
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin);
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
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
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
