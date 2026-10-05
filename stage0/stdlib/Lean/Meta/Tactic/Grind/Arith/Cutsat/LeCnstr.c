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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0_spec__0(lean_object* v_msgData_19_, lean_object* v___y_20_, lean_object* v___y_21_, lean_object* v___y_22_, lean_object* v___y_23_){
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0_spec__0___boxed(lean_object* v_msgData_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0_spec__0(v_msgData_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
lean_dec(v___y_39_);
lean_dec_ref(v___y_38_);
return v_res_43_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_44_; double v___x_45_; 
v___x_44_ = lean_unsigned_to_nat(0u);
v___x_45_ = lean_float_of_nat(v___x_44_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(lean_object* v_cls_49_, lean_object* v_msg_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_){
_start:
{
lean_object* v_ref_56_; lean_object* v___x_57_; lean_object* v_a_58_; lean_object* v___x_60_; uint8_t v_isShared_61_; uint8_t v_isSharedCheck_103_; 
v_ref_56_ = lean_ctor_get(v___y_53_, 2);
v___x_57_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0_spec__0(v_msg_50_, v___y_51_, v___y_52_, v___y_53_, v___y_54_);
v_a_58_ = lean_ctor_get(v___x_57_, 0);
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_57_);
if (v_isSharedCheck_103_ == 0)
{
v___x_60_ = v___x_57_;
v_isShared_61_ = v_isSharedCheck_103_;
goto v_resetjp_59_;
}
else
{
lean_inc(v_a_58_);
lean_dec(v___x_57_);
v___x_60_ = lean_box(0);
v_isShared_61_ = v_isSharedCheck_103_;
goto v_resetjp_59_;
}
v_resetjp_59_:
{
lean_object* v___x_62_; lean_object* v_traceState_63_; lean_object* v_env_64_; lean_object* v_nextMacroScope_65_; lean_object* v_ngen_66_; lean_object* v_auxDeclNGen_67_; lean_object* v_cache_68_; lean_object* v_recordedDeps_69_; lean_object* v_messages_70_; lean_object* v_infoState_71_; lean_object* v_snapshotTasks_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_102_; 
v___x_62_ = lean_st_ref_take(v___y_54_);
v_traceState_63_ = lean_ctor_get(v___x_62_, 4);
v_env_64_ = lean_ctor_get(v___x_62_, 0);
v_nextMacroScope_65_ = lean_ctor_get(v___x_62_, 1);
v_ngen_66_ = lean_ctor_get(v___x_62_, 2);
v_auxDeclNGen_67_ = lean_ctor_get(v___x_62_, 3);
v_cache_68_ = lean_ctor_get(v___x_62_, 5);
v_recordedDeps_69_ = lean_ctor_get(v___x_62_, 6);
v_messages_70_ = lean_ctor_get(v___x_62_, 7);
v_infoState_71_ = lean_ctor_get(v___x_62_, 8);
v_snapshotTasks_72_ = lean_ctor_get(v___x_62_, 9);
v_isSharedCheck_102_ = !lean_is_exclusive(v___x_62_);
if (v_isSharedCheck_102_ == 0)
{
v___x_74_ = v___x_62_;
v_isShared_75_ = v_isSharedCheck_102_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_snapshotTasks_72_);
lean_inc(v_infoState_71_);
lean_inc(v_messages_70_);
lean_inc(v_recordedDeps_69_);
lean_inc(v_cache_68_);
lean_inc(v_traceState_63_);
lean_inc(v_auxDeclNGen_67_);
lean_inc(v_ngen_66_);
lean_inc(v_nextMacroScope_65_);
lean_inc(v_env_64_);
lean_dec(v___x_62_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_102_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
uint64_t v_tid_76_; lean_object* v_traces_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_101_; 
v_tid_76_ = lean_ctor_get_uint64(v_traceState_63_, sizeof(void*)*1);
v_traces_77_ = lean_ctor_get(v_traceState_63_, 0);
v_isSharedCheck_101_ = !lean_is_exclusive(v_traceState_63_);
if (v_isSharedCheck_101_ == 0)
{
v___x_79_ = v_traceState_63_;
v_isShared_80_ = v_isSharedCheck_101_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_traces_77_);
lean_dec(v_traceState_63_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_101_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_81_; lean_object* v___x_82_; double v___x_83_; uint8_t v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_92_; 
v___x_81_ = lean_box(0);
v___x_82_ = lean_box(0);
v___x_83_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__0);
v___x_84_ = 0;
v___x_85_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__1));
v___x_86_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_86_, 0, v_cls_49_);
lean_ctor_set(v___x_86_, 1, v___x_82_);
lean_ctor_set(v___x_86_, 2, v___x_85_);
lean_ctor_set_float(v___x_86_, sizeof(void*)*3, v___x_83_);
lean_ctor_set_float(v___x_86_, sizeof(void*)*3 + 8, v___x_83_);
lean_ctor_set_uint8(v___x_86_, sizeof(void*)*3 + 16, v___x_84_);
v___x_87_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___closed__2));
v___x_88_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_88_, 0, v___x_86_);
lean_ctor_set(v___x_88_, 1, v_a_58_);
lean_ctor_set(v___x_88_, 2, v___x_87_);
lean_inc(v_ref_56_);
v___x_89_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_89_, 0, v_ref_56_);
lean_ctor_set(v___x_89_, 1, v___x_88_);
v___x_90_ = l_Lean_PersistentArray_push___redArg(v_traces_77_, v___x_89_);
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 0, v___x_90_);
v___x_92_ = v___x_79_;
goto v_reusejp_91_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v___x_90_);
lean_ctor_set_uint64(v_reuseFailAlloc_100_, sizeof(void*)*1, v_tid_76_);
v___x_92_ = v_reuseFailAlloc_100_;
goto v_reusejp_91_;
}
v_reusejp_91_:
{
lean_object* v___x_94_; 
if (v_isShared_75_ == 0)
{
lean_ctor_set(v___x_74_, 4, v___x_92_);
v___x_94_ = v___x_74_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_99_; 
v_reuseFailAlloc_99_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_99_, 0, v_env_64_);
lean_ctor_set(v_reuseFailAlloc_99_, 1, v_nextMacroScope_65_);
lean_ctor_set(v_reuseFailAlloc_99_, 2, v_ngen_66_);
lean_ctor_set(v_reuseFailAlloc_99_, 3, v_auxDeclNGen_67_);
lean_ctor_set(v_reuseFailAlloc_99_, 4, v___x_92_);
lean_ctor_set(v_reuseFailAlloc_99_, 5, v_cache_68_);
lean_ctor_set(v_reuseFailAlloc_99_, 6, v_recordedDeps_69_);
lean_ctor_set(v_reuseFailAlloc_99_, 7, v_messages_70_);
lean_ctor_set(v_reuseFailAlloc_99_, 8, v_infoState_71_);
lean_ctor_set(v_reuseFailAlloc_99_, 9, v_snapshotTasks_72_);
v___x_94_ = v_reuseFailAlloc_99_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
lean_object* v___x_95_; lean_object* v___x_97_; 
v___x_95_ = lean_st_ref_put(v___y_54_, v___x_94_);
if (v_isShared_61_ == 0)
{
lean_ctor_set(v___x_60_, 0, v___x_81_);
v___x_97_ = v___x_60_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v___x_81_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg___boxed(lean_object* v_cls_104_, lean_object* v_msg_105_, lean_object* v___y_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v_cls_104_, v_msg_105_, v___y_106_, v___y_107_, v___y_108_, v___y_109_);
lean_dec(v___y_109_);
lean_dec_ref(v___y_108_);
lean_dec(v___y_107_);
lean_dec_ref(v___y_106_);
return v_res_111_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6(void){
_start:
{
lean_object* v_cls_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v_cls_122_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__3));
v___x_123_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_124_ = l_Lean_Name_append(v___x_123_, v_cls_122_);
return v___x_124_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__8(void){
_start:
{
lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_126_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__7));
v___x_127_ = l_Lean_stringToMessageData(v___x_126_);
return v___x_127_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_128_ = lean_unsigned_to_nat(0u);
v___x_129_ = lean_nat_to_int(v___x_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq(lean_object* v_a_130_, lean_object* v_x_131_, lean_object* v_c_u2081_132_, lean_object* v_b_133_, lean_object* v_c_u2082_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_, lean_object* v_a_139_, lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_){
_start:
{
lean_object* v___y_147_; lean_object* v___y_152_; lean_object* v_p_205_; lean_object* v_p_206_; lean_object* v___x_207_; uint8_t v___x_208_; 
v_p_205_ = lean_ctor_get(v_c_u2081_132_, 0);
v_p_206_ = lean_ctor_get(v_c_u2082_134_, 0);
v___x_207_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9);
v___x_208_ = lean_int_dec_le(v___x_207_, v_a_130_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
lean_inc_ref(v_p_205_);
v___x_209_ = l_Int_Internal_Linear_Poly_mul(v_p_205_, v_b_133_);
v___x_210_ = lean_int_neg(v_a_130_);
lean_inc_ref(v_p_206_);
v___x_211_ = l_Int_Internal_Linear_Poly_mul(v_p_206_, v___x_210_);
lean_dec(v___x_210_);
v___x_212_ = l_Int_Internal_Linear_Poly_combine(v___x_209_, v___x_211_);
v___y_152_ = v___x_212_;
goto v___jp_151_;
}
else
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
lean_inc_ref(v_p_206_);
v___x_213_ = l_Int_Internal_Linear_Poly_mul(v_p_206_, v_a_130_);
v___x_214_ = lean_int_neg(v_b_133_);
lean_inc_ref(v_p_205_);
v___x_215_ = l_Int_Internal_Linear_Poly_mul(v_p_205_, v___x_214_);
lean_dec(v___x_214_);
v___x_216_ = l_Int_Internal_Linear_Poly_combine(v___x_213_, v___x_215_);
v___y_152_ = v___x_216_;
goto v___jp_151_;
}
v___jp_146_:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_148_ = lean_alloc_ctor(10, 3, 0);
lean_ctor_set(v___x_148_, 0, v_x_131_);
lean_ctor_set(v___x_148_, 1, v_c_u2081_132_);
lean_ctor_set(v___x_148_, 2, v_c_u2082_134_);
v___x_149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_149_, 0, v___y_147_);
lean_ctor_set(v___x_149_, 1, v___x_148_);
v___x_150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_150_, 0, v___x_149_);
return v___x_150_;
}
v___jp_151_:
{
lean_object* v_toCold_153_; lean_object* v_options_154_; uint8_t v_hasTrace_155_; 
v_toCold_153_ = lean_ctor_get(v_a_143_, 0);
v_options_154_ = lean_ctor_get(v_toCold_153_, 2);
v_hasTrace_155_ = lean_ctor_get_uint8(v_options_154_, sizeof(void*)*1);
if (v_hasTrace_155_ == 0)
{
v___y_147_ = v___y_152_;
goto v___jp_146_;
}
else
{
lean_object* v_inheritedTraceOptions_156_; lean_object* v_cls_157_; lean_object* v___x_158_; uint8_t v___x_159_; 
v_inheritedTraceOptions_156_ = lean_ctor_get(v_toCold_153_, 11);
v_cls_157_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__3));
v___x_158_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__6);
v___x_159_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_156_, v_options_154_, v___x_158_);
if (v___x_159_ == 0)
{
v___y_147_ = v___y_152_;
goto v___jp_146_;
}
else
{
lean_object* v___x_160_; 
v___x_160_ = l_Lean_Meta_Grind_Arith_Cutsat_getVar___redArg(v_x_131_, v_a_135_, v_a_143_);
if (lean_obj_tag(v___x_160_) == 0)
{
lean_object* v_a_161_; lean_object* v___x_162_; 
v_a_161_ = lean_ctor_get(v___x_160_, 0);
lean_inc(v_a_161_);
lean_dec_ref_known(v___x_160_, 1);
lean_inc_ref(v_c_u2081_132_);
v___x_162_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v_c_u2081_132_, v_a_135_, v_a_143_);
if (lean_obj_tag(v___x_162_) == 0)
{
lean_object* v_a_163_; lean_object* v___x_164_; 
v_a_163_ = lean_ctor_get(v___x_162_, 0);
lean_inc(v_a_163_);
lean_dec_ref_known(v___x_162_, 1);
lean_inc_ref(v_c_u2082_134_);
v___x_164_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_u2082_134_, v_a_135_, v_a_143_);
if (lean_obj_tag(v___x_164_) == 0)
{
lean_object* v_a_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v_a_165_ = lean_ctor_get(v___x_164_, 0);
lean_inc(v_a_165_);
lean_dec_ref_known(v___x_164_, 1);
v___x_166_ = l_Lean_MessageData_ofExpr(v_a_161_);
v___x_167_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__8);
v___x_168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_166_);
lean_ctor_set(v___x_168_, 1, v___x_167_);
v___x_169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
lean_ctor_set(v___x_169_, 1, v_a_163_);
v___x_170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
lean_ctor_set(v___x_170_, 1, v___x_167_);
v___x_171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
lean_ctor_set(v___x_171_, 1, v_a_165_);
v___x_172_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v_cls_157_, v___x_171_, v_a_141_, v_a_142_, v_a_143_, v_a_144_);
if (lean_obj_tag(v___x_172_) == 0)
{
lean_dec_ref_known(v___x_172_, 1);
v___y_147_ = v___y_152_;
goto v___jp_146_;
}
else
{
lean_object* v_a_173_; lean_object* v___x_175_; uint8_t v_isShared_176_; uint8_t v_isSharedCheck_180_; 
lean_dec_ref(v___y_152_);
lean_dec_ref(v_c_u2082_134_);
lean_dec_ref(v_c_u2081_132_);
lean_dec(v_x_131_);
v_a_173_ = lean_ctor_get(v___x_172_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v___x_172_);
if (v_isSharedCheck_180_ == 0)
{
v___x_175_ = v___x_172_;
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
else
{
lean_inc(v_a_173_);
lean_dec(v___x_172_);
v___x_175_ = lean_box(0);
v_isShared_176_ = v_isSharedCheck_180_;
goto v_resetjp_174_;
}
v_resetjp_174_:
{
lean_object* v___x_178_; 
if (v_isShared_176_ == 0)
{
v___x_178_ = v___x_175_;
goto v_reusejp_177_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_a_173_);
v___x_178_ = v_reuseFailAlloc_179_;
goto v_reusejp_177_;
}
v_reusejp_177_:
{
return v___x_178_;
}
}
}
}
else
{
lean_object* v_a_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_188_; 
lean_dec(v_a_163_);
lean_dec(v_a_161_);
lean_dec_ref(v___y_152_);
lean_dec_ref(v_c_u2082_134_);
lean_dec_ref(v_c_u2081_132_);
lean_dec(v_x_131_);
v_a_181_ = lean_ctor_get(v___x_164_, 0);
v_isSharedCheck_188_ = !lean_is_exclusive(v___x_164_);
if (v_isSharedCheck_188_ == 0)
{
v___x_183_ = v___x_164_;
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_a_181_);
lean_dec(v___x_164_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_186_; 
if (v_isShared_184_ == 0)
{
v___x_186_ = v___x_183_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_a_181_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
}
else
{
lean_object* v_a_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_196_; 
lean_dec(v_a_161_);
lean_dec_ref(v___y_152_);
lean_dec_ref(v_c_u2082_134_);
lean_dec_ref(v_c_u2081_132_);
lean_dec(v_x_131_);
v_a_189_ = lean_ctor_get(v___x_162_, 0);
v_isSharedCheck_196_ = !lean_is_exclusive(v___x_162_);
if (v_isSharedCheck_196_ == 0)
{
v___x_191_ = v___x_162_;
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_a_189_);
lean_dec(v___x_162_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_196_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_194_; 
if (v_isShared_192_ == 0)
{
v___x_194_ = v___x_191_;
goto v_reusejp_193_;
}
else
{
lean_object* v_reuseFailAlloc_195_; 
v_reuseFailAlloc_195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_195_, 0, v_a_189_);
v___x_194_ = v_reuseFailAlloc_195_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
return v___x_194_;
}
}
}
}
else
{
lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_204_; 
lean_dec_ref(v___y_152_);
lean_dec_ref(v_c_u2082_134_);
lean_dec_ref(v_c_u2081_132_);
lean_dec(v_x_131_);
v_a_197_ = lean_ctor_get(v___x_160_, 0);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_204_ == 0)
{
v___x_199_ = v___x_160_;
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_dec(v___x_160_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_202_; 
if (v_isShared_200_ == 0)
{
v___x_202_ = v___x_199_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_a_197_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___boxed(lean_object* v_a_217_, lean_object* v_x_218_, lean_object* v_c_u2081_219_, lean_object* v_b_220_, lean_object* v_c_u2082_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq(v_a_217_, v_x_218_, v_c_u2081_219_, v_b_220_, v_c_u2082_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_, v_a_230_, v_a_231_);
lean_dec(v_a_231_);
lean_dec_ref(v_a_230_);
lean_dec(v_a_229_);
lean_dec_ref(v_a_228_);
lean_dec(v_a_227_);
lean_dec_ref(v_a_226_);
lean_dec(v_a_225_);
lean_dec_ref(v_a_224_);
lean_dec(v_a_223_);
lean_dec(v_a_222_);
lean_dec(v_b_220_);
lean_dec(v_a_217_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0(lean_object* v_cls_234_, lean_object* v_msg_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_, lean_object* v___y_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v_cls_234_, v_msg_235_, v___y_242_, v___y_243_, v___y_244_, v___y_245_);
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___boxed(lean_object* v_cls_248_, lean_object* v_msg_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_, lean_object* v___y_260_){
_start:
{
lean_object* v_res_261_; 
v_res_261_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0(v_cls_248_, v_msg_249_, v___y_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_);
lean_dec(v___y_259_);
lean_dec_ref(v___y_258_);
lean_dec(v___y_257_);
lean_dec_ref(v___y_256_);
lean_dec(v___y_255_);
lean_dec_ref(v___y_254_);
lean_dec(v___y_253_);
lean_dec_ref(v___y_252_);
lean_dec(v___y_251_);
lean_dec(v___y_250_);
return v_res_261_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = l_Lean_maxRecDepthErrorMessage;
v___x_268_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_268_, 0, v___x_267_);
return v___x_268_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__4(void){
_start:
{
lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_269_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__3);
v___x_270_ = l_Lean_MessageData_ofFormat(v___x_269_);
return v___x_270_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_271_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__4);
v___x_272_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__2));
v___x_273_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
lean_ctor_set(v___x_273_, 1, v___x_271_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg(lean_object* v_ref_274_){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_276_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___closed__5);
v___x_277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_277_, 0, v_ref_274_);
lean_ctor_set(v___x_277_, 1, v___x_276_);
v___x_278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg___boxed(lean_object* v_ref_279_, lean_object* v___y_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg(v_ref_279_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0(lean_object* v_00_u03b1_282_, lean_object* v_ref_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v___x_295_; 
v___x_295_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg(v_ref_283_);
return v___x_295_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___boxed(lean_object* v_00_u03b1_296_, lean_object* v_ref_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_){
_start:
{
lean_object* v_res_309_; 
v_res_309_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0(v_00_u03b1_296_, v_ref_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_, v___y_307_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
lean_dec(v___y_299_);
lean_dec(v___y_298_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts(lean_object* v_c_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_){
_start:
{
lean_object* v_p_322_; lean_object* v_toCold_323_; lean_object* v_currRecDepth_324_; lean_object* v_ref_325_; uint16_t v_optionFlags_326_; uint8_t v_suppressElabErrors_327_; uint8_t v_isRecordingDeps_328_; lean_object* v_maxRecDepth_360_; lean_object* v___x_361_; uint8_t v___x_362_; 
v_p_322_ = lean_ctor_get(v_c_310_, 0);
v_toCold_323_ = lean_ctor_get(v_a_319_, 0);
lean_inc_ref(v_toCold_323_);
v_currRecDepth_324_ = lean_ctor_get(v_a_319_, 1);
lean_inc(v_currRecDepth_324_);
v_ref_325_ = lean_ctor_get(v_a_319_, 2);
lean_inc(v_ref_325_);
v_optionFlags_326_ = lean_ctor_get_uint16(v_a_319_, sizeof(void*)*3);
v_suppressElabErrors_327_ = lean_ctor_get_uint8(v_a_319_, sizeof(void*)*3 + 2);
v_isRecordingDeps_328_ = lean_ctor_get_uint8(v_a_319_, sizeof(void*)*3 + 3);
lean_dec_ref(v_a_319_);
v_maxRecDepth_360_ = lean_ctor_get(v_toCold_323_, 3);
v___x_361_ = lean_unsigned_to_nat(0u);
v___x_362_ = lean_nat_dec_eq(v_maxRecDepth_360_, v___x_361_);
if (v___x_362_ == 0)
{
uint8_t v___x_363_; 
v___x_363_ = lean_nat_dec_eq(v_currRecDepth_324_, v_maxRecDepth_360_);
if (v___x_363_ == 0)
{
goto v___jp_329_;
}
else
{
lean_object* v___x_364_; 
lean_dec(v_currRecDepth_324_);
lean_dec_ref(v_toCold_323_);
lean_dec_ref(v_c_310_);
v___x_364_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg(v_ref_325_);
return v___x_364_;
}
}
else
{
goto v___jp_329_;
}
v___jp_329_:
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_330_ = lean_unsigned_to_nat(1u);
v___x_331_ = lean_nat_add(v_currRecDepth_324_, v___x_330_);
lean_dec(v_currRecDepth_324_);
v___x_332_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_332_, 0, v_toCold_323_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
lean_ctor_set(v___x_332_, 2, v_ref_325_);
lean_ctor_set_uint16(v___x_332_, sizeof(void*)*3, v_optionFlags_326_);
lean_ctor_set_uint8(v___x_332_, sizeof(void*)*3 + 2, v_suppressElabErrors_327_);
lean_ctor_set_uint8(v___x_332_, sizeof(void*)*3 + 3, v_isRecordingDeps_328_);
lean_inc_ref(v_p_322_);
v___x_333_ = l_Int_Internal_Linear_Poly_findVarToSubst___redArg(v_p_322_, v_a_311_, v___x_332_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_a_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_351_; 
v_a_334_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_351_ == 0)
{
v___x_336_ = v___x_333_;
v_isShared_337_ = v_isSharedCheck_351_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_a_334_);
lean_dec(v___x_333_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_351_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
if (lean_obj_tag(v_a_334_) == 1)
{
lean_object* v_val_338_; lean_object* v_snd_339_; lean_object* v_snd_340_; lean_object* v_fst_341_; lean_object* v_fst_342_; lean_object* v_p_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
lean_del_object(v___x_336_);
v_val_338_ = lean_ctor_get(v_a_334_, 0);
lean_inc(v_val_338_);
lean_dec_ref_known(v_a_334_, 1);
v_snd_339_ = lean_ctor_get(v_val_338_, 1);
lean_inc(v_snd_339_);
v_snd_340_ = lean_ctor_get(v_snd_339_, 1);
lean_inc(v_snd_340_);
v_fst_341_ = lean_ctor_get(v_val_338_, 0);
lean_inc(v_fst_341_);
lean_dec(v_val_338_);
v_fst_342_ = lean_ctor_get(v_snd_339_, 0);
lean_inc(v_fst_342_);
lean_dec(v_snd_339_);
v_p_343_ = lean_ctor_get(v_snd_340_, 0);
v___x_344_ = l_Int_Internal_Linear_Poly_coeff(v_p_343_, v_fst_342_);
v___x_345_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq(v___x_344_, v_fst_342_, v_snd_340_, v_fst_341_, v_c_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v___x_332_, v_a_320_);
lean_dec(v_fst_341_);
lean_dec(v___x_344_);
if (lean_obj_tag(v___x_345_) == 0)
{
lean_object* v_a_346_; 
v_a_346_ = lean_ctor_get(v___x_345_, 0);
lean_inc(v_a_346_);
lean_dec_ref_known(v___x_345_, 1);
v_c_310_ = v_a_346_;
v_a_319_ = v___x_332_;
goto _start;
}
else
{
lean_dec_ref_known(v___x_332_, 3);
return v___x_345_;
}
}
else
{
lean_object* v___x_349_; 
lean_dec(v_a_334_);
lean_dec_ref_known(v___x_332_, 3);
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 0, v_c_310_);
v___x_349_ = v___x_336_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v_c_310_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
else
{
lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_359_; 
lean_dec_ref_known(v___x_332_, 3);
lean_dec_ref(v_c_310_);
v_a_352_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_359_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_359_ == 0)
{
v___x_354_ = v___x_333_;
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v___x_333_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_359_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_357_; 
if (v_isShared_355_ == 0)
{
v___x_357_ = v___x_354_;
goto v_reusejp_356_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v_a_352_);
v___x_357_ = v_reuseFailAlloc_358_;
goto v_reusejp_356_;
}
v_reusejp_356_:
{
return v___x_357_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts___boxed(lean_object* v_c_365_, lean_object* v_a_366_, lean_object* v_a_367_, lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts(v_c_365_, v_a_366_, v_a_367_, v_a_368_, v_a_369_, v_a_370_, v_a_371_, v_a_372_, v_a_373_, v_a_374_, v_a_375_);
lean_dec(v_a_375_);
lean_dec(v_a_373_);
lean_dec_ref(v_a_372_);
lean_dec(v_a_371_);
lean_dec_ref(v_a_370_);
lean_dec(v_a_369_);
lean_dec_ref(v_a_368_);
lean_dec(v_a_367_);
lean_dec(v_a_366_);
return v_res_377_;
}
}
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_isNegEq(lean_object* v_p_u2081_378_, lean_object* v_p_u2082_379_){
_start:
{
if (lean_obj_tag(v_p_u2081_378_) == 0)
{
if (lean_obj_tag(v_p_u2082_379_) == 0)
{
lean_object* v_k_380_; lean_object* v_k_381_; lean_object* v___x_382_; uint8_t v___x_383_; 
v_k_380_ = lean_ctor_get(v_p_u2081_378_, 0);
v_k_381_ = lean_ctor_get(v_p_u2082_379_, 0);
v___x_382_ = lean_int_neg(v_k_381_);
v___x_383_ = lean_int_dec_eq(v_k_380_, v___x_382_);
lean_dec(v___x_382_);
return v___x_383_;
}
else
{
uint8_t v___x_384_; 
v___x_384_ = 0;
return v___x_384_;
}
}
else
{
if (lean_obj_tag(v_p_u2082_379_) == 1)
{
lean_object* v_k_385_; lean_object* v_v_386_; lean_object* v_p_387_; lean_object* v_k_388_; lean_object* v_v_389_; lean_object* v_p_390_; lean_object* v___x_391_; uint8_t v___x_392_; 
v_k_385_ = lean_ctor_get(v_p_u2081_378_, 0);
v_v_386_ = lean_ctor_get(v_p_u2081_378_, 1);
v_p_387_ = lean_ctor_get(v_p_u2081_378_, 2);
v_k_388_ = lean_ctor_get(v_p_u2082_379_, 0);
v_v_389_ = lean_ctor_get(v_p_u2082_379_, 1);
v_p_390_ = lean_ctor_get(v_p_u2082_379_, 2);
v___x_391_ = lean_int_neg(v_k_388_);
v___x_392_ = lean_int_dec_eq(v_k_385_, v___x_391_);
lean_dec(v___x_391_);
if (v___x_392_ == 0)
{
return v___x_392_;
}
else
{
uint8_t v___x_393_; 
v___x_393_ = lean_nat_dec_eq(v_v_386_, v_v_389_);
if (v___x_393_ == 0)
{
return v___x_393_;
}
else
{
v_p_u2081_378_ = v_p_387_;
v_p_u2082_379_ = v_p_390_;
goto _start;
}
}
}
else
{
uint8_t v___x_395_; 
v___x_395_ = 0;
return v___x_395_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isNegEq___boxed(lean_object* v_p_u2081_396_, lean_object* v_p_u2082_397_){
_start:
{
uint8_t v_res_398_; lean_object* v_r_399_; 
v_res_398_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_u2081_396_, v_p_u2082_397_);
lean_dec_ref(v_p_u2082_397_);
lean_dec_ref(v_p_u2081_396_);
v_r_399_ = lean_box(v_res_398_);
return v_r_399_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(lean_object* v_c_400_, lean_object* v_as_401_, size_t v_i_402_, size_t v_stop_403_, lean_object* v_b_404_){
_start:
{
lean_object* v___y_406_; uint8_t v___x_410_; 
v___x_410_ = lean_usize_dec_eq(v_i_402_, v_stop_403_);
if (v___x_410_ == 0)
{
lean_object* v___x_411_; lean_object* v_p_412_; lean_object* v_p_413_; uint8_t v___x_414_; 
v___x_411_ = lean_array_uget_borrowed(v_as_401_, v_i_402_);
v_p_412_ = lean_ctor_get(v___x_411_, 0);
v_p_413_ = lean_ctor_get(v_c_400_, 0);
v___x_414_ = l_Int_Internal_Linear_instBEqPoly_beq(v_p_412_, v_p_413_);
if (v___x_414_ == 0)
{
lean_object* v___x_415_; 
lean_inc(v___x_411_);
v___x_415_ = l_Lean_PersistentArray_push___redArg(v_b_404_, v___x_411_);
v___y_406_ = v___x_415_;
goto v___jp_405_;
}
else
{
v___y_406_ = v_b_404_;
goto v___jp_405_;
}
}
else
{
return v_b_404_;
}
v___jp_405_:
{
size_t v___x_407_; size_t v___x_408_; 
v___x_407_ = ((size_t)1ULL);
v___x_408_ = lean_usize_add(v_i_402_, v___x_407_);
v_i_402_ = v___x_408_;
v_b_404_ = v___y_406_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1___boxed(lean_object* v_c_416_, lean_object* v_as_417_, lean_object* v_i_418_, lean_object* v_stop_419_, lean_object* v_b_420_){
_start:
{
size_t v_i_boxed_421_; size_t v_stop_boxed_422_; lean_object* v_res_423_; 
v_i_boxed_421_ = lean_unbox_usize(v_i_418_);
lean_dec(v_i_418_);
v_stop_boxed_422_ = lean_unbox_usize(v_stop_419_);
lean_dec(v_stop_419_);
v_res_423_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v_c_416_, v_as_417_, v_i_boxed_421_, v_stop_boxed_422_, v_b_420_);
lean_dec_ref(v_as_417_);
lean_dec_ref(v_c_416_);
return v_res_423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2(lean_object* v_c_424_, lean_object* v_x_425_, lean_object* v_x_426_){
_start:
{
if (lean_obj_tag(v_x_425_) == 0)
{
lean_object* v_cs_427_; lean_object* v___x_428_; lean_object* v___x_429_; uint8_t v___x_430_; 
v_cs_427_ = lean_ctor_get(v_x_425_, 0);
v___x_428_ = lean_unsigned_to_nat(0u);
v___x_429_ = lean_array_get_size(v_cs_427_);
v___x_430_ = lean_nat_dec_lt(v___x_428_, v___x_429_);
if (v___x_430_ == 0)
{
return v_x_426_;
}
else
{
size_t v___x_431_; size_t v___x_432_; lean_object* v___x_433_; 
v___x_431_ = ((size_t)0ULL);
v___x_432_ = lean_usize_of_nat(v___x_429_);
v___x_433_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v_c_424_, v_cs_427_, v___x_431_, v___x_432_, v_x_426_);
return v___x_433_;
}
}
else
{
lean_object* v_vs_434_; lean_object* v___x_435_; lean_object* v___x_436_; uint8_t v___x_437_; 
v_vs_434_ = lean_ctor_get(v_x_425_, 0);
v___x_435_ = lean_unsigned_to_nat(0u);
v___x_436_ = lean_array_get_size(v_vs_434_);
v___x_437_ = lean_nat_dec_lt(v___x_435_, v___x_436_);
if (v___x_437_ == 0)
{
return v_x_426_;
}
else
{
size_t v___x_438_; size_t v___x_439_; lean_object* v___x_440_; 
v___x_438_ = ((size_t)0ULL);
v___x_439_ = lean_usize_of_nat(v___x_436_);
v___x_440_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v_c_424_, v_vs_434_, v___x_438_, v___x_439_, v_x_426_);
return v___x_440_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(lean_object* v_c_441_, lean_object* v_as_442_, size_t v_i_443_, size_t v_stop_444_, lean_object* v_b_445_){
_start:
{
uint8_t v___x_446_; 
v___x_446_ = lean_usize_dec_eq(v_i_443_, v_stop_444_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; lean_object* v___x_448_; size_t v___x_449_; size_t v___x_450_; 
v___x_447_ = lean_array_uget_borrowed(v_as_442_, v_i_443_);
v___x_448_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2(v_c_441_, v___x_447_, v_b_445_);
v___x_449_ = ((size_t)1ULL);
v___x_450_ = lean_usize_add(v_i_443_, v___x_449_);
v_i_443_ = v___x_450_;
v_b_445_ = v___x_448_;
goto _start;
}
else
{
return v_b_445_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1___boxed(lean_object* v_c_452_, lean_object* v_as_453_, lean_object* v_i_454_, lean_object* v_stop_455_, lean_object* v_b_456_){
_start:
{
size_t v_i_boxed_457_; size_t v_stop_boxed_458_; lean_object* v_res_459_; 
v_i_boxed_457_ = lean_unbox_usize(v_i_454_);
lean_dec(v_i_454_);
v_stop_boxed_458_ = lean_unbox_usize(v_stop_455_);
lean_dec(v_stop_455_);
v_res_459_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v_c_452_, v_as_453_, v_i_boxed_457_, v_stop_boxed_458_, v_b_456_);
lean_dec_ref(v_as_453_);
lean_dec_ref(v_c_452_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2___boxed(lean_object* v_c_460_, lean_object* v_x_461_, lean_object* v_x_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2(v_c_460_, v_x_461_, v_x_462_);
lean_dec_ref(v_x_461_);
lean_dec_ref(v_c_460_);
return v_res_463_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_464_; 
v___x_464_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(lean_object* v_c_465_, lean_object* v_x_466_, size_t v_x_467_, size_t v_x_468_, lean_object* v_x_469_){
_start:
{
if (lean_obj_tag(v_x_466_) == 0)
{
lean_object* v_cs_470_; lean_object* v___x_471_; size_t v___x_472_; lean_object* v_j_473_; lean_object* v___x_474_; size_t v___x_475_; size_t v___x_476_; size_t v___x_477_; size_t v___x_478_; size_t v___x_479_; size_t v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; uint8_t v___x_485_; 
v_cs_470_ = lean_ctor_get(v_x_466_, 0);
v___x_471_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0);
v___x_472_ = lean_usize_shift_right(v_x_467_, v_x_468_);
v_j_473_ = lean_usize_to_nat(v___x_472_);
v___x_474_ = lean_array_get_borrowed(v___x_471_, v_cs_470_, v_j_473_);
v___x_475_ = ((size_t)1ULL);
v___x_476_ = lean_usize_shift_left(v___x_475_, v_x_468_);
v___x_477_ = lean_usize_sub(v___x_476_, v___x_475_);
v___x_478_ = lean_usize_land(v_x_467_, v___x_477_);
v___x_479_ = ((size_t)5ULL);
v___x_480_ = lean_usize_sub(v_x_468_, v___x_479_);
v___x_481_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(v_c_465_, v___x_474_, v___x_478_, v___x_480_, v_x_469_);
v___x_482_ = lean_unsigned_to_nat(1u);
v___x_483_ = lean_nat_add(v_j_473_, v___x_482_);
lean_dec(v_j_473_);
v___x_484_ = lean_array_get_size(v_cs_470_);
v___x_485_ = lean_nat_dec_lt(v___x_483_, v___x_484_);
if (v___x_485_ == 0)
{
lean_dec(v___x_483_);
return v___x_481_;
}
else
{
size_t v___x_486_; size_t v___x_487_; lean_object* v___x_488_; 
v___x_486_ = lean_usize_of_nat(v___x_483_);
lean_dec(v___x_483_);
v___x_487_ = lean_usize_of_nat(v___x_484_);
v___x_488_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v_c_465_, v_cs_470_, v___x_486_, v___x_487_, v___x_481_);
return v___x_488_;
}
}
else
{
lean_object* v_vs_489_; lean_object* v___x_490_; lean_object* v___x_491_; uint8_t v___x_492_; 
v_vs_489_ = lean_ctor_get(v_x_466_, 0);
v___x_490_ = lean_usize_to_nat(v_x_467_);
v___x_491_ = lean_array_get_size(v_vs_489_);
v___x_492_ = lean_nat_dec_lt(v___x_490_, v___x_491_);
if (v___x_492_ == 0)
{
lean_dec(v___x_490_);
return v_x_469_;
}
else
{
size_t v___x_493_; size_t v___x_494_; lean_object* v___x_495_; 
v___x_493_ = lean_usize_of_nat(v___x_490_);
lean_dec(v___x_490_);
v___x_494_ = lean_usize_of_nat(v___x_491_);
v___x_495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v_c_465_, v_vs_489_, v___x_493_, v___x_494_, v_x_469_);
return v___x_495_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___boxed(lean_object* v_c_496_, lean_object* v_x_497_, lean_object* v_x_498_, lean_object* v_x_499_, lean_object* v_x_500_){
_start:
{
size_t v_x_1565__boxed_501_; size_t v_x_1566__boxed_502_; lean_object* v_res_503_; 
v_x_1565__boxed_501_ = lean_unbox_usize(v_x_498_);
lean_dec(v_x_498_);
v_x_1566__boxed_502_ = lean_unbox_usize(v_x_499_);
lean_dec(v_x_499_);
v_res_503_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(v_c_496_, v_x_497_, v_x_1565__boxed_501_, v_x_1566__boxed_502_, v_x_500_);
lean_dec_ref(v_x_497_);
lean_dec_ref(v_c_496_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(lean_object* v_c_504_, lean_object* v_t_505_, lean_object* v_init_506_, lean_object* v_start_507_){
_start:
{
lean_object* v___x_508_; uint8_t v___x_509_; 
v___x_508_ = lean_unsigned_to_nat(0u);
v___x_509_ = lean_nat_dec_eq(v_start_507_, v___x_508_);
if (v___x_509_ == 0)
{
lean_object* v_root_510_; lean_object* v_tail_511_; size_t v_shift_512_; lean_object* v_tailOff_513_; uint8_t v___x_514_; 
v_root_510_ = lean_ctor_get(v_t_505_, 0);
v_tail_511_ = lean_ctor_get(v_t_505_, 1);
v_shift_512_ = lean_ctor_get_usize(v_t_505_, 4);
v_tailOff_513_ = lean_ctor_get(v_t_505_, 3);
v___x_514_ = lean_nat_dec_le(v_tailOff_513_, v_start_507_);
if (v___x_514_ == 0)
{
size_t v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; uint8_t v___x_518_; 
v___x_515_ = lean_usize_of_nat(v_start_507_);
v___x_516_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(v_c_504_, v_root_510_, v___x_515_, v_shift_512_, v_init_506_);
v___x_517_ = lean_array_get_size(v_tail_511_);
v___x_518_ = lean_nat_dec_lt(v___x_508_, v___x_517_);
if (v___x_518_ == 0)
{
return v___x_516_;
}
else
{
size_t v___x_519_; size_t v___x_520_; lean_object* v___x_521_; 
v___x_519_ = ((size_t)0ULL);
v___x_520_ = lean_usize_of_nat(v___x_517_);
v___x_521_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v_c_504_, v_tail_511_, v___x_519_, v___x_520_, v___x_516_);
return v___x_521_;
}
}
else
{
lean_object* v___x_522_; lean_object* v___x_523_; uint8_t v___x_524_; 
v___x_522_ = lean_nat_sub(v_start_507_, v_tailOff_513_);
v___x_523_ = lean_array_get_size(v_tail_511_);
v___x_524_ = lean_nat_dec_lt(v___x_522_, v___x_523_);
if (v___x_524_ == 0)
{
lean_dec(v___x_522_);
return v_init_506_;
}
else
{
size_t v___x_525_; size_t v___x_526_; lean_object* v___x_527_; 
v___x_525_ = lean_usize_of_nat(v___x_522_);
lean_dec(v___x_522_);
v___x_526_ = lean_usize_of_nat(v___x_523_);
v___x_527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v_c_504_, v_tail_511_, v___x_525_, v___x_526_, v_init_506_);
return v___x_527_;
}
}
}
else
{
lean_object* v_root_528_; lean_object* v_tail_529_; lean_object* v___x_530_; lean_object* v___x_531_; uint8_t v___x_532_; 
v_root_528_ = lean_ctor_get(v_t_505_, 0);
v_tail_529_ = lean_ctor_get(v_t_505_, 1);
v___x_530_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2(v_c_504_, v_root_528_, v_init_506_);
v___x_531_ = lean_array_get_size(v_tail_529_);
v___x_532_ = lean_nat_dec_lt(v___x_508_, v___x_531_);
if (v___x_532_ == 0)
{
return v___x_530_;
}
else
{
size_t v___x_533_; size_t v___x_534_; lean_object* v___x_535_; 
v___x_533_ = ((size_t)0ULL);
v___x_534_ = lean_usize_of_nat(v___x_531_);
v___x_535_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v_c_504_, v_tail_529_, v___x_533_, v___x_534_, v___x_530_);
return v___x_535_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0___boxed(lean_object* v_c_536_, lean_object* v_t_537_, lean_object* v_init_538_, lean_object* v_start_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(v_c_536_, v_t_537_, v_init_538_, v_start_539_);
lean_dec(v_start_539_);
lean_dec_ref(v_t_537_);
lean_dec_ref(v_c_536_);
return v_res_540_;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_541_ = lean_unsigned_to_nat(32u);
v___x_542_ = lean_mk_empty_array_with_capacity(v___x_541_);
v___x_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
return v___x_543_;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1(void){
_start:
{
size_t v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_544_ = ((size_t)5ULL);
v___x_545_ = lean_unsigned_to_nat(0u);
v___x_546_ = lean_unsigned_to_nat(32u);
v___x_547_ = lean_mk_empty_array_with_capacity(v___x_546_);
v___x_548_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__0, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__0_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__0);
v___x_549_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_549_, 0, v___x_548_);
lean_ctor_set(v___x_549_, 1, v___x_547_);
lean_ctor_set(v___x_549_, 2, v___x_545_);
lean_ctor_set(v___x_549_, 3, v___x_545_);
lean_ctor_set_usize(v___x_549_, 4, v___x_544_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4(lean_object* v_c_550_, lean_object* v_x_551_, size_t v_x_552_, size_t v_x_553_){
_start:
{
if (lean_obj_tag(v_x_551_) == 0)
{
lean_object* v_cs_554_; size_t v_j_555_; lean_object* v___x_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v_cs_554_ = lean_ctor_get(v_x_551_, 0);
v_j_555_ = lean_usize_shift_right(v_x_552_, v_x_553_);
v___x_556_ = lean_usize_to_nat(v_j_555_);
v___x_557_ = lean_array_get_size(v_cs_554_);
v___x_558_ = lean_nat_dec_lt(v___x_556_, v___x_557_);
if (v___x_558_ == 0)
{
lean_dec(v___x_556_);
return v_x_551_;
}
else
{
lean_object* v___x_560_; uint8_t v_isShared_561_; uint8_t v_isSharedCheck_576_; 
lean_inc_ref(v_cs_554_);
v_isSharedCheck_576_ = !lean_is_exclusive(v_x_551_);
if (v_isSharedCheck_576_ == 0)
{
lean_object* v_unused_577_; 
v_unused_577_ = lean_ctor_get(v_x_551_, 0);
lean_dec(v_unused_577_);
v___x_560_ = v_x_551_;
v_isShared_561_ = v_isSharedCheck_576_;
goto v_resetjp_559_;
}
else
{
lean_dec(v_x_551_);
v___x_560_ = lean_box(0);
v_isShared_561_ = v_isSharedCheck_576_;
goto v_resetjp_559_;
}
v_resetjp_559_:
{
size_t v___x_562_; size_t v___x_563_; size_t v___x_564_; size_t v_i_565_; size_t v___x_566_; size_t v_shift_567_; lean_object* v_v_568_; lean_object* v___x_569_; lean_object* v_xs_x27_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_574_; 
v___x_562_ = ((size_t)1ULL);
v___x_563_ = lean_usize_shift_left(v___x_562_, v_x_553_);
v___x_564_ = lean_usize_sub(v___x_563_, v___x_562_);
v_i_565_ = lean_usize_land(v_x_552_, v___x_564_);
v___x_566_ = ((size_t)5ULL);
v_shift_567_ = lean_usize_sub(v_x_553_, v___x_566_);
v_v_568_ = lean_array_fget(v_cs_554_, v___x_556_);
v___x_569_ = lean_box(0);
v_xs_x27_570_ = lean_array_fset(v_cs_554_, v___x_556_, v___x_569_);
v___x_571_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4(v_c_550_, v_v_568_, v_i_565_, v_shift_567_);
v___x_572_ = lean_array_fset(v_xs_x27_570_, v___x_556_, v___x_571_);
lean_dec(v___x_556_);
if (v_isShared_561_ == 0)
{
lean_ctor_set(v___x_560_, 0, v___x_572_);
v___x_574_ = v___x_560_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v___x_572_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
}
else
{
lean_object* v_vs_578_; lean_object* v___x_579_; lean_object* v___x_580_; uint8_t v___x_581_; 
v_vs_578_ = lean_ctor_get(v_x_551_, 0);
v___x_579_ = lean_usize_to_nat(v_x_552_);
v___x_580_ = lean_array_get_size(v_vs_578_);
v___x_581_ = lean_nat_dec_lt(v___x_579_, v___x_580_);
if (v___x_581_ == 0)
{
lean_dec(v___x_579_);
return v_x_551_;
}
else
{
lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_595_; 
lean_inc_ref(v_vs_578_);
v_isSharedCheck_595_ = !lean_is_exclusive(v_x_551_);
if (v_isSharedCheck_595_ == 0)
{
lean_object* v_unused_596_; 
v_unused_596_ = lean_ctor_get(v_x_551_, 0);
lean_dec(v_unused_596_);
v___x_583_ = v_x_551_;
v_isShared_584_ = v_isSharedCheck_595_;
goto v_resetjp_582_;
}
else
{
lean_dec(v_x_551_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_595_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v_v_585_; lean_object* v___x_586_; lean_object* v_xs_x27_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_593_; 
v_v_585_ = lean_array_fget(v_vs_578_, v___x_579_);
v___x_586_ = lean_box(0);
v_xs_x27_587_ = lean_array_fset(v_vs_578_, v___x_579_, v___x_586_);
v___x_588_ = lean_unsigned_to_nat(0u);
v___x_589_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1);
v___x_590_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(v_c_550_, v_v_585_, v___x_589_, v___x_588_);
lean_dec(v_v_585_);
v___x_591_ = lean_array_fset(v_xs_x27_587_, v___x_579_, v___x_590_);
lean_dec(v___x_579_);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 0, v___x_591_);
v___x_593_ = v___x_583_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_594_; 
v_reuseFailAlloc_594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_594_, 0, v___x_591_);
v___x_593_ = v_reuseFailAlloc_594_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
return v___x_593_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___boxed(lean_object* v_c_597_, lean_object* v_x_598_, lean_object* v_x_599_, lean_object* v_x_600_){
_start:
{
size_t v_x_1692__boxed_601_; size_t v_x_1693__boxed_602_; lean_object* v_res_603_; 
v_x_1692__boxed_601_ = lean_unbox_usize(v_x_599_);
lean_dec(v_x_599_);
v_x_1693__boxed_602_ = lean_unbox_usize(v_x_600_);
lean_dec(v_x_600_);
v_res_603_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4(v_c_597_, v_x_598_, v_x_1692__boxed_601_, v_x_1693__boxed_602_);
lean_dec_ref(v_c_597_);
return v_res_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(lean_object* v_c_604_, lean_object* v_t_605_, lean_object* v_i_606_){
_start:
{
lean_object* v_root_607_; lean_object* v_tail_608_; lean_object* v_size_609_; size_t v_shift_610_; lean_object* v_tailOff_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_639_; 
v_root_607_ = lean_ctor_get(v_t_605_, 0);
v_tail_608_ = lean_ctor_get(v_t_605_, 1);
v_size_609_ = lean_ctor_get(v_t_605_, 2);
v_shift_610_ = lean_ctor_get_usize(v_t_605_, 4);
v_tailOff_611_ = lean_ctor_get(v_t_605_, 3);
v_isSharedCheck_639_ = !lean_is_exclusive(v_t_605_);
if (v_isSharedCheck_639_ == 0)
{
v___x_613_ = v_t_605_;
v_isShared_614_ = v_isSharedCheck_639_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_tailOff_611_);
lean_inc(v_size_609_);
lean_inc(v_tail_608_);
lean_inc(v_root_607_);
lean_dec(v_t_605_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_639_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
uint8_t v___x_615_; 
v___x_615_ = lean_nat_dec_le(v_tailOff_611_, v_i_606_);
if (v___x_615_ == 0)
{
size_t v___x_616_; lean_object* v___x_617_; lean_object* v___x_619_; 
v___x_616_ = lean_usize_of_nat(v_i_606_);
v___x_617_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4(v_c_604_, v_root_607_, v___x_616_, v_shift_610_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v___x_617_);
v___x_619_ = v___x_613_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v___x_617_);
lean_ctor_set(v_reuseFailAlloc_620_, 1, v_tail_608_);
lean_ctor_set(v_reuseFailAlloc_620_, 2, v_size_609_);
lean_ctor_set(v_reuseFailAlloc_620_, 3, v_tailOff_611_);
lean_ctor_set_usize(v_reuseFailAlloc_620_, 4, v_shift_610_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
else
{
lean_object* v___x_621_; lean_object* v___x_622_; uint8_t v___x_623_; 
v___x_621_ = lean_nat_sub(v_i_606_, v_tailOff_611_);
v___x_622_ = lean_array_get_size(v_tail_608_);
v___x_623_ = lean_nat_dec_lt(v___x_621_, v___x_622_);
if (v___x_623_ == 0)
{
lean_object* v___x_625_; 
lean_dec(v___x_621_);
if (v_isShared_614_ == 0)
{
v___x_625_ = v___x_613_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_626_; 
v_reuseFailAlloc_626_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_626_, 0, v_root_607_);
lean_ctor_set(v_reuseFailAlloc_626_, 1, v_tail_608_);
lean_ctor_set(v_reuseFailAlloc_626_, 2, v_size_609_);
lean_ctor_set(v_reuseFailAlloc_626_, 3, v_tailOff_611_);
lean_ctor_set_usize(v_reuseFailAlloc_626_, 4, v_shift_610_);
v___x_625_ = v_reuseFailAlloc_626_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
return v___x_625_;
}
}
else
{
lean_object* v_v_627_; lean_object* v___x_628_; lean_object* v_xs_x27_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_637_; 
v_v_627_ = lean_array_fget(v_tail_608_, v___x_621_);
v___x_628_ = lean_box(0);
v_xs_x27_629_ = lean_array_fset(v_tail_608_, v___x_621_, v___x_628_);
v___x_630_ = lean_unsigned_to_nat(32u);
v___x_631_ = lean_mk_empty_array_with_capacity(v___x_630_);
lean_dec_ref(v___x_631_);
v___x_632_ = lean_unsigned_to_nat(0u);
v___x_633_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1);
v___x_634_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(v_c_604_, v_v_627_, v___x_633_, v___x_632_);
lean_dec(v_v_627_);
v___x_635_ = lean_array_fset(v_xs_x27_629_, v___x_621_, v___x_634_);
lean_dec(v___x_621_);
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 1, v___x_635_);
v___x_637_ = v___x_613_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_root_607_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v___x_635_);
lean_ctor_set(v_reuseFailAlloc_638_, 2, v_size_609_);
lean_ctor_set(v_reuseFailAlloc_638_, 3, v_tailOff_611_);
lean_ctor_set_usize(v_reuseFailAlloc_638_, 4, v_shift_610_);
v___x_637_ = v_reuseFailAlloc_638_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
return v___x_637_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1___boxed(lean_object* v_c_640_, lean_object* v_t_641_, lean_object* v_i_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(v_c_640_, v_t_641_, v_i_642_);
lean_dec(v_i_642_);
lean_dec_ref(v_c_640_);
return v_res_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0(lean_object* v_c_644_, lean_object* v_v_645_, lean_object* v_s_646_){
_start:
{
lean_object* v_vars_647_; lean_object* v_varMap_648_; lean_object* v_varsHistory_649_; lean_object* v_natToIntMap_650_; lean_object* v_natDef_651_; lean_object* v_dvds_652_; lean_object* v_lowers_653_; lean_object* v_uppers_654_; lean_object* v_diseqs_655_; lean_object* v_elimEqs_656_; lean_object* v_elimStack_657_; lean_object* v_occurs_658_; lean_object* v_assignment_659_; lean_object* v_nextCnstrId_660_; uint8_t v_caseSplits_661_; lean_object* v_steps_662_; lean_object* v_conflict_x3f_663_; lean_object* v_diseqSplits_664_; lean_object* v_divMod_665_; uint8_t v_usedCommRing_666_; lean_object* v_nonlinearOccs_667_; lean_object* v___x_669_; uint8_t v_isShared_670_; uint8_t v_isSharedCheck_675_; 
v_vars_647_ = lean_ctor_get(v_s_646_, 0);
v_varMap_648_ = lean_ctor_get(v_s_646_, 1);
v_varsHistory_649_ = lean_ctor_get(v_s_646_, 2);
v_natToIntMap_650_ = lean_ctor_get(v_s_646_, 3);
v_natDef_651_ = lean_ctor_get(v_s_646_, 4);
v_dvds_652_ = lean_ctor_get(v_s_646_, 5);
v_lowers_653_ = lean_ctor_get(v_s_646_, 6);
v_uppers_654_ = lean_ctor_get(v_s_646_, 7);
v_diseqs_655_ = lean_ctor_get(v_s_646_, 8);
v_elimEqs_656_ = lean_ctor_get(v_s_646_, 9);
v_elimStack_657_ = lean_ctor_get(v_s_646_, 10);
v_occurs_658_ = lean_ctor_get(v_s_646_, 11);
v_assignment_659_ = lean_ctor_get(v_s_646_, 12);
v_nextCnstrId_660_ = lean_ctor_get(v_s_646_, 13);
v_caseSplits_661_ = lean_ctor_get_uint8(v_s_646_, sizeof(void*)*19);
v_steps_662_ = lean_ctor_get(v_s_646_, 14);
v_conflict_x3f_663_ = lean_ctor_get(v_s_646_, 15);
v_diseqSplits_664_ = lean_ctor_get(v_s_646_, 16);
v_divMod_665_ = lean_ctor_get(v_s_646_, 17);
v_usedCommRing_666_ = lean_ctor_get_uint8(v_s_646_, sizeof(void*)*19 + 1);
v_nonlinearOccs_667_ = lean_ctor_get(v_s_646_, 18);
v_isSharedCheck_675_ = !lean_is_exclusive(v_s_646_);
if (v_isSharedCheck_675_ == 0)
{
v___x_669_ = v_s_646_;
v_isShared_670_ = v_isSharedCheck_675_;
goto v_resetjp_668_;
}
else
{
lean_inc(v_nonlinearOccs_667_);
lean_inc(v_divMod_665_);
lean_inc(v_diseqSplits_664_);
lean_inc(v_conflict_x3f_663_);
lean_inc(v_steps_662_);
lean_inc(v_nextCnstrId_660_);
lean_inc(v_assignment_659_);
lean_inc(v_occurs_658_);
lean_inc(v_elimStack_657_);
lean_inc(v_elimEqs_656_);
lean_inc(v_diseqs_655_);
lean_inc(v_uppers_654_);
lean_inc(v_lowers_653_);
lean_inc(v_dvds_652_);
lean_inc(v_natDef_651_);
lean_inc(v_natToIntMap_650_);
lean_inc(v_varsHistory_649_);
lean_inc(v_varMap_648_);
lean_inc(v_vars_647_);
lean_dec(v_s_646_);
v___x_669_ = lean_box(0);
v_isShared_670_ = v_isSharedCheck_675_;
goto v_resetjp_668_;
}
v_resetjp_668_:
{
lean_object* v___x_671_; lean_object* v___x_673_; 
v___x_671_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(v_c_644_, v_uppers_654_, v_v_645_);
if (v_isShared_670_ == 0)
{
lean_ctor_set(v___x_669_, 7, v___x_671_);
v___x_673_ = v___x_669_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_674_; 
v_reuseFailAlloc_674_ = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(v_reuseFailAlloc_674_, 0, v_vars_647_);
lean_ctor_set(v_reuseFailAlloc_674_, 1, v_varMap_648_);
lean_ctor_set(v_reuseFailAlloc_674_, 2, v_varsHistory_649_);
lean_ctor_set(v_reuseFailAlloc_674_, 3, v_natToIntMap_650_);
lean_ctor_set(v_reuseFailAlloc_674_, 4, v_natDef_651_);
lean_ctor_set(v_reuseFailAlloc_674_, 5, v_dvds_652_);
lean_ctor_set(v_reuseFailAlloc_674_, 6, v_lowers_653_);
lean_ctor_set(v_reuseFailAlloc_674_, 7, v___x_671_);
lean_ctor_set(v_reuseFailAlloc_674_, 8, v_diseqs_655_);
lean_ctor_set(v_reuseFailAlloc_674_, 9, v_elimEqs_656_);
lean_ctor_set(v_reuseFailAlloc_674_, 10, v_elimStack_657_);
lean_ctor_set(v_reuseFailAlloc_674_, 11, v_occurs_658_);
lean_ctor_set(v_reuseFailAlloc_674_, 12, v_assignment_659_);
lean_ctor_set(v_reuseFailAlloc_674_, 13, v_nextCnstrId_660_);
lean_ctor_set(v_reuseFailAlloc_674_, 14, v_steps_662_);
lean_ctor_set(v_reuseFailAlloc_674_, 15, v_conflict_x3f_663_);
lean_ctor_set(v_reuseFailAlloc_674_, 16, v_diseqSplits_664_);
lean_ctor_set(v_reuseFailAlloc_674_, 17, v_divMod_665_);
lean_ctor_set(v_reuseFailAlloc_674_, 18, v_nonlinearOccs_667_);
lean_ctor_set_uint8(v_reuseFailAlloc_674_, sizeof(void*)*19, v_caseSplits_661_);
lean_ctor_set_uint8(v_reuseFailAlloc_674_, sizeof(void*)*19 + 1, v_usedCommRing_666_);
v___x_673_ = v_reuseFailAlloc_674_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
return v___x_673_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___boxed(lean_object* v_c_676_, lean_object* v_v_677_, lean_object* v_s_678_){
_start:
{
lean_object* v_res_679_; 
v_res_679_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0(v_c_676_, v_v_677_, v_s_678_);
lean_dec(v_v_677_);
lean_dec_ref(v_c_676_);
return v_res_679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1(lean_object* v_c_680_, lean_object* v_v_681_, lean_object* v_s_682_){
_start:
{
lean_object* v_vars_683_; lean_object* v_varMap_684_; lean_object* v_varsHistory_685_; lean_object* v_natToIntMap_686_; lean_object* v_natDef_687_; lean_object* v_dvds_688_; lean_object* v_lowers_689_; lean_object* v_uppers_690_; lean_object* v_diseqs_691_; lean_object* v_elimEqs_692_; lean_object* v_elimStack_693_; lean_object* v_occurs_694_; lean_object* v_assignment_695_; lean_object* v_nextCnstrId_696_; uint8_t v_caseSplits_697_; lean_object* v_steps_698_; lean_object* v_conflict_x3f_699_; lean_object* v_diseqSplits_700_; lean_object* v_divMod_701_; uint8_t v_usedCommRing_702_; lean_object* v_nonlinearOccs_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_711_; 
v_vars_683_ = lean_ctor_get(v_s_682_, 0);
v_varMap_684_ = lean_ctor_get(v_s_682_, 1);
v_varsHistory_685_ = lean_ctor_get(v_s_682_, 2);
v_natToIntMap_686_ = lean_ctor_get(v_s_682_, 3);
v_natDef_687_ = lean_ctor_get(v_s_682_, 4);
v_dvds_688_ = lean_ctor_get(v_s_682_, 5);
v_lowers_689_ = lean_ctor_get(v_s_682_, 6);
v_uppers_690_ = lean_ctor_get(v_s_682_, 7);
v_diseqs_691_ = lean_ctor_get(v_s_682_, 8);
v_elimEqs_692_ = lean_ctor_get(v_s_682_, 9);
v_elimStack_693_ = lean_ctor_get(v_s_682_, 10);
v_occurs_694_ = lean_ctor_get(v_s_682_, 11);
v_assignment_695_ = lean_ctor_get(v_s_682_, 12);
v_nextCnstrId_696_ = lean_ctor_get(v_s_682_, 13);
v_caseSplits_697_ = lean_ctor_get_uint8(v_s_682_, sizeof(void*)*19);
v_steps_698_ = lean_ctor_get(v_s_682_, 14);
v_conflict_x3f_699_ = lean_ctor_get(v_s_682_, 15);
v_diseqSplits_700_ = lean_ctor_get(v_s_682_, 16);
v_divMod_701_ = lean_ctor_get(v_s_682_, 17);
v_usedCommRing_702_ = lean_ctor_get_uint8(v_s_682_, sizeof(void*)*19 + 1);
v_nonlinearOccs_703_ = lean_ctor_get(v_s_682_, 18);
v_isSharedCheck_711_ = !lean_is_exclusive(v_s_682_);
if (v_isSharedCheck_711_ == 0)
{
v___x_705_ = v_s_682_;
v_isShared_706_ = v_isSharedCheck_711_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_nonlinearOccs_703_);
lean_inc(v_divMod_701_);
lean_inc(v_diseqSplits_700_);
lean_inc(v_conflict_x3f_699_);
lean_inc(v_steps_698_);
lean_inc(v_nextCnstrId_696_);
lean_inc(v_assignment_695_);
lean_inc(v_occurs_694_);
lean_inc(v_elimStack_693_);
lean_inc(v_elimEqs_692_);
lean_inc(v_diseqs_691_);
lean_inc(v_uppers_690_);
lean_inc(v_lowers_689_);
lean_inc(v_dvds_688_);
lean_inc(v_natDef_687_);
lean_inc(v_natToIntMap_686_);
lean_inc(v_varsHistory_685_);
lean_inc(v_varMap_684_);
lean_inc(v_vars_683_);
lean_dec(v_s_682_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_711_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_707_; lean_object* v___x_709_; 
v___x_707_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(v_c_680_, v_lowers_689_, v_v_681_);
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 6, v___x_707_);
v___x_709_ = v___x_705_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_vars_683_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v_varMap_684_);
lean_ctor_set(v_reuseFailAlloc_710_, 2, v_varsHistory_685_);
lean_ctor_set(v_reuseFailAlloc_710_, 3, v_natToIntMap_686_);
lean_ctor_set(v_reuseFailAlloc_710_, 4, v_natDef_687_);
lean_ctor_set(v_reuseFailAlloc_710_, 5, v_dvds_688_);
lean_ctor_set(v_reuseFailAlloc_710_, 6, v___x_707_);
lean_ctor_set(v_reuseFailAlloc_710_, 7, v_uppers_690_);
lean_ctor_set(v_reuseFailAlloc_710_, 8, v_diseqs_691_);
lean_ctor_set(v_reuseFailAlloc_710_, 9, v_elimEqs_692_);
lean_ctor_set(v_reuseFailAlloc_710_, 10, v_elimStack_693_);
lean_ctor_set(v_reuseFailAlloc_710_, 11, v_occurs_694_);
lean_ctor_set(v_reuseFailAlloc_710_, 12, v_assignment_695_);
lean_ctor_set(v_reuseFailAlloc_710_, 13, v_nextCnstrId_696_);
lean_ctor_set(v_reuseFailAlloc_710_, 14, v_steps_698_);
lean_ctor_set(v_reuseFailAlloc_710_, 15, v_conflict_x3f_699_);
lean_ctor_set(v_reuseFailAlloc_710_, 16, v_diseqSplits_700_);
lean_ctor_set(v_reuseFailAlloc_710_, 17, v_divMod_701_);
lean_ctor_set(v_reuseFailAlloc_710_, 18, v_nonlinearOccs_703_);
lean_ctor_set_uint8(v_reuseFailAlloc_710_, sizeof(void*)*19, v_caseSplits_697_);
lean_ctor_set_uint8(v_reuseFailAlloc_710_, sizeof(void*)*19 + 1, v_usedCommRing_702_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1___boxed(lean_object* v_c_712_, lean_object* v_v_713_, lean_object* v_s_714_){
_start:
{
lean_object* v_res_715_; 
v_res_715_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1(v_c_712_, v_v_713_, v_s_714_);
lean_dec(v_v_713_);
lean_dec_ref(v_c_712_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(lean_object* v_c_716_, lean_object* v_a_717_, lean_object* v_a_718_, lean_object* v_a_719_, lean_object* v_a_720_, lean_object* v_a_721_){
_start:
{
lean_object* v_p_723_; 
v_p_723_ = lean_ctor_get(v_c_716_, 0);
if (lean_obj_tag(v_p_723_) == 1)
{
lean_object* v_k_724_; lean_object* v_v_725_; lean_object* v___x_726_; uint8_t v___x_727_; 
v_k_724_ = lean_ctor_get(v_p_723_, 0);
v_v_725_ = lean_ctor_get(v_p_723_, 1);
lean_inc(v_v_725_);
v___x_726_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9);
v___x_727_ = lean_int_dec_lt(v_k_724_, v___x_726_);
if (v___x_727_ == 0)
{
lean_object* v___f_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___f_728_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_728_, 0, v_c_716_);
lean_closure_set(v___f_728_, 1, v_v_725_);
v___x_729_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_730_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_729_, v___f_728_, v_a_717_);
return v___x_730_;
}
else
{
lean_object* v___f_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v___f_731_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_731_, 0, v_c_716_);
lean_closure_set(v___f_731_, 1, v_v_725_);
v___x_732_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_733_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_732_, v___f_731_, v_a_717_);
return v___x_733_;
}
}
else
{
lean_object* v___x_734_; 
v___x_734_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_716_, v_a_717_, v_a_718_, v_a_719_, v_a_720_, v_a_721_);
return v___x_734_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___boxed(lean_object* v_c_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_, lean_object* v_a_740_, lean_object* v_a_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_c_735_, v_a_736_, v_a_737_, v_a_738_, v_a_739_, v_a_740_);
lean_dec(v_a_740_);
lean_dec_ref(v_a_739_);
lean_dec(v_a_738_);
lean_dec_ref(v_a_737_);
lean_dec(v_a_736_);
return v_res_742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase(lean_object* v_c_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_){
_start:
{
lean_object* v___x_755_; 
v___x_755_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_c_743_, v_a_744_, v_a_750_, v_a_751_, v_a_752_, v_a_753_);
return v___x_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___boxed(lean_object* v_c_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase(v_c_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_);
lean_dec(v_a_766_);
lean_dec_ref(v_a_765_);
lean_dec(v_a_764_);
lean_dec_ref(v_a_763_);
lean_dec(v_a_762_);
lean_dec_ref(v_a_761_);
lean_dec(v_a_760_);
lean_dec_ref(v_a_759_);
lean_dec(v_a_758_);
lean_dec(v_a_757_);
return v_res_768_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5(void){
_start:
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_782_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_783_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_784_ = l_Lean_Name_append(v___x_783_, v___x_782_);
return v___x_784_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7(void){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; 
v___x_786_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__6));
v___x_787_ = l_Lean_stringToMessageData(v___x_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3(lean_object* v_c_788_, lean_object* v_as_789_, size_t v_sz_790_, size_t v_i_791_, lean_object* v_b_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
uint8_t v___x_804_; 
v___x_804_ = lean_usize_dec_lt(v_i_791_, v_sz_790_);
if (v___x_804_ == 0)
{
lean_object* v___x_805_; 
lean_dec_ref(v_c_788_);
v___x_805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_805_, 0, v_b_792_);
return v___x_805_;
}
else
{
lean_object* v_snd_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_894_; 
v_snd_806_ = lean_ctor_get(v_b_792_, 1);
v_isSharedCheck_894_ = !lean_is_exclusive(v_b_792_);
if (v_isSharedCheck_894_ == 0)
{
lean_object* v_unused_895_; 
v_unused_895_ = lean_ctor_get(v_b_792_, 0);
lean_dec(v_unused_895_);
v___x_808_ = v_b_792_;
v_isShared_809_ = v_isSharedCheck_894_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_snd_806_);
lean_dec(v_b_792_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_894_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v_p_810_; lean_object* v_a_811_; lean_object* v_p_812_; lean_object* v___x_813_; uint8_t v___x_814_; 
v_p_810_ = lean_ctor_get(v_c_788_, 0);
v_a_811_ = lean_array_uget_borrowed(v_as_789_, v_i_791_);
v_p_812_ = lean_ctor_get(v_a_811_, 0);
v___x_813_ = lean_box(0);
v___x_814_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_810_, v_p_812_);
if (v___x_814_ == 0)
{
lean_object* v___x_815_; size_t v___x_816_; size_t v___x_817_; 
lean_del_object(v___x_808_);
lean_dec(v_snd_806_);
v___x_815_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__1));
v___x_816_ = ((size_t)1ULL);
v___x_817_ = lean_usize_add(v_i_791_, v___x_816_);
v_i_791_ = v___x_817_;
v_b_792_ = v___x_815_;
goto _start;
}
else
{
lean_object* v___x_819_; 
lean_inc_ref(v_p_810_);
lean_inc(v_a_811_);
v___x_819_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_811_, v___y_793_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
if (lean_obj_tag(v___x_819_) == 0)
{
lean_object* v_toCold_820_; lean_object* v_options_821_; lean_object* v_inheritedTraceOptions_822_; uint8_t v_hasTrace_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; 
lean_dec_ref_known(v___x_819_, 1);
v_toCold_820_ = lean_ctor_get(v___y_801_, 0);
v_options_821_ = lean_ctor_get(v_toCold_820_, 2);
v_inheritedTraceOptions_822_ = lean_ctor_get(v_toCold_820_, 11);
v_hasTrace_823_ = lean_ctor_get_uint8(v_options_821_, sizeof(void*)*1);
lean_inc(v_a_811_);
v___x_824_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_824_, 0, v_c_788_);
lean_ctor_set(v___x_824_, 1, v_a_811_);
v___x_825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_825_, 0, v_p_810_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
if (v_hasTrace_823_ == 0)
{
v___y_827_ = v___y_793_;
v___y_828_ = v___y_794_;
v___y_829_ = v___y_795_;
v___y_830_ = v___y_796_;
v___y_831_ = v___y_797_;
v___y_832_ = v___y_798_;
v___y_833_ = v___y_799_;
v___y_834_ = v___y_800_;
v___y_835_ = v___y_801_;
v___y_836_ = v___y_802_;
goto v___jp_826_;
}
else
{
lean_object* v___x_862_; lean_object* v___x_863_; uint8_t v___x_864_; 
v___x_862_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_863_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5);
v___x_864_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_822_, v_options_821_, v___x_863_);
if (v___x_864_ == 0)
{
v___y_827_ = v___y_793_;
v___y_828_ = v___y_794_;
v___y_829_ = v___y_795_;
v___y_830_ = v___y_796_;
v___y_831_ = v___y_797_;
v___y_832_ = v___y_798_;
v___y_833_ = v___y_799_;
v___y_834_ = v___y_800_;
v___y_835_ = v___y_801_;
v___y_836_ = v___y_802_;
goto v___jp_826_;
}
else
{
lean_object* v___x_865_; 
lean_inc_ref(v___x_825_);
v___x_865_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_825_, v___y_793_, v___y_801_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v_a_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; 
v_a_866_ = lean_ctor_get(v___x_865_, 0);
lean_inc(v_a_866_);
lean_dec_ref_known(v___x_865_, 1);
v___x_867_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7);
v___x_868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_868_, 0, v___x_867_);
lean_ctor_set(v___x_868_, 1, v_a_866_);
v___x_869_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_862_, v___x_868_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_dec_ref_known(v___x_869_, 1);
v___y_827_ = v___y_793_;
v___y_828_ = v___y_794_;
v___y_829_ = v___y_795_;
v___y_830_ = v___y_796_;
v___y_831_ = v___y_797_;
v___y_832_ = v___y_798_;
v___y_833_ = v___y_799_;
v___y_834_ = v___y_800_;
v___y_835_ = v___y_801_;
v___y_836_ = v___y_802_;
goto v___jp_826_;
}
else
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_877_; 
lean_dec_ref_known(v___x_825_, 2);
lean_del_object(v___x_808_);
lean_dec(v_snd_806_);
v_a_870_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_877_ == 0)
{
v___x_872_ = v___x_869_;
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_869_);
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
else
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_885_; 
lean_dec_ref_known(v___x_825_, 2);
lean_del_object(v___x_808_);
lean_dec(v_snd_806_);
v_a_878_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_885_ == 0)
{
v___x_880_ = v___x_865_;
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v___x_865_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_a_878_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
}
v___jp_826_:
{
lean_object* v___x_837_; 
lean_inc(v___y_836_);
lean_inc_ref(v___y_835_);
lean_inc(v___y_834_);
lean_inc_ref(v___y_833_);
lean_inc(v___y_832_);
lean_inc_ref(v___y_831_);
lean_inc(v___y_830_);
lean_inc_ref(v___y_829_);
lean_inc(v___y_828_);
lean_inc(v___y_827_);
v___x_837_ = lean_grind_cutsat_assert_eq(v___x_825_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_852_; 
v_isSharedCheck_852_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_852_ == 0)
{
lean_object* v_unused_853_; 
v_unused_853_ = lean_ctor_get(v___x_837_, 0);
lean_dec(v_unused_853_);
v___x_839_ = v___x_837_;
v_isShared_840_ = v_isSharedCheck_852_;
goto v_resetjp_838_;
}
else
{
lean_dec(v___x_837_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_852_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_844_; 
v___x_841_ = lean_box(v___x_814_);
v___x_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_842_, 0, v___x_841_);
if (v_isShared_809_ == 0)
{
lean_ctor_set(v___x_808_, 1, v___x_813_);
lean_ctor_set(v___x_808_, 0, v___x_842_);
v___x_844_ = v___x_808_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_842_);
lean_ctor_set(v_reuseFailAlloc_851_, 1, v___x_813_);
v___x_844_ = v_reuseFailAlloc_851_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_849_; 
v___x_845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
v___x_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
v___x_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
lean_ctor_set(v___x_847_, 1, v_snd_806_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 0, v___x_847_);
v___x_849_ = v___x_839_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_850_; 
v_reuseFailAlloc_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_850_, 0, v___x_847_);
v___x_849_ = v_reuseFailAlloc_850_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
return v___x_849_;
}
}
}
}
else
{
lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_861_; 
lean_del_object(v___x_808_);
lean_dec(v_snd_806_);
v_a_854_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_861_ == 0)
{
v___x_856_ = v___x_837_;
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_837_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_859_; 
if (v_isShared_857_ == 0)
{
v___x_859_ = v___x_856_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_a_854_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
}
else
{
lean_object* v_a_886_; lean_object* v___x_888_; uint8_t v_isShared_889_; uint8_t v_isSharedCheck_893_; 
lean_dec_ref(v_p_810_);
lean_del_object(v___x_808_);
lean_dec(v_snd_806_);
lean_dec_ref(v_c_788_);
v_a_886_ = lean_ctor_get(v___x_819_, 0);
v_isSharedCheck_893_ = !lean_is_exclusive(v___x_819_);
if (v_isSharedCheck_893_ == 0)
{
v___x_888_ = v___x_819_;
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
else
{
lean_inc(v_a_886_);
lean_dec(v___x_819_);
v___x_888_ = lean_box(0);
v_isShared_889_ = v_isSharedCheck_893_;
goto v_resetjp_887_;
}
v_resetjp_887_:
{
lean_object* v___x_891_; 
if (v_isShared_889_ == 0)
{
v___x_891_ = v___x_888_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_886_);
v___x_891_ = v_reuseFailAlloc_892_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
return v___x_891_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_c_896_, lean_object* v_as_897_, lean_object* v_sz_898_, lean_object* v_i_899_, lean_object* v_b_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
size_t v_sz_boxed_912_; size_t v_i_boxed_913_; lean_object* v_res_914_; 
v_sz_boxed_912_ = lean_unbox_usize(v_sz_898_);
lean_dec(v_sz_898_);
v_i_boxed_913_ = lean_unbox_usize(v_i_899_);
lean_dec(v_i_899_);
v_res_914_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3(v_c_896_, v_as_897_, v_sz_boxed_912_, v_i_boxed_913_, v_b_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec(v___y_906_);
lean_dec_ref(v___y_905_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_902_);
lean_dec(v___y_901_);
lean_dec_ref(v_as_897_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2(lean_object* v_c_921_, lean_object* v_as_922_, size_t v_sz_923_, size_t v_i_924_, lean_object* v_b_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
uint8_t v___x_937_; 
v___x_937_ = lean_usize_dec_lt(v_i_924_, v_sz_923_);
if (v___x_937_ == 0)
{
lean_object* v___x_938_; 
lean_dec_ref(v_c_921_);
v___x_938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_938_, 0, v_b_925_);
return v___x_938_;
}
else
{
lean_object* v_snd_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_1027_; 
v_snd_939_ = lean_ctor_get(v_b_925_, 1);
v_isSharedCheck_1027_ = !lean_is_exclusive(v_b_925_);
if (v_isSharedCheck_1027_ == 0)
{
lean_object* v_unused_1028_; 
v_unused_1028_ = lean_ctor_get(v_b_925_, 0);
lean_dec(v_unused_1028_);
v___x_941_ = v_b_925_;
v_isShared_942_ = v_isSharedCheck_1027_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_snd_939_);
lean_dec(v_b_925_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_1027_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v_p_943_; lean_object* v_a_944_; lean_object* v_p_945_; lean_object* v___x_946_; uint8_t v___x_947_; 
v_p_943_ = lean_ctor_get(v_c_921_, 0);
v_a_944_ = lean_array_uget_borrowed(v_as_922_, v_i_924_);
v_p_945_ = lean_ctor_get(v_a_944_, 0);
v___x_946_ = lean_box(0);
v___x_947_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_943_, v_p_945_);
if (v___x_947_ == 0)
{
lean_object* v___x_948_; size_t v___x_949_; size_t v___x_950_; lean_object* v___x_951_; 
lean_del_object(v___x_941_);
lean_dec(v_snd_939_);
v___x_948_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__1));
v___x_949_ = ((size_t)1ULL);
v___x_950_ = lean_usize_add(v_i_924_, v___x_949_);
v___x_951_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3(v_c_921_, v_as_922_, v_sz_923_, v___x_950_, v___x_948_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
return v___x_951_;
}
else
{
lean_object* v___x_952_; 
lean_inc_ref(v_p_943_);
lean_inc(v_a_944_);
v___x_952_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_944_, v___y_926_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v_toCold_953_; lean_object* v_options_954_; lean_object* v_inheritedTraceOptions_955_; uint8_t v_hasTrace_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___y_960_; lean_object* v___y_961_; lean_object* v___y_962_; lean_object* v___y_963_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v___y_967_; lean_object* v___y_968_; lean_object* v___y_969_; 
lean_dec_ref_known(v___x_952_, 1);
v_toCold_953_ = lean_ctor_get(v___y_934_, 0);
v_options_954_ = lean_ctor_get(v_toCold_953_, 2);
v_inheritedTraceOptions_955_ = lean_ctor_get(v_toCold_953_, 11);
v_hasTrace_956_ = lean_ctor_get_uint8(v_options_954_, sizeof(void*)*1);
lean_inc(v_a_944_);
v___x_957_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_957_, 0, v_c_921_);
lean_ctor_set(v___x_957_, 1, v_a_944_);
v___x_958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_958_, 0, v_p_943_);
lean_ctor_set(v___x_958_, 1, v___x_957_);
if (v_hasTrace_956_ == 0)
{
v___y_960_ = v___y_926_;
v___y_961_ = v___y_927_;
v___y_962_ = v___y_928_;
v___y_963_ = v___y_929_;
v___y_964_ = v___y_930_;
v___y_965_ = v___y_931_;
v___y_966_ = v___y_932_;
v___y_967_ = v___y_933_;
v___y_968_ = v___y_934_;
v___y_969_ = v___y_935_;
goto v___jp_959_;
}
else
{
lean_object* v___x_995_; lean_object* v___x_996_; uint8_t v___x_997_; 
v___x_995_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_996_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5);
v___x_997_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_955_, v_options_954_, v___x_996_);
if (v___x_997_ == 0)
{
v___y_960_ = v___y_926_;
v___y_961_ = v___y_927_;
v___y_962_ = v___y_928_;
v___y_963_ = v___y_929_;
v___y_964_ = v___y_930_;
v___y_965_ = v___y_931_;
v___y_966_ = v___y_932_;
v___y_967_ = v___y_933_;
v___y_968_ = v___y_934_;
v___y_969_ = v___y_935_;
goto v___jp_959_;
}
else
{
lean_object* v___x_998_; 
lean_inc_ref(v___x_958_);
v___x_998_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_958_, v___y_926_, v___y_934_);
if (lean_obj_tag(v___x_998_) == 0)
{
lean_object* v_a_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v_a_999_ = lean_ctor_get(v___x_998_, 0);
lean_inc(v_a_999_);
lean_dec_ref_known(v___x_998_, 1);
v___x_1000_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7);
v___x_1001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_1000_);
lean_ctor_set(v___x_1001_, 1, v_a_999_);
v___x_1002_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_995_, v___x_1001_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_dec_ref_known(v___x_1002_, 1);
v___y_960_ = v___y_926_;
v___y_961_ = v___y_927_;
v___y_962_ = v___y_928_;
v___y_963_ = v___y_929_;
v___y_964_ = v___y_930_;
v___y_965_ = v___y_931_;
v___y_966_ = v___y_932_;
v___y_967_ = v___y_933_;
v___y_968_ = v___y_934_;
v___y_969_ = v___y_935_;
goto v___jp_959_;
}
else
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
lean_dec_ref_known(v___x_958_, 2);
lean_del_object(v___x_941_);
lean_dec(v_snd_939_);
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_1002_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_1002_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1003_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
lean_dec_ref_known(v___x_958_, 2);
lean_del_object(v___x_941_);
lean_dec(v_snd_939_);
v_a_1011_ = lean_ctor_get(v___x_998_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_998_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_998_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_998_);
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
v___jp_959_:
{
lean_object* v___x_970_; 
lean_inc(v___y_969_);
lean_inc_ref(v___y_968_);
lean_inc(v___y_967_);
lean_inc_ref(v___y_966_);
lean_inc(v___y_965_);
lean_inc_ref(v___y_964_);
lean_inc(v___y_963_);
lean_inc_ref(v___y_962_);
lean_inc(v___y_961_);
lean_inc(v___y_960_);
v___x_970_ = lean_grind_cutsat_assert_eq(v___x_958_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
if (lean_obj_tag(v___x_970_) == 0)
{
lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_985_; 
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_985_ == 0)
{
lean_object* v_unused_986_; 
v_unused_986_ = lean_ctor_get(v___x_970_, 0);
lean_dec(v_unused_986_);
v___x_972_ = v___x_970_;
v_isShared_973_ = v_isSharedCheck_985_;
goto v_resetjp_971_;
}
else
{
lean_dec(v___x_970_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_985_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_977_; 
v___x_974_ = lean_box(v___x_947_);
v___x_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 1, v___x_946_);
lean_ctor_set(v___x_941_, 0, v___x_975_);
v___x_977_ = v___x_941_;
goto v_reusejp_976_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v___x_975_);
lean_ctor_set(v_reuseFailAlloc_984_, 1, v___x_946_);
v___x_977_ = v_reuseFailAlloc_984_;
goto v_reusejp_976_;
}
v_reusejp_976_:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_982_; 
v___x_978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_978_, 0, v___x_977_);
v___x_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_979_, 0, v___x_978_);
v___x_980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_980_, 0, v___x_979_);
lean_ctor_set(v___x_980_, 1, v_snd_939_);
if (v_isShared_973_ == 0)
{
lean_ctor_set(v___x_972_, 0, v___x_980_);
v___x_982_ = v___x_972_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v___x_980_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
}
else
{
lean_object* v_a_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_994_; 
lean_del_object(v___x_941_);
lean_dec(v_snd_939_);
v_a_987_ = lean_ctor_get(v___x_970_, 0);
v_isSharedCheck_994_ = !lean_is_exclusive(v___x_970_);
if (v_isSharedCheck_994_ == 0)
{
v___x_989_ = v___x_970_;
v_isShared_990_ = v_isSharedCheck_994_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_a_987_);
lean_dec(v___x_970_);
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
else
{
lean_object* v_a_1019_; lean_object* v___x_1021_; uint8_t v_isShared_1022_; uint8_t v_isSharedCheck_1026_; 
lean_dec_ref(v_p_943_);
lean_del_object(v___x_941_);
lean_dec(v_snd_939_);
lean_dec_ref(v_c_921_);
v_a_1019_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1021_ = v___x_952_;
v_isShared_1022_ = v_isSharedCheck_1026_;
goto v_resetjp_1020_;
}
else
{
lean_inc(v_a_1019_);
lean_dec(v___x_952_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___boxed(lean_object* v_c_1029_, lean_object* v_as_1030_, lean_object* v_sz_1031_, lean_object* v_i_1032_, lean_object* v_b_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
size_t v_sz_boxed_1045_; size_t v_i_boxed_1046_; lean_object* v_res_1047_; 
v_sz_boxed_1045_ = lean_unbox_usize(v_sz_1031_);
lean_dec(v_sz_1031_);
v_i_boxed_1046_ = lean_unbox_usize(v_i_1032_);
lean_dec(v_i_1032_);
v_res_1047_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2(v_c_1029_, v_as_1030_, v_sz_boxed_1045_, v_i_boxed_1046_, v_b_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
lean_dec(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec_ref(v_as_1030_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(lean_object* v_init_1048_, lean_object* v_c_1049_, lean_object* v_n_1050_, lean_object* v_b_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
if (lean_obj_tag(v_n_1050_) == 0)
{
lean_object* v_cs_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; size_t v_sz_1066_; size_t v___x_1067_; lean_object* v___x_1068_; 
v_cs_1063_ = lean_ctor_get(v_n_1050_, 0);
v___x_1064_ = lean_box(0);
v___x_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
lean_ctor_set(v___x_1065_, 1, v_b_1051_);
v_sz_1066_ = lean_array_size(v_cs_1063_);
v___x_1067_ = ((size_t)0ULL);
v___x_1068_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(v_init_1048_, v_c_1049_, v_cs_1063_, v_sz_1066_, v___x_1067_, v___x_1065_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
if (lean_obj_tag(v___x_1068_) == 0)
{
lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1083_; 
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1083_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1083_ == 0)
{
v___x_1071_ = v___x_1068_;
v_isShared_1072_ = v_isSharedCheck_1083_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v___x_1068_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1083_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v_fst_1073_; 
v_fst_1073_ = lean_ctor_get(v_a_1069_, 0);
if (lean_obj_tag(v_fst_1073_) == 0)
{
lean_object* v_snd_1074_; lean_object* v___x_1075_; lean_object* v___x_1077_; 
v_snd_1074_ = lean_ctor_get(v_a_1069_, 1);
lean_inc(v_snd_1074_);
lean_dec(v_a_1069_);
v___x_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1075_, 0, v_snd_1074_);
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 0, v___x_1075_);
v___x_1077_ = v___x_1071_;
goto v_reusejp_1076_;
}
else
{
lean_object* v_reuseFailAlloc_1078_; 
v_reuseFailAlloc_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1078_, 0, v___x_1075_);
v___x_1077_ = v_reuseFailAlloc_1078_;
goto v_reusejp_1076_;
}
v_reusejp_1076_:
{
return v___x_1077_;
}
}
else
{
lean_object* v_val_1079_; lean_object* v___x_1081_; 
lean_inc_ref(v_fst_1073_);
lean_dec(v_a_1069_);
v_val_1079_ = lean_ctor_get(v_fst_1073_, 0);
lean_inc(v_val_1079_);
lean_dec_ref_known(v_fst_1073_, 1);
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 0, v_val_1079_);
v___x_1081_ = v___x_1071_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_val_1079_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
}
}
else
{
lean_object* v_a_1084_; lean_object* v___x_1086_; uint8_t v_isShared_1087_; uint8_t v_isSharedCheck_1091_; 
v_a_1084_ = lean_ctor_get(v___x_1068_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1068_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1086_ = v___x_1068_;
v_isShared_1087_ = v_isSharedCheck_1091_;
goto v_resetjp_1085_;
}
else
{
lean_inc(v_a_1084_);
lean_dec(v___x_1068_);
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
else
{
lean_object* v_vs_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; size_t v_sz_1095_; size_t v___x_1096_; lean_object* v___x_1097_; 
v_vs_1092_ = lean_ctor_get(v_n_1050_, 0);
v___x_1093_ = lean_box(0);
v___x_1094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1094_, 0, v___x_1093_);
lean_ctor_set(v___x_1094_, 1, v_b_1051_);
v_sz_1095_ = lean_array_size(v_vs_1092_);
v___x_1096_ = ((size_t)0ULL);
v___x_1097_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2(v_c_1049_, v_vs_1092_, v_sz_1095_, v___x_1096_, v___x_1094_, v___y_1052_, v___y_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1112_; 
v_a_1098_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1100_ = v___x_1097_;
v_isShared_1101_ = v_isSharedCheck_1112_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1097_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1112_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v_fst_1102_; 
v_fst_1102_ = lean_ctor_get(v_a_1098_, 0);
if (lean_obj_tag(v_fst_1102_) == 0)
{
lean_object* v_snd_1103_; lean_object* v___x_1104_; lean_object* v___x_1106_; 
v_snd_1103_ = lean_ctor_get(v_a_1098_, 1);
lean_inc(v_snd_1103_);
lean_dec(v_a_1098_);
v___x_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1104_, 0, v_snd_1103_);
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 0, v___x_1104_);
v___x_1106_ = v___x_1100_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1104_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
else
{
lean_object* v_val_1108_; lean_object* v___x_1110_; 
lean_inc_ref(v_fst_1102_);
lean_dec(v_a_1098_);
v_val_1108_ = lean_ctor_get(v_fst_1102_, 0);
lean_inc(v_val_1108_);
lean_dec_ref_known(v_fst_1102_, 1);
if (v_isShared_1101_ == 0)
{
lean_ctor_set(v___x_1100_, 0, v_val_1108_);
v___x_1110_ = v___x_1100_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_val_1108_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
else
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1120_; 
v_a_1113_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1115_ = v___x_1097_;
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1097_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1113_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(lean_object* v_init_1121_, lean_object* v_c_1122_, lean_object* v_as_1123_, size_t v_sz_1124_, size_t v_i_1125_, lean_object* v_b_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_, lean_object* v___y_1129_, lean_object* v___y_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_){
_start:
{
uint8_t v___x_1138_; 
v___x_1138_ = lean_usize_dec_lt(v_i_1125_, v_sz_1124_);
if (v___x_1138_ == 0)
{
lean_object* v___x_1139_; 
lean_dec_ref(v_c_1122_);
v___x_1139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1139_, 0, v_b_1126_);
return v___x_1139_;
}
else
{
lean_object* v_snd_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1174_; 
v_snd_1140_ = lean_ctor_get(v_b_1126_, 1);
v_isSharedCheck_1174_ = !lean_is_exclusive(v_b_1126_);
if (v_isSharedCheck_1174_ == 0)
{
lean_object* v_unused_1175_; 
v_unused_1175_ = lean_ctor_get(v_b_1126_, 0);
lean_dec(v_unused_1175_);
v___x_1142_ = v_b_1126_;
v_isShared_1143_ = v_isSharedCheck_1174_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_snd_1140_);
lean_dec(v_b_1126_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1174_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v___x_1144_; lean_object* v_a_1145_; lean_object* v___x_1146_; 
v___x_1144_ = lean_box(0);
v_a_1145_ = lean_array_uget_borrowed(v_as_1123_, v_i_1125_);
lean_inc(v_snd_1140_);
lean_inc_ref(v_c_1122_);
v___x_1146_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(v_init_1121_, v_c_1122_, v_a_1145_, v_snd_1140_, v___y_1127_, v___y_1128_, v___y_1129_, v___y_1130_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1165_; 
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1149_ = v___x_1146_;
v_isShared_1150_ = v_isSharedCheck_1165_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1146_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1165_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
if (lean_obj_tag(v_a_1147_) == 0)
{
lean_object* v___x_1151_; lean_object* v___x_1153_; 
lean_dec_ref(v_c_1122_);
v___x_1151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1151_, 0, v_a_1147_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 0, v___x_1151_);
v___x_1153_ = v___x_1142_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v___x_1151_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v_snd_1140_);
v___x_1153_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
lean_object* v___x_1155_; 
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 0, v___x_1153_);
v___x_1155_ = v___x_1149_;
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
lean_object* v_a_1158_; lean_object* v___x_1160_; 
lean_del_object(v___x_1149_);
lean_dec(v_snd_1140_);
v_a_1158_ = lean_ctor_get(v_a_1147_, 0);
lean_inc(v_a_1158_);
lean_dec_ref_known(v_a_1147_, 1);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 1, v_a_1158_);
lean_ctor_set(v___x_1142_, 0, v___x_1144_);
v___x_1160_ = v___x_1142_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v___x_1144_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v_a_1158_);
v___x_1160_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
size_t v___x_1161_; size_t v___x_1162_; 
v___x_1161_ = ((size_t)1ULL);
v___x_1162_ = lean_usize_add(v_i_1125_, v___x_1161_);
v_i_1125_ = v___x_1162_;
v_b_1126_ = v___x_1160_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1173_; 
lean_del_object(v___x_1142_);
lean_dec(v_snd_1140_);
lean_dec_ref(v_c_1122_);
v_a_1166_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1173_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1173_ == 0)
{
v___x_1168_ = v___x_1146_;
v_isShared_1169_ = v_isSharedCheck_1173_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_a_1166_);
lean_dec(v___x_1146_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_init_1176_ = _args[0];
lean_object* v_c_1177_ = _args[1];
lean_object* v_as_1178_ = _args[2];
lean_object* v_sz_1179_ = _args[3];
lean_object* v_i_1180_ = _args[4];
lean_object* v_b_1181_ = _args[5];
lean_object* v___y_1182_ = _args[6];
lean_object* v___y_1183_ = _args[7];
lean_object* v___y_1184_ = _args[8];
lean_object* v___y_1185_ = _args[9];
lean_object* v___y_1186_ = _args[10];
lean_object* v___y_1187_ = _args[11];
lean_object* v___y_1188_ = _args[12];
lean_object* v___y_1189_ = _args[13];
lean_object* v___y_1190_ = _args[14];
lean_object* v___y_1191_ = _args[15];
lean_object* v___y_1192_ = _args[16];
_start:
{
size_t v_sz_boxed_1193_; size_t v_i_boxed_1194_; lean_object* v_res_1195_; 
v_sz_boxed_1193_ = lean_unbox_usize(v_sz_1179_);
lean_dec(v_sz_1179_);
v_i_boxed_1194_ = lean_unbox_usize(v_i_1180_);
lean_dec(v_i_1180_);
v_res_1195_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(v_init_1176_, v_c_1177_, v_as_1178_, v_sz_boxed_1193_, v_i_boxed_1194_, v_b_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
lean_dec(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec_ref(v_as_1178_);
lean_dec_ref(v_init_1176_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___boxed(lean_object* v_init_1196_, lean_object* v_c_1197_, lean_object* v_n_1198_, lean_object* v_b_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_){
_start:
{
lean_object* v_res_1211_; 
v_res_1211_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(v_init_1196_, v_c_1197_, v_n_1198_, v_b_1199_, v___y_1200_, v___y_1201_, v___y_1202_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_);
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
lean_dec_ref(v_n_1198_);
lean_dec_ref(v_init_1196_);
return v_res_1211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4(lean_object* v_c_1218_, lean_object* v_as_1219_, size_t v_sz_1220_, size_t v_i_1221_, lean_object* v_b_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
uint8_t v___x_1234_; 
v___x_1234_ = lean_usize_dec_lt(v_i_1221_, v_sz_1220_);
if (v___x_1234_ == 0)
{
lean_object* v___x_1235_; 
lean_dec_ref(v_c_1218_);
v___x_1235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1235_, 0, v_b_1222_);
return v___x_1235_;
}
else
{
lean_object* v_snd_1236_; lean_object* v___x_1238_; uint8_t v_isShared_1239_; uint8_t v_isSharedCheck_1323_; 
v_snd_1236_ = lean_ctor_get(v_b_1222_, 1);
v_isSharedCheck_1323_ = !lean_is_exclusive(v_b_1222_);
if (v_isSharedCheck_1323_ == 0)
{
lean_object* v_unused_1324_; 
v_unused_1324_ = lean_ctor_get(v_b_1222_, 0);
lean_dec(v_unused_1324_);
v___x_1238_ = v_b_1222_;
v_isShared_1239_ = v_isSharedCheck_1323_;
goto v_resetjp_1237_;
}
else
{
lean_inc(v_snd_1236_);
lean_dec(v_b_1222_);
v___x_1238_ = lean_box(0);
v_isShared_1239_ = v_isSharedCheck_1323_;
goto v_resetjp_1237_;
}
v_resetjp_1237_:
{
lean_object* v_p_1240_; lean_object* v_a_1241_; lean_object* v_p_1242_; lean_object* v___x_1243_; uint8_t v___x_1244_; 
v_p_1240_ = lean_ctor_get(v_c_1218_, 0);
v_a_1241_ = lean_array_uget_borrowed(v_as_1219_, v_i_1221_);
v_p_1242_ = lean_ctor_get(v_a_1241_, 0);
v___x_1243_ = lean_box(0);
v___x_1244_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_1240_, v_p_1242_);
if (v___x_1244_ == 0)
{
lean_object* v___x_1245_; size_t v___x_1246_; size_t v___x_1247_; 
lean_del_object(v___x_1238_);
lean_dec(v_snd_1236_);
v___x_1245_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___closed__1));
v___x_1246_ = ((size_t)1ULL);
v___x_1247_ = lean_usize_add(v_i_1221_, v___x_1246_);
v_i_1221_ = v___x_1247_;
v_b_1222_ = v___x_1245_;
goto _start;
}
else
{
lean_object* v___x_1249_; 
lean_inc_ref(v_p_1240_);
lean_inc(v_a_1241_);
v___x_1249_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_1241_, v___y_1223_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v_toCold_1250_; lean_object* v_options_1251_; lean_object* v_inheritedTraceOptions_1252_; uint8_t v_hasTrace_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1260_; lean_object* v___y_1261_; lean_object* v___y_1262_; lean_object* v___y_1263_; lean_object* v___y_1264_; lean_object* v___y_1265_; lean_object* v___y_1266_; 
lean_dec_ref_known(v___x_1249_, 1);
v_toCold_1250_ = lean_ctor_get(v___y_1231_, 0);
v_options_1251_ = lean_ctor_get(v_toCold_1250_, 2);
v_inheritedTraceOptions_1252_ = lean_ctor_get(v_toCold_1250_, 11);
v_hasTrace_1253_ = lean_ctor_get_uint8(v_options_1251_, sizeof(void*)*1);
lean_inc(v_a_1241_);
v___x_1254_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1254_, 0, v_c_1218_);
lean_ctor_set(v___x_1254_, 1, v_a_1241_);
v___x_1255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1255_, 0, v_p_1240_);
lean_ctor_set(v___x_1255_, 1, v___x_1254_);
if (v_hasTrace_1253_ == 0)
{
v___y_1257_ = v___y_1223_;
v___y_1258_ = v___y_1224_;
v___y_1259_ = v___y_1225_;
v___y_1260_ = v___y_1226_;
v___y_1261_ = v___y_1227_;
v___y_1262_ = v___y_1228_;
v___y_1263_ = v___y_1229_;
v___y_1264_ = v___y_1230_;
v___y_1265_ = v___y_1231_;
v___y_1266_ = v___y_1232_;
goto v___jp_1256_;
}
else
{
lean_object* v___x_1291_; lean_object* v___x_1292_; uint8_t v___x_1293_; 
v___x_1291_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_1292_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5);
v___x_1293_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1252_, v_options_1251_, v___x_1292_);
if (v___x_1293_ == 0)
{
v___y_1257_ = v___y_1223_;
v___y_1258_ = v___y_1224_;
v___y_1259_ = v___y_1225_;
v___y_1260_ = v___y_1226_;
v___y_1261_ = v___y_1227_;
v___y_1262_ = v___y_1228_;
v___y_1263_ = v___y_1229_;
v___y_1264_ = v___y_1230_;
v___y_1265_ = v___y_1231_;
v___y_1266_ = v___y_1232_;
goto v___jp_1256_;
}
else
{
lean_object* v___x_1294_; 
lean_inc_ref(v___x_1255_);
v___x_1294_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_1255_, v___y_1223_, v___y_1231_);
if (lean_obj_tag(v___x_1294_) == 0)
{
lean_object* v_a_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v_a_1295_ = lean_ctor_get(v___x_1294_, 0);
lean_inc(v_a_1295_);
lean_dec_ref_known(v___x_1294_, 1);
v___x_1296_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7);
v___x_1297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1297_, 0, v___x_1296_);
lean_ctor_set(v___x_1297_, 1, v_a_1295_);
v___x_1298_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_1291_, v___x_1297_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_dec_ref_known(v___x_1298_, 1);
v___y_1257_ = v___y_1223_;
v___y_1258_ = v___y_1224_;
v___y_1259_ = v___y_1225_;
v___y_1260_ = v___y_1226_;
v___y_1261_ = v___y_1227_;
v___y_1262_ = v___y_1228_;
v___y_1263_ = v___y_1229_;
v___y_1264_ = v___y_1230_;
v___y_1265_ = v___y_1231_;
v___y_1266_ = v___y_1232_;
goto v___jp_1256_;
}
else
{
lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1306_; 
lean_dec_ref_known(v___x_1255_, 2);
lean_del_object(v___x_1238_);
lean_dec(v_snd_1236_);
v_a_1299_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1301_ = v___x_1298_;
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v___x_1298_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1306_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1304_; 
if (v_isShared_1302_ == 0)
{
v___x_1304_ = v___x_1301_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_a_1299_);
v___x_1304_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
return v___x_1304_;
}
}
}
}
else
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1314_; 
lean_dec_ref_known(v___x_1255_, 2);
lean_del_object(v___x_1238_);
lean_dec(v_snd_1236_);
v_a_1307_ = lean_ctor_get(v___x_1294_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1309_ = v___x_1294_;
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1294_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1312_; 
if (v_isShared_1310_ == 0)
{
v___x_1312_ = v___x_1309_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_a_1307_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
}
}
v___jp_1256_:
{
lean_object* v___x_1267_; 
lean_inc(v___y_1266_);
lean_inc_ref(v___y_1265_);
lean_inc(v___y_1264_);
lean_inc_ref(v___y_1263_);
lean_inc(v___y_1262_);
lean_inc_ref(v___y_1261_);
lean_inc(v___y_1260_);
lean_inc_ref(v___y_1259_);
lean_inc(v___y_1258_);
lean_inc(v___y_1257_);
v___x_1267_ = lean_grind_cutsat_assert_eq(v___x_1255_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_);
if (lean_obj_tag(v___x_1267_) == 0)
{
lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1281_; 
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1281_ == 0)
{
lean_object* v_unused_1282_; 
v_unused_1282_ = lean_ctor_get(v___x_1267_, 0);
lean_dec(v_unused_1282_);
v___x_1269_ = v___x_1267_;
v_isShared_1270_ = v_isSharedCheck_1281_;
goto v_resetjp_1268_;
}
else
{
lean_dec(v___x_1267_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1281_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1274_; 
v___x_1271_ = lean_box(v___x_1244_);
v___x_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1271_);
if (v_isShared_1239_ == 0)
{
lean_ctor_set(v___x_1238_, 1, v___x_1243_);
lean_ctor_set(v___x_1238_, 0, v___x_1272_);
v___x_1274_ = v___x_1238_;
goto v_reusejp_1273_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v___x_1272_);
lean_ctor_set(v_reuseFailAlloc_1280_, 1, v___x_1243_);
v___x_1274_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1273_;
}
v_reusejp_1273_:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1278_; 
v___x_1275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1274_);
v___x_1276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1275_);
lean_ctor_set(v___x_1276_, 1, v_snd_1236_);
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 0, v___x_1276_);
v___x_1278_ = v___x_1269_;
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
}
else
{
lean_object* v_a_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1290_; 
lean_del_object(v___x_1238_);
lean_dec(v_snd_1236_);
v_a_1283_ = lean_ctor_get(v___x_1267_, 0);
v_isSharedCheck_1290_ = !lean_is_exclusive(v___x_1267_);
if (v_isSharedCheck_1290_ == 0)
{
v___x_1285_ = v___x_1267_;
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_a_1283_);
lean_dec(v___x_1267_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1290_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v___x_1288_; 
if (v_isShared_1286_ == 0)
{
v___x_1288_ = v___x_1285_;
goto v_reusejp_1287_;
}
else
{
lean_object* v_reuseFailAlloc_1289_; 
v_reuseFailAlloc_1289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1289_, 0, v_a_1283_);
v___x_1288_ = v_reuseFailAlloc_1289_;
goto v_reusejp_1287_;
}
v_reusejp_1287_:
{
return v___x_1288_;
}
}
}
}
}
else
{
lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1322_; 
lean_dec_ref(v_p_1240_);
lean_del_object(v___x_1238_);
lean_dec(v_snd_1236_);
lean_dec_ref(v_c_1218_);
v_a_1315_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1317_ = v___x_1249_;
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_dec(v___x_1249_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1320_; 
if (v_isShared_1318_ == 0)
{
v___x_1320_ = v___x_1317_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_a_1315_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___boxed(lean_object* v_c_1325_, lean_object* v_as_1326_, lean_object* v_sz_1327_, lean_object* v_i_1328_, lean_object* v_b_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
size_t v_sz_boxed_1341_; size_t v_i_boxed_1342_; lean_object* v_res_1343_; 
v_sz_boxed_1341_ = lean_unbox_usize(v_sz_1327_);
lean_dec(v_sz_1327_);
v_i_boxed_1342_ = lean_unbox_usize(v_i_1328_);
lean_dec(v_i_1328_);
v_res_1343_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4(v_c_1325_, v_as_1326_, v_sz_boxed_1341_, v_i_boxed_1342_, v_b_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
lean_dec(v___y_1330_);
lean_dec_ref(v_as_1326_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1(lean_object* v_c_1347_, lean_object* v_as_1348_, size_t v_sz_1349_, size_t v_i_1350_, lean_object* v_b_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_){
_start:
{
uint8_t v___x_1363_; 
v___x_1363_ = lean_usize_dec_lt(v_i_1350_, v_sz_1349_);
if (v___x_1363_ == 0)
{
lean_object* v___x_1364_; 
lean_dec_ref(v_c_1347_);
v___x_1364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1364_, 0, v_b_1351_);
return v___x_1364_;
}
else
{
lean_object* v_snd_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1452_; 
v_snd_1365_ = lean_ctor_get(v_b_1351_, 1);
v_isSharedCheck_1452_ = !lean_is_exclusive(v_b_1351_);
if (v_isSharedCheck_1452_ == 0)
{
lean_object* v_unused_1453_; 
v_unused_1453_ = lean_ctor_get(v_b_1351_, 0);
lean_dec(v_unused_1453_);
v___x_1367_ = v_b_1351_;
v_isShared_1368_ = v_isSharedCheck_1452_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_snd_1365_);
lean_dec(v_b_1351_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1452_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v_p_1369_; lean_object* v_a_1370_; lean_object* v_p_1371_; lean_object* v___x_1372_; uint8_t v___x_1373_; 
v_p_1369_ = lean_ctor_get(v_c_1347_, 0);
v_a_1370_ = lean_array_uget_borrowed(v_as_1348_, v_i_1350_);
v_p_1371_ = lean_ctor_get(v_a_1370_, 0);
v___x_1372_ = lean_box(0);
v___x_1373_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_1369_, v_p_1371_);
if (v___x_1373_ == 0)
{
lean_object* v___x_1374_; size_t v___x_1375_; size_t v___x_1376_; lean_object* v___x_1377_; 
lean_del_object(v___x_1367_);
lean_dec(v_snd_1365_);
v___x_1374_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1___closed__0));
v___x_1375_ = ((size_t)1ULL);
v___x_1376_ = lean_usize_add(v_i_1350_, v___x_1375_);
v___x_1377_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4(v_c_1347_, v_as_1348_, v_sz_1349_, v___x_1376_, v___x_1374_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
return v___x_1377_;
}
else
{
lean_object* v___x_1378_; 
lean_inc_ref(v_p_1369_);
lean_inc(v_a_1370_);
v___x_1378_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_1370_, v___y_1352_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v_toCold_1379_; lean_object* v_options_1380_; lean_object* v_inheritedTraceOptions_1381_; uint8_t v_hasTrace_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1395_; 
lean_dec_ref_known(v___x_1378_, 1);
v_toCold_1379_ = lean_ctor_get(v___y_1360_, 0);
v_options_1380_ = lean_ctor_get(v_toCold_1379_, 2);
v_inheritedTraceOptions_1381_ = lean_ctor_get(v_toCold_1379_, 11);
v_hasTrace_1382_ = lean_ctor_get_uint8(v_options_1380_, sizeof(void*)*1);
lean_inc(v_a_1370_);
v___x_1383_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1383_, 0, v_c_1347_);
lean_ctor_set(v___x_1383_, 1, v_a_1370_);
v___x_1384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1384_, 0, v_p_1369_);
lean_ctor_set(v___x_1384_, 1, v___x_1383_);
if (v_hasTrace_1382_ == 0)
{
v___y_1386_ = v___y_1352_;
v___y_1387_ = v___y_1353_;
v___y_1388_ = v___y_1354_;
v___y_1389_ = v___y_1355_;
v___y_1390_ = v___y_1356_;
v___y_1391_ = v___y_1357_;
v___y_1392_ = v___y_1358_;
v___y_1393_ = v___y_1359_;
v___y_1394_ = v___y_1360_;
v___y_1395_ = v___y_1361_;
goto v___jp_1385_;
}
else
{
lean_object* v___x_1420_; lean_object* v___x_1421_; uint8_t v___x_1422_; 
v___x_1420_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_1421_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5);
v___x_1422_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1381_, v_options_1380_, v___x_1421_);
if (v___x_1422_ == 0)
{
v___y_1386_ = v___y_1352_;
v___y_1387_ = v___y_1353_;
v___y_1388_ = v___y_1354_;
v___y_1389_ = v___y_1355_;
v___y_1390_ = v___y_1356_;
v___y_1391_ = v___y_1357_;
v___y_1392_ = v___y_1358_;
v___y_1393_ = v___y_1359_;
v___y_1394_ = v___y_1360_;
v___y_1395_ = v___y_1361_;
goto v___jp_1385_;
}
else
{
lean_object* v___x_1423_; 
lean_inc_ref(v___x_1384_);
v___x_1423_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_1384_, v___y_1352_, v___y_1360_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v_a_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
lean_inc(v_a_1424_);
lean_dec_ref_known(v___x_1423_, 1);
v___x_1425_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7);
v___x_1426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1426_, 0, v___x_1425_);
lean_ctor_set(v___x_1426_, 1, v_a_1424_);
v___x_1427_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_1420_, v___x_1426_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_dec_ref_known(v___x_1427_, 1);
v___y_1386_ = v___y_1352_;
v___y_1387_ = v___y_1353_;
v___y_1388_ = v___y_1354_;
v___y_1389_ = v___y_1355_;
v___y_1390_ = v___y_1356_;
v___y_1391_ = v___y_1357_;
v___y_1392_ = v___y_1358_;
v___y_1393_ = v___y_1359_;
v___y_1394_ = v___y_1360_;
v___y_1395_ = v___y_1361_;
goto v___jp_1385_;
}
else
{
lean_object* v_a_1428_; lean_object* v___x_1430_; uint8_t v_isShared_1431_; uint8_t v_isSharedCheck_1435_; 
lean_dec_ref_known(v___x_1384_, 2);
lean_del_object(v___x_1367_);
lean_dec(v_snd_1365_);
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1430_ = v___x_1427_;
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
else
{
lean_inc(v_a_1428_);
lean_dec(v___x_1427_);
v___x_1430_ = lean_box(0);
v_isShared_1431_ = v_isSharedCheck_1435_;
goto v_resetjp_1429_;
}
v_resetjp_1429_:
{
lean_object* v___x_1433_; 
if (v_isShared_1431_ == 0)
{
v___x_1433_ = v___x_1430_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v_a_1428_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
}
else
{
lean_object* v_a_1436_; lean_object* v___x_1438_; uint8_t v_isShared_1439_; uint8_t v_isSharedCheck_1443_; 
lean_dec_ref_known(v___x_1384_, 2);
lean_del_object(v___x_1367_);
lean_dec(v_snd_1365_);
v_a_1436_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1438_ = v___x_1423_;
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
else
{
lean_inc(v_a_1436_);
lean_dec(v___x_1423_);
v___x_1438_ = lean_box(0);
v_isShared_1439_ = v_isSharedCheck_1443_;
goto v_resetjp_1437_;
}
v_resetjp_1437_:
{
lean_object* v___x_1441_; 
if (v_isShared_1439_ == 0)
{
v___x_1441_ = v___x_1438_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_a_1436_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
}
}
v___jp_1385_:
{
lean_object* v___x_1396_; 
lean_inc(v___y_1395_);
lean_inc_ref(v___y_1394_);
lean_inc(v___y_1393_);
lean_inc_ref(v___y_1392_);
lean_inc(v___y_1391_);
lean_inc_ref(v___y_1390_);
lean_inc(v___y_1389_);
lean_inc_ref(v___y_1388_);
lean_inc(v___y_1387_);
lean_inc(v___y_1386_);
v___x_1396_ = lean_grind_cutsat_assert_eq(v___x_1384_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
if (lean_obj_tag(v___x_1396_) == 0)
{
lean_object* v___x_1398_; uint8_t v_isShared_1399_; uint8_t v_isSharedCheck_1410_; 
v_isSharedCheck_1410_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1410_ == 0)
{
lean_object* v_unused_1411_; 
v_unused_1411_ = lean_ctor_get(v___x_1396_, 0);
lean_dec(v_unused_1411_);
v___x_1398_ = v___x_1396_;
v_isShared_1399_ = v_isSharedCheck_1410_;
goto v_resetjp_1397_;
}
else
{
lean_dec(v___x_1396_);
v___x_1398_ = lean_box(0);
v_isShared_1399_ = v_isSharedCheck_1410_;
goto v_resetjp_1397_;
}
v_resetjp_1397_:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1403_; 
v___x_1400_ = lean_box(v___x_1373_);
v___x_1401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1401_, 0, v___x_1400_);
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 1, v___x_1372_);
lean_ctor_set(v___x_1367_, 0, v___x_1401_);
v___x_1403_ = v___x_1367_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1401_);
lean_ctor_set(v_reuseFailAlloc_1409_, 1, v___x_1372_);
v___x_1403_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1407_; 
v___x_1404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1404_, 0, v___x_1403_);
v___x_1405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1404_);
lean_ctor_set(v___x_1405_, 1, v_snd_1365_);
if (v_isShared_1399_ == 0)
{
lean_ctor_set(v___x_1398_, 0, v___x_1405_);
v___x_1407_ = v___x_1398_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1408_; 
v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1408_, 0, v___x_1405_);
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
else
{
lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1419_; 
lean_del_object(v___x_1367_);
lean_dec(v_snd_1365_);
v_a_1412_ = lean_ctor_get(v___x_1396_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1396_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1414_ = v___x_1396_;
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v___x_1396_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1417_; 
if (v_isShared_1415_ == 0)
{
v___x_1417_ = v___x_1414_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_a_1412_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
}
}
else
{
lean_object* v_a_1444_; lean_object* v___x_1446_; uint8_t v_isShared_1447_; uint8_t v_isSharedCheck_1451_; 
lean_dec_ref(v_p_1369_);
lean_del_object(v___x_1367_);
lean_dec(v_snd_1365_);
lean_dec_ref(v_c_1347_);
v_a_1444_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1451_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1446_ = v___x_1378_;
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
else
{
lean_inc(v_a_1444_);
lean_dec(v___x_1378_);
v___x_1446_ = lean_box(0);
v_isShared_1447_ = v_isSharedCheck_1451_;
goto v_resetjp_1445_;
}
v_resetjp_1445_:
{
lean_object* v___x_1449_; 
if (v_isShared_1447_ == 0)
{
v___x_1449_ = v___x_1446_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v_a_1444_);
v___x_1449_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
return v___x_1449_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1___boxed(lean_object* v_c_1454_, lean_object* v_as_1455_, lean_object* v_sz_1456_, lean_object* v_i_1457_, lean_object* v_b_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
size_t v_sz_boxed_1470_; size_t v_i_boxed_1471_; lean_object* v_res_1472_; 
v_sz_boxed_1470_ = lean_unbox_usize(v_sz_1456_);
lean_dec(v_sz_1456_);
v_i_boxed_1471_ = lean_unbox_usize(v_i_1457_);
lean_dec(v_i_1457_);
v_res_1472_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1(v_c_1454_, v_as_1455_, v_sz_boxed_1470_, v_i_boxed_1471_, v_b_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec(v___y_1459_);
lean_dec_ref(v_as_1455_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0(lean_object* v_c_1473_, lean_object* v_t_1474_, lean_object* v_init_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v_root_1487_; lean_object* v_tail_1488_; lean_object* v___x_1489_; 
v_root_1487_ = lean_ctor_get(v_t_1474_, 0);
v_tail_1488_ = lean_ctor_get(v_t_1474_, 1);
lean_inc_ref(v_c_1473_);
lean_inc_ref(v_init_1475_);
v___x_1489_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(v_init_1475_, v_c_1473_, v_root_1487_, v_init_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
lean_dec_ref(v_init_1475_);
if (lean_obj_tag(v___x_1489_) == 0)
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1526_; 
v_a_1490_ = lean_ctor_get(v___x_1489_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1489_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1492_ = v___x_1489_;
v_isShared_1493_ = v_isSharedCheck_1526_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1489_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1526_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
if (lean_obj_tag(v_a_1490_) == 0)
{
lean_object* v_a_1494_; lean_object* v___x_1496_; 
lean_dec_ref(v_c_1473_);
v_a_1494_ = lean_ctor_get(v_a_1490_, 0);
lean_inc(v_a_1494_);
lean_dec_ref_known(v_a_1490_, 1);
if (v_isShared_1493_ == 0)
{
lean_ctor_set(v___x_1492_, 0, v_a_1494_);
v___x_1496_ = v___x_1492_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_a_1494_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
else
{
lean_object* v_a_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; size_t v_sz_1501_; size_t v___x_1502_; lean_object* v___x_1503_; 
lean_del_object(v___x_1492_);
v_a_1498_ = lean_ctor_get(v_a_1490_, 0);
lean_inc(v_a_1498_);
lean_dec_ref_known(v_a_1490_, 1);
v___x_1499_ = lean_box(0);
v___x_1500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1499_);
lean_ctor_set(v___x_1500_, 1, v_a_1498_);
v_sz_1501_ = lean_array_size(v_tail_1488_);
v___x_1502_ = ((size_t)0ULL);
v___x_1503_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1(v_c_1473_, v_tail_1488_, v_sz_1501_, v___x_1502_, v___x_1500_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
if (lean_obj_tag(v___x_1503_) == 0)
{
lean_object* v_a_1504_; lean_object* v___x_1506_; uint8_t v_isShared_1507_; uint8_t v_isSharedCheck_1517_; 
v_a_1504_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1506_ = v___x_1503_;
v_isShared_1507_ = v_isSharedCheck_1517_;
goto v_resetjp_1505_;
}
else
{
lean_inc(v_a_1504_);
lean_dec(v___x_1503_);
v___x_1506_ = lean_box(0);
v_isShared_1507_ = v_isSharedCheck_1517_;
goto v_resetjp_1505_;
}
v_resetjp_1505_:
{
lean_object* v_fst_1508_; 
v_fst_1508_ = lean_ctor_get(v_a_1504_, 0);
if (lean_obj_tag(v_fst_1508_) == 0)
{
lean_object* v_snd_1509_; lean_object* v___x_1511_; 
v_snd_1509_ = lean_ctor_get(v_a_1504_, 1);
lean_inc(v_snd_1509_);
lean_dec(v_a_1504_);
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 0, v_snd_1509_);
v___x_1511_ = v___x_1506_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_snd_1509_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
else
{
lean_object* v_val_1513_; lean_object* v___x_1515_; 
lean_inc_ref(v_fst_1508_);
lean_dec(v_a_1504_);
v_val_1513_ = lean_ctor_get(v_fst_1508_, 0);
lean_inc(v_val_1513_);
lean_dec_ref_known(v_fst_1508_, 1);
if (v_isShared_1507_ == 0)
{
lean_ctor_set(v___x_1506_, 0, v_val_1513_);
v___x_1515_ = v___x_1506_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_val_1513_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
}
else
{
lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1525_; 
v_a_1518_ = lean_ctor_get(v___x_1503_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1520_ = v___x_1503_;
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v___x_1503_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1523_; 
if (v_isShared_1521_ == 0)
{
v___x_1523_ = v___x_1520_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_a_1518_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
}
}
}
else
{
lean_object* v_a_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1534_; 
lean_dec_ref(v_c_1473_);
v_a_1527_ = lean_ctor_get(v___x_1489_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1489_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1529_ = v___x_1489_;
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_a_1527_);
lean_dec(v___x_1489_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1532_; 
if (v_isShared_1530_ == 0)
{
v___x_1532_ = v___x_1529_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_a_1527_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0___boxed(lean_object* v_c_1535_, lean_object* v_t_1536_, lean_object* v_init_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0(v_c_1535_, v_t_1536_, v_init_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
lean_dec(v___y_1541_);
lean_dec_ref(v___y_1540_);
lean_dec(v___y_1539_);
lean_dec(v___y_1538_);
lean_dec_ref(v_t_1536_);
return v_res_1549_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0(void){
_start:
{
lean_object* v___x_1550_; 
v___x_1550_ = l_Lean_instInhabitedPersistentArray_default___redArg();
return v___x_1550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq(lean_object* v_c_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_){
_start:
{
lean_object* v_p_1563_; 
v_p_1563_ = lean_ctor_get(v_c_1551_, 0);
if (lean_obj_tag(v_p_1563_) == 1)
{
lean_object* v_k_1564_; lean_object* v_v_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; 
v_k_1564_ = lean_ctor_get(v_p_1563_, 0);
v_v_1565_ = lean_ctor_get(v_p_1563_, 1);
v___x_1566_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0);
v___x_1567_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1552_, v_a_1560_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v_a_1568_; lean_object* v___y_1570_; lean_object* v___x_1596_; uint8_t v___x_1597_; 
v_a_1568_ = lean_ctor_get(v___x_1567_, 0);
lean_inc(v_a_1568_);
lean_dec_ref_known(v___x_1567_, 1);
v___x_1596_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9);
v___x_1597_ = lean_int_dec_lt(v_k_1564_, v___x_1596_);
if (v___x_1597_ == 0)
{
lean_object* v_lowers_1598_; lean_object* v_size_1599_; uint8_t v___x_1600_; 
v_lowers_1598_ = lean_ctor_get(v_a_1568_, 6);
lean_inc_ref(v_lowers_1598_);
lean_dec(v_a_1568_);
v_size_1599_ = lean_ctor_get(v_lowers_1598_, 2);
v___x_1600_ = lean_nat_dec_lt(v_v_1565_, v_size_1599_);
if (v___x_1600_ == 0)
{
lean_object* v___x_1601_; 
lean_dec_ref(v_lowers_1598_);
v___x_1601_ = l_outOfBounds___redArg(v___x_1566_);
v___y_1570_ = v___x_1601_;
goto v___jp_1569_;
}
else
{
lean_object* v___x_1602_; 
v___x_1602_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1566_, v_lowers_1598_, v_v_1565_);
lean_dec_ref(v_lowers_1598_);
v___y_1570_ = v___x_1602_;
goto v___jp_1569_;
}
}
else
{
lean_object* v_uppers_1603_; lean_object* v_size_1604_; uint8_t v___x_1605_; 
v_uppers_1603_ = lean_ctor_get(v_a_1568_, 7);
lean_inc_ref(v_uppers_1603_);
lean_dec(v_a_1568_);
v_size_1604_ = lean_ctor_get(v_uppers_1603_, 2);
v___x_1605_ = lean_nat_dec_lt(v_v_1565_, v_size_1604_);
if (v___x_1605_ == 0)
{
lean_object* v___x_1606_; 
lean_dec_ref(v_uppers_1603_);
v___x_1606_ = l_outOfBounds___redArg(v___x_1566_);
v___y_1570_ = v___x_1606_;
goto v___jp_1569_;
}
else
{
lean_object* v___x_1607_; 
v___x_1607_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1566_, v_uppers_1603_, v_v_1565_);
lean_dec_ref(v_uppers_1603_);
v___y_1570_ = v___x_1607_;
goto v___jp_1569_;
}
}
v___jp_1569_:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1571_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__0));
v___x_1572_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0(v_c_1551_, v___y_1570_, v___x_1571_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_);
lean_dec_ref(v___y_1570_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v_a_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1587_; 
v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1575_ = v___x_1572_;
v_isShared_1576_ = v_isSharedCheck_1587_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_a_1573_);
lean_dec(v___x_1572_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1587_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
lean_object* v_fst_1577_; 
v_fst_1577_ = lean_ctor_get(v_a_1573_, 0);
lean_inc(v_fst_1577_);
lean_dec(v_a_1573_);
if (lean_obj_tag(v_fst_1577_) == 0)
{
uint8_t v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1581_; 
v___x_1578_ = 0;
v___x_1579_ = lean_box(v___x_1578_);
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 0, v___x_1579_);
v___x_1581_ = v___x_1575_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v___x_1579_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
else
{
lean_object* v_val_1583_; lean_object* v___x_1585_; 
v_val_1583_ = lean_ctor_get(v_fst_1577_, 0);
lean_inc(v_val_1583_);
lean_dec_ref_known(v_fst_1577_, 1);
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 0, v_val_1583_);
v___x_1585_ = v___x_1575_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_val_1583_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
}
else
{
lean_object* v_a_1588_; lean_object* v___x_1590_; uint8_t v_isShared_1591_; uint8_t v_isSharedCheck_1595_; 
v_a_1588_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1595_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1590_ = v___x_1572_;
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
else
{
lean_inc(v_a_1588_);
lean_dec(v___x_1572_);
v___x_1590_ = lean_box(0);
v_isShared_1591_ = v_isSharedCheck_1595_;
goto v_resetjp_1589_;
}
v_resetjp_1589_:
{
lean_object* v___x_1593_; 
if (v_isShared_1591_ == 0)
{
v___x_1593_ = v___x_1590_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_a_1588_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
}
else
{
lean_object* v_a_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1615_; 
lean_dec_ref(v_c_1551_);
v_a_1608_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1615_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1615_ == 0)
{
v___x_1610_ = v___x_1567_;
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
else
{
lean_inc(v_a_1608_);
lean_dec(v___x_1567_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1615_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1613_; 
if (v_isShared_1611_ == 0)
{
v___x_1613_ = v___x_1610_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v_a_1608_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
}
else
{
lean_object* v___x_1616_; 
v___x_1616_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_1551_, v_a_1552_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_);
return v___x_1616_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___boxed(lean_object* v_c_1617_, lean_object* v_a_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq(v_c_1617_, v_a_1618_, v_a_1619_, v_a_1620_, v_a_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_);
lean_dec(v_a_1627_);
lean_dec_ref(v_a_1626_);
lean_dec(v_a_1625_);
lean_dec_ref(v_a_1624_);
lean_dec(v_a_1623_);
lean_dec_ref(v_a_1622_);
lean_dec(v_a_1621_);
lean_dec_ref(v_a_1620_);
lean_dec(v_a_1619_);
lean_dec(v_a_1618_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(lean_object* v___x_1630_, lean_object* v_as_1631_, size_t v_i_1632_, size_t v_stop_1633_, lean_object* v_b_1634_){
_start:
{
lean_object* v___y_1636_; uint8_t v___x_1640_; 
v___x_1640_ = lean_usize_dec_eq(v_i_1632_, v_stop_1633_);
if (v___x_1640_ == 0)
{
lean_object* v___x_1641_; lean_object* v_p_1642_; uint8_t v___x_1643_; 
v___x_1641_ = lean_array_uget_borrowed(v_as_1631_, v_i_1632_);
v_p_1642_ = lean_ctor_get(v___x_1641_, 0);
v___x_1643_ = l_Int_Internal_Linear_instBEqPoly_beq(v_p_1642_, v___x_1630_);
if (v___x_1643_ == 0)
{
lean_object* v___x_1644_; 
lean_inc(v___x_1641_);
v___x_1644_ = l_Lean_PersistentArray_push___redArg(v_b_1634_, v___x_1641_);
v___y_1636_ = v___x_1644_;
goto v___jp_1635_;
}
else
{
v___y_1636_ = v_b_1634_;
goto v___jp_1635_;
}
}
else
{
return v_b_1634_;
}
v___jp_1635_:
{
size_t v___x_1637_; size_t v___x_1638_; 
v___x_1637_ = ((size_t)1ULL);
v___x_1638_ = lean_usize_add(v_i_1632_, v___x_1637_);
v_i_1632_ = v___x_1638_;
v_b_1634_ = v___y_1636_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1___boxed(lean_object* v___x_1645_, lean_object* v_as_1646_, lean_object* v_i_1647_, lean_object* v_stop_1648_, lean_object* v_b_1649_){
_start:
{
size_t v_i_boxed_1650_; size_t v_stop_boxed_1651_; lean_object* v_res_1652_; 
v_i_boxed_1650_ = lean_unbox_usize(v_i_1647_);
lean_dec(v_i_1647_);
v_stop_boxed_1651_ = lean_unbox_usize(v_stop_1648_);
lean_dec(v_stop_1648_);
v_res_1652_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1645_, v_as_1646_, v_i_boxed_1650_, v_stop_boxed_1651_, v_b_1649_);
lean_dec_ref(v_as_1646_);
lean_dec_ref(v___x_1645_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(lean_object* v___x_1653_, lean_object* v_x_1654_, lean_object* v_x_1655_){
_start:
{
if (lean_obj_tag(v_x_1654_) == 0)
{
lean_object* v_cs_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; uint8_t v___x_1659_; 
v_cs_1656_ = lean_ctor_get(v_x_1654_, 0);
v___x_1657_ = lean_unsigned_to_nat(0u);
v___x_1658_ = lean_array_get_size(v_cs_1656_);
v___x_1659_ = lean_nat_dec_lt(v___x_1657_, v___x_1658_);
if (v___x_1659_ == 0)
{
return v_x_1655_;
}
else
{
size_t v___x_1660_; size_t v___x_1661_; lean_object* v___x_1662_; 
v___x_1660_ = ((size_t)0ULL);
v___x_1661_ = lean_usize_of_nat(v___x_1658_);
v___x_1662_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1653_, v_cs_1656_, v___x_1660_, v___x_1661_, v_x_1655_);
return v___x_1662_;
}
}
else
{
lean_object* v_vs_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; uint8_t v___x_1666_; 
v_vs_1663_ = lean_ctor_get(v_x_1654_, 0);
v___x_1664_ = lean_unsigned_to_nat(0u);
v___x_1665_ = lean_array_get_size(v_vs_1663_);
v___x_1666_ = lean_nat_dec_lt(v___x_1664_, v___x_1665_);
if (v___x_1666_ == 0)
{
return v_x_1655_;
}
else
{
size_t v___x_1667_; size_t v___x_1668_; lean_object* v___x_1669_; 
v___x_1667_ = ((size_t)0ULL);
v___x_1668_ = lean_usize_of_nat(v___x_1665_);
v___x_1669_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1653_, v_vs_1663_, v___x_1667_, v___x_1668_, v_x_1655_);
return v___x_1669_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(lean_object* v___x_1670_, lean_object* v_as_1671_, size_t v_i_1672_, size_t v_stop_1673_, lean_object* v_b_1674_){
_start:
{
uint8_t v___x_1675_; 
v___x_1675_ = lean_usize_dec_eq(v_i_1672_, v_stop_1673_);
if (v___x_1675_ == 0)
{
lean_object* v___x_1676_; lean_object* v___x_1677_; size_t v___x_1678_; size_t v___x_1679_; 
v___x_1676_ = lean_array_uget_borrowed(v_as_1671_, v_i_1672_);
v___x_1677_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(v___x_1670_, v___x_1676_, v_b_1674_);
v___x_1678_ = ((size_t)1ULL);
v___x_1679_ = lean_usize_add(v_i_1672_, v___x_1678_);
v_i_1672_ = v___x_1679_;
v_b_1674_ = v___x_1677_;
goto _start;
}
else
{
return v_b_1674_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v___x_1681_, lean_object* v_as_1682_, lean_object* v_i_1683_, lean_object* v_stop_1684_, lean_object* v_b_1685_){
_start:
{
size_t v_i_boxed_1686_; size_t v_stop_boxed_1687_; lean_object* v_res_1688_; 
v_i_boxed_1686_ = lean_unbox_usize(v_i_1683_);
lean_dec(v_i_1683_);
v_stop_boxed_1687_ = lean_unbox_usize(v_stop_1684_);
lean_dec(v_stop_1684_);
v_res_1688_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1681_, v_as_1682_, v_i_boxed_1686_, v_stop_boxed_1687_, v_b_1685_);
lean_dec_ref(v_as_1682_);
lean_dec_ref(v___x_1681_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2___boxed(lean_object* v___x_1689_, lean_object* v_x_1690_, lean_object* v_x_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(v___x_1689_, v_x_1690_, v_x_1691_);
lean_dec_ref(v_x_1690_);
lean_dec_ref(v___x_1689_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(lean_object* v___x_1693_, lean_object* v_x_1694_, size_t v_x_1695_, size_t v_x_1696_, lean_object* v_x_1697_){
_start:
{
if (lean_obj_tag(v_x_1694_) == 0)
{
lean_object* v_cs_1698_; lean_object* v___x_1699_; size_t v___x_1700_; lean_object* v_j_1701_; lean_object* v___x_1702_; size_t v___x_1703_; size_t v___x_1704_; size_t v___x_1705_; size_t v___x_1706_; size_t v___x_1707_; size_t v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; uint8_t v___x_1713_; 
v_cs_1698_ = lean_ctor_get(v_x_1694_, 0);
v___x_1699_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0);
v___x_1700_ = lean_usize_shift_right(v_x_1695_, v_x_1696_);
v_j_1701_ = lean_usize_to_nat(v___x_1700_);
v___x_1702_ = lean_array_get_borrowed(v___x_1699_, v_cs_1698_, v_j_1701_);
v___x_1703_ = ((size_t)1ULL);
v___x_1704_ = lean_usize_shift_left(v___x_1703_, v_x_1696_);
v___x_1705_ = lean_usize_sub(v___x_1704_, v___x_1703_);
v___x_1706_ = lean_usize_land(v_x_1695_, v___x_1705_);
v___x_1707_ = ((size_t)5ULL);
v___x_1708_ = lean_usize_sub(v_x_1696_, v___x_1707_);
v___x_1709_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(v___x_1693_, v___x_1702_, v___x_1706_, v___x_1708_, v_x_1697_);
v___x_1710_ = lean_unsigned_to_nat(1u);
v___x_1711_ = lean_nat_add(v_j_1701_, v___x_1710_);
lean_dec(v_j_1701_);
v___x_1712_ = lean_array_get_size(v_cs_1698_);
v___x_1713_ = lean_nat_dec_lt(v___x_1711_, v___x_1712_);
if (v___x_1713_ == 0)
{
lean_dec(v___x_1711_);
return v___x_1709_;
}
else
{
size_t v___x_1714_; size_t v___x_1715_; lean_object* v___x_1716_; 
v___x_1714_ = lean_usize_of_nat(v___x_1711_);
lean_dec(v___x_1711_);
v___x_1715_ = lean_usize_of_nat(v___x_1712_);
v___x_1716_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1693_, v_cs_1698_, v___x_1714_, v___x_1715_, v___x_1709_);
return v___x_1716_;
}
}
else
{
lean_object* v_vs_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; uint8_t v___x_1720_; 
v_vs_1717_ = lean_ctor_get(v_x_1694_, 0);
v___x_1718_ = lean_usize_to_nat(v_x_1695_);
v___x_1719_ = lean_array_get_size(v_vs_1717_);
v___x_1720_ = lean_nat_dec_lt(v___x_1718_, v___x_1719_);
if (v___x_1720_ == 0)
{
lean_dec(v___x_1718_);
return v_x_1697_;
}
else
{
size_t v___x_1721_; size_t v___x_1722_; lean_object* v___x_1723_; 
v___x_1721_ = lean_usize_of_nat(v___x_1718_);
lean_dec(v___x_1718_);
v___x_1722_ = lean_usize_of_nat(v___x_1719_);
v___x_1723_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1693_, v_vs_1717_, v___x_1721_, v___x_1722_, v_x_1697_);
return v___x_1723_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0___boxed(lean_object* v___x_1724_, lean_object* v_x_1725_, lean_object* v_x_1726_, lean_object* v_x_1727_, lean_object* v_x_1728_){
_start:
{
size_t v_x_20533__boxed_1729_; size_t v_x_20534__boxed_1730_; lean_object* v_res_1731_; 
v_x_20533__boxed_1729_ = lean_unbox_usize(v_x_1726_);
lean_dec(v_x_1726_);
v_x_20534__boxed_1730_ = lean_unbox_usize(v_x_1727_);
lean_dec(v_x_1727_);
v_res_1731_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(v___x_1724_, v_x_1725_, v_x_20533__boxed_1729_, v_x_20534__boxed_1730_, v_x_1728_);
lean_dec_ref(v_x_1725_);
lean_dec_ref(v___x_1724_);
return v_res_1731_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(lean_object* v___x_1732_, lean_object* v_t_1733_, lean_object* v_init_1734_, lean_object* v_start_1735_){
_start:
{
lean_object* v___x_1736_; uint8_t v___x_1737_; 
v___x_1736_ = lean_unsigned_to_nat(0u);
v___x_1737_ = lean_nat_dec_eq(v_start_1735_, v___x_1736_);
if (v___x_1737_ == 0)
{
lean_object* v_root_1738_; lean_object* v_tail_1739_; size_t v_shift_1740_; lean_object* v_tailOff_1741_; uint8_t v___x_1742_; 
v_root_1738_ = lean_ctor_get(v_t_1733_, 0);
v_tail_1739_ = lean_ctor_get(v_t_1733_, 1);
v_shift_1740_ = lean_ctor_get_usize(v_t_1733_, 4);
v_tailOff_1741_ = lean_ctor_get(v_t_1733_, 3);
v___x_1742_ = lean_nat_dec_le(v_tailOff_1741_, v_start_1735_);
if (v___x_1742_ == 0)
{
size_t v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; uint8_t v___x_1746_; 
v___x_1743_ = lean_usize_of_nat(v_start_1735_);
v___x_1744_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(v___x_1732_, v_root_1738_, v___x_1743_, v_shift_1740_, v_init_1734_);
v___x_1745_ = lean_array_get_size(v_tail_1739_);
v___x_1746_ = lean_nat_dec_lt(v___x_1736_, v___x_1745_);
if (v___x_1746_ == 0)
{
return v___x_1744_;
}
else
{
size_t v___x_1747_; size_t v___x_1748_; lean_object* v___x_1749_; 
v___x_1747_ = ((size_t)0ULL);
v___x_1748_ = lean_usize_of_nat(v___x_1745_);
v___x_1749_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1732_, v_tail_1739_, v___x_1747_, v___x_1748_, v___x_1744_);
return v___x_1749_;
}
}
else
{
lean_object* v___x_1750_; lean_object* v___x_1751_; uint8_t v___x_1752_; 
v___x_1750_ = lean_nat_sub(v_start_1735_, v_tailOff_1741_);
v___x_1751_ = lean_array_get_size(v_tail_1739_);
v___x_1752_ = lean_nat_dec_lt(v___x_1750_, v___x_1751_);
if (v___x_1752_ == 0)
{
lean_dec(v___x_1750_);
return v_init_1734_;
}
else
{
size_t v___x_1753_; size_t v___x_1754_; lean_object* v___x_1755_; 
v___x_1753_ = lean_usize_of_nat(v___x_1750_);
lean_dec(v___x_1750_);
v___x_1754_ = lean_usize_of_nat(v___x_1751_);
v___x_1755_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1732_, v_tail_1739_, v___x_1753_, v___x_1754_, v_init_1734_);
return v___x_1755_;
}
}
}
else
{
lean_object* v_root_1756_; lean_object* v_tail_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; uint8_t v___x_1760_; 
v_root_1756_ = lean_ctor_get(v_t_1733_, 0);
v_tail_1757_ = lean_ctor_get(v_t_1733_, 1);
v___x_1758_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(v___x_1732_, v_root_1756_, v_init_1734_);
v___x_1759_ = lean_array_get_size(v_tail_1757_);
v___x_1760_ = lean_nat_dec_lt(v___x_1736_, v___x_1759_);
if (v___x_1760_ == 0)
{
return v___x_1758_;
}
else
{
size_t v___x_1761_; size_t v___x_1762_; lean_object* v___x_1763_; 
v___x_1761_ = ((size_t)0ULL);
v___x_1762_ = lean_usize_of_nat(v___x_1759_);
v___x_1763_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1732_, v_tail_1757_, v___x_1761_, v___x_1762_, v___x_1758_);
return v___x_1763_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0___boxed(lean_object* v___x_1764_, lean_object* v_t_1765_, lean_object* v_init_1766_, lean_object* v_start_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(v___x_1764_, v_t_1765_, v_init_1766_, v_start_1767_);
lean_dec(v_start_1767_);
lean_dec_ref(v_t_1765_);
lean_dec_ref(v___x_1764_);
return v_res_1768_;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; 
v___x_1769_ = lean_unsigned_to_nat(32u);
v___x_1770_ = lean_mk_empty_array_with_capacity(v___x_1769_);
v___x_1771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1771_, 0, v___x_1770_);
return v___x_1771_;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1(void){
_start:
{
size_t v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; 
v___x_1772_ = ((size_t)5ULL);
v___x_1773_ = lean_unsigned_to_nat(0u);
v___x_1774_ = lean_unsigned_to_nat(32u);
v___x_1775_ = lean_mk_empty_array_with_capacity(v___x_1774_);
v___x_1776_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0);
v___x_1777_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1777_, 0, v___x_1776_);
lean_ctor_set(v___x_1777_, 1, v___x_1775_);
lean_ctor_set(v___x_1777_, 2, v___x_1773_);
lean_ctor_set(v___x_1777_, 3, v___x_1773_);
lean_ctor_set_usize(v___x_1777_, 4, v___x_1772_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(lean_object* v___x_1778_, lean_object* v_x_1779_, size_t v_x_1780_, size_t v_x_1781_){
_start:
{
if (lean_obj_tag(v_x_1779_) == 0)
{
lean_object* v_cs_1782_; size_t v_j_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; uint8_t v___x_1786_; 
v_cs_1782_ = lean_ctor_get(v_x_1779_, 0);
v_j_1783_ = lean_usize_shift_right(v_x_1780_, v_x_1781_);
v___x_1784_ = lean_usize_to_nat(v_j_1783_);
v___x_1785_ = lean_array_get_size(v_cs_1782_);
v___x_1786_ = lean_nat_dec_lt(v___x_1784_, v___x_1785_);
if (v___x_1786_ == 0)
{
lean_dec(v___x_1784_);
return v_x_1779_;
}
else
{
lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1804_; 
lean_inc_ref(v_cs_1782_);
v_isSharedCheck_1804_ = !lean_is_exclusive(v_x_1779_);
if (v_isSharedCheck_1804_ == 0)
{
lean_object* v_unused_1805_; 
v_unused_1805_ = lean_ctor_get(v_x_1779_, 0);
lean_dec(v_unused_1805_);
v___x_1788_ = v_x_1779_;
v_isShared_1789_ = v_isSharedCheck_1804_;
goto v_resetjp_1787_;
}
else
{
lean_dec(v_x_1779_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1804_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
size_t v___x_1790_; size_t v___x_1791_; size_t v___x_1792_; size_t v_i_1793_; size_t v___x_1794_; size_t v_shift_1795_; lean_object* v_v_1796_; lean_object* v___x_1797_; lean_object* v_xs_x27_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1802_; 
v___x_1790_ = ((size_t)1ULL);
v___x_1791_ = lean_usize_shift_left(v___x_1790_, v_x_1781_);
v___x_1792_ = lean_usize_sub(v___x_1791_, v___x_1790_);
v_i_1793_ = lean_usize_land(v_x_1780_, v___x_1792_);
v___x_1794_ = ((size_t)5ULL);
v_shift_1795_ = lean_usize_sub(v_x_1781_, v___x_1794_);
v_v_1796_ = lean_array_fget(v_cs_1782_, v___x_1784_);
v___x_1797_ = lean_box(0);
v_xs_x27_1798_ = lean_array_fset(v_cs_1782_, v___x_1784_, v___x_1797_);
v___x_1799_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(v___x_1778_, v_v_1796_, v_i_1793_, v_shift_1795_);
v___x_1800_ = lean_array_fset(v_xs_x27_1798_, v___x_1784_, v___x_1799_);
lean_dec(v___x_1784_);
if (v_isShared_1789_ == 0)
{
lean_ctor_set(v___x_1788_, 0, v___x_1800_);
v___x_1802_ = v___x_1788_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v___x_1800_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
}
else
{
lean_object* v_vs_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; uint8_t v___x_1809_; 
v_vs_1806_ = lean_ctor_get(v_x_1779_, 0);
v___x_1807_ = lean_usize_to_nat(v_x_1780_);
v___x_1808_ = lean_array_get_size(v_vs_1806_);
v___x_1809_ = lean_nat_dec_lt(v___x_1807_, v___x_1808_);
if (v___x_1809_ == 0)
{
lean_dec(v___x_1807_);
return v_x_1779_;
}
else
{
lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1823_; 
lean_inc_ref(v_vs_1806_);
v_isSharedCheck_1823_ = !lean_is_exclusive(v_x_1779_);
if (v_isSharedCheck_1823_ == 0)
{
lean_object* v_unused_1824_; 
v_unused_1824_ = lean_ctor_get(v_x_1779_, 0);
lean_dec(v_unused_1824_);
v___x_1811_ = v_x_1779_;
v_isShared_1812_ = v_isSharedCheck_1823_;
goto v_resetjp_1810_;
}
else
{
lean_dec(v_x_1779_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1823_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v_v_1813_; lean_object* v___x_1814_; lean_object* v_xs_x27_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1821_; 
v_v_1813_ = lean_array_fget(v_vs_1806_, v___x_1807_);
v___x_1814_ = lean_box(0);
v_xs_x27_1815_ = lean_array_fset(v_vs_1806_, v___x_1807_, v___x_1814_);
v___x_1816_ = lean_unsigned_to_nat(0u);
v___x_1817_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1);
v___x_1818_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(v___x_1778_, v_v_1813_, v___x_1817_, v___x_1816_);
lean_dec(v_v_1813_);
v___x_1819_ = lean_array_fset(v_xs_x27_1815_, v___x_1807_, v___x_1818_);
lean_dec(v___x_1807_);
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 0, v___x_1819_);
v___x_1821_ = v___x_1811_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1822_; 
v_reuseFailAlloc_1822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1822_, 0, v___x_1819_);
v___x_1821_ = v_reuseFailAlloc_1822_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
return v___x_1821_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___boxed(lean_object* v___x_1825_, lean_object* v_x_1826_, lean_object* v_x_1827_, lean_object* v_x_1828_){
_start:
{
size_t v_x_20665__boxed_1829_; size_t v_x_20666__boxed_1830_; lean_object* v_res_1831_; 
v_x_20665__boxed_1829_ = lean_unbox_usize(v_x_1827_);
lean_dec(v_x_1827_);
v_x_20666__boxed_1830_ = lean_unbox_usize(v_x_1828_);
lean_dec(v_x_1828_);
v_res_1831_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(v___x_1825_, v_x_1826_, v_x_20665__boxed_1829_, v_x_20666__boxed_1830_);
lean_dec_ref(v___x_1825_);
return v_res_1831_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1(lean_object* v___x_1832_, lean_object* v_t_1833_, lean_object* v_i_1834_){
_start:
{
lean_object* v_root_1835_; lean_object* v_tail_1836_; lean_object* v_size_1837_; size_t v_shift_1838_; lean_object* v_tailOff_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1867_; 
v_root_1835_ = lean_ctor_get(v_t_1833_, 0);
v_tail_1836_ = lean_ctor_get(v_t_1833_, 1);
v_size_1837_ = lean_ctor_get(v_t_1833_, 2);
v_shift_1838_ = lean_ctor_get_usize(v_t_1833_, 4);
v_tailOff_1839_ = lean_ctor_get(v_t_1833_, 3);
v_isSharedCheck_1867_ = !lean_is_exclusive(v_t_1833_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1841_ = v_t_1833_;
v_isShared_1842_ = v_isSharedCheck_1867_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_tailOff_1839_);
lean_inc(v_size_1837_);
lean_inc(v_tail_1836_);
lean_inc(v_root_1835_);
lean_dec(v_t_1833_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1867_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
uint8_t v___x_1843_; 
v___x_1843_ = lean_nat_dec_le(v_tailOff_1839_, v_i_1834_);
if (v___x_1843_ == 0)
{
size_t v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1847_; 
v___x_1844_ = lean_usize_of_nat(v_i_1834_);
v___x_1845_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(v___x_1832_, v_root_1835_, v___x_1844_, v_shift_1838_);
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 0, v___x_1845_);
v___x_1847_ = v___x_1841_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v___x_1845_);
lean_ctor_set(v_reuseFailAlloc_1848_, 1, v_tail_1836_);
lean_ctor_set(v_reuseFailAlloc_1848_, 2, v_size_1837_);
lean_ctor_set(v_reuseFailAlloc_1848_, 3, v_tailOff_1839_);
lean_ctor_set_usize(v_reuseFailAlloc_1848_, 4, v_shift_1838_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
else
{
lean_object* v___x_1849_; lean_object* v___x_1850_; uint8_t v___x_1851_; 
v___x_1849_ = lean_nat_sub(v_i_1834_, v_tailOff_1839_);
v___x_1850_ = lean_array_get_size(v_tail_1836_);
v___x_1851_ = lean_nat_dec_lt(v___x_1849_, v___x_1850_);
if (v___x_1851_ == 0)
{
lean_object* v___x_1853_; 
lean_dec(v___x_1849_);
if (v_isShared_1842_ == 0)
{
v___x_1853_ = v___x_1841_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_root_1835_);
lean_ctor_set(v_reuseFailAlloc_1854_, 1, v_tail_1836_);
lean_ctor_set(v_reuseFailAlloc_1854_, 2, v_size_1837_);
lean_ctor_set(v_reuseFailAlloc_1854_, 3, v_tailOff_1839_);
lean_ctor_set_usize(v_reuseFailAlloc_1854_, 4, v_shift_1838_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
else
{
lean_object* v_v_1855_; lean_object* v___x_1856_; lean_object* v_xs_x27_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1865_; 
v_v_1855_ = lean_array_fget(v_tail_1836_, v___x_1849_);
v___x_1856_ = lean_box(0);
v_xs_x27_1857_ = lean_array_fset(v_tail_1836_, v___x_1849_, v___x_1856_);
v___x_1858_ = lean_unsigned_to_nat(32u);
v___x_1859_ = lean_mk_empty_array_with_capacity(v___x_1858_);
lean_dec_ref(v___x_1859_);
v___x_1860_ = lean_unsigned_to_nat(0u);
v___x_1861_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1);
v___x_1862_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(v___x_1832_, v_v_1855_, v___x_1861_, v___x_1860_);
lean_dec(v_v_1855_);
v___x_1863_ = lean_array_fset(v_xs_x27_1857_, v___x_1849_, v___x_1862_);
lean_dec(v___x_1849_);
if (v_isShared_1842_ == 0)
{
lean_ctor_set(v___x_1841_, 1, v___x_1863_);
v___x_1865_ = v___x_1841_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_root_1835_);
lean_ctor_set(v_reuseFailAlloc_1866_, 1, v___x_1863_);
lean_ctor_set(v_reuseFailAlloc_1866_, 2, v_size_1837_);
lean_ctor_set(v_reuseFailAlloc_1866_, 3, v_tailOff_1839_);
lean_ctor_set_usize(v_reuseFailAlloc_1866_, 4, v_shift_1838_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1___boxed(lean_object* v___x_1868_, lean_object* v_t_1869_, lean_object* v_i_1870_){
_start:
{
lean_object* v_res_1871_; 
v_res_1871_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1(v___x_1868_, v_t_1869_, v_i_1870_);
lean_dec(v_i_1870_);
lean_dec_ref(v___x_1868_);
return v_res_1871_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0(lean_object* v_p_1872_, lean_object* v_x_1873_, lean_object* v_s_1874_){
_start:
{
lean_object* v_vars_1875_; lean_object* v_varMap_1876_; lean_object* v_varsHistory_1877_; lean_object* v_natToIntMap_1878_; lean_object* v_natDef_1879_; lean_object* v_dvds_1880_; lean_object* v_lowers_1881_; lean_object* v_uppers_1882_; lean_object* v_diseqs_1883_; lean_object* v_elimEqs_1884_; lean_object* v_elimStack_1885_; lean_object* v_occurs_1886_; lean_object* v_assignment_1887_; lean_object* v_nextCnstrId_1888_; uint8_t v_caseSplits_1889_; lean_object* v_steps_1890_; lean_object* v_conflict_x3f_1891_; lean_object* v_diseqSplits_1892_; lean_object* v_divMod_1893_; uint8_t v_usedCommRing_1894_; lean_object* v_nonlinearOccs_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1903_; 
v_vars_1875_ = lean_ctor_get(v_s_1874_, 0);
v_varMap_1876_ = lean_ctor_get(v_s_1874_, 1);
v_varsHistory_1877_ = lean_ctor_get(v_s_1874_, 2);
v_natToIntMap_1878_ = lean_ctor_get(v_s_1874_, 3);
v_natDef_1879_ = lean_ctor_get(v_s_1874_, 4);
v_dvds_1880_ = lean_ctor_get(v_s_1874_, 5);
v_lowers_1881_ = lean_ctor_get(v_s_1874_, 6);
v_uppers_1882_ = lean_ctor_get(v_s_1874_, 7);
v_diseqs_1883_ = lean_ctor_get(v_s_1874_, 8);
v_elimEqs_1884_ = lean_ctor_get(v_s_1874_, 9);
v_elimStack_1885_ = lean_ctor_get(v_s_1874_, 10);
v_occurs_1886_ = lean_ctor_get(v_s_1874_, 11);
v_assignment_1887_ = lean_ctor_get(v_s_1874_, 12);
v_nextCnstrId_1888_ = lean_ctor_get(v_s_1874_, 13);
v_caseSplits_1889_ = lean_ctor_get_uint8(v_s_1874_, sizeof(void*)*19);
v_steps_1890_ = lean_ctor_get(v_s_1874_, 14);
v_conflict_x3f_1891_ = lean_ctor_get(v_s_1874_, 15);
v_diseqSplits_1892_ = lean_ctor_get(v_s_1874_, 16);
v_divMod_1893_ = lean_ctor_get(v_s_1874_, 17);
v_usedCommRing_1894_ = lean_ctor_get_uint8(v_s_1874_, sizeof(void*)*19 + 1);
v_nonlinearOccs_1895_ = lean_ctor_get(v_s_1874_, 18);
v_isSharedCheck_1903_ = !lean_is_exclusive(v_s_1874_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1897_ = v_s_1874_;
v_isShared_1898_ = v_isSharedCheck_1903_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_nonlinearOccs_1895_);
lean_inc(v_divMod_1893_);
lean_inc(v_diseqSplits_1892_);
lean_inc(v_conflict_x3f_1891_);
lean_inc(v_steps_1890_);
lean_inc(v_nextCnstrId_1888_);
lean_inc(v_assignment_1887_);
lean_inc(v_occurs_1886_);
lean_inc(v_elimStack_1885_);
lean_inc(v_elimEqs_1884_);
lean_inc(v_diseqs_1883_);
lean_inc(v_uppers_1882_);
lean_inc(v_lowers_1881_);
lean_inc(v_dvds_1880_);
lean_inc(v_natDef_1879_);
lean_inc(v_natToIntMap_1878_);
lean_inc(v_varsHistory_1877_);
lean_inc(v_varMap_1876_);
lean_inc(v_vars_1875_);
lean_dec(v_s_1874_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1903_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1899_; lean_object* v___x_1901_; 
v___x_1899_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1(v_p_1872_, v_diseqs_1883_, v_x_1873_);
if (v_isShared_1898_ == 0)
{
lean_ctor_set(v___x_1897_, 8, v___x_1899_);
v___x_1901_ = v___x_1897_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_vars_1875_);
lean_ctor_set(v_reuseFailAlloc_1902_, 1, v_varMap_1876_);
lean_ctor_set(v_reuseFailAlloc_1902_, 2, v_varsHistory_1877_);
lean_ctor_set(v_reuseFailAlloc_1902_, 3, v_natToIntMap_1878_);
lean_ctor_set(v_reuseFailAlloc_1902_, 4, v_natDef_1879_);
lean_ctor_set(v_reuseFailAlloc_1902_, 5, v_dvds_1880_);
lean_ctor_set(v_reuseFailAlloc_1902_, 6, v_lowers_1881_);
lean_ctor_set(v_reuseFailAlloc_1902_, 7, v_uppers_1882_);
lean_ctor_set(v_reuseFailAlloc_1902_, 8, v___x_1899_);
lean_ctor_set(v_reuseFailAlloc_1902_, 9, v_elimEqs_1884_);
lean_ctor_set(v_reuseFailAlloc_1902_, 10, v_elimStack_1885_);
lean_ctor_set(v_reuseFailAlloc_1902_, 11, v_occurs_1886_);
lean_ctor_set(v_reuseFailAlloc_1902_, 12, v_assignment_1887_);
lean_ctor_set(v_reuseFailAlloc_1902_, 13, v_nextCnstrId_1888_);
lean_ctor_set(v_reuseFailAlloc_1902_, 14, v_steps_1890_);
lean_ctor_set(v_reuseFailAlloc_1902_, 15, v_conflict_x3f_1891_);
lean_ctor_set(v_reuseFailAlloc_1902_, 16, v_diseqSplits_1892_);
lean_ctor_set(v_reuseFailAlloc_1902_, 17, v_divMod_1893_);
lean_ctor_set(v_reuseFailAlloc_1902_, 18, v_nonlinearOccs_1895_);
lean_ctor_set_uint8(v_reuseFailAlloc_1902_, sizeof(void*)*19, v_caseSplits_1889_);
lean_ctor_set_uint8(v_reuseFailAlloc_1902_, sizeof(void*)*19 + 1, v_usedCommRing_1894_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed(lean_object* v_p_1904_, lean_object* v_x_1905_, lean_object* v_s_1906_){
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0(v_p_1904_, v_x_1905_, v_s_1906_);
lean_dec(v_x_1905_);
lean_dec_ref(v_p_1904_);
return v_res_1907_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2(void){
_start:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1914_ = lean_unsigned_to_nat(1u);
v___x_1915_ = lean_nat_to_int(v___x_1914_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(lean_object* v_c_1916_, lean_object* v_x_1917_, lean_object* v_as_1918_, size_t v_sz_1919_, size_t v_i_1920_, lean_object* v_b_1921_, lean_object* v___y_1922_){
_start:
{
uint8_t v___x_1924_; 
v___x_1924_ = lean_usize_dec_lt(v_i_1920_, v_sz_1919_);
if (v___x_1924_ == 0)
{
lean_object* v___x_1925_; 
lean_dec(v_x_1917_);
lean_dec_ref(v_c_1916_);
v___x_1925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1925_, 0, v_b_1921_);
return v___x_1925_;
}
else
{
lean_object* v_snd_1926_; lean_object* v___x_1928_; uint8_t v_isShared_1929_; uint8_t v_isSharedCheck_1972_; 
v_snd_1926_ = lean_ctor_get(v_b_1921_, 1);
v_isSharedCheck_1972_ = !lean_is_exclusive(v_b_1921_);
if (v_isSharedCheck_1972_ == 0)
{
lean_object* v_unused_1973_; 
v_unused_1973_ = lean_ctor_get(v_b_1921_, 0);
lean_dec(v_unused_1973_);
v___x_1928_ = v_b_1921_;
v_isShared_1929_ = v_isSharedCheck_1972_;
goto v_resetjp_1927_;
}
else
{
lean_inc(v_snd_1926_);
lean_dec(v_b_1921_);
v___x_1928_ = lean_box(0);
v_isShared_1929_ = v_isSharedCheck_1972_;
goto v_resetjp_1927_;
}
v_resetjp_1927_:
{
lean_object* v_p_1930_; lean_object* v_a_1931_; lean_object* v_p_1932_; lean_object* v___x_1933_; lean_object* v___f_1934_; uint8_t v___y_1936_; uint8_t v___x_1970_; 
v_p_1930_ = lean_ctor_get(v_c_1916_, 0);
v_a_1931_ = lean_array_uget_borrowed(v_as_1918_, v_i_1920_);
v_p_1932_ = lean_ctor_get(v_a_1931_, 0);
v___x_1933_ = lean_box(0);
lean_inc(v_x_1917_);
lean_inc_ref(v_p_1932_);
v___f_1934_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1934_, 0, v_p_1932_);
lean_closure_set(v___f_1934_, 1, v_x_1917_);
v___x_1970_ = l_Int_Internal_Linear_instBEqPoly_beq(v_p_1930_, v_p_1932_);
if (v___x_1970_ == 0)
{
uint8_t v___x_1971_; 
v___x_1971_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_1930_, v_p_1932_);
v___y_1936_ = v___x_1971_;
goto v___jp_1935_;
}
else
{
v___y_1936_ = v___x_1970_;
goto v___jp_1935_;
}
v___jp_1935_:
{
if (v___y_1936_ == 0)
{
lean_object* v___x_1937_; size_t v___x_1938_; size_t v___x_1939_; 
lean_dec_ref(v___f_1934_);
lean_del_object(v___x_1928_);
lean_dec(v_snd_1926_);
v___x_1937_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__1));
v___x_1938_ = ((size_t)1ULL);
v___x_1939_ = lean_usize_add(v_i_1920_, v___x_1938_);
v_i_1920_ = v___x_1939_;
v_b_1921_ = v___x_1937_;
goto _start;
}
else
{
lean_object* v___x_1941_; lean_object* v___x_1942_; 
lean_dec(v_x_1917_);
v___x_1941_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_1942_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1941_, v___f_1934_, v___y_1922_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1960_; 
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1960_ == 0)
{
lean_object* v_unused_1961_; 
v_unused_1961_ = lean_ctor_get(v___x_1942_, 0);
lean_dec(v_unused_1961_);
v___x_1944_ = v___x_1942_;
v_isShared_1945_ = v_isSharedCheck_1960_;
goto v_resetjp_1943_;
}
else
{
lean_dec(v___x_1942_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1960_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1953_; 
v___x_1946_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
lean_inc_ref(v_p_1930_);
v___x_1947_ = l_Int_Internal_Linear_Poly_addConst(v_p_1930_, v___x_1946_);
lean_inc(v_a_1931_);
v___x_1948_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_1948_, 0, v_c_1916_);
lean_ctor_set(v___x_1948_, 1, v_a_1931_);
v___x_1949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1947_);
lean_ctor_set(v___x_1949_, 1, v___x_1948_);
v___x_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1949_);
v___x_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1950_);
if (v_isShared_1929_ == 0)
{
lean_ctor_set(v___x_1928_, 1, v___x_1933_);
lean_ctor_set(v___x_1928_, 0, v___x_1951_);
v___x_1953_ = v___x_1928_;
goto v_reusejp_1952_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v___x_1951_);
lean_ctor_set(v_reuseFailAlloc_1959_, 1, v___x_1933_);
v___x_1953_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1952_;
}
v_reusejp_1952_:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1957_; 
v___x_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1953_);
v___x_1955_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1954_);
lean_ctor_set(v___x_1955_, 1, v_snd_1926_);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 0, v___x_1955_);
v___x_1957_ = v___x_1944_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1955_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
else
{
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1969_; 
lean_del_object(v___x_1928_);
lean_dec(v_snd_1926_);
lean_dec_ref(v_c_1916_);
v_a_1962_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1964_ = v___x_1942_;
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1942_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1967_; 
if (v_isShared_1965_ == 0)
{
v___x_1967_ = v___x_1964_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_a_1962_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___boxed(lean_object* v_c_1974_, lean_object* v_x_1975_, lean_object* v_as_1976_, lean_object* v_sz_1977_, lean_object* v_i_1978_, lean_object* v_b_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_){
_start:
{
size_t v_sz_boxed_1982_; size_t v_i_boxed_1983_; lean_object* v_res_1984_; 
v_sz_boxed_1982_ = lean_unbox_usize(v_sz_1977_);
lean_dec(v_sz_1977_);
v_i_boxed_1983_ = lean_unbox_usize(v_i_1978_);
lean_dec(v_i_1978_);
v_res_1984_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(v_c_1974_, v_x_1975_, v_as_1976_, v_sz_boxed_1982_, v_i_boxed_1983_, v_b_1979_, v___y_1980_);
lean_dec(v___y_1980_);
lean_dec_ref(v_as_1976_);
return v_res_1984_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7(lean_object* v_c_1991_, lean_object* v_x_1992_, lean_object* v_as_1993_, size_t v_sz_1994_, size_t v_i_1995_, lean_object* v_b_1996_, lean_object* v___y_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
uint8_t v___x_2008_; 
v___x_2008_ = lean_usize_dec_lt(v_i_1995_, v_sz_1994_);
if (v___x_2008_ == 0)
{
lean_object* v___x_2009_; 
lean_dec(v_x_1992_);
lean_dec_ref(v_c_1991_);
v___x_2009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2009_, 0, v_b_1996_);
return v___x_2009_;
}
else
{
lean_object* v_snd_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2056_; 
v_snd_2010_ = lean_ctor_get(v_b_1996_, 1);
v_isSharedCheck_2056_ = !lean_is_exclusive(v_b_1996_);
if (v_isSharedCheck_2056_ == 0)
{
lean_object* v_unused_2057_; 
v_unused_2057_ = lean_ctor_get(v_b_1996_, 0);
lean_dec(v_unused_2057_);
v___x_2012_ = v_b_1996_;
v_isShared_2013_ = v_isSharedCheck_2056_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_snd_2010_);
lean_dec(v_b_1996_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2056_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v_p_2014_; lean_object* v_a_2015_; lean_object* v_p_2016_; lean_object* v___x_2017_; lean_object* v___f_2018_; uint8_t v___y_2020_; uint8_t v___x_2054_; 
v_p_2014_ = lean_ctor_get(v_c_1991_, 0);
v_a_2015_ = lean_array_uget_borrowed(v_as_1993_, v_i_1995_);
v_p_2016_ = lean_ctor_get(v_a_2015_, 0);
v___x_2017_ = lean_box(0);
lean_inc(v_x_1992_);
lean_inc_ref(v_p_2016_);
v___f_2018_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2018_, 0, v_p_2016_);
lean_closure_set(v___f_2018_, 1, v_x_1992_);
v___x_2054_ = l_Int_Internal_Linear_instBEqPoly_beq(v_p_2014_, v_p_2016_);
if (v___x_2054_ == 0)
{
uint8_t v___x_2055_; 
v___x_2055_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_2014_, v_p_2016_);
v___y_2020_ = v___x_2055_;
goto v___jp_2019_;
}
else
{
v___y_2020_ = v___x_2054_;
goto v___jp_2019_;
}
v___jp_2019_:
{
if (v___y_2020_ == 0)
{
lean_object* v___x_2021_; size_t v___x_2022_; size_t v___x_2023_; lean_object* v___x_2024_; 
lean_dec_ref(v___f_2018_);
lean_del_object(v___x_2012_);
lean_dec(v_snd_2010_);
v___x_2021_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___closed__1));
v___x_2022_ = ((size_t)1ULL);
v___x_2023_ = lean_usize_add(v_i_1995_, v___x_2022_);
v___x_2024_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(v_c_1991_, v_x_1992_, v_as_1993_, v_sz_1994_, v___x_2023_, v___x_2021_, v___y_1997_);
return v___x_2024_;
}
else
{
lean_object* v___x_2025_; lean_object* v___x_2026_; 
lean_dec(v_x_1992_);
v___x_2025_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2026_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2025_, v___f_2018_, v___y_1997_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2044_; 
v_isSharedCheck_2044_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2044_ == 0)
{
lean_object* v_unused_2045_; 
v_unused_2045_ = lean_ctor_get(v___x_2026_, 0);
lean_dec(v_unused_2045_);
v___x_2028_ = v___x_2026_;
v_isShared_2029_ = v_isSharedCheck_2044_;
goto v_resetjp_2027_;
}
else
{
lean_dec(v___x_2026_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2044_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2037_; 
v___x_2030_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
lean_inc_ref(v_p_2014_);
v___x_2031_ = l_Int_Internal_Linear_Poly_addConst(v_p_2014_, v___x_2030_);
lean_inc(v_a_2015_);
v___x_2032_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_2032_, 0, v_c_1991_);
lean_ctor_set(v___x_2032_, 1, v_a_2015_);
v___x_2033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2031_);
lean_ctor_set(v___x_2033_, 1, v___x_2032_);
v___x_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2033_);
v___x_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2034_);
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 1, v___x_2017_);
lean_ctor_set(v___x_2012_, 0, v___x_2035_);
v___x_2037_ = v___x_2012_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2035_);
lean_ctor_set(v_reuseFailAlloc_2043_, 1, v___x_2017_);
v___x_2037_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2041_; 
v___x_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2037_);
v___x_2039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2039_, 0, v___x_2038_);
lean_ctor_set(v___x_2039_, 1, v_snd_2010_);
if (v_isShared_2029_ == 0)
{
lean_ctor_set(v___x_2028_, 0, v___x_2039_);
v___x_2041_ = v___x_2028_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v___x_2039_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
}
}
else
{
lean_object* v_a_2046_; lean_object* v___x_2048_; uint8_t v_isShared_2049_; uint8_t v_isSharedCheck_2053_; 
lean_del_object(v___x_2012_);
lean_dec(v_snd_2010_);
lean_dec_ref(v_c_1991_);
v_a_2046_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2053_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2053_ == 0)
{
v___x_2048_ = v___x_2026_;
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
else
{
lean_inc(v_a_2046_);
lean_dec(v___x_2026_);
v___x_2048_ = lean_box(0);
v_isShared_2049_ = v_isSharedCheck_2053_;
goto v_resetjp_2047_;
}
v_resetjp_2047_:
{
lean_object* v___x_2051_; 
if (v_isShared_2049_ == 0)
{
v___x_2051_ = v___x_2048_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v_a_2046_);
v___x_2051_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
return v___x_2051_;
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
lean_object* v_c_2058_ = _args[0];
lean_object* v_x_2059_ = _args[1];
lean_object* v_as_2060_ = _args[2];
lean_object* v_sz_2061_ = _args[3];
lean_object* v_i_2062_ = _args[4];
lean_object* v_b_2063_ = _args[5];
lean_object* v___y_2064_ = _args[6];
lean_object* v___y_2065_ = _args[7];
lean_object* v___y_2066_ = _args[8];
lean_object* v___y_2067_ = _args[9];
lean_object* v___y_2068_ = _args[10];
lean_object* v___y_2069_ = _args[11];
lean_object* v___y_2070_ = _args[12];
lean_object* v___y_2071_ = _args[13];
lean_object* v___y_2072_ = _args[14];
lean_object* v___y_2073_ = _args[15];
lean_object* v___y_2074_ = _args[16];
_start:
{
size_t v_sz_boxed_2075_; size_t v_i_boxed_2076_; lean_object* v_res_2077_; 
v_sz_boxed_2075_ = lean_unbox_usize(v_sz_2061_);
lean_dec(v_sz_2061_);
v_i_boxed_2076_ = lean_unbox_usize(v_i_2062_);
lean_dec(v_i_2062_);
v_res_2077_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7(v_c_2058_, v_x_2059_, v_as_2060_, v_sz_boxed_2075_, v_i_boxed_2076_, v_b_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
lean_dec(v___y_2073_);
lean_dec_ref(v___y_2072_);
lean_dec(v___y_2071_);
lean_dec_ref(v___y_2070_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2066_);
lean_dec(v___y_2065_);
lean_dec(v___y_2064_);
lean_dec_ref(v_as_2060_);
return v_res_2077_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(lean_object* v_c_2084_, lean_object* v_x_2085_, lean_object* v_as_2086_, size_t v_sz_2087_, size_t v_i_2088_, lean_object* v_b_2089_, lean_object* v___y_2090_){
_start:
{
uint8_t v___x_2092_; 
v___x_2092_ = lean_usize_dec_lt(v_i_2088_, v_sz_2087_);
if (v___x_2092_ == 0)
{
lean_object* v___x_2093_; 
lean_dec(v_x_2085_);
lean_dec_ref(v_c_2084_);
v___x_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2093_, 0, v_b_2089_);
return v___x_2093_;
}
else
{
lean_object* v_snd_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2141_; 
v_snd_2094_ = lean_ctor_get(v_b_2089_, 1);
v_isSharedCheck_2141_ = !lean_is_exclusive(v_b_2089_);
if (v_isSharedCheck_2141_ == 0)
{
lean_object* v_unused_2142_; 
v_unused_2142_ = lean_ctor_get(v_b_2089_, 0);
lean_dec(v_unused_2142_);
v___x_2096_ = v_b_2089_;
v_isShared_2097_ = v_isSharedCheck_2141_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_snd_2094_);
lean_dec(v_b_2089_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2141_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v_p_2098_; lean_object* v_a_2099_; lean_object* v_p_2100_; lean_object* v___x_2101_; lean_object* v___f_2102_; uint8_t v___y_2104_; uint8_t v___x_2139_; 
v_p_2098_ = lean_ctor_get(v_c_2084_, 0);
v_a_2099_ = lean_array_uget_borrowed(v_as_2086_, v_i_2088_);
v_p_2100_ = lean_ctor_get(v_a_2099_, 0);
v___x_2101_ = lean_box(0);
lean_inc(v_x_2085_);
lean_inc_ref(v_p_2100_);
v___f_2102_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2102_, 0, v_p_2100_);
lean_closure_set(v___f_2102_, 1, v_x_2085_);
v___x_2139_ = l_Int_Internal_Linear_instBEqPoly_beq(v_p_2098_, v_p_2100_);
if (v___x_2139_ == 0)
{
uint8_t v___x_2140_; 
v___x_2140_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_2098_, v_p_2100_);
v___y_2104_ = v___x_2140_;
goto v___jp_2103_;
}
else
{
v___y_2104_ = v___x_2139_;
goto v___jp_2103_;
}
v___jp_2103_:
{
if (v___y_2104_ == 0)
{
lean_object* v___x_2105_; size_t v___x_2106_; size_t v___x_2107_; 
lean_dec_ref(v___f_2102_);
lean_del_object(v___x_2096_);
lean_dec(v_snd_2094_);
v___x_2105_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg___closed__1));
v___x_2106_ = ((size_t)1ULL);
v___x_2107_ = lean_usize_add(v_i_2088_, v___x_2106_);
v_i_2088_ = v___x_2107_;
v_b_2089_ = v___x_2105_;
goto _start;
}
else
{
lean_object* v___x_2109_; lean_object* v___x_2110_; 
lean_dec(v_x_2085_);
v___x_2109_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2110_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2109_, v___f_2102_, v___y_2090_);
if (lean_obj_tag(v___x_2110_) == 0)
{
lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2129_; 
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2129_ == 0)
{
lean_object* v_unused_2130_; 
v_unused_2130_ = lean_ctor_get(v___x_2110_, 0);
lean_dec(v_unused_2130_);
v___x_2112_ = v___x_2110_;
v_isShared_2113_ = v_isSharedCheck_2129_;
goto v_resetjp_2111_;
}
else
{
lean_dec(v___x_2110_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2129_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2121_; 
v___x_2114_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
lean_inc_ref(v_p_2098_);
v___x_2115_ = l_Int_Internal_Linear_Poly_addConst(v_p_2098_, v___x_2114_);
lean_inc(v_a_2099_);
v___x_2116_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_2116_, 0, v_c_2084_);
lean_ctor_set(v___x_2116_, 1, v_a_2099_);
v___x_2117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2115_);
lean_ctor_set(v___x_2117_, 1, v___x_2116_);
v___x_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
v___x_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2118_);
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 1, v___x_2101_);
lean_ctor_set(v___x_2096_, 0, v___x_2119_);
v___x_2121_ = v___x_2096_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v___x_2119_);
lean_ctor_set(v_reuseFailAlloc_2128_, 1, v___x_2101_);
v___x_2121_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2126_; 
v___x_2122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2121_);
v___x_2123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2122_);
v___x_2124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2123_);
lean_ctor_set(v___x_2124_, 1, v_snd_2094_);
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 0, v___x_2124_);
v___x_2126_ = v___x_2112_;
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
lean_del_object(v___x_2096_);
lean_dec(v_snd_2094_);
lean_dec_ref(v_c_2084_);
v_a_2131_ = lean_ctor_get(v___x_2110_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2133_ = v___x_2110_;
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_a_2131_);
lean_dec(v___x_2110_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg___boxed(lean_object* v_c_2143_, lean_object* v_x_2144_, lean_object* v_as_2145_, lean_object* v_sz_2146_, lean_object* v_i_2147_, lean_object* v_b_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
size_t v_sz_boxed_2151_; size_t v_i_boxed_2152_; lean_object* v_res_2153_; 
v_sz_boxed_2151_ = lean_unbox_usize(v_sz_2146_);
lean_dec(v_sz_2146_);
v_i_boxed_2152_ = lean_unbox_usize(v_i_2147_);
lean_dec(v_i_2147_);
v_res_2153_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(v_c_2143_, v_x_2144_, v_as_2145_, v_sz_boxed_2151_, v_i_boxed_2152_, v_b_2148_, v___y_2149_);
lean_dec(v___y_2149_);
lean_dec_ref(v_as_2145_);
return v_res_2153_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9(lean_object* v_c_2157_, lean_object* v_x_2158_, lean_object* v_as_2159_, size_t v_sz_2160_, size_t v_i_2161_, lean_object* v_b_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_){
_start:
{
uint8_t v___x_2174_; 
v___x_2174_ = lean_usize_dec_lt(v_i_2161_, v_sz_2160_);
if (v___x_2174_ == 0)
{
lean_object* v___x_2175_; 
lean_dec(v_x_2158_);
lean_dec_ref(v_c_2157_);
v___x_2175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2175_, 0, v_b_2162_);
return v___x_2175_;
}
else
{
lean_object* v_snd_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2223_; 
v_snd_2176_ = lean_ctor_get(v_b_2162_, 1);
v_isSharedCheck_2223_ = !lean_is_exclusive(v_b_2162_);
if (v_isSharedCheck_2223_ == 0)
{
lean_object* v_unused_2224_; 
v_unused_2224_ = lean_ctor_get(v_b_2162_, 0);
lean_dec(v_unused_2224_);
v___x_2178_ = v_b_2162_;
v_isShared_2179_ = v_isSharedCheck_2223_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_snd_2176_);
lean_dec(v_b_2162_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2223_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v_p_2180_; lean_object* v_a_2181_; lean_object* v_p_2182_; lean_object* v___x_2183_; lean_object* v___f_2184_; uint8_t v___y_2186_; uint8_t v___x_2221_; 
v_p_2180_ = lean_ctor_get(v_c_2157_, 0);
v_a_2181_ = lean_array_uget_borrowed(v_as_2159_, v_i_2161_);
v_p_2182_ = lean_ctor_get(v_a_2181_, 0);
v___x_2183_ = lean_box(0);
lean_inc(v_x_2158_);
lean_inc_ref(v_p_2182_);
v___f_2184_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2184_, 0, v_p_2182_);
lean_closure_set(v___f_2184_, 1, v_x_2158_);
v___x_2221_ = l_Int_Internal_Linear_instBEqPoly_beq(v_p_2180_, v_p_2182_);
if (v___x_2221_ == 0)
{
uint8_t v___x_2222_; 
v___x_2222_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_2180_, v_p_2182_);
v___y_2186_ = v___x_2222_;
goto v___jp_2185_;
}
else
{
v___y_2186_ = v___x_2221_;
goto v___jp_2185_;
}
v___jp_2185_:
{
if (v___y_2186_ == 0)
{
lean_object* v___x_2187_; size_t v___x_2188_; size_t v___x_2189_; lean_object* v___x_2190_; 
lean_dec_ref(v___f_2184_);
lean_del_object(v___x_2178_);
lean_dec(v_snd_2176_);
v___x_2187_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9___closed__0));
v___x_2188_ = ((size_t)1ULL);
v___x_2189_ = lean_usize_add(v_i_2161_, v___x_2188_);
v___x_2190_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(v_c_2157_, v_x_2158_, v_as_2159_, v_sz_2160_, v___x_2189_, v___x_2187_, v___y_2163_);
return v___x_2190_;
}
else
{
lean_object* v___x_2191_; lean_object* v___x_2192_; 
lean_dec(v_x_2158_);
v___x_2191_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2192_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2191_, v___f_2184_, v___y_2163_);
if (lean_obj_tag(v___x_2192_) == 0)
{
lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2211_; 
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2211_ == 0)
{
lean_object* v_unused_2212_; 
v_unused_2212_ = lean_ctor_get(v___x_2192_, 0);
lean_dec(v_unused_2212_);
v___x_2194_ = v___x_2192_;
v_isShared_2195_ = v_isSharedCheck_2211_;
goto v_resetjp_2193_;
}
else
{
lean_dec(v___x_2192_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2211_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2203_; 
v___x_2196_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
lean_inc_ref(v_p_2180_);
v___x_2197_ = l_Int_Internal_Linear_Poly_addConst(v_p_2180_, v___x_2196_);
lean_inc(v_a_2181_);
v___x_2198_ = lean_alloc_ctor(11, 2, 0);
lean_ctor_set(v___x_2198_, 0, v_c_2157_);
lean_ctor_set(v___x_2198_, 1, v_a_2181_);
v___x_2199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2197_);
lean_ctor_set(v___x_2199_, 1, v___x_2198_);
v___x_2200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2199_);
v___x_2201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2200_);
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 1, v___x_2183_);
lean_ctor_set(v___x_2178_, 0, v___x_2201_);
v___x_2203_ = v___x_2178_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v___x_2201_);
lean_ctor_set(v_reuseFailAlloc_2210_, 1, v___x_2183_);
v___x_2203_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2208_; 
v___x_2204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2203_);
v___x_2205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2204_);
v___x_2206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2205_);
lean_ctor_set(v___x_2206_, 1, v_snd_2176_);
if (v_isShared_2195_ == 0)
{
lean_ctor_set(v___x_2194_, 0, v___x_2206_);
v___x_2208_ = v___x_2194_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v___x_2206_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
}
}
else
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
lean_del_object(v___x_2178_);
lean_dec(v_snd_2176_);
lean_dec_ref(v_c_2157_);
v_a_2213_ = lean_ctor_get(v___x_2192_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2192_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2215_ = v___x_2192_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2192_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2213_);
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
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9___boxed(lean_object** _args){
lean_object* v_c_2225_ = _args[0];
lean_object* v_x_2226_ = _args[1];
lean_object* v_as_2227_ = _args[2];
lean_object* v_sz_2228_ = _args[3];
lean_object* v_i_2229_ = _args[4];
lean_object* v_b_2230_ = _args[5];
lean_object* v___y_2231_ = _args[6];
lean_object* v___y_2232_ = _args[7];
lean_object* v___y_2233_ = _args[8];
lean_object* v___y_2234_ = _args[9];
lean_object* v___y_2235_ = _args[10];
lean_object* v___y_2236_ = _args[11];
lean_object* v___y_2237_ = _args[12];
lean_object* v___y_2238_ = _args[13];
lean_object* v___y_2239_ = _args[14];
lean_object* v___y_2240_ = _args[15];
lean_object* v___y_2241_ = _args[16];
_start:
{
size_t v_sz_boxed_2242_; size_t v_i_boxed_2243_; lean_object* v_res_2244_; 
v_sz_boxed_2242_ = lean_unbox_usize(v_sz_2228_);
lean_dec(v_sz_2228_);
v_i_boxed_2243_ = lean_unbox_usize(v_i_2229_);
lean_dec(v_i_2229_);
v_res_2244_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9(v_c_2225_, v_x_2226_, v_as_2227_, v_sz_boxed_2242_, v_i_boxed_2243_, v_b_2230_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
lean_dec(v___y_2234_);
lean_dec_ref(v___y_2233_);
lean_dec(v___y_2232_);
lean_dec(v___y_2231_);
lean_dec_ref(v_as_2227_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(lean_object* v_init_2245_, lean_object* v_c_2246_, lean_object* v_x_2247_, lean_object* v_n_2248_, lean_object* v_b_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_){
_start:
{
if (lean_obj_tag(v_n_2248_) == 0)
{
lean_object* v_cs_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; size_t v_sz_2264_; size_t v___x_2265_; lean_object* v___x_2266_; 
v_cs_2261_ = lean_ctor_get(v_n_2248_, 0);
v___x_2262_ = lean_box(0);
v___x_2263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2263_, 0, v___x_2262_);
lean_ctor_set(v___x_2263_, 1, v_b_2249_);
v_sz_2264_ = lean_array_size(v_cs_2261_);
v___x_2265_ = ((size_t)0ULL);
v___x_2266_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8(v_init_2245_, v_c_2246_, v_x_2247_, v_cs_2261_, v_sz_2264_, v___x_2265_, v___x_2263_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_object* v_a_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2281_; 
v_a_2267_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2269_ = v___x_2266_;
v_isShared_2270_ = v_isSharedCheck_2281_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_a_2267_);
lean_dec(v___x_2266_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2281_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v_fst_2271_; 
v_fst_2271_ = lean_ctor_get(v_a_2267_, 0);
if (lean_obj_tag(v_fst_2271_) == 0)
{
lean_object* v_snd_2272_; lean_object* v___x_2273_; lean_object* v___x_2275_; 
v_snd_2272_ = lean_ctor_get(v_a_2267_, 1);
lean_inc(v_snd_2272_);
lean_dec(v_a_2267_);
v___x_2273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2273_, 0, v_snd_2272_);
if (v_isShared_2270_ == 0)
{
lean_ctor_set(v___x_2269_, 0, v___x_2273_);
v___x_2275_ = v___x_2269_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v___x_2273_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
else
{
lean_object* v_val_2277_; lean_object* v___x_2279_; 
lean_inc_ref(v_fst_2271_);
lean_dec(v_a_2267_);
v_val_2277_ = lean_ctor_get(v_fst_2271_, 0);
lean_inc(v_val_2277_);
lean_dec_ref_known(v_fst_2271_, 1);
if (v_isShared_2270_ == 0)
{
lean_ctor_set(v___x_2269_, 0, v_val_2277_);
v___x_2279_ = v___x_2269_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_val_2277_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
}
}
else
{
lean_object* v_a_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2289_; 
v_a_2282_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2289_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2284_ = v___x_2266_;
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_a_2282_);
lean_dec(v___x_2266_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2287_; 
if (v_isShared_2285_ == 0)
{
v___x_2287_ = v___x_2284_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_a_2282_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
}
else
{
lean_object* v_vs_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; size_t v_sz_2293_; size_t v___x_2294_; lean_object* v___x_2295_; 
v_vs_2290_ = lean_ctor_get(v_n_2248_, 0);
v___x_2291_ = lean_box(0);
v___x_2292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2291_);
lean_ctor_set(v___x_2292_, 1, v_b_2249_);
v_sz_2293_ = lean_array_size(v_vs_2290_);
v___x_2294_ = ((size_t)0ULL);
v___x_2295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9(v_c_2246_, v_x_2247_, v_vs_2290_, v_sz_2293_, v___x_2294_, v___x_2292_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_);
if (lean_obj_tag(v___x_2295_) == 0)
{
lean_object* v_a_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2310_; 
v_a_2296_ = lean_ctor_get(v___x_2295_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2295_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2298_ = v___x_2295_;
v_isShared_2299_ = v_isSharedCheck_2310_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_a_2296_);
lean_dec(v___x_2295_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2310_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v_fst_2300_; 
v_fst_2300_ = lean_ctor_get(v_a_2296_, 0);
if (lean_obj_tag(v_fst_2300_) == 0)
{
lean_object* v_snd_2301_; lean_object* v___x_2302_; lean_object* v___x_2304_; 
v_snd_2301_ = lean_ctor_get(v_a_2296_, 1);
lean_inc(v_snd_2301_);
lean_dec(v_a_2296_);
v___x_2302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2302_, 0, v_snd_2301_);
if (v_isShared_2299_ == 0)
{
lean_ctor_set(v___x_2298_, 0, v___x_2302_);
v___x_2304_ = v___x_2298_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v___x_2302_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
else
{
lean_object* v_val_2306_; lean_object* v___x_2308_; 
lean_inc_ref(v_fst_2300_);
lean_dec(v_a_2296_);
v_val_2306_ = lean_ctor_get(v_fst_2300_, 0);
lean_inc(v_val_2306_);
lean_dec_ref_known(v_fst_2300_, 1);
if (v_isShared_2299_ == 0)
{
lean_ctor_set(v___x_2298_, 0, v_val_2306_);
v___x_2308_ = v___x_2298_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_val_2306_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
}
}
else
{
lean_object* v_a_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2318_; 
v_a_2311_ = lean_ctor_get(v___x_2295_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v___x_2295_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2313_ = v___x_2295_;
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_a_2311_);
lean_dec(v___x_2295_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2318_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2316_; 
if (v_isShared_2314_ == 0)
{
v___x_2316_ = v___x_2313_;
goto v_reusejp_2315_;
}
else
{
lean_object* v_reuseFailAlloc_2317_; 
v_reuseFailAlloc_2317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2317_, 0, v_a_2311_);
v___x_2316_ = v_reuseFailAlloc_2317_;
goto v_reusejp_2315_;
}
v_reusejp_2315_:
{
return v___x_2316_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8(lean_object* v_init_2319_, lean_object* v_c_2320_, lean_object* v_x_2321_, lean_object* v_as_2322_, size_t v_sz_2323_, size_t v_i_2324_, lean_object* v_b_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_){
_start:
{
uint8_t v___x_2337_; 
v___x_2337_ = lean_usize_dec_lt(v_i_2324_, v_sz_2323_);
if (v___x_2337_ == 0)
{
lean_object* v___x_2338_; 
lean_dec(v_x_2321_);
lean_dec_ref(v_c_2320_);
v___x_2338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2338_, 0, v_b_2325_);
return v___x_2338_;
}
else
{
lean_object* v_snd_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2373_; 
v_snd_2339_ = lean_ctor_get(v_b_2325_, 1);
v_isSharedCheck_2373_ = !lean_is_exclusive(v_b_2325_);
if (v_isSharedCheck_2373_ == 0)
{
lean_object* v_unused_2374_; 
v_unused_2374_ = lean_ctor_get(v_b_2325_, 0);
lean_dec(v_unused_2374_);
v___x_2341_ = v_b_2325_;
v_isShared_2342_ = v_isSharedCheck_2373_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_snd_2339_);
lean_dec(v_b_2325_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2373_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v___x_2343_; lean_object* v_a_2344_; lean_object* v___x_2345_; 
v___x_2343_ = lean_box(0);
v_a_2344_ = lean_array_uget_borrowed(v_as_2322_, v_i_2324_);
lean_inc(v_snd_2339_);
lean_inc(v_x_2321_);
lean_inc_ref(v_c_2320_);
v___x_2345_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(v_init_2319_, v_c_2320_, v_x_2321_, v_a_2344_, v_snd_2339_, v___y_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2364_; 
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2348_ = v___x_2345_;
v_isShared_2349_ = v_isSharedCheck_2364_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v___x_2345_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2364_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
if (lean_obj_tag(v_a_2346_) == 0)
{
lean_object* v___x_2350_; lean_object* v___x_2352_; 
lean_dec(v_x_2321_);
lean_dec_ref(v_c_2320_);
v___x_2350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2350_, 0, v_a_2346_);
if (v_isShared_2342_ == 0)
{
lean_ctor_set(v___x_2341_, 0, v___x_2350_);
v___x_2352_ = v___x_2341_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v___x_2350_);
lean_ctor_set(v_reuseFailAlloc_2356_, 1, v_snd_2339_);
v___x_2352_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
lean_object* v___x_2354_; 
if (v_isShared_2349_ == 0)
{
lean_ctor_set(v___x_2348_, 0, v___x_2352_);
v___x_2354_ = v___x_2348_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v___x_2352_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
}
else
{
lean_object* v_a_2357_; lean_object* v___x_2359_; 
lean_del_object(v___x_2348_);
lean_dec(v_snd_2339_);
v_a_2357_ = lean_ctor_get(v_a_2346_, 0);
lean_inc(v_a_2357_);
lean_dec_ref_known(v_a_2346_, 1);
if (v_isShared_2342_ == 0)
{
lean_ctor_set(v___x_2341_, 1, v_a_2357_);
lean_ctor_set(v___x_2341_, 0, v___x_2343_);
v___x_2359_ = v___x_2341_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v___x_2343_);
lean_ctor_set(v_reuseFailAlloc_2363_, 1, v_a_2357_);
v___x_2359_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
size_t v___x_2360_; size_t v___x_2361_; 
v___x_2360_ = ((size_t)1ULL);
v___x_2361_ = lean_usize_add(v_i_2324_, v___x_2360_);
v_i_2324_ = v___x_2361_;
v_b_2325_ = v___x_2359_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2372_; 
lean_del_object(v___x_2341_);
lean_dec(v_snd_2339_);
lean_dec(v_x_2321_);
lean_dec_ref(v_c_2320_);
v_a_2365_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2367_ = v___x_2345_;
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2345_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2370_; 
if (v_isShared_2368_ == 0)
{
v___x_2370_ = v___x_2367_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_a_2365_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8___boxed(lean_object** _args){
lean_object* v_init_2375_ = _args[0];
lean_object* v_c_2376_ = _args[1];
lean_object* v_x_2377_ = _args[2];
lean_object* v_as_2378_ = _args[3];
lean_object* v_sz_2379_ = _args[4];
lean_object* v_i_2380_ = _args[5];
lean_object* v_b_2381_ = _args[6];
lean_object* v___y_2382_ = _args[7];
lean_object* v___y_2383_ = _args[8];
lean_object* v___y_2384_ = _args[9];
lean_object* v___y_2385_ = _args[10];
lean_object* v___y_2386_ = _args[11];
lean_object* v___y_2387_ = _args[12];
lean_object* v___y_2388_ = _args[13];
lean_object* v___y_2389_ = _args[14];
lean_object* v___y_2390_ = _args[15];
lean_object* v___y_2391_ = _args[16];
lean_object* v___y_2392_ = _args[17];
_start:
{
size_t v_sz_boxed_2393_; size_t v_i_boxed_2394_; lean_object* v_res_2395_; 
v_sz_boxed_2393_ = lean_unbox_usize(v_sz_2379_);
lean_dec(v_sz_2379_);
v_i_boxed_2394_ = lean_unbox_usize(v_i_2380_);
lean_dec(v_i_2380_);
v_res_2395_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8(v_init_2375_, v_c_2376_, v_x_2377_, v_as_2378_, v_sz_boxed_2393_, v_i_boxed_2394_, v_b_2381_, v___y_2382_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_);
lean_dec(v___y_2391_);
lean_dec_ref(v___y_2390_);
lean_dec(v___y_2389_);
lean_dec_ref(v___y_2388_);
lean_dec(v___y_2387_);
lean_dec_ref(v___y_2386_);
lean_dec(v___y_2385_);
lean_dec_ref(v___y_2384_);
lean_dec(v___y_2383_);
lean_dec(v___y_2382_);
lean_dec_ref(v_as_2378_);
lean_dec_ref(v_init_2375_);
return v_res_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6___boxed(lean_object* v_init_2396_, lean_object* v_c_2397_, lean_object* v_x_2398_, lean_object* v_n_2399_, lean_object* v_b_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
lean_object* v_res_2412_; 
v_res_2412_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(v_init_2396_, v_c_2397_, v_x_2398_, v_n_2399_, v_b_2400_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec(v___y_2402_);
lean_dec(v___y_2401_);
lean_dec_ref(v_n_2399_);
lean_dec_ref(v_init_2396_);
return v_res_2412_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2(lean_object* v_c_2413_, lean_object* v_x_2414_, lean_object* v_t_2415_, lean_object* v_init_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_){
_start:
{
lean_object* v_root_2428_; lean_object* v_tail_2429_; lean_object* v___x_2430_; 
v_root_2428_ = lean_ctor_get(v_t_2415_, 0);
v_tail_2429_ = lean_ctor_get(v_t_2415_, 1);
lean_inc(v_x_2414_);
lean_inc_ref(v_c_2413_);
lean_inc_ref(v_init_2416_);
v___x_2430_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(v_init_2416_, v_c_2413_, v_x_2414_, v_root_2428_, v_init_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
lean_dec_ref(v_init_2416_);
if (lean_obj_tag(v___x_2430_) == 0)
{
lean_object* v_a_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2467_; 
v_a_2431_ = lean_ctor_get(v___x_2430_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2430_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2433_ = v___x_2430_;
v_isShared_2434_ = v_isSharedCheck_2467_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_a_2431_);
lean_dec(v___x_2430_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2467_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
if (lean_obj_tag(v_a_2431_) == 0)
{
lean_object* v_a_2435_; lean_object* v___x_2437_; 
lean_dec(v_x_2414_);
lean_dec_ref(v_c_2413_);
v_a_2435_ = lean_ctor_get(v_a_2431_, 0);
lean_inc(v_a_2435_);
lean_dec_ref_known(v_a_2431_, 1);
if (v_isShared_2434_ == 0)
{
lean_ctor_set(v___x_2433_, 0, v_a_2435_);
v___x_2437_ = v___x_2433_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_a_2435_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
return v___x_2437_;
}
}
else
{
lean_object* v_a_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; size_t v_sz_2442_; size_t v___x_2443_; lean_object* v___x_2444_; 
lean_del_object(v___x_2433_);
v_a_2439_ = lean_ctor_get(v_a_2431_, 0);
lean_inc(v_a_2439_);
lean_dec_ref_known(v_a_2431_, 1);
v___x_2440_ = lean_box(0);
v___x_2441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2440_);
lean_ctor_set(v___x_2441_, 1, v_a_2439_);
v_sz_2442_ = lean_array_size(v_tail_2429_);
v___x_2443_ = ((size_t)0ULL);
v___x_2444_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7(v_c_2413_, v_x_2414_, v_tail_2429_, v_sz_2442_, v___x_2443_, v___x_2441_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
if (lean_obj_tag(v___x_2444_) == 0)
{
lean_object* v_a_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2458_; 
v_a_2445_ = lean_ctor_get(v___x_2444_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2447_ = v___x_2444_;
v_isShared_2448_ = v_isSharedCheck_2458_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_a_2445_);
lean_dec(v___x_2444_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2458_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v_fst_2449_; 
v_fst_2449_ = lean_ctor_get(v_a_2445_, 0);
if (lean_obj_tag(v_fst_2449_) == 0)
{
lean_object* v_snd_2450_; lean_object* v___x_2452_; 
v_snd_2450_ = lean_ctor_get(v_a_2445_, 1);
lean_inc(v_snd_2450_);
lean_dec(v_a_2445_);
if (v_isShared_2448_ == 0)
{
lean_ctor_set(v___x_2447_, 0, v_snd_2450_);
v___x_2452_ = v___x_2447_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_snd_2450_);
v___x_2452_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
return v___x_2452_;
}
}
else
{
lean_object* v_val_2454_; lean_object* v___x_2456_; 
lean_inc_ref(v_fst_2449_);
lean_dec(v_a_2445_);
v_val_2454_ = lean_ctor_get(v_fst_2449_, 0);
lean_inc(v_val_2454_);
lean_dec_ref_known(v_fst_2449_, 1);
if (v_isShared_2448_ == 0)
{
lean_ctor_set(v___x_2447_, 0, v_val_2454_);
v___x_2456_ = v___x_2447_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2457_; 
v_reuseFailAlloc_2457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2457_, 0, v_val_2454_);
v___x_2456_ = v_reuseFailAlloc_2457_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
return v___x_2456_;
}
}
}
}
else
{
lean_object* v_a_2459_; lean_object* v___x_2461_; uint8_t v_isShared_2462_; uint8_t v_isSharedCheck_2466_; 
v_a_2459_ = lean_ctor_get(v___x_2444_, 0);
v_isSharedCheck_2466_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2466_ == 0)
{
v___x_2461_ = v___x_2444_;
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
else
{
lean_inc(v_a_2459_);
lean_dec(v___x_2444_);
v___x_2461_ = lean_box(0);
v_isShared_2462_ = v_isSharedCheck_2466_;
goto v_resetjp_2460_;
}
v_resetjp_2460_:
{
lean_object* v___x_2464_; 
if (v_isShared_2462_ == 0)
{
v___x_2464_ = v___x_2461_;
goto v_reusejp_2463_;
}
else
{
lean_object* v_reuseFailAlloc_2465_; 
v_reuseFailAlloc_2465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2465_, 0, v_a_2459_);
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
}
}
else
{
lean_object* v_a_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2475_; 
lean_dec(v_x_2414_);
lean_dec_ref(v_c_2413_);
v_a_2468_ = lean_ctor_get(v___x_2430_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2430_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2470_ = v___x_2430_;
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_a_2468_);
lean_dec(v___x_2430_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2473_; 
if (v_isShared_2471_ == 0)
{
v___x_2473_ = v___x_2470_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_a_2468_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2___boxed(lean_object* v_c_2476_, lean_object* v_x_2477_, lean_object* v_t_2478_, lean_object* v_init_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_){
_start:
{
lean_object* v_res_2491_; 
v_res_2491_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2(v_c_2476_, v_x_2477_, v_t_2478_, v_init_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec(v___y_2487_);
lean_dec_ref(v___y_2486_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec(v___y_2481_);
lean_dec(v___y_2480_);
lean_dec_ref(v_t_2478_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(lean_object* v_x_2492_, lean_object* v_c_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_){
_start:
{
lean_object* v___x_2505_; lean_object* v___x_2506_; 
v___x_2505_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0);
v___x_2506_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2494_, v_a_2502_);
if (lean_obj_tag(v___x_2506_) == 0)
{
lean_object* v_a_2507_; lean_object* v___y_2509_; lean_object* v_diseqs_2534_; lean_object* v_size_2535_; uint8_t v___x_2536_; 
v_a_2507_ = lean_ctor_get(v___x_2506_, 0);
lean_inc(v_a_2507_);
lean_dec_ref_known(v___x_2506_, 1);
v_diseqs_2534_ = lean_ctor_get(v_a_2507_, 8);
lean_inc_ref(v_diseqs_2534_);
lean_dec(v_a_2507_);
v_size_2535_ = lean_ctor_get(v_diseqs_2534_, 2);
v___x_2536_ = lean_nat_dec_lt(v_x_2492_, v_size_2535_);
if (v___x_2536_ == 0)
{
lean_object* v___x_2537_; 
lean_dec_ref(v_diseqs_2534_);
v___x_2537_ = l_outOfBounds___redArg(v___x_2505_);
v___y_2509_ = v___x_2537_;
goto v___jp_2508_;
}
else
{
lean_object* v___x_2538_; 
v___x_2538_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2505_, v_diseqs_2534_, v_x_2492_);
lean_dec_ref(v_diseqs_2534_);
v___y_2509_ = v___x_2538_;
goto v___jp_2508_;
}
v___jp_2508_:
{
lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2510_ = lean_box(0);
v___x_2511_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___closed__0));
v___x_2512_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2(v_c_2493_, v_x_2492_, v___y_2509_, v___x_2511_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_);
lean_dec_ref(v___y_2509_);
if (lean_obj_tag(v___x_2512_) == 0)
{
lean_object* v_a_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2525_; 
v_a_2513_ = lean_ctor_get(v___x_2512_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2512_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2515_ = v___x_2512_;
v_isShared_2516_ = v_isSharedCheck_2525_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_a_2513_);
lean_dec(v___x_2512_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2525_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v_fst_2517_; 
v_fst_2517_ = lean_ctor_get(v_a_2513_, 0);
lean_inc(v_fst_2517_);
lean_dec(v_a_2513_);
if (lean_obj_tag(v_fst_2517_) == 0)
{
lean_object* v___x_2519_; 
if (v_isShared_2516_ == 0)
{
lean_ctor_set(v___x_2515_, 0, v___x_2510_);
v___x_2519_ = v___x_2515_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v___x_2510_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
else
{
lean_object* v_val_2521_; lean_object* v___x_2523_; 
v_val_2521_ = lean_ctor_get(v_fst_2517_, 0);
lean_inc(v_val_2521_);
lean_dec_ref_known(v_fst_2517_, 1);
if (v_isShared_2516_ == 0)
{
lean_ctor_set(v___x_2515_, 0, v_val_2521_);
v___x_2523_ = v___x_2515_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_val_2521_);
v___x_2523_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2522_;
}
v_reusejp_2522_:
{
return v___x_2523_;
}
}
}
}
else
{
lean_object* v_a_2526_; lean_object* v___x_2528_; uint8_t v_isShared_2529_; uint8_t v_isSharedCheck_2533_; 
v_a_2526_ = lean_ctor_get(v___x_2512_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v___x_2512_);
if (v_isSharedCheck_2533_ == 0)
{
v___x_2528_ = v___x_2512_;
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
else
{
lean_inc(v_a_2526_);
lean_dec(v___x_2512_);
v___x_2528_ = lean_box(0);
v_isShared_2529_ = v_isSharedCheck_2533_;
goto v_resetjp_2527_;
}
v_resetjp_2527_:
{
lean_object* v___x_2531_; 
if (v_isShared_2529_ == 0)
{
v___x_2531_ = v___x_2528_;
goto v_reusejp_2530_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_a_2526_);
v___x_2531_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2530_;
}
v_reusejp_2530_:
{
return v___x_2531_;
}
}
}
}
}
else
{
lean_object* v_a_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2546_; 
lean_dec_ref(v_c_2493_);
lean_dec(v_x_2492_);
v_a_2539_ = lean_ctor_get(v___x_2506_, 0);
v_isSharedCheck_2546_ = !lean_is_exclusive(v___x_2506_);
if (v_isSharedCheck_2546_ == 0)
{
v___x_2541_ = v___x_2506_;
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_a_2539_);
lean_dec(v___x_2506_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f___boxed(lean_object* v_x_2547_, lean_object* v_c_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_){
_start:
{
lean_object* v_res_2560_; 
v_res_2560_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(v_x_2547_, v_c_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_);
lean_dec(v_a_2558_);
lean_dec_ref(v_a_2557_);
lean_dec(v_a_2556_);
lean_dec_ref(v_a_2555_);
lean_dec(v_a_2554_);
lean_dec_ref(v_a_2553_);
lean_dec(v_a_2552_);
lean_dec_ref(v_a_2551_);
lean_dec(v_a_2550_);
lean_dec(v_a_2549_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11(lean_object* v_c_2561_, lean_object* v_x_2562_, lean_object* v_as_2563_, size_t v_sz_2564_, size_t v_i_2565_, lean_object* v_b_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_){
_start:
{
lean_object* v___x_2578_; 
v___x_2578_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(v_c_2561_, v_x_2562_, v_as_2563_, v_sz_2564_, v_i_2565_, v_b_2566_, v___y_2567_);
return v___x_2578_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___boxed(lean_object** _args){
lean_object* v_c_2579_ = _args[0];
lean_object* v_x_2580_ = _args[1];
lean_object* v_as_2581_ = _args[2];
lean_object* v_sz_2582_ = _args[3];
lean_object* v_i_2583_ = _args[4];
lean_object* v_b_2584_ = _args[5];
lean_object* v___y_2585_ = _args[6];
lean_object* v___y_2586_ = _args[7];
lean_object* v___y_2587_ = _args[8];
lean_object* v___y_2588_ = _args[9];
lean_object* v___y_2589_ = _args[10];
lean_object* v___y_2590_ = _args[11];
lean_object* v___y_2591_ = _args[12];
lean_object* v___y_2592_ = _args[13];
lean_object* v___y_2593_ = _args[14];
lean_object* v___y_2594_ = _args[15];
lean_object* v___y_2595_ = _args[16];
_start:
{
size_t v_sz_boxed_2596_; size_t v_i_boxed_2597_; lean_object* v_res_2598_; 
v_sz_boxed_2596_ = lean_unbox_usize(v_sz_2582_);
lean_dec(v_sz_2582_);
v_i_boxed_2597_ = lean_unbox_usize(v_i_2583_);
lean_dec(v_i_2583_);
v_res_2598_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11(v_c_2579_, v_x_2580_, v_as_2581_, v_sz_boxed_2596_, v_i_boxed_2597_, v_b_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_);
lean_dec(v___y_2594_);
lean_dec_ref(v___y_2593_);
lean_dec(v___y_2592_);
lean_dec_ref(v___y_2591_);
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
lean_dec(v___y_2586_);
lean_dec(v___y_2585_);
lean_dec_ref(v_as_2581_);
return v_res_2598_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10(lean_object* v_c_2599_, lean_object* v_x_2600_, lean_object* v_as_2601_, size_t v_sz_2602_, size_t v_i_2603_, lean_object* v_b_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_){
_start:
{
lean_object* v___x_2616_; 
v___x_2616_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(v_c_2599_, v_x_2600_, v_as_2601_, v_sz_2602_, v_i_2603_, v_b_2604_, v___y_2605_);
return v___x_2616_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___boxed(lean_object** _args){
lean_object* v_c_2617_ = _args[0];
lean_object* v_x_2618_ = _args[1];
lean_object* v_as_2619_ = _args[2];
lean_object* v_sz_2620_ = _args[3];
lean_object* v_i_2621_ = _args[4];
lean_object* v_b_2622_ = _args[5];
lean_object* v___y_2623_ = _args[6];
lean_object* v___y_2624_ = _args[7];
lean_object* v___y_2625_ = _args[8];
lean_object* v___y_2626_ = _args[9];
lean_object* v___y_2627_ = _args[10];
lean_object* v___y_2628_ = _args[11];
lean_object* v___y_2629_ = _args[12];
lean_object* v___y_2630_ = _args[13];
lean_object* v___y_2631_ = _args[14];
lean_object* v___y_2632_ = _args[15];
lean_object* v___y_2633_ = _args[16];
_start:
{
size_t v_sz_boxed_2634_; size_t v_i_boxed_2635_; lean_object* v_res_2636_; 
v_sz_boxed_2634_ = lean_unbox_usize(v_sz_2620_);
lean_dec(v_sz_2620_);
v_i_boxed_2635_ = lean_unbox_usize(v_i_2621_);
lean_dec(v_i_2621_);
v_res_2636_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10(v_c_2617_, v_x_2618_, v_as_2619_, v_sz_boxed_2634_, v_i_boxed_2635_, v_b_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_);
lean_dec(v___y_2632_);
lean_dec_ref(v___y_2631_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
lean_dec(v___y_2626_);
lean_dec_ref(v___y_2625_);
lean_dec(v___y_2624_);
lean_dec(v___y_2623_);
lean_dec_ref(v_as_2619_);
return v_res_2636_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg(lean_object* v_v_2637_, lean_object* v_a_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_){
_start:
{
lean_object* v_snd_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2681_; 
v_snd_2650_ = lean_ctor_get(v_a_2638_, 1);
v_isSharedCheck_2681_ = !lean_is_exclusive(v_a_2638_);
if (v_isSharedCheck_2681_ == 0)
{
lean_object* v_unused_2682_; 
v_unused_2682_ = lean_ctor_get(v_a_2638_, 0);
lean_dec(v_unused_2682_);
v___x_2652_ = v_a_2638_;
v_isShared_2653_ = v_isSharedCheck_2681_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_snd_2650_);
lean_dec(v_a_2638_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2681_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v___x_2654_; lean_object* v___x_2655_; 
v___x_2654_ = lean_box(0);
lean_inc(v_snd_2650_);
lean_inc(v_v_2637_);
v___x_2655_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(v_v_2637_, v_snd_2650_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_);
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_object* v_a_2656_; lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2672_; 
v_a_2656_ = lean_ctor_get(v___x_2655_, 0);
v_isSharedCheck_2672_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2672_ == 0)
{
v___x_2658_ = v___x_2655_;
v_isShared_2659_ = v_isSharedCheck_2672_;
goto v_resetjp_2657_;
}
else
{
lean_inc(v_a_2656_);
lean_dec(v___x_2655_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2672_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
if (lean_obj_tag(v_a_2656_) == 1)
{
lean_object* v_val_2660_; lean_object* v___x_2662_; 
lean_del_object(v___x_2658_);
lean_dec(v_snd_2650_);
v_val_2660_ = lean_ctor_get(v_a_2656_, 0);
lean_inc(v_val_2660_);
lean_dec_ref_known(v_a_2656_, 1);
if (v_isShared_2653_ == 0)
{
lean_ctor_set(v___x_2652_, 1, v_val_2660_);
lean_ctor_set(v___x_2652_, 0, v___x_2654_);
v___x_2662_ = v___x_2652_;
goto v_reusejp_2661_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v___x_2654_);
lean_ctor_set(v_reuseFailAlloc_2664_, 1, v_val_2660_);
v___x_2662_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2661_;
}
v_reusejp_2661_:
{
v_a_2638_ = v___x_2662_;
goto _start;
}
}
else
{
lean_object* v___x_2665_; lean_object* v___x_2667_; 
lean_dec(v_a_2656_);
lean_dec(v_v_2637_);
lean_inc(v_snd_2650_);
v___x_2665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2665_, 0, v_snd_2650_);
if (v_isShared_2653_ == 0)
{
lean_ctor_set(v___x_2652_, 0, v___x_2665_);
v___x_2667_ = v___x_2652_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v___x_2665_);
lean_ctor_set(v_reuseFailAlloc_2671_, 1, v_snd_2650_);
v___x_2667_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
lean_object* v___x_2669_; 
if (v_isShared_2659_ == 0)
{
lean_ctor_set(v___x_2658_, 0, v___x_2667_);
v___x_2669_ = v___x_2658_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2670_; 
v_reuseFailAlloc_2670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2670_, 0, v___x_2667_);
v___x_2669_ = v_reuseFailAlloc_2670_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
return v___x_2669_;
}
}
}
}
}
else
{
lean_object* v_a_2673_; lean_object* v___x_2675_; uint8_t v_isShared_2676_; uint8_t v_isSharedCheck_2680_; 
lean_del_object(v___x_2652_);
lean_dec(v_snd_2650_);
lean_dec(v_v_2637_);
v_a_2673_ = lean_ctor_get(v___x_2655_, 0);
v_isSharedCheck_2680_ = !lean_is_exclusive(v___x_2655_);
if (v_isSharedCheck_2680_ == 0)
{
v___x_2675_ = v___x_2655_;
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
else
{
lean_inc(v_a_2673_);
lean_dec(v___x_2655_);
v___x_2675_ = lean_box(0);
v_isShared_2676_ = v_isSharedCheck_2680_;
goto v_resetjp_2674_;
}
v_resetjp_2674_:
{
lean_object* v___x_2678_; 
if (v_isShared_2676_ == 0)
{
v___x_2678_ = v___x_2675_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2679_; 
v_reuseFailAlloc_2679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2679_, 0, v_a_2673_);
v___x_2678_ = v_reuseFailAlloc_2679_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
return v___x_2678_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg___boxed(lean_object* v_v_2683_, lean_object* v_a_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_){
_start:
{
lean_object* v_res_2696_; 
v_res_2696_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg(v_v_2683_, v_a_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_);
lean_dec(v___y_2694_);
lean_dec_ref(v___y_2693_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
lean_dec(v___y_2690_);
lean_dec_ref(v___y_2689_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
lean_dec(v___y_2686_);
lean_dec(v___y_2685_);
return v_res_2696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(lean_object* v_c_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_){
_start:
{
lean_object* v_p_2709_; 
v_p_2709_ = lean_ctor_get(v_c_2697_, 0);
if (lean_obj_tag(v_p_2709_) == 1)
{
lean_object* v_v_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; 
v_v_2710_ = lean_ctor_get(v_p_2709_, 1);
lean_inc(v_v_2710_);
v___x_2711_ = lean_box(0);
v___x_2712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2712_, 0, v___x_2711_);
lean_ctor_set(v___x_2712_, 1, v_c_2697_);
v___x_2713_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg(v_v_2710_, v___x_2712_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
if (lean_obj_tag(v___x_2713_) == 0)
{
lean_object* v_a_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2727_; 
v_a_2714_ = lean_ctor_get(v___x_2713_, 0);
v_isSharedCheck_2727_ = !lean_is_exclusive(v___x_2713_);
if (v_isSharedCheck_2727_ == 0)
{
v___x_2716_ = v___x_2713_;
v_isShared_2717_ = v_isSharedCheck_2727_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_a_2714_);
lean_dec(v___x_2713_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2727_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v_fst_2718_; 
v_fst_2718_ = lean_ctor_get(v_a_2714_, 0);
if (lean_obj_tag(v_fst_2718_) == 0)
{
lean_object* v_snd_2719_; lean_object* v___x_2721_; 
v_snd_2719_ = lean_ctor_get(v_a_2714_, 1);
lean_inc(v_snd_2719_);
lean_dec(v_a_2714_);
if (v_isShared_2717_ == 0)
{
lean_ctor_set(v___x_2716_, 0, v_snd_2719_);
v___x_2721_ = v___x_2716_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_snd_2719_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
return v___x_2721_;
}
}
else
{
lean_object* v_val_2723_; lean_object* v___x_2725_; 
lean_inc_ref(v_fst_2718_);
lean_dec(v_a_2714_);
v_val_2723_ = lean_ctor_get(v_fst_2718_, 0);
lean_inc(v_val_2723_);
lean_dec_ref_known(v_fst_2718_, 1);
if (v_isShared_2717_ == 0)
{
lean_ctor_set(v___x_2716_, 0, v_val_2723_);
v___x_2725_ = v___x_2716_;
goto v_reusejp_2724_;
}
else
{
lean_object* v_reuseFailAlloc_2726_; 
v_reuseFailAlloc_2726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2726_, 0, v_val_2723_);
v___x_2725_ = v_reuseFailAlloc_2726_;
goto v_reusejp_2724_;
}
v_reusejp_2724_:
{
return v___x_2725_;
}
}
}
}
else
{
lean_object* v_a_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2735_; 
v_a_2728_ = lean_ctor_get(v___x_2713_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2713_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2730_ = v___x_2713_;
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_dec(v___x_2713_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2733_; 
if (v_isShared_2731_ == 0)
{
v___x_2733_ = v___x_2730_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_a_2728_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
}
}
else
{
lean_object* v___x_2736_; 
v___x_2736_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_2697_, v_a_2698_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
return v___x_2736_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq___boxed(lean_object* v_c_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_){
_start:
{
lean_object* v_res_2749_; 
v_res_2749_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(v_c_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_);
lean_dec(v_a_2747_);
lean_dec_ref(v_a_2746_);
lean_dec(v_a_2745_);
lean_dec_ref(v_a_2744_);
lean_dec(v_a_2743_);
lean_dec_ref(v_a_2742_);
lean_dec(v_a_2741_);
lean_dec_ref(v_a_2740_);
lean_dec(v_a_2739_);
lean_dec(v_a_2738_);
return v_res_2749_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0(lean_object* v_v_2750_, lean_object* v_inst_2751_, lean_object* v_a_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_){
_start:
{
lean_object* v___x_2764_; 
v___x_2764_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg(v_v_2750_, v_a_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_);
return v___x_2764_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___boxed(lean_object* v_v_2765_, lean_object* v_inst_2766_, lean_object* v_a_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_){
_start:
{
lean_object* v_res_2779_; 
v_res_2779_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0(v_v_2765_, v_inst_2766_, v_a_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_);
lean_dec(v___y_2777_);
lean_dec_ref(v___y_2776_);
lean_dec(v___y_2775_);
lean_dec_ref(v___y_2774_);
lean_dec(v___y_2773_);
lean_dec_ref(v___y_2772_);
lean_dec(v___y_2771_);
lean_dec_ref(v___y_2770_);
lean_dec(v___y_2769_);
lean_dec(v___y_2768_);
return v_res_2779_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(lean_object* v_a_2780_, lean_object* v_x_2781_, size_t v_x_2782_, size_t v_x_2783_){
_start:
{
if (lean_obj_tag(v_x_2781_) == 0)
{
lean_object* v_cs_2784_; size_t v_j_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; uint8_t v___x_2788_; 
v_cs_2784_ = lean_ctor_get(v_x_2781_, 0);
v_j_2785_ = lean_usize_shift_right(v_x_2782_, v_x_2783_);
v___x_2786_ = lean_usize_to_nat(v_j_2785_);
v___x_2787_ = lean_array_get_size(v_cs_2784_);
v___x_2788_ = lean_nat_dec_lt(v___x_2786_, v___x_2787_);
if (v___x_2788_ == 0)
{
lean_dec(v___x_2786_);
lean_dec_ref(v_a_2780_);
return v_x_2781_;
}
else
{
lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2806_; 
lean_inc_ref(v_cs_2784_);
v_isSharedCheck_2806_ = !lean_is_exclusive(v_x_2781_);
if (v_isSharedCheck_2806_ == 0)
{
lean_object* v_unused_2807_; 
v_unused_2807_ = lean_ctor_get(v_x_2781_, 0);
lean_dec(v_unused_2807_);
v___x_2790_ = v_x_2781_;
v_isShared_2791_ = v_isSharedCheck_2806_;
goto v_resetjp_2789_;
}
else
{
lean_dec(v_x_2781_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2806_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
size_t v___x_2792_; size_t v___x_2793_; size_t v___x_2794_; size_t v_i_2795_; size_t v___x_2796_; size_t v_shift_2797_; lean_object* v_v_2798_; lean_object* v___x_2799_; lean_object* v_xs_x27_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2804_; 
v___x_2792_ = ((size_t)1ULL);
v___x_2793_ = lean_usize_shift_left(v___x_2792_, v_x_2783_);
v___x_2794_ = lean_usize_sub(v___x_2793_, v___x_2792_);
v_i_2795_ = lean_usize_land(v_x_2782_, v___x_2794_);
v___x_2796_ = ((size_t)5ULL);
v_shift_2797_ = lean_usize_sub(v_x_2783_, v___x_2796_);
v_v_2798_ = lean_array_fget(v_cs_2784_, v___x_2786_);
v___x_2799_ = lean_box(0);
v_xs_x27_2800_ = lean_array_fset(v_cs_2784_, v___x_2786_, v___x_2799_);
v___x_2801_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(v_a_2780_, v_v_2798_, v_i_2795_, v_shift_2797_);
v___x_2802_ = lean_array_fset(v_xs_x27_2800_, v___x_2786_, v___x_2801_);
lean_dec(v___x_2786_);
if (v_isShared_2791_ == 0)
{
lean_ctor_set(v___x_2790_, 0, v___x_2802_);
v___x_2804_ = v___x_2790_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v___x_2802_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
return v___x_2804_;
}
}
}
}
else
{
lean_object* v_vs_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; uint8_t v___x_2811_; 
v_vs_2808_ = lean_ctor_get(v_x_2781_, 0);
v___x_2809_ = lean_usize_to_nat(v_x_2782_);
v___x_2810_ = lean_array_get_size(v_vs_2808_);
v___x_2811_ = lean_nat_dec_lt(v___x_2809_, v___x_2810_);
if (v___x_2811_ == 0)
{
lean_dec(v___x_2809_);
lean_dec_ref(v_a_2780_);
return v_x_2781_;
}
else
{
lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2823_; 
lean_inc_ref(v_vs_2808_);
v_isSharedCheck_2823_ = !lean_is_exclusive(v_x_2781_);
if (v_isSharedCheck_2823_ == 0)
{
lean_object* v_unused_2824_; 
v_unused_2824_ = lean_ctor_get(v_x_2781_, 0);
lean_dec(v_unused_2824_);
v___x_2813_ = v_x_2781_;
v_isShared_2814_ = v_isSharedCheck_2823_;
goto v_resetjp_2812_;
}
else
{
lean_dec(v_x_2781_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2823_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v_v_2815_; lean_object* v___x_2816_; lean_object* v_xs_x27_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2821_; 
v_v_2815_ = lean_array_fget(v_vs_2808_, v___x_2809_);
v___x_2816_ = lean_box(0);
v_xs_x27_2817_ = lean_array_fset(v_vs_2808_, v___x_2809_, v___x_2816_);
v___x_2818_ = l_Lean_PersistentArray_push___redArg(v_v_2815_, v_a_2780_);
v___x_2819_ = lean_array_fset(v_xs_x27_2817_, v___x_2809_, v___x_2818_);
lean_dec(v___x_2809_);
if (v_isShared_2814_ == 0)
{
lean_ctor_set(v___x_2813_, 0, v___x_2819_);
v___x_2821_ = v___x_2813_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v___x_2819_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0___boxed(lean_object* v_a_2825_, lean_object* v_x_2826_, lean_object* v_x_2827_, lean_object* v_x_2828_){
_start:
{
size_t v_x_62157__boxed_2829_; size_t v_x_62158__boxed_2830_; lean_object* v_res_2831_; 
v_x_62157__boxed_2829_ = lean_unbox_usize(v_x_2827_);
lean_dec(v_x_2827_);
v_x_62158__boxed_2830_ = lean_unbox_usize(v_x_2828_);
lean_dec(v_x_2828_);
v_res_2831_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(v_a_2825_, v_x_2826_, v_x_62157__boxed_2829_, v_x_62158__boxed_2830_);
return v_res_2831_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(lean_object* v_a_2832_, lean_object* v_t_2833_, lean_object* v_i_2834_){
_start:
{
lean_object* v_root_2835_; lean_object* v_tail_2836_; lean_object* v_size_2837_; size_t v_shift_2838_; lean_object* v_tailOff_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2863_; 
v_root_2835_ = lean_ctor_get(v_t_2833_, 0);
v_tail_2836_ = lean_ctor_get(v_t_2833_, 1);
v_size_2837_ = lean_ctor_get(v_t_2833_, 2);
v_shift_2838_ = lean_ctor_get_usize(v_t_2833_, 4);
v_tailOff_2839_ = lean_ctor_get(v_t_2833_, 3);
v_isSharedCheck_2863_ = !lean_is_exclusive(v_t_2833_);
if (v_isSharedCheck_2863_ == 0)
{
v___x_2841_ = v_t_2833_;
v_isShared_2842_ = v_isSharedCheck_2863_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_tailOff_2839_);
lean_inc(v_size_2837_);
lean_inc(v_tail_2836_);
lean_inc(v_root_2835_);
lean_dec(v_t_2833_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2863_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
uint8_t v___x_2843_; 
v___x_2843_ = lean_nat_dec_le(v_tailOff_2839_, v_i_2834_);
if (v___x_2843_ == 0)
{
size_t v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2847_; 
v___x_2844_ = lean_usize_of_nat(v_i_2834_);
v___x_2845_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(v_a_2832_, v_root_2835_, v___x_2844_, v_shift_2838_);
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 0, v___x_2845_);
v___x_2847_ = v___x_2841_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v___x_2845_);
lean_ctor_set(v_reuseFailAlloc_2848_, 1, v_tail_2836_);
lean_ctor_set(v_reuseFailAlloc_2848_, 2, v_size_2837_);
lean_ctor_set(v_reuseFailAlloc_2848_, 3, v_tailOff_2839_);
lean_ctor_set_usize(v_reuseFailAlloc_2848_, 4, v_shift_2838_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
return v___x_2847_;
}
}
else
{
lean_object* v___x_2849_; lean_object* v___x_2850_; uint8_t v___x_2851_; 
v___x_2849_ = lean_nat_sub(v_i_2834_, v_tailOff_2839_);
v___x_2850_ = lean_array_get_size(v_tail_2836_);
v___x_2851_ = lean_nat_dec_lt(v___x_2849_, v___x_2850_);
if (v___x_2851_ == 0)
{
lean_object* v___x_2853_; 
lean_dec(v___x_2849_);
lean_dec_ref(v_a_2832_);
if (v_isShared_2842_ == 0)
{
v___x_2853_ = v___x_2841_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_root_2835_);
lean_ctor_set(v_reuseFailAlloc_2854_, 1, v_tail_2836_);
lean_ctor_set(v_reuseFailAlloc_2854_, 2, v_size_2837_);
lean_ctor_set(v_reuseFailAlloc_2854_, 3, v_tailOff_2839_);
lean_ctor_set_usize(v_reuseFailAlloc_2854_, 4, v_shift_2838_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
else
{
lean_object* v_v_2855_; lean_object* v___x_2856_; lean_object* v_xs_x27_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2861_; 
v_v_2855_ = lean_array_fget(v_tail_2836_, v___x_2849_);
v___x_2856_ = lean_box(0);
v_xs_x27_2857_ = lean_array_fset(v_tail_2836_, v___x_2849_, v___x_2856_);
v___x_2858_ = l_Lean_PersistentArray_push___redArg(v_v_2855_, v_a_2832_);
v___x_2859_ = lean_array_fset(v_xs_x27_2857_, v___x_2849_, v___x_2858_);
lean_dec(v___x_2849_);
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 1, v___x_2859_);
v___x_2861_ = v___x_2841_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_root_2835_);
lean_ctor_set(v_reuseFailAlloc_2862_, 1, v___x_2859_);
lean_ctor_set(v_reuseFailAlloc_2862_, 2, v_size_2837_);
lean_ctor_set(v_reuseFailAlloc_2862_, 3, v_tailOff_2839_);
lean_ctor_set_usize(v_reuseFailAlloc_2862_, 4, v_shift_2838_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
return v___x_2861_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0___boxed(lean_object* v_a_2864_, lean_object* v_t_2865_, lean_object* v_i_2866_){
_start:
{
lean_object* v_res_2867_; 
v_res_2867_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(v_a_2864_, v_t_2865_, v_i_2866_);
lean_dec(v_i_2866_);
return v_res_2867_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0(lean_object* v_a_2868_, lean_object* v_v_2869_, lean_object* v_s_2870_){
_start:
{
lean_object* v_vars_2871_; lean_object* v_varMap_2872_; lean_object* v_varsHistory_2873_; lean_object* v_natToIntMap_2874_; lean_object* v_natDef_2875_; lean_object* v_dvds_2876_; lean_object* v_lowers_2877_; lean_object* v_uppers_2878_; lean_object* v_diseqs_2879_; lean_object* v_elimEqs_2880_; lean_object* v_elimStack_2881_; lean_object* v_occurs_2882_; lean_object* v_assignment_2883_; lean_object* v_nextCnstrId_2884_; uint8_t v_caseSplits_2885_; lean_object* v_steps_2886_; lean_object* v_conflict_x3f_2887_; lean_object* v_diseqSplits_2888_; lean_object* v_divMod_2889_; uint8_t v_usedCommRing_2890_; lean_object* v_nonlinearOccs_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2899_; 
v_vars_2871_ = lean_ctor_get(v_s_2870_, 0);
v_varMap_2872_ = lean_ctor_get(v_s_2870_, 1);
v_varsHistory_2873_ = lean_ctor_get(v_s_2870_, 2);
v_natToIntMap_2874_ = lean_ctor_get(v_s_2870_, 3);
v_natDef_2875_ = lean_ctor_get(v_s_2870_, 4);
v_dvds_2876_ = lean_ctor_get(v_s_2870_, 5);
v_lowers_2877_ = lean_ctor_get(v_s_2870_, 6);
v_uppers_2878_ = lean_ctor_get(v_s_2870_, 7);
v_diseqs_2879_ = lean_ctor_get(v_s_2870_, 8);
v_elimEqs_2880_ = lean_ctor_get(v_s_2870_, 9);
v_elimStack_2881_ = lean_ctor_get(v_s_2870_, 10);
v_occurs_2882_ = lean_ctor_get(v_s_2870_, 11);
v_assignment_2883_ = lean_ctor_get(v_s_2870_, 12);
v_nextCnstrId_2884_ = lean_ctor_get(v_s_2870_, 13);
v_caseSplits_2885_ = lean_ctor_get_uint8(v_s_2870_, sizeof(void*)*19);
v_steps_2886_ = lean_ctor_get(v_s_2870_, 14);
v_conflict_x3f_2887_ = lean_ctor_get(v_s_2870_, 15);
v_diseqSplits_2888_ = lean_ctor_get(v_s_2870_, 16);
v_divMod_2889_ = lean_ctor_get(v_s_2870_, 17);
v_usedCommRing_2890_ = lean_ctor_get_uint8(v_s_2870_, sizeof(void*)*19 + 1);
v_nonlinearOccs_2891_ = lean_ctor_get(v_s_2870_, 18);
v_isSharedCheck_2899_ = !lean_is_exclusive(v_s_2870_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2893_ = v_s_2870_;
v_isShared_2894_ = v_isSharedCheck_2899_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_nonlinearOccs_2891_);
lean_inc(v_divMod_2889_);
lean_inc(v_diseqSplits_2888_);
lean_inc(v_conflict_x3f_2887_);
lean_inc(v_steps_2886_);
lean_inc(v_nextCnstrId_2884_);
lean_inc(v_assignment_2883_);
lean_inc(v_occurs_2882_);
lean_inc(v_elimStack_2881_);
lean_inc(v_elimEqs_2880_);
lean_inc(v_diseqs_2879_);
lean_inc(v_uppers_2878_);
lean_inc(v_lowers_2877_);
lean_inc(v_dvds_2876_);
lean_inc(v_natDef_2875_);
lean_inc(v_natToIntMap_2874_);
lean_inc(v_varsHistory_2873_);
lean_inc(v_varMap_2872_);
lean_inc(v_vars_2871_);
lean_dec(v_s_2870_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2899_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2895_; lean_object* v___x_2897_; 
v___x_2895_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(v_a_2868_, v_lowers_2877_, v_v_2869_);
if (v_isShared_2894_ == 0)
{
lean_ctor_set(v___x_2893_, 6, v___x_2895_);
v___x_2897_ = v___x_2893_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v_vars_2871_);
lean_ctor_set(v_reuseFailAlloc_2898_, 1, v_varMap_2872_);
lean_ctor_set(v_reuseFailAlloc_2898_, 2, v_varsHistory_2873_);
lean_ctor_set(v_reuseFailAlloc_2898_, 3, v_natToIntMap_2874_);
lean_ctor_set(v_reuseFailAlloc_2898_, 4, v_natDef_2875_);
lean_ctor_set(v_reuseFailAlloc_2898_, 5, v_dvds_2876_);
lean_ctor_set(v_reuseFailAlloc_2898_, 6, v___x_2895_);
lean_ctor_set(v_reuseFailAlloc_2898_, 7, v_uppers_2878_);
lean_ctor_set(v_reuseFailAlloc_2898_, 8, v_diseqs_2879_);
lean_ctor_set(v_reuseFailAlloc_2898_, 9, v_elimEqs_2880_);
lean_ctor_set(v_reuseFailAlloc_2898_, 10, v_elimStack_2881_);
lean_ctor_set(v_reuseFailAlloc_2898_, 11, v_occurs_2882_);
lean_ctor_set(v_reuseFailAlloc_2898_, 12, v_assignment_2883_);
lean_ctor_set(v_reuseFailAlloc_2898_, 13, v_nextCnstrId_2884_);
lean_ctor_set(v_reuseFailAlloc_2898_, 14, v_steps_2886_);
lean_ctor_set(v_reuseFailAlloc_2898_, 15, v_conflict_x3f_2887_);
lean_ctor_set(v_reuseFailAlloc_2898_, 16, v_diseqSplits_2888_);
lean_ctor_set(v_reuseFailAlloc_2898_, 17, v_divMod_2889_);
lean_ctor_set(v_reuseFailAlloc_2898_, 18, v_nonlinearOccs_2891_);
lean_ctor_set_uint8(v_reuseFailAlloc_2898_, sizeof(void*)*19, v_caseSplits_2885_);
lean_ctor_set_uint8(v_reuseFailAlloc_2898_, sizeof(void*)*19 + 1, v_usedCommRing_2890_);
v___x_2897_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
return v___x_2897_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0___boxed(lean_object* v_a_2900_, lean_object* v_v_2901_, lean_object* v_s_2902_){
_start:
{
lean_object* v_res_2903_; 
v_res_2903_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0(v_a_2900_, v_v_2901_, v_s_2902_);
lean_dec(v_v_2901_);
return v_res_2903_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1(lean_object* v_a_2904_, lean_object* v_v_2905_, lean_object* v_s_2906_){
_start:
{
lean_object* v_vars_2907_; lean_object* v_varMap_2908_; lean_object* v_varsHistory_2909_; lean_object* v_natToIntMap_2910_; lean_object* v_natDef_2911_; lean_object* v_dvds_2912_; lean_object* v_lowers_2913_; lean_object* v_uppers_2914_; lean_object* v_diseqs_2915_; lean_object* v_elimEqs_2916_; lean_object* v_elimStack_2917_; lean_object* v_occurs_2918_; lean_object* v_assignment_2919_; lean_object* v_nextCnstrId_2920_; uint8_t v_caseSplits_2921_; lean_object* v_steps_2922_; lean_object* v_conflict_x3f_2923_; lean_object* v_diseqSplits_2924_; lean_object* v_divMod_2925_; uint8_t v_usedCommRing_2926_; lean_object* v_nonlinearOccs_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2935_; 
v_vars_2907_ = lean_ctor_get(v_s_2906_, 0);
v_varMap_2908_ = lean_ctor_get(v_s_2906_, 1);
v_varsHistory_2909_ = lean_ctor_get(v_s_2906_, 2);
v_natToIntMap_2910_ = lean_ctor_get(v_s_2906_, 3);
v_natDef_2911_ = lean_ctor_get(v_s_2906_, 4);
v_dvds_2912_ = lean_ctor_get(v_s_2906_, 5);
v_lowers_2913_ = lean_ctor_get(v_s_2906_, 6);
v_uppers_2914_ = lean_ctor_get(v_s_2906_, 7);
v_diseqs_2915_ = lean_ctor_get(v_s_2906_, 8);
v_elimEqs_2916_ = lean_ctor_get(v_s_2906_, 9);
v_elimStack_2917_ = lean_ctor_get(v_s_2906_, 10);
v_occurs_2918_ = lean_ctor_get(v_s_2906_, 11);
v_assignment_2919_ = lean_ctor_get(v_s_2906_, 12);
v_nextCnstrId_2920_ = lean_ctor_get(v_s_2906_, 13);
v_caseSplits_2921_ = lean_ctor_get_uint8(v_s_2906_, sizeof(void*)*19);
v_steps_2922_ = lean_ctor_get(v_s_2906_, 14);
v_conflict_x3f_2923_ = lean_ctor_get(v_s_2906_, 15);
v_diseqSplits_2924_ = lean_ctor_get(v_s_2906_, 16);
v_divMod_2925_ = lean_ctor_get(v_s_2906_, 17);
v_usedCommRing_2926_ = lean_ctor_get_uint8(v_s_2906_, sizeof(void*)*19 + 1);
v_nonlinearOccs_2927_ = lean_ctor_get(v_s_2906_, 18);
v_isSharedCheck_2935_ = !lean_is_exclusive(v_s_2906_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2929_ = v_s_2906_;
v_isShared_2930_ = v_isSharedCheck_2935_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_nonlinearOccs_2927_);
lean_inc(v_divMod_2925_);
lean_inc(v_diseqSplits_2924_);
lean_inc(v_conflict_x3f_2923_);
lean_inc(v_steps_2922_);
lean_inc(v_nextCnstrId_2920_);
lean_inc(v_assignment_2919_);
lean_inc(v_occurs_2918_);
lean_inc(v_elimStack_2917_);
lean_inc(v_elimEqs_2916_);
lean_inc(v_diseqs_2915_);
lean_inc(v_uppers_2914_);
lean_inc(v_lowers_2913_);
lean_inc(v_dvds_2912_);
lean_inc(v_natDef_2911_);
lean_inc(v_natToIntMap_2910_);
lean_inc(v_varsHistory_2909_);
lean_inc(v_varMap_2908_);
lean_inc(v_vars_2907_);
lean_dec(v_s_2906_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2935_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2931_; lean_object* v___x_2933_; 
v___x_2931_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(v_a_2904_, v_uppers_2914_, v_v_2905_);
if (v_isShared_2930_ == 0)
{
lean_ctor_set(v___x_2929_, 7, v___x_2931_);
v___x_2933_ = v___x_2929_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(0, 19, 2);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_vars_2907_);
lean_ctor_set(v_reuseFailAlloc_2934_, 1, v_varMap_2908_);
lean_ctor_set(v_reuseFailAlloc_2934_, 2, v_varsHistory_2909_);
lean_ctor_set(v_reuseFailAlloc_2934_, 3, v_natToIntMap_2910_);
lean_ctor_set(v_reuseFailAlloc_2934_, 4, v_natDef_2911_);
lean_ctor_set(v_reuseFailAlloc_2934_, 5, v_dvds_2912_);
lean_ctor_set(v_reuseFailAlloc_2934_, 6, v_lowers_2913_);
lean_ctor_set(v_reuseFailAlloc_2934_, 7, v___x_2931_);
lean_ctor_set(v_reuseFailAlloc_2934_, 8, v_diseqs_2915_);
lean_ctor_set(v_reuseFailAlloc_2934_, 9, v_elimEqs_2916_);
lean_ctor_set(v_reuseFailAlloc_2934_, 10, v_elimStack_2917_);
lean_ctor_set(v_reuseFailAlloc_2934_, 11, v_occurs_2918_);
lean_ctor_set(v_reuseFailAlloc_2934_, 12, v_assignment_2919_);
lean_ctor_set(v_reuseFailAlloc_2934_, 13, v_nextCnstrId_2920_);
lean_ctor_set(v_reuseFailAlloc_2934_, 14, v_steps_2922_);
lean_ctor_set(v_reuseFailAlloc_2934_, 15, v_conflict_x3f_2923_);
lean_ctor_set(v_reuseFailAlloc_2934_, 16, v_diseqSplits_2924_);
lean_ctor_set(v_reuseFailAlloc_2934_, 17, v_divMod_2925_);
lean_ctor_set(v_reuseFailAlloc_2934_, 18, v_nonlinearOccs_2927_);
lean_ctor_set_uint8(v_reuseFailAlloc_2934_, sizeof(void*)*19, v_caseSplits_2921_);
lean_ctor_set_uint8(v_reuseFailAlloc_2934_, sizeof(void*)*19 + 1, v_usedCommRing_2926_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1___boxed(lean_object* v_a_2936_, lean_object* v_v_2937_, lean_object* v_s_2938_){
_start:
{
lean_object* v_res_2939_; 
v_res_2939_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1(v_a_2936_, v_v_2937_, v_s_2938_);
lean_dec(v_v_2937_);
return v_res_2939_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3(void){
_start:
{
lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; 
v___x_2947_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2));
v___x_2948_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_2949_ = l_Lean_Name_append(v___x_2948_, v___x_2947_);
return v___x_2949_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6(void){
_start:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; 
v___x_2956_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5));
v___x_2957_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_2958_ = l_Lean_Name_append(v___x_2957_, v___x_2956_);
return v___x_2958_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9(void){
_start:
{
lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
v___x_2965_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__8));
v___x_2966_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_2967_ = l_Lean_Name_append(v___x_2966_, v___x_2965_);
return v___x_2967_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11(void){
_start:
{
lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
v___x_2972_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__10));
v___x_2973_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_2974_ = l_Lean_Name_append(v___x_2973_, v___x_2972_);
return v___x_2974_;
}
}
LEAN_EXPORT lean_object* lean_grind_cutsat_assert_le(lean_object* v_c_2975_, lean_object* v_a_2976_, lean_object* v_a_2977_, lean_object* v_a_2978_, lean_object* v_a_2979_, lean_object* v_a_2980_, lean_object* v_a_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_){
_start:
{
lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v___y_3020_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___x_3059_; 
v___x_3059_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_2976_, v_a_2984_);
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_object* v_a_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3200_; 
v_a_3060_ = lean_ctor_get(v___x_3059_, 0);
v_isSharedCheck_3200_ = !lean_is_exclusive(v___x_3059_);
if (v_isSharedCheck_3200_ == 0)
{
v___x_3062_ = v___x_3059_;
v_isShared_3063_ = v_isSharedCheck_3200_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_a_3060_);
lean_dec(v___x_3059_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3200_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
uint8_t v___x_3064_; 
v___x_3064_ = lean_unbox(v_a_3060_);
lean_dec(v_a_3060_);
if (v___x_3064_ == 0)
{
lean_object* v_toCold_3065_; lean_object* v_options_3066_; lean_object* v_inheritedTraceOptions_3067_; uint8_t v_hasTrace_3068_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; 
lean_del_object(v___x_3062_);
v_toCold_3065_ = lean_ctor_get(v_a_2984_, 0);
v_options_3066_ = lean_ctor_get(v_toCold_3065_, 2);
v_inheritedTraceOptions_3067_ = lean_ctor_get(v_toCold_3065_, 11);
v_hasTrace_3068_ = lean_ctor_get_uint8(v_options_3066_, sizeof(void*)*1);
if (v_hasTrace_3068_ == 0)
{
v___y_3070_ = v_a_2976_;
v___y_3071_ = v_a_2977_;
v___y_3072_ = v_a_2978_;
v___y_3073_ = v_a_2979_;
v___y_3074_ = v_a_2980_;
v___y_3075_ = v_a_2981_;
v___y_3076_ = v_a_2982_;
v___y_3077_ = v_a_2983_;
v___y_3078_ = v_a_2984_;
v___y_3079_ = v_a_2985_;
goto v___jp_3069_;
}
else
{
lean_object* v___x_3182_; lean_object* v___x_3183_; uint8_t v___x_3184_; 
v___x_3182_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__10));
v___x_3183_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11);
v___x_3184_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3067_, v_options_3066_, v___x_3183_);
if (v___x_3184_ == 0)
{
v___y_3070_ = v_a_2976_;
v___y_3071_ = v_a_2977_;
v___y_3072_ = v_a_2978_;
v___y_3073_ = v_a_2979_;
v___y_3074_ = v_a_2980_;
v___y_3075_ = v_a_2981_;
v___y_3076_ = v_a_2982_;
v___y_3077_ = v_a_2983_;
v___y_3078_ = v_a_2984_;
v___y_3079_ = v_a_2985_;
goto v___jp_3069_;
}
else
{
lean_object* v___x_3185_; 
lean_inc_ref(v_c_2975_);
v___x_3185_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_2975_, v_a_2976_, v_a_2984_);
if (lean_obj_tag(v___x_3185_) == 0)
{
lean_object* v_a_3186_; lean_object* v___x_3187_; 
v_a_3186_ = lean_ctor_get(v___x_3185_, 0);
lean_inc(v_a_3186_);
lean_dec_ref_known(v___x_3185_, 1);
v___x_3187_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3182_, v_a_3186_, v_a_2982_, v_a_2983_, v_a_2984_, v_a_2985_);
if (lean_obj_tag(v___x_3187_) == 0)
{
lean_dec_ref_known(v___x_3187_, 1);
v___y_3070_ = v_a_2976_;
v___y_3071_ = v_a_2977_;
v___y_3072_ = v_a_2978_;
v___y_3073_ = v_a_2979_;
v___y_3074_ = v_a_2980_;
v___y_3075_ = v_a_2981_;
v___y_3076_ = v_a_2982_;
v___y_3077_ = v_a_2983_;
v___y_3078_ = v_a_2984_;
v___y_3079_ = v_a_2985_;
goto v___jp_3069_;
}
else
{
lean_dec(v_a_2985_);
lean_dec_ref(v_a_2984_);
lean_dec(v_a_2983_);
lean_dec_ref(v_a_2982_);
lean_dec(v_a_2981_);
lean_dec_ref(v_a_2980_);
lean_dec(v_a_2979_);
lean_dec_ref(v_a_2978_);
lean_dec(v_a_2977_);
lean_dec(v_a_2976_);
lean_dec_ref(v_c_2975_);
return v___x_3187_;
}
}
else
{
lean_object* v_a_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3195_; 
lean_dec(v_a_2985_);
lean_dec_ref(v_a_2984_);
lean_dec(v_a_2983_);
lean_dec_ref(v_a_2982_);
lean_dec(v_a_2981_);
lean_dec_ref(v_a_2980_);
lean_dec(v_a_2979_);
lean_dec_ref(v_a_2978_);
lean_dec(v_a_2977_);
lean_dec(v_a_2976_);
lean_dec_ref(v_c_2975_);
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
v___jp_3069_:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___x_3080_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_norm(v_c_2975_);
lean_inc_ref(v___y_3078_);
v___x_3081_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts(v___x_3080_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
if (lean_obj_tag(v___x_3081_) == 0)
{
lean_object* v_a_3082_; lean_object* v_p_3083_; uint8_t v___x_3084_; 
v_a_3082_ = lean_ctor_get(v___x_3081_, 0);
lean_inc(v_a_3082_);
lean_dec_ref_known(v___x_3081_, 1);
v_p_3083_ = lean_ctor_get(v_a_3082_, 0);
v___x_3084_ = l_Int_Internal_Linear_Poly_isUnsatLe(v_p_3083_);
if (v___x_3084_ == 0)
{
uint8_t v___x_3085_; 
v___x_3085_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(v_a_3082_);
if (v___x_3085_ == 0)
{
if (lean_obj_tag(v_p_3083_) == 1)
{
lean_object* v_k_3086_; lean_object* v_v_3087_; lean_object* v___x_3088_; 
v_k_3086_ = lean_ctor_get(v_p_3083_, 0);
lean_inc(v_k_3086_);
v_v_3087_ = lean_ctor_get(v_p_3083_, 1);
lean_inc(v_v_3087_);
lean_inc(v_a_3082_);
v___x_3088_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq(v_a_3082_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
if (lean_obj_tag(v___x_3088_) == 0)
{
lean_object* v_a_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3128_; 
v_a_3089_ = lean_ctor_get(v___x_3088_, 0);
v_isSharedCheck_3128_ = !lean_is_exclusive(v___x_3088_);
if (v_isSharedCheck_3128_ == 0)
{
v___x_3091_ = v___x_3088_;
v_isShared_3092_ = v_isSharedCheck_3128_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_a_3089_);
lean_dec(v___x_3088_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3128_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
uint8_t v___x_3093_; 
v___x_3093_ = lean_unbox(v_a_3089_);
lean_dec(v_a_3089_);
if (v___x_3093_ == 0)
{
lean_object* v___x_3094_; 
lean_del_object(v___x_3091_);
v___x_3094_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(v_a_3082_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
lean_dec(v___y_3073_);
lean_dec_ref(v___y_3072_);
lean_dec(v___y_3071_);
if (lean_obj_tag(v___x_3094_) == 0)
{
lean_object* v_toCold_3095_; lean_object* v_options_3096_; lean_object* v_a_3097_; lean_object* v_inheritedTraceOptions_3098_; uint8_t v_hasTrace_3099_; lean_object* v___f_3100_; lean_object* v___f_3101_; 
v_toCold_3095_ = lean_ctor_get(v___y_3078_, 0);
v_options_3096_ = lean_ctor_get(v_toCold_3095_, 2);
v_a_3097_ = lean_ctor_get(v___x_3094_, 0);
lean_inc_n(v_a_3097_, 3);
lean_dec_ref_known(v___x_3094_, 1);
v_inheritedTraceOptions_3098_ = lean_ctor_get(v_toCold_3095_, 11);
v_hasTrace_3099_ = lean_ctor_get_uint8(v_options_3096_, sizeof(void*)*1);
lean_inc_n(v_v_3087_, 2);
v___f_3100_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3100_, 0, v_a_3097_);
lean_closure_set(v___f_3100_, 1, v_v_3087_);
v___f_3101_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3101_, 0, v_a_3097_);
lean_closure_set(v___f_3101_, 1, v_v_3087_);
if (v_hasTrace_3099_ == 0)
{
v___y_3018_ = v___f_3100_;
v___y_3019_ = v_a_3097_;
v___y_3020_ = v_v_3087_;
v___y_3021_ = v_k_3086_;
v___y_3022_ = v___f_3101_;
v___y_3023_ = v___y_3070_;
v___y_3024_ = v___y_3076_;
v___y_3025_ = v___y_3077_;
v___y_3026_ = v___y_3078_;
v___y_3027_ = v___y_3079_;
goto v___jp_3017_;
}
else
{
lean_object* v___x_3102_; lean_object* v___x_3103_; uint8_t v___x_3104_; 
v___x_3102_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2));
v___x_3103_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3);
v___x_3104_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3098_, v_options_3096_, v___x_3103_);
if (v___x_3104_ == 0)
{
v___y_3018_ = v___f_3100_;
v___y_3019_ = v_a_3097_;
v___y_3020_ = v_v_3087_;
v___y_3021_ = v_k_3086_;
v___y_3022_ = v___f_3101_;
v___y_3023_ = v___y_3070_;
v___y_3024_ = v___y_3076_;
v___y_3025_ = v___y_3077_;
v___y_3026_ = v___y_3078_;
v___y_3027_ = v___y_3079_;
goto v___jp_3017_;
}
else
{
lean_object* v___x_3105_; 
lean_inc(v_a_3097_);
v___x_3105_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_a_3097_, v___y_3070_, v___y_3078_);
if (lean_obj_tag(v___x_3105_) == 0)
{
lean_object* v_a_3106_; lean_object* v___x_3107_; 
v_a_3106_ = lean_ctor_get(v___x_3105_, 0);
lean_inc(v_a_3106_);
lean_dec_ref_known(v___x_3105_, 1);
v___x_3107_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3102_, v_a_3106_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
if (lean_obj_tag(v___x_3107_) == 0)
{
lean_dec_ref_known(v___x_3107_, 1);
v___y_3018_ = v___f_3100_;
v___y_3019_ = v_a_3097_;
v___y_3020_ = v_v_3087_;
v___y_3021_ = v_k_3086_;
v___y_3022_ = v___f_3101_;
v___y_3023_ = v___y_3070_;
v___y_3024_ = v___y_3076_;
v___y_3025_ = v___y_3077_;
v___y_3026_ = v___y_3078_;
v___y_3027_ = v___y_3079_;
goto v___jp_3017_;
}
else
{
lean_dec_ref(v___f_3101_);
lean_dec_ref(v___f_3100_);
lean_dec(v_a_3097_);
lean_dec(v_v_3087_);
lean_dec(v_k_3086_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v___y_3070_);
return v___x_3107_;
}
}
else
{
lean_object* v_a_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3115_; 
lean_dec_ref(v___f_3101_);
lean_dec_ref(v___f_3100_);
lean_dec(v_a_3097_);
lean_dec(v_v_3087_);
lean_dec(v_k_3086_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v___y_3070_);
v_a_3108_ = lean_ctor_get(v___x_3105_, 0);
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_3105_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3110_ = v___x_3105_;
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_a_3108_);
lean_dec(v___x_3105_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3115_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3113_; 
if (v_isShared_3111_ == 0)
{
v___x_3113_ = v___x_3110_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v_a_3108_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
}
}
}
}
else
{
lean_object* v_a_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3123_; 
lean_dec(v_v_3087_);
lean_dec(v_k_3086_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v___y_3070_);
v_a_3116_ = lean_ctor_get(v___x_3094_, 0);
v_isSharedCheck_3123_ = !lean_is_exclusive(v___x_3094_);
if (v_isSharedCheck_3123_ == 0)
{
v___x_3118_ = v___x_3094_;
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_a_3116_);
lean_dec(v___x_3094_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v___x_3121_; 
if (v_isShared_3119_ == 0)
{
v___x_3121_ = v___x_3118_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_a_3116_);
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
else
{
lean_object* v___x_3124_; lean_object* v___x_3126_; 
lean_dec(v_v_3087_);
lean_dec(v_k_3086_);
lean_dec(v_a_3082_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
lean_dec(v___y_3073_);
lean_dec_ref(v___y_3072_);
lean_dec(v___y_3071_);
lean_dec(v___y_3070_);
v___x_3124_ = lean_box(0);
if (v_isShared_3092_ == 0)
{
lean_ctor_set(v___x_3091_, 0, v___x_3124_);
v___x_3126_ = v___x_3091_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v___x_3124_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
return v___x_3126_;
}
}
}
}
else
{
lean_object* v_a_3129_; lean_object* v___x_3131_; uint8_t v_isShared_3132_; uint8_t v_isSharedCheck_3136_; 
lean_dec(v_v_3087_);
lean_dec(v_k_3086_);
lean_dec(v_a_3082_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
lean_dec(v___y_3073_);
lean_dec_ref(v___y_3072_);
lean_dec(v___y_3071_);
lean_dec(v___y_3070_);
v_a_3129_ = lean_ctor_get(v___x_3088_, 0);
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_3088_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3131_ = v___x_3088_;
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
else
{
lean_inc(v_a_3129_);
lean_dec(v___x_3088_);
v___x_3131_ = lean_box(0);
v_isShared_3132_ = v_isSharedCheck_3136_;
goto v_resetjp_3130_;
}
v_resetjp_3130_:
{
lean_object* v___x_3134_; 
if (v_isShared_3132_ == 0)
{
v___x_3134_ = v___x_3131_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_a_3129_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
return v___x_3134_;
}
}
}
}
else
{
lean_object* v___x_3137_; 
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
lean_dec(v___y_3073_);
lean_dec_ref(v___y_3072_);
lean_dec(v___y_3071_);
v___x_3137_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_a_3082_, v___y_3070_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v___y_3070_);
return v___x_3137_;
}
}
else
{
lean_object* v_toCold_3138_; lean_object* v_options_3139_; uint8_t v_hasTrace_3140_; 
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
lean_dec(v___y_3073_);
lean_dec_ref(v___y_3072_);
lean_dec(v___y_3071_);
v_toCold_3138_ = lean_ctor_get(v___y_3078_, 0);
v_options_3139_ = lean_ctor_get(v_toCold_3138_, 2);
v_hasTrace_3140_ = lean_ctor_get_uint8(v_options_3139_, sizeof(void*)*1);
if (v_hasTrace_3140_ == 0)
{
lean_dec(v_a_3082_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v___y_3070_);
goto v___jp_2987_;
}
else
{
lean_object* v_inheritedTraceOptions_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; uint8_t v___x_3144_; 
v_inheritedTraceOptions_3141_ = lean_ctor_get(v_toCold_3138_, 11);
v___x_3142_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5));
v___x_3143_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6);
v___x_3144_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3141_, v_options_3139_, v___x_3143_);
if (v___x_3144_ == 0)
{
lean_dec(v_a_3082_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v___y_3070_);
goto v___jp_2987_;
}
else
{
lean_object* v___x_3145_; 
v___x_3145_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_a_3082_, v___y_3070_, v___y_3078_);
lean_dec(v___y_3070_);
if (lean_obj_tag(v___x_3145_) == 0)
{
lean_object* v_a_3146_; lean_object* v___x_3147_; 
v_a_3146_ = lean_ctor_get(v___x_3145_, 0);
lean_inc(v_a_3146_);
lean_dec_ref_known(v___x_3145_, 1);
v___x_3147_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3142_, v_a_3146_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
if (lean_obj_tag(v___x_3147_) == 0)
{
lean_dec_ref_known(v___x_3147_, 1);
goto v___jp_2987_;
}
else
{
return v___x_3147_;
}
}
else
{
lean_object* v_a_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3155_; 
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
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
}
else
{
lean_object* v_toCold_3156_; lean_object* v_options_3157_; uint8_t v_hasTrace_3158_; 
v_toCold_3156_ = lean_ctor_get(v___y_3078_, 0);
v_options_3157_ = lean_ctor_get(v_toCold_3156_, 2);
v_hasTrace_3158_ = lean_ctor_get_uint8(v_options_3157_, sizeof(void*)*1);
if (v_hasTrace_3158_ == 0)
{
v___y_3037_ = v_a_3082_;
v___y_3038_ = v___y_3070_;
v___y_3039_ = v___y_3071_;
v___y_3040_ = v___y_3072_;
v___y_3041_ = v___y_3073_;
v___y_3042_ = v___y_3074_;
v___y_3043_ = v___y_3075_;
v___y_3044_ = v___y_3076_;
v___y_3045_ = v___y_3077_;
v___y_3046_ = v___y_3078_;
v___y_3047_ = v___y_3079_;
goto v___jp_3036_;
}
else
{
lean_object* v_inheritedTraceOptions_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; uint8_t v___x_3162_; 
v_inheritedTraceOptions_3159_ = lean_ctor_get(v_toCold_3156_, 11);
v___x_3160_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__8));
v___x_3161_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9);
v___x_3162_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3159_, v_options_3157_, v___x_3161_);
if (v___x_3162_ == 0)
{
v___y_3037_ = v_a_3082_;
v___y_3038_ = v___y_3070_;
v___y_3039_ = v___y_3071_;
v___y_3040_ = v___y_3072_;
v___y_3041_ = v___y_3073_;
v___y_3042_ = v___y_3074_;
v___y_3043_ = v___y_3075_;
v___y_3044_ = v___y_3076_;
v___y_3045_ = v___y_3077_;
v___y_3046_ = v___y_3078_;
v___y_3047_ = v___y_3079_;
goto v___jp_3036_;
}
else
{
lean_object* v___x_3163_; 
lean_inc(v_a_3082_);
v___x_3163_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_a_3082_, v___y_3070_, v___y_3078_);
if (lean_obj_tag(v___x_3163_) == 0)
{
lean_object* v_a_3164_; lean_object* v___x_3165_; 
v_a_3164_ = lean_ctor_get(v___x_3163_, 0);
lean_inc(v_a_3164_);
lean_dec_ref_known(v___x_3163_, 1);
v___x_3165_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3160_, v_a_3164_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
if (lean_obj_tag(v___x_3165_) == 0)
{
lean_dec_ref_known(v___x_3165_, 1);
v___y_3037_ = v_a_3082_;
v___y_3038_ = v___y_3070_;
v___y_3039_ = v___y_3071_;
v___y_3040_ = v___y_3072_;
v___y_3041_ = v___y_3073_;
v___y_3042_ = v___y_3074_;
v___y_3043_ = v___y_3075_;
v___y_3044_ = v___y_3076_;
v___y_3045_ = v___y_3077_;
v___y_3046_ = v___y_3078_;
v___y_3047_ = v___y_3079_;
goto v___jp_3036_;
}
else
{
lean_dec(v_a_3082_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
lean_dec(v___y_3073_);
lean_dec_ref(v___y_3072_);
lean_dec(v___y_3071_);
lean_dec(v___y_3070_);
return v___x_3165_;
}
}
else
{
lean_object* v_a_3166_; lean_object* v___x_3168_; uint8_t v_isShared_3169_; uint8_t v_isSharedCheck_3173_; 
lean_dec(v_a_3082_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
lean_dec(v___y_3073_);
lean_dec_ref(v___y_3072_);
lean_dec(v___y_3071_);
lean_dec(v___y_3070_);
v_a_3166_ = lean_ctor_get(v___x_3163_, 0);
v_isSharedCheck_3173_ = !lean_is_exclusive(v___x_3163_);
if (v_isSharedCheck_3173_ == 0)
{
v___x_3168_ = v___x_3163_;
v_isShared_3169_ = v_isSharedCheck_3173_;
goto v_resetjp_3167_;
}
else
{
lean_inc(v_a_3166_);
lean_dec(v___x_3163_);
v___x_3168_ = lean_box(0);
v_isShared_3169_ = v_isSharedCheck_3173_;
goto v_resetjp_3167_;
}
v_resetjp_3167_:
{
lean_object* v___x_3171_; 
if (v_isShared_3169_ == 0)
{
v___x_3171_ = v___x_3168_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_a_3166_);
v___x_3171_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
return v___x_3171_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3174_; lean_object* v___x_3176_; uint8_t v_isShared_3177_; uint8_t v_isSharedCheck_3181_; 
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
lean_dec(v___y_3073_);
lean_dec_ref(v___y_3072_);
lean_dec(v___y_3071_);
lean_dec(v___y_3070_);
v_a_3174_ = lean_ctor_get(v___x_3081_, 0);
v_isSharedCheck_3181_ = !lean_is_exclusive(v___x_3081_);
if (v_isSharedCheck_3181_ == 0)
{
v___x_3176_ = v___x_3081_;
v_isShared_3177_ = v_isSharedCheck_3181_;
goto v_resetjp_3175_;
}
else
{
lean_inc(v_a_3174_);
lean_dec(v___x_3081_);
v___x_3176_ = lean_box(0);
v_isShared_3177_ = v_isSharedCheck_3181_;
goto v_resetjp_3175_;
}
v_resetjp_3175_:
{
lean_object* v___x_3179_; 
if (v_isShared_3177_ == 0)
{
v___x_3179_ = v___x_3176_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_a_3174_);
v___x_3179_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
return v___x_3179_;
}
}
}
}
}
else
{
lean_object* v___x_3196_; lean_object* v___x_3198_; 
lean_dec(v_a_2985_);
lean_dec_ref(v_a_2984_);
lean_dec(v_a_2983_);
lean_dec_ref(v_a_2982_);
lean_dec(v_a_2981_);
lean_dec_ref(v_a_2980_);
lean_dec(v_a_2979_);
lean_dec_ref(v_a_2978_);
lean_dec(v_a_2977_);
lean_dec(v_a_2976_);
lean_dec_ref(v_c_2975_);
v___x_3196_ = lean_box(0);
if (v_isShared_3063_ == 0)
{
lean_ctor_set(v___x_3062_, 0, v___x_3196_);
v___x_3198_ = v___x_3062_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v___x_3196_);
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
lean_object* v_a_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3208_; 
lean_dec(v_a_2985_);
lean_dec_ref(v_a_2984_);
lean_dec(v_a_2983_);
lean_dec_ref(v_a_2982_);
lean_dec(v_a_2981_);
lean_dec_ref(v_a_2980_);
lean_dec(v_a_2979_);
lean_dec_ref(v_a_2978_);
lean_dec(v_a_2977_);
lean_dec(v_a_2976_);
lean_dec_ref(v_c_2975_);
v_a_3201_ = lean_ctor_get(v___x_3059_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v___x_3059_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3203_ = v___x_3059_;
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_a_3201_);
lean_dec(v___x_3059_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v___x_3206_; 
if (v_isShared_3204_ == 0)
{
v___x_3206_ = v___x_3203_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_a_3201_);
v___x_3206_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
return v___x_3206_;
}
}
}
v___jp_2987_:
{
lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2988_ = lean_box(0);
v___x_2989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2989_, 0, v___x_2988_);
return v___x_2989_;
}
v___jp_2990_:
{
lean_object* v___x_2995_; 
v___x_2995_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(v___y_2991_, v___y_2993_, v___y_2994_);
lean_dec_ref(v___y_2994_);
if (lean_obj_tag(v___x_2995_) == 0)
{
lean_object* v_a_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3008_; 
v_a_2996_ = lean_ctor_get(v___x_2995_, 0);
v_isSharedCheck_3008_ = !lean_is_exclusive(v___x_2995_);
if (v_isSharedCheck_3008_ == 0)
{
v___x_2998_ = v___x_2995_;
v_isShared_2999_ = v_isSharedCheck_3008_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_a_2996_);
lean_dec(v___x_2995_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3008_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
uint8_t v___x_3000_; uint8_t v___x_3001_; uint8_t v___x_3002_; 
v___x_3000_ = 0;
v___x_3001_ = lean_unbox(v_a_2996_);
lean_dec(v_a_2996_);
v___x_3002_ = l_Lean_instBEqLBool_beq(v___x_3001_, v___x_3000_);
if (v___x_3002_ == 0)
{
lean_object* v___x_3003_; lean_object* v___x_3005_; 
lean_dec(v___y_2993_);
lean_dec(v___y_2992_);
v___x_3003_ = lean_box(0);
if (v_isShared_2999_ == 0)
{
lean_ctor_set(v___x_2998_, 0, v___x_3003_);
v___x_3005_ = v___x_2998_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v___x_3003_);
v___x_3005_ = v_reuseFailAlloc_3006_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
return v___x_3005_;
}
}
else
{
lean_object* v___x_3007_; 
lean_del_object(v___x_2998_);
v___x_3007_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v___y_2992_, v___y_2993_);
lean_dec(v___y_2993_);
return v___x_3007_;
}
}
}
else
{
lean_object* v_a_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3016_; 
lean_dec(v___y_2993_);
lean_dec(v___y_2992_);
v_a_3009_ = lean_ctor_get(v___x_2995_, 0);
v_isSharedCheck_3016_ = !lean_is_exclusive(v___x_2995_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_3011_ = v___x_2995_;
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_a_3009_);
lean_dec(v___x_2995_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v___x_3014_; 
if (v_isShared_3012_ == 0)
{
v___x_3014_ = v___x_3011_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v_a_3009_);
v___x_3014_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
return v___x_3014_;
}
}
}
}
v___jp_3017_:
{
lean_object* v_p_3028_; lean_object* v___x_3029_; 
v_p_3028_ = lean_ctor_get(v___y_3019_, 0);
lean_inc_ref(v_p_3028_);
v___x_3029_ = l_Int_Internal_Linear_Poly_updateOccs___redArg(v_p_3028_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_, v___y_3027_);
lean_dec(v___y_3027_);
lean_dec(v___y_3025_);
lean_dec_ref(v___y_3024_);
if (lean_obj_tag(v___x_3029_) == 0)
{
lean_object* v___x_3030_; uint8_t v___x_3031_; 
lean_dec_ref_known(v___x_3029_, 1);
v___x_3030_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9);
v___x_3031_ = lean_int_dec_lt(v___y_3021_, v___x_3030_);
lean_dec(v___y_3021_);
if (v___x_3031_ == 0)
{
lean_object* v___x_3032_; lean_object* v___x_3033_; 
lean_dec_ref(v___y_3018_);
v___x_3032_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_3033_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3032_, v___y_3022_, v___y_3023_);
if (lean_obj_tag(v___x_3033_) == 0)
{
lean_dec_ref_known(v___x_3033_, 1);
v___y_2991_ = v___y_3019_;
v___y_2992_ = v___y_3020_;
v___y_2993_ = v___y_3023_;
v___y_2994_ = v___y_3026_;
goto v___jp_2990_;
}
else
{
lean_dec_ref(v___y_3026_);
lean_dec(v___y_3023_);
lean_dec(v___y_3020_);
lean_dec_ref(v___y_3019_);
return v___x_3033_;
}
}
else
{
lean_object* v___x_3034_; lean_object* v___x_3035_; 
lean_dec_ref(v___y_3022_);
v___x_3034_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_3035_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3034_, v___y_3018_, v___y_3023_);
if (lean_obj_tag(v___x_3035_) == 0)
{
lean_dec_ref_known(v___x_3035_, 1);
v___y_2991_ = v___y_3019_;
v___y_2992_ = v___y_3020_;
v___y_2993_ = v___y_3023_;
v___y_2994_ = v___y_3026_;
goto v___jp_2990_;
}
else
{
lean_dec_ref(v___y_3026_);
lean_dec(v___y_3023_);
lean_dec(v___y_3020_);
lean_dec_ref(v___y_3019_);
return v___x_3035_;
}
}
}
else
{
lean_dec_ref(v___y_3026_);
lean_dec(v___y_3023_);
lean_dec_ref(v___y_3022_);
lean_dec(v___y_3021_);
lean_dec(v___y_3020_);
lean_dec_ref(v___y_3019_);
lean_dec_ref(v___y_3018_);
return v___x_3029_;
}
}
v___jp_3036_:
{
lean_object* v___x_3048_; lean_object* v___x_3049_; 
v___x_3048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3048_, 0, v___y_3037_);
v___x_3049_ = l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(v___x_3048_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_);
lean_dec(v___y_3047_);
lean_dec_ref(v___y_3046_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
lean_dec(v___y_3043_);
lean_dec_ref(v___y_3042_);
lean_dec(v___y_3041_);
lean_dec_ref(v___y_3040_);
lean_dec(v___y_3039_);
lean_dec(v___y_3038_);
if (lean_obj_tag(v___x_3049_) == 0)
{
lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3057_; 
v_isSharedCheck_3057_ = !lean_is_exclusive(v___x_3049_);
if (v_isSharedCheck_3057_ == 0)
{
lean_object* v_unused_3058_; 
v_unused_3058_ = lean_ctor_get(v___x_3049_, 0);
lean_dec(v_unused_3058_);
v___x_3051_ = v___x_3049_;
v_isShared_3052_ = v_isSharedCheck_3057_;
goto v_resetjp_3050_;
}
else
{
lean_dec(v___x_3049_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3057_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3053_; lean_object* v___x_3055_; 
v___x_3053_ = lean_box(0);
if (v_isShared_3052_ == 0)
{
lean_ctor_set(v___x_3051_, 0, v___x_3053_);
v___x_3055_ = v___x_3051_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v___x_3053_);
v___x_3055_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
return v___x_3055_;
}
}
}
else
{
return v___x_3049_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___boxed(lean_object* v_c_3209_, lean_object* v_a_3210_, lean_object* v_a_3211_, lean_object* v_a_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_, lean_object* v_a_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_){
_start:
{
lean_object* v_res_3221_; 
v_res_3221_ = lean_grind_cutsat_assert_le(v_c_3209_, v_a_3210_, v_a_3211_, v_a_3212_, v_a_3213_, v_a_3214_, v_a_3215_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_);
return v_res_3221_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1(void){
_start:
{
lean_object* v___x_3223_; lean_object* v___x_3224_; 
v___x_3223_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__0));
v___x_3224_ = l_Lean_stringToMessageData(v___x_3223_);
return v___x_3224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(lean_object* v_e_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_){
_start:
{
lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; 
v___x_3233_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___closed__1);
v___x_3234_ = l_Lean_indentExpr(v_e_3225_);
v___x_3235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3235_, 0, v___x_3233_);
lean_ctor_set(v___x_3235_, 1, v___x_3234_);
v___x_3236_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_3226_);
if (lean_obj_tag(v___x_3236_) == 0)
{
lean_object* v_a_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3247_; 
v_a_3237_ = lean_ctor_get(v___x_3236_, 0);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3236_);
if (v_isSharedCheck_3247_ == 0)
{
v___x_3239_ = v___x_3236_;
v_isShared_3240_ = v_isSharedCheck_3247_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_a_3237_);
lean_dec(v___x_3236_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3247_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
uint8_t v_verbose_3241_; 
v_verbose_3241_ = lean_ctor_get_uint8(v_a_3237_, 0);
lean_dec(v_a_3237_);
if (v_verbose_3241_ == 0)
{
lean_object* v___x_3242_; lean_object* v___x_3244_; 
lean_dec_ref_known(v___x_3235_, 2);
v___x_3242_ = lean_box(0);
if (v_isShared_3240_ == 0)
{
lean_ctor_set(v___x_3239_, 0, v___x_3242_);
v___x_3244_ = v___x_3239_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v___x_3242_);
v___x_3244_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
return v___x_3244_;
}
}
else
{
lean_object* v___x_3246_; 
lean_del_object(v___x_3239_);
v___x_3246_ = l_Lean_Meta_Sym_reportIssue(v___x_3235_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_);
return v___x_3246_;
}
}
}
else
{
lean_object* v_a_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3255_; 
lean_dec_ref_known(v___x_3235_, 2);
v_a_3248_ = lean_ctor_get(v___x_3236_, 0);
v_isSharedCheck_3255_ = !lean_is_exclusive(v___x_3236_);
if (v_isSharedCheck_3255_ == 0)
{
v___x_3250_ = v___x_3236_;
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_a_3248_);
lean_dec(v___x_3236_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3255_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v___x_3253_; 
if (v_isShared_3251_ == 0)
{
v___x_3253_ = v___x_3250_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v_a_3248_);
v___x_3253_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
return v___x_3253_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg___boxed(lean_object* v_e_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_, lean_object* v_a_3260_, lean_object* v_a_3261_, lean_object* v_a_3262_, lean_object* v_a_3263_){
_start:
{
lean_object* v_res_3264_; 
v_res_3264_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(v_e_3256_, v_a_3257_, v_a_3258_, v_a_3259_, v_a_3260_, v_a_3261_, v_a_3262_);
lean_dec(v_a_3262_);
lean_dec_ref(v_a_3261_);
lean_dec(v_a_3260_);
lean_dec_ref(v_a_3259_);
lean_dec(v_a_3258_);
lean_dec_ref(v_a_3257_);
return v_res_3264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized(lean_object* v_e_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_, lean_object* v_a_3272_, lean_object* v_a_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_){
_start:
{
lean_object* v___x_3277_; 
v___x_3277_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(v_e_3265_, v_a_3270_, v_a_3271_, v_a_3272_, v_a_3273_, v_a_3274_, v_a_3275_);
return v___x_3277_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___boxed(lean_object* v_e_3278_, lean_object* v_a_3279_, lean_object* v_a_3280_, lean_object* v_a_3281_, lean_object* v_a_3282_, lean_object* v_a_3283_, lean_object* v_a_3284_, lean_object* v_a_3285_, lean_object* v_a_3286_, lean_object* v_a_3287_, lean_object* v_a_3288_, lean_object* v_a_3289_){
_start:
{
lean_object* v_res_3290_; 
v_res_3290_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized(v_e_3278_, v_a_3279_, v_a_3280_, v_a_3281_, v_a_3282_, v_a_3283_, v_a_3284_, v_a_3285_, v_a_3286_, v_a_3287_, v_a_3288_);
lean_dec(v_a_3288_);
lean_dec_ref(v_a_3287_);
lean_dec(v_a_3286_);
lean_dec_ref(v_a_3285_);
lean_dec(v_a_3284_);
lean_dec_ref(v_a_3283_);
lean_dec(v_a_3282_);
lean_dec_ref(v_a_3281_);
lean_dec(v_a_3280_);
lean_dec(v_a_3279_);
return v_res_3290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f(lean_object* v_e_3296_, lean_object* v_a_3297_, lean_object* v_a_3298_, lean_object* v_a_3299_, lean_object* v_a_3300_, lean_object* v_a_3301_, lean_object* v_a_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_){
_start:
{
lean_object* v___x_3311_; 
lean_inc_ref(v_e_3296_);
v___x_3311_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3296_, v_a_3304_);
if (lean_obj_tag(v___x_3311_) == 0)
{
lean_object* v_a_3312_; lean_object* v___x_3313_; uint8_t v___x_3314_; 
v_a_3312_ = lean_ctor_get(v___x_3311_, 0);
lean_inc(v_a_3312_);
lean_dec_ref_known(v___x_3311_, 1);
v___x_3313_ = l_Lean_Expr_cleanupAnnotations(v_a_3312_);
v___x_3314_ = l_Lean_Expr_isApp(v___x_3313_);
if (v___x_3314_ == 0)
{
lean_dec_ref(v___x_3313_);
lean_dec_ref(v_e_3296_);
goto v___jp_3308_;
}
else
{
lean_object* v_arg_3315_; lean_object* v___x_3316_; uint8_t v___x_3317_; 
v_arg_3315_ = lean_ctor_get(v___x_3313_, 1);
lean_inc_ref(v_arg_3315_);
v___x_3316_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3313_);
v___x_3317_ = l_Lean_Expr_isApp(v___x_3316_);
if (v___x_3317_ == 0)
{
lean_dec_ref(v___x_3316_);
lean_dec_ref(v_arg_3315_);
lean_dec_ref(v_e_3296_);
goto v___jp_3308_;
}
else
{
lean_object* v_arg_3318_; lean_object* v___x_3319_; uint8_t v___x_3320_; 
v_arg_3318_ = lean_ctor_get(v___x_3316_, 1);
lean_inc_ref(v_arg_3318_);
v___x_3319_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3316_);
v___x_3320_ = l_Lean_Expr_isApp(v___x_3319_);
if (v___x_3320_ == 0)
{
lean_dec_ref(v___x_3319_);
lean_dec_ref(v_arg_3318_);
lean_dec_ref(v_arg_3315_);
lean_dec_ref(v_e_3296_);
goto v___jp_3308_;
}
else
{
lean_object* v_arg_3321_; lean_object* v___x_3322_; uint8_t v___x_3323_; 
v_arg_3321_ = lean_ctor_get(v___x_3319_, 1);
lean_inc_ref(v_arg_3321_);
v___x_3322_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3319_);
v___x_3323_ = l_Lean_Expr_isApp(v___x_3322_);
if (v___x_3323_ == 0)
{
lean_dec_ref(v___x_3322_);
lean_dec_ref(v_arg_3321_);
lean_dec_ref(v_arg_3318_);
lean_dec_ref(v_arg_3315_);
lean_dec_ref(v_e_3296_);
goto v___jp_3308_;
}
else
{
lean_object* v___x_3324_; lean_object* v___x_3325_; uint8_t v___x_3326_; 
v___x_3324_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3322_);
v___x_3325_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2));
v___x_3326_ = l_Lean_Expr_isConstOf(v___x_3324_, v___x_3325_);
lean_dec_ref(v___x_3324_);
if (v___x_3326_ == 0)
{
lean_dec_ref(v_arg_3321_);
lean_dec_ref(v_arg_3318_);
lean_dec_ref(v_arg_3315_);
lean_dec_ref(v_e_3296_);
goto v___jp_3308_;
}
else
{
lean_object* v___x_3327_; 
v___x_3327_ = l_Lean_Meta_Structural_isInstLEInt___redArg(v_arg_3321_, v_a_3304_);
if (lean_obj_tag(v___x_3327_) == 0)
{
lean_object* v_a_3328_; lean_object* v___x_3330_; uint8_t v_isShared_3331_; uint8_t v_isSharedCheck_3410_; 
v_a_3328_ = lean_ctor_get(v___x_3327_, 0);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3327_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3330_ = v___x_3327_;
v_isShared_3331_ = v_isSharedCheck_3410_;
goto v_resetjp_3329_;
}
else
{
lean_inc(v_a_3328_);
lean_dec(v___x_3327_);
v___x_3330_ = lean_box(0);
v_isShared_3331_ = v_isSharedCheck_3410_;
goto v_resetjp_3329_;
}
v_resetjp_3329_:
{
uint8_t v___x_3332_; 
v___x_3332_ = lean_unbox(v_a_3328_);
lean_dec(v_a_3328_);
if (v___x_3332_ == 0)
{
lean_object* v___x_3333_; lean_object* v___x_3335_; 
lean_dec_ref(v_arg_3318_);
lean_dec_ref(v_arg_3315_);
lean_dec_ref(v_e_3296_);
v___x_3333_ = lean_box(0);
if (v_isShared_3331_ == 0)
{
lean_ctor_set(v___x_3330_, 0, v___x_3333_);
v___x_3335_ = v___x_3330_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v___x_3333_);
v___x_3335_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
return v___x_3335_;
}
}
else
{
lean_object* v___x_3337_; 
lean_del_object(v___x_3330_);
v___x_3337_ = l_Lean_Meta_getIntValue_x3f(v_arg_3315_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_);
if (lean_obj_tag(v___x_3337_) == 0)
{
lean_object* v_a_3338_; 
v_a_3338_ = lean_ctor_get(v___x_3337_, 0);
lean_inc(v_a_3338_);
lean_dec_ref_known(v___x_3337_, 1);
if (lean_obj_tag(v_a_3338_) == 1)
{
lean_object* v_val_3339_; lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3383_; 
v_val_3339_ = lean_ctor_get(v_a_3338_, 0);
v_isSharedCheck_3383_ = !lean_is_exclusive(v_a_3338_);
if (v_isSharedCheck_3383_ == 0)
{
v___x_3341_ = v_a_3338_;
v_isShared_3342_ = v_isSharedCheck_3383_;
goto v_resetjp_3340_;
}
else
{
lean_inc(v_val_3339_);
lean_dec(v_a_3338_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3383_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
lean_object* v___x_3343_; uint8_t v___x_3344_; 
v___x_3343_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9);
v___x_3344_ = lean_int_dec_eq(v_val_3339_, v___x_3343_);
lean_dec(v_val_3339_);
if (v___x_3344_ == 0)
{
lean_object* v___x_3345_; 
lean_del_object(v___x_3341_);
lean_dec_ref(v_arg_3318_);
v___x_3345_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(v_e_3296_, v_a_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_);
if (lean_obj_tag(v___x_3345_) == 0)
{
lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3353_; 
v_isSharedCheck_3353_ = !lean_is_exclusive(v___x_3345_);
if (v_isSharedCheck_3353_ == 0)
{
lean_object* v_unused_3354_; 
v_unused_3354_ = lean_ctor_get(v___x_3345_, 0);
lean_dec(v_unused_3354_);
v___x_3347_ = v___x_3345_;
v_isShared_3348_ = v_isSharedCheck_3353_;
goto v_resetjp_3346_;
}
else
{
lean_dec(v___x_3345_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3353_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3349_; lean_object* v___x_3351_; 
v___x_3349_ = lean_box(0);
if (v_isShared_3348_ == 0)
{
lean_ctor_set(v___x_3347_, 0, v___x_3349_);
v___x_3351_ = v___x_3347_;
goto v_reusejp_3350_;
}
else
{
lean_object* v_reuseFailAlloc_3352_; 
v_reuseFailAlloc_3352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3352_, 0, v___x_3349_);
v___x_3351_ = v_reuseFailAlloc_3352_;
goto v_reusejp_3350_;
}
v_reusejp_3350_:
{
return v___x_3351_;
}
}
}
else
{
lean_object* v_a_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3362_; 
v_a_3355_ = lean_ctor_get(v___x_3345_, 0);
v_isSharedCheck_3362_ = !lean_is_exclusive(v___x_3345_);
if (v_isSharedCheck_3362_ == 0)
{
v___x_3357_ = v___x_3345_;
v_isShared_3358_ = v_isSharedCheck_3362_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_a_3355_);
lean_dec(v___x_3345_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3362_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
lean_object* v___x_3360_; 
if (v_isShared_3358_ == 0)
{
v___x_3360_ = v___x_3357_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v_a_3355_);
v___x_3360_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
return v___x_3360_;
}
}
}
}
else
{
lean_object* v___x_3363_; 
lean_dec_ref(v_e_3296_);
v___x_3363_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(v_arg_3318_, v_a_3297_, v_a_3298_, v_a_3299_, v_a_3300_, v_a_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_);
if (lean_obj_tag(v___x_3363_) == 0)
{
lean_object* v_a_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3374_; 
v_a_3364_ = lean_ctor_get(v___x_3363_, 0);
v_isSharedCheck_3374_ = !lean_is_exclusive(v___x_3363_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3366_ = v___x_3363_;
v_isShared_3367_ = v_isSharedCheck_3374_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_a_3364_);
lean_dec(v___x_3363_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3374_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v___x_3369_; 
if (v_isShared_3342_ == 0)
{
lean_ctor_set(v___x_3341_, 0, v_a_3364_);
v___x_3369_ = v___x_3341_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v_a_3364_);
v___x_3369_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
lean_object* v___x_3371_; 
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 0, v___x_3369_);
v___x_3371_ = v___x_3366_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v___x_3369_);
v___x_3371_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
return v___x_3371_;
}
}
}
}
else
{
lean_object* v_a_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3382_; 
lean_del_object(v___x_3341_);
v_a_3375_ = lean_ctor_get(v___x_3363_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3363_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3377_ = v___x_3363_;
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_a_3375_);
lean_dec(v___x_3363_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
lean_object* v___x_3380_; 
if (v_isShared_3378_ == 0)
{
v___x_3380_ = v___x_3377_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v_a_3375_);
v___x_3380_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
return v___x_3380_;
}
}
}
}
}
}
else
{
lean_object* v___x_3384_; 
lean_dec(v_a_3338_);
lean_dec_ref(v_arg_3318_);
v___x_3384_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_reportNonNormalized___redArg(v_e_3296_, v_a_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_);
if (lean_obj_tag(v___x_3384_) == 0)
{
lean_object* v___x_3386_; uint8_t v_isShared_3387_; uint8_t v_isSharedCheck_3392_; 
v_isSharedCheck_3392_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3392_ == 0)
{
lean_object* v_unused_3393_; 
v_unused_3393_ = lean_ctor_get(v___x_3384_, 0);
lean_dec(v_unused_3393_);
v___x_3386_ = v___x_3384_;
v_isShared_3387_ = v_isSharedCheck_3392_;
goto v_resetjp_3385_;
}
else
{
lean_dec(v___x_3384_);
v___x_3386_ = lean_box(0);
v_isShared_3387_ = v_isSharedCheck_3392_;
goto v_resetjp_3385_;
}
v_resetjp_3385_:
{
lean_object* v___x_3388_; lean_object* v___x_3390_; 
v___x_3388_ = lean_box(0);
if (v_isShared_3387_ == 0)
{
lean_ctor_set(v___x_3386_, 0, v___x_3388_);
v___x_3390_ = v___x_3386_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v___x_3388_);
v___x_3390_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
return v___x_3390_;
}
}
}
else
{
lean_object* v_a_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3401_; 
v_a_3394_ = lean_ctor_get(v___x_3384_, 0);
v_isSharedCheck_3401_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3401_ == 0)
{
v___x_3396_ = v___x_3384_;
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_a_3394_);
lean_dec(v___x_3384_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v___x_3399_; 
if (v_isShared_3397_ == 0)
{
v___x_3399_ = v___x_3396_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v_a_3394_);
v___x_3399_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
return v___x_3399_;
}
}
}
}
}
else
{
lean_object* v_a_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3409_; 
lean_dec_ref(v_arg_3318_);
lean_dec_ref(v_e_3296_);
v_a_3402_ = lean_ctor_get(v___x_3337_, 0);
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3337_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3404_ = v___x_3337_;
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_a_3402_);
lean_dec(v___x_3337_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v___x_3407_; 
if (v_isShared_3405_ == 0)
{
v___x_3407_ = v___x_3404_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_a_3402_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
}
}
}
}
}
}
else
{
lean_object* v_a_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3418_; 
lean_dec_ref(v_arg_3318_);
lean_dec_ref(v_arg_3315_);
lean_dec_ref(v_e_3296_);
v_a_3411_ = lean_ctor_get(v___x_3327_, 0);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3327_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3413_ = v___x_3327_;
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_a_3411_);
lean_dec(v___x_3327_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3416_; 
if (v_isShared_3414_ == 0)
{
v___x_3416_ = v___x_3413_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_a_3411_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
return v___x_3416_;
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
lean_object* v_a_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3426_; 
lean_dec_ref(v_e_3296_);
v_a_3419_ = lean_ctor_get(v___x_3311_, 0);
v_isSharedCheck_3426_ = !lean_is_exclusive(v___x_3311_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3421_ = v___x_3311_;
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_a_3419_);
lean_dec(v___x_3311_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v___x_3424_; 
if (v_isShared_3422_ == 0)
{
v___x_3424_ = v___x_3421_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v_a_3419_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
return v___x_3424_;
}
}
}
v___jp_3308_:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; 
v___x_3309_ = lean_box(0);
v___x_3310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3309_);
return v___x_3310_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___boxed(lean_object* v_e_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_, lean_object* v_a_3430_, lean_object* v_a_3431_, lean_object* v_a_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_){
_start:
{
lean_object* v_res_3439_; 
v_res_3439_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f(v_e_3427_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_, v_a_3437_);
lean_dec(v_a_3437_);
lean_dec_ref(v_a_3436_);
lean_dec(v_a_3435_);
lean_dec_ref(v_a_3434_);
lean_dec(v_a_3433_);
lean_dec_ref(v_a_3432_);
lean_dec(v_a_3431_);
lean_dec_ref(v_a_3430_);
lean_dec(v_a_3429_);
lean_dec(v_a_3428_);
return v_res_3439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(lean_object* v_c_3440_, lean_object* v_a_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_){
_start:
{
lean_object* v_p_3452_; lean_object* v___x_3453_; 
v_p_3452_ = lean_ctor_get(v_c_3440_, 0);
lean_inc_ref(v_p_3452_);
v___x_3453_ = l_Int_Internal_Linear_Poly_normCommRing_x3f(v_p_3452_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
if (lean_obj_tag(v___x_3453_) == 0)
{
lean_object* v_a_3454_; 
v_a_3454_ = lean_ctor_get(v___x_3453_, 0);
lean_inc(v_a_3454_);
lean_dec_ref_known(v___x_3453_, 1);
if (lean_obj_tag(v_a_3454_) == 1)
{
lean_object* v_val_3455_; lean_object* v_snd_3456_; lean_object* v_fst_3457_; lean_object* v_fst_3458_; lean_object* v_snd_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3468_; 
v_val_3455_ = lean_ctor_get(v_a_3454_, 0);
lean_inc(v_val_3455_);
lean_dec_ref_known(v_a_3454_, 1);
v_snd_3456_ = lean_ctor_get(v_val_3455_, 1);
lean_inc(v_snd_3456_);
v_fst_3457_ = lean_ctor_get(v_val_3455_, 0);
lean_inc(v_fst_3457_);
lean_dec(v_val_3455_);
v_fst_3458_ = lean_ctor_get(v_snd_3456_, 0);
v_snd_3459_ = lean_ctor_get(v_snd_3456_, 1);
v_isSharedCheck_3468_ = !lean_is_exclusive(v_snd_3456_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3461_ = v_snd_3456_;
v_isShared_3462_ = v_isSharedCheck_3468_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_snd_3459_);
lean_inc(v_fst_3458_);
lean_dec(v_snd_3456_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3468_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___x_3463_; lean_object* v___x_3465_; 
v___x_3463_ = lean_alloc_ctor(17, 3, 0);
lean_ctor_set(v___x_3463_, 0, v_c_3440_);
lean_ctor_set(v___x_3463_, 1, v_fst_3457_);
lean_ctor_set(v___x_3463_, 2, v_fst_3458_);
if (v_isShared_3462_ == 0)
{
lean_ctor_set(v___x_3461_, 1, v___x_3463_);
lean_ctor_set(v___x_3461_, 0, v_snd_3459_);
v___x_3465_ = v___x_3461_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_snd_3459_);
lean_ctor_set(v_reuseFailAlloc_3467_, 1, v___x_3463_);
v___x_3465_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
lean_object* v___x_3466_; 
lean_inc(v_a_3450_);
lean_inc_ref(v_a_3449_);
lean_inc(v_a_3448_);
lean_inc_ref(v_a_3447_);
lean_inc(v_a_3446_);
lean_inc_ref(v_a_3445_);
lean_inc(v_a_3444_);
lean_inc_ref(v_a_3443_);
lean_inc(v_a_3442_);
lean_inc(v_a_3441_);
v___x_3466_ = lean_grind_cutsat_assert_le(v___x_3465_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
return v___x_3466_;
}
}
}
else
{
lean_object* v___x_3469_; 
lean_dec(v_a_3454_);
lean_inc(v_a_3450_);
lean_inc_ref(v_a_3449_);
lean_inc(v_a_3448_);
lean_inc_ref(v_a_3447_);
lean_inc(v_a_3446_);
lean_inc_ref(v_a_3445_);
lean_inc(v_a_3444_);
lean_inc_ref(v_a_3443_);
lean_inc(v_a_3442_);
lean_inc(v_a_3441_);
v___x_3469_ = lean_grind_cutsat_assert_le(v_c_3440_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
return v___x_3469_;
}
}
else
{
lean_object* v_a_3470_; lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3477_; 
lean_dec_ref(v_c_3440_);
v_a_3470_ = lean_ctor_get(v___x_3453_, 0);
v_isSharedCheck_3477_ = !lean_is_exclusive(v___x_3453_);
if (v_isSharedCheck_3477_ == 0)
{
v___x_3472_ = v___x_3453_;
v_isShared_3473_ = v_isSharedCheck_3477_;
goto v_resetjp_3471_;
}
else
{
lean_inc(v_a_3470_);
lean_dec(v___x_3453_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore___boxed(lean_object* v_c_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_){
_start:
{
lean_object* v_res_3490_; 
v_res_3490_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v_c_3478_, v_a_3479_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_);
lean_dec(v_a_3488_);
lean_dec_ref(v_a_3487_);
lean_dec(v_a_3486_);
lean_dec_ref(v_a_3485_);
lean_dec(v_a_3484_);
lean_dec_ref(v_a_3483_);
lean_dec(v_a_3482_);
lean_dec_ref(v_a_3481_);
lean_dec(v_a_3480_);
lean_dec(v_a_3479_);
return v_res_3490_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0(void){
_start:
{
lean_object* v___x_3491_; lean_object* v___x_3492_; 
v___x_3491_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
v___x_3492_ = lean_int_neg(v___x_3491_);
return v___x_3492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe(lean_object* v_e_3493_, uint8_t v_eqTrue_3494_, lean_object* v_a_3495_, lean_object* v_a_3496_, lean_object* v_a_3497_, lean_object* v_a_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_, lean_object* v_a_3504_){
_start:
{
lean_object* v___x_3506_; 
lean_inc_ref(v_e_3493_);
v___x_3506_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f(v_e_3493_, v_a_3495_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_);
if (lean_obj_tag(v___x_3506_) == 0)
{
lean_object* v_a_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3533_; 
v_a_3507_ = lean_ctor_get(v___x_3506_, 0);
v_isSharedCheck_3533_ = !lean_is_exclusive(v___x_3506_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3509_ = v___x_3506_;
v_isShared_3510_ = v_isSharedCheck_3533_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_a_3507_);
lean_dec(v___x_3506_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3533_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
if (lean_obj_tag(v_a_3507_) == 1)
{
lean_del_object(v___x_3509_);
if (v_eqTrue_3494_ == 0)
{
lean_object* v_val_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; 
v_val_3511_ = lean_ctor_get(v_a_3507_, 0);
lean_inc_n(v_val_3511_, 2);
lean_dec_ref_known(v_a_3507_, 1);
v___x_3512_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
v___x_3513_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0);
v___x_3514_ = l_Int_Internal_Linear_Poly_mul(v_val_3511_, v___x_3513_);
v___x_3515_ = l_Int_Internal_Linear_Poly_addConst(v___x_3514_, v___x_3512_);
v___x_3516_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3516_, 0, v_e_3493_);
lean_ctor_set(v___x_3516_, 1, v_val_3511_);
v___x_3517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3517_, 0, v___x_3515_);
lean_ctor_set(v___x_3517_, 1, v___x_3516_);
v___x_3518_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v___x_3517_, v_a_3495_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_);
return v___x_3518_;
}
else
{
lean_object* v_val_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3528_; 
v_val_3519_ = lean_ctor_get(v_a_3507_, 0);
v_isSharedCheck_3528_ = !lean_is_exclusive(v_a_3507_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3521_ = v_a_3507_;
v_isShared_3522_ = v_isSharedCheck_3528_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_val_3519_);
lean_dec(v_a_3507_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3528_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
lean_object* v___x_3524_; 
if (v_isShared_3522_ == 0)
{
lean_ctor_set_tag(v___x_3521_, 0);
lean_ctor_set(v___x_3521_, 0, v_e_3493_);
v___x_3524_ = v___x_3521_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v_e_3493_);
v___x_3524_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
lean_object* v___x_3525_; lean_object* v___x_3526_; 
v___x_3525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3525_, 0, v_val_3519_);
lean_ctor_set(v___x_3525_, 1, v___x_3524_);
v___x_3526_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v___x_3525_, v_a_3495_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_);
return v___x_3526_;
}
}
}
}
else
{
lean_object* v___x_3529_; lean_object* v___x_3531_; 
lean_dec(v_a_3507_);
lean_dec_ref(v_e_3493_);
v___x_3529_ = lean_box(0);
if (v_isShared_3510_ == 0)
{
lean_ctor_set(v___x_3509_, 0, v___x_3529_);
v___x_3531_ = v___x_3509_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v___x_3529_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
return v___x_3531_;
}
}
}
}
else
{
lean_object* v_a_3534_; lean_object* v___x_3536_; uint8_t v_isShared_3537_; uint8_t v_isSharedCheck_3541_; 
lean_dec_ref(v_e_3493_);
v_a_3534_ = lean_ctor_get(v___x_3506_, 0);
v_isSharedCheck_3541_ = !lean_is_exclusive(v___x_3506_);
if (v_isSharedCheck_3541_ == 0)
{
v___x_3536_ = v___x_3506_;
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
else
{
lean_inc(v_a_3534_);
lean_dec(v___x_3506_);
v___x_3536_ = lean_box(0);
v_isShared_3537_ = v_isSharedCheck_3541_;
goto v_resetjp_3535_;
}
v_resetjp_3535_:
{
lean_object* v___x_3539_; 
if (v_isShared_3537_ == 0)
{
v___x_3539_ = v___x_3536_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v_a_3534_);
v___x_3539_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
return v___x_3539_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___boxed(lean_object* v_e_3542_, lean_object* v_eqTrue_3543_, lean_object* v_a_3544_, lean_object* v_a_3545_, lean_object* v_a_3546_, lean_object* v_a_3547_, lean_object* v_a_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_){
_start:
{
uint8_t v_eqTrue_boxed_3555_; lean_object* v_res_3556_; 
v_eqTrue_boxed_3555_ = lean_unbox(v_eqTrue_3543_);
v_res_3556_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe(v_e_3542_, v_eqTrue_boxed_3555_, v_a_3544_, v_a_3545_, v_a_3546_, v_a_3547_, v_a_3548_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_, v_a_3553_);
lean_dec(v_a_3553_);
lean_dec_ref(v_a_3552_);
lean_dec(v_a_3551_);
lean_dec_ref(v_a_3550_);
lean_dec(v_a_3549_);
lean_dec_ref(v_a_3548_);
lean_dec(v_a_3547_);
lean_dec_ref(v_a_3546_);
lean_dec(v_a_3545_);
lean_dec(v_a_3544_);
return v_res_3556_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0(void){
_start:
{
lean_object* v___x_3557_; lean_object* v___x_3558_; 
v___x_3557_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2);
v___x_3558_ = l_Lean_mkIntLit(v___x_3557_);
return v___x_3558_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5(void){
_start:
{
lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; 
v___x_3566_ = lean_box(0);
v___x_3567_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__4));
v___x_3568_ = l_Lean_mkConst(v___x_3567_, v___x_3566_);
return v___x_3568_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8(void){
_start:
{
lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; 
v___x_3574_ = lean_box(0);
v___x_3575_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__7));
v___x_3576_ = l_Lean_mkConst(v___x_3575_, v___x_3574_);
return v___x_3576_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe(lean_object* v_e_3577_, uint8_t v_eqTrue_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_, lean_object* v_a_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_){
_start:
{
lean_object* v___y_3591_; lean_object* v___y_3592_; lean_object* v_fst_3593_; lean_object* v_snd_3594_; lean_object* v___x_3623_; uint8_t v___x_3624_; 
lean_inc_ref(v_e_3577_);
v___x_3623_ = l_Lean_Expr_cleanupAnnotations(v_e_3577_);
v___x_3624_ = l_Lean_Expr_isApp(v___x_3623_);
if (v___x_3624_ == 0)
{
lean_dec_ref(v___x_3623_);
lean_dec_ref(v_e_3577_);
goto v___jp_3620_;
}
else
{
lean_object* v_arg_3625_; lean_object* v___x_3626_; uint8_t v___x_3627_; 
v_arg_3625_ = lean_ctor_get(v___x_3623_, 1);
lean_inc_ref(v_arg_3625_);
v___x_3626_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3623_);
v___x_3627_ = l_Lean_Expr_isApp(v___x_3626_);
if (v___x_3627_ == 0)
{
lean_dec_ref(v___x_3626_);
lean_dec_ref(v_arg_3625_);
lean_dec_ref(v_e_3577_);
goto v___jp_3620_;
}
else
{
lean_object* v_arg_3628_; lean_object* v___y_3630_; lean_object* v___x_3668_; uint8_t v___x_3669_; 
v_arg_3628_ = lean_ctor_get(v___x_3626_, 1);
lean_inc_ref(v_arg_3628_);
v___x_3668_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3626_);
v___x_3669_ = l_Lean_Expr_isApp(v___x_3668_);
if (v___x_3669_ == 0)
{
lean_dec_ref(v___x_3668_);
lean_dec_ref(v_arg_3628_);
lean_dec_ref(v_arg_3625_);
lean_dec_ref(v_e_3577_);
goto v___jp_3620_;
}
else
{
lean_object* v___x_3670_; uint8_t v___x_3671_; 
v___x_3670_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3668_);
v___x_3671_ = l_Lean_Expr_isApp(v___x_3670_);
if (v___x_3671_ == 0)
{
lean_dec_ref(v___x_3670_);
lean_dec_ref(v_arg_3628_);
lean_dec_ref(v_arg_3625_);
lean_dec_ref(v_e_3577_);
goto v___jp_3620_;
}
else
{
lean_object* v___x_3672_; lean_object* v___x_3673_; uint8_t v___x_3674_; 
v___x_3672_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3670_);
v___x_3673_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2));
v___x_3674_ = l_Lean_Expr_isConstOf(v___x_3672_, v___x_3673_);
lean_dec_ref(v___x_3672_);
if (v___x_3674_ == 0)
{
lean_dec_ref(v_arg_3628_);
lean_dec_ref(v_arg_3625_);
lean_dec_ref(v_e_3577_);
goto v___jp_3620_;
}
else
{
if (v_eqTrue_3578_ == 0)
{
lean_object* v___x_3675_; 
v___x_3675_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5);
v___y_3630_ = v___x_3675_;
goto v___jp_3629_;
}
else
{
lean_object* v___x_3676_; 
v___x_3676_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8);
v___y_3630_ = v___x_3676_;
goto v___jp_3629_;
}
}
}
}
v___jp_3629_:
{
lean_object* v___x_3631_; 
v___x_3631_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_3577_, v_a_3579_);
if (lean_obj_tag(v___x_3631_) == 0)
{
lean_object* v_a_3632_; lean_object* v___x_3633_; 
v_a_3632_ = lean_ctor_get(v___x_3631_, 0);
lean_inc(v_a_3632_);
lean_dec_ref_known(v___x_3631_, 1);
lean_inc_ref(v_arg_3628_);
v___x_3633_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_3628_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_, v_a_3585_, v_a_3586_, v_a_3587_, v_a_3588_);
if (lean_obj_tag(v___x_3633_) == 0)
{
lean_object* v_a_3634_; lean_object* v_fst_3635_; lean_object* v_snd_3636_; lean_object* v___x_3637_; 
v_a_3634_ = lean_ctor_get(v___x_3633_, 0);
lean_inc(v_a_3634_);
lean_dec_ref_known(v___x_3633_, 1);
v_fst_3635_ = lean_ctor_get(v_a_3634_, 0);
lean_inc(v_fst_3635_);
v_snd_3636_ = lean_ctor_get(v_a_3634_, 1);
lean_inc(v_snd_3636_);
lean_dec(v_a_3634_);
lean_inc_ref(v_arg_3625_);
v___x_3637_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_3625_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_, v_a_3585_, v_a_3586_, v_a_3587_, v_a_3588_);
if (lean_obj_tag(v___x_3637_) == 0)
{
lean_object* v_a_3638_; lean_object* v_fst_3639_; lean_object* v_snd_3640_; lean_object* v___x_3641_; 
v_a_3638_ = lean_ctor_get(v___x_3637_, 0);
lean_inc(v_a_3638_);
lean_dec_ref_known(v___x_3637_, 1);
v_fst_3639_ = lean_ctor_get(v_a_3638_, 0);
lean_inc_n(v_fst_3639_, 2);
v_snd_3640_ = lean_ctor_get(v_a_3638_, 1);
lean_inc(v_snd_3640_);
lean_dec(v_a_3638_);
lean_inc(v_fst_3635_);
lean_inc_ref(v___y_3630_);
v___x_3641_ = l_Lean_mkApp6(v___y_3630_, v_arg_3628_, v_arg_3625_, v_fst_3635_, v_fst_3639_, v_snd_3636_, v_snd_3640_);
if (v_eqTrue_3578_ == 0)
{
lean_object* v___x_3642_; lean_object* v___x_3643_; 
v___x_3642_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0);
v___x_3643_ = l_Lean_mkIntAdd(v_fst_3639_, v___x_3642_);
v___y_3591_ = v___x_3641_;
v___y_3592_ = v_a_3632_;
v_fst_3593_ = v___x_3643_;
v_snd_3594_ = v_fst_3635_;
goto v___jp_3590_;
}
else
{
v___y_3591_ = v___x_3641_;
v___y_3592_ = v_a_3632_;
v_fst_3593_ = v_fst_3635_;
v_snd_3594_ = v_fst_3639_;
goto v___jp_3590_;
}
}
else
{
lean_object* v_a_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3651_; 
lean_dec(v_snd_3636_);
lean_dec(v_fst_3635_);
lean_dec(v_a_3632_);
lean_dec_ref(v_arg_3628_);
lean_dec_ref(v_arg_3625_);
lean_dec_ref(v_e_3577_);
v_a_3644_ = lean_ctor_get(v___x_3637_, 0);
v_isSharedCheck_3651_ = !lean_is_exclusive(v___x_3637_);
if (v_isSharedCheck_3651_ == 0)
{
v___x_3646_ = v___x_3637_;
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_a_3644_);
lean_dec(v___x_3637_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v___x_3649_; 
if (v_isShared_3647_ == 0)
{
v___x_3649_ = v___x_3646_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v_a_3644_);
v___x_3649_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
return v___x_3649_;
}
}
}
}
else
{
lean_object* v_a_3652_; lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_3659_; 
lean_dec(v_a_3632_);
lean_dec_ref(v_arg_3628_);
lean_dec_ref(v_arg_3625_);
lean_dec_ref(v_e_3577_);
v_a_3652_ = lean_ctor_get(v___x_3633_, 0);
v_isSharedCheck_3659_ = !lean_is_exclusive(v___x_3633_);
if (v_isSharedCheck_3659_ == 0)
{
v___x_3654_ = v___x_3633_;
v_isShared_3655_ = v_isSharedCheck_3659_;
goto v_resetjp_3653_;
}
else
{
lean_inc(v_a_3652_);
lean_dec(v___x_3633_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_3659_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
lean_object* v___x_3657_; 
if (v_isShared_3655_ == 0)
{
v___x_3657_ = v___x_3654_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v_a_3652_);
v___x_3657_ = v_reuseFailAlloc_3658_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
return v___x_3657_;
}
}
}
}
else
{
lean_object* v_a_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3667_; 
lean_dec_ref(v_arg_3628_);
lean_dec_ref(v_arg_3625_);
lean_dec_ref(v_e_3577_);
v_a_3660_ = lean_ctor_get(v___x_3631_, 0);
v_isSharedCheck_3667_ = !lean_is_exclusive(v___x_3631_);
if (v_isSharedCheck_3667_ == 0)
{
v___x_3662_ = v___x_3631_;
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_a_3660_);
lean_dec(v___x_3631_);
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
}
v___jp_3590_:
{
lean_object* v___x_3595_; 
lean_inc(v___y_3592_);
v___x_3595_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_3593_, v___y_3592_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_, v_a_3585_, v_a_3586_, v_a_3587_, v_a_3588_);
if (lean_obj_tag(v___x_3595_) == 0)
{
lean_object* v_a_3596_; lean_object* v___x_3597_; 
v_a_3596_ = lean_ctor_get(v___x_3595_, 0);
lean_inc(v_a_3596_);
lean_dec_ref_known(v___x_3595_, 1);
v___x_3597_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_snd_3594_, v___y_3592_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_, v_a_3585_, v_a_3586_, v_a_3587_, v_a_3588_);
if (lean_obj_tag(v___x_3597_) == 0)
{
lean_object* v_a_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; 
v_a_3598_ = lean_ctor_get(v___x_3597_, 0);
lean_inc_n(v_a_3598_, 2);
lean_dec_ref_known(v___x_3597_, 1);
lean_inc(v_a_3596_);
v___x_3599_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3599_, 0, v_a_3596_);
lean_ctor_set(v___x_3599_, 1, v_a_3598_);
v___x_3600_ = l_Int_Internal_Linear_Expr_norm(v___x_3599_);
lean_dec_ref_known(v___x_3599_, 2);
v___x_3601_ = lean_alloc_ctor(2, 4, 1);
lean_ctor_set(v___x_3601_, 0, v_e_3577_);
lean_ctor_set(v___x_3601_, 1, v___y_3591_);
lean_ctor_set(v___x_3601_, 2, v_a_3596_);
lean_ctor_set(v___x_3601_, 3, v_a_3598_);
lean_ctor_set_uint8(v___x_3601_, sizeof(void*)*4, v_eqTrue_3578_);
v___x_3602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3602_, 0, v___x_3600_);
lean_ctor_set(v___x_3602_, 1, v___x_3601_);
v___x_3603_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v___x_3602_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_, v_a_3585_, v_a_3586_, v_a_3587_, v_a_3588_);
return v___x_3603_;
}
else
{
lean_object* v_a_3604_; lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3611_; 
lean_dec(v_a_3596_);
lean_dec_ref(v___y_3591_);
lean_dec_ref(v_e_3577_);
v_a_3604_ = lean_ctor_get(v___x_3597_, 0);
v_isSharedCheck_3611_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3611_ == 0)
{
v___x_3606_ = v___x_3597_;
v_isShared_3607_ = v_isSharedCheck_3611_;
goto v_resetjp_3605_;
}
else
{
lean_inc(v_a_3604_);
lean_dec(v___x_3597_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3611_;
goto v_resetjp_3605_;
}
v_resetjp_3605_:
{
lean_object* v___x_3609_; 
if (v_isShared_3607_ == 0)
{
v___x_3609_ = v___x_3606_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v_a_3604_);
v___x_3609_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
return v___x_3609_;
}
}
}
}
else
{
lean_object* v_a_3612_; lean_object* v___x_3614_; uint8_t v_isShared_3615_; uint8_t v_isSharedCheck_3619_; 
lean_dec_ref(v_snd_3594_);
lean_dec(v___y_3592_);
lean_dec_ref(v___y_3591_);
lean_dec_ref(v_e_3577_);
v_a_3612_ = lean_ctor_get(v___x_3595_, 0);
v_isSharedCheck_3619_ = !lean_is_exclusive(v___x_3595_);
if (v_isSharedCheck_3619_ == 0)
{
v___x_3614_ = v___x_3595_;
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
else
{
lean_inc(v_a_3612_);
lean_dec(v___x_3595_);
v___x_3614_ = lean_box(0);
v_isShared_3615_ = v_isSharedCheck_3619_;
goto v_resetjp_3613_;
}
v_resetjp_3613_:
{
lean_object* v___x_3617_; 
if (v_isShared_3615_ == 0)
{
v___x_3617_ = v___x_3614_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v_a_3612_);
v___x_3617_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
return v___x_3617_;
}
}
}
}
v___jp_3620_:
{
lean_object* v___x_3621_; lean_object* v___x_3622_; 
v___x_3621_ = lean_box(0);
v___x_3622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3622_, 0, v___x_3621_);
return v___x_3622_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___boxed(lean_object* v_e_3677_, lean_object* v_eqTrue_3678_, lean_object* v_a_3679_, lean_object* v_a_3680_, lean_object* v_a_3681_, lean_object* v_a_3682_, lean_object* v_a_3683_, lean_object* v_a_3684_, lean_object* v_a_3685_, lean_object* v_a_3686_, lean_object* v_a_3687_, lean_object* v_a_3688_, lean_object* v_a_3689_){
_start:
{
uint8_t v_eqTrue_boxed_3690_; lean_object* v_res_3691_; 
v_eqTrue_boxed_3690_ = lean_unbox(v_eqTrue_3678_);
v_res_3691_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe(v_e_3677_, v_eqTrue_boxed_3690_, v_a_3679_, v_a_3680_, v_a_3681_, v_a_3682_, v_a_3683_, v_a_3684_, v_a_3685_, v_a_3686_, v_a_3687_, v_a_3688_);
lean_dec(v_a_3688_);
lean_dec_ref(v_a_3687_);
lean_dec(v_a_3686_);
lean_dec_ref(v_a_3685_);
lean_dec(v_a_3684_);
lean_dec_ref(v_a_3683_);
lean_dec(v_a_3682_);
lean_dec_ref(v_a_3681_);
lean_dec(v_a_3680_);
lean_dec(v_a_3679_);
return v_res_3691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe(lean_object* v_e_3697_, uint8_t v_eqTrue_3698_, lean_object* v_a_3699_, lean_object* v_a_3700_, lean_object* v_a_3701_, lean_object* v_a_3702_, lean_object* v_a_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_, lean_object* v_a_3706_, lean_object* v_a_3707_, lean_object* v_a_3708_){
_start:
{
lean_object* v___x_3713_; 
v___x_3713_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3701_);
if (lean_obj_tag(v___x_3713_) == 0)
{
lean_object* v_a_3714_; lean_object* v___x_3716_; uint8_t v_isShared_3717_; uint8_t v_isSharedCheck_3745_; 
v_a_3714_ = lean_ctor_get(v___x_3713_, 0);
v_isSharedCheck_3745_ = !lean_is_exclusive(v___x_3713_);
if (v_isSharedCheck_3745_ == 0)
{
v___x_3716_ = v___x_3713_;
v_isShared_3717_ = v_isSharedCheck_3745_;
goto v_resetjp_3715_;
}
else
{
lean_inc(v_a_3714_);
lean_dec(v___x_3713_);
v___x_3716_ = lean_box(0);
v_isShared_3717_ = v_isSharedCheck_3745_;
goto v_resetjp_3715_;
}
v_resetjp_3715_:
{
uint8_t v_lia_3718_; 
v_lia_3718_ = lean_ctor_get_uint8(v_a_3714_, sizeof(void*)*14 + 23);
lean_dec(v_a_3714_);
if (v_lia_3718_ == 0)
{
lean_object* v___x_3719_; lean_object* v___x_3721_; 
lean_dec_ref(v_e_3697_);
v___x_3719_ = lean_box(0);
if (v_isShared_3717_ == 0)
{
lean_ctor_set(v___x_3716_, 0, v___x_3719_);
v___x_3721_ = v___x_3716_;
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
else
{
lean_object* v___x_3723_; uint8_t v___x_3724_; 
lean_inc_ref(v_e_3697_);
v___x_3723_ = l_Lean_Expr_cleanupAnnotations(v_e_3697_);
v___x_3724_ = l_Lean_Expr_isApp(v___x_3723_);
if (v___x_3724_ == 0)
{
lean_dec_ref(v___x_3723_);
lean_del_object(v___x_3716_);
lean_dec_ref(v_e_3697_);
goto v___jp_3710_;
}
else
{
lean_object* v___x_3725_; uint8_t v___x_3726_; 
v___x_3725_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3723_);
v___x_3726_ = l_Lean_Expr_isApp(v___x_3725_);
if (v___x_3726_ == 0)
{
lean_dec_ref(v___x_3725_);
lean_del_object(v___x_3716_);
lean_dec_ref(v_e_3697_);
goto v___jp_3710_;
}
else
{
lean_object* v___x_3727_; uint8_t v___x_3728_; 
v___x_3727_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3725_);
v___x_3728_ = l_Lean_Expr_isApp(v___x_3727_);
if (v___x_3728_ == 0)
{
lean_dec_ref(v___x_3727_);
lean_del_object(v___x_3716_);
lean_dec_ref(v_e_3697_);
goto v___jp_3710_;
}
else
{
lean_object* v___x_3729_; uint8_t v___x_3730_; 
v___x_3729_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3727_);
v___x_3730_ = l_Lean_Expr_isApp(v___x_3729_);
if (v___x_3730_ == 0)
{
lean_dec_ref(v___x_3729_);
lean_del_object(v___x_3716_);
lean_dec_ref(v_e_3697_);
goto v___jp_3710_;
}
else
{
lean_object* v_arg_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; uint8_t v___x_3734_; 
v_arg_3731_ = lean_ctor_get(v___x_3729_, 1);
lean_inc_ref(v_arg_3731_);
v___x_3732_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3729_);
v___x_3733_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_toPolyLe_x3f___closed__2));
v___x_3734_ = l_Lean_Expr_isConstOf(v___x_3732_, v___x_3733_);
lean_dec_ref(v___x_3732_);
if (v___x_3734_ == 0)
{
lean_dec_ref(v_arg_3731_);
lean_del_object(v___x_3716_);
lean_dec_ref(v_e_3697_);
goto v___jp_3710_;
}
else
{
lean_object* v___x_3735_; uint8_t v___x_3736_; 
v___x_3735_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__0));
v___x_3736_ = l_Lean_Expr_isConstOf(v_arg_3731_, v___x_3735_);
if (v___x_3736_ == 0)
{
lean_object* v___x_3737_; uint8_t v___x_3738_; 
v___x_3737_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__2));
v___x_3738_ = l_Lean_Expr_isConstOf(v_arg_3731_, v___x_3737_);
lean_dec_ref(v_arg_3731_);
if (v___x_3738_ == 0)
{
lean_object* v___x_3739_; lean_object* v___x_3741_; 
lean_dec_ref(v_e_3697_);
v___x_3739_ = lean_box(0);
if (v_isShared_3717_ == 0)
{
lean_ctor_set(v___x_3716_, 0, v___x_3739_);
v___x_3741_ = v___x_3716_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v___x_3739_);
v___x_3741_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
return v___x_3741_;
}
}
else
{
lean_object* v___x_3743_; 
lean_del_object(v___x_3716_);
v___x_3743_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe(v_e_3697_, v_eqTrue_3698_, v_a_3699_, v_a_3700_, v_a_3701_, v_a_3702_, v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_, v_a_3707_, v_a_3708_);
return v___x_3743_;
}
}
else
{
lean_object* v___x_3744_; 
lean_dec_ref(v_arg_3731_);
lean_del_object(v___x_3716_);
v___x_3744_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe(v_e_3697_, v_eqTrue_3698_, v_a_3699_, v_a_3700_, v_a_3701_, v_a_3702_, v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_, v_a_3707_, v_a_3708_);
return v___x_3744_;
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
lean_object* v_a_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3753_; 
lean_dec_ref(v_e_3697_);
v_a_3746_ = lean_ctor_get(v___x_3713_, 0);
v_isSharedCheck_3753_ = !lean_is_exclusive(v___x_3713_);
if (v_isSharedCheck_3753_ == 0)
{
v___x_3748_ = v___x_3713_;
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_a_3746_);
lean_dec(v___x_3713_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v___x_3751_; 
if (v_isShared_3749_ == 0)
{
v___x_3751_ = v___x_3748_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v_a_3746_);
v___x_3751_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
return v___x_3751_;
}
}
}
v___jp_3710_:
{
lean_object* v___x_3711_; lean_object* v___x_3712_; 
v___x_3711_ = lean_box(0);
v___x_3712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3712_, 0, v___x_3711_);
return v___x_3712_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___boxed(lean_object* v_e_3754_, lean_object* v_eqTrue_3755_, lean_object* v_a_3756_, lean_object* v_a_3757_, lean_object* v_a_3758_, lean_object* v_a_3759_, lean_object* v_a_3760_, lean_object* v_a_3761_, lean_object* v_a_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_){
_start:
{
uint8_t v_eqTrue_boxed_3767_; lean_object* v_res_3768_; 
v_eqTrue_boxed_3767_ = lean_unbox(v_eqTrue_3755_);
v_res_3768_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLe(v_e_3754_, v_eqTrue_boxed_3767_, v_a_3756_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_, v_a_3764_, v_a_3765_);
lean_dec(v_a_3765_);
lean_dec_ref(v_a_3764_);
lean_dec(v_a_3763_);
lean_dec_ref(v_a_3762_);
lean_dec(v_a_3761_);
lean_dec_ref(v_a_3760_);
lean_dec(v_a_3759_);
lean_dec_ref(v_a_3758_);
lean_dec(v_a_3757_);
lean_dec(v_a_3756_);
return v_res_3768_;
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
