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
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Int_Internal_Linear_instBEqPoly_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
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
lean_object* l_Lean_instInhabitedPersistentArray_default___redArg();
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_normCommRing_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_cutsat_assert_le(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Expr_norm(lean_object*);
lean_object* l_Int_Internal_Linear_Poly_mul(lean_object*, lean_object*);
lean_object* l_Int_Internal_Linear_Poly_addConst(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_Structural_isInstLEInt___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__1_value)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2_value;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "norm"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 115, 241, 203, 181, 236, 81, 221)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__2_value),LEAN_SCALAR_PTR_LITERAL(92, 174, 15, 22, 76, 124, 59, 78)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__1_value),LEAN_SCALAR_PTR_LITERAL(87, 130, 109, 65, 232, 6, 169, 172)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__1_value),LEAN_SCALAR_PTR_LITERAL(15, 182, 41, 28, 2, 115, 0, 31)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__3;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "not normalized: "};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__5;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__6_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__7_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__8_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__7_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__8_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "normalized: "};
static const lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__9_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__10;
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
v___x_17_ = lean_alloc_ctor(7, 1, 0);
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
v___x_12_ = lean_alloc_ctor(8, 1, 0);
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
v___x_148_ = lean_alloc_ctor(11, 3, 0);
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
size_t v_x_1573__boxed_501_; size_t v_x_1574__boxed_502_; lean_object* v_res_503_; 
v_x_1573__boxed_501_ = lean_unbox_usize(v_x_498_);
lean_dec(v_x_498_);
v_x_1574__boxed_502_ = lean_unbox_usize(v_x_499_);
lean_dec(v_x_499_);
v_res_503_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(v_c_496_, v_x_497_, v_x_1573__boxed_501_, v_x_1574__boxed_502_, v_x_500_);
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
size_t v_x_1700__boxed_601_; size_t v_x_1701__boxed_602_; lean_object* v_res_603_; 
v_x_1700__boxed_601_ = lean_unbox_usize(v_x_599_);
lean_dec(v_x_599_);
v_x_1701__boxed_602_ = lean_unbox_usize(v_x_600_);
lean_dec(v_x_600_);
v_res_603_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4(v_c_597_, v_x_598_, v_x_1700__boxed_601_, v_x_1701__boxed_602_);
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
lean_object* v_vars_647_; lean_object* v_varMap_648_; lean_object* v_varsHistory_649_; lean_object* v_natToIntMap_650_; lean_object* v_natDef_651_; lean_object* v_dvds_652_; lean_object* v_lowers_653_; lean_object* v_uppers_654_; lean_object* v_diseqs_655_; lean_object* v_elimEqs_656_; lean_object* v_elimStack_657_; lean_object* v_occurs_658_; lean_object* v_assignment_659_; lean_object* v_nextCnstrId_660_; uint8_t v_caseSplits_661_; lean_object* v_steps_662_; lean_object* v_penalties_663_; lean_object* v_numReorderRequests_664_; lean_object* v_conflict_x3f_665_; lean_object* v_diseqSplits_666_; lean_object* v_divMod_667_; uint8_t v_usedCommRing_668_; lean_object* v_nonlinearOccs_669_; lean_object* v___x_671_; uint8_t v_isShared_672_; uint8_t v_isSharedCheck_677_; 
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
v_caseSplits_661_ = lean_ctor_get_uint8(v_s_646_, sizeof(void*)*21);
v_steps_662_ = lean_ctor_get(v_s_646_, 14);
v_penalties_663_ = lean_ctor_get(v_s_646_, 15);
v_numReorderRequests_664_ = lean_ctor_get(v_s_646_, 16);
v_conflict_x3f_665_ = lean_ctor_get(v_s_646_, 17);
v_diseqSplits_666_ = lean_ctor_get(v_s_646_, 18);
v_divMod_667_ = lean_ctor_get(v_s_646_, 19);
v_usedCommRing_668_ = lean_ctor_get_uint8(v_s_646_, sizeof(void*)*21 + 1);
v_nonlinearOccs_669_ = lean_ctor_get(v_s_646_, 20);
v_isSharedCheck_677_ = !lean_is_exclusive(v_s_646_);
if (v_isSharedCheck_677_ == 0)
{
v___x_671_ = v_s_646_;
v_isShared_672_ = v_isSharedCheck_677_;
goto v_resetjp_670_;
}
else
{
lean_inc(v_nonlinearOccs_669_);
lean_inc(v_divMod_667_);
lean_inc(v_diseqSplits_666_);
lean_inc(v_conflict_x3f_665_);
lean_inc(v_numReorderRequests_664_);
lean_inc(v_penalties_663_);
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
v___x_671_ = lean_box(0);
v_isShared_672_ = v_isSharedCheck_677_;
goto v_resetjp_670_;
}
v_resetjp_670_:
{
lean_object* v___x_673_; lean_object* v___x_675_; 
v___x_673_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(v_c_644_, v_uppers_654_, v_v_645_);
if (v_isShared_672_ == 0)
{
lean_ctor_set(v___x_671_, 7, v___x_673_);
v___x_675_ = v___x_671_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(0, 21, 2);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_vars_647_);
lean_ctor_set(v_reuseFailAlloc_676_, 1, v_varMap_648_);
lean_ctor_set(v_reuseFailAlloc_676_, 2, v_varsHistory_649_);
lean_ctor_set(v_reuseFailAlloc_676_, 3, v_natToIntMap_650_);
lean_ctor_set(v_reuseFailAlloc_676_, 4, v_natDef_651_);
lean_ctor_set(v_reuseFailAlloc_676_, 5, v_dvds_652_);
lean_ctor_set(v_reuseFailAlloc_676_, 6, v_lowers_653_);
lean_ctor_set(v_reuseFailAlloc_676_, 7, v___x_673_);
lean_ctor_set(v_reuseFailAlloc_676_, 8, v_diseqs_655_);
lean_ctor_set(v_reuseFailAlloc_676_, 9, v_elimEqs_656_);
lean_ctor_set(v_reuseFailAlloc_676_, 10, v_elimStack_657_);
lean_ctor_set(v_reuseFailAlloc_676_, 11, v_occurs_658_);
lean_ctor_set(v_reuseFailAlloc_676_, 12, v_assignment_659_);
lean_ctor_set(v_reuseFailAlloc_676_, 13, v_nextCnstrId_660_);
lean_ctor_set(v_reuseFailAlloc_676_, 14, v_steps_662_);
lean_ctor_set(v_reuseFailAlloc_676_, 15, v_penalties_663_);
lean_ctor_set(v_reuseFailAlloc_676_, 16, v_numReorderRequests_664_);
lean_ctor_set(v_reuseFailAlloc_676_, 17, v_conflict_x3f_665_);
lean_ctor_set(v_reuseFailAlloc_676_, 18, v_diseqSplits_666_);
lean_ctor_set(v_reuseFailAlloc_676_, 19, v_divMod_667_);
lean_ctor_set(v_reuseFailAlloc_676_, 20, v_nonlinearOccs_669_);
lean_ctor_set_uint8(v_reuseFailAlloc_676_, sizeof(void*)*21, v_caseSplits_661_);
lean_ctor_set_uint8(v_reuseFailAlloc_676_, sizeof(void*)*21 + 1, v_usedCommRing_668_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___boxed(lean_object* v_c_678_, lean_object* v_v_679_, lean_object* v_s_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0(v_c_678_, v_v_679_, v_s_680_);
lean_dec(v_v_679_);
lean_dec_ref(v_c_678_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1(lean_object* v_c_682_, lean_object* v_v_683_, lean_object* v_s_684_){
_start:
{
lean_object* v_vars_685_; lean_object* v_varMap_686_; lean_object* v_varsHistory_687_; lean_object* v_natToIntMap_688_; lean_object* v_natDef_689_; lean_object* v_dvds_690_; lean_object* v_lowers_691_; lean_object* v_uppers_692_; lean_object* v_diseqs_693_; lean_object* v_elimEqs_694_; lean_object* v_elimStack_695_; lean_object* v_occurs_696_; lean_object* v_assignment_697_; lean_object* v_nextCnstrId_698_; uint8_t v_caseSplits_699_; lean_object* v_steps_700_; lean_object* v_penalties_701_; lean_object* v_numReorderRequests_702_; lean_object* v_conflict_x3f_703_; lean_object* v_diseqSplits_704_; lean_object* v_divMod_705_; uint8_t v_usedCommRing_706_; lean_object* v_nonlinearOccs_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_715_; 
v_vars_685_ = lean_ctor_get(v_s_684_, 0);
v_varMap_686_ = lean_ctor_get(v_s_684_, 1);
v_varsHistory_687_ = lean_ctor_get(v_s_684_, 2);
v_natToIntMap_688_ = lean_ctor_get(v_s_684_, 3);
v_natDef_689_ = lean_ctor_get(v_s_684_, 4);
v_dvds_690_ = lean_ctor_get(v_s_684_, 5);
v_lowers_691_ = lean_ctor_get(v_s_684_, 6);
v_uppers_692_ = lean_ctor_get(v_s_684_, 7);
v_diseqs_693_ = lean_ctor_get(v_s_684_, 8);
v_elimEqs_694_ = lean_ctor_get(v_s_684_, 9);
v_elimStack_695_ = lean_ctor_get(v_s_684_, 10);
v_occurs_696_ = lean_ctor_get(v_s_684_, 11);
v_assignment_697_ = lean_ctor_get(v_s_684_, 12);
v_nextCnstrId_698_ = lean_ctor_get(v_s_684_, 13);
v_caseSplits_699_ = lean_ctor_get_uint8(v_s_684_, sizeof(void*)*21);
v_steps_700_ = lean_ctor_get(v_s_684_, 14);
v_penalties_701_ = lean_ctor_get(v_s_684_, 15);
v_numReorderRequests_702_ = lean_ctor_get(v_s_684_, 16);
v_conflict_x3f_703_ = lean_ctor_get(v_s_684_, 17);
v_diseqSplits_704_ = lean_ctor_get(v_s_684_, 18);
v_divMod_705_ = lean_ctor_get(v_s_684_, 19);
v_usedCommRing_706_ = lean_ctor_get_uint8(v_s_684_, sizeof(void*)*21 + 1);
v_nonlinearOccs_707_ = lean_ctor_get(v_s_684_, 20);
v_isSharedCheck_715_ = !lean_is_exclusive(v_s_684_);
if (v_isSharedCheck_715_ == 0)
{
v___x_709_ = v_s_684_;
v_isShared_710_ = v_isSharedCheck_715_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_nonlinearOccs_707_);
lean_inc(v_divMod_705_);
lean_inc(v_diseqSplits_704_);
lean_inc(v_conflict_x3f_703_);
lean_inc(v_numReorderRequests_702_);
lean_inc(v_penalties_701_);
lean_inc(v_steps_700_);
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
lean_inc(v_varsHistory_687_);
lean_inc(v_varMap_686_);
lean_inc(v_vars_685_);
lean_dec(v_s_684_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_715_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_711_; lean_object* v___x_713_; 
v___x_711_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(v_c_682_, v_lowers_691_, v_v_683_);
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 6, v___x_711_);
v___x_713_ = v___x_709_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 21, 2);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v_vars_685_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v_varMap_686_);
lean_ctor_set(v_reuseFailAlloc_714_, 2, v_varsHistory_687_);
lean_ctor_set(v_reuseFailAlloc_714_, 3, v_natToIntMap_688_);
lean_ctor_set(v_reuseFailAlloc_714_, 4, v_natDef_689_);
lean_ctor_set(v_reuseFailAlloc_714_, 5, v_dvds_690_);
lean_ctor_set(v_reuseFailAlloc_714_, 6, v___x_711_);
lean_ctor_set(v_reuseFailAlloc_714_, 7, v_uppers_692_);
lean_ctor_set(v_reuseFailAlloc_714_, 8, v_diseqs_693_);
lean_ctor_set(v_reuseFailAlloc_714_, 9, v_elimEqs_694_);
lean_ctor_set(v_reuseFailAlloc_714_, 10, v_elimStack_695_);
lean_ctor_set(v_reuseFailAlloc_714_, 11, v_occurs_696_);
lean_ctor_set(v_reuseFailAlloc_714_, 12, v_assignment_697_);
lean_ctor_set(v_reuseFailAlloc_714_, 13, v_nextCnstrId_698_);
lean_ctor_set(v_reuseFailAlloc_714_, 14, v_steps_700_);
lean_ctor_set(v_reuseFailAlloc_714_, 15, v_penalties_701_);
lean_ctor_set(v_reuseFailAlloc_714_, 16, v_numReorderRequests_702_);
lean_ctor_set(v_reuseFailAlloc_714_, 17, v_conflict_x3f_703_);
lean_ctor_set(v_reuseFailAlloc_714_, 18, v_diseqSplits_704_);
lean_ctor_set(v_reuseFailAlloc_714_, 19, v_divMod_705_);
lean_ctor_set(v_reuseFailAlloc_714_, 20, v_nonlinearOccs_707_);
lean_ctor_set_uint8(v_reuseFailAlloc_714_, sizeof(void*)*21, v_caseSplits_699_);
lean_ctor_set_uint8(v_reuseFailAlloc_714_, sizeof(void*)*21 + 1, v_usedCommRing_706_);
v___x_713_ = v_reuseFailAlloc_714_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
return v___x_713_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1___boxed(lean_object* v_c_716_, lean_object* v_v_717_, lean_object* v_s_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1(v_c_716_, v_v_717_, v_s_718_);
lean_dec(v_v_717_);
lean_dec_ref(v_c_716_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(lean_object* v_c_720_, lean_object* v_a_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_){
_start:
{
lean_object* v_p_727_; 
v_p_727_ = lean_ctor_get(v_c_720_, 0);
if (lean_obj_tag(v_p_727_) == 1)
{
lean_object* v_k_728_; lean_object* v_v_729_; lean_object* v___x_730_; uint8_t v___x_731_; 
v_k_728_ = lean_ctor_get(v_p_727_, 0);
v_v_729_ = lean_ctor_get(v_p_727_, 1);
lean_inc(v_v_729_);
v___x_730_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9);
v___x_731_ = lean_int_dec_lt(v_k_728_, v___x_730_);
if (v___x_731_ == 0)
{
lean_object* v___f_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___f_732_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_732_, 0, v_c_720_);
lean_closure_set(v___f_732_, 1, v_v_729_);
v___x_733_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_734_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_733_, v___f_732_, v_a_721_);
return v___x_734_;
}
else
{
lean_object* v___f_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___f_735_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_735_, 0, v_c_720_);
lean_closure_set(v___f_735_, 1, v_v_729_);
v___x_736_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_737_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_736_, v___f_735_, v_a_721_);
return v___x_737_;
}
}
else
{
lean_object* v___x_738_; 
v___x_738_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_720_, v_a_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_);
return v___x_738_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___boxed(lean_object* v_c_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_c_739_, v_a_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_);
lean_dec(v_a_744_);
lean_dec_ref(v_a_743_);
lean_dec(v_a_742_);
lean_dec_ref(v_a_741_);
lean_dec(v_a_740_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase(lean_object* v_c_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_c_747_, v_a_748_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___boxed(lean_object* v_c_760_, lean_object* v_a_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase(v_c_760_, v_a_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_);
lean_dec(v_a_770_);
lean_dec_ref(v_a_769_);
lean_dec(v_a_768_);
lean_dec_ref(v_a_767_);
lean_dec(v_a_766_);
lean_dec_ref(v_a_765_);
lean_dec(v_a_764_);
lean_dec_ref(v_a_763_);
lean_dec(v_a_762_);
lean_dec(v_a_761_);
return v_res_772_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5(void){
_start:
{
lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_786_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_787_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_788_ = l_Lean_Name_append(v___x_787_, v___x_786_);
return v___x_788_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7(void){
_start:
{
lean_object* v___x_790_; lean_object* v___x_791_; 
v___x_790_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__6));
v___x_791_ = l_Lean_stringToMessageData(v___x_790_);
return v___x_791_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3(lean_object* v_c_792_, lean_object* v_as_793_, size_t v_sz_794_, size_t v_i_795_, lean_object* v_b_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
uint8_t v___x_808_; 
v___x_808_ = lean_usize_dec_lt(v_i_795_, v_sz_794_);
if (v___x_808_ == 0)
{
lean_object* v___x_809_; 
lean_dec_ref(v_c_792_);
v___x_809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_809_, 0, v_b_796_);
return v___x_809_;
}
else
{
lean_object* v_snd_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_898_; 
v_snd_810_ = lean_ctor_get(v_b_796_, 1);
v_isSharedCheck_898_ = !lean_is_exclusive(v_b_796_);
if (v_isSharedCheck_898_ == 0)
{
lean_object* v_unused_899_; 
v_unused_899_ = lean_ctor_get(v_b_796_, 0);
lean_dec(v_unused_899_);
v___x_812_ = v_b_796_;
v_isShared_813_ = v_isSharedCheck_898_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_snd_810_);
lean_dec(v_b_796_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_898_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v_p_814_; lean_object* v_a_815_; lean_object* v_p_816_; lean_object* v___x_817_; uint8_t v___x_818_; 
v_p_814_ = lean_ctor_get(v_c_792_, 0);
v_a_815_ = lean_array_uget_borrowed(v_as_793_, v_i_795_);
v_p_816_ = lean_ctor_get(v_a_815_, 0);
v___x_817_ = lean_box(0);
v___x_818_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_814_, v_p_816_);
if (v___x_818_ == 0)
{
lean_object* v___x_819_; size_t v___x_820_; size_t v___x_821_; 
lean_del_object(v___x_812_);
lean_dec(v_snd_810_);
v___x_819_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__1));
v___x_820_ = ((size_t)1ULL);
v___x_821_ = lean_usize_add(v_i_795_, v___x_820_);
v_i_795_ = v___x_821_;
v_b_796_ = v___x_819_;
goto _start;
}
else
{
lean_object* v___x_823_; 
lean_inc_ref(v_p_814_);
lean_inc(v_a_815_);
v___x_823_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_815_, v___y_797_, v___y_803_, v___y_804_, v___y_805_, v___y_806_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_toCold_824_; lean_object* v_options_825_; lean_object* v_inheritedTraceOptions_826_; uint8_t v_hasTrace_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v___y_840_; 
lean_dec_ref_known(v___x_823_, 1);
v_toCold_824_ = lean_ctor_get(v___y_805_, 0);
v_options_825_ = lean_ctor_get(v_toCold_824_, 2);
v_inheritedTraceOptions_826_ = lean_ctor_get(v_toCold_824_, 11);
v_hasTrace_827_ = lean_ctor_get_uint8(v_options_825_, sizeof(void*)*1);
lean_inc(v_a_815_);
v___x_828_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_828_, 0, v_c_792_);
lean_ctor_set(v___x_828_, 1, v_a_815_);
v___x_829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_829_, 0, v_p_814_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
if (v_hasTrace_827_ == 0)
{
v___y_831_ = v___y_797_;
v___y_832_ = v___y_798_;
v___y_833_ = v___y_799_;
v___y_834_ = v___y_800_;
v___y_835_ = v___y_801_;
v___y_836_ = v___y_802_;
v___y_837_ = v___y_803_;
v___y_838_ = v___y_804_;
v___y_839_ = v___y_805_;
v___y_840_ = v___y_806_;
goto v___jp_830_;
}
else
{
lean_object* v___x_866_; lean_object* v___x_867_; uint8_t v___x_868_; 
v___x_866_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_867_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5);
v___x_868_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_826_, v_options_825_, v___x_867_);
if (v___x_868_ == 0)
{
v___y_831_ = v___y_797_;
v___y_832_ = v___y_798_;
v___y_833_ = v___y_799_;
v___y_834_ = v___y_800_;
v___y_835_ = v___y_801_;
v___y_836_ = v___y_802_;
v___y_837_ = v___y_803_;
v___y_838_ = v___y_804_;
v___y_839_ = v___y_805_;
v___y_840_ = v___y_806_;
goto v___jp_830_;
}
else
{
lean_object* v___x_869_; 
lean_inc_ref(v___x_829_);
v___x_869_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_829_, v___y_797_, v___y_805_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v_a_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; 
v_a_870_ = lean_ctor_get(v___x_869_, 0);
lean_inc(v_a_870_);
lean_dec_ref_known(v___x_869_, 1);
v___x_871_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7);
v___x_872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_872_, 0, v___x_871_);
lean_ctor_set(v___x_872_, 1, v_a_870_);
v___x_873_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_866_, v___x_872_, v___y_803_, v___y_804_, v___y_805_, v___y_806_);
if (lean_obj_tag(v___x_873_) == 0)
{
lean_dec_ref_known(v___x_873_, 1);
v___y_831_ = v___y_797_;
v___y_832_ = v___y_798_;
v___y_833_ = v___y_799_;
v___y_834_ = v___y_800_;
v___y_835_ = v___y_801_;
v___y_836_ = v___y_802_;
v___y_837_ = v___y_803_;
v___y_838_ = v___y_804_;
v___y_839_ = v___y_805_;
v___y_840_ = v___y_806_;
goto v___jp_830_;
}
else
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_881_; 
lean_dec_ref_known(v___x_829_, 2);
lean_del_object(v___x_812_);
lean_dec(v_snd_810_);
v_a_874_ = lean_ctor_get(v___x_873_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_873_);
if (v_isSharedCheck_881_ == 0)
{
v___x_876_ = v___x_873_;
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_873_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_879_; 
if (v_isShared_877_ == 0)
{
v___x_879_ = v___x_876_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_a_874_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
else
{
lean_object* v_a_882_; lean_object* v___x_884_; uint8_t v_isShared_885_; uint8_t v_isSharedCheck_889_; 
lean_dec_ref_known(v___x_829_, 2);
lean_del_object(v___x_812_);
lean_dec(v_snd_810_);
v_a_882_ = lean_ctor_get(v___x_869_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v___x_869_);
if (v_isSharedCheck_889_ == 0)
{
v___x_884_ = v___x_869_;
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
else
{
lean_inc(v_a_882_);
lean_dec(v___x_869_);
v___x_884_ = lean_box(0);
v_isShared_885_ = v_isSharedCheck_889_;
goto v_resetjp_883_;
}
v_resetjp_883_:
{
lean_object* v___x_887_; 
if (v_isShared_885_ == 0)
{
v___x_887_ = v___x_884_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v_a_882_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
}
v___jp_830_:
{
lean_object* v___x_841_; 
lean_inc(v___y_840_);
lean_inc_ref(v___y_839_);
lean_inc(v___y_838_);
lean_inc_ref(v___y_837_);
lean_inc(v___y_836_);
lean_inc_ref(v___y_835_);
lean_inc(v___y_834_);
lean_inc_ref(v___y_833_);
lean_inc(v___y_832_);
lean_inc(v___y_831_);
v___x_841_ = lean_grind_cutsat_assert_eq(v___x_829_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_856_; 
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_856_ == 0)
{
lean_object* v_unused_857_; 
v_unused_857_ = lean_ctor_get(v___x_841_, 0);
lean_dec(v_unused_857_);
v___x_843_ = v___x_841_;
v_isShared_844_ = v_isSharedCheck_856_;
goto v_resetjp_842_;
}
else
{
lean_dec(v___x_841_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_856_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_848_; 
v___x_845_ = lean_box(v___x_818_);
v___x_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_846_, 0, v___x_845_);
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 1, v___x_817_);
lean_ctor_set(v___x_812_, 0, v___x_846_);
v___x_848_ = v___x_812_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_846_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v___x_817_);
v___x_848_ = v_reuseFailAlloc_855_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_853_; 
v___x_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
v___x_850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_850_, 0, v___x_849_);
v___x_851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
lean_ctor_set(v___x_851_, 1, v_snd_810_);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 0, v___x_851_);
v___x_853_ = v___x_843_;
goto v_reusejp_852_;
}
else
{
lean_object* v_reuseFailAlloc_854_; 
v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_854_, 0, v___x_851_);
v___x_853_ = v_reuseFailAlloc_854_;
goto v_reusejp_852_;
}
v_reusejp_852_:
{
return v___x_853_;
}
}
}
}
else
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_865_; 
lean_del_object(v___x_812_);
lean_dec(v_snd_810_);
v_a_858_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_865_ == 0)
{
v___x_860_ = v___x_841_;
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_841_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_861_ == 0)
{
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_858_);
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
}
else
{
lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_897_; 
lean_dec_ref(v_p_814_);
lean_del_object(v___x_812_);
lean_dec(v_snd_810_);
lean_dec_ref(v_c_792_);
v_a_890_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_897_ == 0)
{
v___x_892_ = v___x_823_;
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v___x_823_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_895_; 
if (v_isShared_893_ == 0)
{
v___x_895_ = v___x_892_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_a_890_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_c_900_, lean_object* v_as_901_, lean_object* v_sz_902_, lean_object* v_i_903_, lean_object* v_b_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_){
_start:
{
size_t v_sz_boxed_916_; size_t v_i_boxed_917_; lean_object* v_res_918_; 
v_sz_boxed_916_ = lean_unbox_usize(v_sz_902_);
lean_dec(v_sz_902_);
v_i_boxed_917_ = lean_unbox_usize(v_i_903_);
lean_dec(v_i_903_);
v_res_918_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3(v_c_900_, v_as_901_, v_sz_boxed_916_, v_i_boxed_917_, v_b_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec(v___y_912_);
lean_dec_ref(v___y_911_);
lean_dec(v___y_910_);
lean_dec_ref(v___y_909_);
lean_dec(v___y_908_);
lean_dec_ref(v___y_907_);
lean_dec(v___y_906_);
lean_dec(v___y_905_);
lean_dec_ref(v_as_901_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2(lean_object* v_c_925_, lean_object* v_as_926_, size_t v_sz_927_, size_t v_i_928_, lean_object* v_b_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
uint8_t v___x_941_; 
v___x_941_ = lean_usize_dec_lt(v_i_928_, v_sz_927_);
if (v___x_941_ == 0)
{
lean_object* v___x_942_; 
lean_dec_ref(v_c_925_);
v___x_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_942_, 0, v_b_929_);
return v___x_942_;
}
else
{
lean_object* v_snd_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_1031_; 
v_snd_943_ = lean_ctor_get(v_b_929_, 1);
v_isSharedCheck_1031_ = !lean_is_exclusive(v_b_929_);
if (v_isSharedCheck_1031_ == 0)
{
lean_object* v_unused_1032_; 
v_unused_1032_ = lean_ctor_get(v_b_929_, 0);
lean_dec(v_unused_1032_);
v___x_945_ = v_b_929_;
v_isShared_946_ = v_isSharedCheck_1031_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_snd_943_);
lean_dec(v_b_929_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_1031_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v_p_947_; lean_object* v_a_948_; lean_object* v_p_949_; lean_object* v___x_950_; uint8_t v___x_951_; 
v_p_947_ = lean_ctor_get(v_c_925_, 0);
v_a_948_ = lean_array_uget_borrowed(v_as_926_, v_i_928_);
v_p_949_ = lean_ctor_get(v_a_948_, 0);
v___x_950_ = lean_box(0);
v___x_951_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_947_, v_p_949_);
if (v___x_951_ == 0)
{
lean_object* v___x_952_; size_t v___x_953_; size_t v___x_954_; lean_object* v___x_955_; 
lean_del_object(v___x_945_);
lean_dec(v_snd_943_);
v___x_952_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__1));
v___x_953_ = ((size_t)1ULL);
v___x_954_ = lean_usize_add(v_i_928_, v___x_953_);
v___x_955_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3(v_c_925_, v_as_926_, v_sz_927_, v___x_954_, v___x_952_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
return v___x_955_;
}
else
{
lean_object* v___x_956_; 
lean_inc_ref(v_p_947_);
lean_inc(v_a_948_);
v___x_956_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_948_, v___y_930_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
if (lean_obj_tag(v___x_956_) == 0)
{
lean_object* v_toCold_957_; lean_object* v_options_958_; lean_object* v_inheritedTraceOptions_959_; uint8_t v_hasTrace_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___y_964_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v___y_967_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; 
lean_dec_ref_known(v___x_956_, 1);
v_toCold_957_ = lean_ctor_get(v___y_938_, 0);
v_options_958_ = lean_ctor_get(v_toCold_957_, 2);
v_inheritedTraceOptions_959_ = lean_ctor_get(v_toCold_957_, 11);
v_hasTrace_960_ = lean_ctor_get_uint8(v_options_958_, sizeof(void*)*1);
lean_inc(v_a_948_);
v___x_961_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_961_, 0, v_c_925_);
lean_ctor_set(v___x_961_, 1, v_a_948_);
v___x_962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_962_, 0, v_p_947_);
lean_ctor_set(v___x_962_, 1, v___x_961_);
if (v_hasTrace_960_ == 0)
{
v___y_964_ = v___y_930_;
v___y_965_ = v___y_931_;
v___y_966_ = v___y_932_;
v___y_967_ = v___y_933_;
v___y_968_ = v___y_934_;
v___y_969_ = v___y_935_;
v___y_970_ = v___y_936_;
v___y_971_ = v___y_937_;
v___y_972_ = v___y_938_;
v___y_973_ = v___y_939_;
goto v___jp_963_;
}
else
{
lean_object* v___x_999_; lean_object* v___x_1000_; uint8_t v___x_1001_; 
v___x_999_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_1000_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5);
v___x_1001_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_959_, v_options_958_, v___x_1000_);
if (v___x_1001_ == 0)
{
v___y_964_ = v___y_930_;
v___y_965_ = v___y_931_;
v___y_966_ = v___y_932_;
v___y_967_ = v___y_933_;
v___y_968_ = v___y_934_;
v___y_969_ = v___y_935_;
v___y_970_ = v___y_936_;
v___y_971_ = v___y_937_;
v___y_972_ = v___y_938_;
v___y_973_ = v___y_939_;
goto v___jp_963_;
}
else
{
lean_object* v___x_1002_; 
lean_inc_ref(v___x_962_);
v___x_1002_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_962_, v___y_930_, v___y_938_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
lean_inc(v_a_1003_);
lean_dec_ref_known(v___x_1002_, 1);
v___x_1004_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7);
v___x_1005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_1004_);
lean_ctor_set(v___x_1005_, 1, v_a_1003_);
v___x_1006_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_999_, v___x_1005_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
if (lean_obj_tag(v___x_1006_) == 0)
{
lean_dec_ref_known(v___x_1006_, 1);
v___y_964_ = v___y_930_;
v___y_965_ = v___y_931_;
v___y_966_ = v___y_932_;
v___y_967_ = v___y_933_;
v___y_968_ = v___y_934_;
v___y_969_ = v___y_935_;
v___y_970_ = v___y_936_;
v___y_971_ = v___y_937_;
v___y_972_ = v___y_938_;
v___y_973_ = v___y_939_;
goto v___jp_963_;
}
else
{
lean_object* v_a_1007_; lean_object* v___x_1009_; uint8_t v_isShared_1010_; uint8_t v_isSharedCheck_1014_; 
lean_dec_ref_known(v___x_962_, 2);
lean_del_object(v___x_945_);
lean_dec(v_snd_943_);
v_a_1007_ = lean_ctor_get(v___x_1006_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_1006_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1009_ = v___x_1006_;
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
else
{
lean_inc(v_a_1007_);
lean_dec(v___x_1006_);
v___x_1009_ = lean_box(0);
v_isShared_1010_ = v_isSharedCheck_1014_;
goto v_resetjp_1008_;
}
v_resetjp_1008_:
{
lean_object* v___x_1012_; 
if (v_isShared_1010_ == 0)
{
v___x_1012_ = v___x_1009_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_a_1007_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
lean_dec_ref_known(v___x_962_, 2);
lean_del_object(v___x_945_);
lean_dec(v_snd_943_);
v_a_1015_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_1002_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_1002_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1015_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
}
v___jp_963_:
{
lean_object* v___x_974_; 
lean_inc(v___y_973_);
lean_inc_ref(v___y_972_);
lean_inc(v___y_971_);
lean_inc_ref(v___y_970_);
lean_inc(v___y_969_);
lean_inc_ref(v___y_968_);
lean_inc(v___y_967_);
lean_inc_ref(v___y_966_);
lean_inc(v___y_965_);
lean_inc(v___y_964_);
v___x_974_ = lean_grind_cutsat_assert_eq(v___x_962_, v___y_964_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_989_; 
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_989_ == 0)
{
lean_object* v_unused_990_; 
v_unused_990_ = lean_ctor_get(v___x_974_, 0);
lean_dec(v_unused_990_);
v___x_976_ = v___x_974_;
v_isShared_977_ = v_isSharedCheck_989_;
goto v_resetjp_975_;
}
else
{
lean_dec(v___x_974_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_989_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_981_; 
v___x_978_ = lean_box(v___x_951_);
v___x_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_979_, 0, v___x_978_);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 1, v___x_950_);
lean_ctor_set(v___x_945_, 0, v___x_979_);
v___x_981_ = v___x_945_;
goto v_reusejp_980_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v___x_979_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v___x_950_);
v___x_981_ = v_reuseFailAlloc_988_;
goto v_reusejp_980_;
}
v_reusejp_980_:
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_986_; 
v___x_982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_982_, 0, v___x_981_);
v___x_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
v___x_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
lean_ctor_set(v___x_984_, 1, v_snd_943_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 0, v___x_984_);
v___x_986_ = v___x_976_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v___x_984_);
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
lean_object* v_a_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_998_; 
lean_del_object(v___x_945_);
lean_dec(v_snd_943_);
v_a_991_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_998_ == 0)
{
v___x_993_ = v___x_974_;
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_a_991_);
lean_dec(v___x_974_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_998_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_996_; 
if (v_isShared_994_ == 0)
{
v___x_996_ = v___x_993_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
}
}
else
{
lean_object* v_a_1023_; lean_object* v___x_1025_; uint8_t v_isShared_1026_; uint8_t v_isSharedCheck_1030_; 
lean_dec_ref(v_p_947_);
lean_del_object(v___x_945_);
lean_dec(v_snd_943_);
lean_dec_ref(v_c_925_);
v_a_1023_ = lean_ctor_get(v___x_956_, 0);
v_isSharedCheck_1030_ = !lean_is_exclusive(v___x_956_);
if (v_isSharedCheck_1030_ == 0)
{
v___x_1025_ = v___x_956_;
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
else
{
lean_inc(v_a_1023_);
lean_dec(v___x_956_);
v___x_1025_ = lean_box(0);
v_isShared_1026_ = v_isSharedCheck_1030_;
goto v_resetjp_1024_;
}
v_resetjp_1024_:
{
lean_object* v___x_1028_; 
if (v_isShared_1026_ == 0)
{
v___x_1028_ = v___x_1025_;
goto v_reusejp_1027_;
}
else
{
lean_object* v_reuseFailAlloc_1029_; 
v_reuseFailAlloc_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1029_, 0, v_a_1023_);
v___x_1028_ = v_reuseFailAlloc_1029_;
goto v_reusejp_1027_;
}
v_reusejp_1027_:
{
return v___x_1028_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___boxed(lean_object* v_c_1033_, lean_object* v_as_1034_, lean_object* v_sz_1035_, lean_object* v_i_1036_, lean_object* v_b_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
size_t v_sz_boxed_1049_; size_t v_i_boxed_1050_; lean_object* v_res_1051_; 
v_sz_boxed_1049_ = lean_unbox_usize(v_sz_1035_);
lean_dec(v_sz_1035_);
v_i_boxed_1050_ = lean_unbox_usize(v_i_1036_);
lean_dec(v_i_1036_);
v_res_1051_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2(v_c_1033_, v_as_1034_, v_sz_boxed_1049_, v_i_boxed_1050_, v_b_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v___y_1039_);
lean_dec(v___y_1038_);
lean_dec_ref(v_as_1034_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(lean_object* v_init_1052_, lean_object* v_c_1053_, lean_object* v_n_1054_, lean_object* v_b_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_){
_start:
{
if (lean_obj_tag(v_n_1054_) == 0)
{
lean_object* v_cs_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; size_t v_sz_1070_; size_t v___x_1071_; lean_object* v___x_1072_; 
v_cs_1067_ = lean_ctor_get(v_n_1054_, 0);
v___x_1068_ = lean_box(0);
v___x_1069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1068_);
lean_ctor_set(v___x_1069_, 1, v_b_1055_);
v_sz_1070_ = lean_array_size(v_cs_1067_);
v___x_1071_ = ((size_t)0ULL);
v___x_1072_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(v_init_1052_, v_c_1053_, v_cs_1067_, v_sz_1070_, v___x_1071_, v___x_1069_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
if (lean_obj_tag(v___x_1072_) == 0)
{
lean_object* v_a_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1087_; 
v_a_1073_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1087_ == 0)
{
v___x_1075_ = v___x_1072_;
v_isShared_1076_ = v_isSharedCheck_1087_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_a_1073_);
lean_dec(v___x_1072_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1087_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v_fst_1077_; 
v_fst_1077_ = lean_ctor_get(v_a_1073_, 0);
if (lean_obj_tag(v_fst_1077_) == 0)
{
lean_object* v_snd_1078_; lean_object* v___x_1079_; lean_object* v___x_1081_; 
v_snd_1078_ = lean_ctor_get(v_a_1073_, 1);
lean_inc(v_snd_1078_);
lean_dec(v_a_1073_);
v___x_1079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1079_, 0, v_snd_1078_);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 0, v___x_1079_);
v___x_1081_ = v___x_1075_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1082_; 
v_reuseFailAlloc_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1082_, 0, v___x_1079_);
v___x_1081_ = v_reuseFailAlloc_1082_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
return v___x_1081_;
}
}
else
{
lean_object* v_val_1083_; lean_object* v___x_1085_; 
lean_inc_ref(v_fst_1077_);
lean_dec(v_a_1073_);
v_val_1083_ = lean_ctor_get(v_fst_1077_, 0);
lean_inc(v_val_1083_);
lean_dec_ref_known(v_fst_1077_, 1);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 0, v_val_1083_);
v___x_1085_ = v___x_1075_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v_val_1083_);
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
lean_object* v_a_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1095_; 
v_a_1088_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1090_ = v___x_1072_;
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_a_1088_);
lean_dec(v___x_1072_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1095_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1093_; 
if (v_isShared_1091_ == 0)
{
v___x_1093_ = v___x_1090_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v_a_1088_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
}
else
{
lean_object* v_vs_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; size_t v_sz_1099_; size_t v___x_1100_; lean_object* v___x_1101_; 
v_vs_1096_ = lean_ctor_get(v_n_1054_, 0);
v___x_1097_ = lean_box(0);
v___x_1098_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1097_);
lean_ctor_set(v___x_1098_, 1, v_b_1055_);
v_sz_1099_ = lean_array_size(v_vs_1096_);
v___x_1100_ = ((size_t)0ULL);
v___x_1101_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2(v_c_1053_, v_vs_1096_, v_sz_1099_, v___x_1100_, v___x_1098_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_);
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1116_; 
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1104_ = v___x_1101_;
v_isShared_1105_ = v_isSharedCheck_1116_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1101_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1116_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v_fst_1106_; 
v_fst_1106_ = lean_ctor_get(v_a_1102_, 0);
if (lean_obj_tag(v_fst_1106_) == 0)
{
lean_object* v_snd_1107_; lean_object* v___x_1108_; lean_object* v___x_1110_; 
v_snd_1107_ = lean_ctor_get(v_a_1102_, 1);
lean_inc(v_snd_1107_);
lean_dec(v_a_1102_);
v___x_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1108_, 0, v_snd_1107_);
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 0, v___x_1108_);
v___x_1110_ = v___x_1104_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v___x_1108_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
else
{
lean_object* v_val_1112_; lean_object* v___x_1114_; 
lean_inc_ref(v_fst_1106_);
lean_dec(v_a_1102_);
v_val_1112_ = lean_ctor_get(v_fst_1106_, 0);
lean_inc(v_val_1112_);
lean_dec_ref_known(v_fst_1106_, 1);
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 0, v_val_1112_);
v___x_1114_ = v___x_1104_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_val_1112_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
}
else
{
lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1124_; 
v_a_1117_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1119_ = v___x_1101_;
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_1101_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1122_; 
if (v_isShared_1120_ == 0)
{
v___x_1122_ = v___x_1119_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_a_1117_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(lean_object* v_init_1125_, lean_object* v_c_1126_, lean_object* v_as_1127_, size_t v_sz_1128_, size_t v_i_1129_, lean_object* v_b_1130_, lean_object* v___y_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_){
_start:
{
uint8_t v___x_1142_; 
v___x_1142_ = lean_usize_dec_lt(v_i_1129_, v_sz_1128_);
if (v___x_1142_ == 0)
{
lean_object* v___x_1143_; 
lean_dec_ref(v_c_1126_);
v___x_1143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1143_, 0, v_b_1130_);
return v___x_1143_;
}
else
{
lean_object* v_snd_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1178_; 
v_snd_1144_ = lean_ctor_get(v_b_1130_, 1);
v_isSharedCheck_1178_ = !lean_is_exclusive(v_b_1130_);
if (v_isSharedCheck_1178_ == 0)
{
lean_object* v_unused_1179_; 
v_unused_1179_ = lean_ctor_get(v_b_1130_, 0);
lean_dec(v_unused_1179_);
v___x_1146_ = v_b_1130_;
v_isShared_1147_ = v_isSharedCheck_1178_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_snd_1144_);
lean_dec(v_b_1130_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1178_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v___x_1148_; lean_object* v_a_1149_; lean_object* v___x_1150_; 
v___x_1148_ = lean_box(0);
v_a_1149_ = lean_array_uget_borrowed(v_as_1127_, v_i_1129_);
lean_inc(v_snd_1144_);
lean_inc_ref(v_c_1126_);
v___x_1150_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(v_init_1125_, v_c_1126_, v_a_1149_, v_snd_1144_, v___y_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1169_; 
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1169_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1153_ = v___x_1150_;
v_isShared_1154_ = v_isSharedCheck_1169_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1150_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1169_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
if (lean_obj_tag(v_a_1151_) == 0)
{
lean_object* v___x_1155_; lean_object* v___x_1157_; 
lean_dec_ref(v_c_1126_);
v___x_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1155_, 0, v_a_1151_);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 0, v___x_1155_);
v___x_1157_ = v___x_1146_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1155_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v_snd_1144_);
v___x_1157_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
lean_object* v___x_1159_; 
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 0, v___x_1157_);
v___x_1159_ = v___x_1153_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v___x_1157_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
else
{
lean_object* v_a_1162_; lean_object* v___x_1164_; 
lean_del_object(v___x_1153_);
lean_dec(v_snd_1144_);
v_a_1162_ = lean_ctor_get(v_a_1151_, 0);
lean_inc(v_a_1162_);
lean_dec_ref_known(v_a_1151_, 1);
if (v_isShared_1147_ == 0)
{
lean_ctor_set(v___x_1146_, 1, v_a_1162_);
lean_ctor_set(v___x_1146_, 0, v___x_1148_);
v___x_1164_ = v___x_1146_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v___x_1148_);
lean_ctor_set(v_reuseFailAlloc_1168_, 1, v_a_1162_);
v___x_1164_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
size_t v___x_1165_; size_t v___x_1166_; 
v___x_1165_ = ((size_t)1ULL);
v___x_1166_ = lean_usize_add(v_i_1129_, v___x_1165_);
v_i_1129_ = v___x_1166_;
v_b_1130_ = v___x_1164_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1177_; 
lean_del_object(v___x_1146_);
lean_dec(v_snd_1144_);
lean_dec_ref(v_c_1126_);
v_a_1170_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1177_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1172_ = v___x_1150_;
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_a_1170_);
lean_dec(v___x_1150_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1177_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1175_; 
if (v_isShared_1173_ == 0)
{
v___x_1175_ = v___x_1172_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_a_1170_);
v___x_1175_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
return v___x_1175_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_init_1180_ = _args[0];
lean_object* v_c_1181_ = _args[1];
lean_object* v_as_1182_ = _args[2];
lean_object* v_sz_1183_ = _args[3];
lean_object* v_i_1184_ = _args[4];
lean_object* v_b_1185_ = _args[5];
lean_object* v___y_1186_ = _args[6];
lean_object* v___y_1187_ = _args[7];
lean_object* v___y_1188_ = _args[8];
lean_object* v___y_1189_ = _args[9];
lean_object* v___y_1190_ = _args[10];
lean_object* v___y_1191_ = _args[11];
lean_object* v___y_1192_ = _args[12];
lean_object* v___y_1193_ = _args[13];
lean_object* v___y_1194_ = _args[14];
lean_object* v___y_1195_ = _args[15];
lean_object* v___y_1196_ = _args[16];
_start:
{
size_t v_sz_boxed_1197_; size_t v_i_boxed_1198_; lean_object* v_res_1199_; 
v_sz_boxed_1197_ = lean_unbox_usize(v_sz_1183_);
lean_dec(v_sz_1183_);
v_i_boxed_1198_ = lean_unbox_usize(v_i_1184_);
lean_dec(v_i_1184_);
v_res_1199_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(v_init_1180_, v_c_1181_, v_as_1182_, v_sz_boxed_1197_, v_i_boxed_1198_, v_b_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec_ref(v_as_1182_);
lean_dec_ref(v_init_1180_);
return v_res_1199_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___boxed(lean_object* v_init_1200_, lean_object* v_c_1201_, lean_object* v_n_1202_, lean_object* v_b_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(v_init_1200_, v_c_1201_, v_n_1202_, v_b_1203_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
lean_dec(v___y_1209_);
lean_dec_ref(v___y_1208_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec_ref(v_n_1202_);
lean_dec_ref(v_init_1200_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4(lean_object* v_c_1222_, lean_object* v_as_1223_, size_t v_sz_1224_, size_t v_i_1225_, lean_object* v_b_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
uint8_t v___x_1238_; 
v___x_1238_ = lean_usize_dec_lt(v_i_1225_, v_sz_1224_);
if (v___x_1238_ == 0)
{
lean_object* v___x_1239_; 
lean_dec_ref(v_c_1222_);
v___x_1239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1239_, 0, v_b_1226_);
return v___x_1239_;
}
else
{
lean_object* v_snd_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1327_; 
v_snd_1240_ = lean_ctor_get(v_b_1226_, 1);
v_isSharedCheck_1327_ = !lean_is_exclusive(v_b_1226_);
if (v_isSharedCheck_1327_ == 0)
{
lean_object* v_unused_1328_; 
v_unused_1328_ = lean_ctor_get(v_b_1226_, 0);
lean_dec(v_unused_1328_);
v___x_1242_ = v_b_1226_;
v_isShared_1243_ = v_isSharedCheck_1327_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_snd_1240_);
lean_dec(v_b_1226_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1327_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v_p_1244_; lean_object* v_a_1245_; lean_object* v_p_1246_; lean_object* v___x_1247_; uint8_t v___x_1248_; 
v_p_1244_ = lean_ctor_get(v_c_1222_, 0);
v_a_1245_ = lean_array_uget_borrowed(v_as_1223_, v_i_1225_);
v_p_1246_ = lean_ctor_get(v_a_1245_, 0);
v___x_1247_ = lean_box(0);
v___x_1248_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_1244_, v_p_1246_);
if (v___x_1248_ == 0)
{
lean_object* v___x_1249_; size_t v___x_1250_; size_t v___x_1251_; 
lean_del_object(v___x_1242_);
lean_dec(v_snd_1240_);
v___x_1249_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___closed__1));
v___x_1250_ = ((size_t)1ULL);
v___x_1251_ = lean_usize_add(v_i_1225_, v___x_1250_);
v_i_1225_ = v___x_1251_;
v_b_1226_ = v___x_1249_;
goto _start;
}
else
{
lean_object* v___x_1253_; 
lean_inc_ref(v_p_1244_);
lean_inc(v_a_1245_);
v___x_1253_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_1245_, v___y_1227_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_toCold_1254_; lean_object* v_options_1255_; lean_object* v_inheritedTraceOptions_1256_; uint8_t v_hasTrace_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___y_1261_; lean_object* v___y_1262_; lean_object* v___y_1263_; lean_object* v___y_1264_; lean_object* v___y_1265_; lean_object* v___y_1266_; lean_object* v___y_1267_; lean_object* v___y_1268_; lean_object* v___y_1269_; lean_object* v___y_1270_; 
lean_dec_ref_known(v___x_1253_, 1);
v_toCold_1254_ = lean_ctor_get(v___y_1235_, 0);
v_options_1255_ = lean_ctor_get(v_toCold_1254_, 2);
v_inheritedTraceOptions_1256_ = lean_ctor_get(v_toCold_1254_, 11);
v_hasTrace_1257_ = lean_ctor_get_uint8(v_options_1255_, sizeof(void*)*1);
lean_inc(v_a_1245_);
v___x_1258_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1258_, 0, v_c_1222_);
lean_ctor_set(v___x_1258_, 1, v_a_1245_);
v___x_1259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1259_, 0, v_p_1244_);
lean_ctor_set(v___x_1259_, 1, v___x_1258_);
if (v_hasTrace_1257_ == 0)
{
v___y_1261_ = v___y_1227_;
v___y_1262_ = v___y_1228_;
v___y_1263_ = v___y_1229_;
v___y_1264_ = v___y_1230_;
v___y_1265_ = v___y_1231_;
v___y_1266_ = v___y_1232_;
v___y_1267_ = v___y_1233_;
v___y_1268_ = v___y_1234_;
v___y_1269_ = v___y_1235_;
v___y_1270_ = v___y_1236_;
goto v___jp_1260_;
}
else
{
lean_object* v___x_1295_; lean_object* v___x_1296_; uint8_t v___x_1297_; 
v___x_1295_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_1296_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5);
v___x_1297_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1256_, v_options_1255_, v___x_1296_);
if (v___x_1297_ == 0)
{
v___y_1261_ = v___y_1227_;
v___y_1262_ = v___y_1228_;
v___y_1263_ = v___y_1229_;
v___y_1264_ = v___y_1230_;
v___y_1265_ = v___y_1231_;
v___y_1266_ = v___y_1232_;
v___y_1267_ = v___y_1233_;
v___y_1268_ = v___y_1234_;
v___y_1269_ = v___y_1235_;
v___y_1270_ = v___y_1236_;
goto v___jp_1260_;
}
else
{
lean_object* v___x_1298_; 
lean_inc_ref(v___x_1259_);
v___x_1298_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_1259_, v___y_1227_, v___y_1235_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v_a_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; 
v_a_1299_ = lean_ctor_get(v___x_1298_, 0);
lean_inc(v_a_1299_);
lean_dec_ref_known(v___x_1298_, 1);
v___x_1300_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7);
v___x_1301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1300_);
lean_ctor_set(v___x_1301_, 1, v_a_1299_);
v___x_1302_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_1295_, v___x_1301_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
if (lean_obj_tag(v___x_1302_) == 0)
{
lean_dec_ref_known(v___x_1302_, 1);
v___y_1261_ = v___y_1227_;
v___y_1262_ = v___y_1228_;
v___y_1263_ = v___y_1229_;
v___y_1264_ = v___y_1230_;
v___y_1265_ = v___y_1231_;
v___y_1266_ = v___y_1232_;
v___y_1267_ = v___y_1233_;
v___y_1268_ = v___y_1234_;
v___y_1269_ = v___y_1235_;
v___y_1270_ = v___y_1236_;
goto v___jp_1260_;
}
else
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1310_; 
lean_dec_ref_known(v___x_1259_, 2);
lean_del_object(v___x_1242_);
lean_dec(v_snd_1240_);
v_a_1303_ = lean_ctor_get(v___x_1302_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1302_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1305_ = v___x_1302_;
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1302_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1308_; 
if (v_isShared_1306_ == 0)
{
v___x_1308_ = v___x_1305_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_a_1303_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
}
else
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1318_; 
lean_dec_ref_known(v___x_1259_, 2);
lean_del_object(v___x_1242_);
lean_dec(v_snd_1240_);
v_a_1311_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1313_ = v___x_1298_;
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1298_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
if (v_isShared_1314_ == 0)
{
v___x_1316_ = v___x_1313_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_a_1311_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
}
}
v___jp_1260_:
{
lean_object* v___x_1271_; 
lean_inc(v___y_1270_);
lean_inc_ref(v___y_1269_);
lean_inc(v___y_1268_);
lean_inc_ref(v___y_1267_);
lean_inc(v___y_1266_);
lean_inc_ref(v___y_1265_);
lean_inc(v___y_1264_);
lean_inc_ref(v___y_1263_);
lean_inc(v___y_1262_);
lean_inc(v___y_1261_);
v___x_1271_ = lean_grind_cutsat_assert_eq(v___x_1259_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1285_; 
v_isSharedCheck_1285_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1285_ == 0)
{
lean_object* v_unused_1286_; 
v_unused_1286_ = lean_ctor_get(v___x_1271_, 0);
lean_dec(v_unused_1286_);
v___x_1273_ = v___x_1271_;
v_isShared_1274_ = v_isSharedCheck_1285_;
goto v_resetjp_1272_;
}
else
{
lean_dec(v___x_1271_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1285_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1278_; 
v___x_1275_ = lean_box(v___x_1248_);
v___x_1276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1276_, 0, v___x_1275_);
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 1, v___x_1247_);
lean_ctor_set(v___x_1242_, 0, v___x_1276_);
v___x_1278_ = v___x_1242_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v___x_1276_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v___x_1247_);
v___x_1278_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1282_; 
v___x_1279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1279_, 0, v___x_1278_);
v___x_1280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1279_);
lean_ctor_set(v___x_1280_, 1, v_snd_1240_);
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 0, v___x_1280_);
v___x_1282_ = v___x_1273_;
goto v_reusejp_1281_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1280_);
v___x_1282_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1281_;
}
v_reusejp_1281_:
{
return v___x_1282_;
}
}
}
}
else
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1294_; 
lean_del_object(v___x_1242_);
lean_dec(v_snd_1240_);
v_a_1287_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1289_ = v___x_1271_;
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1271_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1294_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
lean_object* v___x_1292_; 
if (v_isShared_1290_ == 0)
{
v___x_1292_ = v___x_1289_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_a_1287_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
}
else
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
lean_dec_ref(v_p_1244_);
lean_del_object(v___x_1242_);
lean_dec(v_snd_1240_);
lean_dec_ref(v_c_1222_);
v_a_1319_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1321_ = v___x_1253_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1253_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; 
if (v_isShared_1322_ == 0)
{
v___x_1324_ = v___x_1321_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_a_1319_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___boxed(lean_object* v_c_1329_, lean_object* v_as_1330_, lean_object* v_sz_1331_, lean_object* v_i_1332_, lean_object* v_b_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
size_t v_sz_boxed_1345_; size_t v_i_boxed_1346_; lean_object* v_res_1347_; 
v_sz_boxed_1345_ = lean_unbox_usize(v_sz_1331_);
lean_dec(v_sz_1331_);
v_i_boxed_1346_ = lean_unbox_usize(v_i_1332_);
lean_dec(v_i_1332_);
v_res_1347_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4(v_c_1329_, v_as_1330_, v_sz_boxed_1345_, v_i_boxed_1346_, v_b_1333_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1335_);
lean_dec(v___y_1334_);
lean_dec_ref(v_as_1330_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1(lean_object* v_c_1351_, lean_object* v_as_1352_, size_t v_sz_1353_, size_t v_i_1354_, lean_object* v_b_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
uint8_t v___x_1367_; 
v___x_1367_ = lean_usize_dec_lt(v_i_1354_, v_sz_1353_);
if (v___x_1367_ == 0)
{
lean_object* v___x_1368_; 
lean_dec_ref(v_c_1351_);
v___x_1368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1368_, 0, v_b_1355_);
return v___x_1368_;
}
else
{
lean_object* v_snd_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1456_; 
v_snd_1369_ = lean_ctor_get(v_b_1355_, 1);
v_isSharedCheck_1456_ = !lean_is_exclusive(v_b_1355_);
if (v_isSharedCheck_1456_ == 0)
{
lean_object* v_unused_1457_; 
v_unused_1457_ = lean_ctor_get(v_b_1355_, 0);
lean_dec(v_unused_1457_);
v___x_1371_ = v_b_1355_;
v_isShared_1372_ = v_isSharedCheck_1456_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_snd_1369_);
lean_dec(v_b_1355_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1456_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v_p_1373_; lean_object* v_a_1374_; lean_object* v_p_1375_; lean_object* v___x_1376_; uint8_t v___x_1377_; 
v_p_1373_ = lean_ctor_get(v_c_1351_, 0);
v_a_1374_ = lean_array_uget_borrowed(v_as_1352_, v_i_1354_);
v_p_1375_ = lean_ctor_get(v_a_1374_, 0);
v___x_1376_ = lean_box(0);
v___x_1377_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_1373_, v_p_1375_);
if (v___x_1377_ == 0)
{
lean_object* v___x_1378_; size_t v___x_1379_; size_t v___x_1380_; lean_object* v___x_1381_; 
lean_del_object(v___x_1371_);
lean_dec(v_snd_1369_);
v___x_1378_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1___closed__0));
v___x_1379_ = ((size_t)1ULL);
v___x_1380_ = lean_usize_add(v_i_1354_, v___x_1379_);
v___x_1381_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4(v_c_1351_, v_as_1352_, v_sz_1353_, v___x_1380_, v___x_1378_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
return v___x_1381_;
}
else
{
lean_object* v___x_1382_; 
lean_inc_ref(v_p_1373_);
lean_inc(v_a_1374_);
v___x_1382_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_1374_, v___y_1356_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
if (lean_obj_tag(v___x_1382_) == 0)
{
lean_object* v_toCold_1383_; lean_object* v_options_1384_; lean_object* v_inheritedTraceOptions_1385_; uint8_t v_hasTrace_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1398_; lean_object* v___y_1399_; 
lean_dec_ref_known(v___x_1382_, 1);
v_toCold_1383_ = lean_ctor_get(v___y_1364_, 0);
v_options_1384_ = lean_ctor_get(v_toCold_1383_, 2);
v_inheritedTraceOptions_1385_ = lean_ctor_get(v_toCold_1383_, 11);
v_hasTrace_1386_ = lean_ctor_get_uint8(v_options_1384_, sizeof(void*)*1);
lean_inc(v_a_1374_);
v___x_1387_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1387_, 0, v_c_1351_);
lean_ctor_set(v___x_1387_, 1, v_a_1374_);
v___x_1388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1388_, 0, v_p_1373_);
lean_ctor_set(v___x_1388_, 1, v___x_1387_);
if (v_hasTrace_1386_ == 0)
{
v___y_1390_ = v___y_1356_;
v___y_1391_ = v___y_1357_;
v___y_1392_ = v___y_1358_;
v___y_1393_ = v___y_1359_;
v___y_1394_ = v___y_1360_;
v___y_1395_ = v___y_1361_;
v___y_1396_ = v___y_1362_;
v___y_1397_ = v___y_1363_;
v___y_1398_ = v___y_1364_;
v___y_1399_ = v___y_1365_;
goto v___jp_1389_;
}
else
{
lean_object* v___x_1424_; lean_object* v___x_1425_; uint8_t v___x_1426_; 
v___x_1424_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_1425_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5);
v___x_1426_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1385_, v_options_1384_, v___x_1425_);
if (v___x_1426_ == 0)
{
v___y_1390_ = v___y_1356_;
v___y_1391_ = v___y_1357_;
v___y_1392_ = v___y_1358_;
v___y_1393_ = v___y_1359_;
v___y_1394_ = v___y_1360_;
v___y_1395_ = v___y_1361_;
v___y_1396_ = v___y_1362_;
v___y_1397_ = v___y_1363_;
v___y_1398_ = v___y_1364_;
v___y_1399_ = v___y_1365_;
goto v___jp_1389_;
}
else
{
lean_object* v___x_1427_; 
lean_inc_ref(v___x_1388_);
v___x_1427_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_1388_, v___y_1356_, v___y_1364_);
if (lean_obj_tag(v___x_1427_) == 0)
{
lean_object* v_a_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
lean_inc(v_a_1428_);
lean_dec_ref_known(v___x_1427_, 1);
v___x_1429_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7);
v___x_1430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1429_);
lean_ctor_set(v___x_1430_, 1, v_a_1428_);
v___x_1431_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_1424_, v___x_1430_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
if (lean_obj_tag(v___x_1431_) == 0)
{
lean_dec_ref_known(v___x_1431_, 1);
v___y_1390_ = v___y_1356_;
v___y_1391_ = v___y_1357_;
v___y_1392_ = v___y_1358_;
v___y_1393_ = v___y_1359_;
v___y_1394_ = v___y_1360_;
v___y_1395_ = v___y_1361_;
v___y_1396_ = v___y_1362_;
v___y_1397_ = v___y_1363_;
v___y_1398_ = v___y_1364_;
v___y_1399_ = v___y_1365_;
goto v___jp_1389_;
}
else
{
lean_object* v_a_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1439_; 
lean_dec_ref_known(v___x_1388_, 2);
lean_del_object(v___x_1371_);
lean_dec(v_snd_1369_);
v_a_1432_ = lean_ctor_get(v___x_1431_, 0);
v_isSharedCheck_1439_ = !lean_is_exclusive(v___x_1431_);
if (v_isSharedCheck_1439_ == 0)
{
v___x_1434_ = v___x_1431_;
v_isShared_1435_ = v_isSharedCheck_1439_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_a_1432_);
lean_dec(v___x_1431_);
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
lean_dec_ref_known(v___x_1388_, 2);
lean_del_object(v___x_1371_);
lean_dec(v_snd_1369_);
v_a_1440_ = lean_ctor_get(v___x_1427_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1427_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1442_ = v___x_1427_;
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1427_);
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
v___jp_1389_:
{
lean_object* v___x_1400_; 
lean_inc(v___y_1399_);
lean_inc_ref(v___y_1398_);
lean_inc(v___y_1397_);
lean_inc_ref(v___y_1396_);
lean_inc(v___y_1395_);
lean_inc_ref(v___y_1394_);
lean_inc(v___y_1393_);
lean_inc_ref(v___y_1392_);
lean_inc(v___y_1391_);
lean_inc(v___y_1390_);
v___x_1400_ = lean_grind_cutsat_assert_eq(v___x_1388_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
if (lean_obj_tag(v___x_1400_) == 0)
{
lean_object* v___x_1402_; uint8_t v_isShared_1403_; uint8_t v_isSharedCheck_1414_; 
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1414_ == 0)
{
lean_object* v_unused_1415_; 
v_unused_1415_ = lean_ctor_get(v___x_1400_, 0);
lean_dec(v_unused_1415_);
v___x_1402_ = v___x_1400_;
v_isShared_1403_ = v_isSharedCheck_1414_;
goto v_resetjp_1401_;
}
else
{
lean_dec(v___x_1400_);
v___x_1402_ = lean_box(0);
v_isShared_1403_ = v_isSharedCheck_1414_;
goto v_resetjp_1401_;
}
v_resetjp_1401_:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1407_; 
v___x_1404_ = lean_box(v___x_1377_);
v___x_1405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1405_, 0, v___x_1404_);
if (v_isShared_1372_ == 0)
{
lean_ctor_set(v___x_1371_, 1, v___x_1376_);
lean_ctor_set(v___x_1371_, 0, v___x_1405_);
v___x_1407_ = v___x_1371_;
goto v_reusejp_1406_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v___x_1405_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v___x_1376_);
v___x_1407_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1406_;
}
v_reusejp_1406_:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1411_; 
v___x_1408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1408_, 0, v___x_1407_);
v___x_1409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1408_);
lean_ctor_set(v___x_1409_, 1, v_snd_1369_);
if (v_isShared_1403_ == 0)
{
lean_ctor_set(v___x_1402_, 0, v___x_1409_);
v___x_1411_ = v___x_1402_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v___x_1409_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
}
else
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1423_; 
lean_del_object(v___x_1371_);
lean_dec(v_snd_1369_);
v_a_1416_ = lean_ctor_get(v___x_1400_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1400_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1418_ = v___x_1400_;
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1400_);
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
}
else
{
lean_object* v_a_1448_; lean_object* v___x_1450_; uint8_t v_isShared_1451_; uint8_t v_isSharedCheck_1455_; 
lean_dec_ref(v_p_1373_);
lean_del_object(v___x_1371_);
lean_dec(v_snd_1369_);
lean_dec_ref(v_c_1351_);
v_a_1448_ = lean_ctor_get(v___x_1382_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v___x_1382_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1450_ = v___x_1382_;
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
else
{
lean_inc(v_a_1448_);
lean_dec(v___x_1382_);
v___x_1450_ = lean_box(0);
v_isShared_1451_ = v_isSharedCheck_1455_;
goto v_resetjp_1449_;
}
v_resetjp_1449_:
{
lean_object* v___x_1453_; 
if (v_isShared_1451_ == 0)
{
v___x_1453_ = v___x_1450_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v_a_1448_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
return v___x_1453_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1___boxed(lean_object* v_c_1458_, lean_object* v_as_1459_, lean_object* v_sz_1460_, lean_object* v_i_1461_, lean_object* v_b_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
size_t v_sz_boxed_1474_; size_t v_i_boxed_1475_; lean_object* v_res_1476_; 
v_sz_boxed_1474_ = lean_unbox_usize(v_sz_1460_);
lean_dec(v_sz_1460_);
v_i_boxed_1475_ = lean_unbox_usize(v_i_1461_);
lean_dec(v_i_1461_);
v_res_1476_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1(v_c_1458_, v_as_1459_, v_sz_boxed_1474_, v_i_boxed_1475_, v_b_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v___y_1466_);
lean_dec_ref(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec(v___y_1463_);
lean_dec_ref(v_as_1459_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0(lean_object* v_c_1477_, lean_object* v_t_1478_, lean_object* v_init_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
lean_object* v_root_1491_; lean_object* v_tail_1492_; lean_object* v___x_1493_; 
v_root_1491_ = lean_ctor_get(v_t_1478_, 0);
v_tail_1492_ = lean_ctor_get(v_t_1478_, 1);
lean_inc_ref(v_c_1477_);
lean_inc_ref(v_init_1479_);
v___x_1493_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(v_init_1479_, v_c_1477_, v_root_1491_, v_init_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
lean_dec_ref(v_init_1479_);
if (lean_obj_tag(v___x_1493_) == 0)
{
lean_object* v_a_1494_; lean_object* v___x_1496_; uint8_t v_isShared_1497_; uint8_t v_isSharedCheck_1530_; 
v_a_1494_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1496_ = v___x_1493_;
v_isShared_1497_ = v_isSharedCheck_1530_;
goto v_resetjp_1495_;
}
else
{
lean_inc(v_a_1494_);
lean_dec(v___x_1493_);
v___x_1496_ = lean_box(0);
v_isShared_1497_ = v_isSharedCheck_1530_;
goto v_resetjp_1495_;
}
v_resetjp_1495_:
{
if (lean_obj_tag(v_a_1494_) == 0)
{
lean_object* v_a_1498_; lean_object* v___x_1500_; 
lean_dec_ref(v_c_1477_);
v_a_1498_ = lean_ctor_get(v_a_1494_, 0);
lean_inc(v_a_1498_);
lean_dec_ref_known(v_a_1494_, 1);
if (v_isShared_1497_ == 0)
{
lean_ctor_set(v___x_1496_, 0, v_a_1498_);
v___x_1500_ = v___x_1496_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_a_1498_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
else
{
lean_object* v_a_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; size_t v_sz_1505_; size_t v___x_1506_; lean_object* v___x_1507_; 
lean_del_object(v___x_1496_);
v_a_1502_ = lean_ctor_get(v_a_1494_, 0);
lean_inc(v_a_1502_);
lean_dec_ref_known(v_a_1494_, 1);
v___x_1503_ = lean_box(0);
v___x_1504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1503_);
lean_ctor_set(v___x_1504_, 1, v_a_1502_);
v_sz_1505_ = lean_array_size(v_tail_1492_);
v___x_1506_ = ((size_t)0ULL);
v___x_1507_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1(v_c_1477_, v_tail_1492_, v_sz_1505_, v___x_1506_, v___x_1504_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v_a_1508_; lean_object* v___x_1510_; uint8_t v_isShared_1511_; uint8_t v_isSharedCheck_1521_; 
v_a_1508_ = lean_ctor_get(v___x_1507_, 0);
v_isSharedCheck_1521_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1521_ == 0)
{
v___x_1510_ = v___x_1507_;
v_isShared_1511_ = v_isSharedCheck_1521_;
goto v_resetjp_1509_;
}
else
{
lean_inc(v_a_1508_);
lean_dec(v___x_1507_);
v___x_1510_ = lean_box(0);
v_isShared_1511_ = v_isSharedCheck_1521_;
goto v_resetjp_1509_;
}
v_resetjp_1509_:
{
lean_object* v_fst_1512_; 
v_fst_1512_ = lean_ctor_get(v_a_1508_, 0);
if (lean_obj_tag(v_fst_1512_) == 0)
{
lean_object* v_snd_1513_; lean_object* v___x_1515_; 
v_snd_1513_ = lean_ctor_get(v_a_1508_, 1);
lean_inc(v_snd_1513_);
lean_dec(v_a_1508_);
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 0, v_snd_1513_);
v___x_1515_ = v___x_1510_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_snd_1513_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
else
{
lean_object* v_val_1517_; lean_object* v___x_1519_; 
lean_inc_ref(v_fst_1512_);
lean_dec(v_a_1508_);
v_val_1517_ = lean_ctor_get(v_fst_1512_, 0);
lean_inc(v_val_1517_);
lean_dec_ref_known(v_fst_1512_, 1);
if (v_isShared_1511_ == 0)
{
lean_ctor_set(v___x_1510_, 0, v_val_1517_);
v___x_1519_ = v___x_1510_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_val_1517_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
}
else
{
lean_object* v_a_1522_; lean_object* v___x_1524_; uint8_t v_isShared_1525_; uint8_t v_isSharedCheck_1529_; 
v_a_1522_ = lean_ctor_get(v___x_1507_, 0);
v_isSharedCheck_1529_ = !lean_is_exclusive(v___x_1507_);
if (v_isSharedCheck_1529_ == 0)
{
v___x_1524_ = v___x_1507_;
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
else
{
lean_inc(v_a_1522_);
lean_dec(v___x_1507_);
v___x_1524_ = lean_box(0);
v_isShared_1525_ = v_isSharedCheck_1529_;
goto v_resetjp_1523_;
}
v_resetjp_1523_:
{
lean_object* v___x_1527_; 
if (v_isShared_1525_ == 0)
{
v___x_1527_ = v___x_1524_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v_a_1522_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
}
}
}
}
else
{
lean_object* v_a_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1538_; 
lean_dec_ref(v_c_1477_);
v_a_1531_ = lean_ctor_get(v___x_1493_, 0);
v_isSharedCheck_1538_ = !lean_is_exclusive(v___x_1493_);
if (v_isSharedCheck_1538_ == 0)
{
v___x_1533_ = v___x_1493_;
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
else
{
lean_inc(v_a_1531_);
lean_dec(v___x_1493_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1536_; 
if (v_isShared_1534_ == 0)
{
v___x_1536_ = v___x_1533_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_a_1531_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0___boxed(lean_object* v_c_1539_, lean_object* v_t_1540_, lean_object* v_init_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_){
_start:
{
lean_object* v_res_1553_; 
v_res_1553_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0(v_c_1539_, v_t_1540_, v_init_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec(v___y_1543_);
lean_dec(v___y_1542_);
lean_dec_ref(v_t_1540_);
return v_res_1553_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0(void){
_start:
{
lean_object* v___x_1554_; 
v___x_1554_ = l_Lean_instInhabitedPersistentArray_default___redArg();
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq(lean_object* v_c_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_){
_start:
{
lean_object* v_p_1567_; 
v_p_1567_ = lean_ctor_get(v_c_1555_, 0);
if (lean_obj_tag(v_p_1567_) == 1)
{
lean_object* v_k_1568_; lean_object* v_v_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v_k_1568_ = lean_ctor_get(v_p_1567_, 0);
v_v_1569_ = lean_ctor_get(v_p_1567_, 1);
v___x_1570_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0);
v___x_1571_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1556_, v_a_1564_);
if (lean_obj_tag(v___x_1571_) == 0)
{
lean_object* v_a_1572_; lean_object* v___y_1574_; lean_object* v___x_1600_; uint8_t v___x_1601_; 
v_a_1572_ = lean_ctor_get(v___x_1571_, 0);
lean_inc(v_a_1572_);
lean_dec_ref_known(v___x_1571_, 1);
v___x_1600_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9);
v___x_1601_ = lean_int_dec_lt(v_k_1568_, v___x_1600_);
if (v___x_1601_ == 0)
{
lean_object* v_lowers_1602_; lean_object* v_size_1603_; uint8_t v___x_1604_; 
v_lowers_1602_ = lean_ctor_get(v_a_1572_, 6);
lean_inc_ref(v_lowers_1602_);
lean_dec(v_a_1572_);
v_size_1603_ = lean_ctor_get(v_lowers_1602_, 2);
v___x_1604_ = lean_nat_dec_lt(v_v_1569_, v_size_1603_);
if (v___x_1604_ == 0)
{
lean_object* v___x_1605_; 
lean_dec_ref(v_lowers_1602_);
v___x_1605_ = l_outOfBounds___redArg(v___x_1570_);
v___y_1574_ = v___x_1605_;
goto v___jp_1573_;
}
else
{
lean_object* v___x_1606_; 
v___x_1606_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1570_, v_lowers_1602_, v_v_1569_);
lean_dec_ref(v_lowers_1602_);
v___y_1574_ = v___x_1606_;
goto v___jp_1573_;
}
}
else
{
lean_object* v_uppers_1607_; lean_object* v_size_1608_; uint8_t v___x_1609_; 
v_uppers_1607_ = lean_ctor_get(v_a_1572_, 7);
lean_inc_ref(v_uppers_1607_);
lean_dec(v_a_1572_);
v_size_1608_ = lean_ctor_get(v_uppers_1607_, 2);
v___x_1609_ = lean_nat_dec_lt(v_v_1569_, v_size_1608_);
if (v___x_1609_ == 0)
{
lean_object* v___x_1610_; 
lean_dec_ref(v_uppers_1607_);
v___x_1610_ = l_outOfBounds___redArg(v___x_1570_);
v___y_1574_ = v___x_1610_;
goto v___jp_1573_;
}
else
{
lean_object* v___x_1611_; 
v___x_1611_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1570_, v_uppers_1607_, v_v_1569_);
lean_dec_ref(v_uppers_1607_);
v___y_1574_ = v___x_1611_;
goto v___jp_1573_;
}
}
v___jp_1573_:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1575_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__0));
v___x_1576_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0(v_c_1555_, v___y_1574_, v___x_1575_, v_a_1556_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_);
lean_dec_ref(v___y_1574_);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1591_; 
v_a_1577_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1591_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1591_ == 0)
{
v___x_1579_ = v___x_1576_;
v_isShared_1580_ = v_isSharedCheck_1591_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1576_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1591_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v_fst_1581_; 
v_fst_1581_ = lean_ctor_get(v_a_1577_, 0);
lean_inc(v_fst_1581_);
lean_dec(v_a_1577_);
if (lean_obj_tag(v_fst_1581_) == 0)
{
uint8_t v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1585_; 
v___x_1582_ = 0;
v___x_1583_ = lean_box(v___x_1582_);
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 0, v___x_1583_);
v___x_1585_ = v___x_1579_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v___x_1583_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
else
{
lean_object* v_val_1587_; lean_object* v___x_1589_; 
v_val_1587_ = lean_ctor_get(v_fst_1581_, 0);
lean_inc(v_val_1587_);
lean_dec_ref_known(v_fst_1581_, 1);
if (v_isShared_1580_ == 0)
{
lean_ctor_set(v___x_1579_, 0, v_val_1587_);
v___x_1589_ = v___x_1579_;
goto v_reusejp_1588_;
}
else
{
lean_object* v_reuseFailAlloc_1590_; 
v_reuseFailAlloc_1590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1590_, 0, v_val_1587_);
v___x_1589_ = v_reuseFailAlloc_1590_;
goto v_reusejp_1588_;
}
v_reusejp_1588_:
{
return v___x_1589_;
}
}
}
}
else
{
lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1599_; 
v_a_1592_ = lean_ctor_get(v___x_1576_, 0);
v_isSharedCheck_1599_ = !lean_is_exclusive(v___x_1576_);
if (v_isSharedCheck_1599_ == 0)
{
v___x_1594_ = v___x_1576_;
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_dec(v___x_1576_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1599_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1597_; 
if (v_isShared_1595_ == 0)
{
v___x_1597_ = v___x_1594_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_a_1592_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
}
else
{
lean_object* v_a_1612_; lean_object* v___x_1614_; uint8_t v_isShared_1615_; uint8_t v_isSharedCheck_1619_; 
lean_dec_ref(v_c_1555_);
v_a_1612_ = lean_ctor_get(v___x_1571_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v___x_1571_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1614_ = v___x_1571_;
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
else
{
lean_inc(v_a_1612_);
lean_dec(v___x_1571_);
v___x_1614_ = lean_box(0);
v_isShared_1615_ = v_isSharedCheck_1619_;
goto v_resetjp_1613_;
}
v_resetjp_1613_:
{
lean_object* v___x_1617_; 
if (v_isShared_1615_ == 0)
{
v___x_1617_ = v___x_1614_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_a_1612_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
}
else
{
lean_object* v___x_1620_; 
v___x_1620_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_1555_, v_a_1556_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_);
return v___x_1620_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___boxed(lean_object* v_c_1621_, lean_object* v_a_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq(v_c_1621_, v_a_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_);
lean_dec(v_a_1631_);
lean_dec_ref(v_a_1630_);
lean_dec(v_a_1629_);
lean_dec_ref(v_a_1628_);
lean_dec(v_a_1627_);
lean_dec_ref(v_a_1626_);
lean_dec(v_a_1625_);
lean_dec_ref(v_a_1624_);
lean_dec(v_a_1623_);
lean_dec(v_a_1622_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(lean_object* v___x_1634_, lean_object* v_as_1635_, size_t v_i_1636_, size_t v_stop_1637_, lean_object* v_b_1638_){
_start:
{
lean_object* v___y_1640_; uint8_t v___x_1644_; 
v___x_1644_ = lean_usize_dec_eq(v_i_1636_, v_stop_1637_);
if (v___x_1644_ == 0)
{
lean_object* v___x_1645_; lean_object* v_p_1646_; uint8_t v___x_1647_; 
v___x_1645_ = lean_array_uget_borrowed(v_as_1635_, v_i_1636_);
v_p_1646_ = lean_ctor_get(v___x_1645_, 0);
v___x_1647_ = l_Int_Internal_Linear_instBEqPoly_beq(v_p_1646_, v___x_1634_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; 
lean_inc(v___x_1645_);
v___x_1648_ = l_Lean_PersistentArray_push___redArg(v_b_1638_, v___x_1645_);
v___y_1640_ = v___x_1648_;
goto v___jp_1639_;
}
else
{
v___y_1640_ = v_b_1638_;
goto v___jp_1639_;
}
}
else
{
return v_b_1638_;
}
v___jp_1639_:
{
size_t v___x_1641_; size_t v___x_1642_; 
v___x_1641_ = ((size_t)1ULL);
v___x_1642_ = lean_usize_add(v_i_1636_, v___x_1641_);
v_i_1636_ = v___x_1642_;
v_b_1638_ = v___y_1640_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1___boxed(lean_object* v___x_1649_, lean_object* v_as_1650_, lean_object* v_i_1651_, lean_object* v_stop_1652_, lean_object* v_b_1653_){
_start:
{
size_t v_i_boxed_1654_; size_t v_stop_boxed_1655_; lean_object* v_res_1656_; 
v_i_boxed_1654_ = lean_unbox_usize(v_i_1651_);
lean_dec(v_i_1651_);
v_stop_boxed_1655_ = lean_unbox_usize(v_stop_1652_);
lean_dec(v_stop_1652_);
v_res_1656_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1649_, v_as_1650_, v_i_boxed_1654_, v_stop_boxed_1655_, v_b_1653_);
lean_dec_ref(v_as_1650_);
lean_dec_ref(v___x_1649_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(lean_object* v___x_1657_, lean_object* v_x_1658_, lean_object* v_x_1659_){
_start:
{
if (lean_obj_tag(v_x_1658_) == 0)
{
lean_object* v_cs_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; uint8_t v___x_1663_; 
v_cs_1660_ = lean_ctor_get(v_x_1658_, 0);
v___x_1661_ = lean_unsigned_to_nat(0u);
v___x_1662_ = lean_array_get_size(v_cs_1660_);
v___x_1663_ = lean_nat_dec_lt(v___x_1661_, v___x_1662_);
if (v___x_1663_ == 0)
{
return v_x_1659_;
}
else
{
size_t v___x_1664_; size_t v___x_1665_; lean_object* v___x_1666_; 
v___x_1664_ = ((size_t)0ULL);
v___x_1665_ = lean_usize_of_nat(v___x_1662_);
v___x_1666_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1657_, v_cs_1660_, v___x_1664_, v___x_1665_, v_x_1659_);
return v___x_1666_;
}
}
else
{
lean_object* v_vs_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; uint8_t v___x_1670_; 
v_vs_1667_ = lean_ctor_get(v_x_1658_, 0);
v___x_1668_ = lean_unsigned_to_nat(0u);
v___x_1669_ = lean_array_get_size(v_vs_1667_);
v___x_1670_ = lean_nat_dec_lt(v___x_1668_, v___x_1669_);
if (v___x_1670_ == 0)
{
return v_x_1659_;
}
else
{
size_t v___x_1671_; size_t v___x_1672_; lean_object* v___x_1673_; 
v___x_1671_ = ((size_t)0ULL);
v___x_1672_ = lean_usize_of_nat(v___x_1669_);
v___x_1673_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1657_, v_vs_1667_, v___x_1671_, v___x_1672_, v_x_1659_);
return v___x_1673_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(lean_object* v___x_1674_, lean_object* v_as_1675_, size_t v_i_1676_, size_t v_stop_1677_, lean_object* v_b_1678_){
_start:
{
uint8_t v___x_1679_; 
v___x_1679_ = lean_usize_dec_eq(v_i_1676_, v_stop_1677_);
if (v___x_1679_ == 0)
{
lean_object* v___x_1680_; lean_object* v___x_1681_; size_t v___x_1682_; size_t v___x_1683_; 
v___x_1680_ = lean_array_uget_borrowed(v_as_1675_, v_i_1676_);
v___x_1681_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(v___x_1674_, v___x_1680_, v_b_1678_);
v___x_1682_ = ((size_t)1ULL);
v___x_1683_ = lean_usize_add(v_i_1676_, v___x_1682_);
v_i_1676_ = v___x_1683_;
v_b_1678_ = v___x_1681_;
goto _start;
}
else
{
return v_b_1678_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v___x_1685_, lean_object* v_as_1686_, lean_object* v_i_1687_, lean_object* v_stop_1688_, lean_object* v_b_1689_){
_start:
{
size_t v_i_boxed_1690_; size_t v_stop_boxed_1691_; lean_object* v_res_1692_; 
v_i_boxed_1690_ = lean_unbox_usize(v_i_1687_);
lean_dec(v_i_1687_);
v_stop_boxed_1691_ = lean_unbox_usize(v_stop_1688_);
lean_dec(v_stop_1688_);
v_res_1692_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1685_, v_as_1686_, v_i_boxed_1690_, v_stop_boxed_1691_, v_b_1689_);
lean_dec_ref(v_as_1686_);
lean_dec_ref(v___x_1685_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2___boxed(lean_object* v___x_1693_, lean_object* v_x_1694_, lean_object* v_x_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(v___x_1693_, v_x_1694_, v_x_1695_);
lean_dec_ref(v_x_1694_);
lean_dec_ref(v___x_1693_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(lean_object* v___x_1697_, lean_object* v_x_1698_, size_t v_x_1699_, size_t v_x_1700_, lean_object* v_x_1701_){
_start:
{
if (lean_obj_tag(v_x_1698_) == 0)
{
lean_object* v_cs_1702_; lean_object* v___x_1703_; size_t v___x_1704_; lean_object* v_j_1705_; lean_object* v___x_1706_; size_t v___x_1707_; size_t v___x_1708_; size_t v___x_1709_; size_t v___x_1710_; size_t v___x_1711_; size_t v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; uint8_t v___x_1717_; 
v_cs_1702_ = lean_ctor_get(v_x_1698_, 0);
v___x_1703_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0);
v___x_1704_ = lean_usize_shift_right(v_x_1699_, v_x_1700_);
v_j_1705_ = lean_usize_to_nat(v___x_1704_);
v___x_1706_ = lean_array_get_borrowed(v___x_1703_, v_cs_1702_, v_j_1705_);
v___x_1707_ = ((size_t)1ULL);
v___x_1708_ = lean_usize_shift_left(v___x_1707_, v_x_1700_);
v___x_1709_ = lean_usize_sub(v___x_1708_, v___x_1707_);
v___x_1710_ = lean_usize_land(v_x_1699_, v___x_1709_);
v___x_1711_ = ((size_t)5ULL);
v___x_1712_ = lean_usize_sub(v_x_1700_, v___x_1711_);
v___x_1713_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(v___x_1697_, v___x_1706_, v___x_1710_, v___x_1712_, v_x_1701_);
v___x_1714_ = lean_unsigned_to_nat(1u);
v___x_1715_ = lean_nat_add(v_j_1705_, v___x_1714_);
lean_dec(v_j_1705_);
v___x_1716_ = lean_array_get_size(v_cs_1702_);
v___x_1717_ = lean_nat_dec_lt(v___x_1715_, v___x_1716_);
if (v___x_1717_ == 0)
{
lean_dec(v___x_1715_);
return v___x_1713_;
}
else
{
size_t v___x_1718_; size_t v___x_1719_; lean_object* v___x_1720_; 
v___x_1718_ = lean_usize_of_nat(v___x_1715_);
lean_dec(v___x_1715_);
v___x_1719_ = lean_usize_of_nat(v___x_1716_);
v___x_1720_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1697_, v_cs_1702_, v___x_1718_, v___x_1719_, v___x_1713_);
return v___x_1720_;
}
}
else
{
lean_object* v_vs_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; uint8_t v___x_1724_; 
v_vs_1721_ = lean_ctor_get(v_x_1698_, 0);
v___x_1722_ = lean_usize_to_nat(v_x_1699_);
v___x_1723_ = lean_array_get_size(v_vs_1721_);
v___x_1724_ = lean_nat_dec_lt(v___x_1722_, v___x_1723_);
if (v___x_1724_ == 0)
{
lean_dec(v___x_1722_);
return v_x_1701_;
}
else
{
size_t v___x_1725_; size_t v___x_1726_; lean_object* v___x_1727_; 
v___x_1725_ = lean_usize_of_nat(v___x_1722_);
lean_dec(v___x_1722_);
v___x_1726_ = lean_usize_of_nat(v___x_1723_);
v___x_1727_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1697_, v_vs_1721_, v___x_1725_, v___x_1726_, v_x_1701_);
return v___x_1727_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0___boxed(lean_object* v___x_1728_, lean_object* v_x_1729_, lean_object* v_x_1730_, lean_object* v_x_1731_, lean_object* v_x_1732_){
_start:
{
size_t v_x_20995__boxed_1733_; size_t v_x_20996__boxed_1734_; lean_object* v_res_1735_; 
v_x_20995__boxed_1733_ = lean_unbox_usize(v_x_1730_);
lean_dec(v_x_1730_);
v_x_20996__boxed_1734_ = lean_unbox_usize(v_x_1731_);
lean_dec(v_x_1731_);
v_res_1735_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(v___x_1728_, v_x_1729_, v_x_20995__boxed_1733_, v_x_20996__boxed_1734_, v_x_1732_);
lean_dec_ref(v_x_1729_);
lean_dec_ref(v___x_1728_);
return v_res_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(lean_object* v___x_1736_, lean_object* v_t_1737_, lean_object* v_init_1738_, lean_object* v_start_1739_){
_start:
{
lean_object* v___x_1740_; uint8_t v___x_1741_; 
v___x_1740_ = lean_unsigned_to_nat(0u);
v___x_1741_ = lean_nat_dec_eq(v_start_1739_, v___x_1740_);
if (v___x_1741_ == 0)
{
lean_object* v_root_1742_; lean_object* v_tail_1743_; size_t v_shift_1744_; lean_object* v_tailOff_1745_; uint8_t v___x_1746_; 
v_root_1742_ = lean_ctor_get(v_t_1737_, 0);
v_tail_1743_ = lean_ctor_get(v_t_1737_, 1);
v_shift_1744_ = lean_ctor_get_usize(v_t_1737_, 4);
v_tailOff_1745_ = lean_ctor_get(v_t_1737_, 3);
v___x_1746_ = lean_nat_dec_le(v_tailOff_1745_, v_start_1739_);
if (v___x_1746_ == 0)
{
size_t v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; uint8_t v___x_1750_; 
v___x_1747_ = lean_usize_of_nat(v_start_1739_);
v___x_1748_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(v___x_1736_, v_root_1742_, v___x_1747_, v_shift_1744_, v_init_1738_);
v___x_1749_ = lean_array_get_size(v_tail_1743_);
v___x_1750_ = lean_nat_dec_lt(v___x_1740_, v___x_1749_);
if (v___x_1750_ == 0)
{
return v___x_1748_;
}
else
{
size_t v___x_1751_; size_t v___x_1752_; lean_object* v___x_1753_; 
v___x_1751_ = ((size_t)0ULL);
v___x_1752_ = lean_usize_of_nat(v___x_1749_);
v___x_1753_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1736_, v_tail_1743_, v___x_1751_, v___x_1752_, v___x_1748_);
return v___x_1753_;
}
}
else
{
lean_object* v___x_1754_; lean_object* v___x_1755_; uint8_t v___x_1756_; 
v___x_1754_ = lean_nat_sub(v_start_1739_, v_tailOff_1745_);
v___x_1755_ = lean_array_get_size(v_tail_1743_);
v___x_1756_ = lean_nat_dec_lt(v___x_1754_, v___x_1755_);
if (v___x_1756_ == 0)
{
lean_dec(v___x_1754_);
return v_init_1738_;
}
else
{
size_t v___x_1757_; size_t v___x_1758_; lean_object* v___x_1759_; 
v___x_1757_ = lean_usize_of_nat(v___x_1754_);
lean_dec(v___x_1754_);
v___x_1758_ = lean_usize_of_nat(v___x_1755_);
v___x_1759_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1736_, v_tail_1743_, v___x_1757_, v___x_1758_, v_init_1738_);
return v___x_1759_;
}
}
}
else
{
lean_object* v_root_1760_; lean_object* v_tail_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; uint8_t v___x_1764_; 
v_root_1760_ = lean_ctor_get(v_t_1737_, 0);
v_tail_1761_ = lean_ctor_get(v_t_1737_, 1);
v___x_1762_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(v___x_1736_, v_root_1760_, v_init_1738_);
v___x_1763_ = lean_array_get_size(v_tail_1761_);
v___x_1764_ = lean_nat_dec_lt(v___x_1740_, v___x_1763_);
if (v___x_1764_ == 0)
{
return v___x_1762_;
}
else
{
size_t v___x_1765_; size_t v___x_1766_; lean_object* v___x_1767_; 
v___x_1765_ = ((size_t)0ULL);
v___x_1766_ = lean_usize_of_nat(v___x_1763_);
v___x_1767_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1736_, v_tail_1761_, v___x_1765_, v___x_1766_, v___x_1762_);
return v___x_1767_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0___boxed(lean_object* v___x_1768_, lean_object* v_t_1769_, lean_object* v_init_1770_, lean_object* v_start_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(v___x_1768_, v_t_1769_, v_init_1770_, v_start_1771_);
lean_dec(v_start_1771_);
lean_dec_ref(v_t_1769_);
lean_dec_ref(v___x_1768_);
return v_res_1772_;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1773_ = lean_unsigned_to_nat(32u);
v___x_1774_ = lean_mk_empty_array_with_capacity(v___x_1773_);
v___x_1775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1774_);
return v___x_1775_;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1(void){
_start:
{
size_t v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; 
v___x_1776_ = ((size_t)5ULL);
v___x_1777_ = lean_unsigned_to_nat(0u);
v___x_1778_ = lean_unsigned_to_nat(32u);
v___x_1779_ = lean_mk_empty_array_with_capacity(v___x_1778_);
v___x_1780_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0);
v___x_1781_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1781_, 0, v___x_1780_);
lean_ctor_set(v___x_1781_, 1, v___x_1779_);
lean_ctor_set(v___x_1781_, 2, v___x_1777_);
lean_ctor_set(v___x_1781_, 3, v___x_1777_);
lean_ctor_set_usize(v___x_1781_, 4, v___x_1776_);
return v___x_1781_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(lean_object* v___x_1782_, lean_object* v_x_1783_, size_t v_x_1784_, size_t v_x_1785_){
_start:
{
if (lean_obj_tag(v_x_1783_) == 0)
{
lean_object* v_cs_1786_; size_t v_j_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; uint8_t v___x_1790_; 
v_cs_1786_ = lean_ctor_get(v_x_1783_, 0);
v_j_1787_ = lean_usize_shift_right(v_x_1784_, v_x_1785_);
v___x_1788_ = lean_usize_to_nat(v_j_1787_);
v___x_1789_ = lean_array_get_size(v_cs_1786_);
v___x_1790_ = lean_nat_dec_lt(v___x_1788_, v___x_1789_);
if (v___x_1790_ == 0)
{
lean_dec(v___x_1788_);
return v_x_1783_;
}
else
{
lean_object* v___x_1792_; uint8_t v_isShared_1793_; uint8_t v_isSharedCheck_1808_; 
lean_inc_ref(v_cs_1786_);
v_isSharedCheck_1808_ = !lean_is_exclusive(v_x_1783_);
if (v_isSharedCheck_1808_ == 0)
{
lean_object* v_unused_1809_; 
v_unused_1809_ = lean_ctor_get(v_x_1783_, 0);
lean_dec(v_unused_1809_);
v___x_1792_ = v_x_1783_;
v_isShared_1793_ = v_isSharedCheck_1808_;
goto v_resetjp_1791_;
}
else
{
lean_dec(v_x_1783_);
v___x_1792_ = lean_box(0);
v_isShared_1793_ = v_isSharedCheck_1808_;
goto v_resetjp_1791_;
}
v_resetjp_1791_:
{
size_t v___x_1794_; size_t v___x_1795_; size_t v___x_1796_; size_t v_i_1797_; size_t v___x_1798_; size_t v_shift_1799_; lean_object* v_v_1800_; lean_object* v___x_1801_; lean_object* v_xs_x27_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1806_; 
v___x_1794_ = ((size_t)1ULL);
v___x_1795_ = lean_usize_shift_left(v___x_1794_, v_x_1785_);
v___x_1796_ = lean_usize_sub(v___x_1795_, v___x_1794_);
v_i_1797_ = lean_usize_land(v_x_1784_, v___x_1796_);
v___x_1798_ = ((size_t)5ULL);
v_shift_1799_ = lean_usize_sub(v_x_1785_, v___x_1798_);
v_v_1800_ = lean_array_fget(v_cs_1786_, v___x_1788_);
v___x_1801_ = lean_box(0);
v_xs_x27_1802_ = lean_array_fset(v_cs_1786_, v___x_1788_, v___x_1801_);
v___x_1803_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(v___x_1782_, v_v_1800_, v_i_1797_, v_shift_1799_);
v___x_1804_ = lean_array_fset(v_xs_x27_1802_, v___x_1788_, v___x_1803_);
lean_dec(v___x_1788_);
if (v_isShared_1793_ == 0)
{
lean_ctor_set(v___x_1792_, 0, v___x_1804_);
v___x_1806_ = v___x_1792_;
goto v_reusejp_1805_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v___x_1804_);
v___x_1806_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1805_;
}
v_reusejp_1805_:
{
return v___x_1806_;
}
}
}
}
else
{
lean_object* v_vs_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; uint8_t v___x_1813_; 
v_vs_1810_ = lean_ctor_get(v_x_1783_, 0);
v___x_1811_ = lean_usize_to_nat(v_x_1784_);
v___x_1812_ = lean_array_get_size(v_vs_1810_);
v___x_1813_ = lean_nat_dec_lt(v___x_1811_, v___x_1812_);
if (v___x_1813_ == 0)
{
lean_dec(v___x_1811_);
return v_x_1783_;
}
else
{
lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1827_; 
lean_inc_ref(v_vs_1810_);
v_isSharedCheck_1827_ = !lean_is_exclusive(v_x_1783_);
if (v_isSharedCheck_1827_ == 0)
{
lean_object* v_unused_1828_; 
v_unused_1828_ = lean_ctor_get(v_x_1783_, 0);
lean_dec(v_unused_1828_);
v___x_1815_ = v_x_1783_;
v_isShared_1816_ = v_isSharedCheck_1827_;
goto v_resetjp_1814_;
}
else
{
lean_dec(v_x_1783_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1827_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v_v_1817_; lean_object* v___x_1818_; lean_object* v_xs_x27_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1825_; 
v_v_1817_ = lean_array_fget(v_vs_1810_, v___x_1811_);
v___x_1818_ = lean_box(0);
v_xs_x27_1819_ = lean_array_fset(v_vs_1810_, v___x_1811_, v___x_1818_);
v___x_1820_ = lean_unsigned_to_nat(0u);
v___x_1821_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1);
v___x_1822_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(v___x_1782_, v_v_1817_, v___x_1821_, v___x_1820_);
lean_dec(v_v_1817_);
v___x_1823_ = lean_array_fset(v_xs_x27_1819_, v___x_1811_, v___x_1822_);
lean_dec(v___x_1811_);
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 0, v___x_1823_);
v___x_1825_ = v___x_1815_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1823_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___boxed(lean_object* v___x_1829_, lean_object* v_x_1830_, lean_object* v_x_1831_, lean_object* v_x_1832_){
_start:
{
size_t v_x_21127__boxed_1833_; size_t v_x_21128__boxed_1834_; lean_object* v_res_1835_; 
v_x_21127__boxed_1833_ = lean_unbox_usize(v_x_1831_);
lean_dec(v_x_1831_);
v_x_21128__boxed_1834_ = lean_unbox_usize(v_x_1832_);
lean_dec(v_x_1832_);
v_res_1835_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(v___x_1829_, v_x_1830_, v_x_21127__boxed_1833_, v_x_21128__boxed_1834_);
lean_dec_ref(v___x_1829_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1(lean_object* v___x_1836_, lean_object* v_t_1837_, lean_object* v_i_1838_){
_start:
{
lean_object* v_root_1839_; lean_object* v_tail_1840_; lean_object* v_size_1841_; size_t v_shift_1842_; lean_object* v_tailOff_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1871_; 
v_root_1839_ = lean_ctor_get(v_t_1837_, 0);
v_tail_1840_ = lean_ctor_get(v_t_1837_, 1);
v_size_1841_ = lean_ctor_get(v_t_1837_, 2);
v_shift_1842_ = lean_ctor_get_usize(v_t_1837_, 4);
v_tailOff_1843_ = lean_ctor_get(v_t_1837_, 3);
v_isSharedCheck_1871_ = !lean_is_exclusive(v_t_1837_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1845_ = v_t_1837_;
v_isShared_1846_ = v_isSharedCheck_1871_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_tailOff_1843_);
lean_inc(v_size_1841_);
lean_inc(v_tail_1840_);
lean_inc(v_root_1839_);
lean_dec(v_t_1837_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1871_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
uint8_t v___x_1847_; 
v___x_1847_ = lean_nat_dec_le(v_tailOff_1843_, v_i_1838_);
if (v___x_1847_ == 0)
{
size_t v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1851_; 
v___x_1848_ = lean_usize_of_nat(v_i_1838_);
v___x_1849_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(v___x_1836_, v_root_1839_, v___x_1848_, v_shift_1842_);
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 0, v___x_1849_);
v___x_1851_ = v___x_1845_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v___x_1849_);
lean_ctor_set(v_reuseFailAlloc_1852_, 1, v_tail_1840_);
lean_ctor_set(v_reuseFailAlloc_1852_, 2, v_size_1841_);
lean_ctor_set(v_reuseFailAlloc_1852_, 3, v_tailOff_1843_);
lean_ctor_set_usize(v_reuseFailAlloc_1852_, 4, v_shift_1842_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
else
{
lean_object* v___x_1853_; lean_object* v___x_1854_; uint8_t v___x_1855_; 
v___x_1853_ = lean_nat_sub(v_i_1838_, v_tailOff_1843_);
v___x_1854_ = lean_array_get_size(v_tail_1840_);
v___x_1855_ = lean_nat_dec_lt(v___x_1853_, v___x_1854_);
if (v___x_1855_ == 0)
{
lean_object* v___x_1857_; 
lean_dec(v___x_1853_);
if (v_isShared_1846_ == 0)
{
v___x_1857_ = v___x_1845_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_root_1839_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v_tail_1840_);
lean_ctor_set(v_reuseFailAlloc_1858_, 2, v_size_1841_);
lean_ctor_set(v_reuseFailAlloc_1858_, 3, v_tailOff_1843_);
lean_ctor_set_usize(v_reuseFailAlloc_1858_, 4, v_shift_1842_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
else
{
lean_object* v_v_1859_; lean_object* v___x_1860_; lean_object* v_xs_x27_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1869_; 
v_v_1859_ = lean_array_fget(v_tail_1840_, v___x_1853_);
v___x_1860_ = lean_box(0);
v_xs_x27_1861_ = lean_array_fset(v_tail_1840_, v___x_1853_, v___x_1860_);
v___x_1862_ = lean_unsigned_to_nat(32u);
v___x_1863_ = lean_mk_empty_array_with_capacity(v___x_1862_);
lean_dec_ref(v___x_1863_);
v___x_1864_ = lean_unsigned_to_nat(0u);
v___x_1865_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1);
v___x_1866_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(v___x_1836_, v_v_1859_, v___x_1865_, v___x_1864_);
lean_dec(v_v_1859_);
v___x_1867_ = lean_array_fset(v_xs_x27_1861_, v___x_1853_, v___x_1866_);
lean_dec(v___x_1853_);
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 1, v___x_1867_);
v___x_1869_ = v___x_1845_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v_root_1839_);
lean_ctor_set(v_reuseFailAlloc_1870_, 1, v___x_1867_);
lean_ctor_set(v_reuseFailAlloc_1870_, 2, v_size_1841_);
lean_ctor_set(v_reuseFailAlloc_1870_, 3, v_tailOff_1843_);
lean_ctor_set_usize(v_reuseFailAlloc_1870_, 4, v_shift_1842_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1___boxed(lean_object* v___x_1872_, lean_object* v_t_1873_, lean_object* v_i_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1(v___x_1872_, v_t_1873_, v_i_1874_);
lean_dec(v_i_1874_);
lean_dec_ref(v___x_1872_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0(lean_object* v_p_1876_, lean_object* v_x_1877_, lean_object* v_s_1878_){
_start:
{
lean_object* v_vars_1879_; lean_object* v_varMap_1880_; lean_object* v_varsHistory_1881_; lean_object* v_natToIntMap_1882_; lean_object* v_natDef_1883_; lean_object* v_dvds_1884_; lean_object* v_lowers_1885_; lean_object* v_uppers_1886_; lean_object* v_diseqs_1887_; lean_object* v_elimEqs_1888_; lean_object* v_elimStack_1889_; lean_object* v_occurs_1890_; lean_object* v_assignment_1891_; lean_object* v_nextCnstrId_1892_; uint8_t v_caseSplits_1893_; lean_object* v_steps_1894_; lean_object* v_penalties_1895_; lean_object* v_numReorderRequests_1896_; lean_object* v_conflict_x3f_1897_; lean_object* v_diseqSplits_1898_; lean_object* v_divMod_1899_; uint8_t v_usedCommRing_1900_; lean_object* v_nonlinearOccs_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1909_; 
v_vars_1879_ = lean_ctor_get(v_s_1878_, 0);
v_varMap_1880_ = lean_ctor_get(v_s_1878_, 1);
v_varsHistory_1881_ = lean_ctor_get(v_s_1878_, 2);
v_natToIntMap_1882_ = lean_ctor_get(v_s_1878_, 3);
v_natDef_1883_ = lean_ctor_get(v_s_1878_, 4);
v_dvds_1884_ = lean_ctor_get(v_s_1878_, 5);
v_lowers_1885_ = lean_ctor_get(v_s_1878_, 6);
v_uppers_1886_ = lean_ctor_get(v_s_1878_, 7);
v_diseqs_1887_ = lean_ctor_get(v_s_1878_, 8);
v_elimEqs_1888_ = lean_ctor_get(v_s_1878_, 9);
v_elimStack_1889_ = lean_ctor_get(v_s_1878_, 10);
v_occurs_1890_ = lean_ctor_get(v_s_1878_, 11);
v_assignment_1891_ = lean_ctor_get(v_s_1878_, 12);
v_nextCnstrId_1892_ = lean_ctor_get(v_s_1878_, 13);
v_caseSplits_1893_ = lean_ctor_get_uint8(v_s_1878_, sizeof(void*)*21);
v_steps_1894_ = lean_ctor_get(v_s_1878_, 14);
v_penalties_1895_ = lean_ctor_get(v_s_1878_, 15);
v_numReorderRequests_1896_ = lean_ctor_get(v_s_1878_, 16);
v_conflict_x3f_1897_ = lean_ctor_get(v_s_1878_, 17);
v_diseqSplits_1898_ = lean_ctor_get(v_s_1878_, 18);
v_divMod_1899_ = lean_ctor_get(v_s_1878_, 19);
v_usedCommRing_1900_ = lean_ctor_get_uint8(v_s_1878_, sizeof(void*)*21 + 1);
v_nonlinearOccs_1901_ = lean_ctor_get(v_s_1878_, 20);
v_isSharedCheck_1909_ = !lean_is_exclusive(v_s_1878_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1903_ = v_s_1878_;
v_isShared_1904_ = v_isSharedCheck_1909_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_nonlinearOccs_1901_);
lean_inc(v_divMod_1899_);
lean_inc(v_diseqSplits_1898_);
lean_inc(v_conflict_x3f_1897_);
lean_inc(v_numReorderRequests_1896_);
lean_inc(v_penalties_1895_);
lean_inc(v_steps_1894_);
lean_inc(v_nextCnstrId_1892_);
lean_inc(v_assignment_1891_);
lean_inc(v_occurs_1890_);
lean_inc(v_elimStack_1889_);
lean_inc(v_elimEqs_1888_);
lean_inc(v_diseqs_1887_);
lean_inc(v_uppers_1886_);
lean_inc(v_lowers_1885_);
lean_inc(v_dvds_1884_);
lean_inc(v_natDef_1883_);
lean_inc(v_natToIntMap_1882_);
lean_inc(v_varsHistory_1881_);
lean_inc(v_varMap_1880_);
lean_inc(v_vars_1879_);
lean_dec(v_s_1878_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1909_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1905_; lean_object* v___x_1907_; 
v___x_1905_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1(v_p_1876_, v_diseqs_1887_, v_x_1877_);
if (v_isShared_1904_ == 0)
{
lean_ctor_set(v___x_1903_, 8, v___x_1905_);
v___x_1907_ = v___x_1903_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 21, 2);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_vars_1879_);
lean_ctor_set(v_reuseFailAlloc_1908_, 1, v_varMap_1880_);
lean_ctor_set(v_reuseFailAlloc_1908_, 2, v_varsHistory_1881_);
lean_ctor_set(v_reuseFailAlloc_1908_, 3, v_natToIntMap_1882_);
lean_ctor_set(v_reuseFailAlloc_1908_, 4, v_natDef_1883_);
lean_ctor_set(v_reuseFailAlloc_1908_, 5, v_dvds_1884_);
lean_ctor_set(v_reuseFailAlloc_1908_, 6, v_lowers_1885_);
lean_ctor_set(v_reuseFailAlloc_1908_, 7, v_uppers_1886_);
lean_ctor_set(v_reuseFailAlloc_1908_, 8, v___x_1905_);
lean_ctor_set(v_reuseFailAlloc_1908_, 9, v_elimEqs_1888_);
lean_ctor_set(v_reuseFailAlloc_1908_, 10, v_elimStack_1889_);
lean_ctor_set(v_reuseFailAlloc_1908_, 11, v_occurs_1890_);
lean_ctor_set(v_reuseFailAlloc_1908_, 12, v_assignment_1891_);
lean_ctor_set(v_reuseFailAlloc_1908_, 13, v_nextCnstrId_1892_);
lean_ctor_set(v_reuseFailAlloc_1908_, 14, v_steps_1894_);
lean_ctor_set(v_reuseFailAlloc_1908_, 15, v_penalties_1895_);
lean_ctor_set(v_reuseFailAlloc_1908_, 16, v_numReorderRequests_1896_);
lean_ctor_set(v_reuseFailAlloc_1908_, 17, v_conflict_x3f_1897_);
lean_ctor_set(v_reuseFailAlloc_1908_, 18, v_diseqSplits_1898_);
lean_ctor_set(v_reuseFailAlloc_1908_, 19, v_divMod_1899_);
lean_ctor_set(v_reuseFailAlloc_1908_, 20, v_nonlinearOccs_1901_);
lean_ctor_set_uint8(v_reuseFailAlloc_1908_, sizeof(void*)*21, v_caseSplits_1893_);
lean_ctor_set_uint8(v_reuseFailAlloc_1908_, sizeof(void*)*21 + 1, v_usedCommRing_1900_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed(lean_object* v_p_1910_, lean_object* v_x_1911_, lean_object* v_s_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0(v_p_1910_, v_x_1911_, v_s_1912_);
lean_dec(v_x_1911_);
lean_dec_ref(v_p_1910_);
return v_res_1913_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1914_ = lean_unsigned_to_nat(1u);
v___x_1915_ = lean_nat_to_int(v___x_1914_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(lean_object* v_c_1922_, lean_object* v_x_1923_, lean_object* v_as_1924_, size_t v_sz_1925_, size_t v_i_1926_, lean_object* v_b_1927_, lean_object* v___y_1928_){
_start:
{
uint8_t v___x_1930_; 
v___x_1930_ = lean_usize_dec_lt(v_i_1926_, v_sz_1925_);
if (v___x_1930_ == 0)
{
lean_object* v___x_1931_; 
lean_dec(v_x_1923_);
lean_dec_ref(v_c_1922_);
v___x_1931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1931_, 0, v_b_1927_);
return v___x_1931_;
}
else
{
lean_object* v_snd_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1977_; 
v_snd_1932_ = lean_ctor_get(v_b_1927_, 1);
v_isSharedCheck_1977_ = !lean_is_exclusive(v_b_1927_);
if (v_isSharedCheck_1977_ == 0)
{
lean_object* v_unused_1978_; 
v_unused_1978_ = lean_ctor_get(v_b_1927_, 0);
lean_dec(v_unused_1978_);
v___x_1934_ = v_b_1927_;
v_isShared_1935_ = v_isSharedCheck_1977_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_snd_1932_);
lean_dec(v_b_1927_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1977_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v_p_1936_; lean_object* v_a_1937_; lean_object* v_p_1938_; lean_object* v___x_1939_; lean_object* v___f_1940_; uint8_t v___x_1971_; 
v_p_1936_ = lean_ctor_get(v_c_1922_, 0);
v_a_1937_ = lean_array_uget_borrowed(v_as_1924_, v_i_1926_);
v_p_1938_ = lean_ctor_get(v_a_1937_, 0);
v___x_1939_ = lean_box(0);
lean_inc(v_x_1923_);
lean_inc_ref(v_p_1938_);
v___f_1940_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1940_, 0, v_p_1938_);
lean_closure_set(v___f_1940_, 1, v_x_1923_);
v___x_1971_ = l_Int_Internal_Linear_instBEqPoly_beq(v_p_1936_, v_p_1938_);
if (v___x_1971_ == 0)
{
uint8_t v___x_1972_; 
v___x_1972_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_1936_, v_p_1938_);
if (v___x_1972_ == 0)
{
lean_object* v___x_1973_; size_t v___x_1974_; size_t v___x_1975_; 
lean_dec_ref(v___f_1940_);
lean_del_object(v___x_1934_);
lean_dec(v_snd_1932_);
v___x_1973_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2));
v___x_1974_ = ((size_t)1ULL);
v___x_1975_ = lean_usize_add(v_i_1926_, v___x_1974_);
v_i_1926_ = v___x_1975_;
v_b_1927_ = v___x_1973_;
goto _start;
}
else
{
lean_dec(v_x_1923_);
goto v___jp_1941_;
}
}
else
{
lean_dec(v_x_1923_);
goto v___jp_1941_;
}
v___jp_1941_:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1942_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_1943_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1942_, v___f_1940_, v___y_1928_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1961_; 
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1961_ == 0)
{
lean_object* v_unused_1962_; 
v_unused_1962_ = lean_ctor_get(v___x_1943_, 0);
lean_dec(v_unused_1962_);
v___x_1945_ = v___x_1943_;
v_isShared_1946_ = v_isSharedCheck_1961_;
goto v_resetjp_1944_;
}
else
{
lean_dec(v___x_1943_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1961_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1954_; 
v___x_1947_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0);
lean_inc_ref(v_p_1936_);
v___x_1948_ = l_Int_Internal_Linear_Poly_addConst(v_p_1936_, v___x_1947_);
lean_inc(v_a_1937_);
v___x_1949_ = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(v___x_1949_, 0, v_c_1922_);
lean_ctor_set(v___x_1949_, 1, v_a_1937_);
v___x_1950_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1948_);
lean_ctor_set(v___x_1950_, 1, v___x_1949_);
v___x_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1950_);
v___x_1952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1951_);
if (v_isShared_1935_ == 0)
{
lean_ctor_set(v___x_1934_, 1, v___x_1939_);
lean_ctor_set(v___x_1934_, 0, v___x_1952_);
v___x_1954_ = v___x_1934_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v___x_1952_);
lean_ctor_set(v_reuseFailAlloc_1960_, 1, v___x_1939_);
v___x_1954_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1958_; 
v___x_1955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1954_);
v___x_1956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1956_, 0, v___x_1955_);
lean_ctor_set(v___x_1956_, 1, v_snd_1932_);
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 0, v___x_1956_);
v___x_1958_ = v___x_1945_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v___x_1956_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
}
else
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1970_; 
lean_del_object(v___x_1934_);
lean_dec(v_snd_1932_);
lean_dec_ref(v_c_1922_);
v_a_1963_ = lean_ctor_get(v___x_1943_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1965_ = v___x_1943_;
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1943_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1968_; 
if (v_isShared_1966_ == 0)
{
v___x_1968_ = v___x_1965_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_a_1963_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___boxed(lean_object* v_c_1979_, lean_object* v_x_1980_, lean_object* v_as_1981_, lean_object* v_sz_1982_, lean_object* v_i_1983_, lean_object* v_b_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
size_t v_sz_boxed_1987_; size_t v_i_boxed_1988_; lean_object* v_res_1989_; 
v_sz_boxed_1987_ = lean_unbox_usize(v_sz_1982_);
lean_dec(v_sz_1982_);
v_i_boxed_1988_ = lean_unbox_usize(v_i_1983_);
lean_dec(v_i_1983_);
v_res_1989_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(v_c_1979_, v_x_1980_, v_as_1981_, v_sz_boxed_1987_, v_i_boxed_1988_, v_b_1984_, v___y_1985_);
lean_dec(v___y_1985_);
lean_dec_ref(v_as_1981_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7(lean_object* v_c_1996_, lean_object* v_x_1997_, lean_object* v_as_1998_, size_t v_sz_1999_, size_t v_i_2000_, lean_object* v_b_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_){
_start:
{
uint8_t v___x_2013_; 
v___x_2013_ = lean_usize_dec_lt(v_i_2000_, v_sz_1999_);
if (v___x_2013_ == 0)
{
lean_object* v___x_2014_; 
lean_dec(v_x_1997_);
lean_dec_ref(v_c_1996_);
v___x_2014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2014_, 0, v_b_2001_);
return v___x_2014_;
}
else
{
lean_object* v_snd_2015_; lean_object* v___x_2017_; uint8_t v_isShared_2018_; uint8_t v_isSharedCheck_2060_; 
v_snd_2015_ = lean_ctor_get(v_b_2001_, 1);
v_isSharedCheck_2060_ = !lean_is_exclusive(v_b_2001_);
if (v_isSharedCheck_2060_ == 0)
{
lean_object* v_unused_2061_; 
v_unused_2061_ = lean_ctor_get(v_b_2001_, 0);
lean_dec(v_unused_2061_);
v___x_2017_ = v_b_2001_;
v_isShared_2018_ = v_isSharedCheck_2060_;
goto v_resetjp_2016_;
}
else
{
lean_inc(v_snd_2015_);
lean_dec(v_b_2001_);
v___x_2017_ = lean_box(0);
v_isShared_2018_ = v_isSharedCheck_2060_;
goto v_resetjp_2016_;
}
v_resetjp_2016_:
{
lean_object* v_p_2019_; lean_object* v_a_2020_; lean_object* v_p_2021_; lean_object* v___x_2022_; lean_object* v___f_2023_; uint8_t v___x_2054_; 
v_p_2019_ = lean_ctor_get(v_c_1996_, 0);
v_a_2020_ = lean_array_uget_borrowed(v_as_1998_, v_i_2000_);
v_p_2021_ = lean_ctor_get(v_a_2020_, 0);
v___x_2022_ = lean_box(0);
lean_inc(v_x_1997_);
lean_inc_ref(v_p_2021_);
v___f_2023_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2023_, 0, v_p_2021_);
lean_closure_set(v___f_2023_, 1, v_x_1997_);
v___x_2054_ = l_Int_Internal_Linear_instBEqPoly_beq(v_p_2019_, v_p_2021_);
if (v___x_2054_ == 0)
{
uint8_t v___x_2055_; 
v___x_2055_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_2019_, v_p_2021_);
if (v___x_2055_ == 0)
{
lean_object* v___x_2056_; size_t v___x_2057_; size_t v___x_2058_; lean_object* v___x_2059_; 
lean_dec_ref(v___f_2023_);
lean_del_object(v___x_2017_);
lean_dec(v_snd_2015_);
v___x_2056_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___closed__1));
v___x_2057_ = ((size_t)1ULL);
v___x_2058_ = lean_usize_add(v_i_2000_, v___x_2057_);
v___x_2059_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(v_c_1996_, v_x_1997_, v_as_1998_, v_sz_1999_, v___x_2058_, v___x_2056_, v___y_2002_);
return v___x_2059_;
}
else
{
lean_dec(v_x_1997_);
goto v___jp_2024_;
}
}
else
{
lean_dec(v_x_1997_);
goto v___jp_2024_;
}
v___jp_2024_:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2025_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2026_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2025_, v___f_2023_, v___y_2002_);
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
v___x_2030_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0);
lean_inc_ref(v_p_2019_);
v___x_2031_ = l_Int_Internal_Linear_Poly_addConst(v_p_2019_, v___x_2030_);
lean_inc(v_a_2020_);
v___x_2032_ = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(v___x_2032_, 0, v_c_1996_);
lean_ctor_set(v___x_2032_, 1, v_a_2020_);
v___x_2033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2031_);
lean_ctor_set(v___x_2033_, 1, v___x_2032_);
v___x_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2033_);
v___x_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2034_);
if (v_isShared_2018_ == 0)
{
lean_ctor_set(v___x_2017_, 1, v___x_2022_);
lean_ctor_set(v___x_2017_, 0, v___x_2035_);
v___x_2037_ = v___x_2017_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v___x_2035_);
lean_ctor_set(v_reuseFailAlloc_2043_, 1, v___x_2022_);
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
lean_ctor_set(v___x_2039_, 1, v_snd_2015_);
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
lean_del_object(v___x_2017_);
lean_dec(v_snd_2015_);
lean_dec_ref(v_c_1996_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___boxed(lean_object** _args){
lean_object* v_c_2062_ = _args[0];
lean_object* v_x_2063_ = _args[1];
lean_object* v_as_2064_ = _args[2];
lean_object* v_sz_2065_ = _args[3];
lean_object* v_i_2066_ = _args[4];
lean_object* v_b_2067_ = _args[5];
lean_object* v___y_2068_ = _args[6];
lean_object* v___y_2069_ = _args[7];
lean_object* v___y_2070_ = _args[8];
lean_object* v___y_2071_ = _args[9];
lean_object* v___y_2072_ = _args[10];
lean_object* v___y_2073_ = _args[11];
lean_object* v___y_2074_ = _args[12];
lean_object* v___y_2075_ = _args[13];
lean_object* v___y_2076_ = _args[14];
lean_object* v___y_2077_ = _args[15];
lean_object* v___y_2078_ = _args[16];
_start:
{
size_t v_sz_boxed_2079_; size_t v_i_boxed_2080_; lean_object* v_res_2081_; 
v_sz_boxed_2079_ = lean_unbox_usize(v_sz_2065_);
lean_dec(v_sz_2065_);
v_i_boxed_2080_ = lean_unbox_usize(v_i_2066_);
lean_dec(v_i_2066_);
v_res_2081_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7(v_c_2062_, v_x_2063_, v_as_2064_, v_sz_boxed_2079_, v_i_boxed_2080_, v_b_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
lean_dec(v___y_2077_);
lean_dec_ref(v___y_2076_);
lean_dec(v___y_2075_);
lean_dec_ref(v___y_2074_);
lean_dec(v___y_2073_);
lean_dec_ref(v___y_2072_);
lean_dec(v___y_2071_);
lean_dec_ref(v___y_2070_);
lean_dec(v___y_2069_);
lean_dec(v___y_2068_);
lean_dec_ref(v_as_2064_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(lean_object* v_c_2088_, lean_object* v_x_2089_, lean_object* v_as_2090_, size_t v_sz_2091_, size_t v_i_2092_, lean_object* v_b_2093_, lean_object* v___y_2094_){
_start:
{
uint8_t v___x_2096_; 
v___x_2096_ = lean_usize_dec_lt(v_i_2092_, v_sz_2091_);
if (v___x_2096_ == 0)
{
lean_object* v___x_2097_; 
lean_dec(v_x_2089_);
lean_dec_ref(v_c_2088_);
v___x_2097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2097_, 0, v_b_2093_);
return v___x_2097_;
}
else
{
lean_object* v_snd_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2144_; 
v_snd_2098_ = lean_ctor_get(v_b_2093_, 1);
v_isSharedCheck_2144_ = !lean_is_exclusive(v_b_2093_);
if (v_isSharedCheck_2144_ == 0)
{
lean_object* v_unused_2145_; 
v_unused_2145_ = lean_ctor_get(v_b_2093_, 0);
lean_dec(v_unused_2145_);
v___x_2100_ = v_b_2093_;
v_isShared_2101_ = v_isSharedCheck_2144_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_snd_2098_);
lean_dec(v_b_2093_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2144_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v_p_2102_; lean_object* v_a_2103_; lean_object* v_p_2104_; lean_object* v___x_2105_; lean_object* v___f_2106_; uint8_t v___x_2138_; 
v_p_2102_ = lean_ctor_get(v_c_2088_, 0);
v_a_2103_ = lean_array_uget_borrowed(v_as_2090_, v_i_2092_);
v_p_2104_ = lean_ctor_get(v_a_2103_, 0);
v___x_2105_ = lean_box(0);
lean_inc(v_x_2089_);
lean_inc_ref(v_p_2104_);
v___f_2106_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2106_, 0, v_p_2104_);
lean_closure_set(v___f_2106_, 1, v_x_2089_);
v___x_2138_ = l_Int_Internal_Linear_instBEqPoly_beq(v_p_2102_, v_p_2104_);
if (v___x_2138_ == 0)
{
uint8_t v___x_2139_; 
v___x_2139_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_2102_, v_p_2104_);
if (v___x_2139_ == 0)
{
lean_object* v___x_2140_; size_t v___x_2141_; size_t v___x_2142_; 
lean_dec_ref(v___f_2106_);
lean_del_object(v___x_2100_);
lean_dec(v_snd_2098_);
v___x_2140_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg___closed__1));
v___x_2141_ = ((size_t)1ULL);
v___x_2142_ = lean_usize_add(v_i_2092_, v___x_2141_);
v_i_2092_ = v___x_2142_;
v_b_2093_ = v___x_2140_;
goto _start;
}
else
{
lean_dec(v_x_2089_);
goto v___jp_2107_;
}
}
else
{
lean_dec(v_x_2089_);
goto v___jp_2107_;
}
v___jp_2107_:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2108_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2109_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2108_, v___f_2106_, v___y_2094_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2128_; 
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2128_ == 0)
{
lean_object* v_unused_2129_; 
v_unused_2129_ = lean_ctor_get(v___x_2109_, 0);
lean_dec(v_unused_2129_);
v___x_2111_ = v___x_2109_;
v_isShared_2112_ = v_isSharedCheck_2128_;
goto v_resetjp_2110_;
}
else
{
lean_dec(v___x_2109_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2128_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2120_; 
v___x_2113_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0);
lean_inc_ref(v_p_2102_);
v___x_2114_ = l_Int_Internal_Linear_Poly_addConst(v_p_2102_, v___x_2113_);
lean_inc(v_a_2103_);
v___x_2115_ = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(v___x_2115_, 0, v_c_2088_);
lean_ctor_set(v___x_2115_, 1, v_a_2103_);
v___x_2116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2114_);
lean_ctor_set(v___x_2116_, 1, v___x_2115_);
v___x_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2116_);
v___x_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
if (v_isShared_2101_ == 0)
{
lean_ctor_set(v___x_2100_, 1, v___x_2105_);
lean_ctor_set(v___x_2100_, 0, v___x_2118_);
v___x_2120_ = v___x_2100_;
goto v_reusejp_2119_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v___x_2118_);
lean_ctor_set(v_reuseFailAlloc_2127_, 1, v___x_2105_);
v___x_2120_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2119_;
}
v_reusejp_2119_:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2125_; 
v___x_2121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2120_);
v___x_2122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2121_);
v___x_2123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2123_, 0, v___x_2122_);
lean_ctor_set(v___x_2123_, 1, v_snd_2098_);
if (v_isShared_2112_ == 0)
{
lean_ctor_set(v___x_2111_, 0, v___x_2123_);
v___x_2125_ = v___x_2111_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v___x_2123_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
else
{
lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2137_; 
lean_del_object(v___x_2100_);
lean_dec(v_snd_2098_);
lean_dec_ref(v_c_2088_);
v_a_2130_ = lean_ctor_get(v___x_2109_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2132_ = v___x_2109_;
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___x_2109_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2135_; 
if (v_isShared_2133_ == 0)
{
v___x_2135_ = v___x_2132_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_a_2130_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg___boxed(lean_object* v_c_2146_, lean_object* v_x_2147_, lean_object* v_as_2148_, lean_object* v_sz_2149_, lean_object* v_i_2150_, lean_object* v_b_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_){
_start:
{
size_t v_sz_boxed_2154_; size_t v_i_boxed_2155_; lean_object* v_res_2156_; 
v_sz_boxed_2154_ = lean_unbox_usize(v_sz_2149_);
lean_dec(v_sz_2149_);
v_i_boxed_2155_ = lean_unbox_usize(v_i_2150_);
lean_dec(v_i_2150_);
v_res_2156_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(v_c_2146_, v_x_2147_, v_as_2148_, v_sz_boxed_2154_, v_i_boxed_2155_, v_b_2151_, v___y_2152_);
lean_dec(v___y_2152_);
lean_dec_ref(v_as_2148_);
return v_res_2156_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9(lean_object* v_c_2160_, lean_object* v_x_2161_, lean_object* v_as_2162_, size_t v_sz_2163_, size_t v_i_2164_, lean_object* v_b_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_){
_start:
{
uint8_t v___x_2177_; 
v___x_2177_ = lean_usize_dec_lt(v_i_2164_, v_sz_2163_);
if (v___x_2177_ == 0)
{
lean_object* v___x_2178_; 
lean_dec(v_x_2161_);
lean_dec_ref(v_c_2160_);
v___x_2178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2178_, 0, v_b_2165_);
return v___x_2178_;
}
else
{
lean_object* v_snd_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2225_; 
v_snd_2179_ = lean_ctor_get(v_b_2165_, 1);
v_isSharedCheck_2225_ = !lean_is_exclusive(v_b_2165_);
if (v_isSharedCheck_2225_ == 0)
{
lean_object* v_unused_2226_; 
v_unused_2226_ = lean_ctor_get(v_b_2165_, 0);
lean_dec(v_unused_2226_);
v___x_2181_ = v_b_2165_;
v_isShared_2182_ = v_isSharedCheck_2225_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_snd_2179_);
lean_dec(v_b_2165_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2225_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v_p_2183_; lean_object* v_a_2184_; lean_object* v_p_2185_; lean_object* v___x_2186_; lean_object* v___f_2187_; uint8_t v___x_2219_; 
v_p_2183_ = lean_ctor_get(v_c_2160_, 0);
v_a_2184_ = lean_array_uget_borrowed(v_as_2162_, v_i_2164_);
v_p_2185_ = lean_ctor_get(v_a_2184_, 0);
v___x_2186_ = lean_box(0);
lean_inc(v_x_2161_);
lean_inc_ref(v_p_2185_);
v___f_2187_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2187_, 0, v_p_2185_);
lean_closure_set(v___f_2187_, 1, v_x_2161_);
v___x_2219_ = l_Int_Internal_Linear_instBEqPoly_beq(v_p_2183_, v_p_2185_);
if (v___x_2219_ == 0)
{
uint8_t v___x_2220_; 
v___x_2220_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_2183_, v_p_2185_);
if (v___x_2220_ == 0)
{
lean_object* v___x_2221_; size_t v___x_2222_; size_t v___x_2223_; lean_object* v___x_2224_; 
lean_dec_ref(v___f_2187_);
lean_del_object(v___x_2181_);
lean_dec(v_snd_2179_);
v___x_2221_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9___closed__0));
v___x_2222_ = ((size_t)1ULL);
v___x_2223_ = lean_usize_add(v_i_2164_, v___x_2222_);
v___x_2224_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(v_c_2160_, v_x_2161_, v_as_2162_, v_sz_2163_, v___x_2223_, v___x_2221_, v___y_2166_);
return v___x_2224_;
}
else
{
lean_dec(v_x_2161_);
goto v___jp_2188_;
}
}
else
{
lean_dec(v_x_2161_);
goto v___jp_2188_;
}
v___jp_2188_:
{
lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2189_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2190_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2189_, v___f_2187_, v___y_2166_);
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
v___x_2194_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0);
lean_inc_ref(v_p_2183_);
v___x_2195_ = l_Int_Internal_Linear_Poly_addConst(v_p_2183_, v___x_2194_);
lean_inc(v_a_2184_);
v___x_2196_ = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(v___x_2196_, 0, v_c_2160_);
lean_ctor_set(v___x_2196_, 1, v_a_2184_);
v___x_2197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2195_);
lean_ctor_set(v___x_2197_, 1, v___x_2196_);
v___x_2198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2198_, 0, v___x_2197_);
v___x_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2198_);
if (v_isShared_2182_ == 0)
{
lean_ctor_set(v___x_2181_, 1, v___x_2186_);
lean_ctor_set(v___x_2181_, 0, v___x_2199_);
v___x_2201_ = v___x_2181_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v___x_2199_);
lean_ctor_set(v_reuseFailAlloc_2208_, 1, v___x_2186_);
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
lean_ctor_set(v___x_2204_, 1, v_snd_2179_);
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
lean_del_object(v___x_2181_);
lean_dec(v_snd_2179_);
lean_dec_ref(v_c_2160_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9___boxed(lean_object** _args){
lean_object* v_c_2227_ = _args[0];
lean_object* v_x_2228_ = _args[1];
lean_object* v_as_2229_ = _args[2];
lean_object* v_sz_2230_ = _args[3];
lean_object* v_i_2231_ = _args[4];
lean_object* v_b_2232_ = _args[5];
lean_object* v___y_2233_ = _args[6];
lean_object* v___y_2234_ = _args[7];
lean_object* v___y_2235_ = _args[8];
lean_object* v___y_2236_ = _args[9];
lean_object* v___y_2237_ = _args[10];
lean_object* v___y_2238_ = _args[11];
lean_object* v___y_2239_ = _args[12];
lean_object* v___y_2240_ = _args[13];
lean_object* v___y_2241_ = _args[14];
lean_object* v___y_2242_ = _args[15];
lean_object* v___y_2243_ = _args[16];
_start:
{
size_t v_sz_boxed_2244_; size_t v_i_boxed_2245_; lean_object* v_res_2246_; 
v_sz_boxed_2244_ = lean_unbox_usize(v_sz_2230_);
lean_dec(v_sz_2230_);
v_i_boxed_2245_ = lean_unbox_usize(v_i_2231_);
lean_dec(v_i_2231_);
v_res_2246_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9(v_c_2227_, v_x_2228_, v_as_2229_, v_sz_boxed_2244_, v_i_boxed_2245_, v_b_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_);
lean_dec(v___y_2242_);
lean_dec_ref(v___y_2241_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
lean_dec(v___y_2234_);
lean_dec(v___y_2233_);
lean_dec_ref(v_as_2229_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(lean_object* v_init_2247_, lean_object* v_c_2248_, lean_object* v_x_2249_, lean_object* v_n_2250_, lean_object* v_b_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_){
_start:
{
if (lean_obj_tag(v_n_2250_) == 0)
{
lean_object* v_cs_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; size_t v_sz_2266_; size_t v___x_2267_; lean_object* v___x_2268_; 
v_cs_2263_ = lean_ctor_get(v_n_2250_, 0);
v___x_2264_ = lean_box(0);
v___x_2265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2265_, 0, v___x_2264_);
lean_ctor_set(v___x_2265_, 1, v_b_2251_);
v_sz_2266_ = lean_array_size(v_cs_2263_);
v___x_2267_ = ((size_t)0ULL);
v___x_2268_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8(v_init_2247_, v_c_2248_, v_x_2249_, v_cs_2263_, v_sz_2266_, v___x_2267_, v___x_2265_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_);
if (lean_obj_tag(v___x_2268_) == 0)
{
lean_object* v_a_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2283_; 
v_a_2269_ = lean_ctor_get(v___x_2268_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2271_ = v___x_2268_;
v_isShared_2272_ = v_isSharedCheck_2283_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_a_2269_);
lean_dec(v___x_2268_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2283_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v_fst_2273_; 
v_fst_2273_ = lean_ctor_get(v_a_2269_, 0);
if (lean_obj_tag(v_fst_2273_) == 0)
{
lean_object* v_snd_2274_; lean_object* v___x_2275_; lean_object* v___x_2277_; 
v_snd_2274_ = lean_ctor_get(v_a_2269_, 1);
lean_inc(v_snd_2274_);
lean_dec(v_a_2269_);
v___x_2275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2275_, 0, v_snd_2274_);
if (v_isShared_2272_ == 0)
{
lean_ctor_set(v___x_2271_, 0, v___x_2275_);
v___x_2277_ = v___x_2271_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v___x_2275_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
else
{
lean_object* v_val_2279_; lean_object* v___x_2281_; 
lean_inc_ref(v_fst_2273_);
lean_dec(v_a_2269_);
v_val_2279_ = lean_ctor_get(v_fst_2273_, 0);
lean_inc(v_val_2279_);
lean_dec_ref_known(v_fst_2273_, 1);
if (v_isShared_2272_ == 0)
{
lean_ctor_set(v___x_2271_, 0, v_val_2279_);
v___x_2281_ = v___x_2271_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_val_2279_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
}
else
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2291_; 
v_a_2284_ = lean_ctor_get(v___x_2268_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2286_ = v___x_2268_;
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2268_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2289_; 
if (v_isShared_2287_ == 0)
{
v___x_2289_ = v___x_2286_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_a_2284_);
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
lean_object* v_vs_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; size_t v_sz_2295_; size_t v___x_2296_; lean_object* v___x_2297_; 
v_vs_2292_ = lean_ctor_get(v_n_2250_, 0);
v___x_2293_ = lean_box(0);
v___x_2294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2294_, 0, v___x_2293_);
lean_ctor_set(v___x_2294_, 1, v_b_2251_);
v_sz_2295_ = lean_array_size(v_vs_2292_);
v___x_2296_ = ((size_t)0ULL);
v___x_2297_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9(v_c_2248_, v_x_2249_, v_vs_2292_, v_sz_2295_, v___x_2296_, v___x_2294_, v___y_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_);
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2312_; 
v_a_2298_ = lean_ctor_get(v___x_2297_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2300_ = v___x_2297_;
v_isShared_2301_ = v_isSharedCheck_2312_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2297_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2312_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v_fst_2302_; 
v_fst_2302_ = lean_ctor_get(v_a_2298_, 0);
if (lean_obj_tag(v_fst_2302_) == 0)
{
lean_object* v_snd_2303_; lean_object* v___x_2304_; lean_object* v___x_2306_; 
v_snd_2303_ = lean_ctor_get(v_a_2298_, 1);
lean_inc(v_snd_2303_);
lean_dec(v_a_2298_);
v___x_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2304_, 0, v_snd_2303_);
if (v_isShared_2301_ == 0)
{
lean_ctor_set(v___x_2300_, 0, v___x_2304_);
v___x_2306_ = v___x_2300_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v___x_2304_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
else
{
lean_object* v_val_2308_; lean_object* v___x_2310_; 
lean_inc_ref(v_fst_2302_);
lean_dec(v_a_2298_);
v_val_2308_ = lean_ctor_get(v_fst_2302_, 0);
lean_inc(v_val_2308_);
lean_dec_ref_known(v_fst_2302_, 1);
if (v_isShared_2301_ == 0)
{
lean_ctor_set(v___x_2300_, 0, v_val_2308_);
v___x_2310_ = v___x_2300_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_val_2308_);
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
else
{
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2320_; 
v_a_2313_ = lean_ctor_get(v___x_2297_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2315_ = v___x_2297_;
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2297_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2318_; 
if (v_isShared_2316_ == 0)
{
v___x_2318_ = v___x_2315_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2313_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8(lean_object* v_init_2321_, lean_object* v_c_2322_, lean_object* v_x_2323_, lean_object* v_as_2324_, size_t v_sz_2325_, size_t v_i_2326_, lean_object* v_b_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
uint8_t v___x_2339_; 
v___x_2339_ = lean_usize_dec_lt(v_i_2326_, v_sz_2325_);
if (v___x_2339_ == 0)
{
lean_object* v___x_2340_; 
lean_dec(v_x_2323_);
lean_dec_ref(v_c_2322_);
v___x_2340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2340_, 0, v_b_2327_);
return v___x_2340_;
}
else
{
lean_object* v_snd_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2375_; 
v_snd_2341_ = lean_ctor_get(v_b_2327_, 1);
v_isSharedCheck_2375_ = !lean_is_exclusive(v_b_2327_);
if (v_isSharedCheck_2375_ == 0)
{
lean_object* v_unused_2376_; 
v_unused_2376_ = lean_ctor_get(v_b_2327_, 0);
lean_dec(v_unused_2376_);
v___x_2343_ = v_b_2327_;
v_isShared_2344_ = v_isSharedCheck_2375_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_snd_2341_);
lean_dec(v_b_2327_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2375_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___x_2345_; lean_object* v_a_2346_; lean_object* v___x_2347_; 
v___x_2345_ = lean_box(0);
v_a_2346_ = lean_array_uget_borrowed(v_as_2324_, v_i_2326_);
lean_inc(v_snd_2341_);
lean_inc(v_x_2323_);
lean_inc_ref(v_c_2322_);
v___x_2347_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(v_init_2321_, v_c_2322_, v_x_2323_, v_a_2346_, v_snd_2341_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2366_; 
v_a_2348_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2366_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2366_ == 0)
{
v___x_2350_ = v___x_2347_;
v_isShared_2351_ = v_isSharedCheck_2366_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___x_2347_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2366_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
if (lean_obj_tag(v_a_2348_) == 0)
{
lean_object* v___x_2352_; lean_object* v___x_2354_; 
lean_dec(v_x_2323_);
lean_dec_ref(v_c_2322_);
v___x_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2352_, 0, v_a_2348_);
if (v_isShared_2344_ == 0)
{
lean_ctor_set(v___x_2343_, 0, v___x_2352_);
v___x_2354_ = v___x_2343_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v___x_2352_);
lean_ctor_set(v_reuseFailAlloc_2358_, 1, v_snd_2341_);
v___x_2354_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
lean_object* v___x_2356_; 
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
}
else
{
lean_object* v_a_2359_; lean_object* v___x_2361_; 
lean_del_object(v___x_2350_);
lean_dec(v_snd_2341_);
v_a_2359_ = lean_ctor_get(v_a_2348_, 0);
lean_inc(v_a_2359_);
lean_dec_ref_known(v_a_2348_, 1);
if (v_isShared_2344_ == 0)
{
lean_ctor_set(v___x_2343_, 1, v_a_2359_);
lean_ctor_set(v___x_2343_, 0, v___x_2345_);
v___x_2361_ = v___x_2343_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2365_; 
v_reuseFailAlloc_2365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2365_, 0, v___x_2345_);
lean_ctor_set(v_reuseFailAlloc_2365_, 1, v_a_2359_);
v___x_2361_ = v_reuseFailAlloc_2365_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
size_t v___x_2362_; size_t v___x_2363_; 
v___x_2362_ = ((size_t)1ULL);
v___x_2363_ = lean_usize_add(v_i_2326_, v___x_2362_);
v_i_2326_ = v___x_2363_;
v_b_2327_ = v___x_2361_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2374_; 
lean_del_object(v___x_2343_);
lean_dec(v_snd_2341_);
lean_dec(v_x_2323_);
lean_dec_ref(v_c_2322_);
v_a_2367_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2369_ = v___x_2347_;
v_isShared_2370_ = v_isSharedCheck_2374_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v___x_2347_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8___boxed(lean_object** _args){
lean_object* v_init_2377_ = _args[0];
lean_object* v_c_2378_ = _args[1];
lean_object* v_x_2379_ = _args[2];
lean_object* v_as_2380_ = _args[3];
lean_object* v_sz_2381_ = _args[4];
lean_object* v_i_2382_ = _args[5];
lean_object* v_b_2383_ = _args[6];
lean_object* v___y_2384_ = _args[7];
lean_object* v___y_2385_ = _args[8];
lean_object* v___y_2386_ = _args[9];
lean_object* v___y_2387_ = _args[10];
lean_object* v___y_2388_ = _args[11];
lean_object* v___y_2389_ = _args[12];
lean_object* v___y_2390_ = _args[13];
lean_object* v___y_2391_ = _args[14];
lean_object* v___y_2392_ = _args[15];
lean_object* v___y_2393_ = _args[16];
lean_object* v___y_2394_ = _args[17];
_start:
{
size_t v_sz_boxed_2395_; size_t v_i_boxed_2396_; lean_object* v_res_2397_; 
v_sz_boxed_2395_ = lean_unbox_usize(v_sz_2381_);
lean_dec(v_sz_2381_);
v_i_boxed_2396_ = lean_unbox_usize(v_i_2382_);
lean_dec(v_i_2382_);
v_res_2397_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8(v_init_2377_, v_c_2378_, v_x_2379_, v_as_2380_, v_sz_boxed_2395_, v_i_boxed_2396_, v_b_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_);
lean_dec(v___y_2393_);
lean_dec_ref(v___y_2392_);
lean_dec(v___y_2391_);
lean_dec_ref(v___y_2390_);
lean_dec(v___y_2389_);
lean_dec_ref(v___y_2388_);
lean_dec(v___y_2387_);
lean_dec_ref(v___y_2386_);
lean_dec(v___y_2385_);
lean_dec(v___y_2384_);
lean_dec_ref(v_as_2380_);
lean_dec_ref(v_init_2377_);
return v_res_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6___boxed(lean_object* v_init_2398_, lean_object* v_c_2399_, lean_object* v_x_2400_, lean_object* v_n_2401_, lean_object* v_b_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_){
_start:
{
lean_object* v_res_2414_; 
v_res_2414_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(v_init_2398_, v_c_2399_, v_x_2400_, v_n_2401_, v_b_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec(v___y_2404_);
lean_dec(v___y_2403_);
lean_dec_ref(v_n_2401_);
lean_dec_ref(v_init_2398_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2(lean_object* v_c_2415_, lean_object* v_x_2416_, lean_object* v_t_2417_, lean_object* v_init_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_){
_start:
{
lean_object* v_root_2430_; lean_object* v_tail_2431_; lean_object* v___x_2432_; 
v_root_2430_ = lean_ctor_get(v_t_2417_, 0);
v_tail_2431_ = lean_ctor_get(v_t_2417_, 1);
lean_inc(v_x_2416_);
lean_inc_ref(v_c_2415_);
lean_inc_ref(v_init_2418_);
v___x_2432_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(v_init_2418_, v_c_2415_, v_x_2416_, v_root_2430_, v_init_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
lean_dec_ref(v_init_2418_);
if (lean_obj_tag(v___x_2432_) == 0)
{
lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2469_; 
v_a_2433_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2435_ = v___x_2432_;
v_isShared_2436_ = v_isSharedCheck_2469_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_dec(v___x_2432_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2469_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
if (lean_obj_tag(v_a_2433_) == 0)
{
lean_object* v_a_2437_; lean_object* v___x_2439_; 
lean_dec(v_x_2416_);
lean_dec_ref(v_c_2415_);
v_a_2437_ = lean_ctor_get(v_a_2433_, 0);
lean_inc(v_a_2437_);
lean_dec_ref_known(v_a_2433_, 1);
if (v_isShared_2436_ == 0)
{
lean_ctor_set(v___x_2435_, 0, v_a_2437_);
v___x_2439_ = v___x_2435_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v_a_2437_);
v___x_2439_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
return v___x_2439_;
}
}
else
{
lean_object* v_a_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; size_t v_sz_2444_; size_t v___x_2445_; lean_object* v___x_2446_; 
lean_del_object(v___x_2435_);
v_a_2441_ = lean_ctor_get(v_a_2433_, 0);
lean_inc(v_a_2441_);
lean_dec_ref_known(v_a_2433_, 1);
v___x_2442_ = lean_box(0);
v___x_2443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2443_, 0, v___x_2442_);
lean_ctor_set(v___x_2443_, 1, v_a_2441_);
v_sz_2444_ = lean_array_size(v_tail_2431_);
v___x_2445_ = ((size_t)0ULL);
v___x_2446_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7(v_c_2415_, v_x_2416_, v_tail_2431_, v_sz_2444_, v___x_2445_, v___x_2443_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
if (lean_obj_tag(v___x_2446_) == 0)
{
lean_object* v_a_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2460_; 
v_a_2447_ = lean_ctor_get(v___x_2446_, 0);
v_isSharedCheck_2460_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2449_ = v___x_2446_;
v_isShared_2450_ = v_isSharedCheck_2460_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_a_2447_);
lean_dec(v___x_2446_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2460_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v_fst_2451_; 
v_fst_2451_ = lean_ctor_get(v_a_2447_, 0);
if (lean_obj_tag(v_fst_2451_) == 0)
{
lean_object* v_snd_2452_; lean_object* v___x_2454_; 
v_snd_2452_ = lean_ctor_get(v_a_2447_, 1);
lean_inc(v_snd_2452_);
lean_dec(v_a_2447_);
if (v_isShared_2450_ == 0)
{
lean_ctor_set(v___x_2449_, 0, v_snd_2452_);
v___x_2454_ = v___x_2449_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_snd_2452_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
return v___x_2454_;
}
}
else
{
lean_object* v_val_2456_; lean_object* v___x_2458_; 
lean_inc_ref(v_fst_2451_);
lean_dec(v_a_2447_);
v_val_2456_ = lean_ctor_get(v_fst_2451_, 0);
lean_inc(v_val_2456_);
lean_dec_ref_known(v_fst_2451_, 1);
if (v_isShared_2450_ == 0)
{
lean_ctor_set(v___x_2449_, 0, v_val_2456_);
v___x_2458_ = v___x_2449_;
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
v_a_2461_ = lean_ctor_get(v___x_2446_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2463_ = v___x_2446_;
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v___x_2446_);
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
}
else
{
lean_object* v_a_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2477_; 
lean_dec(v_x_2416_);
lean_dec_ref(v_c_2415_);
v_a_2470_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2472_ = v___x_2432_;
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_a_2470_);
lean_dec(v___x_2432_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2475_; 
if (v_isShared_2473_ == 0)
{
v___x_2475_ = v___x_2472_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_a_2470_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
return v___x_2475_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2___boxed(lean_object* v_c_2478_, lean_object* v_x_2479_, lean_object* v_t_2480_, lean_object* v_init_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_){
_start:
{
lean_object* v_res_2493_; 
v_res_2493_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2(v_c_2478_, v_x_2479_, v_t_2480_, v_init_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
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
lean_dec_ref(v_t_2480_);
return v_res_2493_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(lean_object* v_x_2494_, lean_object* v_c_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_){
_start:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2507_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0);
v___x_2508_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2496_, v_a_2504_);
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_object* v_a_2509_; lean_object* v___y_2511_; lean_object* v_diseqs_2536_; lean_object* v_size_2537_; uint8_t v___x_2538_; 
v_a_2509_ = lean_ctor_get(v___x_2508_, 0);
lean_inc(v_a_2509_);
lean_dec_ref_known(v___x_2508_, 1);
v_diseqs_2536_ = lean_ctor_get(v_a_2509_, 8);
lean_inc_ref(v_diseqs_2536_);
lean_dec(v_a_2509_);
v_size_2537_ = lean_ctor_get(v_diseqs_2536_, 2);
v___x_2538_ = lean_nat_dec_lt(v_x_2494_, v_size_2537_);
if (v___x_2538_ == 0)
{
lean_object* v___x_2539_; 
lean_dec_ref(v_diseqs_2536_);
v___x_2539_ = l_outOfBounds___redArg(v___x_2507_);
v___y_2511_ = v___x_2539_;
goto v___jp_2510_;
}
else
{
lean_object* v___x_2540_; 
v___x_2540_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2507_, v_diseqs_2536_, v_x_2494_);
lean_dec_ref(v_diseqs_2536_);
v___y_2511_ = v___x_2540_;
goto v___jp_2510_;
}
v___jp_2510_:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2512_ = lean_box(0);
v___x_2513_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___closed__0));
v___x_2514_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2(v_c_2495_, v_x_2494_, v___y_2511_, v___x_2513_, v_a_2496_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_);
lean_dec_ref(v___y_2511_);
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_object* v_a_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2527_; 
v_a_2515_ = lean_ctor_get(v___x_2514_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2514_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2517_ = v___x_2514_;
v_isShared_2518_ = v_isSharedCheck_2527_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_a_2515_);
lean_dec(v___x_2514_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2527_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v_fst_2519_; 
v_fst_2519_ = lean_ctor_get(v_a_2515_, 0);
lean_inc(v_fst_2519_);
lean_dec(v_a_2515_);
if (lean_obj_tag(v_fst_2519_) == 0)
{
lean_object* v___x_2521_; 
if (v_isShared_2518_ == 0)
{
lean_ctor_set(v___x_2517_, 0, v___x_2512_);
v___x_2521_ = v___x_2517_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v___x_2512_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
else
{
lean_object* v_val_2523_; lean_object* v___x_2525_; 
v_val_2523_ = lean_ctor_get(v_fst_2519_, 0);
lean_inc(v_val_2523_);
lean_dec_ref_known(v_fst_2519_, 1);
if (v_isShared_2518_ == 0)
{
lean_ctor_set(v___x_2517_, 0, v_val_2523_);
v___x_2525_ = v___x_2517_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v_val_2523_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
}
}
else
{
lean_object* v_a_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2535_; 
v_a_2528_ = lean_ctor_get(v___x_2514_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2514_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2530_ = v___x_2514_;
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_a_2528_);
lean_dec(v___x_2514_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2533_; 
if (v_isShared_2531_ == 0)
{
v___x_2533_ = v___x_2530_;
goto v_reusejp_2532_;
}
else
{
lean_object* v_reuseFailAlloc_2534_; 
v_reuseFailAlloc_2534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2534_, 0, v_a_2528_);
v___x_2533_ = v_reuseFailAlloc_2534_;
goto v_reusejp_2532_;
}
v_reusejp_2532_:
{
return v___x_2533_;
}
}
}
}
}
else
{
lean_object* v_a_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2548_; 
lean_dec_ref(v_c_2495_);
lean_dec(v_x_2494_);
v_a_2541_ = lean_ctor_get(v___x_2508_, 0);
v_isSharedCheck_2548_ = !lean_is_exclusive(v___x_2508_);
if (v_isSharedCheck_2548_ == 0)
{
v___x_2543_ = v___x_2508_;
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_a_2541_);
lean_dec(v___x_2508_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2548_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2546_; 
if (v_isShared_2544_ == 0)
{
v___x_2546_ = v___x_2543_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v_a_2541_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f___boxed(lean_object* v_x_2549_, lean_object* v_c_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_){
_start:
{
lean_object* v_res_2562_; 
v_res_2562_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(v_x_2549_, v_c_2550_, v_a_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_);
lean_dec(v_a_2560_);
lean_dec_ref(v_a_2559_);
lean_dec(v_a_2558_);
lean_dec_ref(v_a_2557_);
lean_dec(v_a_2556_);
lean_dec_ref(v_a_2555_);
lean_dec(v_a_2554_);
lean_dec_ref(v_a_2553_);
lean_dec(v_a_2552_);
lean_dec(v_a_2551_);
return v_res_2562_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11(lean_object* v_c_2563_, lean_object* v_x_2564_, lean_object* v_as_2565_, size_t v_sz_2566_, size_t v_i_2567_, lean_object* v_b_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_){
_start:
{
lean_object* v___x_2580_; 
v___x_2580_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(v_c_2563_, v_x_2564_, v_as_2565_, v_sz_2566_, v_i_2567_, v_b_2568_, v___y_2569_);
return v___x_2580_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___boxed(lean_object** _args){
lean_object* v_c_2581_ = _args[0];
lean_object* v_x_2582_ = _args[1];
lean_object* v_as_2583_ = _args[2];
lean_object* v_sz_2584_ = _args[3];
lean_object* v_i_2585_ = _args[4];
lean_object* v_b_2586_ = _args[5];
lean_object* v___y_2587_ = _args[6];
lean_object* v___y_2588_ = _args[7];
lean_object* v___y_2589_ = _args[8];
lean_object* v___y_2590_ = _args[9];
lean_object* v___y_2591_ = _args[10];
lean_object* v___y_2592_ = _args[11];
lean_object* v___y_2593_ = _args[12];
lean_object* v___y_2594_ = _args[13];
lean_object* v___y_2595_ = _args[14];
lean_object* v___y_2596_ = _args[15];
lean_object* v___y_2597_ = _args[16];
_start:
{
size_t v_sz_boxed_2598_; size_t v_i_boxed_2599_; lean_object* v_res_2600_; 
v_sz_boxed_2598_ = lean_unbox_usize(v_sz_2584_);
lean_dec(v_sz_2584_);
v_i_boxed_2599_ = lean_unbox_usize(v_i_2585_);
lean_dec(v_i_2585_);
v_res_2600_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11(v_c_2581_, v_x_2582_, v_as_2583_, v_sz_boxed_2598_, v_i_boxed_2599_, v_b_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_);
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
lean_dec_ref(v_as_2583_);
return v_res_2600_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10(lean_object* v_c_2601_, lean_object* v_x_2602_, lean_object* v_as_2603_, size_t v_sz_2604_, size_t v_i_2605_, lean_object* v_b_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_){
_start:
{
lean_object* v___x_2618_; 
v___x_2618_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(v_c_2601_, v_x_2602_, v_as_2603_, v_sz_2604_, v_i_2605_, v_b_2606_, v___y_2607_);
return v___x_2618_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___boxed(lean_object** _args){
lean_object* v_c_2619_ = _args[0];
lean_object* v_x_2620_ = _args[1];
lean_object* v_as_2621_ = _args[2];
lean_object* v_sz_2622_ = _args[3];
lean_object* v_i_2623_ = _args[4];
lean_object* v_b_2624_ = _args[5];
lean_object* v___y_2625_ = _args[6];
lean_object* v___y_2626_ = _args[7];
lean_object* v___y_2627_ = _args[8];
lean_object* v___y_2628_ = _args[9];
lean_object* v___y_2629_ = _args[10];
lean_object* v___y_2630_ = _args[11];
lean_object* v___y_2631_ = _args[12];
lean_object* v___y_2632_ = _args[13];
lean_object* v___y_2633_ = _args[14];
lean_object* v___y_2634_ = _args[15];
lean_object* v___y_2635_ = _args[16];
_start:
{
size_t v_sz_boxed_2636_; size_t v_i_boxed_2637_; lean_object* v_res_2638_; 
v_sz_boxed_2636_ = lean_unbox_usize(v_sz_2622_);
lean_dec(v_sz_2622_);
v_i_boxed_2637_ = lean_unbox_usize(v_i_2623_);
lean_dec(v_i_2623_);
v_res_2638_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10(v_c_2619_, v_x_2620_, v_as_2621_, v_sz_boxed_2636_, v_i_boxed_2637_, v_b_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_);
lean_dec(v___y_2634_);
lean_dec_ref(v___y_2633_);
lean_dec(v___y_2632_);
lean_dec_ref(v___y_2631_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
lean_dec(v___y_2626_);
lean_dec(v___y_2625_);
lean_dec_ref(v_as_2621_);
return v_res_2638_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg(lean_object* v_v_2639_, lean_object* v_a_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_){
_start:
{
lean_object* v_snd_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2683_; 
v_snd_2652_ = lean_ctor_get(v_a_2640_, 1);
v_isSharedCheck_2683_ = !lean_is_exclusive(v_a_2640_);
if (v_isSharedCheck_2683_ == 0)
{
lean_object* v_unused_2684_; 
v_unused_2684_ = lean_ctor_get(v_a_2640_, 0);
lean_dec(v_unused_2684_);
v___x_2654_ = v_a_2640_;
v_isShared_2655_ = v_isSharedCheck_2683_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_snd_2652_);
lean_dec(v_a_2640_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2683_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2656_; lean_object* v___x_2657_; 
v___x_2656_ = lean_box(0);
lean_inc(v_snd_2652_);
lean_inc(v_v_2639_);
v___x_2657_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(v_v_2639_, v_snd_2652_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_);
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_object* v_a_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2674_; 
v_a_2658_ = lean_ctor_get(v___x_2657_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2660_ = v___x_2657_;
v_isShared_2661_ = v_isSharedCheck_2674_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_a_2658_);
lean_dec(v___x_2657_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2674_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
if (lean_obj_tag(v_a_2658_) == 1)
{
lean_object* v_val_2662_; lean_object* v___x_2664_; 
lean_del_object(v___x_2660_);
lean_dec(v_snd_2652_);
v_val_2662_ = lean_ctor_get(v_a_2658_, 0);
lean_inc(v_val_2662_);
lean_dec_ref_known(v_a_2658_, 1);
if (v_isShared_2655_ == 0)
{
lean_ctor_set(v___x_2654_, 1, v_val_2662_);
lean_ctor_set(v___x_2654_, 0, v___x_2656_);
v___x_2664_ = v___x_2654_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v___x_2656_);
lean_ctor_set(v_reuseFailAlloc_2666_, 1, v_val_2662_);
v___x_2664_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
v_a_2640_ = v___x_2664_;
goto _start;
}
}
else
{
lean_object* v___x_2667_; lean_object* v___x_2669_; 
lean_dec(v_a_2658_);
lean_dec(v_v_2639_);
lean_inc(v_snd_2652_);
v___x_2667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2667_, 0, v_snd_2652_);
if (v_isShared_2655_ == 0)
{
lean_ctor_set(v___x_2654_, 0, v___x_2667_);
v___x_2669_ = v___x_2654_;
goto v_reusejp_2668_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v___x_2667_);
lean_ctor_set(v_reuseFailAlloc_2673_, 1, v_snd_2652_);
v___x_2669_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2668_;
}
v_reusejp_2668_:
{
lean_object* v___x_2671_; 
if (v_isShared_2661_ == 0)
{
lean_ctor_set(v___x_2660_, 0, v___x_2669_);
v___x_2671_ = v___x_2660_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v___x_2669_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
return v___x_2671_;
}
}
}
}
}
else
{
lean_object* v_a_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2682_; 
lean_del_object(v___x_2654_);
lean_dec(v_snd_2652_);
lean_dec(v_v_2639_);
v_a_2675_ = lean_ctor_get(v___x_2657_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2657_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2677_ = v___x_2657_;
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_a_2675_);
lean_dec(v___x_2657_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2680_; 
if (v_isShared_2678_ == 0)
{
v___x_2680_ = v___x_2677_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_a_2675_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg___boxed(lean_object* v_v_2685_, lean_object* v_a_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_){
_start:
{
lean_object* v_res_2698_; 
v_res_2698_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg(v_v_2685_, v_a_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_);
lean_dec(v___y_2696_);
lean_dec_ref(v___y_2695_);
lean_dec(v___y_2694_);
lean_dec_ref(v___y_2693_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
lean_dec(v___y_2690_);
lean_dec_ref(v___y_2689_);
lean_dec(v___y_2688_);
lean_dec(v___y_2687_);
return v_res_2698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(lean_object* v_c_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_){
_start:
{
lean_object* v_p_2711_; 
v_p_2711_ = lean_ctor_get(v_c_2699_, 0);
if (lean_obj_tag(v_p_2711_) == 1)
{
lean_object* v_v_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
v_v_2712_ = lean_ctor_get(v_p_2711_, 1);
lean_inc(v_v_2712_);
v___x_2713_ = lean_box(0);
v___x_2714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2714_, 0, v___x_2713_);
lean_ctor_set(v___x_2714_, 1, v_c_2699_);
v___x_2715_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg(v_v_2712_, v___x_2714_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_);
if (lean_obj_tag(v___x_2715_) == 0)
{
lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2729_; 
v_a_2716_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2718_ = v___x_2715_;
v_isShared_2719_ = v_isSharedCheck_2729_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v___x_2715_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2729_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v_fst_2720_; 
v_fst_2720_ = lean_ctor_get(v_a_2716_, 0);
if (lean_obj_tag(v_fst_2720_) == 0)
{
lean_object* v_snd_2721_; lean_object* v___x_2723_; 
v_snd_2721_ = lean_ctor_get(v_a_2716_, 1);
lean_inc(v_snd_2721_);
lean_dec(v_a_2716_);
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 0, v_snd_2721_);
v___x_2723_ = v___x_2718_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v_snd_2721_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
else
{
lean_object* v_val_2725_; lean_object* v___x_2727_; 
lean_inc_ref(v_fst_2720_);
lean_dec(v_a_2716_);
v_val_2725_ = lean_ctor_get(v_fst_2720_, 0);
lean_inc(v_val_2725_);
lean_dec_ref_known(v_fst_2720_, 1);
if (v_isShared_2719_ == 0)
{
lean_ctor_set(v___x_2718_, 0, v_val_2725_);
v___x_2727_ = v___x_2718_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v_val_2725_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
}
else
{
lean_object* v_a_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2737_; 
v_a_2730_ = lean_ctor_get(v___x_2715_, 0);
v_isSharedCheck_2737_ = !lean_is_exclusive(v___x_2715_);
if (v_isSharedCheck_2737_ == 0)
{
v___x_2732_ = v___x_2715_;
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_a_2730_);
lean_dec(v___x_2715_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2737_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2735_; 
if (v_isShared_2733_ == 0)
{
v___x_2735_ = v___x_2732_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2736_; 
v_reuseFailAlloc_2736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2736_, 0, v_a_2730_);
v___x_2735_ = v_reuseFailAlloc_2736_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
return v___x_2735_;
}
}
}
}
else
{
lean_object* v___x_2738_; 
v___x_2738_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_2699_, v_a_2700_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_);
return v___x_2738_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq___boxed(lean_object* v_c_2739_, lean_object* v_a_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(v_c_2739_, v_a_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_);
lean_dec(v_a_2749_);
lean_dec_ref(v_a_2748_);
lean_dec(v_a_2747_);
lean_dec_ref(v_a_2746_);
lean_dec(v_a_2745_);
lean_dec_ref(v_a_2744_);
lean_dec(v_a_2743_);
lean_dec_ref(v_a_2742_);
lean_dec(v_a_2741_);
lean_dec(v_a_2740_);
return v_res_2751_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0(lean_object* v_v_2752_, lean_object* v_inst_2753_, lean_object* v_a_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_){
_start:
{
lean_object* v___x_2766_; 
v___x_2766_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg(v_v_2752_, v_a_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_);
return v___x_2766_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___boxed(lean_object* v_v_2767_, lean_object* v_inst_2768_, lean_object* v_a_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_){
_start:
{
lean_object* v_res_2781_; 
v_res_2781_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0(v_v_2767_, v_inst_2768_, v_a_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(lean_object* v_a_2782_, lean_object* v_x_2783_, size_t v_x_2784_, size_t v_x_2785_){
_start:
{
if (lean_obj_tag(v_x_2783_) == 0)
{
lean_object* v_cs_2786_; size_t v_j_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; uint8_t v___x_2790_; 
v_cs_2786_ = lean_ctor_get(v_x_2783_, 0);
v_j_2787_ = lean_usize_shift_right(v_x_2784_, v_x_2785_);
v___x_2788_ = lean_usize_to_nat(v_j_2787_);
v___x_2789_ = lean_array_get_size(v_cs_2786_);
v___x_2790_ = lean_nat_dec_lt(v___x_2788_, v___x_2789_);
if (v___x_2790_ == 0)
{
lean_dec(v___x_2788_);
lean_dec_ref(v_a_2782_);
return v_x_2783_;
}
else
{
lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2808_; 
lean_inc_ref(v_cs_2786_);
v_isSharedCheck_2808_ = !lean_is_exclusive(v_x_2783_);
if (v_isSharedCheck_2808_ == 0)
{
lean_object* v_unused_2809_; 
v_unused_2809_ = lean_ctor_get(v_x_2783_, 0);
lean_dec(v_unused_2809_);
v___x_2792_ = v_x_2783_;
v_isShared_2793_ = v_isSharedCheck_2808_;
goto v_resetjp_2791_;
}
else
{
lean_dec(v_x_2783_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2808_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
size_t v___x_2794_; size_t v___x_2795_; size_t v___x_2796_; size_t v_i_2797_; size_t v___x_2798_; size_t v_shift_2799_; lean_object* v_v_2800_; lean_object* v___x_2801_; lean_object* v_xs_x27_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2806_; 
v___x_2794_ = ((size_t)1ULL);
v___x_2795_ = lean_usize_shift_left(v___x_2794_, v_x_2785_);
v___x_2796_ = lean_usize_sub(v___x_2795_, v___x_2794_);
v_i_2797_ = lean_usize_land(v_x_2784_, v___x_2796_);
v___x_2798_ = ((size_t)5ULL);
v_shift_2799_ = lean_usize_sub(v_x_2785_, v___x_2798_);
v_v_2800_ = lean_array_fget(v_cs_2786_, v___x_2788_);
v___x_2801_ = lean_box(0);
v_xs_x27_2802_ = lean_array_fset(v_cs_2786_, v___x_2788_, v___x_2801_);
v___x_2803_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(v_a_2782_, v_v_2800_, v_i_2797_, v_shift_2799_);
v___x_2804_ = lean_array_fset(v_xs_x27_2802_, v___x_2788_, v___x_2803_);
lean_dec(v___x_2788_);
if (v_isShared_2793_ == 0)
{
lean_ctor_set(v___x_2792_, 0, v___x_2804_);
v___x_2806_ = v___x_2792_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v___x_2804_);
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
lean_object* v_vs_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; uint8_t v___x_2813_; 
v_vs_2810_ = lean_ctor_get(v_x_2783_, 0);
v___x_2811_ = lean_usize_to_nat(v_x_2784_);
v___x_2812_ = lean_array_get_size(v_vs_2810_);
v___x_2813_ = lean_nat_dec_lt(v___x_2811_, v___x_2812_);
if (v___x_2813_ == 0)
{
lean_dec(v___x_2811_);
lean_dec_ref(v_a_2782_);
return v_x_2783_;
}
else
{
lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2825_; 
lean_inc_ref(v_vs_2810_);
v_isSharedCheck_2825_ = !lean_is_exclusive(v_x_2783_);
if (v_isSharedCheck_2825_ == 0)
{
lean_object* v_unused_2826_; 
v_unused_2826_ = lean_ctor_get(v_x_2783_, 0);
lean_dec(v_unused_2826_);
v___x_2815_ = v_x_2783_;
v_isShared_2816_ = v_isSharedCheck_2825_;
goto v_resetjp_2814_;
}
else
{
lean_dec(v_x_2783_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2825_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v_v_2817_; lean_object* v___x_2818_; lean_object* v_xs_x27_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2823_; 
v_v_2817_ = lean_array_fget(v_vs_2810_, v___x_2811_);
v___x_2818_ = lean_box(0);
v_xs_x27_2819_ = lean_array_fset(v_vs_2810_, v___x_2811_, v___x_2818_);
v___x_2820_ = l_Lean_PersistentArray_push___redArg(v_v_2817_, v_a_2782_);
v___x_2821_ = lean_array_fset(v_xs_x27_2819_, v___x_2811_, v___x_2820_);
lean_dec(v___x_2811_);
if (v_isShared_2816_ == 0)
{
lean_ctor_set(v___x_2815_, 0, v___x_2821_);
v___x_2823_ = v___x_2815_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v___x_2821_);
v___x_2823_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
return v___x_2823_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0___boxed(lean_object* v_a_2827_, lean_object* v_x_2828_, lean_object* v_x_2829_, lean_object* v_x_2830_){
_start:
{
size_t v_x_62885__boxed_2831_; size_t v_x_62886__boxed_2832_; lean_object* v_res_2833_; 
v_x_62885__boxed_2831_ = lean_unbox_usize(v_x_2829_);
lean_dec(v_x_2829_);
v_x_62886__boxed_2832_ = lean_unbox_usize(v_x_2830_);
lean_dec(v_x_2830_);
v_res_2833_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(v_a_2827_, v_x_2828_, v_x_62885__boxed_2831_, v_x_62886__boxed_2832_);
return v_res_2833_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(lean_object* v_a_2834_, lean_object* v_t_2835_, lean_object* v_i_2836_){
_start:
{
lean_object* v_root_2837_; lean_object* v_tail_2838_; lean_object* v_size_2839_; size_t v_shift_2840_; lean_object* v_tailOff_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2865_; 
v_root_2837_ = lean_ctor_get(v_t_2835_, 0);
v_tail_2838_ = lean_ctor_get(v_t_2835_, 1);
v_size_2839_ = lean_ctor_get(v_t_2835_, 2);
v_shift_2840_ = lean_ctor_get_usize(v_t_2835_, 4);
v_tailOff_2841_ = lean_ctor_get(v_t_2835_, 3);
v_isSharedCheck_2865_ = !lean_is_exclusive(v_t_2835_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2843_ = v_t_2835_;
v_isShared_2844_ = v_isSharedCheck_2865_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_tailOff_2841_);
lean_inc(v_size_2839_);
lean_inc(v_tail_2838_);
lean_inc(v_root_2837_);
lean_dec(v_t_2835_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2865_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
uint8_t v___x_2845_; 
v___x_2845_ = lean_nat_dec_le(v_tailOff_2841_, v_i_2836_);
if (v___x_2845_ == 0)
{
size_t v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2849_; 
v___x_2846_ = lean_usize_of_nat(v_i_2836_);
v___x_2847_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(v_a_2834_, v_root_2837_, v___x_2846_, v_shift_2840_);
if (v_isShared_2844_ == 0)
{
lean_ctor_set(v___x_2843_, 0, v___x_2847_);
v___x_2849_ = v___x_2843_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v___x_2847_);
lean_ctor_set(v_reuseFailAlloc_2850_, 1, v_tail_2838_);
lean_ctor_set(v_reuseFailAlloc_2850_, 2, v_size_2839_);
lean_ctor_set(v_reuseFailAlloc_2850_, 3, v_tailOff_2841_);
lean_ctor_set_usize(v_reuseFailAlloc_2850_, 4, v_shift_2840_);
v___x_2849_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
return v___x_2849_;
}
}
else
{
lean_object* v___x_2851_; lean_object* v___x_2852_; uint8_t v___x_2853_; 
v___x_2851_ = lean_nat_sub(v_i_2836_, v_tailOff_2841_);
v___x_2852_ = lean_array_get_size(v_tail_2838_);
v___x_2853_ = lean_nat_dec_lt(v___x_2851_, v___x_2852_);
if (v___x_2853_ == 0)
{
lean_object* v___x_2855_; 
lean_dec(v___x_2851_);
lean_dec_ref(v_a_2834_);
if (v_isShared_2844_ == 0)
{
v___x_2855_ = v___x_2843_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_root_2837_);
lean_ctor_set(v_reuseFailAlloc_2856_, 1, v_tail_2838_);
lean_ctor_set(v_reuseFailAlloc_2856_, 2, v_size_2839_);
lean_ctor_set(v_reuseFailAlloc_2856_, 3, v_tailOff_2841_);
lean_ctor_set_usize(v_reuseFailAlloc_2856_, 4, v_shift_2840_);
v___x_2855_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
return v___x_2855_;
}
}
else
{
lean_object* v_v_2857_; lean_object* v___x_2858_; lean_object* v_xs_x27_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2863_; 
v_v_2857_ = lean_array_fget(v_tail_2838_, v___x_2851_);
v___x_2858_ = lean_box(0);
v_xs_x27_2859_ = lean_array_fset(v_tail_2838_, v___x_2851_, v___x_2858_);
v___x_2860_ = l_Lean_PersistentArray_push___redArg(v_v_2857_, v_a_2834_);
v___x_2861_ = lean_array_fset(v_xs_x27_2859_, v___x_2851_, v___x_2860_);
lean_dec(v___x_2851_);
if (v_isShared_2844_ == 0)
{
lean_ctor_set(v___x_2843_, 1, v___x_2861_);
v___x_2863_ = v___x_2843_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_root_2837_);
lean_ctor_set(v_reuseFailAlloc_2864_, 1, v___x_2861_);
lean_ctor_set(v_reuseFailAlloc_2864_, 2, v_size_2839_);
lean_ctor_set(v_reuseFailAlloc_2864_, 3, v_tailOff_2841_);
lean_ctor_set_usize(v_reuseFailAlloc_2864_, 4, v_shift_2840_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0___boxed(lean_object* v_a_2866_, lean_object* v_t_2867_, lean_object* v_i_2868_){
_start:
{
lean_object* v_res_2869_; 
v_res_2869_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(v_a_2866_, v_t_2867_, v_i_2868_);
lean_dec(v_i_2868_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0(lean_object* v_a_2870_, lean_object* v_v_2871_, lean_object* v_s_2872_){
_start:
{
lean_object* v_vars_2873_; lean_object* v_varMap_2874_; lean_object* v_varsHistory_2875_; lean_object* v_natToIntMap_2876_; lean_object* v_natDef_2877_; lean_object* v_dvds_2878_; lean_object* v_lowers_2879_; lean_object* v_uppers_2880_; lean_object* v_diseqs_2881_; lean_object* v_elimEqs_2882_; lean_object* v_elimStack_2883_; lean_object* v_occurs_2884_; lean_object* v_assignment_2885_; lean_object* v_nextCnstrId_2886_; uint8_t v_caseSplits_2887_; lean_object* v_steps_2888_; lean_object* v_penalties_2889_; lean_object* v_numReorderRequests_2890_; lean_object* v_conflict_x3f_2891_; lean_object* v_diseqSplits_2892_; lean_object* v_divMod_2893_; uint8_t v_usedCommRing_2894_; lean_object* v_nonlinearOccs_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2903_; 
v_vars_2873_ = lean_ctor_get(v_s_2872_, 0);
v_varMap_2874_ = lean_ctor_get(v_s_2872_, 1);
v_varsHistory_2875_ = lean_ctor_get(v_s_2872_, 2);
v_natToIntMap_2876_ = lean_ctor_get(v_s_2872_, 3);
v_natDef_2877_ = lean_ctor_get(v_s_2872_, 4);
v_dvds_2878_ = lean_ctor_get(v_s_2872_, 5);
v_lowers_2879_ = lean_ctor_get(v_s_2872_, 6);
v_uppers_2880_ = lean_ctor_get(v_s_2872_, 7);
v_diseqs_2881_ = lean_ctor_get(v_s_2872_, 8);
v_elimEqs_2882_ = lean_ctor_get(v_s_2872_, 9);
v_elimStack_2883_ = lean_ctor_get(v_s_2872_, 10);
v_occurs_2884_ = lean_ctor_get(v_s_2872_, 11);
v_assignment_2885_ = lean_ctor_get(v_s_2872_, 12);
v_nextCnstrId_2886_ = lean_ctor_get(v_s_2872_, 13);
v_caseSplits_2887_ = lean_ctor_get_uint8(v_s_2872_, sizeof(void*)*21);
v_steps_2888_ = lean_ctor_get(v_s_2872_, 14);
v_penalties_2889_ = lean_ctor_get(v_s_2872_, 15);
v_numReorderRequests_2890_ = lean_ctor_get(v_s_2872_, 16);
v_conflict_x3f_2891_ = lean_ctor_get(v_s_2872_, 17);
v_diseqSplits_2892_ = lean_ctor_get(v_s_2872_, 18);
v_divMod_2893_ = lean_ctor_get(v_s_2872_, 19);
v_usedCommRing_2894_ = lean_ctor_get_uint8(v_s_2872_, sizeof(void*)*21 + 1);
v_nonlinearOccs_2895_ = lean_ctor_get(v_s_2872_, 20);
v_isSharedCheck_2903_ = !lean_is_exclusive(v_s_2872_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2897_ = v_s_2872_;
v_isShared_2898_ = v_isSharedCheck_2903_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_nonlinearOccs_2895_);
lean_inc(v_divMod_2893_);
lean_inc(v_diseqSplits_2892_);
lean_inc(v_conflict_x3f_2891_);
lean_inc(v_numReorderRequests_2890_);
lean_inc(v_penalties_2889_);
lean_inc(v_steps_2888_);
lean_inc(v_nextCnstrId_2886_);
lean_inc(v_assignment_2885_);
lean_inc(v_occurs_2884_);
lean_inc(v_elimStack_2883_);
lean_inc(v_elimEqs_2882_);
lean_inc(v_diseqs_2881_);
lean_inc(v_uppers_2880_);
lean_inc(v_lowers_2879_);
lean_inc(v_dvds_2878_);
lean_inc(v_natDef_2877_);
lean_inc(v_natToIntMap_2876_);
lean_inc(v_varsHistory_2875_);
lean_inc(v_varMap_2874_);
lean_inc(v_vars_2873_);
lean_dec(v_s_2872_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2903_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2899_; lean_object* v___x_2901_; 
v___x_2899_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(v_a_2870_, v_lowers_2879_, v_v_2871_);
if (v_isShared_2898_ == 0)
{
lean_ctor_set(v___x_2897_, 6, v___x_2899_);
v___x_2901_ = v___x_2897_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(0, 21, 2);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_vars_2873_);
lean_ctor_set(v_reuseFailAlloc_2902_, 1, v_varMap_2874_);
lean_ctor_set(v_reuseFailAlloc_2902_, 2, v_varsHistory_2875_);
lean_ctor_set(v_reuseFailAlloc_2902_, 3, v_natToIntMap_2876_);
lean_ctor_set(v_reuseFailAlloc_2902_, 4, v_natDef_2877_);
lean_ctor_set(v_reuseFailAlloc_2902_, 5, v_dvds_2878_);
lean_ctor_set(v_reuseFailAlloc_2902_, 6, v___x_2899_);
lean_ctor_set(v_reuseFailAlloc_2902_, 7, v_uppers_2880_);
lean_ctor_set(v_reuseFailAlloc_2902_, 8, v_diseqs_2881_);
lean_ctor_set(v_reuseFailAlloc_2902_, 9, v_elimEqs_2882_);
lean_ctor_set(v_reuseFailAlloc_2902_, 10, v_elimStack_2883_);
lean_ctor_set(v_reuseFailAlloc_2902_, 11, v_occurs_2884_);
lean_ctor_set(v_reuseFailAlloc_2902_, 12, v_assignment_2885_);
lean_ctor_set(v_reuseFailAlloc_2902_, 13, v_nextCnstrId_2886_);
lean_ctor_set(v_reuseFailAlloc_2902_, 14, v_steps_2888_);
lean_ctor_set(v_reuseFailAlloc_2902_, 15, v_penalties_2889_);
lean_ctor_set(v_reuseFailAlloc_2902_, 16, v_numReorderRequests_2890_);
lean_ctor_set(v_reuseFailAlloc_2902_, 17, v_conflict_x3f_2891_);
lean_ctor_set(v_reuseFailAlloc_2902_, 18, v_diseqSplits_2892_);
lean_ctor_set(v_reuseFailAlloc_2902_, 19, v_divMod_2893_);
lean_ctor_set(v_reuseFailAlloc_2902_, 20, v_nonlinearOccs_2895_);
lean_ctor_set_uint8(v_reuseFailAlloc_2902_, sizeof(void*)*21, v_caseSplits_2887_);
lean_ctor_set_uint8(v_reuseFailAlloc_2902_, sizeof(void*)*21 + 1, v_usedCommRing_2894_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0___boxed(lean_object* v_a_2904_, lean_object* v_v_2905_, lean_object* v_s_2906_){
_start:
{
lean_object* v_res_2907_; 
v_res_2907_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0(v_a_2904_, v_v_2905_, v_s_2906_);
lean_dec(v_v_2905_);
return v_res_2907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1(lean_object* v_a_2908_, lean_object* v_v_2909_, lean_object* v_s_2910_){
_start:
{
lean_object* v_vars_2911_; lean_object* v_varMap_2912_; lean_object* v_varsHistory_2913_; lean_object* v_natToIntMap_2914_; lean_object* v_natDef_2915_; lean_object* v_dvds_2916_; lean_object* v_lowers_2917_; lean_object* v_uppers_2918_; lean_object* v_diseqs_2919_; lean_object* v_elimEqs_2920_; lean_object* v_elimStack_2921_; lean_object* v_occurs_2922_; lean_object* v_assignment_2923_; lean_object* v_nextCnstrId_2924_; uint8_t v_caseSplits_2925_; lean_object* v_steps_2926_; lean_object* v_penalties_2927_; lean_object* v_numReorderRequests_2928_; lean_object* v_conflict_x3f_2929_; lean_object* v_diseqSplits_2930_; lean_object* v_divMod_2931_; uint8_t v_usedCommRing_2932_; lean_object* v_nonlinearOccs_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2941_; 
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
v_caseSplits_2925_ = lean_ctor_get_uint8(v_s_2910_, sizeof(void*)*21);
v_steps_2926_ = lean_ctor_get(v_s_2910_, 14);
v_penalties_2927_ = lean_ctor_get(v_s_2910_, 15);
v_numReorderRequests_2928_ = lean_ctor_get(v_s_2910_, 16);
v_conflict_x3f_2929_ = lean_ctor_get(v_s_2910_, 17);
v_diseqSplits_2930_ = lean_ctor_get(v_s_2910_, 18);
v_divMod_2931_ = lean_ctor_get(v_s_2910_, 19);
v_usedCommRing_2932_ = lean_ctor_get_uint8(v_s_2910_, sizeof(void*)*21 + 1);
v_nonlinearOccs_2933_ = lean_ctor_get(v_s_2910_, 20);
v_isSharedCheck_2941_ = !lean_is_exclusive(v_s_2910_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2935_ = v_s_2910_;
v_isShared_2936_ = v_isSharedCheck_2941_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_nonlinearOccs_2933_);
lean_inc(v_divMod_2931_);
lean_inc(v_diseqSplits_2930_);
lean_inc(v_conflict_x3f_2929_);
lean_inc(v_numReorderRequests_2928_);
lean_inc(v_penalties_2927_);
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
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2941_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2937_; lean_object* v___x_2939_; 
v___x_2937_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(v_a_2908_, v_uppers_2918_, v_v_2909_);
if (v_isShared_2936_ == 0)
{
lean_ctor_set(v___x_2935_, 7, v___x_2937_);
v___x_2939_ = v___x_2935_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(0, 21, 2);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_vars_2911_);
lean_ctor_set(v_reuseFailAlloc_2940_, 1, v_varMap_2912_);
lean_ctor_set(v_reuseFailAlloc_2940_, 2, v_varsHistory_2913_);
lean_ctor_set(v_reuseFailAlloc_2940_, 3, v_natToIntMap_2914_);
lean_ctor_set(v_reuseFailAlloc_2940_, 4, v_natDef_2915_);
lean_ctor_set(v_reuseFailAlloc_2940_, 5, v_dvds_2916_);
lean_ctor_set(v_reuseFailAlloc_2940_, 6, v_lowers_2917_);
lean_ctor_set(v_reuseFailAlloc_2940_, 7, v___x_2937_);
lean_ctor_set(v_reuseFailAlloc_2940_, 8, v_diseqs_2919_);
lean_ctor_set(v_reuseFailAlloc_2940_, 9, v_elimEqs_2920_);
lean_ctor_set(v_reuseFailAlloc_2940_, 10, v_elimStack_2921_);
lean_ctor_set(v_reuseFailAlloc_2940_, 11, v_occurs_2922_);
lean_ctor_set(v_reuseFailAlloc_2940_, 12, v_assignment_2923_);
lean_ctor_set(v_reuseFailAlloc_2940_, 13, v_nextCnstrId_2924_);
lean_ctor_set(v_reuseFailAlloc_2940_, 14, v_steps_2926_);
lean_ctor_set(v_reuseFailAlloc_2940_, 15, v_penalties_2927_);
lean_ctor_set(v_reuseFailAlloc_2940_, 16, v_numReorderRequests_2928_);
lean_ctor_set(v_reuseFailAlloc_2940_, 17, v_conflict_x3f_2929_);
lean_ctor_set(v_reuseFailAlloc_2940_, 18, v_diseqSplits_2930_);
lean_ctor_set(v_reuseFailAlloc_2940_, 19, v_divMod_2931_);
lean_ctor_set(v_reuseFailAlloc_2940_, 20, v_nonlinearOccs_2933_);
lean_ctor_set_uint8(v_reuseFailAlloc_2940_, sizeof(void*)*21, v_caseSplits_2925_);
lean_ctor_set_uint8(v_reuseFailAlloc_2940_, sizeof(void*)*21 + 1, v_usedCommRing_2932_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1___boxed(lean_object* v_a_2942_, lean_object* v_v_2943_, lean_object* v_s_2944_){
_start:
{
lean_object* v_res_2945_; 
v_res_2945_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1(v_a_2942_, v_v_2943_, v_s_2944_);
lean_dec(v_v_2943_);
return v_res_2945_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3(void){
_start:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___x_2953_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2));
v___x_2954_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_2955_ = l_Lean_Name_append(v___x_2954_, v___x_2953_);
return v___x_2955_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6(void){
_start:
{
lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; 
v___x_2962_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5));
v___x_2963_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_2964_ = l_Lean_Name_append(v___x_2963_, v___x_2962_);
return v___x_2964_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9(void){
_start:
{
lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___x_2971_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__8));
v___x_2972_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_2973_ = l_Lean_Name_append(v___x_2972_, v___x_2971_);
return v___x_2973_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11(void){
_start:
{
lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; 
v___x_2978_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__10));
v___x_2979_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_2980_ = l_Lean_Name_append(v___x_2979_, v___x_2978_);
return v___x_2980_;
}
}
LEAN_EXPORT lean_object* lean_grind_cutsat_assert_le(lean_object* v_c_2981_, lean_object* v_a_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_){
_start:
{
lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___x_3065_; 
v___x_3065_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_2982_, v_a_2990_);
if (lean_obj_tag(v___x_3065_) == 0)
{
lean_object* v_a_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3206_; 
v_a_3066_ = lean_ctor_get(v___x_3065_, 0);
v_isSharedCheck_3206_ = !lean_is_exclusive(v___x_3065_);
if (v_isSharedCheck_3206_ == 0)
{
v___x_3068_ = v___x_3065_;
v_isShared_3069_ = v_isSharedCheck_3206_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_a_3066_);
lean_dec(v___x_3065_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3206_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
uint8_t v___x_3070_; 
v___x_3070_ = lean_unbox(v_a_3066_);
lean_dec(v_a_3066_);
if (v___x_3070_ == 0)
{
lean_object* v_toCold_3071_; lean_object* v_options_3072_; lean_object* v_inheritedTraceOptions_3073_; uint8_t v_hasTrace_3074_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; 
lean_del_object(v___x_3068_);
v_toCold_3071_ = lean_ctor_get(v_a_2990_, 0);
v_options_3072_ = lean_ctor_get(v_toCold_3071_, 2);
v_inheritedTraceOptions_3073_ = lean_ctor_get(v_toCold_3071_, 11);
v_hasTrace_3074_ = lean_ctor_get_uint8(v_options_3072_, sizeof(void*)*1);
if (v_hasTrace_3074_ == 0)
{
v___y_3076_ = v_a_2982_;
v___y_3077_ = v_a_2983_;
v___y_3078_ = v_a_2984_;
v___y_3079_ = v_a_2985_;
v___y_3080_ = v_a_2986_;
v___y_3081_ = v_a_2987_;
v___y_3082_ = v_a_2988_;
v___y_3083_ = v_a_2989_;
v___y_3084_ = v_a_2990_;
v___y_3085_ = v_a_2991_;
goto v___jp_3075_;
}
else
{
lean_object* v___x_3188_; lean_object* v___x_3189_; uint8_t v___x_3190_; 
v___x_3188_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__10));
v___x_3189_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11);
v___x_3190_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3073_, v_options_3072_, v___x_3189_);
if (v___x_3190_ == 0)
{
v___y_3076_ = v_a_2982_;
v___y_3077_ = v_a_2983_;
v___y_3078_ = v_a_2984_;
v___y_3079_ = v_a_2985_;
v___y_3080_ = v_a_2986_;
v___y_3081_ = v_a_2987_;
v___y_3082_ = v_a_2988_;
v___y_3083_ = v_a_2989_;
v___y_3084_ = v_a_2990_;
v___y_3085_ = v_a_2991_;
goto v___jp_3075_;
}
else
{
lean_object* v___x_3191_; 
lean_inc_ref(v_c_2981_);
v___x_3191_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_2981_, v_a_2982_, v_a_2990_);
if (lean_obj_tag(v___x_3191_) == 0)
{
lean_object* v_a_3192_; lean_object* v___x_3193_; 
v_a_3192_ = lean_ctor_get(v___x_3191_, 0);
lean_inc(v_a_3192_);
lean_dec_ref_known(v___x_3191_, 1);
v___x_3193_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3188_, v_a_3192_, v_a_2988_, v_a_2989_, v_a_2990_, v_a_2991_);
if (lean_obj_tag(v___x_3193_) == 0)
{
lean_dec_ref_known(v___x_3193_, 1);
v___y_3076_ = v_a_2982_;
v___y_3077_ = v_a_2983_;
v___y_3078_ = v_a_2984_;
v___y_3079_ = v_a_2985_;
v___y_3080_ = v_a_2986_;
v___y_3081_ = v_a_2987_;
v___y_3082_ = v_a_2988_;
v___y_3083_ = v_a_2989_;
v___y_3084_ = v_a_2990_;
v___y_3085_ = v_a_2991_;
goto v___jp_3075_;
}
else
{
lean_dec(v_a_2991_);
lean_dec_ref(v_a_2990_);
lean_dec(v_a_2989_);
lean_dec_ref(v_a_2988_);
lean_dec(v_a_2987_);
lean_dec_ref(v_a_2986_);
lean_dec(v_a_2985_);
lean_dec_ref(v_a_2984_);
lean_dec(v_a_2983_);
lean_dec(v_a_2982_);
lean_dec_ref(v_c_2981_);
return v___x_3193_;
}
}
else
{
lean_object* v_a_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3201_; 
lean_dec(v_a_2991_);
lean_dec_ref(v_a_2990_);
lean_dec(v_a_2989_);
lean_dec_ref(v_a_2988_);
lean_dec(v_a_2987_);
lean_dec_ref(v_a_2986_);
lean_dec(v_a_2985_);
lean_dec_ref(v_a_2984_);
lean_dec(v_a_2983_);
lean_dec(v_a_2982_);
lean_dec_ref(v_c_2981_);
v_a_3194_ = lean_ctor_get(v___x_3191_, 0);
v_isSharedCheck_3201_ = !lean_is_exclusive(v___x_3191_);
if (v_isSharedCheck_3201_ == 0)
{
v___x_3196_ = v___x_3191_;
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_a_3194_);
lean_dec(v___x_3191_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___x_3199_; 
if (v_isShared_3197_ == 0)
{
v___x_3199_ = v___x_3196_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v_a_3194_);
v___x_3199_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
return v___x_3199_;
}
}
}
}
}
v___jp_3075_:
{
lean_object* v___x_3086_; lean_object* v___x_3087_; 
v___x_3086_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_norm(v_c_2981_);
lean_inc_ref(v___y_3084_);
v___x_3087_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts(v___x_3086_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_);
if (lean_obj_tag(v___x_3087_) == 0)
{
lean_object* v_a_3088_; lean_object* v_p_3089_; uint8_t v___x_3090_; 
v_a_3088_ = lean_ctor_get(v___x_3087_, 0);
lean_inc(v_a_3088_);
lean_dec_ref_known(v___x_3087_, 1);
v_p_3089_ = lean_ctor_get(v_a_3088_, 0);
v___x_3090_ = l_Int_Internal_Linear_Poly_isUnsatLe(v_p_3089_);
if (v___x_3090_ == 0)
{
uint8_t v___x_3091_; 
v___x_3091_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(v_a_3088_);
if (v___x_3091_ == 0)
{
if (lean_obj_tag(v_p_3089_) == 1)
{
lean_object* v_k_3092_; lean_object* v_v_3093_; lean_object* v___x_3094_; 
v_k_3092_ = lean_ctor_get(v_p_3089_, 0);
lean_inc(v_k_3092_);
v_v_3093_ = lean_ctor_get(v_p_3089_, 1);
lean_inc(v_v_3093_);
lean_inc(v_a_3088_);
v___x_3094_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq(v_a_3088_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_);
if (lean_obj_tag(v___x_3094_) == 0)
{
lean_object* v_a_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3134_; 
v_a_3095_ = lean_ctor_get(v___x_3094_, 0);
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_3094_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_3097_ = v___x_3094_;
v_isShared_3098_ = v_isSharedCheck_3134_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_a_3095_);
lean_dec(v___x_3094_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3134_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
uint8_t v___x_3099_; 
v___x_3099_ = lean_unbox(v_a_3095_);
lean_dec(v_a_3095_);
if (v___x_3099_ == 0)
{
lean_object* v___x_3100_; 
lean_del_object(v___x_3097_);
v___x_3100_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(v_a_3088_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_);
lean_dec(v___y_3081_);
lean_dec_ref(v___y_3080_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
if (lean_obj_tag(v___x_3100_) == 0)
{
lean_object* v_toCold_3101_; lean_object* v_options_3102_; lean_object* v_a_3103_; lean_object* v_inheritedTraceOptions_3104_; uint8_t v_hasTrace_3105_; lean_object* v___f_3106_; lean_object* v___f_3107_; 
v_toCold_3101_ = lean_ctor_get(v___y_3084_, 0);
v_options_3102_ = lean_ctor_get(v_toCold_3101_, 2);
v_a_3103_ = lean_ctor_get(v___x_3100_, 0);
lean_inc_n(v_a_3103_, 3);
lean_dec_ref_known(v___x_3100_, 1);
v_inheritedTraceOptions_3104_ = lean_ctor_get(v_toCold_3101_, 11);
v_hasTrace_3105_ = lean_ctor_get_uint8(v_options_3102_, sizeof(void*)*1);
lean_inc_n(v_v_3093_, 2);
v___f_3106_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3106_, 0, v_a_3103_);
lean_closure_set(v___f_3106_, 1, v_v_3093_);
v___f_3107_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3107_, 0, v_a_3103_);
lean_closure_set(v___f_3107_, 1, v_v_3093_);
if (v_hasTrace_3105_ == 0)
{
v___y_3024_ = v___f_3107_;
v___y_3025_ = v_a_3103_;
v___y_3026_ = v___f_3106_;
v___y_3027_ = v_v_3093_;
v___y_3028_ = v_k_3092_;
v___y_3029_ = v___y_3076_;
v___y_3030_ = v___y_3082_;
v___y_3031_ = v___y_3083_;
v___y_3032_ = v___y_3084_;
v___y_3033_ = v___y_3085_;
goto v___jp_3023_;
}
else
{
lean_object* v___x_3108_; lean_object* v___x_3109_; uint8_t v___x_3110_; 
v___x_3108_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2));
v___x_3109_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3);
v___x_3110_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3104_, v_options_3102_, v___x_3109_);
if (v___x_3110_ == 0)
{
v___y_3024_ = v___f_3107_;
v___y_3025_ = v_a_3103_;
v___y_3026_ = v___f_3106_;
v___y_3027_ = v_v_3093_;
v___y_3028_ = v_k_3092_;
v___y_3029_ = v___y_3076_;
v___y_3030_ = v___y_3082_;
v___y_3031_ = v___y_3083_;
v___y_3032_ = v___y_3084_;
v___y_3033_ = v___y_3085_;
goto v___jp_3023_;
}
else
{
lean_object* v___x_3111_; 
lean_inc(v_a_3103_);
v___x_3111_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_a_3103_, v___y_3076_, v___y_3084_);
if (lean_obj_tag(v___x_3111_) == 0)
{
lean_object* v_a_3112_; lean_object* v___x_3113_; 
v_a_3112_ = lean_ctor_get(v___x_3111_, 0);
lean_inc(v_a_3112_);
lean_dec_ref_known(v___x_3111_, 1);
v___x_3113_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3108_, v_a_3112_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_);
if (lean_obj_tag(v___x_3113_) == 0)
{
lean_dec_ref_known(v___x_3113_, 1);
v___y_3024_ = v___f_3107_;
v___y_3025_ = v_a_3103_;
v___y_3026_ = v___f_3106_;
v___y_3027_ = v_v_3093_;
v___y_3028_ = v_k_3092_;
v___y_3029_ = v___y_3076_;
v___y_3030_ = v___y_3082_;
v___y_3031_ = v___y_3083_;
v___y_3032_ = v___y_3084_;
v___y_3033_ = v___y_3085_;
goto v___jp_3023_;
}
else
{
lean_dec_ref(v___f_3107_);
lean_dec_ref(v___f_3106_);
lean_dec(v_a_3103_);
lean_dec(v_v_3093_);
lean_dec(v_k_3092_);
lean_dec(v___y_3085_);
lean_dec_ref(v___y_3084_);
lean_dec(v___y_3083_);
lean_dec_ref(v___y_3082_);
lean_dec(v___y_3076_);
return v___x_3113_;
}
}
else
{
lean_object* v_a_3114_; lean_object* v___x_3116_; uint8_t v_isShared_3117_; uint8_t v_isSharedCheck_3121_; 
lean_dec_ref(v___f_3107_);
lean_dec_ref(v___f_3106_);
lean_dec(v_a_3103_);
lean_dec(v_v_3093_);
lean_dec(v_k_3092_);
lean_dec(v___y_3085_);
lean_dec_ref(v___y_3084_);
lean_dec(v___y_3083_);
lean_dec_ref(v___y_3082_);
lean_dec(v___y_3076_);
v_a_3114_ = lean_ctor_get(v___x_3111_, 0);
v_isSharedCheck_3121_ = !lean_is_exclusive(v___x_3111_);
if (v_isSharedCheck_3121_ == 0)
{
v___x_3116_ = v___x_3111_;
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
else
{
lean_inc(v_a_3114_);
lean_dec(v___x_3111_);
v___x_3116_ = lean_box(0);
v_isShared_3117_ = v_isSharedCheck_3121_;
goto v_resetjp_3115_;
}
v_resetjp_3115_:
{
lean_object* v___x_3119_; 
if (v_isShared_3117_ == 0)
{
v___x_3119_ = v___x_3116_;
goto v_reusejp_3118_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v_a_3114_);
v___x_3119_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3118_;
}
v_reusejp_3118_:
{
return v___x_3119_;
}
}
}
}
}
}
else
{
lean_object* v_a_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3129_; 
lean_dec(v_v_3093_);
lean_dec(v_k_3092_);
lean_dec(v___y_3085_);
lean_dec_ref(v___y_3084_);
lean_dec(v___y_3083_);
lean_dec_ref(v___y_3082_);
lean_dec(v___y_3076_);
v_a_3122_ = lean_ctor_get(v___x_3100_, 0);
v_isSharedCheck_3129_ = !lean_is_exclusive(v___x_3100_);
if (v_isSharedCheck_3129_ == 0)
{
v___x_3124_ = v___x_3100_;
v_isShared_3125_ = v_isSharedCheck_3129_;
goto v_resetjp_3123_;
}
else
{
lean_inc(v_a_3122_);
lean_dec(v___x_3100_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3129_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
lean_object* v___x_3127_; 
if (v_isShared_3125_ == 0)
{
v___x_3127_ = v___x_3124_;
goto v_reusejp_3126_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v_a_3122_);
v___x_3127_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3126_;
}
v_reusejp_3126_:
{
return v___x_3127_;
}
}
}
}
else
{
lean_object* v___x_3130_; lean_object* v___x_3132_; 
lean_dec(v_v_3093_);
lean_dec(v_k_3092_);
lean_dec(v_a_3088_);
lean_dec(v___y_3085_);
lean_dec_ref(v___y_3084_);
lean_dec(v___y_3083_);
lean_dec_ref(v___y_3082_);
lean_dec(v___y_3081_);
lean_dec_ref(v___y_3080_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec(v___y_3076_);
v___x_3130_ = lean_box(0);
if (v_isShared_3098_ == 0)
{
lean_ctor_set(v___x_3097_, 0, v___x_3130_);
v___x_3132_ = v___x_3097_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v___x_3130_);
v___x_3132_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
return v___x_3132_;
}
}
}
}
else
{
lean_object* v_a_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3142_; 
lean_dec(v_v_3093_);
lean_dec(v_k_3092_);
lean_dec(v_a_3088_);
lean_dec(v___y_3085_);
lean_dec_ref(v___y_3084_);
lean_dec(v___y_3083_);
lean_dec_ref(v___y_3082_);
lean_dec(v___y_3081_);
lean_dec_ref(v___y_3080_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec(v___y_3076_);
v_a_3135_ = lean_ctor_get(v___x_3094_, 0);
v_isSharedCheck_3142_ = !lean_is_exclusive(v___x_3094_);
if (v_isSharedCheck_3142_ == 0)
{
v___x_3137_ = v___x_3094_;
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
else
{
lean_inc(v_a_3135_);
lean_dec(v___x_3094_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
lean_object* v___x_3140_; 
if (v_isShared_3138_ == 0)
{
v___x_3140_ = v___x_3137_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_a_3135_);
v___x_3140_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
return v___x_3140_;
}
}
}
}
else
{
lean_object* v___x_3143_; 
lean_dec(v___y_3081_);
lean_dec_ref(v___y_3080_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
v___x_3143_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_a_3088_, v___y_3076_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_);
lean_dec(v___y_3085_);
lean_dec_ref(v___y_3084_);
lean_dec(v___y_3083_);
lean_dec_ref(v___y_3082_);
lean_dec(v___y_3076_);
return v___x_3143_;
}
}
else
{
lean_object* v_toCold_3144_; lean_object* v_options_3145_; uint8_t v_hasTrace_3146_; 
lean_dec(v___y_3081_);
lean_dec_ref(v___y_3080_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
v_toCold_3144_ = lean_ctor_get(v___y_3084_, 0);
v_options_3145_ = lean_ctor_get(v_toCold_3144_, 2);
v_hasTrace_3146_ = lean_ctor_get_uint8(v_options_3145_, sizeof(void*)*1);
if (v_hasTrace_3146_ == 0)
{
lean_dec(v_a_3088_);
lean_dec(v___y_3085_);
lean_dec_ref(v___y_3084_);
lean_dec(v___y_3083_);
lean_dec_ref(v___y_3082_);
lean_dec(v___y_3076_);
goto v___jp_2993_;
}
else
{
lean_object* v_inheritedTraceOptions_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; uint8_t v___x_3150_; 
v_inheritedTraceOptions_3147_ = lean_ctor_get(v_toCold_3144_, 11);
v___x_3148_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5));
v___x_3149_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6);
v___x_3150_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3147_, v_options_3145_, v___x_3149_);
if (v___x_3150_ == 0)
{
lean_dec(v_a_3088_);
lean_dec(v___y_3085_);
lean_dec_ref(v___y_3084_);
lean_dec(v___y_3083_);
lean_dec_ref(v___y_3082_);
lean_dec(v___y_3076_);
goto v___jp_2993_;
}
else
{
lean_object* v___x_3151_; 
v___x_3151_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_a_3088_, v___y_3076_, v___y_3084_);
lean_dec(v___y_3076_);
if (lean_obj_tag(v___x_3151_) == 0)
{
lean_object* v_a_3152_; lean_object* v___x_3153_; 
v_a_3152_ = lean_ctor_get(v___x_3151_, 0);
lean_inc(v_a_3152_);
lean_dec_ref_known(v___x_3151_, 1);
v___x_3153_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3148_, v_a_3152_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_);
lean_dec(v___y_3085_);
lean_dec_ref(v___y_3084_);
lean_dec(v___y_3083_);
lean_dec_ref(v___y_3082_);
if (lean_obj_tag(v___x_3153_) == 0)
{
lean_dec_ref_known(v___x_3153_, 1);
goto v___jp_2993_;
}
else
{
return v___x_3153_;
}
}
else
{
lean_object* v_a_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3161_; 
lean_dec(v___y_3085_);
lean_dec_ref(v___y_3084_);
lean_dec(v___y_3083_);
lean_dec_ref(v___y_3082_);
v_a_3154_ = lean_ctor_get(v___x_3151_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3156_ = v___x_3151_;
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_a_3154_);
lean_dec(v___x_3151_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v___x_3159_; 
if (v_isShared_3157_ == 0)
{
v___x_3159_ = v___x_3156_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_a_3154_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
return v___x_3159_;
}
}
}
}
}
}
}
else
{
lean_object* v_toCold_3162_; lean_object* v_options_3163_; uint8_t v_hasTrace_3164_; 
v_toCold_3162_ = lean_ctor_get(v___y_3084_, 0);
v_options_3163_ = lean_ctor_get(v_toCold_3162_, 2);
v_hasTrace_3164_ = lean_ctor_get_uint8(v_options_3163_, sizeof(void*)*1);
if (v_hasTrace_3164_ == 0)
{
v___y_3043_ = v_a_3088_;
v___y_3044_ = v___y_3076_;
v___y_3045_ = v___y_3077_;
v___y_3046_ = v___y_3078_;
v___y_3047_ = v___y_3079_;
v___y_3048_ = v___y_3080_;
v___y_3049_ = v___y_3081_;
v___y_3050_ = v___y_3082_;
v___y_3051_ = v___y_3083_;
v___y_3052_ = v___y_3084_;
v___y_3053_ = v___y_3085_;
goto v___jp_3042_;
}
else
{
lean_object* v_inheritedTraceOptions_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; uint8_t v___x_3168_; 
v_inheritedTraceOptions_3165_ = lean_ctor_get(v_toCold_3162_, 11);
v___x_3166_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__8));
v___x_3167_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9);
v___x_3168_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3165_, v_options_3163_, v___x_3167_);
if (v___x_3168_ == 0)
{
v___y_3043_ = v_a_3088_;
v___y_3044_ = v___y_3076_;
v___y_3045_ = v___y_3077_;
v___y_3046_ = v___y_3078_;
v___y_3047_ = v___y_3079_;
v___y_3048_ = v___y_3080_;
v___y_3049_ = v___y_3081_;
v___y_3050_ = v___y_3082_;
v___y_3051_ = v___y_3083_;
v___y_3052_ = v___y_3084_;
v___y_3053_ = v___y_3085_;
goto v___jp_3042_;
}
else
{
lean_object* v___x_3169_; 
lean_inc(v_a_3088_);
v___x_3169_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_a_3088_, v___y_3076_, v___y_3084_);
if (lean_obj_tag(v___x_3169_) == 0)
{
lean_object* v_a_3170_; lean_object* v___x_3171_; 
v_a_3170_ = lean_ctor_get(v___x_3169_, 0);
lean_inc(v_a_3170_);
lean_dec_ref_known(v___x_3169_, 1);
v___x_3171_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3166_, v_a_3170_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_);
if (lean_obj_tag(v___x_3171_) == 0)
{
lean_dec_ref_known(v___x_3171_, 1);
v___y_3043_ = v_a_3088_;
v___y_3044_ = v___y_3076_;
v___y_3045_ = v___y_3077_;
v___y_3046_ = v___y_3078_;
v___y_3047_ = v___y_3079_;
v___y_3048_ = v___y_3080_;
v___y_3049_ = v___y_3081_;
v___y_3050_ = v___y_3082_;
v___y_3051_ = v___y_3083_;
v___y_3052_ = v___y_3084_;
v___y_3053_ = v___y_3085_;
goto v___jp_3042_;
}
else
{
lean_dec(v_a_3088_);
lean_dec(v___y_3085_);
lean_dec_ref(v___y_3084_);
lean_dec(v___y_3083_);
lean_dec_ref(v___y_3082_);
lean_dec(v___y_3081_);
lean_dec_ref(v___y_3080_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec(v___y_3076_);
return v___x_3171_;
}
}
else
{
lean_object* v_a_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3179_; 
lean_dec(v_a_3088_);
lean_dec(v___y_3085_);
lean_dec_ref(v___y_3084_);
lean_dec(v___y_3083_);
lean_dec_ref(v___y_3082_);
lean_dec(v___y_3081_);
lean_dec_ref(v___y_3080_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec(v___y_3076_);
v_a_3172_ = lean_ctor_get(v___x_3169_, 0);
v_isSharedCheck_3179_ = !lean_is_exclusive(v___x_3169_);
if (v_isSharedCheck_3179_ == 0)
{
v___x_3174_ = v___x_3169_;
v_isShared_3175_ = v_isSharedCheck_3179_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_a_3172_);
lean_dec(v___x_3169_);
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
}
}
}
else
{
lean_object* v_a_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3187_; 
lean_dec(v___y_3085_);
lean_dec_ref(v___y_3084_);
lean_dec(v___y_3083_);
lean_dec_ref(v___y_3082_);
lean_dec(v___y_3081_);
lean_dec_ref(v___y_3080_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec(v___y_3076_);
v_a_3180_ = lean_ctor_get(v___x_3087_, 0);
v_isSharedCheck_3187_ = !lean_is_exclusive(v___x_3087_);
if (v_isSharedCheck_3187_ == 0)
{
v___x_3182_ = v___x_3087_;
v_isShared_3183_ = v_isSharedCheck_3187_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_a_3180_);
lean_dec(v___x_3087_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3187_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v___x_3185_; 
if (v_isShared_3183_ == 0)
{
v___x_3185_ = v___x_3182_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v_a_3180_);
v___x_3185_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
return v___x_3185_;
}
}
}
}
}
else
{
lean_object* v___x_3202_; lean_object* v___x_3204_; 
lean_dec(v_a_2991_);
lean_dec_ref(v_a_2990_);
lean_dec(v_a_2989_);
lean_dec_ref(v_a_2988_);
lean_dec(v_a_2987_);
lean_dec_ref(v_a_2986_);
lean_dec(v_a_2985_);
lean_dec_ref(v_a_2984_);
lean_dec(v_a_2983_);
lean_dec(v_a_2982_);
lean_dec_ref(v_c_2981_);
v___x_3202_ = lean_box(0);
if (v_isShared_3069_ == 0)
{
lean_ctor_set(v___x_3068_, 0, v___x_3202_);
v___x_3204_ = v___x_3068_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v___x_3202_);
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
else
{
lean_object* v_a_3207_; lean_object* v___x_3209_; uint8_t v_isShared_3210_; uint8_t v_isSharedCheck_3214_; 
lean_dec(v_a_2991_);
lean_dec_ref(v_a_2990_);
lean_dec(v_a_2989_);
lean_dec_ref(v_a_2988_);
lean_dec(v_a_2987_);
lean_dec_ref(v_a_2986_);
lean_dec(v_a_2985_);
lean_dec_ref(v_a_2984_);
lean_dec(v_a_2983_);
lean_dec(v_a_2982_);
lean_dec_ref(v_c_2981_);
v_a_3207_ = lean_ctor_get(v___x_3065_, 0);
v_isSharedCheck_3214_ = !lean_is_exclusive(v___x_3065_);
if (v_isSharedCheck_3214_ == 0)
{
v___x_3209_ = v___x_3065_;
v_isShared_3210_ = v_isSharedCheck_3214_;
goto v_resetjp_3208_;
}
else
{
lean_inc(v_a_3207_);
lean_dec(v___x_3065_);
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
v___jp_2993_:
{
lean_object* v___x_2994_; lean_object* v___x_2995_; 
v___x_2994_ = lean_box(0);
v___x_2995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2995_, 0, v___x_2994_);
return v___x_2995_;
}
v___jp_2996_:
{
lean_object* v___x_3001_; 
v___x_3001_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(v___y_2997_, v___y_2999_, v___y_3000_);
lean_dec_ref(v___y_3000_);
if (lean_obj_tag(v___x_3001_) == 0)
{
lean_object* v_a_3002_; lean_object* v___x_3004_; uint8_t v_isShared_3005_; uint8_t v_isSharedCheck_3014_; 
v_a_3002_ = lean_ctor_get(v___x_3001_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_3004_ = v___x_3001_;
v_isShared_3005_ = v_isSharedCheck_3014_;
goto v_resetjp_3003_;
}
else
{
lean_inc(v_a_3002_);
lean_dec(v___x_3001_);
v___x_3004_ = lean_box(0);
v_isShared_3005_ = v_isSharedCheck_3014_;
goto v_resetjp_3003_;
}
v_resetjp_3003_:
{
uint8_t v___x_3006_; uint8_t v___x_3007_; uint8_t v___x_3008_; 
v___x_3006_ = 0;
v___x_3007_ = lean_unbox(v_a_3002_);
lean_dec(v_a_3002_);
v___x_3008_ = l_Lean_instBEqLBool_beq(v___x_3007_, v___x_3006_);
if (v___x_3008_ == 0)
{
lean_object* v___x_3009_; lean_object* v___x_3011_; 
lean_dec(v___y_2999_);
lean_dec(v___y_2998_);
v___x_3009_ = lean_box(0);
if (v_isShared_3005_ == 0)
{
lean_ctor_set(v___x_3004_, 0, v___x_3009_);
v___x_3011_ = v___x_3004_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v___x_3009_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
return v___x_3011_;
}
}
else
{
lean_object* v___x_3013_; 
lean_del_object(v___x_3004_);
v___x_3013_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v___y_2998_, v___y_2999_);
lean_dec(v___y_2999_);
return v___x_3013_;
}
}
}
else
{
lean_object* v_a_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3022_; 
lean_dec(v___y_2999_);
lean_dec(v___y_2998_);
v_a_3015_ = lean_ctor_get(v___x_3001_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_3017_ = v___x_3001_;
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_a_3015_);
lean_dec(v___x_3001_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v___x_3020_; 
if (v_isShared_3018_ == 0)
{
v___x_3020_ = v___x_3017_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_a_3015_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
return v___x_3020_;
}
}
}
}
v___jp_3023_:
{
lean_object* v_p_3034_; lean_object* v___x_3035_; 
v_p_3034_ = lean_ctor_get(v___y_3025_, 0);
lean_inc_ref(v_p_3034_);
v___x_3035_ = l_Int_Internal_Linear_Poly_updateOccs___redArg(v_p_3034_, v___y_3029_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_);
lean_dec(v___y_3033_);
lean_dec(v___y_3031_);
lean_dec_ref(v___y_3030_);
if (lean_obj_tag(v___x_3035_) == 0)
{
lean_object* v___x_3036_; uint8_t v___x_3037_; 
lean_dec_ref_known(v___x_3035_, 1);
v___x_3036_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9);
v___x_3037_ = lean_int_dec_lt(v___y_3028_, v___x_3036_);
lean_dec(v___y_3028_);
if (v___x_3037_ == 0)
{
lean_object* v___x_3038_; lean_object* v___x_3039_; 
lean_dec_ref(v___y_3026_);
v___x_3038_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_3039_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3038_, v___y_3024_, v___y_3029_);
if (lean_obj_tag(v___x_3039_) == 0)
{
lean_dec_ref_known(v___x_3039_, 1);
v___y_2997_ = v___y_3025_;
v___y_2998_ = v___y_3027_;
v___y_2999_ = v___y_3029_;
v___y_3000_ = v___y_3032_;
goto v___jp_2996_;
}
else
{
lean_dec_ref(v___y_3032_);
lean_dec(v___y_3029_);
lean_dec(v___y_3027_);
lean_dec_ref(v___y_3025_);
return v___x_3039_;
}
}
else
{
lean_object* v___x_3040_; lean_object* v___x_3041_; 
lean_dec_ref(v___y_3024_);
v___x_3040_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_3041_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3040_, v___y_3026_, v___y_3029_);
if (lean_obj_tag(v___x_3041_) == 0)
{
lean_dec_ref_known(v___x_3041_, 1);
v___y_2997_ = v___y_3025_;
v___y_2998_ = v___y_3027_;
v___y_2999_ = v___y_3029_;
v___y_3000_ = v___y_3032_;
goto v___jp_2996_;
}
else
{
lean_dec_ref(v___y_3032_);
lean_dec(v___y_3029_);
lean_dec(v___y_3027_);
lean_dec_ref(v___y_3025_);
return v___x_3041_;
}
}
}
else
{
lean_dec_ref(v___y_3032_);
lean_dec(v___y_3029_);
lean_dec(v___y_3028_);
lean_dec(v___y_3027_);
lean_dec_ref(v___y_3026_);
lean_dec_ref(v___y_3025_);
lean_dec_ref(v___y_3024_);
return v___x_3035_;
}
}
v___jp_3042_:
{
lean_object* v___x_3054_; lean_object* v___x_3055_; 
v___x_3054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3054_, 0, v___y_3043_);
v___x_3055_ = l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(v___x_3054_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_);
lean_dec(v___y_3053_);
lean_dec_ref(v___y_3052_);
lean_dec(v___y_3051_);
lean_dec_ref(v___y_3050_);
lean_dec(v___y_3049_);
lean_dec_ref(v___y_3048_);
lean_dec(v___y_3047_);
lean_dec_ref(v___y_3046_);
lean_dec(v___y_3045_);
lean_dec(v___y_3044_);
if (lean_obj_tag(v___x_3055_) == 0)
{
lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3063_; 
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_3055_);
if (v_isSharedCheck_3063_ == 0)
{
lean_object* v_unused_3064_; 
v_unused_3064_ = lean_ctor_get(v___x_3055_, 0);
lean_dec(v_unused_3064_);
v___x_3057_ = v___x_3055_;
v_isShared_3058_ = v_isSharedCheck_3063_;
goto v_resetjp_3056_;
}
else
{
lean_dec(v___x_3055_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3063_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3059_; lean_object* v___x_3061_; 
v___x_3059_ = lean_box(0);
if (v_isShared_3058_ == 0)
{
lean_ctor_set(v___x_3057_, 0, v___x_3059_);
v___x_3061_ = v___x_3057_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v___x_3059_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
}
else
{
return v___x_3055_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___boxed(lean_object* v_c_3215_, lean_object* v_a_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_){
_start:
{
lean_object* v_res_3227_; 
v_res_3227_ = lean_grind_cutsat_assert_le(v_c_3215_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_);
return v_res_3227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(lean_object* v_c_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_){
_start:
{
lean_object* v_p_3240_; lean_object* v___x_3241_; 
v_p_3240_ = lean_ctor_get(v_c_3228_, 0);
lean_inc_ref(v_p_3240_);
v___x_3241_ = l_Int_Internal_Linear_Poly_normCommRing_x3f(v_p_3240_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_);
if (lean_obj_tag(v___x_3241_) == 0)
{
lean_object* v_a_3242_; 
v_a_3242_ = lean_ctor_get(v___x_3241_, 0);
lean_inc(v_a_3242_);
lean_dec_ref_known(v___x_3241_, 1);
if (lean_obj_tag(v_a_3242_) == 1)
{
lean_object* v_val_3243_; lean_object* v_snd_3244_; lean_object* v_fst_3245_; lean_object* v_fst_3246_; lean_object* v_snd_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3256_; 
v_val_3243_ = lean_ctor_get(v_a_3242_, 0);
lean_inc(v_val_3243_);
lean_dec_ref_known(v_a_3242_, 1);
v_snd_3244_ = lean_ctor_get(v_val_3243_, 1);
lean_inc(v_snd_3244_);
v_fst_3245_ = lean_ctor_get(v_val_3243_, 0);
lean_inc(v_fst_3245_);
lean_dec(v_val_3243_);
v_fst_3246_ = lean_ctor_get(v_snd_3244_, 0);
v_snd_3247_ = lean_ctor_get(v_snd_3244_, 1);
v_isSharedCheck_3256_ = !lean_is_exclusive(v_snd_3244_);
if (v_isSharedCheck_3256_ == 0)
{
v___x_3249_ = v_snd_3244_;
v_isShared_3250_ = v_isSharedCheck_3256_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_snd_3247_);
lean_inc(v_fst_3246_);
lean_dec(v_snd_3244_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3256_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v___x_3251_; lean_object* v___x_3253_; 
v___x_3251_ = lean_alloc_ctor(17, 3, 0);
lean_ctor_set(v___x_3251_, 0, v_c_3228_);
lean_ctor_set(v___x_3251_, 1, v_fst_3245_);
lean_ctor_set(v___x_3251_, 2, v_fst_3246_);
if (v_isShared_3250_ == 0)
{
lean_ctor_set(v___x_3249_, 1, v___x_3251_);
lean_ctor_set(v___x_3249_, 0, v_snd_3247_);
v___x_3253_ = v___x_3249_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v_snd_3247_);
lean_ctor_set(v_reuseFailAlloc_3255_, 1, v___x_3251_);
v___x_3253_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
lean_object* v___x_3254_; 
lean_inc(v_a_3238_);
lean_inc_ref(v_a_3237_);
lean_inc(v_a_3236_);
lean_inc_ref(v_a_3235_);
lean_inc(v_a_3234_);
lean_inc_ref(v_a_3233_);
lean_inc(v_a_3232_);
lean_inc_ref(v_a_3231_);
lean_inc(v_a_3230_);
lean_inc(v_a_3229_);
v___x_3254_ = lean_grind_cutsat_assert_le(v___x_3253_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_);
return v___x_3254_;
}
}
}
else
{
lean_object* v___x_3257_; 
lean_dec(v_a_3242_);
lean_inc(v_a_3238_);
lean_inc_ref(v_a_3237_);
lean_inc(v_a_3236_);
lean_inc_ref(v_a_3235_);
lean_inc(v_a_3234_);
lean_inc_ref(v_a_3233_);
lean_inc(v_a_3232_);
lean_inc_ref(v_a_3231_);
lean_inc(v_a_3230_);
lean_inc(v_a_3229_);
v___x_3257_ = lean_grind_cutsat_assert_le(v_c_3228_, v_a_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_);
return v___x_3257_;
}
}
else
{
lean_object* v_a_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3265_; 
lean_dec_ref(v_c_3228_);
v_a_3258_ = lean_ctor_get(v___x_3241_, 0);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3241_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3260_ = v___x_3241_;
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_a_3258_);
lean_dec(v___x_3241_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
lean_object* v___x_3263_; 
if (v_isShared_3261_ == 0)
{
v___x_3263_ = v___x_3260_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_a_3258_);
v___x_3263_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
return v___x_3263_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore___boxed(lean_object* v_c_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_, lean_object* v_a_3272_, lean_object* v_a_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_){
_start:
{
lean_object* v_res_3278_; 
v_res_3278_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v_c_3266_, v_a_3267_, v_a_3268_, v_a_3269_, v_a_3270_, v_a_3271_, v_a_3272_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_);
lean_dec(v_a_3276_);
lean_dec_ref(v_a_3275_);
lean_dec(v_a_3274_);
lean_dec_ref(v_a_3273_);
lean_dec(v_a_3272_);
lean_dec_ref(v_a_3271_);
lean_dec(v_a_3270_);
lean_dec_ref(v_a_3269_);
lean_dec(v_a_3268_);
lean_dec(v_a_3267_);
return v_res_3278_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0(void){
_start:
{
lean_object* v___x_3279_; lean_object* v___x_3280_; 
v___x_3279_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0);
v___x_3280_ = lean_int_neg(v___x_3279_);
return v___x_3280_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__3(void){
_start:
{
lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; 
v___x_3287_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__2));
v___x_3288_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_3289_ = l_Lean_Name_append(v___x_3288_, v___x_3287_);
return v___x_3289_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__5(void){
_start:
{
lean_object* v___x_3291_; lean_object* v___x_3292_; 
v___x_3291_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__4));
v___x_3292_ = l_Lean_stringToMessageData(v___x_3291_);
return v___x_3292_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__10(void){
_start:
{
lean_object* v___x_3299_; lean_object* v___x_3300_; 
v___x_3299_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__9));
v___x_3300_ = l_Lean_stringToMessageData(v___x_3299_);
return v___x_3300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe(lean_object* v_e_3301_, uint8_t v_eqTrue_3302_, lean_object* v_a_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_){
_start:
{
lean_object* v_c_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___x_3356_; 
lean_inc_ref(v_e_3301_);
v___x_3356_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3301_, v_a_3310_);
if (lean_obj_tag(v___x_3356_) == 0)
{
lean_object* v_a_3357_; lean_object* v___x_3358_; uint8_t v___x_3359_; 
v_a_3357_ = lean_ctor_get(v___x_3356_, 0);
lean_inc(v_a_3357_);
lean_dec_ref_known(v___x_3356_, 1);
v___x_3358_ = l_Lean_Expr_cleanupAnnotations(v_a_3357_);
v___x_3359_ = l_Lean_Expr_isApp(v___x_3358_);
if (v___x_3359_ == 0)
{
lean_dec_ref(v___x_3358_);
lean_dec_ref(v_e_3301_);
goto v___jp_3336_;
}
else
{
lean_object* v_arg_3360_; lean_object* v___x_3361_; uint8_t v___x_3362_; 
v_arg_3360_ = lean_ctor_get(v___x_3358_, 1);
lean_inc_ref(v_arg_3360_);
v___x_3361_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3358_);
v___x_3362_ = l_Lean_Expr_isApp(v___x_3361_);
if (v___x_3362_ == 0)
{
lean_dec_ref(v___x_3361_);
lean_dec_ref(v_arg_3360_);
lean_dec_ref(v_e_3301_);
goto v___jp_3336_;
}
else
{
lean_object* v_arg_3363_; lean_object* v___y_3365_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v___y_3371_; lean_object* v___y_3372_; lean_object* v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3419_; lean_object* v___y_3420_; lean_object* v___y_3421_; lean_object* v___x_3433_; uint8_t v___x_3434_; 
v_arg_3363_ = lean_ctor_get(v___x_3361_, 1);
lean_inc_ref(v_arg_3363_);
v___x_3433_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3361_);
v___x_3434_ = l_Lean_Expr_isApp(v___x_3433_);
if (v___x_3434_ == 0)
{
lean_dec_ref(v___x_3433_);
lean_dec_ref(v_arg_3363_);
lean_dec_ref(v_arg_3360_);
lean_dec_ref(v_e_3301_);
goto v___jp_3336_;
}
else
{
lean_object* v_arg_3435_; lean_object* v___x_3436_; uint8_t v___x_3437_; 
v_arg_3435_ = lean_ctor_get(v___x_3433_, 1);
lean_inc_ref(v_arg_3435_);
v___x_3436_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3433_);
v___x_3437_ = l_Lean_Expr_isApp(v___x_3436_);
if (v___x_3437_ == 0)
{
lean_dec_ref(v___x_3436_);
lean_dec_ref(v_arg_3435_);
lean_dec_ref(v_arg_3363_);
lean_dec_ref(v_arg_3360_);
lean_dec_ref(v_e_3301_);
goto v___jp_3336_;
}
else
{
lean_object* v___x_3438_; lean_object* v___x_3439_; uint8_t v___x_3440_; 
v___x_3438_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3436_);
v___x_3439_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__8));
v___x_3440_ = l_Lean_Expr_isConstOf(v___x_3438_, v___x_3439_);
lean_dec_ref(v___x_3438_);
if (v___x_3440_ == 0)
{
lean_dec_ref(v_arg_3435_);
lean_dec_ref(v_arg_3363_);
lean_dec_ref(v_arg_3360_);
lean_dec_ref(v_e_3301_);
goto v___jp_3336_;
}
else
{
lean_object* v___x_3441_; 
v___x_3441_ = l_Lean_Meta_Structural_isInstLEInt___redArg(v_arg_3435_, v_a_3310_);
if (lean_obj_tag(v___x_3441_) == 0)
{
lean_object* v_a_3442_; lean_object* v___x_3444_; uint8_t v_isShared_3445_; uint8_t v_isSharedCheck_3511_; 
v_a_3442_ = lean_ctor_get(v___x_3441_, 0);
v_isSharedCheck_3511_ = !lean_is_exclusive(v___x_3441_);
if (v_isSharedCheck_3511_ == 0)
{
v___x_3444_ = v___x_3441_;
v_isShared_3445_ = v_isSharedCheck_3511_;
goto v_resetjp_3443_;
}
else
{
lean_inc(v_a_3442_);
lean_dec(v___x_3441_);
v___x_3444_ = lean_box(0);
v_isShared_3445_ = v_isSharedCheck_3511_;
goto v_resetjp_3443_;
}
v_resetjp_3443_:
{
uint8_t v___x_3446_; 
v___x_3446_ = lean_unbox(v_a_3442_);
lean_dec(v_a_3442_);
if (v___x_3446_ == 0)
{
lean_object* v___x_3447_; lean_object* v___x_3449_; 
lean_dec_ref(v_arg_3363_);
lean_dec_ref(v_arg_3360_);
lean_dec_ref(v_e_3301_);
v___x_3447_ = lean_box(0);
if (v_isShared_3445_ == 0)
{
lean_ctor_set(v___x_3444_, 0, v___x_3447_);
v___x_3449_ = v___x_3444_;
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
else
{
lean_object* v___x_3451_; 
lean_del_object(v___x_3444_);
lean_inc_ref(v_arg_3360_);
v___x_3451_ = l_Lean_Meta_getIntValue_x3f(v_arg_3360_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
if (lean_obj_tag(v___x_3451_) == 0)
{
lean_object* v_a_3452_; 
v_a_3452_ = lean_ctor_get(v___x_3451_, 0);
lean_inc(v_a_3452_);
lean_dec_ref_known(v___x_3451_, 1);
if (lean_obj_tag(v_a_3452_) == 1)
{
lean_object* v_val_3453_; lean_object* v___x_3454_; uint8_t v___x_3455_; 
v_val_3453_ = lean_ctor_get(v_a_3452_, 0);
lean_inc(v_val_3453_);
lean_dec_ref_known(v_a_3452_, 1);
v___x_3454_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9);
v___x_3455_ = lean_int_dec_eq(v_val_3453_, v___x_3454_);
lean_dec(v_val_3453_);
if (v___x_3455_ == 0)
{
v___y_3412_ = v_a_3303_;
v___y_3413_ = v_a_3304_;
v___y_3414_ = v_a_3305_;
v___y_3415_ = v_a_3306_;
v___y_3416_ = v_a_3307_;
v___y_3417_ = v_a_3308_;
v___y_3418_ = v_a_3309_;
v___y_3419_ = v_a_3310_;
v___y_3420_ = v_a_3311_;
v___y_3421_ = v_a_3312_;
goto v___jp_3411_;
}
else
{
lean_object* v___x_3456_; 
lean_inc_ref(v_arg_3363_);
v___x_3456_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly_x3f(v_arg_3363_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
if (lean_obj_tag(v___x_3456_) == 0)
{
lean_object* v_a_3457_; 
v_a_3457_ = lean_ctor_get(v___x_3456_, 0);
lean_inc(v_a_3457_);
lean_dec_ref_known(v___x_3456_, 1);
if (lean_obj_tag(v_a_3457_) == 1)
{
lean_object* v_val_3458_; lean_object* v___x_3460_; uint8_t v_isShared_3461_; uint8_t v_isSharedCheck_3494_; 
lean_dec_ref(v_arg_3363_);
lean_dec_ref(v_arg_3360_);
v_val_3458_ = lean_ctor_get(v_a_3457_, 0);
v_isSharedCheck_3494_ = !lean_is_exclusive(v_a_3457_);
if (v_isSharedCheck_3494_ == 0)
{
v___x_3460_ = v_a_3457_;
v_isShared_3461_ = v_isSharedCheck_3494_;
goto v_resetjp_3459_;
}
else
{
lean_inc(v_val_3458_);
lean_dec(v_a_3457_);
v___x_3460_ = lean_box(0);
v_isShared_3461_ = v_isSharedCheck_3494_;
goto v_resetjp_3459_;
}
v_resetjp_3459_:
{
lean_object* v___y_3463_; lean_object* v___y_3464_; lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v_toCold_3483_; lean_object* v_options_3484_; uint8_t v_hasTrace_3485_; 
v_toCold_3483_ = lean_ctor_get(v_a_3311_, 0);
v_options_3484_ = lean_ctor_get(v_toCold_3483_, 2);
v_hasTrace_3485_ = lean_ctor_get_uint8(v_options_3484_, sizeof(void*)*1);
if (v_hasTrace_3485_ == 0)
{
v___y_3463_ = v_a_3303_;
v___y_3464_ = v_a_3304_;
v___y_3465_ = v_a_3305_;
v___y_3466_ = v_a_3306_;
v___y_3467_ = v_a_3307_;
v___y_3468_ = v_a_3308_;
v___y_3469_ = v_a_3309_;
v___y_3470_ = v_a_3310_;
v___y_3471_ = v_a_3311_;
v___y_3472_ = v_a_3312_;
goto v___jp_3462_;
}
else
{
lean_object* v_inheritedTraceOptions_3486_; lean_object* v___x_3487_; lean_object* v___x_3488_; uint8_t v___x_3489_; 
v_inheritedTraceOptions_3486_ = lean_ctor_get(v_toCold_3483_, 11);
v___x_3487_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__2));
v___x_3488_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__3);
v___x_3489_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3486_, v_options_3484_, v___x_3488_);
if (v___x_3489_ == 0)
{
v___y_3463_ = v_a_3303_;
v___y_3464_ = v_a_3304_;
v___y_3465_ = v_a_3305_;
v___y_3466_ = v_a_3306_;
v___y_3467_ = v_a_3307_;
v___y_3468_ = v_a_3308_;
v___y_3469_ = v_a_3309_;
v___y_3470_ = v_a_3310_;
v___y_3471_ = v_a_3311_;
v___y_3472_ = v_a_3312_;
goto v___jp_3462_;
}
else
{
lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; 
v___x_3490_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__10, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__10_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__10);
lean_inc_ref(v_e_3301_);
v___x_3491_ = l_Lean_MessageData_ofExpr(v_e_3301_);
v___x_3492_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3492_, 0, v___x_3490_);
lean_ctor_set(v___x_3492_, 1, v___x_3491_);
v___x_3493_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3487_, v___x_3492_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
if (lean_obj_tag(v___x_3493_) == 0)
{
lean_dec_ref_known(v___x_3493_, 1);
v___y_3463_ = v_a_3303_;
v___y_3464_ = v_a_3304_;
v___y_3465_ = v_a_3305_;
v___y_3466_ = v_a_3306_;
v___y_3467_ = v_a_3307_;
v___y_3468_ = v_a_3308_;
v___y_3469_ = v_a_3309_;
v___y_3470_ = v_a_3310_;
v___y_3471_ = v_a_3311_;
v___y_3472_ = v_a_3312_;
goto v___jp_3462_;
}
else
{
lean_del_object(v___x_3460_);
lean_dec(v_val_3458_);
lean_dec_ref(v_e_3301_);
return v___x_3493_;
}
}
}
v___jp_3462_:
{
if (v_eqTrue_3302_ == 0)
{
lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; 
lean_del_object(v___x_3460_);
v___x_3473_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0);
v___x_3474_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0);
lean_inc(v_val_3458_);
v___x_3475_ = l_Int_Internal_Linear_Poly_mul(v_val_3458_, v___x_3474_);
v___x_3476_ = l_Int_Internal_Linear_Poly_addConst(v___x_3475_, v___x_3473_);
v___x_3477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3477_, 0, v_e_3301_);
lean_ctor_set(v___x_3477_, 1, v_val_3458_);
v___x_3478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3478_, 0, v___x_3476_);
lean_ctor_set(v___x_3478_, 1, v___x_3477_);
v_c_3315_ = v___x_3478_;
v___y_3316_ = v___y_3463_;
v___y_3317_ = v___y_3464_;
v___y_3318_ = v___y_3465_;
v___y_3319_ = v___y_3466_;
v___y_3320_ = v___y_3467_;
v___y_3321_ = v___y_3468_;
v___y_3322_ = v___y_3469_;
v___y_3323_ = v___y_3470_;
v___y_3324_ = v___y_3471_;
v___y_3325_ = v___y_3472_;
goto v___jp_3314_;
}
else
{
lean_object* v___x_3480_; 
if (v_isShared_3461_ == 0)
{
lean_ctor_set_tag(v___x_3460_, 0);
lean_ctor_set(v___x_3460_, 0, v_e_3301_);
v___x_3480_ = v___x_3460_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v_e_3301_);
v___x_3480_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
lean_object* v___x_3481_; 
v___x_3481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3481_, 0, v_val_3458_);
lean_ctor_set(v___x_3481_, 1, v___x_3480_);
v_c_3315_ = v___x_3481_;
v___y_3316_ = v___y_3463_;
v___y_3317_ = v___y_3464_;
v___y_3318_ = v___y_3465_;
v___y_3319_ = v___y_3466_;
v___y_3320_ = v___y_3467_;
v___y_3321_ = v___y_3468_;
v___y_3322_ = v___y_3469_;
v___y_3323_ = v___y_3470_;
v___y_3324_ = v___y_3471_;
v___y_3325_ = v___y_3472_;
goto v___jp_3314_;
}
}
}
}
}
else
{
lean_dec(v_a_3457_);
v___y_3412_ = v_a_3303_;
v___y_3413_ = v_a_3304_;
v___y_3414_ = v_a_3305_;
v___y_3415_ = v_a_3306_;
v___y_3416_ = v_a_3307_;
v___y_3417_ = v_a_3308_;
v___y_3418_ = v_a_3309_;
v___y_3419_ = v_a_3310_;
v___y_3420_ = v_a_3311_;
v___y_3421_ = v_a_3312_;
goto v___jp_3411_;
}
}
else
{
lean_object* v_a_3495_; lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3502_; 
lean_dec_ref(v_arg_3363_);
lean_dec_ref(v_arg_3360_);
lean_dec_ref(v_e_3301_);
v_a_3495_ = lean_ctor_get(v___x_3456_, 0);
v_isSharedCheck_3502_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3502_ == 0)
{
v___x_3497_ = v___x_3456_;
v_isShared_3498_ = v_isSharedCheck_3502_;
goto v_resetjp_3496_;
}
else
{
lean_inc(v_a_3495_);
lean_dec(v___x_3456_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3502_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
lean_object* v___x_3500_; 
if (v_isShared_3498_ == 0)
{
v___x_3500_ = v___x_3497_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v_a_3495_);
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
}
else
{
lean_dec(v_a_3452_);
v___y_3412_ = v_a_3303_;
v___y_3413_ = v_a_3304_;
v___y_3414_ = v_a_3305_;
v___y_3415_ = v_a_3306_;
v___y_3416_ = v_a_3307_;
v___y_3417_ = v_a_3308_;
v___y_3418_ = v_a_3309_;
v___y_3419_ = v_a_3310_;
v___y_3420_ = v_a_3311_;
v___y_3421_ = v_a_3312_;
goto v___jp_3411_;
}
}
else
{
lean_object* v_a_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3510_; 
lean_dec_ref(v_arg_3363_);
lean_dec_ref(v_arg_3360_);
lean_dec_ref(v_e_3301_);
v_a_3503_ = lean_ctor_get(v___x_3451_, 0);
v_isSharedCheck_3510_ = !lean_is_exclusive(v___x_3451_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3505_ = v___x_3451_;
v_isShared_3506_ = v_isSharedCheck_3510_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_a_3503_);
lean_dec(v___x_3451_);
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
}
else
{
lean_object* v_a_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3519_; 
lean_dec_ref(v_arg_3363_);
lean_dec_ref(v_arg_3360_);
lean_dec_ref(v_e_3301_);
v_a_3512_ = lean_ctor_get(v___x_3441_, 0);
v_isSharedCheck_3519_ = !lean_is_exclusive(v___x_3441_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3514_ = v___x_3441_;
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_a_3512_);
lean_dec(v___x_3441_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
lean_object* v___x_3517_; 
if (v_isShared_3515_ == 0)
{
v___x_3517_ = v___x_3514_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v_a_3512_);
v___x_3517_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
return v___x_3517_;
}
}
}
}
}
}
v___jp_3364_:
{
lean_object* v___x_3375_; 
v___x_3375_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_3301_, v___y_3365_);
if (lean_obj_tag(v___x_3375_) == 0)
{
lean_object* v_a_3376_; lean_object* v___x_3377_; 
v_a_3376_ = lean_ctor_get(v___x_3375_, 0);
lean_inc_n(v_a_3376_, 2);
lean_dec_ref_known(v___x_3375_, 1);
v___x_3377_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_arg_3363_, v_a_3376_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_);
if (lean_obj_tag(v___x_3377_) == 0)
{
lean_object* v_a_3378_; lean_object* v___x_3379_; 
v_a_3378_ = lean_ctor_get(v___x_3377_, 0);
lean_inc(v_a_3378_);
lean_dec_ref_known(v___x_3377_, 1);
v___x_3379_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_arg_3360_, v_a_3376_, v___y_3365_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_);
if (lean_obj_tag(v___x_3379_) == 0)
{
lean_object* v_a_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; 
v_a_3380_ = lean_ctor_get(v___x_3379_, 0);
lean_inc_n(v_a_3380_, 2);
lean_dec_ref_known(v___x_3379_, 1);
lean_inc(v_a_3378_);
v___x_3381_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3381_, 0, v_a_3378_);
lean_ctor_set(v___x_3381_, 1, v_a_3380_);
v___x_3382_ = l_Int_Internal_Linear_Expr_norm(v___x_3381_);
lean_dec_ref_known(v___x_3381_, 2);
if (v_eqTrue_3302_ == 0)
{
lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; 
v___x_3383_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0);
v___x_3384_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0);
v___x_3385_ = l_Int_Internal_Linear_Poly_mul(v___x_3382_, v___x_3384_);
v___x_3386_ = l_Int_Internal_Linear_Poly_addConst(v___x_3385_, v___x_3383_);
v___y_3340_ = v_a_3380_;
v___y_3341_ = v___y_3370_;
v___y_3342_ = v___y_3368_;
v___y_3343_ = v___y_3369_;
v___y_3344_ = v___y_3365_;
v___y_3345_ = v___y_3367_;
v___y_3346_ = v___y_3366_;
v___y_3347_ = v___y_3372_;
v___y_3348_ = v___y_3374_;
v___y_3349_ = v___y_3371_;
v___y_3350_ = v___y_3373_;
v___y_3351_ = v_a_3378_;
v___y_3352_ = v___x_3386_;
goto v___jp_3339_;
}
else
{
v___y_3340_ = v_a_3380_;
v___y_3341_ = v___y_3370_;
v___y_3342_ = v___y_3368_;
v___y_3343_ = v___y_3369_;
v___y_3344_ = v___y_3365_;
v___y_3345_ = v___y_3367_;
v___y_3346_ = v___y_3366_;
v___y_3347_ = v___y_3372_;
v___y_3348_ = v___y_3374_;
v___y_3349_ = v___y_3371_;
v___y_3350_ = v___y_3373_;
v___y_3351_ = v_a_3378_;
v___y_3352_ = v___x_3382_;
goto v___jp_3339_;
}
}
else
{
lean_object* v_a_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3394_; 
lean_dec(v_a_3378_);
lean_dec_ref(v_e_3301_);
v_a_3387_ = lean_ctor_get(v___x_3379_, 0);
v_isSharedCheck_3394_ = !lean_is_exclusive(v___x_3379_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3389_ = v___x_3379_;
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_a_3387_);
lean_dec(v___x_3379_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v___x_3392_; 
if (v_isShared_3390_ == 0)
{
v___x_3392_ = v___x_3389_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v_a_3387_);
v___x_3392_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
return v___x_3392_;
}
}
}
}
else
{
lean_object* v_a_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3402_; 
lean_dec(v_a_3376_);
lean_dec_ref(v_arg_3360_);
lean_dec_ref(v_e_3301_);
v_a_3395_ = lean_ctor_get(v___x_3377_, 0);
v_isSharedCheck_3402_ = !lean_is_exclusive(v___x_3377_);
if (v_isSharedCheck_3402_ == 0)
{
v___x_3397_ = v___x_3377_;
v_isShared_3398_ = v_isSharedCheck_3402_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_a_3395_);
lean_dec(v___x_3377_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3402_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v___x_3400_; 
if (v_isShared_3398_ == 0)
{
v___x_3400_ = v___x_3397_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v_a_3395_);
v___x_3400_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
return v___x_3400_;
}
}
}
}
else
{
lean_object* v_a_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3410_; 
lean_dec_ref(v_arg_3363_);
lean_dec_ref(v_arg_3360_);
lean_dec_ref(v_e_3301_);
v_a_3403_ = lean_ctor_get(v___x_3375_, 0);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3375_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3405_ = v___x_3375_;
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_a_3403_);
lean_dec(v___x_3375_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
lean_object* v___x_3408_; 
if (v_isShared_3406_ == 0)
{
v___x_3408_ = v___x_3405_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v_a_3403_);
v___x_3408_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
return v___x_3408_;
}
}
}
}
v___jp_3411_:
{
lean_object* v_toCold_3422_; lean_object* v_options_3423_; uint8_t v_hasTrace_3424_; 
v_toCold_3422_ = lean_ctor_get(v___y_3420_, 0);
v_options_3423_ = lean_ctor_get(v_toCold_3422_, 2);
v_hasTrace_3424_ = lean_ctor_get_uint8(v_options_3423_, sizeof(void*)*1);
if (v_hasTrace_3424_ == 0)
{
v___y_3365_ = v___y_3412_;
v___y_3366_ = v___y_3413_;
v___y_3367_ = v___y_3414_;
v___y_3368_ = v___y_3415_;
v___y_3369_ = v___y_3416_;
v___y_3370_ = v___y_3417_;
v___y_3371_ = v___y_3418_;
v___y_3372_ = v___y_3419_;
v___y_3373_ = v___y_3420_;
v___y_3374_ = v___y_3421_;
goto v___jp_3364_;
}
else
{
lean_object* v_inheritedTraceOptions_3425_; lean_object* v___x_3426_; lean_object* v___x_3427_; uint8_t v___x_3428_; 
v_inheritedTraceOptions_3425_ = lean_ctor_get(v_toCold_3422_, 11);
v___x_3426_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__2));
v___x_3427_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__3);
v___x_3428_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3425_, v_options_3423_, v___x_3427_);
if (v___x_3428_ == 0)
{
v___y_3365_ = v___y_3412_;
v___y_3366_ = v___y_3413_;
v___y_3367_ = v___y_3414_;
v___y_3368_ = v___y_3415_;
v___y_3369_ = v___y_3416_;
v___y_3370_ = v___y_3417_;
v___y_3371_ = v___y_3418_;
v___y_3372_ = v___y_3419_;
v___y_3373_ = v___y_3420_;
v___y_3374_ = v___y_3421_;
goto v___jp_3364_;
}
else
{
lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; 
v___x_3429_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__5);
lean_inc_ref(v_e_3301_);
v___x_3430_ = l_Lean_MessageData_ofExpr(v_e_3301_);
v___x_3431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3431_, 0, v___x_3429_);
lean_ctor_set(v___x_3431_, 1, v___x_3430_);
v___x_3432_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3426_, v___x_3431_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_);
if (lean_obj_tag(v___x_3432_) == 0)
{
lean_dec_ref_known(v___x_3432_, 1);
v___y_3365_ = v___y_3412_;
v___y_3366_ = v___y_3413_;
v___y_3367_ = v___y_3414_;
v___y_3368_ = v___y_3415_;
v___y_3369_ = v___y_3416_;
v___y_3370_ = v___y_3417_;
v___y_3371_ = v___y_3418_;
v___y_3372_ = v___y_3419_;
v___y_3373_ = v___y_3420_;
v___y_3374_ = v___y_3421_;
goto v___jp_3364_;
}
else
{
lean_dec_ref(v_arg_3363_);
lean_dec_ref(v_arg_3360_);
lean_dec_ref(v_e_3301_);
return v___x_3432_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3527_; 
lean_dec_ref(v_e_3301_);
v_a_3520_ = lean_ctor_get(v___x_3356_, 0);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3356_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3522_ = v___x_3356_;
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v___x_3356_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3525_; 
if (v_isShared_3523_ == 0)
{
v___x_3525_ = v___x_3522_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_a_3520_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
return v___x_3525_;
}
}
}
v___jp_3314_:
{
lean_object* v___x_3326_; 
v___x_3326_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v_c_3315_, v___y_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_);
if (lean_obj_tag(v___x_3326_) == 0)
{
lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3334_; 
v_isSharedCheck_3334_ = !lean_is_exclusive(v___x_3326_);
if (v_isSharedCheck_3334_ == 0)
{
lean_object* v_unused_3335_; 
v_unused_3335_ = lean_ctor_get(v___x_3326_, 0);
lean_dec(v_unused_3335_);
v___x_3328_ = v___x_3326_;
v_isShared_3329_ = v_isSharedCheck_3334_;
goto v_resetjp_3327_;
}
else
{
lean_dec(v___x_3326_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3334_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v___x_3330_; lean_object* v___x_3332_; 
v___x_3330_ = lean_box(0);
if (v_isShared_3329_ == 0)
{
lean_ctor_set(v___x_3328_, 0, v___x_3330_);
v___x_3332_ = v___x_3328_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v___x_3330_);
v___x_3332_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
return v___x_3332_;
}
}
}
else
{
return v___x_3326_;
}
}
v___jp_3336_:
{
lean_object* v___x_3337_; lean_object* v___x_3338_; 
v___x_3337_ = lean_box(0);
v___x_3338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3338_, 0, v___x_3337_);
return v___x_3338_;
}
v___jp_3339_:
{
lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; 
v___x_3353_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v___x_3353_, 0, v_e_3301_);
lean_ctor_set(v___x_3353_, 1, v___y_3351_);
lean_ctor_set(v___x_3353_, 2, v___y_3340_);
lean_ctor_set_uint8(v___x_3353_, sizeof(void*)*3, v_eqTrue_3302_);
v___x_3354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3354_, 0, v___y_3352_);
lean_ctor_set(v___x_3354_, 1, v___x_3353_);
v___x_3355_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v___x_3354_, v___y_3344_, v___y_3346_, v___y_3345_, v___y_3342_, v___y_3343_, v___y_3341_, v___y_3349_, v___y_3347_, v___y_3350_, v___y_3348_);
return v___x_3355_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___boxed(lean_object* v_e_3528_, lean_object* v_eqTrue_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_){
_start:
{
uint8_t v_eqTrue_boxed_3541_; lean_object* v_res_3542_; 
v_eqTrue_boxed_3541_ = lean_unbox(v_eqTrue_3529_);
v_res_3542_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe(v_e_3528_, v_eqTrue_boxed_3541_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_);
lean_dec(v_a_3539_);
lean_dec_ref(v_a_3538_);
lean_dec(v_a_3537_);
lean_dec_ref(v_a_3536_);
lean_dec(v_a_3535_);
lean_dec_ref(v_a_3534_);
lean_dec(v_a_3533_);
lean_dec_ref(v_a_3532_);
lean_dec(v_a_3531_);
lean_dec(v_a_3530_);
return v_res_3542_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0(void){
_start:
{
lean_object* v___x_3543_; lean_object* v___x_3544_; 
v___x_3543_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0);
v___x_3544_ = l_Lean_mkIntLit(v___x_3543_);
return v___x_3544_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5(void){
_start:
{
lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; 
v___x_3552_ = lean_box(0);
v___x_3553_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__4));
v___x_3554_ = l_Lean_mkConst(v___x_3553_, v___x_3552_);
return v___x_3554_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8(void){
_start:
{
lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; 
v___x_3560_ = lean_box(0);
v___x_3561_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__7));
v___x_3562_ = l_Lean_mkConst(v___x_3561_, v___x_3560_);
return v___x_3562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe(lean_object* v_e_3563_, uint8_t v_eqTrue_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_){
_start:
{
lean_object* v___y_3577_; lean_object* v___y_3578_; lean_object* v_fst_3579_; lean_object* v_snd_3580_; lean_object* v___x_3609_; uint8_t v___x_3610_; 
lean_inc_ref(v_e_3563_);
v___x_3609_ = l_Lean_Expr_cleanupAnnotations(v_e_3563_);
v___x_3610_ = l_Lean_Expr_isApp(v___x_3609_);
if (v___x_3610_ == 0)
{
lean_dec_ref(v___x_3609_);
lean_dec_ref(v_e_3563_);
goto v___jp_3606_;
}
else
{
lean_object* v_arg_3611_; lean_object* v___x_3612_; uint8_t v___x_3613_; 
v_arg_3611_ = lean_ctor_get(v___x_3609_, 1);
lean_inc_ref(v_arg_3611_);
v___x_3612_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3609_);
v___x_3613_ = l_Lean_Expr_isApp(v___x_3612_);
if (v___x_3613_ == 0)
{
lean_dec_ref(v___x_3612_);
lean_dec_ref(v_arg_3611_);
lean_dec_ref(v_e_3563_);
goto v___jp_3606_;
}
else
{
lean_object* v_arg_3614_; lean_object* v___y_3616_; lean_object* v___x_3654_; uint8_t v___x_3655_; 
v_arg_3614_ = lean_ctor_get(v___x_3612_, 1);
lean_inc_ref(v_arg_3614_);
v___x_3654_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3612_);
v___x_3655_ = l_Lean_Expr_isApp(v___x_3654_);
if (v___x_3655_ == 0)
{
lean_dec_ref(v___x_3654_);
lean_dec_ref(v_arg_3614_);
lean_dec_ref(v_arg_3611_);
lean_dec_ref(v_e_3563_);
goto v___jp_3606_;
}
else
{
lean_object* v___x_3656_; uint8_t v___x_3657_; 
v___x_3656_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3654_);
v___x_3657_ = l_Lean_Expr_isApp(v___x_3656_);
if (v___x_3657_ == 0)
{
lean_dec_ref(v___x_3656_);
lean_dec_ref(v_arg_3614_);
lean_dec_ref(v_arg_3611_);
lean_dec_ref(v_e_3563_);
goto v___jp_3606_;
}
else
{
lean_object* v___x_3658_; lean_object* v___x_3659_; uint8_t v___x_3660_; 
v___x_3658_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3656_);
v___x_3659_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__8));
v___x_3660_ = l_Lean_Expr_isConstOf(v___x_3658_, v___x_3659_);
lean_dec_ref(v___x_3658_);
if (v___x_3660_ == 0)
{
lean_dec_ref(v_arg_3614_);
lean_dec_ref(v_arg_3611_);
lean_dec_ref(v_e_3563_);
goto v___jp_3606_;
}
else
{
if (v_eqTrue_3564_ == 0)
{
lean_object* v___x_3661_; 
v___x_3661_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5);
v___y_3616_ = v___x_3661_;
goto v___jp_3615_;
}
else
{
lean_object* v___x_3662_; 
v___x_3662_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8);
v___y_3616_ = v___x_3662_;
goto v___jp_3615_;
}
}
}
}
v___jp_3615_:
{
lean_object* v___x_3617_; 
v___x_3617_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_3563_, v_a_3565_);
if (lean_obj_tag(v___x_3617_) == 0)
{
lean_object* v_a_3618_; lean_object* v___x_3619_; 
v_a_3618_ = lean_ctor_get(v___x_3617_, 0);
lean_inc(v_a_3618_);
lean_dec_ref_known(v___x_3617_, 1);
lean_inc_ref(v_arg_3614_);
v___x_3619_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_3614_, v_a_3565_, v_a_3566_, v_a_3567_, v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_);
if (lean_obj_tag(v___x_3619_) == 0)
{
lean_object* v_a_3620_; lean_object* v_fst_3621_; lean_object* v_snd_3622_; lean_object* v___x_3623_; 
v_a_3620_ = lean_ctor_get(v___x_3619_, 0);
lean_inc(v_a_3620_);
lean_dec_ref_known(v___x_3619_, 1);
v_fst_3621_ = lean_ctor_get(v_a_3620_, 0);
lean_inc(v_fst_3621_);
v_snd_3622_ = lean_ctor_get(v_a_3620_, 1);
lean_inc(v_snd_3622_);
lean_dec(v_a_3620_);
lean_inc_ref(v_arg_3611_);
v___x_3623_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_3611_, v_a_3565_, v_a_3566_, v_a_3567_, v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_);
if (lean_obj_tag(v___x_3623_) == 0)
{
lean_object* v_a_3624_; lean_object* v_fst_3625_; lean_object* v_snd_3626_; lean_object* v___x_3627_; 
v_a_3624_ = lean_ctor_get(v___x_3623_, 0);
lean_inc(v_a_3624_);
lean_dec_ref_known(v___x_3623_, 1);
v_fst_3625_ = lean_ctor_get(v_a_3624_, 0);
lean_inc_n(v_fst_3625_, 2);
v_snd_3626_ = lean_ctor_get(v_a_3624_, 1);
lean_inc(v_snd_3626_);
lean_dec(v_a_3624_);
lean_inc(v_fst_3621_);
lean_inc_ref(v___y_3616_);
v___x_3627_ = l_Lean_mkApp6(v___y_3616_, v_arg_3614_, v_arg_3611_, v_fst_3621_, v_fst_3625_, v_snd_3622_, v_snd_3626_);
if (v_eqTrue_3564_ == 0)
{
lean_object* v___x_3628_; lean_object* v___x_3629_; 
v___x_3628_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0);
v___x_3629_ = l_Lean_mkIntAdd(v_fst_3625_, v___x_3628_);
v___y_3577_ = v___x_3627_;
v___y_3578_ = v_a_3618_;
v_fst_3579_ = v___x_3629_;
v_snd_3580_ = v_fst_3621_;
goto v___jp_3576_;
}
else
{
v___y_3577_ = v___x_3627_;
v___y_3578_ = v_a_3618_;
v_fst_3579_ = v_fst_3621_;
v_snd_3580_ = v_fst_3625_;
goto v___jp_3576_;
}
}
else
{
lean_object* v_a_3630_; lean_object* v___x_3632_; uint8_t v_isShared_3633_; uint8_t v_isSharedCheck_3637_; 
lean_dec(v_snd_3622_);
lean_dec(v_fst_3621_);
lean_dec(v_a_3618_);
lean_dec_ref(v_arg_3614_);
lean_dec_ref(v_arg_3611_);
lean_dec_ref(v_e_3563_);
v_a_3630_ = lean_ctor_get(v___x_3623_, 0);
v_isSharedCheck_3637_ = !lean_is_exclusive(v___x_3623_);
if (v_isSharedCheck_3637_ == 0)
{
v___x_3632_ = v___x_3623_;
v_isShared_3633_ = v_isSharedCheck_3637_;
goto v_resetjp_3631_;
}
else
{
lean_inc(v_a_3630_);
lean_dec(v___x_3623_);
v___x_3632_ = lean_box(0);
v_isShared_3633_ = v_isSharedCheck_3637_;
goto v_resetjp_3631_;
}
v_resetjp_3631_:
{
lean_object* v___x_3635_; 
if (v_isShared_3633_ == 0)
{
v___x_3635_ = v___x_3632_;
goto v_reusejp_3634_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v_a_3630_);
v___x_3635_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3634_;
}
v_reusejp_3634_:
{
return v___x_3635_;
}
}
}
}
else
{
lean_object* v_a_3638_; lean_object* v___x_3640_; uint8_t v_isShared_3641_; uint8_t v_isSharedCheck_3645_; 
lean_dec(v_a_3618_);
lean_dec_ref(v_arg_3614_);
lean_dec_ref(v_arg_3611_);
lean_dec_ref(v_e_3563_);
v_a_3638_ = lean_ctor_get(v___x_3619_, 0);
v_isSharedCheck_3645_ = !lean_is_exclusive(v___x_3619_);
if (v_isSharedCheck_3645_ == 0)
{
v___x_3640_ = v___x_3619_;
v_isShared_3641_ = v_isSharedCheck_3645_;
goto v_resetjp_3639_;
}
else
{
lean_inc(v_a_3638_);
lean_dec(v___x_3619_);
v___x_3640_ = lean_box(0);
v_isShared_3641_ = v_isSharedCheck_3645_;
goto v_resetjp_3639_;
}
v_resetjp_3639_:
{
lean_object* v___x_3643_; 
if (v_isShared_3641_ == 0)
{
v___x_3643_ = v___x_3640_;
goto v_reusejp_3642_;
}
else
{
lean_object* v_reuseFailAlloc_3644_; 
v_reuseFailAlloc_3644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3644_, 0, v_a_3638_);
v___x_3643_ = v_reuseFailAlloc_3644_;
goto v_reusejp_3642_;
}
v_reusejp_3642_:
{
return v___x_3643_;
}
}
}
}
else
{
lean_object* v_a_3646_; lean_object* v___x_3648_; uint8_t v_isShared_3649_; uint8_t v_isSharedCheck_3653_; 
lean_dec_ref(v_arg_3614_);
lean_dec_ref(v_arg_3611_);
lean_dec_ref(v_e_3563_);
v_a_3646_ = lean_ctor_get(v___x_3617_, 0);
v_isSharedCheck_3653_ = !lean_is_exclusive(v___x_3617_);
if (v_isSharedCheck_3653_ == 0)
{
v___x_3648_ = v___x_3617_;
v_isShared_3649_ = v_isSharedCheck_3653_;
goto v_resetjp_3647_;
}
else
{
lean_inc(v_a_3646_);
lean_dec(v___x_3617_);
v___x_3648_ = lean_box(0);
v_isShared_3649_ = v_isSharedCheck_3653_;
goto v_resetjp_3647_;
}
v_resetjp_3647_:
{
lean_object* v___x_3651_; 
if (v_isShared_3649_ == 0)
{
v___x_3651_ = v___x_3648_;
goto v_reusejp_3650_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v_a_3646_);
v___x_3651_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3650_;
}
v_reusejp_3650_:
{
return v___x_3651_;
}
}
}
}
}
}
v___jp_3576_:
{
lean_object* v___x_3581_; 
lean_inc(v___y_3578_);
v___x_3581_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_3579_, v___y_3578_, v_a_3565_, v_a_3566_, v_a_3567_, v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_);
if (lean_obj_tag(v___x_3581_) == 0)
{
lean_object* v_a_3582_; lean_object* v___x_3583_; 
v_a_3582_ = lean_ctor_get(v___x_3581_, 0);
lean_inc(v_a_3582_);
lean_dec_ref_known(v___x_3581_, 1);
v___x_3583_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_snd_3580_, v___y_3578_, v_a_3565_, v_a_3566_, v_a_3567_, v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_);
if (lean_obj_tag(v___x_3583_) == 0)
{
lean_object* v_a_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; 
v_a_3584_ = lean_ctor_get(v___x_3583_, 0);
lean_inc_n(v_a_3584_, 2);
lean_dec_ref_known(v___x_3583_, 1);
lean_inc(v_a_3582_);
v___x_3585_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3585_, 0, v_a_3582_);
lean_ctor_set(v___x_3585_, 1, v_a_3584_);
v___x_3586_ = l_Int_Internal_Linear_Expr_norm(v___x_3585_);
lean_dec_ref_known(v___x_3585_, 2);
v___x_3587_ = lean_alloc_ctor(2, 4, 1);
lean_ctor_set(v___x_3587_, 0, v_e_3563_);
lean_ctor_set(v___x_3587_, 1, v___y_3577_);
lean_ctor_set(v___x_3587_, 2, v_a_3582_);
lean_ctor_set(v___x_3587_, 3, v_a_3584_);
lean_ctor_set_uint8(v___x_3587_, sizeof(void*)*4, v_eqTrue_3564_);
v___x_3588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3588_, 0, v___x_3586_);
lean_ctor_set(v___x_3588_, 1, v___x_3587_);
v___x_3589_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v___x_3588_, v_a_3565_, v_a_3566_, v_a_3567_, v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_);
return v___x_3589_;
}
else
{
lean_object* v_a_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3597_; 
lean_dec(v_a_3582_);
lean_dec_ref(v___y_3577_);
lean_dec_ref(v_e_3563_);
v_a_3590_ = lean_ctor_get(v___x_3583_, 0);
v_isSharedCheck_3597_ = !lean_is_exclusive(v___x_3583_);
if (v_isSharedCheck_3597_ == 0)
{
v___x_3592_ = v___x_3583_;
v_isShared_3593_ = v_isSharedCheck_3597_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_a_3590_);
lean_dec(v___x_3583_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3597_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v___x_3595_; 
if (v_isShared_3593_ == 0)
{
v___x_3595_ = v___x_3592_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3596_; 
v_reuseFailAlloc_3596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3596_, 0, v_a_3590_);
v___x_3595_ = v_reuseFailAlloc_3596_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
return v___x_3595_;
}
}
}
}
else
{
lean_object* v_a_3598_; lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3605_; 
lean_dec_ref(v_snd_3580_);
lean_dec(v___y_3578_);
lean_dec_ref(v___y_3577_);
lean_dec_ref(v_e_3563_);
v_a_3598_ = lean_ctor_get(v___x_3581_, 0);
v_isSharedCheck_3605_ = !lean_is_exclusive(v___x_3581_);
if (v_isSharedCheck_3605_ == 0)
{
v___x_3600_ = v___x_3581_;
v_isShared_3601_ = v_isSharedCheck_3605_;
goto v_resetjp_3599_;
}
else
{
lean_inc(v_a_3598_);
lean_dec(v___x_3581_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3605_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
lean_object* v___x_3603_; 
if (v_isShared_3601_ == 0)
{
v___x_3603_ = v___x_3600_;
goto v_reusejp_3602_;
}
else
{
lean_object* v_reuseFailAlloc_3604_; 
v_reuseFailAlloc_3604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3604_, 0, v_a_3598_);
v___x_3603_ = v_reuseFailAlloc_3604_;
goto v_reusejp_3602_;
}
v_reusejp_3602_:
{
return v___x_3603_;
}
}
}
}
v___jp_3606_:
{
lean_object* v___x_3607_; lean_object* v___x_3608_; 
v___x_3607_ = lean_box(0);
v___x_3608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3608_, 0, v___x_3607_);
return v___x_3608_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___boxed(lean_object* v_e_3663_, lean_object* v_eqTrue_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_){
_start:
{
uint8_t v_eqTrue_boxed_3676_; lean_object* v_res_3677_; 
v_eqTrue_boxed_3676_ = lean_unbox(v_eqTrue_3664_);
v_res_3677_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe(v_e_3663_, v_eqTrue_boxed_3676_, v_a_3665_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_);
lean_dec(v_a_3674_);
lean_dec_ref(v_a_3673_);
lean_dec(v_a_3672_);
lean_dec_ref(v_a_3671_);
lean_dec(v_a_3670_);
lean_dec_ref(v_a_3669_);
lean_dec(v_a_3668_);
lean_dec_ref(v_a_3667_);
lean_dec(v_a_3666_);
lean_dec(v_a_3665_);
return v_res_3677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe(lean_object* v_e_3683_, uint8_t v_eqTrue_3684_, lean_object* v_a_3685_, lean_object* v_a_3686_, lean_object* v_a_3687_, lean_object* v_a_3688_, lean_object* v_a_3689_, lean_object* v_a_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_){
_start:
{
lean_object* v___x_3699_; 
v___x_3699_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3687_);
if (lean_obj_tag(v___x_3699_) == 0)
{
lean_object* v_a_3700_; lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3731_; 
v_a_3700_ = lean_ctor_get(v___x_3699_, 0);
v_isSharedCheck_3731_ = !lean_is_exclusive(v___x_3699_);
if (v_isSharedCheck_3731_ == 0)
{
v___x_3702_ = v___x_3699_;
v_isShared_3703_ = v_isSharedCheck_3731_;
goto v_resetjp_3701_;
}
else
{
lean_inc(v_a_3700_);
lean_dec(v___x_3699_);
v___x_3702_ = lean_box(0);
v_isShared_3703_ = v_isSharedCheck_3731_;
goto v_resetjp_3701_;
}
v_resetjp_3701_:
{
uint8_t v_lia_3704_; 
v_lia_3704_ = lean_ctor_get_uint8(v_a_3700_, sizeof(void*)*17 + 24);
lean_dec(v_a_3700_);
if (v_lia_3704_ == 0)
{
lean_object* v___x_3705_; lean_object* v___x_3707_; 
lean_dec_ref(v_e_3683_);
v___x_3705_ = lean_box(0);
if (v_isShared_3703_ == 0)
{
lean_ctor_set(v___x_3702_, 0, v___x_3705_);
v___x_3707_ = v___x_3702_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v___x_3705_);
v___x_3707_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
return v___x_3707_;
}
}
else
{
lean_object* v___x_3709_; uint8_t v___x_3710_; 
lean_inc_ref(v_e_3683_);
v___x_3709_ = l_Lean_Expr_cleanupAnnotations(v_e_3683_);
v___x_3710_ = l_Lean_Expr_isApp(v___x_3709_);
if (v___x_3710_ == 0)
{
lean_dec_ref(v___x_3709_);
lean_del_object(v___x_3702_);
lean_dec_ref(v_e_3683_);
goto v___jp_3696_;
}
else
{
lean_object* v___x_3711_; uint8_t v___x_3712_; 
v___x_3711_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3709_);
v___x_3712_ = l_Lean_Expr_isApp(v___x_3711_);
if (v___x_3712_ == 0)
{
lean_dec_ref(v___x_3711_);
lean_del_object(v___x_3702_);
lean_dec_ref(v_e_3683_);
goto v___jp_3696_;
}
else
{
lean_object* v___x_3713_; uint8_t v___x_3714_; 
v___x_3713_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3711_);
v___x_3714_ = l_Lean_Expr_isApp(v___x_3713_);
if (v___x_3714_ == 0)
{
lean_dec_ref(v___x_3713_);
lean_del_object(v___x_3702_);
lean_dec_ref(v_e_3683_);
goto v___jp_3696_;
}
else
{
lean_object* v___x_3715_; uint8_t v___x_3716_; 
v___x_3715_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3713_);
v___x_3716_ = l_Lean_Expr_isApp(v___x_3715_);
if (v___x_3716_ == 0)
{
lean_dec_ref(v___x_3715_);
lean_del_object(v___x_3702_);
lean_dec_ref(v_e_3683_);
goto v___jp_3696_;
}
else
{
lean_object* v_arg_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; uint8_t v___x_3720_; 
v_arg_3717_ = lean_ctor_get(v___x_3715_, 1);
lean_inc_ref(v_arg_3717_);
v___x_3718_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3715_);
v___x_3719_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__8));
v___x_3720_ = l_Lean_Expr_isConstOf(v___x_3718_, v___x_3719_);
lean_dec_ref(v___x_3718_);
if (v___x_3720_ == 0)
{
lean_dec_ref(v_arg_3717_);
lean_del_object(v___x_3702_);
lean_dec_ref(v_e_3683_);
goto v___jp_3696_;
}
else
{
lean_object* v___x_3721_; uint8_t v___x_3722_; 
v___x_3721_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__0));
v___x_3722_ = l_Lean_Expr_isConstOf(v_arg_3717_, v___x_3721_);
if (v___x_3722_ == 0)
{
lean_object* v___x_3723_; uint8_t v___x_3724_; 
v___x_3723_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__2));
v___x_3724_ = l_Lean_Expr_isConstOf(v_arg_3717_, v___x_3723_);
lean_dec_ref(v_arg_3717_);
if (v___x_3724_ == 0)
{
lean_object* v___x_3725_; lean_object* v___x_3727_; 
lean_dec_ref(v_e_3683_);
v___x_3725_ = lean_box(0);
if (v_isShared_3703_ == 0)
{
lean_ctor_set(v___x_3702_, 0, v___x_3725_);
v___x_3727_ = v___x_3702_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v___x_3725_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
else
{
lean_object* v___x_3729_; 
lean_del_object(v___x_3702_);
v___x_3729_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe(v_e_3683_, v_eqTrue_3684_, v_a_3685_, v_a_3686_, v_a_3687_, v_a_3688_, v_a_3689_, v_a_3690_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_);
return v___x_3729_;
}
}
else
{
lean_object* v___x_3730_; 
lean_dec_ref(v_arg_3717_);
lean_del_object(v___x_3702_);
v___x_3730_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe(v_e_3683_, v_eqTrue_3684_, v_a_3685_, v_a_3686_, v_a_3687_, v_a_3688_, v_a_3689_, v_a_3690_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_);
return v___x_3730_;
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
lean_object* v_a_3732_; lean_object* v___x_3734_; uint8_t v_isShared_3735_; uint8_t v_isSharedCheck_3739_; 
lean_dec_ref(v_e_3683_);
v_a_3732_ = lean_ctor_get(v___x_3699_, 0);
v_isSharedCheck_3739_ = !lean_is_exclusive(v___x_3699_);
if (v_isSharedCheck_3739_ == 0)
{
v___x_3734_ = v___x_3699_;
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
else
{
lean_inc(v_a_3732_);
lean_dec(v___x_3699_);
v___x_3734_ = lean_box(0);
v_isShared_3735_ = v_isSharedCheck_3739_;
goto v_resetjp_3733_;
}
v_resetjp_3733_:
{
lean_object* v___x_3737_; 
if (v_isShared_3735_ == 0)
{
v___x_3737_ = v___x_3734_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v_a_3732_);
v___x_3737_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
return v___x_3737_;
}
}
}
v___jp_3696_:
{
lean_object* v___x_3697_; lean_object* v___x_3698_; 
v___x_3697_ = lean_box(0);
v___x_3698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3698_, 0, v___x_3697_);
return v___x_3698_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___boxed(lean_object* v_e_3740_, lean_object* v_eqTrue_3741_, lean_object* v_a_3742_, lean_object* v_a_3743_, lean_object* v_a_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_, lean_object* v_a_3752_){
_start:
{
uint8_t v_eqTrue_boxed_3753_; lean_object* v_res_3754_; 
v_eqTrue_boxed_3753_ = lean_unbox(v_eqTrue_3741_);
v_res_3754_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLe(v_e_3740_, v_eqTrue_boxed_3753_, v_a_3742_, v_a_3743_, v_a_3744_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_);
lean_dec(v_a_3751_);
lean_dec_ref(v_a_3750_);
lean_dec(v_a_3749_);
lean_dec_ref(v_a_3748_);
lean_dec(v_a_3747_);
lean_dec_ref(v_a_3746_);
lean_dec(v_a_3745_);
lean_dec_ref(v_a_3744_);
lean_dec(v_a_3743_);
lean_dec(v_a_3742_);
return v_res_3754_;
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
