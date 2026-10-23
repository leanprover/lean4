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
lean_object* v_p_322_; lean_object* v_toCold_323_; lean_object* v_currRecDepth_324_; lean_object* v_ref_325_; uint16_t v_optionFlags_326_; uint8_t v_suppressElabErrors_327_; uint8_t v_checkDeprecated_328_; uint8_t v_isRecordingDeps_329_; lean_object* v_maxRecDepth_361_; lean_object* v___x_362_; uint8_t v___x_363_; 
v_p_322_ = lean_ctor_get(v_c_310_, 0);
v_toCold_323_ = lean_ctor_get(v_a_319_, 0);
lean_inc_ref(v_toCold_323_);
v_currRecDepth_324_ = lean_ctor_get(v_a_319_, 1);
lean_inc(v_currRecDepth_324_);
v_ref_325_ = lean_ctor_get(v_a_319_, 2);
lean_inc(v_ref_325_);
v_optionFlags_326_ = lean_ctor_get_uint16(v_a_319_, sizeof(void*)*3);
v_suppressElabErrors_327_ = lean_ctor_get_uint8(v_a_319_, sizeof(void*)*3 + 2);
v_checkDeprecated_328_ = lean_ctor_get_uint8(v_a_319_, sizeof(void*)*3 + 3);
v_isRecordingDeps_329_ = lean_ctor_get_uint8(v_a_319_, sizeof(void*)*3 + 4);
lean_dec_ref(v_a_319_);
v_maxRecDepth_361_ = lean_ctor_get(v_toCold_323_, 3);
v___x_362_ = lean_unsigned_to_nat(0u);
v___x_363_ = lean_nat_dec_eq(v_maxRecDepth_361_, v___x_362_);
if (v___x_363_ == 0)
{
uint8_t v___x_364_; 
v___x_364_ = lean_nat_dec_eq(v_currRecDepth_324_, v_maxRecDepth_361_);
if (v___x_364_ == 0)
{
goto v___jp_330_;
}
else
{
lean_object* v___x_365_; 
lean_dec(v_currRecDepth_324_);
lean_dec_ref(v_toCold_323_);
lean_dec_ref(v_c_310_);
v___x_365_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts_spec__0___redArg(v_ref_325_);
return v___x_365_;
}
}
else
{
goto v___jp_330_;
}
v___jp_330_:
{
lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; 
v___x_331_ = lean_unsigned_to_nat(1u);
v___x_332_ = lean_nat_add(v_currRecDepth_324_, v___x_331_);
lean_dec(v_currRecDepth_324_);
v___x_333_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_333_, 0, v_toCold_323_);
lean_ctor_set(v___x_333_, 1, v___x_332_);
lean_ctor_set(v___x_333_, 2, v_ref_325_);
lean_ctor_set_uint16(v___x_333_, sizeof(void*)*3, v_optionFlags_326_);
lean_ctor_set_uint8(v___x_333_, sizeof(void*)*3 + 2, v_suppressElabErrors_327_);
lean_ctor_set_uint8(v___x_333_, sizeof(void*)*3 + 3, v_checkDeprecated_328_);
lean_ctor_set_uint8(v___x_333_, sizeof(void*)*3 + 4, v_isRecordingDeps_329_);
lean_inc_ref(v_p_322_);
v___x_334_ = l_Int_Internal_Linear_Poly_findVarToSubst___redArg(v_p_322_, v_a_311_, v___x_333_);
if (lean_obj_tag(v___x_334_) == 0)
{
lean_object* v_a_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_352_; 
v_a_335_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_352_ == 0)
{
v___x_337_ = v___x_334_;
v_isShared_338_ = v_isSharedCheck_352_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_a_335_);
lean_dec(v___x_334_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_352_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
if (lean_obj_tag(v_a_335_) == 1)
{
lean_object* v_val_339_; lean_object* v_snd_340_; lean_object* v_snd_341_; lean_object* v_fst_342_; lean_object* v_fst_343_; lean_object* v_p_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
lean_del_object(v___x_337_);
v_val_339_ = lean_ctor_get(v_a_335_, 0);
lean_inc(v_val_339_);
lean_dec_ref_known(v_a_335_, 1);
v_snd_340_ = lean_ctor_get(v_val_339_, 1);
lean_inc(v_snd_340_);
v_snd_341_ = lean_ctor_get(v_snd_340_, 1);
lean_inc(v_snd_341_);
v_fst_342_ = lean_ctor_get(v_val_339_, 0);
lean_inc(v_fst_342_);
lean_dec(v_val_339_);
v_fst_343_ = lean_ctor_get(v_snd_340_, 0);
lean_inc(v_fst_343_);
lean_dec(v_snd_340_);
v_p_344_ = lean_ctor_get(v_snd_341_, 0);
v___x_345_ = l_Int_Internal_Linear_Poly_coeff(v_p_344_, v_fst_343_);
v___x_346_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq(v___x_345_, v_fst_343_, v_snd_341_, v_fst_342_, v_c_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, v_a_318_, v___x_333_, v_a_320_);
lean_dec(v_fst_342_);
lean_dec(v___x_345_);
if (lean_obj_tag(v___x_346_) == 0)
{
lean_object* v_a_347_; 
v_a_347_ = lean_ctor_get(v___x_346_, 0);
lean_inc(v_a_347_);
lean_dec_ref_known(v___x_346_, 1);
v_c_310_ = v_a_347_;
v_a_319_ = v___x_333_;
goto _start;
}
else
{
lean_dec_ref_known(v___x_333_, 3);
return v___x_346_;
}
}
else
{
lean_object* v___x_350_; 
lean_dec(v_a_335_);
lean_dec_ref_known(v___x_333_, 3);
if (v_isShared_338_ == 0)
{
lean_ctor_set(v___x_337_, 0, v_c_310_);
v___x_350_ = v___x_337_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_c_310_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
else
{
lean_object* v_a_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_360_; 
lean_dec_ref_known(v___x_333_, 3);
lean_dec_ref(v_c_310_);
v_a_353_ = lean_ctor_get(v___x_334_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_334_);
if (v_isSharedCheck_360_ == 0)
{
v___x_355_ = v___x_334_;
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_a_353_);
lean_dec(v___x_334_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_358_; 
if (v_isShared_356_ == 0)
{
v___x_358_ = v___x_355_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_a_353_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
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
LEAN_EXPORT uint8_t l_Int_Internal_Linear_Poly_isNegEq(lean_object* v_p_u2081_379_, lean_object* v_p_u2082_380_){
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
lean_object* v_k_386_; lean_object* v_v_387_; lean_object* v_p_388_; lean_object* v_k_389_; lean_object* v_v_390_; lean_object* v_p_391_; lean_object* v___x_392_; uint8_t v___x_393_; 
v_k_386_ = lean_ctor_get(v_p_u2081_379_, 0);
v_v_387_ = lean_ctor_get(v_p_u2081_379_, 1);
v_p_388_ = lean_ctor_get(v_p_u2081_379_, 2);
v_k_389_ = lean_ctor_get(v_p_u2082_380_, 0);
v_v_390_ = lean_ctor_get(v_p_u2082_380_, 1);
v_p_391_ = lean_ctor_get(v_p_u2082_380_, 2);
v___x_392_ = lean_int_neg(v_k_389_);
v___x_393_ = lean_int_dec_eq(v_k_386_, v___x_392_);
lean_dec(v___x_392_);
if (v___x_393_ == 0)
{
return v___x_393_;
}
else
{
uint8_t v___x_394_; 
v___x_394_ = lean_nat_dec_eq(v_v_387_, v_v_390_);
if (v___x_394_ == 0)
{
return v___x_394_;
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
uint8_t v___x_396_; 
v___x_396_ = 0;
return v___x_396_;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Internal_Linear_Poly_isNegEq___boxed(lean_object* v_p_u2081_397_, lean_object* v_p_u2082_398_){
_start:
{
uint8_t v_res_399_; lean_object* v_r_400_; 
v_res_399_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_u2081_397_, v_p_u2082_398_);
lean_dec_ref(v_p_u2082_398_);
lean_dec_ref(v_p_u2081_397_);
v_r_400_ = lean_box(v_res_399_);
return v_r_400_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(lean_object* v_c_401_, lean_object* v_as_402_, size_t v_i_403_, size_t v_stop_404_, lean_object* v_b_405_){
_start:
{
lean_object* v___y_407_; uint8_t v___x_411_; 
v___x_411_ = lean_usize_dec_eq(v_i_403_, v_stop_404_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; lean_object* v_p_413_; lean_object* v_p_414_; uint8_t v___x_415_; 
v___x_412_ = lean_array_uget_borrowed(v_as_402_, v_i_403_);
v_p_413_ = lean_ctor_get(v___x_412_, 0);
v_p_414_ = lean_ctor_get(v_c_401_, 0);
v___x_415_ = l_Int_Internal_Linear_instBEqPoly_beq(v_p_413_, v_p_414_);
if (v___x_415_ == 0)
{
lean_object* v___x_416_; 
lean_inc(v___x_412_);
v___x_416_ = l_Lean_PersistentArray_push___redArg(v_b_405_, v___x_412_);
v___y_407_ = v___x_416_;
goto v___jp_406_;
}
else
{
v___y_407_ = v_b_405_;
goto v___jp_406_;
}
}
else
{
return v_b_405_;
}
v___jp_406_:
{
size_t v___x_408_; size_t v___x_409_; 
v___x_408_ = ((size_t)1ULL);
v___x_409_ = lean_usize_add(v_i_403_, v___x_408_);
v_i_403_ = v___x_409_;
v_b_405_ = v___y_407_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1___boxed(lean_object* v_c_417_, lean_object* v_as_418_, lean_object* v_i_419_, lean_object* v_stop_420_, lean_object* v_b_421_){
_start:
{
size_t v_i_boxed_422_; size_t v_stop_boxed_423_; lean_object* v_res_424_; 
v_i_boxed_422_ = lean_unbox_usize(v_i_419_);
lean_dec(v_i_419_);
v_stop_boxed_423_ = lean_unbox_usize(v_stop_420_);
lean_dec(v_stop_420_);
v_res_424_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v_c_417_, v_as_418_, v_i_boxed_422_, v_stop_boxed_423_, v_b_421_);
lean_dec_ref(v_as_418_);
lean_dec_ref(v_c_417_);
return v_res_424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2(lean_object* v_c_425_, lean_object* v_x_426_, lean_object* v_x_427_){
_start:
{
if (lean_obj_tag(v_x_426_) == 0)
{
lean_object* v_cs_428_; lean_object* v___x_429_; lean_object* v___x_430_; uint8_t v___x_431_; 
v_cs_428_ = lean_ctor_get(v_x_426_, 0);
v___x_429_ = lean_unsigned_to_nat(0u);
v___x_430_ = lean_array_get_size(v_cs_428_);
v___x_431_ = lean_nat_dec_lt(v___x_429_, v___x_430_);
if (v___x_431_ == 0)
{
return v_x_427_;
}
else
{
size_t v___x_432_; size_t v___x_433_; lean_object* v___x_434_; 
v___x_432_ = ((size_t)0ULL);
v___x_433_ = lean_usize_of_nat(v___x_430_);
v___x_434_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v_c_425_, v_cs_428_, v___x_432_, v___x_433_, v_x_427_);
return v___x_434_;
}
}
else
{
lean_object* v_vs_435_; lean_object* v___x_436_; lean_object* v___x_437_; uint8_t v___x_438_; 
v_vs_435_ = lean_ctor_get(v_x_426_, 0);
v___x_436_ = lean_unsigned_to_nat(0u);
v___x_437_ = lean_array_get_size(v_vs_435_);
v___x_438_ = lean_nat_dec_lt(v___x_436_, v___x_437_);
if (v___x_438_ == 0)
{
return v_x_427_;
}
else
{
size_t v___x_439_; size_t v___x_440_; lean_object* v___x_441_; 
v___x_439_ = ((size_t)0ULL);
v___x_440_ = lean_usize_of_nat(v___x_437_);
v___x_441_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v_c_425_, v_vs_435_, v___x_439_, v___x_440_, v_x_427_);
return v___x_441_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(lean_object* v_c_442_, lean_object* v_as_443_, size_t v_i_444_, size_t v_stop_445_, lean_object* v_b_446_){
_start:
{
uint8_t v___x_447_; 
v___x_447_ = lean_usize_dec_eq(v_i_444_, v_stop_445_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; lean_object* v___x_449_; size_t v___x_450_; size_t v___x_451_; 
v___x_448_ = lean_array_uget_borrowed(v_as_443_, v_i_444_);
v___x_449_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2(v_c_442_, v___x_448_, v_b_446_);
v___x_450_ = ((size_t)1ULL);
v___x_451_ = lean_usize_add(v_i_444_, v___x_450_);
v_i_444_ = v___x_451_;
v_b_446_ = v___x_449_;
goto _start;
}
else
{
return v_b_446_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1___boxed(lean_object* v_c_453_, lean_object* v_as_454_, lean_object* v_i_455_, lean_object* v_stop_456_, lean_object* v_b_457_){
_start:
{
size_t v_i_boxed_458_; size_t v_stop_boxed_459_; lean_object* v_res_460_; 
v_i_boxed_458_ = lean_unbox_usize(v_i_455_);
lean_dec(v_i_455_);
v_stop_boxed_459_ = lean_unbox_usize(v_stop_456_);
lean_dec(v_stop_456_);
v_res_460_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v_c_453_, v_as_454_, v_i_boxed_458_, v_stop_boxed_459_, v_b_457_);
lean_dec_ref(v_as_454_);
lean_dec_ref(v_c_453_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2___boxed(lean_object* v_c_461_, lean_object* v_x_462_, lean_object* v_x_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2(v_c_461_, v_x_462_, v_x_463_);
lean_dec_ref(v_x_462_);
lean_dec_ref(v_c_461_);
return v_res_464_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0(void){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(lean_object* v_c_466_, lean_object* v_x_467_, size_t v_x_468_, size_t v_x_469_, lean_object* v_x_470_){
_start:
{
if (lean_obj_tag(v_x_467_) == 0)
{
lean_object* v_cs_471_; lean_object* v___x_472_; size_t v___x_473_; lean_object* v_j_474_; lean_object* v___x_475_; size_t v___x_476_; size_t v___x_477_; size_t v___x_478_; size_t v___x_479_; size_t v___x_480_; size_t v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; lean_object* v___x_484_; lean_object* v___x_485_; uint8_t v___x_486_; 
v_cs_471_ = lean_ctor_get(v_x_467_, 0);
v___x_472_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0);
v___x_473_ = lean_usize_shift_right(v_x_468_, v_x_469_);
v_j_474_ = lean_usize_to_nat(v___x_473_);
v___x_475_ = lean_array_get_borrowed(v___x_472_, v_cs_471_, v_j_474_);
v___x_476_ = ((size_t)1ULL);
v___x_477_ = lean_usize_shift_left(v___x_476_, v_x_469_);
v___x_478_ = lean_usize_sub(v___x_477_, v___x_476_);
v___x_479_ = lean_usize_land(v_x_468_, v___x_478_);
v___x_480_ = ((size_t)5ULL);
v___x_481_ = lean_usize_sub(v_x_469_, v___x_480_);
v___x_482_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(v_c_466_, v___x_475_, v___x_479_, v___x_481_, v_x_470_);
v___x_483_ = lean_unsigned_to_nat(1u);
v___x_484_ = lean_nat_add(v_j_474_, v___x_483_);
lean_dec(v_j_474_);
v___x_485_ = lean_array_get_size(v_cs_471_);
v___x_486_ = lean_nat_dec_lt(v___x_484_, v___x_485_);
if (v___x_486_ == 0)
{
lean_dec(v___x_484_);
return v___x_482_;
}
else
{
size_t v___x_487_; size_t v___x_488_; lean_object* v___x_489_; 
v___x_487_ = lean_usize_of_nat(v___x_484_);
lean_dec(v___x_484_);
v___x_488_ = lean_usize_of_nat(v___x_485_);
v___x_489_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0_spec__1(v_c_466_, v_cs_471_, v___x_487_, v___x_488_, v___x_482_);
return v___x_489_;
}
}
else
{
lean_object* v_vs_490_; lean_object* v___x_491_; lean_object* v___x_492_; uint8_t v___x_493_; 
v_vs_490_ = lean_ctor_get(v_x_467_, 0);
v___x_491_ = lean_usize_to_nat(v_x_468_);
v___x_492_ = lean_array_get_size(v_vs_490_);
v___x_493_ = lean_nat_dec_lt(v___x_491_, v___x_492_);
if (v___x_493_ == 0)
{
lean_dec(v___x_491_);
return v_x_470_;
}
else
{
size_t v___x_494_; size_t v___x_495_; lean_object* v___x_496_; 
v___x_494_ = lean_usize_of_nat(v___x_491_);
lean_dec(v___x_491_);
v___x_495_ = lean_usize_of_nat(v___x_492_);
v___x_496_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v_c_466_, v_vs_490_, v___x_494_, v___x_495_, v_x_470_);
return v___x_496_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___boxed(lean_object* v_c_497_, lean_object* v_x_498_, lean_object* v_x_499_, lean_object* v_x_500_, lean_object* v_x_501_){
_start:
{
size_t v_x_1573__boxed_502_; size_t v_x_1574__boxed_503_; lean_object* v_res_504_; 
v_x_1573__boxed_502_ = lean_unbox_usize(v_x_499_);
lean_dec(v_x_499_);
v_x_1574__boxed_503_ = lean_unbox_usize(v_x_500_);
lean_dec(v_x_500_);
v_res_504_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(v_c_497_, v_x_498_, v_x_1573__boxed_502_, v_x_1574__boxed_503_, v_x_501_);
lean_dec_ref(v_x_498_);
lean_dec_ref(v_c_497_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(lean_object* v_c_505_, lean_object* v_t_506_, lean_object* v_init_507_, lean_object* v_start_508_){
_start:
{
lean_object* v___x_509_; uint8_t v___x_510_; 
v___x_509_ = lean_unsigned_to_nat(0u);
v___x_510_ = lean_nat_dec_eq(v_start_508_, v___x_509_);
if (v___x_510_ == 0)
{
lean_object* v_root_511_; lean_object* v_tail_512_; size_t v_shift_513_; lean_object* v_tailOff_514_; uint8_t v___x_515_; 
v_root_511_ = lean_ctor_get(v_t_506_, 0);
v_tail_512_ = lean_ctor_get(v_t_506_, 1);
v_shift_513_ = lean_ctor_get_usize(v_t_506_, 4);
v_tailOff_514_ = lean_ctor_get(v_t_506_, 3);
v___x_515_ = lean_nat_dec_le(v_tailOff_514_, v_start_508_);
if (v___x_515_ == 0)
{
size_t v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; uint8_t v___x_519_; 
v___x_516_ = lean_usize_of_nat(v_start_508_);
v___x_517_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0(v_c_505_, v_root_511_, v___x_516_, v_shift_513_, v_init_507_);
v___x_518_ = lean_array_get_size(v_tail_512_);
v___x_519_ = lean_nat_dec_lt(v___x_509_, v___x_518_);
if (v___x_519_ == 0)
{
return v___x_517_;
}
else
{
size_t v___x_520_; size_t v___x_521_; lean_object* v___x_522_; 
v___x_520_ = ((size_t)0ULL);
v___x_521_ = lean_usize_of_nat(v___x_518_);
v___x_522_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v_c_505_, v_tail_512_, v___x_520_, v___x_521_, v___x_517_);
return v___x_522_;
}
}
else
{
lean_object* v___x_523_; lean_object* v___x_524_; uint8_t v___x_525_; 
v___x_523_ = lean_nat_sub(v_start_508_, v_tailOff_514_);
v___x_524_ = lean_array_get_size(v_tail_512_);
v___x_525_ = lean_nat_dec_lt(v___x_523_, v___x_524_);
if (v___x_525_ == 0)
{
lean_dec(v___x_523_);
return v_init_507_;
}
else
{
size_t v___x_526_; size_t v___x_527_; lean_object* v___x_528_; 
v___x_526_ = lean_usize_of_nat(v___x_523_);
lean_dec(v___x_523_);
v___x_527_ = lean_usize_of_nat(v___x_524_);
v___x_528_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v_c_505_, v_tail_512_, v___x_526_, v___x_527_, v_init_507_);
return v___x_528_;
}
}
}
else
{
lean_object* v_root_529_; lean_object* v_tail_530_; lean_object* v___x_531_; lean_object* v___x_532_; uint8_t v___x_533_; 
v_root_529_ = lean_ctor_get(v_t_506_, 0);
v_tail_530_ = lean_ctor_get(v_t_506_, 1);
v___x_531_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__2(v_c_505_, v_root_529_, v_init_507_);
v___x_532_ = lean_array_get_size(v_tail_530_);
v___x_533_ = lean_nat_dec_lt(v___x_509_, v___x_532_);
if (v___x_533_ == 0)
{
return v___x_531_;
}
else
{
size_t v___x_534_; size_t v___x_535_; lean_object* v___x_536_; 
v___x_534_ = ((size_t)0ULL);
v___x_535_ = lean_usize_of_nat(v___x_532_);
v___x_536_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__1(v_c_505_, v_tail_530_, v___x_534_, v___x_535_, v___x_531_);
return v___x_536_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0___boxed(lean_object* v_c_537_, lean_object* v_t_538_, lean_object* v_init_539_, lean_object* v_start_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(v_c_537_, v_t_538_, v_init_539_, v_start_540_);
lean_dec(v_start_540_);
lean_dec_ref(v_t_538_);
lean_dec_ref(v_c_537_);
return v_res_541_;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_542_ = lean_unsigned_to_nat(32u);
v___x_543_ = lean_mk_empty_array_with_capacity(v___x_542_);
v___x_544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_544_, 0, v___x_543_);
return v___x_544_;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1(void){
_start:
{
size_t v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
v___x_545_ = ((size_t)5ULL);
v___x_546_ = lean_unsigned_to_nat(0u);
v___x_547_ = lean_unsigned_to_nat(32u);
v___x_548_ = lean_mk_empty_array_with_capacity(v___x_547_);
v___x_549_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__0, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__0_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__0);
v___x_550_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_550_, 0, v___x_549_);
lean_ctor_set(v___x_550_, 1, v___x_548_);
lean_ctor_set(v___x_550_, 2, v___x_546_);
lean_ctor_set(v___x_550_, 3, v___x_546_);
lean_ctor_set_usize(v___x_550_, 4, v___x_545_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4(lean_object* v_c_551_, lean_object* v_x_552_, size_t v_x_553_, size_t v_x_554_){
_start:
{
if (lean_obj_tag(v_x_552_) == 0)
{
lean_object* v_cs_555_; size_t v_j_556_; lean_object* v___x_557_; lean_object* v___x_558_; uint8_t v___x_559_; 
v_cs_555_ = lean_ctor_get(v_x_552_, 0);
v_j_556_ = lean_usize_shift_right(v_x_553_, v_x_554_);
v___x_557_ = lean_usize_to_nat(v_j_556_);
v___x_558_ = lean_array_get_size(v_cs_555_);
v___x_559_ = lean_nat_dec_lt(v___x_557_, v___x_558_);
if (v___x_559_ == 0)
{
lean_dec(v___x_557_);
return v_x_552_;
}
else
{
lean_object* v___x_561_; uint8_t v_isShared_562_; uint8_t v_isSharedCheck_577_; 
lean_inc_ref(v_cs_555_);
v_isSharedCheck_577_ = !lean_is_exclusive(v_x_552_);
if (v_isSharedCheck_577_ == 0)
{
lean_object* v_unused_578_; 
v_unused_578_ = lean_ctor_get(v_x_552_, 0);
lean_dec(v_unused_578_);
v___x_561_ = v_x_552_;
v_isShared_562_ = v_isSharedCheck_577_;
goto v_resetjp_560_;
}
else
{
lean_dec(v_x_552_);
v___x_561_ = lean_box(0);
v_isShared_562_ = v_isSharedCheck_577_;
goto v_resetjp_560_;
}
v_resetjp_560_:
{
size_t v___x_563_; size_t v___x_564_; size_t v___x_565_; size_t v_i_566_; size_t v___x_567_; size_t v_shift_568_; lean_object* v_v_569_; lean_object* v___x_570_; lean_object* v_xs_x27_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_575_; 
v___x_563_ = ((size_t)1ULL);
v___x_564_ = lean_usize_shift_left(v___x_563_, v_x_554_);
v___x_565_ = lean_usize_sub(v___x_564_, v___x_563_);
v_i_566_ = lean_usize_land(v_x_553_, v___x_565_);
v___x_567_ = ((size_t)5ULL);
v_shift_568_ = lean_usize_sub(v_x_554_, v___x_567_);
v_v_569_ = lean_array_fget(v_cs_555_, v___x_557_);
v___x_570_ = lean_box(0);
v_xs_x27_571_ = lean_array_fset(v_cs_555_, v___x_557_, v___x_570_);
v___x_572_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4(v_c_551_, v_v_569_, v_i_566_, v_shift_568_);
v___x_573_ = lean_array_fset(v_xs_x27_571_, v___x_557_, v___x_572_);
lean_dec(v___x_557_);
if (v_isShared_562_ == 0)
{
lean_ctor_set(v___x_561_, 0, v___x_573_);
v___x_575_ = v___x_561_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v___x_573_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
}
}
else
{
lean_object* v_vs_579_; lean_object* v___x_580_; lean_object* v___x_581_; uint8_t v___x_582_; 
v_vs_579_ = lean_ctor_get(v_x_552_, 0);
v___x_580_ = lean_usize_to_nat(v_x_553_);
v___x_581_ = lean_array_get_size(v_vs_579_);
v___x_582_ = lean_nat_dec_lt(v___x_580_, v___x_581_);
if (v___x_582_ == 0)
{
lean_dec(v___x_580_);
return v_x_552_;
}
else
{
lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_596_; 
lean_inc_ref(v_vs_579_);
v_isSharedCheck_596_ = !lean_is_exclusive(v_x_552_);
if (v_isSharedCheck_596_ == 0)
{
lean_object* v_unused_597_; 
v_unused_597_ = lean_ctor_get(v_x_552_, 0);
lean_dec(v_unused_597_);
v___x_584_ = v_x_552_;
v_isShared_585_ = v_isSharedCheck_596_;
goto v_resetjp_583_;
}
else
{
lean_dec(v_x_552_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_596_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v_v_586_; lean_object* v___x_587_; lean_object* v_xs_x27_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_594_; 
v_v_586_ = lean_array_fget(v_vs_579_, v___x_580_);
v___x_587_ = lean_box(0);
v_xs_x27_588_ = lean_array_fset(v_vs_579_, v___x_580_, v___x_587_);
v___x_589_ = lean_unsigned_to_nat(0u);
v___x_590_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1);
v___x_591_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(v_c_551_, v_v_586_, v___x_590_, v___x_589_);
lean_dec(v_v_586_);
v___x_592_ = lean_array_fset(v_xs_x27_588_, v___x_580_, v___x_591_);
lean_dec(v___x_580_);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 0, v___x_592_);
v___x_594_ = v___x_584_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_592_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___boxed(lean_object* v_c_598_, lean_object* v_x_599_, lean_object* v_x_600_, lean_object* v_x_601_){
_start:
{
size_t v_x_1700__boxed_602_; size_t v_x_1701__boxed_603_; lean_object* v_res_604_; 
v_x_1700__boxed_602_ = lean_unbox_usize(v_x_600_);
lean_dec(v_x_600_);
v_x_1701__boxed_603_ = lean_unbox_usize(v_x_601_);
lean_dec(v_x_601_);
v_res_604_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4(v_c_598_, v_x_599_, v_x_1700__boxed_602_, v_x_1701__boxed_603_);
lean_dec_ref(v_c_598_);
return v_res_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(lean_object* v_c_605_, lean_object* v_t_606_, lean_object* v_i_607_){
_start:
{
lean_object* v_root_608_; lean_object* v_tail_609_; lean_object* v_size_610_; size_t v_shift_611_; lean_object* v_tailOff_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_640_; 
v_root_608_ = lean_ctor_get(v_t_606_, 0);
v_tail_609_ = lean_ctor_get(v_t_606_, 1);
v_size_610_ = lean_ctor_get(v_t_606_, 2);
v_shift_611_ = lean_ctor_get_usize(v_t_606_, 4);
v_tailOff_612_ = lean_ctor_get(v_t_606_, 3);
v_isSharedCheck_640_ = !lean_is_exclusive(v_t_606_);
if (v_isSharedCheck_640_ == 0)
{
v___x_614_ = v_t_606_;
v_isShared_615_ = v_isSharedCheck_640_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_tailOff_612_);
lean_inc(v_size_610_);
lean_inc(v_tail_609_);
lean_inc(v_root_608_);
lean_dec(v_t_606_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_640_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
uint8_t v___x_616_; 
v___x_616_ = lean_nat_dec_le(v_tailOff_612_, v_i_607_);
if (v___x_616_ == 0)
{
size_t v___x_617_; lean_object* v___x_618_; lean_object* v___x_620_; 
v___x_617_ = lean_usize_of_nat(v_i_607_);
v___x_618_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4(v_c_605_, v_root_608_, v___x_617_, v_shift_611_);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 0, v___x_618_);
v___x_620_ = v___x_614_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_618_);
lean_ctor_set(v_reuseFailAlloc_621_, 1, v_tail_609_);
lean_ctor_set(v_reuseFailAlloc_621_, 2, v_size_610_);
lean_ctor_set(v_reuseFailAlloc_621_, 3, v_tailOff_612_);
lean_ctor_set_usize(v_reuseFailAlloc_621_, 4, v_shift_611_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
else
{
lean_object* v___x_622_; lean_object* v___x_623_; uint8_t v___x_624_; 
v___x_622_ = lean_nat_sub(v_i_607_, v_tailOff_612_);
v___x_623_ = lean_array_get_size(v_tail_609_);
v___x_624_ = lean_nat_dec_lt(v___x_622_, v___x_623_);
if (v___x_624_ == 0)
{
lean_object* v___x_626_; 
lean_dec(v___x_622_);
if (v_isShared_615_ == 0)
{
v___x_626_ = v___x_614_;
goto v_reusejp_625_;
}
else
{
lean_object* v_reuseFailAlloc_627_; 
v_reuseFailAlloc_627_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_627_, 0, v_root_608_);
lean_ctor_set(v_reuseFailAlloc_627_, 1, v_tail_609_);
lean_ctor_set(v_reuseFailAlloc_627_, 2, v_size_610_);
lean_ctor_set(v_reuseFailAlloc_627_, 3, v_tailOff_612_);
lean_ctor_set_usize(v_reuseFailAlloc_627_, 4, v_shift_611_);
v___x_626_ = v_reuseFailAlloc_627_;
goto v_reusejp_625_;
}
v_reusejp_625_:
{
return v___x_626_;
}
}
else
{
lean_object* v_v_628_; lean_object* v___x_629_; lean_object* v_xs_x27_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_638_; 
v_v_628_ = lean_array_fget(v_tail_609_, v___x_622_);
v___x_629_ = lean_box(0);
v_xs_x27_630_ = lean_array_fset(v_tail_609_, v___x_622_, v___x_629_);
v___x_631_ = lean_unsigned_to_nat(32u);
v___x_632_ = lean_mk_empty_array_with_capacity(v___x_631_);
lean_dec_ref(v___x_632_);
v___x_633_ = lean_unsigned_to_nat(0u);
v___x_634_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1_spec__4___closed__1);
v___x_635_ = l_Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0(v_c_605_, v_v_628_, v___x_634_, v___x_633_);
lean_dec(v_v_628_);
v___x_636_ = lean_array_fset(v_xs_x27_630_, v___x_622_, v___x_635_);
lean_dec(v___x_622_);
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 1, v___x_636_);
v___x_638_ = v___x_614_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v_root_608_);
lean_ctor_set(v_reuseFailAlloc_639_, 1, v___x_636_);
lean_ctor_set(v_reuseFailAlloc_639_, 2, v_size_610_);
lean_ctor_set(v_reuseFailAlloc_639_, 3, v_tailOff_612_);
lean_ctor_set_usize(v_reuseFailAlloc_639_, 4, v_shift_611_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1___boxed(lean_object* v_c_641_, lean_object* v_t_642_, lean_object* v_i_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(v_c_641_, v_t_642_, v_i_643_);
lean_dec(v_i_643_);
lean_dec_ref(v_c_641_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0(lean_object* v_c_645_, lean_object* v_v_646_, lean_object* v_s_647_){
_start:
{
lean_object* v_vars_648_; lean_object* v_varMap_649_; lean_object* v_varsHistory_650_; lean_object* v_natToIntMap_651_; lean_object* v_natDef_652_; lean_object* v_dvds_653_; lean_object* v_lowers_654_; lean_object* v_uppers_655_; lean_object* v_diseqs_656_; lean_object* v_elimEqs_657_; lean_object* v_elimStack_658_; lean_object* v_occurs_659_; lean_object* v_assignment_660_; lean_object* v_nextCnstrId_661_; uint8_t v_caseSplits_662_; lean_object* v_steps_663_; lean_object* v_penalties_664_; lean_object* v_numReorderRequests_665_; lean_object* v_conflict_x3f_666_; lean_object* v_diseqSplits_667_; lean_object* v_divMod_668_; uint8_t v_usedCommRing_669_; lean_object* v_nonlinearOccs_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_678_; 
v_vars_648_ = lean_ctor_get(v_s_647_, 0);
v_varMap_649_ = lean_ctor_get(v_s_647_, 1);
v_varsHistory_650_ = lean_ctor_get(v_s_647_, 2);
v_natToIntMap_651_ = lean_ctor_get(v_s_647_, 3);
v_natDef_652_ = lean_ctor_get(v_s_647_, 4);
v_dvds_653_ = lean_ctor_get(v_s_647_, 5);
v_lowers_654_ = lean_ctor_get(v_s_647_, 6);
v_uppers_655_ = lean_ctor_get(v_s_647_, 7);
v_diseqs_656_ = lean_ctor_get(v_s_647_, 8);
v_elimEqs_657_ = lean_ctor_get(v_s_647_, 9);
v_elimStack_658_ = lean_ctor_get(v_s_647_, 10);
v_occurs_659_ = lean_ctor_get(v_s_647_, 11);
v_assignment_660_ = lean_ctor_get(v_s_647_, 12);
v_nextCnstrId_661_ = lean_ctor_get(v_s_647_, 13);
v_caseSplits_662_ = lean_ctor_get_uint8(v_s_647_, sizeof(void*)*21);
v_steps_663_ = lean_ctor_get(v_s_647_, 14);
v_penalties_664_ = lean_ctor_get(v_s_647_, 15);
v_numReorderRequests_665_ = lean_ctor_get(v_s_647_, 16);
v_conflict_x3f_666_ = lean_ctor_get(v_s_647_, 17);
v_diseqSplits_667_ = lean_ctor_get(v_s_647_, 18);
v_divMod_668_ = lean_ctor_get(v_s_647_, 19);
v_usedCommRing_669_ = lean_ctor_get_uint8(v_s_647_, sizeof(void*)*21 + 1);
v_nonlinearOccs_670_ = lean_ctor_get(v_s_647_, 20);
v_isSharedCheck_678_ = !lean_is_exclusive(v_s_647_);
if (v_isSharedCheck_678_ == 0)
{
v___x_672_ = v_s_647_;
v_isShared_673_ = v_isSharedCheck_678_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_nonlinearOccs_670_);
lean_inc(v_divMod_668_);
lean_inc(v_diseqSplits_667_);
lean_inc(v_conflict_x3f_666_);
lean_inc(v_numReorderRequests_665_);
lean_inc(v_penalties_664_);
lean_inc(v_steps_663_);
lean_inc(v_nextCnstrId_661_);
lean_inc(v_assignment_660_);
lean_inc(v_occurs_659_);
lean_inc(v_elimStack_658_);
lean_inc(v_elimEqs_657_);
lean_inc(v_diseqs_656_);
lean_inc(v_uppers_655_);
lean_inc(v_lowers_654_);
lean_inc(v_dvds_653_);
lean_inc(v_natDef_652_);
lean_inc(v_natToIntMap_651_);
lean_inc(v_varsHistory_650_);
lean_inc(v_varMap_649_);
lean_inc(v_vars_648_);
lean_dec(v_s_647_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_678_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_674_; lean_object* v___x_676_; 
v___x_674_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(v_c_645_, v_uppers_655_, v_v_646_);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 7, v___x_674_);
v___x_676_ = v___x_672_;
goto v_reusejp_675_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(0, 21, 2);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_vars_648_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v_varMap_649_);
lean_ctor_set(v_reuseFailAlloc_677_, 2, v_varsHistory_650_);
lean_ctor_set(v_reuseFailAlloc_677_, 3, v_natToIntMap_651_);
lean_ctor_set(v_reuseFailAlloc_677_, 4, v_natDef_652_);
lean_ctor_set(v_reuseFailAlloc_677_, 5, v_dvds_653_);
lean_ctor_set(v_reuseFailAlloc_677_, 6, v_lowers_654_);
lean_ctor_set(v_reuseFailAlloc_677_, 7, v___x_674_);
lean_ctor_set(v_reuseFailAlloc_677_, 8, v_diseqs_656_);
lean_ctor_set(v_reuseFailAlloc_677_, 9, v_elimEqs_657_);
lean_ctor_set(v_reuseFailAlloc_677_, 10, v_elimStack_658_);
lean_ctor_set(v_reuseFailAlloc_677_, 11, v_occurs_659_);
lean_ctor_set(v_reuseFailAlloc_677_, 12, v_assignment_660_);
lean_ctor_set(v_reuseFailAlloc_677_, 13, v_nextCnstrId_661_);
lean_ctor_set(v_reuseFailAlloc_677_, 14, v_steps_663_);
lean_ctor_set(v_reuseFailAlloc_677_, 15, v_penalties_664_);
lean_ctor_set(v_reuseFailAlloc_677_, 16, v_numReorderRequests_665_);
lean_ctor_set(v_reuseFailAlloc_677_, 17, v_conflict_x3f_666_);
lean_ctor_set(v_reuseFailAlloc_677_, 18, v_diseqSplits_667_);
lean_ctor_set(v_reuseFailAlloc_677_, 19, v_divMod_668_);
lean_ctor_set(v_reuseFailAlloc_677_, 20, v_nonlinearOccs_670_);
lean_ctor_set_uint8(v_reuseFailAlloc_677_, sizeof(void*)*21, v_caseSplits_662_);
lean_ctor_set_uint8(v_reuseFailAlloc_677_, sizeof(void*)*21 + 1, v_usedCommRing_669_);
v___x_676_ = v_reuseFailAlloc_677_;
goto v_reusejp_675_;
}
v_reusejp_675_:
{
return v___x_676_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___boxed(lean_object* v_c_679_, lean_object* v_v_680_, lean_object* v_s_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0(v_c_679_, v_v_680_, v_s_681_);
lean_dec(v_v_680_);
lean_dec_ref(v_c_679_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1(lean_object* v_c_683_, lean_object* v_v_684_, lean_object* v_s_685_){
_start:
{
lean_object* v_vars_686_; lean_object* v_varMap_687_; lean_object* v_varsHistory_688_; lean_object* v_natToIntMap_689_; lean_object* v_natDef_690_; lean_object* v_dvds_691_; lean_object* v_lowers_692_; lean_object* v_uppers_693_; lean_object* v_diseqs_694_; lean_object* v_elimEqs_695_; lean_object* v_elimStack_696_; lean_object* v_occurs_697_; lean_object* v_assignment_698_; lean_object* v_nextCnstrId_699_; uint8_t v_caseSplits_700_; lean_object* v_steps_701_; lean_object* v_penalties_702_; lean_object* v_numReorderRequests_703_; lean_object* v_conflict_x3f_704_; lean_object* v_diseqSplits_705_; lean_object* v_divMod_706_; uint8_t v_usedCommRing_707_; lean_object* v_nonlinearOccs_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_716_; 
v_vars_686_ = lean_ctor_get(v_s_685_, 0);
v_varMap_687_ = lean_ctor_get(v_s_685_, 1);
v_varsHistory_688_ = lean_ctor_get(v_s_685_, 2);
v_natToIntMap_689_ = lean_ctor_get(v_s_685_, 3);
v_natDef_690_ = lean_ctor_get(v_s_685_, 4);
v_dvds_691_ = lean_ctor_get(v_s_685_, 5);
v_lowers_692_ = lean_ctor_get(v_s_685_, 6);
v_uppers_693_ = lean_ctor_get(v_s_685_, 7);
v_diseqs_694_ = lean_ctor_get(v_s_685_, 8);
v_elimEqs_695_ = lean_ctor_get(v_s_685_, 9);
v_elimStack_696_ = lean_ctor_get(v_s_685_, 10);
v_occurs_697_ = lean_ctor_get(v_s_685_, 11);
v_assignment_698_ = lean_ctor_get(v_s_685_, 12);
v_nextCnstrId_699_ = lean_ctor_get(v_s_685_, 13);
v_caseSplits_700_ = lean_ctor_get_uint8(v_s_685_, sizeof(void*)*21);
v_steps_701_ = lean_ctor_get(v_s_685_, 14);
v_penalties_702_ = lean_ctor_get(v_s_685_, 15);
v_numReorderRequests_703_ = lean_ctor_get(v_s_685_, 16);
v_conflict_x3f_704_ = lean_ctor_get(v_s_685_, 17);
v_diseqSplits_705_ = lean_ctor_get(v_s_685_, 18);
v_divMod_706_ = lean_ctor_get(v_s_685_, 19);
v_usedCommRing_707_ = lean_ctor_get_uint8(v_s_685_, sizeof(void*)*21 + 1);
v_nonlinearOccs_708_ = lean_ctor_get(v_s_685_, 20);
v_isSharedCheck_716_ = !lean_is_exclusive(v_s_685_);
if (v_isSharedCheck_716_ == 0)
{
v___x_710_ = v_s_685_;
v_isShared_711_ = v_isSharedCheck_716_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_nonlinearOccs_708_);
lean_inc(v_divMod_706_);
lean_inc(v_diseqSplits_705_);
lean_inc(v_conflict_x3f_704_);
lean_inc(v_numReorderRequests_703_);
lean_inc(v_penalties_702_);
lean_inc(v_steps_701_);
lean_inc(v_nextCnstrId_699_);
lean_inc(v_assignment_698_);
lean_inc(v_occurs_697_);
lean_inc(v_elimStack_696_);
lean_inc(v_elimEqs_695_);
lean_inc(v_diseqs_694_);
lean_inc(v_uppers_693_);
lean_inc(v_lowers_692_);
lean_inc(v_dvds_691_);
lean_inc(v_natDef_690_);
lean_inc(v_natToIntMap_689_);
lean_inc(v_varsHistory_688_);
lean_inc(v_varMap_687_);
lean_inc(v_vars_686_);
lean_dec(v_s_685_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_716_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_712_; lean_object* v___x_714_; 
v___x_712_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__1(v_c_683_, v_lowers_692_, v_v_684_);
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 6, v___x_712_);
v___x_714_ = v___x_710_;
goto v_reusejp_713_;
}
else
{
lean_object* v_reuseFailAlloc_715_; 
v_reuseFailAlloc_715_ = lean_alloc_ctor(0, 21, 2);
lean_ctor_set(v_reuseFailAlloc_715_, 0, v_vars_686_);
lean_ctor_set(v_reuseFailAlloc_715_, 1, v_varMap_687_);
lean_ctor_set(v_reuseFailAlloc_715_, 2, v_varsHistory_688_);
lean_ctor_set(v_reuseFailAlloc_715_, 3, v_natToIntMap_689_);
lean_ctor_set(v_reuseFailAlloc_715_, 4, v_natDef_690_);
lean_ctor_set(v_reuseFailAlloc_715_, 5, v_dvds_691_);
lean_ctor_set(v_reuseFailAlloc_715_, 6, v___x_712_);
lean_ctor_set(v_reuseFailAlloc_715_, 7, v_uppers_693_);
lean_ctor_set(v_reuseFailAlloc_715_, 8, v_diseqs_694_);
lean_ctor_set(v_reuseFailAlloc_715_, 9, v_elimEqs_695_);
lean_ctor_set(v_reuseFailAlloc_715_, 10, v_elimStack_696_);
lean_ctor_set(v_reuseFailAlloc_715_, 11, v_occurs_697_);
lean_ctor_set(v_reuseFailAlloc_715_, 12, v_assignment_698_);
lean_ctor_set(v_reuseFailAlloc_715_, 13, v_nextCnstrId_699_);
lean_ctor_set(v_reuseFailAlloc_715_, 14, v_steps_701_);
lean_ctor_set(v_reuseFailAlloc_715_, 15, v_penalties_702_);
lean_ctor_set(v_reuseFailAlloc_715_, 16, v_numReorderRequests_703_);
lean_ctor_set(v_reuseFailAlloc_715_, 17, v_conflict_x3f_704_);
lean_ctor_set(v_reuseFailAlloc_715_, 18, v_diseqSplits_705_);
lean_ctor_set(v_reuseFailAlloc_715_, 19, v_divMod_706_);
lean_ctor_set(v_reuseFailAlloc_715_, 20, v_nonlinearOccs_708_);
lean_ctor_set_uint8(v_reuseFailAlloc_715_, sizeof(void*)*21, v_caseSplits_700_);
lean_ctor_set_uint8(v_reuseFailAlloc_715_, sizeof(void*)*21 + 1, v_usedCommRing_707_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1___boxed(lean_object* v_c_717_, lean_object* v_v_718_, lean_object* v_s_719_){
_start:
{
lean_object* v_res_720_; 
v_res_720_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1(v_c_717_, v_v_718_, v_s_719_);
lean_dec(v_v_718_);
lean_dec_ref(v_c_717_);
return v_res_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(lean_object* v_c_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_){
_start:
{
lean_object* v_p_728_; 
v_p_728_ = lean_ctor_get(v_c_721_, 0);
if (lean_obj_tag(v_p_728_) == 1)
{
lean_object* v_k_729_; lean_object* v_v_730_; lean_object* v___x_731_; uint8_t v___x_732_; 
v_k_729_ = lean_ctor_get(v_p_728_, 0);
v_v_730_ = lean_ctor_get(v_p_728_, 1);
lean_inc(v_v_730_);
v___x_731_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9);
v___x_732_ = lean_int_dec_lt(v_k_729_, v___x_731_);
if (v___x_732_ == 0)
{
lean_object* v___f_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v___f_733_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_733_, 0, v_c_721_);
lean_closure_set(v___f_733_, 1, v_v_730_);
v___x_734_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_735_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_734_, v___f_733_, v_a_722_);
return v___x_735_;
}
else
{
lean_object* v___f_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v___f_736_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_736_, 0, v_c_721_);
lean_closure_set(v___f_736_, 1, v_v_730_);
v___x_737_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_738_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_737_, v___f_736_, v_a_722_);
return v___x_738_;
}
}
else
{
lean_object* v___x_739_; 
v___x_739_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_);
return v___x_739_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg___boxed(lean_object* v_c_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_, lean_object* v_a_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_c_740_, v_a_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_);
lean_dec(v_a_745_);
lean_dec_ref(v_a_744_);
lean_dec(v_a_743_);
lean_dec_ref(v_a_742_);
lean_dec(v_a_741_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase(lean_object* v_c_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_){
_start:
{
lean_object* v___x_760_; 
v___x_760_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_c_748_, v_a_749_, v_a_755_, v_a_756_, v_a_757_, v_a_758_);
return v___x_760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___boxed(lean_object* v_c_761_, lean_object* v_a_762_, lean_object* v_a_763_, lean_object* v_a_764_, lean_object* v_a_765_, lean_object* v_a_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase(v_c_761_, v_a_762_, v_a_763_, v_a_764_, v_a_765_, v_a_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_);
lean_dec(v_a_771_);
lean_dec_ref(v_a_770_);
lean_dec(v_a_769_);
lean_dec_ref(v_a_768_);
lean_dec(v_a_767_);
lean_dec_ref(v_a_766_);
lean_dec(v_a_765_);
lean_dec_ref(v_a_764_);
lean_dec(v_a_763_);
lean_dec(v_a_762_);
return v_res_773_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5(void){
_start:
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_787_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_788_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_789_ = l_Lean_Name_append(v___x_788_, v___x_787_);
return v___x_789_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7(void){
_start:
{
lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_791_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__6));
v___x_792_ = l_Lean_stringToMessageData(v___x_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3(lean_object* v_c_793_, lean_object* v_as_794_, size_t v_sz_795_, size_t v_i_796_, lean_object* v_b_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
uint8_t v___x_809_; 
v___x_809_ = lean_usize_dec_lt(v_i_796_, v_sz_795_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; 
lean_dec_ref(v_c_793_);
v___x_810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_810_, 0, v_b_797_);
return v___x_810_;
}
else
{
lean_object* v_snd_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_899_; 
v_snd_811_ = lean_ctor_get(v_b_797_, 1);
v_isSharedCheck_899_ = !lean_is_exclusive(v_b_797_);
if (v_isSharedCheck_899_ == 0)
{
lean_object* v_unused_900_; 
v_unused_900_ = lean_ctor_get(v_b_797_, 0);
lean_dec(v_unused_900_);
v___x_813_ = v_b_797_;
v_isShared_814_ = v_isSharedCheck_899_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_snd_811_);
lean_dec(v_b_797_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_899_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v_p_815_; lean_object* v_a_816_; lean_object* v_p_817_; lean_object* v___x_818_; uint8_t v___x_819_; 
v_p_815_ = lean_ctor_get(v_c_793_, 0);
v_a_816_ = lean_array_uget_borrowed(v_as_794_, v_i_796_);
v_p_817_ = lean_ctor_get(v_a_816_, 0);
v___x_818_ = lean_box(0);
v___x_819_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_815_, v_p_817_);
if (v___x_819_ == 0)
{
lean_object* v___x_820_; size_t v___x_821_; size_t v___x_822_; 
lean_del_object(v___x_813_);
lean_dec(v_snd_811_);
v___x_820_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__1));
v___x_821_ = ((size_t)1ULL);
v___x_822_ = lean_usize_add(v_i_796_, v___x_821_);
v_i_796_ = v___x_822_;
v_b_797_ = v___x_820_;
goto _start;
}
else
{
lean_object* v___x_824_; 
lean_inc_ref(v_p_815_);
lean_inc(v_a_816_);
v___x_824_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_816_, v___y_798_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
if (lean_obj_tag(v___x_824_) == 0)
{
lean_object* v_toCold_825_; lean_object* v_options_826_; lean_object* v_inheritedTraceOptions_827_; uint8_t v_hasTrace_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___y_837_; lean_object* v___y_838_; lean_object* v___y_839_; lean_object* v___y_840_; lean_object* v___y_841_; 
lean_dec_ref_known(v___x_824_, 1);
v_toCold_825_ = lean_ctor_get(v___y_806_, 0);
v_options_826_ = lean_ctor_get(v_toCold_825_, 2);
v_inheritedTraceOptions_827_ = lean_ctor_get(v_toCold_825_, 11);
v_hasTrace_828_ = lean_ctor_get_uint8(v_options_826_, sizeof(void*)*1);
lean_inc(v_a_816_);
v___x_829_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_829_, 0, v_c_793_);
lean_ctor_set(v___x_829_, 1, v_a_816_);
v___x_830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_830_, 0, v_p_815_);
lean_ctor_set(v___x_830_, 1, v___x_829_);
if (v_hasTrace_828_ == 0)
{
v___y_832_ = v___y_798_;
v___y_833_ = v___y_799_;
v___y_834_ = v___y_800_;
v___y_835_ = v___y_801_;
v___y_836_ = v___y_802_;
v___y_837_ = v___y_803_;
v___y_838_ = v___y_804_;
v___y_839_ = v___y_805_;
v___y_840_ = v___y_806_;
v___y_841_ = v___y_807_;
goto v___jp_831_;
}
else
{
lean_object* v___x_867_; lean_object* v___x_868_; uint8_t v___x_869_; 
v___x_867_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_868_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5);
v___x_869_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_827_, v_options_826_, v___x_868_);
if (v___x_869_ == 0)
{
v___y_832_ = v___y_798_;
v___y_833_ = v___y_799_;
v___y_834_ = v___y_800_;
v___y_835_ = v___y_801_;
v___y_836_ = v___y_802_;
v___y_837_ = v___y_803_;
v___y_838_ = v___y_804_;
v___y_839_ = v___y_805_;
v___y_840_ = v___y_806_;
v___y_841_ = v___y_807_;
goto v___jp_831_;
}
else
{
lean_object* v___x_870_; 
lean_inc_ref(v___x_830_);
v___x_870_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_830_, v___y_798_, v___y_806_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
lean_inc(v_a_871_);
lean_dec_ref_known(v___x_870_, 1);
v___x_872_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7);
v___x_873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_873_, 0, v___x_872_);
lean_ctor_set(v___x_873_, 1, v_a_871_);
v___x_874_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_867_, v___x_873_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_dec_ref_known(v___x_874_, 1);
v___y_832_ = v___y_798_;
v___y_833_ = v___y_799_;
v___y_834_ = v___y_800_;
v___y_835_ = v___y_801_;
v___y_836_ = v___y_802_;
v___y_837_ = v___y_803_;
v___y_838_ = v___y_804_;
v___y_839_ = v___y_805_;
v___y_840_ = v___y_806_;
v___y_841_ = v___y_807_;
goto v___jp_831_;
}
else
{
lean_object* v_a_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_882_; 
lean_dec_ref_known(v___x_830_, 2);
lean_del_object(v___x_813_);
lean_dec(v_snd_811_);
v_a_875_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_882_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_882_ == 0)
{
v___x_877_ = v___x_874_;
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_a_875_);
lean_dec(v___x_874_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_882_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_a_875_);
v___x_880_ = v_reuseFailAlloc_881_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
return v___x_880_;
}
}
}
}
else
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_890_; 
lean_dec_ref_known(v___x_830_, 2);
lean_del_object(v___x_813_);
lean_dec(v_snd_811_);
v_a_883_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_890_ == 0)
{
v___x_885_ = v___x_870_;
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_870_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
if (v_isShared_886_ == 0)
{
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_a_883_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
}
v___jp_831_:
{
lean_object* v___x_842_; 
lean_inc(v___y_841_);
lean_inc_ref(v___y_840_);
lean_inc(v___y_839_);
lean_inc_ref(v___y_838_);
lean_inc(v___y_837_);
lean_inc_ref(v___y_836_);
lean_inc(v___y_835_);
lean_inc_ref(v___y_834_);
lean_inc(v___y_833_);
lean_inc(v___y_832_);
v___x_842_ = lean_grind_cutsat_assert_eq(v___x_830_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_857_; 
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_857_ == 0)
{
lean_object* v_unused_858_; 
v_unused_858_ = lean_ctor_get(v___x_842_, 0);
lean_dec(v_unused_858_);
v___x_844_ = v___x_842_;
v_isShared_845_ = v_isSharedCheck_857_;
goto v_resetjp_843_;
}
else
{
lean_dec(v___x_842_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_857_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_849_; 
v___x_846_ = lean_box(v___x_819_);
v___x_847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_847_, 0, v___x_846_);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 1, v___x_818_);
lean_ctor_set(v___x_813_, 0, v___x_847_);
v___x_849_ = v___x_813_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v___x_847_);
lean_ctor_set(v_reuseFailAlloc_856_, 1, v___x_818_);
v___x_849_ = v_reuseFailAlloc_856_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_854_; 
v___x_850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_850_, 0, v___x_849_);
v___x_851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
v___x_852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_852_, 0, v___x_851_);
lean_ctor_set(v___x_852_, 1, v_snd_811_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 0, v___x_852_);
v___x_854_ = v___x_844_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_852_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
else
{
lean_object* v_a_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_866_; 
lean_del_object(v___x_813_);
lean_dec(v_snd_811_);
v_a_859_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_866_ == 0)
{
v___x_861_ = v___x_842_;
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_a_859_);
lean_dec(v___x_842_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_866_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_864_; 
if (v_isShared_862_ == 0)
{
v___x_864_ = v___x_861_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_a_859_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
}
}
else
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_898_; 
lean_dec_ref(v_p_815_);
lean_del_object(v___x_813_);
lean_dec(v_snd_811_);
lean_dec_ref(v_c_793_);
v_a_891_ = lean_ctor_get(v___x_824_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_898_ == 0)
{
v___x_893_ = v___x_824_;
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v___x_824_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_c_901_, lean_object* v_as_902_, lean_object* v_sz_903_, lean_object* v_i_904_, lean_object* v_b_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
size_t v_sz_boxed_917_; size_t v_i_boxed_918_; lean_object* v_res_919_; 
v_sz_boxed_917_ = lean_unbox_usize(v_sz_903_);
lean_dec(v_sz_903_);
v_i_boxed_918_ = lean_unbox_usize(v_i_904_);
lean_dec(v_i_904_);
v_res_919_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3(v_c_901_, v_as_902_, v_sz_boxed_917_, v_i_boxed_918_, v_b_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v___y_907_);
lean_dec(v___y_906_);
lean_dec_ref(v_as_902_);
return v_res_919_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2(lean_object* v_c_926_, lean_object* v_as_927_, size_t v_sz_928_, size_t v_i_929_, lean_object* v_b_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
uint8_t v___x_942_; 
v___x_942_ = lean_usize_dec_lt(v_i_929_, v_sz_928_);
if (v___x_942_ == 0)
{
lean_object* v___x_943_; 
lean_dec_ref(v_c_926_);
v___x_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_943_, 0, v_b_930_);
return v___x_943_;
}
else
{
lean_object* v_snd_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_1032_; 
v_snd_944_ = lean_ctor_get(v_b_930_, 1);
v_isSharedCheck_1032_ = !lean_is_exclusive(v_b_930_);
if (v_isSharedCheck_1032_ == 0)
{
lean_object* v_unused_1033_; 
v_unused_1033_ = lean_ctor_get(v_b_930_, 0);
lean_dec(v_unused_1033_);
v___x_946_ = v_b_930_;
v_isShared_947_ = v_isSharedCheck_1032_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_snd_944_);
lean_dec(v_b_930_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_1032_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v_p_948_; lean_object* v_a_949_; lean_object* v_p_950_; lean_object* v___x_951_; uint8_t v___x_952_; 
v_p_948_ = lean_ctor_get(v_c_926_, 0);
v_a_949_ = lean_array_uget_borrowed(v_as_927_, v_i_929_);
v_p_950_ = lean_ctor_get(v_a_949_, 0);
v___x_951_ = lean_box(0);
v___x_952_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_948_, v_p_950_);
if (v___x_952_ == 0)
{
lean_object* v___x_953_; size_t v___x_954_; size_t v___x_955_; lean_object* v___x_956_; 
lean_del_object(v___x_946_);
lean_dec(v_snd_944_);
v___x_953_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__1));
v___x_954_ = ((size_t)1ULL);
v___x_955_ = lean_usize_add(v_i_929_, v___x_954_);
v___x_956_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3(v_c_926_, v_as_927_, v_sz_928_, v___x_955_, v___x_953_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
return v___x_956_;
}
else
{
lean_object* v___x_957_; 
lean_inc_ref(v_p_948_);
lean_inc(v_a_949_);
v___x_957_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_949_, v___y_931_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v_toCold_958_; lean_object* v_options_959_; lean_object* v_inheritedTraceOptions_960_; uint8_t v_hasTrace_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___y_965_; lean_object* v___y_966_; lean_object* v___y_967_; lean_object* v___y_968_; lean_object* v___y_969_; lean_object* v___y_970_; lean_object* v___y_971_; lean_object* v___y_972_; lean_object* v___y_973_; lean_object* v___y_974_; 
lean_dec_ref_known(v___x_957_, 1);
v_toCold_958_ = lean_ctor_get(v___y_939_, 0);
v_options_959_ = lean_ctor_get(v_toCold_958_, 2);
v_inheritedTraceOptions_960_ = lean_ctor_get(v_toCold_958_, 11);
v_hasTrace_961_ = lean_ctor_get_uint8(v_options_959_, sizeof(void*)*1);
lean_inc(v_a_949_);
v___x_962_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_962_, 0, v_c_926_);
lean_ctor_set(v___x_962_, 1, v_a_949_);
v___x_963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_963_, 0, v_p_948_);
lean_ctor_set(v___x_963_, 1, v___x_962_);
if (v_hasTrace_961_ == 0)
{
v___y_965_ = v___y_931_;
v___y_966_ = v___y_932_;
v___y_967_ = v___y_933_;
v___y_968_ = v___y_934_;
v___y_969_ = v___y_935_;
v___y_970_ = v___y_936_;
v___y_971_ = v___y_937_;
v___y_972_ = v___y_938_;
v___y_973_ = v___y_939_;
v___y_974_ = v___y_940_;
goto v___jp_964_;
}
else
{
lean_object* v___x_1000_; lean_object* v___x_1001_; uint8_t v___x_1002_; 
v___x_1000_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_1001_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5);
v___x_1002_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_960_, v_options_959_, v___x_1001_);
if (v___x_1002_ == 0)
{
v___y_965_ = v___y_931_;
v___y_966_ = v___y_932_;
v___y_967_ = v___y_933_;
v___y_968_ = v___y_934_;
v___y_969_ = v___y_935_;
v___y_970_ = v___y_936_;
v___y_971_ = v___y_937_;
v___y_972_ = v___y_938_;
v___y_973_ = v___y_939_;
v___y_974_ = v___y_940_;
goto v___jp_964_;
}
else
{
lean_object* v___x_1003_; 
lean_inc_ref(v___x_963_);
v___x_1003_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_963_, v___y_931_, v___y_939_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
lean_inc(v_a_1004_);
lean_dec_ref_known(v___x_1003_, 1);
v___x_1005_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7);
v___x_1006_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
lean_ctor_set(v___x_1006_, 1, v_a_1004_);
v___x_1007_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_1000_, v___x_1006_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
if (lean_obj_tag(v___x_1007_) == 0)
{
lean_dec_ref_known(v___x_1007_, 1);
v___y_965_ = v___y_931_;
v___y_966_ = v___y_932_;
v___y_967_ = v___y_933_;
v___y_968_ = v___y_934_;
v___y_969_ = v___y_935_;
v___y_970_ = v___y_936_;
v___y_971_ = v___y_937_;
v___y_972_ = v___y_938_;
v___y_973_ = v___y_939_;
v___y_974_ = v___y_940_;
goto v___jp_964_;
}
else
{
lean_object* v_a_1008_; lean_object* v___x_1010_; uint8_t v_isShared_1011_; uint8_t v_isSharedCheck_1015_; 
lean_dec_ref_known(v___x_963_, 2);
lean_del_object(v___x_946_);
lean_dec(v_snd_944_);
v_a_1008_ = lean_ctor_get(v___x_1007_, 0);
v_isSharedCheck_1015_ = !lean_is_exclusive(v___x_1007_);
if (v_isSharedCheck_1015_ == 0)
{
v___x_1010_ = v___x_1007_;
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
else
{
lean_inc(v_a_1008_);
lean_dec(v___x_1007_);
v___x_1010_ = lean_box(0);
v_isShared_1011_ = v_isSharedCheck_1015_;
goto v_resetjp_1009_;
}
v_resetjp_1009_:
{
lean_object* v___x_1013_; 
if (v_isShared_1011_ == 0)
{
v___x_1013_ = v___x_1010_;
goto v_reusejp_1012_;
}
else
{
lean_object* v_reuseFailAlloc_1014_; 
v_reuseFailAlloc_1014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1014_, 0, v_a_1008_);
v___x_1013_ = v_reuseFailAlloc_1014_;
goto v_reusejp_1012_;
}
v_reusejp_1012_:
{
return v___x_1013_;
}
}
}
}
else
{
lean_object* v_a_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1023_; 
lean_dec_ref_known(v___x_963_, 2);
lean_del_object(v___x_946_);
lean_dec(v_snd_944_);
v_a_1016_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1023_ == 0)
{
v___x_1018_ = v___x_1003_;
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_a_1016_);
lean_dec(v___x_1003_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1023_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v___x_1021_; 
if (v_isShared_1019_ == 0)
{
v___x_1021_ = v___x_1018_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v_a_1016_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
}
}
v___jp_964_:
{
lean_object* v___x_975_; 
lean_inc(v___y_974_);
lean_inc_ref(v___y_973_);
lean_inc(v___y_972_);
lean_inc_ref(v___y_971_);
lean_inc(v___y_970_);
lean_inc_ref(v___y_969_);
lean_inc(v___y_968_);
lean_inc_ref(v___y_967_);
lean_inc(v___y_966_);
lean_inc(v___y_965_);
v___x_975_ = lean_grind_cutsat_assert_eq(v___x_963_, v___y_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_990_; 
v_isSharedCheck_990_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_990_ == 0)
{
lean_object* v_unused_991_; 
v_unused_991_ = lean_ctor_get(v___x_975_, 0);
lean_dec(v_unused_991_);
v___x_977_ = v___x_975_;
v_isShared_978_ = v_isSharedCheck_990_;
goto v_resetjp_976_;
}
else
{
lean_dec(v___x_975_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_990_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_982_; 
v___x_979_ = lean_box(v___x_952_);
v___x_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_980_, 0, v___x_979_);
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 1, v___x_951_);
lean_ctor_set(v___x_946_, 0, v___x_980_);
v___x_982_ = v___x_946_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_989_; 
v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_989_, 0, v___x_980_);
lean_ctor_set(v_reuseFailAlloc_989_, 1, v___x_951_);
v___x_982_ = v_reuseFailAlloc_989_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_987_; 
v___x_983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_983_, 0, v___x_982_);
v___x_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_984_, 0, v___x_983_);
v___x_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_984_);
lean_ctor_set(v___x_985_, 1, v_snd_944_);
if (v_isShared_978_ == 0)
{
lean_ctor_set(v___x_977_, 0, v___x_985_);
v___x_987_ = v___x_977_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v___x_985_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
}
else
{
lean_object* v_a_992_; lean_object* v___x_994_; uint8_t v_isShared_995_; uint8_t v_isSharedCheck_999_; 
lean_del_object(v___x_946_);
lean_dec(v_snd_944_);
v_a_992_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_999_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_999_ == 0)
{
v___x_994_ = v___x_975_;
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
else
{
lean_inc(v_a_992_);
lean_dec(v___x_975_);
v___x_994_ = lean_box(0);
v_isShared_995_ = v_isSharedCheck_999_;
goto v_resetjp_993_;
}
v_resetjp_993_:
{
lean_object* v___x_997_; 
if (v_isShared_995_ == 0)
{
v___x_997_ = v___x_994_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_a_992_);
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
}
else
{
lean_object* v_a_1024_; lean_object* v___x_1026_; uint8_t v_isShared_1027_; uint8_t v_isSharedCheck_1031_; 
lean_dec_ref(v_p_948_);
lean_del_object(v___x_946_);
lean_dec(v_snd_944_);
lean_dec_ref(v_c_926_);
v_a_1024_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_1031_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_1031_ == 0)
{
v___x_1026_ = v___x_957_;
v_isShared_1027_ = v_isSharedCheck_1031_;
goto v_resetjp_1025_;
}
else
{
lean_inc(v_a_1024_);
lean_dec(v___x_957_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___boxed(lean_object* v_c_1034_, lean_object* v_as_1035_, lean_object* v_sz_1036_, lean_object* v_i_1037_, lean_object* v_b_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_){
_start:
{
size_t v_sz_boxed_1050_; size_t v_i_boxed_1051_; lean_object* v_res_1052_; 
v_sz_boxed_1050_ = lean_unbox_usize(v_sz_1036_);
lean_dec(v_sz_1036_);
v_i_boxed_1051_ = lean_unbox_usize(v_i_1037_);
lean_dec(v_i_1037_);
v_res_1052_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2(v_c_1034_, v_as_1035_, v_sz_boxed_1050_, v_i_boxed_1051_, v_b_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec(v___y_1040_);
lean_dec(v___y_1039_);
lean_dec_ref(v_as_1035_);
return v_res_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(lean_object* v_init_1053_, lean_object* v_c_1054_, lean_object* v_n_1055_, lean_object* v_b_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
if (lean_obj_tag(v_n_1055_) == 0)
{
lean_object* v_cs_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; size_t v_sz_1071_; size_t v___x_1072_; lean_object* v___x_1073_; 
v_cs_1068_ = lean_ctor_get(v_n_1055_, 0);
v___x_1069_ = lean_box(0);
v___x_1070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1070_, 0, v___x_1069_);
lean_ctor_set(v___x_1070_, 1, v_b_1056_);
v_sz_1071_ = lean_array_size(v_cs_1068_);
v___x_1072_ = ((size_t)0ULL);
v___x_1073_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(v_init_1053_, v_c_1054_, v_cs_1068_, v_sz_1071_, v___x_1072_, v___x_1070_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
if (lean_obj_tag(v___x_1073_) == 0)
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1088_; 
v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1088_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1076_ = v___x_1073_;
v_isShared_1077_ = v_isSharedCheck_1088_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1073_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1088_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v_fst_1078_; 
v_fst_1078_ = lean_ctor_get(v_a_1074_, 0);
if (lean_obj_tag(v_fst_1078_) == 0)
{
lean_object* v_snd_1079_; lean_object* v___x_1080_; lean_object* v___x_1082_; 
v_snd_1079_ = lean_ctor_get(v_a_1074_, 1);
lean_inc(v_snd_1079_);
lean_dec(v_a_1074_);
v___x_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1080_, 0, v_snd_1079_);
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 0, v___x_1080_);
v___x_1082_ = v___x_1076_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v___x_1080_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
else
{
lean_object* v_val_1084_; lean_object* v___x_1086_; 
lean_inc_ref(v_fst_1078_);
lean_dec(v_a_1074_);
v_val_1084_ = lean_ctor_get(v_fst_1078_, 0);
lean_inc(v_val_1084_);
lean_dec_ref_known(v_fst_1078_, 1);
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 0, v_val_1084_);
v___x_1086_ = v___x_1076_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_val_1084_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
else
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1096_; 
v_a_1089_ = lean_ctor_get(v___x_1073_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v___x_1073_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1091_ = v___x_1073_;
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1073_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1096_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1094_; 
if (v_isShared_1092_ == 0)
{
v___x_1094_ = v___x_1091_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_a_1089_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
else
{
lean_object* v_vs_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; size_t v_sz_1100_; size_t v___x_1101_; lean_object* v___x_1102_; 
v_vs_1097_ = lean_ctor_get(v_n_1055_, 0);
v___x_1098_ = lean_box(0);
v___x_1099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1098_);
lean_ctor_set(v___x_1099_, 1, v_b_1056_);
v_sz_1100_ = lean_array_size(v_vs_1097_);
v___x_1101_ = ((size_t)0ULL);
v___x_1102_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2(v_c_1054_, v_vs_1097_, v_sz_1100_, v___x_1101_, v___x_1099_, v___y_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1117_; 
v_a_1103_ = lean_ctor_get(v___x_1102_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1105_ = v___x_1102_;
v_isShared_1106_ = v_isSharedCheck_1117_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1102_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1117_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v_fst_1107_; 
v_fst_1107_ = lean_ctor_get(v_a_1103_, 0);
if (lean_obj_tag(v_fst_1107_) == 0)
{
lean_object* v_snd_1108_; lean_object* v___x_1109_; lean_object* v___x_1111_; 
v_snd_1108_ = lean_ctor_get(v_a_1103_, 1);
lean_inc(v_snd_1108_);
lean_dec(v_a_1103_);
v___x_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1109_, 0, v_snd_1108_);
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 0, v___x_1109_);
v___x_1111_ = v___x_1105_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v___x_1109_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
else
{
lean_object* v_val_1113_; lean_object* v___x_1115_; 
lean_inc_ref(v_fst_1107_);
lean_dec(v_a_1103_);
v_val_1113_ = lean_ctor_get(v_fst_1107_, 0);
lean_inc(v_val_1113_);
lean_dec_ref_known(v_fst_1107_, 1);
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 0, v_val_1113_);
v___x_1115_ = v___x_1105_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_val_1113_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
else
{
lean_object* v_a_1118_; lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
v_a_1118_ = lean_ctor_get(v___x_1102_, 0);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1120_ = v___x_1102_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_inc(v_a_1118_);
lean_dec(v___x_1102_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1118_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(lean_object* v_init_1126_, lean_object* v_c_1127_, lean_object* v_as_1128_, size_t v_sz_1129_, size_t v_i_1130_, lean_object* v_b_1131_, lean_object* v___y_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
uint8_t v___x_1143_; 
v___x_1143_ = lean_usize_dec_lt(v_i_1130_, v_sz_1129_);
if (v___x_1143_ == 0)
{
lean_object* v___x_1144_; 
lean_dec_ref(v_c_1127_);
v___x_1144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1144_, 0, v_b_1131_);
return v___x_1144_;
}
else
{
lean_object* v_snd_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1179_; 
v_snd_1145_ = lean_ctor_get(v_b_1131_, 1);
v_isSharedCheck_1179_ = !lean_is_exclusive(v_b_1131_);
if (v_isSharedCheck_1179_ == 0)
{
lean_object* v_unused_1180_; 
v_unused_1180_ = lean_ctor_get(v_b_1131_, 0);
lean_dec(v_unused_1180_);
v___x_1147_ = v_b_1131_;
v_isShared_1148_ = v_isSharedCheck_1179_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_snd_1145_);
lean_dec(v_b_1131_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1179_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1149_; lean_object* v_a_1150_; lean_object* v___x_1151_; 
v___x_1149_ = lean_box(0);
v_a_1150_ = lean_array_uget_borrowed(v_as_1128_, v_i_1130_);
lean_inc(v_snd_1145_);
lean_inc_ref(v_c_1127_);
v___x_1151_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(v_init_1126_, v_c_1127_, v_a_1150_, v_snd_1145_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1170_; 
v_a_1152_ = lean_ctor_get(v___x_1151_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1154_ = v___x_1151_;
v_isShared_1155_ = v_isSharedCheck_1170_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1151_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1170_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
if (lean_obj_tag(v_a_1152_) == 0)
{
lean_object* v___x_1156_; lean_object* v___x_1158_; 
lean_dec_ref(v_c_1127_);
v___x_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1156_, 0, v_a_1152_);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 0, v___x_1156_);
v___x_1158_ = v___x_1147_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v___x_1156_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v_snd_1145_);
v___x_1158_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
lean_object* v___x_1160_; 
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 0, v___x_1158_);
v___x_1160_ = v___x_1154_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v___x_1158_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
else
{
lean_object* v_a_1163_; lean_object* v___x_1165_; 
lean_del_object(v___x_1154_);
lean_dec(v_snd_1145_);
v_a_1163_ = lean_ctor_get(v_a_1152_, 0);
lean_inc(v_a_1163_);
lean_dec_ref_known(v_a_1152_, 1);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 1, v_a_1163_);
lean_ctor_set(v___x_1147_, 0, v___x_1149_);
v___x_1165_ = v___x_1147_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v___x_1149_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v_a_1163_);
v___x_1165_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
size_t v___x_1166_; size_t v___x_1167_; 
v___x_1166_ = ((size_t)1ULL);
v___x_1167_ = lean_usize_add(v_i_1130_, v___x_1166_);
v_i_1130_ = v___x_1167_;
v_b_1131_ = v___x_1165_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1178_; 
lean_del_object(v___x_1147_);
lean_dec(v_snd_1145_);
lean_dec_ref(v_c_1127_);
v_a_1171_ = lean_ctor_get(v___x_1151_, 0);
v_isSharedCheck_1178_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1173_ = v___x_1151_;
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_a_1171_);
lean_dec(v___x_1151_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1178_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___x_1176_; 
if (v_isShared_1174_ == 0)
{
v___x_1176_ = v___x_1173_;
goto v_reusejp_1175_;
}
else
{
lean_object* v_reuseFailAlloc_1177_; 
v_reuseFailAlloc_1177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1177_, 0, v_a_1171_);
v___x_1176_ = v_reuseFailAlloc_1177_;
goto v_reusejp_1175_;
}
v_reusejp_1175_:
{
return v___x_1176_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1___boxed(lean_object** _args){
lean_object* v_init_1181_ = _args[0];
lean_object* v_c_1182_ = _args[1];
lean_object* v_as_1183_ = _args[2];
lean_object* v_sz_1184_ = _args[3];
lean_object* v_i_1185_ = _args[4];
lean_object* v_b_1186_ = _args[5];
lean_object* v___y_1187_ = _args[6];
lean_object* v___y_1188_ = _args[7];
lean_object* v___y_1189_ = _args[8];
lean_object* v___y_1190_ = _args[9];
lean_object* v___y_1191_ = _args[10];
lean_object* v___y_1192_ = _args[11];
lean_object* v___y_1193_ = _args[12];
lean_object* v___y_1194_ = _args[13];
lean_object* v___y_1195_ = _args[14];
lean_object* v___y_1196_ = _args[15];
lean_object* v___y_1197_ = _args[16];
_start:
{
size_t v_sz_boxed_1198_; size_t v_i_boxed_1199_; lean_object* v_res_1200_; 
v_sz_boxed_1198_ = lean_unbox_usize(v_sz_1184_);
lean_dec(v_sz_1184_);
v_i_boxed_1199_ = lean_unbox_usize(v_i_1185_);
lean_dec(v_i_1185_);
v_res_1200_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__1(v_init_1181_, v_c_1182_, v_as_1183_, v_sz_boxed_1198_, v_i_boxed_1199_, v_b_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec_ref(v_as_1183_);
lean_dec_ref(v_init_1181_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0___boxed(lean_object* v_init_1201_, lean_object* v_c_1202_, lean_object* v_n_1203_, lean_object* v_b_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(v_init_1201_, v_c_1202_, v_n_1203_, v_b_1204_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
lean_dec(v___y_1210_);
lean_dec_ref(v___y_1209_);
lean_dec(v___y_1208_);
lean_dec_ref(v___y_1207_);
lean_dec(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec_ref(v_n_1203_);
lean_dec_ref(v_init_1201_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4(lean_object* v_c_1223_, lean_object* v_as_1224_, size_t v_sz_1225_, size_t v_i_1226_, lean_object* v_b_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
uint8_t v___x_1239_; 
v___x_1239_ = lean_usize_dec_lt(v_i_1226_, v_sz_1225_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1240_; 
lean_dec_ref(v_c_1223_);
v___x_1240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1240_, 0, v_b_1227_);
return v___x_1240_;
}
else
{
lean_object* v_snd_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1328_; 
v_snd_1241_ = lean_ctor_get(v_b_1227_, 1);
v_isSharedCheck_1328_ = !lean_is_exclusive(v_b_1227_);
if (v_isSharedCheck_1328_ == 0)
{
lean_object* v_unused_1329_; 
v_unused_1329_ = lean_ctor_get(v_b_1227_, 0);
lean_dec(v_unused_1329_);
v___x_1243_ = v_b_1227_;
v_isShared_1244_ = v_isSharedCheck_1328_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_snd_1241_);
lean_dec(v_b_1227_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1328_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v_p_1245_; lean_object* v_a_1246_; lean_object* v_p_1247_; lean_object* v___x_1248_; uint8_t v___x_1249_; 
v_p_1245_ = lean_ctor_get(v_c_1223_, 0);
v_a_1246_ = lean_array_uget_borrowed(v_as_1224_, v_i_1226_);
v_p_1247_ = lean_ctor_get(v_a_1246_, 0);
v___x_1248_ = lean_box(0);
v___x_1249_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_1245_, v_p_1247_);
if (v___x_1249_ == 0)
{
lean_object* v___x_1250_; size_t v___x_1251_; size_t v___x_1252_; 
lean_del_object(v___x_1243_);
lean_dec(v_snd_1241_);
v___x_1250_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___closed__1));
v___x_1251_ = ((size_t)1ULL);
v___x_1252_ = lean_usize_add(v_i_1226_, v___x_1251_);
v_i_1226_ = v___x_1252_;
v_b_1227_ = v___x_1250_;
goto _start;
}
else
{
lean_object* v___x_1254_; 
lean_inc_ref(v_p_1245_);
lean_inc(v_a_1246_);
v___x_1254_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_1246_, v___y_1228_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_object* v_toCold_1255_; lean_object* v_options_1256_; lean_object* v_inheritedTraceOptions_1257_; uint8_t v_hasTrace_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___y_1262_; lean_object* v___y_1263_; lean_object* v___y_1264_; lean_object* v___y_1265_; lean_object* v___y_1266_; lean_object* v___y_1267_; lean_object* v___y_1268_; lean_object* v___y_1269_; lean_object* v___y_1270_; lean_object* v___y_1271_; 
lean_dec_ref_known(v___x_1254_, 1);
v_toCold_1255_ = lean_ctor_get(v___y_1236_, 0);
v_options_1256_ = lean_ctor_get(v_toCold_1255_, 2);
v_inheritedTraceOptions_1257_ = lean_ctor_get(v_toCold_1255_, 11);
v_hasTrace_1258_ = lean_ctor_get_uint8(v_options_1256_, sizeof(void*)*1);
lean_inc(v_a_1246_);
v___x_1259_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1259_, 0, v_c_1223_);
lean_ctor_set(v___x_1259_, 1, v_a_1246_);
v___x_1260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1260_, 0, v_p_1245_);
lean_ctor_set(v___x_1260_, 1, v___x_1259_);
if (v_hasTrace_1258_ == 0)
{
v___y_1262_ = v___y_1228_;
v___y_1263_ = v___y_1229_;
v___y_1264_ = v___y_1230_;
v___y_1265_ = v___y_1231_;
v___y_1266_ = v___y_1232_;
v___y_1267_ = v___y_1233_;
v___y_1268_ = v___y_1234_;
v___y_1269_ = v___y_1235_;
v___y_1270_ = v___y_1236_;
v___y_1271_ = v___y_1237_;
goto v___jp_1261_;
}
else
{
lean_object* v___x_1296_; lean_object* v___x_1297_; uint8_t v___x_1298_; 
v___x_1296_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_1297_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5);
v___x_1298_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1257_, v_options_1256_, v___x_1297_);
if (v___x_1298_ == 0)
{
v___y_1262_ = v___y_1228_;
v___y_1263_ = v___y_1229_;
v___y_1264_ = v___y_1230_;
v___y_1265_ = v___y_1231_;
v___y_1266_ = v___y_1232_;
v___y_1267_ = v___y_1233_;
v___y_1268_ = v___y_1234_;
v___y_1269_ = v___y_1235_;
v___y_1270_ = v___y_1236_;
v___y_1271_ = v___y_1237_;
goto v___jp_1261_;
}
else
{
lean_object* v___x_1299_; 
lean_inc_ref(v___x_1260_);
v___x_1299_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_1260_, v___y_1228_, v___y_1236_);
if (lean_obj_tag(v___x_1299_) == 0)
{
lean_object* v_a_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; 
v_a_1300_ = lean_ctor_get(v___x_1299_, 0);
lean_inc(v_a_1300_);
lean_dec_ref_known(v___x_1299_, 1);
v___x_1301_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7);
v___x_1302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1301_);
lean_ctor_set(v___x_1302_, 1, v_a_1300_);
v___x_1303_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_1296_, v___x_1302_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_dec_ref_known(v___x_1303_, 1);
v___y_1262_ = v___y_1228_;
v___y_1263_ = v___y_1229_;
v___y_1264_ = v___y_1230_;
v___y_1265_ = v___y_1231_;
v___y_1266_ = v___y_1232_;
v___y_1267_ = v___y_1233_;
v___y_1268_ = v___y_1234_;
v___y_1269_ = v___y_1235_;
v___y_1270_ = v___y_1236_;
v___y_1271_ = v___y_1237_;
goto v___jp_1261_;
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
lean_dec_ref_known(v___x_1260_, 2);
lean_del_object(v___x_1243_);
lean_dec(v_snd_1241_);
v_a_1304_ = lean_ctor_get(v___x_1303_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1303_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1303_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
else
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1319_; 
lean_dec_ref_known(v___x_1260_, 2);
lean_del_object(v___x_1243_);
lean_dec(v_snd_1241_);
v_a_1312_ = lean_ctor_get(v___x_1299_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1299_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1314_ = v___x_1299_;
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1299_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1317_; 
if (v_isShared_1315_ == 0)
{
v___x_1317_ = v___x_1314_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_a_1312_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
}
}
v___jp_1261_:
{
lean_object* v___x_1272_; 
lean_inc(v___y_1271_);
lean_inc_ref(v___y_1270_);
lean_inc(v___y_1269_);
lean_inc_ref(v___y_1268_);
lean_inc(v___y_1267_);
lean_inc_ref(v___y_1266_);
lean_inc(v___y_1265_);
lean_inc_ref(v___y_1264_);
lean_inc(v___y_1263_);
lean_inc(v___y_1262_);
v___x_1272_ = lean_grind_cutsat_assert_eq(v___x_1260_, v___y_1262_, v___y_1263_, v___y_1264_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1286_; 
v_isSharedCheck_1286_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1286_ == 0)
{
lean_object* v_unused_1287_; 
v_unused_1287_ = lean_ctor_get(v___x_1272_, 0);
lean_dec(v_unused_1287_);
v___x_1274_ = v___x_1272_;
v_isShared_1275_ = v_isSharedCheck_1286_;
goto v_resetjp_1273_;
}
else
{
lean_dec(v___x_1272_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1286_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1279_; 
v___x_1276_ = lean_box(v___x_1249_);
v___x_1277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1276_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 1, v___x_1248_);
lean_ctor_set(v___x_1243_, 0, v___x_1277_);
v___x_1279_ = v___x_1243_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1285_; 
v_reuseFailAlloc_1285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1285_, 0, v___x_1277_);
lean_ctor_set(v_reuseFailAlloc_1285_, 1, v___x_1248_);
v___x_1279_ = v_reuseFailAlloc_1285_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1283_; 
v___x_1280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1280_, 0, v___x_1279_);
v___x_1281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1280_);
lean_ctor_set(v___x_1281_, 1, v_snd_1241_);
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 0, v___x_1281_);
v___x_1283_ = v___x_1274_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v___x_1281_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
lean_del_object(v___x_1243_);
lean_dec(v_snd_1241_);
v_a_1288_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1272_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1272_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1288_);
v___x_1293_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1292_;
}
v_reusejp_1292_:
{
return v___x_1293_;
}
}
}
}
}
else
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1327_; 
lean_dec_ref(v_p_1245_);
lean_del_object(v___x_1243_);
lean_dec(v_snd_1241_);
lean_dec_ref(v_c_1223_);
v_a_1320_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1322_ = v___x_1254_;
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1254_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1325_; 
if (v_isShared_1323_ == 0)
{
v___x_1325_ = v___x_1322_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_a_1320_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4___boxed(lean_object* v_c_1330_, lean_object* v_as_1331_, lean_object* v_sz_1332_, lean_object* v_i_1333_, lean_object* v_b_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
size_t v_sz_boxed_1346_; size_t v_i_boxed_1347_; lean_object* v_res_1348_; 
v_sz_boxed_1346_ = lean_unbox_usize(v_sz_1332_);
lean_dec(v_sz_1332_);
v_i_boxed_1347_ = lean_unbox_usize(v_i_1333_);
lean_dec(v_i_1333_);
v_res_1348_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4(v_c_1330_, v_as_1331_, v_sz_boxed_1346_, v_i_boxed_1347_, v_b_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
lean_dec(v___y_1342_);
lean_dec_ref(v___y_1341_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec(v___y_1335_);
lean_dec_ref(v_as_1331_);
return v_res_1348_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1(lean_object* v_c_1352_, lean_object* v_as_1353_, size_t v_sz_1354_, size_t v_i_1355_, lean_object* v_b_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
uint8_t v___x_1368_; 
v___x_1368_ = lean_usize_dec_lt(v_i_1355_, v_sz_1354_);
if (v___x_1368_ == 0)
{
lean_object* v___x_1369_; 
lean_dec_ref(v_c_1352_);
v___x_1369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1369_, 0, v_b_1356_);
return v___x_1369_;
}
else
{
lean_object* v_snd_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1457_; 
v_snd_1370_ = lean_ctor_get(v_b_1356_, 1);
v_isSharedCheck_1457_ = !lean_is_exclusive(v_b_1356_);
if (v_isSharedCheck_1457_ == 0)
{
lean_object* v_unused_1458_; 
v_unused_1458_ = lean_ctor_get(v_b_1356_, 0);
lean_dec(v_unused_1458_);
v___x_1372_ = v_b_1356_;
v_isShared_1373_ = v_isSharedCheck_1457_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_snd_1370_);
lean_dec(v_b_1356_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1457_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v_p_1374_; lean_object* v_a_1375_; lean_object* v_p_1376_; lean_object* v___x_1377_; uint8_t v___x_1378_; 
v_p_1374_ = lean_ctor_get(v_c_1352_, 0);
v_a_1375_ = lean_array_uget_borrowed(v_as_1353_, v_i_1355_);
v_p_1376_ = lean_ctor_get(v_a_1375_, 0);
v___x_1377_ = lean_box(0);
v___x_1378_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_1374_, v_p_1376_);
if (v___x_1378_ == 0)
{
lean_object* v___x_1379_; size_t v___x_1380_; size_t v___x_1381_; lean_object* v___x_1382_; 
lean_del_object(v___x_1372_);
lean_dec(v_snd_1370_);
v___x_1379_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1___closed__0));
v___x_1380_ = ((size_t)1ULL);
v___x_1381_ = lean_usize_add(v_i_1355_, v___x_1380_);
v___x_1382_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1_spec__4(v_c_1352_, v_as_1353_, v_sz_1354_, v___x_1381_, v___x_1379_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
return v___x_1382_;
}
else
{
lean_object* v___x_1383_; 
lean_inc_ref(v_p_1374_);
lean_inc(v_a_1375_);
v___x_1383_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase___redArg(v_a_1375_, v___y_1357_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_toCold_1384_; lean_object* v_options_1385_; lean_object* v_inheritedTraceOptions_1386_; uint8_t v_hasTrace_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1400_; 
lean_dec_ref_known(v___x_1383_, 1);
v_toCold_1384_ = lean_ctor_get(v___y_1365_, 0);
v_options_1385_ = lean_ctor_get(v_toCold_1384_, 2);
v_inheritedTraceOptions_1386_ = lean_ctor_get(v_toCold_1384_, 11);
v_hasTrace_1387_ = lean_ctor_get_uint8(v_options_1385_, sizeof(void*)*1);
lean_inc(v_a_1375_);
v___x_1388_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1388_, 0, v_c_1352_);
lean_ctor_set(v___x_1388_, 1, v_a_1375_);
v___x_1389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1389_, 0, v_p_1374_);
lean_ctor_set(v___x_1389_, 1, v___x_1388_);
if (v_hasTrace_1387_ == 0)
{
v___y_1391_ = v___y_1357_;
v___y_1392_ = v___y_1358_;
v___y_1393_ = v___y_1359_;
v___y_1394_ = v___y_1360_;
v___y_1395_ = v___y_1361_;
v___y_1396_ = v___y_1362_;
v___y_1397_ = v___y_1363_;
v___y_1398_ = v___y_1364_;
v___y_1399_ = v___y_1365_;
v___y_1400_ = v___y_1366_;
goto v___jp_1390_;
}
else
{
lean_object* v___x_1425_; lean_object* v___x_1426_; uint8_t v___x_1427_; 
v___x_1425_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__4));
v___x_1426_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__5);
v___x_1427_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1386_, v_options_1385_, v___x_1426_);
if (v___x_1427_ == 0)
{
v___y_1391_ = v___y_1357_;
v___y_1392_ = v___y_1358_;
v___y_1393_ = v___y_1359_;
v___y_1394_ = v___y_1360_;
v___y_1395_ = v___y_1361_;
v___y_1396_ = v___y_1362_;
v___y_1397_ = v___y_1363_;
v___y_1398_ = v___y_1364_;
v___y_1399_ = v___y_1365_;
v___y_1400_ = v___y_1366_;
goto v___jp_1390_;
}
else
{
lean_object* v___x_1428_; 
lean_inc_ref(v___x_1389_);
v___x_1428_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(v___x_1389_, v___y_1357_, v___y_1365_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_a_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
lean_inc(v_a_1429_);
lean_dec_ref_known(v___x_1428_, 1);
v___x_1430_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2_spec__3___closed__7);
v___x_1431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1430_);
lean_ctor_set(v___x_1431_, 1, v_a_1429_);
v___x_1432_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_1425_, v___x_1431_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
if (lean_obj_tag(v___x_1432_) == 0)
{
lean_dec_ref_known(v___x_1432_, 1);
v___y_1391_ = v___y_1357_;
v___y_1392_ = v___y_1358_;
v___y_1393_ = v___y_1359_;
v___y_1394_ = v___y_1360_;
v___y_1395_ = v___y_1361_;
v___y_1396_ = v___y_1362_;
v___y_1397_ = v___y_1363_;
v___y_1398_ = v___y_1364_;
v___y_1399_ = v___y_1365_;
v___y_1400_ = v___y_1366_;
goto v___jp_1390_;
}
else
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1440_; 
lean_dec_ref_known(v___x_1389_, 2);
lean_del_object(v___x_1372_);
lean_dec(v_snd_1370_);
v_a_1433_ = lean_ctor_get(v___x_1432_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1432_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1435_ = v___x_1432_;
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v___x_1432_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1438_; 
if (v_isShared_1436_ == 0)
{
v___x_1438_ = v___x_1435_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_a_1433_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
}
else
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
lean_dec_ref_known(v___x_1389_, 2);
lean_del_object(v___x_1372_);
lean_dec(v_snd_1370_);
v_a_1441_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1443_ = v___x_1428_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1428_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1446_; 
if (v_isShared_1444_ == 0)
{
v___x_1446_ = v___x_1443_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_a_1441_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
}
}
v___jp_1390_:
{
lean_object* v___x_1401_; 
lean_inc(v___y_1400_);
lean_inc_ref(v___y_1399_);
lean_inc(v___y_1398_);
lean_inc_ref(v___y_1397_);
lean_inc(v___y_1396_);
lean_inc_ref(v___y_1395_);
lean_inc(v___y_1394_);
lean_inc_ref(v___y_1393_);
lean_inc(v___y_1392_);
lean_inc(v___y_1391_);
v___x_1401_ = lean_grind_cutsat_assert_eq(v___x_1389_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_);
if (lean_obj_tag(v___x_1401_) == 0)
{
lean_object* v___x_1403_; uint8_t v_isShared_1404_; uint8_t v_isSharedCheck_1415_; 
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1415_ == 0)
{
lean_object* v_unused_1416_; 
v_unused_1416_ = lean_ctor_get(v___x_1401_, 0);
lean_dec(v_unused_1416_);
v___x_1403_ = v___x_1401_;
v_isShared_1404_ = v_isSharedCheck_1415_;
goto v_resetjp_1402_;
}
else
{
lean_dec(v___x_1401_);
v___x_1403_ = lean_box(0);
v_isShared_1404_ = v_isSharedCheck_1415_;
goto v_resetjp_1402_;
}
v_resetjp_1402_:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1408_; 
v___x_1405_ = lean_box(v___x_1378_);
v___x_1406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1405_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 1, v___x_1377_);
lean_ctor_set(v___x_1372_, 0, v___x_1406_);
v___x_1408_ = v___x_1372_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1406_);
lean_ctor_set(v_reuseFailAlloc_1414_, 1, v___x_1377_);
v___x_1408_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1412_; 
v___x_1409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1408_);
v___x_1410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1409_);
lean_ctor_set(v___x_1410_, 1, v_snd_1370_);
if (v_isShared_1404_ == 0)
{
lean_ctor_set(v___x_1403_, 0, v___x_1410_);
v___x_1412_ = v___x_1403_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v___x_1410_);
v___x_1412_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
return v___x_1412_;
}
}
}
}
else
{
lean_object* v_a_1417_; lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1424_; 
lean_del_object(v___x_1372_);
lean_dec(v_snd_1370_);
v_a_1417_ = lean_ctor_get(v___x_1401_, 0);
v_isSharedCheck_1424_ = !lean_is_exclusive(v___x_1401_);
if (v_isSharedCheck_1424_ == 0)
{
v___x_1419_ = v___x_1401_;
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
else
{
lean_inc(v_a_1417_);
lean_dec(v___x_1401_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1424_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v___x_1422_; 
if (v_isShared_1420_ == 0)
{
v___x_1422_ = v___x_1419_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v_a_1417_);
v___x_1422_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
return v___x_1422_;
}
}
}
}
}
else
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1456_; 
lean_dec_ref(v_p_1374_);
lean_del_object(v___x_1372_);
lean_dec(v_snd_1370_);
lean_dec_ref(v_c_1352_);
v_a_1449_ = lean_ctor_get(v___x_1383_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1383_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1451_ = v___x_1383_;
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1383_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1454_; 
if (v_isShared_1452_ == 0)
{
v___x_1454_ = v___x_1451_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_a_1449_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1___boxed(lean_object* v_c_1459_, lean_object* v_as_1460_, lean_object* v_sz_1461_, lean_object* v_i_1462_, lean_object* v_b_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
size_t v_sz_boxed_1475_; size_t v_i_boxed_1476_; lean_object* v_res_1477_; 
v_sz_boxed_1475_ = lean_unbox_usize(v_sz_1461_);
lean_dec(v_sz_1461_);
v_i_boxed_1476_ = lean_unbox_usize(v_i_1462_);
lean_dec(v_i_1462_);
v_res_1477_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1(v_c_1459_, v_as_1460_, v_sz_boxed_1475_, v_i_boxed_1476_, v_b_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_);
lean_dec(v___y_1473_);
lean_dec_ref(v___y_1472_);
lean_dec(v___y_1471_);
lean_dec_ref(v___y_1470_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec_ref(v_as_1460_);
return v_res_1477_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0(lean_object* v_c_1478_, lean_object* v_t_1479_, lean_object* v_init_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v_root_1492_; lean_object* v_tail_1493_; lean_object* v___x_1494_; 
v_root_1492_ = lean_ctor_get(v_t_1479_, 0);
v_tail_1493_ = lean_ctor_get(v_t_1479_, 1);
lean_inc_ref(v_c_1478_);
lean_inc_ref(v_init_1480_);
v___x_1494_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0(v_init_1480_, v_c_1478_, v_root_1492_, v_init_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
lean_dec_ref(v_init_1480_);
if (lean_obj_tag(v___x_1494_) == 0)
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1531_; 
v_a_1495_ = lean_ctor_get(v___x_1494_, 0);
v_isSharedCheck_1531_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1531_ == 0)
{
v___x_1497_ = v___x_1494_;
v_isShared_1498_ = v_isSharedCheck_1531_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1494_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1531_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
if (lean_obj_tag(v_a_1495_) == 0)
{
lean_object* v_a_1499_; lean_object* v___x_1501_; 
lean_dec_ref(v_c_1478_);
v_a_1499_ = lean_ctor_get(v_a_1495_, 0);
lean_inc(v_a_1499_);
lean_dec_ref_known(v_a_1495_, 1);
if (v_isShared_1498_ == 0)
{
lean_ctor_set(v___x_1497_, 0, v_a_1499_);
v___x_1501_ = v___x_1497_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1502_; 
v_reuseFailAlloc_1502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1502_, 0, v_a_1499_);
v___x_1501_ = v_reuseFailAlloc_1502_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
return v___x_1501_;
}
}
else
{
lean_object* v_a_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; size_t v_sz_1506_; size_t v___x_1507_; lean_object* v___x_1508_; 
lean_del_object(v___x_1497_);
v_a_1503_ = lean_ctor_get(v_a_1495_, 0);
lean_inc(v_a_1503_);
lean_dec_ref_known(v_a_1495_, 1);
v___x_1504_ = lean_box(0);
v___x_1505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1504_);
lean_ctor_set(v___x_1505_, 1, v_a_1503_);
v_sz_1506_ = lean_array_size(v_tail_1493_);
v___x_1507_ = ((size_t)0ULL);
v___x_1508_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__1(v_c_1478_, v_tail_1493_, v_sz_1506_, v___x_1507_, v___x_1505_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
if (lean_obj_tag(v___x_1508_) == 0)
{
lean_object* v_a_1509_; lean_object* v___x_1511_; uint8_t v_isShared_1512_; uint8_t v_isSharedCheck_1522_; 
v_a_1509_ = lean_ctor_get(v___x_1508_, 0);
v_isSharedCheck_1522_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1522_ == 0)
{
v___x_1511_ = v___x_1508_;
v_isShared_1512_ = v_isSharedCheck_1522_;
goto v_resetjp_1510_;
}
else
{
lean_inc(v_a_1509_);
lean_dec(v___x_1508_);
v___x_1511_ = lean_box(0);
v_isShared_1512_ = v_isSharedCheck_1522_;
goto v_resetjp_1510_;
}
v_resetjp_1510_:
{
lean_object* v_fst_1513_; 
v_fst_1513_ = lean_ctor_get(v_a_1509_, 0);
if (lean_obj_tag(v_fst_1513_) == 0)
{
lean_object* v_snd_1514_; lean_object* v___x_1516_; 
v_snd_1514_ = lean_ctor_get(v_a_1509_, 1);
lean_inc(v_snd_1514_);
lean_dec(v_a_1509_);
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 0, v_snd_1514_);
v___x_1516_ = v___x_1511_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_snd_1514_);
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
lean_object* v_val_1518_; lean_object* v___x_1520_; 
lean_inc_ref(v_fst_1513_);
lean_dec(v_a_1509_);
v_val_1518_ = lean_ctor_get(v_fst_1513_, 0);
lean_inc(v_val_1518_);
lean_dec_ref_known(v_fst_1513_, 1);
if (v_isShared_1512_ == 0)
{
lean_ctor_set(v___x_1511_, 0, v_val_1518_);
v___x_1520_ = v___x_1511_;
goto v_reusejp_1519_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_val_1518_);
v___x_1520_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1519_;
}
v_reusejp_1519_:
{
return v___x_1520_;
}
}
}
}
else
{
lean_object* v_a_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1530_; 
v_a_1523_ = lean_ctor_get(v___x_1508_, 0);
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_1508_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1525_ = v___x_1508_;
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_a_1523_);
lean_dec(v___x_1508_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1528_; 
if (v_isShared_1526_ == 0)
{
v___x_1528_ = v___x_1525_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_a_1523_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
}
}
}
}
else
{
lean_object* v_a_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1539_; 
lean_dec_ref(v_c_1478_);
v_a_1532_ = lean_ctor_get(v___x_1494_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1494_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1534_ = v___x_1494_;
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_a_1532_);
lean_dec(v___x_1494_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1537_; 
if (v_isShared_1535_ == 0)
{
v___x_1537_ = v___x_1534_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_a_1532_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0___boxed(lean_object* v_c_1540_, lean_object* v_t_1541_, lean_object* v_init_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0(v_c_1540_, v_t_1541_, v_init_1542_, v___y_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
lean_dec(v___y_1548_);
lean_dec_ref(v___y_1547_);
lean_dec(v___y_1546_);
lean_dec_ref(v___y_1545_);
lean_dec(v___y_1544_);
lean_dec(v___y_1543_);
lean_dec_ref(v_t_1541_);
return v_res_1554_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0(void){
_start:
{
lean_object* v___x_1555_; 
v___x_1555_ = l_Lean_instInhabitedPersistentArray_default___redArg();
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq(lean_object* v_c_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v_a_1566_){
_start:
{
lean_object* v_p_1568_; 
v_p_1568_ = lean_ctor_get(v_c_1556_, 0);
if (lean_obj_tag(v_p_1568_) == 1)
{
lean_object* v_k_1569_; lean_object* v_v_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v_k_1569_ = lean_ctor_get(v_p_1568_, 0);
v_v_1570_ = lean_ctor_get(v_p_1568_, 1);
v___x_1571_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0);
v___x_1572_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_1557_, v_a_1565_);
if (lean_obj_tag(v___x_1572_) == 0)
{
lean_object* v_a_1573_; lean_object* v___y_1575_; lean_object* v___x_1601_; uint8_t v___x_1602_; 
v_a_1573_ = lean_ctor_get(v___x_1572_, 0);
lean_inc(v_a_1573_);
lean_dec_ref_known(v___x_1572_, 1);
v___x_1601_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9);
v___x_1602_ = lean_int_dec_lt(v_k_1569_, v___x_1601_);
if (v___x_1602_ == 0)
{
lean_object* v_lowers_1603_; lean_object* v_size_1604_; uint8_t v___x_1605_; 
v_lowers_1603_ = lean_ctor_get(v_a_1573_, 6);
lean_inc_ref(v_lowers_1603_);
lean_dec(v_a_1573_);
v_size_1604_ = lean_ctor_get(v_lowers_1603_, 2);
v___x_1605_ = lean_nat_dec_lt(v_v_1570_, v_size_1604_);
if (v___x_1605_ == 0)
{
lean_object* v___x_1606_; 
lean_dec_ref(v_lowers_1603_);
v___x_1606_ = l_outOfBounds___redArg(v___x_1571_);
v___y_1575_ = v___x_1606_;
goto v___jp_1574_;
}
else
{
lean_object* v___x_1607_; 
v___x_1607_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1571_, v_lowers_1603_, v_v_1570_);
lean_dec_ref(v_lowers_1603_);
v___y_1575_ = v___x_1607_;
goto v___jp_1574_;
}
}
else
{
lean_object* v_uppers_1608_; lean_object* v_size_1609_; uint8_t v___x_1610_; 
v_uppers_1608_ = lean_ctor_get(v_a_1573_, 7);
lean_inc_ref(v_uppers_1608_);
lean_dec(v_a_1573_);
v_size_1609_ = lean_ctor_get(v_uppers_1608_, 2);
v___x_1610_ = lean_nat_dec_lt(v_v_1570_, v_size_1609_);
if (v___x_1610_ == 0)
{
lean_object* v___x_1611_; 
lean_dec_ref(v_uppers_1608_);
v___x_1611_ = l_outOfBounds___redArg(v___x_1571_);
v___y_1575_ = v___x_1611_;
goto v___jp_1574_;
}
else
{
lean_object* v___x_1612_; 
v___x_1612_ = l_Lean_PersistentArray_get_x21___redArg(v___x_1571_, v_uppers_1608_, v_v_1570_);
lean_dec_ref(v_uppers_1608_);
v___y_1575_ = v___x_1612_;
goto v___jp_1574_;
}
}
v___jp_1574_:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1576_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0_spec__0_spec__2___closed__0));
v___x_1577_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq_spec__0(v_c_1556_, v___y_1575_, v___x_1576_, v_a_1557_, v_a_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_);
lean_dec_ref(v___y_1575_);
if (lean_obj_tag(v___x_1577_) == 0)
{
lean_object* v_a_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1592_; 
v_a_1578_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1592_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1580_ = v___x_1577_;
v_isShared_1581_ = v_isSharedCheck_1592_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_dec(v___x_1577_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1592_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v_fst_1582_; 
v_fst_1582_ = lean_ctor_get(v_a_1578_, 0);
lean_inc(v_fst_1582_);
lean_dec(v_a_1578_);
if (lean_obj_tag(v_fst_1582_) == 0)
{
uint8_t v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1586_; 
v___x_1583_ = 0;
v___x_1584_ = lean_box(v___x_1583_);
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 0, v___x_1584_);
v___x_1586_ = v___x_1580_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v___x_1584_);
v___x_1586_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
return v___x_1586_;
}
}
else
{
lean_object* v_val_1588_; lean_object* v___x_1590_; 
v_val_1588_ = lean_ctor_get(v_fst_1582_, 0);
lean_inc(v_val_1588_);
lean_dec_ref_known(v_fst_1582_, 1);
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 0, v_val_1588_);
v___x_1590_ = v___x_1580_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v_val_1588_);
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
else
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1600_; 
v_a_1593_ = lean_ctor_get(v___x_1577_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1577_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1595_ = v___x_1577_;
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1577_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1600_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1598_; 
if (v_isShared_1596_ == 0)
{
v___x_1598_ = v___x_1595_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v_a_1593_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
}
}
else
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1620_; 
lean_dec_ref(v_c_1556_);
v_a_1613_ = lean_ctor_get(v___x_1572_, 0);
v_isSharedCheck_1620_ = !lean_is_exclusive(v___x_1572_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1615_ = v___x_1572_;
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1572_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1620_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1618_; 
if (v_isShared_1616_ == 0)
{
v___x_1618_ = v___x_1615_;
goto v_reusejp_1617_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_a_1613_);
v___x_1618_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1617_;
}
v_reusejp_1617_:
{
return v___x_1618_;
}
}
}
}
else
{
lean_object* v___x_1621_; 
v___x_1621_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_1556_, v_a_1557_, v_a_1563_, v_a_1564_, v_a_1565_, v_a_1566_);
return v___x_1621_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___boxed(lean_object* v_c_1622_, lean_object* v_a_1623_, lean_object* v_a_1624_, lean_object* v_a_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_, lean_object* v_a_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq(v_c_1622_, v_a_1623_, v_a_1624_, v_a_1625_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_, v_a_1630_, v_a_1631_, v_a_1632_);
lean_dec(v_a_1632_);
lean_dec_ref(v_a_1631_);
lean_dec(v_a_1630_);
lean_dec_ref(v_a_1629_);
lean_dec(v_a_1628_);
lean_dec_ref(v_a_1627_);
lean_dec(v_a_1626_);
lean_dec_ref(v_a_1625_);
lean_dec(v_a_1624_);
lean_dec(v_a_1623_);
return v_res_1634_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(lean_object* v___x_1635_, lean_object* v_as_1636_, size_t v_i_1637_, size_t v_stop_1638_, lean_object* v_b_1639_){
_start:
{
lean_object* v___y_1641_; uint8_t v___x_1645_; 
v___x_1645_ = lean_usize_dec_eq(v_i_1637_, v_stop_1638_);
if (v___x_1645_ == 0)
{
lean_object* v___x_1646_; lean_object* v_p_1647_; uint8_t v___x_1648_; 
v___x_1646_ = lean_array_uget_borrowed(v_as_1636_, v_i_1637_);
v_p_1647_ = lean_ctor_get(v___x_1646_, 0);
v___x_1648_ = l_Int_Internal_Linear_instBEqPoly_beq(v_p_1647_, v___x_1635_);
if (v___x_1648_ == 0)
{
lean_object* v___x_1649_; 
lean_inc(v___x_1646_);
v___x_1649_ = l_Lean_PersistentArray_push___redArg(v_b_1639_, v___x_1646_);
v___y_1641_ = v___x_1649_;
goto v___jp_1640_;
}
else
{
v___y_1641_ = v_b_1639_;
goto v___jp_1640_;
}
}
else
{
return v_b_1639_;
}
v___jp_1640_:
{
size_t v___x_1642_; size_t v___x_1643_; 
v___x_1642_ = ((size_t)1ULL);
v___x_1643_ = lean_usize_add(v_i_1637_, v___x_1642_);
v_i_1637_ = v___x_1643_;
v_b_1639_ = v___y_1641_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1___boxed(lean_object* v___x_1650_, lean_object* v_as_1651_, lean_object* v_i_1652_, lean_object* v_stop_1653_, lean_object* v_b_1654_){
_start:
{
size_t v_i_boxed_1655_; size_t v_stop_boxed_1656_; lean_object* v_res_1657_; 
v_i_boxed_1655_ = lean_unbox_usize(v_i_1652_);
lean_dec(v_i_1652_);
v_stop_boxed_1656_ = lean_unbox_usize(v_stop_1653_);
lean_dec(v_stop_1653_);
v_res_1657_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1650_, v_as_1651_, v_i_boxed_1655_, v_stop_boxed_1656_, v_b_1654_);
lean_dec_ref(v_as_1651_);
lean_dec_ref(v___x_1650_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(lean_object* v___x_1658_, lean_object* v_x_1659_, lean_object* v_x_1660_){
_start:
{
if (lean_obj_tag(v_x_1659_) == 0)
{
lean_object* v_cs_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; uint8_t v___x_1664_; 
v_cs_1661_ = lean_ctor_get(v_x_1659_, 0);
v___x_1662_ = lean_unsigned_to_nat(0u);
v___x_1663_ = lean_array_get_size(v_cs_1661_);
v___x_1664_ = lean_nat_dec_lt(v___x_1662_, v___x_1663_);
if (v___x_1664_ == 0)
{
return v_x_1660_;
}
else
{
size_t v___x_1665_; size_t v___x_1666_; lean_object* v___x_1667_; 
v___x_1665_ = ((size_t)0ULL);
v___x_1666_ = lean_usize_of_nat(v___x_1663_);
v___x_1667_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1658_, v_cs_1661_, v___x_1665_, v___x_1666_, v_x_1660_);
return v___x_1667_;
}
}
else
{
lean_object* v_vs_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; uint8_t v___x_1671_; 
v_vs_1668_ = lean_ctor_get(v_x_1659_, 0);
v___x_1669_ = lean_unsigned_to_nat(0u);
v___x_1670_ = lean_array_get_size(v_vs_1668_);
v___x_1671_ = lean_nat_dec_lt(v___x_1669_, v___x_1670_);
if (v___x_1671_ == 0)
{
return v_x_1660_;
}
else
{
size_t v___x_1672_; size_t v___x_1673_; lean_object* v___x_1674_; 
v___x_1672_ = ((size_t)0ULL);
v___x_1673_ = lean_usize_of_nat(v___x_1670_);
v___x_1674_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1658_, v_vs_1668_, v___x_1672_, v___x_1673_, v_x_1660_);
return v___x_1674_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(lean_object* v___x_1675_, lean_object* v_as_1676_, size_t v_i_1677_, size_t v_stop_1678_, lean_object* v_b_1679_){
_start:
{
uint8_t v___x_1680_; 
v___x_1680_ = lean_usize_dec_eq(v_i_1677_, v_stop_1678_);
if (v___x_1680_ == 0)
{
lean_object* v___x_1681_; lean_object* v___x_1682_; size_t v___x_1683_; size_t v___x_1684_; 
v___x_1681_ = lean_array_uget_borrowed(v_as_1676_, v_i_1677_);
v___x_1682_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(v___x_1675_, v___x_1681_, v_b_1679_);
v___x_1683_ = ((size_t)1ULL);
v___x_1684_ = lean_usize_add(v_i_1677_, v___x_1683_);
v_i_1677_ = v___x_1684_;
v_b_1679_ = v___x_1682_;
goto _start;
}
else
{
return v_b_1679_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v___x_1686_, lean_object* v_as_1687_, lean_object* v_i_1688_, lean_object* v_stop_1689_, lean_object* v_b_1690_){
_start:
{
size_t v_i_boxed_1691_; size_t v_stop_boxed_1692_; lean_object* v_res_1693_; 
v_i_boxed_1691_ = lean_unbox_usize(v_i_1688_);
lean_dec(v_i_1688_);
v_stop_boxed_1692_ = lean_unbox_usize(v_stop_1689_);
lean_dec(v_stop_1689_);
v_res_1693_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1686_, v_as_1687_, v_i_boxed_1691_, v_stop_boxed_1692_, v_b_1690_);
lean_dec_ref(v_as_1687_);
lean_dec_ref(v___x_1686_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2___boxed(lean_object* v___x_1694_, lean_object* v_x_1695_, lean_object* v_x_1696_){
_start:
{
lean_object* v_res_1697_; 
v_res_1697_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(v___x_1694_, v_x_1695_, v_x_1696_);
lean_dec_ref(v_x_1695_);
lean_dec_ref(v___x_1694_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(lean_object* v___x_1698_, lean_object* v_x_1699_, size_t v_x_1700_, size_t v_x_1701_, lean_object* v_x_1702_){
_start:
{
if (lean_obj_tag(v_x_1699_) == 0)
{
lean_object* v_cs_1703_; lean_object* v___x_1704_; size_t v___x_1705_; lean_object* v_j_1706_; lean_object* v___x_1707_; size_t v___x_1708_; size_t v___x_1709_; size_t v___x_1710_; size_t v___x_1711_; size_t v___x_1712_; size_t v___x_1713_; lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; uint8_t v___x_1718_; 
v_cs_1703_ = lean_ctor_get(v_x_1699_, 0);
v___x_1704_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_erase_spec__0_spec__0___closed__0);
v___x_1705_ = lean_usize_shift_right(v_x_1700_, v_x_1701_);
v_j_1706_ = lean_usize_to_nat(v___x_1705_);
v___x_1707_ = lean_array_get_borrowed(v___x_1704_, v_cs_1703_, v_j_1706_);
v___x_1708_ = ((size_t)1ULL);
v___x_1709_ = lean_usize_shift_left(v___x_1708_, v_x_1701_);
v___x_1710_ = lean_usize_sub(v___x_1709_, v___x_1708_);
v___x_1711_ = lean_usize_land(v_x_1700_, v___x_1710_);
v___x_1712_ = ((size_t)5ULL);
v___x_1713_ = lean_usize_sub(v_x_1701_, v___x_1712_);
v___x_1714_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(v___x_1698_, v___x_1707_, v___x_1711_, v___x_1713_, v_x_1702_);
v___x_1715_ = lean_unsigned_to_nat(1u);
v___x_1716_ = lean_nat_add(v_j_1706_, v___x_1715_);
lean_dec(v_j_1706_);
v___x_1717_ = lean_array_get_size(v_cs_1703_);
v___x_1718_ = lean_nat_dec_lt(v___x_1716_, v___x_1717_);
if (v___x_1718_ == 0)
{
lean_dec(v___x_1716_);
return v___x_1714_;
}
else
{
size_t v___x_1719_; size_t v___x_1720_; lean_object* v___x_1721_; 
v___x_1719_ = lean_usize_of_nat(v___x_1716_);
lean_dec(v___x_1716_);
v___x_1720_ = lean_usize_of_nat(v___x_1717_);
v___x_1721_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0_spec__1(v___x_1698_, v_cs_1703_, v___x_1719_, v___x_1720_, v___x_1714_);
return v___x_1721_;
}
}
else
{
lean_object* v_vs_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; uint8_t v___x_1725_; 
v_vs_1722_ = lean_ctor_get(v_x_1699_, 0);
v___x_1723_ = lean_usize_to_nat(v_x_1700_);
v___x_1724_ = lean_array_get_size(v_vs_1722_);
v___x_1725_ = lean_nat_dec_lt(v___x_1723_, v___x_1724_);
if (v___x_1725_ == 0)
{
lean_dec(v___x_1723_);
return v_x_1702_;
}
else
{
size_t v___x_1726_; size_t v___x_1727_; lean_object* v___x_1728_; 
v___x_1726_ = lean_usize_of_nat(v___x_1723_);
lean_dec(v___x_1723_);
v___x_1727_ = lean_usize_of_nat(v___x_1724_);
v___x_1728_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1698_, v_vs_1722_, v___x_1726_, v___x_1727_, v_x_1702_);
return v___x_1728_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0___boxed(lean_object* v___x_1729_, lean_object* v_x_1730_, lean_object* v_x_1731_, lean_object* v_x_1732_, lean_object* v_x_1733_){
_start:
{
size_t v_x_20995__boxed_1734_; size_t v_x_20996__boxed_1735_; lean_object* v_res_1736_; 
v_x_20995__boxed_1734_ = lean_unbox_usize(v_x_1731_);
lean_dec(v_x_1731_);
v_x_20996__boxed_1735_ = lean_unbox_usize(v_x_1732_);
lean_dec(v_x_1732_);
v_res_1736_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(v___x_1729_, v_x_1730_, v_x_20995__boxed_1734_, v_x_20996__boxed_1735_, v_x_1733_);
lean_dec_ref(v_x_1730_);
lean_dec_ref(v___x_1729_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(lean_object* v___x_1737_, lean_object* v_t_1738_, lean_object* v_init_1739_, lean_object* v_start_1740_){
_start:
{
lean_object* v___x_1741_; uint8_t v___x_1742_; 
v___x_1741_ = lean_unsigned_to_nat(0u);
v___x_1742_ = lean_nat_dec_eq(v_start_1740_, v___x_1741_);
if (v___x_1742_ == 0)
{
lean_object* v_root_1743_; lean_object* v_tail_1744_; size_t v_shift_1745_; lean_object* v_tailOff_1746_; uint8_t v___x_1747_; 
v_root_1743_ = lean_ctor_get(v_t_1738_, 0);
v_tail_1744_ = lean_ctor_get(v_t_1738_, 1);
v_shift_1745_ = lean_ctor_get_usize(v_t_1738_, 4);
v_tailOff_1746_ = lean_ctor_get(v_t_1738_, 3);
v___x_1747_ = lean_nat_dec_le(v_tailOff_1746_, v_start_1740_);
if (v___x_1747_ == 0)
{
size_t v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; uint8_t v___x_1751_; 
v___x_1748_ = lean_usize_of_nat(v_start_1740_);
v___x_1749_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__0(v___x_1737_, v_root_1743_, v___x_1748_, v_shift_1745_, v_init_1739_);
v___x_1750_ = lean_array_get_size(v_tail_1744_);
v___x_1751_ = lean_nat_dec_lt(v___x_1741_, v___x_1750_);
if (v___x_1751_ == 0)
{
return v___x_1749_;
}
else
{
size_t v___x_1752_; size_t v___x_1753_; lean_object* v___x_1754_; 
v___x_1752_ = ((size_t)0ULL);
v___x_1753_ = lean_usize_of_nat(v___x_1750_);
v___x_1754_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1737_, v_tail_1744_, v___x_1752_, v___x_1753_, v___x_1749_);
return v___x_1754_;
}
}
else
{
lean_object* v___x_1755_; lean_object* v___x_1756_; uint8_t v___x_1757_; 
v___x_1755_ = lean_nat_sub(v_start_1740_, v_tailOff_1746_);
v___x_1756_ = lean_array_get_size(v_tail_1744_);
v___x_1757_ = lean_nat_dec_lt(v___x_1755_, v___x_1756_);
if (v___x_1757_ == 0)
{
lean_dec(v___x_1755_);
return v_init_1739_;
}
else
{
size_t v___x_1758_; size_t v___x_1759_; lean_object* v___x_1760_; 
v___x_1758_ = lean_usize_of_nat(v___x_1755_);
lean_dec(v___x_1755_);
v___x_1759_ = lean_usize_of_nat(v___x_1756_);
v___x_1760_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1737_, v_tail_1744_, v___x_1758_, v___x_1759_, v_init_1739_);
return v___x_1760_;
}
}
}
else
{
lean_object* v_root_1761_; lean_object* v_tail_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; uint8_t v___x_1765_; 
v_root_1761_ = lean_ctor_get(v_t_1738_, 0);
v_tail_1762_ = lean_ctor_get(v_t_1738_, 1);
v___x_1763_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__2(v___x_1737_, v_root_1761_, v_init_1739_);
v___x_1764_ = lean_array_get_size(v_tail_1762_);
v___x_1765_ = lean_nat_dec_lt(v___x_1741_, v___x_1764_);
if (v___x_1765_ == 0)
{
return v___x_1763_;
}
else
{
size_t v___x_1766_; size_t v___x_1767_; lean_object* v___x_1768_; 
v___x_1766_ = ((size_t)0ULL);
v___x_1767_ = lean_usize_of_nat(v___x_1764_);
v___x_1768_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0_spec__1(v___x_1737_, v_tail_1762_, v___x_1766_, v___x_1767_, v___x_1763_);
return v___x_1768_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0___boxed(lean_object* v___x_1769_, lean_object* v_t_1770_, lean_object* v_init_1771_, lean_object* v_start_1772_){
_start:
{
lean_object* v_res_1773_; 
v_res_1773_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(v___x_1769_, v_t_1770_, v_init_1771_, v_start_1772_);
lean_dec(v_start_1772_);
lean_dec_ref(v_t_1770_);
lean_dec_ref(v___x_1769_);
return v_res_1773_;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1774_ = lean_unsigned_to_nat(32u);
v___x_1775_ = lean_mk_empty_array_with_capacity(v___x_1774_);
v___x_1776_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1775_);
return v___x_1776_;
}
}
static lean_object* _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1(void){
_start:
{
size_t v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1777_ = ((size_t)5ULL);
v___x_1778_ = lean_unsigned_to_nat(0u);
v___x_1779_ = lean_unsigned_to_nat(32u);
v___x_1780_ = lean_mk_empty_array_with_capacity(v___x_1779_);
v___x_1781_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__0);
v___x_1782_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1782_, 0, v___x_1781_);
lean_ctor_set(v___x_1782_, 1, v___x_1780_);
lean_ctor_set(v___x_1782_, 2, v___x_1778_);
lean_ctor_set(v___x_1782_, 3, v___x_1778_);
lean_ctor_set_usize(v___x_1782_, 4, v___x_1777_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(lean_object* v___x_1783_, lean_object* v_x_1784_, size_t v_x_1785_, size_t v_x_1786_){
_start:
{
if (lean_obj_tag(v_x_1784_) == 0)
{
lean_object* v_cs_1787_; size_t v_j_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; uint8_t v___x_1791_; 
v_cs_1787_ = lean_ctor_get(v_x_1784_, 0);
v_j_1788_ = lean_usize_shift_right(v_x_1785_, v_x_1786_);
v___x_1789_ = lean_usize_to_nat(v_j_1788_);
v___x_1790_ = lean_array_get_size(v_cs_1787_);
v___x_1791_ = lean_nat_dec_lt(v___x_1789_, v___x_1790_);
if (v___x_1791_ == 0)
{
lean_dec(v___x_1789_);
return v_x_1784_;
}
else
{
lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1809_; 
lean_inc_ref(v_cs_1787_);
v_isSharedCheck_1809_ = !lean_is_exclusive(v_x_1784_);
if (v_isSharedCheck_1809_ == 0)
{
lean_object* v_unused_1810_; 
v_unused_1810_ = lean_ctor_get(v_x_1784_, 0);
lean_dec(v_unused_1810_);
v___x_1793_ = v_x_1784_;
v_isShared_1794_ = v_isSharedCheck_1809_;
goto v_resetjp_1792_;
}
else
{
lean_dec(v_x_1784_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1809_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
size_t v___x_1795_; size_t v___x_1796_; size_t v___x_1797_; size_t v_i_1798_; size_t v___x_1799_; size_t v_shift_1800_; lean_object* v_v_1801_; lean_object* v___x_1802_; lean_object* v_xs_x27_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1807_; 
v___x_1795_ = ((size_t)1ULL);
v___x_1796_ = lean_usize_shift_left(v___x_1795_, v_x_1786_);
v___x_1797_ = lean_usize_sub(v___x_1796_, v___x_1795_);
v_i_1798_ = lean_usize_land(v_x_1785_, v___x_1797_);
v___x_1799_ = ((size_t)5ULL);
v_shift_1800_ = lean_usize_sub(v_x_1786_, v___x_1799_);
v_v_1801_ = lean_array_fget(v_cs_1787_, v___x_1789_);
v___x_1802_ = lean_box(0);
v_xs_x27_1803_ = lean_array_fset(v_cs_1787_, v___x_1789_, v___x_1802_);
v___x_1804_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(v___x_1783_, v_v_1801_, v_i_1798_, v_shift_1800_);
v___x_1805_ = lean_array_fset(v_xs_x27_1803_, v___x_1789_, v___x_1804_);
lean_dec(v___x_1789_);
if (v_isShared_1794_ == 0)
{
lean_ctor_set(v___x_1793_, 0, v___x_1805_);
v___x_1807_ = v___x_1793_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v___x_1805_);
v___x_1807_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
return v___x_1807_;
}
}
}
}
else
{
lean_object* v_vs_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; uint8_t v___x_1814_; 
v_vs_1811_ = lean_ctor_get(v_x_1784_, 0);
v___x_1812_ = lean_usize_to_nat(v_x_1785_);
v___x_1813_ = lean_array_get_size(v_vs_1811_);
v___x_1814_ = lean_nat_dec_lt(v___x_1812_, v___x_1813_);
if (v___x_1814_ == 0)
{
lean_dec(v___x_1812_);
return v_x_1784_;
}
else
{
lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1828_; 
lean_inc_ref(v_vs_1811_);
v_isSharedCheck_1828_ = !lean_is_exclusive(v_x_1784_);
if (v_isSharedCheck_1828_ == 0)
{
lean_object* v_unused_1829_; 
v_unused_1829_ = lean_ctor_get(v_x_1784_, 0);
lean_dec(v_unused_1829_);
v___x_1816_ = v_x_1784_;
v_isShared_1817_ = v_isSharedCheck_1828_;
goto v_resetjp_1815_;
}
else
{
lean_dec(v_x_1784_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1828_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
lean_object* v_v_1818_; lean_object* v___x_1819_; lean_object* v_xs_x27_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; lean_object* v___x_1826_; 
v_v_1818_ = lean_array_fget(v_vs_1811_, v___x_1812_);
v___x_1819_ = lean_box(0);
v_xs_x27_1820_ = lean_array_fset(v_vs_1811_, v___x_1812_, v___x_1819_);
v___x_1821_ = lean_unsigned_to_nat(0u);
v___x_1822_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1);
v___x_1823_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(v___x_1783_, v_v_1818_, v___x_1822_, v___x_1821_);
lean_dec(v_v_1818_);
v___x_1824_ = lean_array_fset(v_xs_x27_1820_, v___x_1812_, v___x_1823_);
lean_dec(v___x_1812_);
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 0, v___x_1824_);
v___x_1826_ = v___x_1816_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v___x_1824_);
v___x_1826_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
return v___x_1826_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___boxed(lean_object* v___x_1830_, lean_object* v_x_1831_, lean_object* v_x_1832_, lean_object* v_x_1833_){
_start:
{
size_t v_x_21127__boxed_1834_; size_t v_x_21128__boxed_1835_; lean_object* v_res_1836_; 
v_x_21127__boxed_1834_ = lean_unbox_usize(v_x_1832_);
lean_dec(v_x_1832_);
v_x_21128__boxed_1835_ = lean_unbox_usize(v_x_1833_);
lean_dec(v_x_1833_);
v_res_1836_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(v___x_1830_, v_x_1831_, v_x_21127__boxed_1834_, v_x_21128__boxed_1835_);
lean_dec_ref(v___x_1830_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1(lean_object* v___x_1837_, lean_object* v_t_1838_, lean_object* v_i_1839_){
_start:
{
lean_object* v_root_1840_; lean_object* v_tail_1841_; lean_object* v_size_1842_; size_t v_shift_1843_; lean_object* v_tailOff_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_1872_; 
v_root_1840_ = lean_ctor_get(v_t_1838_, 0);
v_tail_1841_ = lean_ctor_get(v_t_1838_, 1);
v_size_1842_ = lean_ctor_get(v_t_1838_, 2);
v_shift_1843_ = lean_ctor_get_usize(v_t_1838_, 4);
v_tailOff_1844_ = lean_ctor_get(v_t_1838_, 3);
v_isSharedCheck_1872_ = !lean_is_exclusive(v_t_1838_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1846_ = v_t_1838_;
v_isShared_1847_ = v_isSharedCheck_1872_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_tailOff_1844_);
lean_inc(v_size_1842_);
lean_inc(v_tail_1841_);
lean_inc(v_root_1840_);
lean_dec(v_t_1838_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_1872_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
uint8_t v___x_1848_; 
v___x_1848_ = lean_nat_dec_le(v_tailOff_1844_, v_i_1839_);
if (v___x_1848_ == 0)
{
size_t v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1852_; 
v___x_1849_ = lean_usize_of_nat(v_i_1839_);
v___x_1850_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4(v___x_1837_, v_root_1840_, v___x_1849_, v_shift_1843_);
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 0, v___x_1850_);
v___x_1852_ = v___x_1846_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v___x_1850_);
lean_ctor_set(v_reuseFailAlloc_1853_, 1, v_tail_1841_);
lean_ctor_set(v_reuseFailAlloc_1853_, 2, v_size_1842_);
lean_ctor_set(v_reuseFailAlloc_1853_, 3, v_tailOff_1844_);
lean_ctor_set_usize(v_reuseFailAlloc_1853_, 4, v_shift_1843_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
else
{
lean_object* v___x_1854_; lean_object* v___x_1855_; uint8_t v___x_1856_; 
v___x_1854_ = lean_nat_sub(v_i_1839_, v_tailOff_1844_);
v___x_1855_ = lean_array_get_size(v_tail_1841_);
v___x_1856_ = lean_nat_dec_lt(v___x_1854_, v___x_1855_);
if (v___x_1856_ == 0)
{
lean_object* v___x_1858_; 
lean_dec(v___x_1854_);
if (v_isShared_1847_ == 0)
{
v___x_1858_ = v___x_1846_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_root_1840_);
lean_ctor_set(v_reuseFailAlloc_1859_, 1, v_tail_1841_);
lean_ctor_set(v_reuseFailAlloc_1859_, 2, v_size_1842_);
lean_ctor_set(v_reuseFailAlloc_1859_, 3, v_tailOff_1844_);
lean_ctor_set_usize(v_reuseFailAlloc_1859_, 4, v_shift_1843_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
else
{
lean_object* v_v_1860_; lean_object* v___x_1861_; lean_object* v_xs_x27_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1870_; 
v_v_1860_ = lean_array_fget(v_tail_1841_, v___x_1854_);
v___x_1861_ = lean_box(0);
v_xs_x27_1862_ = lean_array_fset(v_tail_1841_, v___x_1854_, v___x_1861_);
v___x_1863_ = lean_unsigned_to_nat(32u);
v___x_1864_ = lean_mk_empty_array_with_capacity(v___x_1863_);
lean_dec_ref(v___x_1864_);
v___x_1865_ = lean_unsigned_to_nat(0u);
v___x_1866_ = lean_obj_once(&l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1, &l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1_once, _init_l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1_spec__4___closed__1);
v___x_1867_ = l_Lean_PersistentArray_foldlM___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__0(v___x_1837_, v_v_1860_, v___x_1866_, v___x_1865_);
lean_dec(v_v_1860_);
v___x_1868_ = lean_array_fset(v_xs_x27_1862_, v___x_1854_, v___x_1867_);
lean_dec(v___x_1854_);
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 1, v___x_1868_);
v___x_1870_ = v___x_1846_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_root_1840_);
lean_ctor_set(v_reuseFailAlloc_1871_, 1, v___x_1868_);
lean_ctor_set(v_reuseFailAlloc_1871_, 2, v_size_1842_);
lean_ctor_set(v_reuseFailAlloc_1871_, 3, v_tailOff_1844_);
lean_ctor_set_usize(v_reuseFailAlloc_1871_, 4, v_shift_1843_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1___boxed(lean_object* v___x_1873_, lean_object* v_t_1874_, lean_object* v_i_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1(v___x_1873_, v_t_1874_, v_i_1875_);
lean_dec(v_i_1875_);
lean_dec_ref(v___x_1873_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0(lean_object* v_p_1877_, lean_object* v_x_1878_, lean_object* v_s_1879_){
_start:
{
lean_object* v_vars_1880_; lean_object* v_varMap_1881_; lean_object* v_varsHistory_1882_; lean_object* v_natToIntMap_1883_; lean_object* v_natDef_1884_; lean_object* v_dvds_1885_; lean_object* v_lowers_1886_; lean_object* v_uppers_1887_; lean_object* v_diseqs_1888_; lean_object* v_elimEqs_1889_; lean_object* v_elimStack_1890_; lean_object* v_occurs_1891_; lean_object* v_assignment_1892_; lean_object* v_nextCnstrId_1893_; uint8_t v_caseSplits_1894_; lean_object* v_steps_1895_; lean_object* v_penalties_1896_; lean_object* v_numReorderRequests_1897_; lean_object* v_conflict_x3f_1898_; lean_object* v_diseqSplits_1899_; lean_object* v_divMod_1900_; uint8_t v_usedCommRing_1901_; lean_object* v_nonlinearOccs_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1910_; 
v_vars_1880_ = lean_ctor_get(v_s_1879_, 0);
v_varMap_1881_ = lean_ctor_get(v_s_1879_, 1);
v_varsHistory_1882_ = lean_ctor_get(v_s_1879_, 2);
v_natToIntMap_1883_ = lean_ctor_get(v_s_1879_, 3);
v_natDef_1884_ = lean_ctor_get(v_s_1879_, 4);
v_dvds_1885_ = lean_ctor_get(v_s_1879_, 5);
v_lowers_1886_ = lean_ctor_get(v_s_1879_, 6);
v_uppers_1887_ = lean_ctor_get(v_s_1879_, 7);
v_diseqs_1888_ = lean_ctor_get(v_s_1879_, 8);
v_elimEqs_1889_ = lean_ctor_get(v_s_1879_, 9);
v_elimStack_1890_ = lean_ctor_get(v_s_1879_, 10);
v_occurs_1891_ = lean_ctor_get(v_s_1879_, 11);
v_assignment_1892_ = lean_ctor_get(v_s_1879_, 12);
v_nextCnstrId_1893_ = lean_ctor_get(v_s_1879_, 13);
v_caseSplits_1894_ = lean_ctor_get_uint8(v_s_1879_, sizeof(void*)*21);
v_steps_1895_ = lean_ctor_get(v_s_1879_, 14);
v_penalties_1896_ = lean_ctor_get(v_s_1879_, 15);
v_numReorderRequests_1897_ = lean_ctor_get(v_s_1879_, 16);
v_conflict_x3f_1898_ = lean_ctor_get(v_s_1879_, 17);
v_diseqSplits_1899_ = lean_ctor_get(v_s_1879_, 18);
v_divMod_1900_ = lean_ctor_get(v_s_1879_, 19);
v_usedCommRing_1901_ = lean_ctor_get_uint8(v_s_1879_, sizeof(void*)*21 + 1);
v_nonlinearOccs_1902_ = lean_ctor_get(v_s_1879_, 20);
v_isSharedCheck_1910_ = !lean_is_exclusive(v_s_1879_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1904_ = v_s_1879_;
v_isShared_1905_ = v_isSharedCheck_1910_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_nonlinearOccs_1902_);
lean_inc(v_divMod_1900_);
lean_inc(v_diseqSplits_1899_);
lean_inc(v_conflict_x3f_1898_);
lean_inc(v_numReorderRequests_1897_);
lean_inc(v_penalties_1896_);
lean_inc(v_steps_1895_);
lean_inc(v_nextCnstrId_1893_);
lean_inc(v_assignment_1892_);
lean_inc(v_occurs_1891_);
lean_inc(v_elimStack_1890_);
lean_inc(v_elimEqs_1889_);
lean_inc(v_diseqs_1888_);
lean_inc(v_uppers_1887_);
lean_inc(v_lowers_1886_);
lean_inc(v_dvds_1885_);
lean_inc(v_natDef_1884_);
lean_inc(v_natToIntMap_1883_);
lean_inc(v_varsHistory_1882_);
lean_inc(v_varMap_1881_);
lean_inc(v_vars_1880_);
lean_dec(v_s_1879_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1910_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1906_; lean_object* v___x_1908_; 
v___x_1906_ = l_Lean_PersistentArray_modify___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__1(v_p_1877_, v_diseqs_1888_, v_x_1878_);
if (v_isShared_1905_ == 0)
{
lean_ctor_set(v___x_1904_, 8, v___x_1906_);
v___x_1908_ = v___x_1904_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(0, 21, 2);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_vars_1880_);
lean_ctor_set(v_reuseFailAlloc_1909_, 1, v_varMap_1881_);
lean_ctor_set(v_reuseFailAlloc_1909_, 2, v_varsHistory_1882_);
lean_ctor_set(v_reuseFailAlloc_1909_, 3, v_natToIntMap_1883_);
lean_ctor_set(v_reuseFailAlloc_1909_, 4, v_natDef_1884_);
lean_ctor_set(v_reuseFailAlloc_1909_, 5, v_dvds_1885_);
lean_ctor_set(v_reuseFailAlloc_1909_, 6, v_lowers_1886_);
lean_ctor_set(v_reuseFailAlloc_1909_, 7, v_uppers_1887_);
lean_ctor_set(v_reuseFailAlloc_1909_, 8, v___x_1906_);
lean_ctor_set(v_reuseFailAlloc_1909_, 9, v_elimEqs_1889_);
lean_ctor_set(v_reuseFailAlloc_1909_, 10, v_elimStack_1890_);
lean_ctor_set(v_reuseFailAlloc_1909_, 11, v_occurs_1891_);
lean_ctor_set(v_reuseFailAlloc_1909_, 12, v_assignment_1892_);
lean_ctor_set(v_reuseFailAlloc_1909_, 13, v_nextCnstrId_1893_);
lean_ctor_set(v_reuseFailAlloc_1909_, 14, v_steps_1895_);
lean_ctor_set(v_reuseFailAlloc_1909_, 15, v_penalties_1896_);
lean_ctor_set(v_reuseFailAlloc_1909_, 16, v_numReorderRequests_1897_);
lean_ctor_set(v_reuseFailAlloc_1909_, 17, v_conflict_x3f_1898_);
lean_ctor_set(v_reuseFailAlloc_1909_, 18, v_diseqSplits_1899_);
lean_ctor_set(v_reuseFailAlloc_1909_, 19, v_divMod_1900_);
lean_ctor_set(v_reuseFailAlloc_1909_, 20, v_nonlinearOccs_1902_);
lean_ctor_set_uint8(v_reuseFailAlloc_1909_, sizeof(void*)*21, v_caseSplits_1894_);
lean_ctor_set_uint8(v_reuseFailAlloc_1909_, sizeof(void*)*21 + 1, v_usedCommRing_1901_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed(lean_object* v_p_1911_, lean_object* v_x_1912_, lean_object* v_s_1913_){
_start:
{
lean_object* v_res_1914_; 
v_res_1914_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0(v_p_1911_, v_x_1912_, v_s_1913_);
lean_dec(v_x_1912_);
lean_dec_ref(v_p_1911_);
return v_res_1914_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0(void){
_start:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1915_ = lean_unsigned_to_nat(1u);
v___x_1916_ = lean_nat_to_int(v___x_1915_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(lean_object* v_c_1923_, lean_object* v_x_1924_, lean_object* v_as_1925_, size_t v_sz_1926_, size_t v_i_1927_, lean_object* v_b_1928_, lean_object* v___y_1929_){
_start:
{
uint8_t v___x_1931_; 
v___x_1931_ = lean_usize_dec_lt(v_i_1927_, v_sz_1926_);
if (v___x_1931_ == 0)
{
lean_object* v___x_1932_; 
lean_dec(v_x_1924_);
lean_dec_ref(v_c_1923_);
v___x_1932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1932_, 0, v_b_1928_);
return v___x_1932_;
}
else
{
lean_object* v_snd_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1978_; 
v_snd_1933_ = lean_ctor_get(v_b_1928_, 1);
v_isSharedCheck_1978_ = !lean_is_exclusive(v_b_1928_);
if (v_isSharedCheck_1978_ == 0)
{
lean_object* v_unused_1979_; 
v_unused_1979_ = lean_ctor_get(v_b_1928_, 0);
lean_dec(v_unused_1979_);
v___x_1935_ = v_b_1928_;
v_isShared_1936_ = v_isSharedCheck_1978_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_snd_1933_);
lean_dec(v_b_1928_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1978_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v_p_1937_; lean_object* v_a_1938_; lean_object* v_p_1939_; lean_object* v___x_1940_; lean_object* v___f_1941_; uint8_t v___x_1972_; 
v_p_1937_ = lean_ctor_get(v_c_1923_, 0);
v_a_1938_ = lean_array_uget_borrowed(v_as_1925_, v_i_1927_);
v_p_1939_ = lean_ctor_get(v_a_1938_, 0);
v___x_1940_ = lean_box(0);
lean_inc(v_x_1924_);
lean_inc_ref(v_p_1939_);
v___f_1941_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1941_, 0, v_p_1939_);
lean_closure_set(v___f_1941_, 1, v_x_1924_);
v___x_1972_ = l_Int_Internal_Linear_instBEqPoly_beq(v_p_1937_, v_p_1939_);
if (v___x_1972_ == 0)
{
uint8_t v___x_1973_; 
v___x_1973_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_1937_, v_p_1939_);
if (v___x_1973_ == 0)
{
lean_object* v___x_1974_; size_t v___x_1975_; size_t v___x_1976_; 
lean_dec_ref(v___f_1941_);
lean_del_object(v___x_1935_);
lean_dec(v_snd_1933_);
v___x_1974_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__2));
v___x_1975_ = ((size_t)1ULL);
v___x_1976_ = lean_usize_add(v_i_1927_, v___x_1975_);
v_i_1927_ = v___x_1976_;
v_b_1928_ = v___x_1974_;
goto _start;
}
else
{
lean_dec(v_x_1924_);
goto v___jp_1942_;
}
}
else
{
lean_dec(v_x_1924_);
goto v___jp_1942_;
}
v___jp_1942_:
{
lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1943_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_1944_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1943_, v___f_1941_, v___y_1929_);
if (lean_obj_tag(v___x_1944_) == 0)
{
lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1962_; 
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_1962_ == 0)
{
lean_object* v_unused_1963_; 
v_unused_1963_ = lean_ctor_get(v___x_1944_, 0);
lean_dec(v_unused_1963_);
v___x_1946_ = v___x_1944_;
v_isShared_1947_ = v_isSharedCheck_1962_;
goto v_resetjp_1945_;
}
else
{
lean_dec(v___x_1944_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1962_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1955_; 
v___x_1948_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0);
lean_inc_ref(v_p_1937_);
v___x_1949_ = l_Int_Internal_Linear_Poly_addConst(v_p_1937_, v___x_1948_);
lean_inc(v_a_1938_);
v___x_1950_ = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(v___x_1950_, 0, v_c_1923_);
lean_ctor_set(v___x_1950_, 1, v_a_1938_);
v___x_1951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1949_);
lean_ctor_set(v___x_1951_, 1, v___x_1950_);
v___x_1952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1951_);
v___x_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1952_);
if (v_isShared_1936_ == 0)
{
lean_ctor_set(v___x_1935_, 1, v___x_1940_);
lean_ctor_set(v___x_1935_, 0, v___x_1953_);
v___x_1955_ = v___x_1935_;
goto v_reusejp_1954_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v___x_1953_);
lean_ctor_set(v_reuseFailAlloc_1961_, 1, v___x_1940_);
v___x_1955_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1954_;
}
v_reusejp_1954_:
{
lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1959_; 
v___x_1956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1956_, 0, v___x_1955_);
v___x_1957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1957_, 0, v___x_1956_);
lean_ctor_set(v___x_1957_, 1, v_snd_1933_);
if (v_isShared_1947_ == 0)
{
lean_ctor_set(v___x_1946_, 0, v___x_1957_);
v___x_1959_ = v___x_1946_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v___x_1957_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
}
else
{
lean_object* v_a_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1971_; 
lean_del_object(v___x_1935_);
lean_dec(v_snd_1933_);
lean_dec_ref(v_c_1923_);
v_a_1964_ = lean_ctor_get(v___x_1944_, 0);
v_isSharedCheck_1971_ = !lean_is_exclusive(v___x_1944_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1966_ = v___x_1944_;
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_a_1964_);
lean_dec(v___x_1944_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1971_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1969_; 
if (v_isShared_1967_ == 0)
{
v___x_1969_ = v___x_1966_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1970_; 
v_reuseFailAlloc_1970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1970_, 0, v_a_1964_);
v___x_1969_ = v_reuseFailAlloc_1970_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
return v___x_1969_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___boxed(lean_object* v_c_1980_, lean_object* v_x_1981_, lean_object* v_as_1982_, lean_object* v_sz_1983_, lean_object* v_i_1984_, lean_object* v_b_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_){
_start:
{
size_t v_sz_boxed_1988_; size_t v_i_boxed_1989_; lean_object* v_res_1990_; 
v_sz_boxed_1988_ = lean_unbox_usize(v_sz_1983_);
lean_dec(v_sz_1983_);
v_i_boxed_1989_ = lean_unbox_usize(v_i_1984_);
lean_dec(v_i_1984_);
v_res_1990_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(v_c_1980_, v_x_1981_, v_as_1982_, v_sz_boxed_1988_, v_i_boxed_1989_, v_b_1985_, v___y_1986_);
lean_dec(v___y_1986_);
lean_dec_ref(v_as_1982_);
return v_res_1990_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7(lean_object* v_c_1997_, lean_object* v_x_1998_, lean_object* v_as_1999_, size_t v_sz_2000_, size_t v_i_2001_, lean_object* v_b_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_, lean_object* v___y_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_){
_start:
{
uint8_t v___x_2014_; 
v___x_2014_ = lean_usize_dec_lt(v_i_2001_, v_sz_2000_);
if (v___x_2014_ == 0)
{
lean_object* v___x_2015_; 
lean_dec(v_x_1998_);
lean_dec_ref(v_c_1997_);
v___x_2015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2015_, 0, v_b_2002_);
return v___x_2015_;
}
else
{
lean_object* v_snd_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2061_; 
v_snd_2016_ = lean_ctor_get(v_b_2002_, 1);
v_isSharedCheck_2061_ = !lean_is_exclusive(v_b_2002_);
if (v_isSharedCheck_2061_ == 0)
{
lean_object* v_unused_2062_; 
v_unused_2062_ = lean_ctor_get(v_b_2002_, 0);
lean_dec(v_unused_2062_);
v___x_2018_ = v_b_2002_;
v_isShared_2019_ = v_isSharedCheck_2061_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_snd_2016_);
lean_dec(v_b_2002_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2061_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v_p_2020_; lean_object* v_a_2021_; lean_object* v_p_2022_; lean_object* v___x_2023_; lean_object* v___f_2024_; uint8_t v___x_2055_; 
v_p_2020_ = lean_ctor_get(v_c_1997_, 0);
v_a_2021_ = lean_array_uget_borrowed(v_as_1999_, v_i_2001_);
v_p_2022_ = lean_ctor_get(v_a_2021_, 0);
v___x_2023_ = lean_box(0);
lean_inc(v_x_1998_);
lean_inc_ref(v_p_2022_);
v___f_2024_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2024_, 0, v_p_2022_);
lean_closure_set(v___f_2024_, 1, v_x_1998_);
v___x_2055_ = l_Int_Internal_Linear_instBEqPoly_beq(v_p_2020_, v_p_2022_);
if (v___x_2055_ == 0)
{
uint8_t v___x_2056_; 
v___x_2056_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_2020_, v_p_2022_);
if (v___x_2056_ == 0)
{
lean_object* v___x_2057_; size_t v___x_2058_; size_t v___x_2059_; lean_object* v___x_2060_; 
lean_dec_ref(v___f_2024_);
lean_del_object(v___x_2018_);
lean_dec(v_snd_2016_);
v___x_2057_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___closed__1));
v___x_2058_ = ((size_t)1ULL);
v___x_2059_ = lean_usize_add(v_i_2001_, v___x_2058_);
v___x_2060_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(v_c_1997_, v_x_1998_, v_as_1999_, v_sz_2000_, v___x_2059_, v___x_2057_, v___y_2003_);
return v___x_2060_;
}
else
{
lean_dec(v_x_1998_);
goto v___jp_2025_;
}
}
else
{
lean_dec(v_x_1998_);
goto v___jp_2025_;
}
v___jp_2025_:
{
lean_object* v___x_2026_; lean_object* v___x_2027_; 
v___x_2026_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2027_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2026_, v___f_2024_, v___y_2003_);
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
v___x_2031_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0);
lean_inc_ref(v_p_2020_);
v___x_2032_ = l_Int_Internal_Linear_Poly_addConst(v_p_2020_, v___x_2031_);
lean_inc(v_a_2021_);
v___x_2033_ = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(v___x_2033_, 0, v_c_1997_);
lean_ctor_set(v___x_2033_, 1, v_a_2021_);
v___x_2034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2032_);
lean_ctor_set(v___x_2034_, 1, v___x_2033_);
v___x_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2034_);
v___x_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2036_, 0, v___x_2035_);
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 1, v___x_2023_);
lean_ctor_set(v___x_2018_, 0, v___x_2036_);
v___x_2038_ = v___x_2018_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v___x_2036_);
lean_ctor_set(v_reuseFailAlloc_2044_, 1, v___x_2023_);
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
lean_ctor_set(v___x_2040_, 1, v_snd_2016_);
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
lean_del_object(v___x_2018_);
lean_dec(v_snd_2016_);
lean_dec_ref(v_c_1997_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___boxed(lean_object** _args){
lean_object* v_c_2063_ = _args[0];
lean_object* v_x_2064_ = _args[1];
lean_object* v_as_2065_ = _args[2];
lean_object* v_sz_2066_ = _args[3];
lean_object* v_i_2067_ = _args[4];
lean_object* v_b_2068_ = _args[5];
lean_object* v___y_2069_ = _args[6];
lean_object* v___y_2070_ = _args[7];
lean_object* v___y_2071_ = _args[8];
lean_object* v___y_2072_ = _args[9];
lean_object* v___y_2073_ = _args[10];
lean_object* v___y_2074_ = _args[11];
lean_object* v___y_2075_ = _args[12];
lean_object* v___y_2076_ = _args[13];
lean_object* v___y_2077_ = _args[14];
lean_object* v___y_2078_ = _args[15];
lean_object* v___y_2079_ = _args[16];
_start:
{
size_t v_sz_boxed_2080_; size_t v_i_boxed_2081_; lean_object* v_res_2082_; 
v_sz_boxed_2080_ = lean_unbox_usize(v_sz_2066_);
lean_dec(v_sz_2066_);
v_i_boxed_2081_ = lean_unbox_usize(v_i_2067_);
lean_dec(v_i_2067_);
v_res_2082_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7(v_c_2063_, v_x_2064_, v_as_2065_, v_sz_boxed_2080_, v_i_boxed_2081_, v_b_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
lean_dec(v___y_2076_);
lean_dec_ref(v___y_2075_);
lean_dec(v___y_2074_);
lean_dec_ref(v___y_2073_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
lean_dec(v___y_2070_);
lean_dec(v___y_2069_);
lean_dec_ref(v_as_2065_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(lean_object* v_c_2089_, lean_object* v_x_2090_, lean_object* v_as_2091_, size_t v_sz_2092_, size_t v_i_2093_, lean_object* v_b_2094_, lean_object* v___y_2095_){
_start:
{
uint8_t v___x_2097_; 
v___x_2097_ = lean_usize_dec_lt(v_i_2093_, v_sz_2092_);
if (v___x_2097_ == 0)
{
lean_object* v___x_2098_; 
lean_dec(v_x_2090_);
lean_dec_ref(v_c_2089_);
v___x_2098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2098_, 0, v_b_2094_);
return v___x_2098_;
}
else
{
lean_object* v_snd_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2145_; 
v_snd_2099_ = lean_ctor_get(v_b_2094_, 1);
v_isSharedCheck_2145_ = !lean_is_exclusive(v_b_2094_);
if (v_isSharedCheck_2145_ == 0)
{
lean_object* v_unused_2146_; 
v_unused_2146_ = lean_ctor_get(v_b_2094_, 0);
lean_dec(v_unused_2146_);
v___x_2101_ = v_b_2094_;
v_isShared_2102_ = v_isSharedCheck_2145_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_snd_2099_);
lean_dec(v_b_2094_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2145_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v_p_2103_; lean_object* v_a_2104_; lean_object* v_p_2105_; lean_object* v___x_2106_; lean_object* v___f_2107_; uint8_t v___x_2139_; 
v_p_2103_ = lean_ctor_get(v_c_2089_, 0);
v_a_2104_ = lean_array_uget_borrowed(v_as_2091_, v_i_2093_);
v_p_2105_ = lean_ctor_get(v_a_2104_, 0);
v___x_2106_ = lean_box(0);
lean_inc(v_x_2090_);
lean_inc_ref(v_p_2105_);
v___f_2107_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2107_, 0, v_p_2105_);
lean_closure_set(v___f_2107_, 1, v_x_2090_);
v___x_2139_ = l_Int_Internal_Linear_instBEqPoly_beq(v_p_2103_, v_p_2105_);
if (v___x_2139_ == 0)
{
uint8_t v___x_2140_; 
v___x_2140_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_2103_, v_p_2105_);
if (v___x_2140_ == 0)
{
lean_object* v___x_2141_; size_t v___x_2142_; size_t v___x_2143_; 
lean_dec_ref(v___f_2107_);
lean_del_object(v___x_2101_);
lean_dec(v_snd_2099_);
v___x_2141_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg___closed__1));
v___x_2142_ = ((size_t)1ULL);
v___x_2143_ = lean_usize_add(v_i_2093_, v___x_2142_);
v_i_2093_ = v___x_2143_;
v_b_2094_ = v___x_2141_;
goto _start;
}
else
{
lean_dec(v_x_2090_);
goto v___jp_2108_;
}
}
else
{
lean_dec(v_x_2090_);
goto v___jp_2108_;
}
v___jp_2108_:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2109_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2110_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2109_, v___f_2107_, v___y_2095_);
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
v___x_2114_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0);
lean_inc_ref(v_p_2103_);
v___x_2115_ = l_Int_Internal_Linear_Poly_addConst(v_p_2103_, v___x_2114_);
lean_inc(v_a_2104_);
v___x_2116_ = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(v___x_2116_, 0, v_c_2089_);
lean_ctor_set(v___x_2116_, 1, v_a_2104_);
v___x_2117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2115_);
lean_ctor_set(v___x_2117_, 1, v___x_2116_);
v___x_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
v___x_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2118_);
if (v_isShared_2102_ == 0)
{
lean_ctor_set(v___x_2101_, 1, v___x_2106_);
lean_ctor_set(v___x_2101_, 0, v___x_2119_);
v___x_2121_ = v___x_2101_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v___x_2119_);
lean_ctor_set(v_reuseFailAlloc_2128_, 1, v___x_2106_);
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
lean_ctor_set(v___x_2124_, 1, v_snd_2099_);
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
lean_del_object(v___x_2101_);
lean_dec(v_snd_2099_);
lean_dec_ref(v_c_2089_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg___boxed(lean_object* v_c_2147_, lean_object* v_x_2148_, lean_object* v_as_2149_, lean_object* v_sz_2150_, lean_object* v_i_2151_, lean_object* v_b_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_){
_start:
{
size_t v_sz_boxed_2155_; size_t v_i_boxed_2156_; lean_object* v_res_2157_; 
v_sz_boxed_2155_ = lean_unbox_usize(v_sz_2150_);
lean_dec(v_sz_2150_);
v_i_boxed_2156_ = lean_unbox_usize(v_i_2151_);
lean_dec(v_i_2151_);
v_res_2157_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(v_c_2147_, v_x_2148_, v_as_2149_, v_sz_boxed_2155_, v_i_boxed_2156_, v_b_2152_, v___y_2153_);
lean_dec(v___y_2153_);
lean_dec_ref(v_as_2149_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9(lean_object* v_c_2161_, lean_object* v_x_2162_, lean_object* v_as_2163_, size_t v_sz_2164_, size_t v_i_2165_, lean_object* v_b_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
uint8_t v___x_2178_; 
v___x_2178_ = lean_usize_dec_lt(v_i_2165_, v_sz_2164_);
if (v___x_2178_ == 0)
{
lean_object* v___x_2179_; 
lean_dec(v_x_2162_);
lean_dec_ref(v_c_2161_);
v___x_2179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2179_, 0, v_b_2166_);
return v___x_2179_;
}
else
{
lean_object* v_snd_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2226_; 
v_snd_2180_ = lean_ctor_get(v_b_2166_, 1);
v_isSharedCheck_2226_ = !lean_is_exclusive(v_b_2166_);
if (v_isSharedCheck_2226_ == 0)
{
lean_object* v_unused_2227_; 
v_unused_2227_ = lean_ctor_get(v_b_2166_, 0);
lean_dec(v_unused_2227_);
v___x_2182_ = v_b_2166_;
v_isShared_2183_ = v_isSharedCheck_2226_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_snd_2180_);
lean_dec(v_b_2166_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2226_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v_p_2184_; lean_object* v_a_2185_; lean_object* v_p_2186_; lean_object* v___x_2187_; lean_object* v___f_2188_; uint8_t v___x_2220_; 
v_p_2184_ = lean_ctor_get(v_c_2161_, 0);
v_a_2185_ = lean_array_uget_borrowed(v_as_2163_, v_i_2165_);
v_p_2186_ = lean_ctor_get(v_a_2185_, 0);
v___x_2187_ = lean_box(0);
lean_inc(v_x_2162_);
lean_inc_ref(v_p_2186_);
v___f_2188_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___lam__0___boxed), 3, 2);
lean_closure_set(v___f_2188_, 0, v_p_2186_);
lean_closure_set(v___f_2188_, 1, v_x_2162_);
v___x_2220_ = l_Int_Internal_Linear_instBEqPoly_beq(v_p_2184_, v_p_2186_);
if (v___x_2220_ == 0)
{
uint8_t v___x_2221_; 
v___x_2221_ = l_Int_Internal_Linear_Poly_isNegEq(v_p_2184_, v_p_2186_);
if (v___x_2221_ == 0)
{
lean_object* v___x_2222_; size_t v___x_2223_; size_t v___x_2224_; lean_object* v___x_2225_; 
lean_dec_ref(v___f_2188_);
lean_del_object(v___x_2182_);
lean_dec(v_snd_2180_);
v___x_2222_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9___closed__0));
v___x_2223_ = ((size_t)1ULL);
v___x_2224_ = lean_usize_add(v_i_2165_, v___x_2223_);
v___x_2225_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(v_c_2161_, v_x_2162_, v_as_2163_, v_sz_2164_, v___x_2224_, v___x_2222_, v___y_2167_);
return v___x_2225_;
}
else
{
lean_dec(v_x_2162_);
goto v___jp_2189_;
}
}
else
{
lean_dec(v_x_2162_);
goto v___jp_2189_;
}
v___jp_2189_:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2190_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_2191_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2190_, v___f_2188_, v___y_2167_);
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
v___x_2195_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0);
lean_inc_ref(v_p_2184_);
v___x_2196_ = l_Int_Internal_Linear_Poly_addConst(v_p_2184_, v___x_2195_);
lean_inc(v_a_2185_);
v___x_2197_ = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(v___x_2197_, 0, v_c_2161_);
lean_ctor_set(v___x_2197_, 1, v_a_2185_);
v___x_2198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2198_, 0, v___x_2196_);
lean_ctor_set(v___x_2198_, 1, v___x_2197_);
v___x_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2198_);
v___x_2200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2199_);
if (v_isShared_2183_ == 0)
{
lean_ctor_set(v___x_2182_, 1, v___x_2187_);
lean_ctor_set(v___x_2182_, 0, v___x_2200_);
v___x_2202_ = v___x_2182_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v___x_2200_);
lean_ctor_set(v_reuseFailAlloc_2209_, 1, v___x_2187_);
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
lean_ctor_set(v___x_2205_, 1, v_snd_2180_);
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
lean_del_object(v___x_2182_);
lean_dec(v_snd_2180_);
lean_dec_ref(v_c_2161_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9___boxed(lean_object** _args){
lean_object* v_c_2228_ = _args[0];
lean_object* v_x_2229_ = _args[1];
lean_object* v_as_2230_ = _args[2];
lean_object* v_sz_2231_ = _args[3];
lean_object* v_i_2232_ = _args[4];
lean_object* v_b_2233_ = _args[5];
lean_object* v___y_2234_ = _args[6];
lean_object* v___y_2235_ = _args[7];
lean_object* v___y_2236_ = _args[8];
lean_object* v___y_2237_ = _args[9];
lean_object* v___y_2238_ = _args[10];
lean_object* v___y_2239_ = _args[11];
lean_object* v___y_2240_ = _args[12];
lean_object* v___y_2241_ = _args[13];
lean_object* v___y_2242_ = _args[14];
lean_object* v___y_2243_ = _args[15];
lean_object* v___y_2244_ = _args[16];
_start:
{
size_t v_sz_boxed_2245_; size_t v_i_boxed_2246_; lean_object* v_res_2247_; 
v_sz_boxed_2245_ = lean_unbox_usize(v_sz_2231_);
lean_dec(v_sz_2231_);
v_i_boxed_2246_ = lean_unbox_usize(v_i_2232_);
lean_dec(v_i_2232_);
v_res_2247_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9(v_c_2228_, v_x_2229_, v_as_2230_, v_sz_boxed_2245_, v_i_boxed_2246_, v_b_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
lean_dec(v___y_2235_);
lean_dec(v___y_2234_);
lean_dec_ref(v_as_2230_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(lean_object* v_init_2248_, lean_object* v_c_2249_, lean_object* v_x_2250_, lean_object* v_n_2251_, lean_object* v_b_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
if (lean_obj_tag(v_n_2251_) == 0)
{
lean_object* v_cs_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; size_t v_sz_2267_; size_t v___x_2268_; lean_object* v___x_2269_; 
v_cs_2264_ = lean_ctor_get(v_n_2251_, 0);
v___x_2265_ = lean_box(0);
v___x_2266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2266_, 0, v___x_2265_);
lean_ctor_set(v___x_2266_, 1, v_b_2252_);
v_sz_2267_ = lean_array_size(v_cs_2264_);
v___x_2268_ = ((size_t)0ULL);
v___x_2269_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8(v_init_2248_, v_c_2249_, v_x_2250_, v_cs_2264_, v_sz_2267_, v___x_2268_, v___x_2266_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_);
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_object* v_a_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2284_; 
v_a_2270_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2272_ = v___x_2269_;
v_isShared_2273_ = v_isSharedCheck_2284_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_a_2270_);
lean_dec(v___x_2269_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2284_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v_fst_2274_; 
v_fst_2274_ = lean_ctor_get(v_a_2270_, 0);
if (lean_obj_tag(v_fst_2274_) == 0)
{
lean_object* v_snd_2275_; lean_object* v___x_2276_; lean_object* v___x_2278_; 
v_snd_2275_ = lean_ctor_get(v_a_2270_, 1);
lean_inc(v_snd_2275_);
lean_dec(v_a_2270_);
v___x_2276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2276_, 0, v_snd_2275_);
if (v_isShared_2273_ == 0)
{
lean_ctor_set(v___x_2272_, 0, v___x_2276_);
v___x_2278_ = v___x_2272_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v___x_2276_);
v___x_2278_ = v_reuseFailAlloc_2279_;
goto v_reusejp_2277_;
}
v_reusejp_2277_:
{
return v___x_2278_;
}
}
else
{
lean_object* v_val_2280_; lean_object* v___x_2282_; 
lean_inc_ref(v_fst_2274_);
lean_dec(v_a_2270_);
v_val_2280_ = lean_ctor_get(v_fst_2274_, 0);
lean_inc(v_val_2280_);
lean_dec_ref_known(v_fst_2274_, 1);
if (v_isShared_2273_ == 0)
{
lean_ctor_set(v___x_2272_, 0, v_val_2280_);
v___x_2282_ = v___x_2272_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_val_2280_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
}
}
else
{
lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2292_; 
v_a_2285_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2287_ = v___x_2269_;
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v___x_2269_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v___x_2290_; 
if (v_isShared_2288_ == 0)
{
v___x_2290_ = v___x_2287_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_a_2285_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
}
else
{
lean_object* v_vs_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; size_t v_sz_2296_; size_t v___x_2297_; lean_object* v___x_2298_; 
v_vs_2293_ = lean_ctor_get(v_n_2251_, 0);
v___x_2294_ = lean_box(0);
v___x_2295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2294_);
lean_ctor_set(v___x_2295_, 1, v_b_2252_);
v_sz_2296_ = lean_array_size(v_vs_2293_);
v___x_2297_ = ((size_t)0ULL);
v___x_2298_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9(v_c_2249_, v_x_2250_, v_vs_2293_, v_sz_2296_, v___x_2297_, v___x_2295_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_);
if (lean_obj_tag(v___x_2298_) == 0)
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2313_; 
v_a_2299_ = lean_ctor_get(v___x_2298_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2301_ = v___x_2298_;
v_isShared_2302_ = v_isSharedCheck_2313_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2298_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2313_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v_fst_2303_; 
v_fst_2303_ = lean_ctor_get(v_a_2299_, 0);
if (lean_obj_tag(v_fst_2303_) == 0)
{
lean_object* v_snd_2304_; lean_object* v___x_2305_; lean_object* v___x_2307_; 
v_snd_2304_ = lean_ctor_get(v_a_2299_, 1);
lean_inc(v_snd_2304_);
lean_dec(v_a_2299_);
v___x_2305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2305_, 0, v_snd_2304_);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 0, v___x_2305_);
v___x_2307_ = v___x_2301_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v___x_2305_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
else
{
lean_object* v_val_2309_; lean_object* v___x_2311_; 
lean_inc_ref(v_fst_2303_);
lean_dec(v_a_2299_);
v_val_2309_ = lean_ctor_get(v_fst_2303_, 0);
lean_inc(v_val_2309_);
lean_dec_ref_known(v_fst_2303_, 1);
if (v_isShared_2302_ == 0)
{
lean_ctor_set(v___x_2301_, 0, v_val_2309_);
v___x_2311_ = v___x_2301_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_val_2309_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
}
}
else
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2321_; 
v_a_2314_ = lean_ctor_get(v___x_2298_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2316_ = v___x_2298_;
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2298_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2319_; 
if (v_isShared_2317_ == 0)
{
v___x_2319_ = v___x_2316_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2314_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8(lean_object* v_init_2322_, lean_object* v_c_2323_, lean_object* v_x_2324_, lean_object* v_as_2325_, size_t v_sz_2326_, size_t v_i_2327_, lean_object* v_b_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_){
_start:
{
uint8_t v___x_2340_; 
v___x_2340_ = lean_usize_dec_lt(v_i_2327_, v_sz_2326_);
if (v___x_2340_ == 0)
{
lean_object* v___x_2341_; 
lean_dec(v_x_2324_);
lean_dec_ref(v_c_2323_);
v___x_2341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2341_, 0, v_b_2328_);
return v___x_2341_;
}
else
{
lean_object* v_snd_2342_; lean_object* v___x_2344_; uint8_t v_isShared_2345_; uint8_t v_isSharedCheck_2376_; 
v_snd_2342_ = lean_ctor_get(v_b_2328_, 1);
v_isSharedCheck_2376_ = !lean_is_exclusive(v_b_2328_);
if (v_isSharedCheck_2376_ == 0)
{
lean_object* v_unused_2377_; 
v_unused_2377_ = lean_ctor_get(v_b_2328_, 0);
lean_dec(v_unused_2377_);
v___x_2344_ = v_b_2328_;
v_isShared_2345_ = v_isSharedCheck_2376_;
goto v_resetjp_2343_;
}
else
{
lean_inc(v_snd_2342_);
lean_dec(v_b_2328_);
v___x_2344_ = lean_box(0);
v_isShared_2345_ = v_isSharedCheck_2376_;
goto v_resetjp_2343_;
}
v_resetjp_2343_:
{
lean_object* v___x_2346_; lean_object* v_a_2347_; lean_object* v___x_2348_; 
v___x_2346_ = lean_box(0);
v_a_2347_ = lean_array_uget_borrowed(v_as_2325_, v_i_2327_);
lean_inc(v_snd_2342_);
lean_inc(v_x_2324_);
lean_inc_ref(v_c_2323_);
v___x_2348_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(v_init_2322_, v_c_2323_, v_x_2324_, v_a_2347_, v_snd_2342_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2367_; 
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2351_ = v___x_2348_;
v_isShared_2352_ = v_isSharedCheck_2367_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2348_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2367_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
if (lean_obj_tag(v_a_2349_) == 0)
{
lean_object* v___x_2353_; lean_object* v___x_2355_; 
lean_dec(v_x_2324_);
lean_dec_ref(v_c_2323_);
v___x_2353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2353_, 0, v_a_2349_);
if (v_isShared_2345_ == 0)
{
lean_ctor_set(v___x_2344_, 0, v___x_2353_);
v___x_2355_ = v___x_2344_;
goto v_reusejp_2354_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v___x_2353_);
lean_ctor_set(v_reuseFailAlloc_2359_, 1, v_snd_2342_);
v___x_2355_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2354_;
}
v_reusejp_2354_:
{
lean_object* v___x_2357_; 
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 0, v___x_2355_);
v___x_2357_ = v___x_2351_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v___x_2355_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; 
lean_del_object(v___x_2351_);
lean_dec(v_snd_2342_);
v_a_2360_ = lean_ctor_get(v_a_2349_, 0);
lean_inc(v_a_2360_);
lean_dec_ref_known(v_a_2349_, 1);
if (v_isShared_2345_ == 0)
{
lean_ctor_set(v___x_2344_, 1, v_a_2360_);
lean_ctor_set(v___x_2344_, 0, v___x_2346_);
v___x_2362_ = v___x_2344_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v___x_2346_);
lean_ctor_set(v_reuseFailAlloc_2366_, 1, v_a_2360_);
v___x_2362_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
size_t v___x_2363_; size_t v___x_2364_; 
v___x_2363_ = ((size_t)1ULL);
v___x_2364_ = lean_usize_add(v_i_2327_, v___x_2363_);
v_i_2327_ = v___x_2364_;
v_b_2328_ = v___x_2362_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2375_; 
lean_del_object(v___x_2344_);
lean_dec(v_snd_2342_);
lean_dec(v_x_2324_);
lean_dec_ref(v_c_2323_);
v_a_2368_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2370_ = v___x_2348_;
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2348_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2373_; 
if (v_isShared_2371_ == 0)
{
v___x_2373_ = v___x_2370_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_a_2368_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8___boxed(lean_object** _args){
lean_object* v_init_2378_ = _args[0];
lean_object* v_c_2379_ = _args[1];
lean_object* v_x_2380_ = _args[2];
lean_object* v_as_2381_ = _args[3];
lean_object* v_sz_2382_ = _args[4];
lean_object* v_i_2383_ = _args[5];
lean_object* v_b_2384_ = _args[6];
lean_object* v___y_2385_ = _args[7];
lean_object* v___y_2386_ = _args[8];
lean_object* v___y_2387_ = _args[9];
lean_object* v___y_2388_ = _args[10];
lean_object* v___y_2389_ = _args[11];
lean_object* v___y_2390_ = _args[12];
lean_object* v___y_2391_ = _args[13];
lean_object* v___y_2392_ = _args[14];
lean_object* v___y_2393_ = _args[15];
lean_object* v___y_2394_ = _args[16];
lean_object* v___y_2395_ = _args[17];
_start:
{
size_t v_sz_boxed_2396_; size_t v_i_boxed_2397_; lean_object* v_res_2398_; 
v_sz_boxed_2396_ = lean_unbox_usize(v_sz_2382_);
lean_dec(v_sz_2382_);
v_i_boxed_2397_ = lean_unbox_usize(v_i_2383_);
lean_dec(v_i_2383_);
v_res_2398_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__8(v_init_2378_, v_c_2379_, v_x_2380_, v_as_2381_, v_sz_boxed_2396_, v_i_boxed_2397_, v_b_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v___y_2386_);
lean_dec(v___y_2385_);
lean_dec_ref(v_as_2381_);
lean_dec_ref(v_init_2378_);
return v_res_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6___boxed(lean_object* v_init_2399_, lean_object* v_c_2400_, lean_object* v_x_2401_, lean_object* v_n_2402_, lean_object* v_b_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_){
_start:
{
lean_object* v_res_2415_; 
v_res_2415_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(v_init_2399_, v_c_2400_, v_x_2401_, v_n_2402_, v_b_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_);
lean_dec(v___y_2413_);
lean_dec_ref(v___y_2412_);
lean_dec(v___y_2411_);
lean_dec_ref(v___y_2410_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
lean_dec(v___y_2405_);
lean_dec(v___y_2404_);
lean_dec_ref(v_n_2402_);
lean_dec_ref(v_init_2399_);
return v_res_2415_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2(lean_object* v_c_2416_, lean_object* v_x_2417_, lean_object* v_t_2418_, lean_object* v_init_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_){
_start:
{
lean_object* v_root_2431_; lean_object* v_tail_2432_; lean_object* v___x_2433_; 
v_root_2431_ = lean_ctor_get(v_t_2418_, 0);
v_tail_2432_ = lean_ctor_get(v_t_2418_, 1);
lean_inc(v_x_2417_);
lean_inc_ref(v_c_2416_);
lean_inc_ref(v_init_2419_);
v___x_2433_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6(v_init_2419_, v_c_2416_, v_x_2417_, v_root_2431_, v_init_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_);
lean_dec_ref(v_init_2419_);
if (lean_obj_tag(v___x_2433_) == 0)
{
lean_object* v_a_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2470_; 
v_a_2434_ = lean_ctor_get(v___x_2433_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2436_ = v___x_2433_;
v_isShared_2437_ = v_isSharedCheck_2470_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_a_2434_);
lean_dec(v___x_2433_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2470_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
if (lean_obj_tag(v_a_2434_) == 0)
{
lean_object* v_a_2438_; lean_object* v___x_2440_; 
lean_dec(v_x_2417_);
lean_dec_ref(v_c_2416_);
v_a_2438_ = lean_ctor_get(v_a_2434_, 0);
lean_inc(v_a_2438_);
lean_dec_ref_known(v_a_2434_, 1);
if (v_isShared_2437_ == 0)
{
lean_ctor_set(v___x_2436_, 0, v_a_2438_);
v___x_2440_ = v___x_2436_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v_a_2438_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
else
{
lean_object* v_a_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; size_t v_sz_2445_; size_t v___x_2446_; lean_object* v___x_2447_; 
lean_del_object(v___x_2436_);
v_a_2442_ = lean_ctor_get(v_a_2434_, 0);
lean_inc(v_a_2442_);
lean_dec_ref_known(v_a_2434_, 1);
v___x_2443_ = lean_box(0);
v___x_2444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2444_, 0, v___x_2443_);
lean_ctor_set(v___x_2444_, 1, v_a_2442_);
v_sz_2445_ = lean_array_size(v_tail_2432_);
v___x_2446_ = ((size_t)0ULL);
v___x_2447_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7(v_c_2416_, v_x_2417_, v_tail_2432_, v_sz_2445_, v___x_2446_, v___x_2444_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_);
if (lean_obj_tag(v___x_2447_) == 0)
{
lean_object* v_a_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2461_; 
v_a_2448_ = lean_ctor_get(v___x_2447_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2450_ = v___x_2447_;
v_isShared_2451_ = v_isSharedCheck_2461_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_a_2448_);
lean_dec(v___x_2447_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2461_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v_fst_2452_; 
v_fst_2452_ = lean_ctor_get(v_a_2448_, 0);
if (lean_obj_tag(v_fst_2452_) == 0)
{
lean_object* v_snd_2453_; lean_object* v___x_2455_; 
v_snd_2453_ = lean_ctor_get(v_a_2448_, 1);
lean_inc(v_snd_2453_);
lean_dec(v_a_2448_);
if (v_isShared_2451_ == 0)
{
lean_ctor_set(v___x_2450_, 0, v_snd_2453_);
v___x_2455_ = v___x_2450_;
goto v_reusejp_2454_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_snd_2453_);
v___x_2455_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2454_;
}
v_reusejp_2454_:
{
return v___x_2455_;
}
}
else
{
lean_object* v_val_2457_; lean_object* v___x_2459_; 
lean_inc_ref(v_fst_2452_);
lean_dec(v_a_2448_);
v_val_2457_ = lean_ctor_get(v_fst_2452_, 0);
lean_inc(v_val_2457_);
lean_dec_ref_known(v_fst_2452_, 1);
if (v_isShared_2451_ == 0)
{
lean_ctor_set(v___x_2450_, 0, v_val_2457_);
v___x_2459_ = v___x_2450_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v_val_2457_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
}
}
else
{
lean_object* v_a_2462_; lean_object* v___x_2464_; uint8_t v_isShared_2465_; uint8_t v_isSharedCheck_2469_; 
v_a_2462_ = lean_ctor_get(v___x_2447_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2464_ = v___x_2447_;
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
else
{
lean_inc(v_a_2462_);
lean_dec(v___x_2447_);
v___x_2464_ = lean_box(0);
v_isShared_2465_ = v_isSharedCheck_2469_;
goto v_resetjp_2463_;
}
v_resetjp_2463_:
{
lean_object* v___x_2467_; 
if (v_isShared_2465_ == 0)
{
v___x_2467_ = v___x_2464_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_a_2462_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
}
}
}
else
{
lean_object* v_a_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2478_; 
lean_dec(v_x_2417_);
lean_dec_ref(v_c_2416_);
v_a_2471_ = lean_ctor_get(v___x_2433_, 0);
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2473_ = v___x_2433_;
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_a_2471_);
lean_dec(v___x_2433_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v___x_2476_; 
if (v_isShared_2474_ == 0)
{
v___x_2476_ = v___x_2473_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_a_2471_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2___boxed(lean_object* v_c_2479_, lean_object* v_x_2480_, lean_object* v_t_2481_, lean_object* v_init_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_){
_start:
{
lean_object* v_res_2494_; 
v_res_2494_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2(v_c_2479_, v_x_2480_, v_t_2481_, v_init_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_);
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
lean_dec_ref(v_t_2481_);
return v_res_2494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(lean_object* v_x_2495_, lean_object* v_c_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_, lean_object* v_a_2499_, lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_){
_start:
{
lean_object* v___x_2508_; lean_object* v___x_2509_; 
v___x_2508_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0, &l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0_once, _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq___closed__0);
v___x_2509_ = l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_2497_, v_a_2505_);
if (lean_obj_tag(v___x_2509_) == 0)
{
lean_object* v_a_2510_; lean_object* v___y_2512_; lean_object* v_diseqs_2537_; lean_object* v_size_2538_; uint8_t v___x_2539_; 
v_a_2510_ = lean_ctor_get(v___x_2509_, 0);
lean_inc(v_a_2510_);
lean_dec_ref_known(v___x_2509_, 1);
v_diseqs_2537_ = lean_ctor_get(v_a_2510_, 8);
lean_inc_ref(v_diseqs_2537_);
lean_dec(v_a_2510_);
v_size_2538_ = lean_ctor_get(v_diseqs_2537_, 2);
v___x_2539_ = lean_nat_dec_lt(v_x_2495_, v_size_2538_);
if (v___x_2539_ == 0)
{
lean_object* v___x_2540_; 
lean_dec_ref(v_diseqs_2537_);
v___x_2540_ = l_outOfBounds___redArg(v___x_2508_);
v___y_2512_ = v___x_2540_;
goto v___jp_2511_;
}
else
{
lean_object* v___x_2541_; 
v___x_2541_ = l_Lean_PersistentArray_get_x21___redArg(v___x_2508_, v_diseqs_2537_, v_x_2495_);
lean_dec_ref(v_diseqs_2537_);
v___y_2512_ = v___x_2541_;
goto v___jp_2511_;
}
v___jp_2511_:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2513_ = lean_box(0);
v___x_2514_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7___closed__0));
v___x_2515_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2(v_c_2496_, v_x_2495_, v___y_2512_, v___x_2514_, v_a_2497_, v_a_2498_, v_a_2499_, v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_);
lean_dec_ref(v___y_2512_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2528_; 
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2528_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2528_ == 0)
{
v___x_2518_ = v___x_2515_;
v_isShared_2519_ = v_isSharedCheck_2528_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2515_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2528_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v_fst_2520_; 
v_fst_2520_ = lean_ctor_get(v_a_2516_, 0);
lean_inc(v_fst_2520_);
lean_dec(v_a_2516_);
if (lean_obj_tag(v_fst_2520_) == 0)
{
lean_object* v___x_2522_; 
if (v_isShared_2519_ == 0)
{
lean_ctor_set(v___x_2518_, 0, v___x_2513_);
v___x_2522_ = v___x_2518_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v___x_2513_);
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
lean_object* v_val_2524_; lean_object* v___x_2526_; 
v_val_2524_ = lean_ctor_get(v_fst_2520_, 0);
lean_inc(v_val_2524_);
lean_dec_ref_known(v_fst_2520_, 1);
if (v_isShared_2519_ == 0)
{
lean_ctor_set(v___x_2518_, 0, v_val_2524_);
v___x_2526_ = v___x_2518_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_val_2524_);
v___x_2526_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
return v___x_2526_;
}
}
}
}
else
{
lean_object* v_a_2529_; lean_object* v___x_2531_; uint8_t v_isShared_2532_; uint8_t v_isSharedCheck_2536_; 
v_a_2529_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2536_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2536_ == 0)
{
v___x_2531_ = v___x_2515_;
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
else
{
lean_inc(v_a_2529_);
lean_dec(v___x_2515_);
v___x_2531_ = lean_box(0);
v_isShared_2532_ = v_isSharedCheck_2536_;
goto v_resetjp_2530_;
}
v_resetjp_2530_:
{
lean_object* v___x_2534_; 
if (v_isShared_2532_ == 0)
{
v___x_2534_ = v___x_2531_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2535_; 
v_reuseFailAlloc_2535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2535_, 0, v_a_2529_);
v___x_2534_ = v_reuseFailAlloc_2535_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
return v___x_2534_;
}
}
}
}
}
else
{
lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2549_; 
lean_dec_ref(v_c_2496_);
lean_dec(v_x_2495_);
v_a_2542_ = lean_ctor_get(v___x_2509_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2544_ = v___x_2509_;
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v___x_2509_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2547_; 
if (v_isShared_2545_ == 0)
{
v___x_2547_ = v___x_2544_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_a_2542_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f___boxed(lean_object* v_x_2550_, lean_object* v_c_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(v_x_2550_, v_c_2551_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_);
lean_dec(v_a_2561_);
lean_dec_ref(v_a_2560_);
lean_dec(v_a_2559_);
lean_dec_ref(v_a_2558_);
lean_dec(v_a_2557_);
lean_dec_ref(v_a_2556_);
lean_dec(v_a_2555_);
lean_dec_ref(v_a_2554_);
lean_dec(v_a_2553_);
lean_dec(v_a_2552_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11(lean_object* v_c_2564_, lean_object* v_x_2565_, lean_object* v_as_2566_, size_t v_sz_2567_, size_t v_i_2568_, lean_object* v_b_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_){
_start:
{
lean_object* v___x_2581_; 
v___x_2581_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg(v_c_2564_, v_x_2565_, v_as_2566_, v_sz_2567_, v_i_2568_, v_b_2569_, v___y_2570_);
return v___x_2581_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___boxed(lean_object** _args){
lean_object* v_c_2582_ = _args[0];
lean_object* v_x_2583_ = _args[1];
lean_object* v_as_2584_ = _args[2];
lean_object* v_sz_2585_ = _args[3];
lean_object* v_i_2586_ = _args[4];
lean_object* v_b_2587_ = _args[5];
lean_object* v___y_2588_ = _args[6];
lean_object* v___y_2589_ = _args[7];
lean_object* v___y_2590_ = _args[8];
lean_object* v___y_2591_ = _args[9];
lean_object* v___y_2592_ = _args[10];
lean_object* v___y_2593_ = _args[11];
lean_object* v___y_2594_ = _args[12];
lean_object* v___y_2595_ = _args[13];
lean_object* v___y_2596_ = _args[14];
lean_object* v___y_2597_ = _args[15];
lean_object* v___y_2598_ = _args[16];
_start:
{
size_t v_sz_boxed_2599_; size_t v_i_boxed_2600_; lean_object* v_res_2601_; 
v_sz_boxed_2599_ = lean_unbox_usize(v_sz_2585_);
lean_dec(v_sz_2585_);
v_i_boxed_2600_ = lean_unbox_usize(v_i_2586_);
lean_dec(v_i_2586_);
v_res_2601_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11(v_c_2582_, v_x_2583_, v_as_2584_, v_sz_boxed_2599_, v_i_boxed_2600_, v_b_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_, v___y_2594_, v___y_2595_, v___y_2596_, v___y_2597_);
lean_dec(v___y_2597_);
lean_dec_ref(v___y_2596_);
lean_dec(v___y_2595_);
lean_dec_ref(v___y_2594_);
lean_dec(v___y_2593_);
lean_dec_ref(v___y_2592_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec(v___y_2589_);
lean_dec(v___y_2588_);
lean_dec_ref(v_as_2584_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10(lean_object* v_c_2602_, lean_object* v_x_2603_, lean_object* v_as_2604_, size_t v_sz_2605_, size_t v_i_2606_, lean_object* v_b_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_, lean_object* v___y_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_){
_start:
{
lean_object* v___x_2619_; 
v___x_2619_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___redArg(v_c_2602_, v_x_2603_, v_as_2604_, v_sz_2605_, v_i_2606_, v_b_2607_, v___y_2608_);
return v___x_2619_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10___boxed(lean_object** _args){
lean_object* v_c_2620_ = _args[0];
lean_object* v_x_2621_ = _args[1];
lean_object* v_as_2622_ = _args[2];
lean_object* v_sz_2623_ = _args[3];
lean_object* v_i_2624_ = _args[4];
lean_object* v_b_2625_ = _args[5];
lean_object* v___y_2626_ = _args[6];
lean_object* v___y_2627_ = _args[7];
lean_object* v___y_2628_ = _args[8];
lean_object* v___y_2629_ = _args[9];
lean_object* v___y_2630_ = _args[10];
lean_object* v___y_2631_ = _args[11];
lean_object* v___y_2632_ = _args[12];
lean_object* v___y_2633_ = _args[13];
lean_object* v___y_2634_ = _args[14];
lean_object* v___y_2635_ = _args[15];
lean_object* v___y_2636_ = _args[16];
_start:
{
size_t v_sz_boxed_2637_; size_t v_i_boxed_2638_; lean_object* v_res_2639_; 
v_sz_boxed_2637_ = lean_unbox_usize(v_sz_2623_);
lean_dec(v_sz_2623_);
v_i_boxed_2638_ = lean_unbox_usize(v_i_2624_);
lean_dec(v_i_2624_);
v_res_2639_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__6_spec__9_spec__10(v_c_2620_, v_x_2621_, v_as_2622_, v_sz_boxed_2637_, v_i_boxed_2638_, v_b_2625_, v___y_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec(v___y_2633_);
lean_dec_ref(v___y_2632_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec(v___y_2627_);
lean_dec(v___y_2626_);
lean_dec_ref(v_as_2622_);
return v_res_2639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg(lean_object* v_v_2640_, lean_object* v_a_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_, lean_object* v___y_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_){
_start:
{
lean_object* v_snd_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2684_; 
v_snd_2653_ = lean_ctor_get(v_a_2641_, 1);
v_isSharedCheck_2684_ = !lean_is_exclusive(v_a_2641_);
if (v_isSharedCheck_2684_ == 0)
{
lean_object* v_unused_2685_; 
v_unused_2685_ = lean_ctor_get(v_a_2641_, 0);
lean_dec(v_unused_2685_);
v___x_2655_ = v_a_2641_;
v_isShared_2656_ = v_isSharedCheck_2684_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_snd_2653_);
lean_dec(v_a_2641_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2684_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2657_ = lean_box(0);
lean_inc(v_snd_2653_);
lean_inc(v_v_2640_);
v___x_2658_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f(v_v_2640_, v_snd_2653_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_, v___y_2650_, v___y_2651_);
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_object* v_a_2659_; lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2675_; 
v_a_2659_ = lean_ctor_get(v___x_2658_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2661_ = v___x_2658_;
v_isShared_2662_ = v_isSharedCheck_2675_;
goto v_resetjp_2660_;
}
else
{
lean_inc(v_a_2659_);
lean_dec(v___x_2658_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2675_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
if (lean_obj_tag(v_a_2659_) == 1)
{
lean_object* v_val_2663_; lean_object* v___x_2665_; 
lean_del_object(v___x_2661_);
lean_dec(v_snd_2653_);
v_val_2663_ = lean_ctor_get(v_a_2659_, 0);
lean_inc(v_val_2663_);
lean_dec_ref_known(v_a_2659_, 1);
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 1, v_val_2663_);
lean_ctor_set(v___x_2655_, 0, v___x_2657_);
v___x_2665_ = v___x_2655_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v___x_2657_);
lean_ctor_set(v_reuseFailAlloc_2667_, 1, v_val_2663_);
v___x_2665_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
v_a_2641_ = v___x_2665_;
goto _start;
}
}
else
{
lean_object* v___x_2668_; lean_object* v___x_2670_; 
lean_dec(v_a_2659_);
lean_dec(v_v_2640_);
lean_inc(v_snd_2653_);
v___x_2668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2668_, 0, v_snd_2653_);
if (v_isShared_2656_ == 0)
{
lean_ctor_set(v___x_2655_, 0, v___x_2668_);
v___x_2670_ = v___x_2655_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v___x_2668_);
lean_ctor_set(v_reuseFailAlloc_2674_, 1, v_snd_2653_);
v___x_2670_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
lean_object* v___x_2672_; 
if (v_isShared_2662_ == 0)
{
lean_ctor_set(v___x_2661_, 0, v___x_2670_);
v___x_2672_ = v___x_2661_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v___x_2670_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
}
}
else
{
lean_object* v_a_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2683_; 
lean_del_object(v___x_2655_);
lean_dec(v_snd_2653_);
lean_dec(v_v_2640_);
v_a_2676_ = lean_ctor_get(v___x_2658_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2658_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2678_ = v___x_2658_;
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_a_2676_);
lean_dec(v___x_2658_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2681_; 
if (v_isShared_2679_ == 0)
{
v___x_2681_ = v___x_2678_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_a_2676_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg___boxed(lean_object* v_v_2686_, lean_object* v_a_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_){
_start:
{
lean_object* v_res_2699_; 
v_res_2699_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg(v_v_2686_, v_a_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
lean_dec(v___y_2697_);
lean_dec_ref(v___y_2696_);
lean_dec(v___y_2695_);
lean_dec_ref(v___y_2694_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
lean_dec(v___y_2691_);
lean_dec_ref(v___y_2690_);
lean_dec(v___y_2689_);
lean_dec(v___y_2688_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(lean_object* v_c_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_){
_start:
{
lean_object* v_p_2712_; 
v_p_2712_ = lean_ctor_get(v_c_2700_, 0);
if (lean_obj_tag(v_p_2712_) == 1)
{
lean_object* v_v_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; 
v_v_2713_ = lean_ctor_get(v_p_2712_, 1);
lean_inc(v_v_2713_);
v___x_2714_ = lean_box(0);
v___x_2715_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2715_, 0, v___x_2714_);
lean_ctor_set(v___x_2715_, 1, v_c_2700_);
v___x_2716_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg(v_v_2713_, v___x_2715_, v_a_2701_, v_a_2702_, v_a_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_);
if (lean_obj_tag(v___x_2716_) == 0)
{
lean_object* v_a_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2730_; 
v_a_2717_ = lean_ctor_get(v___x_2716_, 0);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2719_ = v___x_2716_;
v_isShared_2720_ = v_isSharedCheck_2730_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_a_2717_);
lean_dec(v___x_2716_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2730_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v_fst_2721_; 
v_fst_2721_ = lean_ctor_get(v_a_2717_, 0);
if (lean_obj_tag(v_fst_2721_) == 0)
{
lean_object* v_snd_2722_; lean_object* v___x_2724_; 
v_snd_2722_ = lean_ctor_get(v_a_2717_, 1);
lean_inc(v_snd_2722_);
lean_dec(v_a_2717_);
if (v_isShared_2720_ == 0)
{
lean_ctor_set(v___x_2719_, 0, v_snd_2722_);
v___x_2724_ = v___x_2719_;
goto v_reusejp_2723_;
}
else
{
lean_object* v_reuseFailAlloc_2725_; 
v_reuseFailAlloc_2725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2725_, 0, v_snd_2722_);
v___x_2724_ = v_reuseFailAlloc_2725_;
goto v_reusejp_2723_;
}
v_reusejp_2723_:
{
return v___x_2724_;
}
}
else
{
lean_object* v_val_2726_; lean_object* v___x_2728_; 
lean_inc_ref(v_fst_2721_);
lean_dec(v_a_2717_);
v_val_2726_ = lean_ctor_get(v_fst_2721_, 0);
lean_inc(v_val_2726_);
lean_dec_ref_known(v_fst_2721_, 1);
if (v_isShared_2720_ == 0)
{
lean_ctor_set(v___x_2719_, 0, v_val_2726_);
v___x_2728_ = v___x_2719_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v_val_2726_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
}
}
else
{
lean_object* v_a_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2738_; 
v_a_2731_ = lean_ctor_get(v___x_2716_, 0);
v_isSharedCheck_2738_ = !lean_is_exclusive(v___x_2716_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2733_ = v___x_2716_;
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_a_2731_);
lean_dec(v___x_2716_);
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
else
{
lean_object* v___x_2739_; 
v___x_2739_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_c_2700_, v_a_2701_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_);
return v___x_2739_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq___boxed(lean_object* v_c_2740_, lean_object* v_a_2741_, lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_){
_start:
{
lean_object* v_res_2752_; 
v_res_2752_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(v_c_2740_, v_a_2741_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_, v_a_2750_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0(lean_object* v_v_2753_, lean_object* v_inst_2754_, lean_object* v_a_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_){
_start:
{
lean_object* v___x_2767_; 
v___x_2767_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___redArg(v_v_2753_, v_a_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_);
return v___x_2767_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0___boxed(lean_object* v_v_2768_, lean_object* v_inst_2769_, lean_object* v_a_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_){
_start:
{
lean_object* v_res_2782_; 
v_res_2782_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_spec__0(v_v_2768_, v_inst_2769_, v_a_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_);
lean_dec(v___y_2780_);
lean_dec_ref(v___y_2779_);
lean_dec(v___y_2778_);
lean_dec_ref(v___y_2777_);
lean_dec(v___y_2776_);
lean_dec_ref(v___y_2775_);
lean_dec(v___y_2774_);
lean_dec_ref(v___y_2773_);
lean_dec(v___y_2772_);
lean_dec(v___y_2771_);
return v_res_2782_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(lean_object* v_a_2783_, lean_object* v_x_2784_, size_t v_x_2785_, size_t v_x_2786_){
_start:
{
if (lean_obj_tag(v_x_2784_) == 0)
{
lean_object* v_cs_2787_; size_t v_j_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; uint8_t v___x_2791_; 
v_cs_2787_ = lean_ctor_get(v_x_2784_, 0);
v_j_2788_ = lean_usize_shift_right(v_x_2785_, v_x_2786_);
v___x_2789_ = lean_usize_to_nat(v_j_2788_);
v___x_2790_ = lean_array_get_size(v_cs_2787_);
v___x_2791_ = lean_nat_dec_lt(v___x_2789_, v___x_2790_);
if (v___x_2791_ == 0)
{
lean_dec(v___x_2789_);
lean_dec_ref(v_a_2783_);
return v_x_2784_;
}
else
{
lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2809_; 
lean_inc_ref(v_cs_2787_);
v_isSharedCheck_2809_ = !lean_is_exclusive(v_x_2784_);
if (v_isSharedCheck_2809_ == 0)
{
lean_object* v_unused_2810_; 
v_unused_2810_ = lean_ctor_get(v_x_2784_, 0);
lean_dec(v_unused_2810_);
v___x_2793_ = v_x_2784_;
v_isShared_2794_ = v_isSharedCheck_2809_;
goto v_resetjp_2792_;
}
else
{
lean_dec(v_x_2784_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2809_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
size_t v___x_2795_; size_t v___x_2796_; size_t v___x_2797_; size_t v_i_2798_; size_t v___x_2799_; size_t v_shift_2800_; lean_object* v_v_2801_; lean_object* v___x_2802_; lean_object* v_xs_x27_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2807_; 
v___x_2795_ = ((size_t)1ULL);
v___x_2796_ = lean_usize_shift_left(v___x_2795_, v_x_2786_);
v___x_2797_ = lean_usize_sub(v___x_2796_, v___x_2795_);
v_i_2798_ = lean_usize_land(v_x_2785_, v___x_2797_);
v___x_2799_ = ((size_t)5ULL);
v_shift_2800_ = lean_usize_sub(v_x_2786_, v___x_2799_);
v_v_2801_ = lean_array_fget(v_cs_2787_, v___x_2789_);
v___x_2802_ = lean_box(0);
v_xs_x27_2803_ = lean_array_fset(v_cs_2787_, v___x_2789_, v___x_2802_);
v___x_2804_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(v_a_2783_, v_v_2801_, v_i_2798_, v_shift_2800_);
v___x_2805_ = lean_array_fset(v_xs_x27_2803_, v___x_2789_, v___x_2804_);
lean_dec(v___x_2789_);
if (v_isShared_2794_ == 0)
{
lean_ctor_set(v___x_2793_, 0, v___x_2805_);
v___x_2807_ = v___x_2793_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v___x_2805_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
return v___x_2807_;
}
}
}
}
else
{
lean_object* v_vs_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; uint8_t v___x_2814_; 
v_vs_2811_ = lean_ctor_get(v_x_2784_, 0);
v___x_2812_ = lean_usize_to_nat(v_x_2785_);
v___x_2813_ = lean_array_get_size(v_vs_2811_);
v___x_2814_ = lean_nat_dec_lt(v___x_2812_, v___x_2813_);
if (v___x_2814_ == 0)
{
lean_dec(v___x_2812_);
lean_dec_ref(v_a_2783_);
return v_x_2784_;
}
else
{
lean_object* v___x_2816_; uint8_t v_isShared_2817_; uint8_t v_isSharedCheck_2826_; 
lean_inc_ref(v_vs_2811_);
v_isSharedCheck_2826_ = !lean_is_exclusive(v_x_2784_);
if (v_isSharedCheck_2826_ == 0)
{
lean_object* v_unused_2827_; 
v_unused_2827_ = lean_ctor_get(v_x_2784_, 0);
lean_dec(v_unused_2827_);
v___x_2816_ = v_x_2784_;
v_isShared_2817_ = v_isSharedCheck_2826_;
goto v_resetjp_2815_;
}
else
{
lean_dec(v_x_2784_);
v___x_2816_ = lean_box(0);
v_isShared_2817_ = v_isSharedCheck_2826_;
goto v_resetjp_2815_;
}
v_resetjp_2815_:
{
lean_object* v_v_2818_; lean_object* v___x_2819_; lean_object* v_xs_x27_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2824_; 
v_v_2818_ = lean_array_fget(v_vs_2811_, v___x_2812_);
v___x_2819_ = lean_box(0);
v_xs_x27_2820_ = lean_array_fset(v_vs_2811_, v___x_2812_, v___x_2819_);
v___x_2821_ = l_Lean_PersistentArray_push___redArg(v_v_2818_, v_a_2783_);
v___x_2822_ = lean_array_fset(v_xs_x27_2820_, v___x_2812_, v___x_2821_);
lean_dec(v___x_2812_);
if (v_isShared_2817_ == 0)
{
lean_ctor_set(v___x_2816_, 0, v___x_2822_);
v___x_2824_ = v___x_2816_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v___x_2822_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0___boxed(lean_object* v_a_2828_, lean_object* v_x_2829_, lean_object* v_x_2830_, lean_object* v_x_2831_){
_start:
{
size_t v_x_62885__boxed_2832_; size_t v_x_62886__boxed_2833_; lean_object* v_res_2834_; 
v_x_62885__boxed_2832_ = lean_unbox_usize(v_x_2830_);
lean_dec(v_x_2830_);
v_x_62886__boxed_2833_ = lean_unbox_usize(v_x_2831_);
lean_dec(v_x_2831_);
v_res_2834_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(v_a_2828_, v_x_2829_, v_x_62885__boxed_2832_, v_x_62886__boxed_2833_);
return v_res_2834_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(lean_object* v_a_2835_, lean_object* v_t_2836_, lean_object* v_i_2837_){
_start:
{
lean_object* v_root_2838_; lean_object* v_tail_2839_; lean_object* v_size_2840_; size_t v_shift_2841_; lean_object* v_tailOff_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2866_; 
v_root_2838_ = lean_ctor_get(v_t_2836_, 0);
v_tail_2839_ = lean_ctor_get(v_t_2836_, 1);
v_size_2840_ = lean_ctor_get(v_t_2836_, 2);
v_shift_2841_ = lean_ctor_get_usize(v_t_2836_, 4);
v_tailOff_2842_ = lean_ctor_get(v_t_2836_, 3);
v_isSharedCheck_2866_ = !lean_is_exclusive(v_t_2836_);
if (v_isSharedCheck_2866_ == 0)
{
v___x_2844_ = v_t_2836_;
v_isShared_2845_ = v_isSharedCheck_2866_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_tailOff_2842_);
lean_inc(v_size_2840_);
lean_inc(v_tail_2839_);
lean_inc(v_root_2838_);
lean_dec(v_t_2836_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2866_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
uint8_t v___x_2846_; 
v___x_2846_ = lean_nat_dec_le(v_tailOff_2842_, v_i_2837_);
if (v___x_2846_ == 0)
{
size_t v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2850_; 
v___x_2847_ = lean_usize_of_nat(v_i_2837_);
v___x_2848_ = l_Lean_PersistentArray_modifyAux___at___00Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0_spec__0(v_a_2835_, v_root_2838_, v___x_2847_, v_shift_2841_);
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 0, v___x_2848_);
v___x_2850_ = v___x_2844_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v___x_2848_);
lean_ctor_set(v_reuseFailAlloc_2851_, 1, v_tail_2839_);
lean_ctor_set(v_reuseFailAlloc_2851_, 2, v_size_2840_);
lean_ctor_set(v_reuseFailAlloc_2851_, 3, v_tailOff_2842_);
lean_ctor_set_usize(v_reuseFailAlloc_2851_, 4, v_shift_2841_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
return v___x_2850_;
}
}
else
{
lean_object* v___x_2852_; lean_object* v___x_2853_; uint8_t v___x_2854_; 
v___x_2852_ = lean_nat_sub(v_i_2837_, v_tailOff_2842_);
v___x_2853_ = lean_array_get_size(v_tail_2839_);
v___x_2854_ = lean_nat_dec_lt(v___x_2852_, v___x_2853_);
if (v___x_2854_ == 0)
{
lean_object* v___x_2856_; 
lean_dec(v___x_2852_);
lean_dec_ref(v_a_2835_);
if (v_isShared_2845_ == 0)
{
v___x_2856_ = v___x_2844_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v_root_2838_);
lean_ctor_set(v_reuseFailAlloc_2857_, 1, v_tail_2839_);
lean_ctor_set(v_reuseFailAlloc_2857_, 2, v_size_2840_);
lean_ctor_set(v_reuseFailAlloc_2857_, 3, v_tailOff_2842_);
lean_ctor_set_usize(v_reuseFailAlloc_2857_, 4, v_shift_2841_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
return v___x_2856_;
}
}
else
{
lean_object* v_v_2858_; lean_object* v___x_2859_; lean_object* v_xs_x27_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2864_; 
v_v_2858_ = lean_array_fget(v_tail_2839_, v___x_2852_);
v___x_2859_ = lean_box(0);
v_xs_x27_2860_ = lean_array_fset(v_tail_2839_, v___x_2852_, v___x_2859_);
v___x_2861_ = l_Lean_PersistentArray_push___redArg(v_v_2858_, v_a_2835_);
v___x_2862_ = lean_array_fset(v_xs_x27_2860_, v___x_2852_, v___x_2861_);
lean_dec(v___x_2852_);
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 1, v___x_2862_);
v___x_2864_ = v___x_2844_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v_root_2838_);
lean_ctor_set(v_reuseFailAlloc_2865_, 1, v___x_2862_);
lean_ctor_set(v_reuseFailAlloc_2865_, 2, v_size_2840_);
lean_ctor_set(v_reuseFailAlloc_2865_, 3, v_tailOff_2842_);
lean_ctor_set_usize(v_reuseFailAlloc_2865_, 4, v_shift_2841_);
v___x_2864_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
return v___x_2864_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0___boxed(lean_object* v_a_2867_, lean_object* v_t_2868_, lean_object* v_i_2869_){
_start:
{
lean_object* v_res_2870_; 
v_res_2870_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(v_a_2867_, v_t_2868_, v_i_2869_);
lean_dec(v_i_2869_);
return v_res_2870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0(lean_object* v_a_2871_, lean_object* v_v_2872_, lean_object* v_s_2873_){
_start:
{
lean_object* v_vars_2874_; lean_object* v_varMap_2875_; lean_object* v_varsHistory_2876_; lean_object* v_natToIntMap_2877_; lean_object* v_natDef_2878_; lean_object* v_dvds_2879_; lean_object* v_lowers_2880_; lean_object* v_uppers_2881_; lean_object* v_diseqs_2882_; lean_object* v_elimEqs_2883_; lean_object* v_elimStack_2884_; lean_object* v_occurs_2885_; lean_object* v_assignment_2886_; lean_object* v_nextCnstrId_2887_; uint8_t v_caseSplits_2888_; lean_object* v_steps_2889_; lean_object* v_penalties_2890_; lean_object* v_numReorderRequests_2891_; lean_object* v_conflict_x3f_2892_; lean_object* v_diseqSplits_2893_; lean_object* v_divMod_2894_; uint8_t v_usedCommRing_2895_; lean_object* v_nonlinearOccs_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2904_; 
v_vars_2874_ = lean_ctor_get(v_s_2873_, 0);
v_varMap_2875_ = lean_ctor_get(v_s_2873_, 1);
v_varsHistory_2876_ = lean_ctor_get(v_s_2873_, 2);
v_natToIntMap_2877_ = lean_ctor_get(v_s_2873_, 3);
v_natDef_2878_ = lean_ctor_get(v_s_2873_, 4);
v_dvds_2879_ = lean_ctor_get(v_s_2873_, 5);
v_lowers_2880_ = lean_ctor_get(v_s_2873_, 6);
v_uppers_2881_ = lean_ctor_get(v_s_2873_, 7);
v_diseqs_2882_ = lean_ctor_get(v_s_2873_, 8);
v_elimEqs_2883_ = lean_ctor_get(v_s_2873_, 9);
v_elimStack_2884_ = lean_ctor_get(v_s_2873_, 10);
v_occurs_2885_ = lean_ctor_get(v_s_2873_, 11);
v_assignment_2886_ = lean_ctor_get(v_s_2873_, 12);
v_nextCnstrId_2887_ = lean_ctor_get(v_s_2873_, 13);
v_caseSplits_2888_ = lean_ctor_get_uint8(v_s_2873_, sizeof(void*)*21);
v_steps_2889_ = lean_ctor_get(v_s_2873_, 14);
v_penalties_2890_ = lean_ctor_get(v_s_2873_, 15);
v_numReorderRequests_2891_ = lean_ctor_get(v_s_2873_, 16);
v_conflict_x3f_2892_ = lean_ctor_get(v_s_2873_, 17);
v_diseqSplits_2893_ = lean_ctor_get(v_s_2873_, 18);
v_divMod_2894_ = lean_ctor_get(v_s_2873_, 19);
v_usedCommRing_2895_ = lean_ctor_get_uint8(v_s_2873_, sizeof(void*)*21 + 1);
v_nonlinearOccs_2896_ = lean_ctor_get(v_s_2873_, 20);
v_isSharedCheck_2904_ = !lean_is_exclusive(v_s_2873_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2898_ = v_s_2873_;
v_isShared_2899_ = v_isSharedCheck_2904_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_nonlinearOccs_2896_);
lean_inc(v_divMod_2894_);
lean_inc(v_diseqSplits_2893_);
lean_inc(v_conflict_x3f_2892_);
lean_inc(v_numReorderRequests_2891_);
lean_inc(v_penalties_2890_);
lean_inc(v_steps_2889_);
lean_inc(v_nextCnstrId_2887_);
lean_inc(v_assignment_2886_);
lean_inc(v_occurs_2885_);
lean_inc(v_elimStack_2884_);
lean_inc(v_elimEqs_2883_);
lean_inc(v_diseqs_2882_);
lean_inc(v_uppers_2881_);
lean_inc(v_lowers_2880_);
lean_inc(v_dvds_2879_);
lean_inc(v_natDef_2878_);
lean_inc(v_natToIntMap_2877_);
lean_inc(v_varsHistory_2876_);
lean_inc(v_varMap_2875_);
lean_inc(v_vars_2874_);
lean_dec(v_s_2873_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2904_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2900_; lean_object* v___x_2902_; 
v___x_2900_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(v_a_2871_, v_lowers_2880_, v_v_2872_);
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 6, v___x_2900_);
v___x_2902_ = v___x_2898_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 21, 2);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_vars_2874_);
lean_ctor_set(v_reuseFailAlloc_2903_, 1, v_varMap_2875_);
lean_ctor_set(v_reuseFailAlloc_2903_, 2, v_varsHistory_2876_);
lean_ctor_set(v_reuseFailAlloc_2903_, 3, v_natToIntMap_2877_);
lean_ctor_set(v_reuseFailAlloc_2903_, 4, v_natDef_2878_);
lean_ctor_set(v_reuseFailAlloc_2903_, 5, v_dvds_2879_);
lean_ctor_set(v_reuseFailAlloc_2903_, 6, v___x_2900_);
lean_ctor_set(v_reuseFailAlloc_2903_, 7, v_uppers_2881_);
lean_ctor_set(v_reuseFailAlloc_2903_, 8, v_diseqs_2882_);
lean_ctor_set(v_reuseFailAlloc_2903_, 9, v_elimEqs_2883_);
lean_ctor_set(v_reuseFailAlloc_2903_, 10, v_elimStack_2884_);
lean_ctor_set(v_reuseFailAlloc_2903_, 11, v_occurs_2885_);
lean_ctor_set(v_reuseFailAlloc_2903_, 12, v_assignment_2886_);
lean_ctor_set(v_reuseFailAlloc_2903_, 13, v_nextCnstrId_2887_);
lean_ctor_set(v_reuseFailAlloc_2903_, 14, v_steps_2889_);
lean_ctor_set(v_reuseFailAlloc_2903_, 15, v_penalties_2890_);
lean_ctor_set(v_reuseFailAlloc_2903_, 16, v_numReorderRequests_2891_);
lean_ctor_set(v_reuseFailAlloc_2903_, 17, v_conflict_x3f_2892_);
lean_ctor_set(v_reuseFailAlloc_2903_, 18, v_diseqSplits_2893_);
lean_ctor_set(v_reuseFailAlloc_2903_, 19, v_divMod_2894_);
lean_ctor_set(v_reuseFailAlloc_2903_, 20, v_nonlinearOccs_2896_);
lean_ctor_set_uint8(v_reuseFailAlloc_2903_, sizeof(void*)*21, v_caseSplits_2888_);
lean_ctor_set_uint8(v_reuseFailAlloc_2903_, sizeof(void*)*21 + 1, v_usedCommRing_2895_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0___boxed(lean_object* v_a_2905_, lean_object* v_v_2906_, lean_object* v_s_2907_){
_start:
{
lean_object* v_res_2908_; 
v_res_2908_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0(v_a_2905_, v_v_2906_, v_s_2907_);
lean_dec(v_v_2906_);
return v_res_2908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1(lean_object* v_a_2909_, lean_object* v_v_2910_, lean_object* v_s_2911_){
_start:
{
lean_object* v_vars_2912_; lean_object* v_varMap_2913_; lean_object* v_varsHistory_2914_; lean_object* v_natToIntMap_2915_; lean_object* v_natDef_2916_; lean_object* v_dvds_2917_; lean_object* v_lowers_2918_; lean_object* v_uppers_2919_; lean_object* v_diseqs_2920_; lean_object* v_elimEqs_2921_; lean_object* v_elimStack_2922_; lean_object* v_occurs_2923_; lean_object* v_assignment_2924_; lean_object* v_nextCnstrId_2925_; uint8_t v_caseSplits_2926_; lean_object* v_steps_2927_; lean_object* v_penalties_2928_; lean_object* v_numReorderRequests_2929_; lean_object* v_conflict_x3f_2930_; lean_object* v_diseqSplits_2931_; lean_object* v_divMod_2932_; uint8_t v_usedCommRing_2933_; lean_object* v_nonlinearOccs_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2942_; 
v_vars_2912_ = lean_ctor_get(v_s_2911_, 0);
v_varMap_2913_ = lean_ctor_get(v_s_2911_, 1);
v_varsHistory_2914_ = lean_ctor_get(v_s_2911_, 2);
v_natToIntMap_2915_ = lean_ctor_get(v_s_2911_, 3);
v_natDef_2916_ = lean_ctor_get(v_s_2911_, 4);
v_dvds_2917_ = lean_ctor_get(v_s_2911_, 5);
v_lowers_2918_ = lean_ctor_get(v_s_2911_, 6);
v_uppers_2919_ = lean_ctor_get(v_s_2911_, 7);
v_diseqs_2920_ = lean_ctor_get(v_s_2911_, 8);
v_elimEqs_2921_ = lean_ctor_get(v_s_2911_, 9);
v_elimStack_2922_ = lean_ctor_get(v_s_2911_, 10);
v_occurs_2923_ = lean_ctor_get(v_s_2911_, 11);
v_assignment_2924_ = lean_ctor_get(v_s_2911_, 12);
v_nextCnstrId_2925_ = lean_ctor_get(v_s_2911_, 13);
v_caseSplits_2926_ = lean_ctor_get_uint8(v_s_2911_, sizeof(void*)*21);
v_steps_2927_ = lean_ctor_get(v_s_2911_, 14);
v_penalties_2928_ = lean_ctor_get(v_s_2911_, 15);
v_numReorderRequests_2929_ = lean_ctor_get(v_s_2911_, 16);
v_conflict_x3f_2930_ = lean_ctor_get(v_s_2911_, 17);
v_diseqSplits_2931_ = lean_ctor_get(v_s_2911_, 18);
v_divMod_2932_ = lean_ctor_get(v_s_2911_, 19);
v_usedCommRing_2933_ = lean_ctor_get_uint8(v_s_2911_, sizeof(void*)*21 + 1);
v_nonlinearOccs_2934_ = lean_ctor_get(v_s_2911_, 20);
v_isSharedCheck_2942_ = !lean_is_exclusive(v_s_2911_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2936_ = v_s_2911_;
v_isShared_2937_ = v_isSharedCheck_2942_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_nonlinearOccs_2934_);
lean_inc(v_divMod_2932_);
lean_inc(v_diseqSplits_2931_);
lean_inc(v_conflict_x3f_2930_);
lean_inc(v_numReorderRequests_2929_);
lean_inc(v_penalties_2928_);
lean_inc(v_steps_2927_);
lean_inc(v_nextCnstrId_2925_);
lean_inc(v_assignment_2924_);
lean_inc(v_occurs_2923_);
lean_inc(v_elimStack_2922_);
lean_inc(v_elimEqs_2921_);
lean_inc(v_diseqs_2920_);
lean_inc(v_uppers_2919_);
lean_inc(v_lowers_2918_);
lean_inc(v_dvds_2917_);
lean_inc(v_natDef_2916_);
lean_inc(v_natToIntMap_2915_);
lean_inc(v_varsHistory_2914_);
lean_inc(v_varMap_2913_);
lean_inc(v_vars_2912_);
lean_dec(v_s_2911_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2942_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2938_; lean_object* v___x_2940_; 
v___x_2938_ = l_Lean_PersistentArray_modify___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl_spec__0(v_a_2909_, v_uppers_2919_, v_v_2910_);
if (v_isShared_2937_ == 0)
{
lean_ctor_set(v___x_2936_, 7, v___x_2938_);
v___x_2940_ = v___x_2936_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(0, 21, 2);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v_vars_2912_);
lean_ctor_set(v_reuseFailAlloc_2941_, 1, v_varMap_2913_);
lean_ctor_set(v_reuseFailAlloc_2941_, 2, v_varsHistory_2914_);
lean_ctor_set(v_reuseFailAlloc_2941_, 3, v_natToIntMap_2915_);
lean_ctor_set(v_reuseFailAlloc_2941_, 4, v_natDef_2916_);
lean_ctor_set(v_reuseFailAlloc_2941_, 5, v_dvds_2917_);
lean_ctor_set(v_reuseFailAlloc_2941_, 6, v_lowers_2918_);
lean_ctor_set(v_reuseFailAlloc_2941_, 7, v___x_2938_);
lean_ctor_set(v_reuseFailAlloc_2941_, 8, v_diseqs_2920_);
lean_ctor_set(v_reuseFailAlloc_2941_, 9, v_elimEqs_2921_);
lean_ctor_set(v_reuseFailAlloc_2941_, 10, v_elimStack_2922_);
lean_ctor_set(v_reuseFailAlloc_2941_, 11, v_occurs_2923_);
lean_ctor_set(v_reuseFailAlloc_2941_, 12, v_assignment_2924_);
lean_ctor_set(v_reuseFailAlloc_2941_, 13, v_nextCnstrId_2925_);
lean_ctor_set(v_reuseFailAlloc_2941_, 14, v_steps_2927_);
lean_ctor_set(v_reuseFailAlloc_2941_, 15, v_penalties_2928_);
lean_ctor_set(v_reuseFailAlloc_2941_, 16, v_numReorderRequests_2929_);
lean_ctor_set(v_reuseFailAlloc_2941_, 17, v_conflict_x3f_2930_);
lean_ctor_set(v_reuseFailAlloc_2941_, 18, v_diseqSplits_2931_);
lean_ctor_set(v_reuseFailAlloc_2941_, 19, v_divMod_2932_);
lean_ctor_set(v_reuseFailAlloc_2941_, 20, v_nonlinearOccs_2934_);
lean_ctor_set_uint8(v_reuseFailAlloc_2941_, sizeof(void*)*21, v_caseSplits_2926_);
lean_ctor_set_uint8(v_reuseFailAlloc_2941_, sizeof(void*)*21 + 1, v_usedCommRing_2933_);
v___x_2940_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
return v___x_2940_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1___boxed(lean_object* v_a_2943_, lean_object* v_v_2944_, lean_object* v_s_2945_){
_start:
{
lean_object* v_res_2946_; 
v_res_2946_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1(v_a_2943_, v_v_2944_, v_s_2945_);
lean_dec(v_v_2944_);
return v_res_2946_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3(void){
_start:
{
lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; 
v___x_2954_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2));
v___x_2955_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_2956_ = l_Lean_Name_append(v___x_2955_, v___x_2954_);
return v___x_2956_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6(void){
_start:
{
lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; 
v___x_2963_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5));
v___x_2964_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_2965_ = l_Lean_Name_append(v___x_2964_, v___x_2963_);
return v___x_2965_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9(void){
_start:
{
lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; 
v___x_2972_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__8));
v___x_2973_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_2974_ = l_Lean_Name_append(v___x_2973_, v___x_2972_);
return v___x_2974_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11(void){
_start:
{
lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; 
v___x_2979_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__10));
v___x_2980_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_2981_ = l_Lean_Name_append(v___x_2980_, v___x_2979_);
return v___x_2981_;
}
}
LEAN_EXPORT lean_object* lean_grind_cutsat_assert_le(lean_object* v_c_2982_, lean_object* v_a_2983_, lean_object* v_a_2984_, lean_object* v_a_2985_, lean_object* v_a_2986_, lean_object* v_a_2987_, lean_object* v_a_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_){
_start:
{
lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v___y_3034_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___x_3066_; 
v___x_3066_ = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(v_a_2983_, v_a_2991_);
if (lean_obj_tag(v___x_3066_) == 0)
{
lean_object* v_a_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3207_; 
v_a_3067_ = lean_ctor_get(v___x_3066_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_3066_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3069_ = v___x_3066_;
v_isShared_3070_ = v_isSharedCheck_3207_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_a_3067_);
lean_dec(v___x_3066_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3207_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
uint8_t v___x_3071_; 
v___x_3071_ = lean_unbox(v_a_3067_);
lean_dec(v_a_3067_);
if (v___x_3071_ == 0)
{
lean_object* v_toCold_3072_; lean_object* v_options_3073_; lean_object* v_inheritedTraceOptions_3074_; uint8_t v_hasTrace_3075_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v___y_3085_; lean_object* v___y_3086_; 
lean_del_object(v___x_3069_);
v_toCold_3072_ = lean_ctor_get(v_a_2991_, 0);
v_options_3073_ = lean_ctor_get(v_toCold_3072_, 2);
v_inheritedTraceOptions_3074_ = lean_ctor_get(v_toCold_3072_, 11);
v_hasTrace_3075_ = lean_ctor_get_uint8(v_options_3073_, sizeof(void*)*1);
if (v_hasTrace_3075_ == 0)
{
v___y_3077_ = v_a_2983_;
v___y_3078_ = v_a_2984_;
v___y_3079_ = v_a_2985_;
v___y_3080_ = v_a_2986_;
v___y_3081_ = v_a_2987_;
v___y_3082_ = v_a_2988_;
v___y_3083_ = v_a_2989_;
v___y_3084_ = v_a_2990_;
v___y_3085_ = v_a_2991_;
v___y_3086_ = v_a_2992_;
goto v___jp_3076_;
}
else
{
lean_object* v___x_3189_; lean_object* v___x_3190_; uint8_t v___x_3191_; 
v___x_3189_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__10));
v___x_3190_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__11);
v___x_3191_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3074_, v_options_3073_, v___x_3190_);
if (v___x_3191_ == 0)
{
v___y_3077_ = v_a_2983_;
v___y_3078_ = v_a_2984_;
v___y_3079_ = v_a_2985_;
v___y_3080_ = v_a_2986_;
v___y_3081_ = v_a_2987_;
v___y_3082_ = v_a_2988_;
v___y_3083_ = v_a_2989_;
v___y_3084_ = v_a_2990_;
v___y_3085_ = v_a_2991_;
v___y_3086_ = v_a_2992_;
goto v___jp_3076_;
}
else
{
lean_object* v___x_3192_; 
lean_inc_ref(v_c_2982_);
v___x_3192_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_c_2982_, v_a_2983_, v_a_2991_);
if (lean_obj_tag(v___x_3192_) == 0)
{
lean_object* v_a_3193_; lean_object* v___x_3194_; 
v_a_3193_ = lean_ctor_get(v___x_3192_, 0);
lean_inc(v_a_3193_);
lean_dec_ref_known(v___x_3192_, 1);
v___x_3194_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3189_, v_a_3193_, v_a_2989_, v_a_2990_, v_a_2991_, v_a_2992_);
if (lean_obj_tag(v___x_3194_) == 0)
{
lean_dec_ref_known(v___x_3194_, 1);
v___y_3077_ = v_a_2983_;
v___y_3078_ = v_a_2984_;
v___y_3079_ = v_a_2985_;
v___y_3080_ = v_a_2986_;
v___y_3081_ = v_a_2987_;
v___y_3082_ = v_a_2988_;
v___y_3083_ = v_a_2989_;
v___y_3084_ = v_a_2990_;
v___y_3085_ = v_a_2991_;
v___y_3086_ = v_a_2992_;
goto v___jp_3076_;
}
else
{
lean_dec(v_a_2992_);
lean_dec_ref(v_a_2991_);
lean_dec(v_a_2990_);
lean_dec_ref(v_a_2989_);
lean_dec(v_a_2988_);
lean_dec_ref(v_a_2987_);
lean_dec(v_a_2986_);
lean_dec_ref(v_a_2985_);
lean_dec(v_a_2984_);
lean_dec(v_a_2983_);
lean_dec_ref(v_c_2982_);
return v___x_3194_;
}
}
else
{
lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3202_; 
lean_dec(v_a_2992_);
lean_dec_ref(v_a_2991_);
lean_dec(v_a_2990_);
lean_dec_ref(v_a_2989_);
lean_dec(v_a_2988_);
lean_dec_ref(v_a_2987_);
lean_dec(v_a_2986_);
lean_dec_ref(v_a_2985_);
lean_dec(v_a_2984_);
lean_dec(v_a_2983_);
lean_dec_ref(v_c_2982_);
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
v___jp_3076_:
{
lean_object* v___x_3087_; lean_object* v___x_3088_; 
v___x_3087_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_norm(v_c_2982_);
lean_inc_ref(v___y_3085_);
v___x_3088_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applySubsts(v___x_3087_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_);
if (lean_obj_tag(v___x_3088_) == 0)
{
lean_object* v_a_3089_; lean_object* v_p_3090_; uint8_t v___x_3091_; 
v_a_3089_ = lean_ctor_get(v___x_3088_, 0);
lean_inc(v_a_3089_);
lean_dec_ref_known(v___x_3088_, 1);
v_p_3090_ = lean_ctor_get(v_a_3089_, 0);
v___x_3091_ = l_Int_Internal_Linear_Poly_isUnsatLe(v_p_3090_);
if (v___x_3091_ == 0)
{
uint8_t v___x_3092_; 
v___x_3092_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_isTrivial(v_a_3089_);
if (v___x_3092_ == 0)
{
if (lean_obj_tag(v_p_3090_) == 1)
{
lean_object* v_k_3093_; lean_object* v_v_3094_; lean_object* v___x_3095_; 
v_k_3093_ = lean_ctor_get(v_p_3090_, 0);
lean_inc(v_k_3093_);
v_v_3094_ = lean_ctor_get(v_p_3090_, 1);
lean_inc(v_v_3094_);
lean_inc(v_a_3089_);
v___x_3095_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_findEq(v_a_3089_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_);
if (lean_obj_tag(v___x_3095_) == 0)
{
lean_object* v_a_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3135_; 
v_a_3096_ = lean_ctor_get(v___x_3095_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v___x_3095_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3098_ = v___x_3095_;
v_isShared_3099_ = v_isSharedCheck_3135_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_a_3096_);
lean_dec(v___x_3095_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3135_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
uint8_t v___x_3100_; 
v___x_3100_ = lean_unbox(v_a_3096_);
lean_dec(v_a_3096_);
if (v___x_3100_ == 0)
{
lean_object* v___x_3101_; 
lean_del_object(v___x_3098_);
v___x_3101_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq(v_a_3089_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_);
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3081_);
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3079_);
lean_dec(v___y_3078_);
if (lean_obj_tag(v___x_3101_) == 0)
{
lean_object* v_toCold_3102_; lean_object* v_options_3103_; lean_object* v_a_3104_; lean_object* v_inheritedTraceOptions_3105_; uint8_t v_hasTrace_3106_; lean_object* v___f_3107_; lean_object* v___f_3108_; 
v_toCold_3102_ = lean_ctor_get(v___y_3085_, 0);
v_options_3103_ = lean_ctor_get(v_toCold_3102_, 2);
v_a_3104_ = lean_ctor_get(v___x_3101_, 0);
lean_inc_n(v_a_3104_, 3);
lean_dec_ref_known(v___x_3101_, 1);
v_inheritedTraceOptions_3105_ = lean_ctor_get(v_toCold_3102_, 11);
v_hasTrace_3106_ = lean_ctor_get_uint8(v_options_3103_, sizeof(void*)*1);
lean_inc_n(v_v_3094_, 2);
v___f_3107_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3107_, 0, v_a_3104_);
lean_closure_set(v___f_3107_, 1, v_v_3094_);
v___f_3108_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___lam__1___boxed), 3, 2);
lean_closure_set(v___f_3108_, 0, v_a_3104_);
lean_closure_set(v___f_3108_, 1, v_v_3094_);
if (v_hasTrace_3106_ == 0)
{
v___y_3025_ = v___f_3108_;
v___y_3026_ = v_a_3104_;
v___y_3027_ = v___f_3107_;
v___y_3028_ = v_v_3094_;
v___y_3029_ = v_k_3093_;
v___y_3030_ = v___y_3077_;
v___y_3031_ = v___y_3083_;
v___y_3032_ = v___y_3084_;
v___y_3033_ = v___y_3085_;
v___y_3034_ = v___y_3086_;
goto v___jp_3024_;
}
else
{
lean_object* v___x_3109_; lean_object* v___x_3110_; uint8_t v___x_3111_; 
v___x_3109_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__2));
v___x_3110_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__3);
v___x_3111_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3105_, v_options_3103_, v___x_3110_);
if (v___x_3111_ == 0)
{
v___y_3025_ = v___f_3108_;
v___y_3026_ = v_a_3104_;
v___y_3027_ = v___f_3107_;
v___y_3028_ = v_v_3094_;
v___y_3029_ = v_k_3093_;
v___y_3030_ = v___y_3077_;
v___y_3031_ = v___y_3083_;
v___y_3032_ = v___y_3084_;
v___y_3033_ = v___y_3085_;
v___y_3034_ = v___y_3086_;
goto v___jp_3024_;
}
else
{
lean_object* v___x_3112_; 
lean_inc(v_a_3104_);
v___x_3112_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_a_3104_, v___y_3077_, v___y_3085_);
if (lean_obj_tag(v___x_3112_) == 0)
{
lean_object* v_a_3113_; lean_object* v___x_3114_; 
v_a_3113_ = lean_ctor_get(v___x_3112_, 0);
lean_inc(v_a_3113_);
lean_dec_ref_known(v___x_3112_, 1);
v___x_3114_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3109_, v_a_3113_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_);
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_dec_ref_known(v___x_3114_, 1);
v___y_3025_ = v___f_3108_;
v___y_3026_ = v_a_3104_;
v___y_3027_ = v___f_3107_;
v___y_3028_ = v_v_3094_;
v___y_3029_ = v_k_3093_;
v___y_3030_ = v___y_3077_;
v___y_3031_ = v___y_3083_;
v___y_3032_ = v___y_3084_;
v___y_3033_ = v___y_3085_;
v___y_3034_ = v___y_3086_;
goto v___jp_3024_;
}
else
{
lean_dec_ref(v___f_3108_);
lean_dec_ref(v___f_3107_);
lean_dec(v_a_3104_);
lean_dec(v_v_3094_);
lean_dec(v_k_3093_);
lean_dec(v___y_3086_);
lean_dec_ref(v___y_3085_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
lean_dec(v___y_3077_);
return v___x_3114_;
}
}
else
{
lean_object* v_a_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3122_; 
lean_dec_ref(v___f_3108_);
lean_dec_ref(v___f_3107_);
lean_dec(v_a_3104_);
lean_dec(v_v_3094_);
lean_dec(v_k_3093_);
lean_dec(v___y_3086_);
lean_dec_ref(v___y_3085_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
lean_dec(v___y_3077_);
v_a_3115_ = lean_ctor_get(v___x_3112_, 0);
v_isSharedCheck_3122_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3122_ == 0)
{
v___x_3117_ = v___x_3112_;
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_a_3115_);
lean_dec(v___x_3112_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v___x_3120_; 
if (v_isShared_3118_ == 0)
{
v___x_3120_ = v___x_3117_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v_a_3115_);
v___x_3120_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
return v___x_3120_;
}
}
}
}
}
}
else
{
lean_object* v_a_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3130_; 
lean_dec(v_v_3094_);
lean_dec(v_k_3093_);
lean_dec(v___y_3086_);
lean_dec_ref(v___y_3085_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
lean_dec(v___y_3077_);
v_a_3123_ = lean_ctor_get(v___x_3101_, 0);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3125_ = v___x_3101_;
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_a_3123_);
lean_dec(v___x_3101_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3128_; 
if (v_isShared_3126_ == 0)
{
v___x_3128_ = v___x_3125_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v_a_3123_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
return v___x_3128_;
}
}
}
}
else
{
lean_object* v___x_3131_; lean_object* v___x_3133_; 
lean_dec(v_v_3094_);
lean_dec(v_k_3093_);
lean_dec(v_a_3089_);
lean_dec(v___y_3086_);
lean_dec_ref(v___y_3085_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3081_);
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3079_);
lean_dec(v___y_3078_);
lean_dec(v___y_3077_);
v___x_3131_ = lean_box(0);
if (v_isShared_3099_ == 0)
{
lean_ctor_set(v___x_3098_, 0, v___x_3131_);
v___x_3133_ = v___x_3098_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v___x_3131_);
v___x_3133_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
return v___x_3133_;
}
}
}
}
else
{
lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3143_; 
lean_dec(v_v_3094_);
lean_dec(v_k_3093_);
lean_dec(v_a_3089_);
lean_dec(v___y_3086_);
lean_dec_ref(v___y_3085_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3081_);
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3079_);
lean_dec(v___y_3078_);
lean_dec(v___y_3077_);
v_a_3136_ = lean_ctor_get(v___x_3095_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_3095_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3138_ = v___x_3095_;
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_dec(v___x_3095_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3141_; 
if (v_isShared_3139_ == 0)
{
v___x_3141_ = v___x_3138_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_a_3136_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
return v___x_3141_;
}
}
}
}
else
{
lean_object* v___x_3144_; 
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3081_);
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3079_);
lean_dec(v___y_3078_);
v___x_3144_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_throwUnexpected___redArg(v_a_3089_, v___y_3077_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_);
lean_dec(v___y_3086_);
lean_dec_ref(v___y_3085_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
lean_dec(v___y_3077_);
return v___x_3144_;
}
}
else
{
lean_object* v_toCold_3145_; lean_object* v_options_3146_; uint8_t v_hasTrace_3147_; 
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3081_);
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3079_);
lean_dec(v___y_3078_);
v_toCold_3145_ = lean_ctor_get(v___y_3085_, 0);
v_options_3146_ = lean_ctor_get(v_toCold_3145_, 2);
v_hasTrace_3147_ = lean_ctor_get_uint8(v_options_3146_, sizeof(void*)*1);
if (v_hasTrace_3147_ == 0)
{
lean_dec(v_a_3089_);
lean_dec(v___y_3086_);
lean_dec_ref(v___y_3085_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
lean_dec(v___y_3077_);
goto v___jp_2994_;
}
else
{
lean_object* v_inheritedTraceOptions_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; uint8_t v___x_3151_; 
v_inheritedTraceOptions_3148_ = lean_ctor_get(v_toCold_3145_, 11);
v___x_3149_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__5));
v___x_3150_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__6);
v___x_3151_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3148_, v_options_3146_, v___x_3150_);
if (v___x_3151_ == 0)
{
lean_dec(v_a_3089_);
lean_dec(v___y_3086_);
lean_dec_ref(v___y_3085_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
lean_dec(v___y_3077_);
goto v___jp_2994_;
}
else
{
lean_object* v___x_3152_; 
v___x_3152_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_a_3089_, v___y_3077_, v___y_3085_);
lean_dec(v___y_3077_);
if (lean_obj_tag(v___x_3152_) == 0)
{
lean_object* v_a_3153_; lean_object* v___x_3154_; 
v_a_3153_ = lean_ctor_get(v___x_3152_, 0);
lean_inc(v_a_3153_);
lean_dec_ref_known(v___x_3152_, 1);
v___x_3154_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3149_, v_a_3153_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_);
lean_dec(v___y_3086_);
lean_dec_ref(v___y_3085_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
if (lean_obj_tag(v___x_3154_) == 0)
{
lean_dec_ref_known(v___x_3154_, 1);
goto v___jp_2994_;
}
else
{
return v___x_3154_;
}
}
else
{
lean_object* v_a_3155_; lean_object* v___x_3157_; uint8_t v_isShared_3158_; uint8_t v_isSharedCheck_3162_; 
lean_dec(v___y_3086_);
lean_dec_ref(v___y_3085_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
v_a_3155_ = lean_ctor_get(v___x_3152_, 0);
v_isSharedCheck_3162_ = !lean_is_exclusive(v___x_3152_);
if (v_isSharedCheck_3162_ == 0)
{
v___x_3157_ = v___x_3152_;
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
else
{
lean_inc(v_a_3155_);
lean_dec(v___x_3152_);
v___x_3157_ = lean_box(0);
v_isShared_3158_ = v_isSharedCheck_3162_;
goto v_resetjp_3156_;
}
v_resetjp_3156_:
{
lean_object* v___x_3160_; 
if (v_isShared_3158_ == 0)
{
v___x_3160_ = v___x_3157_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v_a_3155_);
v___x_3160_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3159_;
}
v_reusejp_3159_:
{
return v___x_3160_;
}
}
}
}
}
}
}
else
{
lean_object* v_toCold_3163_; lean_object* v_options_3164_; uint8_t v_hasTrace_3165_; 
v_toCold_3163_ = lean_ctor_get(v___y_3085_, 0);
v_options_3164_ = lean_ctor_get(v_toCold_3163_, 2);
v_hasTrace_3165_ = lean_ctor_get_uint8(v_options_3164_, sizeof(void*)*1);
if (v_hasTrace_3165_ == 0)
{
v___y_3044_ = v_a_3089_;
v___y_3045_ = v___y_3077_;
v___y_3046_ = v___y_3078_;
v___y_3047_ = v___y_3079_;
v___y_3048_ = v___y_3080_;
v___y_3049_ = v___y_3081_;
v___y_3050_ = v___y_3082_;
v___y_3051_ = v___y_3083_;
v___y_3052_ = v___y_3084_;
v___y_3053_ = v___y_3085_;
v___y_3054_ = v___y_3086_;
goto v___jp_3043_;
}
else
{
lean_object* v_inheritedTraceOptions_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; uint8_t v___x_3169_; 
v_inheritedTraceOptions_3166_ = lean_ctor_get(v_toCold_3163_, 11);
v___x_3167_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__8));
v___x_3168_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___closed__9);
v___x_3169_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3166_, v_options_3164_, v___x_3168_);
if (v___x_3169_ == 0)
{
v___y_3044_ = v_a_3089_;
v___y_3045_ = v___y_3077_;
v___y_3046_ = v___y_3078_;
v___y_3047_ = v___y_3079_;
v___y_3048_ = v___y_3080_;
v___y_3049_ = v___y_3081_;
v___y_3050_ = v___y_3082_;
v___y_3051_ = v___y_3083_;
v___y_3052_ = v___y_3084_;
v___y_3053_ = v___y_3085_;
v___y_3054_ = v___y_3086_;
goto v___jp_3043_;
}
else
{
lean_object* v___x_3170_; 
lean_inc(v_a_3089_);
v___x_3170_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_pp___redArg(v_a_3089_, v___y_3077_, v___y_3085_);
if (lean_obj_tag(v___x_3170_) == 0)
{
lean_object* v_a_3171_; lean_object* v___x_3172_; 
v_a_3171_ = lean_ctor_get(v___x_3170_, 0);
lean_inc(v_a_3171_);
lean_dec_ref_known(v___x_3170_, 1);
v___x_3172_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3167_, v_a_3171_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_);
if (lean_obj_tag(v___x_3172_) == 0)
{
lean_dec_ref_known(v___x_3172_, 1);
v___y_3044_ = v_a_3089_;
v___y_3045_ = v___y_3077_;
v___y_3046_ = v___y_3078_;
v___y_3047_ = v___y_3079_;
v___y_3048_ = v___y_3080_;
v___y_3049_ = v___y_3081_;
v___y_3050_ = v___y_3082_;
v___y_3051_ = v___y_3083_;
v___y_3052_ = v___y_3084_;
v___y_3053_ = v___y_3085_;
v___y_3054_ = v___y_3086_;
goto v___jp_3043_;
}
else
{
lean_dec(v_a_3089_);
lean_dec(v___y_3086_);
lean_dec_ref(v___y_3085_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3081_);
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3079_);
lean_dec(v___y_3078_);
lean_dec(v___y_3077_);
return v___x_3172_;
}
}
else
{
lean_object* v_a_3173_; lean_object* v___x_3175_; uint8_t v_isShared_3176_; uint8_t v_isSharedCheck_3180_; 
lean_dec(v_a_3089_);
lean_dec(v___y_3086_);
lean_dec_ref(v___y_3085_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3081_);
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3079_);
lean_dec(v___y_3078_);
lean_dec(v___y_3077_);
v_a_3173_ = lean_ctor_get(v___x_3170_, 0);
v_isSharedCheck_3180_ = !lean_is_exclusive(v___x_3170_);
if (v_isSharedCheck_3180_ == 0)
{
v___x_3175_ = v___x_3170_;
v_isShared_3176_ = v_isSharedCheck_3180_;
goto v_resetjp_3174_;
}
else
{
lean_inc(v_a_3173_);
lean_dec(v___x_3170_);
v___x_3175_ = lean_box(0);
v_isShared_3176_ = v_isSharedCheck_3180_;
goto v_resetjp_3174_;
}
v_resetjp_3174_:
{
lean_object* v___x_3178_; 
if (v_isShared_3176_ == 0)
{
v___x_3178_ = v___x_3175_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3179_; 
v_reuseFailAlloc_3179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3179_, 0, v_a_3173_);
v___x_3178_ = v_reuseFailAlloc_3179_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
return v___x_3178_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3188_; 
lean_dec(v___y_3086_);
lean_dec_ref(v___y_3085_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3081_);
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3079_);
lean_dec(v___y_3078_);
lean_dec(v___y_3077_);
v_a_3181_ = lean_ctor_get(v___x_3088_, 0);
v_isSharedCheck_3188_ = !lean_is_exclusive(v___x_3088_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3183_ = v___x_3088_;
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_a_3181_);
lean_dec(v___x_3088_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v___x_3186_; 
if (v_isShared_3184_ == 0)
{
v___x_3186_ = v___x_3183_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v_a_3181_);
v___x_3186_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
return v___x_3186_;
}
}
}
}
}
else
{
lean_object* v___x_3203_; lean_object* v___x_3205_; 
lean_dec(v_a_2992_);
lean_dec_ref(v_a_2991_);
lean_dec(v_a_2990_);
lean_dec_ref(v_a_2989_);
lean_dec(v_a_2988_);
lean_dec_ref(v_a_2987_);
lean_dec(v_a_2986_);
lean_dec_ref(v_a_2985_);
lean_dec(v_a_2984_);
lean_dec(v_a_2983_);
lean_dec_ref(v_c_2982_);
v___x_3203_ = lean_box(0);
if (v_isShared_3070_ == 0)
{
lean_ctor_set(v___x_3069_, 0, v___x_3203_);
v___x_3205_ = v___x_3069_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v___x_3203_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
}
else
{
lean_object* v_a_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3215_; 
lean_dec(v_a_2992_);
lean_dec_ref(v_a_2991_);
lean_dec(v_a_2990_);
lean_dec_ref(v_a_2989_);
lean_dec(v_a_2988_);
lean_dec_ref(v_a_2987_);
lean_dec(v_a_2986_);
lean_dec_ref(v_a_2985_);
lean_dec(v_a_2984_);
lean_dec(v_a_2983_);
lean_dec_ref(v_c_2982_);
v_a_3208_ = lean_ctor_get(v___x_3066_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___x_3066_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3210_ = v___x_3066_;
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_a_3208_);
lean_dec(v___x_3066_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3213_; 
if (v_isShared_3211_ == 0)
{
v___x_3213_ = v___x_3210_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v_a_3208_);
v___x_3213_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
return v___x_3213_;
}
}
}
v___jp_2994_:
{
lean_object* v___x_2995_; lean_object* v___x_2996_; 
v___x_2995_ = lean_box(0);
v___x_2996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2996_, 0, v___x_2995_);
return v___x_2996_;
}
v___jp_2997_:
{
lean_object* v___x_3002_; 
v___x_3002_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_satisfied___redArg(v___y_2998_, v___y_3000_, v___y_3001_);
lean_dec_ref(v___y_3001_);
if (lean_obj_tag(v___x_3002_) == 0)
{
lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3015_; 
v_a_3003_ = lean_ctor_get(v___x_3002_, 0);
v_isSharedCheck_3015_ = !lean_is_exclusive(v___x_3002_);
if (v_isSharedCheck_3015_ == 0)
{
v___x_3005_ = v___x_3002_;
v_isShared_3006_ = v_isSharedCheck_3015_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_dec(v___x_3002_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3015_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
uint8_t v___x_3007_; uint8_t v___x_3008_; uint8_t v___x_3009_; 
v___x_3007_ = 0;
v___x_3008_ = lean_unbox(v_a_3003_);
lean_dec(v_a_3003_);
v___x_3009_ = l_Lean_instBEqLBool_beq(v___x_3008_, v___x_3007_);
if (v___x_3009_ == 0)
{
lean_object* v___x_3010_; lean_object* v___x_3012_; 
lean_dec(v___y_3000_);
lean_dec(v___y_2999_);
v___x_3010_ = lean_box(0);
if (v_isShared_3006_ == 0)
{
lean_ctor_set(v___x_3005_, 0, v___x_3010_);
v___x_3012_ = v___x_3005_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v___x_3010_);
v___x_3012_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
return v___x_3012_;
}
}
else
{
lean_object* v___x_3014_; 
lean_del_object(v___x_3005_);
v___x_3014_ = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(v___y_2999_, v___y_3000_);
lean_dec(v___y_3000_);
return v___x_3014_;
}
}
}
else
{
lean_object* v_a_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3023_; 
lean_dec(v___y_3000_);
lean_dec(v___y_2999_);
v_a_3016_ = lean_ctor_get(v___x_3002_, 0);
v_isSharedCheck_3023_ = !lean_is_exclusive(v___x_3002_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_3018_ = v___x_3002_;
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_a_3016_);
lean_dec(v___x_3002_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v___x_3021_; 
if (v_isShared_3019_ == 0)
{
v___x_3021_ = v___x_3018_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_a_3016_);
v___x_3021_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
return v___x_3021_;
}
}
}
}
v___jp_3024_:
{
lean_object* v_p_3035_; lean_object* v___x_3036_; 
v_p_3035_ = lean_ctor_get(v___y_3026_, 0);
lean_inc_ref(v_p_3035_);
v___x_3036_ = l_Int_Internal_Linear_Poly_updateOccs___redArg(v_p_3035_, v___y_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_);
lean_dec(v___y_3034_);
lean_dec(v___y_3032_);
lean_dec_ref(v___y_3031_);
if (lean_obj_tag(v___x_3036_) == 0)
{
lean_object* v___x_3037_; uint8_t v___x_3038_; 
lean_dec_ref_known(v___x_3036_, 1);
v___x_3037_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9);
v___x_3038_ = lean_int_dec_lt(v___y_3029_, v___x_3037_);
lean_dec(v___y_3029_);
if (v___x_3038_ == 0)
{
lean_object* v___x_3039_; lean_object* v___x_3040_; 
lean_dec_ref(v___y_3027_);
v___x_3039_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_3040_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3039_, v___y_3025_, v___y_3030_);
if (lean_obj_tag(v___x_3040_) == 0)
{
lean_dec_ref_known(v___x_3040_, 1);
v___y_2998_ = v___y_3026_;
v___y_2999_ = v___y_3028_;
v___y_3000_ = v___y_3030_;
v___y_3001_ = v___y_3033_;
goto v___jp_2997_;
}
else
{
lean_dec_ref(v___y_3033_);
lean_dec(v___y_3030_);
lean_dec(v___y_3028_);
lean_dec_ref(v___y_3026_);
return v___x_3040_;
}
}
else
{
lean_object* v___x_3041_; lean_object* v___x_3042_; 
lean_dec_ref(v___y_3025_);
v___x_3041_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
v___x_3042_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3041_, v___y_3027_, v___y_3030_);
if (lean_obj_tag(v___x_3042_) == 0)
{
lean_dec_ref_known(v___x_3042_, 1);
v___y_2998_ = v___y_3026_;
v___y_2999_ = v___y_3028_;
v___y_3000_ = v___y_3030_;
v___y_3001_ = v___y_3033_;
goto v___jp_2997_;
}
else
{
lean_dec_ref(v___y_3033_);
lean_dec(v___y_3030_);
lean_dec(v___y_3028_);
lean_dec_ref(v___y_3026_);
return v___x_3042_;
}
}
}
else
{
lean_dec_ref(v___y_3033_);
lean_dec(v___y_3030_);
lean_dec(v___y_3029_);
lean_dec(v___y_3028_);
lean_dec_ref(v___y_3027_);
lean_dec_ref(v___y_3026_);
lean_dec_ref(v___y_3025_);
return v___x_3036_;
}
}
v___jp_3043_:
{
lean_object* v___x_3055_; lean_object* v___x_3056_; 
v___x_3055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3055_, 0, v___y_3044_);
v___x_3056_ = l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(v___x_3055_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_);
lean_dec(v___y_3054_);
lean_dec_ref(v___y_3053_);
lean_dec(v___y_3052_);
lean_dec_ref(v___y_3051_);
lean_dec(v___y_3050_);
lean_dec_ref(v___y_3049_);
lean_dec(v___y_3048_);
lean_dec_ref(v___y_3047_);
lean_dec(v___y_3046_);
lean_dec(v___y_3045_);
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3064_; 
v_isSharedCheck_3064_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3064_ == 0)
{
lean_object* v_unused_3065_; 
v_unused_3065_ = lean_ctor_get(v___x_3056_, 0);
lean_dec(v_unused_3065_);
v___x_3058_ = v___x_3056_;
v_isShared_3059_ = v_isSharedCheck_3064_;
goto v_resetjp_3057_;
}
else
{
lean_dec(v___x_3056_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3064_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3060_; lean_object* v___x_3062_; 
v___x_3060_ = lean_box(0);
if (v_isShared_3059_ == 0)
{
lean_ctor_set(v___x_3058_, 0, v___x_3060_);
v___x_3062_ = v___x_3058_;
goto v_reusejp_3061_;
}
else
{
lean_object* v_reuseFailAlloc_3063_; 
v_reuseFailAlloc_3063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3063_, 0, v___x_3060_);
v___x_3062_ = v_reuseFailAlloc_3063_;
goto v_reusejp_3061_;
}
v_reusejp_3061_:
{
return v___x_3062_;
}
}
}
else
{
return v___x_3056_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertImpl___boxed(lean_object* v_c_3216_, lean_object* v_a_3217_, lean_object* v_a_3218_, lean_object* v_a_3219_, lean_object* v_a_3220_, lean_object* v_a_3221_, lean_object* v_a_3222_, lean_object* v_a_3223_, lean_object* v_a_3224_, lean_object* v_a_3225_, lean_object* v_a_3226_, lean_object* v_a_3227_){
_start:
{
lean_object* v_res_3228_; 
v_res_3228_ = lean_grind_cutsat_assert_le(v_c_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_);
return v_res_3228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(lean_object* v_c_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_, lean_object* v_a_3238_, lean_object* v_a_3239_){
_start:
{
lean_object* v_p_3241_; lean_object* v___x_3242_; 
v_p_3241_ = lean_ctor_get(v_c_3229_, 0);
lean_inc_ref(v_p_3241_);
v___x_3242_ = l_Int_Internal_Linear_Poly_normCommRing_x3f(v_p_3241_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_);
if (lean_obj_tag(v___x_3242_) == 0)
{
lean_object* v_a_3243_; 
v_a_3243_ = lean_ctor_get(v___x_3242_, 0);
lean_inc(v_a_3243_);
lean_dec_ref_known(v___x_3242_, 1);
if (lean_obj_tag(v_a_3243_) == 1)
{
lean_object* v_val_3244_; lean_object* v_snd_3245_; lean_object* v_fst_3246_; lean_object* v_fst_3247_; lean_object* v_snd_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3257_; 
v_val_3244_ = lean_ctor_get(v_a_3243_, 0);
lean_inc(v_val_3244_);
lean_dec_ref_known(v_a_3243_, 1);
v_snd_3245_ = lean_ctor_get(v_val_3244_, 1);
lean_inc(v_snd_3245_);
v_fst_3246_ = lean_ctor_get(v_val_3244_, 0);
lean_inc(v_fst_3246_);
lean_dec(v_val_3244_);
v_fst_3247_ = lean_ctor_get(v_snd_3245_, 0);
v_snd_3248_ = lean_ctor_get(v_snd_3245_, 1);
v_isSharedCheck_3257_ = !lean_is_exclusive(v_snd_3245_);
if (v_isSharedCheck_3257_ == 0)
{
v___x_3250_ = v_snd_3245_;
v_isShared_3251_ = v_isSharedCheck_3257_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_snd_3248_);
lean_inc(v_fst_3247_);
lean_dec(v_snd_3245_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3257_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v___x_3252_; lean_object* v___x_3254_; 
v___x_3252_ = lean_alloc_ctor(17, 3, 0);
lean_ctor_set(v___x_3252_, 0, v_c_3229_);
lean_ctor_set(v___x_3252_, 1, v_fst_3246_);
lean_ctor_set(v___x_3252_, 2, v_fst_3247_);
if (v_isShared_3251_ == 0)
{
lean_ctor_set(v___x_3250_, 1, v___x_3252_);
lean_ctor_set(v___x_3250_, 0, v_snd_3248_);
v___x_3254_ = v___x_3250_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v_snd_3248_);
lean_ctor_set(v_reuseFailAlloc_3256_, 1, v___x_3252_);
v___x_3254_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
lean_object* v___x_3255_; 
lean_inc(v_a_3239_);
lean_inc_ref(v_a_3238_);
lean_inc(v_a_3237_);
lean_inc_ref(v_a_3236_);
lean_inc(v_a_3235_);
lean_inc_ref(v_a_3234_);
lean_inc(v_a_3233_);
lean_inc_ref(v_a_3232_);
lean_inc(v_a_3231_);
lean_inc(v_a_3230_);
v___x_3255_ = lean_grind_cutsat_assert_le(v___x_3254_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_);
return v___x_3255_;
}
}
}
else
{
lean_object* v___x_3258_; 
lean_dec(v_a_3243_);
lean_inc(v_a_3239_);
lean_inc_ref(v_a_3238_);
lean_inc(v_a_3237_);
lean_inc_ref(v_a_3236_);
lean_inc(v_a_3235_);
lean_inc_ref(v_a_3234_);
lean_inc(v_a_3233_);
lean_inc_ref(v_a_3232_);
lean_inc(v_a_3231_);
lean_inc(v_a_3230_);
v___x_3258_ = lean_grind_cutsat_assert_le(v_c_3229_, v_a_3230_, v_a_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_);
return v___x_3258_;
}
}
else
{
lean_object* v_a_3259_; lean_object* v___x_3261_; uint8_t v_isShared_3262_; uint8_t v_isSharedCheck_3266_; 
lean_dec_ref(v_c_3229_);
v_a_3259_ = lean_ctor_get(v___x_3242_, 0);
v_isSharedCheck_3266_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3261_ = v___x_3242_;
v_isShared_3262_ = v_isSharedCheck_3266_;
goto v_resetjp_3260_;
}
else
{
lean_inc(v_a_3259_);
lean_dec(v___x_3242_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore___boxed(lean_object* v_c_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_, lean_object* v_a_3272_, lean_object* v_a_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_){
_start:
{
lean_object* v_res_3279_; 
v_res_3279_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v_c_3267_, v_a_3268_, v_a_3269_, v_a_3270_, v_a_3271_, v_a_3272_, v_a_3273_, v_a_3274_, v_a_3275_, v_a_3276_, v_a_3277_);
lean_dec(v_a_3277_);
lean_dec_ref(v_a_3276_);
lean_dec(v_a_3275_);
lean_dec_ref(v_a_3274_);
lean_dec(v_a_3273_);
lean_dec_ref(v_a_3272_);
lean_dec(v_a_3271_);
lean_dec_ref(v_a_3270_);
lean_dec(v_a_3269_);
lean_dec(v_a_3268_);
return v_res_3279_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0(void){
_start:
{
lean_object* v___x_3280_; lean_object* v___x_3281_; 
v___x_3280_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0);
v___x_3281_ = lean_int_neg(v___x_3280_);
return v___x_3281_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__3(void){
_start:
{
lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; 
v___x_3288_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__2));
v___x_3289_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__5));
v___x_3290_ = l_Lean_Name_append(v___x_3289_, v___x_3288_);
return v___x_3290_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__5(void){
_start:
{
lean_object* v___x_3292_; lean_object* v___x_3293_; 
v___x_3292_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__4));
v___x_3293_ = l_Lean_stringToMessageData(v___x_3292_);
return v___x_3293_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__10(void){
_start:
{
lean_object* v___x_3300_; lean_object* v___x_3301_; 
v___x_3300_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__9));
v___x_3301_ = l_Lean_stringToMessageData(v___x_3300_);
return v___x_3301_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe(lean_object* v_e_3302_, uint8_t v_eqTrue_3303_, lean_object* v_a_3304_, lean_object* v_a_3305_, lean_object* v_a_3306_, lean_object* v_a_3307_, lean_object* v_a_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_){
_start:
{
lean_object* v_c_3316_; lean_object* v___y_3317_; lean_object* v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3320_; lean_object* v___y_3321_; lean_object* v___y_3322_; lean_object* v___y_3323_; lean_object* v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; lean_object* v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3353_; lean_object* v___x_3357_; 
lean_inc_ref(v_e_3302_);
v___x_3357_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3302_, v_a_3311_);
if (lean_obj_tag(v___x_3357_) == 0)
{
lean_object* v_a_3358_; lean_object* v___x_3359_; uint8_t v___x_3360_; 
v_a_3358_ = lean_ctor_get(v___x_3357_, 0);
lean_inc(v_a_3358_);
lean_dec_ref_known(v___x_3357_, 1);
v___x_3359_ = l_Lean_Expr_cleanupAnnotations(v_a_3358_);
v___x_3360_ = l_Lean_Expr_isApp(v___x_3359_);
if (v___x_3360_ == 0)
{
lean_dec_ref(v___x_3359_);
lean_dec_ref(v_e_3302_);
goto v___jp_3337_;
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
lean_dec_ref(v_e_3302_);
goto v___jp_3337_;
}
else
{
lean_object* v_arg_3364_; lean_object* v___y_3366_; lean_object* v___y_3367_; lean_object* v___y_3368_; lean_object* v___y_3369_; lean_object* v___y_3370_; lean_object* v___y_3371_; lean_object* v___y_3372_; lean_object* v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3375_; lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3419_; lean_object* v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v___x_3434_; uint8_t v___x_3435_; 
v_arg_3364_ = lean_ctor_get(v___x_3362_, 1);
lean_inc_ref(v_arg_3364_);
v___x_3434_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3362_);
v___x_3435_ = l_Lean_Expr_isApp(v___x_3434_);
if (v___x_3435_ == 0)
{
lean_dec_ref(v___x_3434_);
lean_dec_ref(v_arg_3364_);
lean_dec_ref(v_arg_3361_);
lean_dec_ref(v_e_3302_);
goto v___jp_3337_;
}
else
{
lean_object* v_arg_3436_; lean_object* v___x_3437_; uint8_t v___x_3438_; 
v_arg_3436_ = lean_ctor_get(v___x_3434_, 1);
lean_inc_ref(v_arg_3436_);
v___x_3437_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3434_);
v___x_3438_ = l_Lean_Expr_isApp(v___x_3437_);
if (v___x_3438_ == 0)
{
lean_dec_ref(v___x_3437_);
lean_dec_ref(v_arg_3436_);
lean_dec_ref(v_arg_3364_);
lean_dec_ref(v_arg_3361_);
lean_dec_ref(v_e_3302_);
goto v___jp_3337_;
}
else
{
lean_object* v___x_3439_; lean_object* v___x_3440_; uint8_t v___x_3441_; 
v___x_3439_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3437_);
v___x_3440_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__8));
v___x_3441_ = l_Lean_Expr_isConstOf(v___x_3439_, v___x_3440_);
lean_dec_ref(v___x_3439_);
if (v___x_3441_ == 0)
{
lean_dec_ref(v_arg_3436_);
lean_dec_ref(v_arg_3364_);
lean_dec_ref(v_arg_3361_);
lean_dec_ref(v_e_3302_);
goto v___jp_3337_;
}
else
{
lean_object* v___x_3442_; 
v___x_3442_ = l_Lean_Meta_Structural_isInstLEInt___redArg(v_arg_3436_, v_a_3311_);
if (lean_obj_tag(v___x_3442_) == 0)
{
lean_object* v_a_3443_; lean_object* v___x_3445_; uint8_t v_isShared_3446_; uint8_t v_isSharedCheck_3512_; 
v_a_3443_ = lean_ctor_get(v___x_3442_, 0);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3442_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3445_ = v___x_3442_;
v_isShared_3446_ = v_isSharedCheck_3512_;
goto v_resetjp_3444_;
}
else
{
lean_inc(v_a_3443_);
lean_dec(v___x_3442_);
v___x_3445_ = lean_box(0);
v_isShared_3446_ = v_isSharedCheck_3512_;
goto v_resetjp_3444_;
}
v_resetjp_3444_:
{
uint8_t v___x_3447_; 
v___x_3447_ = lean_unbox(v_a_3443_);
lean_dec(v_a_3443_);
if (v___x_3447_ == 0)
{
lean_object* v___x_3448_; lean_object* v___x_3450_; 
lean_dec_ref(v_arg_3364_);
lean_dec_ref(v_arg_3361_);
lean_dec_ref(v_e_3302_);
v___x_3448_ = lean_box(0);
if (v_isShared_3446_ == 0)
{
lean_ctor_set(v___x_3445_, 0, v___x_3448_);
v___x_3450_ = v___x_3445_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v___x_3448_);
v___x_3450_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
return v___x_3450_;
}
}
else
{
lean_object* v___x_3452_; 
lean_del_object(v___x_3445_);
lean_inc_ref(v_arg_3361_);
v___x_3452_ = l_Lean_Meta_getIntValue_x3f(v_arg_3361_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
if (lean_obj_tag(v___x_3452_) == 0)
{
lean_object* v_a_3453_; 
v_a_3453_ = lean_ctor_get(v___x_3452_, 0);
lean_inc(v_a_3453_);
lean_dec_ref_known(v___x_3452_, 1);
if (lean_obj_tag(v_a_3453_) == 1)
{
lean_object* v_val_3454_; lean_object* v___x_3455_; uint8_t v___x_3456_; 
v_val_3454_ = lean_ctor_get(v_a_3453_, 0);
lean_inc(v_val_3454_);
lean_dec_ref_known(v_a_3453_, 1);
v___x_3455_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9, &l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq___closed__9);
v___x_3456_ = lean_int_dec_eq(v_val_3454_, v___x_3455_);
lean_dec(v_val_3454_);
if (v___x_3456_ == 0)
{
v___y_3413_ = v_a_3304_;
v___y_3414_ = v_a_3305_;
v___y_3415_ = v_a_3306_;
v___y_3416_ = v_a_3307_;
v___y_3417_ = v_a_3308_;
v___y_3418_ = v_a_3309_;
v___y_3419_ = v_a_3310_;
v___y_3420_ = v_a_3311_;
v___y_3421_ = v_a_3312_;
v___y_3422_ = v_a_3313_;
goto v___jp_3412_;
}
else
{
lean_object* v___x_3457_; 
lean_inc_ref(v_arg_3364_);
v___x_3457_ = l_Lean_Meta_Grind_Arith_Cutsat_toPoly_x3f(v_arg_3364_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
if (lean_obj_tag(v___x_3457_) == 0)
{
lean_object* v_a_3458_; 
v_a_3458_ = lean_ctor_get(v___x_3457_, 0);
lean_inc(v_a_3458_);
lean_dec_ref_known(v___x_3457_, 1);
if (lean_obj_tag(v_a_3458_) == 1)
{
lean_object* v_val_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3495_; 
lean_dec_ref(v_arg_3364_);
lean_dec_ref(v_arg_3361_);
v_val_3459_ = lean_ctor_get(v_a_3458_, 0);
v_isSharedCheck_3495_ = !lean_is_exclusive(v_a_3458_);
if (v_isSharedCheck_3495_ == 0)
{
v___x_3461_ = v_a_3458_;
v_isShared_3462_ = v_isSharedCheck_3495_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_val_3459_);
lean_dec(v_a_3458_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3495_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___y_3464_; lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v___y_3473_; lean_object* v_toCold_3484_; lean_object* v_options_3485_; uint8_t v_hasTrace_3486_; 
v_toCold_3484_ = lean_ctor_get(v_a_3312_, 0);
v_options_3485_ = lean_ctor_get(v_toCold_3484_, 2);
v_hasTrace_3486_ = lean_ctor_get_uint8(v_options_3485_, sizeof(void*)*1);
if (v_hasTrace_3486_ == 0)
{
v___y_3464_ = v_a_3304_;
v___y_3465_ = v_a_3305_;
v___y_3466_ = v_a_3306_;
v___y_3467_ = v_a_3307_;
v___y_3468_ = v_a_3308_;
v___y_3469_ = v_a_3309_;
v___y_3470_ = v_a_3310_;
v___y_3471_ = v_a_3311_;
v___y_3472_ = v_a_3312_;
v___y_3473_ = v_a_3313_;
goto v___jp_3463_;
}
else
{
lean_object* v_inheritedTraceOptions_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; uint8_t v___x_3490_; 
v_inheritedTraceOptions_3487_ = lean_ctor_get(v_toCold_3484_, 11);
v___x_3488_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__2));
v___x_3489_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__3);
v___x_3490_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3487_, v_options_3485_, v___x_3489_);
if (v___x_3490_ == 0)
{
v___y_3464_ = v_a_3304_;
v___y_3465_ = v_a_3305_;
v___y_3466_ = v_a_3306_;
v___y_3467_ = v_a_3307_;
v___y_3468_ = v_a_3308_;
v___y_3469_ = v_a_3309_;
v___y_3470_ = v_a_3310_;
v___y_3471_ = v_a_3311_;
v___y_3472_ = v_a_3312_;
v___y_3473_ = v_a_3313_;
goto v___jp_3463_;
}
else
{
lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; 
v___x_3491_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__10, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__10_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__10);
lean_inc_ref(v_e_3302_);
v___x_3492_ = l_Lean_MessageData_ofExpr(v_e_3302_);
v___x_3493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3493_, 0, v___x_3491_);
lean_ctor_set(v___x_3493_, 1, v___x_3492_);
v___x_3494_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3488_, v___x_3493_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
if (lean_obj_tag(v___x_3494_) == 0)
{
lean_dec_ref_known(v___x_3494_, 1);
v___y_3464_ = v_a_3304_;
v___y_3465_ = v_a_3305_;
v___y_3466_ = v_a_3306_;
v___y_3467_ = v_a_3307_;
v___y_3468_ = v_a_3308_;
v___y_3469_ = v_a_3309_;
v___y_3470_ = v_a_3310_;
v___y_3471_ = v_a_3311_;
v___y_3472_ = v_a_3312_;
v___y_3473_ = v_a_3313_;
goto v___jp_3463_;
}
else
{
lean_del_object(v___x_3461_);
lean_dec(v_val_3459_);
lean_dec_ref(v_e_3302_);
return v___x_3494_;
}
}
}
v___jp_3463_:
{
if (v_eqTrue_3303_ == 0)
{
lean_object* v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; 
lean_del_object(v___x_3461_);
v___x_3474_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0);
v___x_3475_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0);
lean_inc(v_val_3459_);
v___x_3476_ = l_Int_Internal_Linear_Poly_mul(v_val_3459_, v___x_3475_);
v___x_3477_ = l_Int_Internal_Linear_Poly_addConst(v___x_3476_, v___x_3474_);
v___x_3478_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3478_, 0, v_e_3302_);
lean_ctor_set(v___x_3478_, 1, v_val_3459_);
v___x_3479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3479_, 0, v___x_3477_);
lean_ctor_set(v___x_3479_, 1, v___x_3478_);
v_c_3316_ = v___x_3479_;
v___y_3317_ = v___y_3464_;
v___y_3318_ = v___y_3465_;
v___y_3319_ = v___y_3466_;
v___y_3320_ = v___y_3467_;
v___y_3321_ = v___y_3468_;
v___y_3322_ = v___y_3469_;
v___y_3323_ = v___y_3470_;
v___y_3324_ = v___y_3471_;
v___y_3325_ = v___y_3472_;
v___y_3326_ = v___y_3473_;
goto v___jp_3315_;
}
else
{
lean_object* v___x_3481_; 
if (v_isShared_3462_ == 0)
{
lean_ctor_set_tag(v___x_3461_, 0);
lean_ctor_set(v___x_3461_, 0, v_e_3302_);
v___x_3481_ = v___x_3461_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_e_3302_);
v___x_3481_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
lean_object* v___x_3482_; 
v___x_3482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3482_, 0, v_val_3459_);
lean_ctor_set(v___x_3482_, 1, v___x_3481_);
v_c_3316_ = v___x_3482_;
v___y_3317_ = v___y_3464_;
v___y_3318_ = v___y_3465_;
v___y_3319_ = v___y_3466_;
v___y_3320_ = v___y_3467_;
v___y_3321_ = v___y_3468_;
v___y_3322_ = v___y_3469_;
v___y_3323_ = v___y_3470_;
v___y_3324_ = v___y_3471_;
v___y_3325_ = v___y_3472_;
v___y_3326_ = v___y_3473_;
goto v___jp_3315_;
}
}
}
}
}
else
{
lean_dec(v_a_3458_);
v___y_3413_ = v_a_3304_;
v___y_3414_ = v_a_3305_;
v___y_3415_ = v_a_3306_;
v___y_3416_ = v_a_3307_;
v___y_3417_ = v_a_3308_;
v___y_3418_ = v_a_3309_;
v___y_3419_ = v_a_3310_;
v___y_3420_ = v_a_3311_;
v___y_3421_ = v_a_3312_;
v___y_3422_ = v_a_3313_;
goto v___jp_3412_;
}
}
else
{
lean_object* v_a_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3503_; 
lean_dec_ref(v_arg_3364_);
lean_dec_ref(v_arg_3361_);
lean_dec_ref(v_e_3302_);
v_a_3496_ = lean_ctor_get(v___x_3457_, 0);
v_isSharedCheck_3503_ = !lean_is_exclusive(v___x_3457_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3498_ = v___x_3457_;
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_a_3496_);
lean_dec(v___x_3457_);
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
else
{
lean_dec(v_a_3453_);
v___y_3413_ = v_a_3304_;
v___y_3414_ = v_a_3305_;
v___y_3415_ = v_a_3306_;
v___y_3416_ = v_a_3307_;
v___y_3417_ = v_a_3308_;
v___y_3418_ = v_a_3309_;
v___y_3419_ = v_a_3310_;
v___y_3420_ = v_a_3311_;
v___y_3421_ = v_a_3312_;
v___y_3422_ = v_a_3313_;
goto v___jp_3412_;
}
}
else
{
lean_object* v_a_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3511_; 
lean_dec_ref(v_arg_3364_);
lean_dec_ref(v_arg_3361_);
lean_dec_ref(v_e_3302_);
v_a_3504_ = lean_ctor_get(v___x_3452_, 0);
v_isSharedCheck_3511_ = !lean_is_exclusive(v___x_3452_);
if (v_isSharedCheck_3511_ == 0)
{
v___x_3506_ = v___x_3452_;
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_a_3504_);
lean_dec(v___x_3452_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3511_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v___x_3509_; 
if (v_isShared_3507_ == 0)
{
v___x_3509_ = v___x_3506_;
goto v_reusejp_3508_;
}
else
{
lean_object* v_reuseFailAlloc_3510_; 
v_reuseFailAlloc_3510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3510_, 0, v_a_3504_);
v___x_3509_ = v_reuseFailAlloc_3510_;
goto v_reusejp_3508_;
}
v_reusejp_3508_:
{
return v___x_3509_;
}
}
}
}
}
}
else
{
lean_object* v_a_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3520_; 
lean_dec_ref(v_arg_3364_);
lean_dec_ref(v_arg_3361_);
lean_dec_ref(v_e_3302_);
v_a_3513_ = lean_ctor_get(v___x_3442_, 0);
v_isSharedCheck_3520_ = !lean_is_exclusive(v___x_3442_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3515_ = v___x_3442_;
v_isShared_3516_ = v_isSharedCheck_3520_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_a_3513_);
lean_dec(v___x_3442_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3520_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___x_3518_; 
if (v_isShared_3516_ == 0)
{
v___x_3518_ = v___x_3515_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v_a_3513_);
v___x_3518_ = v_reuseFailAlloc_3519_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
return v___x_3518_;
}
}
}
}
}
}
v___jp_3365_:
{
lean_object* v___x_3376_; 
v___x_3376_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_3302_, v___y_3366_);
if (lean_obj_tag(v___x_3376_) == 0)
{
lean_object* v_a_3377_; lean_object* v___x_3378_; 
v_a_3377_ = lean_ctor_get(v___x_3376_, 0);
lean_inc_n(v_a_3377_, 2);
lean_dec_ref_known(v___x_3376_, 1);
v___x_3378_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_arg_3364_, v_a_3377_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
if (lean_obj_tag(v___x_3378_) == 0)
{
lean_object* v_a_3379_; lean_object* v___x_3380_; 
v_a_3379_ = lean_ctor_get(v___x_3378_, 0);
lean_inc(v_a_3379_);
lean_dec_ref_known(v___x_3378_, 1);
v___x_3380_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_arg_3361_, v_a_3377_, v___y_3366_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_);
if (lean_obj_tag(v___x_3380_) == 0)
{
lean_object* v_a_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; 
v_a_3381_ = lean_ctor_get(v___x_3380_, 0);
lean_inc_n(v_a_3381_, 2);
lean_dec_ref_known(v___x_3380_, 1);
lean_inc(v_a_3379_);
v___x_3382_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3382_, 0, v_a_3379_);
lean_ctor_set(v___x_3382_, 1, v_a_3381_);
v___x_3383_ = l_Int_Internal_Linear_Expr_norm(v___x_3382_);
lean_dec_ref_known(v___x_3382_, 2);
if (v_eqTrue_3303_ == 0)
{
lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; 
v___x_3384_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0);
v___x_3385_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__0);
v___x_3386_ = l_Int_Internal_Linear_Poly_mul(v___x_3383_, v___x_3385_);
v___x_3387_ = l_Int_Internal_Linear_Poly_addConst(v___x_3386_, v___x_3384_);
v___y_3341_ = v_a_3381_;
v___y_3342_ = v___y_3371_;
v___y_3343_ = v___y_3369_;
v___y_3344_ = v___y_3370_;
v___y_3345_ = v___y_3366_;
v___y_3346_ = v___y_3368_;
v___y_3347_ = v___y_3367_;
v___y_3348_ = v___y_3373_;
v___y_3349_ = v___y_3375_;
v___y_3350_ = v___y_3372_;
v___y_3351_ = v___y_3374_;
v___y_3352_ = v_a_3379_;
v___y_3353_ = v___x_3387_;
goto v___jp_3340_;
}
else
{
v___y_3341_ = v_a_3381_;
v___y_3342_ = v___y_3371_;
v___y_3343_ = v___y_3369_;
v___y_3344_ = v___y_3370_;
v___y_3345_ = v___y_3366_;
v___y_3346_ = v___y_3368_;
v___y_3347_ = v___y_3367_;
v___y_3348_ = v___y_3373_;
v___y_3349_ = v___y_3375_;
v___y_3350_ = v___y_3372_;
v___y_3351_ = v___y_3374_;
v___y_3352_ = v_a_3379_;
v___y_3353_ = v___x_3383_;
goto v___jp_3340_;
}
}
else
{
lean_object* v_a_3388_; lean_object* v___x_3390_; uint8_t v_isShared_3391_; uint8_t v_isSharedCheck_3395_; 
lean_dec(v_a_3379_);
lean_dec_ref(v_e_3302_);
v_a_3388_ = lean_ctor_get(v___x_3380_, 0);
v_isSharedCheck_3395_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3390_ = v___x_3380_;
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
else
{
lean_inc(v_a_3388_);
lean_dec(v___x_3380_);
v___x_3390_ = lean_box(0);
v_isShared_3391_ = v_isSharedCheck_3395_;
goto v_resetjp_3389_;
}
v_resetjp_3389_:
{
lean_object* v___x_3393_; 
if (v_isShared_3391_ == 0)
{
v___x_3393_ = v___x_3390_;
goto v_reusejp_3392_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v_a_3388_);
v___x_3393_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3392_;
}
v_reusejp_3392_:
{
return v___x_3393_;
}
}
}
}
else
{
lean_object* v_a_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3403_; 
lean_dec(v_a_3377_);
lean_dec_ref(v_arg_3361_);
lean_dec_ref(v_e_3302_);
v_a_3396_ = lean_ctor_get(v___x_3378_, 0);
v_isSharedCheck_3403_ = !lean_is_exclusive(v___x_3378_);
if (v_isSharedCheck_3403_ == 0)
{
v___x_3398_ = v___x_3378_;
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_a_3396_);
lean_dec(v___x_3378_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v___x_3401_; 
if (v_isShared_3399_ == 0)
{
v___x_3401_ = v___x_3398_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_a_3396_);
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
lean_object* v_a_3404_; lean_object* v___x_3406_; uint8_t v_isShared_3407_; uint8_t v_isSharedCheck_3411_; 
lean_dec_ref(v_arg_3364_);
lean_dec_ref(v_arg_3361_);
lean_dec_ref(v_e_3302_);
v_a_3404_ = lean_ctor_get(v___x_3376_, 0);
v_isSharedCheck_3411_ = !lean_is_exclusive(v___x_3376_);
if (v_isSharedCheck_3411_ == 0)
{
v___x_3406_ = v___x_3376_;
v_isShared_3407_ = v_isSharedCheck_3411_;
goto v_resetjp_3405_;
}
else
{
lean_inc(v_a_3404_);
lean_dec(v___x_3376_);
v___x_3406_ = lean_box(0);
v_isShared_3407_ = v_isSharedCheck_3411_;
goto v_resetjp_3405_;
}
v_resetjp_3405_:
{
lean_object* v___x_3409_; 
if (v_isShared_3407_ == 0)
{
v___x_3409_ = v___x_3406_;
goto v_reusejp_3408_;
}
else
{
lean_object* v_reuseFailAlloc_3410_; 
v_reuseFailAlloc_3410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3410_, 0, v_a_3404_);
v___x_3409_ = v_reuseFailAlloc_3410_;
goto v_reusejp_3408_;
}
v_reusejp_3408_:
{
return v___x_3409_;
}
}
}
}
v___jp_3412_:
{
lean_object* v_toCold_3423_; lean_object* v_options_3424_; uint8_t v_hasTrace_3425_; 
v_toCold_3423_ = lean_ctor_get(v___y_3421_, 0);
v_options_3424_ = lean_ctor_get(v_toCold_3423_, 2);
v_hasTrace_3425_ = lean_ctor_get_uint8(v_options_3424_, sizeof(void*)*1);
if (v_hasTrace_3425_ == 0)
{
v___y_3366_ = v___y_3413_;
v___y_3367_ = v___y_3414_;
v___y_3368_ = v___y_3415_;
v___y_3369_ = v___y_3416_;
v___y_3370_ = v___y_3417_;
v___y_3371_ = v___y_3418_;
v___y_3372_ = v___y_3419_;
v___y_3373_ = v___y_3420_;
v___y_3374_ = v___y_3421_;
v___y_3375_ = v___y_3422_;
goto v___jp_3365_;
}
else
{
lean_object* v_inheritedTraceOptions_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; uint8_t v___x_3429_; 
v_inheritedTraceOptions_3426_ = lean_ctor_get(v_toCold_3423_, 11);
v___x_3427_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__2));
v___x_3428_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__3, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__3_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__3);
v___x_3429_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3426_, v_options_3424_, v___x_3428_);
if (v___x_3429_ == 0)
{
v___y_3366_ = v___y_3413_;
v___y_3367_ = v___y_3414_;
v___y_3368_ = v___y_3415_;
v___y_3369_ = v___y_3416_;
v___y_3370_ = v___y_3417_;
v___y_3371_ = v___y_3418_;
v___y_3372_ = v___y_3419_;
v___y_3373_ = v___y_3420_;
v___y_3374_ = v___y_3421_;
v___y_3375_ = v___y_3422_;
goto v___jp_3365_;
}
else
{
lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; 
v___x_3430_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__5);
lean_inc_ref(v_e_3302_);
v___x_3431_ = l_Lean_MessageData_ofExpr(v_e_3302_);
v___x_3432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3432_, 0, v___x_3430_);
lean_ctor_set(v___x_3432_, 1, v___x_3431_);
v___x_3433_ = l_Lean_addTrace___at___00Lean_Meta_Grind_Arith_Cutsat_LeCnstr_applyEq_spec__0___redArg(v___x_3427_, v___x_3432_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_);
if (lean_obj_tag(v___x_3433_) == 0)
{
lean_dec_ref_known(v___x_3433_, 1);
v___y_3366_ = v___y_3413_;
v___y_3367_ = v___y_3414_;
v___y_3368_ = v___y_3415_;
v___y_3369_ = v___y_3416_;
v___y_3370_ = v___y_3417_;
v___y_3371_ = v___y_3418_;
v___y_3372_ = v___y_3419_;
v___y_3373_ = v___y_3420_;
v___y_3374_ = v___y_3421_;
v___y_3375_ = v___y_3422_;
goto v___jp_3365_;
}
else
{
lean_dec_ref(v_arg_3364_);
lean_dec_ref(v_arg_3361_);
lean_dec_ref(v_e_3302_);
return v___x_3433_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3521_; lean_object* v___x_3523_; uint8_t v_isShared_3524_; uint8_t v_isSharedCheck_3528_; 
lean_dec_ref(v_e_3302_);
v_a_3521_ = lean_ctor_get(v___x_3357_, 0);
v_isSharedCheck_3528_ = !lean_is_exclusive(v___x_3357_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3523_ = v___x_3357_;
v_isShared_3524_ = v_isSharedCheck_3528_;
goto v_resetjp_3522_;
}
else
{
lean_inc(v_a_3521_);
lean_dec(v___x_3357_);
v___x_3523_ = lean_box(0);
v_isShared_3524_ = v_isSharedCheck_3528_;
goto v_resetjp_3522_;
}
v_resetjp_3522_:
{
lean_object* v___x_3526_; 
if (v_isShared_3524_ == 0)
{
v___x_3526_ = v___x_3523_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v_a_3521_);
v___x_3526_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
return v___x_3526_;
}
}
}
v___jp_3315_:
{
lean_object* v___x_3327_; 
v___x_3327_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v_c_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_, v___y_3326_);
if (lean_obj_tag(v___x_3327_) == 0)
{
lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3335_; 
v_isSharedCheck_3335_ = !lean_is_exclusive(v___x_3327_);
if (v_isSharedCheck_3335_ == 0)
{
lean_object* v_unused_3336_; 
v_unused_3336_ = lean_ctor_get(v___x_3327_, 0);
lean_dec(v_unused_3336_);
v___x_3329_ = v___x_3327_;
v_isShared_3330_ = v_isSharedCheck_3335_;
goto v_resetjp_3328_;
}
else
{
lean_dec(v___x_3327_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3335_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
lean_object* v___x_3331_; lean_object* v___x_3333_; 
v___x_3331_ = lean_box(0);
if (v_isShared_3330_ == 0)
{
lean_ctor_set(v___x_3329_, 0, v___x_3331_);
v___x_3333_ = v___x_3329_;
goto v_reusejp_3332_;
}
else
{
lean_object* v_reuseFailAlloc_3334_; 
v_reuseFailAlloc_3334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3334_, 0, v___x_3331_);
v___x_3333_ = v_reuseFailAlloc_3334_;
goto v_reusejp_3332_;
}
v_reusejp_3332_:
{
return v___x_3333_;
}
}
}
else
{
return v___x_3327_;
}
}
v___jp_3337_:
{
lean_object* v___x_3338_; lean_object* v___x_3339_; 
v___x_3338_ = lean_box(0);
v___x_3339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3339_, 0, v___x_3338_);
return v___x_3339_;
}
v___jp_3340_:
{
lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
v___x_3354_ = lean_alloc_ctor(3, 3, 1);
lean_ctor_set(v___x_3354_, 0, v_e_3302_);
lean_ctor_set(v___x_3354_, 1, v___y_3352_);
lean_ctor_set(v___x_3354_, 2, v___y_3341_);
lean_ctor_set_uint8(v___x_3354_, sizeof(void*)*3, v_eqTrue_3303_);
v___x_3355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3355_, 0, v___y_3353_);
lean_ctor_set(v___x_3355_, 1, v___x_3354_);
v___x_3356_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v___x_3355_, v___y_3345_, v___y_3347_, v___y_3346_, v___y_3343_, v___y_3344_, v___y_3342_, v___y_3350_, v___y_3348_, v___y_3351_, v___y_3349_);
return v___x_3356_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___boxed(lean_object* v_e_3529_, lean_object* v_eqTrue_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_){
_start:
{
uint8_t v_eqTrue_boxed_3542_; lean_object* v_res_3543_; 
v_eqTrue_boxed_3542_ = lean_unbox(v_eqTrue_3530_);
v_res_3543_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe(v_e_3529_, v_eqTrue_boxed_3542_, v_a_3531_, v_a_3532_, v_a_3533_, v_a_3534_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_, v_a_3539_, v_a_3540_);
lean_dec(v_a_3540_);
lean_dec_ref(v_a_3539_);
lean_dec(v_a_3538_);
lean_dec_ref(v_a_3537_);
lean_dec(v_a_3536_);
lean_dec_ref(v_a_3535_);
lean_dec(v_a_3534_);
lean_dec_ref(v_a_3533_);
lean_dec(v_a_3532_);
lean_dec(v_a_3531_);
return v_res_3543_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0(void){
_start:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; 
v___x_3544_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_refineWithDiseq_refineWithDiseqStep_x3f_spec__2_spec__7_spec__11___redArg___closed__0);
v___x_3545_ = l_Lean_mkIntLit(v___x_3544_);
return v___x_3545_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5(void){
_start:
{
lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; 
v___x_3553_ = lean_box(0);
v___x_3554_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__4));
v___x_3555_ = l_Lean_mkConst(v___x_3554_, v___x_3553_);
return v___x_3555_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8(void){
_start:
{
lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; 
v___x_3561_ = lean_box(0);
v___x_3562_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__7));
v___x_3563_ = l_Lean_mkConst(v___x_3562_, v___x_3561_);
return v___x_3563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe(lean_object* v_e_3564_, uint8_t v_eqTrue_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_){
_start:
{
lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v_fst_3580_; lean_object* v_snd_3581_; lean_object* v___x_3610_; uint8_t v___x_3611_; 
lean_inc_ref(v_e_3564_);
v___x_3610_ = l_Lean_Expr_cleanupAnnotations(v_e_3564_);
v___x_3611_ = l_Lean_Expr_isApp(v___x_3610_);
if (v___x_3611_ == 0)
{
lean_dec_ref(v___x_3610_);
lean_dec_ref(v_e_3564_);
goto v___jp_3607_;
}
else
{
lean_object* v_arg_3612_; lean_object* v___x_3613_; uint8_t v___x_3614_; 
v_arg_3612_ = lean_ctor_get(v___x_3610_, 1);
lean_inc_ref(v_arg_3612_);
v___x_3613_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3610_);
v___x_3614_ = l_Lean_Expr_isApp(v___x_3613_);
if (v___x_3614_ == 0)
{
lean_dec_ref(v___x_3613_);
lean_dec_ref(v_arg_3612_);
lean_dec_ref(v_e_3564_);
goto v___jp_3607_;
}
else
{
lean_object* v_arg_3615_; lean_object* v___y_3617_; lean_object* v___x_3655_; uint8_t v___x_3656_; 
v_arg_3615_ = lean_ctor_get(v___x_3613_, 1);
lean_inc_ref(v_arg_3615_);
v___x_3655_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3613_);
v___x_3656_ = l_Lean_Expr_isApp(v___x_3655_);
if (v___x_3656_ == 0)
{
lean_dec_ref(v___x_3655_);
lean_dec_ref(v_arg_3615_);
lean_dec_ref(v_arg_3612_);
lean_dec_ref(v_e_3564_);
goto v___jp_3607_;
}
else
{
lean_object* v___x_3657_; uint8_t v___x_3658_; 
v___x_3657_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3655_);
v___x_3658_ = l_Lean_Expr_isApp(v___x_3657_);
if (v___x_3658_ == 0)
{
lean_dec_ref(v___x_3657_);
lean_dec_ref(v_arg_3615_);
lean_dec_ref(v_arg_3612_);
lean_dec_ref(v_e_3564_);
goto v___jp_3607_;
}
else
{
lean_object* v___x_3659_; lean_object* v___x_3660_; uint8_t v___x_3661_; 
v___x_3659_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3657_);
v___x_3660_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__8));
v___x_3661_ = l_Lean_Expr_isConstOf(v___x_3659_, v___x_3660_);
lean_dec_ref(v___x_3659_);
if (v___x_3661_ == 0)
{
lean_dec_ref(v_arg_3615_);
lean_dec_ref(v_arg_3612_);
lean_dec_ref(v_e_3564_);
goto v___jp_3607_;
}
else
{
if (v_eqTrue_3565_ == 0)
{
lean_object* v___x_3662_; 
v___x_3662_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__5);
v___y_3617_ = v___x_3662_;
goto v___jp_3616_;
}
else
{
lean_object* v___x_3663_; 
v___x_3663_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__8);
v___y_3617_ = v___x_3663_;
goto v___jp_3616_;
}
}
}
}
v___jp_3616_:
{
lean_object* v___x_3618_; 
v___x_3618_ = l_Lean_Meta_Grind_getGeneration___redArg(v_e_3564_, v_a_3566_);
if (lean_obj_tag(v___x_3618_) == 0)
{
lean_object* v_a_3619_; lean_object* v___x_3620_; 
v_a_3619_ = lean_ctor_get(v___x_3618_, 0);
lean_inc(v_a_3619_);
lean_dec_ref_known(v___x_3618_, 1);
lean_inc_ref(v_arg_3615_);
v___x_3620_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_3615_, v_a_3566_, v_a_3567_, v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_);
if (lean_obj_tag(v___x_3620_) == 0)
{
lean_object* v_a_3621_; lean_object* v_fst_3622_; lean_object* v_snd_3623_; lean_object* v___x_3624_; 
v_a_3621_ = lean_ctor_get(v___x_3620_, 0);
lean_inc(v_a_3621_);
lean_dec_ref_known(v___x_3620_, 1);
v_fst_3622_ = lean_ctor_get(v_a_3621_, 0);
lean_inc(v_fst_3622_);
v_snd_3623_ = lean_ctor_get(v_a_3621_, 1);
lean_inc(v_snd_3623_);
lean_dec(v_a_3621_);
lean_inc_ref(v_arg_3612_);
v___x_3624_ = l_Lean_Meta_Grind_Arith_Cutsat_natToInt(v_arg_3612_, v_a_3566_, v_a_3567_, v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_);
if (lean_obj_tag(v___x_3624_) == 0)
{
lean_object* v_a_3625_; lean_object* v_fst_3626_; lean_object* v_snd_3627_; lean_object* v___x_3628_; 
v_a_3625_ = lean_ctor_get(v___x_3624_, 0);
lean_inc(v_a_3625_);
lean_dec_ref_known(v___x_3624_, 1);
v_fst_3626_ = lean_ctor_get(v_a_3625_, 0);
lean_inc_n(v_fst_3626_, 2);
v_snd_3627_ = lean_ctor_get(v_a_3625_, 1);
lean_inc(v_snd_3627_);
lean_dec(v_a_3625_);
lean_inc(v_fst_3622_);
lean_inc_ref(v___y_3617_);
v___x_3628_ = l_Lean_mkApp6(v___y_3617_, v_arg_3615_, v_arg_3612_, v_fst_3622_, v_fst_3626_, v_snd_3623_, v_snd_3627_);
if (v_eqTrue_3565_ == 0)
{
lean_object* v___x_3629_; lean_object* v___x_3630_; 
v___x_3629_ = lean_obj_once(&l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0, &l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0_once, _init_l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___closed__0);
v___x_3630_ = l_Lean_mkIntAdd(v_fst_3626_, v___x_3629_);
v___y_3578_ = v___x_3628_;
v___y_3579_ = v_a_3619_;
v_fst_3580_ = v___x_3630_;
v_snd_3581_ = v_fst_3622_;
goto v___jp_3577_;
}
else
{
v___y_3578_ = v___x_3628_;
v___y_3579_ = v_a_3619_;
v_fst_3580_ = v_fst_3622_;
v_snd_3581_ = v_fst_3626_;
goto v___jp_3577_;
}
}
else
{
lean_object* v_a_3631_; lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3638_; 
lean_dec(v_snd_3623_);
lean_dec(v_fst_3622_);
lean_dec(v_a_3619_);
lean_dec_ref(v_arg_3615_);
lean_dec_ref(v_arg_3612_);
lean_dec_ref(v_e_3564_);
v_a_3631_ = lean_ctor_get(v___x_3624_, 0);
v_isSharedCheck_3638_ = !lean_is_exclusive(v___x_3624_);
if (v_isSharedCheck_3638_ == 0)
{
v___x_3633_ = v___x_3624_;
v_isShared_3634_ = v_isSharedCheck_3638_;
goto v_resetjp_3632_;
}
else
{
lean_inc(v_a_3631_);
lean_dec(v___x_3624_);
v___x_3633_ = lean_box(0);
v_isShared_3634_ = v_isSharedCheck_3638_;
goto v_resetjp_3632_;
}
v_resetjp_3632_:
{
lean_object* v___x_3636_; 
if (v_isShared_3634_ == 0)
{
v___x_3636_ = v___x_3633_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v_a_3631_);
v___x_3636_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
return v___x_3636_;
}
}
}
}
else
{
lean_object* v_a_3639_; lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3646_; 
lean_dec(v_a_3619_);
lean_dec_ref(v_arg_3615_);
lean_dec_ref(v_arg_3612_);
lean_dec_ref(v_e_3564_);
v_a_3639_ = lean_ctor_get(v___x_3620_, 0);
v_isSharedCheck_3646_ = !lean_is_exclusive(v___x_3620_);
if (v_isSharedCheck_3646_ == 0)
{
v___x_3641_ = v___x_3620_;
v_isShared_3642_ = v_isSharedCheck_3646_;
goto v_resetjp_3640_;
}
else
{
lean_inc(v_a_3639_);
lean_dec(v___x_3620_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3646_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
lean_object* v___x_3644_; 
if (v_isShared_3642_ == 0)
{
v___x_3644_ = v___x_3641_;
goto v_reusejp_3643_;
}
else
{
lean_object* v_reuseFailAlloc_3645_; 
v_reuseFailAlloc_3645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3645_, 0, v_a_3639_);
v___x_3644_ = v_reuseFailAlloc_3645_;
goto v_reusejp_3643_;
}
v_reusejp_3643_:
{
return v___x_3644_;
}
}
}
}
else
{
lean_object* v_a_3647_; lean_object* v___x_3649_; uint8_t v_isShared_3650_; uint8_t v_isSharedCheck_3654_; 
lean_dec_ref(v_arg_3615_);
lean_dec_ref(v_arg_3612_);
lean_dec_ref(v_e_3564_);
v_a_3647_ = lean_ctor_get(v___x_3618_, 0);
v_isSharedCheck_3654_ = !lean_is_exclusive(v___x_3618_);
if (v_isSharedCheck_3654_ == 0)
{
v___x_3649_ = v___x_3618_;
v_isShared_3650_ = v_isSharedCheck_3654_;
goto v_resetjp_3648_;
}
else
{
lean_inc(v_a_3647_);
lean_dec(v___x_3618_);
v___x_3649_ = lean_box(0);
v_isShared_3650_ = v_isSharedCheck_3654_;
goto v_resetjp_3648_;
}
v_resetjp_3648_:
{
lean_object* v___x_3652_; 
if (v_isShared_3650_ == 0)
{
v___x_3652_ = v___x_3649_;
goto v_reusejp_3651_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v_a_3647_);
v___x_3652_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3651_;
}
v_reusejp_3651_:
{
return v___x_3652_;
}
}
}
}
}
}
v___jp_3577_:
{
lean_object* v___x_3582_; 
lean_inc(v___y_3579_);
v___x_3582_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_fst_3580_, v___y_3579_, v_a_3566_, v_a_3567_, v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_);
if (lean_obj_tag(v___x_3582_) == 0)
{
lean_object* v_a_3583_; lean_object* v___x_3584_; 
v_a_3583_ = lean_ctor_get(v___x_3582_, 0);
lean_inc(v_a_3583_);
lean_dec_ref_known(v___x_3582_, 1);
v___x_3584_ = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(v_snd_3581_, v___y_3579_, v_a_3566_, v_a_3567_, v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_);
if (lean_obj_tag(v___x_3584_) == 0)
{
lean_object* v_a_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; 
v_a_3585_ = lean_ctor_get(v___x_3584_, 0);
lean_inc_n(v_a_3585_, 2);
lean_dec_ref_known(v___x_3584_, 1);
lean_inc(v_a_3583_);
v___x_3586_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_3586_, 0, v_a_3583_);
lean_ctor_set(v___x_3586_, 1, v_a_3585_);
v___x_3587_ = l_Int_Internal_Linear_Expr_norm(v___x_3586_);
lean_dec_ref_known(v___x_3586_, 2);
v___x_3588_ = lean_alloc_ctor(2, 4, 1);
lean_ctor_set(v___x_3588_, 0, v_e_3564_);
lean_ctor_set(v___x_3588_, 1, v___y_3578_);
lean_ctor_set(v___x_3588_, 2, v_a_3583_);
lean_ctor_set(v___x_3588_, 3, v_a_3585_);
lean_ctor_set_uint8(v___x_3588_, sizeof(void*)*4, v_eqTrue_3565_);
v___x_3589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3589_, 0, v___x_3587_);
lean_ctor_set(v___x_3589_, 1, v___x_3588_);
v___x_3590_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr_0__Lean_Meta_Grind_Arith_Cutsat_LeCnstr_assertCore(v___x_3589_, v_a_3566_, v_a_3567_, v_a_3568_, v_a_3569_, v_a_3570_, v_a_3571_, v_a_3572_, v_a_3573_, v_a_3574_, v_a_3575_);
return v___x_3590_;
}
else
{
lean_object* v_a_3591_; lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3598_; 
lean_dec(v_a_3583_);
lean_dec_ref(v___y_3578_);
lean_dec_ref(v_e_3564_);
v_a_3591_ = lean_ctor_get(v___x_3584_, 0);
v_isSharedCheck_3598_ = !lean_is_exclusive(v___x_3584_);
if (v_isSharedCheck_3598_ == 0)
{
v___x_3593_ = v___x_3584_;
v_isShared_3594_ = v_isSharedCheck_3598_;
goto v_resetjp_3592_;
}
else
{
lean_inc(v_a_3591_);
lean_dec(v___x_3584_);
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
else
{
lean_object* v_a_3599_; lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3606_; 
lean_dec_ref(v_snd_3581_);
lean_dec(v___y_3579_);
lean_dec_ref(v___y_3578_);
lean_dec_ref(v_e_3564_);
v_a_3599_ = lean_ctor_get(v___x_3582_, 0);
v_isSharedCheck_3606_ = !lean_is_exclusive(v___x_3582_);
if (v_isSharedCheck_3606_ == 0)
{
v___x_3601_ = v___x_3582_;
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
else
{
lean_inc(v_a_3599_);
lean_dec(v___x_3582_);
v___x_3601_ = lean_box(0);
v_isShared_3602_ = v_isSharedCheck_3606_;
goto v_resetjp_3600_;
}
v_resetjp_3600_:
{
lean_object* v___x_3604_; 
if (v_isShared_3602_ == 0)
{
v___x_3604_ = v___x_3601_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3605_; 
v_reuseFailAlloc_3605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3605_, 0, v_a_3599_);
v___x_3604_ = v_reuseFailAlloc_3605_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
return v___x_3604_;
}
}
}
}
v___jp_3607_:
{
lean_object* v___x_3608_; lean_object* v___x_3609_; 
v___x_3608_ = lean_box(0);
v___x_3609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3609_, 0, v___x_3608_);
return v___x_3609_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe___boxed(lean_object* v_e_3664_, lean_object* v_eqTrue_3665_, lean_object* v_a_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_, lean_object* v_a_3669_, lean_object* v_a_3670_, lean_object* v_a_3671_, lean_object* v_a_3672_, lean_object* v_a_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_){
_start:
{
uint8_t v_eqTrue_boxed_3677_; lean_object* v_res_3678_; 
v_eqTrue_boxed_3677_ = lean_unbox(v_eqTrue_3665_);
v_res_3678_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe(v_e_3664_, v_eqTrue_boxed_3677_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_, v_a_3670_, v_a_3671_, v_a_3672_, v_a_3673_, v_a_3674_, v_a_3675_);
lean_dec(v_a_3675_);
lean_dec_ref(v_a_3674_);
lean_dec(v_a_3673_);
lean_dec_ref(v_a_3672_);
lean_dec(v_a_3671_);
lean_dec_ref(v_a_3670_);
lean_dec(v_a_3669_);
lean_dec_ref(v_a_3668_);
lean_dec(v_a_3667_);
lean_dec(v_a_3666_);
return v_res_3678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe(lean_object* v_e_3684_, uint8_t v_eqTrue_3685_, lean_object* v_a_3686_, lean_object* v_a_3687_, lean_object* v_a_3688_, lean_object* v_a_3689_, lean_object* v_a_3690_, lean_object* v_a_3691_, lean_object* v_a_3692_, lean_object* v_a_3693_, lean_object* v_a_3694_, lean_object* v_a_3695_){
_start:
{
lean_object* v___x_3700_; 
v___x_3700_ = l_Lean_Meta_Grind_getConfig___redArg(v_a_3688_);
if (lean_obj_tag(v___x_3700_) == 0)
{
lean_object* v_a_3701_; lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3732_; 
v_a_3701_ = lean_ctor_get(v___x_3700_, 0);
v_isSharedCheck_3732_ = !lean_is_exclusive(v___x_3700_);
if (v_isSharedCheck_3732_ == 0)
{
v___x_3703_ = v___x_3700_;
v_isShared_3704_ = v_isSharedCheck_3732_;
goto v_resetjp_3702_;
}
else
{
lean_inc(v_a_3701_);
lean_dec(v___x_3700_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_3732_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
uint8_t v_lia_3705_; 
v_lia_3705_ = lean_ctor_get_uint8(v_a_3701_, sizeof(void*)*17 + 24);
lean_dec(v_a_3701_);
if (v_lia_3705_ == 0)
{
lean_object* v___x_3706_; lean_object* v___x_3708_; 
lean_dec_ref(v_e_3684_);
v___x_3706_ = lean_box(0);
if (v_isShared_3704_ == 0)
{
lean_ctor_set(v___x_3703_, 0, v___x_3706_);
v___x_3708_ = v___x_3703_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v___x_3706_);
v___x_3708_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
return v___x_3708_;
}
}
else
{
lean_object* v___x_3710_; uint8_t v___x_3711_; 
lean_inc_ref(v_e_3684_);
v___x_3710_ = l_Lean_Expr_cleanupAnnotations(v_e_3684_);
v___x_3711_ = l_Lean_Expr_isApp(v___x_3710_);
if (v___x_3711_ == 0)
{
lean_dec_ref(v___x_3710_);
lean_del_object(v___x_3703_);
lean_dec_ref(v_e_3684_);
goto v___jp_3697_;
}
else
{
lean_object* v___x_3712_; uint8_t v___x_3713_; 
v___x_3712_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3710_);
v___x_3713_ = l_Lean_Expr_isApp(v___x_3712_);
if (v___x_3713_ == 0)
{
lean_dec_ref(v___x_3712_);
lean_del_object(v___x_3703_);
lean_dec_ref(v_e_3684_);
goto v___jp_3697_;
}
else
{
lean_object* v___x_3714_; uint8_t v___x_3715_; 
v___x_3714_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3712_);
v___x_3715_ = l_Lean_Expr_isApp(v___x_3714_);
if (v___x_3715_ == 0)
{
lean_dec_ref(v___x_3714_);
lean_del_object(v___x_3703_);
lean_dec_ref(v_e_3684_);
goto v___jp_3697_;
}
else
{
lean_object* v___x_3716_; uint8_t v___x_3717_; 
v___x_3716_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3714_);
v___x_3717_ = l_Lean_Expr_isApp(v___x_3716_);
if (v___x_3717_ == 0)
{
lean_dec_ref(v___x_3716_);
lean_del_object(v___x_3703_);
lean_dec_ref(v_e_3684_);
goto v___jp_3697_;
}
else
{
lean_object* v_arg_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; uint8_t v___x_3721_; 
v_arg_3718_ = lean_ctor_get(v___x_3716_, 1);
lean_inc_ref(v_arg_3718_);
v___x_3719_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3716_);
v___x_3720_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe___closed__8));
v___x_3721_ = l_Lean_Expr_isConstOf(v___x_3719_, v___x_3720_);
lean_dec_ref(v___x_3719_);
if (v___x_3721_ == 0)
{
lean_dec_ref(v_arg_3718_);
lean_del_object(v___x_3703_);
lean_dec_ref(v_e_3684_);
goto v___jp_3697_;
}
else
{
lean_object* v___x_3722_; uint8_t v___x_3723_; 
v___x_3722_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__0));
v___x_3723_ = l_Lean_Expr_isConstOf(v_arg_3718_, v___x_3722_);
if (v___x_3723_ == 0)
{
lean_object* v___x_3724_; uint8_t v___x_3725_; 
v___x_3724_ = ((lean_object*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___closed__2));
v___x_3725_ = l_Lean_Expr_isConstOf(v_arg_3718_, v___x_3724_);
lean_dec_ref(v_arg_3718_);
if (v___x_3725_ == 0)
{
lean_object* v___x_3726_; lean_object* v___x_3728_; 
lean_dec_ref(v_e_3684_);
v___x_3726_ = lean_box(0);
if (v_isShared_3704_ == 0)
{
lean_ctor_set(v___x_3703_, 0, v___x_3726_);
v___x_3728_ = v___x_3703_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v___x_3726_);
v___x_3728_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
return v___x_3728_;
}
}
else
{
lean_object* v___x_3730_; 
lean_del_object(v___x_3703_);
v___x_3730_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntLe(v_e_3684_, v_eqTrue_3685_, v_a_3686_, v_a_3687_, v_a_3688_, v_a_3689_, v_a_3690_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_);
return v___x_3730_;
}
}
else
{
lean_object* v___x_3731_; 
lean_dec_ref(v_arg_3718_);
lean_del_object(v___x_3703_);
v___x_3731_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatLe(v_e_3684_, v_eqTrue_3685_, v_a_3686_, v_a_3687_, v_a_3688_, v_a_3689_, v_a_3690_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_);
return v___x_3731_;
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
lean_object* v_a_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3740_; 
lean_dec_ref(v_e_3684_);
v_a_3733_ = lean_ctor_get(v___x_3700_, 0);
v_isSharedCheck_3740_ = !lean_is_exclusive(v___x_3700_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3735_ = v___x_3700_;
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_a_3733_);
lean_dec(v___x_3700_);
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
v___jp_3697_:
{
lean_object* v___x_3698_; lean_object* v___x_3699_; 
v___x_3698_ = lean_box(0);
v___x_3699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3699_, 0, v___x_3698_);
return v___x_3699_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe___boxed(lean_object* v_e_3741_, lean_object* v_eqTrue_3742_, lean_object* v_a_3743_, lean_object* v_a_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_, lean_object* v_a_3751_, lean_object* v_a_3752_, lean_object* v_a_3753_){
_start:
{
uint8_t v_eqTrue_boxed_3754_; lean_object* v_res_3755_; 
v_eqTrue_boxed_3754_ = lean_unbox(v_eqTrue_3742_);
v_res_3755_ = l_Lean_Meta_Grind_Arith_Cutsat_propagateLe(v_e_3741_, v_eqTrue_boxed_3754_, v_a_3743_, v_a_3744_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_, v_a_3751_, v_a_3752_);
lean_dec(v_a_3752_);
lean_dec_ref(v_a_3751_);
lean_dec(v_a_3750_);
lean_dec_ref(v_a_3749_);
lean_dec(v_a_3748_);
lean_dec_ref(v_a_3747_);
lean_dec(v_a_3746_);
lean_dec_ref(v_a_3745_);
lean_dec(v_a_3744_);
lean_dec(v_a_3743_);
return v_res_3755_;
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
